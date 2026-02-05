package main

import (
	"bufio"
	"bytes"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"image"
	"image/color"
	"io"
	"math"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"time"

	"github.com/hajimehoshi/ebiten/v2"
	"github.com/hajimehoshi/ebiten/v2/audio"
	"github.com/hajimehoshi/ebiten/v2/ebitenutil"
	"github.com/hajimehoshi/ebiten/v2/inpututil"
	"github.com/hajimehoshi/ebiten/v2/vector"
	"github.com/klauspost/compress/zstd"
)

const (
	alixBlockFrames = 1024
	alixOpSilence   = 0x00
	alixOpPCM       = 0x01
	alixOpD8        = 0x02
	alixOpD16       = 0x03
)

const (
	maxMeshVerticesPerBatch = 60000
)

const (
	waveformPoints    = 1024
	waveformLineWidth = 2
)

var meshWhiteImage = func() *ebiten.Image {
	img := ebiten.NewImage(1, 1)
	img.Fill(color.White)
	return img
}()

var PureColorTokens = map[color.RGBA]string{
	{0, 0, 0, 255}:       "K",
	{255, 255, 255, 255}: "W",
	{255, 0, 0, 255}:     "R",
	{0, 255, 0, 255}:     "G",
	{0, 0, 255, 255}:     "B",
	{255, 255, 0, 255}:   "Y",
	{255, 165, 0, 255}:   "O",
	{128, 0, 128, 255}:   "P",
}
var PureLookup = func() map[string]color.RGBA {
	m := make(map[string]color.RGBA)
	for k, v := range PureColorTokens {
		m[v] = k
	}
	return m
}()

var dctCos = func() [8][8]float64 {
	var c [8][8]float64
	for u := 0; u < 8; u++ {
		for x := 0; x < 8; x++ {
			c[u][x] = math.Cos((float64(2*x+1) * float64(u) * math.Pi) / 16.0)
		}
	}
	return c
}()

var dctScale = func() [8]float64 {
	var s [8]float64
	for i := 0; i < 8; i++ {
		s[i] = 1.0
	}
	s[0] = 1.0 / math.Sqrt2
	return s
}()

var zigZagOrder = [64]int{
	0, 1, 8, 16, 9, 2, 3, 10,
	17, 24, 32, 25, 18, 11, 4, 5,
	12, 19, 26, 33, 40, 48, 41, 34,
	27, 20, 13, 6, 7, 14, 21, 28,
	35, 42, 49, 56, 57, 50, 43, 36,
	29, 22, 15, 23, 30, 37, 44, 51,
	58, 59, 52, 45, 38, 31, 39, 46,
	53, 60, 61, 54, 47, 55, 62, 63,
}

var jpegLumaQuant = [64]int{
	16, 11, 10, 16, 24, 40, 51, 61,
	12, 12, 14, 19, 26, 58, 60, 55,
	14, 13, 16, 24, 40, 57, 69, 56,
	14, 17, 22, 29, 51, 87, 80, 62,
	18, 22, 37, 56, 68, 109, 103, 77,
	24, 35, 55, 64, 81, 104, 113, 92,
	49, 64, 78, 87, 103, 121, 120, 101,
	72, 92, 95, 98, 112, 100, 103, 99,
}

var jpegChromaQuant = [64]int{
	17, 18, 24, 47, 99, 99, 99, 99,
	18, 21, 26, 66, 99, 99, 99, 99,
	24, 26, 56, 99, 99, 99, 99, 99,
	47, 66, 99, 99, 99, 99, 99, 99,
	99, 99, 99, 99, 99, 99, 99, 99,
	99, 99, 99, 99, 99, 99, 99, 99,
	99, 99, 99, 99, 99, 99, 99, 99,
	99, 99, 99, 99, 99, 99, 99, 99,
}

func scaleQuantTable(base [64]int, quality int) [64]int {
	if quality < 1 {
		quality = 1
	}
	if quality > 100 {
		quality = 100
	}
	var scale int
	if quality < 50 {
		scale = 5000 / quality
	} else {
		scale = 200 - 2*quality
	}
	var out [64]int
	for i := 0; i < 64; i++ {
		v := (base[i]*scale + 50) / 100
		if v < 1 {
			v = 1
		}
		if v > 255 {
			v = 255
		}
		out[i] = v
	}
	return out
}

func dct8x8(block [64]float64) [64]float64 {
	var out [64]float64
	for v := 0; v < 8; v++ {
		for u := 0; u < 8; u++ {
			sum := 0.0
			for y := 0; y < 8; y++ {
				for x := 0; x < 8; x++ {
					sum += block[y*8+x] * dctCos[u][x] * dctCos[v][y]
				}
			}
			out[v*8+u] = 0.25 * dctScale[u] * dctScale[v] * sum
		}
	}
	return out
}

func idct8x8(coeff [64]float64) [64]float64 {
	var out [64]float64
	for y := 0; y < 8; y++ {
		for x := 0; x < 8; x++ {
			sum := 0.0
			for v := 0; v < 8; v++ {
				for u := 0; u < 8; u++ {
					sum += dctScale[u] * dctScale[v] * coeff[v*8+u] * dctCos[u][x] * dctCos[v][y]
				}
			}
			out[y*8+x] = 0.25 * sum
		}
	}
	return out
}

func readSVarint(r *bufio.Reader) (int32, error) {
	u, err := binary.ReadUvarint(r)
	if err != nil {
		return 0, err
	}
	v := int32(u>>1) ^ -int32(u&1)
	return v, nil
}

type bitReader struct {
	data  []byte
	idx   int
	nbits uint8
	cur   byte
}

func newBitReader(data []byte) *bitReader {
	return &bitReader{data: data}
}

func (r *bitReader) ReadBit() (uint8, error) {
	if r.nbits == 0 {
		if r.idx >= len(r.data) {
			return 0, io.EOF
		}
		r.cur = r.data[r.idx]
		r.idx++
		r.nbits = 8
	}
	r.nbits--
	bit := (r.cur >> r.nbits) & 1
	return bit, nil
}

func (r *bitReader) ReadBits(n uint8) (uint64, error) {
	var v uint64
	for i := uint8(0); i < n; i++ {
		bit, err := r.ReadBit()
		if err != nil {
			return 0, err
		}
		v = (v << 1) | uint64(bit)
	}
	return v, nil
}

func readRiceSigned(r *bitReader, k uint8) (int, error) {
	var q uint32
	for {
		bit, err := r.ReadBit()
		if err != nil {
			return 0, err
		}
		if bit == 1 {
			break
		}
		q++
	}
	var rem uint64
	if k > 0 {
		v, err := r.ReadBits(k)
		if err != nil {
			return 0, err
		}
		rem = v
	}
	u := (q << k) | uint32(rem)
	s := int32(u>>1) ^ -int32(u&1)
	return int(s), nil
}

func readRiceUnsigned(r *bitReader, k uint8) (uint32, error) {
	var q uint32
	for {
		bit, err := r.ReadBit()
		if err != nil {
			return 0, err
		}
		if bit == 1 {
			break
		}
		q++
	}
	var rem uint64
	if k > 0 {
		v, err := r.ReadBits(k)
		if err != nil {
			return 0, err
		}
		rem = v
	}
	return (q << k) | uint32(rem), nil
}

type ycbcrPlanes struct {
	y      []float64
	cb     []float64
	cr     []float64
	a      []float64
	w, h   int
	cw, ch int
	mode   string
}

func planesToRGBA(p ycbcrPlanes) *image.RGBA {
	img := image.NewRGBA(image.Rect(0, 0, p.w, p.h))
	for yy := 0; yy < p.h; yy++ {
		for xx := 0; xx < p.w; xx++ {
			yv := p.y[yy*p.w+xx]
			av := p.a[yy*p.w+xx]
			cx, cy := xx, yy
			switch p.mode {
			case "422":
				cx = xx / 2
			case "420":
				cx = xx / 2
				cy = yy / 2
			}
			ci := cy*p.cw + cx
			cb := p.cb[ci]
			cr := p.cr[ci]
			if yv < 0 {
				yv = 0
			} else if yv > 255 {
				yv = 255
			}
			if cb < 0 {
				cb = 0
			} else if cb > 255 {
				cb = 255
			}
			if cr < 0 {
				cr = 0
			} else if cr > 255 {
				cr = 255
			}
			if av < 0 {
				av = 0
			} else if av > 255 {
				av = 255
			}
			r, g, b := color.YCbCrToRGB(uint8(yv+0.5), uint8(cb+0.5), uint8(cr+0.5))
			img.SetRGBA(xx, yy, color.RGBA{R: r, G: g, B: b, A: uint8(av + 0.5)})
		}
	}
	return img
}

func decodePlaneDCT(r *bufio.Reader, pw, ph int, qtable [64]int, center bool, clamp bool) ([]float64, error) {
	bw := (pw + 7) / 8
	bh := (ph + 7) / 8
	out := make([]float64, pw*ph)
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			var coeff [64]float64
			for i := 0; i < 64; i++ {
				v, err := readSVarint(r)
				if err != nil {
					return nil, err
				}
				idx := zigZagOrder[i]
				coeff[idx] = float64(v) * float64(qtable[idx])
			}
			block := idct8x8(coeff)
			for y := 0; y < 8; y++ {
				sy := by*8 + y
				if sy >= ph {
					continue
				}
				for x := 0; x < 8; x++ {
					sx := bx*8 + x
					if sx >= pw {
						continue
					}
					v := block[y*8+x]
					if center {
						v += 128.0
					}
					if clamp {
						if v < 0 {
							v = 0
						} else if v > 255 {
							v = 255
						}
					}
					out[sy*pw+sx] = v
				}
			}
		}
	}
	return out, nil
}

func decodePlaneDCTRiceEx(r *bitReader, pw, ph int, qtable [64]int, center bool, clamp bool, k uint8, predDC, zeroRun, blockSkip, acMag bool) ([]float64, error) {
	bw := (pw + 7) / 8
	bh := (ph + 7) / 8
	out := make([]float64, pw*ph)
	var dcVals []int
	if predDC {
		dcVals = make([]int, bw*bh)
	}
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			if blockSkip {
				bit, err := r.ReadBit()
				if err != nil {
					return nil, err
				}
				if bit == 1 {
					if predDC {
						dcVals[by*bw+bx] = 0
					}
					for y := 0; y < 8; y++ {
						sy := by*8 + y
						if sy >= ph {
							continue
						}
						for x := 0; x < 8; x++ {
							sx := bx*8 + x
							if sx >= pw {
								continue
							}
							v := 0.0
							if center {
								v += 128.0
							}
							if clamp {
								if v < 0 {
									v = 0
								} else if v > 255 {
									v = 255
								}
							}
							out[sy*pw+sx] = v
						}
					}
					continue
				}
			}
			var coeff [64]float64
			if predDC {
				pred := 0
				if bx > 0 && by > 0 {
					left := dcVals[by*bw+bx-1]
					up := dcVals[(by-1)*bw+bx]
					pred = (left + up) / 2
				} else if bx > 0 {
					pred = dcVals[by*bw+bx-1]
				} else if by > 0 {
					pred = dcVals[(by-1)*bw+bx]
				}
				diff, err := readRiceSigned(r, k)
				if err != nil {
					return nil, err
				}
				dc := pred + diff
				dcVals[by*bw+bx] = dc
				coeff[0] = float64(dc) * float64(qtable[0])
			} else {
				v, err := readRiceSigned(r, k)
				if err != nil {
					return nil, err
				}
				coeff[0] = float64(v) * float64(qtable[0])
			}
			if zeroRun {
				pos := 1
				for pos < 64 {
					remaining := 64 - pos
					runU, err := readRiceUnsigned(r, k)
					if err != nil {
						return nil, err
					}
					run := int(runU)
					if run > remaining {
						return nil, fmt.Errorf("zero-run overflow: %d > %d", run, remaining)
					}
					pos += run
					if run == remaining {
						break
					}
					var v int
					if acMag {
						sign, err := r.ReadBit()
						if err != nil {
							return nil, err
						}
						magU, err := readRiceUnsigned(r, k)
						if err != nil {
							return nil, err
						}
						v = int(magU)
						if sign == 1 {
							v = -v
						}
					} else {
						val, err := readRiceSigned(r, k)
						if err != nil {
							return nil, err
						}
						v = val
					}
					idx := zigZagOrder[pos]
					coeff[idx] = float64(v) * float64(qtable[idx])
					pos++
				}
			} else {
				for i := 1; i < 64; i++ {
					v, err := readRiceSigned(r, k)
					if err != nil {
						return nil, err
					}
					idx := zigZagOrder[i]
					coeff[idx] = float64(v) * float64(qtable[idx])
				}
			}
			block := idct8x8(coeff)
			for y := 0; y < 8; y++ {
				sy := by*8 + y
				if sy >= ph {
					continue
				}
				for x := 0; x < 8; x++ {
					sx := bx*8 + x
					if sx >= pw {
						continue
					}
					v := block[y*8+x]
					if center {
						v += 128.0
					}
					if clamp {
						if v < 0 {
							v = 0
						} else if v > 255 {
							v = 255
						}
					}
					out[sy*pw+sx] = v
				}
			}
		}
	}
	return out, nil
}

func decodePlaneDCTRice(r *bitReader, pw, ph int, qtable [64]int, center bool, clamp bool, k uint8) ([]float64, error) {
	return decodePlaneDCTRiceEx(r, pw, ph, qtable, center, clamp, k, false, false, false, false)
}

func decodePlaneDCTRicePred(r *bitReader, pw, ph int, qtable [64]int, center bool, clamp bool, k uint8) ([]float64, error) {
	return decodePlaneDCTRiceEx(r, pw, ph, qtable, center, clamp, k, true, false, false, false)
}

func addPlane(base, delta []float64) []float64 {
	out := make([]float64, len(base))
	for i := range base {
		v := base[i] + delta[i]
		if v < 0 {
			v = 0
		} else if v > 255 {
			v = 255
		}
		out[i] = v
	}
	return out
}

func filledPlane(n int, v float64) []float64 {
	out := make([]float64, n)
	for i := range out {
		out[i] = v
	}
	return out
}

func fillPredBlock(pred, ref []float64, frameW, frameH int, bx, by, bw, bh, dx, dy int) {
	if ref == nil {
		return
	}
	sx := bx + dx
	sy := by + dy
	if sx < 0 || sy < 0 || sx+bw > frameW || sy+bh > frameH {
		return
	}
	for y := 0; y < bh; y++ {
		for x := 0; x < bw; x++ {
			pred[(by+y)*frameW+(bx+x)] = ref[(sy+y)*frameW+(sx+x)]
		}
	}
}

func fillPredBlockBi(pred, refA, refB []float64, frameW, frameH int, bx, by, bw, bh, dxA, dyA, dxB, dyB int) {
	if refA == nil || refB == nil {
		return
	}
	sxA := bx + dxA
	syA := by + dyA
	sxB := bx + dxB
	syB := by + dyB
	if sxA < 0 || syA < 0 || sxB < 0 || syB < 0 || sxA+bw > frameW || syA+bh > frameH || sxB+bw > frameW || syB+bh > frameH {
		return
	}
	for y := 0; y < bh; y++ {
		for x := 0; x < bw; x++ {
			a := refA[(syA+y)*frameW+(sxA+x)]
			b := refB[(syB+y)*frameW+(sxB+x)]
			pred[(by+y)*frameW+(bx+x)] = (a + b) / 2
		}
	}
}

func fillPredBlockChroma(pred, ref []float64, cw, ch, subX, subY int, bx, by, bw, bh, dx, dy int) {
	if ref == nil {
		return
	}
	cbx := bx / subX
	cby := by / subY
	cbw := (bw + subX - 1) / subX
	cbh := (bh + subY - 1) / subY
	cdx := dx / subX
	cdy := dy / subY
	sx := cbx + cdx
	sy := cby + cdy
	if sx < 0 || sy < 0 || sx+cbw > cw || sy+cbh > ch {
		return
	}
	for y := 0; y < cbh; y++ {
		for x := 0; x < cbw; x++ {
			pred[(cby+y)*cw+(cbx+x)] = ref[(sy+y)*cw+(sx+x)]
		}
	}
}

func fillPredBlockChromaBi(pred, refA, refB []float64, cw, ch, subX, subY int, bx, by, bw, bh, dxA, dyA, dxB, dyB int) {
	if refA == nil || refB == nil {
		return
	}
	cbx := bx / subX
	cby := by / subY
	cbw := (bw + subX - 1) / subX
	cbh := (bh + subY - 1) / subY
	cdxA := dxA / subX
	cdyA := dyA / subY
	cdxB := dxB / subX
	cdyB := dyB / subY
	sxA := cbx + cdxA
	syA := cby + cdyA
	sxB := cbx + cdxB
	syB := cby + cdyB
	if sxA < 0 || syA < 0 || sxB < 0 || syB < 0 || sxA+cbw > cw || syA+cbh > ch || sxB+cbw > cw || syB+cbh > ch {
		return
	}
	for y := 0; y < cbh; y++ {
		for x := 0; x < cbw; x++ {
			a := refA[(syA+y)*cw+(sxA+x)]
			b := refB[(syB+y)*cw+(sxB+x)]
			pred[(cby+y)*cw+(cbx+x)] = (a + b) / 2
		}
	}
}

func isHexDigit(b byte) bool {
	return (b >= '0' && b <= '9') || (b >= 'A' && b <= 'F') || (b >= 'a' && b <= 'f')
}

func isAllHex(s string) bool {
	if len(s) == 0 {
		return false
	}
	for i := 0; i < len(s); i++ {
		if !isHexDigit(s[i]) {
			return false
		}
	}
	return true
}

type Vec3 struct {
	X, Y, Z float64
}

type Vec2 struct {
	U, V float64
}

type ElixFace struct {
	V [3]int
	T [3]int
	N [3]int
}

type ElixMesh struct {
	Verts   []Vec3
	UVs     []Vec2
	Normals []Vec3
	Faces   []ElixFace
	Edges   [][2]int
	Center  Vec3
	Radius  float64
}

type meshTri struct {
	i0    int
	i1    int
	i2    int
	depth float64
	shade float32
}

type elixRef struct {
	v int
	t int
	n int
}

func parseElixIndexMaybe(s string, indexBase int) (int, error) {
	if s == "" {
		return -1, nil
	}
	i, err := strconv.Atoi(s)
	if err != nil {
		return -1, err
	}
	i -= indexBase
	if i < 0 {
		return -1, fmt.Errorf("ELIX index underflow: %d", i+indexBase)
	}
	return i, nil
}

func parseElixRef(token string, indexBase int) (elixRef, error) {
	parts := strings.Split(token, "/")
	if len(parts) > 3 {
		return elixRef{}, fmt.Errorf("invalid ELIX face token: %s", token)
	}
	if parts[0] == "" {
		return elixRef{}, fmt.Errorf("missing ELIX vertex index in token: %s", token)
	}
	v, err := parseElixIndexMaybe(parts[0], indexBase)
	if err != nil {
		return elixRef{}, err
	}
	t := -1
	n := -1
	if len(parts) >= 2 {
		t, err = parseElixIndexMaybe(parts[1], indexBase)
		if err != nil {
			return elixRef{}, err
		}
	}
	if len(parts) == 3 {
		n, err = parseElixIndexMaybe(parts[2], indexBase)
		if err != nil {
			return elixRef{}, err
		}
	}
	return elixRef{v: v, t: t, n: n}, nil
}

func buildMeshEdges(mesh *ElixMesh) {
	edgeSet := make(map[[2]int]struct{})
	addEdge := func(a, b int) {
		if a < 0 || b < 0 || a == b {
			return
		}
		if a > b {
			a, b = b, a
		}
		edgeSet[[2]int{a, b}] = struct{}{}
	}
	for _, f := range mesh.Faces {
		addEdge(f.V[0], f.V[1])
		addEdge(f.V[1], f.V[2])
		addEdge(f.V[2], f.V[0])
	}
	mesh.Edges = make([][2]int, 0, len(edgeSet))
	for e := range edgeSet {
		mesh.Edges = append(mesh.Edges, e)
	}
}

func computeMeshBounds(mesh *ElixMesh) {
	if len(mesh.Verts) == 0 {
		return
	}
	min := mesh.Verts[0]
	max := mesh.Verts[0]
	for _, v := range mesh.Verts[1:] {
		if v.X < min.X {
			min.X = v.X
		}
		if v.Y < min.Y {
			min.Y = v.Y
		}
		if v.Z < min.Z {
			min.Z = v.Z
		}
		if v.X > max.X {
			max.X = v.X
		}
		if v.Y > max.Y {
			max.Y = v.Y
		}
		if v.Z > max.Z {
			max.Z = v.Z
		}
	}
	mesh.Center = Vec3{
		X: (min.X + max.X) / 2,
		Y: (min.Y + max.Y) / 2,
		Z: (min.Z + max.Z) / 2,
	}
	radius := 0.0
	for _, v := range mesh.Verts {
		dx := v.X - mesh.Center.X
		dy := v.Y - mesh.Center.Y
		dz := v.Z - mesh.Center.Z
		d := math.Sqrt(dx*dx + dy*dy + dz*dz)
		if d > radius {
			radius = d
		}
	}
	if radius == 0 {
		radius = 1
	}
	mesh.Radius = radius
}

func decodeElixToMesh(path string) (*ElixMesh, error) {
	in, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer in.Close()
	dc, err := zstd.NewReader(in)
	if err != nil {
		return nil, err
	}
	defer dc.Close()
	raw, err := io.ReadAll(dc)
	if err != nil {
		return nil, err
	}
	rawText := string(raw)
	rawLines := strings.Split(strings.ReplaceAll(rawText, "\r\n", "\n"), "\n")
	var wantVerts, wantUVs, wantNorms, wantFaces int
	var hasVerts, hasUVs, hasNorms, hasFaces bool
	indexBase := 0
	mesh := &ElixMesh{}
	for _, ln := range rawLines {
		line := strings.TrimSpace(ln)
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		if strings.HasPrefix(line, "ELIX") {
			continue
		}
		if strings.Contains(line, "=") && !strings.HasPrefix(line, "V ") && !strings.HasPrefix(line, "T ") && !strings.HasPrefix(line, "N ") && !strings.HasPrefix(line, "F ") {
			parts := strings.SplitN(line, "=", 2)
			if len(parts) != 2 {
				continue
			}
			key := strings.TrimSpace(parts[0])
			val := strings.TrimSpace(parts[1])
			switch key {
			case "VERTS":
				wantVerts, _ = strconv.Atoi(val)
				hasVerts = true
			case "UVS":
				wantUVs, _ = strconv.Atoi(val)
				hasUVs = true
			case "NORMS":
				wantNorms, _ = strconv.Atoi(val)
				hasNorms = true
			case "FACES":
				wantFaces, _ = strconv.Atoi(val)
				hasFaces = true
			case "INDEX_BASE":
				indexBase, _ = strconv.Atoi(val)
			}
			continue
		}
		fields := strings.Fields(line)
		if len(fields) == 0 {
			continue
		}
		switch fields[0] {
		case "V":
			if len(fields) < 4 {
				return nil, fmt.Errorf("ELIX V expects 3 floats: %q", line)
			}
			x, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return nil, err
			}
			y, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return nil, err
			}
			z, err := strconv.ParseFloat(fields[3], 64)
			if err != nil {
				return nil, err
			}
			mesh.Verts = append(mesh.Verts, Vec3{X: x, Y: y, Z: z})
		case "T":
			if len(fields) < 3 {
				return nil, fmt.Errorf("ELIX T expects 2 floats: %q", line)
			}
			u, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return nil, err
			}
			v, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return nil, err
			}
			mesh.UVs = append(mesh.UVs, Vec2{U: u, V: v})
		case "N":
			if len(fields) < 4 {
				return nil, fmt.Errorf("ELIX N expects 3 floats: %q", line)
			}
			x, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return nil, err
			}
			y, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return nil, err
			}
			z, err := strconv.ParseFloat(fields[3], 64)
			if err != nil {
				return nil, err
			}
			mesh.Normals = append(mesh.Normals, Vec3{X: x, Y: y, Z: z})
		case "F":
			if len(fields) < 4 {
				return nil, fmt.Errorf("ELIX F expects 3 vertices: %q", line)
			}
			refs := make([]elixRef, 0, len(fields)-1)
			for _, tok := range fields[1:] {
				ref, err := parseElixRef(tok, indexBase)
				if err != nil {
					return nil, err
				}
				refs = append(refs, ref)
			}
			for i := 1; i+1 < len(refs); i++ {
				face := ElixFace{
					V: [3]int{refs[0].v, refs[i].v, refs[i+1].v},
					T: [3]int{refs[0].t, refs[i].t, refs[i+1].t},
					N: [3]int{refs[0].n, refs[i].n, refs[i+1].n},
				}
				mesh.Faces = append(mesh.Faces, face)
			}
		}
	}
	if hasVerts && wantVerts != len(mesh.Verts) {
		return nil, fmt.Errorf("ELIX vertex count mismatch: got %d, expected %d", len(mesh.Verts), wantVerts)
	}
	if hasUVs && wantUVs != len(mesh.UVs) {
		return nil, fmt.Errorf("ELIX UV count mismatch: got %d, expected %d", len(mesh.UVs), wantUVs)
	}
	if hasNorms && wantNorms != len(mesh.Normals) {
		return nil, fmt.Errorf("ELIX normal count mismatch: got %d, expected %d", len(mesh.Normals), wantNorms)
	}
	if hasFaces && wantFaces != len(mesh.Faces) {
		return nil, fmt.Errorf("ELIX face count mismatch: got %d, expected %d", len(mesh.Faces), wantFaces)
	}
	if len(mesh.Verts) == 0 || len(mesh.Faces) == 0 {
		return nil, fmt.Errorf("ELIX mesh missing vertices or faces")
	}
	buildMeshEdges(mesh)
	computeMeshBounds(mesh)
	return mesh, nil
}

func tokenizeLine(s string) []string {
	var tokens []string
	i, n := 0, len(s)
	readRepeat := func(j int) (int, bool) {
		if j < n && s[j] == '*' {
			j++
			start := j
			for j < n && s[j] >= '0' && s[j] <= '9' {
				j++
			}
			if start == j {
				return j, false
			}
			return j, true
		}
		return j, false
	}
	for i < n {
		for i < n && (s[i] == ' ' || s[i] == '\t') {
			i++
		}
		if i >= n {
			break
		}
		if s[i] == '(' {
			depth, j := 0, i
			for j < n {
				if s[j] == '(' {
					depth++
				} else if s[j] == ')' {
					depth--
					if depth == 0 {
						j++
						break
					}
				}
				j++
			}
			k, _ := readRepeat(j)
			tokens = append(tokens, s[i:k])
			i = k
			continue
		}
		if strings.HasPrefix(s[i:], "BG") {
			j := i + 2
			j, _ = readRepeat(j)
			tokens = append(tokens, s[i:j])
			i = j
			continue
		}
		if strings.ContainsRune("SKWRGBYOP", rune(s[i])) {
			if !(isHexDigit(s[i]) && i+1 < n && isHexDigit(s[i+1])) {
				j := i + 1
				j, _ = readRepeat(j)
				tokens = append(tokens, s[i:j])
				i = j
				continue
			}
		}
		if s[i] == '#' {
			j := i + 1
			for j < n && !(s[j] == ' ' || s[j] == '\t') {
				j++
			}
			tokens = append(tokens, s[i:j])
			i = j
			continue
		}
		if isHexDigit(s[i]) {
			j := i
			for j < n && isHexDigit(s[j]) {
				j++
			}
			hasRepeat := false
			k := j
			if k < n && s[k] == '*' {
				k++
				start := k
				for k < n && s[k] >= '0' && s[k] <= '9' {
					k++
				}
				if start != k {
					hasRepeat = true
				} else {
					k = j
				}
			}
			seq := s[i:j]
			if len(seq)%8 != 0 {
				tokens = append(tokens, seq)
				i = j
				continue
			}
			for off := 0; off < len(seq); off += 8 {
				chunk := seq[off : off+8]
				if hasRepeat && off+8 == len(seq) {
					tokens = append(tokens, chunk+s[j:k])
				} else {
					tokens = append(tokens, chunk)
				}
			}
			i = k
			continue
		}
		j := i
		for j < n && !(s[j] == ' ' || s[j] == '\t') {
			j++
		}
		tokens = append(tokens, s[i:j])
		i = j
	}
	return tokens
}

func tokenizeLineWithMacros(s string, macroNames map[string]struct{}) []string {
	if len(macroNames) == 0 {
		return tokenizeLine(s)
	}
	var tokens []string
	i, n := 0, len(s)
	readRepeat := func(j int) (int, bool) {
		if j < n && s[j] == '*' {
			j++
			start := j
			for j < n && s[j] >= '0' && s[j] <= '9' {
				j++
			}
			if start == j {
				return j, false
			}
			return j, true
		}
		return j, false
	}
	for i < n {
		for i < n && (s[i] == ' ' || s[i] == '\t') {
			i++
		}
		if i >= n {
			break
		}
		if s[i] == '(' {
			depth, j := 0, i
			for j < n {
				if s[j] == '(' {
					depth++
				} else if s[j] == ')' {
					depth--
					if depth == 0 {
						j++
						break
					}
				}
				j++
			}
			k, _ := readRepeat(j)
			tokens = append(tokens, s[i:k])
			i = k
			continue
		}
		if strings.HasPrefix(s[i:], "BG") {
			j := i + 2
			j, _ = readRepeat(j)
			tokens = append(tokens, s[i:j])
			i = j
			continue
		}
		if strings.ContainsRune("SKWRGBYOP", rune(s[i])) {
			if !(isHexDigit(s[i]) && i+1 < n && isHexDigit(s[i+1])) {
				j := i + 1
				j, _ = readRepeat(j)
				tokens = append(tokens, s[i:j])
				i = j
				continue
			}
		}
		if s[i] == '#' {
			j := i + 1
			for j < n && !(s[j] == ' ' || s[j] == '\t') {
				j++
			}
			tokens = append(tokens, s[i:j])
			i = j
			continue
		}
		if isHexDigit(s[i]) {
			j := i
			for j < n && isHexDigit(s[j]) {
				j++
			}
			hasRepeat := false
			k := j
			if k < n && s[k] == '*' {
				k++
				start := k
				for k < n && s[k] >= '0' && s[k] <= '9' {
					k++
				}
				if start != k {
					hasRepeat = true
				} else {
					k = j
				}
			}
			seq := s[i:j]
			if len(seq)%8 != 0 {
				tokens = append(tokens, seq)
				i = j
				continue
			}
			for off := 0; off < len(seq); off += 8 {
				chunk := seq[off : off+8]
				if hasRepeat && off+8 == len(seq) {
					tokens = append(tokens, chunk+s[j:k])
				} else {
					tokens = append(tokens, chunk)
				}
			}
			i = k
			continue
		}
		if s[i] == 'M' {
			matched := ""
			if i+3 <= n {
				cand := s[i : i+3]
				if _, ok := macroNames[cand]; ok {
					matched = cand
					i += 3
				}
			}
			if matched == "" && i+2 <= n {
				cand := s[i : i+2]
				if _, ok := macroNames[cand]; ok {
					matched = cand
					i += 2
				}
			}
			if matched != "" {
				j := i
				j, _ = readRepeat(j)
				tokens = append(tokens, matched+s[i:j])
				i = j
				continue
			}
		}
		j := i
		for j < n && !(s[j] == ' ' || s[j] == '\t') {
			j++
		}
		tokens = append(tokens, s[i:j])
		i = j
	}
	return tokens
}

func tokenizeLineStrict(s string, macroNames map[string]struct{}) ([]string, error) {
	var tokens []string
	i, n := 0, len(s)
	readRepeat := func(j int) (int, bool) {
		if j < n && s[j] == '*' {
			j++
			start := j
			for j < n && s[j] >= '0' && s[j] <= '9' {
				j++
			}
			if start == j {
				return j, false
			}
			return j, true
		}
		return j, false
	}
	for i < n {
		for i < n && (s[i] == ' ' || s[i] == '\t') {
			i++
		}
		if i >= n {
			break
		}
		if s[i] == '(' {
			depth, j := 0, i
			for j < n {
				if s[j] == '(' {
					depth++
				} else if s[j] == ')' {
					depth--
					if depth == 0 {
						j++
						break
					}
				}
				j++
			}
			k, _ := readRepeat(j)
			tokens = append(tokens, s[i:k])
			i = k
			continue
		}
		if strings.HasPrefix(s[i:], "BG") {
			j := i + 2
			j, _ = readRepeat(j)
			tokens = append(tokens, s[i:j])
			i = j
			continue
		}
		if strings.ContainsRune("SKWRGBYOP", rune(s[i])) && !(isHexDigit(s[i]) && i+1 < n && isHexDigit(s[i+1])) {
			j := i + 1
			j, _ = readRepeat(j)
			tokens = append(tokens, s[i:j])
			i = j
			continue
		}
		if s[i] == '#' {
			j := i + 1
			for j < n && !(s[j] == ' ' || s[j] == '\t') {
				j++
			}
			tokens = append(tokens, s[i:j])
			i = j
			continue
		}
		if isHexDigit(s[i]) {
			j := i
			for j < n && isHexDigit(s[j]) {
				j++
			}
			hasRepeat := false
			k := j
			if k < n && s[k] == '*' {
				k++
				start := k
				for k < n && s[k] >= '0' && s[k] <= '9' {
					k++
				}
				if start != k {
					hasRepeat = true
				} else {
					k = j
				}
			}
			seq := s[i:j]
			if len(seq)%8 != 0 {
				left := i - 16
				if left < 0 {
					left = 0
				}
				right := j + 16
				if right > n {
					right = n
				}
				snippet := s[left:right]
				caret := strings.Repeat(" ", i-left) + "^"
				return nil, fmt.Errorf("hex run not multiple of 8 at col %d: %q\n%s\n%s", i+1, seq, snippet, caret)
			}
			for off := 0; off < len(seq); off += 8 {
				chunk := seq[off : off+8]
				if hasRepeat && off+8 == len(seq) {
					tokens = append(tokens, chunk+s[j:k])
				} else {
					tokens = append(tokens, chunk)
				}
			}
			i = k
			continue
		}
		if s[i] == 'M' && len(macroNames) > 0 {
			matched := ""
			if i+3 <= n {
				cand := s[i : i+3]
				if _, ok := macroNames[cand]; ok {
					matched = cand
					i += 3
				}
			}
			if matched == "" && i+2 <= n {
				cand := s[i : i+2]
				if _, ok := macroNames[cand]; ok {
					matched = cand
					i += 2
				}
			}
			if matched == "" {
				left := i - 16
				if left < 0 {
					left = 0
				}
				right := i + 16
				if right > n {
					right = n
				}
				snippet := s[left:right]
				caret := strings.Repeat(" ", i-left) + "^"
				return nil, fmt.Errorf("unknown macro at col %d\n%s\n%s", i+1, snippet, caret)
			}
			j := i
			j, _ = readRepeat(j)
			tokens = append(tokens, matched+s[i:j])
			i = j
			continue
		}
		j := i
		for j < n && !(s[j] == ' ' || s[j] == '\t') {
			j++
		}
		tokens = append(tokens, s[i:j])
		i = j
	}
	return tokens, nil
}

func tokenToRGBAe(tok string, bg *color.RGBA, prev *color.RGBA) (color.RGBA, error) {
	switch tok {
	case "S":
		if prev == nil {
			return color.RGBA{}, fmt.Errorf("'S' token before previous pixel")
		}
		return *prev, nil
	case "BG":
		if bg == nil {
			return color.RGBA{}, fmt.Errorf("'BG' token without BG header")
		}
		return *bg, nil
	}
	if px, ok := PureLookup[tok]; ok {
		return px, nil
	}
	if (len(tok) == 6 || len(tok) == 8) && isAllHex(tok) {
		return parseCompactHex(tok), nil
	}
	if strings.HasPrefix(tok, "#") {
		return parseCompactHex(tok), nil
	}
	parts := map[byte]int{}
	i := 0
	for i < len(tok) {
		ch := tok[i]
		if strings.ContainsRune("RGBA", rune(ch)) {
			i++
			start := i
			for i < len(tok) && tok[i] >= '0' && tok[i] <= '9' {
				i++
			}
			if start == i {
				return color.RGBA{}, fmt.Errorf("missing number after '%c' in token %q", ch, tok)
			}
			num, _ := strconv.Atoi(tok[start:i])
			parts[ch] = num
		} else {
			return color.RGBA{}, fmt.Errorf("unexpected char %q in token %q", tok[i], tok)
		}
	}
	r, g, b, a := parts['R'], parts['G'], parts['B'], 255
	if v, ok := parts['A']; ok {
		a = v
	}
	return color.RGBA{uint8(r), uint8(g), uint8(b), uint8(a)}, nil
}

func expandGroupToken(token string) []string {
	count := 1
	var inner string
	if strings.Contains(token, ")*") {
		pos := strings.LastIndex(token, ")*")
		inner = token[1:pos]
		cnt, _ := strconv.Atoi(token[pos+2:])
		count = cnt
	} else {
		r := strings.LastIndex(token, ")")
		inner = token[1:r]
		if tail := token[r+1:]; strings.HasPrefix(tail, "*") {
			cnt, _ := strconv.Atoi(tail[1:])
			count = cnt
		}
	}
	innerTokens := tokenizeLine(inner)
	expanded := expandTokens(innerTokens)
	out := make([]string, 0, len(expanded)*count)
	for i := 0; i < count; i++ {
		out = append(out, expanded...)
	}
	return out
}
func expandSimpleOrRepeatToken(token string) []string {
	if strings.Contains(token, "*") && !strings.HasPrefix(token, "(") {
		i := strings.LastIndexByte(token, '*')
		if i >= 0 && i+1 < len(token) {
			base := token[:i]
			cnt := token[i+1:]
			n, err := strconv.Atoi(cnt)
			if err == nil && n > 0 {
				out := make([]string, n)
				for k := 0; k < n; k++ {
					out[k] = base
				}
				return out
			}
		}
	}
	return []string{token}
}
func expandTokens(tokens []string) []string {
	out := []string{}
	for _, t := range tokens {
		if t == "" {
			continue
		}
		if strings.HasPrefix(t, "(") {
			out = append(out, expandGroupToken(t)...)
		} else {
			out = append(out, expandSimpleOrRepeatToken(t)...)
		}
	}
	return out
}

func parseCompactHex(tok string) color.RGBA {
	h := strings.TrimPrefix(tok, "#")
	if len(h) == 6 {
		h += "FF"
	}
	b, err := hex.DecodeString(h)
	if err != nil || len(b) != 4 {
		panic(fmt.Sprintf("invalid hex: %q", tok))
	}
	return color.RGBA{b[0], b[1], b[2], b[3]}
}
func tokenToRGBA(tok string, bg *color.RGBA, prev *color.RGBA) color.RGBA {
	switch tok {
	case "S":
		if prev == nil {
			panic("S before prev")
		}
		return *prev
	case "BG":
		if bg == nil {
			panic("BG w/out BG")
		}
		return *bg
	}
	if px, ok := PureLookup[tok]; ok {
		return px
	}
	if (len(tok) == 6 || len(tok) == 8) && isAllHex(tok) {
		return parseCompactHex(tok)
	}
	if strings.HasPrefix(tok, "#") {
		return parseCompactHex(tok)
	}
	parts := map[byte]int{}
	i := 0
	for i < len(tok) {
		ch := tok[i]
		if strings.ContainsRune("RGBA", rune(ch)) {
			i++
			start := i
			for i < len(tok) && tok[i] >= '0' && tok[i] <= '9' {
				i++
			}
			num, _ := strconv.Atoi(tok[start:i])
			parts[ch] = num
		} else {
			panic(fmt.Sprintf("unexpected char %q in token %q", tok[i], tok))
		}
	}
	r, g, b, a := parts['R'], parts['G'], parts['B'], 255
	if v, ok := parts['A']; ok {
		a = v
	}
	return color.RGBA{uint8(r), uint8(g), uint8(b), uint8(a)}
}

func decodeClixToImage(path string) (image.Image, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	dec, _ := zstd.NewReader(nil)
	defer dec.Close()
	raw, err := dec.DecodeAll(data, nil)
	if err != nil {
		return nil, err
	}
	txt := strings.ReplaceAll(string(raw), "\r\n", "\n")
	lines := strings.Split(txt, "\n")
	var width, height int
	var bg *color.RGBA
	var dataLines []string
	macros := make(map[string]color.RGBA)
	for _, raw := range lines {
		ln := strings.TrimSpace(raw)
		if ln == "" {
			continue
		}
		if strings.HasPrefix(ln, "CLIX") {
			continue
		}
		if strings.HasPrefix(ln, "RES=") {
			val := strings.TrimPrefix(ln, "RES=")
			parts := strings.SplitN(val, "x", 2)
			if len(parts) == 2 {
				fmt.Sscanf(parts[0], "%d", &width)
				fmt.Sscanf(parts[1], "%d", &height)
			}
			continue
		}
		if strings.HasPrefix(ln, "WIDTH=") {
			fmt.Sscanf(ln, "WIDTH=%d", &width)
			continue
		}
		if strings.HasPrefix(ln, "HEIGHT=") {
			fmt.Sscanf(ln, "HEIGHT=%d", &height)
			continue
		}
		if strings.HasPrefix(ln, "BG=") {
			tok := strings.TrimPrefix(ln, "BG=")
			tmp := tokenToRGBA(tok, nil, nil)
			bg = &tmp
			continue
		}
		if strings.Contains(ln, "M_S") && strings.Contains(ln, "M_E") {
			start := strings.Index(ln, "M_S")
			end := strings.LastIndex(ln, "M_E")
			if start >= 0 && end > start+3 {
				body := ln[start+3 : end]
				for len(body) >= 10 {
					name := body[:2]
					hex := body[2:10]
					if len(hex) != 8 || !isAllHex(hex) {
						break
					}
					px := parseCompactHex(hex)
					macros[name] = px
					body = body[10:]
				}
			}
			continue
		}
		if strings.Contains(ln, "=") {
			key := strings.SplitN(ln, "=", 2)[0]
			switch key {
			case "ORDER", "ENCODING", "MODE", "ROUND_STEP", "DELTA_SNAP_THRESHOLD", "PALETTE_SIZE", "PALETTE_DITHER", "BLOCK_SIZE", "BLOCK_VAR_THRESHOLD", "ZSTD_LEVEL", "HEX_ALPHA":
				continue
			}
		}
		dataLines = append(dataLines, ln)
	}
	macroNames := make(map[string]struct{}, len(macros))
	for name := range macros {
		macroNames[name] = struct{}{}
	}
	var tokens []string
	for idx, ln := range dataLines {
		if strings.TrimSpace(ln) != "" {
			ts, terr := tokenizeLineStrict(ln, macroNames)
			if terr != nil {
				return nil, fmt.Errorf("tokenization error on data line %d: %v", idx+1, terr)
			}
			tokens = append(tokens, ts...)
		}
	}
	expanded := expandTokens(tokens)
	pixels := make([]color.RGBA, 0, width*height)
	var prev *color.RGBA
	for ti, t := range expanded {
		if m, ok := macros[t]; ok {
			px := m
			pixels = append(pixels, px)
			prev = &px
			continue
		}
		px, e := tokenToRGBAe(t, bg, prev)
		if e != nil {
			start := ti - 5
			if start < 0 {
				start = 0
			}
			end := ti + 5
			if end > len(expanded) {
				end = len(expanded)
			}
			context := strings.Join(expanded[start:end], " ")
			return nil, fmt.Errorf("bad token at index %d: %q: %v\ncontext: %s", ti, t, e, context)
		}
		pixels = append(pixels, px)
		prev = &px
	}
	if len(pixels) != width*height {
		return nil, fmt.Errorf("pixel mismatch: got %d expected %d", len(pixels), width*height)
	}
	img := image.NewRGBA(image.Rect(0, 0, width, height))
	for i, px := range pixels {
		x := i % width
		y := i / width
		img.SetRGBA(x, y, px)
	}
	return img, nil
}

/* BLIX 2.0 binary token stream */

const (
	blxOpRepeat = 0x80
	blxOpSeq    = 0x81
	vlxOpBlock  = 0x82
	vlxOpMotion = 0x83
	blxOpPure0  = 0xF0
	blxOpBG     = 0xFA
	blxOpS      = 0xFB
	blxOpRGBA   = 0xFC
	vlxOpT      = 0xFD
)

const (
	vlxFrameKey   = 0x01
	vlxFrameDelta = 0x02
	vlxFrameB     = 0x03
	vlxFlagBG     = 0x01
)

const (
	vlxDefaultBlockDim = 8
)

const (
	vlxDctRiceK    = 3
	vlxDctResRiceK = 2
	vlxMvRiceK     = 2
)

var blxPureList = []color.RGBA{
	{0, 0, 0, 255}, {255, 255, 255, 255}, {255, 0, 0, 255}, {0, 255, 0, 255},
	{0, 0, 255, 255}, {255, 255, 0, 255}, {255, 165, 0, 255}, {128, 0, 128, 255},
}

type simpleSym struct {
	kind byte
	px   color.RGBA
}

type vlixHeader struct {
	width          int
	height         int
	fps            float64
	framesExpected int
	audioBytes     int
	motion         bool
	blockDim       int
	codec          string
	chromaMode     string
	dctQuality     int
	dctResQuality  int
	dctRiceK       int
	dctResRiceK    int
	mvRiceK        int
	dctPred        bool
	dctZeroRun     bool
	dctBlockSkip   bool
	dctAcMag       bool
	dctPlaneMask   bool
	alphaEnabled   bool
}

type vlixStream struct {
	hdr vlixHeader
	f   *os.File
	zr  *zstd.Decoder
	br  *bufio.Reader
}

type streamFrame struct {
	idx int
	img image.Image
}

type streamAudio struct {
	pcm        []byte
	sampleRate int
}

const (
	sKindLit  = 1
	sKindBG   = 2
	sKindS    = 3
	sKindPure = 4
	sKindT    = 5
)

func readSimpleSymFromOp(op byte, br *bufio.Reader) (simpleSym, error) {
	switch {
	case op >= blxOpPure0 && op <= blxOpPure0+7:
		return simpleSym{kind: sKindPure, px: blxPureList[int(op-blxOpPure0)]}, nil
	case op == blxOpBG:
		return simpleSym{kind: sKindBG}, nil
	case op == blxOpS:
		return simpleSym{kind: sKindS}, nil
	case op == blxOpRGBA:
		b := make([]byte, 4)
		if _, err := io.ReadFull(br, b); err != nil {
			return simpleSym{}, err
		}
		return simpleSym{kind: sKindLit, px: color.RGBA{b[0], b[1], b[2], b[3]}}, nil
	default:
		return simpleSym{}, fmt.Errorf("unknown opcode 0x%X", op)
	}
}
func readSimpleSym(br *bufio.Reader) (simpleSym, error) {
	op, err := br.ReadByte()
	if err != nil {
		return simpleSym{}, err
	}
	return readSimpleSymFromOp(op, br)
}
func emitSimpleSym(sym simpleSym, bg *color.RGBA, prev **color.RGBA, out *[]color.RGBA) error {
	switch sym.kind {
	case sKindPure, sKindLit:
		*out = append(*out, sym.px)
		tmp := sym.px
		*prev = &tmp
		return nil
	case sKindBG:
		if bg == nil {
			return fmt.Errorf("BG but no BG in header")
		}
		*out = append(*out, *bg)
		tmp := *bg
		*prev = &tmp
		return nil
	case sKindS:
		if *prev == nil {
			return fmt.Errorf("S before previous")
		}
		*out = append(*out, **prev)
		tmp := **prev
		*prev = &tmp
		return nil
	default:
		return fmt.Errorf("bad simple kind")
	}
}

func decodeBlixToImage(path string) (image.Image, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	zr, err := zstd.NewReader(f)
	if err != nil {
		return nil, err
	}
	defer zr.Close()
	br := bufio.NewReader(zr)
	readLine := func() (string, error) {
		s, e := br.ReadString('\n')
		if e != nil {
			return "", e
		}
		return strings.TrimRight(s, "\r\n"), nil
	}

	hdr, err := readLine()
	if err != nil {
		return nil, err
	}
	if !strings.HasPrefix(hdr, "BLIX") {
		return nil, fmt.Errorf("not a BLIX stream: %q", hdr)
	}
	version := "1.0"
	if flds := strings.Fields(hdr); len(flds) > 1 {
		version = flds[1]
	}

	wline, err := readLine()
	if err != nil {
		return nil, err
	}
	hline, err := readLine()
	if err != nil {
		return nil, err
	}

	var width, height int
	if strings.HasPrefix(wline, "WIDTH=") {
		width, _ = strconv.Atoi(strings.SplitN(wline, "=", 2)[1])
	}
	if strings.HasPrefix(hline, "HEIGHT=") {
		height, _ = strconv.Atoi(strings.SplitN(hline, "=", 2)[1])
	}
	if width <= 0 || height <= 0 {
		return nil, fmt.Errorf("invalid BLIX header (WIDTH/HEIGHT)")
	}

	var bg *color.RGBA
	for {
		line, e := readLine()
		if e != nil {
			return nil, e
		}
		if line == "" {
			break
		}
		if strings.HasPrefix(line, "BG=") {
			hex := strings.TrimPrefix(line, "BG=")
			px := parseCompactHex(hex)
			bg = &px
		}
	}

	if strings.HasPrefix(version, "2.") {
		pixels := make([]color.RGBA, 0, width*height)
		var prev *color.RGBA
		for len(pixels) < width*height {
			op, e := br.ReadByte()
			if e != nil {
				return nil, e
			}
			switch op {
			case blxOpRepeat:
				sub, e2 := readSimpleSym(br)
				if e2 != nil {
					return nil, e2
				}
				cnt, e3 := binary.ReadUvarint(br)
				if e3 != nil {
					return nil, e3
				}
				for i := uint64(0); i < cnt; i++ {
					if e := emitSimpleSym(sub, bg, &prev, &pixels); e != nil {
						return nil, e
					}
				}
			case blxOpSeq:
				L, e2 := binary.ReadUvarint(br)
				if e2 != nil {
					return nil, e2
				}
				N, e3 := binary.ReadUvarint(br)
				if e3 != nil {
					return nil, e3
				}
				steps := make([]simpleSym, L)
				for i := uint64(0); i < L; i++ {
					sym, e4 := readSimpleSym(br)
					if e4 != nil {
						return nil, e4
					}
					steps[i] = sym
				}
				for r := uint64(0); r < N; r++ {
					for i := 0; i < len(steps); i++ {
						if e := emitSimpleSym(steps[i], bg, &prev, &pixels); e != nil {
							return nil, e
						}
					}
				}
			default:
				sym, e2 := readSimpleSymFromOp(op, br)
				if e2 != nil {
					return nil, e2
				}
				if e := emitSimpleSym(sym, bg, &prev, &pixels); e != nil {
					return nil, e
				}
			}
		}
		if len(pixels) != width*height {
			return nil, fmt.Errorf("decoded %d pixels, expected %d", len(pixels), width*height)
		}
		img := image.NewRGBA(image.Rect(0, 0, width, height))
		for i, px := range pixels {
			x := i % width
			y := i / width
			img.SetRGBA(x, y, px)
		}
		return img, nil
	}

	total := width * height * 4
	buf := make([]byte, total)
	if _, err := io.ReadFull(br, buf); err != nil {
		return nil, err
	}
	img := image.NewRGBA(image.Rect(0, 0, width, height))
	copy(img.Pix, buf)
	return img, nil
}

func toStereoPCM(samples []int16, channels int) []byte {
	if channels <= 0 {
		return nil
	}
	frames := len(samples) / channels
	out := make([]byte, frames*4)
	for i := 0; i < frames; i++ {
		var l, r int16
		switch {
		case channels == 1:
			l = samples[i]
			r = l
		default:
			l = samples[i*channels]
			r = samples[i*channels+1]
		}
		off := i * 4
		binary.LittleEndian.PutUint16(out[off:], uint16(l))
		binary.LittleEndian.PutUint16(out[off+2:], uint16(r))
	}
	return out
}

func decodeALIXBinary(data []byte) ([]byte, int, int, error) {
	br := bufio.NewReader(bytes.NewReader(data))
	readLine := func() (string, error) {
		s, e := br.ReadString('\n')
		if e != nil {
			return "", e
		}
		return strings.TrimRight(s, "\r\n"), nil
	}
	h1, err := readLine()
	if err != nil {
		return nil, 0, 0, err
	}
	if !strings.HasPrefix(h1, "ALIX") && !strings.HasPrefix(h1, "VLA") {
		return nil, 0, 0, fmt.Errorf("not an ALIX stream: %q", h1)
	}
	var sampleRate, channels, samples int
	blockFrames := alixBlockFrames
	codec := ""
	for {
		line, e := readLine()
		if e != nil {
			return nil, 0, 0, e
		}
		if line == "" {
			break
		}
		if !strings.Contains(line, "=") {
			continue
		}
		parts := strings.SplitN(line, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key := strings.TrimSpace(parts[0])
		val := strings.TrimSpace(parts[1])
		switch key {
		case "SR":
			sampleRate, _ = strconv.Atoi(val)
		case "CH":
			channels, _ = strconv.Atoi(val)
		case "SAMPLES":
			samples, _ = strconv.Atoi(val)
		case "CODEC":
			codec = val
		case "BLOCK":
			if v, err := strconv.Atoi(val); err == nil && v > 0 {
				blockFrames = v
			}
		}
	}
	if sampleRate <= 0 || channels <= 0 || samples <= 0 {
		return nil, 0, 0, fmt.Errorf("invalid ALIX header")
	}
	payload, err := io.ReadAll(br)
	if err != nil {
		return nil, 0, 0, err
	}
	dec, err := zstd.NewReader(nil)
	if err != nil {
		return nil, 0, 0, err
	}
	raw, err := dec.DecodeAll(payload, nil)
	dec.Close()
	if err != nil {
		return nil, 0, 0, err
	}
	total := samples * channels
	prev := make([]int16, channels)
	outSamples := make([]int16, 0, total)
	r := bytes.NewReader(raw)
	switch {
	case codec == "" || codec == "DPCM16":
		for i := 0; i < samples; i++ {
			for ch := 0; ch < channels; ch++ {
				u, err := binary.ReadUvarint(r)
				if err != nil {
					return nil, 0, 0, err
				}
				delta := int32(u>>1) ^ -int32(u&1)
				sample := int32(prev[ch]) + delta
				if sample > 32767 {
					sample = 32767
				} else if sample < -32768 {
					sample = -32768
				}
				prev[ch] = int16(sample)
				outSamples = append(outSamples, prev[ch])
			}
		}
	case codec == "ALIX" || codec == "CLXA":
		framesLeft := samples
		for framesLeft > 0 {
			n := blockFrames
			if n > framesLeft {
				n = framesLeft
			}
			op, err := r.ReadByte()
			if err != nil {
				return nil, 0, 0, err
			}
			switch op {
			case alixOpSilence:
				for i := 0; i < n; i++ {
					for ch := 0; ch < channels; ch++ {
						outSamples = append(outSamples, 0)
					}
				}
				for ch := range prev {
					prev[ch] = 0
				}
			case alixOpPCM:
				for i := 0; i < n; i++ {
					for ch := 0; ch < channels; ch++ {
						var b [2]byte
						if _, err := io.ReadFull(r, b[:]); err != nil {
							return nil, 0, 0, err
						}
						sample := int16(binary.LittleEndian.Uint16(b[:]))
						prev[ch] = sample
						outSamples = append(outSamples, sample)
					}
				}
			case alixOpD8:
				for i := 0; i < n; i++ {
					for ch := 0; ch < channels; ch++ {
						b, err := r.ReadByte()
						if err != nil {
							return nil, 0, 0, err
						}
						delta := int16(int8(b))
						sample := int32(prev[ch]) + int32(delta)
						if sample > 32767 {
							sample = 32767
						} else if sample < -32768 {
							sample = -32768
						}
						prev[ch] = int16(sample)
						outSamples = append(outSamples, prev[ch])
					}
				}
			case alixOpD16:
				for i := 0; i < n; i++ {
					for ch := 0; ch < channels; ch++ {
						var b [2]byte
						if _, err := io.ReadFull(r, b[:]); err != nil {
							return nil, 0, 0, err
						}
						delta := int16(binary.LittleEndian.Uint16(b[:]))
						sample := int32(prev[ch]) + int32(delta)
						if sample > 32767 {
							sample = 32767
						} else if sample < -32768 {
							sample = -32768
						}
						prev[ch] = int16(sample)
						outSamples = append(outSamples, prev[ch])
					}
				}
			default:
				return nil, 0, 0, fmt.Errorf("unknown ALIX op 0x%X", op)
			}
			framesLeft -= n
		}
	default:
		return nil, 0, 0, fmt.Errorf("unsupported ALIX codec: %s", codec)
	}
	pcm := toStereoPCM(outSamples, channels)
	return pcm, sampleRate, 2, nil
}

func decodeALIXContainer(data []byte) ([]byte, error) {
	br := bufio.NewReader(bytes.NewReader(data))
	readLine := func() (string, error) {
		s, e := br.ReadString('\n')
		if e != nil {
			return "", e
		}
		return strings.TrimRight(s, "\r\n"), nil
	}
	h1, err := readLine()
	if err != nil {
		return nil, err
	}
	if !strings.HasPrefix(h1, "ALIX") && !strings.HasPrefix(h1, "CLXA") && !strings.HasPrefix(h1, "VLA") {
		return nil, fmt.Errorf("not an ALIX stream: %q", h1)
	}
	encoding := ""
	for {
		line, e := readLine()
		if e != nil {
			return nil, e
		}
		if line == "" {
			break
		}
		if !strings.Contains(line, "=") {
			continue
		}
		parts := strings.SplitN(line, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key := strings.TrimSpace(parts[0])
		val := strings.TrimSpace(parts[1])
		if strings.EqualFold(key, "ENCODING") {
			encoding = val
		}
	}
	payload, err := io.ReadAll(br)
	if err != nil {
		return nil, err
	}
	if !strings.EqualFold(encoding, "BASE64") {
		return data, nil
	}
	clean := make([]byte, 0, len(payload))
	for _, b := range payload {
		if b == '\n' || b == '\r' || b == ' ' || b == '\t' {
			continue
		}
		clean = append(clean, b)
	}
	out := make([]byte, base64.StdEncoding.DecodedLen(len(clean)))
	n, err := base64.StdEncoding.Decode(out, clean)
	if err != nil {
		return nil, err
	}
	return out[:n], nil
}

func readVlxSimpleSymFromOp(op byte, br *bufio.Reader) (simpleSym, error) {
	switch {
	case op >= blxOpPure0 && op <= blxOpPure0+7:
		return simpleSym{kind: sKindPure, px: blxPureList[int(op-blxOpPure0)]}, nil
	case op == blxOpBG:
		return simpleSym{kind: sKindBG}, nil
	case op == blxOpS:
		return simpleSym{kind: sKindS}, nil
	case op == vlxOpT:
		return simpleSym{kind: sKindT}, nil
	case op == blxOpRGBA:
		b := make([]byte, 4)
		if _, err := io.ReadFull(br, b); err != nil {
			return simpleSym{}, err
		}
		return simpleSym{kind: sKindLit, px: color.RGBA{b[0], b[1], b[2], b[3]}}, nil
	default:
		return simpleSym{}, fmt.Errorf("unknown opcode 0x%X", op)
	}
}

func readVlxSimpleSym(br *bufio.Reader) (simpleSym, error) {
	op, err := br.ReadByte()
	if err != nil {
		return simpleSym{}, err
	}
	return readVlxSimpleSymFromOp(op, br)
}

func emitVlxSym(sym simpleSym, bg *color.RGBA, prev **color.RGBA, prevFrame []color.RGBA, out *[]color.RGBA, allowTemporal bool) error {
	switch sym.kind {
	case sKindPure, sKindLit:
		*out = append(*out, sym.px)
		tmp := sym.px
		*prev = &tmp
		return nil
	case sKindBG:
		if bg == nil {
			return fmt.Errorf("BG but no BG in header")
		}
		*out = append(*out, *bg)
		tmp := *bg
		*prev = &tmp
		return nil
	case sKindS:
		if *prev == nil {
			return fmt.Errorf("S before previous")
		}
		*out = append(*out, **prev)
		tmp := **prev
		*prev = &tmp
		return nil
	case sKindT:
		if !allowTemporal {
			return fmt.Errorf("T token in keyframe")
		}
		if prevFrame == nil {
			return fmt.Errorf("T token but no previous frame")
		}
		idx := len(*out)
		if idx >= len(prevFrame) {
			return fmt.Errorf("T token out of range")
		}
		px := prevFrame[idx]
		*out = append(*out, px)
		tmp := px
		*prev = &tmp
		return nil
	default:
		return fmt.Errorf("bad simple kind")
	}
}

func emitVlxSymBlock(sym simpleSym, bg *color.RGBA, prev **color.RGBA, out *[]color.RGBA) error {
	switch sym.kind {
	case sKindPure, sKindLit:
		*out = append(*out, sym.px)
		tmp := sym.px
		*prev = &tmp
		return nil
	case sKindBG:
		if bg == nil {
			return fmt.Errorf("BG but no BG in header")
		}
		*out = append(*out, *bg)
		tmp := *bg
		*prev = &tmp
		return nil
	case sKindS:
		if *prev == nil {
			return fmt.Errorf("S before previous")
		}
		*out = append(*out, **prev)
		tmp := **prev
		*prev = &tmp
		return nil
	case sKindT:
		return fmt.Errorf("T token in block stream")
	default:
		return fmt.Errorf("bad simple kind")
	}
}

func readVlixHeader(br *bufio.Reader) (vlixHeader, error) {
	readLine := func() (string, error) {
		s, e := br.ReadString('\n')
		if e != nil {
			return "", e
		}
		return strings.TrimRight(s, "\r\n"), nil
	}
	hdrLine, err := readLine()
	if err != nil {
		return vlixHeader{}, err
	}
	if !strings.HasPrefix(hdrLine, "VLIX") {
		return vlixHeader{}, fmt.Errorf("not a VLIX stream: %q", hdrLine)
	}
	hdr := vlixHeader{
		blockDim:      vlxDefaultBlockDim,
		chromaMode:    "444",
		dctQuality:    75,
		dctResQuality: 70,
		dctRiceK:      vlxDctRiceK,
		dctResRiceK:   vlxDctResRiceK,
		mvRiceK:       vlxMvRiceK,
		dctPred:       false,
		dctZeroRun:    false,
		dctBlockSkip:  false,
		dctAcMag:      false,
		dctPlaneMask:  false,
		alphaEnabled:  true,
	}
	for {
		line, e := readLine()
		if e != nil {
			return vlixHeader{}, e
		}
		if line == "" {
			break
		}
		if !strings.Contains(line, "=") {
			continue
		}
		parts := strings.SplitN(line, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key := strings.TrimSpace(parts[0])
		val := strings.TrimSpace(parts[1])
		switch key {
		case "CODEC":
			hdr.codec = strings.ToUpper(val)
		case "CHROMA":
			hdr.chromaMode = strings.ToLower(val)
		case "DCT_QUALITY":
			if v, err := strconv.Atoi(val); err == nil {
				hdr.dctQuality = v
			}
		case "DCT_RES_QUALITY":
			if v, err := strconv.Atoi(val); err == nil {
				hdr.dctResQuality = v
			}
		case "DCT_RICE_K":
			if v, err := strconv.Atoi(val); err == nil {
				hdr.dctRiceK = v
			}
		case "DCT_DC_PRED":
			hdr.dctPred = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_ZERO_RUN":
			hdr.dctZeroRun = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_BLOCK_SKIP":
			hdr.dctBlockSkip = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_AC_MAG":
			hdr.dctAcMag = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_PLANE_MASK":
			hdr.dctPlaneMask = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "ALPHA":
			hdr.alphaEnabled = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_RES_RICE_K":
			if v, err := strconv.Atoi(val); err == nil {
				hdr.dctResRiceK = v
			}
		case "MV_RICE_K":
			if v, err := strconv.Atoi(val); err == nil {
				hdr.mvRiceK = v
			}
		case "WIDTH":
			hdr.width, _ = strconv.Atoi(val)
		case "HEIGHT":
			hdr.height, _ = strconv.Atoi(val)
		case "FPS":
			hdr.fps, _ = strconv.ParseFloat(val, 64)
		case "FRAMES":
			hdr.framesExpected, _ = strconv.Atoi(val)
		case "AUDIO_BYTES":
			hdr.audioBytes, _ = strconv.Atoi(val)
		case "MOTION":
			hdr.motion = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "BLOCK_DIM":
			if v, err := strconv.Atoi(val); err == nil && v > 0 {
				hdr.blockDim = v
			}
		}
	}
	if hdr.codec == "" {
		hdr.codec = "VLIX1"
	}
	return hdr, nil
}

func openVlixStream(path string) (*vlixStream, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	zr, err := zstd.NewReader(f)
	if err != nil {
		f.Close()
		return nil, err
	}
	br := bufio.NewReader(zr)
	hdr, err := readVlixHeader(br)
	if err != nil {
		zr.Close()
		f.Close()
		return nil, err
	}
	return &vlixStream{hdr: hdr, f: f, zr: zr, br: br}, nil
}

func (vs *vlixStream) Close() {
	if vs == nil {
		return
	}
	if vs.zr != nil {
		vs.zr.Close()
	}
	if vs.f != nil {
		vs.f.Close()
	}
}

func decodeVlix(path string) ([]image.Image, float64, []byte, error) {
	vs, err := openVlixStream(path)
	if err != nil {
		return nil, 0, nil, err
	}
	defer vs.Close()
	hdr := vs.hdr
	br := vs.br
	if hdr.width <= 0 || hdr.height <= 0 {
		return nil, 0, nil, fmt.Errorf("invalid VLIX header (WIDTH/HEIGHT)")
	}
	width, height := hdr.width, hdr.height
	if hdr.codec == "VLIX2" {
		if hdr.chromaMode != "444" && hdr.chromaMode != "422" && hdr.chromaMode != "420" {
			return nil, 0, nil, fmt.Errorf("invalid VLIX chroma mode: %s", hdr.chromaMode)
		}
		if hdr.dctQuality < 1 {
			hdr.dctQuality = 1
		} else if hdr.dctQuality > 100 {
			hdr.dctQuality = 100
		}
		if hdr.dctResQuality < 1 {
			hdr.dctResQuality = 1
		} else if hdr.dctResQuality > 100 {
			hdr.dctResQuality = 100
		}
		return decodeVlixV2(br, hdr.width, hdr.height, hdr.framesExpected, hdr.audioBytes, hdr.fps, hdr.chromaMode, hdr.dctQuality, hdr.dctResQuality, hdr.blockDim, hdr.alphaEnabled, hdr.dctPred, hdr.dctZeroRun, hdr.dctBlockSkip, hdr.dctAcMag, hdr.dctPlaneMask, hdr.dctRiceK, hdr.dctResRiceK, hdr.mvRiceK)
	}
	if hdr.codec != "VLIX1" {
		return nil, 0, nil, fmt.Errorf("unsupported VLIX codec: %s", hdr.codec)
	}
	if hdr.fps <= 0 {
		hdr.fps = 30
	}
	var frames []image.Image
	var prevFrame []color.RGBA
	for {
		if hdr.framesExpected > 0 && len(frames) >= hdr.framesExpected {
			break
		}
		frameType, e := br.ReadByte()
		if e == io.EOF {
			break
		}
		if e != nil {
			return nil, 0, nil, e
		}
		flags, e := br.ReadByte()
		if e != nil {
			return nil, 0, nil, e
		}
		var bg *color.RGBA
		if flags&vlxFlagBG != 0 {
			b := make([]byte, 4)
			if _, err := io.ReadFull(br, b); err != nil {
				return nil, 0, nil, err
			}
			tmp := color.RGBA{b[0], b[1], b[2], b[3]}
			bg = &tmp
		}
		allowTemporal := frameType == vlxFrameDelta
		if allowTemporal && prevFrame == nil {
			return nil, 0, nil, fmt.Errorf("delta frame with no previous frame")
		}
		var pixels []color.RGBA
		if hdr.motion {
			pixels = make([]color.RGBA, width*height)
			blockW := hdr.blockDim
			blockH := hdr.blockDim
			for by := 0; by < height; by += blockH {
				hh := blockH
				if by+hh > height {
					hh = height - by
				}
				for bx := 0; bx < width; bx += blockW {
					ww := blockW
					if bx+ww > width {
						ww = width - bx
					}
					op, e2 := br.ReadByte()
					if e2 != nil {
						return nil, 0, nil, e2
					}
					switch op {
					case vlxOpMotion:
						if prevFrame == nil {
							return nil, 0, nil, fmt.Errorf("motion block without previous frame")
						}
						bdx, err := br.ReadByte()
						if err != nil {
							return nil, 0, nil, err
						}
						bdy, err := br.ReadByte()
						if err != nil {
							return nil, 0, nil, err
						}
						dx := int(int8(bdx))
						dy := int(int8(bdy))
						for y := 0; y < hh; y++ {
							for x := 0; x < ww; x++ {
								sx := bx + x + dx
								sy := by + y + dy
								if sx < 0 || sy < 0 || sx >= width || sy >= height {
									return nil, 0, nil, fmt.Errorf("motion vector out of bounds")
								}
								pixels[(by+y)*width+(bx+x)] = prevFrame[sy*width+sx]
							}
						}
					case vlxOpBlock:
						blockPixels := make([]color.RGBA, 0, ww*hh)
						var prev *color.RGBA
						for len(blockPixels) < ww*hh {
							op2, e3 := br.ReadByte()
							if e3 != nil {
								return nil, 0, nil, e3
							}
							switch op2 {
							case blxOpRepeat:
								sub, e4 := readVlxSimpleSym(br)
								if e4 != nil {
									return nil, 0, nil, e4
								}
								cnt, e5 := binary.ReadUvarint(br)
								if e5 != nil {
									return nil, 0, nil, e5
								}
								for i := uint64(0); i < cnt; i++ {
									if e := emitVlxSymBlock(sub, bg, &prev, &blockPixels); e != nil {
										return nil, 0, nil, e
									}
								}
							case blxOpSeq:
								L, e4 := binary.ReadUvarint(br)
								if e4 != nil {
									return nil, 0, nil, e4
								}
								N, e5 := binary.ReadUvarint(br)
								if e5 != nil {
									return nil, 0, nil, e5
								}
								steps := make([]simpleSym, L)
								for i := uint64(0); i < L; i++ {
									sym, e6 := readVlxSimpleSym(br)
									if e6 != nil {
										return nil, 0, nil, e6
									}
									steps[i] = sym
								}
								for r := uint64(0); r < N; r++ {
									for i := 0; i < len(steps); i++ {
										if e := emitVlxSymBlock(steps[i], bg, &prev, &blockPixels); e != nil {
											return nil, 0, nil, e
										}
									}
								}
							default:
								sym, e4 := readVlxSimpleSymFromOp(op2, br)
								if e4 != nil {
									return nil, 0, nil, e4
								}
								if e := emitVlxSymBlock(sym, bg, &prev, &blockPixels); e != nil {
									return nil, 0, nil, e
								}
							}
						}
						if len(blockPixels) != ww*hh {
							return nil, 0, nil, fmt.Errorf("block pixel mismatch: got %d expected %d", len(blockPixels), ww*hh)
						}
						i := 0
						for y := 0; y < hh; y++ {
							for x := 0; x < ww; x++ {
								pixels[(by+y)*width+(bx+x)] = blockPixels[i]
								i++
							}
						}
					default:
						return nil, 0, nil, fmt.Errorf("unknown block opcode 0x%X", op)
					}
				}
			}
		} else {
			pixels = make([]color.RGBA, 0, width*height)
			var prev *color.RGBA
			for len(pixels) < width*height {
				op, e2 := br.ReadByte()
				if e2 != nil {
					return nil, 0, nil, e2
				}
				switch op {
				case blxOpRepeat:
					sub, e3 := readVlxSimpleSym(br)
					if e3 != nil {
						return nil, 0, nil, e3
					}
					cnt, e4 := binary.ReadUvarint(br)
					if e4 != nil {
						return nil, 0, nil, e4
					}
					for i := uint64(0); i < cnt; i++ {
						if e := emitVlxSym(sub, bg, &prev, prevFrame, &pixels, allowTemporal); e != nil {
							return nil, 0, nil, e
						}
					}
				case blxOpSeq:
					L, e3 := binary.ReadUvarint(br)
					if e3 != nil {
						return nil, 0, nil, e3
					}
					N, e4 := binary.ReadUvarint(br)
					if e4 != nil {
						return nil, 0, nil, e4
					}
					steps := make([]simpleSym, L)
					for i := uint64(0); i < L; i++ {
						sym, e5 := readVlxSimpleSym(br)
						if e5 != nil {
							return nil, 0, nil, e5
						}
						steps[i] = sym
					}
					for r := uint64(0); r < N; r++ {
						for i := 0; i < len(steps); i++ {
							if e := emitVlxSym(steps[i], bg, &prev, prevFrame, &pixels, allowTemporal); e != nil {
								return nil, 0, nil, e
							}
						}
					}
				default:
					sym, e3 := readVlxSimpleSymFromOp(op, br)
					if e3 != nil {
						return nil, 0, nil, e3
					}
					if e := emitVlxSym(sym, bg, &prev, prevFrame, &pixels, allowTemporal); e != nil {
						return nil, 0, nil, e
					}
				}
			}
			if len(pixels) != width*height {
				return nil, 0, nil, fmt.Errorf("decoded %d pixels, expected %d", len(pixels), width*height)
			}
		}
		img := image.NewRGBA(image.Rect(0, 0, width, height))
		for i, px := range pixels {
			x := i % width
			y := i / width
			img.SetRGBA(x, y, px)
		}
		frames = append(frames, img)
		prevFrame = pixels
	}
	if hdr.framesExpected > 0 && len(frames) != hdr.framesExpected {
		return nil, 0, nil, fmt.Errorf("decoded %d frames, expected %d", len(frames), hdr.framesExpected)
	}
	if len(frames) == 0 {
		return nil, 0, nil, fmt.Errorf("no frames decoded")
	}
	var audioBlob []byte
	if hdr.audioBytes > 0 {
		audioBlob = make([]byte, hdr.audioBytes)
		if _, err := io.ReadFull(br, audioBlob); err != nil {
			return nil, 0, nil, err
		}
	}
	return frames, hdr.fps, audioBlob, nil
}

func decodeVlixV2(br *bufio.Reader, width, height, framesExpected, audioBytes int, fps float64, chromaMode string, dctQuality, dctResQuality int, blockDim int, alphaEnabled, dctPred, dctZeroRun, dctBlockSkip, dctAcMag, dctPlaneMask bool, dctRiceK, dctResRiceK, mvRiceK int) ([]image.Image, float64, []byte, error) {
	qY := scaleQuantTable(jpegLumaQuant, dctQuality)
	qC := scaleQuantTable(jpegChromaQuant, dctQuality)
	qYRes := scaleQuantTable(jpegLumaQuant, dctResQuality)
	qCRes := scaleQuantTable(jpegChromaQuant, dctResQuality)
	decodePlane := func(r *bitReader, pw, ph int, qtable [64]int, center bool, clamp bool, k uint8) ([]float64, error) {
		return decodePlaneDCTRiceEx(r, pw, ph, qtable, center, clamp, k, dctPred, dctZeroRun, dctBlockSkip, dctAcMag)
	}

	if blockDim <= 0 {
		blockDim = vlxDefaultBlockDim
	}
	subX, subY := 1, 1
	switch chromaMode {
	case "422":
		subX = 2
	case "420":
		subX = 2
		subY = 2
	}

	refPlanes := make(map[int]ycbcrPlanes)
	frameMap := make(map[int]image.Image)
	decodedCount := 0
	maxIdx := -1
	for {
		if framesExpected > 0 && decodedCount >= framesExpected {
			break
		}
		frameType, e := br.ReadByte()
		if e == io.EOF {
			break
		}
		if e != nil {
			return nil, 0, nil, e
		}
		if frameType != vlxFrameKey && frameType != vlxFrameDelta && frameType != vlxFrameB {
			return nil, 0, nil, fmt.Errorf("unknown frame type 0x%X", frameType)
		}
		idxU, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, 0, nil, err
		}
		displayIdx := int(idxU)
		if displayIdx > maxIdx {
			maxIdx = displayIdx
		}

		if frameType == vlxFrameKey {
			coeffLen, err := binary.ReadUvarint(br)
			if err != nil {
				return nil, 0, nil, err
			}
			coeffBytes := make([]byte, coeffLen)
			if _, err := io.ReadFull(br, coeffBytes); err != nil {
				return nil, 0, nil, err
			}
			coeffReader := newBitReader(coeffBytes)
			mask := uint8(0x1 | 0x2 | 0x4 | 0x8)
			if dctPlaneMask {
				m, err := coeffReader.ReadBits(8)
				if err != nil {
					return nil, 0, nil, err
				}
				mask = uint8(m)
			}
			if mask&0x1 == 0 || mask&0x2 == 0 || mask&0x4 == 0 {
				return nil, 0, nil, fmt.Errorf("missing required planes in keyframe mask: 0x%X", mask)
			}
			yPlane, err := decodePlane(coeffReader, width, height, qY, true, true, uint8(dctRiceK))
			if err != nil {
				return nil, 0, nil, err
			}
			cw, ch := width, height
			switch chromaMode {
			case "422":
				cw = (width + 1) / 2
			case "420":
				cw = (width + 1) / 2
				ch = (height + 1) / 2
			}
			cbPlane, err := decodePlane(coeffReader, cw, ch, qC, true, true, uint8(dctRiceK))
			if err != nil {
				return nil, 0, nil, err
			}
			crPlane, err := decodePlane(coeffReader, cw, ch, qC, true, true, uint8(dctRiceK))
			if err != nil {
				return nil, 0, nil, err
			}
			var aPlane []float64
			if alphaEnabled && (mask&0x8 != 0) {
				ap, err := decodePlane(coeffReader, width, height, qY, true, true, uint8(dctRiceK))
				if err != nil {
					return nil, 0, nil, err
				}
				aPlane = ap
			} else {
				aPlane = filledPlane(width*height, 255)
			}
			planes := ycbcrPlanes{
				y:    yPlane,
				cb:   cbPlane,
				cr:   crPlane,
				a:    aPlane,
				w:    width,
				h:    height,
				cw:   cw,
				ch:   ch,
				mode: chromaMode,
			}
			img := planesToRGBA(planes)
			frameMap[displayIdx] = img
			refPlanes[displayIdx] = planes
			decodedCount++
			continue
		}

		refPrevU, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, 0, nil, err
		}
		refNextU, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, 0, nil, err
		}
		refPrevIdx := int(refPrevU)
		refNextIdx := int(refNextU)
		prevRef, ok := refPlanes[refPrevIdx]
		if !ok {
			return nil, 0, nil, fmt.Errorf("missing reference frame %d", refPrevIdx)
		}
		nextRef := prevRef
		if frameType == vlxFrameB {
			nr, ok := refPlanes[refNextIdx]
			if !ok {
				return nil, 0, nil, fmt.Errorf("missing reference frame %d", refNextIdx)
			}
			nextRef = nr
		}

		mvLen, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, 0, nil, err
		}
		mvBytes := make([]byte, mvLen)
		if mvLen > 0 {
			if _, err := io.ReadFull(br, mvBytes); err != nil {
				return nil, 0, nil, err
			}
		}
		coeffLen, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, 0, nil, err
		}
		coeffBytes := make([]byte, coeffLen)
		if coeffLen > 0 {
			if _, err := io.ReadFull(br, coeffBytes); err != nil {
				return nil, 0, nil, err
			}
		}

		predY := make([]float64, width*height)
		var predA []float64
		if alphaEnabled {
			predA = make([]float64, width*height)
		} else {
			predA = filledPlane(width*height, 255)
		}
		predCb := make([]float64, prevRef.cw*prevRef.ch)
		predCr := make([]float64, prevRef.cw*prevRef.ch)
		mvReader := newBitReader(mvBytes)
		bwBlocks := (width + blockDim - 1) / blockDim
		bhBlocks := (height + blockDim - 1) / blockDim
		for by := 0; by < bhBlocks; by++ {
			for bx := 0; bx < bwBlocks; bx++ {
				bxPix := bx * blockDim
				byPix := by * blockDim
				bwPix := blockDim
				bhPix := blockDim
				if bxPix+bwPix > width {
					bwPix = width - bxPix
				}
				if byPix+bhPix > height {
					bhPix = height - byPix
				}
				modeBits, err := mvReader.ReadBits(2)
				if err != nil {
					return nil, 0, nil, err
				}
				mode := uint8(modeBits)
				dx1, dy1, dx2, dy2 := 0, 0, 0, 0
				switch mode {
				case 1, 2:
					dx1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, 0, nil, err
					}
					dy1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, 0, nil, err
					}
				case 3:
					dx1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, 0, nil, err
					}
					dy1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, 0, nil, err
					}
					dx2, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, 0, nil, err
					}
					dy2, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, 0, nil, err
					}
				}
				switch mode {
				case 1:
					fillPredBlock(predY, prevRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					if alphaEnabled {
						fillPredBlock(predA, prevRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					}
					fillPredBlockChroma(predCb, prevRef.cb, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					fillPredBlockChroma(predCr, prevRef.cr, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
				case 2:
					fillPredBlock(predY, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					if alphaEnabled {
						fillPredBlock(predA, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					}
					fillPredBlockChroma(predCb, nextRef.cb, nextRef.cw, nextRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					fillPredBlockChroma(predCr, nextRef.cr, nextRef.cw, nextRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
				case 3:
					fillPredBlockBi(predY, prevRef.y, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					if alphaEnabled {
						fillPredBlockBi(predA, prevRef.a, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					}
					fillPredBlockChromaBi(predCb, prevRef.cb, nextRef.cb, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					fillPredBlockChromaBi(predCr, prevRef.cr, nextRef.cr, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
				}
			}
		}

		coeffReader := newBitReader(coeffBytes)
		mask := uint8(0x1 | 0x2 | 0x4 | 0x8)
		if dctPlaneMask {
			m, err := coeffReader.ReadBits(8)
			if err != nil {
				return nil, 0, nil, err
			}
			mask = uint8(m)
		}
		var yRes, cbRes, crRes, aRes []float64
		if !dctPlaneMask || mask&0x1 != 0 {
			yRes, err = decodePlane(coeffReader, width, height, qYRes, false, false, uint8(dctResRiceK))
			if err != nil {
				return nil, 0, nil, err
			}
		} else {
			yRes = filledPlane(width*height, 0)
		}
		if !dctPlaneMask || mask&0x2 != 0 {
			cbRes, err = decodePlane(coeffReader, prevRef.cw, prevRef.ch, qCRes, false, false, uint8(dctResRiceK))
			if err != nil {
				return nil, 0, nil, err
			}
		} else {
			cbRes = filledPlane(prevRef.cw*prevRef.ch, 0)
		}
		if !dctPlaneMask || mask&0x4 != 0 {
			crRes, err = decodePlane(coeffReader, prevRef.cw, prevRef.ch, qCRes, false, false, uint8(dctResRiceK))
			if err != nil {
				return nil, 0, nil, err
			}
		} else {
			crRes = filledPlane(prevRef.cw*prevRef.ch, 0)
		}
		if alphaEnabled {
			if !dctPlaneMask || mask&0x8 != 0 {
				aRes, err = decodePlane(coeffReader, width, height, qYRes, false, false, uint8(dctResRiceK))
				if err != nil {
					return nil, 0, nil, err
				}
			} else {
				aRes = filledPlane(width*height, 0)
			}
		} else {
			aRes = filledPlane(width*height, 0)
		}
		planes := ycbcrPlanes{
			y:    addPlane(predY, yRes),
			cb:   addPlane(predCb, cbRes),
			cr:   addPlane(predCr, crRes),
			a:    addPlane(predA, aRes),
			w:    width,
			h:    height,
			cw:   prevRef.cw,
			ch:   prevRef.ch,
			mode: chromaMode,
		}
		img := planesToRGBA(planes)
		frameMap[displayIdx] = img
		if frameType == vlxFrameDelta {
			refPlanes[displayIdx] = planes
		}
		decodedCount++
	}

	if decodedCount == 0 {
		return nil, 0, nil, fmt.Errorf("no frames decoded")
	}
	var frames []image.Image
	if framesExpected > 0 {
		if decodedCount != framesExpected {
			return nil, 0, nil, fmt.Errorf("decoded %d frames, expected %d", decodedCount, framesExpected)
		}
		frames = make([]image.Image, framesExpected)
		for i := 0; i < framesExpected; i++ {
			img, ok := frameMap[i]
			if !ok {
				return nil, 0, nil, fmt.Errorf("missing frame %d", i)
			}
			frames[i] = img
		}
	} else {
		if maxIdx < 0 {
			return nil, 0, nil, fmt.Errorf("no frames decoded")
		}
		frames = make([]image.Image, maxIdx+1)
		for i := 0; i <= maxIdx; i++ {
			img, ok := frameMap[i]
			if !ok {
				return nil, 0, nil, fmt.Errorf("missing frame %d", i)
			}
			frames[i] = img
		}
	}
	var audioBlob []byte
	if audioBytes > 0 {
		audioBlob = make([]byte, audioBytes)
		if _, err := io.ReadFull(br, audioBlob); err != nil {
			return nil, 0, nil, err
		}
	}
	if fps <= 0 {
		fps = 30
	}
	return frames, fps, audioBlob, nil
}

func decodeVlixV2Stream(br *bufio.Reader, width, height, framesExpected, audioBytes int, chromaMode string, dctQuality, dctResQuality int, blockDim int, alphaEnabled, dctPred, dctZeroRun, dctBlockSkip, dctAcMag, dctPlaneMask bool, dctRiceK, dctResRiceK, mvRiceK int, onFrame func(int, image.Image) error) ([]byte, error) {
	if onFrame == nil {
		return nil, fmt.Errorf("missing frame callback")
	}
	qY := scaleQuantTable(jpegLumaQuant, dctQuality)
	qC := scaleQuantTable(jpegChromaQuant, dctQuality)
	qYRes := scaleQuantTable(jpegLumaQuant, dctResQuality)
	qCRes := scaleQuantTable(jpegChromaQuant, dctResQuality)
	decodePlane := func(r *bitReader, pw, ph int, qtable [64]int, center bool, clamp bool, k uint8) ([]float64, error) {
		return decodePlaneDCTRiceEx(r, pw, ph, qtable, center, clamp, k, dctPred, dctZeroRun, dctBlockSkip, dctAcMag)
	}

	if blockDim <= 0 {
		blockDim = vlxDefaultBlockDim
	}
	subX, subY := 1, 1
	switch chromaMode {
	case "422":
		subX = 2
	case "420":
		subX = 2
		subY = 2
	}

	refPlanes := make(map[int]ycbcrPlanes)
	framesDecoded := 0
	for {
		if framesExpected > 0 && framesDecoded >= framesExpected {
			break
		}
		frameType, e := br.ReadByte()
		if e == io.EOF {
			break
		}
		if e != nil {
			return nil, e
		}
		if frameType != vlxFrameKey && frameType != vlxFrameDelta && frameType != vlxFrameB {
			return nil, fmt.Errorf("unknown frame type 0x%X", frameType)
		}
		idxU, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, err
		}
		displayIdx := int(idxU)

		if frameType == vlxFrameKey {
			coeffLen, err := binary.ReadUvarint(br)
			if err != nil {
				return nil, err
			}
			coeffBytes := make([]byte, coeffLen)
			if _, err := io.ReadFull(br, coeffBytes); err != nil {
				return nil, err
			}
			coeffReader := newBitReader(coeffBytes)
			mask := uint8(0x1 | 0x2 | 0x4 | 0x8)
			if dctPlaneMask {
				m, err := coeffReader.ReadBits(8)
				if err != nil {
					return nil, err
				}
				mask = uint8(m)
			}
			if mask&0x1 == 0 || mask&0x2 == 0 || mask&0x4 == 0 {
				return nil, fmt.Errorf("missing required planes in keyframe mask: 0x%X", mask)
			}
			yPlane, err := decodePlane(coeffReader, width, height, qY, true, true, uint8(dctRiceK))
			if err != nil {
				return nil, err
			}
			cw, ch := width, height
			switch chromaMode {
			case "422":
				cw = (width + 1) / 2
			case "420":
				cw = (width + 1) / 2
				ch = (height + 1) / 2
			}
			cbPlane, err := decodePlane(coeffReader, cw, ch, qC, true, true, uint8(dctRiceK))
			if err != nil {
				return nil, err
			}
			crPlane, err := decodePlane(coeffReader, cw, ch, qC, true, true, uint8(dctRiceK))
			if err != nil {
				return nil, err
			}
			var aPlane []float64
			if alphaEnabled && (mask&0x8 != 0) {
				ap, err := decodePlane(coeffReader, width, height, qY, true, true, uint8(dctRiceK))
				if err != nil {
					return nil, err
				}
				aPlane = ap
			} else {
				aPlane = filledPlane(width*height, 255)
			}
			planes := ycbcrPlanes{
				y:    yPlane,
				cb:   cbPlane,
				cr:   crPlane,
				a:    aPlane,
				w:    width,
				h:    height,
				cw:   cw,
				ch:   ch,
				mode: chromaMode,
			}
			img := planesToRGBA(planes)
			if err := onFrame(displayIdx, img); err != nil {
				return nil, err
			}
			refPlanes[displayIdx] = planes
			framesDecoded++
			continue
		}

		refPrevU, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, err
		}
		refNextU, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, err
		}
		refPrevIdx := int(refPrevU)
		refNextIdx := int(refNextU)
		prevRef, ok := refPlanes[refPrevIdx]
		if !ok {
			return nil, fmt.Errorf("missing reference frame %d", refPrevIdx)
		}
		nextRef := prevRef
		if frameType == vlxFrameB {
			nr, ok := refPlanes[refNextIdx]
			if !ok {
				return nil, fmt.Errorf("missing reference frame %d", refNextIdx)
			}
			nextRef = nr
		}

		mvLen, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, err
		}
		mvBytes := make([]byte, mvLen)
		if mvLen > 0 {
			if _, err := io.ReadFull(br, mvBytes); err != nil {
				return nil, err
			}
		}
		coeffLen, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, err
		}
		coeffBytes := make([]byte, coeffLen)
		if coeffLen > 0 {
			if _, err := io.ReadFull(br, coeffBytes); err != nil {
				return nil, err
			}
		}

		predY := make([]float64, width*height)
		var predA []float64
		if alphaEnabled {
			predA = make([]float64, width*height)
		} else {
			predA = filledPlane(width*height, 255)
		}
		predCb := make([]float64, prevRef.cw*prevRef.ch)
		predCr := make([]float64, prevRef.cw*prevRef.ch)
		mvReader := newBitReader(mvBytes)
		bwBlocks := (width + blockDim - 1) / blockDim
		bhBlocks := (height + blockDim - 1) / blockDim
		for by := 0; by < bhBlocks; by++ {
			for bx := 0; bx < bwBlocks; bx++ {
				bxPix := bx * blockDim
				byPix := by * blockDim
				bwPix := blockDim
				bhPix := blockDim
				if bxPix+bwPix > width {
					bwPix = width - bxPix
				}
				if byPix+bhPix > height {
					bhPix = height - byPix
				}
				modeBits, err := mvReader.ReadBits(2)
				if err != nil {
					return nil, err
				}
				mode := uint8(modeBits)
				dx1, dy1, dx2, dy2 := 0, 0, 0, 0
				switch mode {
				case 1, 2:
					dx1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, err
					}
					dy1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, err
					}
				case 3:
					dx1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, err
					}
					dy1, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, err
					}
					dx2, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, err
					}
					dy2, err = readRiceSigned(mvReader, uint8(mvRiceK))
					if err != nil {
						return nil, err
					}
				}
				switch mode {
				case 1:
					fillPredBlock(predY, prevRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					if alphaEnabled {
						fillPredBlock(predA, prevRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					}
					fillPredBlockChroma(predCb, prevRef.cb, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					fillPredBlockChroma(predCr, prevRef.cr, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
				case 2:
					fillPredBlock(predY, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					if alphaEnabled {
						fillPredBlock(predA, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					}
					fillPredBlockChroma(predCb, nextRef.cb, nextRef.cw, nextRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					fillPredBlockChroma(predCr, nextRef.cr, nextRef.cw, nextRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
				case 3:
					fillPredBlockBi(predY, prevRef.y, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					if alphaEnabled {
						fillPredBlockBi(predA, prevRef.a, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					}
					fillPredBlockChromaBi(predCb, prevRef.cb, nextRef.cb, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					fillPredBlockChromaBi(predCr, prevRef.cr, nextRef.cr, prevRef.cw, prevRef.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
				}
			}
		}

		coeffReader := newBitReader(coeffBytes)
		mask := uint8(0x1 | 0x2 | 0x4 | 0x8)
		if dctPlaneMask {
			m, err := coeffReader.ReadBits(8)
			if err != nil {
				return nil, err
			}
			mask = uint8(m)
		}
		var yRes, cbRes, crRes, aRes []float64
		if !dctPlaneMask || mask&0x1 != 0 {
			yRes, err = decodePlane(coeffReader, width, height, qYRes, false, false, uint8(dctResRiceK))
			if err != nil {
				return nil, err
			}
		} else {
			yRes = filledPlane(width*height, 0)
		}
		if !dctPlaneMask || mask&0x2 != 0 {
			cbRes, err = decodePlane(coeffReader, prevRef.cw, prevRef.ch, qCRes, false, false, uint8(dctResRiceK))
			if err != nil {
				return nil, err
			}
		} else {
			cbRes = filledPlane(prevRef.cw*prevRef.ch, 0)
		}
		if !dctPlaneMask || mask&0x4 != 0 {
			crRes, err = decodePlane(coeffReader, prevRef.cw, prevRef.ch, qCRes, false, false, uint8(dctResRiceK))
			if err != nil {
				return nil, err
			}
		} else {
			crRes = filledPlane(prevRef.cw*prevRef.ch, 0)
		}
		if alphaEnabled {
			if !dctPlaneMask || mask&0x8 != 0 {
				aRes, err = decodePlane(coeffReader, width, height, qYRes, false, false, uint8(dctResRiceK))
				if err != nil {
					return nil, err
				}
			} else {
				aRes = filledPlane(width*height, 0)
			}
		} else {
			aRes = filledPlane(width*height, 0)
		}
		planes := ycbcrPlanes{
			y:    addPlane(predY, yRes),
			cb:   addPlane(predCb, cbRes),
			cr:   addPlane(predCr, crRes),
			a:    addPlane(predA, aRes),
			w:    width,
			h:    height,
			cw:   prevRef.cw,
			ch:   prevRef.ch,
			mode: chromaMode,
		}
		img := planesToRGBA(planes)
		if err := onFrame(displayIdx, img); err != nil {
			return nil, err
		}
		if frameType == vlxFrameDelta {
			refPlanes[displayIdx] = planes
		}
		framesDecoded++
	}
	if framesExpected > 0 && framesDecoded != framesExpected {
		return nil, fmt.Errorf("decoded %d frames, expected %d", framesDecoded, framesExpected)
	}
	if audioBytes > 0 {
		buf := make([]byte, audioBytes)
		if _, err := io.ReadFull(br, buf); err != nil {
			return nil, err
		}
		return buf, nil
	}
	return nil, nil
}

type Game struct {
	frames          []*ebiten.Image
	fps             float64
	playing         bool
	frameIdx        int
	lastTick        time.Time
	accum           float64
	audioCtx        *audio.Context
	audioPlayer     *audio.Player
	audioDuration   time.Duration
	audioPCM        []byte
	audioSampleRate int
	visualizeAudio  bool
	waveformBuffer  *ebiten.Image
	scale           float64
	offsetX         float64
	offsetY         float64
	dragging        bool
	lastX           int
	lastY           int
	dragButton      ebiten.MouseButton
	showDebug       bool
	imgWidth        int
	imgHeight       int
	winWidth        int
	winHeight       int
	fitted          bool
	mesh            *ElixMesh
	meshMode        bool
	meshYaw         float64
	meshPitch       float64
	meshDistance    float64
	meshScale       float64
	meshPanX        float64
	meshPanY        float64
	meshFitted      bool
	meshProjected   [][2]float64
	meshVisible     []bool
	meshDepth       []float64
	meshVertices    []ebiten.Vertex
	meshIndices     []uint16
	meshTris        []meshTri
	streaming       bool
	streamDone      bool
	readyFrames     int
	totalFrames     int
	maxFrameIdx     int
	frameCh         <-chan streamFrame
	audioCh         <-chan streamAudio
	errCh           <-chan error
	streamAuto      bool
	streamStarted   bool
	navLastTick     time.Time
	navHoldLeft     float64
	navHoldRight    float64
	navNextLeft     float64
	navNextRight    float64
}

func (g *Game) pauseAudio() {
	if g.audioPlayer != nil {
		g.audioPlayer.Pause()
	}
}

func (g *Game) playAudio() {
	if g.audioPlayer != nil {
		g.audioPlayer.Play()
	}
}

func (g *Game) syncAudioToFrame() {
	if g.audioPlayer == nil {
		return
	}
	pos := time.Duration(float64(g.frameIdx) / g.fps * float64(time.Second))
	if pos < 0 {
		pos = 0
	}
	if g.audioDuration > 0 && pos > g.audioDuration {
		pos = g.audioDuration
	}
	_ = g.audioPlayer.SetPosition(pos)
}

func (g *Game) syncAudioToFrameLocked(maxDrift time.Duration) {
	if g.audioPlayer == nil {
		return
	}
	pos := time.Duration(float64(g.frameIdx) / g.fps * float64(time.Second))
	if pos < 0 {
		pos = 0
	}
	if g.audioDuration > 0 && pos > g.audioDuration {
		pos = g.audioDuration
	}
	cur := g.audioPlayer.Position()
	if cur < pos {
		if pos-cur > maxDrift {
			_ = g.audioPlayer.SetPosition(pos)
		}
	} else if cur-pos > maxDrift {
		_ = g.audioPlayer.SetPosition(pos)
	}
}

func (g *Game) stepFrame(delta int) {
	playable := g.playableFrames()
	if playable <= 0 {
		return
	}
	idx := g.frameIdx + delta
	if idx < 0 {
		idx = 0
	} else if idx >= playable {
		idx = playable - 1
	}
	if idx != g.frameIdx {
		g.frameIdx = idx
	}
	g.playing = false
	g.pauseAudio()
	g.syncAudioToFrame()
}

func (g *Game) seekAudio(delta time.Duration) {
	if g.audioPlayer == nil {
		return
	}
	pos := g.audioPlayer.Position() + delta
	if pos < 0 {
		pos = 0
	}
	if g.audioDuration > 0 && pos > g.audioDuration {
		pos = g.audioDuration
	}
	_ = g.audioPlayer.SetPosition(pos)
	if g.playing {
		g.playAudio()
	}
}

func (g *Game) playableFrames() int {
	if g.streaming {
		return g.readyFrames
	}
	return len(g.frames)
}

func (g *Game) totalFrameCount() int {
	if g.streaming && g.totalFrames > 0 {
		return g.totalFrames
	}
	return len(g.frames)
}

func (g *Game) addStreamFrame(idx int, img image.Image) {
	if idx < 0 {
		return
	}
	if g.totalFrames > 0 {
		if idx >= len(g.frames) {
			return
		}
	} else if idx >= len(g.frames) {
		newFrames := make([]*ebiten.Image, idx+1)
		copy(newFrames, g.frames)
		g.frames = newFrames
	}
	if idx > g.maxFrameIdx {
		g.maxFrameIdx = idx
	}
	if g.frames[idx] == nil {
		g.frames[idx] = ebiten.NewImageFromImage(img)
		for g.readyFrames < len(g.frames) && g.frames[g.readyFrames] != nil {
			g.readyFrames++
		}
		if g.totalFrames == 0 && g.readyFrames > 0 {
			g.totalFrames = g.readyFrames
		}
	}
}

func (g *Game) attachAudio(pcm []byte, sampleRate int) {
	if g.audioPlayer != nil || len(pcm) == 0 || sampleRate <= 0 {
		return
	}
	ctx := audio.NewContext(sampleRate)
	player, err := ctx.NewPlayer(bytes.NewReader(pcm))
	if err != nil {
		fmt.Fprintln(os.Stderr, "Audio init error:", err)
		return
	}
	g.audioCtx = ctx
	g.audioPlayer = player
	g.audioDuration = time.Duration(float64(len(pcm)) / float64(sampleRate*4) * float64(time.Second))
	if g.visualizeAudio {
		g.audioPCM = pcm
		g.audioSampleRate = sampleRate
		if g.waveformBuffer != nil {
			g.waveformBuffer.Fill(color.Black)
		}
	}
	if g.playing {
		g.syncAudioToFrame()
		g.playAudio()
	}
}

func (g *Game) pumpStream() error {
	for g.frameCh != nil {
		select {
		case fr, ok := <-g.frameCh:
			if !ok {
				g.frameCh = nil
				g.streamDone = true
				if g.totalFrames == 0 {
					g.totalFrames = g.readyFrames
				}
			} else {
				g.addStreamFrame(fr.idx, fr.img)
			}
		default:
			goto audioPump
		}
	}
audioPump:
	if g.audioCh != nil {
		select {
		case a, ok := <-g.audioCh:
			if !ok {
				g.audioCh = nil
			} else {
				g.attachAudio(a.pcm, a.sampleRate)
			}
		default:
		}
	}
	if g.errCh != nil {
		select {
		case err, ok := <-g.errCh:
			if ok && err != nil {
				return err
			}
		default:
		}
	}
	return nil
}

func (g *Game) Update() error {
	if g.meshMode {
		return g.updateMesh()
	}
	if g.streaming {
		if err := g.pumpStream(); err != nil {
			return err
		}
		if g.streamDone {
			g.streaming = false
		}
		if !g.streamDone {
			if g.playing {
				g.playing = false
				g.pauseAudio()
			}
		} else if !g.streamStarted {
			g.playing = true
			g.streamStarted = true
			g.lastTick = time.Now()
			g.accum = 0
			if g.audioPlayer != nil {
				g.syncAudioToFrame()
				g.playAudio()
			}
		}
	}
	if inpututil.IsKeyJustPressed(ebiten.KeyD) {
		g.showDebug = !g.showDebug
	}
	if inpututil.IsKeyJustPressed(ebiten.KeyR) {
		fitToWindow(g)
	}
	hasTimeline := g.totalFrameCount() > 1 || g.audioPlayer != nil
	if hasTimeline {
		if inpututil.IsKeyJustPressed(ebiten.KeySpace) {
			if g.playing {
				g.playing = false
				g.pauseAudio()
			} else {
				if g.streaming && !g.streamDone {
					g.playing = false
					g.pauseAudio()
					g.lastTick = time.Now()
					g.accum = 0
				} else {
					playable := g.playableFrames()
					if playable > 0 && g.frameIdx >= playable-1 {
						g.frameIdx = 0
					}
					if g.audioPlayer != nil && g.audioDuration > 0 && g.audioPlayer.Position() >= g.audioDuration {
						_ = g.audioPlayer.SetPosition(0)
					}
					if !(g.visualizeAudio && g.totalFrameCount() <= 1) {
						g.syncAudioToFrame()
					}
					g.playing = true
					g.playAudio()
					g.lastTick = time.Now()
					g.accum = 0
					if g.streaming {
						g.streamStarted = true
					}
				}
			}
		}
		if inpututil.IsKeyJustPressed(ebiten.KeyRight) {
			if g.visualizeAudio && g.audioPlayer != nil && g.totalFrameCount() <= 1 {
				g.seekAudio(1 * time.Second)
			} else {
				g.stepFrame(1)
			}
		}
		if inpututil.IsKeyJustPressed(ebiten.KeyLeft) {
			if g.visualizeAudio && g.audioPlayer != nil && g.totalFrameCount() <= 1 {
				g.seekAudio(-1 * time.Second)
			} else {
				g.stepFrame(-1)
			}
		}
		if inpututil.IsKeyJustPressed(ebiten.KeyHome) {
			g.frameIdx = 0
			g.playing = false
			g.pauseAudio()
			g.syncAudioToFrame()
		}
		if inpututil.IsKeyJustPressed(ebiten.KeyEnd) {
			playable := g.playableFrames()
			if playable > 0 {
				g.frameIdx = playable - 1
			}
			g.playing = false
			g.pauseAudio()
			g.syncAudioToFrame()
		}
		now := time.Now()
		if g.navLastTick.IsZero() {
			g.navLastTick = now
		}
		navDt := now.Sub(g.navLastTick).Seconds()
		g.navLastTick = now
		repeatDelay := 0.25
		repeatRate := 0.05
		if ebiten.IsKeyPressed(ebiten.KeyRight) {
			if g.navHoldRight == 0 {
				g.navHoldRight = navDt
				g.navNextRight = repeatDelay
			} else {
				g.navHoldRight += navDt
			}
			for g.navHoldRight >= g.navNextRight {
				if g.visualizeAudio && g.audioPlayer != nil && g.totalFrameCount() <= 1 {
					g.seekAudio(1 * time.Second)
				} else {
					g.stepFrame(1)
				}
				g.navNextRight += repeatRate
			}
		} else {
			g.navHoldRight = 0
			g.navNextRight = 0
		}
		if ebiten.IsKeyPressed(ebiten.KeyLeft) {
			if g.navHoldLeft == 0 {
				g.navHoldLeft = navDt
				g.navNextLeft = repeatDelay
			} else {
				g.navHoldLeft += navDt
			}
			for g.navHoldLeft >= g.navNextLeft {
				if g.visualizeAudio && g.audioPlayer != nil && g.totalFrameCount() <= 1 {
					g.seekAudio(-1 * time.Second)
				} else {
					g.stepFrame(-1)
				}
				g.navNextLeft += repeatRate
			}
		} else {
			g.navHoldLeft = 0
			g.navNextLeft = 0
		}
	}
	if g.playing {
		if g.audioPlayer != nil && (!g.streaming || g.streamDone) {
			if g.totalFrameCount() > 1 {
				pos := g.audioPlayer.Position().Seconds()
				idx := int(pos*g.fps + 1e-6)
				playable := g.playableFrames()
				if playable > 0 {
					if idx >= playable-1 {
						if g.streamDone || playable == g.totalFrameCount() {
							g.frameIdx = playable - 1
							g.playing = false
							g.pauseAudio()
							g.accum = 0
						} else {
							g.frameIdx = playable - 1
						}
					} else if idx >= 0 {
						g.frameIdx = idx
					}
				}
			} else if g.audioDuration > 0 && g.audioPlayer.Position() >= g.audioDuration {
				g.playing = false
				g.pauseAudio()
			}
		} else if g.playableFrames() > 1 {
			now := time.Now()
			if g.lastTick.IsZero() {
				g.lastTick = now
			}
			dt := now.Sub(g.lastTick).Seconds()
			g.lastTick = now
			g.accum += dt
			frameDur := 1.0 / g.fps
			for g.accum >= frameDur && g.playing {
				playable := g.playableFrames()
				if playable <= 0 {
					g.accum = 0
					break
				}
				if g.frameIdx >= playable-1 {
					if g.streamDone || playable == g.totalFrameCount() {
						g.frameIdx = playable - 1
						g.playing = false
						g.accum = 0
					} else {
						g.frameIdx = playable - 1
						g.accum = 0
					}
					break
				}
				g.frameIdx++
				g.accum -= frameDur
			}
		}
	} else {
		g.lastTick = time.Now()
	}
	if g.streaming && g.playing && g.audioPlayer != nil {
		g.syncAudioToFrameLocked(25 * time.Millisecond)
	}
	mx, my := ebiten.CursorPosition()
	_, dy := ebiten.Wheel()
	if dy != 0 {
		f := 1.1
		if dy < 0 {
			f = 1.0 / 1.1
		}
		cx, cy := float64(mx), float64(my)
		g.offsetX = cx - (cx-g.offsetX)*f
		g.offsetY = cy - (cy-g.offsetY)*f
		g.scale *= f
		if g.scale < 0.1 {
			g.scale = 0.1
		}
	}
	if ebiten.IsMouseButtonPressed(ebiten.MouseButtonLeft) {
		x, y := ebiten.CursorPosition()
		if !g.dragging {
			g.dragging = true
			g.lastX, g.lastY = x, y
		} else {
			dx := float64(x - g.lastX)
			dy := float64(y - g.lastY)
			g.offsetX += dx
			g.offsetY += dy
			g.lastX, g.lastY = x, y
		}
	} else {
		g.dragging = false
	}
	return nil
}

func (g *Game) updateMesh() error {
	if g.mesh == nil {
		return nil
	}
	if inpututil.IsKeyJustPressed(ebiten.KeyD) {
		g.showDebug = !g.showDebug
	}
	if inpututil.IsKeyJustPressed(ebiten.KeyR) {
		fitMeshToWindow(g)
	}
	_, dy := ebiten.Wheel()
	if dy != 0 {
		factor := math.Pow(1.1, -dy)
		g.meshDistance *= factor
		minDist := g.mesh.Radius * 0.2
		if g.meshDistance < minDist {
			g.meshDistance = minDist
		}
	}
	if ebiten.IsMouseButtonPressed(ebiten.MouseButtonLeft) {
		x, y := ebiten.CursorPosition()
		if !g.dragging || g.dragButton != ebiten.MouseButtonLeft {
			g.dragging = true
			g.dragButton = ebiten.MouseButtonLeft
			g.lastX, g.lastY = x, y
		} else {
			dx := float64(x - g.lastX)
			dy := float64(y - g.lastY)
			g.meshYaw -= dx * 0.01
			g.meshPitch -= dy * 0.01
			if g.meshPitch > math.Pi/2 {
				g.meshPitch = math.Pi / 2
			}
			if g.meshPitch < -math.Pi/2 {
				g.meshPitch = -math.Pi / 2
			}
			g.lastX, g.lastY = x, y
		}
	} else if ebiten.IsMouseButtonPressed(ebiten.MouseButtonRight) {
		x, y := ebiten.CursorPosition()
		if !g.dragging || g.dragButton != ebiten.MouseButtonRight {
			g.dragging = true
			g.dragButton = ebiten.MouseButtonRight
			g.lastX, g.lastY = x, y
		} else {
			dx := float64(x - g.lastX)
			dy := float64(y - g.lastY)
			g.meshPanX += dx
			g.meshPanY += dy
			g.lastX, g.lastY = x, y
		}
	} else {
		g.dragging = false
	}
	return nil
}

func (g *Game) drawWaveform(screen *ebiten.Image) {
	w := screen.Bounds().Dx()
	h := screen.Bounds().Dy()
	if w <= 0 || h <= 0 {
		return
	}
	if g.waveformBuffer == nil || g.waveformBuffer.Bounds().Dx() != w || g.waveformBuffer.Bounds().Dy() != h {
		g.waveformBuffer = ebiten.NewImage(w, h)
		g.waveformBuffer.Fill(color.Black)
	}
	fade := color.RGBA{0, 0, 0, uint8(255 * 0.2)}
	vector.DrawFilledRect(g.waveformBuffer, 0, 0, float32(w), float32(h), fade, false)
	if g.audioSampleRate <= 0 || len(g.audioPCM) < 4 {
		screen.DrawImage(g.waveformBuffer, nil)
		return
	}
	totalFrames := len(g.audioPCM) / 4
	if totalFrames <= 0 {
		screen.DrawImage(g.waveformBuffer, nil)
		return
	}
	curFrame := 0
	if g.audioPlayer != nil {
		curFrame = int(g.audioPlayer.Position().Seconds() * float64(g.audioSampleRate))
	}
	if curFrame < 0 {
		curFrame = 0
	}
	if curFrame > totalFrames {
		curFrame = totalFrames
	}
	start := curFrame - waveformPoints/2
	if waveformPoints <= 0 {
		screen.DrawImage(g.waveformBuffer, nil)
		return
	}
	sliceWidth := float32(w) / float32(waveformPoints)
	x := float32(0)
	var prevX, prevY float32
	for i := 0; i < waveformPoints; i++ {
		sampleIdx := start + i
		var sample int16
		if sampleIdx >= 0 && sampleIdx < totalFrames {
			off := sampleIdx * 4
			l := int16(binary.LittleEndian.Uint16(g.audioPCM[off : off+2]))
			r := int16(binary.LittleEndian.Uint16(g.audioPCM[off+2 : off+4]))
			sample = int16((int32(l) + int32(r)) / 2)
		} else {
			sample = 0
		}
		v := float32(sample) / 32768.0
		y := (v + 1) * float32(h) / 2
		if i > 0 {
			vector.StrokeLine(g.waveformBuffer, prevX, prevY, x, y, float32(waveformLineWidth), color.RGBA{255, 0, 0, 255}, true)
		}
		prevX, prevY = x, y
		x += sliceWidth
	}
	screen.DrawImage(g.waveformBuffer, nil)
}

func (g *Game) Draw(screen *ebiten.Image) {
	if g.meshMode {
		drawMesh(screen, g)
		return
	}
	screen.Fill(color.Black)
	if g.visualizeAudio {
		g.drawWaveform(screen)
	} else {
		op := &ebiten.DrawImageOptions{}
		op.GeoM.Scale(g.scale, g.scale)
		op.GeoM.Translate(g.offsetX, g.offsetY)
		if len(g.frames) > 0 && g.frameIdx >= 0 && g.frameIdx < len(g.frames) {
			if g.frames[g.frameIdx] != nil {
				screen.DrawImage(g.frames[g.frameIdx], op)
			}
		}
	}
	if g.showDebug {
		msg := fmt.Sprintf("Scale: %.2f  Offset: (%.1f, %.1f)", g.scale, g.offsetX, g.offsetY)
		if g.totalFrameCount() > 1 || g.audioPlayer != nil {
			state := "PAUSE"
			if g.playing {
				state = "PLAY"
			}
			msg = fmt.Sprintf("%s  Frame: %d/%d  FPS: %.2f  %s", msg, g.frameIdx+1, g.totalFrameCount(), g.fps, state)
			if g.audioPlayer != nil {
				msg = fmt.Sprintf("%s  AUDIO", msg)
			}
		}
		ebitenutil.DebugPrint(screen, msg)
	}
	if !g.showDebug && g.streaming && !g.streamDone {
		if g.totalFrames > 0 {
			ebitenutil.DebugPrint(screen, fmt.Sprintf("Video decoding... %d/%d", g.readyFrames, g.totalFrames))
		} else {
			ebitenutil.DebugPrint(screen, fmt.Sprintf("Video decoding... %d/?", g.readyFrames))
		}
	}
}

func drawMesh(screen *ebiten.Image, g *Game) {
	screen.Fill(color.Black)
	if g.mesh == nil {
		return
	}
	vertCount := len(g.mesh.Verts)
	if cap(g.meshProjected) < vertCount {
		g.meshProjected = make([][2]float64, vertCount)
	} else {
		g.meshProjected = g.meshProjected[:vertCount]
	}
	if cap(g.meshVisible) < vertCount {
		g.meshVisible = make([]bool, vertCount)
	} else {
		g.meshVisible = g.meshVisible[:vertCount]
	}
	if cap(g.meshDepth) < vertCount {
		g.meshDepth = make([]float64, vertCount)
	} else {
		g.meshDepth = g.meshDepth[:vertCount]
	}
	for i, v := range g.mesh.Verts {
		x, y, z, ok := projectMeshVertex(g, v)
		g.meshProjected[i] = [2]float64{x, y}
		g.meshVisible[i] = ok
		g.meshDepth[i] = z
	}
	lightDir := vecNormalize(Vec3{X: -0.3, Y: 0.6, Z: 0.7})
	ambient := 0.25
	if cap(g.meshTris) < len(g.mesh.Faces) {
		g.meshTris = make([]meshTri, 0, len(g.mesh.Faces))
	} else {
		g.meshTris = g.meshTris[:0]
	}
	buildTris := func(cull bool) {
		g.meshTris = g.meshTris[:0]
		for _, f := range g.mesh.Faces {
			i0, i1, i2 := f.V[0], f.V[1], f.V[2]
			if i0 < 0 || i1 < 0 || i2 < 0 || i0 >= vertCount || i1 >= vertCount || i2 >= vertCount {
				continue
			}
			if !g.meshVisible[i0] || !g.meshVisible[i1] || !g.meshVisible[i2] {
				continue
			}
			v0 := g.mesh.Verts[i0]
			v1 := g.mesh.Verts[i1]
			v2 := g.mesh.Verts[i2]
			n := vecCross(vecSub(v1, v0), vecSub(v2, v0))
			n = rotateYawPitch(n, g.meshYaw, g.meshPitch)
			if cull && n.Z >= 0 {
				continue
			}
			n = vecNormalize(n)
			diff := vecDot(n, lightDir)
			if diff < 0 {
				if cull {
					diff = 0
				} else {
					diff = -diff
				}
			}
			shade := float32(ambient + diff*0.75)
			if shade > 1 {
				shade = 1
			}
			depth := (g.meshDepth[i0] + g.meshDepth[i1] + g.meshDepth[i2]) / 3
			g.meshTris = append(g.meshTris, meshTri{i0: i0, i1: i1, i2: i2, depth: depth, shade: shade})
		}
	}
	buildTris(true)
	if len(g.meshTris) == 0 {
		buildTris(false)
	}
	sort.Slice(g.meshTris, func(i, j int) bool {
		return g.meshTris[i].depth > g.meshTris[j].depth
	})
	verts := g.meshVertices[:0]
	inds := g.meshIndices[:0]
	op := &ebiten.DrawTrianglesOptions{AntiAlias: false}
	flush := func() {
		if len(inds) == 0 {
			return
		}
		screen.DrawTriangles(verts, inds, meshWhiteImage, op)
		verts = verts[:0]
		inds = inds[:0]
	}
	drawnTris := 0
	for _, tri := range g.meshTris {
		if len(verts)+3 > maxMeshVerticesPerBatch {
			flush()
		}
		a := g.meshProjected[tri.i0]
		b := g.meshProjected[tri.i1]
		c := g.meshProjected[tri.i2]
		base := uint16(len(verts))
		sh := tri.shade
		verts = append(verts,
			ebiten.Vertex{DstX: float32(a[0]), DstY: float32(a[1]), SrcX: 0, SrcY: 0, ColorR: sh, ColorG: sh, ColorB: sh, ColorA: 1},
			ebiten.Vertex{DstX: float32(b[0]), DstY: float32(b[1]), SrcX: 0, SrcY: 0, ColorR: sh, ColorG: sh, ColorB: sh, ColorA: 1},
			ebiten.Vertex{DstX: float32(c[0]), DstY: float32(c[1]), SrcX: 0, SrcY: 0, ColorR: sh, ColorG: sh, ColorB: sh, ColorA: 1},
		)
		inds = append(inds, base, base+1, base+2)
		drawnTris++
	}
	flush()
	g.meshVertices = verts
	g.meshIndices = inds
	if g.showDebug {
		msg := fmt.Sprintf("Verts: %d  Faces: %d  Tris: %d  Yaw: %.2f  Pitch: %.2f  Dist: %.2f", len(g.mesh.Verts), len(g.mesh.Faces), drawnTris, g.meshYaw, g.meshPitch, g.meshDistance)
		msg = msg + "  Controls: L-drag rotate, R-drag pan, wheel zoom, R reset"
		ebitenutil.DebugPrint(screen, msg)
	}
}

func projectMeshVertex(g *Game, v Vec3) (float64, float64, float64, bool) {
	if g.mesh == nil {
		return 0, 0, 0, false
	}
	x := v.X - g.mesh.Center.X
	y := v.Y - g.mesh.Center.Y
	z := v.Z - g.mesh.Center.Z
	cy, sy := math.Cos(g.meshYaw), math.Sin(g.meshYaw)
	cp, sp := math.Cos(g.meshPitch), math.Sin(g.meshPitch)
	x1 := x*cy + z*sy
	z1 := -x*sy + z*cy
	y2 := y*cp - z1*sp
	z2 := y*sp + z1*cp
	z2 += g.meshDistance
	if z2 <= 0.01 {
		return 0, 0, z2, false
	}
	sx := x1 / z2 * g.meshScale
	sy2 := y2 / z2 * g.meshScale
	cx := float64(g.winWidth)/2 + g.meshPanX
	cy2 := float64(g.winHeight)/2 + g.meshPanY
	return cx + sx, cy2 - sy2, z2, true
}

func rotateYawPitch(v Vec3, yaw, pitch float64) Vec3 {
	cy, sy := math.Cos(yaw), math.Sin(yaw)
	cp, sp := math.Cos(pitch), math.Sin(pitch)
	x1 := v.X*cy + v.Z*sy
	z1 := -v.X*sy + v.Z*cy
	y2 := v.Y*cp - z1*sp
	z2 := v.Y*sp + z1*cp
	return Vec3{X: x1, Y: y2, Z: z2}
}

func vecSub(a, b Vec3) Vec3 {
	return Vec3{X: a.X - b.X, Y: a.Y - b.Y, Z: a.Z - b.Z}
}

func vecCross(a, b Vec3) Vec3 {
	return Vec3{
		X: a.Y*b.Z - a.Z*b.Y,
		Y: a.Z*b.X - a.X*b.Z,
		Z: a.X*b.Y - a.Y*b.X,
	}
}

func vecDot(a, b Vec3) float64 {
	return a.X*b.X + a.Y*b.Y + a.Z*b.Z
}

func vecLen(a Vec3) float64 {
	return math.Sqrt(a.X*a.X + a.Y*a.Y + a.Z*a.Z)
}

func vecNormalize(a Vec3) Vec3 {
	l := vecLen(a)
	if l <= 1e-9 {
		return Vec3{}
	}
	return Vec3{X: a.X / l, Y: a.Y / l, Z: a.Z / l}
}
func (g *Game) Layout(w, h int) (int, int) {
	g.winWidth, g.winHeight = w, h
	if g.meshMode {
		if !g.meshFitted && w > 0 && h > 0 {
			fitMeshToWindow(g)
			g.meshFitted = true
		}
		return w, h
	}
	if !g.fitted && w > 0 && h > 0 {
		fitToWindow(g)
		g.fitted = true
	}
	return w, h
}
func fitToWindow(g *Game) {
	sx := float64(g.winWidth) / float64(g.imgWidth)
	sy := float64(g.winHeight) / float64(g.imgHeight)
	g.scale = sx
	if sy < sx {
		g.scale = sy
	}
	g.offsetX = float64(g.winWidth)/2 - float64(g.imgWidth)*g.scale/2
	g.offsetY = float64(g.winHeight)/2 - float64(g.imgHeight)*g.scale/2
}

func fitMeshToWindow(g *Game) {
	if g.mesh == nil {
		return
	}
	minDim := float64(g.winWidth)
	if g.winHeight < g.winWidth {
		minDim = float64(g.winHeight)
	}
	if minDim <= 0 {
		minDim = 1
	}
	g.meshScale = minDim * 0.6
	g.meshDistance = g.mesh.Radius * 3
	g.meshYaw = 0.6
	g.meshPitch = -0.4
	g.meshPanX = 0
	g.meshPanY = 0
}

func runMeshViewer(mesh *ElixMesh) {
	printMeshHotkeys()
	game := &Game{
		mesh:         mesh,
		meshMode:     true,
		meshDistance: mesh.Radius * 3,
		meshScale:    300,
		meshYaw:      0.6,
		meshPitch:    -0.4,
	}
	ebiten.SetWindowSize(900, 700)
	ebiten.SetWindowResizingMode(ebiten.WindowResizingModeEnabled)
	ebiten.SetWindowTitle("Vcblix Viewer 2.9")
	if err := ebiten.RunGame(game); err != nil {
		panic(err)
	}
}

func printViewerHotkeys() {
	fmt.Println("Viewer hotkeys:")
	fmt.Println("  Space: Play/Pause")
	fmt.Println("  Left/Right: Step frame")
	fmt.Println("  Home/End: Jump to start/end")
	fmt.Println("  R: Reset fit to window")
	fmt.Println("  Mouse wheel: Zoom")
	fmt.Println("  Left drag: Pan")
	fmt.Println("")
}

func printMeshHotkeys() {
	fmt.Println("Mesh viewer hotkeys:")
	fmt.Println("  R: Reset view")
	fmt.Println("  Mouse wheel: Zoom")
	fmt.Println("  Left drag: Rotate")
	fmt.Println("  Right drag: Pan")
	fmt.Println("")
}

func main() {
	if len(os.Args) < 2 || len(os.Args) > 3 {
		fmt.Println("Usage: clix view <file.clix|file.blix|file.vlix|file.alix|file.elix> [file.alix]")
		os.Exit(1)
	}
	args := os.Args[1:]
	var vlixPath, audioPath, imagePath, meshPath string
	if len(args) == 2 {
		for _, p := range args {
			ext := strings.ToLower(filepath.Ext(p))
			switch ext {
			case ".vlix":
				vlixPath = p
			case ".vla", ".alix", ".clxa":
				audioPath = p
			default:
				fmt.Fprintln(os.Stderr, "Error: when passing two files, expected one .vlix and one .alix")
				os.Exit(2)
			}
		}
		if vlixPath == "" || audioPath == "" {
			fmt.Fprintln(os.Stderr, "Error: when passing two files, expected one .vlix and one audio file")
			os.Exit(2)
		}
	} else {
		ext := strings.ToLower(filepath.Ext(args[0]))
		switch ext {
		case ".vlix":
			vlixPath = args[0]
		case ".vla", ".alix", ".clxa":
			audioPath = args[0]
		case ".blix", ".clix":
			imagePath = args[0]
		case ".elix":
			meshPath = args[0]
		default:
			fmt.Fprintln(os.Stderr, "Error: unsupported file type")
			os.Exit(2)
		}
	}
	audioOnly := audioPath != "" && vlixPath == "" && imagePath == "" && meshPath == ""
	var frames []image.Image
	var fps float64
	var audioBlob []byte
	var mesh *ElixMesh
	var err error
	var streaming bool
	var streamHdr *vlixHeader
	var frameCh <-chan streamFrame
	var audioCh <-chan streamAudio
	var errCh <-chan error
	if vlixPath != "" {
		vs, err := openVlixStream(vlixPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
		if vs.hdr.codec == "VLIX2" {
			streaming = true
			hdr := vs.hdr
			if hdr.width <= 0 || hdr.height <= 0 {
				vs.Close()
				fmt.Fprintln(os.Stderr, "Error: invalid VLIX header (WIDTH/HEIGHT)")
				os.Exit(2)
			}
			if hdr.fps <= 0 {
				hdr.fps = 30
			}
			if hdr.chromaMode != "444" && hdr.chromaMode != "422" && hdr.chromaMode != "420" {
				vs.Close()
				fmt.Fprintf(os.Stderr, "Error: invalid VLIX chroma mode: %s\n", hdr.chromaMode)
				os.Exit(2)
			}
			if hdr.dctQuality < 1 {
				hdr.dctQuality = 1
			} else if hdr.dctQuality > 100 {
				hdr.dctQuality = 100
			}
			if hdr.dctResQuality < 1 {
				hdr.dctResQuality = 1
			} else if hdr.dctResQuality > 100 {
				hdr.dctResQuality = 100
			}
			streamHdr = &hdr
			frameChan := make(chan streamFrame, 8)
			audioChan := make(chan streamAudio, 1)
			errChan := make(chan error, 1)
			frameCh = frameChan
			audioCh = audioChan
			errCh = errChan
			go func() {
				defer close(frameChan)
				defer close(audioChan)
				defer close(errChan)
				defer vs.Close()
				audioBytes, err := decodeVlixV2Stream(vs.br, hdr.width, hdr.height, hdr.framesExpected, hdr.audioBytes, hdr.chromaMode, hdr.dctQuality, hdr.dctResQuality, hdr.blockDim, hdr.alphaEnabled, hdr.dctPred, hdr.dctZeroRun, hdr.dctBlockSkip, hdr.dctAcMag, hdr.dctPlaneMask, hdr.dctRiceK, hdr.dctResRiceK, hdr.mvRiceK, func(idx int, img image.Image) error {
					frameChan <- streamFrame{idx: idx, img: img}
					return nil
				})
				if err != nil {
					errChan <- err
					return
				}
				if len(audioBytes) > 0 && audioPath == "" {
					decoded, err := decodeALIXContainer(audioBytes)
					if err != nil {
						errChan <- err
						return
					}
					pcm, sampleRate, _, err := decodeALIXBinary(decoded)
					if err != nil {
						errChan <- err
						return
					}
					audioChan <- streamAudio{pcm: pcm, sampleRate: sampleRate}
				}
			}()
		} else {
			vs.Close()
			frames, fps, audioBlob, err = decodeVlix(vlixPath)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(2)
			}
		}
	}
	if imagePath != "" {
		if strings.HasSuffix(strings.ToLower(imagePath), ".blix") {
			var img image.Image
			img, err = decodeBlixToImage(imagePath)
			if err == nil {
				frames = []image.Image{img}
			}
		} else {
			var img image.Image
			img, err = decodeClixToImage(imagePath)
			if err == nil {
				frames = []image.Image{img}
			}
		}
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
	}
	if meshPath != "" {
		mesh, err = decodeElixToMesh(meshPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
		runMeshViewer(mesh)
		return
	}
	if audioPath != "" {
		audioBlob, err = os.ReadFile(audioPath)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
		decoded, err := decodeALIXContainer(audioBlob)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
		audioBlob = decoded
	}
	var audioPlayer *audio.Player
	var audioDuration time.Duration
	var audioCtx *audio.Context
	var audioPCM []byte
	var audioSampleRate int
	if len(audioBlob) > 0 {
		pcm, sampleRate, _, err := decodeALIXBinary(audioBlob)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
		audioPCM = pcm
		audioSampleRate = sampleRate
		audioCtx = audio.NewContext(sampleRate)
		player, err := audioCtx.NewPlayer(bytes.NewReader(pcm))
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
		audioPlayer = player
		audioDuration = time.Duration(float64(len(pcm)) / float64(sampleRate*4) * float64(time.Second))
	}
	if len(frames) == 0 {
		if audioPlayer == nil && !streaming {
			fmt.Fprintln(os.Stderr, "Error: no frames decoded")
			os.Exit(2)
		}
		if !streaming {
			frames = []image.Image{image.NewRGBA(image.Rect(0, 0, 1, 1))}
			fps = 1
		}
	}
	if fps <= 0 {
		fps = 30
	}
	var game *Game
	if streaming && streamHdr != nil {
		totalFrames := streamHdr.framesExpected
		ebFrames := make([]*ebiten.Image, totalFrames)
		autoplay := totalFrames > 1 || audioPlayer != nil
		game = &Game{
			frames:          ebFrames,
			fps:             streamHdr.fps,
			playing:         false,
			audioCtx:        audioCtx,
			audioPlayer:     audioPlayer,
			audioDuration:   audioDuration,
			audioPCM:        audioPCM,
			audioSampleRate: audioSampleRate,
			visualizeAudio:  audioOnly,
			imgWidth:        streamHdr.width,
			imgHeight:       streamHdr.height,
			streaming:       true,
			totalFrames:     totalFrames,
			frameCh:         frameCh,
			audioCh:         audioCh,
			errCh:           errCh,
			streamAuto:      autoplay,
		}
	} else {
		b := frames[0].Bounds()
		ebFrames := make([]*ebiten.Image, 0, len(frames))
		for _, f := range frames {
			ebFrames = append(ebFrames, ebiten.NewImageFromImage(f))
		}
		autoplay := len(ebFrames) > 1 || audioPlayer != nil
		game = &Game{
			frames:          ebFrames,
			fps:             fps,
			playing:         autoplay,
			audioCtx:        audioCtx,
			audioPlayer:     audioPlayer,
			audioDuration:   audioDuration,
			audioPCM:        audioPCM,
			audioSampleRate: audioSampleRate,
			visualizeAudio:  audioOnly,
			imgWidth:        b.Dx(),
			imgHeight:       b.Dy(),
		}
	}
	if game != nil && game.playing && game.audioPlayer != nil && (!game.streaming || game.streamDone) {
		game.audioPlayer.Play()
	}
	if meshPath == "" {
		printViewerHotkeys()
	}
	ebiten.SetWindowSize(800, 600)
	ebiten.SetWindowResizingMode(ebiten.WindowResizingModeEnabled)
	ebiten.SetWindowTitle("VABEC Viewer 2.10")
	if err := ebiten.RunGame(game); err != nil {
		panic(err)
	}
}
