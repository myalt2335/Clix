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
	"runtime"
	"strconv"
	"strings"
	"sync"
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
	waveformPoints    = 1024
	waveformLineWidth = 2
)

const (
	streamCacheBackMinFrames = 8
	streamCacheBackMaxFrames = 120
	streamMaxAheadMinFrames  = 12
	streamMaxAheadMaxFrames = 1800
	streamMaxAheadSeconds   = 5.0
	streamPrebufferSeconds  = 0.30
	streamPausedAheadMaxCap = 2400
)

const (
	viewerVersion      = "2.15"
	viewerVantaVersion = "2.A025.01.260612.K9ENUS@c1x14"
	clixVersion        = "2.12"
	blixVersion        = "2.0"
	trixVersion        = "0.2"
	vlixVersion        = "2.5"
	alixVersion        = "1.3"
)

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
	var tmp [64]float64
	for v := 0; v < 8; v++ {
		for x := 0; x < 8; x++ {
			sum := 0.0
			for u := 0; u < 8; u++ {
				sum += dctScale[u] * coeff[v*8+u] * dctCos[u][x]
			}
			tmp[v*8+x] = sum
		}
	}
	for y := 0; y < 8; y++ {
		for x := 0; x < 8; x++ {
			sum := 0.0
			for v := 0; v < 8; v++ {
				sum += dctScale[v] * tmp[v*8+x] * dctCos[v][y]
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
	if p.w == 0 || p.h == 0 {
		return img
	}
	clampToByte := func(v float64) uint8 {
		if v < 0 {
			return 0
		}
		if v > 255 {
			return 255
		}
		return uint8(v + 0.5)
	}
	workers := runtime.GOMAXPROCS(0)
	if workers < 1 {
		workers = 1
	}
	if workers > p.h {
		workers = p.h
	}
	if workers == 1 {
		workers = 0
	}
	processRows := func(y0, y1 int) {
		switch p.mode {
		case "422":
			for yy := y0; yy < y1; yy++ {
				rowOff := yy * img.Stride
				for xx := 0; xx < p.w; xx++ {
					ci := yy*p.cw + (xx / 2)
					yv := clampToByte(p.y[yy*p.w+xx])
					cb := clampToByte(p.cb[ci])
					cr := clampToByte(p.cr[ci])
					av := clampToByte(p.a[yy*p.w+xx])
					r, g, b := color.YCbCrToRGB(yv, cb, cr)
					off := rowOff + xx*4
					img.Pix[off+0] = r
					img.Pix[off+1] = g
					img.Pix[off+2] = b
					img.Pix[off+3] = av
				}
			}
		case "420":
			for yy := y0; yy < y1; yy++ {
				rowOff := yy * img.Stride
				cy := yy / 2
				for xx := 0; xx < p.w; xx++ {
					ci := cy*p.cw + (xx / 2)
					yv := clampToByte(p.y[yy*p.w+xx])
					cb := clampToByte(p.cb[ci])
					cr := clampToByte(p.cr[ci])
					av := clampToByte(p.a[yy*p.w+xx])
					r, g, b := color.YCbCrToRGB(yv, cb, cr)
					off := rowOff + xx*4
					img.Pix[off+0] = r
					img.Pix[off+1] = g
					img.Pix[off+2] = b
					img.Pix[off+3] = av
				}
			}
		default:
			for yy := y0; yy < y1; yy++ {
				rowOff := yy * img.Stride
				for xx := 0; xx < p.w; xx++ {
					ci := yy*p.cw + xx
					yv := clampToByte(p.y[yy*p.w+xx])
					cb := clampToByte(p.cb[ci])
					cr := clampToByte(p.cr[ci])
					av := clampToByte(p.a[yy*p.w+xx])
					r, g, b := color.YCbCrToRGB(yv, cb, cr)
					off := rowOff + xx*4
					img.Pix[off+0] = r
					img.Pix[off+1] = g
					img.Pix[off+2] = b
					img.Pix[off+3] = av
				}
			}
		}
	}
	if workers == 0 {
		processRows(0, p.h)
		return img
	}
	rowsPer := (p.h + workers - 1) / workers
	var wg sync.WaitGroup
	for i := 0; i < workers; i++ {
		y0 := i * rowsPer
		if y0 >= p.h {
			break
		}
		y1 := y0 + rowsPer
		if y1 > p.h {
			y1 = p.h
		}
		wg.Add(1)
		go func(a, b int) {
			defer wg.Done()
			processRows(a, b)
		}(y0, y1)
	}
	wg.Wait()
	return img
}

func decodePlaneDCT(r *bufio.Reader, pw, ph int, qtable [64]int, center bool, clamp bool) ([]float64, error) {
	bw := (pw + 7) / 8
	bh := (ph + 7) / 8
	blocks := bw * bh
	out := make([]float64, pw*ph)
	coeffAll := make([]float64, blocks*64)
	blockAll := make([]float64, blocks*64)
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			off := (by*bw + bx) * 64
			for i := 0; i < 64; i++ {
				v, err := readSVarint(r)
				if err != nil {
					return nil, err
				}
				idx := zigZagOrder[i]
				coeffAll[off+idx] = float64(v) * float64(qtable[idx])
			}
		}
	}
	idctDecodeMany(coeffAll, blockAll)
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			off := (by*bw + bx) * 64
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
					v := blockAll[off+y*8+x]
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
	blocks := bw * bh
	out := make([]float64, pw*ph)
	coeffAll := make([]float64, blocks*64)
	blockAll := make([]float64, blocks*64)
	var dcVals []int
	if predDC {
		dcVals = make([]int, bw*bh)
	}
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			base := (by*bw + bx) * 64
			if blockSkip {
				bit, err := r.ReadBit()
				if err != nil {
					return nil, err
				}
				if bit == 1 {
					if predDC {
						dcVals[by*bw+bx] = 0
					}
					continue
				}
			}
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
				coeffAll[base] = float64(dc) * float64(qtable[0])
			} else {
				v, err := readRiceSigned(r, k)
				if err != nil {
					return nil, err
				}
				coeffAll[base] = float64(v) * float64(qtable[0])
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
					coeffAll[base+idx] = float64(v) * float64(qtable[idx])
					pos++
				}
			} else {
				for i := 1; i < 64; i++ {
					v, err := readRiceSigned(r, k)
					if err != nil {
						return nil, err
					}
					idx := zigZagOrder[i]
					coeffAll[base+idx] = float64(v) * float64(qtable[idx])
				}
			}
		}
	}
	idctDecodeMany(coeffAll, blockAll)
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			base := (by*bw + bx) * 64
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
					v := blockAll[base+y*8+x]
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
	n := len(base)
	workers := runtime.GOMAXPROCS(0)
	if workers < 1 {
		workers = 1
	}
	if workers > n/16384 {
		workers = n / 16384
	}
	if workers < 1 {
		workers = 1
	}
	if workers == 1 {
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
	chunk := (n + workers - 1) / workers
	var wg sync.WaitGroup
	for w := 0; w < workers; w++ {
		start := w * chunk
		if start >= n {
			break
		}
		end := start + chunk
		if end > n {
			end = n
		}
		wg.Add(1)
		go func(a, b int) {
			defer wg.Done()
			for i := a; i < b; i++ {
				v := base[i] + delta[i]
				if v < 0 {
					v = 0
				} else if v > 255 {
					v = 255
				}
				out[i] = v
			}
		}(start, end)
	}
	wg.Wait()
	return out
}

func filledPlane(n int, v float64) []float64 {
	out := make([]float64, n)
	for i := range out {
		out[i] = v
	}
	return out
}

func clampToByte(v float64) uint8 {
	if v < 0 {
		return 0
	}
	if v > 255 {
		return 255
	}
	return uint8(math.Round(v))
}

func clampRoundByte(v float64) float64 {
	if v < 0 {
		return 0
	}
	if v > 255 {
		return 255
	}
	return math.Round(v)
}

func normalizePlaneToByteInPlace(p []float64) {
	for i := range p {
		p[i] = clampRoundByte(p[i])
	}
}

func normalizeRefPlanesInPlace(p *ycbcrPlanes) {
	if p == nil {
		return
	}
	normalizePlaneToByteInPlace(p.y)
	normalizePlaneToByteInPlace(p.cb)
	normalizePlaneToByteInPlace(p.cr)
	normalizePlaneToByteInPlace(p.a)
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

func floorDivPositiveDenom(a, b int) int {
	q := a / b
	r := a % b
	if r != 0 && a < 0 {
		q--
	}
	return q
}

func fillPredBlockChroma(pred, ref []float64, cw, ch, subX, subY int, bx, by, bw, bh, dx, dy int) {
	if ref == nil {
		return
	}
	cbx := bx / subX
	cby := by / subY
	cbw := (bw + subX - 1) / subX
	cbh := (bh + subY - 1) / subY
	cdx := floorDivPositiveDenom(dx, subX)
	cdy := floorDivPositiveDenom(dy, subY)
	fx := dx - cdx*subX
	fy := dy - cdy*subY
	sx := cbx + cdx
	sy := cby + cdy
	extraX := 0
	extraY := 0
	if fx != 0 {
		extraX = 1
	}
	if fy != 0 {
		extraY = 1
	}
	if sx < 0 || sy < 0 || sx+cbw+extraX > cw || sy+cbh+extraY > ch {
		return
	}
	if fx == 0 && fy == 0 {
		for y := 0; y < cbh; y++ {
			for x := 0; x < cbw; x++ {
				pred[(cby+y)*cw+(cbx+x)] = ref[(sy+y)*cw+(sx+x)]
			}
		}
		return
	}
	wx := float64(fx) / float64(subX)
	wy := float64(fy) / float64(subY)
	for y := 0; y < cbh; y++ {
		for x := 0; x < cbw; x++ {
			i00 := (sy+y)*cw + (sx + x)
			p00 := ref[i00]
			p10 := p00
			p01 := p00
			p11 := p00
			if fx != 0 {
				p10 = ref[i00+1]
				p11 = p10
			}
			if fy != 0 {
				i01 := (sy+y+1)*cw + (sx + x)
				p01 = ref[i01]
				p11 = p01
				if fx != 0 {
					p11 = ref[i01+1]
				}
			}
			v0 := p00 + (p10-p00)*wx
			v1 := p01 + (p11-p01)*wx
			pred[(cby+y)*cw+(cbx+x)] = v0 + (v1-v0)*wy
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
	cdxA := floorDivPositiveDenom(dxA, subX)
	cdyA := floorDivPositiveDenom(dyA, subY)
	cdxB := floorDivPositiveDenom(dxB, subX)
	cdyB := floorDivPositiveDenom(dyB, subY)
	fxA := dxA - cdxA*subX
	fyA := dyA - cdyA*subY
	fxB := dxB - cdxB*subX
	fyB := dyB - cdyB*subY
	sxA := cbx + cdxA
	syA := cby + cdyA
	sxB := cbx + cdxB
	syB := cby + cdyB
	extraXA, extraYA := 0, 0
	extraXB, extraYB := 0, 0
	if fxA != 0 {
		extraXA = 1
	}
	if fyA != 0 {
		extraYA = 1
	}
	if fxB != 0 {
		extraXB = 1
	}
	if fyB != 0 {
		extraYB = 1
	}
	if sxA < 0 || syA < 0 || sxB < 0 || syB < 0 || sxA+cbw+extraXA > cw || syA+cbh+extraYA > ch || sxB+cbw+extraXB > cw || syB+cbh+extraYB > ch {
		return
	}
	wxA := float64(fxA) / float64(subX)
	wyA := float64(fyA) / float64(subY)
	wxB := float64(fxB) / float64(subX)
	wyB := float64(fyB) / float64(subY)

	sample := func(ref []float64, sx, sy, x, y int, fx, fy int, wx, wy float64) float64 {
		i00 := (sy+y)*cw + (sx + x)
		p00 := ref[i00]
		p10 := p00
		p01 := p00
		p11 := p00
		if fx != 0 {
			p10 = ref[i00+1]
			p11 = p10
		}
		if fy != 0 {
			i01 := (sy+y+1)*cw + (sx + x)
			p01 = ref[i01]
			p11 = p01
			if fx != 0 {
				p11 = ref[i01+1]
			}
		}
		v0 := p00 + (p10-p00)*wx
		v1 := p01 + (p11-p01)*wx
		return v0 + (v1-v0)*wy
	}

	for y := 0; y < cbh; y++ {
		for x := 0; x < cbw; x++ {
			a := sample(refA, sxA, syA, x, y, fxA, fyA, wxA, wyA)
			b := sample(refB, sxB, syB, x, y, fxB, fyB, wxB, wyB)
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

func hexNibble(b byte) (uint8, bool) {
	switch {
	case b >= '0' && b <= '9':
		return b - '0', true
	case b >= 'A' && b <= 'F':
		return b - 'A' + 10, true
	case b >= 'a' && b <= 'f':
		return b - 'a' + 10, true
	default:
		return 0, false
	}
}

func parseHexBytePair(s string, pos int) (uint8, bool) {
	if pos+2 > len(s) {
		return 0, false
	}
	hi, ok := hexNibble(s[pos])
	if !ok {
		return 0, false
	}
	lo, ok := hexNibble(s[pos+1])
	if !ok {
		return 0, false
	}
	return hi<<4 | lo, true
}

func channelRefValue(ref byte, vals *[4]uint8, channel int) (uint8, bool) {
	switch ref {
	case 'R':
		if channel > 0 {
			return vals[0], true
		}
	case 'G':
		if channel > 1 {
			return vals[1], true
		}
	case 'Z':
		if channel > 2 {
			return vals[2], true
		}
	}
	return 0, false
}

func scanCompactRGBALiteral(s string, pos int) (end int, hasRef bool, ok bool) {
	var vals [4]uint8
	v, ok := parseHexBytePair(s, pos)
	if !ok {
		return pos, false, false
	}
	vals[0] = v
	pos += 2
	for channel := 1; channel < 4; channel++ {
		if pos >= len(s) {
			return pos, hasRef, false
		}
		if v, ok := channelRefValue(s[pos], &vals, channel); ok {
			vals[channel] = v
			hasRef = true
			pos++
			continue
		}
		v, ok := parseHexBytePair(s, pos)
		if !ok {
			return pos, hasRef, false
		}
		vals[channel] = v
		pos += 2
	}
	return pos, hasRef, true
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
			start := i
			parsed := false
			for i < n && isHexDigit(s[i]) {
				j, _, ok := scanCompactRGBALiteral(s, i)
				if !ok {
					break
				}
				k, repeated := readRepeat(j)
				tok := s[i:j]
				if repeated {
					tok = s[i:k]
				}
				tokens = append(tokens, tok)
				i = k
				parsed = true
				if repeated {
					break
				}
			}
			if parsed {
				continue
			}
			j := start
			for j < n && isHexDigit(s[j]) {
				j++
			}
			tokens = append(tokens, s[start:j])
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
			start := i
			parsed := false
			for i < n && isHexDigit(s[i]) {
				j, _, ok := scanCompactRGBALiteral(s, i)
				if !ok {
					break
				}
				k, repeated := readRepeat(j)
				tok := s[i:j]
				if repeated {
					tok = s[i:k]
				}
				tokens = append(tokens, tok)
				i = k
				parsed = true
				if repeated {
					break
				}
			}
			if parsed {
				continue
			}
			j := start
			for j < n && isHexDigit(s[j]) {
				j++
			}
			tokens = append(tokens, s[start:j])
			i = j
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
			start := i
			parsed := false
			for i < n && isHexDigit(s[i]) {
				j, _, ok := scanCompactRGBALiteral(s, i)
				if !ok {
					break
				}
				k, repeated := readRepeat(j)
				tok := s[i:j]
				if repeated {
					tok = s[i:k]
				}
				tokens = append(tokens, tok)
				i = k
				parsed = true
				if repeated {
					break
				}
			}
			if parsed {
				continue
			}
			j := start
			for j < n && isHexDigit(s[j]) {
				j++
			}
			left := start - 16
			if left < 0 {
				left = 0
			}
			right := j + 16
			if right > n {
				right = n
			}
			snippet := s[left:right]
			caret := strings.Repeat(" ", start-left) + "^"
			return nil, fmt.Errorf("bad compact RGBA token at col %d: %q\n%s\n%s", start+1, s[start:j], snippet, caret)
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
	if strings.HasPrefix(tok, "#") {
		return parseCompactHexStrict(tok)
	}
	if (len(tok) == 6 || len(tok) == 8) && isAllHex(tok) {
		return parseCompactHexStrict(tok)
	}
	if len(tok) >= 5 && isHexDigit(tok[0]) && strings.ContainsAny(tok, "RGZ") {
		return parseCompactHexStrict(tok)
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

func parseCompactHexStrict(tok string) (color.RGBA, error) {
	h := strings.TrimPrefix(tok, "#")
	if strings.ContainsAny(h, "RGZ") {
		var vals [4]uint8
		v, ok := parseHexBytePair(h, 0)
		if !ok {
			return color.RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
		}
		vals[0] = v
		pos := 2
		for channel := 1; channel < 4; channel++ {
			if pos >= len(h) {
				return color.RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
			}
			if v, ok := channelRefValue(h[pos], &vals, channel); ok {
				vals[channel] = v
				pos++
				continue
			}
			v, ok := parseHexBytePair(h, pos)
			if !ok {
				return color.RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
			}
			vals[channel] = v
			pos += 2
		}
		if pos != len(h) {
			return color.RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
		}
		return color.RGBA{vals[0], vals[1], vals[2], vals[3]}, nil
	}
	if len(h) == 6 {
		h += "FF"
	}
	b, err := hex.DecodeString(h)
	if err != nil || len(b) != 4 {
		return color.RGBA{}, fmt.Errorf("invalid hex: %q", tok)
	}
	return color.RGBA{b[0], b[1], b[2], b[3]}, nil
}

func parseCompactHex(tok string) color.RGBA {
	px, err := parseCompactHexStrict(tok)
	if err != nil {
		panic(err)
	}
	return px
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
	if len(tok) >= 5 && isHexDigit(tok[0]) && strings.ContainsAny(tok, "RGZ") {
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

type clixDecodeMeta struct {
	mode         string
	modeRaw      string
	modeFallback bool
}

func normalizeClixMode(raw string) (string, bool) {
	mode := strings.ToLower(strings.TrimSpace(raw))
	switch mode {
	case "lossless", "safe", "unsafe", "experimental":
		return mode, false
	default:
		return "safe", true
	}
}

func decodeClixToImage(path string) (image.Image, []uint32, clixDecodeMeta, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, nil, clixDecodeMeta{}, err
	}
	dec, _ := zstd.NewReader(nil)
	defer dec.Close()
	raw, err := dec.DecodeAll(data, nil)
	if err != nil {
		return nil, nil, clixDecodeMeta{}, err
	}
	txt := strings.ReplaceAll(string(raw), "\r\n", "\n")
	lines := strings.Split(txt, "\n")
	var width, height int
	var bg *color.RGBA
	var dataLines []string
	macros := make(map[string]color.RGBA)
	meta := clixDecodeMeta{mode: "safe", modeRaw: "safe", modeFallback: false}
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
		if strings.HasPrefix(ln, "MODE=") {
			rawMode := strings.TrimPrefix(ln, "MODE=")
			mode, fallback := normalizeClixMode(rawMode)
			meta.modeRaw = strings.TrimSpace(rawMode)
			meta.mode = mode
			meta.modeFallback = fallback
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
	if width <= 0 || height <= 0 {
		return nil, nil, clixDecodeMeta{}, fmt.Errorf("missing RES or WIDTH/HEIGHT in CLIX header")
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
				return nil, nil, clixDecodeMeta{}, fmt.Errorf("tokenization error on data line %d: %v", idx+1, terr)
			}
			tokens = append(tokens, ts...)
		}
	}
	expanded := expandTokens(tokens)
	total := width * height
	pixels := make([]color.RGBA, total)
	filled := make([]bool, total)
	shapeIDs := make([]uint32, total)
	nextShapeID := uint32(1)
	var prev *color.RGBA
	cursor := 0
	ellipseContains := func(localX, localY, w, h int) bool {
		if w <= 0 || h <= 0 {
			return false
		}
		dx := int64(2*localX + 1 - w)
		dy := int64(2*localY + 1 - h)
		ww := int64(w)
		hh := int64(h)
		lhs := dx*dx*hh*hh + dy*dy*ww*ww
		rhs := ww * ww * hh * hh
		return lhs <= rhs
	}
	triangleContains := func(localX, localY, w, h, orient int) bool {
		if w <= 0 || h <= 0 {
			return false
		}
		fx := float64(2*localX+1) / float64(2*w)
		fy := float64(2*localY+1) / float64(2*h)
		const eps = 1e-12
		switch orient {
		case 0:
			return fy <= 1.0-fx+eps
		case 1:
			return fy <= fx+eps
		case 2:
			return fy+eps >= fx
		case 3:
			return fy+eps >= 1.0-fx
		case 4:
			return math.Abs(fx-0.5) <= fy*0.5+eps
		case 5:
			return math.Abs(fy-0.5) <= fx*0.5+eps
		case 6:
			return math.Abs(fx-0.5) <= (1.0-fy)*0.5+eps
		case 7:
			return math.Abs(fy-0.5) <= (1.0-fx)*0.5+eps
		default:
			return false
		}
	}
	resolvePixel := func(base string) (color.RGBA, error) {
		if m, ok := macros[base]; ok {
			return m, nil
		}
		return tokenToRGBAe(base, bg, prev)
	}
	type clixShapeSpec struct {
		kind byte
		x    int
		y    int
		w    int
		h    int
		o    int
		fill string
	}
	parseShape := func(tok string) (clixShapeSpec, bool, error) {
		if !strings.HasPrefix(tok, "@") {
			return clixShapeSpec{}, false, nil
		}
		body := tok[1:]
		eq := strings.IndexByte(body, '=')
		if eq <= 0 || eq+1 >= len(body) {
			return clixShapeSpec{}, true, fmt.Errorf("expected @x,y,w,h=TOKEN or @C,x,y,w,h=TOKEN or @T,x,y,w,h,o=TOKEN")
		}
		spec := clixShapeSpec{kind: 'R', fill: body[eq+1:]}
		shapeHead := body[:eq]
		if strings.HasPrefix(shapeHead, "C,") {
			spec.kind = 'C'
			shapeHead = shapeHead[2:]
		} else if strings.HasPrefix(shapeHead, "T,") {
			spec.kind = 'T'
			shapeHead = shapeHead[2:]
		}
		parts := strings.Split(shapeHead, ",")
		wantParts := 4
		if spec.kind == 'T' {
			wantParts = 5
		}
		if len(parts) != wantParts {
			switch spec.kind {
			case 'R':
				return clixShapeSpec{}, true, fmt.Errorf("rectangle must have 4 comma-separated numbers")
			case 'C':
				return clixShapeSpec{}, true, fmt.Errorf("circle/ellipse must have 4 comma-separated numbers")
			default:
				return clixShapeSpec{}, true, fmt.Errorf("triangle must have 5 comma-separated numbers (x,y,w,h,orient)")
			}
		}
		nums := make([]int, len(parts))
		for i, p := range parts {
			v, e := strconv.Atoi(strings.TrimSpace(p))
			if e != nil {
				return clixShapeSpec{}, true, fmt.Errorf("invalid shape number %q", p)
			}
			nums[i] = v
		}
		spec.x, spec.y, spec.w, spec.h = nums[0], nums[1], nums[2], nums[3]
		if spec.w <= 0 || spec.h <= 0 {
			return clixShapeSpec{}, true, fmt.Errorf("shape width/height must be > 0")
		}
		if spec.kind == 'T' {
			spec.o = nums[4]
			if spec.o < 0 || spec.o > 7 {
				return clixShapeSpec{}, true, fmt.Errorf("triangle orientation must be 0..7")
			}
		}
		return spec, true, nil
	}
	for ti, t := range expanded {
		spec, isShape, serr := parseShape(t)
		if serr != nil {
			return nil, nil, clixDecodeMeta{}, fmt.Errorf("bad shape token at index %d: %q (%v)", ti, t, serr)
		}
		if isShape {
			if spec.x < 0 || spec.y < 0 || spec.x+spec.w > width || spec.y+spec.h > height {
				return nil, nil, clixDecodeMeta{}, fmt.Errorf("shape out of bounds at index %d: %q for image %dx%d", ti, t, width, height)
			}
			px, e := resolvePixel(spec.fill)
			if e != nil {
				return nil, nil, clixDecodeMeta{}, fmt.Errorf("bad shape fill token at index %d: %q: %v", ti, spec.fill, e)
			}
			shapeID := nextShapeID
			nextShapeID++
			for y := 0; y < spec.h; y++ {
				rowOff := (spec.y + y) * width
				for x := 0; x < spec.w; x++ {
					write := false
					switch spec.kind {
					case 'R':
						write = true
					case 'C':
						write = ellipseContains(x, y, spec.w, spec.h)
					case 'T':
						write = triangleContains(x, y, spec.w, spec.h, spec.o)
					}
					if write {
						idx := rowOff + (spec.x + x)
						pixels[idx] = px
						filled[idx] = true
						shapeIDs[idx] = shapeID
					}
				}
			}
			tmp := px
			prev = &tmp
			continue
		}
		if cursor >= total {
			return nil, nil, clixDecodeMeta{}, fmt.Errorf("pixel mismatch: got more than %d pixels", total)
		}
		px, e := resolvePixel(t)
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
			return nil, nil, clixDecodeMeta{}, fmt.Errorf("bad token at index %d: %q: %v\ncontext: %s", ti, t, e, context)
		}
		pixels[cursor] = px
		filled[cursor] = true
		shapeIDs[cursor] = 0
		cursor++
		tmp := px
		prev = &tmp
	}
	for idx, ok := range filled {
		if !ok {
			x := idx % width
			y := idx / width
			return nil, nil, clixDecodeMeta{}, fmt.Errorf("decoded pixel map incomplete: missing pixel at (%d,%d)", x, y)
		}
	}
	img := image.NewRGBA(image.Rect(0, 0, width, height))
	for y := 0; y < height; y++ {
		rowOff := y * width
		for x := 0; x < width; x++ {
			img.SetRGBA(x, y, pixels[rowOff+x])
		}
	}
	return img, shapeIDs, meta, nil
}

func rgbForShapeID(shapeID uint32, used map[uint32]struct{}) color.NRGBA {
	for attempt := uint32(0); attempt < 2048; attempt++ {
		seed := shapeID*0x9e3779b1 + (attempt+1)*0x85ebca6b
		seed ^= seed >> 16
		seed *= 0x7feb352d
		seed ^= seed >> 15
		seed *= 0x846ca68b
		seed ^= seed >> 16
		h := float64(seed%36000) / 100.0
		s := 0.78 + float64((seed>>9)%190)/1000.0
		v := 0.88 + float64((seed>>18)%110)/1000.0
		c := v * s
		x := c * (1.0 - math.Abs(math.Mod(h/60.0, 2.0)-1.0))
		m := v - c
		var rf, gf, bf float64
		switch {
		case h < 60:
			rf, gf, bf = c, x, 0
		case h < 120:
			rf, gf, bf = x, c, 0
		case h < 180:
			rf, gf, bf = 0, c, x
		case h < 240:
			rf, gf, bf = 0, x, c
		case h < 300:
			rf, gf, bf = x, 0, c
		default:
			rf, gf, bf = c, 0, x
		}
		r := uint8(math.Round((rf + m) * 255))
		g := uint8(math.Round((gf + m) * 255))
		b := uint8(math.Round((bf + m) * 255))
		hex := (uint32(r) << 16) | (uint32(g) << 8) | uint32(b)
		if _, exists := used[hex]; exists {
			continue
		}
		used[hex] = struct{}{}
		return color.NRGBA{R: r, G: g, B: b, A: 255}
	}
	return color.NRGBA{R: 255, G: 0, B: 255, A: 255}
}

func buildShapeDebugOverlay(shapeIDs []uint32, width, height int) *ebiten.Image {
	if width <= 0 || height <= 0 || len(shapeIDs) != width*height {
		return nil
	}
	buf := image.NewNRGBA(image.Rect(0, 0, width, height))
	shapeColors := make(map[uint32]color.NRGBA)
	used := make(map[uint32]struct{})
	hasAny := false
	for y := 0; y < height; y++ {
		rowOff := y * width
		for x := 0; x < width; x++ {
			shapeID := shapeIDs[rowOff+x]
			if shapeID == 0 {
				continue
			}
			clr, ok := shapeColors[shapeID]
			if !ok {
				clr = rgbForShapeID(shapeID, used)
				shapeColors[shapeID] = clr
			}
			buf.SetNRGBA(x, y, clr)
			hasAny = true
		}
	}
	if !hasAny {
		return nil
	}
	return ebiten.NewImageFromImage(buf)
}

func buildTrixDebugOverlay(methods []byte, width, height, blockDim int) (*ebiten.Image, [2]int) {
	var counts [2]int
	if width <= 0 || height <= 0 || blockDim <= 0 || len(methods) == 0 {
		return nil, counts
	}
	blocksX := (width + blockDim - 1) / blockDim
	blocksY := (height + blockDim - 1) / blockDim
	if len(methods) != blocksX*blocksY {
		return nil, counts
	}
	buf := image.NewNRGBA(image.Rect(0, 0, width, height))
	i := 0
	for by := 0; by < height; by += blockDim {
		bh := blockDim
		if by+bh > height {
			bh = height - by
		}
		for bx := 0; bx < width; bx += blockDim {
			bw := blockDim
			if bx+bw > width {
				bw = width - bx
			}
			method := methods[i]
			i++
			clr := color.NRGBA{R: 255, G: 170, B: 0, A: 150}
			if method == trixMethodDCT {
				clr = color.NRGBA{R: 0, G: 190, B: 255, A: 150}
				counts[1]++
			} else {
				counts[0]++
			}
			for y := 0; y < bh; y++ {
				for x := 0; x < bw; x++ {
					buf.SetNRGBA(bx+x, by+y, clr)
				}
			}
		}
	}
	return ebiten.NewImageFromImage(buf), counts
}

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
	blxOpMacro  = 0xFE
)

const (
	trixDefaultBlockDim = 8
	trixMethodBLX       = 0
	trixMethodDCT       = 1
	trixMacroMaxEntries = 64
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

func parseBlixMacroHex(tok string) (color.RGBA, error) {
	if len(tok) != 8 || !isAllHex(tok) {
		return color.RGBA{}, fmt.Errorf("invalid macro hex: %q", tok)
	}
	b, err := hex.DecodeString(tok)
	if err != nil || len(b) != 4 {
		return color.RGBA{}, fmt.Errorf("invalid macro hex: %q", tok)
	}
	return color.RGBA{b[0], b[1], b[2], b[3]}, nil
}

func readSimpleSymFromOp(op byte, br *bufio.Reader, macros []color.RGBA) (simpleSym, error) {
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
	case op == blxOpMacro:
		idx, err := binary.ReadUvarint(br)
		if err != nil {
			return simpleSym{}, err
		}
		if idx >= uint64(len(macros)) {
			return simpleSym{}, fmt.Errorf("macro index %d out of range", idx)
		}
		return simpleSym{kind: sKindLit, px: macros[idx]}, nil
	default:
		return simpleSym{}, fmt.Errorf("unknown opcode 0x%X", op)
	}
}
func readSimpleSym(br *bufio.Reader, macros []color.RGBA) (simpleSym, error) {
	op, err := br.ReadByte()
	if err != nil {
		return simpleSym{}, err
	}
	return readSimpleSymFromOp(op, br, macros)
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

func clixCheckRepeat(cnt uint64, remaining int) error {
	if remaining < 0 {
		remaining = 0
	}
	if cnt > uint64(remaining) {
		return fmt.Errorf("repeat count %d exceeds remaining %d pixels", cnt, remaining)
	}
	return nil
}

func clixCheckSeq(stepCount, reps uint64, remaining int) error {
	if remaining < 0 {
		remaining = 0
	}
	r := uint64(remaining)
	if stepCount > r || reps > r || stepCount*reps > r {
		return fmt.Errorf("sequence %d steps x %d reps exceeds remaining %d pixels", stepCount, reps, remaining)
	}
	return nil
}

func vlxCheckByteLen(n, maxBytes uint64) error {
	if n > maxBytes {
		return fmt.Errorf("declared frame data length %d exceeds maximum %d", n, maxBytes)
	}
	return nil
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
	var macros []color.RGBA
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
		if strings.HasPrefix(line, "MACROS=") {
			body := strings.TrimSpace(strings.TrimPrefix(line, "MACROS="))
			if body == "" {
				continue
			}
			parts := strings.Split(body, ",")
			macros = make([]color.RGBA, 0, len(parts))
			for _, p := range parts {
				p = strings.TrimSpace(p)
				if p == "" {
					continue
				}
				px, err := parseBlixMacroHex(p)
				if err != nil {
					return nil, err
				}
				macros = append(macros, px)
			}
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
				sub, e2 := readSimpleSym(br, macros)
				if e2 != nil {
					return nil, e2
				}
				cnt, e3 := binary.ReadUvarint(br)
				if e3 != nil {
					return nil, e3
				}
				if err := clixCheckRepeat(cnt, width*height-len(pixels)); err != nil {
					return nil, err
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
				if err := clixCheckSeq(L, N, width*height-len(pixels)); err != nil {
					return nil, err
				}
				steps := make([]simpleSym, L)
				for i := uint64(0); i < L; i++ {
					sym, e4 := readSimpleSym(br, macros)
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
				sym, e2 := readSimpleSymFromOp(op, br, macros)
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

func decodeTrixBLXBlock(payload []byte, count int) ([]color.RGBA, error) {
	br := bufio.NewReader(bytes.NewReader(payload))
	macroCount, err := binary.ReadUvarint(br)
	if err != nil {
		return nil, err
	}
	if macroCount > trixMacroMaxEntries {
		return nil, fmt.Errorf("TRIX BLX macro count %d exceeds max %d", macroCount, trixMacroMaxEntries)
	}
	macros := make([]color.RGBA, int(macroCount))
	for i := range macros {
		var b [4]byte
		if _, err := io.ReadFull(br, b[:]); err != nil {
			return nil, err
		}
		macros[i] = color.RGBA{b[0], b[1], b[2], b[3]}
	}
	pixels := make([]color.RGBA, 0, count)
	var prev *color.RGBA
	for len(pixels) < count {
		op, err := br.ReadByte()
		if err != nil {
			return nil, err
		}
		switch op {
		case blxOpRepeat:
			sub, err := readSimpleSym(br, macros)
			if err != nil {
				return nil, err
			}
			cnt, err := binary.ReadUvarint(br)
			if err != nil {
				return nil, err
			}
			if err := clixCheckRepeat(cnt, count-len(pixels)); err != nil {
				return nil, err
			}
			for i := uint64(0); i < cnt; i++ {
				if err := emitSimpleSym(sub, nil, &prev, &pixels); err != nil {
					return nil, err
				}
			}
		case blxOpSeq:
			l, err := binary.ReadUvarint(br)
			if err != nil {
				return nil, err
			}
			n, err := binary.ReadUvarint(br)
			if err != nil {
				return nil, err
			}
			if err := clixCheckSeq(l, n, count-len(pixels)); err != nil {
				return nil, err
			}
			steps := make([]simpleSym, l)
			for i := uint64(0); i < l; i++ {
				sym, err := readSimpleSym(br, macros)
				if err != nil {
					return nil, err
				}
				steps[i] = sym
			}
			for r := uint64(0); r < n; r++ {
				for i := range steps {
					if err := emitSimpleSym(steps[i], nil, &prev, &pixels); err != nil {
						return nil, err
					}
				}
			}
		default:
			sym, err := readSimpleSymFromOp(op, br, macros)
			if err != nil {
				return nil, err
			}
			if err := emitSimpleSym(sym, nil, &prev, &pixels); err != nil {
				return nil, err
			}
		}
	}
	if len(pixels) > count {
		return nil, fmt.Errorf("TRIX BLX block overrun: got %d pixels, expected %d", len(pixels), count)
	}
	return pixels, nil
}

func decodeTrixDCTBlock(payload []byte, w, h int, qY, qC [64]int) ([]color.RGBA, error) {
	if len(payload) == 0 {
		return nil, fmt.Errorf("empty TRIX DCT block")
	}
	mask := payload[0]
	if mask&0x7 != 0x7 {
		return nil, fmt.Errorf("TRIX DCT block missing YCbCr planes: mask=0x%X", mask)
	}
	r := newBitReader(payload[1:])
	yPlane, err := decodePlaneDCTRiceEx(r, w, h, qY, true, true, vlxDctRiceK, true, true, true, true)
	if err != nil {
		return nil, err
	}
	cbPlane, err := decodePlaneDCTRiceEx(r, w, h, qC, true, true, vlxDctRiceK, true, true, true, true)
	if err != nil {
		return nil, err
	}
	crPlane, err := decodePlaneDCTRiceEx(r, w, h, qC, true, true, vlxDctRiceK, true, true, true, true)
	if err != nil {
		return nil, err
	}
	aPlane := filledPlane(w*h, 255)
	if mask&0x8 != 0 {
		aPlane, err = decodePlaneDCTRiceEx(r, w, h, qY, true, true, vlxDctRiceK, true, true, true, true)
		if err != nil {
			return nil, err
		}
	}
	pixels := make([]color.RGBA, w*h)
	for i := range pixels {
		yy := clampToByte(yPlane[i])
		cb := clampToByte(cbPlane[i])
		cr := clampToByte(crPlane[i])
		rr, gg, bb := color.YCbCrToRGB(yy, cb, cr)
		pixels[i] = color.RGBA{rr, gg, bb, clampToByte(aPlane[i])}
	}
	return pixels, nil
}

func decodeTrixToImage(path string) (image.Image, []byte, int, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, nil, 0, err
	}
	defer f.Close()
	zr, err := zstd.NewReader(f)
	if err != nil {
		return nil, nil, 0, err
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
		return nil, nil, 0, err
	}
	if !strings.HasPrefix(hdr, "TRIX") {
		return nil, nil, 0, fmt.Errorf("not a TRIX stream: %q", hdr)
	}
	planar := false
	if f := strings.Fields(hdr); len(f) >= 2 && f[1] != "0.1" {
		planar = true
	}
	width, height := 0, 0
	blockDim := trixDefaultBlockDim
	dctQuality := 75
	for {
		line, err := readLine()
		if err != nil {
			return nil, nil, 0, err
		}
		if line == "" {
			break
		}
		parts := strings.SplitN(line, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key := strings.TrimSpace(parts[0])
		val := strings.TrimSpace(parts[1])
		switch key {
		case "WIDTH":
			width, _ = strconv.Atoi(val)
		case "HEIGHT":
			height, _ = strconv.Atoi(val)
		case "BLOCK":
			if v, err := strconv.Atoi(val); err == nil && v > 0 {
				blockDim = v
			}
		case "DCT_QUALITY":
			if v, err := strconv.Atoi(val); err == nil {
				if v < 1 {
					v = 1
				} else if v > 100 {
					v = 100
				}
				dctQuality = v
			}
		}
	}
	if width <= 0 || height <= 0 {
		return nil, nil, 0, fmt.Errorf("invalid TRIX header (WIDTH/HEIGHT)")
	}
	out := image.NewRGBA(image.Rect(0, 0, width, height))
	blocksX := (width + blockDim - 1) / blockDim
	blocksY := (height + blockDim - 1) / blockDim
	numBlocks := blocksX * blocksY
	maxBlockBytes := uint64(blockDim)*uint64(blockDim)*8 + 4096
	methods := make([]byte, 0, numBlocks)
	qY := scaleQuantTable(jpegLumaQuant, dctQuality)
	qC := scaleQuantTable(jpegChromaQuant, dctQuality)
	var planeMethods []byte
	var planeLens []uint64
	if planar {
		planeMethods = make([]byte, numBlocks)
		if _, err := io.ReadFull(br, planeMethods); err != nil {
			return nil, nil, 0, err
		}
		planeLens = make([]uint64, numBlocks)
		for i := range planeLens {
			n, err := binary.ReadUvarint(br)
			if err != nil {
				return nil, nil, 0, err
			}
			if n > maxBlockBytes {
				return nil, nil, 0, fmt.Errorf("TRIX payload length %d exceeds max %d", n, maxBlockBytes)
			}
			planeLens[i] = n
		}
	}
	blockIdx := 0
	for by := 0; by < height; by += blockDim {
		bh := blockDim
		if by+bh > height {
			bh = height - by
		}
		for bx := 0; bx < width; bx += blockDim {
			bw := blockDim
			if bx+bw > width {
				bw = width - bx
			}
			var method byte
			var payloadLen uint64
			if planar {
				method = planeMethods[blockIdx]
				payloadLen = planeLens[blockIdx]
			} else {
				m, err := br.ReadByte()
				if err != nil {
					return nil, nil, 0, err
				}
				n, err := binary.ReadUvarint(br)
				if err != nil {
					return nil, nil, 0, err
				}
				if n > maxBlockBytes {
					return nil, nil, 0, fmt.Errorf("TRIX payload length %d exceeds max %d", n, maxBlockBytes)
				}
				method, payloadLen = m, n
			}
			blockIdx++
			payload := make([]byte, payloadLen)
			if _, err := io.ReadFull(br, payload); err != nil {
				return nil, nil, 0, err
			}
			var pixels []color.RGBA
			var err error
			switch method {
			case trixMethodBLX:
				pixels, err = decodeTrixBLXBlock(payload, bw*bh)
			case trixMethodDCT:
				pixels, err = decodeTrixDCTBlock(payload, bw, bh, qY, qC)
			default:
				err = fmt.Errorf("unknown TRIX block method 0x%X", method)
			}
			if err != nil {
				return nil, nil, 0, err
			}
			methods = append(methods, method)
			i := 0
			for y := 0; y < bh; y++ {
				for x := 0; x < bw; x++ {
					out.SetRGBA(bx+x, by+y, pixels[i])
					i++
				}
			}
		}
	}
	return out, methods, blockDim, nil
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
			codec = strings.ToUpper(val)
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
						prev[ch] = int16(sample)
						outSamples = append(outSamples, prev[ch])
					}
				}
			default:
				return nil, 0, 0, fmt.Errorf("unknown ALIX op 0x%X", op)
			}
			framesLeft -= n
		}
	case codec == "ALIX2":
		br2 := newBitReader(raw)
		clampS16 := func(v int32) int16 {
			if v > 32767 {
				return 32767
			}
			if v < -32768 {
				return -32768
			}
			return int16(v)
		}
		decodeSeries := func(n int) ([]int32, error) {
			ob, err := br2.ReadBits(2)
			if err != nil {
				return nil, err
			}
			kb, err := br2.ReadBits(5)
			if err != nil {
				return nil, err
			}
			order := int(ob)
			k := uint8(kb)
			x := make([]int32, n)
			get := func(j int) int32 {
				if j < 0 {
					return 0
				}
				return x[j]
			}
			for i := 0; i < n; i++ {
				rv, err := readRiceSigned(br2, k)
				if err != nil {
					return nil, err
				}
				var pred int32
				switch order {
				case 1:
					pred = get(i - 1)
				case 2:
					pred = 2*get(i-1) - get(i-2)
				case 3:
					pred = 3*get(i-1) - 3*get(i-2) + get(i-3)
				}
				x[i] = int32(rv) + pred
			}
			return x, nil
		}
		framesLeft := samples
		for framesLeft > 0 {
			n := blockFrames
			if n > framesLeft {
				n = framesLeft
			}
			silence, err := br2.ReadBit()
			if err != nil {
				return nil, 0, 0, err
			}
			if silence == 1 {
				for i := 0; i < n*channels; i++ {
					outSamples = append(outSamples, 0)
				}
				framesLeft -= n
				continue
			}
			if channels == 2 {
				decorr, err := br2.ReadBit()
				if err != nil {
					return nil, 0, 0, err
				}
				a, err := decodeSeries(n)
				if err != nil {
					return nil, 0, 0, err
				}
				b, err := decodeSeries(n)
				if err != nil {
					return nil, 0, 0, err
				}
				if decorr == 1 {
					for i := 0; i < n; i++ {
						mid := a[i]
						side := b[i]
						l := mid + ((side + (side & 1)) >> 1)
						r := l - side
						outSamples = append(outSamples, clampS16(l), clampS16(r))
					}
				} else {
					for i := 0; i < n; i++ {
						outSamples = append(outSamples, clampS16(a[i]), clampS16(b[i]))
					}
				}
			} else {
				chSeries := make([][]int32, channels)
				for c := 0; c < channels; c++ {
					s, err := decodeSeries(n)
					if err != nil {
						return nil, 0, 0, err
					}
					chSeries[c] = s
				}
				for i := 0; i < n; i++ {
					for c := 0; c < channels; c++ {
						outSamples = append(outSamples, clampS16(chSeries[c][i]))
					}
				}
			}
			framesLeft -= n
		}
	case codec == "PCM16" || codec == "PCM" || codec == "RAW":
		expected := total * 2
		if len(raw) < expected {
			return nil, 0, 0, fmt.Errorf("invalid PCM payload: got %d bytes, expected %d", len(raw), expected)
		}
		if len(raw) > expected {
			raw = raw[:expected]
		}
		outSamples = make([]int16, 0, total)
		for i := 0; i < expected; i += 2 {
			outSamples = append(outSamples, int16(binary.LittleEndian.Uint16(raw[i:i+2])))
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
						if !allowTemporal {
							return nil, 0, nil, fmt.Errorf("motion block in keyframe")
						}
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
								if err := clixCheckRepeat(cnt, ww*hh-len(blockPixels)); err != nil {
									return nil, 0, nil, err
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
								if err := clixCheckSeq(L, N, ww*hh-len(blockPixels)); err != nil {
									return nil, 0, nil, err
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
					if err := clixCheckRepeat(cnt, width*height-len(pixels)); err != nil {
						return nil, 0, nil, err
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
					if err := clixCheckSeq(L, N, width*height-len(pixels)); err != nil {
						return nil, 0, nil, err
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
	maxFrameBytes := uint64(64)*uint64(width)*uint64(height) + (1 << 16)
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
			if err := vlxCheckByteLen(coeffLen, maxFrameBytes); err != nil {
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
			normalizeRefPlanesInPlace(&planes)
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
		if err := vlxCheckByteLen(mvLen, maxFrameBytes); err != nil {
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
		if err := vlxCheckByteLen(coeffLen, maxFrameBytes); err != nil {
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
		normalizeRefPlanesInPlace(&planes)
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
	maxFrameBytes := uint64(64)*uint64(width)*uint64(height) + (1 << 16)
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
			if err := vlxCheckByteLen(coeffLen, maxFrameBytes); err != nil {
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
			normalizeRefPlanesInPlace(&planes)
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
		if err := vlxCheckByteLen(mvLen, maxFrameBytes); err != nil {
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
		if err := vlxCheckByteLen(coeffLen, maxFrameBytes); err != nil {
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
		normalizeRefPlanesInPlace(&planes)
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

func discardReaderBytes(br *bufio.Reader, n uint64) error {
	if n == 0 {
		return nil
	}
	if n > uint64(^uint64(0)>>1) {
		return fmt.Errorf("discard size too large: %d", n)
	}
	if _, err := io.CopyN(io.Discard, br, int64(n)); err != nil {
		return err
	}
	return nil
}

func decodeVlixV2AudioOnly(path string) ([]byte, int, error) {
	vs, err := openVlixStream(path)
	if err != nil {
		return nil, 0, err
	}
	defer vs.Close()
	hdr := vs.hdr
	if hdr.codec != "VLIX2" || hdr.audioBytes <= 0 {
		return nil, 0, nil
	}
	br := vs.br
	framesSeen := 0
	for {
		if hdr.framesExpected > 0 && framesSeen >= hdr.framesExpected {
			break
		}
		frameType, e := br.ReadByte()
		if e == io.EOF {
			break
		}
		if e != nil {
			return nil, 0, e
		}
		if frameType != vlxFrameKey && frameType != vlxFrameDelta && frameType != vlxFrameB {
			return nil, 0, fmt.Errorf("unknown frame type 0x%X", frameType)
		}
		if _, err := binary.ReadUvarint(br); err != nil {
			return nil, 0, err
		}
		if frameType == vlxFrameKey {
			coeffLen, err := binary.ReadUvarint(br)
			if err != nil {
				return nil, 0, err
			}
			if err := discardReaderBytes(br, coeffLen); err != nil {
				return nil, 0, err
			}
			framesSeen++
			continue
		}
		if _, err := binary.ReadUvarint(br); err != nil {
			return nil, 0, err
		}
		if _, err := binary.ReadUvarint(br); err != nil {
			return nil, 0, err
		}
		mvLen, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, 0, err
		}
		if err := discardReaderBytes(br, mvLen); err != nil {
			return nil, 0, err
		}
		coeffLen, err := binary.ReadUvarint(br)
		if err != nil {
			return nil, 0, err
		}
		if err := discardReaderBytes(br, coeffLen); err != nil {
			return nil, 0, err
		}
		framesSeen++
	}
	audioBlob := make([]byte, hdr.audioBytes)
	if _, err := io.ReadFull(br, audioBlob); err != nil {
		return nil, 0, err
	}
	decoded, err := decodeALIXContainer(audioBlob)
	if err != nil {
		return nil, 0, err
	}
	pcm, sampleRate, _, err := decodeALIXBinary(decoded)
	if err != nil {
		return nil, 0, err
	}
	return pcm, sampleRate, nil
}

func startVlixV2StreamWorkers(path string, hdr vlixHeader, decodeAudio bool) (<-chan streamFrame, <-chan streamAudio, <-chan error, error) {
	vs, err := openVlixStream(path)
	if err != nil {
		return nil, nil, nil, err
	}
	if vs.hdr.codec != "VLIX2" {
		vs.Close()
		return nil, nil, nil, fmt.Errorf("expected VLIX2 stream, got %q", vs.hdr.codec)
	}

	frameChan := make(chan streamFrame, 8)
	audioChan := make(chan streamAudio, 1)
	errChan := make(chan error, 1)

	if decodeAudio && hdr.audioBytes > 0 {
		go func(path string) {
			defer close(audioChan)
			pcm, sampleRate, err := decodeVlixV2AudioOnly(path)
			if err != nil {
				fmt.Fprintln(os.Stderr, "[!] VLIX2 audio decode error:", err)
				return
			}
			if len(pcm) > 0 && sampleRate > 0 {
				audioChan <- streamAudio{pcm: pcm, sampleRate: sampleRate}
			}
		}(path)
	} else {
		close(audioChan)
	}

	go func() {
		decodeStart := time.Now()
		defer close(frameChan)
		defer close(errChan)
		defer vs.Close()
		_, err := decodeVlixV2Stream(vs.br, hdr.width, hdr.height, hdr.framesExpected, hdr.audioBytes, hdr.chromaMode, hdr.dctQuality, hdr.dctResQuality, hdr.blockDim, hdr.alphaEnabled, hdr.dctPred, hdr.dctZeroRun, hdr.dctBlockSkip, hdr.dctAcMag, hdr.dctPlaneMask, hdr.dctRiceK, hdr.dctResRiceK, hdr.mvRiceK, func(idx int, img image.Image) error {
			frameChan <- streamFrame{idx: idx, img: img}
			return nil
		})
		if err != nil {
			errChan <- err
			return
		}
		fmt.Printf("[*] VLIX2 decode finished in %s\n", time.Since(decodeStart).Round(time.Millisecond))
	}()

	return frameChan, audioChan, errChan, nil
}

type Game struct {
	frames               []*ebiten.Image
	fps                  float64
	playing              bool
	loopPlayback         bool
	frameIdx             int
	lastTick             time.Time
	accum                float64
	audioCtx             *audio.Context
	audioPlayer          *audio.Player
	audioDuration        time.Duration
	audioPCM             []byte
	audioSampleRate      int
	visualizeAudio       bool
	waveformBuffer       *ebiten.Image
	waveWindowSamps      int
	waveDebug            string
	scale                float64
	offsetX              float64
	offsetY              float64
	dragging             bool
	lastX                int
	lastY                int
	dragButton           ebiten.MouseButton
	showDebug            bool
	shapeOverlay         *ebiten.Image
	trixOverlay          *ebiten.Image
	trixMethodCounts     [2]int
	clixMode             string
	clixModeRaw          string
	clixModeFallback     bool
	imgWidth             int
	imgHeight            int
	winWidth             int
	winHeight            int
	fitted               bool
	streaming            bool
	streamDone           bool
	streamRealtime       bool
	streamPrebuffer      int
	streamCacheBack      int
	streamMaxAhead       int
	streamMaxAheadPaused int
	streamMinFrame       int
	readyFrames          int
	totalFrames          int
	maxFrameIdx          int
	streamCache          map[int]*ebiten.Image
	frameCh              <-chan streamFrame
	audioCh              <-chan streamAudio
	errCh                <-chan error
	streamAuto           bool
	streamStarted        bool
	streamSourcePath     string
	streamHeader         vlixHeader
	streamDecodeAudio    bool
	navLastTick          time.Time
	navHoldLeft          float64
	navHoldRight         float64
	navNextLeft          float64
	navNextRight         float64
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
	if g.streaming && idx < g.streamMinFrame {
		idx = g.streamMinFrame
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

func (g *Game) loopToBeginning() {
	if g.streaming && g.streamDone && g.streamMinFrame > 0 {
		if g.restartStreamFromBeginning() {
			return
		}
	}
	if g.streaming && g.streamMinFrame > 0 {
		g.frameIdx = g.streamMinFrame
	} else {
		g.frameIdx = 0
	}
	g.accum = 0
	if g.audioPlayer != nil {
		_ = g.audioPlayer.SetPosition(0)
		if !(g.visualizeAudio && g.totalFrameCount() <= 1) {
			g.syncAudioToFrame()
		}
		if g.playing {
			g.playAudio()
		}
	}
	g.lastTick = time.Now()
}

func (g *Game) playableFrames() int {
	if g.streaming {
		return g.readyFrames
	}
	return len(g.frames)
}

func (g *Game) totalFrameCount() int {
	if g.streaming {
		if g.totalFrames > 0 {
			return g.totalFrames
		}
		total := g.readyFrames
		if g.maxFrameIdx+1 > total {
			total = g.maxFrameIdx + 1
		}
		return total
	}
	return len(g.frames)
}

func (g *Game) addStreamFrame(idx int, img image.Image) {
	if idx < 0 || img == nil {
		return
	}
	if g.totalFrames > 0 {
		if idx >= g.totalFrames {
			return
		}
	}
	if idx > g.maxFrameIdx {
		g.maxFrameIdx = idx
	}
	if g.streamCache == nil {
		g.streamCache = make(map[int]*ebiten.Image)
	}
	if _, exists := g.streamCache[idx]; exists {
		return
	}
	g.streamCache[idx] = ebiten.NewImageFromImage(img)
	for {
		if _, ok := g.streamCache[g.readyFrames]; ok {
			g.readyFrames++
			continue
		}
		break
	}
	g.evictStreamFrames()
}

func (g *Game) streamBufferedAhead() int {
	ahead := g.readyFrames - g.frameIdx - 1
	if ahead < 0 {
		return 0
	}
	return ahead
}

func (g *Game) streamAheadLimit() int {
	limit := g.streamMaxAhead
	if !g.playing && !g.streamDone && g.streamMaxAheadPaused > limit {
		limit = g.streamMaxAheadPaused
	}
	if g.totalFrames > 0 {
		remaining := g.totalFrames - g.frameIdx - 1
		if remaining < limit {
			limit = remaining
		}
	}
	if limit < 1 {
		limit = 1
	}
	return limit
}

func (g *Game) streamFrameAt(idx int) *ebiten.Image {
	if idx < 0 || g.streamCache == nil {
		return nil
	}
	return g.streamCache[idx]
}

func (g *Game) evictStreamFrames() {
	if !g.streaming || len(g.streamCache) == 0 {
		return
	}
	keepBack := g.streamCacheBack
	if keepBack < 0 {
		keepBack = 0
	}
	minKeep := g.frameIdx - keepBack
	if minKeep < 0 {
		minKeep = 0
	}
	if minKeep <= g.streamMinFrame {
		return
	}
	for idx := range g.streamCache {
		if idx < minKeep {
			delete(g.streamCache, idx)
		}
	}
	g.streamMinFrame = minKeep
}

func (g *Game) resetWaveWindow() {
	window := waveformPoints
	if window < 1 {
		window = 1
	}
	totalFrames := len(g.audioPCM) / 4
	if totalFrames > 0 && window > totalFrames {
		window = totalFrames
	}
	g.waveWindowSamps = window
}

func (g *Game) adjustWaveWindow(factor float64) {
	if factor <= 0 {
		return
	}
	if g.waveWindowSamps <= 0 {
		g.resetWaveWindow()
		return
	}
	next := int(float64(g.waveWindowSamps) * factor)
	if next < 1 {
		next = 1
	}
	totalFrames := len(g.audioPCM) / 4
	if totalFrames > 0 && next > totalFrames {
		next = totalFrames
	}
	g.waveWindowSamps = next
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
		if g.waveWindowSamps <= 0 {
			g.resetWaveWindow()
		}
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
framePump:
	for g.frameCh != nil {
		if g.streamAheadLimit() > 0 && g.streamBufferedAhead() >= g.streamAheadLimit() {
			break framePump
		}
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

func (g *Game) restartStreamFromBeginning() bool {
	if !g.streaming || g.streamSourcePath == "" {
		return false
	}
	frameCh, audioCh, errCh, err := startVlixV2StreamWorkers(g.streamSourcePath, g.streamHeader, g.streamDecodeAudio && g.audioPlayer == nil)
	if err != nil {
		fmt.Fprintln(os.Stderr, "[!] Stream replay restart failed:", err)
		return false
	}
	cacheCap := g.streamPrebuffer + g.streamCacheBack + g.streamMaxAhead + 8
	if cacheCap < 16 {
		cacheCap = 16
	}
	g.frameCh = frameCh
	g.audioCh = audioCh
	g.errCh = errCh
	g.streamCache = make(map[int]*ebiten.Image, cacheCap)
	g.streamMinFrame = 0
	g.readyFrames = 0
	g.maxFrameIdx = -1
	g.frameIdx = 0
	g.streamDone = false
	g.streamStarted = false
	g.playing = false
	g.accum = 0
	g.lastTick = time.Now()
	if g.audioPlayer != nil {
		_ = g.audioPlayer.SetPosition(0)
		g.pauseAudio()
	}
	return true
}

func (g *Game) Update() error {
	if g.streaming {
		if err := g.pumpStream(); err != nil {
			return err
		}
		if !g.streamDone {
			if g.streamRealtime {
				if !g.streamStarted {
					need := g.streamPrebuffer
					if need < 1 {
						need = 1
					}
					if g.totalFrames > 0 && need > g.totalFrames {
						need = g.totalFrames
					}
					if g.readyFrames >= need {
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
			} else {
				if g.playing {
					g.playing = false
					g.pauseAudio()
				}
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
	if inpututil.IsKeyJustPressed(ebiten.KeyD) && !ebiten.IsKeyPressed(ebiten.KeyR) && !ebiten.IsKeyPressed(ebiten.KeyT) {
		g.showDebug = !g.showDebug
	}
	if inpututil.IsKeyJustPressed(ebiten.KeyR) && !ebiten.IsKeyPressed(ebiten.KeyD) {
		if g.visualizeAudio {
			g.resetWaveWindow()
		} else {
			fitToWindow(g)
		}
	}
	hasTimeline := g.totalFrameCount() > 1 || g.audioPlayer != nil
	if hasTimeline {
		if inpututil.IsKeyJustPressed(ebiten.KeyL) {
			g.loopPlayback = !g.loopPlayback
		}
		if inpututil.IsKeyJustPressed(ebiten.KeySpace) {
			if g.playing {
				g.playing = false
				g.pauseAudio()
			} else {
				if g.streaming && !g.streamDone && !g.streamRealtime {
					g.playing = false
					g.pauseAudio()
					g.lastTick = time.Now()
					g.accum = 0
				} else {
					canStart := true
					if g.streaming && g.streamDone {
						playable := g.playableFrames()
						atTail := playable > 0 && g.frameIdx >= playable-1
						if atTail && g.streamMinFrame > 0 {
							if g.restartStreamFromBeginning() {
								canStart = false
							}
						}
					}
					if g.streaming && !g.streamDone && g.streamRealtime && g.readyFrames <= 1 {
						canStart = false
						g.playing = false
						g.pauseAudio()
						g.lastTick = time.Now()
						g.accum = 0
					}
					if canStart {
						playable := g.playableFrames()
						if playable > 0 && g.frameIdx >= playable-1 {
							if g.streaming && g.streamMinFrame > 0 {
								g.frameIdx = g.streamMinFrame
							} else {
								g.frameIdx = 0
							}
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
			if g.streaming && g.streamDone && g.streamMinFrame > 0 {
				g.restartStreamFromBeginning()
			} else {
				g.frameIdx = 0
				if g.streaming && g.frameIdx < g.streamMinFrame {
					g.frameIdx = g.streamMinFrame
				}
			}
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
							if g.loopPlayback {
								g.loopToBeginning()
							} else {
								g.frameIdx = playable - 1
								g.playing = false
								g.pauseAudio()
								g.accum = 0
							}
						} else {
							g.frameIdx = playable - 1
						}
					} else if idx >= 0 {
						g.frameIdx = idx
					}
				}
			} else if g.audioDuration > 0 && g.audioPlayer.Position() >= g.audioDuration {
				if g.loopPlayback {
					g.loopToBeginning()
				} else {
					g.playing = false
					g.pauseAudio()
				}
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
						if g.loopPlayback {
							g.loopToBeginning()
						} else {
							g.frameIdx = playable - 1
							g.playing = false
							g.accum = 0
						}
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
	if g.streaming {
		g.evictStreamFrames()
	}
	if g.streaming && g.playing && g.audioPlayer != nil {
		playable := g.playableFrames()
		atDecodedTail := playable <= 0 || g.frameIdx >= playable-1
		if !g.streamDone && atDecodedTail {
			g.pauseAudio()
		} else {
			g.playAudio()
		}
		g.syncAudioToFrameLocked(25 * time.Millisecond)
	}
	mx, my := ebiten.CursorPosition()
	_, dy := ebiten.Wheel()
	if dy != 0 {
		if g.visualizeAudio {
			factor := math.Pow(1.1, -dy)
			g.adjustWaveWindow(factor)
		} else {
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
	points := waveformPoints
	if points > w {
		points = w
	}
	if points <= 0 {
		screen.DrawImage(g.waveformBuffer, nil)
		return
	}
	windowSamples := g.waveWindowSamps
	if windowSamples <= 0 {
		windowSamples = waveformPoints
	}
	if windowSamples < points {
		windowSamples = points
	}
	if totalFrames > 0 && windowSamples > totalFrames {
		windowSamples = totalFrames
	}
	g.waveWindowSamps = windowSamples
	samplesPerPoint := windowSamples / points
	if samplesPerPoint < 1 {
		samplesPerPoint = 1
	}
	start := curFrame - windowSamples/2
	mean := int32(0)
	peakAbs := int32(1)
	rawMin := int16(32767)
	rawMax := int16(-32768)
	if windowSamples > 0 {
		var sum int64
		valid := 0
		for i := 0; i < windowSamples; i++ {
			sampleIdx := start + i
			if sampleIdx < 0 || sampleIdx >= totalFrames {
				continue
			}
			off := sampleIdx * 4
			l := int16(binary.LittleEndian.Uint16(g.audioPCM[off : off+2]))
			r := int16(binary.LittleEndian.Uint16(g.audioPCM[off+2 : off+4]))
			sample := int16((int32(l) + int32(r)) / 2)
			sum += int64(sample)
			valid++
			if sample < rawMin {
				rawMin = sample
			}
			if sample > rawMax {
				rawMax = sample
			}
		}
		if valid > 0 {
			mean = int32(sum / int64(valid))
		} else {
			rawMin = 0
			rawMax = 0
		}
		for i := 0; i < windowSamples; i++ {
			sampleIdx := start + i
			if sampleIdx < 0 || sampleIdx >= totalFrames {
				continue
			}
			off := sampleIdx * 4
			l := int16(binary.LittleEndian.Uint16(g.audioPCM[off : off+2]))
			r := int16(binary.LittleEndian.Uint16(g.audioPCM[off+2 : off+4]))
			sample := int16((int32(l) + int32(r)) / 2)
			diff := int32(sample) - mean
			if diff < 0 {
				diff = -diff
			}
			if diff > peakAbs {
				peakAbs = diff
			}
		}
	}
	var sliceWidth float32
	if points > 1 {
		sliceWidth = float32(w-1) / float32(points-1)
	}
	x := float32(0)
	var prevX, prevY float32
	for i := 0; i < points; i++ {
		base := start + i*samplesPerPoint
		if samplesPerPoint == 1 {
			sampleIdx := base
			var sample int16
			if sampleIdx >= 0 && sampleIdx < totalFrames {
				off := sampleIdx * 4
				l := int16(binary.LittleEndian.Uint16(g.audioPCM[off : off+2]))
				r := int16(binary.LittleEndian.Uint16(g.audioPCM[off+2 : off+4]))
				sample = int16((int32(l) + int32(r)) / 2)
			}
			diff := int32(sample) - mean
			v := float32(diff) / float32(peakAbs)
			if v > 1 {
				v = 1
			} else if v < -1 {
				v = -1
			}
			y := (v + 1) * float32(h) / 2
			if i > 0 {
				vector.StrokeLine(g.waveformBuffer, prevX, prevY, x, y, float32(waveformLineWidth), color.RGBA{255, 0, 0, 255}, true)
			}
			prevX, prevY = x, y
		} else {
			minDiff := int32(math.MaxInt32)
			maxDiff := int32(math.MinInt32)
			haveSample := false
			for j := 0; j < samplesPerPoint; j++ {
				sampleIdx := base + j
				var sample int16
				if sampleIdx < 0 || sampleIdx >= totalFrames {
					continue
				}
				off := sampleIdx * 4
				l := int16(binary.LittleEndian.Uint16(g.audioPCM[off : off+2]))
				r := int16(binary.LittleEndian.Uint16(g.audioPCM[off+2 : off+4]))
				sample = int16((int32(l) + int32(r)) / 2)
				haveSample = true
				diff := int32(sample) - mean
				if diff < minDiff {
					minDiff = diff
				}
				if diff > maxDiff {
					maxDiff = diff
				}
			}
			if !haveSample {
				minDiff = 0
				maxDiff = 0
			}
			vMin := float32(minDiff) / float32(peakAbs)
			vMax := float32(maxDiff) / float32(peakAbs)
			if vMin < -1 {
				vMin = -1
			}
			if vMax > 1 {
				vMax = 1
			}
			yMin := (vMin + 1) * float32(h) / 2
			yMax := (vMax + 1) * float32(h) / 2
			if yMin == yMax {
				if yMin > 0 {
					yMin -= 1
				}
				if yMax < float32(h-1) {
					yMax += 1
				}
			}
			vector.StrokeLine(g.waveformBuffer, x, yMin, x, yMax, float32(waveformLineWidth), color.RGBA{255, 0, 0, 255}, true)
		}
		x += sliceWidth
	}
	g.waveDebug = fmt.Sprintf("Wave: mean=%d peakAbs=%d rawMin=%d rawMax=%d spp=%d pts=%d win=%d",
		mean, peakAbs, rawMin, rawMax, samplesPerPoint, points, windowSamples)
	screen.DrawImage(g.waveformBuffer, nil)
}

func (g *Game) Draw(screen *ebiten.Image) {
	screen.Fill(color.Black)
	if g.visualizeAudio {
		g.drawWaveform(screen)
	} else {
		shapeComboHeld := ebiten.IsKeyPressed(ebiten.KeyD) && ebiten.IsKeyPressed(ebiten.KeyR)
		trixComboHeld := ebiten.IsKeyPressed(ebiten.KeyD) && ebiten.IsKeyPressed(ebiten.KeyT)
		op := &ebiten.DrawImageOptions{}
		op.GeoM.Scale(g.scale, g.scale)
		op.GeoM.Translate(g.offsetX, g.offsetY)
		if g.streaming {
			if img := g.streamFrameAt(g.frameIdx); img != nil {
				screen.DrawImage(img, op)
			}
		} else if len(g.frames) > 0 && g.frameIdx >= 0 && g.frameIdx < len(g.frames) {
			if g.frames[g.frameIdx] != nil {
				screen.DrawImage(g.frames[g.frameIdx], op)
			}
		}
		if g.shapeOverlay != nil && shapeComboHeld {
			screen.DrawImage(g.shapeOverlay, op)
		}
		if g.trixOverlay != nil && trixComboHeld {
			screen.DrawImage(g.trixOverlay, op)
			ebitenutil.DebugPrint(screen, fmt.Sprintf("D+T: TRIX block map  orange=BLIX-style (%d)  cyan=DCT (%d)", g.trixMethodCounts[0], g.trixMethodCounts[1]))
		}
		if g.shapeOverlay == nil && shapeComboHeld {
			msg := "D+R held: no CLIX shape primitives found in this image"
			if g.clixMode != "" {
				msg = msg + " (MODE=" + strings.ToUpper(g.clixMode) + ")"
			}
			ebitenutil.DebugPrint(screen, msg)
		}
		if g.trixOverlay == nil && trixComboHeld {
			ebitenutil.DebugPrint(screen, "D+T held: no TRIX block-method map for this image")
		}
	}
	if g.showDebug {
		if g.visualizeAudio {
			posSec := 0.0
			if g.audioPlayer != nil {
				posSec = g.audioPlayer.Position().Seconds()
			}
			winSec := 0.0
			if g.audioSampleRate > 0 {
				winSec = float64(g.waveWindowSamps) / float64(g.audioSampleRate)
			}
			msg := fmt.Sprintf("Wave win: %d (%.3fs)  Pos: %.3fs", g.waveWindowSamps, winSec, posSec)
			if g.waveDebug != "" {
				msg = msg + "\n" + g.waveDebug
			}
			ebitenutil.DebugPrint(screen, msg)
		} else {
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
			if g.shapeOverlay != nil {
				msg = msg + "\nHold D+R: highlight each shape instance with a unique color"
			}
			if g.trixOverlay != nil {
				msg = msg + fmt.Sprintf("\nHold D+T: TRIX blocks, BLIX-style=%d DCT=%d", g.trixMethodCounts[0], g.trixMethodCounts[1])
			}
			if g.clixMode != "" {
				msg = msg + "\nCLIX mode: " + strings.ToUpper(g.clixMode)
				if g.clixModeFallback && g.clixModeRaw != "" {
					msg = msg + " (unknown header mode \"" + g.clixModeRaw + "\" -> SAFE compatibility)"
				}
			}
			ebitenutil.DebugPrint(screen, msg)
		}
	}
	if !g.showDebug && g.streaming && !g.streamDone {
		if g.totalFrames > 0 {
			ebitenutil.DebugPrint(screen, fmt.Sprintf("Video decoding... %d/%d", g.readyFrames, g.totalFrames))
		} else {
			ebitenutil.DebugPrint(screen, fmt.Sprintf("Video decoding... %d/?", g.readyFrames))
		}
	}
}

func (g *Game) Layout(w, h int) (int, int) {
	g.winWidth, g.winHeight = w, h
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

func printViewerHotkeys() {
	fmt.Println("Viewer hotkeys:")
	fmt.Println("  Space: Play/Pause")
	fmt.Println("  L: Toggle infinite loop at end")
	fmt.Println("  Left/Right: Step frame")
	fmt.Println("  Home/End: Jump to start/end")
	fmt.Println("  R: Reset fit to window")
	fmt.Println("  Hold D+R: Highlight each CLIX shape instance with a unique color")
	fmt.Println("  Hold D+T: Highlight TRIX block method map")
	fmt.Println("  Mouse wheel: Zoom")
	fmt.Println("  Left drag: Pan")
	fmt.Println("  Audio: Mouse wheel zooms waveform, R resets window")
	fmt.Println("")
}

func printViewerVersionInfo() {
	fmt.Printf("CABLE Viewer %s\n", viewerVersion)
	fmt.Printf("Vanta: %s\n", viewerVantaVersion)
	fmt.Printf("Formats: CLIX %s  BLIX %s  TRIX %s  VLIX %s  ALIX %s\n", clixVersion, blixVersion, trixVersion, vlixVersion, alixVersion)
	fmt.Printf("Platform: %s/%s  Go: %s\n", runtime.GOOS, runtime.GOARCH, runtime.Version())
	fmt.Printf("Runtime: CPUs=%d  GOMAXPROCS=%d\n", runtime.NumCPU(), runtime.GOMAXPROCS(0))
	fmt.Printf("Backends: IDCT=%s  Compute=%s\n", idctBackendName(), computeBackendName())
	if note := computeBackendNote(); note != "" {
		fmt.Printf("Compute note: %s\n", note)
	}
	fmt.Printf("Streaming cache defaults: keep-back=%d..%d  max-ahead=%d..%d\n", streamCacheBackMinFrames, streamCacheBackMaxFrames, streamMaxAheadMinFrames, streamMaxAheadMaxFrames)
}

func main() {
	usage := "Usage: clix view [--version] [--simd-backend] [--compute=auto|cpu|cuda|vulkan] [--ahead-seconds=N] [--prebuffer-seconds=N] <file.clix|file.blix|file.trix|file.vlix|file.alix> [file.alix]"
	rawArgs := os.Args[1:]
	args := make([]string, 0, len(rawArgs))
	showSIMDBackend := false
	showVersion := false
	computeSpec := "auto"
	aheadSeconds := streamMaxAheadSeconds
	prebufferSeconds := streamPrebufferSeconds
	parseSeconds := func(name, s string) float64 {
		v, e := strconv.ParseFloat(strings.TrimSpace(s), 64)
		if e != nil || v < 0 {
			fmt.Fprintf(os.Stderr, "Error: invalid value for %s (expected seconds >= 0)\n", name)
			fmt.Println(usage)
			os.Exit(2)
		}
		return v
	}
	for i := 0; i < len(rawArgs); i++ {
		a := rawArgs[i]
		if strings.HasPrefix(a, "-") {
			switch a {
			case "--simd-backend":
				showSIMDBackend = true
			case "--version":
				showVersion = true
			case "--compute":
				if i+1 >= len(rawArgs) {
					fmt.Fprintln(os.Stderr, "Error: missing value for --compute")
					fmt.Println(usage)
					os.Exit(2)
				}
				i++
				computeSpec = rawArgs[i]
			case "--ahead-seconds":
				if i+1 >= len(rawArgs) {
					fmt.Fprintln(os.Stderr, "Error: missing value for --ahead-seconds")
					fmt.Println(usage)
					os.Exit(2)
				}
				i++
				aheadSeconds = parseSeconds("--ahead-seconds", rawArgs[i])
			case "--prebuffer-seconds":
				if i+1 >= len(rawArgs) {
					fmt.Fprintln(os.Stderr, "Error: missing value for --prebuffer-seconds")
					fmt.Println(usage)
					os.Exit(2)
				}
				i++
				prebufferSeconds = parseSeconds("--prebuffer-seconds", rawArgs[i])
			case "-h", "--help":
				fmt.Println(usage)
				os.Exit(0)
			default:
				if strings.HasPrefix(a, "--compute=") {
					computeSpec = strings.TrimSpace(strings.TrimPrefix(a, "--compute="))
					continue
				}
				if strings.HasPrefix(a, "--ahead-seconds=") {
					aheadSeconds = parseSeconds("--ahead-seconds", strings.TrimPrefix(a, "--ahead-seconds="))
					continue
				}
				if strings.HasPrefix(a, "--prebuffer-seconds=") {
					prebufferSeconds = parseSeconds("--prebuffer-seconds", strings.TrimPrefix(a, "--prebuffer-seconds="))
					continue
				}
				fmt.Fprintf(os.Stderr, "Error: unknown flag %s\n", a)
				fmt.Println(usage)
				os.Exit(2)
			}
			continue
		}
		args = append(args, a)
	}
	if err := setComputeBackend(computeSpec); err != nil {
		fmt.Fprintln(os.Stderr, "Error:", err)
		fmt.Println(usage)
		os.Exit(2)
	}
	if showVersion {
		if len(args) > 0 {
			fmt.Fprintln(os.Stderr, "Error: --version cannot be combined with an input path.")
			fmt.Println(usage)
			os.Exit(2)
		}
		printViewerVersionInfo()
		return
	}
	if note := computeBackendNote(); note != "" {
		fmt.Fprintf(os.Stderr, "[!] Compute backend %q requested; using fallback (%s)\n", computeBackendName(), note)
	}
	if len(args) < 1 || len(args) > 2 {
		fmt.Println(usage)
		os.Exit(1)
	}
	var vlixPath, audioPath, imagePath string
	vlixCodec := ""
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
		case ".blix", ".clix", ".trix":
			imagePath = args[0]
		default:
			fmt.Fprintln(os.Stderr, "Error: unsupported file type")
			os.Exit(2)
		}
	}
	audioOnly := audioPath != "" && vlixPath == "" && imagePath == ""
	var frames []image.Image
	var fps float64
	var audioBlob []byte
	var clixShapeIDs []uint32
	var clixMeta clixDecodeMeta
	var trixMethods []byte
	var trixBlockDim int
	var err error
	var streaming bool
	var streamHdr *vlixHeader
	var streamDecodeAudio bool
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
			vlixCodec = "VLIX2"
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
			streamDecodeAudio = audioPath == "" && hdr.audioBytes > 0
			vs.Close()
			frameCh, audioCh, errCh, err = startVlixV2StreamWorkers(vlixPath, hdr, streamDecodeAudio)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(2)
			}
		} else {
			vlixCodec = vs.hdr.codec
			vs.Close()
			decodeStart := time.Now()
			frames, fps, audioBlob, err = decodeVlix(vlixPath)
			if err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(2)
			}
			fmt.Printf("[*] %s decode finished in %s\n", vlixCodec, time.Since(decodeStart).Round(time.Millisecond))
		}
	}
	if imagePath != "" {
		lowerImagePath := strings.ToLower(imagePath)
		if strings.HasSuffix(lowerImagePath, ".blix") {
			var img image.Image
			img, err = decodeBlixToImage(imagePath)
			if err == nil {
				frames = []image.Image{img}
			}
		} else if strings.HasSuffix(lowerImagePath, ".trix") {
			var img image.Image
			img, trixMethods, trixBlockDim, err = decodeTrixToImage(imagePath)
			if err == nil {
				frames = []image.Image{img}
			}
		} else {
			var img image.Image
			img, clixShapeIDs, clixMeta, err = decodeClixToImage(imagePath)
			if err == nil {
				frames = []image.Image{img}
			}
		}
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(2)
		}
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
	waveWindowSamps := 0
	if len(audioPCM) > 0 {
		window := waveformPoints
		if window < 1 {
			window = 1
		}
		totalFrames := len(audioPCM) / 4
		if totalFrames > 0 && window > totalFrames {
			window = totalFrames
		}
		waveWindowSamps = window
	}
	var game *Game
	if streaming && streamHdr != nil {
		totalFrames := streamHdr.framesExpected
		autoplay := totalFrames > 1 || audioPlayer != nil
		streamRealtime := streamHdr.fps > 0
		streamCacheBack := int(math.Round(streamHdr.fps * 0.5))
		if streamCacheBack < streamCacheBackMinFrames {
			streamCacheBack = streamCacheBackMinFrames
		}
		if streamCacheBack > streamCacheBackMaxFrames {
			streamCacheBack = streamCacheBackMaxFrames
		}
		streamMaxAhead := int(math.Round(streamHdr.fps * aheadSeconds))
		if streamMaxAhead < streamMaxAheadMinFrames {
			streamMaxAhead = streamMaxAheadMinFrames
		}
		if streamMaxAhead > streamMaxAheadMaxFrames {
			streamMaxAhead = streamMaxAheadMaxFrames
		}
		if totalFrames > 0 {
			remaining := totalFrames - 1
			if streamMaxAhead > remaining {
				streamMaxAhead = remaining
			}
		}
		if streamMaxAhead < 1 {
			streamMaxAhead = 1
		}
		streamPrebuffer := int(math.Round(streamHdr.fps * prebufferSeconds))
		if streamPrebuffer < 4 {
			streamPrebuffer = 4
		}
		if streamPrebuffer > streamMaxAhead {
			streamPrebuffer = streamMaxAhead
		}
		if totalFrames > 0 && streamPrebuffer > totalFrames {
			streamPrebuffer = totalFrames
		}
		streamMaxAheadPaused := int(math.Round(streamHdr.fps * 20.0))
		if streamMaxAheadPaused < streamMaxAhead*3 {
			streamMaxAheadPaused = streamMaxAhead * 3
		}
		if streamMaxAheadPaused > streamPausedAheadMaxCap {
			streamMaxAheadPaused = streamPausedAheadMaxCap
		}
		if totalFrames > 0 {
			remaining := totalFrames - 1
			if streamMaxAheadPaused > remaining {
				streamMaxAheadPaused = remaining
			}
		}
		if streamMaxAheadPaused < streamMaxAhead {
			streamMaxAheadPaused = streamMaxAhead
		}
		game = &Game{
			fps:                  streamHdr.fps,
			playing:              false,
			audioCtx:             audioCtx,
			audioPlayer:          audioPlayer,
			audioDuration:        audioDuration,
			audioPCM:             audioPCM,
			audioSampleRate:      audioSampleRate,
			visualizeAudio:       audioOnly,
			waveWindowSamps:      waveWindowSamps,
			imgWidth:             streamHdr.width,
			imgHeight:            streamHdr.height,
			streaming:            true,
			streamRealtime:       streamRealtime,
			streamPrebuffer:      streamPrebuffer,
			streamCacheBack:      streamCacheBack,
			streamMaxAhead:       streamMaxAhead,
			streamMaxAheadPaused: streamMaxAheadPaused,
			totalFrames:          totalFrames,
			streamCache:          make(map[int]*ebiten.Image, streamPrebuffer+streamCacheBack+streamMaxAhead+8),
			frameCh:              frameCh,
			audioCh:              audioCh,
			errCh:                errCh,
			streamAuto:           autoplay,
			streamSourcePath:     vlixPath,
			streamHeader:         *streamHdr,
			streamDecodeAudio:    streamDecodeAudio,
		}
	} else {
		b := frames[0].Bounds()
		ebFrames := make([]*ebiten.Image, 0, len(frames))
		for _, f := range frames {
			ebFrames = append(ebFrames, ebiten.NewImageFromImage(f))
		}
		shapeOverlay := (*ebiten.Image)(nil)
		clixMode := ""
		clixModeRaw := ""
		clixModeFallback := false
		if imagePath != "" && strings.HasSuffix(strings.ToLower(imagePath), ".clix") {
			shapeOverlay = buildShapeDebugOverlay(clixShapeIDs, b.Dx(), b.Dy())
			clixMode = clixMeta.mode
			clixModeRaw = clixMeta.modeRaw
			clixModeFallback = clixMeta.modeFallback
		}
		trixOverlay, trixCounts := buildTrixDebugOverlay(trixMethods, b.Dx(), b.Dy(), trixBlockDim)
		autoplay := len(ebFrames) > 1 || audioPlayer != nil
		game = &Game{
			frames:           ebFrames,
			fps:              fps,
			playing:          autoplay,
			audioCtx:         audioCtx,
			audioPlayer:      audioPlayer,
			audioDuration:    audioDuration,
			audioPCM:         audioPCM,
			audioSampleRate:  audioSampleRate,
			visualizeAudio:   audioOnly,
			waveWindowSamps:  waveWindowSamps,
			imgWidth:         b.Dx(),
			imgHeight:        b.Dy(),
			shapeOverlay:     shapeOverlay,
			trixOverlay:      trixOverlay,
			trixMethodCounts: trixCounts,
			clixMode:         clixMode,
			clixModeRaw:      clixModeRaw,
			clixModeFallback: clixModeFallback,
		}
	}
	if game != nil && game.playing && game.audioPlayer != nil && (!game.streaming || game.streamDone) {
		game.audioPlayer.Play()
	}
	printViewerHotkeys()
	if streaming && streamHdr != nil {
		fmt.Printf("[*] Realtime decode playback: ON (fps=%.3g, prebuffer=%d frames)\n", streamHdr.fps, game.streamPrebuffer)
		fmt.Printf("[*] Streaming frame cache: keep-back=%d, max-ahead(play)=%d, max-ahead(pause)=%d\n", game.streamCacheBack, game.streamMaxAhead, game.streamMaxAheadPaused)
	}
	if showSIMDBackend {
		if vlixPath != "" && vlixCodec == "VLIX2" {
			fmt.Printf("VLIX2 IDCT backend: %s\n", idctBackendName())
			fmt.Printf("Compute backend: %s\n\n", computeBackendName())
		} else if vlixPath != "" {
			fmt.Printf("VLIX codec: %s (SIMD backend reporting applies to VLIX2)\n", vlixCodec)
			fmt.Printf("Compute backend: %s\n\n", computeBackendName())
		} else {
			fmt.Printf("VLIX2 IDCT backend: %s\n", idctBackendName())
			fmt.Printf("Compute backend: %s\n\n", computeBackendName())
		}
	}
	ebiten.SetWindowSize(800, 600)
	ebiten.SetWindowResizingMode(ebiten.WindowResizingModeEnabled)
	ebiten.SetWindowTitle("CABLE Viewer 2.15")
	if err := ebiten.RunGame(game); err != nil {
		panic(err)
	}
}
