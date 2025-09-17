package main

import (
	"bufio"
	"bytes"
	"errors"
	"fmt"
	"image"
	"image/color"
	"image/draw"
	"image/jpeg"
	"image/png"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strconv"
	"strings"

	_ "image/gif"

	"github.com/klauspost/compress/zstd"
	"github.com/soniakeys/quant/median"
	"github.com/spf13/pflag"
)

type RGBA struct{ R, G, B, A uint8 }

func (p RGBA) toColor() color.NRGBA { return color.NRGBA{R: p.R, G: p.G, B: p.B, A: p.A} }
func fromColor(c color.Color) RGBA {
	r, g, b, a := c.RGBA()
	return RGBA{uint8(r >> 8), uint8(g >> 8), uint8(b >> 8), uint8(a >> 8)}
}

var PURE_COLOR_TOKENS = map[RGBA]string{
	{0, 0, 0, 255}:       "K",
	{255, 255, 255, 255}: "W",
	{255, 0, 0, 255}:     "R",
	{0, 255, 0, 255}:     "G",
	{0, 0, 255, 255}:     "B",
	{255, 255, 0, 255}:   "Y",
	{255, 165, 0, 255}:   "O",
	{128, 0, 128, 255}:   "P",
}

var PURE_LOOKUP = func() map[string]RGBA {
	m := make(map[string]RGBA, len(PURE_COLOR_TOKENS))
	for k, v := range PURE_COLOR_TOKENS {
		m[v] = k
	}
	return m
}()

func tokenizeLine(s string) ([]string, error) {
	var tokens []string
	i := 0
	n := len(s)
	for i < n {
		for i < n && isSpace(s[i]) {
			i++
		}
		if i >= n {
			break
		}
		if s[i] == '(' {
			depth := 0
			j := i
			for j < n {
				c := s[j]
				if c == '(' {
					depth++
				} else if c == ')' {
					depth--
					if depth == 0 {
						j++
						break
					}
				}
				j++
			}
			if depth != 0 {
				return nil, fmt.Errorf("unbalanced parentheses starting at: %q", s[i:])
			}
			k := j
			if k < n && s[k] == '*' {
				k++
				start := k
				for k < n && isDigit(s[k]) {
					k++
				}
				if start == k {
					return nil, errors.New("expected integer after '*'")
				}
				tokens = append(tokens, s[i:k])
				i = k
			} else {
				tokens = append(tokens, s[i:j])
				i = j
			}
		} else {
			j := i
			for j < n && !isSpace(s[j]) {
				j++
			}
			tokens = append(tokens, s[i:j])
			i = j
		}
	}
	return tokens, nil
}

func expandGroupToken(token string) ([]string, error) {
	token = strings.TrimSpace(token)
	count := 1
	var inner string
	if strings.HasSuffix(token, ")") && !strings.Contains(token, ")*") {
		inner = token[1 : len(token)-1]
	} else if strings.Contains(token, ")*") {
		pos := strings.LastIndex(token, ")*")
		inner = token[1:pos]
		cntStr := token[pos+2:]
		if !isAllDigits(cntStr) {
			return nil, fmt.Errorf("bad repeat count in token: %s", token)
		}
		v, _ := strconv.Atoi(cntStr)
		count = v
	} else {
		r := strings.LastIndexByte(token, ')')
		if r == -1 {
			return nil, fmt.Errorf("malformed group token: %s", token)
		}
		inner = token[1:r]
		tail := token[r+1:]
		if strings.HasPrefix(tail, "*") {
			cnt := tail[1:]
			if !isAllDigits(cnt) {
				return nil, fmt.Errorf("bad repeat count in token: %s", token)
			}
			v, _ := strconv.Atoi(cnt)
			count = v
		}
	}
	innerTokens, err := tokenizeLine(inner)
	if err != nil {
		return nil, err
	}
	expandedInner, err := expandTokens(innerTokens)
	if err != nil {
		return nil, err
	}
	out := make([]string, 0, len(expandedInner)*count)
	for i := 0; i < count; i++ {
		out = append(out, expandedInner...)
	}
	return out, nil
}

func expandSimpleOrRepeatToken(token string) []string {
	if strings.Contains(token, "*") && !strings.HasPrefix(token, "(") {
		i := strings.LastIndexByte(token, '*')
		if i >= 0 && i+1 < len(token) {
			base := token[:i]
			cnt := token[i+1:]
			if isAllDigits(cnt) {
				n, _ := strconv.Atoi(cnt)
				if n > 0 {
					out := make([]string, n)
					for k := 0; k < n; k++ {
						out[k] = base
					}
					return out
				}
			}
		}
	}
	return []string{token}
}

func expandTokens(tokens []string) ([]string, error) {
	out := make([]string, 0, len(tokens))
	for _, t := range tokens {
		if t == "" {
			continue
		}
		if strings.HasPrefix(t, "(") {
			exp, err := expandGroupToken(t)
			if err != nil {
				return nil, err
			}
			out = append(out, exp...)
		} else {
			out = append(out, expandSimpleOrRepeatToken(t)...)
		}
	}
	return out, nil
}

func rleTokens(tokens []string) []string {
	if len(tokens) == 0 {
		return nil
	}
	out := make([]string, 0, len(tokens))
	prev := tokens[0]
	count := 1
	for _, t := range tokens[1:] {
		if t == prev {
			count++
		} else {
			if count > 1 {
				out = append(out, fmt.Sprintf("%s*%d", prev, count))
			} else {
				out = append(out, prev)
			}
			prev = t
			count = 1
		}
	}
	if count > 1 {
		out = append(out, fmt.Sprintf("%s*%d", prev, count))
	} else {
		out = append(out, prev)
	}
	return out
}

func sequenceRLE(tokens []string, maxSeqLen int) []string {
	if maxSeqLen <= 0 {
		maxSeqLen = 64
	}
	out := []string{}
	i := 0
	n := len(tokens)
	for i < n {
		bestLen, bestCount := 1, 1
		var bestSeq []string
		limit := maxSeqLen
		if rem := n - i; rem < limit {
			limit = rem
		}
		for L := 1; L <= limit; L++ {
			seq := tokens[i : i+L]
			count := 1
			j := i + L
			for j+L <= n && equalSlice(tokens[j:j+L], seq) {
				count++
				j += L
			}
			if count > 1 && L*count > bestLen*bestCount {
				bestLen, bestCount, bestSeq = L, count, seq
			}
		}
		if bestCount > 1 {
			out = append(out, fmt.Sprintf("(%s)*%d", strings.Join(bestSeq, " "), bestCount))
			i += bestLen * bestCount
		} else {
			out = append(out, tokens[i])
			i++
		}
	}
	return out
}

func equalSlice(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func detectBackground(pixels []RGBA) (RGBA, float64) {
	counts := make(map[uint32]int)
	var pack = func(p RGBA) uint32 {
		return uint32(p.R)<<24 | uint32(p.G)<<16 | uint32(p.B)<<8 | uint32(p.A)
	}
	var unpack = func(u uint32) RGBA {
		return RGBA{uint8(u >> 24), uint8(u >> 16), uint8(u >> 8), uint8(u)}
	}
	for _, px := range pixels {
		counts[pack(px)]++
	}
	var maxKey uint32
	maxCnt := -1
	for k, c := range counts {
		if c > maxCnt {
			maxCnt = c
			maxKey = k
		}
	}
	bg := unpack(maxKey)
	share := float64(maxCnt) / float64(len(pixels))
	return bg, share
}

func applyRound(px RGBA, step int) RGBA {
	if step <= 0 {
		return px
	}
	rr := func(v uint8) uint8 {
		q := int(float64(v)/float64(step) + 0.5)
		q *= step
		if q < 0 {
			q = 0
		}
		if q > 255 {
			q = 255
		}
		return uint8(q)
	}
	return RGBA{rr(px.R), rr(px.G), rr(px.B), px.A}
}

func withinDelta(p1, p2 RGBA, thr int) bool {
	ad := func(a, b uint8) int {
		if a > b {
			return int(a - b)
		}
		return int(b - a)
	}
	return ad(p1.R, p2.R) <= thr &&
		ad(p1.G, p2.G) <= thr &&
		ad(p1.B, p2.B) <= thr &&
		ad(p1.A, p2.A) <= thr
}

func rgbaToToken(px RGBA) string {
	if t, ok := PURE_COLOR_TOKENS[px]; ok {
		return t
	}
	return fmt.Sprintf("R%dG%dB%dA%d", px.R, px.G, px.B, px.A)
}

var rgbaPartRe = regexp.MustCompile(`[RGBA]\d+`)

func tokenToRGBA(tok string, bg *RGBA, prev *RGBA) (RGBA, error) {
	switch tok {
	case "S":
		if prev == nil {
			return RGBA{}, errors.New("encountered 'S' before any previous pixel")
		}
		return *prev, nil
	case "BG":
		if bg == nil {
			return RGBA{}, errors.New("BG token encountered but no BG= in header")
		}
		return *bg, nil
	default:
		if px, ok := PURE_LOOKUP[tok]; ok {
			return px, nil
		}
		parts := rgbaPartRe.FindAllString(tok, -1)
		if len(parts) == 0 {
			return RGBA{}, fmt.Errorf("unexpected token: %q", tok)
		}
		m := map[byte]int{}
		for _, p := range parts {
			ch := p[0]
			num := p[1:]
			v, err := strconv.Atoi(num)
			if err != nil {
				return RGBA{}, fmt.Errorf("malformed token segment: %s", tok)
			}
			m[ch] = v
		}
		r := m['R']
		g := m['G']
		b := m['B']
		a := m['A']
		if _, ok := m['A']; !ok {
			a = 255
		}
		clamp := func(v int) uint8 {
			if v < 0 {
				return 0
			}
			if v > 255 {
				return 255
			}
			return uint8(v)
		}
		return RGBA{clamp(r), clamp(g), clamp(b), clamp(a)}, nil
	}
}

func blockSmooth(img image.Image, block int, varThreshold float64) image.Image {
	if block <= 1 {
		return img
	}
	b := img.Bounds()
	out := image.NewNRGBA(b)
	for y := b.Min.Y; y < b.Max.Y; y++ {
		for x := b.Min.X; x < b.Max.X; x++ {
			out.SetNRGBA(x, y, color.NRGBAModel.Convert(img.At(x, y)).(color.NRGBA))
		}
	}
	for y0 := b.Min.Y; y0 < b.Max.Y; y0 += block {
		for x0 := b.Min.X; x0 < b.Max.X; x0 += block {
			x1 := min(x0+block, b.Max.X)
			y1 := min(y0+block, b.Max.Y)
			var rs, gs, bs, count float64
			var r2, g2, b2 float64
			for y := y0; y < y1; y++ {
				for x := x0; x < x1; x++ {
					c := fromColor(out.At(x, y))
					r, g, bl := float64(c.R), float64(c.G), float64(c.B)
					rs += r
					gs += g
					bs += bl
					r2 += r * r
					g2 += g * g
					b2 += bl * bl
					count++
				}
			}
			if count == 0 {
				continue
			}
			mr, mg, mb := rs/count, gs/count, bs/count
			vr := r2/count - mr*mr
			vg := g2/count - mg*mg
			vb := b2/count - mb*mb
			avgVar := (vr + vg + vb) / 3.0
			if avgVar <= varThreshold {
				R := uint8(mr + 0.5)
				G := uint8(mg + 0.5)
				B := uint8(mb + 0.5)
				for y := y0; y < y1; y++ {
					for x := x0; x < x1; x++ {
						a := fromColor(out.At(x, y)).A
						out.Set(x, y, color.NRGBA{R, G, B, a})
					}
				}
			}
		}
	}
	return out
}

type encodeSettings struct {
	mode                 string
	useGlobalStream      bool
	enableTokenRLE       bool
	enableSequenceRLE    bool
	enableBackground     bool
	backgroundMinShare   float64
	roundStep            int
	deltaSnapThreshold   int
	paletteSize          int
	paletteDither        bool
	blockSize            int
	blockVarThreshold    float64
	sequenceRLEMaxSeqLen int
	zstdLevel            int
}

func encodeCLIX(imagePath, clixPath string, st encodeSettings) error {
	imgFile, err := os.Open(imagePath)
	if err != nil {
		return err
	}
	defer imgFile.Close()
	src, _, err := image.Decode(imgFile)
	if err != nil {
		return err
	}
	img := imageToNRGBA(src)
	switch st.mode {
	case "lossless":
	case "safe":
		if st.roundStep > 0 {
			img = applyRoundImage(img, st.roundStep)
		}
	case "unsafe":
		if st.paletteSize > 0 {
			q := median.Quantizer(st.paletteSize)
			pal := q.Quantize(make([]color.Color, 0, st.paletteSize), img)
			bounds := img.Bounds()
			paletted := image.NewPaletted(bounds, pal)
			if st.paletteDither {
				draw.FloydSteinberg.Draw(paletted, bounds, img, image.Point{})
			} else {
				draw.Draw(paletted, bounds, img, image.Point{}, draw.Src)
			}
			img = imageToNRGBA(paletted)
		}
		if st.blockSize > 1 {
			img = imageToNRGBA(blockSmooth(img, st.blockSize, st.blockVarThreshold))
		}
		if st.roundStep > 0 {
			img = applyRoundImage(img, st.roundStep)
		}
	default:
		return errors.New("mode must be 'lossless', 'safe', or 'unsafe'")
	}
	b := img.Bounds()
	width := b.Dx()
	height := b.Dy()
	pixels := make([]RGBA, 0, width*height)
	for y := b.Min.Y; y < b.Max.Y; y++ {
		for x := b.Min.X; x < b.Max.X; x++ {
			pixels = append(pixels, fromColor(img.At(x, y)))
		}
	}
	var bg RGBA
	var bgShare float64
	if st.enableBackground {
		bg, bgShare = detectBackground(pixels)
	}
	useBG := st.enableBackground && bgShare >= st.backgroundMinShare
	var tokens []string
	var prev *RGBA
	if st.useGlobalStream {
		for _, px := range pixels {
			if useBG && px == bg {
				tokens = append(tokens, "BG")
				prev = &px
				continue
			}
			if prev == nil {
				tokens = append(tokens, rgbaToToken(px))
				prev = &px
				continue
			}
			if st.deltaSnapThreshold > 0 && withinDelta(px, *prev, st.deltaSnapThreshold) {
				tokens = append(tokens, "S")
			} else {
				tokens = append(tokens, rgbaToToken(px))
				tmp := px
				prev = &tmp
			}
		}
	} else {
		for y := 0; y < height; y++ {
			prev = nil
			for x := 0; x < width; x++ {
				px := pixels[y*width+x]
				if useBG && px == bg {
					tokens = append(tokens, "BG")
					prev = &px
					continue
				}
				if prev == nil {
					tokens = append(tokens, rgbaToToken(px))
					prev = &px
					continue
				}
				if st.deltaSnapThreshold > 0 && withinDelta(px, *prev, st.deltaSnapThreshold) {
					tokens = append(tokens, "S")
				} else {
					tokens = append(tokens, rgbaToToken(px))
					tmp := px
					prev = &tmp
				}
			}
			tokens = append(tokens, "\n")
		}
	}
	var chunks [][]string
	order := "STREAM_GLOBAL"
	if st.useGlobalStream {
		chunks = [][]string{tokens}
	} else {
		order = "ROWMAJOR"
		var cur []string
		for _, t := range tokens {
			if t == "\n" {
				chunks = append(chunks, cur)
				cur = nil
				continue
			}
			cur = append(cur, t)
		}
		if len(cur) > 0 {
			chunks = append(chunks, cur)
		}
	}
	compressedLines := make([][]string, 0, len(chunks))
	for _, ch := range chunks {
		tmp := ch
		if st.enableTokenRLE {
			tmp = rleTokens(tmp)
		}
		if st.enableSequenceRLE {
			tmp = sequenceRLE(tmp, st.sequenceRLEMaxSeqLen)
		}
		compressedLines = append(compressedLines, tmp)
	}
	var lines []string
	if st.useGlobalStream {
		lines = []string{strings.Join(compressedLines[0], " ")}
	} else {
		for _, line := range compressedLines {
			lines = append(lines, strings.Join(line, " "))
		}
	}
	out, err := os.Create(clixPath)
	if err != nil {
		return err
	}
	defer out.Close()
	enc, err := zstd.NewWriter(out, zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(st.zstdLevel)))
	if err != nil {
		return err
	}
	defer enc.Close()
	bw := bufio.NewWriter(enc)
	defer bw.Flush()
	writeLine := func(s string) error {
		_, err := bw.WriteString(s + "\n")
		return err
	}
	if err := writeLine("CLIX 1.7"); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("WIDTH=%d", width)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("HEIGHT=%d", height)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("ORDER=%s", order)); err != nil {
		return err
	}
	var encFlags []string
	if st.enableTokenRLE {
		encFlags = append(encFlags, "RLE")
	}
	if st.enableSequenceRLE {
		encFlags = append(encFlags, "SEQ")
	}
	if err := writeLine("ENCODING=" + func() string {
		if len(encFlags) == 0 {
			return "NONE"
		}
		return strings.Join(encFlags, "+")
	}()); err != nil {
		return err
	}
	if useBG {
		if err := writeLine(fmt.Sprintf("BG=R%dG%dB%dA%d", bg.R, bg.G, bg.B, bg.A)); err != nil {
			return err
		}
	}
	if err := writeLine(fmt.Sprintf("MODE=%s", st.mode)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("ROUND_STEP=%d", st.roundStep)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("DELTA_SNAP_THRESHOLD=%d", st.deltaSnapThreshold)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("PALETTE_SIZE=%d", st.paletteSize)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("PALETTE_DITHER=%d", boolTo01(st.paletteDither))); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("BLOCK_SIZE=%d", st.blockSize)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("BLOCK_VAR_THRESHOLD=%g", st.blockVarThreshold)); err != nil {
		return err
	}
	if err := writeLine(""); err != nil {
		return err
	}
	for _, ln := range lines {
		if err := writeLine(ln); err != nil {
			return err
		}
	}
	return nil
}

func decodeCLIX(clixPath, outputPNG string) error {
	in, err := os.Open(clixPath)
	if err != nil {
		return err
	}
	defer in.Close()
	dc, err := zstd.NewReader(in)
	if err != nil {
		return err
	}
	defer dc.Close()
	raw, err := io.ReadAll(dc)
	if err != nil {
		return err
	}
	rawText := string(raw)
	rawLines := strings.Split(strings.ReplaceAll(rawText, "\r\n", "\n"), "\n")
	for i := range rawLines {
		rawLines[i] = strings.TrimRight(rawLines[i], "\n")
	}
	var width, height int
	order := "STREAM_GLOBAL"
	var bg *RGBA
	pixelSection := false
	var dataLines []string
	for _, ln := range rawLines {
		if strings.TrimSpace(ln) == "" {
			pixelSection = true
			continue
		}
		if !pixelSection {
			if strings.HasPrefix(ln, "CLIX") {
				continue
			} else if strings.HasPrefix(ln, "WIDTH=") {
				width, _ = strconv.Atoi(strings.SplitN(ln, "=", 2)[1])
			} else if strings.HasPrefix(ln, "HEIGHT=") {
				height, _ = strconv.Atoi(strings.SplitN(ln, "=", 2)[1])
			} else if strings.HasPrefix(ln, "ORDER=") {
				order = strings.TrimSpace(strings.SplitN(ln, "=", 2)[1])
			} else if strings.HasPrefix(ln, "BG=") {
				bgTok := strings.TrimSpace(strings.SplitN(ln, "=", 2)[1])
				p, err := tokenToRGBA(bgTok, nil, nil)
				if err != nil {
					return err
				}
				bg = &p
			}
		} else {
			dataLines = append(dataLines, ln)
		}
	}
	if width == 0 || height == 0 {
		return errors.New("missing WIDTH/HEIGHT in CLIX header")
	}
	var tokens []string
	for _, ln := range dataLines {
		if strings.TrimSpace(ln) == "" {
			continue
		}
		ts, err := tokenizeLine(ln)
		if err != nil {
			return err
		}
		tokens = append(tokens, ts...)
	}
	expanded, err := expandTokens(tokens)
	if err != nil {
		return err
	}
	pixels := make([]RGBA, 0, width*height)
	var prev *RGBA
	for _, base := range expanded {
		if base == "S" {
			if prev == nil {
				return errors.New("encountered 'S' before any previous pixel")
			}
			pixels = append(pixels, *prev)
			tmp := *prev
			prev = &tmp
			continue
		}
		px, err := tokenToRGBA(base, bg, prev)
		if err != nil {
			return err
		}
		pixels = append(pixels, px)
		tmp := px
		prev = &tmp
	}
	total := width * height
	if len(pixels) != total {
		return fmt.Errorf("decoded pixel count mismatch: got %d, expected %d (ORDER=%s)", len(pixels), total, order)
	}
	out := image.NewNRGBA(image.Rect(0, 0, width, height))
	i := 0
	for y := 0; y < height; y++ {
		for x := 0; x < width; x++ {
			out.SetNRGBA(x, y, pixels[i].toColor())
			i++
		}
	}
	f, err := os.Create(outputPNG)
	if err != nil {
		return err
	}
	defer f.Close()
	return png.Encode(f, out)
}

func main() {
	preset := pflag.String("preset", "safe", "Compression preset: lossless | safe | unsafe")
	dither := pflag.Bool("dither", false, "Enable Floyd-Steinberg dithering in palette mode")
	palette := pflag.Int("palette", 0, "Palette size (1-256, unsafe mode only)")
	blocksize := pflag.Int("blocksize", 0, "Block smoothing size (e.g., 2 or 4, unsafe mode only)")
	blockvar := pflag.Float64("blockvar", 12.0, "Variance threshold for block smoothing (unsafe mode)")
	roundstep := pflag.Int("roundstep", -1, "Channel rounding step (0=off)")
	deltasnap := pflag.Int("deltasnap", -1, "Delta snap threshold (0=off)")
	pflag.Parse()
	if pflag.NArg() < 1 {
		pflag.Usage()
		os.Exit(2)
	}
	input := pflag.Arg(0)
	name := strings.TrimSuffix(input, filepath.Ext(input))
	ext := strings.ToLower(filepath.Ext(input))
	if ext == ".clix" {
		if err := decodeCLIX(input, name+".png"); err != nil {
			fmt.Fprintln(os.Stderr, "[-] Decode error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Decoded %s -> %s.png\n", input, name)
		return
	}
	mode := strings.ToLower(*preset)
	var rs, ds, pal, blk int
	var dith bool
	var blkVar float64
	switch mode {
	case "lossless":
		rs, ds, pal, blk, dith, blkVar = 0, 0, 0, 0, false, *blockvar
	case "safe":
		rs = ifElse(*roundstep >= 0, *roundstep, 2)
		ds = ifElse(*deltasnap >= 0, *deltasnap, 2)
		pal, blk, dith, blkVar = 0, 0, false, *blockvar
	case "unsafe":
		rs = ifElse(*roundstep >= 0, *roundstep, 3)
		ds = ifElse(*deltasnap >= 0, *deltasnap, 3)
		pal = clampInt(ifElse(*palette > 0, *palette, 64), 1, 256)
		blk = ifElse(*blocksize > 0, *blocksize, 2)
		dith = *dither
		blkVar = *blockvar
	default:
		fmt.Fprintln(os.Stderr, "Unknown preset:", mode)
		os.Exit(1)
	}
	st := encodeSettings{
		mode:                 mode,
		useGlobalStream:      true,
		enableTokenRLE:       true,
		enableSequenceRLE:    true,
		enableBackground:     true,
		backgroundMinShare:   0.20,
		roundStep:            rs,
		deltaSnapThreshold:   ds,
		paletteSize:          pal,
		paletteDither:        dith,
		blockSize:            blk,
		blockVarThreshold:    blkVar,
		sequenceRLEMaxSeqLen: 64,
		zstdLevel:            22,
	}
	out := name + ".clix"
	if err := encodeCLIX(input, out, st); err != nil {
		fmt.Fprintln(os.Stderr, "[-] Encode error:", err)
		os.Exit(1)
	}
	fmt.Printf("[+] Encoded %s -> %s (preset=%s)\n", input, out, mode)
}

func imageToNRGBA(img image.Image) *image.NRGBA {
	b := img.Bounds()
	out := image.NewNRGBA(b)
	for y := b.Min.Y; y < b.Max.Y; y++ {
		for x := b.Min.X; x < b.Max.X; x++ {
			out.SetNRGBA(x, y, color.NRGBAModel.Convert(img.At(x, y)).(color.NRGBA))
		}
	}
	return out
}

func applyRoundImage(img *image.NRGBA, step int) *image.NRGBA {
	if step <= 0 {
		return img
	}
	out := image.NewNRGBA(img.Bounds())
	copy(out.Pix, img.Pix)
	for y := img.Rect.Min.Y; y < img.Rect.Max.Y; y++ {
		for x := img.Rect.Min.X; x < img.Rect.Max.X; x++ {
			o := img.PixOffset(x, y)
			R := out.Pix[o+0]
			G := out.Pix[o+1]
			B := out.Pix[o+2]
			A := out.Pix[o+3]
			p := applyRound(RGBA{R, G, B, A}, step)
			out.Pix[o+0] = p.R
			out.Pix[o+1] = p.G
			out.Pix[o+2] = p.B
			out.Pix[o+3] = p.A
		}
	}
	return out
}

func isSpace(b byte) bool { return b == ' ' || b == '\t' || b == '\n' || b == '\r' }
func isDigit(b byte) bool { return b >= '0' && b <= '9' }
func isAllDigits(s string) bool {
	if s == "" {
		return false
	}
	for i := 0; i < len(s); i++ {
		if !isDigit(s[i]) {
			return false
		}
	}
	return true
}

func boolTo01(b bool) int {
	if b {
		return 1
	}
	return 0
}

func clampInt(v, lo, hi int) int {
	if v < lo {
		return lo
	}
	if v > hi {
		return hi
	}
	return v
}

func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}

func saveJPEG(w io.Writer, img image.Image, quality int) error {
	var buf bytes.Buffer
	err := jpeg.Encode(&buf, img, &jpeg.Options{Quality: quality})
	if err != nil {
		return err
	}
	_, err = io.Copy(w, &buf)
	return err
}

func ifElse(cond bool, a, b int) int {
	if cond {
		return a
	}
	return b
}

var _ = slices.Contains[[]int]
