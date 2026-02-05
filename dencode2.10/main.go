package main

import (
	"bufio"
	"bytes"
	"encoding/base64"
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"image"
	"image/color"
	"image/draw"
	"image/png"
	"io"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"

	_ "image/gif"
	_ "image/jpeg"

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
}

const (
	encoderVersion = "2.10"
	clixVersion    = "2.7"
	blixVersion    = "2.0"
	vlixVersion    = "2.5"
	vlixCodecV1    = "VLIX1"
	vlixCodecV2    = "VLIX2"
	alixVersion    = "1.2"
	alixCodec      = "ALIX"
	elixVersion    = "0.1"
)

var PURE_COLOR_TOKENS = map[RGBA]string{{0, 0, 0, 255}: "K", {255, 255, 255, 255}: "W", {255, 0, 0, 255}: "R", {0, 255, 0, 255}: "G", {0, 0, 255, 255}: "B", {255, 255, 0, 255}: "Y", {255, 165, 0, 255}: "O", {128, 0, 128, 255}: "P"}
var PURE_LOOKUP = func() map[string]RGBA {
	m := make(map[string]RGBA, len(PURE_COLOR_TOKENS))
	for k, v := range PURE_COLOR_TOKENS {
		m[v] = k
	}
	return m
}()

func isSpace(b byte) bool { return b == ' ' || b == '\t' || b == '\n' || b == '\r' }
func isDigit(b byte) bool { return b >= '0' && b <= '9' }
func isHexDigit(b byte) bool {
	return (b >= '0' && b <= '9') || (b >= 'A' && b <= 'F') || (b >= 'a' && b <= 'f')
}
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
func isAllHex(s string) bool {
	if s == "" {
		return false
	}
	for i := 0; i < len(s); i++ {
		if !isHexDigit(s[i]) {
			return false
		}
	}
	return true
}
func rgbaToCompactHex(px RGBA) string {
	return fmt.Sprintf("%02X%02X%02X%02X", px.R, px.G, px.B, px.A)
}

func rgbaToToken(px RGBA) string {
	if tok, ok := PURE_COLOR_TOKENS[px]; ok {
		return tok
	}
	return rgbaToCompactHex(px)
}

var macroNameAlphabet = []rune{
	'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
	'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
	'0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
	'!', '@', '$', '%', '^', '&', '-', '_', '=', '+', ';', ':', ',', '.', '/', '?', '<', '>', '[', ']', '{', '}', '|', '~', '`',
}

func generateMacroNames(n int) []string {
	names := make([]string, 0, n)
	for _, r := range macroNameAlphabet {
		names = append(names, "M"+string(r))
		if len(names) == n {
			return names
		}
	}
	if n > len(names) {
		for _, r1 := range macroNameAlphabet {
			for _, r2 := range macroNameAlphabet {
				names = append(names, "M"+string(r1)+string(r2))
				if len(names) == n {
					return names
				}
			}
		}
	}
	return names
}

func tokenizeLine(s string) ([]string, error) {
	var tokens []string
	i := 0
	n := len(s)
	readRepeat := func(j int) (int, bool) {
		if j < n && s[j] == '*' {
			j++
			start := j
			for j < n && isDigit(s[j]) {
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
				return nil, fmt.Errorf("unbalanced parentheses at: %q", s[i:])
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
		if s[i] == 'S' || s[i] == 'K' || s[i] == 'W' || s[i] == 'R' || s[i] == 'G' || s[i] == 'B' || s[i] == 'Y' || s[i] == 'O' || s[i] == 'P' {
			if isHexDigit(s[i]) && i+1 < n && isHexDigit(s[i+1]) {
			} else {
				j := i + 1
				j, _ = readRepeat(j)
				tokens = append(tokens, s[i:j])
				i = j
				continue
			}
		}
		if s[i] == '#' {
			j := i + 1
			for j < n && !isSpace(s[j]) {
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
			if j-i == 8 && j < n && s[j] == '*' {
				k := j + 1
				start := k
				for k < n && isDigit(s[k]) {
					k++
				}
				if start == k {
					tokens = append(tokens, s[i:j])
					i = j
					continue
				}
				tokens = append(tokens, s[i:k])
				i = k
				continue
			}
			seq := s[i:j]
			if len(seq)%8 != 0 {
				return nil, fmt.Errorf("hex run not multiple of 8 at: %q", seq)
			}
			for off := 0; off < len(seq); off += 8 {
				tokens = append(tokens, seq[off:off+8])
			}
			i = j
			continue
		}
		j := i
		for j < n && !isSpace(s[j]) {
			j++
		}
		tokens = append(tokens, s[i:j])
		i = j
	}
	return tokens, nil
}

func expandGroupToken(token string) ([]string, error) {
	token = strings.TrimSpace(token)
	count := 1
	var inner string
	if strings.Contains(token, ")*") {
		pos := strings.LastIndex(token, ")*")
		inner = token[1:pos]
		cntStr := token[pos+2:]
		if !isAllDigits(cntStr) {
			return nil, fmt.Errorf("bad repeat in %q", token)
		}
		v, _ := strconv.Atoi(cntStr)
		count = v
	} else {
		r := strings.LastIndexByte(token, ')')
		if r == -1 {
			return nil, fmt.Errorf("malformed group: %s", token)
		}
		inner = token[1:r]
		tail := token[r+1:]
		if strings.HasPrefix(tail, "*") {
			cnt := tail[1:]
			if !isAllDigits(cnt) {
				return nil, fmt.Errorf("bad repeat in %q", token)
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

func tokensToLines(tokens []string, perLine int) []string {
	if perLine <= 0 {
		perLine = len(tokens)
	}
	lines := make([]string, 0, (len(tokens)+perLine-1)/perLine)
	for i := 0; i < len(tokens); i += perLine {
		end := i + perLine
		if end > len(tokens) {
			end = len(tokens)
		}
		lines = append(lines, strings.Join(tokens[i:end], ""))
	}
	return lines
}

func tokenizeLineWithMacros(s string, macroNames map[string]struct{}) ([]string, error) {
	if len(macroNames) == 0 {
		return tokenizeLine(s)
	}
	var tokens []string
	i := 0
	n := len(s)
	readRepeat := func(j int) (int, bool) {
		if j < n && s[j] == '*' {
			j++
			start := j
			for j < n && isDigit(s[j]) {
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
				return nil, fmt.Errorf("unbalanced parentheses at: %q", s[i:])
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
		if s[i] == 'S' || s[i] == 'K' || s[i] == 'W' || s[i] == 'R' || s[i] == 'G' || s[i] == 'B' || s[i] == 'Y' || s[i] == 'O' || s[i] == 'P' {
			if isHexDigit(s[i]) && i+1 < n && isHexDigit(s[i+1]) {
			} else {
				j := i + 1
				j, _ = readRepeat(j)
				tokens = append(tokens, s[i:j])
				i = j
				continue
			}
		}
		if s[i] == '#' {
			j := i + 1
			for j < n && !isSpace(s[j]) {
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
				for k < n && isDigit(s[k]) {
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
				return nil, fmt.Errorf("hex run not multiple of 8 at: %q", seq)
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
			if matched == "" {
				return nil, fmt.Errorf("unknown macro at: %q", s[i:])
			}
			j := i
			j, _ = readRepeat(j)
			tokens = append(tokens, matched+s[i:j])
			i = j
			continue
		}
		j := i
		for j < n && !isSpace(s[j]) {
			j++
		}
		tokens = append(tokens, s[i:j])
		i = j
	}
	return tokens, nil
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
	pack := func(p RGBA) uint32 { return uint32(p.R)<<24 | uint32(p.G)<<16 | uint32(p.B)<<8 | uint32(p.A) }
	unpack := func(u uint32) RGBA { return RGBA{uint8(u >> 24), uint8(u >> 16), uint8(u >> 8), uint8(u)} }
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
	return ad(p1.R, p2.R) <= thr && ad(p1.G, p2.G) <= thr && ad(p1.B, p2.B) <= thr && ad(p1.A, p2.A) <= thr
}

var rgbaPartRe = regexp.MustCompile(`[RGBA]\d+`)

func parseHexTokenHash(tok string) (RGBA, error) {
	if len(tok) != 7 && len(tok) != 9 {
		return RGBA{}, fmt.Errorf("bad hex token length: %q", tok)
	}
	if tok[0] != '#' {
		return RGBA{}, fmt.Errorf("not a hex token: %q", tok)
	}
	hex := tok[1:]
	parseByte := func(s string) (uint8, error) {
		v, err := strconv.ParseUint(s, 16, 8)
		if err != nil {
			return 0, err
		}
		return uint8(v), nil
	}
	r, err := parseByte(hex[0:2])
	if err != nil {
		return RGBA{}, err
	}
	g, err := parseByte(hex[2:4])
	if err != nil {
		return RGBA{}, err
	}
	b, err := parseByte(hex[4:6])
	if err != nil {
		return RGBA{}, err
	}
	a := uint8(255)
	if len(hex) == 8 {
		a, err = parseByte(hex[6:8])
		if err != nil {
			return RGBA{}, err
		}
	}
	return RGBA{r, g, b, a}, nil
}

func parseHexTokenCompact(tok string) (RGBA, error) {
	if len(tok) != 6 && len(tok) != 8 {
		return RGBA{}, fmt.Errorf("bad compact hex length: %q", tok)
	}
	if !isAllHex(tok) {
		return RGBA{}, fmt.Errorf("invalid hex: %q", tok)
	}
	parseByte := func(s string) (uint8, error) {
		v, err := strconv.ParseUint(s, 16, 8)
		if err != nil {
			return 0, err
		}
		return uint8(v), nil
	}
	r, err := parseByte(tok[0:2])
	if err != nil {
		return RGBA{}, err
	}
	g, err := parseByte(tok[2:4])
	if err != nil {
		return RGBA{}, err
	}
	b, err := parseByte(tok[4:6])
	if err != nil {
		return RGBA{}, err
	}
	a := uint8(255)
	if len(tok) == 8 {
		a, err = parseByte(tok[6:8])
		if err != nil {
			return RGBA{}, err
		}
	}
	return RGBA{r, g, b, a}, nil
}

func tokenToRGBA(tok string, bg *RGBA, prev *RGBA) (RGBA, error) {
	switch tok {
	case "S":
		if prev == nil {
			return RGBA{}, errors.New("encountered 'S' before any previous pixel")
		}
		return *prev, nil
	case "BG":
		if bg == nil {
			return RGBA{}, errors.New("BG token without BG")
		}
		return *bg, nil
	}
	if px, ok := PURE_LOOKUP[tok]; ok {
		return px, nil
	}
	if strings.HasPrefix(tok, "#") {
		return parseHexTokenHash(tok)
	}
	if (len(tok) == 6 || len(tok) == 8) && isAllHex(tok) {
		return parseHexTokenCompact(tok)
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
			return RGBA{}, fmt.Errorf("malformed token: %s", tok)
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
	chromaMode           string
	roundStep            int
	deltaSnapThreshold   int
	paletteSize          int
	paletteDither        bool
	blockSize            int
	blockVarThreshold    float64
	sequenceRLEMaxSeqLen int
	zstdLevel            int
}

func prepareImageForEncoding(src image.Image, st encodeSettings) (*image.NRGBA, error) {
	img := imageToNRGBA(src)
	if st.chromaMode != "" && st.chromaMode != "444" {
		img = applyChromaSubsample(img, st.chromaMode)
	}
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
		return nil, errors.New("mode must be 'lossless', 'safe', or 'unsafe'")
	}
	return img, nil
}

func imageToPixels(img *image.NRGBA) []RGBA {
	b := img.Bounds()
	pixels := make([]RGBA, 0, b.Dx()*b.Dy())
	for y := b.Min.Y; y < b.Max.Y; y++ {
		for x := b.Min.X; x < b.Max.X; x++ {
			pixels = append(pixels, fromColor(img.At(x, y)))
		}
	}
	return pixels
}

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

type bitWriter struct {
	buf   []byte
	cur   byte
	nbits uint8
}

func (w *bitWriter) WriteBit(bit uint8) {
	if bit != 0 {
		w.cur |= 1 << (7 - w.nbits)
	}
	w.nbits++
	if w.nbits == 8 {
		w.buf = append(w.buf, w.cur)
		w.cur = 0
		w.nbits = 0
	}
}

func (w *bitWriter) WriteBits(v uint64, n uint8) {
	for i := int(n) - 1; i >= 0; i-- {
		bit := uint8((v >> uint(i)) & 1)
		w.WriteBit(bit)
	}
}

func (w *bitWriter) Bytes() []byte {
	if w.nbits > 0 {
		w.buf = append(w.buf, w.cur)
		w.cur = 0
		w.nbits = 0
	}
	return w.buf
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

func writeRiceSigned(w *bitWriter, v int, k uint8) {
	u := uint32(int32(v<<1) ^ int32(v>>31))
	q := u >> k
	for i := uint32(0); i < q; i++ {
		w.WriteBit(0)
	}
	w.WriteBit(1)
	if k > 0 {
		mask := uint32((1 << k) - 1)
		w.WriteBits(uint64(u&mask), k)
	}
}

func writeRiceUnsigned(w *bitWriter, v uint32, k uint8) {
	q := v >> k
	for i := uint32(0); i < q; i++ {
		w.WriteBit(0)
	}
	w.WriteBit(1)
	if k > 0 {
		mask := uint32((1 << k) - 1)
		w.WriteBits(uint64(v&mask), k)
	}
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

func writeSVarint(w io.Writer, v int32) error {
	u := uint64(uint32(v<<1) ^ uint32(v>>31))
	return writeUvarint(w, u)
}

func readSVarint(r *bufio.Reader) (int32, error) {
	u, err := binary.ReadUvarint(r)
	if err != nil {
		return 0, err
	}
	v := int32(u>>1) ^ -int32(u&1)
	return v, nil
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

func buildYCbCrPlanes(img *image.NRGBA, mode string) ycbcrPlanes {
	mode = strings.ToLower(strings.TrimSpace(mode))
	if mode == "" {
		mode = "444"
	}
	b := img.Bounds()
	w, h := b.Dx(), b.Dy()
	cw, ch := w, h
	switch mode {
	case "422":
		cw = (w + 1) / 2
	case "420":
		cw = (w + 1) / 2
		ch = (h + 1) / 2
	default:
		mode = "444"
	}
	y := make([]float64, w*h)
	a := make([]float64, w*h)
	cb := make([]float64, cw*ch)
	cr := make([]float64, cw*ch)
	counts := make([]int, cw*ch)
	for yy := 0; yy < h; yy++ {
		for xx := 0; xx < w; xx++ {
			o := img.PixOffset(xx+b.Min.X, yy+b.Min.Y)
			r := img.Pix[o+0]
			g := img.Pix[o+1]
			bl := img.Pix[o+2]
			al := img.Pix[o+3]
			iy := yy*w + xx
			yyc, cbv, crv := color.RGBToYCbCr(r, g, bl)
			y[iy] = float64(yyc)
			a[iy] = float64(al)
			cx, cy := xx, yy
			switch mode {
			case "422":
				cx = xx / 2
			case "420":
				cx = xx / 2
				cy = yy / 2
			}
			ci := cy*cw + cx
			cb[ci] += float64(cbv)
			cr[ci] += float64(crv)
			counts[ci]++
		}
	}
	for i := range cb {
		if counts[i] > 0 {
			cb[i] /= float64(counts[i])
			cr[i] /= float64(counts[i])
		}
	}
	return ycbcrPlanes{y: y, cb: cb, cr: cr, a: a, w: w, h: h, cw: cw, ch: ch, mode: mode}
}

func planesToNRGBA(p ycbcrPlanes) *image.NRGBA {
	img := image.NewNRGBA(image.Rect(0, 0, p.w, p.h))
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
			yv = math.Max(0, math.Min(255, yv))
			cb = math.Max(0, math.Min(255, cb))
			cr = math.Max(0, math.Min(255, cr))
			av = math.Max(0, math.Min(255, av))
			r, g, b := color.YCbCrToRGB(uint8(yv+0.5), uint8(cb+0.5), uint8(cr+0.5))
			img.SetNRGBA(xx, yy, color.NRGBA{R: r, G: g, B: b, A: uint8(av + 0.5)})
		}
	}
	return img
}

func encodePlaneDCT(w io.Writer, plane []float64, pw, ph int, qtable [64]int, center bool) error {
	bw := (pw + 7) / 8
	bh := (ph + 7) / 8
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			var block [64]float64
			for y := 0; y < 8; y++ {
				sy := by*8 + y
				if sy >= ph {
					sy = ph - 1
				}
				for x := 0; x < 8; x++ {
					sx := bx*8 + x
					if sx >= pw {
						sx = pw - 1
					}
					v := plane[sy*pw+sx]
					if center {
						v -= 128.0
					}
					block[y*8+x] = v
				}
			}
			coeff := dct8x8(block)
			for i := 0; i < 64; i++ {
				idx := zigZagOrder[i]
				q := int32(math.Round(coeff[idx] / float64(qtable[idx])))
				if err := writeSVarint(w, q); err != nil {
					return err
				}
			}
		}
	}
	return nil
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

func encodePlaneDCTRiceEx(w *bitWriter, plane []float64, pw, ph int, qtable [64]int, center bool, k uint8, predDC, zeroRun, blockSkip, acMag bool) error {
	bw := (pw + 7) / 8
	bh := (ph + 7) / 8
	var dcVals []int
	if predDC {
		dcVals = make([]int, bw*bh)
	}
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			var block [64]float64
			for y := 0; y < 8; y++ {
				sy := by*8 + y
				if sy >= ph {
					sy = ph - 1
				}
				for x := 0; x < 8; x++ {
					sx := bx*8 + x
					if sx >= pw {
						sx = pw - 1
					}
					v := plane[sy*pw+sx]
					if center {
						v -= 128.0
					}
					block[y*8+x] = v
				}
			}
			coeff := dct8x8(block)
			var quant [64]int
			allZero := true
			for i := 0; i < 64; i++ {
				q := int(math.Round(coeff[i] / float64(qtable[i])))
				quant[i] = q
				if q != 0 {
					allZero = false
				}
			}
			if blockSkip {
				if allZero {
					w.WriteBit(1)
					if predDC {
						dcVals[by*bw+bx] = 0
					}
					continue
				}
				w.WriteBit(0)
			}

			if predDC {
				dc := quant[0]
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
				writeRiceSigned(w, dc-pred, k)
				dcVals[by*bw+bx] = dc
			} else {
				writeRiceSigned(w, quant[0], k)
			}

			if zeroRun {
				pos := 1
				for pos < 64 {
					run := 0
					for pos+run < 64 && quant[zigZagOrder[pos+run]] == 0 {
						run++
					}
					remaining := 64 - pos
					writeRiceUnsigned(w, uint32(run), k)
					if run == remaining {
						break
					}
					pos += run
					val := quant[zigZagOrder[pos]]
					if acMag {
						if val < 0 {
							w.WriteBit(1)
							val = -val
						} else {
							w.WriteBit(0)
						}
						writeRiceUnsigned(w, uint32(val), k)
					} else {
						writeRiceSigned(w, val, k)
					}
					pos++
				}
			} else {
				for i := 1; i < 64; i++ {
					writeRiceSigned(w, quant[zigZagOrder[i]], k)
				}
			}
		}
	}
	return nil
}

func encodePlaneDCTRice(w *bitWriter, plane []float64, pw, ph int, qtable [64]int, center bool, k uint8) error {
	return encodePlaneDCTRiceEx(w, plane, pw, ph, qtable, center, k, false, false, false, false)
}

func encodePlaneDCTRicePred(w *bitWriter, plane []float64, pw, ph int, qtable [64]int, center bool, k uint8) error {
	return encodePlaneDCTRiceEx(w, plane, pw, ph, qtable, center, k, true, false, false, false)
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

func diffPlane(cur, prev []float64) []float64 {
	out := make([]float64, len(cur))
	for i := range cur {
		out[i] = cur[i] - prev[i]
	}
	return out
}

func planeAllZero(p []float64, eps float64) bool {
	if len(p) == 0 {
		return true
	}
	for _, v := range p {
		if v > eps || v < -eps {
			return false
		}
	}
	return true
}

func filledPlane(n int, v float64) []float64 {
	out := make([]float64, n)
	for i := range out {
		out[i] = v
	}
	return out
}

func imageHasAlpha(img *image.NRGBA) bool {
	if img == nil {
		return false
	}
	pix := img.Pix
	for i := 3; i < len(pix); i += 4 {
		if pix[i] != 255 {
			return true
		}
	}
	return false
}

func detectFramesAlpha(frames []string, st encodeSettings, ffmpegPath string) (bool, error) {
	for _, framePath := range frames {
		raw, err := decodeImageFile(framePath, ffmpegPath)
		if err != nil {
			return false, err
		}
		img, err := prepareImageForEncoding(raw, st)
		if err != nil {
			return false, err
		}
		if imageHasAlpha(img) {
			return true, nil
		}
	}
	return false, nil
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

func applyChromaSubsample(img *image.NRGBA, mode string) *image.NRGBA {
	mode = strings.ToLower(strings.TrimSpace(mode))
	if mode == "" || mode == "444" {
		return img
	}
	b := img.Bounds()
	out := image.NewNRGBA(b)
	w := b.Dx()
	h := b.Dy()
	getYCbCr := func(x, y int) (uint8, uint8, uint8, uint8) {
		o := img.PixOffset(x+b.Min.X, y+b.Min.Y)
		r := img.Pix[o+0]
		g := img.Pix[o+1]
		bl := img.Pix[o+2]
		a := img.Pix[o+3]
		yy, cb, cr := color.RGBToYCbCr(r, g, bl)
		return yy, cb, cr, a
	}
	switch mode {
	case "422":
		for y := 0; y < h; y++ {
			for x := 0; x < w; x += 2 {
				yy0, cb0, cr0, a0 := getYCbCr(x, y)
				yy1, cb1, cr1, a1 := yy0, cb0, cr0, a0
				if x+1 < w {
					yy1, cb1, cr1, a1 = getYCbCr(x+1, y)
				}
				cb := uint8((int(cb0) + int(cb1)) / 2)
				cr := uint8((int(cr0) + int(cr1)) / 2)
				r0, g0, b0 := color.YCbCrToRGB(yy0, cb, cr)
				r1, g1, b1 := color.YCbCrToRGB(yy1, cb, cr)
				o0 := out.PixOffset(x+b.Min.X, y+b.Min.Y)
				out.Pix[o0+0] = r0
				out.Pix[o0+1] = g0
				out.Pix[o0+2] = b0
				out.Pix[o0+3] = a0
				if x+1 < w {
					o1 := out.PixOffset(x+1+b.Min.X, y+b.Min.Y)
					out.Pix[o1+0] = r1
					out.Pix[o1+1] = g1
					out.Pix[o1+2] = b1
					out.Pix[o1+3] = a1
				}
			}
		}
	case "420":
		for y := 0; y < h; y += 2 {
			for x := 0; x < w; x += 2 {
				var ys [4]uint8
				var alphas [4]uint8
				cbs := 0
				crs := 0
				count := 0
				for dy := 0; dy < 2; dy++ {
					for dx := 0; dx < 2; dx++ {
						ix := x + dx
						iy := y + dy
						if ix >= w || iy >= h {
							continue
						}
						yy, cb, cr, a := getYCbCr(ix, iy)
						ys[dy*2+dx] = yy
						alphas[dy*2+dx] = a
						cbs += int(cb)
						crs += int(cr)
						count++
					}
				}
				if count == 0 {
					continue
				}
				cb := uint8(cbs / count)
				cr := uint8(crs / count)
				for dy := 0; dy < 2; dy++ {
					for dx := 0; dx < 2; dx++ {
						ix := x + dx
						iy := y + dy
						if ix >= w || iy >= h {
							continue
						}
						yy := ys[dy*2+dx]
						a := alphas[dy*2+dx]
						r, g, bl := color.YCbCrToRGB(yy, cb, cr)
						o := out.PixOffset(ix+b.Min.X, iy+b.Min.Y)
						out.Pix[o+0] = r
						out.Pix[o+1] = g
						out.Pix[o+2] = bl
						out.Pix[o+3] = a
					}
				}
			}
		}
	default:
		return img
	}
	return out
}

const elixPrecision = 6

func formatElixFloat(v float64) string {
	return strconv.FormatFloat(v, 'f', elixPrecision, 64)
}

type elixRef struct {
	v int
	t int
	n int
}

func parseOBJIndex(s string, count int) (int, error) {
	i, err := strconv.Atoi(s)
	if err != nil {
		return -1, err
	}
	if i == 0 {
		return -1, errors.New("OBJ indices are 1-based; 0 is invalid")
	}
	if i < 0 {
		i = count + i
	} else {
		i = i - 1
	}
	if i < 0 || i >= count {
		return -1, fmt.Errorf("OBJ index out of range: %d (count=%d)", i, count)
	}
	return i, nil
}

func parseOBJIndexMaybe(s string, count int) (int, error) {
	if s == "" {
		return -1, nil
	}
	return parseOBJIndex(s, count)
}

func parseOBJRef(token string, vCount, tCount, nCount int) (elixRef, error) {
	parts := strings.Split(token, "/")
	if len(parts) > 3 {
		return elixRef{}, fmt.Errorf("invalid OBJ face token: %s", token)
	}
	if parts[0] == "" {
		return elixRef{}, fmt.Errorf("missing OBJ vertex index in token: %s", token)
	}
	v, err := parseOBJIndex(parts[0], vCount)
	if err != nil {
		return elixRef{}, err
	}
	t := -1
	n := -1
	if len(parts) >= 2 {
		t, err = parseOBJIndexMaybe(parts[1], tCount)
		if err != nil {
			return elixRef{}, err
		}
	}
	if len(parts) == 3 {
		n, err = parseOBJIndexMaybe(parts[2], nCount)
		if err != nil {
			return elixRef{}, err
		}
	}
	return elixRef{v: v, t: t, n: n}, nil
}

func parseOBJ(path string) (*ElixMesh, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	mesh := &ElixMesh{}
	scanner := bufio.NewScanner(f)
	scanner.Buffer(make([]byte, 0, 64*1024), 1024*1024)
	lineNo := 0
	for scanner.Scan() {
		lineNo++
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}
		fields := strings.Fields(line)
		if len(fields) == 0 {
			continue
		}
		switch fields[0] {
		case "v":
			if len(fields) < 4 {
				return nil, fmt.Errorf("OBJ v expects 3 floats at line %d", lineNo)
			}
			x, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ v parse error at line %d: %v", lineNo, err)
			}
			y, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ v parse error at line %d: %v", lineNo, err)
			}
			z, err := strconv.ParseFloat(fields[3], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ v parse error at line %d: %v", lineNo, err)
			}
			mesh.Verts = append(mesh.Verts, Vec3{X: x, Y: y, Z: z})
		case "vt":
			if len(fields) < 3 {
				return nil, fmt.Errorf("OBJ vt expects 2 floats at line %d", lineNo)
			}
			u, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ vt parse error at line %d: %v", lineNo, err)
			}
			v, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ vt parse error at line %d: %v", lineNo, err)
			}
			mesh.UVs = append(mesh.UVs, Vec2{U: u, V: v})
		case "vn":
			if len(fields) < 4 {
				return nil, fmt.Errorf("OBJ vn expects 3 floats at line %d", lineNo)
			}
			x, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ vn parse error at line %d: %v", lineNo, err)
			}
			y, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ vn parse error at line %d: %v", lineNo, err)
			}
			z, err := strconv.ParseFloat(fields[3], 64)
			if err != nil {
				return nil, fmt.Errorf("OBJ vn parse error at line %d: %v", lineNo, err)
			}
			mesh.Normals = append(mesh.Normals, Vec3{X: x, Y: y, Z: z})
		case "f":
			if len(fields) < 4 {
				return nil, fmt.Errorf("OBJ f expects at least 3 vertices at line %d", lineNo)
			}
			refs := make([]elixRef, 0, len(fields)-1)
			for _, tok := range fields[1:] {
				ref, err := parseOBJRef(tok, len(mesh.Verts), len(mesh.UVs), len(mesh.Normals))
				if err != nil {
					return nil, fmt.Errorf("OBJ f parse error at line %d: %v", lineNo, err)
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
		default:
			continue
		}
	}
	if err := scanner.Err(); err != nil {
		return nil, err
	}
	if len(mesh.Verts) == 0 {
		return nil, errors.New("OBJ has no vertices")
	}
	if len(mesh.Faces) == 0 {
		return nil, errors.New("OBJ has no faces")
	}
	return mesh, nil
}

func formatFaceRef(v, t, n int) string {
	vStr := strconv.Itoa(v)
	if t >= 0 && n >= 0 {
		return vStr + "/" + strconv.Itoa(t) + "/" + strconv.Itoa(n)
	}
	if t >= 0 {
		return vStr + "/" + strconv.Itoa(t)
	}
	if n >= 0 {
		return vStr + "//" + strconv.Itoa(n)
	}
	return vStr
}

func formatOBJFaceRef(v, t, n int) string {
	vStr := strconv.Itoa(v + 1)
	if t >= 0 && n >= 0 {
		return vStr + "/" + strconv.Itoa(t+1) + "/" + strconv.Itoa(n+1)
	}
	if t >= 0 {
		return vStr + "/" + strconv.Itoa(t+1)
	}
	if n >= 0 {
		return vStr + "//" + strconv.Itoa(n+1)
	}
	return vStr
}

func encodeELIX(objPath, elixPath string, zstdLevel int) error {
	mesh, err := parseOBJ(objPath)
	if err != nil {
		return err
	}
	out, err := os.Create(elixPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(zstdLevel, 1, 22)
	enc, err := zstd.NewWriter(out, zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(level)))
	if err != nil {
		return err
	}
	bw := bufio.NewWriter(enc)
	writeLine := func(s string) error { _, err := bw.WriteString(s + "\n"); return err }
	if err := writeLine("ELIX " + elixVersion); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("VERTS=%d", len(mesh.Verts))); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("UVS=%d", len(mesh.UVs))); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("NORMS=%d", len(mesh.Normals))); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("FACES=%d", len(mesh.Faces))); err != nil {
		return err
	}
	if err := writeLine("INDEX_BASE=0"); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("PRECISION=%d", elixPrecision)); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("ZSTD_LEVEL=%d", level)); err != nil {
		return err
	}
	if err := writeLine(""); err != nil {
		return err
	}
	for _, v := range mesh.Verts {
		if err := writeLine("V " + formatElixFloat(v.X) + " " + formatElixFloat(v.Y) + " " + formatElixFloat(v.Z)); err != nil {
			return err
		}
	}
	for _, t := range mesh.UVs {
		if err := writeLine("T " + formatElixFloat(t.U) + " " + formatElixFloat(t.V)); err != nil {
			return err
		}
	}
	for _, n := range mesh.Normals {
		if err := writeLine("N " + formatElixFloat(n.X) + " " + formatElixFloat(n.Y) + " " + formatElixFloat(n.Z)); err != nil {
			return err
		}
	}
	for _, f := range mesh.Faces {
		ref0 := formatFaceRef(f.V[0], f.T[0], f.N[0])
		ref1 := formatFaceRef(f.V[1], f.T[1], f.N[1])
		ref2 := formatFaceRef(f.V[2], f.T[2], f.N[2])
		if err := writeLine("F " + ref0 + " " + ref1 + " " + ref2); err != nil {
			return err
		}
	}
	if err := bw.Flush(); err != nil {
		return err
	}
	if err := enc.Close(); err != nil {
		return err
	}
	if err := out.Sync(); err != nil {
		return err
	}
	return nil
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

func writeOBJ(mesh *ElixMesh, outputOBJ string) error {
	out, err := os.Create(outputOBJ)
	if err != nil {
		return err
	}
	defer out.Close()
	bw := bufio.NewWriter(out)
	if _, err := bw.WriteString("# Converted from ELIX\n"); err != nil {
		return err
	}
	for _, v := range mesh.Verts {
		if _, err := bw.WriteString("v " + formatElixFloat(v.X) + " " + formatElixFloat(v.Y) + " " + formatElixFloat(v.Z) + "\n"); err != nil {
			return err
		}
	}
	for _, t := range mesh.UVs {
		if _, err := bw.WriteString("vt " + formatElixFloat(t.U) + " " + formatElixFloat(t.V) + "\n"); err != nil {
			return err
		}
	}
	for _, n := range mesh.Normals {
		if _, err := bw.WriteString("vn " + formatElixFloat(n.X) + " " + formatElixFloat(n.Y) + " " + formatElixFloat(n.Z) + "\n"); err != nil {
			return err
		}
	}
	for _, f := range mesh.Faces {
		ref0 := formatOBJFaceRef(f.V[0], f.T[0], f.N[0])
		ref1 := formatOBJFaceRef(f.V[1], f.T[1], f.N[1])
		ref2 := formatOBJFaceRef(f.V[2], f.T[2], f.N[2])
		if _, err := bw.WriteString("f " + ref0 + " " + ref1 + " " + ref2 + "\n"); err != nil {
			return err
		}
	}
	if err := bw.Flush(); err != nil {
		return err
	}
	return out.Sync()
}

func decodeELIX(elixPath, outputOBJ string) error {
	in, err := os.Open(elixPath)
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
				return fmt.Errorf("ELIX V expects 3 floats: %q", line)
			}
			x, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return err
			}
			y, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return err
			}
			z, err := strconv.ParseFloat(fields[3], 64)
			if err != nil {
				return err
			}
			mesh.Verts = append(mesh.Verts, Vec3{X: x, Y: y, Z: z})
		case "T":
			if len(fields) < 3 {
				return fmt.Errorf("ELIX T expects 2 floats: %q", line)
			}
			u, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return err
			}
			v, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return err
			}
			mesh.UVs = append(mesh.UVs, Vec2{U: u, V: v})
		case "N":
			if len(fields) < 4 {
				return fmt.Errorf("ELIX N expects 3 floats: %q", line)
			}
			x, err := strconv.ParseFloat(fields[1], 64)
			if err != nil {
				return err
			}
			y, err := strconv.ParseFloat(fields[2], 64)
			if err != nil {
				return err
			}
			z, err := strconv.ParseFloat(fields[3], 64)
			if err != nil {
				return err
			}
			mesh.Normals = append(mesh.Normals, Vec3{X: x, Y: y, Z: z})
		case "F":
			if len(fields) < 4 {
				return fmt.Errorf("ELIX F expects 3 vertices: %q", line)
			}
			refs := make([]elixRef, 0, len(fields)-1)
			for _, tok := range fields[1:] {
				ref, err := parseElixRef(tok, indexBase)
				if err != nil {
					return err
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
		return fmt.Errorf("ELIX vertex count mismatch: got %d, expected %d", len(mesh.Verts), wantVerts)
	}
	if hasUVs && wantUVs != len(mesh.UVs) {
		return fmt.Errorf("ELIX UV count mismatch: got %d, expected %d", len(mesh.UVs), wantUVs)
	}
	if hasNorms && wantNorms != len(mesh.Normals) {
		return fmt.Errorf("ELIX normal count mismatch: got %d, expected %d", len(mesh.Normals), wantNorms)
	}
	if hasFaces && wantFaces != len(mesh.Faces) {
		return fmt.Errorf("ELIX face count mismatch: got %d, expected %d", len(mesh.Faces), wantFaces)
	}
	return writeOBJ(mesh, outputOBJ)
}

func encodeCLIX(imagePath, clixPath string, st encodeSettings, ffmpegPath string) error {
	src, err := decodeImageFile(imagePath, ffmpegPath)
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
	var bgToken string
	if st.enableBackground {
		bg, bgShare = detectBackground(pixels)
		bgToken = rgbaToToken(bg)
	}
	useBG := st.enableBackground && bgShare >= st.backgroundMinShare
	if useBG && len(bgToken) < len("BG") {
		useBG = false
	}
	var tokens []string
	var prev *RGBA
	for _, px := range pixels {
		if useBG && px == bg {
			tokens = append(tokens, "BG")
			tmp := px
			prev = &tmp
			continue
		}
		if prev == nil {
			tokens = append(tokens, rgbaToToken(px))
			tmp := px
			prev = &tmp
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
	macroHexToName := map[string]string{}
	macrosOrdered := [][2]string{}
	freq := map[string]int{}
	for _, t := range tokens {
		if len(t) == 8 && isAllHex(t) {
			freq[t]++
		}
	}
	type kv struct {
		hex string
		n   int
	}
	list := make([]kv, 0, len(freq))
	for h, n := range freq {
		list = append(list, kv{h, n})
	}
	sort.Slice(list, func(i, j int) bool {
		if list[i].n != list[j].n {
			return list[i].n > list[j].n
		}
		return list[i].hex < list[j].hex
	})
	limit := len(macroNameAlphabet)
	if len(list) > limit {
		list = list[:limit]
	}
	names := generateMacroNames(len(list))
	for i, it := range list {
		name := names[i]
		macroHexToName[it.hex] = name
		macrosOrdered = append(macrosOrdered, [2]string{name, it.hex})
	}
	if len(macroHexToName) > 0 {
		for i := range tokens {
			if repl, ok := macroHexToName[tokens[i]]; ok {
				tokens[i] = repl
			}
		}
	}

	tmp := tokens
	if st.enableTokenRLE {
		tmp = rleTokens(tmp)
	}
	if st.enableSequenceRLE {
		tmp = sequenceRLE(tmp, st.sequenceRLEMaxSeqLen)
	}
	perLine := 1024
	if perLine <= 0 {
		perLine = len(tmp)
	}
	macroNamesSet := make(map[string]struct{}, len(macrosOrdered))
	for _, p := range macrosOrdered {
		macroNamesSet[p[0]] = struct{}{}
	}
	makeLine := func(slice []string) string {
		compact := strings.Join(slice, "")
		if len(slice) == 0 {
			return compact
		}
		if toks, err := tokenizeLineWithMacros(compact, macroNamesSet); err == nil {
			if equalSlice(toks, slice) {
				return compact
			}
		}
		return strings.Join(slice, " ")
	}
	lines := make([]string, 0, (len(tmp)+perLine-1)/perLine)
	for i := 0; i < len(tmp); i += perLine {
		end := i + perLine
		if end > len(tmp) {
			end = len(tmp)
		}
		lines = append(lines, makeLine(tmp[i:end]))
	}
	out, err := os.Create(clixPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := zstd.NewWriter(out, zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(level)))
	if err != nil {
		return err
	}
	bw := bufio.NewWriter(enc)
	writeLine := func(s string) error { _, err := bw.WriteString(s + "\n"); return err }
	if err := writeLine("CLIX " + clixVersion); err != nil {
		return err
	}
	if err := writeLine(fmt.Sprintf("RES=%dx%d", width, height)); err != nil {
		return err
	}
	if err := writeLine("ORDER=STREAM_GLOBAL"); err != nil {
		return err
	}
	encFlags := []string{"RLE", "SEQ"}
	if !st.enableTokenRLE && !st.enableSequenceRLE {
		encFlags = []string{"NONE"}
	} else if st.enableTokenRLE && !st.enableSequenceRLE {
		encFlags = []string{"RLE"}
	} else if !st.enableTokenRLE && st.enableSequenceRLE {
		encFlags = []string{"SEQ"}
	}
	if err := writeLine("ENCODING=" + strings.Join(encFlags, "+")); err != nil {
		return err
	}
	if useBG {
		if err := writeLine(fmt.Sprintf("BG=%02X%02X%02X%02X", bg.R, bg.G, bg.B, bg.A)); err != nil {
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
	if err := writeLine(fmt.Sprintf("ZSTD_LEVEL=%d", level)); err != nil {
		return err
	}
	if err := writeLine("HEX_ALPHA=1"); err != nil {
		return err
	}
	if len(macrosOrdered) > 0 {
		if err := writeLine(""); err != nil {
			return err
		}
		var b strings.Builder
		b.WriteString("M_S")
		for _, pair := range macrosOrdered {
			b.WriteString(pair[0])
			b.WriteString(pair[1])
		}
		b.WriteString("M_E")
		if err := writeLine(b.String()); err != nil {
			return err
		}
	}
	if err := writeLine(""); err != nil {
		return err
	}
	for _, ln := range lines {
		if err := writeLine(ln); err != nil {
			return err
		}
	}
	if err := bw.Flush(); err != nil {
		return err
	}
	if err := enc.Close(); err != nil {
		return err
	}
	if err := out.Sync(); err != nil {
		return err
	}
	return nil
}

const (
	opRepeat = 0x80
	opSeq    = 0x81
	opBlock  = 0x82
	opMotion = 0x83
	opPure0  = 0xF0
	opBG     = 0xFA
	opS      = 0xFB
	opRGBA   = 0xFC
	opT      = 0xFD
)

const (
	vlxFrameKey   = 0x01
	vlxFrameDelta = 0x02
	vlxFrameB     = 0x03
	vlxFlagBG     = 0x01
)

const (
	vlxDefaultBlockDim        = 8
	vlxDefaultSearchRadius    = 4
	vlxDefaultMotionThreshold = 1
	vlxDefaultBFrames         = 2
)

const (
	vlxDctRiceK    = 3
	vlxDctResRiceK = 2
	vlxMvRiceK     = 2
)

var blxPureList = []RGBA{{0, 0, 0, 255}, {255, 255, 255, 255}, {255, 0, 0, 255}, {0, 255, 0, 255}, {0, 0, 255, 255}, {255, 255, 0, 255}, {255, 165, 0, 255}, {128, 0, 128, 255}}
var blxPureIndex = map[string]byte{"K": 0, "W": 1, "R": 2, "G": 3, "B": 4, "Y": 5, "O": 6, "P": 7}

func writeUvarint(w io.Writer, x uint64) error {
	var buf [10]byte
	n := binary.PutUvarint(buf[:], x)
	_, err := w.Write(buf[:n])
	return err
}

func blxWriteSimpleToken(w io.Writer, tok string) error {
	if tok == "BG" {
		_, err := w.Write([]byte{opBG})
		return err
	}
	if tok == "S" {
		_, err := w.Write([]byte{opS})
		return err
	}
	if idx, ok := blxPureIndex[tok]; ok {
		_, err := w.Write([]byte{opPure0 + idx})
		return err
	}
	var px RGBA
	var err error
	switch {
	case len(tok) == 8 && isAllHex(tok):
		px, err = parseHexTokenCompact(tok)
	case strings.HasPrefix(tok, "#"):
		px, err = parseHexTokenHash(tok)
	default:
		px, err = tokenToRGBA(tok, nil, nil)
	}
	if err != nil {
		return err
	}
	if _, err := w.Write([]byte{opRGBA}); err != nil {
		return err
	}
	_, err = w.Write([]byte{px.R, px.G, px.B, px.A})
	return err
}

func blxParseGroup(token string) (innerTokens []string, count int, err error) {
	token = strings.TrimSpace(token)
	count = 1
	var inner string
	if strings.Contains(token, ")*") {
		pos := strings.LastIndex(token, ")*")
		inner = token[1:pos]
		cntStr := token[pos+2:]
		if !isAllDigits(cntStr) {
			return nil, 0, fmt.Errorf("bad repeat in %q", token)
		}
		v, _ := strconv.Atoi(cntStr)
		count = v
	} else {
		r := strings.LastIndexByte(token, ')')
		if r < 0 {
			return nil, 0, fmt.Errorf("malformed group: %q", token)
		}
		inner = token[1:r]
		tail := token[r+1:]
		if strings.HasPrefix(tail, "*") {
			nStr := tail[1:]
			if !isAllDigits(nStr) {
				return nil, 0, fmt.Errorf("bad repeat in %q", token)
			}
			v, _ := strconv.Atoi(nStr)
			count = v
		}
	}
	toks, err := tokenizeLine(inner)
	if err != nil {
		return nil, 0, err
	}
	exp, err := expandTokens(toks)
	if err != nil {
		return nil, 0, err
	}
	return exp, count, nil
}

func blxWriteRepeat(w io.Writer, base string, count int) error {
	if count <= 0 {
		return nil
	}
	if _, err := w.Write([]byte{opRepeat}); err != nil {
		return err
	}
	if err := blxWriteSimpleToken(w, base); err != nil {
		return err
	}
	return writeUvarint(w, uint64(count))
}

func blxWriteSeq(w io.Writer, inner []string, count int) error {
	if count <= 0 || len(inner) == 0 {
		return nil
	}
	if _, err := w.Write([]byte{opSeq}); err != nil {
		return err
	}
	if err := writeUvarint(w, uint64(len(inner))); err != nil {
		return err
	}
	if err := writeUvarint(w, uint64(count)); err != nil {
		return err
	}
	for _, t := range inner {
		if err := blxWriteSimpleToken(w, t); err != nil {
			return err
		}
	}
	return nil
}

func encodeBLIX(imagePath, blixPath string, st encodeSettings, ffmpegPath string) error {
	src, err := decodeImageFile(imagePath, ffmpegPath)
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
	width, height := b.Dx(), b.Dy()
	pixels := make([]RGBA, 0, width*height)
	for y := b.Min.Y; y < b.Max.Y; y++ {
		for x := b.Min.X; x < b.Max.X; x++ {
			pixels = append(pixels, fromColor(img.At(x, y)))
		}
	}
	var bg RGBA
	var bgShare float64
	var bgToken string
	if st.enableBackground {
		bg, bgShare = detectBackground(pixels)
		bgToken = rgbaToToken(bg)
	}
	useBG := st.enableBackground && bgShare >= st.backgroundMinShare
	if useBG && len(bgToken) < len("BG") {
		useBG = false
	}
	var tokens []string
	var prev *RGBA
	for _, px := range pixels {
		if useBG && px == bg {
			tokens = append(tokens, "BG")
			tmp := px
			prev = &tmp
			continue
		}
		if prev == nil {
			tokens = append(tokens, rgbaToToken(px))
			tmp := px
			prev = &tmp
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
	tmp := tokens
	if st.enableTokenRLE {
		tmp = rleTokens(tmp)
	}
	if st.enableSequenceRLE {
		tmp = sequenceRLE(tmp, st.sequenceRLEMaxSeqLen)
	}
	out, err := os.Create(blixPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := zstd.NewWriter(out, zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(level)))
	if err != nil {
		return err
	}
	bw := bufio.NewWriter(enc)
	if _, err := fmt.Fprintf(bw, "BLIX %s\nWIDTH=%d\nHEIGHT=%d\nZSTD_LEVEL=%d\n", blixVersion, width, height, level); err != nil {
		return err
	}
	if useBG {
		if _, err := fmt.Fprintf(bw, "BG=%02X%02X%02X%02X\n", bg.R, bg.G, bg.B, bg.A); err != nil {
			return err
		}
	}
	if _, err := bw.WriteString("\n"); err != nil {
		return err
	}
	for _, t := range tmp {
		if strings.HasPrefix(t, "(") {
			in, cnt, e := blxParseGroup(t)
			if e != nil {
				return e
			}
			if err := blxWriteSeq(bw, in, cnt); err != nil {
				return err
			}
			continue
		}
		if strings.Contains(t, "*") {
			i := strings.LastIndexByte(t, '*')
			base := t[:i]
			cntStr := t[i+1:]
			if !isAllDigits(cntStr) {
				return fmt.Errorf("bad repeat: %q", t)
			}
			n, _ := strconv.Atoi(cntStr)
			if err := blxWriteRepeat(bw, base, n); err != nil {
				return err
			}
			continue
		}
		if err := blxWriteSimpleToken(bw, t); err != nil {
			return err
		}
	}
	if err := bw.Flush(); err != nil {
		return err
	}
	if err := enc.Close(); err != nil {
		return err
	}
	if err := out.Sync(); err != nil {
		return err
	}
	return nil
}

func vlxBuildTokens(pixels []RGBA, prevFrame []RGBA, st encodeSettings, useTemporal bool) (tokens []string, bg *RGBA, useBG bool) {
	var bgVal RGBA
	var bgShare float64
	var bgToken string
	if st.enableBackground {
		bgVal, bgShare = detectBackground(pixels)
		bgToken = rgbaToToken(bgVal)
	}
	useBG = st.enableBackground && bgShare >= st.backgroundMinShare
	if useBG && len(bgToken) < len("BG") {
		useBG = false
	}
	var prev *RGBA
	for i, px := range pixels {
		if useTemporal && prevFrame != nil && i < len(prevFrame) && px == prevFrame[i] {
			tokens = append(tokens, "T")
			tmp := px
			prev = &tmp
			continue
		}
		if useBG && px == bgVal {
			tokens = append(tokens, "BG")
			tmp := px
			prev = &tmp
			continue
		}
		if prev == nil {
			tokens = append(tokens, rgbaToToken(px))
			tmp := px
			prev = &tmp
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
	if useBG {
		bg = &bgVal
	}
	return tokens, bg, useBG
}

func vlxBuildBlockTokens(pixels []RGBA, st encodeSettings, useBG bool, bg RGBA, blockX, blockY, blockW, blockH, frameW int) []string {
	var tokens []string
	var prev *RGBA
	for y := 0; y < blockH; y++ {
		for x := 0; x < blockW; x++ {
			idx := (blockY+y)*frameW + (blockX + x)
			px := pixels[idx]
			if useBG && px == bg {
				tokens = append(tokens, "BG")
				tmp := px
				prev = &tmp
				continue
			}
			if prev == nil {
				tokens = append(tokens, rgbaToToken(px))
				tmp := px
				prev = &tmp
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
	}
	return tokens
}

func blockMatchScore(pixels, prev []RGBA, frameW int, curX, curY, srcX, srcY, blockW, blockH, threshold int) (int, bool) {
	sad := 0
	limit := threshold * blockW * blockH * 4
	if threshold == 0 {
		for y := 0; y < blockH; y++ {
			for x := 0; x < blockW; x++ {
				cur := pixels[(curY+y)*frameW+(curX+x)]
				ref := prev[(srcY+y)*frameW+(srcX+x)]
				if cur != ref {
					return 1, false
				}
			}
		}
		return 0, true
	}
	for y := 0; y < blockH; y++ {
		for x := 0; x < blockW; x++ {
			cur := pixels[(curY+y)*frameW+(curX+x)]
			ref := prev[(srcY+y)*frameW+(srcX+x)]
			sad += absInt(int(cur.R) - int(ref.R))
			sad += absInt(int(cur.G) - int(ref.G))
			sad += absInt(int(cur.B) - int(ref.B))
			sad += absInt(int(cur.A) - int(ref.A))
			if sad > limit {
				return sad, false
			}
		}
	}
	return sad, true
}

func findMotionVector(pixels, prev []RGBA, frameW, frameH int, curX, curY, blockW, blockH, radius, threshold int) (int, int, bool) {
	if prev == nil {
		return 0, 0, false
	}
	if _, ok := blockMatchScore(pixels, prev, frameW, curX, curY, curX, curY, blockW, blockH, threshold); ok {
		return 0, 0, true
	}
	for dy := -radius; dy <= radius; dy++ {
		for dx := -radius; dx <= radius; dx++ {
			if dx == 0 && dy == 0 {
				continue
			}
			sx := curX + dx
			sy := curY + dy
			if sx < 0 || sy < 0 || sx+blockW > frameW || sy+blockH > frameH {
				continue
			}
			if _, ok := blockMatchScore(pixels, prev, frameW, curX, curY, sx, sy, blockW, blockH, threshold); ok {
				return dx, dy, true
			}
		}
	}
	return 0, 0, false
}

func blockMatchScorePlane(cur, ref []float64, frameW, frameH int, curX, curY, srcX, srcY, blockW, blockH, threshold int) (int, bool) {
	if curX < 0 || curY < 0 || srcX < 0 || srcY < 0 || curX+blockW > frameW || curY+blockH > frameH || srcX+blockW > frameW || srcY+blockH > frameH {
		return 0, false
	}
	sad := 0
	limit := threshold * blockW * blockH
	if threshold == 0 {
		for y := 0; y < blockH; y++ {
			for x := 0; x < blockW; x++ {
				curV := int(cur[(curY+y)*frameW+(curX+x)] + 0.5)
				refV := int(ref[(srcY+y)*frameW+(srcX+x)] + 0.5)
				if curV != refV {
					return 1, false
				}
			}
		}
		return 0, true
	}
	for y := 0; y < blockH; y++ {
		for x := 0; x < blockW; x++ {
			curV := int(cur[(curY+y)*frameW+(curX+x)] + 0.5)
			refV := int(ref[(srcY+y)*frameW+(srcX+x)] + 0.5)
			d := curV - refV
			if d < 0 {
				d = -d
			}
			sad += d
			if sad > limit {
				return sad, false
			}
		}
	}
	return sad, true
}

func findBestMotionVectorPlane(cur, ref []float64, frameW, frameH int, curX, curY, blockW, blockH, radius, threshold int) (int, int, int, bool) {
	if ref == nil {
		return 0, 0, 0, false
	}
	bestSad := int(^uint(0) >> 1)
	bestDx, bestDy := 0, 0
	found := false
	if radius < 0 {
		radius = 0
	}
	for dy := -radius; dy <= radius; dy++ {
		for dx := -radius; dx <= radius; dx++ {
			sx := curX + dx
			sy := curY + dy
			sad, ok := blockMatchScorePlane(cur, ref, frameW, frameH, curX, curY, sx, sy, blockW, blockH, threshold)
			if !ok {
				continue
			}
			if sad < bestSad {
				bestSad = sad
				bestDx = dx
				bestDy = dy
				found = true
				if sad == 0 {
					return bestDx, bestDy, bestSad, true
				}
			}
		}
	}
	return bestDx, bestDy, bestSad, found
}

func blockSADBi(cur, refA, refB []float64, frameW, frameH int, curX, curY, blockW, blockH, dxA, dyA, dxB, dyB int) (int, bool) {
	if refA == nil || refB == nil {
		return 0, false
	}
	sxA := curX + dxA
	syA := curY + dyA
	sxB := curX + dxB
	syB := curY + dyB
	if sxA < 0 || syA < 0 || sxB < 0 || syB < 0 || sxA+blockW > frameW || syA+blockH > frameH || sxB+blockW > frameW || syB+blockH > frameH {
		return 0, false
	}
	sad := 0
	for y := 0; y < blockH; y++ {
		for x := 0; x < blockW; x++ {
			curV := int(cur[(curY+y)*frameW+(curX+x)] + 0.5)
			a := int(refA[(syA+y)*frameW+(sxA+x)] + 0.5)
			b := int(refB[(syB+y)*frameW+(sxB+x)] + 0.5)
			p := (a + b) / 2
			d := curV - p
			if d < 0 {
				d = -d
			}
			sad += d
		}
	}
	return sad, true
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

func vlxWriteSimpleToken(w io.Writer, tok string) error {
	switch tok {
	case "BG":
		_, err := w.Write([]byte{opBG})
		return err
	case "S":
		_, err := w.Write([]byte{opS})
		return err
	case "T":
		_, err := w.Write([]byte{opT})
		return err
	}
	if idx, ok := blxPureIndex[tok]; ok {
		_, err := w.Write([]byte{opPure0 + idx})
		return err
	}
	var px RGBA
	var err error
	switch {
	case len(tok) == 8 && isAllHex(tok):
		px, err = parseHexTokenCompact(tok)
	case strings.HasPrefix(tok, "#"):
		px, err = parseHexTokenHash(tok)
	default:
		px, err = tokenToRGBA(tok, nil, nil)
	}
	if err != nil {
		return err
	}
	if _, err := w.Write([]byte{opRGBA}); err != nil {
		return err
	}
	_, err = w.Write([]byte{px.R, px.G, px.B, px.A})
	return err
}

func vlxWriteRepeat(w io.Writer, base string, count int) error {
	if count <= 0 {
		return nil
	}
	if _, err := w.Write([]byte{opRepeat}); err != nil {
		return err
	}
	if err := vlxWriteSimpleToken(w, base); err != nil {
		return err
	}
	return writeUvarint(w, uint64(count))
}

func vlxWriteSeq(w io.Writer, inner []string, count int) error {
	if count <= 0 || len(inner) == 0 {
		return nil
	}
	if _, err := w.Write([]byte{opSeq}); err != nil {
		return err
	}
	if err := writeUvarint(w, uint64(len(inner))); err != nil {
		return err
	}
	if err := writeUvarint(w, uint64(count)); err != nil {
		return err
	}
	for _, t := range inner {
		if err := vlxWriteSimpleToken(w, t); err != nil {
			return err
		}
	}
	return nil
}

func listFrameFiles(dir string) ([]string, error) {
	entries, err := os.ReadDir(dir)
	if err != nil {
		return nil, err
	}
	var files []string
	for _, ent := range entries {
		if ent.IsDir() {
			continue
		}
		files = append(files, filepath.Join(dir, ent.Name()))
	}
	sort.Strings(files)
	return files, nil
}

func encodeVLIX(dirPath, outPath string, st encodeSettings, fps float64, keyInterval int, audio []byte, ffmpegPath string, motion bool, blockDim, searchRadius, motionThreshold int, codec string) error {
	if keyInterval <= 0 {
		keyInterval = 1
	}
	frames, err := listFrameFiles(dirPath)
	if err != nil {
		return err
	}
	if len(frames) == 0 {
		return errors.New("no frames found")
	}
	firstFile := frames[0]
	firstImgRaw, err := decodeImageFile(firstFile, ffmpegPath)
	if err != nil {
		return err
	}
	firstImg, err := prepareImageForEncoding(firstImgRaw, st)
	if err != nil {
		return err
	}
	b := firstImg.Bounds()
	width, height := b.Dx(), b.Dy()

	out, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := zstd.NewWriter(out, zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(level)))
	if err != nil {
		return err
	}
	bw := bufio.NewWriter(enc)
	writeLine := func(s string) error { _, err := bw.WriteString(s + "\n"); return err }
	writeLines := func(lines ...string) error {
		for _, line := range lines {
			if err := writeLine(line); err != nil {
				return err
			}
		}
		return nil
	}
	headerLines := []string{
		"VLIX " + vlixVersion,
		"CODEC=" + codec,
		"ENCODER=" + encoderVersion,
		"CLIX=" + clixVersion,
		"BLIX=" + blixVersion,
		fmt.Sprintf("WIDTH=%d", width),
		fmt.Sprintf("HEIGHT=%d", height),
		fmt.Sprintf("FPS=%.6g", fps),
		fmt.Sprintf("FRAMES=%d", len(frames)),
		fmt.Sprintf("KEY_INTERVAL=%d", keyInterval),
		fmt.Sprintf("MODE=%s", st.mode),
		fmt.Sprintf("ROUND_STEP=%d", st.roundStep),
		fmt.Sprintf("DELTA_SNAP_THRESHOLD=%d", st.deltaSnapThreshold),
		fmt.Sprintf("PALETTE_SIZE=%d", st.paletteSize),
		fmt.Sprintf("PALETTE_DITHER=%d", boolTo01(st.paletteDither)),
		fmt.Sprintf("BLOCK_SIZE=%d", st.blockSize),
		fmt.Sprintf("BLOCK_VAR_THRESHOLD=%g", st.blockVarThreshold),
		fmt.Sprintf("ZSTD_LEVEL=%d", level),
		"HEX_ALPHA=1",
	}
	if motion {
		headerLines = append(headerLines,
			"MOTION=1",
			fmt.Sprintf("BLOCK_DIM=%d", blockDim),
			fmt.Sprintf("SEARCH_RADIUS=%d", searchRadius),
			fmt.Sprintf("MOTION_THRESHOLD=%d", motionThreshold),
		)
	}
	if len(audio) > 0 {
		headerLines = append(headerLines,
			"AUDIO_CODEC=ALIX1",
			fmt.Sprintf("AUDIO_BYTES=%d", len(audio)),
		)
	}
	headerLines = append(headerLines, "")
	if err := writeLines(headerLines...); err != nil {
		return err
	}

	var prevFrame []RGBA
	for i, framePath := range frames {
		raw, err := decodeImageFile(framePath, ffmpegPath)
		if err != nil {
			return err
		}
		img, err := prepareImageForEncoding(raw, st)
		if err != nil {
			return err
		}
		if img.Bounds().Dx() != width || img.Bounds().Dy() != height {
			return fmt.Errorf("frame size mismatch for %s (got %dx%d, expected %dx%d)", framePath, img.Bounds().Dx(), img.Bounds().Dy(), width, height)
		}
		pixels := imageToPixels(img)
		keyframe := i%keyInterval == 0
		frameType := byte(vlxFrameDelta)
		useTemporal := true
		if keyframe || prevFrame == nil {
			frameType = vlxFrameKey
			useTemporal = false
		}
		if err := bw.WriteByte(frameType); err != nil {
			return err
		}
		if motion {
			flags := byte(0)
			var bg RGBA
			var useBG bool
			if st.enableBackground {
				var share float64
				bg, share = detectBackground(pixels)
				if share >= st.backgroundMinShare && len(rgbaToToken(bg)) >= len("BG") {
					useBG = true
				}
			}
			if useBG {
				flags |= vlxFlagBG
			}
			if err := bw.WriteByte(flags); err != nil {
				return err
			}
			if useBG {
				if _, err := bw.Write([]byte{bg.R, bg.G, bg.B, bg.A}); err != nil {
					return err
				}
			}
			blockW := blockDim
			blockH := blockDim
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
					if prevFrame != nil {
						if dx, dy, ok := findMotionVector(pixels, prevFrame, width, height, bx, by, ww, hh, searchRadius, motionThreshold); ok {
							if err := bw.WriteByte(opMotion); err != nil {
								return err
							}
							if err := bw.WriteByte(byte(int8(dx))); err != nil {
								return err
							}
							if err := bw.WriteByte(byte(int8(dy))); err != nil {
								return err
							}
							continue
						}
					}
					if err := bw.WriteByte(opBlock); err != nil {
						return err
					}
					tokens := vlxBuildBlockTokens(pixels, st, useBG, bg, bx, by, ww, hh, width)
					if st.enableTokenRLE {
						tokens = rleTokens(tokens)
					}
					if st.enableSequenceRLE {
						tokens = sequenceRLE(tokens, st.sequenceRLEMaxSeqLen)
					}
					for _, t := range tokens {
						if strings.HasPrefix(t, "(") {
							in, cnt, e := blxParseGroup(t)
							if e != nil {
								return e
							}
							if err := vlxWriteSeq(bw, in, cnt); err != nil {
								return err
							}
							continue
						}
						if strings.Contains(t, "*") {
							i := strings.LastIndexByte(t, '*')
							base := t[:i]
							cntStr := t[i+1:]
							if !isAllDigits(cntStr) {
								return fmt.Errorf("bad repeat: %q", t)
							}
							n, _ := strconv.Atoi(cntStr)
							if err := vlxWriteRepeat(bw, base, n); err != nil {
								return err
							}
							continue
						}
						if err := vlxWriteSimpleToken(bw, t); err != nil {
							return err
						}
					}
				}
			}
		} else {
			tokens, bgPtr, useBGTokens := vlxBuildTokens(pixels, prevFrame, st, useTemporal)
			if st.enableTokenRLE {
				tokens = rleTokens(tokens)
			}
			if st.enableSequenceRLE {
				tokens = sequenceRLE(tokens, st.sequenceRLEMaxSeqLen)
			}
			flags := byte(0)
			if useBGTokens {
				flags |= vlxFlagBG
			}
			if err := bw.WriteByte(flags); err != nil {
				return err
			}
			if useBGTokens && bgPtr != nil {
				if _, err := bw.Write([]byte{bgPtr.R, bgPtr.G, bgPtr.B, bgPtr.A}); err != nil {
					return err
				}
			}
			for _, t := range tokens {
				if strings.HasPrefix(t, "(") {
					in, cnt, e := blxParseGroup(t)
					if e != nil {
						return e
					}
					if err := vlxWriteSeq(bw, in, cnt); err != nil {
						return err
					}
					continue
				}
				if strings.Contains(t, "*") {
					i := strings.LastIndexByte(t, '*')
					base := t[:i]
					cntStr := t[i+1:]
					if !isAllDigits(cntStr) {
						return fmt.Errorf("bad repeat: %q", t)
					}
					n, _ := strconv.Atoi(cntStr)
					if err := vlxWriteRepeat(bw, base, n); err != nil {
						return err
					}
					continue
				}
				if err := vlxWriteSimpleToken(bw, t); err != nil {
					return err
				}
			}
		}
		prevFrame = pixels
	}
	if len(audio) > 0 {
		if _, err := bw.Write(audio); err != nil {
			return err
		}
	}
	if err := bw.Flush(); err != nil {
		return err
	}
	if err := enc.Close(); err != nil {
		return err
	}
	if err := out.Sync(); err != nil {
		return err
	}
	return nil
}

func encodeVLIX2(dirPath, outPath string, st encodeSettings, fps float64, keyInterval int, audio []byte, ffmpegPath string, chromaMode string, dctQuality, dctResQuality int, motion bool, blockDim, searchRadius, motionThreshold int, bframes int) error {
	if keyInterval <= 0 {
		keyInterval = 1
	}
	dctPred := true
	dctZeroRun := true
	dctBlockSkip := true
	dctAcMag := true
	dctPlaneMask := true
	frames, err := listFrameFiles(dirPath)
	if err != nil {
		return err
	}
	if len(frames) == 0 {
		return errors.New("no frames found")
	}
	firstFile := frames[0]
	firstImgRaw, err := decodeImageFile(firstFile, ffmpegPath)
	if err != nil {
		return err
	}
	firstImg, err := prepareImageForEncoding(firstImgRaw, st)
	if err != nil {
		return err
	}
	b := firstImg.Bounds()
	width, height := b.Dx(), b.Dy()
	alphaEnabled := imageHasAlpha(firstImg)
	if !alphaEnabled && len(frames) > 1 {
		if hasAlpha, err := detectFramesAlpha(frames[1:], st, ffmpegPath); err != nil {
			return err
		} else {
			alphaEnabled = hasAlpha
		}
	}

	out, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := zstd.NewWriter(out, zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(level)))
	if err != nil {
		return err
	}
	bw := bufio.NewWriter(enc)
	writeLine := func(s string) error { _, err := bw.WriteString(s + "\n"); return err }
	writeLines := func(lines ...string) error {
		for _, line := range lines {
			if err := writeLine(line); err != nil {
				return err
			}
		}
		return nil
	}
	headerLines := []string{
		"VLIX " + vlixVersion,
		"CODEC=" + vlixCodecV2,
		"ENCODER=" + encoderVersion,
		fmt.Sprintf("WIDTH=%d", width),
		fmt.Sprintf("HEIGHT=%d", height),
		fmt.Sprintf("FPS=%.6g", fps),
		fmt.Sprintf("FRAMES=%d", len(frames)),
		fmt.Sprintf("KEY_INTERVAL=%d", keyInterval),
		fmt.Sprintf("CHROMA=%s", strings.ToUpper(chromaMode)),
		fmt.Sprintf("BLOCK_DIM=%d", blockDim),
		fmt.Sprintf("BFRAMES=%d", bframes),
		"DCT_BLOCK=8",
		fmt.Sprintf("DCT_QUALITY=%d", dctQuality),
		fmt.Sprintf("DCT_RES_QUALITY=%d", dctResQuality),
		fmt.Sprintf("DCT_DC_PRED=%d", boolToInt(dctPred)),
		fmt.Sprintf("DCT_ZERO_RUN=%d", boolToInt(dctZeroRun)),
		fmt.Sprintf("DCT_BLOCK_SKIP=%d", boolToInt(dctBlockSkip)),
		fmt.Sprintf("DCT_AC_MAG=%d", boolToInt(dctAcMag)),
		fmt.Sprintf("DCT_PLANE_MASK=%d", boolToInt(dctPlaneMask)),
		fmt.Sprintf("DCT_RICE_K=%d", vlxDctRiceK),
		fmt.Sprintf("DCT_RES_RICE_K=%d", vlxDctResRiceK),
		fmt.Sprintf("MV_RICE_K=%d", vlxMvRiceK),
		fmt.Sprintf("MOTION=%d", boolToInt(motion)),
		fmt.Sprintf("SEARCH_RADIUS=%d", searchRadius),
		fmt.Sprintf("MOTION_THRESHOLD=%d", motionThreshold),
		fmt.Sprintf("ZSTD_LEVEL=%d", level),
		fmt.Sprintf("ALPHA=%d", boolToInt(alphaEnabled)),
	}
	if len(audio) > 0 {
		headerLines = append(headerLines,
			"AUDIO_CODEC=ALIX1",
			fmt.Sprintf("AUDIO_BYTES=%d", len(audio)),
		)
	}
	headerLines = append(headerLines, "")
	if err := writeLines(headerLines...); err != nil {
		return err
	}

	qY := scaleQuantTable(jpegLumaQuant, dctQuality)
	qC := scaleQuantTable(jpegChromaQuant, dctQuality)
	qYRes := scaleQuantTable(jpegLumaQuant, dctResQuality)
	qCRes := scaleQuantTable(jpegChromaQuant, dctResQuality)
	encodePlane := func(w *bitWriter, plane []float64, pw, ph int, qtable [64]int, center bool, k uint8) error {
		return encodePlaneDCTRiceEx(w, plane, pw, ph, qtable, center, k, dctPred, dctZeroRun, dctBlockSkip, dctAcMag)
	}

	plans, coding := buildVLIX2Plan(len(frames), keyInterval, bframes)
	subX, subY := 1, 1
	switch strings.ToLower(strings.TrimSpace(chromaMode)) {
	case "422":
		subX = 2
	case "420":
		subX = 2
		subY = 2
	}
	refPlanes := make(map[int]ycbcrPlanes)
	bwBlocks := (width + blockDim - 1) / blockDim
	bhBlocks := (height + blockDim - 1) / blockDim

	for _, idx := range coding {
		if idx < 0 || idx >= len(frames) {
			return fmt.Errorf("frame index out of range: %d", idx)
		}
		plan := plans[idx]
		framePath := frames[idx]
		raw, err := decodeImageFile(framePath, ffmpegPath)
		if err != nil {
			return err
		}
		img, err := prepareImageForEncoding(raw, st)
		if err != nil {
			return err
		}
		if img.Bounds().Dx() != width || img.Bounds().Dy() != height {
			return fmt.Errorf("frame size mismatch for %s (got %dx%d, expected %dx%d)", framePath, img.Bounds().Dx(), img.Bounds().Dy(), width, height)
		}
		planes := buildYCbCrPlanes(img, chromaMode)
		if !alphaEnabled {
			planes.a = filledPlane(width*height, 255)
		}

		if err := bw.WriteByte(plan.ftype); err != nil {
			return err
		}
		if err := writeUvarint(bw, uint64(plan.idx)); err != nil {
			return err
		}

		if plan.ftype == vlxFrameKey {
			var coeffBits bitWriter
			if dctPlaneMask {
				mask := uint8(0x1 | 0x2 | 0x4)
				if alphaEnabled {
					mask |= 0x8
				}
				coeffBits.WriteBits(uint64(mask), 8)
			}
			if err := encodePlane(&coeffBits, planes.y, planes.w, planes.h, qY, true, vlxDctRiceK); err != nil {
				return err
			}
			if err := encodePlane(&coeffBits, planes.cb, planes.cw, planes.ch, qC, true, vlxDctRiceK); err != nil {
				return err
			}
			if err := encodePlane(&coeffBits, planes.cr, planes.cw, planes.ch, qC, true, vlxDctRiceK); err != nil {
				return err
			}
			if alphaEnabled {
				if err := encodePlane(&coeffBits, planes.a, planes.w, planes.h, qY, true, vlxDctRiceK); err != nil {
					return err
				}
			}
			coeffBytes := coeffBits.Bytes()
			if err := writeUvarint(bw, uint64(len(coeffBytes))); err != nil {
				return err
			}
			if _, err := bw.Write(coeffBytes); err != nil {
				return err
			}
			refPlanes[plan.idx] = planes
			continue
		}

		prevRef, ok := refPlanes[plan.refPrev]
		if !ok {
			return fmt.Errorf("missing reference frame %d", plan.refPrev)
		}
		nextRef := prevRef
		if plan.ftype == vlxFrameB {
			nr, ok := refPlanes[plan.refNext]
			if !ok {
				return fmt.Errorf("missing reference frame %d", plan.refNext)
			}
			nextRef = nr
		}

		if err := writeUvarint(bw, uint64(plan.refPrev)); err != nil {
			return err
		}
		if err := writeUvarint(bw, uint64(plan.refNext)); err != nil {
			return err
		}

		predY := make([]float64, width*height)
		var predA []float64
		if alphaEnabled {
			predA = make([]float64, width*height)
		}
		predCb := make([]float64, planes.cw*planes.ch)
		predCr := make([]float64, planes.cw*planes.ch)

		var mvBits bitWriter
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
				mode := uint8(0)
				dx1, dy1, dx2, dy2 := 0, 0, 0, 0
				if motion {
					switch plan.ftype {
					case vlxFrameDelta:
						dx, dy, sad, ok := findBestMotionVectorPlane(planes.y, prevRef.y, width, height, bxPix, byPix, bwPix, bhPix, searchRadius, motionThreshold)
						if ok && (motionThreshold > 0 || sad == 0) {
							mode = 1
							dx1, dy1 = dx, dy
						}
					case vlxFrameB:
						dxP, dyP, sadP, okP := findBestMotionVectorPlane(planes.y, prevRef.y, width, height, bxPix, byPix, bwPix, bhPix, searchRadius, motionThreshold)
						dxN, dyN, sadN, okN := findBestMotionVectorPlane(planes.y, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, searchRadius, motionThreshold)
						bestSad := int(^uint(0) >> 1)
						if okP {
							mode = 1
							bestSad = sadP
							dx1, dy1 = dxP, dyP
						}
						if okN && sadN < bestSad {
							mode = 2
							bestSad = sadN
							dx1, dy1 = dxN, dyN
						}
						if okP && okN {
							if sadBi, ok := blockSADBi(planes.y, prevRef.y, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, dxP, dyP, dxN, dyN); ok {
								limit := motionThreshold * bwPix * bhPix
								if motionThreshold == 0 {
									limit = 0
								}
								if sadBi <= limit && sadBi < bestSad {
									mode = 3
									dx1, dy1, dx2, dy2 = dxP, dyP, dxN, dyN
								}
							}
						}
					}
				}

				mvBits.WriteBits(uint64(mode), 2)
				switch mode {
				case 1, 2:
					writeRiceSigned(&mvBits, dx1, vlxMvRiceK)
					writeRiceSigned(&mvBits, dy1, vlxMvRiceK)
				case 3:
					writeRiceSigned(&mvBits, dx1, vlxMvRiceK)
					writeRiceSigned(&mvBits, dy1, vlxMvRiceK)
					writeRiceSigned(&mvBits, dx2, vlxMvRiceK)
					writeRiceSigned(&mvBits, dy2, vlxMvRiceK)
				}

				switch mode {
				case 1:
					fillPredBlock(predY, prevRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					if alphaEnabled {
						fillPredBlock(predA, prevRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					}
					fillPredBlockChroma(predCb, prevRef.cb, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					fillPredBlockChroma(predCr, prevRef.cr, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
				case 2:
					fillPredBlock(predY, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					if alphaEnabled {
						fillPredBlock(predA, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					}
					fillPredBlockChroma(predCb, nextRef.cb, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
					fillPredBlockChroma(predCr, nextRef.cr, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1)
				case 3:
					fillPredBlockBi(predY, prevRef.y, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					if alphaEnabled {
						fillPredBlockBi(predA, prevRef.a, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					}
					fillPredBlockChromaBi(predCb, prevRef.cb, nextRef.cb, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
					fillPredBlockChromaBi(predCr, prevRef.cr, nextRef.cr, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, dx1, dy1, dx2, dy2)
				}
			}
		}

		mvBytes := mvBits.Bytes()
		if err := writeUvarint(bw, uint64(len(mvBytes))); err != nil {
			return err
		}
		if len(mvBytes) > 0 {
			if _, err := bw.Write(mvBytes); err != nil {
				return err
			}
		}

		resY := diffPlane(planes.y, predY)
		resCb := diffPlane(planes.cb, predCb)
		resCr := diffPlane(planes.cr, predCr)
		var resA []float64
		if alphaEnabled {
			resA = diffPlane(planes.a, predA)
		}
		var coeffBits bitWriter
		mask := uint8(0x1 | 0x2 | 0x4)
		if alphaEnabled {
			mask |= 0x8
		}
		if dctPlaneMask {
			mask = 0
			if !planeAllZero(resY, 1e-3) {
				mask |= 0x1
			}
			if !planeAllZero(resCb, 1e-3) {
				mask |= 0x2
			}
			if !planeAllZero(resCr, 1e-3) {
				mask |= 0x4
			}
			if alphaEnabled && !planeAllZero(resA, 1e-3) {
				mask |= 0x8
			}
			coeffBits.WriteBits(uint64(mask), 8)
		}
		if !dctPlaneMask || mask&0x1 != 0 {
			if err := encodePlane(&coeffBits, resY, planes.w, planes.h, qYRes, false, vlxDctResRiceK); err != nil {
				return err
			}
		}
		if !dctPlaneMask || mask&0x2 != 0 {
			if err := encodePlane(&coeffBits, resCb, planes.cw, planes.ch, qCRes, false, vlxDctResRiceK); err != nil {
				return err
			}
		}
		if !dctPlaneMask || mask&0x4 != 0 {
			if err := encodePlane(&coeffBits, resCr, planes.cw, planes.ch, qCRes, false, vlxDctResRiceK); err != nil {
				return err
			}
		}
		if alphaEnabled && (!dctPlaneMask || mask&0x8 != 0) {
			if err := encodePlane(&coeffBits, resA, planes.w, planes.h, qYRes, false, vlxDctResRiceK); err != nil {
				return err
			}
		}
		coeffBytes := coeffBits.Bytes()
		if err := writeUvarint(bw, uint64(len(coeffBytes))); err != nil {
			return err
		}
		if len(coeffBytes) > 0 {
			if _, err := bw.Write(coeffBytes); err != nil {
				return err
			}
		}

		if plan.ftype == vlxFrameDelta {
			refPlanes[plan.idx] = planes
		}
	}
	if len(audio) > 0 {
		if _, err := bw.Write(audio); err != nil {
			return err
		}
	}
	if err := bw.Flush(); err != nil {
		return err
	}
	if err := enc.Close(); err != nil {
		return err
	}
	if err := out.Sync(); err != nil {
		return err
	}
	return nil
}

type simpleSym struct {
	kind byte
	px   RGBA
}

type vlix2FramePlan struct {
	idx     int
	ftype   byte
	refPrev int
	refNext int
}

func buildVLIX2Plan(total, keyInterval, bframes int) ([]vlix2FramePlan, []int) {
	if keyInterval <= 0 {
		keyInterval = 1
	}
	if bframes < 0 {
		bframes = 0
	}
	pInterval := bframes + 1
	plans := make([]vlix2FramePlan, total)
	var coding []int
	for gopStart := 0; gopStart < total; gopStart += keyInterval {
		gopEnd := gopStart + keyInterval
		if gopEnd > total {
			gopEnd = total
		}
		refs := []int{gopStart}
		if pInterval > 0 {
			for r := gopStart + pInterval; r < gopEnd; r += pInterval {
				refs = append(refs, r)
			}
		}
		if refs[len(refs)-1] != gopEnd-1 {
			refs = append(refs, gopEnd-1)
		}
		prevRef := refs[0]
		plans[prevRef] = vlix2FramePlan{idx: prevRef, ftype: vlxFrameKey, refPrev: -1, refNext: -1}
		coding = append(coding, prevRef)
		for i := 1; i < len(refs); i++ {
			ref := refs[i]
			plans[ref] = vlix2FramePlan{idx: ref, ftype: vlxFrameDelta, refPrev: prevRef, refNext: prevRef}
			coding = append(coding, ref)
			for b := prevRef + 1; b < ref; b++ {
				plans[b] = vlix2FramePlan{idx: b, ftype: vlxFrameB, refPrev: prevRef, refNext: ref}
				coding = append(coding, b)
			}
			prevRef = ref
		}
	}
	return plans, coding
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
	case op >= opPure0 && op <= opPure0+7:
		return simpleSym{kind: sKindPure, px: blxPureList[int(op-opPure0)]}, nil
	case op == opBG:
		return simpleSym{kind: sKindBG}, nil
	case op == opS:
		return simpleSym{kind: sKindS}, nil
	case op == opRGBA:
		b := make([]byte, 4)
		if _, err := io.ReadFull(br, b); err != nil {
			return simpleSym{}, err
		}
		return simpleSym{kind: sKindLit, px: RGBA{b[0], b[1], b[2], b[3]}}, nil
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

func emitSimpleSym(sym simpleSym, bg *RGBA, prev **RGBA, out *[]RGBA) error {
	switch sym.kind {
	case sKindPure, sKindLit:
		*out = append(*out, sym.px)
		tmp := sym.px
		*prev = &tmp
		return nil
	case sKindBG:
		if bg == nil {
			return errors.New("BG token but no BG in header")
		}
		*out = append(*out, *bg)
		tmp := *bg
		*prev = &tmp
		return nil
	case sKindS:
		if *prev == nil {
			return errors.New("s before previous")
		}
		*out = append(*out, **prev)
		tmp := **prev
		*prev = &tmp
		return nil
	default:
		return errors.New("bad simple kind")
	}
}

func decodeBLIX(path, outputPNG string) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	zr, err := zstd.NewReader(f)
	if err != nil {
		return err
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
	h1, err := readLine()
	if err != nil {
		return err
	}
	if !strings.HasPrefix(h1, "BLIX") {
		return fmt.Errorf("not a BLIX stream: %q", h1)
	}
	wline, err := readLine()
	if err != nil {
		return err
	}
	hline, err := readLine()
	if err != nil {
		return err
	}
	var bg *RGBA
	for {
		line, e := readLine()
		if e != nil {
			return e
		}
		if line == "" {
			break
		}
		if strings.HasPrefix(line, "BG=") {
			hex := strings.TrimPrefix(line, "BG=")
			p, e2 := parseHexTokenCompact(hex)
			if e2 != nil {
				return e2
			}
			bg = &p
		}
	}
	var width, height int
	if strings.HasPrefix(wline, "WIDTH=") {
		width, _ = strconv.Atoi(strings.SplitN(wline, "=", 2)[1])
	}
	if strings.HasPrefix(hline, "HEIGHT=") {
		height, _ = strconv.Atoi(strings.SplitN(hline, "=", 2)[1])
	}
	if width <= 0 || height <= 0 {
		return errors.New("invalid BLIX header (WIDTH/HEIGHT)")
	}
	pixels := make([]RGBA, 0, width*height)
	var prev *RGBA
	for len(pixels) < width*height {
		op, e := br.ReadByte()
		if e != nil {
			return e
		}
		switch op {
		case opRepeat:
			sub, e2 := readSimpleSym(br)
			if e2 != nil {
				return e2
			}
			cnt, e3 := binary.ReadUvarint(br)
			if e3 != nil {
				return e3
			}
			for i := uint64(0); i < cnt; i++ {
				if e := emitSimpleSym(sub, bg, &prev, &pixels); e != nil {
					return e
				}
			}
		case opSeq:
			L, e2 := binary.ReadUvarint(br)
			if e2 != nil {
				return e2
			}
			N, e3 := binary.ReadUvarint(br)
			if e3 != nil {
				return e3
			}
			steps := make([]simpleSym, L)
			for i := uint64(0); i < L; i++ {
				sym, e4 := readSimpleSym(br)
				if e4 != nil {
					return e4
				}
				steps[i] = sym
			}
			for r := uint64(0); r < N; r++ {
				for i := 0; i < len(steps); i++ {
					if e := emitSimpleSym(steps[i], bg, &prev, &pixels); e != nil {
						return e
					}
				}
			}
		default:
			sym, e2 := readSimpleSymFromOp(op, br)
			if e2 != nil {
				return e2
			}
			if e := emitSimpleSym(sym, bg, &prev, &pixels); e != nil {
				return e
			}
		}
	}
	if len(pixels) != width*height {
		return fmt.Errorf("decoded %d pixels, expected %d", len(pixels), width*height)
	}
	out := image.NewNRGBA(image.Rect(0, 0, width, height))
	i := 0
	for y := 0; y < height; y++ {
		for x := 0; x < width; x++ {
			out.SetNRGBA(x, y, pixels[i].toColor())
			i++
		}
	}
	f2, err := os.Create(outputPNG)
	if err != nil {
		return err
	}
	defer f2.Close()
	return png.Encode(f2, out)
}

func readVlxSimpleSymFromOp(op byte, br *bufio.Reader) (simpleSym, error) {
	switch {
	case op >= opPure0 && op <= opPure0+7:
		return simpleSym{kind: sKindPure, px: blxPureList[int(op-opPure0)]}, nil
	case op == opBG:
		return simpleSym{kind: sKindBG}, nil
	case op == opS:
		return simpleSym{kind: sKindS}, nil
	case op == opT:
		return simpleSym{kind: sKindT}, nil
	case op == opRGBA:
		b := make([]byte, 4)
		if _, err := io.ReadFull(br, b); err != nil {
			return simpleSym{}, err
		}
		return simpleSym{kind: sKindLit, px: RGBA{b[0], b[1], b[2], b[3]}}, nil
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

func emitVlxSym(sym simpleSym, bg *RGBA, prev **RGBA, prevFrame []RGBA, out *[]RGBA, allowTemporal bool) error {
	switch sym.kind {
	case sKindPure, sKindLit:
		*out = append(*out, sym.px)
		tmp := sym.px
		*prev = &tmp
		return nil
	case sKindBG:
		if bg == nil {
			return errors.New("BG token but no BG in header")
		}
		*out = append(*out, *bg)
		tmp := *bg
		*prev = &tmp
		return nil
	case sKindS:
		if *prev == nil {
			return errors.New("s before previous")
		}
		*out = append(*out, **prev)
		tmp := **prev
		*prev = &tmp
		return nil
	case sKindT:
		if !allowTemporal {
			return errors.New("T token in keyframe")
		}
		if prevFrame == nil {
			return errors.New("T token but no previous frame")
		}
		idx := len(*out)
		if idx >= len(prevFrame) {
			return errors.New("T token out of range")
		}
		px := prevFrame[idx]
		*out = append(*out, px)
		tmp := px
		*prev = &tmp
		return nil
	default:
		return errors.New("bad simple kind")
	}
}

func emitVlxSymBlock(sym simpleSym, bg *RGBA, prev **RGBA, out *[]RGBA) error {
	switch sym.kind {
	case sKindPure, sKindLit:
		*out = append(*out, sym.px)
		tmp := sym.px
		*prev = &tmp
		return nil
	case sKindBG:
		if bg == nil {
			return errors.New("BG token but no BG in header")
		}
		*out = append(*out, *bg)
		tmp := *bg
		*prev = &tmp
		return nil
	case sKindS:
		if *prev == nil {
			return errors.New("s before previous")
		}
		*out = append(*out, **prev)
		tmp := **prev
		*prev = &tmp
		return nil
	case sKindT:
		return errors.New("T token in block stream")
	default:
		return errors.New("bad simple kind")
	}
}

func decodeVLIX(path, outDir string) ([]byte, error) {
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
	h1, err := readLine()
	if err != nil {
		return nil, err
	}
	if !strings.HasPrefix(h1, "VLIX") {
		return nil, fmt.Errorf("not a VLIX stream: %q", h1)
	}
	var width, height int
	var fps float64
	var framesExpected int
	var audioBytes int
	var motion bool
	blockDim := vlxDefaultBlockDim
	codec := ""
	chromaMode := "444"
	dctQuality := 75
	dctResQuality := 70
	dctRiceK := vlxDctRiceK
	dctResRiceK := vlxDctResRiceK
	mvRiceK := vlxMvRiceK
	dctPred := false
	dctZeroRun := false
	dctBlockSkip := false
	dctAcMag := false
	dctPlaneMask := false
	alphaEnabled := true
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
		switch key {
		case "CODEC":
			codec = strings.ToUpper(val)
		case "DCT_RICE_K":
			if v, err := strconv.Atoi(val); err == nil {
				dctRiceK = v
			}
		case "DCT_DC_PRED":
			dctPred = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_ZERO_RUN":
			dctZeroRun = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_BLOCK_SKIP":
			dctBlockSkip = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_AC_MAG":
			dctAcMag = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_PLANE_MASK":
			dctPlaneMask = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "ALPHA":
			alphaEnabled = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "DCT_RES_RICE_K":
			if v, err := strconv.Atoi(val); err == nil {
				dctResRiceK = v
			}
		case "MV_RICE_K":
			if v, err := strconv.Atoi(val); err == nil {
				mvRiceK = v
			}
		case "CHROMA":
			chromaMode = strings.ToLower(val)
		case "DCT_QUALITY":
			if v, err := strconv.Atoi(val); err == nil {
				dctQuality = v
			}
		case "DCT_RES_QUALITY":
			if v, err := strconv.Atoi(val); err == nil {
				dctResQuality = v
			}
		case "WIDTH":
			width, _ = strconv.Atoi(val)
		case "HEIGHT":
			height, _ = strconv.Atoi(val)
		case "FPS":
			fps, _ = strconv.ParseFloat(val, 64)
		case "FRAMES":
			framesExpected, _ = strconv.Atoi(val)
		case "AUDIO_BYTES":
			audioBytes, _ = strconv.Atoi(val)
		case "MOTION":
			motion = val == "1" || strings.EqualFold(val, "true") || strings.EqualFold(val, "yes")
		case "BLOCK_DIM":
			if v, err := strconv.Atoi(val); err == nil && v > 0 {
				blockDim = v
			}
		}
	}
	if width <= 0 || height <= 0 {
		return nil, errors.New("invalid VLIX header (WIDTH/HEIGHT)")
	}
	if codec == "" {
		codec = vlixCodecV1
	}
	if codec == vlixCodecV2 {
		if v, err := resolveChromaMode(chromaMode); err == nil {
			chromaMode = v
		} else {
			return nil, fmt.Errorf("invalid VLIX chroma mode: %s", chromaMode)
		}
		if dctQuality < 1 {
			dctQuality = 1
		} else if dctQuality > 100 {
			dctQuality = 100
		}
		if dctResQuality < 1 {
			dctResQuality = 1
		} else if dctResQuality > 100 {
			dctResQuality = 100
		}
		return decodeVLIX2(br, outDir, width, height, framesExpected, audioBytes, chromaMode, dctQuality, dctResQuality, blockDim, alphaEnabled, dctPred, dctZeroRun, dctBlockSkip, dctAcMag, dctPlaneMask, dctRiceK, dctResRiceK, mvRiceK)
	}
	if codec != vlixCodecV1 {
		return nil, fmt.Errorf("unsupported VLIX codec: %s", codec)
	}
	if fps <= 0 {
		fps = 30
	}
	if err := os.MkdirAll(outDir, 0o755); err != nil {
		return nil, err
	}
	var prevFrame []RGBA
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
		flags, e := br.ReadByte()
		if e != nil {
			return nil, e
		}
		var bg *RGBA
		if flags&vlxFlagBG != 0 {
			b := make([]byte, 4)
			if _, err := io.ReadFull(br, b); err != nil {
				return nil, err
			}
			tmp := RGBA{b[0], b[1], b[2], b[3]}
			bg = &tmp
		}
		allowTemporal := frameType == vlxFrameDelta
		if allowTemporal && prevFrame == nil {
			return nil, errors.New("delta frame with no previous frame")
		}
		var pixels []RGBA
		if motion {
			pixels = make([]RGBA, width*height)
			blockW := blockDim
			blockH := blockDim
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
						return nil, e2
					}
					switch op {
					case opMotion:
						if prevFrame == nil {
							return nil, errors.New("motion block without previous frame")
						}
						bdx, err := br.ReadByte()
						if err != nil {
							return nil, err
						}
						bdy, err := br.ReadByte()
						if err != nil {
							return nil, err
						}
						dx := int(int8(bdx))
						dy := int(int8(bdy))
						for y := 0; y < hh; y++ {
							for x := 0; x < ww; x++ {
								sx := bx + x + dx
								sy := by + y + dy
								if sx < 0 || sy < 0 || sx >= width || sy >= height {
									return nil, errors.New("motion vector out of bounds")
								}
								pixels[(by+y)*width+(bx+x)] = prevFrame[sy*width+sx]
							}
						}
					case opBlock:
						blockPixels := make([]RGBA, 0, ww*hh)
						var prev *RGBA
						for len(blockPixels) < ww*hh {
							op2, e3 := br.ReadByte()
							if e3 != nil {
								return nil, e3
							}
							switch op2 {
							case opRepeat:
								sub, e4 := readVlxSimpleSym(br)
								if e4 != nil {
									return nil, e4
								}
								cnt, e5 := binary.ReadUvarint(br)
								if e5 != nil {
									return nil, e5
								}
								for i := uint64(0); i < cnt; i++ {
									if e := emitVlxSymBlock(sub, bg, &prev, &blockPixels); e != nil {
										return nil, e
									}
								}
							case opSeq:
								L, e4 := binary.ReadUvarint(br)
								if e4 != nil {
									return nil, e4
								}
								N, e5 := binary.ReadUvarint(br)
								if e5 != nil {
									return nil, e5
								}
								steps := make([]simpleSym, L)
								for i := uint64(0); i < L; i++ {
									sym, e6 := readVlxSimpleSym(br)
									if e6 != nil {
										return nil, e6
									}
									steps[i] = sym
								}
								for r := uint64(0); r < N; r++ {
									for i := 0; i < len(steps); i++ {
										if e := emitVlxSymBlock(steps[i], bg, &prev, &blockPixels); e != nil {
											return nil, e
										}
									}
								}
							default:
								sym, e4 := readVlxSimpleSymFromOp(op2, br)
								if e4 != nil {
									return nil, e4
								}
								if e := emitVlxSymBlock(sym, bg, &prev, &blockPixels); e != nil {
									return nil, e
								}
							}
						}
						if len(blockPixels) != ww*hh {
							return nil, fmt.Errorf("block pixel mismatch: got %d expected %d", len(blockPixels), ww*hh)
						}
						i := 0
						for y := 0; y < hh; y++ {
							for x := 0; x < ww; x++ {
								pixels[(by+y)*width+(bx+x)] = blockPixels[i]
								i++
							}
						}
					default:
						return nil, fmt.Errorf("unknown block opcode 0x%X", op)
					}
				}
			}
		} else {
			pixels = make([]RGBA, 0, width*height)
			var prev *RGBA
			for len(pixels) < width*height {
				op, e2 := br.ReadByte()
				if e2 != nil {
					return nil, e2
				}
				switch op {
				case opRepeat:
					sub, e3 := readVlxSimpleSym(br)
					if e3 != nil {
						return nil, e3
					}
					cnt, e4 := binary.ReadUvarint(br)
					if e4 != nil {
						return nil, e4
					}
					for i := uint64(0); i < cnt; i++ {
						if e := emitVlxSym(sub, bg, &prev, prevFrame, &pixels, allowTemporal); e != nil {
							return nil, e
						}
					}
				case opSeq:
					L, e3 := binary.ReadUvarint(br)
					if e3 != nil {
						return nil, e3
					}
					N, e4 := binary.ReadUvarint(br)
					if e4 != nil {
						return nil, e4
					}
					steps := make([]simpleSym, L)
					for i := uint64(0); i < L; i++ {
						sym, e5 := readVlxSimpleSym(br)
						if e5 != nil {
							return nil, e5
						}
						steps[i] = sym
					}
					for r := uint64(0); r < N; r++ {
						for i := 0; i < len(steps); i++ {
							if e := emitVlxSym(steps[i], bg, &prev, prevFrame, &pixels, allowTemporal); e != nil {
								return nil, e
							}
						}
					}
				default:
					sym, e3 := readVlxSimpleSymFromOp(op, br)
					if e3 != nil {
						return nil, e3
					}
					if e := emitVlxSym(sym, bg, &prev, prevFrame, &pixels, allowTemporal); e != nil {
						return nil, e
					}
				}
			}
			if len(pixels) != width*height {
				return nil, fmt.Errorf("decoded %d pixels, expected %d", len(pixels), width*height)
			}
		}
		out := image.NewNRGBA(image.Rect(0, 0, width, height))
		i := 0
		for y := 0; y < height; y++ {
			for x := 0; x < width; x++ {
				out.SetNRGBA(x, y, pixels[i].toColor())
				i++
			}
		}
		outPath := filepath.Join(outDir, fmt.Sprintf("frame_%06d.png", framesDecoded))
		f2, err := os.Create(outPath)
		if err != nil {
			return nil, err
		}
		if err := png.Encode(f2, out); err != nil {
			f2.Close()
			return nil, err
		}
		if err := f2.Close(); err != nil {
			return nil, err
		}
		prevFrame = pixels
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

func decodeVLIX2(br *bufio.Reader, outDir string, width, height, framesExpected, audioBytes int, chromaMode string, dctQuality, dctResQuality int, blockDim int, alphaEnabled, dctPred, dctZeroRun, dctBlockSkip, dctAcMag, dctPlaneMask bool, dctRiceK, dctResRiceK, mvRiceK int) ([]byte, error) {
	if err := os.MkdirAll(outDir, 0o755); err != nil {
		return nil, err
	}
	if blockDim <= 0 {
		blockDim = vlxDefaultBlockDim
	}
	qY := scaleQuantTable(jpegLumaQuant, dctQuality)
	qC := scaleQuantTable(jpegChromaQuant, dctQuality)
	qYRes := scaleQuantTable(jpegLumaQuant, dctResQuality)
	qCRes := scaleQuantTable(jpegChromaQuant, dctResQuality)
	decodePlane := func(r *bitReader, pw, ph int, qtable [64]int, center bool, clamp bool, k uint8) ([]float64, error) {
		return decodePlaneDCTRiceEx(r, pw, ph, qtable, center, clamp, k, dctPred, dctZeroRun, dctBlockSkip, dctAcMag)
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
			img := planesToNRGBA(planes)
			outPath := filepath.Join(outDir, fmt.Sprintf("frame_%06d.png", displayIdx))
			f2, err := os.Create(outPath)
			if err != nil {
				return nil, err
			}
			if err := png.Encode(f2, img); err != nil {
				f2.Close()
				return nil, err
			}
			if err := f2.Close(); err != nil {
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
		img := planesToNRGBA(planes)
		outPath := filepath.Join(outDir, fmt.Sprintf("frame_%06d.png", displayIdx))
		f2, err := os.Create(outPath)
		if err != nil {
			return nil, err
		}
		if err := png.Encode(f2, img); err != nil {
			f2.Close()
			return nil, err
		}
		if err := f2.Close(); err != nil {
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
	var bg *RGBA
	var dataLines []string
	macros := make(map[string]RGBA)

	for _, ln := range rawLines {
		line := strings.TrimSpace(ln)
		if line == "" {
			continue
		}
		if strings.HasPrefix(line, "CLIX") {
			continue
		}
		if strings.HasPrefix(line, "RES=") {
			val := strings.TrimPrefix(line, "RES=")
			parts := strings.SplitN(val, "x", 2)
			if len(parts) == 2 {
				width, _ = strconv.Atoi(parts[0])
				height, _ = strconv.Atoi(parts[1])
			}
			continue
		}
		if strings.HasPrefix(line, "WIDTH=") {
			width, _ = strconv.Atoi(strings.SplitN(line, "=", 2)[1])
			continue
		}
		if strings.HasPrefix(line, "HEIGHT=") {
			height, _ = strconv.Atoi(strings.SplitN(line, "=", 2)[1])
			continue
		}
		if strings.HasPrefix(line, "BG=") {
			bgTok := strings.TrimSpace(strings.SplitN(line, "=", 2)[1])
			p, err := tokenToRGBA(bgTok, nil, nil)
			if err != nil {
				return err
			}
			tmp := p
			bg = &tmp
			continue
		}
		if strings.Contains(line, "M_S") && strings.Contains(line, "M_E") {
			start := strings.Index(line, "M_S")
			end := strings.LastIndex(line, "M_E")
			if start >= 0 && end > start+3 {
				body := line[start+3 : end]
				for len(body) >= 10 {
					name := body[:2]
					hex := body[2:10]
					if !isAllHex(hex) {
						break
					}
					px, e := parseHexTokenCompact(hex)
					if e != nil {
						return e
					}
					macros[name] = px
					body = body[10:]
				}
			}
			continue
		}
		if strings.Contains(line, "=") {
			key := strings.SplitN(line, "=", 2)[0]
			switch key {
			case "ORDER", "ENCODING", "MODE", "ROUND_STEP", "DELTA_SNAP_THRESHOLD", "PALETTE_SIZE", "PALETTE_DITHER", "BLOCK_SIZE", "BLOCK_VAR_THRESHOLD", "ZSTD_LEVEL", "HEX_ALPHA":
				continue
			}
		}
		dataLines = append(dataLines, line)
	}
	if width == 0 || height == 0 {
		return errors.New("missing RES or WIDTH/HEIGHT in CLIX header")
	}
	macroNames := make(map[string]struct{}, len(macros))
	for name := range macros {
		macroNames[name] = struct{}{}
	}
	var tokens []string
	for li, ln := range dataLines {
		if strings.TrimSpace(ln) == "" {
			continue
		}
		ts, err := tokenizeLineWithMacros(ln, macroNames)
		if err != nil {
			snippet := ln
			if len(snippet) > 120 {
				snippet = snippet[:120] + "..."
			}
			return fmt.Errorf("tokenization error on data line %d: %v\nline: %s", li+1, err, snippet)
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
		if pxm, ok := macros[base]; ok {
			pixels = append(pixels, pxm)
			tmp := pxm
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
		return fmt.Errorf("decoded pixel count mismatch: got %d, expected %d", len(pixels), total)
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

func parseBoolLoose(s string) (bool, error) {
	switch strings.ToLower(strings.TrimSpace(s)) {
	case "1", "t", "true", "yes", "y", "on":
		return true, nil
	case "0", "f", "false", "no", "n", "off":
		return false, nil
	}
	return false, fmt.Errorf("invalid bool: %q", s)
}

func isVideoExt(ext string) bool {
	switch strings.ToLower(ext) {
	case ".mp4", ".mov", ".mkv", ".webm", ".avi", ".m4v":
		return true
	default:
		return false
	}
}

func isAudioExt(ext string) bool {
	switch strings.ToLower(ext) {
	case ".mp3", ".wav", ".flac", ".ogg", ".opus", ".m4a", ".aac":
		return true
	default:
		return false
	}
}

type ffprobeStream struct {
	CodecType    string `json:"codec_type"`
	NbFrames     string `json:"nb_frames"`
	AvgFrameRate string `json:"avg_frame_rate"`
}

type ffprobeFormat struct {
	Duration string `json:"duration"`
}

type ffprobeOutput struct {
	Streams []ffprobeStream `json:"streams"`
	Format  ffprobeFormat   `json:"format"`
}

type mediaProbe struct {
	hasVideo    bool
	hasAudio    bool
	videoFrames int
	avgRate     float64
	duration    float64
}

func probeMedia(path, ffprobePath string) (mediaProbe, error) {
	cmd := exec.Command(
		ffprobePath,
		"-v", "error",
		"-show_entries", "stream=codec_type,nb_frames,avg_frame_rate",
		"-show_entries", "format=duration",
		"-of", "json",
		path,
	)
	out, err := cmd.Output()
	if err != nil {
		return mediaProbe{}, fmt.Errorf("ffprobe failed: %w", err)
	}
	var parsed ffprobeOutput
	if err := json.Unmarshal(out, &parsed); err != nil {
		return mediaProbe{}, fmt.Errorf("ffprobe parse error: %w", err)
	}
	probe := mediaProbe{}
	for _, stream := range parsed.Streams {
		switch stream.CodecType {
		case "video":
			probe.hasVideo = true
			if probe.videoFrames == 0 && stream.NbFrames != "" {
				if v, err := strconv.Atoi(stream.NbFrames); err == nil {
					probe.videoFrames = v
				}
			}
			if probe.avgRate == 0 && stream.AvgFrameRate != "" {
				if v, err := parseRate(stream.AvgFrameRate); err == nil {
					probe.avgRate = v
				}
			}
		case "audio":
			probe.hasAudio = true
		}
	}
	if parsed.Format.Duration != "" {
		if v, err := strconv.ParseFloat(parsed.Format.Duration, 64); err == nil {
			probe.duration = v
		}
	}
	return probe, nil
}

func detectMediaJob(path string, isDir bool) (jobKind, bool) {
	if isDir {
		return jobVideoEncode, false
	}
	ext := strings.ToLower(filepath.Ext(path))
	switch {
	case isVideoExt(ext):
		return jobVideoEncode, false
	case isAudioExt(ext):
		return jobAudioEncode, false
	case ext == ".alix" || ext == ".clxa" || ext == ".vla":
		return jobAudioConvert, false
	case ext == ".elix":
		return jobModelDecode, false
	case ext == ".obj":
		return jobModelEncode, false
	case ext == ".clix" || ext == ".blix":
		return jobImageDecode, false
	case ext == ".vlix":
		return jobVideoDecode, false
	}
	ffprobePath, err := findTool("ffprobe")
	if err != nil || ffprobePath == "" {
		return jobImageEncode, false
	}
	probe, err := probeMedia(path, ffprobePath)
	if err != nil {
		return jobImageEncode, false
	}
	if probe.hasVideo {
		isStill := !probe.hasAudio && (probe.videoFrames == 1 || probe.duration == 0 || probe.avgRate == 0)
		if isStill {
			return jobImageEncode, true
		}
		return jobVideoEncode, false
	}
	if probe.hasAudio {
		return jobAudioEncode, false
	}
	return jobImageEncode, false
}

const (
	alixBlockFrames = 1024
	alixOpSilence   = 0x00
	alixOpPCM       = 0x01
	alixOpD8        = 0x02
	alixOpD16       = 0x03
)

func findTool(name string) (string, error) {
	exe, err := os.Executable()
	if err != nil {
		return "", fmt.Errorf("%s not found in PATH", name)
	}
	dir := filepath.Dir(exe)
	candidates := []string{name}
	if !strings.HasSuffix(strings.ToLower(name), ".exe") {
		candidates = append(candidates, name+".exe")
	}
	for _, c := range candidates {
		p := filepath.Join(dir, c)
		if _, err := os.Stat(p); err == nil {
			return p, nil
		}
	}
	if p, err := exec.LookPath(name); err == nil {
		return p, nil
	}
	return "", fmt.Errorf("%s not found alongside executable or in PATH", name)
}

func parseRate(s string) (float64, error) {
	s = strings.TrimSpace(s)
	if s == "" {
		return 0, errors.New("empty rate")
	}
	if strings.Contains(s, "/") {
		parts := strings.SplitN(s, "/", 2)
		if len(parts) != 2 {
			return 0, fmt.Errorf("bad rate: %q", s)
		}
		num, err := strconv.ParseFloat(strings.TrimSpace(parts[0]), 64)
		if err != nil {
			return 0, err
		}
		den, err := strconv.ParseFloat(strings.TrimSpace(parts[1]), 64)
		if err != nil {
			return 0, err
		}
		if den == 0 {
			return 0, fmt.Errorf("zero rate denominator: %q", s)
		}
		return num / den, nil
	}
	return strconv.ParseFloat(s, 64)
}

func probeVideoFPS(path, ffprobePath string) (float64, error) {
	cmd := exec.Command(
		ffprobePath,
		"-v", "error",
		"-select_streams", "v:0",
		"-show_entries", "stream=avg_frame_rate,r_frame_rate",
		"-of", "default=nk=1:nw=1",
		path,
	)
	out, err := cmd.Output()
	if err != nil {
		return 0, fmt.Errorf("ffprobe failed: %w", err)
	}
	lines := strings.Split(strings.TrimSpace(string(out)), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" || line == "0/0" || line == "0" {
			continue
		}
		if v, err := parseRate(line); err == nil && v > 0 {
			return v, nil
		}
	}
	return 0, errors.New("no valid fps found")
}

func probeAudioInfo(path, ffprobePath string) (int, int, error) {
	cmd := exec.Command(
		ffprobePath,
		"-v", "error",
		"-select_streams", "a:0",
		"-show_entries", "stream=sample_rate,channels",
		"-of", "default=nk=1:nw=1",
		path,
	)
	out, err := cmd.Output()
	if err != nil {
		return 0, 0, fmt.Errorf("ffprobe failed: %w", err)
	}
	var nums []int
	for _, line := range strings.Split(strings.TrimSpace(string(out)), "\n") {
		line = strings.TrimSpace(line)
		if line == "" {
			continue
		}
		if v, err := strconv.Atoi(line); err == nil {
			nums = append(nums, v)
		}
	}
	if len(nums) == 0 {
		return 0, 0, errors.New("no audio stream info found")
	}
	sr := nums[0]
	ch := 2
	if len(nums) > 1 {
		ch = nums[1]
	}
	if sr <= 0 {
		return 0, 0, errors.New("invalid audio sample rate")
	}
	if ch <= 0 {
		ch = 2
	}
	return sr, ch, nil
}

func extractVideoFrames(path, outDir, ffmpegPath string) error {
	cmd := exec.Command(
		ffmpegPath,
		"-v", "error",
		"-i", path,
		"-vsync", "0",
		filepath.Join(outDir, "frame_%06d.png"),
	)
	if err := cmd.Run(); err != nil {
		return fmt.Errorf("ffmpeg failed: %w", err)
	}
	return nil
}

func extractAudioPCM(path, ffmpegPath string, sampleRate, channels int) ([]byte, error) {
	if channels < 1 {
		channels = 2
	}
	cmd := exec.Command(
		ffmpegPath,
		"-v", "error",
		"-i", path,
		"-vn",
		"-acodec", "pcm_s16le",
		"-ar", strconv.Itoa(sampleRate),
		"-ac", strconv.Itoa(channels),
		"-f", "s16le",
		"-",
	)
	var out bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		errMsg := strings.TrimSpace(stderr.String())
		if errMsg == "" {
			errMsg = err.Error()
		}
		return nil, fmt.Errorf("ffmpeg failed: %s", errMsg)
	}
	return out.Bytes(), nil
}

func decodeImageWithFFmpeg(path, ffmpegPath string) (image.Image, error) {
	cmd := exec.Command(
		ffmpegPath,
		"-v", "error",
		"-i", path,
		"-vframes", "1",
		"-f", "image2pipe",
		"-vcodec", "png",
		"-",
	)
	var out bytes.Buffer
	var stderr bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		errMsg := strings.TrimSpace(stderr.String())
		if errMsg == "" {
			errMsg = err.Error()
		}
		return nil, fmt.Errorf("ffmpeg failed: %s", errMsg)
	}
	img, _, err := image.Decode(bytes.NewReader(out.Bytes()))
	if err != nil {
		return nil, err
	}
	return img, nil
}

func decodeImageFile(path, ffmpegPath string) (image.Image, error) {
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	img, _, err := image.Decode(f)
	if err == nil {
		return img, nil
	}
	if ffmpegPath == "" {
		return nil, err
	}
	img, ffErr := decodeImageWithFFmpeg(path, ffmpegPath)
	if ffErr == nil {
		return img, nil
	}
	return nil, fmt.Errorf("image decode failed: %v; ffmpeg decode failed: %v", err, ffErr)
}

func encodeALIXFromPCM(pcm []byte, sampleRate, channels, zstdLevel, blockFrames int) ([]byte, int, error) {
	if channels <= 0 {
		return nil, 0, errors.New("invalid channels")
	}
	if sampleRate <= 0 {
		return nil, 0, errors.New("invalid sample rate")
	}
	if blockFrames <= 0 {
		blockFrames = alixBlockFrames
	}
	frameSize := 2 * channels
	if len(pcm)%frameSize != 0 {
		return nil, 0, errors.New("pcm buffer not aligned to frame size")
	}
	frames := len(pcm) / frameSize
	prev := make([]int16, channels)
	var raw bytes.Buffer
	deltas := make([]int16, 0, blockFrames*channels)
	var buf2 [2]byte
	for base := 0; base < frames; base += blockFrames {
		n := blockFrames
		if base+n > frames {
			n = frames - base
		}
		start := base * frameSize
		end := (base + n) * frameSize
		allZero := true
		for i := start; i < end; i += 2 {
			if pcm[i] != 0 || pcm[i+1] != 0 {
				allZero = false
				break
			}
		}
		if allZero {
			raw.WriteByte(alixOpSilence)
			for ch := range prev {
				prev[ch] = 0
			}
			continue
		}
		deltas = deltas[:0]
		d8OK := true
		for i := 0; i < n; i++ {
			for ch := 0; ch < channels; ch++ {
				off := (base+i)*channels + ch
				sample := int16(binary.LittleEndian.Uint16(pcm[off*2:]))
				delta := sample - prev[ch]
				prev[ch] = sample
				deltas = append(deltas, delta)
				if delta < -128 || delta > 127 {
					d8OK = false
				}
			}
		}
		if d8OK {
			raw.WriteByte(alixOpD8)
			for _, d := range deltas {
				raw.WriteByte(byte(int8(d)))
			}
		} else {
			raw.WriteByte(alixOpD16)
			for _, d := range deltas {
				binary.LittleEndian.PutUint16(buf2[:], uint16(d))
				if _, err := raw.Write(buf2[:]); err != nil {
					return nil, 0, err
				}
			}
		}
	}
	var payload bytes.Buffer
	level := clampInt(zstdLevel, 1, 22)
	enc, err := zstd.NewWriter(&payload, zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(level)))
	if err != nil {
		return nil, 0, err
	}
	if _, err := enc.Write(raw.Bytes()); err != nil {
		enc.Close()
		return nil, 0, err
	}
	if err := enc.Close(); err != nil {
		return nil, 0, err
	}
	var out bytes.Buffer
	header := []string{
		"ALIX " + alixVersion,
		"ENCODER=" + encoderVersion,
		fmt.Sprintf("SR=%d", sampleRate),
		fmt.Sprintf("CH=%d", channels),
		fmt.Sprintf("SAMPLES=%d", frames),
		"CODEC=" + alixCodec,
		fmt.Sprintf("BLOCK=%d", blockFrames),
		fmt.Sprintf("ZSTD_LEVEL=%d", level),
	}
	for _, line := range header {
		out.WriteString(line)
		out.WriteString("\n")
	}
	out.WriteString("\n")
	if _, err := out.Write(payload.Bytes()); err != nil {
		return nil, 0, err
	}
	return out.Bytes(), frames, nil
}

func encodeALIXTextFromBinary(alix []byte) []byte {
	var out bytes.Buffer
	out.WriteString("ALIX " + alixVersion + "\n")
	out.WriteString("ENCODER=" + encoderVersion + "\n")
	out.WriteString("ENCODING=BASE64\n")
	out.WriteString(fmt.Sprintf("ALIX_BYTES=%d\n", len(alix)))
	out.WriteString("\n")
	b64 := base64.StdEncoding.EncodeToString(alix)
	for len(b64) > 76 {
		out.WriteString(b64[:76])
		out.WriteString("\n")
		b64 = b64[76:]
	}
	if len(b64) > 0 {
		out.WriteString(b64)
		out.WriteString("\n")
	}
	return out.Bytes()
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

func buildEncodeSettings(
	base string,
	dither bool,
	palette int,
	blocksize int,
	blockvar float64,
	roundstep int,
	deltasnap int,
	zstdLevelFlag int,
	changed map[string]bool,
	fast bool,
) (encodeSettings, string, int) {
	if base != "lossless" && base != "unsafe" && base != "safe" {
		base = "safe"
	}
	var rs, ds, pal, blk int
	var dith bool
	blkVar := blockvar
	switch base {
	case "lossless":
		rs, ds, pal, blk, dith = 0, 0, 0, 0, false
	case "unsafe":
		rs, ds, pal, blk, dith = 3, 3, 64, 2, dither
	default:
		rs, ds, pal, blk, dith = 2, 2, 0, 0, false
		base = "safe"
	}
	custom := false
	if changed["roundstep"] {
		rs = roundstep
		custom = true
	}
	if changed["deltasnap"] {
		ds = deltasnap
		custom = true
	}
	if changed["palette"] && palette > 0 {
		pal = clampInt(palette, 1, 256)
		custom = true
	}
	if changed["blocksize"] && blocksize > 0 {
		blk = blocksize
		custom = true
	}
	if changed["blockvar"] {
		blkVar = blockvar
		custom = true
	}
	if changed["dither"] {
		dith = dither
		custom = true
	}
	zstdLevel := clampInt(zstdLevelFlag, 1, 22)
	if fast && zstdLevel > 5 {
		zstdLevel = 5
	}
	st := encodeSettings{
		mode:                 base,
		useGlobalStream:      true,
		enableTokenRLE:       true,
		enableSequenceRLE:    !fast,
		enableBackground:     true,
		backgroundMinShare:   0.20,
		chromaMode:           "444",
		roundStep:            rs,
		deltaSnapThreshold:   ds,
		paletteSize:          pal,
		paletteDither:        dith,
		blockSize:            blk,
		blockVarThreshold:    blkVar,
		sequenceRLEMaxSeqLen: 64,
		zstdLevel:            zstdLevel,
	}
	presetStr := base
	if custom {
		presetStr = fmt.Sprintf("custom (base=%s)", base)
	}
	return st, presetStr, zstdLevel
}

type jobKind int

const (
	jobUnknown jobKind = iota
	jobImageEncode
	jobImageDecode
	jobVideoEncode
	jobVideoDecode
	jobAudioEncode
	jobAudioConvert
	jobModelEncode
	jobModelDecode
)

var (
	flagGroupGeneral = []string{"help", "version", "binary", "fast", "zstd-level"}
	flagGroupImage   = []string{"preset", "dither", "palette", "blocksize", "blockvar", "roundstep", "deltasnap"}
	flagGroupVlix    = []string{"fps", "keyint", "motion", "block-size", "search", "motion-threshold", "bframes", "chroma", "codec", "dct-quality", "dct-res-quality", "no-audio", "keep-audio", "sep-audio"}
	flagGroupAlix    = []string{"audio-zstd", "audio-block", "audio-ch", "audio-rate"}
)

func classifyJob(input string, isDir bool) jobKind {
	job, _ := detectMediaJob(input, isDir)
	return job
}

func jobLabel(job jobKind) string {
	switch job {
	case jobImageEncode:
		return "image encode (clix/blix)"
	case jobImageDecode:
		return "image decode (clix/blix)"
	case jobVideoEncode:
		return "video/frames encode (vlix)"
	case jobVideoDecode:
		return "video decode (vlix)"
	case jobAudioEncode:
		return "audio encode (alix)"
	case jobAudioConvert:
		return "audio convert (alix container)"
	case jobModelEncode:
		return "model encode (elix)"
	case jobModelDecode:
		return "model decode (elix)"
	default:
		return "unknown operation"
	}
}

func flagSet(groups ...[]string) map[string]bool {
	out := make(map[string]bool)
	for _, g := range groups {
		for _, name := range g {
			out[name] = true
		}
	}
	return out
}

func allowedFlagsFor(job jobKind) map[string]bool {
	base := []string{"help", "version"}
	commonEncode := []string{"fast", "zstd-level"}
	binary := []string{"binary"}
	switch job {
	case jobImageEncode:
		return flagSet(base, commonEncode, binary, flagGroupImage)
	case jobImageDecode:
		return flagSet(base)
	case jobVideoEncode:
		return flagSet(base, commonEncode, binary, flagGroupImage, flagGroupVlix, flagGroupAlix)
	case jobVideoDecode:
		return flagSet(base, binary)
	case jobAudioEncode:
		return flagSet(base, commonEncode, binary, flagGroupAlix)
	case jobAudioConvert:
		return flagSet(base, binary)
	case jobModelEncode:
		return flagSet(base, commonEncode)
	case jobModelDecode:
		return flagSet(base)
	default:
		return flagSet(base)
	}
}

func validateFlagUsage(job jobKind, changed map[string]bool) error {
	if len(changed) == 0 {
		return nil
	}
	allowed := allowedFlagsFor(job)
	var invalid []string
	for name := range changed {
		if !allowed[name] {
			invalid = append(invalid, "--"+name)
		}
	}
	if len(invalid) == 0 {
		return nil
	}
	sort.Strings(invalid)
	return fmt.Errorf("flags not valid for %s: %s", jobLabel(job), strings.Join(invalid, ", "))
}

func printFlagGroup(w io.Writer, title string, names []string) {
	if len(names) == 0 {
		return
	}
	fmt.Fprintf(w, "%s:\n", title)
	for _, name := range names {
		f := pflag.Lookup(name)
		if f == nil {
			continue
		}
		label := "--" + f.Name
		if f.Shorthand != "" {
			label += ", -" + f.Shorthand
		}
		if f.DefValue != "" {
			fmt.Fprintf(w, "  %-24s %s (default: %s)\n", label, f.Usage, f.DefValue)
		} else {
			fmt.Fprintf(w, "  %-24s %s\n", label, f.Usage)
		}
	}
	fmt.Fprintln(w, "")
}

func printUsage() {
	out := os.Stderr
	exe := filepath.Base(os.Args[0])
	fmt.Fprintf(out, "Usage: %s [flags] <input>\n", exe)
	fmt.Fprintln(out, "")
	fmt.Fprintln(out, "Inputs:")
	fmt.Fprintln(out, "  Images -> .clix/.blix")
	fmt.Fprintln(out, "  Video or frames dir -> .vlix")
	fmt.Fprintln(out, "  Audio -> .alix")
	fmt.Fprintln(out, "  Models (.obj) -> .elix")
	fmt.Fprintln(out, "  Decode: .clix/.blix -> .png | .vlix -> frames (+.alix) | .elix -> .obj | .alix -> .alix")
	fmt.Fprintln(out, "")
	fmt.Fprintln(out, "Flags by type:")
	printFlagGroup(out, "General", flagGroupGeneral)
	printFlagGroup(out, "Image Quality (CLIX/BLIX/VLIX)", flagGroupImage)
	printFlagGroup(out, "Video (VLIX)", flagGroupVlix)
	printFlagGroup(out, "Audio (ALIX)", flagGroupAlix)
	fmt.Fprintln(out, "Notes:")
	fmt.Fprintln(out, "  - Image quality flags apply to CLIX/BLIX encoding and VLIX frame encoding.")
	fmt.Fprintln(out, "  - Audio flags apply to ALIX encoding and VLIX audio when present.")
	fmt.Fprintln(out, "  - --chroma defaults to 420 for VLIX to reduce size with minimal impact.")
	fmt.Fprintln(out, "  - --codec=vlix2 enables the DCT-based codec (smaller, lossy).")
	fmt.Fprintln(out, "  - --dct-quality/--dct-res-quality tune VLIX2 size vs quality (1-100).")
	fmt.Fprintln(out, "  - --bframes controls VLIX2 B-frames (0=off, higher=smaller/slower).")
	fmt.Fprintln(out, "  - Use --binary=true for smallest .alix/.blix output (avoids base64).")
	fmt.Fprintln(out, "  - --fast disables motion unless --motion is explicitly set.")
	fmt.Fprintln(out, "  - --audio-zstd defaults to --zstd-level capped at 10 unless overridden.")
	fmt.Fprintln(out, "  - --audio-rate defaults to 44100 when source is higher, unless overridden.")
	fmt.Fprintln(out, "  - Set --motion-threshold=0 for lossless motion matching.")
	fmt.Fprintln(out, "  - Flags are validated against input type; incompatible flags will error.")
}

func resolveAudioZstd(base int, audioOverride int, audioOverrideSet bool, fast bool) int {
	level := base
	if level > 10 {
		level = 10
	}
	if audioOverrideSet {
		level = audioOverride
	}
	level = clampInt(level, 1, 22)
	if fast && level > 5 {
		level = 5
	}
	return level
}

func resolveAlixBlock(blockFlag int) int {
	if blockFlag > 0 {
		return blockFlag
	}
	return alixBlockFrames
}

func resolveAudioChannels(probed int, override int) int {
	if override == 1 || override == 2 {
		return override
	}
	if probed == 1 || probed == 2 {
		return probed
	}
	if probed <= 0 {
		return 2
	}
	return 2
}

func resolveAudioRate(probed int, spec string) (int, error) {
	s := strings.TrimSpace(strings.ToLower(spec))
	switch s {
	case "", "auto":
		if probed > 44100 {
			return 44100, nil
		}
		if probed > 0 {
			return probed, nil
		}
		return 44100, nil
	case "source", "src":
		if probed > 0 {
			return probed, nil
		}
		return 44100, nil
	default:
		v, err := strconv.Atoi(s)
		if err != nil || v <= 0 {
			return 0, fmt.Errorf("invalid audio rate: %q", spec)
		}
		return v, nil
	}
}

func resolveChromaMode(spec string) (string, error) {
	s := strings.TrimSpace(strings.ToLower(spec))
	switch s {
	case "", "444":
		return "444", nil
	case "422":
		return "422", nil
	case "420":
		return "420", nil
	default:
		return "", fmt.Errorf("invalid chroma mode: %q", spec)
	}
}

func resolveVlixCodec(spec string) (string, error) {
	s := strings.TrimSpace(strings.ToLower(spec))
	switch s {
	case "", "vlix1":
		return vlixCodecV1, nil
	case "vlix2":
		return vlixCodecV2, nil
	default:
		return "", fmt.Errorf("invalid codec: %q", spec)
	}
}

func main() {
	helpFlag := pflag.BoolP("help", "h", false, "Show this help and exit")
	preset := pflag.String("preset", "safe", "Compression preset base for CLIX/BLIX/VLIX: lossless | safe | unsafe")
	dither := pflag.Bool("dither", false, "Enable Floyd-Steinberg dithering in palette mode (unsafe, CLIX/BLIX/VLIX)")
	palette := pflag.Int("palette", 0, "Palette size (1-256, unsafe mode only, CLIX/BLIX/VLIX)")
	blocksize := pflag.Int("blocksize", 0, "Block smoothing size (e.g., 2 or 4, unsafe mode only, CLIX/BLIX/VLIX)")
	blockvar := pflag.Float64("blockvar", 12.0, "Variance threshold for block smoothing (unsafe, CLIX/BLIX/VLIX)")
	roundstep := pflag.Int("roundstep", -1, "Channel rounding step (0=off, CLIX/BLIX/VLIX)")
	deltasnap := pflag.Int("deltasnap", -1, "Delta snap threshold (0=off, CLIX/BLIX/VLIX)")
	zstdLevelFlag := pflag.Int("zstd-level", 22, "Zstd compression level for CLIX/BLIX/VLIX/ELIX (1-22)")
	fastFlag := pflag.Bool("fast", false, "Faster encode (lower zstd and simpler RLE)")
	versionFlag := pflag.Bool("version", false, "Print version and exit")
	binaryStr := pflag.String("binary", "false", "Write binary output where supported (e.g., .blix/.alix). Accepts: true|false")
	fpsFlag := pflag.Float64("fps", 30, "Frames per second for Vlix encoding")
	keyintFlag := pflag.Int("keyint", 30, "Keyframe interval for Vlix encoding (frames)")
	motionFlag := pflag.Bool("motion", true, "Enable motion search for Vlix (slower, can reduce size)")
	blockSizeFlag := pflag.Int("block-size", vlxDefaultBlockDim, "Motion block size in pixels for Vlix")
	searchFlag := pflag.Int("search", vlxDefaultSearchRadius, "Motion search radius in pixels for Vlix")
	motionThreshFlag := pflag.Int("motion-threshold", vlxDefaultMotionThreshold, "Motion match threshold for Vlix (0=lossless, higher=more compression)")
	bframesFlag := pflag.Int("bframes", vlxDefaultBFrames, "Number of B-frames between references for VLIX2 (0=off)")
	chromaFlag := pflag.String("chroma", "420", "Chroma subsampling for Vlix: 444|422|420")
	codecFlag := pflag.String("codec", "vlix1", "VLIX codec: vlix1 (default) | vlix2 (DCT-based, smaller, lossy)")
	dctQualityFlag := pflag.Int("dct-quality", 75, "DCT quality for VLIX2 keyframes (1-100, higher=better)")
	dctResQualityFlag := pflag.Int("dct-res-quality", 70, "DCT quality for VLIX2 residuals (1-100, higher=better)")
	noAudioFlag := pflag.Bool("no-audio", false, "Disable audio extraction for video input")
	keepAudioFlag := pflag.BoolP("keep-audio", "k", false, "Keep a .alix file alongside the .vlix output")
	separateAudioFlag := pflag.Bool("sep-audio", false, "Write audio to .alix and keep .vlix video-only")
	audioZstdFlag := pflag.Int("audio-zstd", 0, "Zstd level for ALIX audio (1-22, 0=use --zstd-level capped at 10)")
	audioBlockFlag := pflag.Int("audio-block", 0, "ALIX block size in frames (0=default 1024)")
	audioChFlag := pflag.Int("audio-ch", 0, "Audio channels for ALIX encoding (0=source, 1=mono, 2=stereo)")
	audioRateFlag := pflag.String("audio-rate", "auto", "Audio sample rate: auto|source|<Hz> (auto downsamples >44100)")
	pflag.Usage = printUsage
	pflag.Parse()
	if *helpFlag {
		pflag.Usage()
		return
	}
	if *versionFlag {
		if len(os.Args) == 2 {
			fmt.Printf("Clix Encoder | Version %s\n", encoderVersion)
			fmt.Printf("Clix | Version %s\n", clixVersion)
			fmt.Printf("Blix | Version %s\n", blixVersion)
			fmt.Printf("Vlix | Version %s\n", vlixVersion)
			fmt.Printf("Alix | Version %s\n", alixVersion)
			fmt.Printf("Elix | Version %s\n", elixVersion)
			return
		}
		fmt.Fprintln(os.Stderr, "Error: --version cannot be combined with other arguments.")
		os.Exit(2)
	}
	if pflag.NArg() < 1 {
		pflag.Usage()
		os.Exit(2)
	}
	input := pflag.Arg(0)
	changedFlags := map[string]bool{}
	pflag.Visit(func(f *pflag.Flag) {
		changedFlags[f.Name] = true
	})
	changed := map[string]bool{
		"roundstep": changedFlags["roundstep"],
		"deltasnap": changedFlags["deltasnap"],
		"palette":   changedFlags["palette"],
		"blocksize": changedFlags["blocksize"],
		"blockvar":  changedFlags["blockvar"],
		"dither":    changedFlags["dither"],
		"fps":       changedFlags["fps"],
		"keyint":    changedFlags["keyint"],
	}
	info, statErr := os.Stat(input)
	isDir := statErr == nil && info.IsDir()
	job := classifyJob(input, isDir)
	if err := validateFlagUsage(job, changedFlags); err != nil {
		fmt.Fprintln(os.Stderr, "[-] Flag error:", err)
		pflag.Usage()
		os.Exit(2)
	}
	if changedFlags["audio-zstd"] && *audioZstdFlag != 0 && (*audioZstdFlag < 1 || *audioZstdFlag > 22) {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --audio-zstd: must be 0 or between 1 and 22")
		os.Exit(2)
	}
	if changedFlags["audio-block"] && *audioBlockFlag <= 0 {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --audio-block: must be > 0")
		os.Exit(2)
	}
	if changedFlags["audio-ch"] && *audioChFlag != 0 && *audioChFlag != 1 && *audioChFlag != 2 {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --audio-ch: must be 0, 1, or 2")
		os.Exit(2)
	}
	if changedFlags["block-size"] && *blockSizeFlag <= 0 {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --block-size: must be > 0")
		os.Exit(2)
	}
	if changedFlags["search"] && *searchFlag < 0 {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --search: must be >= 0")
		os.Exit(2)
	}
	if changedFlags["motion-threshold"] && *motionThreshFlag < 0 {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --motion-threshold: must be >= 0")
		os.Exit(2)
	}
	if changedFlags["bframes"] && *bframesFlag < 0 {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --bframes: must be >= 0")
		os.Exit(2)
	}
	if changedFlags["dct-quality"] && (*dctQualityFlag < 1 || *dctQualityFlag > 100) {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --dct-quality: must be between 1 and 100")
		os.Exit(2)
	}
	if changedFlags["dct-res-quality"] && (*dctResQualityFlag < 1 || *dctResQualityFlag > 100) {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --dct-res-quality: must be between 1 and 100")
		os.Exit(2)
	}
	bin, err := parseBoolLoose(*binaryStr)
	if err != nil {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --binary:", err)
		os.Exit(2)
	}
	motionEnabled := *motionFlag
	if *fastFlag && !changedFlags["motion"] {
		motionEnabled = false
	}
	blockDim := *blockSizeFlag
	if blockDim <= 0 {
		blockDim = vlxDefaultBlockDim
	}
	searchRadius := *searchFlag
	if searchRadius < 0 {
		searchRadius = 0
	}
	motionThreshold := *motionThreshFlag
	if motionThreshold < 0 {
		motionThreshold = 0
	}
	bframes := *bframesFlag
	if bframes < 0 {
		bframes = 0
	}
	chromaMode := "444"
	if job == jobVideoEncode {
		if v, err := resolveChromaMode(*chromaFlag); err == nil {
			chromaMode = v
		} else {
			fmt.Fprintln(os.Stderr, "[-] Flag error for --chroma:", err)
			os.Exit(2)
		}
	}
	codec := vlixCodecV1
	if job == jobVideoEncode {
		if v, err := resolveVlixCodec(*codecFlag); err == nil {
			codec = v
		} else {
			fmt.Fprintln(os.Stderr, "[-] Flag error for --codec:", err)
			os.Exit(2)
		}
		if codec == vlixCodecV1 && (changedFlags["dct-quality"] || changedFlags["dct-res-quality"]) {
			fmt.Fprintln(os.Stderr, "[-] DCT quality flags require --codec=vlix2")
			os.Exit(2)
		}
		if codec == vlixCodecV1 && changedFlags["bframes"] {
			fmt.Fprintln(os.Stderr, "[-] --bframes requires --codec=vlix2")
			os.Exit(2)
		}
	}
	logStep := func(format string, args ...interface{}) {
		fmt.Printf("[*] "+format+"\n", args...)
	}
	ffmpegPath := ""
	if job == jobVideoEncode || job == jobAudioEncode || job == jobImageEncode {
		if p, err := findTool("ffmpeg"); err == nil {
			ffmpegPath = p
		} else if job == jobVideoEncode || job == jobAudioEncode {
			if !isDir {
				fmt.Fprintln(os.Stderr, "[-]", err)
				os.Exit(1)
			}
		}
	}
	if isDir {
		out := filepath.Clean(input) + ".vlix"
		logStep("Encoding frames from %s", input)
		st, presetStr, zstdLevel := buildEncodeSettings(
			strings.ToLower(*preset),
			*dither,
			*palette,
			*blocksize,
			*blockvar,
			*roundstep,
			*deltasnap,
			*zstdLevelFlag,
			changed,
			*fastFlag,
		)
		if codec == vlixCodecV2 {
			st.chromaMode = "444"
			if err := encodeVLIX2(input, out, st, *fpsFlag, *keyintFlag, nil, ffmpegPath, chromaMode, *dctQualityFlag, *dctResQualityFlag, motionEnabled, blockDim, searchRadius, motionThreshold, bframes); err != nil {
				fmt.Fprintln(os.Stderr, "[-] Vlix2 encode error:", err)
				os.Exit(1)
			}
		} else {
			st.chromaMode = chromaMode
			if err := encodeVLIX(input, out, st, *fpsFlag, *keyintFlag, nil, ffmpegPath, motionEnabled, blockDim, searchRadius, motionThreshold, codec); err != nil {
				fmt.Fprintln(os.Stderr, "[-] Vlix encode error:", err)
				os.Exit(1)
			}
		}
		fmt.Printf("[+] Encoded %s -> %s (preset=%s, fps=%.3g, keyint=%d, zstd=%d)\n", input, out, presetStr, *fpsFlag, *keyintFlag, zstdLevel)
		return
	}
	name := strings.TrimSuffix(input, filepath.Ext(input))
	ext := strings.ToLower(filepath.Ext(input))
	if job == jobVideoEncode {
		ffprobePath, _ := findTool("ffprobe")
		fps := *fpsFlag
		if !changed["fps"] {
			if ffprobePath == "" {
				fmt.Fprintln(os.Stderr, "[!] ffprobe not found; using default fps", fps)
			} else if v, err := probeVideoFPS(input, ffprobePath); err == nil && v > 0 {
				fps = v
			} else {
				fmt.Fprintln(os.Stderr, "[!] Could not detect fps; using default", fps)
			}
		}
		keyint := *keyintFlag
		if !changed["keyint"] {
			keyint = int(math.Round(fps))
			if keyint < 1 {
				keyint = 1
			}
		}
		logStep("Decoding video: %s", input)
		tmpDir, err := os.MkdirTemp("", "vlix_frames_*")
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] Temp dir error:", err)
			os.Exit(1)
		}
		defer os.RemoveAll(tmpDir)
		logStep("Extracting frames")
		if err := extractVideoFrames(input, tmpDir, ffmpegPath); err != nil {
			fmt.Fprintln(os.Stderr, "[-] Frame extraction error:", err)
			os.Exit(1)
		}
		var audioBlob []byte
		wroteAudio := false
		audioSidecarPath := ""
		if !*noAudioFlag {
			logStep("Extracting audio")
			sr := 48000
			ch := 2
			if ffprobePath != "" {
				if v, c, err := probeAudioInfo(input, ffprobePath); err == nil {
					sr = v
					ch = c
				} else {
					fmt.Fprintln(os.Stderr, "[!] Could not probe audio; using defaults", sr, "Hz,", ch, "ch")
				}
			}
			ch = resolveAudioChannels(ch, *audioChFlag)
			if v, err := resolveAudioRate(sr, *audioRateFlag); err == nil {
				sr = v
			} else {
				fmt.Fprintln(os.Stderr, "[-] Flag error for --audio-rate:", err)
				os.Exit(2)
			}
			if pcm, err := extractAudioPCM(input, ffmpegPath, sr, ch); err == nil && len(pcm) > 0 {
				logStep("Encoding ALIX audio")
				audioOverrideSet := changedFlags["audio-zstd"] && *audioZstdFlag != 0
				audioZstd := resolveAudioZstd(*zstdLevelFlag, *audioZstdFlag, audioOverrideSet, *fastFlag)
				alixBlock := resolveAlixBlock(*audioBlockFlag)
				if blob, _, err := encodeALIXFromPCM(pcm, sr, ch, audioZstd, alixBlock); err == nil {
					audioBlob = blob
					if *keepAudioFlag || *separateAudioFlag {
						audioExt := ".alix"
						audioOut := audioBlob
						if !bin {
							audioOut = encodeALIXTextFromBinary(audioBlob)
						}
						outPath := name + audioExt
						if err := os.WriteFile(outPath, audioOut, 0o644); err == nil {
							logStep("Wrote %s", outPath)
							wroteAudio = true
							audioSidecarPath = outPath
						}
					}
					if *separateAudioFlag {
						audioBlob = nil
					}
				} else {
					fmt.Fprintln(os.Stderr, "[!] Audio encode failed:", err)
				}
			} else if err != nil {
				fmt.Fprintln(os.Stderr, "[!] Audio extraction failed:", err)
			}
		}
		out := name + ".vlix"
		st, presetStr, zstdLevel := buildEncodeSettings(
			strings.ToLower(*preset),
			*dither,
			*palette,
			*blocksize,
			*blockvar,
			*roundstep,
			*deltasnap,
			*zstdLevelFlag,
			changed,
			*fastFlag,
		)
		logStep("Encoding VLIX")
		if codec == vlixCodecV2 {
			st.chromaMode = "444"
			if err := encodeVLIX2(tmpDir, out, st, fps, keyint, audioBlob, ffmpegPath, chromaMode, *dctQualityFlag, *dctResQualityFlag, motionEnabled, blockDim, searchRadius, motionThreshold, bframes); err != nil {
				fmt.Fprintln(os.Stderr, "[-] Vlix2 encode error:", err)
				os.Exit(1)
			}
		} else {
			st.chromaMode = chromaMode
			if err := encodeVLIX(tmpDir, out, st, fps, keyint, audioBlob, ffmpegPath, motionEnabled, blockDim, searchRadius, motionThreshold, codec); err != nil {
				fmt.Fprintln(os.Stderr, "[-] Vlix encode error:", err)
				os.Exit(1)
			}
		}
		if wroteAudio && *separateAudioFlag && audioSidecarPath != "" {
			logStep("Wrote %s (audio only, vlix video-only)", audioSidecarPath)
		}
		fmt.Printf("[+] Encoded %s -> %s (preset=%s, fps=%.3g, keyint=%d, zstd=%d)\n", input, out, presetStr, fps, keyint, zstdLevel)
		return
	}
	if job == jobAudioEncode {
		ffprobePath, _ := findTool("ffprobe")
		logStep("Decoding audio: %s", input)
		sr := 48000
		ch := 2
		if ffprobePath != "" {
			if v, c, err := probeAudioInfo(input, ffprobePath); err == nil {
				sr = v
				ch = c
			} else {
				fmt.Fprintln(os.Stderr, "[!] Could not probe audio; using defaults", sr, "Hz,", ch, "ch")
			}
		}
		ch = resolveAudioChannels(ch, *audioChFlag)
		if v, err := resolveAudioRate(sr, *audioRateFlag); err == nil {
			sr = v
		} else {
			fmt.Fprintln(os.Stderr, "[-] Flag error for --audio-rate:", err)
			os.Exit(2)
		}
		pcm, err := extractAudioPCM(input, ffmpegPath, sr, ch)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] Audio extraction error:", err)
			os.Exit(1)
		}
		logStep("Encoding ALIX")
		audioOverrideSet := changedFlags["audio-zstd"] && *audioZstdFlag != 0
		audioZstd := resolveAudioZstd(*zstdLevelFlag, *audioZstdFlag, audioOverrideSet, *fastFlag)
		alixBlock := resolveAlixBlock(*audioBlockFlag)
		blob, _, err := encodeALIXFromPCM(pcm, sr, ch, audioZstd, alixBlock)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] ALIX encode error:", err)
			os.Exit(1)
		}
		outExt := ".alix"
		outData := blob
		if !bin {
			outData = encodeALIXTextFromBinary(blob)
		}
		out := name + outExt
		if err := os.WriteFile(out, outData, 0o644); err != nil {
			fmt.Fprintln(os.Stderr, "[-] ALIX write error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Encoded %s -> %s\n", input, out)
		return
	}
	if ext == ".alix" || ext == ".clxa" || ext == ".vla" {
		raw, err := os.ReadFile(input)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] ALIX read error:", err)
			os.Exit(1)
		}
		alix, err := decodeALIXContainer(raw)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] ALIX decode error:", err)
			os.Exit(1)
		}
		outData := alix
		if !bin {
			outData = encodeALIXTextFromBinary(alix)
		}
		out := name + ".alix"
		if err := os.WriteFile(out, outData, 0o644); err != nil {
			fmt.Fprintln(os.Stderr, "[-] ALIX write error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Converted %s -> %s\n", input, out)
		return
	}
	if ext == ".elix" {
		out := name + ".obj"
		if err := decodeELIX(input, out); err != nil {
			fmt.Fprintln(os.Stderr, "[-] ELIX decode error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Decoded %s -> %s\n", input, out)
		return
	}
	if ext == ".obj" {
		elixZstd := clampInt(*zstdLevelFlag, 1, 22)
		if *fastFlag && elixZstd > 5 {
			elixZstd = 5
		}
		out := name + ".elix"
		if err := encodeELIX(input, out, elixZstd); err != nil {
			fmt.Fprintln(os.Stderr, "[-] ELIX encode error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Encoded %s -> %s (zstd=%d)\n", input, out, elixZstd)
		return
	}
	if ext == ".clix" {
		if err := decodeCLIX(input, name+".png"); err != nil {
			fmt.Fprintln(os.Stderr, "[-] Decode error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Decoded %s -> %s.png\n", input, name)
		return
	}
	if ext == ".blix" {
		if err := decodeBLIX(input, name+".png"); err != nil {
			fmt.Fprintln(os.Stderr, "[-] Decode error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Decoded %s -> %s.png\n", input, name)
		return
	}
	if ext == ".vlix" {
		outDir := name + "_frames"
		audioBlob, err := decodeVLIX(input, outDir)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] Vlix decode error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Decoded %s -> %s/\n", input, outDir)
		if len(audioBlob) > 0 {
			audioExt := ".alix"
			audioOut := audioBlob
			if !bin {
				audioOut = encodeALIXTextFromBinary(audioBlob)
			}
			audioPath := name + audioExt
			if err := os.WriteFile(audioPath, audioOut, 0o644); err != nil {
				fmt.Fprintln(os.Stderr, "[!] Audio write error:", err)
			} else {
				fmt.Printf("[+] Extracted audio -> %s\n", audioPath)
			}
		}
		return
	}
	st, presetStr, zstdLevel := buildEncodeSettings(
		strings.ToLower(*preset),
		*dither,
		*palette,
		*blocksize,
		*blockvar,
		*roundstep,
		*deltasnap,
		*zstdLevelFlag,
		changed,
		*fastFlag,
	)
	var out string
	if bin {
		out = name + ".blix"
		if err := encodeBLIX(input, out, st, ffmpegPath); err != nil {
			fmt.Fprintln(os.Stderr, "[-] Encode error:", err)
			os.Exit(1)
		}
	} else {
		out = name + ".clix"
		if err := encodeCLIX(input, out, st, ffmpegPath); err != nil {
			fmt.Fprintln(os.Stderr, "[-] Encode error:", err)
			os.Exit(1)
		}
	}
	fmt.Printf("[+] Encoded %s -> %s (preset=%s, zstd=%d)\n", input, out, presetStr, zstdLevel)
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

func boolToInt(v bool) int {
	if v {
		return 1
	}
	return 0
}

func absInt(v int) int {
	if v < 0 {
		return -v
	}
	return v
}
func min(a, b int) int {
	if a < b {
		return a
	}
	return b
}
