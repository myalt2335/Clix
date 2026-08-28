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
	"runtime"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	_ "image/gif"
	_ "image/jpeg"

	"github.com/klauspost/compress/zstd"
	"github.com/soniakeys/quant/median"
	"github.com/spf13/pflag"
)

type RGBA struct{ R, G, B, A uint8 }

func (p RGBA) toColor() color.NRGBA { return color.NRGBA{R: p.R, G: p.G, B: p.B, A: p.A} }
func fromColor(c color.Color) RGBA {
	if nc, ok := c.(color.NRGBA); ok {
		return RGBA{nc.R, nc.G, nc.B, nc.A}
	}
	nc := color.NRGBAModel.Convert(c).(color.NRGBA)
	return RGBA{nc.R, nc.G, nc.B, nc.A}
}

const (
	encoderVersion          = "2.15"
	encoderAuxiliaryVersion = "2.A025.01.260612.K9ENUS@c1x14"
	clixVersion             = "2.12"
	blixVersion             = "2.1"
	trixVersion             = "0.2"
	vlixVersion             = "2.5"
	vlixCodecV1             = "VLIX1"
	vlixCodecV2             = "VLIX2"
	alixVersion             = "1.3"
	alixCodec               = "ALIX"
	alix2Codec              = "ALIX2"
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
func rgbaToCompactHex(px RGBA) string {
	return fmt.Sprintf("%02X%02X%02X%02X", px.R, px.G, px.B, px.A)
}

func rgbaToCompactRefToken(px RGBA) string {
	vals := [4]uint8{px.R, px.G, px.B, px.A}
	refs := [4]byte{'R', 'G', 'Z', 0}
	var b strings.Builder
	b.Grow(8)
	b.WriteString(fmt.Sprintf("%02X", vals[0]))
	for i := 1; i < 4; i++ {
		ref := byte(0)
		for j := 0; j < i; j++ {
			if vals[i] == vals[j] {
				ref = refs[j]
				break
			}
		}
		if ref != 0 {
			b.WriteByte(ref)
		} else {
			b.WriteString(fmt.Sprintf("%02X", vals[i]))
		}
	}
	tok := b.String()
	if len(tok) < 8 {
		return tok
	}
	return rgbaToCompactHex(px)
}

func rgbaToToken(px RGBA) string {
	if tok, ok := PURE_COLOR_TOKENS[px]; ok {
		return tok
	}
	return rgbaToCompactRefToken(px)
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
			return nil, fmt.Errorf("bad compact RGBA token at: %q", s[start:j])
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
	prevEmit := tokens[0]
	count := 1
	for _, t := range tokens[1:] {
		canon := t
		if t == "S" {
			canon = prev
		}
		if canon == prev {
			count++
		} else {
			if count > 1 {
				out = append(out, fmt.Sprintf("%s*%d", prevEmit, count))
			} else {
				out = append(out, prevEmit)
			}
			prev = canon
			prevEmit = t
			count = 1
		}
	}
	if count > 1 {
		out = append(out, fmt.Sprintf("%s*%d", prevEmit, count))
	} else {
		out = append(out, prevEmit)
	}
	return out
}

func sequenceRLE(tokens []string, maxSeqLen int) []string {
	if maxSeqLen <= 0 {
		maxSeqLen = 64
	}
	n := len(tokens)
	if n == 0 {
		return []string{}
	}
	// for every stride at every position. The chosen runs are identical to the
	ids := make([]int32, n)
	idOf := make(map[string]int32, n)
	for i, t := range tokens {
		id, ok := idOf[t]
		if !ok {
			id = int32(len(idOf))
			idOf[t] = id
		}
		ids[i] = id
	}
	equalRun := func(a, b, L int) bool {
		for k := 0; k < L; k++ {
			if ids[a+k] != ids[b+k] {
				return false
			}
		}
		return true
	}
	out := make([]string, 0, n)
	i := 0
	for i < n {
		bestLen, bestCount := 1, 1
		limit := maxSeqLen
		if rem := n - i; rem < limit {
			limit = rem
		}
		for L := 1; L <= limit; L++ {
			count := 1
			j := i + L
			for j+L <= n && equalRun(i, j, L) {
				count++
				j += L
			}
			if count > 1 && L*count > bestLen*bestCount {
				bestLen, bestCount = L, count
			}
		}
		if bestCount > 1 {
			out = append(out, fmt.Sprintf("(%s)*%d", strings.Join(tokens[i:i+bestLen], " "), bestCount))
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
			return nil, fmt.Errorf("bad compact RGBA token at: %q", s[start:j])
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

func packRGBA(p RGBA) uint32 { return uint32(p.R)<<24 | uint32(p.G)<<16 | uint32(p.B)<<8 | uint32(p.A) }
func unpackRGBA(u uint32) RGBA {
	return RGBA{uint8(u >> 24), uint8(u >> 16), uint8(u >> 8), uint8(u)}
}

func detectBackground(pixels []RGBA) (RGBA, float64) {
	counts := make(map[uint32]int)
	for _, px := range pixels {
		counts[packRGBA(px)]++
	}
	var maxKey uint32
	maxCnt := -1
	for k, c := range counts {
		if c > maxCnt {
			maxCnt = c
			maxKey = k
		}
	}
	bg := unpackRGBA(maxKey)
	share := float64(maxCnt) / float64(len(pixels))
	return bg, share
}

type clixRectRunKey struct {
	color uint32
	x0    int
	x1    int
}

type clixRect struct {
	x     int
	y     int
	w     int
	h     int
	color RGBA
}

type clixComponent struct {
	x0    int
	y0    int
	w     int
	h     int
	color RGBA
	mask  []bool
}

func clixEllipseContains(localX, localY, w, h int) bool {
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

func clixTriangleContains(localX, localY, w, h, orient int) bool {
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

func clixMatchEllipseMask(mask []bool, w, h int) bool {
	if w <= 0 || h <= 0 || len(mask) != w*h {
		return false
	}
	for y := 0; y < h; y++ {
		rowOff := y * w
		for x := 0; x < w; x++ {
			if mask[rowOff+x] != clixEllipseContains(x, y, w, h) {
				return false
			}
		}
	}
	return true
}

func clixMatchTriangleMask(mask []bool, w, h int) (int, bool) {
	if w <= 0 || h <= 0 || len(mask) != w*h {
		return 0, false
	}
	for orient := 0; orient < 8; orient++ {
		ok := true
		for y := 0; y < h && ok; y++ {
			rowOff := y * w
			for x := 0; x < w; x++ {
				if mask[rowOff+x] != clixTriangleContains(x, y, w, h, orient) {
					ok = false
					break
				}
			}
		}
		if ok {
			return orient, true
		}
	}
	return 0, false
}

func buildCLIXComponentsForBase(pixels []RGBA, width, height int, base RGBA) []clixComponent {
	total := width * height
	if width <= 0 || height <= 0 || len(pixels) != total {
		return nil
	}
	visited := make([]bool, total)
	comps := make([]clixComponent, 0)
	for idx := 0; idx < total; idx++ {
		if visited[idx] || pixels[idx] == base {
			continue
		}
		color := pixels[idx]
		queue := []int{idx}
		visited[idx] = true
		cells := make([]int, 0, 64)
		x0, y0 := idx%width, idx/width
		x1, y1 := x0, y0
		for q := 0; q < len(queue); q++ {
			cur := queue[q]
			cells = append(cells, cur)
			x := cur % width
			y := cur / width
			if x < x0 {
				x0 = x
			}
			if x > x1 {
				x1 = x
			}
			if y < y0 {
				y0 = y
			}
			if y > y1 {
				y1 = y
			}
			if x > 0 {
				n := cur - 1
				if !visited[n] && pixels[n] == color {
					visited[n] = true
					queue = append(queue, n)
				}
			}
			if x+1 < width {
				n := cur + 1
				if !visited[n] && pixels[n] == color {
					visited[n] = true
					queue = append(queue, n)
				}
			}
			if y > 0 {
				n := cur - width
				if !visited[n] && pixels[n] == color {
					visited[n] = true
					queue = append(queue, n)
				}
			}
			if y+1 < height {
				n := cur + width
				if !visited[n] && pixels[n] == color {
					visited[n] = true
					queue = append(queue, n)
				}
			}
		}
		w := x1 - x0 + 1
		h := y1 - y0 + 1
		mask := make([]bool, w*h)
		for _, c := range cells {
			x := c%width - x0
			y := c/width - y0
			mask[y*w+x] = true
		}
		comps = append(comps, clixComponent{
			x0:    x0,
			y0:    y0,
			w:     w,
			h:     h,
			color: color,
			mask:  mask,
		})
	}
	return comps
}

func buildCLIXRectanglesForMask(mask []bool, bx, by, bw, bh int, color RGBA) []clixRect {
	if bw <= 0 || bh <= 0 || len(mask) != bw*bh {
		return nil
	}
	rects := make([]clixRect, 0, bh)
	active := make(map[[2]int]int)
	for y := 0; y < bh; y++ {
		next := make(map[[2]int]int)
		rowOff := y * bw
		for x := 0; x < bw; {
			if !mask[rowOff+x] {
				x++
				continue
			}
			x0 := x
			x++
			for x < bw && mask[rowOff+x] {
				x++
			}
			x1 := x - 1
			key := [2]int{x0, x1}
			if idx, ok := active[key]; ok {
				rects[idx].h++
				next[key] = idx
				continue
			}
			rects = append(rects, clixRect{
				x:     bx + x0,
				y:     by + y,
				w:     x1 - x0 + 1,
				h:     1,
				color: color,
			})
			next[key] = len(rects) - 1
		}
		active = next
	}
	return rects
}

func buildCLIXApproxEllipsePatchTokens(c clixComponent, fillToken, baseToken string, allowLossySnap bool) ([]string, int, bool) {
	area := c.w * c.h
	if area <= 0 || len(c.mask) != area {
		return nil, 0, false
	}
	extra := make([]bool, area)
	miss := make([]bool, area)
	xor := 0
	for y := 0; y < c.h; y++ {
		rowOff := y * c.w
		for x := 0; x < c.w; x++ {
			i := rowOff + x
			inE := clixEllipseContains(x, y, c.w, c.h)
			inM := c.mask[i]
			if inE != inM {
				xor++
				if inE {
					extra[i] = true
				} else {
					miss[i] = true
				}
			}
		}
	}
	if xor == 0 {
		return nil, 0, false
	}
	if allowLossySnap && xor <= 256 && xor*500 <= area {
		return []string{fmt.Sprintf("@C,%d,%d,%d,%d=%s", c.x0, c.y0, c.w, c.h, fillToken)}, 1, true
	}
	if xor > 4096 || xor*20 > area {
		return nil, 0, false
	}
	extraRects := buildCLIXRectanglesForMask(extra, c.x0, c.y0, c.w, c.h, c.color)
	missRects := buildCLIXRectanglesForMask(miss, c.x0, c.y0, c.w, c.h, c.color)
	tokens := make([]string, 0, 1+len(extraRects)+len(missRects))
	tokens = append(tokens, fmt.Sprintf("@C,%d,%d,%d,%d=%s", c.x0, c.y0, c.w, c.h, fillToken))
	for _, r := range extraRects {
		tokens = append(tokens, fmt.Sprintf("@%d,%d,%d,%d=%s", r.x, r.y, r.w, r.h, baseToken))
	}
	for _, r := range missRects {
		tokens = append(tokens, fmt.Sprintf("@%d,%d,%d,%d=%s", r.x, r.y, r.w, r.h, fillToken))
	}
	return tokens, len(tokens), true
}

func buildCLIXApproxTrianglePatchTokens(c clixComponent, fillToken, baseToken string, allowLossySnap bool) ([]string, int, bool) {
	area := c.w * c.h
	if area <= 0 || len(c.mask) != area {
		return nil, 0, false
	}
	bestOrient := -1
	bestXor := area + 1
	var bestExtra, bestMiss []bool
	for orient := 0; orient < 8; orient++ {
		extra := make([]bool, area)
		miss := make([]bool, area)
		xor := 0
		for y := 0; y < c.h; y++ {
			rowOff := y * c.w
			for x := 0; x < c.w; x++ {
				i := rowOff + x
				inT := clixTriangleContains(x, y, c.w, c.h, orient)
				inM := c.mask[i]
				if inT != inM {
					xor++
					if inT {
						extra[i] = true
					} else {
						miss[i] = true
					}
				}
			}
		}
		if xor < bestXor {
			bestXor = xor
			bestOrient = orient
			bestExtra = extra
			bestMiss = miss
		}
	}
	if bestOrient < 0 || bestXor == 0 {
		return nil, 0, false
	}
	if allowLossySnap && bestXor <= 8192 && bestXor*20 <= area {
		return []string{fmt.Sprintf("@T,%d,%d,%d,%d,%d=%s", c.x0, c.y0, c.w, c.h, bestOrient, fillToken)}, 1, true
	}
	if bestXor > 16384 || bestXor*4 > area {
		return nil, 0, false
	}
	extraRects := buildCLIXRectanglesForMask(bestExtra, c.x0, c.y0, c.w, c.h, c.color)
	missRects := buildCLIXRectanglesForMask(bestMiss, c.x0, c.y0, c.w, c.h, c.color)
	tokens := make([]string, 0, 1+len(extraRects)+len(missRects))
	tokens = append(tokens, fmt.Sprintf("@T,%d,%d,%d,%d,%d=%s", c.x0, c.y0, c.w, c.h, bestOrient, fillToken))
	for _, r := range extraRects {
		tokens = append(tokens, fmt.Sprintf("@%d,%d,%d,%d=%s", r.x, r.y, r.w, r.h, baseToken))
	}
	for _, r := range missRects {
		tokens = append(tokens, fmt.Sprintf("@%d,%d,%d,%d=%s", r.x, r.y, r.w, r.h, fillToken))
	}
	return tokens, len(tokens), true
}

func buildCLIXShapeTokensForBase(pixels []RGBA, width, height int, base RGBA, baseToken string, allowLossySnap bool) ([]string, int) {
	total := width * height
	if total <= 0 {
		return nil, 0
	}
	tokens := []string{fmt.Sprintf("%s*%d", baseToken, total)}
	cmdCount := 0
	comps := buildCLIXComponentsForBase(pixels, width, height, base)
	for _, c := range comps {
		fill := rgbaToToken(c.color)
		if clixMatchEllipseMask(c.mask, c.w, c.h) {
			tokens = append(tokens, fmt.Sprintf("@C,%d,%d,%d,%d=%s", c.x0, c.y0, c.w, c.h, fill))
			cmdCount++
			continue
		}
		if orient, ok := clixMatchTriangleMask(c.mask, c.w, c.h); ok {
			tokens = append(tokens, fmt.Sprintf("@T,%d,%d,%d,%d,%d=%s", c.x0, c.y0, c.w, c.h, orient, fill))
			cmdCount++
			continue
		}
		if approxTokens, approxCmds, ok := buildCLIXApproxEllipsePatchTokens(c, fill, baseToken, allowLossySnap); ok {
			tokens = append(tokens, approxTokens...)
			cmdCount += approxCmds
			continue
		}
		if approxTokens, approxCmds, ok := buildCLIXApproxTrianglePatchTokens(c, fill, baseToken, allowLossySnap); ok {
			tokens = append(tokens, approxTokens...)
			cmdCount += approxCmds
			continue
		}
		rects := buildCLIXRectanglesForMask(c.mask, c.x0, c.y0, c.w, c.h, c.color)
		for _, r := range rects {
			tokens = append(tokens, fmt.Sprintf("@%d,%d,%d,%d=%s", r.x, r.y, r.w, r.h, fill))
		}
		cmdCount += len(rects)
	}
	return tokens, cmdCount
}

func buildCLIXRectanglesForBase(pixels []RGBA, width, height int, base RGBA) []clixRect {
	if width <= 0 || height <= 0 || len(pixels) == 0 {
		return nil
	}
	baseKey := packRGBA(base)
	rects := make([]clixRect, 0, height)
	active := make(map[clixRectRunKey]int)
	for y := 0; y < height; y++ {
		next := make(map[clixRectRunKey]int)
		rowOff := y * width
		for x := 0; x < width; {
			px := pixels[rowOff+x]
			key := packRGBA(px)
			if key == baseKey {
				x++
				continue
			}
			x0 := x
			x++
			for x < width && packRGBA(pixels[rowOff+x]) == key {
				x++
			}
			x1 := x - 1
			runKey := clixRectRunKey{color: key, x0: x0, x1: x1}
			if idx, ok := active[runKey]; ok {
				rects[idx].h++
				next[runKey] = idx
				continue
			}
			rects = append(rects, clixRect{
				x:     x0,
				y:     y,
				w:     x1 - x0 + 1,
				h:     1,
				color: px,
			})
			next[runKey] = len(rects) - 1
		}
		active = next
	}
	return rects
}

func clixLiteralCanonicalHex(tok string) (string, bool) {
	switch tok {
	case "BG", "S", "T":
		return "", false
	}
	if _, ok := PURE_LOOKUP[tok]; ok {
		return "", false
	}
	if strings.HasPrefix(tok, "@") {
		return "", false
	}
	px, err := tokenToRGBA(tok, nil, nil)
	if err != nil {
		return "", false
	}
	return rgbaToCompactHex(px), true
}

func buildCLIXMacroMapping(tokens []string) (map[string]string, [][2]string) {
	freq := map[string]int{}
	for _, t := range tokens {
		if h, ok := clixLiteralCanonicalHex(t); ok {
			freq[h]++
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
	macroHexToName := map[string]string{}
	macrosOrdered := make([][2]string, 0, len(list))
	names := generateMacroNames(len(list))
	for i, it := range list {
		name := names[i]
		macroHexToName[it.hex] = name
		macrosOrdered = append(macrosOrdered, [2]string{name, it.hex})
	}
	return macroHexToName, macrosOrdered
}

func clixTokensToLines(tokens []string, macrosOrdered [][2]string, perLine int) []string {
	if perLine <= 0 {
		perLine = len(tokens)
	}
	if perLine <= 0 {
		perLine = 1
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
	lines := make([]string, 0, (len(tokens)+perLine-1)/perLine)
	for i := 0; i < len(tokens); i += perLine {
		end := i + perLine
		if end > len(tokens) {
			end = len(tokens)
		}
		lines = append(lines, makeLine(tokens[i:end]))
	}
	return lines
}

func clixPlanScore(lines []string, macrosOrdered [][2]string, useBG bool) int {
	score := 0
	for _, ln := range lines {
		score += len(ln) + 1
	}
	if useBG {
		score += len("BG=00000000") + 1
	}
	if len(macrosOrdered) > 0 {
		score += 1
		score += len("M_SM_E") + 10*len(macrosOrdered) + 1
	}
	return score
}

type clixPresetDefaults struct {
	roundStep          int
	deltaSnapThreshold int
	paletteSize        int
	paletteDither      bool
	blockSize          int
	blockVarThreshold  float64
}

func clixDefaultsForMode(mode string) clixPresetDefaults {
	switch mode {
	case "lossless":
		return clixPresetDefaults{
			roundStep:          0,
			deltaSnapThreshold: 0,
			paletteSize:        0,
			paletteDither:      false,
			blockSize:          0,
			blockVarThreshold:  12.0,
		}
	case "unsafe":
		return clixPresetDefaults{
			roundStep:          3,
			deltaSnapThreshold: 3,
			paletteSize:        64,
			paletteDither:      false,
			blockSize:          2,
			blockVarThreshold:  12.0,
		}
	case "safe", "experimental":
		return clixPresetDefaults{
			roundStep:          2,
			deltaSnapThreshold: 2,
			paletteSize:        0,
			paletteDither:      false,
			blockSize:          0,
			blockVarThreshold:  12.0,
		}
	default:
		return clixPresetDefaults{
			roundStep:          2,
			deltaSnapThreshold: 2,
			paletteSize:        0,
			paletteDither:      false,
			blockSize:          0,
			blockVarThreshold:  12.0,
		}
	}
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
	if tok[0] != '#' {
		return RGBA{}, fmt.Errorf("not a hex token: %q", tok)
	}
	hex := tok[1:]
	if strings.ContainsAny(hex, "RGZ") {
		return parseHexTokenCompact(hex)
	}
	if len(hex) != 6 && len(hex) != 8 {
		return RGBA{}, fmt.Errorf("bad hex token length: %q", tok)
	}
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
	if strings.ContainsAny(tok, "RGZ") {
		var vals [4]uint8
		v, ok := parseHexBytePair(tok, 0)
		if !ok {
			return RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
		}
		vals[0] = v
		pos := 2
		for channel := 1; channel < 4; channel++ {
			if pos >= len(tok) {
				return RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
			}
			if v, ok := channelRefValue(tok[pos], &vals, channel); ok {
				vals[channel] = v
				pos++
				continue
			}
			v, ok := parseHexBytePair(tok, pos)
			if !ok {
				return RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
			}
			vals[channel] = v
			pos += 2
		}
		if pos != len(tok) {
			return RGBA{}, fmt.Errorf("bad compact RGBA token: %q", tok)
		}
		return RGBA{vals[0], vals[1], vals[2], vals[3]}, nil
	}
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
	if len(tok) >= 5 && isHexDigit(tok[0]) && strings.ContainsAny(tok, "RGZ") {
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
	if src, ok := img.(*image.NRGBA); ok {
		w := b.Dx() * 4
		for y := 0; y < b.Dy(); y++ {
			so := src.PixOffset(b.Min.X, b.Min.Y+y)
			do := out.PixOffset(b.Min.X, b.Min.Y+y)
			copy(out.Pix[do:do+w], src.Pix[so:so+w])
		}
	} else {
		for y := b.Min.Y; y < b.Max.Y; y++ {
			for x := b.Min.X; x < b.Max.X; x++ {
				out.SetNRGBA(x, y, color.NRGBAModel.Convert(img.At(x, y)).(color.NRGBA))
			}
		}
	}
	for y0 := b.Min.Y; y0 < b.Max.Y; y0 += block {
		for x0 := b.Min.X; x0 < b.Max.X; x0 += block {
			x1 := min(x0+block, b.Max.X)
			y1 := min(y0+block, b.Max.Y)
			var rs, gs, bs, count float64
			var r2, g2, b2 float64
			for y := y0; y < y1; y++ {
				o := out.PixOffset(x0, y)
				for x := x0; x < x1; x++ {
					r := float64(out.Pix[o+0])
					g := float64(out.Pix[o+1])
					bl := float64(out.Pix[o+2])
					rs += r
					gs += g
					bs += bl
					r2 += r * r
					g2 += g * g
					b2 += bl * bl
					count++
					o += 4
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
					o := out.PixOffset(x0, y)
					for x := x0; x < x1; x++ {
						out.Pix[o+0] = R
						out.Pix[o+1] = G
						out.Pix[o+2] = B
						o += 4
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
	enableShapes         bool
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

func applyImageModeSettings(img *image.NRGBA, st encodeSettings) (*image.NRGBA, error) {
	switch st.mode {
	case "lossless":
	case "safe", "experimental":
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
		return nil, errors.New("mode must be 'lossless', 'safe', 'unsafe', or 'experimental'")
	}
	return img, nil
}

func prepareImageForEncoding(src image.Image, st encodeSettings) (*image.NRGBA, error) {
	img := imageToNRGBA(src)
	if st.chromaMode != "" && st.chromaMode != "444" {
		img = applyChromaSubsample(img, st.chromaMode)
	}
	return applyImageModeSettings(img, st)
}

func imageToPixels(img *image.NRGBA) []RGBA {
	b := img.Bounds()
	w, h := b.Dx(), b.Dy()
	pixels := make([]RGBA, 0, w*h)
	for y := 0; y < h; y++ {
		row := img.PixOffset(b.Min.X, b.Min.Y+y)
		line := img.Pix[row : row+w*4]
		for x := 0; x < len(line); x += 4 {
			pixels = append(pixels, RGBA{line[x], line[x+1], line[x+2], line[x+3]})
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

func (w *bitWriter) WriteFrom(src *bitWriter) {
	for _, b := range src.buf {
		w.WriteBits(uint64(b), 8)
	}
	if src.nbits == 0 {
		return
	}
	for i := uint8(0); i < src.nbits; i++ {
		bit := (src.cur >> (7 - i)) & 1
		w.WriteBit(bit)
	}
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

func dct8x8Into(block []float64, out []float64) {
	var tmp [64]float64
	for y := 0; y < 8; y++ {
		row := y * 8
		for u := 0; u < 8; u++ {
			sum := 0.0
			crow := dctCos[u]
			for x := 0; x < 8; x++ {
				sum += block[row+x] * crow[x]
			}
			tmp[row+u] = sum
		}
	}
	for v := 0; v < 8; v++ {
		sv := dctScale[v]
		crow := dctCos[v]
		for u := 0; u < 8; u++ {
			sum := 0.0
			for y := 0; y < 8; y++ {
				sum += tmp[y*8+u] * crow[y]
			}
			out[v*8+u] = 0.25 * dctScale[u] * sv * sum
		}
	}
}

func dct8x8(block [64]float64) [64]float64 {
	var out [64]float64
	dct8x8Into(block[:], out[:])
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

func encodePlaneDCTRiceEx(w *bitWriter, plane []float64, pw, ph int, qtable [64]int, center bool, k uint8, predDC, zeroRun, blockSkip, acMag bool) error {
	bw := (pw + 7) / 8
	bh := (ph + 7) / 8
	blocks := bw * bh
	blockAll := make([]float64, blocks*64)
	coeffAll := make([]float64, blocks*64)
	var dcVals []int
	if predDC {
		dcVals = make([]int, bw*bh)
	}
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			off := (by*bw + bx) * 64
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
					blockAll[off+y*8+x] = v
				}
			}
		}
	}
	dctEncodeMany(blockAll, coeffAll)
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			off := (by*bw + bx) * 64
			var quant [64]int
			allZero := true
			for i := 0; i < 64; i++ {
				q := int(math.Round(coeffAll[off+i] / float64(qtable[i])))
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

func reconstructPlaneFromQuantizedDCT(plane []float64, pw, ph int, qtable [64]int, center bool, clamp bool) []float64 {
	bw := (pw + 7) / 8
	bh := (ph + 7) / 8
	blocks := bw * bh
	blockAll := make([]float64, blocks*64)
	coeffAll := make([]float64, blocks*64)
	reconBlocks := make([]float64, blocks*64)
	out := make([]float64, pw*ph)
	for by := 0; by < bh; by++ {
		for bx := 0; bx < bw; bx++ {
			off := (by*bw + bx) * 64
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
					blockAll[off+y*8+x] = v
				}
			}
		}
	}
	dctEncodeMany(blockAll, coeffAll)
	for i := range coeffAll {
		q := int(math.Round(coeffAll[i] / float64(qtable[i%64])))
		coeffAll[i] = float64(q) * float64(qtable[i%64])
	}
	idctDecodeMany(coeffAll, reconBlocks)
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
					v := reconBlocks[off+y*8+x]
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
	return out
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

func planeAllValue(p []float64, v float64, eps float64) bool {
	if len(p) == 0 {
		return true
	}
	for _, x := range p {
		if math.Abs(x-v) > eps {
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
	for i, framePath := range frames {
		raw, err := decodeImageFile(framePath, ffmpegPath)
		if err != nil {
			return false, err
		}
		img, err := prepareImageForEncoding(raw, st)
		if err != nil {
			return false, err
		}
		if imageHasAlpha(img) {
			printProgress(i+1, len(frames))
			return true, nil
		}
		printProgress(i+1, len(frames))
	}
	return false, nil
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

func encodeCLIX(imagePath, clixPath string, st encodeSettings, ffmpegPath string) error {
	src, err := decodeImageFile(imagePath, ffmpegPath)
	if err != nil {
		return err
	}
	img, err := applyImageModeSettings(imageToNRGBA(src), st)
	if err != nil {
		return err
	}
	b := img.Bounds()
	width := b.Dx()
	height := b.Dy()
	pixels := imageToPixels(img)
	bg, bgShare := detectBackground(pixels)
	bgToken := rgbaToToken(bg)
	useBG := st.enableBackground && bgShare >= st.backgroundMinShare
	if useBG && len(bgToken) < len("BG") {
		useBG = false
	}

	streamRaw := make([]string, 0, len(pixels))
	var prev *RGBA
	for _, px := range pixels {
		if useBG && px == bg {
			streamRaw = append(streamRaw, "BG")
			tmp := px
			prev = &tmp
			continue
		}
		if prev == nil {
			streamRaw = append(streamRaw, rgbaToToken(px))
			tmp := px
			prev = &tmp
			continue
		}
		if st.deltaSnapThreshold > 0 && withinDelta(px, *prev, st.deltaSnapThreshold) {
			streamRaw = append(streamRaw, "S")
		} else {
			streamRaw = append(streamRaw, rgbaToToken(px))
			tmp := px
			prev = &tmp
		}
	}

	type clixPlan struct {
		lines         []string
		macrosOrdered [][2]string
		useBG         bool
		score         int
		commandCount  int
	}
	buildPlan := func(raw []string, planUseBG bool, allowMacros bool, commandCount int) clixPlan {
		tokens := append([]string(nil), raw...)
		macrosOrdered := [][2]string{}
		if allowMacros {
			macroHexToName, ordered := buildCLIXMacroMapping(tokens)
			macrosOrdered = ordered
			if len(macroHexToName) > 0 {
				for i := range tokens {
					h, isLit := clixLiteralCanonicalHex(tokens[i])
					if !isLit {
						continue
					}
					if repl, ok := macroHexToName[h]; ok {
						tokens[i] = repl
					}
				}
			}
		}
		if st.enableTokenRLE {
			tokens = rleTokens(tokens)
		}
		if st.enableSequenceRLE {
			tokens = sequenceRLE(tokens, st.sequenceRLEMaxSeqLen)
		}
		lines := clixTokensToLines(tokens, macrosOrdered, 1024)
		return clixPlan{
			lines:         lines,
			macrosOrdered: macrosOrdered,
			useBG:         planUseBG,
			score:         clixPlanScore(lines, macrosOrdered, planUseBG),
			commandCount:  commandCount,
		}
	}

	streamPlan := buildPlan(streamRaw, useBG, true, 0)

	selected := streamPlan
	if st.enableShapes {
		rects := buildCLIXRectanglesForBase(pixels, width, height, bg)
		baseFillToken := bgToken
		rectPlanUseBG := false
		if useBG {
			baseFillToken = "BG"
			rectPlanUseBG = true
		}
		rectRaw := make([]string, 0, len(rects)+1)
		rectRaw = append(rectRaw, fmt.Sprintf("%s*%d", baseFillToken, width*height))
		for _, r := range rects {
			rectRaw = append(rectRaw, fmt.Sprintf("@%d,%d,%d,%d=%s", r.x, r.y, r.w, r.h, rgbaToToken(r.color)))
		}
		rectPlan := buildPlan(rectRaw, rectPlanUseBG, false, len(rects))

		allowLossyShapeSnap := st.mode != "lossless"
		shapeRaw, shapeCmdCount := buildCLIXShapeTokensForBase(pixels, width, height, bg, baseFillToken, allowLossyShapeSnap)
		shapePlan := buildPlan(shapeRaw, rectPlanUseBG, false, shapeCmdCount)
		shapeHasAdvancedPrimitive := false
		for _, tok := range shapeRaw {
			if strings.HasPrefix(tok, "@C,") || strings.HasPrefix(tok, "@T,") {
				shapeHasAdvancedPrimitive = true
				break
			}
		}

		selectedKind := "stream"
		bestEffectiveScore := streamPlan.score
		const clixShapePlanMinSavings = 8
		const clixShapePlanPerCommandPenalty = 2
		for _, candInfo := range []struct {
			kind string
			plan clixPlan
		}{
			{kind: "rect", plan: rectPlan},
			{kind: "shape", plan: shapePlan},
		} {
			cand := candInfo.plan
			candEffective := cand.score + cand.commandCount*clixShapePlanPerCommandPenalty
			if candEffective+clixShapePlanMinSavings < streamPlan.score && candEffective < bestEffectiveScore {
				selected = cand
				selectedKind = candInfo.kind
				bestEffectiveScore = candEffective
			}
		}
		if selectedKind == "stream" && shapeHasAdvancedPrimitive {
			const clixShapeNearTieTolerance = 24
			if shapePlan.score <= streamPlan.score+clixShapeNearTieTolerance {
				selected = shapePlan
				selectedKind = "shape"
			}
		}
	}

	lines := selected.lines
	macrosOrdered := selected.macrosOrdered
	useBG = selected.useBG

	out, err := os.Create(clixPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := newZstdWriter(out, level)
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
	if err := writeLine(fmt.Sprintf("MODE=%s", st.mode)); err != nil {
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
	encLine := strings.Join(encFlags, "+")
	if encLine != "RLE+SEQ" {
		if err := writeLine("ENCODING=" + encLine); err != nil {
			return err
		}
	}
	if useBG {
		if err := writeLine(fmt.Sprintf("BG=%02X%02X%02X%02X", bg.R, bg.G, bg.B, bg.A)); err != nil {
			return err
		}
	}
	def := clixDefaultsForMode(st.mode)
	if st.roundStep != def.roundStep {
		if err := writeLine(fmt.Sprintf("ROUND_STEP=%d", st.roundStep)); err != nil {
			return err
		}
	}
	if st.deltaSnapThreshold != def.deltaSnapThreshold {
		if err := writeLine(fmt.Sprintf("DELTA_SNAP_THRESHOLD=%d", st.deltaSnapThreshold)); err != nil {
			return err
		}
	}
	if st.paletteSize != def.paletteSize {
		if err := writeLine(fmt.Sprintf("PALETTE_SIZE=%d", st.paletteSize)); err != nil {
			return err
		}
	}
	if st.paletteDither != def.paletteDither {
		if err := writeLine(fmt.Sprintf("PALETTE_DITHER=%d", boolTo01(st.paletteDither))); err != nil {
			return err
		}
	}
	if st.blockSize != def.blockSize {
		if err := writeLine(fmt.Sprintf("BLOCK_SIZE=%d", st.blockSize)); err != nil {
			return err
		}
	}
	if math.Abs(st.blockVarThreshold-def.blockVarThreshold) > 1e-9 {
		if err := writeLine(fmt.Sprintf("BLOCK_VAR_THRESHOLD=%g", st.blockVarThreshold)); err != nil {
			return err
		}
	}
	if level != 22 {
		if err := writeLine(fmt.Sprintf("ZSTD_LEVEL=%d", level)); err != nil {
			return err
		}
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
	opMacro  = 0xFE
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

const (
	blxMacroMaxEntries = 64
	blxMacroMinUses    = 4
)

func blxLiteralHex(tok string) (string, error) {
	switch tok {
	case "BG", "S", "T":
		return "", nil
	}
	if _, ok := blxPureIndex[tok]; ok {
		return "", nil
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
		return "", err
	}
	return rgbaToCompactHex(px), nil
}

func blxCollectLiteralFreq(tokens []string) (map[string]int, error) {
	freq := make(map[string]int)
	for _, t := range tokens {
		if strings.HasPrefix(t, "(") {
			in, _, err := blxParseGroup(t)
			if err != nil {
				return nil, err
			}
			for _, inner := range in {
				h, err := blxLiteralHex(inner)
				if err != nil {
					return nil, err
				}
				if h != "" {
					freq[h]++
				}
			}
			continue
		}
		base := t
		if strings.Contains(t, "*") {
			i := strings.LastIndexByte(t, '*')
			if i > 0 {
				cntStr := t[i+1:]
				if isAllDigits(cntStr) {
					base = t[:i]
				}
			}
		}
		h, err := blxLiteralHex(base)
		if err != nil {
			return nil, err
		}
		if h != "" {
			freq[h]++
		}
	}
	return freq, nil
}

func blxBuildMacros(tokens []string) ([]RGBA, map[string]byte, error) {
	freq, err := blxCollectLiteralFreq(tokens)
	if err != nil {
		return nil, nil, err
	}
	type kv struct {
		hex string
		n   int
	}
	list := make([]kv, 0, len(freq))
	for h, n := range freq {
		list = append(list, kv{hex: h, n: n})
	}
	sort.Slice(list, func(i, j int) bool {
		if list[i].n != list[j].n {
			return list[i].n > list[j].n
		}
		return list[i].hex < list[j].hex
	})
	macros := make([]RGBA, 0, blxMacroMaxEntries)
	macroHexToIndex := make(map[string]byte, blxMacroMaxEntries)
	for _, it := range list {
		if it.n < blxMacroMinUses || len(macros) >= blxMacroMaxEntries {
			break
		}
		px, err := parseHexTokenCompact(it.hex)
		if err != nil {
			return nil, nil, err
		}
		macroHexToIndex[it.hex] = byte(len(macros))
		macros = append(macros, px)
	}
	return macros, macroHexToIndex, nil
}

func writeUvarint(w io.Writer, x uint64) error {
	var buf [10]byte
	n := binary.PutUvarint(buf[:], x)
	_, err := w.Write(buf[:n])
	return err
}

func blxWriteSimpleToken(w io.Writer, tok string, macroHexToIndex map[string]byte) error {
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
	if len(macroHexToIndex) > 0 {
		if idx, ok := macroHexToIndex[rgbaToCompactHex(px)]; ok {
			if _, err := w.Write([]byte{opMacro}); err != nil {
				return err
			}
			return writeUvarint(w, uint64(idx))
		}
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

func blxWriteRepeat(w io.Writer, base string, count int, macroHexToIndex map[string]byte) error {
	if count <= 0 {
		return nil
	}
	if _, err := w.Write([]byte{opRepeat}); err != nil {
		return err
	}
	if err := blxWriteSimpleToken(w, base, macroHexToIndex); err != nil {
		return err
	}
	return writeUvarint(w, uint64(count))
}

func blxWriteSeq(w io.Writer, inner []string, count int, macroHexToIndex map[string]byte) error {
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
		if err := blxWriteSimpleToken(w, t, macroHexToIndex); err != nil {
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
	img, err := applyImageModeSettings(imageToNRGBA(src), st)
	if err != nil {
		return err
	}
	b := img.Bounds()
	width, height := b.Dx(), b.Dy()
	pixels := imageToPixels(img)
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
	blxMacros, blxMacroHexToIndex, err := blxBuildMacros(tmp)
	if err != nil {
		return err
	}
	out, err := os.Create(blixPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := newZstdWriter(out, level)
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
	if len(blxMacros) > 0 {
		var m strings.Builder
		m.WriteString("MACROS=")
		for i, px := range blxMacros {
			if i > 0 {
				m.WriteByte(',')
			}
			m.WriteString(rgbaToCompactHex(px))
		}
		if _, err := bw.WriteString(m.String() + "\n"); err != nil {
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
			if err := blxWriteSeq(bw, in, cnt, blxMacroHexToIndex); err != nil {
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
			if err := blxWriteRepeat(bw, base, n, blxMacroHexToIndex); err != nil {
				return err
			}
			continue
		}
		if err := blxWriteSimpleToken(bw, t, blxMacroHexToIndex); err != nil {
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

func planeToMatchI16(p []float64) []int16 {
	if p == nil {
		return nil
	}
	out := make([]int16, len(p))
	for i, v := range p {
		out[i] = int16(v + 0.5)
	}
	return out
}

func blockMatchScoreI16(cur, ref []int16, frameW, frameH, curX, curY, srcX, srcY, blockW, blockH, threshold int) (int, bool) {
	if curX < 0 || curY < 0 || srcX < 0 || srcY < 0 || curX+blockW > frameW || curY+blockH > frameH || srcX+blockW > frameW || srcY+blockH > frameH {
		return 0, false
	}
	if threshold == 0 {
		for y := 0; y < blockH; y++ {
			cRow := (curY+y)*frameW + curX
			rRow := (srcY+y)*frameW + srcX
			for x := 0; x < blockW; x++ {
				if cur[cRow+x] != ref[rRow+x] {
					return 1, false
				}
			}
		}
		return 0, true
	}
	sad := 0
	limit := threshold * blockW * blockH
	for y := 0; y < blockH; y++ {
		cRow := (curY+y)*frameW + curX
		rRow := (srcY+y)*frameW + srcX
		for x := 0; x < blockW; x++ {
			d := int(cur[cRow+x]) - int(ref[rRow+x])
			if d < 0 {
				d = -d
			}
			sad += d
		}
		if sad > limit {
			return sad, false
		}
	}
	return sad, true
}

func exhaustiveMotionI16(cur, ref []int16, frameW, frameH, curX, curY, blockW, blockH, radius, threshold int) (int, int, int, bool) {
	bestSad := int(^uint(0) >> 1)
	bestDx, bestDy := 0, 0
	found := false
	for dy := -radius; dy <= radius; dy++ {
		for dx := -radius; dx <= radius; dx++ {
			sad, ok := blockMatchScoreI16(cur, ref, frameW, frameH, curX, curY, curX+dx, curY+dy, blockW, blockH, threshold)
			if !ok {
				continue
			}
			if sad < bestSad {
				bestSad, bestDx, bestDy, found = sad, dx, dy, true
				if sad == 0 {
					return bestDx, bestDy, bestSad, true
				}
			}
		}
	}
	return bestDx, bestDy, bestSad, found
}

func blockSADI16(cur, ref []int16, frameW, frameH, curX, curY, srcX, srcY, blockW, blockH int) (int, bool) {
	if curX < 0 || curY < 0 || srcX < 0 || srcY < 0 || curX+blockW > frameW || curY+blockH > frameH || srcX+blockW > frameW || srcY+blockH > frameH {
		return 0, false
	}
	sad := 0
	for y := 0; y < blockH; y++ {
		cRow := (curY+y)*frameW + curX
		rRow := (srcY+y)*frameW + srcX
		for x := 0; x < blockW; x++ {
			d := int(cur[cRow+x]) - int(ref[rRow+x])
			if d < 0 {
				d = -d
			}
			sad += d
		}
	}
	return sad, true
}

func diamondMotionI16(cur, ref []int16, frameW, frameH, curX, curY, blockW, blockH, radius, threshold int) (int, int, int, bool) {
	type pt struct{ dx, dy int }
	large := [...]pt{{0, -2}, {0, 2}, {-2, 0}, {2, 0}, {-1, -1}, {-1, 1}, {1, -1}, {1, 1}}
	const refine = 2

	bestDx, bestDy := 0, 0
	bestSad := int(^uint(0) >> 1)
	found := false

	eval := func(dx, dy int) (int, bool) {
		if dx < -radius || dx > radius || dy < -radius || dy > radius {
			return 0, false
		}
		return blockSADI16(cur, ref, frameW, frameH, curX, curY, curX+dx, curY+dy, blockW, blockH)
	}

	accept := func() (int, int, int, bool) {
		if !found {
			return 0, 0, 0, false
		}
		if bestSad > threshold*blockW*blockH {
			return bestDx, bestDy, bestSad, false
		}
		return bestDx, bestDy, bestSad, true
	}

	if sad, ok := eval(0, 0); ok {
		bestSad, bestDx, bestDy, found = sad, 0, 0, true
		if sad == 0 {
			return 0, 0, 0, true
		}
	}

	for steps := 0; steps < 4*radius+4; steps++ {
		moveDx, moveDy := bestDx, bestDy
		improved := false
		for _, p := range large {
			dx, dy := bestDx+p.dx, bestDy+p.dy
			sad, ok := eval(dx, dy)
			if !ok {
				continue
			}
			if !found || sad < bestSad {
				bestSad, moveDx, moveDy, found, improved = sad, dx, dy, true, true
			}
		}
		if !improved {
			break
		}
		bestDx, bestDy = moveDx, moveDy
		if bestSad == 0 {
			return bestDx, bestDy, 0, true
		}
	}

	cx, cy := bestDx, bestDy
	for dy := cy - refine; dy <= cy+refine; dy++ {
		for dx := cx - refine; dx <= cx+refine; dx++ {
			if dx == cx && dy == cy {
				continue
			}
			sad, ok := eval(dx, dy)
			if !ok {
				continue
			}
			if !found || sad < bestSad {
				bestSad, bestDx, bestDy, found = sad, dx, dy, true
			}
		}
	}

	return accept()
}

func findBestMotionVectorI16(cur, ref []int16, frameW, frameH, curX, curY, blockW, blockH, radius, threshold int) (int, int, int, bool) {
	if ref == nil {
		return 0, 0, 0, false
	}
	if radius < 0 {
		radius = 0
	}
	if threshold == 0 || radius <= 1 {
		return exhaustiveMotionI16(cur, ref, frameW, frameH, curX, curY, blockW, blockH, radius, threshold)
	}
	return diamondMotionI16(cur, ref, frameW, frameH, curX, curY, blockW, blockH, radius, threshold)
}

func blockSADBiI16(cur, refA, refB []int16, frameW, frameH, curX, curY, blockW, blockH, dxA, dyA, dxB, dyB int) (int, bool) {
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
		cRow := (curY+y)*frameW + curX
		aRow := (syA+y)*frameW + sxA
		bRow := (syB+y)*frameW + sxB
		for x := 0; x < blockW; x++ {
			p := (int(refA[aRow+x]) + int(refB[bRow+x])) / 2
			d := int(cur[cRow+x]) - p
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
	enc, err := newZstdWriter(out, level)
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
					if useTemporal && prevFrame != nil {
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
		printProgress(i+1, len(frames))
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

func encodeVLIX2(dirPath, outPath string, st encodeSettings, fps float64, keyInterval int, audio []byte, ffmpegPath string, chromaMode string, dctQuality, dctResQuality int, motion bool, blockDim, searchRadius, motionThreshold int, bframes int, fast bool) error {
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

	// Declare ALPHA=0 for fully-opaque videos so the decoder drops the alpha
	alphaEnabled := true
	if !fast {
		alphaEnabled, err = detectFramesAlpha(frames, st, ffmpegPath)
		if err != nil {
			return err
		}
	}

	out, err := os.Create(outPath)
	if err != nil {
		return err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := newZstdWriter(out, level)
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
	type planeTask struct {
		enabled bool
		plane   []float64
		pw      int
		ph      int
		qtable  [64]int
		center  bool
		k       uint8
	}
	encodePlaneTasks := func(tasks []planeTask) ([]bitWriter, error) {
		outParts := make([]bitWriter, len(tasks))
		var wg sync.WaitGroup
		var mu sync.Mutex
		var firstErr error
		for i := range tasks {
			t := tasks[i]
			if !t.enabled {
				continue
			}
			wg.Add(1)
			go func(idx int, task planeTask) {
				defer wg.Done()
				var bw bitWriter
				if err := encodePlane(&bw, task.plane, task.pw, task.ph, task.qtable, task.center, task.k); err != nil {
					mu.Lock()
					if firstErr == nil {
						firstErr = err
					}
					mu.Unlock()
					return
				}
				outParts[idx] = bw
			}(i, t)
		}
		wg.Wait()
		if firstErr != nil {
			return nil, firstErr
		}
		return outParts, nil
	}

	plans, coding := buildVLIX2Plan(len(frames), keyInterval, bframes)
	refUses := buildVLIX2RefUseCounts(plans, coding)
	encodedCount := 0
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
			keyMask := uint8(0x1 | 0x2 | 0x4)
			keyAlphaEncoded := alphaEnabled && !planeAllValue(planes.a, 255, 1e-6)
			if keyAlphaEncoded {
				keyMask |= 0x8
			}
			if dctPlaneMask {
				coeffBits.WriteBits(uint64(keyMask), 8)
			}
			tasks := []planeTask{
				{enabled: true, plane: planes.y, pw: planes.w, ph: planes.h, qtable: qY, center: true, k: vlxDctRiceK},
				{enabled: true, plane: planes.cb, pw: planes.cw, ph: planes.ch, qtable: qC, center: true, k: vlxDctRiceK},
				{enabled: true, plane: planes.cr, pw: planes.cw, ph: planes.ch, qtable: qC, center: true, k: vlxDctRiceK},
				{enabled: keyAlphaEncoded, plane: planes.a, pw: planes.w, ph: planes.h, qtable: qY, center: true, k: vlxDctRiceK},
			}
			parts, err := encodePlaneTasks(tasks)
			if err != nil {
				return err
			}
			for i := range tasks {
				if tasks[i].enabled {
					coeffBits.WriteFrom(&parts[i])
				}
			}
			coeffBytes := coeffBits.Bytes()
			if err := writeUvarint(bw, uint64(len(coeffBytes))); err != nil {
				return err
			}
			if _, err := bw.Write(coeffBytes); err != nil {
				return err
			}
			reconPlanes := ycbcrPlanes{
				y:    reconstructPlaneFromQuantizedDCT(planes.y, planes.w, planes.h, qY, true, true),
				cb:   reconstructPlaneFromQuantizedDCT(planes.cb, planes.cw, planes.ch, qC, true, true),
				cr:   reconstructPlaneFromQuantizedDCT(planes.cr, planes.cw, planes.ch, qC, true, true),
				a:    filledPlane(planes.w*planes.h, 255),
				w:    planes.w,
				h:    planes.h,
				cw:   planes.cw,
				ch:   planes.ch,
				mode: planes.mode,
			}
			if alphaEnabled && (!dctPlaneMask || (keyMask&0x8) != 0) {
				reconPlanes.a = reconstructPlaneFromQuantizedDCT(planes.a, planes.w, planes.h, qY, true, true)
			}
			normalizeRefPlanesInPlace(&reconPlanes)
			refPlanes[plan.idx] = reconPlanes
			encodedCount++
			printProgress(encodedCount, len(frames))
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

		blockMVs := computeVLIX2BlockMVs(plan.ftype, planes.y, prevRef.y, nextRef.y, width, height, blockDim, searchRadius, motionThreshold, motion)
		var mvBits bitWriter
		for by := 0; by < bhBlocks; by++ {
			for bx := 0; bx < bwBlocks; bx++ {
				bi := by*bwBlocks + bx
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
				mv := blockMVs[bi]
				mvBits.WriteBits(uint64(mv.mode), 2)
				switch mv.mode {
				case 1, 2:
					writeRiceSigned(&mvBits, mv.dx1, vlxMvRiceK)
					writeRiceSigned(&mvBits, mv.dy1, vlxMvRiceK)
				case 3:
					writeRiceSigned(&mvBits, mv.dx1, vlxMvRiceK)
					writeRiceSigned(&mvBits, mv.dy1, vlxMvRiceK)
					writeRiceSigned(&mvBits, mv.dx2, vlxMvRiceK)
					writeRiceSigned(&mvBits, mv.dy2, vlxMvRiceK)
				}

				switch mv.mode {
				case 1:
					fillPredBlock(predY, prevRef.y, width, height, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
					if alphaEnabled {
						fillPredBlock(predA, prevRef.a, width, height, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
					}
					fillPredBlockChroma(predCb, prevRef.cb, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
					fillPredBlockChroma(predCr, prevRef.cr, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
				case 2:
					fillPredBlock(predY, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
					if alphaEnabled {
						fillPredBlock(predA, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
					}
					fillPredBlockChroma(predCb, nextRef.cb, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
					fillPredBlockChroma(predCr, nextRef.cr, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1)
				case 3:
					fillPredBlockBi(predY, prevRef.y, nextRef.y, width, height, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1, mv.dx2, mv.dy2)
					if alphaEnabled {
						fillPredBlockBi(predA, prevRef.a, nextRef.a, width, height, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1, mv.dx2, mv.dy2)
					}
					fillPredBlockChromaBi(predCb, prevRef.cb, nextRef.cb, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1, mv.dx2, mv.dy2)
					fillPredBlockChromaBi(predCr, prevRef.cr, nextRef.cr, planes.cw, planes.ch, subX, subY, bxPix, byPix, bwPix, bhPix, mv.dx1, mv.dy1, mv.dx2, mv.dy2)
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
		tasks := []planeTask{
			{enabled: !dctPlaneMask || mask&0x1 != 0, plane: resY, pw: planes.w, ph: planes.h, qtable: qYRes, center: false, k: vlxDctResRiceK},
			{enabled: !dctPlaneMask || mask&0x2 != 0, plane: resCb, pw: planes.cw, ph: planes.ch, qtable: qCRes, center: false, k: vlxDctResRiceK},
			{enabled: !dctPlaneMask || mask&0x4 != 0, plane: resCr, pw: planes.cw, ph: planes.ch, qtable: qCRes, center: false, k: vlxDctResRiceK},
			{enabled: alphaEnabled && (!dctPlaneMask || mask&0x8 != 0), plane: resA, pw: planes.w, ph: planes.h, qtable: qYRes, center: false, k: vlxDctResRiceK},
		}
		parts, err := encodePlaneTasks(tasks)
		if err != nil {
			return err
		}
		for i := range tasks {
			if tasks[i].enabled {
				coeffBits.WriteFrom(&parts[i])
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
			reconYRes := filledPlane(planes.w*planes.h, 0)
			if !dctPlaneMask || (mask&0x1) != 0 {
				reconYRes = reconstructPlaneFromQuantizedDCT(resY, planes.w, planes.h, qYRes, false, false)
			}
			reconCbRes := filledPlane(planes.cw*planes.ch, 0)
			if !dctPlaneMask || (mask&0x2) != 0 {
				reconCbRes = reconstructPlaneFromQuantizedDCT(resCb, planes.cw, planes.ch, qCRes, false, false)
			}
			reconCrRes := filledPlane(planes.cw*planes.ch, 0)
			if !dctPlaneMask || (mask&0x4) != 0 {
				reconCrRes = reconstructPlaneFromQuantizedDCT(resCr, planes.cw, planes.ch, qCRes, false, false)
			}
			reconARes := filledPlane(planes.w*planes.h, 0)
			if alphaEnabled && (!dctPlaneMask || (mask&0x8) != 0) {
				reconARes = reconstructPlaneFromQuantizedDCT(resA, planes.w, planes.h, qYRes, false, false)
			}
			reconA := filledPlane(planes.w*planes.h, 255)
			if alphaEnabled {
				reconA = addPlane(predA, reconARes)
			}
			recon := ycbcrPlanes{
				y:    addPlane(predY, reconYRes),
				cb:   addPlane(predCb, reconCbRes),
				cr:   addPlane(predCr, reconCrRes),
				a:    reconA,
				w:    planes.w,
				h:    planes.h,
				cw:   planes.cw,
				ch:   planes.ch,
				mode: planes.mode,
			}
			normalizeRefPlanesInPlace(&recon)
			refPlanes[plan.idx] = recon
		}
		switch plan.ftype {
		case vlxFrameDelta:
			consumeVLIX2Ref(refUses, plan.refPrev, refPlanes)
		case vlxFrameB:
			consumeVLIX2Ref(refUses, plan.refPrev, refPlanes)
			if plan.refNext != plan.refPrev {
				consumeVLIX2Ref(refUses, plan.refNext, refPlanes)
			}
		}
		encodedCount++
		printProgress(encodedCount, len(frames))
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

type vlix2BlockMV struct {
	mode     uint8
	dx1, dy1 int
	dx2, dy2 int
}

func computeVLIX2BlockMVs(
	planType byte,
	curY []float64,
	prevY []float64,
	nextY []float64,
	width, height int,
	blockDim int,
	searchRadius int,
	motionThreshold int,
	motionEnabled bool,
) []vlix2BlockMV {
	bwBlocks := (width + blockDim - 1) / blockDim
	bhBlocks := (height + blockDim - 1) / blockDim
	total := bwBlocks * bhBlocks
	if total == 0 {
		return nil
	}
	if !motionEnabled {
		// which bloats output badly (e.g. with --fast or --motion=false).
		defaultMode := uint8(1)
		if planType == vlxFrameB {
			defaultMode = 3
		}
		mvs := make([]vlix2BlockMV, total)
		for bi := range mvs {
			mvs[bi].mode = defaultMode
		}
		return mvs
	}
	if mvs, ok := tryComputeMotionMVs(planType, curY, prevY, nextY, width, height, blockDim, searchRadius, motionThreshold, motionEnabled); ok {
		return mvs
	}
	mvs := make([]vlix2BlockMV, total)

	curI := planeToMatchI16(curY)
	prevI := planeToMatchI16(prevY)
	nextI := planeToMatchI16(nextY)

	workers := runtime.GOMAXPROCS(0)
	if workers < 1 {
		workers = 1
	}
	if workers > total {
		workers = total
	}
	batch := (total + workers - 1) / workers
	var wg sync.WaitGroup
	for w := 0; w < workers; w++ {
		start := w * batch
		end := start + batch
		if end > total {
			end = total
		}
		if start >= end {
			continue
		}
		wg.Add(1)
		go func(a, b int) {
			defer wg.Done()
			for bi := a; bi < b; bi++ {
				bx := bi % bwBlocks
				by := bi / bwBlocks
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
				mv := vlix2BlockMV{}
				switch planType {
				case vlxFrameDelta:
					dx, dy, sad, ok := findBestMotionVectorI16(curI, prevI, width, height, bxPix, byPix, bwPix, bhPix, searchRadius, motionThreshold)
					if ok && (motionThreshold > 0 || sad == 0) {
						mv.mode = 1
						mv.dx1, mv.dy1 = dx, dy
					}
				case vlxFrameB:
					dxP, dyP, sadP, okP := findBestMotionVectorI16(curI, prevI, width, height, bxPix, byPix, bwPix, bhPix, searchRadius, motionThreshold)
					dxN, dyN, sadN, okN := findBestMotionVectorI16(curI, nextI, width, height, bxPix, byPix, bwPix, bhPix, searchRadius, motionThreshold)
					bestSad := int(^uint(0) >> 1)
					if okP {
						mv.mode = 1
						bestSad = sadP
						mv.dx1, mv.dy1 = dxP, dyP
					}
					if okN && sadN < bestSad {
						mv.mode = 2
						bestSad = sadN
						mv.dx1, mv.dy1 = dxN, dyN
					}
					if okP && okN {
						if sadBi, ok := blockSADBiI16(curI, prevI, nextI, width, height, bxPix, byPix, bwPix, bhPix, dxP, dyP, dxN, dyN); ok {
							limit := motionThreshold * bwPix * bhPix
							if motionThreshold == 0 {
								limit = 0
							}
							if sadBi <= limit && sadBi < bestSad {
								mv.mode = 3
								mv.dx1, mv.dy1, mv.dx2, mv.dy2 = dxP, dyP, dxN, dyN
							}
						}
					}
				}
				mvs[bi] = mv
			}
		}(start, end)
	}
	wg.Wait()
	return mvs
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

func buildVLIX2RefUseCounts(plans []vlix2FramePlan, coding []int) map[int]int {
	uses := make(map[int]int)
	for _, idx := range coding {
		if idx < 0 || idx >= len(plans) {
			continue
		}
		p := plans[idx]
		switch p.ftype {
		case vlxFrameDelta:
			if p.refPrev >= 0 {
				uses[p.refPrev]++
			}
		case vlxFrameB:
			if p.refPrev >= 0 {
				uses[p.refPrev]++
			}
			if p.refNext >= 0 {
				uses[p.refNext]++
			}
		}
	}
	return uses
}

func consumeVLIX2Ref(refUses map[int]int, refIdx int, refs map[int]ycbcrPlanes) {
	if refIdx < 0 || refUses == nil {
		return
	}
	n, ok := refUses[refIdx]
	if !ok {
		return
	}
	n--
	if n <= 0 {
		delete(refUses, refIdx)
		delete(refs, refIdx)
		return
	}
	refUses[refIdx] = n
}

const (
	sKindLit  = 1
	sKindBG   = 2
	sKindS    = 3
	sKindPure = 4
	sKindT    = 5
)

func readSimpleSymFromOp(op byte, br *bufio.Reader, macros []RGBA) (simpleSym, error) {
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
	case op == opMacro:
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

func readSimpleSym(br *bufio.Reader, macros []RGBA) (simpleSym, error) {
	op, err := br.ReadByte()
	if err != nil {
		return simpleSym{}, err
	}
	return readSimpleSymFromOp(op, br, macros)
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
	var macros []RGBA
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
		if strings.HasPrefix(line, "MACROS=") {
			body := strings.TrimSpace(strings.TrimPrefix(line, "MACROS="))
			if body == "" {
				continue
			}
			parts := strings.Split(body, ",")
			macros = make([]RGBA, 0, len(parts))
			for _, p := range parts {
				p = strings.TrimSpace(p)
				if p == "" {
					continue
				}
				px, e2 := parseHexTokenCompact(p)
				if e2 != nil {
					return fmt.Errorf("invalid BLIX macro %q: %w", p, e2)
				}
				macros = append(macros, px)
			}
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
			sub, e2 := readSimpleSym(br, macros)
			if e2 != nil {
				return e2
			}
			cnt, e3 := binary.ReadUvarint(br)
			if e3 != nil {
				return e3
			}
			if err := clixCheckRepeat(cnt, width*height-len(pixels)); err != nil {
				return err
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
			if err := clixCheckSeq(L, N, width*height-len(pixels)); err != nil {
				return err
			}
			steps := make([]simpleSym, L)
			for i := uint64(0); i < L; i++ {
				sym, e4 := readSimpleSym(br, macros)
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
			sym, e2 := readSimpleSymFromOp(op, br, macros)
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

const (
	trixDefaultBlockDim = 8
	trixMethodBLX       = 0
	trixMethodDCT       = 1
)

type trixBlockChoice int

const (
	trixChoiceTest trixBlockChoice = iota
	trixChoiceBLX
	trixChoiceDCT
)

type trixStats struct {
	blocks    int
	blx       int
	dct       int
	blxBytes  int
	dctBytes  int
	abTests   int
	skipTests int
}

func trixApplyImageSettings(src image.Image, st encodeSettings) (*image.NRGBA, error) {
	return applyImageModeSettings(imageToNRGBA(src), st)
}

func trixWriteBLXTokens(w io.Writer, tokens []string, macros map[string]byte) error {
	for _, t := range tokens {
		if strings.HasPrefix(t, "(") {
			in, cnt, e := blxParseGroup(t)
			if e != nil {
				return e
			}
			if err := blxWriteSeq(w, in, cnt, macros); err != nil {
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
			if err := blxWriteRepeat(w, base, n, macros); err != nil {
				return err
			}
			continue
		}
		if err := blxWriteSimpleToken(w, t, macros); err != nil {
			return err
		}
	}
	return nil
}

func trixBuildBLXBlockTokens(pixels []RGBA, st encodeSettings) []string {
	tokens := make([]string, 0, len(pixels))
	var prev *RGBA
	for _, px := range pixels {
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
	if st.enableTokenRLE {
		tokens = rleTokens(tokens)
	}
	if st.enableSequenceRLE {
		tokens = sequenceRLE(tokens, st.sequenceRLEMaxSeqLen)
	}
	return tokens
}

func uvarintLen(x uint64) int {
	var tmp [10]byte
	return binary.PutUvarint(tmp[:], x)
}

func trixBLXSimpleTokenSize(tok string, macroHexToIndex map[string]byte) (int, error) {
	if tok == "BG" || tok == "S" {
		return 1, nil
	}
	if _, ok := blxPureIndex[tok]; ok {
		return 1, nil
	}
	hex, err := blxLiteralHex(tok)
	if err != nil {
		return 0, err
	}
	if len(macroHexToIndex) > 0 {
		if idx, ok := macroHexToIndex[hex]; ok {
			return 1 + uvarintLen(uint64(idx)), nil
		}
	}
	return 5, nil
}

func trixMeasureBLXTokens(tokens []string, macros []RGBA, macroHexToIndex map[string]byte) (int, error) {
	size := uvarintLen(uint64(len(macros))) + len(macros)*4
	for _, t := range tokens {
		if strings.HasPrefix(t, "(") {
			in, cnt, err := blxParseGroup(t)
			if err != nil {
				return 0, err
			}
			size += 1 + uvarintLen(uint64(len(in))) + uvarintLen(uint64(cnt))
			for _, inner := range in {
				n, err := trixBLXSimpleTokenSize(inner, macroHexToIndex)
				if err != nil {
					return 0, err
				}
				size += n
			}
			continue
		}
		if strings.Contains(t, "*") {
			i := strings.LastIndexByte(t, '*')
			base := t[:i]
			cntStr := t[i+1:]
			if !isAllDigits(cntStr) {
				return 0, fmt.Errorf("bad repeat: %q", t)
			}
			n, _ := strconv.Atoi(cntStr)
			baseSize, err := trixBLXSimpleTokenSize(base, macroHexToIndex)
			if err != nil {
				return 0, err
			}
			size += 1 + baseSize + uvarintLen(uint64(n))
			continue
		}
		n, err := trixBLXSimpleTokenSize(t, macroHexToIndex)
		if err != nil {
			return 0, err
		}
		size += n
	}
	return size, nil
}

func trixPrepareBLXBlock(pixels []RGBA, st encodeSettings) ([]string, []RGBA, map[string]byte, int, error) {
	tokens := trixBuildBLXBlockTokens(pixels, st)
	macros, macroMap, err := blxBuildMacros(tokens)
	if err != nil {
		return nil, nil, nil, 0, err
	}
	payloadLen, err := trixMeasureBLXTokens(tokens, macros, macroMap)
	if err != nil {
		return nil, nil, nil, 0, err
	}
	return tokens, macros, macroMap, payloadLen, nil
}

func trixEncodePreparedBLXBlock(tokens []string, macros []RGBA, macroMap map[string]byte) ([]byte, error) {
	var buf bytes.Buffer
	if err := writeUvarint(&buf, uint64(len(macros))); err != nil {
		return nil, err
	}
	for _, px := range macros {
		buf.Write([]byte{px.R, px.G, px.B, px.A})
	}
	if err := trixWriteBLXTokens(&buf, tokens, macroMap); err != nil {
		return nil, err
	}
	return buf.Bytes(), nil
}

func trixEncodeBLXBlock(pixels []RGBA, st encodeSettings) ([]byte, error) {
	tokens, macros, macroMap, _, err := trixPrepareBLXBlock(pixels, st)
	if err != nil {
		return nil, err
	}
	return trixEncodePreparedBLXBlock(tokens, macros, macroMap)
}

func trixBlockPlanes(pixels []RGBA, w, h int) ([]float64, []float64, []float64, []float64, bool) {
	yPlane := make([]float64, w*h)
	cbPlane := make([]float64, w*h)
	crPlane := make([]float64, w*h)
	aPlane := make([]float64, w*h)
	hasAlpha := false
	for i, px := range pixels {
		yy, cb, cr := color.RGBToYCbCr(px.R, px.G, px.B)
		yPlane[i] = float64(yy)
		cbPlane[i] = float64(cb)
		crPlane[i] = float64(cr)
		aPlane[i] = float64(px.A)
		if px.A != 255 {
			hasAlpha = true
		}
	}
	return yPlane, cbPlane, crPlane, aPlane, hasAlpha
}

func trixEncodeDCTBlock(pixels []RGBA, w, h int, qY, qC [64]int) ([]byte, error) {
	yPlane, cbPlane, crPlane, aPlane, hasAlpha := trixBlockPlanes(pixels, w, h)
	var bits bitWriter
	if err := encodePlaneDCTRiceEx(&bits, yPlane, w, h, qY, true, vlxDctRiceK, true, true, true, true); err != nil {
		return nil, err
	}
	if err := encodePlaneDCTRiceEx(&bits, cbPlane, w, h, qC, true, vlxDctRiceK, true, true, true, true); err != nil {
		return nil, err
	}
	if err := encodePlaneDCTRiceEx(&bits, crPlane, w, h, qC, true, vlxDctRiceK, true, true, true, true); err != nil {
		return nil, err
	}
	mask := byte(0x7)
	if hasAlpha {
		mask |= 0x8
		if err := encodePlaneDCTRiceEx(&bits, aPlane, w, h, qY, true, vlxDctRiceK, true, true, true, true); err != nil {
			return nil, err
		}
	}
	payload := []byte{mask}
	payload = append(payload, bits.Bytes()...)
	return payload, nil
}

func trixRecordSize(payloadLen int) int {
	var tmp [10]byte
	return 1 + binary.PutUvarint(tmp[:], uint64(payloadLen)) + payloadLen
}

func trixBlockPixels(img *image.NRGBA, x0, y0, w, h int) []RGBA {
	pixels := make([]RGBA, 0, w*h)
	for y := 0; y < h; y++ {
		row := img.PixOffset(x0, y0+y)
		for x := 0; x < w; x++ {
			off := row + x*4
			pixels = append(pixels, RGBA{img.Pix[off], img.Pix[off+1], img.Pix[off+2], img.Pix[off+3]})
		}
	}
	return pixels
}

func trixPredictBlockChoice(pixels []RGBA, w, h int) trixBlockChoice {
	count := len(pixels)
	if count == 0 {
		return trixChoiceTest
	}

	var keys [64]uint32
	var keyCounts [64]int
	var keyStack [64]uint32
	var yStack [64]uint8
	keyVals := keyStack[:]
	yVals := yStack[:]
	if count > len(keyVals) {
		keyVals = make([]uint32, count)
	} else {
		keyVals = keyVals[:count]
	}
	if count > len(yVals) {
		yVals = make([]uint8, count)
	} else {
		yVals = yVals[:count]
	}

	unique := 0
	maxCount := 0
	sameRuns := 0
	sumY := 0.0
	sumY2 := 0.0
	var prevKey uint32
	for i, px := range pixels {
		key := uint32(px.R)<<24 | uint32(px.G)<<16 | uint32(px.B)<<8 | uint32(px.A)
		keyVals[i] = key
		found := -1
		for j := 0; j < unique; j++ {
			if keys[j] == key {
				found = j
				break
			}
		}
		if found < 0 {
			if unique < len(keys) {
				keys[unique] = key
				keyCounts[unique] = 1
			}
			found = unique
			unique++
		} else {
			keyCounts[found]++
		}
		if found < len(keyCounts) && keyCounts[found] > maxCount {
			maxCount = keyCounts[found]
		}
		if i > 0 && key == prevKey {
			sameRuns++
		}
		prevKey = key

		yy, _, _ := color.RGBToYCbCr(px.R, px.G, px.B)
		yVals[i] = yy
		fy := float64(yy)
		sumY += fy
		sumY2 += fy * fy
	}

	edgeSum := 0
	edgeCount := 0
	horizontalTransitions := 0
	repeatedRows := 0
	rowPatternChanges := 0
	for y := 0; y < h; y++ {
		row := y * w
		if y > 0 {
			prevRow := row - w
			rowSame := true
			for x := 0; x < w; x++ {
				if keyVals[row+x] != keyVals[prevRow+x] {
					rowSame = false
					break
				}
			}
			if rowSame {
				repeatedRows++
			} else {
				rowPatternChanges++
			}
		}
		for x := 0; x < w; x++ {
			idx := row + x
			if x > 0 {
				if keyVals[idx] != keyVals[idx-1] {
					horizontalTransitions++
				}
				edgeSum += absInt(int(yVals[idx]) - int(yVals[idx-1]))
				edgeCount++
			}
			if y > 0 {
				edgeSum += absInt(int(yVals[idx]) - int(yVals[idx-w]))
				edgeCount++
			}
		}
	}

	n := float64(count)
	meanY := sumY / n
	varY := sumY2/n - meanY*meanY
	avgEdge := 0.0
	if edgeCount > 0 {
		avgEdge = float64(edgeSum) / float64(edgeCount)
	}
	dominantFrac := float64(maxCount) / n
	repeatFrac := 0.0
	if count > 1 {
		repeatFrac = float64(sameRuns) / float64(count-1)
	}

	strongSmallPaletteStructure := dominantFrac >= 0.88 ||
		repeatFrac >= 0.60 ||
		horizontalTransitions <= 16 ||
		repeatedRows >= 3
	strongIndexedStructure := repeatFrac >= 0.60 &&
		horizontalTransitions <= 16 &&
		rowPatternChanges <= 2

	if unique <= 4 && strongSmallPaletteStructure {
		return trixChoiceBLX
	}
	if unique <= 12 && strongIndexedStructure {
		return trixChoiceBLX
	}
	if unique >= 60 && dominantFrac <= 0.12 {
		return trixChoiceDCT
	}
	if unique >= 52 && dominantFrac <= 0.18 && (avgEdge >= 36.0 || varY >= 650.0) {
		return trixChoiceDCT
	}
	if unique >= 44 && dominantFrac <= 0.20 && avgEdge <= 14.0 && varY >= 100.0 {
		return trixChoiceDCT
	}
	return trixChoiceTest
}

func encodeTRIX(imagePath, trixPath string, st encodeSettings, ffmpegPath string, dctQuality int, forceAB bool) (trixStats, error) {
	var stats trixStats
	src, err := decodeImageFile(imagePath, ffmpegPath)
	if err != nil {
		return stats, err
	}
	img, err := trixApplyImageSettings(src, st)
	if err != nil {
		return stats, err
	}
	b := img.Bounds()
	width, height := b.Dx(), b.Dy()
	blockDim := trixDefaultBlockDim
	qY := scaleQuantTable(jpegLumaQuant, dctQuality)
	qC := scaleQuantTable(jpegChromaQuant, dctQuality)
	out, err := os.Create(trixPath)
	if err != nil {
		return stats, err
	}
	defer out.Close()
	level := clampInt(st.zstdLevel, 1, 22)
	enc, err := newZstdWriter(out, level)
	if err != nil {
		return stats, err
	}
	bw := bufio.NewWriter(enc)
	if _, err := fmt.Fprintf(bw, "TRIX %s\nWIDTH=%d\nHEIGHT=%d\nBLOCK=%d\nDCT_QUALITY=%d\nZSTD_LEVEL=%d\n\n", trixVersion, width, height, blockDim, dctQuality, level); err != nil {
		return stats, err
	}
	numBlocks := ((width + blockDim - 1) / blockDim) * ((height + blockDim - 1) / blockDim)
	methods := make([]byte, 0, numBlocks)
	payloads := make([][]byte, 0, numBlocks)
	for by := 0; by < height; by += blockDim {
		bh := blockDim
		if by+bh > height {
			bh = height - by
		}
		for bx := 0; bx < width; bx += blockDim {
			bwBlock := blockDim
			if bx+bwBlock > width {
				bwBlock = width - bx
			}
			pixels := trixBlockPixels(img, bx, by, bwBlock, bh)
			method := byte(trixMethodBLX)
			var payload []byte
			choice := trixPredictBlockChoice(pixels, bwBlock, bh)
			if forceAB {
				choice = trixChoiceTest
			}
			switch choice {
			case trixChoiceBLX:
				payload, err = trixEncodeBLXBlock(pixels, st)
				if err != nil {
					return stats, err
				}
				stats.skipTests++
				stats.blx++
				stats.blxBytes += trixRecordSize(len(payload))
			case trixChoiceDCT:
				method = trixMethodDCT
				payload, err = trixEncodeDCTBlock(pixels, bwBlock, bh, qY, qC)
				if err != nil {
					return stats, err
				}
				stats.skipTests++
				stats.dct++
				stats.dctBytes += trixRecordSize(len(payload))
			default:
				dctPayload, err := trixEncodeDCTBlock(pixels, bwBlock, bh, qY, qC)
				if err != nil {
					return stats, err
				}
				blxTokens, blxMacros, blxMacroMap, blxPayloadLen, err := trixPrepareBLXBlock(pixels, st)
				if err != nil {
					return stats, err
				}
				dctRecordSize := trixRecordSize(len(dctPayload))
				blxRecordSize := trixRecordSize(blxPayloadLen)
				if dctRecordSize < blxRecordSize {
					method = trixMethodDCT
					payload = dctPayload
					stats.dct++
					stats.dctBytes += dctRecordSize
					stats.skipTests++
				} else {
					blxPayload, err := trixEncodePreparedBLXBlock(blxTokens, blxMacros, blxMacroMap)
					if err != nil {
						return stats, err
					}
					payload = blxPayload
					stats.blx++
					stats.blxBytes += trixRecordSize(len(blxPayload))
					stats.abTests++
				}
			}
			stats.blocks++
			methods = append(methods, method)
			payloads = append(payloads, payload)
		}
	}
	for _, m := range methods {
		if err := bw.WriteByte(m); err != nil {
			return stats, err
		}
	}
	for _, p := range payloads {
		if err := writeUvarint(bw, uint64(len(p))); err != nil {
			return stats, err
		}
	}
	for _, p := range payloads {
		if _, err := bw.Write(p); err != nil {
			return stats, err
		}
	}
	if err := bw.Flush(); err != nil {
		return stats, err
	}
	if err := enc.Close(); err != nil {
		return stats, err
	}
	return stats, out.Sync()
}

func trixDecodeBLXBlock(payload []byte, count int) ([]RGBA, error) {
	br := bufio.NewReader(bytes.NewReader(payload))
	macroCount, err := binary.ReadUvarint(br)
	if err != nil {
		return nil, err
	}
	if macroCount > blxMacroMaxEntries {
		return nil, fmt.Errorf("TRIX BLX macro count %d exceeds max %d", macroCount, blxMacroMaxEntries)
	}
	macros := make([]RGBA, int(macroCount))
	for i := range macros {
		var b [4]byte
		if _, err := io.ReadFull(br, b[:]); err != nil {
			return nil, err
		}
		macros[i] = RGBA{b[0], b[1], b[2], b[3]}
	}
	pixels := make([]RGBA, 0, count)
	var prev *RGBA
	for len(pixels) < count {
		op, err := br.ReadByte()
		if err != nil {
			return nil, err
		}
		switch op {
		case opRepeat:
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
		case opSeq:
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

func trixDecodeDCTBlock(payload []byte, w, h int, qY, qC [64]int) ([]RGBA, error) {
	if len(payload) == 0 {
		return nil, errors.New("empty TRIX DCT block")
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
	pixels := make([]RGBA, w*h)
	for i := range pixels {
		yy := clampToByte(yPlane[i])
		cb := clampToByte(cbPlane[i])
		cr := clampToByte(crPlane[i])
		rr, gg, bb := color.YCbCrToRGB(yy, cb, cr)
		pixels[i] = RGBA{rr, gg, bb, clampToByte(aPlane[i])}
	}
	return pixels, nil
}

func decodeTRIXToImage(path string) (*image.NRGBA, []byte, int, error) {
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
				dctQuality = clampInt(v, 1, 100)
			}
		}
	}
	if width <= 0 || height <= 0 {
		return nil, nil, 0, errors.New("invalid TRIX header (WIDTH/HEIGHT)")
	}
	out := image.NewNRGBA(image.Rect(0, 0, width, height))
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
			bwBlock := blockDim
			if bx+bwBlock > width {
				bwBlock = width - bx
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
			var pixels []RGBA
			var err error
			switch method {
			case trixMethodBLX:
				pixels, err = trixDecodeBLXBlock(payload, bwBlock*bh)
			case trixMethodDCT:
				pixels, err = trixDecodeDCTBlock(payload, bwBlock, bh, qY, qC)
			default:
				err = fmt.Errorf("unknown TRIX block method 0x%X", method)
			}
			if err != nil {
				return nil, nil, 0, err
			}
			methods = append(methods, method)
			i := 0
			for y := 0; y < bh; y++ {
				for x := 0; x < bwBlock; x++ {
					px := pixels[i]
					off := out.PixOffset(bx+x, by+y)
					out.Pix[off+0] = px.R
					out.Pix[off+1] = px.G
					out.Pix[off+2] = px.B
					out.Pix[off+3] = px.A
					i++
				}
			}
		}
	}
	return out, methods, blockDim, nil
}

func decodeTRIX(path, outputPNG string) error {
	img, _, _, err := decodeTRIXToImage(path)
	if err != nil {
		return err
	}
	f, err := os.Create(outputPNG)
	if err != nil {
		return err
	}
	defer f.Close()
	return png.Encode(f, img)
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
	var keyInterval int
	var bframes int
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
		case "KEY_INTERVAL":
			if v, err := strconv.Atoi(val); err == nil && v > 0 {
				keyInterval = v
			}
		case "BFRAMES":
			if v, err := strconv.Atoi(val); err == nil && v >= 0 {
				bframes = v
			}
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
		return decodeVLIX2(br, outDir, width, height, framesExpected, keyInterval, bframes, audioBytes, chromaMode, dctQuality, dctResQuality, blockDim, alphaEnabled, dctPred, dctZeroRun, dctBlockSkip, dctAcMag, dctPlaneMask, dctRiceK, dctResRiceK, mvRiceK)
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
						if !allowTemporal {
							return nil, errors.New("motion block in keyframe")
						}
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
								if err := clixCheckRepeat(cnt, ww*hh-len(blockPixels)); err != nil {
									return nil, err
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
								if err := clixCheckSeq(L, N, ww*hh-len(blockPixels)); err != nil {
									return nil, err
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
					if err := clixCheckRepeat(cnt, width*height-len(pixels)); err != nil {
						return nil, err
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
					if err := clixCheckSeq(L, N, width*height-len(pixels)); err != nil {
						return nil, err
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

func decodeVLIX2(br *bufio.Reader, outDir string, width, height, framesExpected, keyInterval, bframes, audioBytes int, chromaMode string, dctQuality, dctResQuality int, blockDim int, alphaEnabled, dctPred, dctZeroRun, dctBlockSkip, dctAcMag, dctPlaneMask bool, dctRiceK, dctResRiceK, mvRiceK int) ([]byte, error) {
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
	maxFrameBytes := uint64(64)*uint64(width)*uint64(height) + (1 << 16)
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
	var refUses map[int]int
	if framesExpected > 0 && keyInterval > 0 {
		plans, coding := buildVLIX2Plan(framesExpected, keyInterval, bframes)
		refUses = buildVLIX2RefUseCounts(plans, coding)
	}
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
		switch frameType {
		case vlxFrameDelta:
			consumeVLIX2Ref(refUses, refPrevIdx, refPlanes)
		case vlxFrameB:
			consumeVLIX2Ref(refUses, refPrevIdx, refPlanes)
			if refNextIdx != refPrevIdx {
				consumeVLIX2Ref(refUses, refNextIdx, refPlanes)
			}
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
					if name[0] != 'M' || !isAllHex(hex) {
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
	total := width * height
	pixels := make([]RGBA, total)
	filled := make([]bool, total)
	var prev *RGBA
	cursor := 0
	resolvePixel := func(base string) (RGBA, error) {
		if base == "S" {
			if prev == nil {
				return RGBA{}, errors.New("encountered 'S' before any previous pixel")
			}
			return *prev, nil
		}
		if pxm, ok := macros[base]; ok {
			return pxm, nil
		}
		px, err := tokenToRGBA(base, bg, prev)
		if err != nil {
			return RGBA{}, err
		}
		return px, nil
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
	for ti, base := range expanded {
		spec, isShape, serr := parseShape(base)
		if serr != nil {
			return fmt.Errorf("bad shape token at index %d: %q (%v)", ti, base, serr)
		}
		if isShape {
			if spec.x < 0 || spec.y < 0 || spec.x+spec.w > width || spec.y+spec.h > height {
				return fmt.Errorf("shape out of bounds at index %d: %q for image %dx%d", ti, base, width, height)
			}
			px, err := resolvePixel(spec.fill)
			if err != nil {
				return fmt.Errorf("bad shape fill token at index %d: %q (%v)", ti, spec.fill, err)
			}
			for y := 0; y < spec.h; y++ {
				rowOff := (spec.y + y) * width
				for x := 0; x < spec.w; x++ {
					write := false
					switch spec.kind {
					case 'R':
						write = true
					case 'C':
						write = clixEllipseContains(x, y, spec.w, spec.h)
					case 'T':
						write = clixTriangleContains(x, y, spec.w, spec.h, spec.o)
					}
					if write {
						idx := rowOff + (spec.x + x)
						pixels[idx] = px
						filled[idx] = true
					}
				}
			}
			tmp := px
			prev = &tmp
			continue
		}
		if cursor >= total {
			return fmt.Errorf("decoded pixel count mismatch: got more than %d pixels", total)
		}
		px, err := resolvePixel(base)
		if err != nil {
			return err
		}
		pixels[cursor] = px
		filled[cursor] = true
		cursor++
		tmp := px
		prev = &tmp
	}
	for idx, ok := range filled {
		if !ok {
			x := idx % width
			y := idx / width
			return fmt.Errorf("decoded pixel map incomplete: missing pixel at (%d,%d)", x, y)
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

func isImageFile(path string) bool {
	f, err := os.Open(path)
	if err != nil {
		return false
	}
	defer f.Close()
	_, _, err = image.DecodeConfig(f)
	return err == nil
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
	case ext == ".clix" || ext == ".blix" || ext == ".trix":
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
		if !probe.hasAudio && isImageFile(path) {
			return jobImageEncode, true
		}
		isStill := !probe.hasAudio && (probe.videoFrames == 1 || probe.duration == 0 || probe.avgRate == 0)
		if isStill {
			return jobImageEncode, true
		}
		return jobVideoEncode, false
	}
	if probe.hasAudio {
		return jobAudioEncode, false
	}
	if isImageFile(path) {
		return jobImageEncode, true
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

func encodeALIXBlockRaw(pcm []byte, channels, blockFrames int) ([]byte, error) {
	if channels <= 0 {
		return nil, errors.New("invalid channels")
	}
	if blockFrames <= 0 {
		return nil, errors.New("invalid ALIX block size")
	}
	frameSize := 2 * channels
	if len(pcm)%frameSize != 0 {
		return nil, errors.New("pcm buffer not aligned to frame size")
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
					return nil, err
				}
			}
		}
	}
	return raw.Bytes(), nil
}

func encodeALIXVarintRaw(pcm []byte, channels int) ([]byte, error) {
	if channels <= 0 {
		return nil, errors.New("invalid channels")
	}
	frameSize := 2 * channels
	if len(pcm)%frameSize != 0 {
		return nil, errors.New("pcm buffer not aligned to frame size")
	}
	frames := len(pcm) / frameSize
	prev := make([]int16, channels)
	var raw bytes.Buffer
	var varintBuf [binary.MaxVarintLen32]byte
	for i := 0; i < frames; i++ {
		for ch := 0; ch < channels; ch++ {
			off := (i*channels + ch) * 2
			sample := int16(binary.LittleEndian.Uint16(pcm[off:]))
			delta := int32(sample) - int32(prev[ch])
			prev[ch] = sample
			zigzag := uint32((delta << 1) ^ (delta >> 31))
			n := binary.PutUvarint(varintBuf[:], uint64(zigzag))
			if _, err := raw.Write(varintBuf[:n]); err != nil {
				return nil, err
			}
		}
	}
	return raw.Bytes(), nil
}

const (
	alix2DefaultBlock = 4096
	alix2MaxOrder     = 3
	alix2MaxK         = 30
)

func alix2ZigZag(v int32) uint32 { return uint32((v << 1) ^ (v >> 31)) }

// for the series x. Samples before index 0 are treated as zero so each block is
func alix2FixedResidual(x []int32, order int, dst []int32) {
	get := func(j int) int32 {
		if j < 0 {
			return 0
		}
		return x[j]
	}
	for i := range x {
		var pred int32
		switch order {
		case 1:
			pred = get(i - 1)
		case 2:
			pred = 2*get(i-1) - get(i-2)
		case 3:
			pred = 3*get(i-1) - 3*get(i-2) + get(i-3)
		}
		dst[i] = x[i] - pred
	}
}

func alix2RiceCost(res []int32, k uint8) int {
	cost := 0
	for _, v := range res {
		cost += int(alix2ZigZag(v)>>k) + 1 + int(k)
	}
	return cost
}

func alix2BestK(res []int32) (uint8, int) {
	if len(res) == 0 {
		return 0, 0
	}
	var sumU uint64
	for _, v := range res {
		sumU += uint64(alix2ZigZag(v))
	}
	mean := sumU / uint64(len(res))
	k0 := 0
	for k0 < alix2MaxK && uint64(1)<<uint(k0+1) <= mean+1 {
		k0++
	}
	lo := k0 - 1
	if lo < 0 {
		lo = 0
	}
	hi := k0 + 1
	if hi > alix2MaxK {
		hi = alix2MaxK
	}
	bestK := uint8(lo)
	bestCost := -1
	for k := lo; k <= hi; k++ {
		c := alix2RiceCost(res, uint8(k))
		if bestCost < 0 || c < bestCost {
			bestCost = c
			bestK = uint8(k)
		}
	}
	return bestK, bestCost
}

type alix2ChannelPlan struct {
	order int
	k     uint8
	res   []int32
	cost  int
}

func alix2PlanChannel(x []int32, scratch []int32) alix2ChannelPlan {
	bestOrder := 0
	bestSum := uint64(math.MaxUint64)
	for order := 0; order <= alix2MaxOrder; order++ {
		alix2FixedResidual(x, order, scratch[:len(x)])
		var sum uint64
		for _, v := range scratch[:len(x)] {
			sum += uint64(alix2ZigZag(v))
		}
		if sum < bestSum {
			bestSum = sum
			bestOrder = order
		}
	}
	res := make([]int32, len(x))
	alix2FixedResidual(x, bestOrder, res)
	k, cost := alix2BestK(res)
	return alix2ChannelPlan{order: bestOrder, k: k, res: res, cost: cost}
}

func alix2EmitChannel(w *bitWriter, p alix2ChannelPlan) {
	w.WriteBits(uint64(p.order), 2)
	w.WriteBits(uint64(p.k), 5)
	for _, v := range p.res {
		writeRiceSigned(w, int(v), p.k)
	}
}

func encodeALIX2Raw(pcm []byte, channels, blockFrames int) ([]byte, error) {
	if channels <= 0 {
		return nil, errors.New("invalid channels")
	}
	if blockFrames <= 0 {
		return nil, errors.New("invalid ALIX2 block size")
	}
	frameSize := 2 * channels
	if len(pcm)%frameSize != 0 {
		return nil, errors.New("pcm buffer not aligned to frame size")
	}
	frames := len(pcm) / frameSize
	var w bitWriter
	series := make([][]int32, channels)
	for c := range series {
		series[c] = make([]int32, blockFrames)
	}
	scratch := make([]int32, blockFrames)
	sampleAt := func(frame, ch int) int32 {
		off := (frame*channels + ch) * 2
		return int32(int16(binary.LittleEndian.Uint16(pcm[off:])))
	}
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
			w.WriteBit(1)
			continue
		}
		w.WriteBit(0)
		for c := 0; c < channels; c++ {
			s := series[c][:n]
			for i := 0; i < n; i++ {
				s[i] = sampleAt(base+i, c)
			}
		}
		if channels == 2 {
			l := series[0][:n]
			r := series[1][:n]
			planL := alix2PlanChannel(l, scratch)
			planR := alix2PlanChannel(r, scratch)
			mid := make([]int32, n)
			side := make([]int32, n)
			for i := 0; i < n; i++ {
				mid[i] = (l[i] + r[i]) >> 1
				side[i] = l[i] - r[i]
			}
			planM := alix2PlanChannel(mid, scratch)
			planS := alix2PlanChannel(side, scratch)
			if planM.cost+planS.cost < planL.cost+planR.cost {
				w.WriteBit(1)
				alix2EmitChannel(&w, planM)
				alix2EmitChannel(&w, planS)
			} else {
				w.WriteBit(0)
				alix2EmitChannel(&w, planL)
				alix2EmitChannel(&w, planR)
			}
		} else {
			for c := 0; c < channels; c++ {
				plan := alix2PlanChannel(series[c][:n], scratch)
				alix2EmitChannel(&w, plan)
			}
		}
	}
	return w.Bytes(), nil
}

func compressALIXRaw(raw []byte, level int) ([]byte, error) {
	var payload bytes.Buffer
	enc, err := newZstdWriter(&payload, level)
	if err != nil {
		return nil, err
	}
	if _, err := enc.Write(raw); err != nil {
		enc.Close()
		return nil, err
	}
	if err := enc.Close(); err != nil {
		return nil, err
	}
	return payload.Bytes(), nil
}

func encodeALIXFromPCM(pcm []byte, sampleRate, channels, zstdLevel, blockFrames int) ([]byte, int, error) {
	if channels <= 0 {
		return nil, 0, errors.New("invalid channels")
	}
	if sampleRate <= 0 {
		return nil, 0, errors.New("invalid sample rate")
	}
	frameSize := 2 * channels
	if len(pcm)%frameSize != 0 {
		return nil, 0, errors.New("pcm buffer not aligned to frame size")
	}
	frames := len(pcm) / frameSize
	level := clampInt(zstdLevel, 1, 22)

	const (
		candKindALIX  = 0
		candKindALIX2 = 1
		candKindDPCM  = 2
	)
	type candidateSpec struct {
		codec string
		kind  int
		block int
	}
	var specs []candidateSpec
	alixBlocks := []int{256, 512, alixBlockFrames, 2048}
	alix2Blocks := []int{1024, alix2DefaultBlock}
	if blockFrames > 0 {
		alixBlocks = []int{blockFrames}
		alix2Blocks = []int{blockFrames}
	}
	seenALIX := make(map[int]struct{}, len(alixBlocks))
	for _, b := range alixBlocks {
		if b <= 0 {
			continue
		}
		if _, ok := seenALIX[b]; ok {
			continue
		}
		seenALIX[b] = struct{}{}
		specs = append(specs, candidateSpec{codec: alixCodec, kind: candKindALIX, block: b})
	}
	seenALIX2 := make(map[int]struct{}, len(alix2Blocks))
	for _, b := range alix2Blocks {
		if b <= 0 {
			continue
		}
		if _, ok := seenALIX2[b]; ok {
			continue
		}
		seenALIX2[b] = struct{}{}
		specs = append(specs, candidateSpec{codec: alix2Codec, kind: candKindALIX2, block: b})
	}
	specs = append(specs, candidateSpec{codec: "DPCM16", kind: candKindDPCM, block: 0})

	compressed := make([][]byte, len(specs))
	errsList := make([]error, len(specs))
	var wg sync.WaitGroup
	for i := range specs {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			s := specs[i]
			var raw []byte
			var err error
			switch s.kind {
			case candKindALIX:
				raw, err = encodeALIXBlockRaw(pcm, channels, s.block)
			case candKindALIX2:
				raw, err = encodeALIX2Raw(pcm, channels, s.block)
			case candKindDPCM:
				raw, err = encodeALIXVarintRaw(pcm, channels)
			}
			if err != nil {
				errsList[i] = err
				return
			}
			compressed[i], errsList[i] = compressALIXRaw(raw, level)
		}(i)
	}
	wg.Wait()

	bestCodec := ""
	bestBlock := 0
	var bestPayload []byte
	best := -1
	for i := range specs {
		if errsList[i] != nil {
			return nil, 0, errsList[i]
		}
		if best < 0 || len(compressed[i]) < len(compressed[best]) {
			best = i
		}
	}
	if best < 0 {
		return nil, 0, errors.New("failed to encode ALIX payload")
	}
	bestCodec = specs[best].codec
	bestBlock = specs[best].block
	bestPayload = compressed[best]
	if len(bestPayload) == 0 || bestCodec == "" {
		return nil, 0, errors.New("failed to encode ALIX payload")
	}

	var out bytes.Buffer
	header := []string{
		"ALIX " + alixVersion,
		"ENCODER=" + encoderVersion,
		fmt.Sprintf("SR=%d", sampleRate),
		fmt.Sprintf("CH=%d", channels),
		fmt.Sprintf("SAMPLES=%d", frames),
		"CODEC=" + bestCodec,
		fmt.Sprintf("ZSTD_LEVEL=%d", level),
	}
	if (bestCodec == alixCodec || bestCodec == alix2Codec) && bestBlock > 0 {
		header = append(header, fmt.Sprintf("BLOCK=%d", bestBlock))
	}
	for _, line := range header {
		out.WriteString(line)
		out.WriteString("\n")
	}
	out.WriteString("\n")
	if _, err := out.Write(bestPayload); err != nil {
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

func decodeALIXToPCM(container []byte) (pcm []byte, sampleRate, channels int, err error) {
	data, err := decodeALIXContainer(container)
	if err != nil {
		return nil, 0, 0, err
	}
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
	if !strings.HasPrefix(h1, "ALIX") && !strings.HasPrefix(h1, "VLA") && !strings.HasPrefix(h1, "CLXA") {
		return nil, 0, 0, fmt.Errorf("not an ALIX stream: %q", h1)
	}
	var samples int
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
		parts := strings.SplitN(line, "=", 2)
		if len(parts) != 2 {
			continue
		}
		key, val := strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1])
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
			if v, e := strconv.Atoi(val); e == nil && v > 0 {
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
	out := make([]int16, 0, total)
	r := bytes.NewReader(raw)
	clampS16 := func(v int32) int16 {
		if v > 32767 {
			return 32767
		}
		if v < -32768 {
			return -32768
		}
		return int16(v)
	}
	switch {
	case codec == "" || codec == "DPCM16":
		for i := 0; i < samples; i++ {
			for ch := 0; ch < channels; ch++ {
				u, e := binary.ReadUvarint(r)
				if e != nil {
					return nil, 0, 0, e
				}
				delta := int32(u>>1) ^ -int32(u&1)
				prev[ch] = clampS16(int32(prev[ch]) + delta)
				out = append(out, prev[ch])
			}
		}
	case codec == "ALIX" || codec == "CLXA":
		framesLeft := samples
		for framesLeft > 0 {
			n := blockFrames
			if n > framesLeft {
				n = framesLeft
			}
			op, e := r.ReadByte()
			if e != nil {
				return nil, 0, 0, e
			}
			switch op {
			case alixOpSilence:
				for i := 0; i < n*channels; i++ {
					out = append(out, 0)
				}
				for ch := range prev {
					prev[ch] = 0
				}
			case alixOpPCM:
				for i := 0; i < n; i++ {
					for ch := 0; ch < channels; ch++ {
						var b [2]byte
						if _, e := io.ReadFull(r, b[:]); e != nil {
							return nil, 0, 0, e
						}
						prev[ch] = int16(binary.LittleEndian.Uint16(b[:]))
						out = append(out, prev[ch])
					}
				}
			case alixOpD8:
				for i := 0; i < n; i++ {
					for ch := 0; ch < channels; ch++ {
						b, e := r.ReadByte()
						if e != nil {
							return nil, 0, 0, e
						}
						prev[ch] = int16(int32(prev[ch]) + int32(int8(b)))
						out = append(out, prev[ch])
					}
				}
			case alixOpD16:
				for i := 0; i < n; i++ {
					for ch := 0; ch < channels; ch++ {
						var b [2]byte
						if _, e := io.ReadFull(r, b[:]); e != nil {
							return nil, 0, 0, e
						}
						delta := int16(binary.LittleEndian.Uint16(b[:]))
						prev[ch] = int16(int32(prev[ch]) + int32(delta))
						out = append(out, prev[ch])
					}
				}
			default:
				return nil, 0, 0, fmt.Errorf("unknown ALIX op 0x%X", op)
			}
			framesLeft -= n
		}
	case codec == "ALIX2":
		br2 := newBitReader(raw)
		decodeSeries := func(n int) ([]int32, error) {
			ob, e := br2.ReadBits(2)
			if e != nil {
				return nil, e
			}
			kb, e := br2.ReadBits(5)
			if e != nil {
				return nil, e
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
				rv, e := readRiceSigned(br2, k)
				if e != nil {
					return nil, e
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
			silence, e := br2.ReadBit()
			if e != nil {
				return nil, 0, 0, e
			}
			if silence == 1 {
				for i := 0; i < n*channels; i++ {
					out = append(out, 0)
				}
				framesLeft -= n
				continue
			}
			if channels == 2 {
				decorr, e := br2.ReadBit()
				if e != nil {
					return nil, 0, 0, e
				}
				a, e := decodeSeries(n)
				if e != nil {
					return nil, 0, 0, e
				}
				b, e := decodeSeries(n)
				if e != nil {
					return nil, 0, 0, e
				}
				if decorr == 1 {
					for i := 0; i < n; i++ {
						mid, side := a[i], b[i]
						l := mid + ((side + (side & 1)) >> 1)
						out = append(out, clampS16(l), clampS16(l-side))
					}
				} else {
					for i := 0; i < n; i++ {
						out = append(out, clampS16(a[i]), clampS16(b[i]))
					}
				}
			} else {
				chSeries := make([][]int32, channels)
				for c := 0; c < channels; c++ {
					s, e := decodeSeries(n)
					if e != nil {
						return nil, 0, 0, e
					}
					chSeries[c] = s
				}
				for i := 0; i < n; i++ {
					for c := 0; c < channels; c++ {
						out = append(out, clampS16(chSeries[c][i]))
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
		for i := 0; i < expected; i += 2 {
			out = append(out, int16(binary.LittleEndian.Uint16(raw[i:i+2])))
		}
	default:
		return nil, 0, 0, fmt.Errorf("unsupported ALIX codec: %s", codec)
	}
	pcm = make([]byte, len(out)*2)
	for i, s := range out {
		binary.LittleEndian.PutUint16(pcm[i*2:], uint16(s))
	}
	return pcm, sampleRate, channels, nil
}

func writeWAV(path string, pcm []byte, sampleRate, channels int) error {
	f, err := os.Create(path)
	if err != nil {
		return err
	}
	defer f.Close()
	var hdr bytes.Buffer
	hdr.WriteString("RIFF")
	binary.Write(&hdr, binary.LittleEndian, uint32(36+len(pcm)))
	hdr.WriteString("WAVE")
	hdr.WriteString("fmt ")
	binary.Write(&hdr, binary.LittleEndian, uint32(16))
	binary.Write(&hdr, binary.LittleEndian, uint16(1))
	binary.Write(&hdr, binary.LittleEndian, uint16(channels))
	binary.Write(&hdr, binary.LittleEndian, uint32(sampleRate))
	binary.Write(&hdr, binary.LittleEndian, uint32(sampleRate*channels*2))
	binary.Write(&hdr, binary.LittleEndian, uint16(channels*2))
	binary.Write(&hdr, binary.LittleEndian, uint16(16))
	hdr.WriteString("data")
	binary.Write(&hdr, binary.LittleEndian, uint32(len(pcm)))
	if _, err := f.Write(hdr.Bytes()); err != nil {
		return err
	}
	_, err = f.Write(pcm)
	return err
}

func pcmToFLAC(ffmpegPath, outPath string, pcm []byte, sampleRate, channels int) error {
	cmd := exec.Command(ffmpegPath, "-v", "error", "-y",
		"-f", "s16le", "-ar", strconv.Itoa(sampleRate), "-ac", strconv.Itoa(channels),
		"-i", "-", "-c:a", "flac", outPath)
	cmd.Stdin = bytes.NewReader(pcm)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		msg := strings.TrimSpace(stderr.String())
		if msg == "" {
			msg = err.Error()
		}
		return fmt.Errorf("ffmpeg flac: %s", msg)
	}
	return nil
}

func framesToMP4(ffmpegPath, framesDir, outPath string, fps float64, audioWav string) error {
	if fps <= 0 {
		fps = 30
	}
	args := []string{"-v", "error", "-y",
		"-framerate", fmt.Sprintf("%g", fps),
		"-start_number", "0",
		"-i", filepath.Join(framesDir, "frame_%06d.png")}
	if audioWav != "" {
		args = append(args, "-i", audioWav)
	}
	args = append(args, "-c:v", "libx264", "-pix_fmt", "yuv420p", "-crf", "18")
	if audioWav != "" {
		args = append(args, "-c:a", "aac", "-b:a", "192k", "-shortest")
	}
	args = append(args, outPath)
	cmd := exec.Command(ffmpegPath, args...)
	var stderr bytes.Buffer
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		msg := strings.TrimSpace(stderr.String())
		if msg == "" {
			msg = err.Error()
		}
		return fmt.Errorf("ffmpeg mp4: %s", msg)
	}
	return nil
}

func vlixHeaderFPS(path string) float64 {
	f, err := os.Open(path)
	if err != nil {
		return 30
	}
	defer f.Close()
	zr, err := zstd.NewReader(f)
	if err != nil {
		return 30
	}
	defer zr.Close()
	br := bufio.NewReader(zr)
	fps := 0.0
	for {
		line, e := br.ReadString('\n')
		if e != nil {
			break
		}
		line = strings.TrimRight(line, "\r\n")
		if line == "" {
			break
		}
		if strings.HasPrefix(line, "FPS=") {
			fps, _ = strconv.ParseFloat(strings.TrimSpace(strings.TrimPrefix(line, "FPS=")), 64)
		}
	}
	if fps <= 0 {
		fps = 30
	}
	return fps
}

func buildEncodeSettings(
	base string,
	dither bool,
	palette int,
	blocksize int,
	blockvar float64,
	roundstep int,
	deltasnap int,
	shapes bool,
	zstdLevelFlag int,
	changed map[string]bool,
	fast bool,
) (encodeSettings, string, int) {
	if base != "lossless" && base != "unsafe" && base != "safe" && base != "experimental" {
		base = "safe"
	}
	var rs, ds, pal, blk int
	var dith bool
	defaultShapes := false
	blkVar := blockvar
	switch base {
	case "lossless":
		rs, ds, pal, blk, dith = 0, 0, 0, 0, false
	case "unsafe":
		rs, ds, pal, blk, dith = 3, 3, 64, 2, dither
	case "experimental":
		rs, ds, pal, blk, dith = 2, 2, 0, 0, false
		defaultShapes = true
	default:
		rs, ds, pal, blk, dith = 2, 2, 0, 0, false
		base = "safe"
	}
	shapesEnabled := shapes
	if !changed["shapes"] {
		shapesEnabled = defaultShapes
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
	if changed["shapes"] && shapesEnabled != defaultShapes {
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
		enableShapes:         shapesEnabled,
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

func resolveTrixDCTQuality(mode string, requested int, explicit bool) int {
	if explicit {
		return requested
	}
	switch mode {
	case "lossless":
		return 100
	case "unsafe":
		return 50
	default:
		return requested
	}
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
)

var (
	flagGroupGeneral = []string{"help", "version", "simd-backend", "compute", "binary", "fast", "zstd-level", "frames", "wav"}
	flagGroupImage   = []string{"preset", "dither", "palette", "blocksize", "blockvar", "roundstep", "deltasnap", "shapes", "trix", "trix-ab-test-all", "dct-quality"}
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
	base := []string{"help", "version", "simd-backend", "compute"}
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
		return flagSet(base, binary, []string{"frames"})
	case jobAudioEncode:
		return flagSet(base, commonEncode, binary, flagGroupAlix)
	case jobAudioConvert:
		return flagSet(base, binary, []string{"wav"})
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
	fmt.Fprintln(out, "  Images -> .clix/.blix/.trix")
	fmt.Fprintln(out, "  Video or frames dir -> .vlix")
	fmt.Fprintln(out, "  Audio -> .alix")
	fmt.Fprintln(out, "  Decode: .clix/.blix/.trix -> .png | .vlix -> .mp4 (--frames for PNGs) | .alix -> .flac (--wav for WAV)")
	fmt.Fprintln(out, "")
	fmt.Fprintln(out, "Flags by type:")
	printFlagGroup(out, "General", flagGroupGeneral)
	printFlagGroup(out, "Image Quality (CLIX/BLIX/VLIX)", flagGroupImage)
	printFlagGroup(out, "Video (VLIX)", flagGroupVlix)
	printFlagGroup(out, "Audio (ALIX)", flagGroupAlix)
	fmt.Fprintln(out, "Notes:")
	fmt.Fprintln(out, "  - Image quality flags apply to CLIX/BLIX/TRIX encoding and VLIX frame encoding.")
	fmt.Fprintln(out, "  - Audio flags apply to ALIX encoding and VLIX audio when present.")
	fmt.Fprintln(out, "  - Zstd output uses the largest window supported by the Go zstd backend for better long-range matches.")
	fmt.Fprintln(out, "  - --chroma defaults to 420 for VLIX to reduce size with minimal impact.")
	fmt.Fprintln(out, "  - --codec defaults to vlix2 (DCT-based, smaller, lossy); set --codec=vlix1 for legacy mode.")
	fmt.Fprintln(out, "  - --dct-quality/--dct-res-quality tune VLIX2 size vs quality (1-100).")
	fmt.Fprintln(out, "  - TRIX uses preset-aware DCT defaults unless --dct-quality is set: lossless=100, safe/experimental=75, unsafe=50.")
	fmt.Fprintln(out, "  - --bframes controls VLIX2 B-frames (0=off, higher=smaller/slower).")
	fmt.Fprintln(out, "  - Use --binary=true for smallest .alix/.blix output (avoids base64); add --trix for mixed block image encoding.")
	fmt.Fprintln(out, "  - --trix-ab-test-all disables TRIX block prediction and uses exact BLIX-vs-DCT choice for every block.")
	fmt.Fprintln(out, "  - --fast disables motion unless --motion is explicitly set.")
	fmt.Fprintln(out, "  - --audio-zstd defaults to --zstd-level capped at 10 unless overridden.")
	fmt.Fprintln(out, "  - --audio-block=0 auto-tests ALIX block sizes (256/512/1024/2048) for smaller output.")
	fmt.Fprintln(out, "  - --audio-rate defaults to 44100 when source is higher, unless overridden.")
	fmt.Fprintln(out, "  - --shapes defaults to false, except preset=experimental enables shapes by default.")
	fmt.Fprintln(out, "  - Set --motion-threshold=0 for lossless motion matching.")
	fmt.Fprintln(out, "  - --simd-backend prints the active VLIX2 IDCT backend (avx2/sse2/scalar).")
	fmt.Fprintln(out, "  - --compute selects numerical backend scaffold: auto|cpu|cuda|cuda-f32|vulkan.")
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
	return 0
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
	case "":
		return vlixCodecV2, nil
	case "vlix1":
		return vlixCodecV1, nil
	case "vlix2":
		return vlixCodecV2, nil
	default:
		return "", fmt.Errorf("invalid codec: %q", spec)
	}
}

func printProgress(current, total int) {
	if total <= 0 {
		return
	}
	if current < 0 {
		current = 0
	}
	if current > total {
		current = total
	}
	if progressStart.IsZero() || progressTotal != total || current <= 1 {
		progressStart = time.Now()
		progressTotal = total
	}
	const width = 40
	filled := width * current / total
	pct := 100 * current / total
	bar := make([]byte, width)
	for i := range bar {
		if i < filled {
			bar[i] = '='
		} else if i == filled {
			bar[i] = '>'
		} else {
			bar[i] = ' '
		}
	}
	eta := "--:--"
	if current > 0 {
		elapsed := time.Since(progressStart)
		remaining := total - current
		if remaining <= 0 {
			eta = "00:00"
		} else if elapsed > 0 {
			perItem := elapsed / time.Duration(current)
			eta = formatETA(perItem * time.Duration(remaining))
		}
	}
	fmt.Fprintf(os.Stderr, "\r  [%s] %3d%%  frame %d/%d  ETA %s",
		bar, pct, current, total, eta)
	if current >= total {
		fmt.Fprintln(os.Stderr)
	}
}

var progressStart time.Time
var progressTotal int

func formatETA(d time.Duration) string {
	if d < 0 {
		d = 0
	}
	secs := int((d + time.Second/2) / time.Second)
	h := secs / 3600
	m := (secs % 3600) / 60
	s := secs % 60
	if h > 0 {
		return fmt.Sprintf("%d:%02d:%02d", h, m, s)
	}
	return fmt.Sprintf("%02d:%02d", m, s)
}

func printEncoderVersionInfo() {
	fmt.Printf("Clix Encoder %s\n", encoderVersion)
	fmt.Printf("Vanta Version: %s\n", encoderAuxiliaryVersion)
	fmt.Printf("Formats: CLIX %s  BLIX %s  TRIX %s  VLIX %s  ALIX %s\n", clixVersion, blixVersion, trixVersion, vlixVersion, alixVersion)
	fmt.Printf("Platform: %s/%s  Go: %s\n", runtime.GOOS, runtime.GOARCH, runtime.Version())
	fmt.Printf("Runtime: CPUs=%d  GOMAXPROCS=%d\n", runtime.NumCPU(), runtime.GOMAXPROCS(0))
	fmt.Printf("Backends: IDCT=%s  Compute=%s\n", idctBackendName(), computeBackendName())
	if note := computeBackendNote(); note != "" {
		fmt.Printf("Compute note: %s\n", note)
	}
	fmt.Printf("Defaults: codec=vlix2  chroma=420  dct-quality=75  dct-res-quality=70  bframes=%d\n", vlxDefaultBFrames)
	fmt.Println("TRIX DCT defaults: lossless=100  safe=75  experimental=75  unsafe=50 (overridden by --dct-quality)")
}

func main() {
	helpFlag := pflag.BoolP("help", "h", false, "Show this help and exit")
	preset := pflag.String("preset", "safe", "Compression preset base for CLIX/BLIX/VLIX: lossless | safe | unsafe | experimental")
	dither := pflag.Bool("dither", false, "Enable Floyd-Steinberg dithering in palette mode (unsafe, CLIX/BLIX/VLIX)")
	palette := pflag.Int("palette", 0, "Palette size (1-256, unsafe mode only, CLIX/BLIX/VLIX)")
	blocksize := pflag.Int("blocksize", 0, "Block smoothing size (e.g., 2 or 4, unsafe mode only, CLIX/BLIX/VLIX)")
	blockvar := pflag.Float64("blockvar", 12.0, "Variance threshold for block smoothing (unsafe, CLIX/BLIX/VLIX)")
	roundstep := pflag.Int("roundstep", -1, "Channel rounding step (0=off, CLIX/BLIX/VLIX)")
	deltasnap := pflag.Int("deltasnap", -1, "Delta snap threshold (0=off, CLIX/BLIX/VLIX)")
	shapesStr := pflag.String("shapes", "false", "Enable shape primitives in CLIX encode. Accepts: true|false")
	trixFlag := pflag.Bool("trix", false, "Encode still images as TRIX mixed DCT/BLIX-style blocks")
	trixABTestAllFlag := pflag.Bool("trix-ab-test-all", false, "For TRIX, force exact BLIX-vs-DCT choice for every block")
	zstdLevelFlag := pflag.Int("zstd-level", 22, "Zstd compression level for CLIX/BLIX/TRIX/VLIX (1-22)")
	fastFlag := pflag.Bool("fast", false, "Faster encode (lower zstd and simpler RLE)")
	versionFlag := pflag.Bool("version", false, "Print version and exit")
	simdBackendFlag := pflag.Bool("simd-backend", false, "Print active VLIX2 IDCT backend and continue (or exit if no input)")
	computeFlag := pflag.String("compute", "auto", "Compute backend scaffold: auto|cpu|cuda|cuda-f32|vulkan")
	binaryStr := pflag.String("binary", "false", "Write binary output where supported (e.g., .blix/.alix). Accepts: true|false")
	fpsFlag := pflag.Float64("fps", 30, "Frames per second for Vlix encoding")
	keyintFlag := pflag.Int("keyint", 30, "Keyframe interval for Vlix encoding (frames)")
	motionFlag := pflag.Bool("motion", true, "Enable motion search for Vlix (slower, can reduce size)")
	blockSizeFlag := pflag.Int("block-size", vlxDefaultBlockDim, "Motion block size in pixels for Vlix")
	searchFlag := pflag.Int("search", vlxDefaultSearchRadius, "Motion search radius in pixels for Vlix")
	motionThreshFlag := pflag.Int("motion-threshold", vlxDefaultMotionThreshold, "Motion match threshold for Vlix (0=lossless, higher=more compression)")
	bframesFlag := pflag.Int("bframes", vlxDefaultBFrames, "Number of B-frames between references for VLIX2 (0=off)")
	chromaFlag := pflag.String("chroma", "420", "Chroma subsampling for Vlix: 444|422|420")
	codecFlag := pflag.String("codec", "vlix2", "VLIX codec: vlix2 (default, DCT-based, smaller, lossy) | vlix1")
	dctQualityFlag := pflag.Int("dct-quality", 75, "DCT quality for TRIX blocks and VLIX2 keyframes (1-100, higher=better)")
	dctResQualityFlag := pflag.Int("dct-res-quality", 70, "DCT quality for VLIX2 residuals (1-100, higher=better)")
	noAudioFlag := pflag.Bool("no-audio", false, "Disable audio extraction for video input")
	keepAudioFlag := pflag.BoolP("keep-audio", "k", false, "Keep a .alix file alongside the .vlix output")
	separateAudioFlag := pflag.Bool("sep-audio", false, "Write audio to .alix and keep .vlix video-only")
	framesOutFlag := pflag.Bool("frames", false, "Decode .vlix to a folder of PNG frames instead of an .mp4")
	wavOutFlag := pflag.Bool("wav", false, "Decode .alix to .wav instead of .flac")
	audioZstdFlag := pflag.Int("audio-zstd", 0, "Zstd level for ALIX audio (1-22, 0=use --zstd-level capped at 10)")
	audioBlockFlag := pflag.Int("audio-block", 0, "ALIX block size in frames (0=auto size optimize)")
	audioChFlag := pflag.Int("audio-ch", 0, "Audio channels for ALIX encoding (0=source, 1=mono, 2=stereo)")
	audioRateFlag := pflag.String("audio-rate", "auto", "Audio sample rate: auto|source|<Hz> (auto downsamples >44100)")
	pflag.Usage = printUsage
	pflag.Parse()
	if *helpFlag {
		pflag.Usage()
		return
	}
	if err := setComputeBackend(*computeFlag); err != nil {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --compute:", err)
		os.Exit(2)
	}
	if *versionFlag {
		if pflag.NArg() == 0 {
			printEncoderVersionInfo()
			return
		}
		fmt.Fprintln(os.Stderr, "Error: --version cannot be combined with an input path.")
		os.Exit(2)
	}
	if note := computeBackendNote(); note != "" {
		fmt.Fprintf(os.Stderr, "[!] Compute backend %q requested; using scaffold fallback (%s)\n", computeBackendName(), note)
	}
	if *simdBackendFlag {
		fmt.Printf("VLIX2 IDCT backend: %s\n", idctBackendName())
		fmt.Printf("Compute backend: %s\n", computeBackendName())
		if pflag.NArg() == 0 {
			return
		}
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
		"shapes":    changedFlags["shapes"],
		"trix":      changedFlags["trix"],
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
	if changedFlags["audio-block"] && *audioBlockFlag < 0 {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --audio-block: must be >= 0")
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
	shapesEnabled, err := parseBoolLoose(*shapesStr)
	if err != nil {
		fmt.Fprintln(os.Stderr, "[-] Flag error for --shapes:", err)
		os.Exit(2)
	}
	trixEnabled := *trixFlag
	if *trixABTestAllFlag && !trixEnabled {
		fmt.Fprintln(os.Stderr, "[-] --trix-ab-test-all requires --trix")
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
	codec := vlixCodecV2
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
			shapesEnabled,
			*zstdLevelFlag,
			changed,
			*fastFlag,
		)
		if codec == vlixCodecV2 {
			st.chromaMode = "444"
			if err := encodeVLIX2(input, out, st, *fpsFlag, *keyintFlag, nil, ffmpegPath, chromaMode, *dctQualityFlag, *dctResQualityFlag, motionEnabled, blockDim, searchRadius, motionThreshold, bframes, *fastFlag); err != nil {
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
			shapesEnabled,
			*zstdLevelFlag,
			changed,
			*fastFlag,
		)
		logStep("Encoding VLIX")
		if codec == vlixCodecV2 && motionEnabled && !computeSupportsMotionSearch() {
			logStep("Motion search backend: cpu (compute=%s currently accelerates DCT/IDCT only)", computeBackendName())
		}
		if codec == vlixCodecV2 {
			st.chromaMode = "444"
			if err := encodeVLIX2(tmpDir, out, st, fps, keyint, audioBlob, ffmpegPath, chromaMode, *dctQualityFlag, *dctResQualityFlag, motionEnabled, blockDim, searchRadius, motionThreshold, bframes, *fastFlag); err != nil {
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
		pcm, sr, ch, err := decodeALIXToPCM(raw)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] ALIX decode error:", err)
			os.Exit(1)
		}
		ffPath, _ := findTool("ffmpeg")
		if !*wavOutFlag {
			if ffPath != "" {
				out := name + ".flac"
				if err := pcmToFLAC(ffPath, out, pcm, sr, ch); err != nil {
					fmt.Fprintln(os.Stderr, "[!] FLAC encode failed, writing WAV instead:", err)
				} else {
					fmt.Printf("[+] Decoded %s -> %s\n", input, out)
					return
				}
			} else {
				fmt.Fprintln(os.Stderr, "[!] ffmpeg not found; writing WAV (install ffmpeg for FLAC, or pass --wav)")
			}
		}
		out := name + ".wav"
		if err := writeWAV(out, pcm, sr, ch); err != nil {
			fmt.Fprintln(os.Stderr, "[-] WAV write error:", err)
			os.Exit(1)
		}
		fmt.Printf("[+] Decoded %s -> %s\n", input, out)
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
	if ext == ".trix" {
		if err := decodeTRIX(input, name+".png"); err != nil {
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
		framesDir := name + "_frames"
		audioBlob, err := decodeVLIX(input, framesDir)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] Vlix decode error:", err)
			os.Exit(1)
		}
		ffPath, _ := findTool("ffmpeg")
		if !*framesOutFlag {
			if ffPath != "" {
				audioWav := ""
				if len(audioBlob) > 0 {
					if pcm, sr, ch, aerr := decodeALIXToPCM(audioBlob); aerr == nil {
						if tf, terr := os.CreateTemp("", "vlxaudio*.wav"); terr == nil {
							tf.Close()
							if writeWAV(tf.Name(), pcm, sr, ch) == nil {
								audioWav = tf.Name()
								defer os.Remove(audioWav)
							}
						}
					} else {
						fmt.Fprintln(os.Stderr, "[!] embedded audio decode failed; muxing video only:", aerr)
					}
				}
				out := name + ".mp4"
				if err := framesToMP4(ffPath, framesDir, out, vlixHeaderFPS(input), audioWav); err != nil {
					fmt.Fprintln(os.Stderr, "[!] mp4 mux failed, keeping frames:", err)
				} else {
					os.RemoveAll(framesDir)
					fmt.Printf("[+] Decoded %s -> %s\n", input, out)
					return
				}
			} else {
				fmt.Fprintln(os.Stderr, "[!] ffmpeg not found; emitting frames (install ffmpeg for .mp4, or pass --frames)")
			}
		}
		fmt.Printf("[+] Decoded %s -> %s/\n", input, framesDir)
		if len(audioBlob) > 0 {
			audioOut := audioBlob
			if !bin {
				audioOut = encodeALIXTextFromBinary(audioBlob)
			}
			audioPath := name + ".alix"
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
		shapesEnabled,
		*zstdLevelFlag,
		changed,
		*fastFlag,
	)
	var out string
	if trixEnabled {
		out = name + ".trix"
		trixDCTQuality := resolveTrixDCTQuality(st.mode, *dctQualityFlag, changedFlags["dct-quality"])
		stats, err := encodeTRIX(input, out, st, ffmpegPath, trixDCTQuality, *trixABTestAllFlag)
		if err != nil {
			fmt.Fprintln(os.Stderr, "[-] Encode error:", err)
			os.Exit(1)
		}
		fmt.Printf("[*] TRIX blocks: total=%d BLIX-style=%d DCT=%d blx-built=%d shortcuts=%d payload=%d bytes\n", stats.blocks, stats.blx, stats.dct, stats.abTests, stats.skipTests, stats.blxBytes+stats.dctBytes)
	} else if bin {
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
	if src, ok := img.(*image.NRGBA); ok {
		w := b.Dx()
		for y := 0; y < b.Dy(); y++ {
			srcRow := src.PixOffset(b.Min.X, b.Min.Y+y)
			dstRow := out.PixOffset(b.Min.X, b.Min.Y+y)
			copy(out.Pix[dstRow:dstRow+w*4], src.Pix[srcRow:srcRow+w*4])
		}
		return out
	}
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

func newZstdWriter(w io.Writer, level int) (*zstd.Encoder, error) {
	level = clampInt(level, 1, 22)
	return zstd.NewWriter(
		w,
		zstd.WithEncoderLevel(zstd.EncoderLevelFromZstd(level)),
		zstd.WithWindowSize(zstd.MaxWindowSize),
	)
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
