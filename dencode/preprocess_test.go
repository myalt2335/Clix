package main

import (
	"fmt"
	"image"
	"image/color"
	"math/rand"
	"strings"
	"testing"
)

func sequenceRLERef(tokens []string, maxSeqLen int) []string {
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

func randTokens(rng *rand.Rand, n, alphabet int) []string {
	t := make([]string, n)
	for i := range t {
		t[i] = fmt.Sprintf("t%d", rng.Intn(alphabet))
	}
	return t
}

func TestSequenceRLEMatchesReference(t *testing.T) {
	rng := rand.New(rand.NewSource(3))
	seqLens := []int{4, 16, 64}
	for trial := 0; trial < 400; trial++ {
		n := rng.Intn(120)
		// Small alphabets induce lots of repeats (the interesting RLE cases);
		alphabet := 1 + rng.Intn(6)
		tokens := randTokens(rng, n, alphabet)
		msl := seqLens[rng.Intn(len(seqLens))]
		want := sequenceRLERef(tokens, msl)
		got := sequenceRLE(tokens, msl)
		if len(got) != len(want) {
			t.Fatalf("trial %d (n=%d alpha=%d msl=%d): len %d != %d\nwant %v\ngot  %v", trial, n, alphabet, msl, len(got), len(want), want, got)
		}
		for i := range want {
			if got[i] != want[i] {
				t.Fatalf("trial %d: token %d differs: %q != %q", trial, i, got[i], want[i])
			}
		}
	}
}

func TestSequenceRLEStructured(t *testing.T) {
	tokens := strings.Fields("a b a b a b a b")
	got := sequenceRLE(tokens, 64)
	want := []string{"(a b)*4"}
	if len(got) != 1 || got[0] != want[0] {
		t.Fatalf("got %v, want %v", got, want)
	}
}

func blockSmoothRef(src *image.NRGBA, block int, varThreshold float64) *image.NRGBA {
	b := src.Bounds()
	out := image.NewNRGBA(b)
	for y := b.Min.Y; y < b.Max.Y; y++ {
		for x := b.Min.X; x < b.Max.X; x++ {
			out.SetNRGBA(x, y, src.NRGBAAt(x, y))
		}
	}
	for y0 := b.Min.Y; y0 < b.Max.Y; y0 += block {
		for x0 := b.Min.X; x0 < b.Max.X; x0 += block {
			x1 := min(x0+block, b.Max.X)
			y1 := min(y0+block, b.Max.Y)
			var rs, gs, bs, count, r2, g2, b2 float64
			for y := y0; y < y1; y++ {
				for x := x0; x < x1; x++ {
					c := out.NRGBAAt(x, y)
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
			avgVar := ((r2/count - mr*mr) + (g2/count - mg*mg) + (b2/count - mb*mb)) / 3.0
			if avgVar <= varThreshold {
				R, G, B := uint8(mr+0.5), uint8(mg+0.5), uint8(mb+0.5)
				for y := y0; y < y1; y++ {
					for x := x0; x < x1; x++ {
						a := out.NRGBAAt(x, y).A
						out.SetNRGBA(x, y, color.NRGBA{R, G, B, a})
					}
				}
			}
		}
	}
	return out
}

func TestBlockSmoothMatchesReference(t *testing.T) {
	rng := rand.New(rand.NewSource(5))
	const W, H = 37, 29
	img := image.NewNRGBA(image.Rect(0, 0, W, H))
	for by := 0; by < H; by += 8 {
		for bx := 0; bx < W; bx += 8 {
			flat := rng.Intn(2) == 0
			fr, fg, fb := uint8(rng.Intn(256)), uint8(rng.Intn(256)), uint8(rng.Intn(256))
			for y := by; y < by+8 && y < H; y++ {
				for x := bx; x < bx+8 && x < W; x++ {
					a := uint8((x*5 + y*3) % 256)
					if flat {
						img.SetNRGBA(x, y, color.NRGBA{fr, fg, fb, a})
					} else {
						img.SetNRGBA(x, y, color.NRGBA{uint8(rng.Intn(256)), uint8(rng.Intn(256)), uint8(rng.Intn(256)), a})
					}
				}
			}
		}
	}
	const block = 8
	const thr = 50.0
	want := blockSmoothRef(img, block, thr)
	got := blockSmooth(img, block, thr).(*image.NRGBA)
	if got.Bounds() != want.Bounds() {
		t.Fatalf("bounds %v != %v", got.Bounds(), want.Bounds())
	}
	for i := range want.Pix {
		if got.Pix[i] != want.Pix[i] {
			t.Fatalf("pixel byte %d differs: %d != %d", i, got.Pix[i], want.Pix[i])
		}
	}
}
