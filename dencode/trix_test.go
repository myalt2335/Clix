package main

import (
	"math"
	"testing"
)

func TestTrixPredictBlockChoice(t *testing.T) {
	flat := make([]RGBA, 64)
	for i := range flat {
		flat[i] = RGBA{0, 0, 0, 255}
	}
	if got := trixPredictBlockChoice(flat, 8, 8); got != trixChoiceBLX {
		t.Fatalf("flat block choice = %v, want BLX", got)
	}

	noisy := make([]RGBA, 64)
	for i := range noisy {
		noisy[i] = RGBA{
			R: uint8((i*37 + 11) & 0xff),
			G: uint8((i*73 + 29) & 0xff),
			B: uint8((i*109 + 47) & 0xff),
			A: 255,
		}
	}
	if got := trixPredictBlockChoice(noisy, 8, 8); got != trixChoiceDCT {
		t.Fatalf("high-entropy block choice = %v, want DCT", got)
	}

	checker := make([]RGBA, 64)
	for y := 0; y < 8; y++ {
		for x := 0; x < 8; x++ {
			if (x+y)%2 == 0 {
				checker[y*8+x] = RGBA{0, 0, 0, 255}
			} else {
				checker[y*8+x] = RGBA{255, 255, 255, 255}
			}
		}
	}
	if got := trixPredictBlockChoice(checker, 8, 8); got != trixChoiceTest {
		t.Fatalf("checkerboard block choice = %v, want A/B test", got)
	}
}

func TestDCT8x8IntoMatchesDirectDCT(t *testing.T) {
	var block [64]float64
	for i := range block {
		block[i] = float64((i*17)%251) - 120.0
	}
	var got [64]float64
	dct8x8Into(block[:], got[:])

	var want [64]float64
	for v := 0; v < 8; v++ {
		for u := 0; u < 8; u++ {
			sum := 0.0
			for y := 0; y < 8; y++ {
				for x := 0; x < 8; x++ {
					sum += block[y*8+x] * dctCos[u][x] * dctCos[v][y]
				}
			}
			want[v*8+u] = 0.25 * dctScale[u] * dctScale[v] * sum
		}
	}

	for i := range want {
		if math.Abs(got[i]-want[i]) > 1e-9 {
			t.Fatalf("coefficient %d = %.12f, want %.12f", i, got[i], want[i])
		}
	}
}

func TestCompactChannelReferenceTokens(t *testing.T) {
	cases := []struct {
		px   RGBA
		want string
	}{
		{RGBA{0xAB, 0xAB, 0xAB, 0xFF}, "ABRRFF"},
		{RGBA{0xAA, 0x32, 0xAA, 0xFF}, "AA32RFF"},
		{RGBA{0x12, 0x34, 0x34, 0xFF}, "1234GFF"},
		{RGBA{0xFF, 0xFF, 0xFF, 0xFF}, "W"},
	}
	for _, tc := range cases {
		if got := rgbaToToken(tc.px); got != tc.want {
			t.Fatalf("rgbaToToken(%#v) = %q, want %q", tc.px, got, tc.want)
		}
		decoded, err := tokenToRGBA(tc.want, nil, nil)
		if err != nil {
			t.Fatalf("tokenToRGBA(%q): %v", tc.want, err)
		}
		if decoded != tc.px {
			t.Fatalf("tokenToRGBA(%q) = %#v, want %#v", tc.want, decoded, tc.px)
		}
	}

	tokens, err := tokenizeLineWithMacros("ABRRFF1234GFFW", nil)
	if err != nil {
		t.Fatal(err)
	}
	wantTokens := []string{"ABRRFF", "1234GFF", "W"}
	if len(tokens) != len(wantTokens) {
		t.Fatalf("tokens = %#v, want %#v", tokens, wantTokens)
	}
	for i := range wantTokens {
		if tokens[i] != wantTokens[i] {
			t.Fatalf("tokens = %#v, want %#v", tokens, wantTokens)
		}
	}
}

func TestTrixBLXMeasureMatchesEncodedPayload(t *testing.T) {
	pixels := make([]RGBA, 64)
	for i := range pixels {
		switch {
		case i < 18:
			pixels[i] = RGBA{0x22, 0x22, 0x22, 0xFF}
		case i%5 == 0:
			pixels[i] = RGBA{0x12, 0x34, 0x34, 0xFF}
		default:
			pixels[i] = RGBA{uint8(i * 3), uint8(i * 7), uint8(i * 11), 0xFF}
		}
	}
	st, _, _ := buildEncodeSettings("safe", false, 0, 0, 12, -1, -1, false, 22, map[string]bool{}, false)
	tokens, macros, macroMap, measured, err := trixPrepareBLXBlock(pixels, st)
	if err != nil {
		t.Fatal(err)
	}
	payload, err := trixEncodePreparedBLXBlock(tokens, macros, macroMap)
	if err != nil {
		t.Fatal(err)
	}
	if measured != len(payload) {
		t.Fatalf("measured BLX payload size = %d, encoded size = %d", measured, len(payload))
	}
}

func TestResolveTrixDCTQuality(t *testing.T) {
	cases := []struct {
		name      string
		mode      string
		requested int
		explicit  bool
		want      int
	}{
		{"lossless default", "lossless", 75, false, 100},
		{"unsafe default", "unsafe", 75, false, 50},
		{"safe default", "safe", 75, false, 75},
		{"experimental default", "experimental", 75, false, 75},
		{"lossless explicit", "lossless", 80, true, 80},
		{"unsafe explicit", "unsafe", 90, true, 90},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			if got := resolveTrixDCTQuality(tc.mode, tc.requested, tc.explicit); got != tc.want {
				t.Fatalf("resolveTrixDCTQuality(%q, %d, %v) = %d, want %d", tc.mode, tc.requested, tc.explicit, got, tc.want)
			}
		})
	}
}
