package main

import (
	"image"
	"image/color"
	"image/png"
	"os"
	"path/filepath"
	"testing"
)

func writeTestPNG(t *testing.T, path string, img *image.NRGBA) {
	t.Helper()
	f, err := os.Create(path)
	if err != nil {
		t.Fatalf("create png: %v", err)
	}
	defer f.Close()
	if err := png.Encode(f, img); err != nil {
		t.Fatalf("encode png: %v", err)
	}
}

func loadNRGBA(t *testing.T, path string) *image.NRGBA {
	t.Helper()
	f, err := os.Open(path)
	if err != nil {
		t.Fatalf("open png: %v", err)
	}
	defer f.Close()
	im, err := png.Decode(f)
	if err != nil {
		t.Fatalf("decode png: %v", err)
	}
	return imageToNRGBA(im)
}

func assertPixEqual(t *testing.T, a, b *image.NRGBA) {
	t.Helper()
	if a.Bounds() != b.Bounds() {
		t.Fatalf("bounds differ: %v vs %v", a.Bounds(), b.Bounds())
	}
	for i := range a.Pix {
		if a.Pix[i] != b.Pix[i] {
			t.Fatalf("pixel byte %d differs: %d vs %d", i, a.Pix[i], b.Pix[i])
		}
	}
}

func alphaTestImage() *image.NRGBA {
	const W, H = 20, 12
	img := image.NewNRGBA(image.Rect(0, 0, W, H))
	for y := 0; y < H; y++ {
		for x := 0; x < W; x++ {
			img.SetNRGBA(x, y, color.NRGBA{R: 200, G: 100, B: 50, A: uint8((x*13 + y*7) % 256)})
		}
	}
	return img
}

func opaqueTestImage() *image.NRGBA {
	const W, H = 24, 16
	img := image.NewNRGBA(image.Rect(0, 0, W, H))
	for y := 0; y < H; y++ {
		for x := 0; x < W; x++ {
			img.SetNRGBA(x, y, color.NRGBA{R: uint8(x * 7), G: uint8(y * 9), B: uint8(x + y), A: 255})
		}
	}
	return img
}

func losslessSettings(t *testing.T) encodeSettings {
	t.Helper()
	st, _, _ := buildEncodeSettings("lossless", false, 0, 0, 12.0, -1, -1, false, 22, map[string]bool{}, false)
	return st
}

func TestCLIXLosslessRoundTrip(t *testing.T) {
	dir := t.TempDir()
	cases := map[string]*image.NRGBA{
		"alpha":  alphaTestImage(),
		"opaque": opaqueTestImage(),
	}
	for name, img := range cases {
		t.Run(name, func(t *testing.T) {
			src := filepath.Join(dir, name+".png")
			writeTestPNG(t, src, img)
			clixPath := filepath.Join(dir, name+".clix")
			if err := encodeCLIX(src, clixPath, losslessSettings(t), ""); err != nil {
				t.Fatalf("encodeCLIX: %v", err)
			}
			outPath := filepath.Join(dir, name+"_out.png")
			if err := decodeCLIX(clixPath, outPath); err != nil {
				t.Fatalf("decodeCLIX: %v", err)
			}
			assertPixEqual(t, img, loadNRGBA(t, outPath))
		})
	}
}

func manyColorImage() *image.NRGBA {
	const W, H = 32, 24
	img := image.NewNRGBA(image.Rect(0, 0, W, H))
	for y := 0; y < H; y++ {
		for x := 0; x < W; x++ {
			c := (y*W + x) / 5
			img.SetNRGBA(x, y, color.NRGBA{R: uint8(c * 7), G: uint8(c * 13), B: uint8(c*29 + 3), A: 255})
		}
	}
	return img
}

func TestCLIXManyMacrosRoundTrip(t *testing.T) {
	dir := t.TempDir()
	img := manyColorImage()
	src := filepath.Join(dir, "many.png")
	writeTestPNG(t, src, img)
	clixPath := filepath.Join(dir, "many.clix")
	if err := encodeCLIX(src, clixPath, losslessSettings(t), ""); err != nil {
		t.Fatalf("encodeCLIX: %v", err)
	}
	outPath := filepath.Join(dir, "many_out.png")
	if err := decodeCLIX(clixPath, outPath); err != nil {
		t.Fatalf("decodeCLIX: %v", err)
	}
	assertPixEqual(t, img, loadNRGBA(t, outPath))
}

func TestBLIXLosslessRoundTrip(t *testing.T) {
	dir := t.TempDir()
	cases := map[string]*image.NRGBA{
		"alpha":  alphaTestImage(),
		"opaque": opaqueTestImage(),
	}
	for name, img := range cases {
		t.Run(name, func(t *testing.T) {
			src := filepath.Join(dir, name+".png")
			writeTestPNG(t, src, img)
			blixPath := filepath.Join(dir, name+".blix")
			if err := encodeBLIX(src, blixPath, losslessSettings(t), ""); err != nil {
				t.Fatalf("encodeBLIX: %v", err)
			}
			outPath := filepath.Join(dir, name+"_out.png")
			if err := decodeBLIX(blixPath, outPath); err != nil {
				t.Fatalf("decodeBLIX: %v", err)
			}
			assertPixEqual(t, img, loadNRGBA(t, outPath))
		})
	}
}
