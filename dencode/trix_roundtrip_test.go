package main

import (
	"bufio"
	"fmt"
	"image"
	"image/color"
	"os"
	"path/filepath"
	"testing"
)

// Solid cells have zero variance, so TRIX codes them all as lossless BLX blocks;
func distinctBlockImage(w, h, blockDim int) *image.NRGBA {
	img := image.NewNRGBA(image.Rect(0, 0, w, h))
	bx := (w + blockDim - 1) / blockDim
	for by := 0; by < h; by += blockDim {
		for bxp := 0; bxp < w; bxp += blockDim {
			bi := (by/blockDim)*bx + bxp/blockDim
			c := color.NRGBA{uint8(30 + bi*17), uint8(60 + bi*11), uint8(20 + bi*23), 255}
			for y := by; y < by+blockDim && y < h; y++ {
				for x := bxp; x < bxp+blockDim && x < w; x++ {
					img.SetNRGBA(x, y, c)
				}
			}
		}
	}
	return img
}

func TestTrixPlanarRoundTrip(t *testing.T) {
	dir := t.TempDir()
	img := distinctBlockImage(43, 27, trixDefaultBlockDim)
	src := filepath.Join(dir, "in.png")
	writeTestPNG(t, src, img)
	trixPath := filepath.Join(dir, "out.trix")
	if _, err := encodeTRIX(src, trixPath, losslessSettings(t), "", 100, false); err != nil {
		t.Fatalf("encodeTRIX: %v", err)
	}
	got, methods, _, err := decodeTRIXToImage(trixPath)
	if err != nil {
		t.Fatalf("decodeTRIXToImage: %v", err)
	}
	for i, m := range methods {
		if m != trixMethodBLX {
			t.Fatalf("block %d method = %d, want BLX (flat blocks)", i, m)
		}
	}
	assertPixEqual(t, img, got)
}

func writeLegacyTRIX(t *testing.T, path string, img *image.NRGBA, st encodeSettings) {
	t.Helper()
	b := img.Bounds()
	width, height := b.Dx(), b.Dy()
	blockDim := trixDefaultBlockDim
	f, err := os.Create(path)
	if err != nil {
		t.Fatalf("create: %v", err)
	}
	defer f.Close()
	enc, err := newZstdWriter(f, 19)
	if err != nil {
		t.Fatalf("zstd: %v", err)
	}
	bw := bufio.NewWriter(enc)
	fmt.Fprintf(bw, "TRIX 0.1\nWIDTH=%d\nHEIGHT=%d\nBLOCK=%d\nDCT_QUALITY=%d\nZSTD_LEVEL=%d\n\n", width, height, blockDim, 100, 19)
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
			payload, err := trixEncodeBLXBlock(pixels, st)
			if err != nil {
				t.Fatalf("encode block: %v", err)
			}
			bw.WriteByte(trixMethodBLX)
			if err := writeUvarint(bw, uint64(len(payload))); err != nil {
				t.Fatalf("uvarint: %v", err)
			}
			bw.Write(payload)
		}
	}
	if err := bw.Flush(); err != nil {
		t.Fatalf("flush: %v", err)
	}
	if err := enc.Close(); err != nil {
		t.Fatalf("enc close: %v", err)
	}
}

func TestTrixLegacyInterleavedRoundTrip(t *testing.T) {
	dir := t.TempDir()
	img := distinctBlockImage(43, 27, trixDefaultBlockDim)
	trixPath := filepath.Join(dir, "legacy.trix")
	writeLegacyTRIX(t, trixPath, img, losslessSettings(t))
	got, methods, _, err := decodeTRIXToImage(trixPath)
	if err != nil {
		t.Fatalf("decodeTRIXToImage (legacy): %v", err)
	}
	for i, m := range methods {
		if m != trixMethodBLX {
			t.Fatalf("block %d method = %d, want BLX", i, m)
		}
	}
	assertPixEqual(t, img, got)
}
