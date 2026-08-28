//go:build !cgo

package main

func idctBackendName() string {
	return "go-scalar"
}

func idct8x8Decode(coeff [64]float64) [64]float64 {
	return idct8x8(coeff)
}

func idct8x8DecodeMany(coeffBlocks []float64, outBlocks []float64) {
	if len(coeffBlocks) == 0 {
		return
	}
	blocks := len(coeffBlocks) / 64
	for i := 0; i < blocks; i++ {
		off := i * 64
		var coeff [64]float64
		copy(coeff[:], coeffBlocks[off:off+64])
		blk := idct8x8(coeff)
		copy(outBlocks[off:off+64], blk[:])
	}
}

func dct8x8Encode(block [64]float64) [64]float64 {
	return dct8x8(block)
}

func dct8x8EncodeMany(blocksIn []float64, coeffOut []float64) {
	if len(blocksIn) == 0 {
		return
	}
	blocks := len(blocksIn) / 64
	for i := 0; i < blocks; i++ {
		off := i * 64
		dct8x8Into(blocksIn[off:off+64], coeffOut[off:off+64])
	}
}
