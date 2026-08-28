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
