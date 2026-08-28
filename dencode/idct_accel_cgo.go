package main

import "C"
import "unsafe"

func idctBackendName() string {
	switch int(C.vlix_idct_backend_id()) {
	case 2:
		return "avx2"
	case 1:
		return "sse2"
	default:
		return "scalar"
	}
}

func idct8x8Decode(coeff [64]float64) [64]float64 {
	var out [64]float64
	C.vlix_idct8x8(
		(*C.double)(unsafe.Pointer(&coeff[0])),
		(*C.double)(unsafe.Pointer(&dctCos[0][0])),
		(*C.double)(unsafe.Pointer(&dctScale[0])),
		(*C.double)(unsafe.Pointer(&out[0])),
	)
	return out
}

func idct8x8DecodeMany(coeffBlocks []float64, outBlocks []float64) {
	if len(coeffBlocks) == 0 {
		return
	}
	blocks := len(coeffBlocks) / 64
	if blocks == 0 {
		return
	}
	C.vlix_idct8x8_many(
		(*C.double)(unsafe.Pointer(&coeffBlocks[0])),
		C.int(blocks),
		(*C.double)(unsafe.Pointer(&dctCos[0][0])),
		(*C.double)(unsafe.Pointer(&dctScale[0])),
		(*C.double)(unsafe.Pointer(&outBlocks[0])),
	)
}

func dct8x8Encode(block [64]float64) [64]float64 {
	var out [64]float64
	C.vlix_dct8x8(
		(*C.double)(unsafe.Pointer(&block[0])),
		(*C.double)(unsafe.Pointer(&dctCos[0][0])),
		(*C.double)(unsafe.Pointer(&dctScale[0])),
		(*C.double)(unsafe.Pointer(&out[0])),
	)
	return out
}

func dct8x8EncodeMany(blocksIn []float64, coeffOut []float64) {
	if len(blocksIn) == 0 {
		return
	}
	blocks := len(blocksIn) / 64
	if blocks == 0 {
		return
	}
	C.vlix_dct8x8_many(
		(*C.double)(unsafe.Pointer(&blocksIn[0])),
		C.int(blocks),
		(*C.double)(unsafe.Pointer(&dctCos[0][0])),
		(*C.double)(unsafe.Pointer(&dctScale[0])),
		(*C.double)(unsafe.Pointer(&coeffOut[0])),
	)
}
