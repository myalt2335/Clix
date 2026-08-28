//   nvcc -ptx -arch=compute_75 vlx_kernels.cu -o vlx_kernels.ptx
// Init table T[r*8+c] = 0.5*scale[r]*cos[r][c]; DCT = T.B.T^T, IDCT = T^T.F.T,

extern "C" __global__ void dct_many(const double *in, int n, const double *T, double *out) {
	int blk = blockIdx.x;
	if (blk >= n) return;
	int t = threadIdx.x;
	__shared__ double B[64];
	__shared__ double Ts[64];
	B[t] = in[blk * 64 + t];
	Ts[t] = T[t];
	__syncthreads();
	int v = t >> 3, u = t & 7;
	double acc = 0.0;
	for (int y = 0; y < 8; y++)
		for (int x = 0; x < 8; x++) acc += Ts[u * 8 + x] * B[y * 8 + x] * Ts[v * 8 + y];
	out[blk * 64 + t] = acc;
}

extern "C" __global__ void idct_many(const double *in, int n, const double *T, double *out) {
	int blk = blockIdx.x;
	if (blk >= n) return;
	int t = threadIdx.x;
	__shared__ double F[64];
	__shared__ double Ts[64];
	F[t] = in[blk * 64 + t];
	Ts[t] = T[t];
	__syncthreads();
	int y = t >> 3, x = t & 7;
	double acc = 0.0;
	for (int v = 0; v < 8; v++)
		for (int u = 0; u < 8; u++) acc += F[v * 8 + u] * Ts[u * 8 + x] * Ts[v * 8 + y];
	out[blk * 64 + t] = acc;
}
