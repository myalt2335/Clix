//   nvcc -ptx -arch=compute_75 vlx_kernels.cu -o vlx_kernels.ptx
//   #   static const char *VLX_PTX = "<line>\n" ... ;
// The init table is T[r*8+c] = 0.5*scale[r]*cos[r][c], so the separable DCT is
// C = T.B.T^T and the IDCT is B = T^T.F.T, matching the Go scalar transforms.

extern "C" __global__ void dct_many(const float *in, int n, const float *T, float *out) {
	int blk = blockIdx.x;
	if (blk >= n) return;
	int t = threadIdx.x;
	__shared__ float B[64];
	__shared__ float Ts[64];
	B[t] = in[blk * 64 + t];
	Ts[t] = T[t];
	__syncthreads();
	int v = t >> 3, u = t & 7;
	float acc = 0.f;
	for (int y = 0; y < 8; y++)
		for (int x = 0; x < 8; x++) acc += Ts[u * 8 + x] * B[y * 8 + x] * Ts[v * 8 + y];
	out[blk * 64 + t] = acc;
}

extern "C" __global__ void idct_many(const float *in, int n, const float *T, float *out) {
	int blk = blockIdx.x;
	if (blk >= n) return;
	int t = threadIdx.x;
	__shared__ float F[64];
	__shared__ float Ts[64];
	F[t] = in[blk * 64 + t];
	Ts[t] = T[t];
	__syncthreads();
	int y = t >> 3, x = t & 7;
	float acc = 0.f;
	for (int v = 0; v < 8; v++)
		for (int u = 0; u < 8; u++) acc += F[v * 8 + u] * Ts[u * 8 + x] * Ts[v * 8 + y];
	out[blk * 64 + t] = acc;
}

__device__ long long vlx_block_sad(const float *ref, const float *cur, int w, int bx, int by,
	int bw, int bh, int sx, int sy) {
	long long sad = 0;
	for (int y = 0; y < bh; y++)
		for (int x = 0; x < bw; x++) {
			float c = cur[(by + y) * w + (bx + x)];
			float r = ref[(sy + y) * w + (sx + x)];
			float d = c - r;
			if (d < 0) d = -d;
			sad += (long long)(d + 0.5f);
		}
	return sad;
}

__device__ long long vlx_best(const float *ref, const float *cur, int w, int h, int bx, int by,
	int bw, int bh, int radius, int *odx, int *ody) {
	long long best = -1;
	int bdx = 0, bdy = 0;
	for (int dy = -radius; dy <= radius; dy++)
		for (int dx = -radius; dx <= radius; dx++) {
			int sx = bx + dx, sy = by + dy;
			if (sx < 0 || sy < 0 || sx + bw > w || sy + bh > h) continue;
			long long s = vlx_block_sad(ref, cur, w, bx, by, bw, bh, sx, sy);
			if (best < 0 || s < best) { best = s; bdx = dx; bdy = dy; }
		}
	*odx = bdx;
	*ody = bdy;
	return best;
}

// planType: 2 = delta (search prev), 3 = B-frame (prev / next / bi).
extern "C" __global__ void motion_search(const float *cur, const float *prev, const float *next,
	int w, int h, int blkdim, int radius, int threshold, int planType, int total, int *out) {
	int bi = blockIdx.x * blockDim.x + threadIdx.x;
	if (bi >= total) return;
	int bwBlocks = (w + blkdim - 1) / blkdim;
	int bx = (bi % bwBlocks) * blkdim, by = (bi / bwBlocks) * blkdim;
	int bw = blkdim;
	if (bx + bw > w) bw = w - bx;
	int bh = blkdim;
	if (by + bh > h) bh = h - by;
	int mode = 0, dx1 = 0, dy1 = 0, dx2 = 0, dy2 = 0;
	long long limit = (long long)threshold * bw * bh;
	int accept_eq0 = (threshold == 0);
	bool hasPrev = (prev != 0), hasNext = (next != 0);
	if (planType == 2) {
		if (hasPrev) {
			int dx, dy;
			long long s = vlx_best(prev, cur, w, h, bx, by, bw, bh, radius, &dx, &dy);
			if (s >= 0 && ((accept_eq0 && s == 0) || (!accept_eq0 && s <= limit))) { mode = 1; dx1 = dx; dy1 = dy; }
		}
	} else if (planType == 3) {
		long long bestSad = -1;
		int pdx = 0, pdy = 0, ndx = 0, ndy = 0;
		long long sp = -1, sn = -1;
		if (hasPrev) sp = vlx_best(prev, cur, w, h, bx, by, bw, bh, radius, &pdx, &pdy);
		if (hasNext) sn = vlx_best(next, cur, w, h, bx, by, bw, bh, radius, &ndx, &ndy);
		if (sp >= 0) { mode = 1; bestSad = sp; dx1 = pdx; dy1 = pdy; }
		if (sn >= 0 && (bestSad < 0 || sn < bestSad)) { mode = 2; bestSad = sn; dx1 = ndx; dy1 = ndy; }
		if (sp >= 0 && sn >= 0) {
			int spx = bx + pdx, spy = by + pdy, snx = bx + ndx, sny = by + ndy;
			long long sb = 0;
			for (int y = 0; y < bh; y++)
				for (int x = 0; x < bw; x++) {
					float c = cur[(by + y) * w + (bx + x)];
					float a = prev[(spy + y) * w + (spx + x)];
					float bb = next[(sny + y) * w + (snx + x)];
					float p = (a + bb) * 0.5f;
					float d = c - p;
					if (d < 0) d = -d;
					sb += (long long)(d + 0.5f);
				}
			long long bl = (accept_eq0) ? 0 : limit;
			if (sb <= bl && (bestSad < 0 || sb < bestSad)) { mode = 3; dx1 = pdx; dy1 = pdy; dx2 = ndx; dy2 = ndy; }
		}
		if (mode != 0 && !accept_eq0 && bestSad > limit && mode != 3) { mode = 0; dx1 = dy1 = 0; }
	}
	out[bi * 5 + 0] = mode;
	out[bi * 5 + 1] = dx1;
	out[bi * 5 + 2] = dy1;
	out[bi * 5 + 3] = dx2;
	out[bi * 5 + 4] = dy2;
}
