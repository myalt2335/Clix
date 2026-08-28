#ifndef VLX_ACCEL_H
#define VLX_ACCEL_H

#ifdef __cplusplus
extern "C" {
#endif

typedef struct vlx_motion_mv {
	int mode;
	int dx1, dy1;
	int dx2, dy2;
} vlx_motion_mv;

int  vlix_idct_backend_id(void);
void vlix_idct8x8(const double *coeff, const double *dctCos, const double *dctScale, double *out);
void vlix_idct8x8_many(const double *coeff, int blocks, const double *dctCos, const double *dctScale, double *out);
void vlix_dct8x8(const double *block, const double *dctCos, const double *dctScale, double *out);
void vlix_dct8x8_many(const double *block, int blocks, const double *dctCos, const double *dctScale, double *out);

const char *vlx_cuda_init_f32(const float *table64);
const char *vlx_cuda_dct_many_f32(const float *in, int n, float *out);
const char *vlx_cuda_idct_many_f32(const float *in, int n, float *out);
const char *vlx_cuda_motion_search_f32(const float *cur, const float *prev, const float *next,
	int width, int height, int blockDim, int searchRadius, int motionThreshold,
	int planType, int total, vlx_motion_mv *out);

#ifdef __cplusplus
}
#endif

#endif
