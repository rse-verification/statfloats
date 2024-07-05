#include "errno.h"
#include "stdlib.h"
#include "stdio.h"
#include "fenv.h"
#include "math.h"
#include "mpfr.h"

extern int ( /* missing proto */ atoi)(const char *x_0);


float uniform(float lo, float hi) {
  return ((float)rand()/(float)(RAND_MAX)) * (hi-lo) + lo;
}
