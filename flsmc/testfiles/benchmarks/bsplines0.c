
/*@
  \flostat::distribution u, "Uniform", 0.0, 1.0;
  \flostat::prob_ensures 0.99, 0.001,
		\flteq(\result, ((1-u) * (1-u) * (1-u)) / 6 , 0.0000000571);
*/
float bsplines0(float u) {
	return ((1.0f - u) * (1.0f - u) * (1.0f - u)) / 6.0f;
}
