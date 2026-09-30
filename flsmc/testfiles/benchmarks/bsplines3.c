/*@
  \flostat::distribution u, "Uniform", 0.0, 1.0;
  \flostat::prob_ensures 0.99, 0.001,
      \flteq(\result, -u*u*u / 6.0, 0.0000000422);
*/
float bsplines3(float u) {
	return -u*u*u / 6.0f;
}
