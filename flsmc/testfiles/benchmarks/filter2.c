
/*@
  \flostat::distribution x0, "Uniform", -2.0, 2.0;
  \flostat::distribution x1, "Uniform", -2.0, 2.0;
  \flostat::prob_ensures 0.99, 0.001,
		\flteq(\result, 0.7 * x1 - 1.3 * x0 + 1.4f * (0.7 * x0), 0.000000793);
*/
float filter2 (float x1, float x0) {
    return (0.7f) * x1 - (1.3f) * x0 + (1.4f) * ((0.7f) * x0);
}
