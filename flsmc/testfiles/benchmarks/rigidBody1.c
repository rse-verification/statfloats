/*@
  \flostat::distribution x1, "Uniform", -15.0, 15.0;
	\flostat::distribution x2, "Uniform", -15.0, 15.0;
	\flostat::distribution x3, "Uniform", -15.0, 15.0;
	\flostat::prob_ensures 0.99, 0.001,
	\flteq(\result, -x1 * x2 - 2.0*x2*x3 - x1 - x3, 0.000158);
*/
float rigidBody1(float x1, float x2, float x3) {
	return -x1 * x2 - 2.0f*x2*x3 - x1 - x3;
}
