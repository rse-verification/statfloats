/*@
  \flsmc::distribution x1, "Uniform", -15.0, 15.0;
	\flsmc::distribution x2, "Uniform", -15.0, 15.0;
	\flsmc::distribution x3, "Uniform", -15.0, 15.0;
	\flsmc::prob_ensures 0.99, 0.001,
	\flteq(\result, 2*(x1*x2*x3) + (3*x3*x3) - x2*(x1*x2*x3) + (3*x3*x3) - x2, 0.0196);
*/
float rigidBody2(float x1, float x2, float x3) {
	float t1 = x1*x2*x3;
	float t2 = 3.0f*x3*x3;
	return 2.0f*(t1) + t2 - x2*(t1) + t2 - x2;
}
