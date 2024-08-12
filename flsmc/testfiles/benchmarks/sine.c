
/*@
  \flsmc::distribution x, "Uniform", -1.57079632679, 1.57079632679;
  \flsmc::prob_ensures 0.99, 0.001,
	\flteq(\result, x - (x*x*x)/6.0 + (x*x*x*x*x)/120.0 -
		(x*x*x*x*x*x*x)/5040.0, 0.000000237);
*/
float sine(float x) {
    // require(x > -1.57079632679 && x < 1.57079632679)
    return x - (x*x*x)/6.0f + (x*x*x*x*x)/120.0f -
			(x*x*x*x*x*x*x)/5040.0f;
}
