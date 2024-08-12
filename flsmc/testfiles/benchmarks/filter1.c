
/*@
  \flsmc::distribution x0, "Uniform", -2.0, 2.0;
  \flsmc::prob_ensures 0.99, 0.001,
		\flteq(\result, 0.7 * x0 , 0.000000125);
*/
float filter1 (float x0) {
    // require(-2 <= x0 && x0 <= 2)
    return 0.7f * x0;
}
