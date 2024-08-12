
/*@
  \flsmc::distribution x0, "Uniform", -2.0, 2.0;
  \flsmc::distribution x1, "Uniform", -2.0, 2.0;
  \flsmc::distribution x2, "Uniform", -2.0, 2.0;
  \flsmc::prob_ensures 0.99, 0.001,
  \flteq(\result, (0.7) * x2 - (1.3) * x1 + (1.1) * x0 + (1.4) * ((0.7) * x1 -
    (1.3) * x0 + (1.4) * (0.7 * x0)) - (0.7) * (0.7 * x0), 
    0.00000234);
*/
float filter3 (float x2, float x1, float x0) {
  float t1 = ((0.7f) * x0);
  return (0.7f) * x2 - (1.3f) * x1 + (1.1f) * x0 + (1.4f) * ((0.7f) * x1 -
    (1.3f) * x0 + (1.4f) * t1) - (0.7f) * t1;
}
