
/*@
  \flsmc::distribution x0, "Uniform", -2.0, 2.0;
  \flsmc::distribution x1, "Uniform", -2.0, 2.0;
  \flsmc::distribution x2, "Uniform", -2.0, 2.0;
  \flsmc::distribution x3, "Uniform", -2.0, 2.0;
  \flsmc::prob_ensures 0.99, 0.001,
  \flteq(\result, (0.7f) * x3 - (1.3f) * x2 + (1.1f) * x1 + (1.4f) *
    ((0.7f) * x2 - (1.3f) * x1 + (1.1f) * x0 + (1.4f) * ((0.7f) * x1 - (1.3f) *
    x0 + (1.4f) * ((0.7f) * x0)) - (0.7f) *
    ((0.7f) * x0)) - (0.7f) * ((0.7f) * x1 - (1.3f) * x0 + (1.4f) * ((0.7f) * x0)),
    0.00000415);
*/
float filter4 (float x3, float x2, float x1, float x0) {
  float t1 = (0.7f) * x1 - (1.3f) * x0 + (1.4f) * ((0.7f) * x0);
  return (0.7f) * x3 - (1.3f) * x2 + (1.1f) * x1 + (1.4f) *
    ((0.7f) * x2 - (1.3f) * x1 + (1.1f) * x0 + (1.4f) * (t1) - (0.7f) *
    ((0.7f) * x0)) - (0.7f) * (t1);
}
