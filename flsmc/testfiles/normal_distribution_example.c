/*@
  \flostat::distribution input, "Normal", 0.25, 0.5;
  \flostat::prob_ensures
    0.99,
    \round_error(\result) <= 0.000001;
*/
float normal_input(float input) {
	return input;
}
