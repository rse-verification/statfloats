int output;

void square_8bit(int x) {
  output = x * x;
}


/*@
  requires input * input <= 128;
  ensures output == -(\old(input) * \old(input));
*/
void neg_square_8bit(int input) {
  square_8bit(input);
  output = -output;
}
