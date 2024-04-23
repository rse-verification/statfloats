typedef struct {
    float phaseA;
    float phaseB;
    float phaseC;
} Current;


/*@
  ensures \result == \sin(x);
*/
float sinf(float x);

/*@
    requires 0 <= c.phaseA <= 2*3.14 &&
             0 <= c.phaseB <= 2*3.14 &&
             0 <= c.phaseC <= 2*3.14;
             ensures \result == \sin(c.phaseA + c.phaseB + c.phaseC);
    // ensures \Prob(|\result - \sin(c.phaseA + c.phaseB + c.phaseC)| >= DIFF) >= 0.99;
*/
float calcTorque(Current c) {
    float c_sum = c.phaseA;
    c_sum += c.phaseB;
    c_sum += c.phaseC;
    float torque = sinf(c_sum);
    return torque;
}
