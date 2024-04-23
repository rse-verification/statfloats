// typedef struct {
//     float phaseA;
//     float phaseB;
//     float phaseC;
// } Current;

float phaseA;
float phaseB;
float phaseC;

/*@
  ensures \result == \sin(x);
*/
float sinf(float x);

/*
    requires 0 <= c.phaseA <= 2*3.14 &&
             0 <= c.phaseB <= 2*3.14 &&
             0 <= c.phaseC <= 2*3.14;
             ensures \result == \sin(c.phaseA + c.phaseB + c.phaseC);
    // ensures \Prob(|\result - \sin(c.phaseA + c.phaseB + c.phaseC)| >= DIFF) >= 0.99;
*/
float calcTorque(float phA, float phB, float phC) {
    float c_sum = phA;
    c_sum = c_sum + phB;
    c_sum = c_sum + phC;
    float torque = sinf(c_sum);
    return torque;
}
