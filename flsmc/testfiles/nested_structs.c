struct inner {
  float value;
};

struct outer {
  int tag;
  struct inner nested;
  float value;
};

struct wrapper {
  struct outer content;
};

/*@
  \flostat::distribution input, "Uniform", 0.0, 1.0;
  \flostat::prob_ensures 0.99, 0.001,
    \flteq(\result, input + 2.0, 0.000001);
*/
float calculate(float input) {
  struct wrapper source;
  struct wrapper value;
  source.content.nested.value = input;
  source.content.value = 2.0f;
  value = source;
  return value.content.nested.value + value.content.value;
}
