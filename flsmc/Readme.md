# FloStat

FloStat is a Frama-C plugin for statistically checking floating-point
rounding error. It compares executions of a C function using native
floating-point arithmetic with executions of a generated MPFR version.

## Build

Build with Dune from the plugin source directory:

```sh
cd src
dune build
```

FloStat requires Frama-C and the libraries listed in `src/dune` to be
installed in the active OCaml/Dune environment.

## Run

Run Frama-C from this directory, selecting the function whose ACSL contract
FloStat should check:

```sh
dune exec --root src -- frama-c \
  -main calculate -flostat -fs-execs 1000 \
  testfiles/nested_structs.c
```

`-main` must name an existing function with a FloStat contract. If
`-fs-out-dir DIR` is omitted, generated C files, the executable, samples, and
results are written to a new directory based on the input filename and time.
Useful options include:

- `-fs-execs N`: number of sampled executions (default: `10`).
- `-fs-prec N`: MPFR precision in bits (default: `256`).
- `-fs-out-dir DIR`: output directory.
- `-fs-sample-file FILE`: use a CSV file of input samples instead of drawing
  random samples. Columns must correspond to the contract's distributions.
- `-fs-only-sample`: generate samples without running the comparison.
- `-fs-more-stats`: also print minimum, maximum, and mean absolute measured
  differences; the default statistics output remains unchanged.

## Contracts

Attach uniform input distributions and one probability postcondition to the
selected function. The existing form takes a probability, a confidence level,
and a `\flteq` predicate:

```c
/*@
  \flostat::distribution input, "Uniform", 0.0, 1.0;
  \flostat::prob_ensures 0.99, 0.001,
    \flteq(\result, input + 2.0, 0.000001);
*/
float calculate(float input) {
  return input + 2.0f;
}
```

The probability and confidence arguments must be real constants. A shorter
rounding-error form is also supported; its reported confidence level defaults
to `0.95`:

```c
/*@
  \flostat::distribution input, "Uniform", 0.0, 1.0;
  \flostat::prob_ensures
    0.99,
    \round_error(\result) <= 0.00034;
*/
float calculate(float input) {
  return input * input;
}
```

`\round_error(x)` measures the absolute difference between the native
floating-point evaluation of `x` and its MPFR evaluation, equivalent to
`\abs(x - \real(x))`. The predicate currently supports `\round_error(x) <=
tolerance`. Both forms compare the requested probability of staying within
the tolerance. Distributions support `"Uniform"` with real-constant lower and
upper bounds, and `"Normal"` with a real-constant mean and standard deviation.

Use `\flostat::equation target, expression;` to define an input from other
sampled inputs. Equation expressions are evaluated in MPFR before either
program execution; each result is rounded once to `float`, then that same
rounded value is supplied to both the native and MPFR executions. This lets
you generate correlated inputs without including equation-evaluation rounding
in the measured function difference:

```c
/*@
  \flostat::distribution input.angle, "Uniform", -3.14159, 3.14159;
  \flostat::equation input.x, 0.01 * \cos(input.angle);
*/
```

Equation targets must be floating-point entry-point arguments and should not
also have distributions. The supported right-hand-side forms are floating
constants, entry-point argument fields, unary negation, `+`, `-`, `*`, `/`,
and one-argument `\sin(...)` / `\cos(...)`. Equations execute in declaration
order, so a later equation can use a target assigned by an earlier equation.
Only the distribution targets appear as columns in `samples.csv`; equation
targets are calculated after those columns have been read.

To sample a fresh value for every element of a fixed-size array, use an
inclusive ACSL range in the distribution target. Each expanded element becomes
its own sample column, and the full row is used for one execution:

```c
typedef struct {
  float values[100];
} inputs_t;

/*@
  \flostat::distribution inputs.values[0..99], "Uniform", 0.0, 1.0;
  \flostat::prob_ensures 0.99, 0.001,
    \flteq(\result, 0.0, 100.0);
*/
float sum_inputs(inputs_t inputs) {
  float sum = 0.0f;
  for (int i = 0; i < 100; i++) {
    sum += inputs.values[i];
  }
  return sum;
}
```

Range endpoints must be integer constants, and the target must be an lvalue
that FloStat can convert to a C array element. Bounds are inclusive, so
`[0..99]` expands to 100 independently sampled elements. MPFR arrays embedded
in structs are initialized element-by-element during comparison.

The `vesc/foc_observer_output.c` harness samples the motor's initial d/q
currents, speed, and electrical angle; motor parameters, sample period, and
voltage command are fixed for each run. It uses the electrical and mechanical
plant equations extracted into `vesc/vesc_virtual_motor_model.c` from
[VESC's virtual motor](https://github.com/vedderb/bldc/blob/master/motor/virtual_motor.c),
simulates 100 steps, and derives observer currents from the simulated motor
state. It does not run the VESC current controller or hardware/ADC simulation;
it is an equation-driven open-loop plant test with fixed pole-pair count, bus
voltage, and current limit.

`vesc/foc_observer_single_output.c` calls `foc_observer_update()` exactly once
with sampled voltage, current, and flux-angle inputs. The program derives the
observer flux state from that angle, current, and the fixed inductance and flux
linkage immediately before the observer call, so this setup arithmetic is
included in the rounding-error analysis. The timestep, observer gain, and
motor resistance, inductance, and flux linkage are fixed constants.
The observer mode is fixed to `FOC_OBSERVER_MXV_LAMBDA_COMP`, with saturation,
saliency, and temperature compensation disabled. Its initial estimated flux
linkage is set to the fixed motor flux linkage; it is not sampled.
The sampled voltage, current, and flux angle values are independent; this does
not model a complete controller-generated motor snapshot.
`vesc/foc_observer_mxv_lambda_comp_daisy.scala` is a Daisy-format one-update
specialization of the same mode and input setup.
For a smaller standalone presentation example of that mode, see
`vesc/paper_simple_example_mxv.c` (FloStat) and
`vesc/paper_simple_example_mxv_daisy.scala` (Daisy). Both use the same sampled
input ranges and fixed motor parameters.
The `paper_examples/` directory collects three matched FloStat/Daisy
presentations with independent alpha/beta input box limits of ±400 V and
±500 A; see its README for the examples and assumptions.

The `vesc/virtual_motor_observer_output.c` variant preserves the firmware-style
`virtual_motor_int_handler(v_alpha, v_beta)` loop. It includes the first
harness to reuse its observer implementation and the same extracted plant
model. The motor equations and inverse-Park/Clarke transforms have been
factored into `vesc/vesc_virtual_motor_model.c`, a parameterized extraction of
the matching sections in VESC's `motor/virtual_motor.c`; the source file marks
the original functions and identifies the hardware-dependent behavior left
out. The local handler mock calls that plant step, reconstructs ideal alpha/beta
current readings from simulated phase currents, updates the observer, and
supplies the next open-loop voltage command. The mock does not run VESC's ADC
hardware setup or current controller, and it omits ADC count quantization,
analog scaling, and sensor noise. Select `virtual_motor_harness` with `-main`
when running FloStat on this file.

Both harnesses initialize the persistent plant state through
`vesc_virtual_motor_init()`. It applies each sampled initial condition and
derives `id_integral` so the model's next d-axis update starts from the chosen
`id`; fixed motor parameters remain explicit in each harness.

## Supported C syntax and limitations

FloStat operates on the Frama-C C AST; source must first be accepted by the
installed Frama-C parser. The MPFR translator supports a subset of C, not every
valid C program:

- Floating-point arithmetic currently covers `+`, `-`, `*`, `/`, unary
  negation, and floating-point comparisons. Other operators or expression
  forms may be rejected or translated incorrectly.
- Implicit casts are not fully supported. FloStat prints a warning about this
  when it starts; use explicit, simple casts where possible.
- Transcendental-function translation is limited to the functions mapped in
  `src/mpfr_utils.ml`. Other library calls are not automatically given
  MPFR-equivalent behavior.
- Structs and nested structs containing floating-point fields are supported
  for the covered operations. Pointer-to-struct fields are supported in
  common cases, but arbitrary pointer aliasing, pointer arithmetic, and
  indirect memory patterns are not generally supported.
- Struct copies containing arrays require compatible, fixed-size arrays.
  Variable-length or otherwise non-constant array sizes are unsupported.
- A function contract must have a single behavior. Multiple behaviors,
  multiple probability clauses, predicates other than `\flteq`, and
  distribution kinds other than `"Uniform"` are unsupported.
- Contract terms are limited to the forms handled by the translator, such as
  constants, variables, `\result`, supported binary arithmetic, and
  `\old(...)`. Arbitrary field expressions and general ACSL logic are not
  supported.

Unsupported cases may stop with a diagnostic during translation or C
compilation. A successful run only checks the generated samples; it does not
establish correctness for inputs outside the sampled distribution.
