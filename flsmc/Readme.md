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

## Contracts

Attach uniform input distributions and one probability postcondition to the
selected function:

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

The probability and confidence arguments must be real constants. The
postcondition currently supports `\flteq(result, reference, tolerance)`.
Distributions currently support `"Uniform"` with real-constant lower and
upper bounds.

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
