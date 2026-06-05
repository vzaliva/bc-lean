# Eval-only reference tests

These fixtures are run by `scripts/run_eval_tests.sh` and are intentionally not
part of the Lean AST golden corpus.

- `gnu/` contains GNU bc 1.07.1 reference fixtures that are useful for evaluator
  coverage but are not picked up by the AST test layout.
- `local/` contains small focused POSIX bc programs written for this project.

Input-driven tests may provide a sidecar named either `program.stdin` or
`program.b.stdin`; the eval harness feeds that file to both GNU `bc` and
`bc-lean`.
