# Eval-only reference tests

These fixtures are run by `scripts/run_eval_tests.sh` and are also parsed by the
Lean AST golden tests.

- `gnu/` contains GNU bc 1.07.1 reference fixtures that are useful for evaluator
  coverage but are not picked up by the AST test layout.
- `local/` contains small focused POSIX bc programs written for this project.
