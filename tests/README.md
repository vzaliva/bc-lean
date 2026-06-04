# bc reference test programs

Copied from GNU bc 1.07.1 (`bc-1.07.1/Test/` and `bc-1.07.1/Examples/`).
Same license as GNU bc (GPL-3.0-or-later).

## Layout

- `Test/` — regression scripts from the upstream tarball
- `Examples/` — sample programs (pi digits, primes, etc.)

## Parser regression

All `**/*.b` and `**/*.bc` files are parsed by `make parser-test` (tree-sitter).

**Excluded from parser regression** (not bc source):

- `Test/signum` — shell wrapper around a bc script
- `Test/timetest` — shell benchmark script

## Reference bc binary

Many `Test/` programs need libmath. To run with the system GNU bc:

```bash
bc -l tests/Test/array.b
bc -l tests/Examples/pi.b
```

Use plain `bc` when libmath is not required. Parser development only needs syntax
acceptance (non-zero exit / error message means invalid bc input).

## Ground truth for grammar

When parsing behaviour is unclear, consult locally (not committed):

- `bc-1.07.1/bc/bc.y` — yacc grammar
- `bc-1.07.1/bc/scan.l` — lexer
- `bc-1.07.1/doc/bc.texi` — language manual
