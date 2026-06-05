# bc reference test programs

Copied from GNU bc 1.07.1 (`bc-1.07.1/Test/` and `bc-1.07.1/Examples/`).
Same license as GNU bc (GPL-3.0-or-later).

## Layout

- `Test/` — regression scripts from the upstream tarball
- `Examples/` — sample programs (pi digits, primes, etc.)
- `parse-invalid/` — deliberately malformed parser fixtures
- `semantics/` — future context/semantic fixtures, not used by parser tests

## Parser regression

All upstream corpus `Test/` and `Examples/` `.b`/`.bc` files are parsed by
`make parser-test` (tree-sitter). `tests/parse-invalid/` and `tests/semantics/`
are excluded from parser acceptance tests.

**Excluded from parser regression** (not bc source):

- `Test/signum` — shell wrapper around a bc script
- `Test/timetest` — shell benchmark script

## Reference bc binary

Many `Test/` programs need libmath. To run with the system GNU bc:

```bash
bc -s -c -l tests/Test/array.b
bc -s -c -l tests/Examples/pi.b
```

Use `bc -s -c` without `-l` when libmath is not required. Parser development only
needs standard syntax acceptance (non-zero exit / error message means invalid
standard bc input).

## Lean AST regression

After `make lean-build` and `make parser`:

```bash
make test                 # corpus files + tests/parse-invalid/ fixtures
make ast-test-update      # rewrite tests/ast-expected/ from current parser
```

Golden files mirror paths under `tests/` (e.g. `tests/ast-expected/Test/array.b.output`).
Parser-invalid fixtures use matching `.fail` files under
`tests/ast-expected/parse-invalid/`. Fixtures under `tests/semantics/` are kept
for later semantics/context work and are not exercised by parser or AST tests.

## Ground truth for grammar

When parsing behaviour is unclear, consult locally (not committed):

- `bc-1.07.1/bc/bc.y` — yacc grammar
- `bc-1.07.1/bc/scan.l` — lexer
- `bc-1.07.1/doc/bc.texi` — language manual
