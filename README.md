# bc-lean

An experiment in **AI-assisted semantics extraction**: deriving complete,
executable formal semantics for an existing language from its implementation
source, test cases, and sample runs, with the work driven by an AI agent.

The target language is the POSIX bc subset, checked against
[GNU bc](https://www.gnu.org/software/bc/) **1.07.1** as the reference
implementation. The semantics are formalised in
[Lean 4](https://leanprover.github.io/).

## Scope

This project models bc's **operational semantics** as an executable Lean
interpreter. There is no type checker — bc is an untyped arbitrary-precision
calculator language, so the formalisation is an evaluator that runs `.bc`
programs. The current parser work targets the POSIX/standard subset; use
`bc -s -c` when comparing syntax acceptance against the reference implementation.

The reference implementation (`bc-1.07.1/`) is unpacked locally for consultation
but is not part of this repository.

## Semantics and metatheory

Two independent operational semantics are provided, both executable and
fuel-bounded, and both cross-checked against GNU bc by `make eval-test`:

- **Big-step** (`Bc/BigStep.lean`) — a recursive evaluator.
- **Small-step** (`Bc/SmallStep.lean`) — a structural one-step function
  `step : Config → StepResult` over source-shaped residual terms, with fuel only
  in the runner.

Shared, semantics-agnostic logic (numeric operators, assignment, builtins, and
`quit` detection) lives in `Bc/Runtime.lean` so the two evaluators cannot drift
on those points.

**What is currently proved** (`Bc/Progress.lean`): the small-step transition
relation has no stuck configurations — every configuration is either terminal
(normal completion, propagated control, or a runtime error) or can take a step,
and terminal configurations coincide with normal forms. Note this is established
*by construction*: the relation is defined as the graph of the total function
`step`, so the result certifies that `step` is total and its outcomes are
exhaustively classified, rather than a Wright–Felleisen "well-typed programs do
not get stuck" theorem (bc is untyped).

**Not yet proved** (intended future metatheory): equivalence of the big-step and
small-step semantics; adequacy of `step` against an independently-defined
inductive reduction relation; and algebraic/canonical-form metatheory for the
`Num` arbitrary-precision type.

## Parser (tree-sitter)

A standalone tree-sitter grammar for POSIX bc surface syntax lives under
`parser/`. It does not require Lean or Lake — only the [tree-sitter
CLI](https://tree-sitter.github.io/tree-sitter/cli) (**0.25.x** recommended).

### Build and test

```bash
make parser          # generate + build grammar; writes config.json
make parser-test     # parse the upstream valid corpus
make parser-all      # both of the above
```

Manual checks:

```bash
tree-sitter parse examples/hello.bc --config-path config.json --stat
tree-sitter parse tests/Test/array.b --config-path config.json
```

Generated artifacts are committed under `parser/tree-sitter-bc/src/` (`grammar.json`,
`parser.c`, `node-types.json`). After editing `grammar.js`, run `make parser` and
review the diff in `src/grammar.json` if needed.

### Test corpus

Reference programs copied from GNU bc 1.07.1 are under `tests/` — see
[tests/README.md](tests/README.md).

### Grammar reference

When parsing behaviour is unclear, consult the local reference tree (not
committed): `bc-1.07.1/bc/bc.y`, `bc-1.07.1/bc/scan.l`, and
`bc-1.07.1/doc/bc.texi`. The system `/usr/bin/bc` binary can confirm that a
snippet is accepted as valid standard bc input (`bc -s -c file.b`; add `-l` for
libmath-heavy tests when needed).

## Building

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (managed via
  `elan`; the toolchain is pinned in `lean-toolchain`)

### Build

```bash
make
```

The project has **no external Lean dependencies** — it uses only the Lean
toolchain's `Std` library and core tactics — so there is nothing to download and
`make` simply runs `lake build`. To force a clean rebuild (e.g. after a toolchain
bump):

```bash
make cache-refresh   # equivalent to `lake clean`
```

### Run

```bash
# Run a bc program
make run BC=examples/hello.bc
lake exe bc-lean --semantics small examples/hello.bc

# Parse to AST (golden test CLI)
lake exe bc-parse-test tests/Test/array.b

# AST golden tests plus big-step and small-step evaluator comparisons
make test
```

## AST parse tests

Lean parses `.b`/`.bc` files via tree-sitter XML (`Bc/Parser.lean`), builds a
surface AST (`Bc/Syntax.lean`), and pretty-prints it for regression. The parser
is intentionally syntax-only; context and semantic checks are postponed.

```bash
make test              # AST tests + big-step and small-step eval tests
make ast-test          # AST tests only
make eval-test         # eval tests with both semantics
make eval-test-big     # eval tests with big-step semantics
make eval-test-small   # eval tests with small-step semantics
make ast-test-update   # refresh tests/ast-expected/ after intentional AST changes
```

Expected outputs live under `tests/ast-expected/`. Deliberately malformed parser
fixtures live under `tests/parse-invalid/`; future context/semantic fixtures live
under `tests/semantics/` and are not exercised by parser or AST tests.

## Project Structure

- `parser/`          — tree-sitter grammar (`parser/tree-sitter-bc/`)
- `tests/`           — POSIX bc reference programs and parser/semantic fixtures
- `Bc/`            — surface AST, parser bridge, runtime helpers, and semantics
- `Main.lean`      — interpreter entry point
- `lakefile.lean`  — Lake build configuration
- `Makefile`       — convenience targets (build, cache, run, clean)
- `bc-1.07.1/`     — unpacked GNU bc reference source (not committed)

## License

This project is licensed under the GNU General Public License v3.0 — the same
license as GNU bc. See the [LICENSE](LICENSE) file for details.
