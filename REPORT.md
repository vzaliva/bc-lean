# bc-lean — AI-assisted semantics extraction report

This file records milestones in the project: what was requested, how it was
implemented, which model did the work, and how long it took. Intended as a
lab notebook for the experiment.

---

## Step 1 — Standalone tree-sitter parser (GNU bc 1.07.1)

**Date:** 4 June 2026  
**Model:** Cursor Agent (Composer)  
**Duration:** ~45 minutes wall-clock for the full session (planning, plan
refinement, and implementation in one chat). The implementation burst itself
(files written and grammar iterated to green) spanned roughly **15:56–16:00
PDT** (~4 minutes of filesystem activity), with most time spent on grammar
conflict resolution and incremental test fixes.

### Rough prompt

> Start with a parser using tree-sitter. Set up a minimal tree-sitter layout
> (grammar, Makefile, root `config.json`; no full language bindings). Copy all
> unit tests from `bc-1.07.1/Test/` and `bc-1.07.1/Examples/` into a `tests/`
> folder and use them to regression-test the parser. Develop a tree-sitter grammar
> that correctly parses all `.b`/`.bc` test files; verify with `tree-sitter
> generate` and `tree-sitter parse --stat`. **No Lean integration** — parser
> only, standalone. Consult `bc-1.07.1` (`bc.y`, `scan.l`, `doc/bc.texi`) and
> `/usr/bin/bc` when parsing behaviour is unclear.

(The prompt was refined over several plan iterations: drop Lean/XML wiring,
confirm minimal tree-sitter infra, add reference-source and live-`bc`
disambiguation workflow.)

### Deliverables

| Area | Location |
|------|----------|
| Grammar source | `parser/tree-sitter-bc/grammar.js` (~360 lines) |
| Generated parser | `parser/tree-sitter-bc/src/` (`grammar.json`, `parser.c`, `node-types.json`) |
| Build | `parser/Makefile`, root `Makefile` targets `parser`, `parser-test`, `parser-all` |
| Test corpus | `tests/Test/` (18 files from upstream), `tests/Examples/` (4 files) |
| Regression script | `scripts/parse_all_tests.sh` |
| Docs | `README.md` (Parser section), `AGENTS.md`, `tests/README.md` |

**Out of scope (deferred):** Lean `Bc/Parser.lean`, XML→AST, evaluator, golden
output comparison against reference `bc`.

### Verification

```bash
make parser-all
# parse_all_tests: 22 passed, 0 failed (22 total)
```

Regression set: all `tests/**/*.b` and `tests/**/*.bc` (22 files). Shell
wrappers `tests/Test/signum` and `tests/Test/timetest` are copied for
provenance but excluded from parser regression.

**Toolchain:** tree-sitter CLI 0.25.10.

### Notable grammar work

Ground truth: GNU bc 1.07.1 `bc/bc.y` and `bc/scan.l`.

- Expression precedence with **chained** operators (`a / b * c`, etc.) via
  `repeat` on each precedence level.
- Significant newlines at top level; `statement_sequence` for semicolon-separated
  statements on one line.
- `\` **line continuation** as an extra (needed for `mul.b`, `twins.b`).
- Multiline **strings** with embedded newlines (`testfn.b`, `checklib.b`).
- GNU extensions: `if`/`else`, `&&`/`||`, `print`, `define`/`auto`, array
  params (`*a[]`, `&a[]`), builtins, pseudo-variables.
- No external `scanner.c` required — number continuations and line continuations
  handled in `grammar.js` extras/tokens.

Initial `tree-sitter generate` passed 17/22 tests; five failures
(`pi.b`, `twins.b`, `checklib.b`, `mul.b`, `testfn.b`) were fixed by
chained multiplicative expressions, `\` line continuation, and
semicolon-separated statements inside function bodies.

### Next step (planned)

Wire the grammar into Lean: `tree-sitter parse -x` → AST in `Bc/`, then an
executable semantics/evaluator with golden tests against `/usr/bin/bc`.
