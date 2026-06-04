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

---

## Step 2 — Parser code review (correctness & accuracy)

**Date:** 4 June 2026  
**Agent:** Cursor Agent (Claude Opus 4.8)  
**Duration:** ~30 minutes (review, differential testing against `/usr/bin/bc`,
grammar fixes, re-verification).

### Request

> We have implemented a tree-sitter parser (Step 1). Examine the current
> implementation, run the tests, make sure it is correct and accurate, and
> document the work in `REPORT.md` as Step 2.

### Method

1. **Re-ran the regression** (`make parser-all`): 22/22 green, but it only greps
   `tree-sitter parse --stat` output for `error`.
2. **Hardened the pass criterion**: parsed every corpus file with the full tree
   printer and confirmed **no `ERROR`, `MISSING`, or `UNEXPECTED` nodes** — the
   22 files parse cleanly, not merely via error recovery. Also verified the
   regression harness *does* flag failures (deliberately malformed input → exit
   1 with an `ERROR` node).
3. **Differential testing against the reference `bc` 1.07.1** (`/usr/bin/bc`):
   wrote a harness that classifies each snippet as accept/reject in both the
   real `bc` and the tree-sitter grammar, then compared. Ground truth for the
   grammar rules: `bc-1.07.1/bc/bc.y` (precedence table at `bc.y:110–119` and
   the `expression`/`named_expression` rules).

### Findings (3 accuracy defects + 1 warning)

| # | Issue | Real `bc` | Old grammar |
|---|-------|-----------|-------------|
| 1 | Chained relational `a<b<c`, `1<2==3` (`REL_OP` is `%left` in `bc.y`) | accept | **reject** |
| 2 | Unary plus `+5` (only unary `-` exists in `bc.y:626`) | reject | **accept** |
| 3 | `++`/`--` on non-lvalues (`5++`, `++5`, `f(x)++`; `bc.y` requires `named_expression`) | reject | **accept** |
| 4 | `tree-sitter generate` emitted `unnecessary conflicts: special_variable, builtin_call` | — | warning |

Defect #1 is the most serious: the parser **rejected valid `bc` programs**.
#2/#3 were over-permissiveness (accepting invalid input). #4 violates the
project's "no warnings" standard.

### Fixes (`parser/tree-sitter-bc/grammar.js`)

- **Chained relational**: `relational_expression` now uses
  `prec.left(5, seq(additive, repeat(seq(rel_op, additive))))` — the same
  left-chaining pattern as the additive/multiplicative levels — instead of a
  single `additive rel_op additive`.
- **Unary plus removed**: the sign operator is now `"-"` only (was
  `choice("+","-")`).
- **Incr/decr lvalue restriction**: prefix and postfix `++`/`--` operands
  changed from `postfix_expression`/`primary_expression` to `named_expression`,
  matching `bc.y`. This needed a new GLR conflict
  `[$.primary_expression, $.named_expression]` (an `identifier` followed by
  `++` can reduce either way; tree-sitter resolves it dynamically).
- **Unnecessary conflict removed**: dropped the stale
  `[$.special_variable, $.builtin_call]` entry. `scale(…)` still parses as
  `builtin_call` and bare `scale` as `special_variable`.

`tree-sitter generate` is now **warning-free**.

### Verification

```bash
make parser-all
# parse_all_tests: 22 passed, 0 failed (22 total)   (no generate warnings)
```

Differential check vs `/usr/bin/bc` over ~30 snippets (precedence, associativity,
assignment chains, incr/decr placement, builtins, `read()`, arrays) — **all
accept/reject verdicts now MATCH**, including the four cases above. Spot-checked
parse trees: `a<b<c` yields one flat `relational_expression` with two `rel_op`s;
`scale(5)` → `builtin_call`; `scale=3` → assignment with `special_variable` lhs.

### Known remaining gaps (deferred, not defects in scope)

- The parser is a recogniser only: the layered precedence grammar resolves
  associativity but the project does not yet validate `bc`'s *semantic*
  warnings (e.g. "comparison in assignment", "return requires parenthesis"),
  which `bc.y` raises as `ct_warn`/`yyerror` actions rather than grammar errors.
- No golden-output comparison yet (still planned for the evaluator step).
