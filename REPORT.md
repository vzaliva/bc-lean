# bc-lean — AI-assisted semantics extraction report

This file records milestones in the project: what was requested, how it was
implemented, which model did the work, and how long it took. Intended as a
lab notebook for the experiment.

---

## Step 1 — Standalone tree-sitter parser (POSIX bc)

**Model:** Cursor Agent (Composer-2.5)  
**Duration:** ~45 minutes wall-clock for the full session (planning, plan
refinement, and implementation in one chat). The implementation burst itself
(files written and grammar iterated to green) was roughly **4 minutes** of
filesystem activity, with most time spent on grammar conflict resolution and
incremental test fixes.

### Rough prompt

> Start with a parser using tree-sitter. Set up a minimal tree-sitter layout
> (grammar, Makefile, root `config.json`; no full language bindings). Copy all
> POSIX-compatible tests from the GNU bc 1.07.1 source tree into a `tests/`
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
| Test corpus | `tests/Test/` (POSIX-compatible upstream files) |
| Regression script | `scripts/parse_all_tests.sh` |
| Docs | `README.md` (Parser section), `AGENTS.md`, `tests/README.md` |

**Out of scope (deferred):** Lean `Bc/Parser.lean`, XML→AST, evaluator, golden
output comparison against reference `bc`.

### Verification

```bash
make parser-all
# parse_all_tests: 37 passed, 0 failed (37 total)
```

Regression set: POSIX `.b` and `.bc` files under `tests/`. Shell
wrappers `tests/Test/signum` and `tests/Test/timetest` are copied for
provenance but excluded from parser regression.

**Toolchain:** tree-sitter CLI 0.25.10.

### Notable grammar work

Ground truth: GNU bc 1.07.1 `bc/bc.y` and `bc/scan.l`.

- Expression precedence with **chained** operators (`a / b * c`, etc.) via
  `repeat` on each precedence level.
- Significant newlines at top level; `statement_sequence` for semicolon-separated
  statements on one line.
- `\` **line continuation** as an extra.
- Multiline **strings** with embedded newlines (`testfn.b`, `checklib.b`).
- POSIX function definitions, autos, arrays, builtins, and special variables.
- No external `scanner.c` required — number continuations and line continuations
  handled in `grammar.js` extras/tokens.

Initial `tree-sitter generate` passed most of the corpus. The remaining
failures were fixed by chained multiplicative expressions, `\` line
continuation, and semicolon-separated statements inside function bodies.

### Next step (planned)

Wire the grammar into Lean: `tree-sitter parse -x` → AST in `Bc/`, then an
executable semantics/evaluator with golden tests against `/usr/bin/bc`.

---

## Step 2 — Parser code review (correctness & accuracy)

**Agent:** Cursor Agent (Claude Opus 4.8 1M)  
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
# parse_all_tests: 37 passed, 0 failed (37 total)   (no generate warnings)
```

Differential check vs `/usr/bin/bc` over POSIX snippets (precedence,
associativity, assignment chains, incr/decr placement, builtins, arrays) — **all
accept/reject verdicts now MATCH**, including the four cases above. Spot-checked
parse trees: `a<b<c` yields one flat `relational_expression` with two `rel_op`s;
`scale(5)` → `builtin_call`; `scale=3` → assignment with `special_variable` lhs.

### Known remaining gaps (deferred, not defects in scope)

- The parser is a recogniser only: the layered precedence grammar resolves
  associativity but the project does not yet validate `bc`'s *semantic*
  warnings (e.g. "comparison in assignment", "return requires parenthesis"),
  which `bc.y` raises as `ct_warn`/`yyerror` actions rather than grammar errors.
- No golden-output comparison yet (still planned for the evaluator step).

---

## Step 3 — Lean AST, tree-sitter bridge, and golden parse tests

**Agent:** Cursor Agent (Composer-2.5)  
**Duration:** ~30 minutes (AST modules, XML bridge, constraint checks, test harness,
goldens).

### Request

> Define Lean AST for bc, implement Lean wrapper parsing via tree-sitter, enforce
> bc.y expression-context constraints deferred in Step 2, golden AST tests
> (`.output` / `.fail`), `make test`, document as Step 3. Follow poison-lang
> patterns.

### Pipeline

`tree-sitter parse -x` → vendored `Bc.Xml` → `Bc.Parser` → `Bc.Constraints` →
`Bc.Pretty` (golden text).

| Module | Role |
|--------|------|
| `Bc/Xml/*` | XML parse (from poison-lang / Lean core) |
| `Bc/Syntax.lean` | Surface AST (`Program`, `Stmt`, `Expr`, …) |
| `Bc/Meta.lean` | `ExprInfo` flags mirroring `bc.y` bits |
| `Bc/Parser.lean` | tree-sitter subprocess + XML→AST |
| `Bc/Constraints.lean` | bc.y context checks (not operational semantics) |
| `Bc/Pretty.lean` | Stable pretty-printer for goldens |
| `Bc/ParseTestMain.lean` | `bc-parse-test` CLI |

Prior art: [poison-lang `LeanPoison/Parser.lean`](../poison-lang/LeanPoison/Parser.lean),
[`scripts/run_tests.sh`](../poison-lang/scripts/run_tests.sh).

### Expression-context constraints enforced

Hard errors in `Bc.Constraints` (via `ExprInfo`):

- Nested assignment RHS (`comparison in assignment`)
- `comparison in argument` / `comparison in subscript` (including builtins)
- `Comparison in first/third for expression`
- `Return outside of a function.`

**Deferred:** context-sensitive checks that depend on semantics rather than
tree-sitter syntax.

### Tests

```bash
make test              # alias for ast-test
make ast-test          # 27 cases: 22 corpus + 5 constraint failures
make ast-test-update   # refresh tests/ast-expected/
```

Layout:

- `tests/ast-expected/` — mirrors `tests/**` and `tests/constraints/`
- `tests/constraints/` — hand-written `.fail` fixtures
- `scripts/run_ast_tests.sh`, `scripts/update_ast_tests.sh`

### Verification

```bash
make parser-all   # 22/22 tree-sitter (unchanged)
make test         # 27 passed, 0 failed
make lean-build   # warning-clean
```

---

## Step 4 — Review and repair of Step 3 AST/constraint implementation

**Agent:** Codex (GPT-5.5 xhigh)  
**Duration:** ~20 minutes wall-clock, including a roughly **12 minute**
fix/retest loop.

### Request

Review the Step 3 implementation described in `REPORT.md`: inspect the Lean
source and test harnesses, run the relevant parser and AST tests, and consult
the GNU bc 1.07.1 reference source where behaviour is unclear. Fix any problems
found. Revisit the Step 3 **Deferred** note, decide which items should be fixed
now and which genuinely depend on future operational semantics, and record the
findings as Step 4 in this report, including timing, model, and prompt.

### Method

- Re-read the Step 3 modules (`Bc/Syntax.lean`, `Bc/Parser.lean`,
  `Bc/Constraints.lean`, `Bc/Pretty.lean`), test harnesses, and goldens.
- Re-ran the advertised targets. Initial `make parser-all` failed because Step 3
  negative fixtures were being included in the parser-only acceptance corpus.
- Checked the relevant GNU bc 1.07.1 actions in `bc-1.07.1/bc/bc.y` and string
  handling in `scan.l`/`execute.c`.
- Spot-checked current tree-sitter XML for `return(expr)` and reference
  behaviours for warning-only `ct_warn` cases versus hard `yyerror` cases.

### Findings and fixes

1. **Parser-only regression was broken by Step 3 fixtures.** `make parser-all`
   discovered `tests/constraints/parse-error.b`, which is intentionally invalid.
   Fixed `scripts/parse_all_tests.sh` to exclude `tests/constraints/`; parser
   regression is again the 22 upstream corpus files.
2. **AST harness discovered constraint fixtures twice and used basename-only temp
   files.** This caused duplicate output and could hide collisions. Fixed
   `scripts/run_ast_tests.sh` / `scripts/update_ast_tests.sh` to discover each
   test once and use path-derived temp names.
3. **`return(expr)` was parsed as `return; expr`.** The grammar allowed adjacent
   statements without semicolon/newline separation, both in `statement_sequence`
   and in block/function body items. Fixed the grammar so semicolon/newline
   separation is required, while allowing a final unterminated statement sequence
   before `}`. The deferred return parser note is therefore **fixed now**, not
   postponed.
4. **String literals were not represented accurately.** The XML conversion used
   trimmed XML character text, which included quote delimiters and could discard
   significant spaces/newlines. `Bc.Parser` now slices string spans from the
   original source and stores the literal body.
5. **Function metadata was over-modelled.** Later POSIX pruning simplified
   function definitions to the standard form.
6. **Hard errors were conflated with GNU bc warnings.** Nested assignment,
   comparison in builtin arguments, comparison in `for` init/update, and
   return-parenthesis/return-comparison are accepted by default GNU bc; many are
   `ct_warn` diagnostics only in strict/warning modes. Converted those fixtures
   to `.output` goldens. Kept hard failures for `yyerror`-style checks available
   without operational semantics: return outside a function and `break` outside
   a loop.
7. **Exponentiation AST associativity was wrong.** `^` is right-associative in
   `bc.y`; the XML bridge had been left-folding the flat tree-sitter node. Added
   a right fold for power expressions.
8. **Stale tree-sitter conflict declarations caused warnings.** Removed the now
   unnecessary conflict entries; `tree-sitter generate` is warning-free.

### Deferred decision

The return parsing part of the Step 3 deferred note was a grammar bug and is now
fixed. Return-parenthesis and return-comparison diagnostics should **not** be hard
parse failures for the GNU bc default semantics; they belong in a future
diagnostics/strict-standard mode if the project models `bc -s` / `bc -w`.

Definition-dependent call diagnostics should stay deferred until the project has
a function symbol table / operational semantics: GNU bc's behaviour depends on
function definitions and call resolution, not just local syntax.

### Verification

```bash
lake build
# Build completed successfully (24 jobs).

make parser-all
# parse_all_tests: 22 passed, 0 failed (22 total)

make test
# AST Test Summary: Passed: 33, Failed: 0, Skipped: 0
```

---

## Step 5 — Human-guided correction of parser scope and proof boundary

**Agent:** Codex (GPT-5.5 xhigh)  
**Duration:** ~40 minutes.

This step records a human-guided review of the Step 3/4 direction. The focus was
not a new feature, but correcting the project boundary before semantics work
starts: the parser should remain syntax-only, while semantic/context checks and
diagnostics should be postponed until the operational semantics are defined.

### Decisions enforced

1. **No type checker or constraint checker in the parser layer.** GNU bc is an
   untyped calculator language, so the project should not introduce a type
   checker. Context-sensitive checks such as `return` outside a function,
   `break` outside loops, and similar
   control-flow validity checks are not parser responsibilities. They are future
   semantics/context work.
2. **No `Bc.Diagnostics` layer yet.** Warning/strict-mode diagnostics are useful,
   but adding a separate diagnostics subsystem now would be premature. The
   current parser should only reject malformed syntax.
3. **Use the POSIX/standard syntax subset for reference checks.** Documentation
   now says to use `bc -s -c` for reference syntax testing, adding `-l` only
   when libmath is needed.
4. **Separate syntax tests from future semantics fixtures.** The old
   `tests/constraints/` role was removed. The syntactically malformed fixture was
   moved to `tests/parse-invalid/`; context/semantic fixtures were moved to
   `tests/semantics/` and are not exercised by parser or AST tests.
5. **Keep the proof/model surface total.** `partial` is disallowed in
   `Bc/Syntax.lean`, future operational semantics, and functions/predicates that
   AST or semantic definitions will reference. `partial` remains acceptable in
   non-verified infrastructure: parser/XML conversion and golden-test
   pretty-printing.

### Implementation changes

- Removed the current constraint-checking path from `Bc/Parser.lean`.
- Deleted `Bc/Constraints.lean` and `Bc/Meta.lean`; their checks are deferred
  until there is a semantics/context layer.
- Updated parser and AST test scripts so `tests/semantics/` is skipped, while
  `tests/parse-invalid/` remains available for malformed syntax failures.
- Updated `README.md`, `AGENTS.md`, and `tests/README.md` to document syntax-only
  parser scope, `bc -s -c` reference testing, the semantics-fixture directory,
  and the clarified partial-function rule.
- Audited current partial-function use. Remaining partials are confined to
  `Bc/Parser.lean`, `Bc/Xml/*`, and `Bc/Pretty.lean`; none are present in
  `Bc/Syntax.lean` or the current executable entry point.

### Verification

```bash
lake build
# Build completed successfully (20 jobs).

make test
# AST Test Summary: Passed: 38, Failed: 0, Skipped: 0

make parser-all
# parse_all_tests: 37 passed, 0 failed (37 total)
```

---

## Step 6 — Big-step operational semantics and definitional interpreter

**Agent:** Codex (GPT-5.5 xhigh)  
**Duration:** ~2 hours wall-clock, including reference-source inspection,
poison-lang comparison, implementation, and regression testing.

### Request

Implement the next project step: a big-step operational semantics for POSIX bc
that can also run as the definitional interpreter. Use poison-lang as
inspiration for an executable, `IO`-based evaluator. Do not use `partial`
functions in the semantics. Faithfully implement bc semantics for the POSIX
syntax and add tests that run fixtures through the interpreter and compare
outputs against the GNU `bc` command.

### Reference material

- GNU bc 1.07.1 source under `bc-1.07.1/`, especially `bc/execute.c`,
  `bc/storage.c`, `lib/number.c`, `bc/bc.y`, and `bc/libmath.b`.
- Current poison-lang checkout at commit
  `f052d113586f742417c89438a346626720ce66c2`; `LeanPoison/BigStep.lean`
  was used as an `IO`-based big-step evaluator reference.
- Live `bc --version`: GNU bc 1.07.1.

### Deliverables

| Area | Location |
|------|----------|
| Big-step evaluator | `Bc/Eval.lean` |
| CLI runner | `Main.lean` (`bc-lean [--fuel N] [-l|--mathlib] file...`) |
| Eval regression harness | `scripts/run_eval_tests.sh` |
| Make target | `make eval-test`; `make test` now runs AST + eval tests |

### Semantics implemented

- Total, fuel-bounded mutually recursive semantic functions; no `partial`,
  `sorry`, or axioms in `Bc/Eval.lean`.
- Runtime state for globals, stacked function frames, autos, arrays, function
  definitions, `ibase`, `obase`, `scale`, output, and stop state.
- Executable decimal number model with bc-style scale rules for addition,
  subtraction, multiplication, division, modulo, exponentiation, square root,
  input-base parsing, output-base rendering, and 70-column output wrapping.
- Statements and control flow: expression output rules, strings, blocks, `if`,
  `while`, `for`, `break`, `return`, and `quit`.
- Functions: dynamic definitions, parameters, autos, recursion, call-by-value
  scalar and array parameters.
- Builtins: `length`, `scale`, and `sqrt`.
- `-l` / `--mathlib` CLI mode preloads `bc-1.07.1/bc/libmath.b`, matching the
  reference tests that depend on `s`, `c`, `a`, `l`, `e`, and `j`.

### Tests

`scripts/run_eval_tests.sh` discovers checked-in POSIX corpus files, builds the
interpreter once when needed, runs the compiled `bc-lean` executable, runs the
same file through GNU `bc`, and diffs stdout. The harness runs tests in
parallel by default, supports `-j` / `--jobs` to cap concurrency, and reports
progress as each worker finishes (`[done/total]`). Math-library fixtures are
run with `-l` on both sides.

`make test` now runs both:

1. AST golden tests (`scripts/run_ast_tests.sh`)
2. Eval reference comparisons (`scripts/run_eval_tests.sh`)

### Verification

```bash
lake build
# Build completed successfully (22 jobs).

make eval-test
# Eval Test Summary:
# Passed: 37
# Failed: 0
# Skipped: 0

make test
# AST Test Summary:
# Passed: 38
# Failed: 0
# Skipped: 0
#
# Eval Test Summary:
# Passed: 37
# Failed: 0
# Skipped: 0
```

### Notes and limitations

The evaluator is intended as an executable semantics, not a diagnostics layer.
It reports runtime errors for invalid control-flow/runtime cases but does not
attempt to reproduce every `bc -s` / `bc -w` compile-time warning. The decimal
number implementation was validated against the checked-in reference corpus,
including heavy arithmetic and libmath tests, but it remains a Lean model rather
than a direct binding to GNU bc's `lib/number.c`.
