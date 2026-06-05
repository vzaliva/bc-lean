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

---

## Step 6 — Big-step operational semantics and definitional interpreter

**Agent:** Codex (GPT-5.5 xhigh)  
**Duration:** ~2 hours wall-clock, including reference-source inspection,
poison-lang comparison, implementation, and regression testing.

### Request

Implement the next project step: a big-step operational semantics for POSIX bc
that can also run as the definitional interpreter. Use poison-lang as
inspiration for an executable evaluator. Do not use `partial` functions in the
semantics. Faithfully implement bc semantics for the POSIX syntax and add tests
that run fixtures through the interpreter and compare outputs against the GNU
`bc` command.

### Reference material

- GNU bc 1.07.1 source under `bc-1.07.1/`, especially `bc/execute.c`,
  `bc/storage.c`, `lib/number.c`, `bc/bc.y`, and `bc/libmath.b`.
- Current poison-lang checkout at commit
  `f052d113586f742417c89438a346626720ce66c2`; `LeanPoison/BigStep.lean`
  was used as a big-step evaluator reference.
- Live `bc --version`: GNU bc 1.07.1.

### Deliverables

| Area | Location |
|------|----------|
| Runtime and numeric helpers | `Bc/Runtime.lean` |
| Big-step evaluator | `Bc/BigStep.lean` |
| CLI runner | `Main.lean` (`bc-lean [--fuel N] [--semantics big|small] [-l|--mathlib] file...`) |
| Eval regression harness | `scripts/run_eval_tests.sh` |
| Make target | `make eval-test`; `make test` now runs AST + eval tests |

### Semantics implemented

- Total, fuel-bounded mutually recursive semantic functions; no `partial`,
  `sorry`, or axioms in `Bc/BigStep.lean`.
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

---

## Step 7 — Human-guided POSIX consolidation and evaluator cleanup

**Agent:** Codex (GPT-5.5 xhigh)  
**Duration:** ~1.5 hours.

This step records the human-guided follow-up after the initial evaluator landed.
The work tightened the project boundary and improved confidence in the
definitional interpreter.

### Changes

1. **Added more evaluator tests.** Imported a curated BSD-licensed subset of
   Gavin Howard's bc tests under `tests/external/gavin-bc/posix/`, added license
   and provenance notes, and wired those fixtures into the evaluator comparison
   harness and AST golden coverage.
2. **Restricted the project to POSIX bc.** Pruned the AST, tree-sitter grammar,
   XML bridge, pretty-printer, evaluator, docs, and fixtures so the checked-in
   project models only the POSIX subset. Removed stale test files and generated
   goldens for syntax and behavior outside that scope, regenerated parser
   artifacts, and refreshed AST expected output.
3. **Removed `IO` from the semantics.** After POSIX pruning removed input and
   nondeterministic effects from the language model, `Bc.BigStep` was refactored so
   semantic functions return `Result` / `RunResult` directly. `IO` remains only
   in the CLI/parser layer for file access and output.

---

## Step 8 — Small-step operational semantics

**Agent:** Codex (GPT-5.5 xhigh)
**Duration:** ~30 min.

### Request

Add a pure small-step operational semantics in `Bc/SmallStep.lean`, with a
fuel-bounded evaluator that repeatedly steps until termination or fuel
exhaustion. Update the evaluator test runner so tests can select which semantics
to use, and update Make targets so evaluator tests run against both semantics.
The implementation follows the small-step idea from Software Foundations'
Programming Language Foundations chapter on small-step semantics:
`https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html`.

### Implementation

- Added `Bc/SmallStep.lean`, a pure control-machine semantics with explicit
  `Task` continuations, a `Config`, a single-step function, and a fuel-bounded
  `runConfig` / `runProgramWithState`.
- Small-step execution reduces top-level items, statement lists, bodies, blocks,
  loops, `break`, `return`, and `quit` through explicit control steps.
  Expression, function-body, statement, and top-level transitions are local to
  `Bc.SmallStep`; it does not import or delegate to `Bc.BigStep`.
- Shared code is limited to `Bc.Runtime`: numeric operations, runtime state,
  result/control datatypes, output helpers, and environment update helpers.
  This is intentional because bc expressions can mutate state and call
  functions, so expression evaluation belongs to each concrete semantics.
- Added CLI selection in `Main.lean`: `--semantics big|small`, plus
  `--big-step` and `--small-step`.
- Extended `scripts/run_eval_tests.sh` with `--semantics big|small` and the
  `BC_LEAN_SEMANTICS` environment variable.
- Updated `Makefile`: `make eval-test` now runs both `eval-test-big` and
  `eval-test-small`. Small-step eval tests use a larger default fuel budget
  because control steps are finer-grained than big-step evaluation.

### Notes and limitations

The evaluator is intended as an executable semantics, not a diagnostics layer.
It reports runtime errors for invalid control-flow/runtime cases but does not
attempt to reproduce every `bc -s` / `bc -w` compile-time warning. The decimal
number implementation was validated against the checked-in reference corpus,
including heavy arithmetic and libmath tests, but it remains a Lean model rather
than a direct binding to GNU bc's `lib/number.c`.

---

## Step 9 — Human-guided big-step/small-step split and code reorganization

**Agent:** Codex (GPT-5.5 xhigh)
**Duration:** ~1 hour.

This step records a human-guided correction after the first small-step
implementation. The initial version made `Bc.SmallStep` import `Bc.BigStep`,
which blurred the distinction between the two operational semantics. The follow
up reorganized the code so big-step and small-step are sibling implementations
over a shared runtime layer.

### Changes

1. **Split shared runtime code out of big-step.** Added `Bc/Runtime.lean` for
   numeric operations, `RuntimeState`, `Result`, `RunResult`, `Control`, output
   helpers, function/array/scalar environment helpers, and other runtime update
   utilities.
2. **Made the semantics independent siblings.** `Bc.BigStep` and
   `Bc.SmallStep` now both import `Bc.Runtime`; `Bc.SmallStep` no longer imports
   or delegates to `Bc.BigStep`. Only `Main.lean` imports both semantics to
   dispatch the CLI-selected evaluator.
3. **Kept expression evaluation concrete per semantics.** Because bc expressions
   can mutate state through assignment, increment/decrement, array allocation,
   and function calls, expression evaluation was not treated as a pure shared
   evaluator. Each semantics owns its own expression/body/statement evaluation
   path, while sharing only runtime helper operations.
4. **Updated project documentation.** Refreshed `README.md`, `AGENTS.md`, and
   this report to describe `Bc.Runtime` and the intended dependency structure.

---

## Step 10 — Progress theorem for small-step semantics

**Agent:** Codex (GPT-5.5 xhigh)
**Duration:** ~1.5 hours.

### Request

Prove a Progress theorem for the small-step semantics, following the idea from
Software Foundations' Programming Language Foundations chapter on small-step
semantics:
`https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html`.
Additional human review and guidance clarified that the theorem should
ultimately be stated over a fuel-free small-step relation, with expressions
evaluated by small steps rather than by a hidden recursive evaluator.

### Implementation

- Added `Bc/Progress.lean`.
- Defined `SmallStep.Transition`, a relational view of one executable small-step
  transition, where only `StepResult.next` outcomes are proper transitions.
- Defined `SmallStep.Terminal` for terminal one-step outcomes of the
  fuel-free machine: `.done`, `.control`, and `.runtimeError`.
- Defined `NormalForm` and `Stuck` predicates.
- Proved `SmallStep.progress`: every configuration is terminal or can step to
  another configuration.
- Proved supporting results:
  - `terminal_is_normal_form`
  - `normal_form_is_terminal`
  - `normal_form_iff_terminal`
  - `not_stuck`
- Refactored `Bc/SmallStep.lean` so the semantic one-step function is
  `step : Config -> StepResult`, with no fuel argument and no `.outOfFuel`
  result.
- Replaced the small-step module's hidden recursive expression evaluator with
  expression tasks, value tasks, lvalue tasks, and continuation frames on the
  same `Config`/task stack.
- Kept fuel only in `runConfig`, `runProgramWithState`, and `evalBody` as an
  executable interpreter bound.

### Human-guided review

The initial theorem was wrong for the intended semantics: it was adapted to the
executable fuel-bounded interpreter wrapper and classified fuel exhaustion as a
terminal outcome. Human review identified that this was only a no-stuck theorem
for the runner, not the canonical semantic Progress theorem.

Additional human guidance clarified the desired design: expressions should also
be evaluated by small steps, using the same `Config`/task stack extended with
expression tasks and continuation frames. The corrected theorem is now stated
over the fuel-free small-step relation, matching the Software Foundations
congruence-rule/evaluation-context approach more closely.

---

## Step 11 — Structural source-AST small-step semantics

**Agent:** Codex (GPT-5.5 xhigh)
**Duration:** ~1 hour.

### Request

Human review identified that the Step 10 implementation was a small-step
abstract-machine semantics using explicit `Task`/continuation frames, not a
textbook structural small-step semantics over source terms. Replace it with a
source-AST residual semantics, keep the one-step relation fuel-free, and keep
the interpreter runner as the only fuel-bounded layer.

### Implementation

- Replaced `Bc.SmallStep`'s continuation/task machine with source-shaped
  residual terms:
  - `ProgramTerm`
  - `TopItemTerm`
  - `StmtTerm`
  - `BodyTerm`
  - `ExprTerm`
  - `LValTerm`
  - `ArgTerm`
- `Config` now stores `RuntimeState` plus a residual `ProgramTerm`, so one step
  has the textbook shape: current environment plus current residual source term
  reduces to a new environment plus new residual source term.
- `ProgramTerm` remains the sequence of top-level residual terms; source
  `TopItem.stmts` groups are flattened to individual `TopItemTerm.stmt` entries.
  Groups containing top-level `quit` are collapsed to a single residual stop
  marker to preserve GNU bc's "skip the whole input item" behaviour.
- Expression stepping is structural over `ExprTerm`, with values represented as
  `ExprTerm.value`; lvalue resolution is structural over `LValTerm`, with
  resolved runtime targets represented as `LValTerm.target`.
- Statement and body stepping reduce residual statements and bodies directly
  rather than pushing control-stack tasks.
- Source `BodyItem.newline` entries are erased during conversion; residual body
  terms are plain statement sequences.
- Function calls are represented structurally as `ExprTerm.activeCall`, whose
  body is a residual `BodyTerm`; return, break, quit, and runtime errors remain
  explicit terminal/control outcomes.
- Fuel remains only in `runConfig`, `runProgramWithState`, and `evalBody`.
- Updated `Bc.Progress` comments to describe the structural residual semantics;
  the theorem itself remains the fuel-free progress theorem for `step`.


---

## Step 12 — Quit terminology cleanup and manual fixture

**Agent:** Codex (GPT-5.5 xhigh)
**Duration:** ~0.25 hours.

### Request

Human review found the residual small-step representation clumsy because it had
both source-level `quit` and an artificial source-level `stop` marker. Human
review also requested a focused unit test for the GNU bc manual example that
`if (0 == 1) quit` terminates the processor even though the condition is false.

### Implementation

- Removed `TopItemTerm.stop`; top-level source groups containing `quit` now
  collapse to a residual `StmtTerm.quit`.
- Renamed the shared control outcome from `Control.stop` to `Control.quit`, so
  the internal control-flow name matches the source construct.
- Added `tests/eval/local/quit-if-false-comparison.b` with an AST golden.
