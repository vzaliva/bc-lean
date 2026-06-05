# AGENTS.md

This file provides guidance to AI agents when working with code in this repository.

## Project Overview

`bc-lean` is an experiment in **AI-assisted semantics extraction**: deriving a
complete, executable formal semantics for an existing language from its
implementation source, test cases, and sample runs, with the work driven by an
AI agent. The target language is [GNU bc](https://www.gnu.org/software/bc/),
version **1.07.1**.

This is a Lean 4 project. The semantics are modelled as an **executable
interpreter** — there is no type checker, since bc is an untyped
arbitrary-precision calculator language.

- **Parser** (`parser/`) — tree-sitter grammar for `.b`/`.bc` files (standalone;
  see README *Parser (tree-sitter)* section)
- **Core implementation** (`Bc/`) — surface AST and tree-sitter bridge
- **Interpreter entry point** (`Main.lean`) — CLI (`bc-lean`; evaluator WIP)
- **Parse test CLI** (`Bc/ParseTestMain.lean`) — `bc-parse-test` for AST goldens
- **Reference source** (`bc-1.07.1/`) — the unpacked GNU bc 1.07.1 source, kept
  locally for consultation. It is **not committed** (see `.gitignore`).

## General Coding Standards

- **Indentation**: Use spaces only, never tabs (Lean source). Note the
  `Makefile` necessarily uses tabs for recipe lines.
- **Compilation**: Always leave code in a compilable state at checkpoints (no
  build errors)
- **Warnings**: Avoid compilation warnings
- **Unused binders**: Prefix unused variables and parameters with `_` so the
  tree stays warning-clean (warnings can fail CI or tests)
- **Partial functions**: Keep the proof/model surface total. Do not use `partial`
  in `Bc/Syntax.lean`, future operational semantics, or functions/predicates
  intended to be referenced by AST or semantic definitions. `partial` is
  acceptable in non-verified infrastructure such as the parser, XML bridge, and
  golden-test pretty printer.
- **Build verification**: Run `lake build` (or `make`) to check compilation
  before committing
- **No parallel builds**: Do not run concurrent builds (including via parallel
  sub-agents) for files that share dependencies; `lake` builds all transitive
  dependencies, so concurrent builds of interdependent files will conflict and
  produce spurious errors
- **CLI tools**: fd (fdfind), ripgrep, jq, rename, shellcheck, sd, delta, gh,
  difftastic (`difft` on some installs), scc, yq, hyperfine, comby, ast-grep,
  dtrx; fzf, bat (navigation/preview), just (task runner), entr, watchexec
  (rebuild on change), parallel (gnu parallel; independent per-file checks).

## Build Commands

```bash
# tree-sitter bc parser (no Lean dependency)
make parser                            # Build tree-sitter grammar
make parser-test                       # Parse the upstream valid corpus
make parser-all                        # Build + parse regression

# Lean AST golden tests
make test                              # same as ast-test
make ast-test                          # bc-parse-test vs tests/ast-expected/
make ast-test-update                   # refresh golden files

# Build everything (Lean libraries and the interpreter)
make                                   # == make lean-build
make lean-build                        # Build Lean libraries and executables
make lean-build-file FILE=Bc/Eval.lean # Build one module (path or dotted name, e.g. Bc.Eval)

# Running the interpreter
make run BC=examples/hello.bc          # Run a .bc file
lake exe bc-lean examples/hello.bc     # ...or directly via lake

# Lean cache (mathlib); `lean-build` already depends on `cache`
make cache                             # Download precompiled caches if needed
make cache-refresh                     # Force fresh cache (use after toolchain/mathlib bumps)

# Cleaning (WARNING: distclean invalidates the mathlib cache - avoid; ask user
# permission if absolutely necessary)
make clean                             # Clean Lean build artifacts (lake clean)
make distclean                         # Also remove .lake and lake-manifest.json
# After a distclean, run: lake exe cache get
```

## Architecture

### `parser/` — tree-sitter grammar

Standalone bc parser for `.b` and `.bc` files. Grammar source:
`parser/tree-sitter-bc/grammar.js`. Regression inputs under `tests/`. See README
*Parser (tree-sitter)*.

### `Bc/` — Core Implementation

Surface AST, tree-sitter XML bridge (`Bc/Parser.lean`), and (future)
operational semantics under the `Bc` namespace (`lakefile.lean` → `lean_lib Bc`).
The parser is syntax-only; do not add context checks, diagnostics, or semantic
checks to it. Modules avoid mathlib except where the evaluator will need it
later.

### Other Components

- `Main.lean` — interpreter entry point with CLI
- `examples/` — sample `.bc` programs
- `lakefile.lean` — Lake build configuration (`lean_lib Bc`, `lean_exe bc-lean`)
- `Makefile` — convenience targets (build, cache, run, clean)
- `lean-toolchain` — pinned Lean/Lake toolchain version

## Working with the Reference Source

The GNU bc 1.07.1 source in `bc-1.07.1/` is the **ground truth** for the
semantics being extracted. When the modelled behaviour is unclear, consult it
(notably `bc-1.07.1/bc/` for the grammar and execution engine, and
`bc-1.07.1/Test/` and `bc-1.07.1/Examples/` for behavioural examples). Do not
modify or commit anything under `bc-1.07.1/`.

For reference syntax checks, use GNU bc standard compile-only mode (`bc -s -c`,
adding `-l` only when libmath is needed). Treat non-zero output from `bc -s -c`
as outside the currently supported POSIX/standard syntax subset.

## Testing

- **Tree-sitter:** `make parser-test` — valid-corpus syntax acceptance only.
- **Lean AST:** `make test` — parses each corpus file via `bc-parse-test`, compares
  to `tests/ast-expected/` (`.output` success, `.fail` for `tests/parse-invalid/`).
- **Context/semantic fixtures:** `tests/semantics/` is reserved for later work and
  is not exercised by parser or AST tests.
- **Evaluator (planned):** golden output comparison against reference `bc`.

## Git and GitHub

- **Read-only git operations**: You may use `git` to review commit history,
  compare branches, and inspect changes
- **No repository modifications without approval**: Do not run commands that
  modify the repository (e.g., `git commit`, `git push`, `git merge`) unless the
  user asks
- **GitHub CLI**: You may use `gh` to view issues; request user approval before
  creating or modifying GitHub issues
- **Backtick handling**: When creating issues/comments, prefer `--body-file` to
  avoid shell backtick problems

## License

This project is licensed under the **GNU General Public License v3.0** — the
same license as GNU bc. See `LICENSE`.
