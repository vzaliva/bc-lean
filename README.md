# bc-lean

An experiment in **AI-assisted semantics extraction**: deriving complete,
executable formal semantics for an existing language from its implementation
source, test cases, and sample runs, with the work driven by an AI agent.

The target language is [GNU bc](https://www.gnu.org/software/bc/), version
**1.07.1**. The semantics are formalised in [Lean 4](https://leanprover.github.io/).

## Scope

This project models bc's **operational semantics** as an executable Lean
interpreter. There is no type checker — bc is an untyped arbitrary-precision
calculator language, so the formalisation is an evaluator that runs `.bc`
programs.

The reference implementation (`bc-1.07.1/`) is unpacked locally for consultation
but is not part of this repository.

## Building

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) (managed via
  `elan`; the toolchain is pinned in `lean-toolchain`)

### Build

```bash
make
```

This downloads the precompiled mathlib cache (idempotent) and then runs
`lake build`. To force a fresh cache after a toolchain or mathlib bump:

```bash
make cache-refresh
```

### Run

```bash
# Run a bc program
make run BC=examples/hello.bc

# ...or directly via lake
lake exe bc-lean examples/hello.bc
```

## Project Structure

- `Bc/`            — core operational semantics (Lean modules under the `Bc` namespace)
- `Main.lean`      — interpreter entry point
- `lakefile.lean`  — Lake build configuration
- `Makefile`       — convenience targets (build, cache, run, clean)
- `bc-1.07.1/`     — unpacked GNU bc reference source (not committed)

## License

This project is licensed under the GNU General Public License v3.0 — the same
license as GNU bc. See the [LICENSE](LICENSE) file for details.
