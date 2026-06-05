# Gavin Howard bc POSIX eval fixtures

These tests are copied from Gavin Howard's bc test suite:

- Repository: `https://github.com/gavinhoward/bc`
- Source commit inspected: `8292c1b`
- Upstream paths: `tests/bc/*.txt`
- License: BSD-2-Clause; see `LICENSE.md` in this directory.

FreeBSD's current source tree vendors Gavin Howard's bc under `contrib/bc`,
including the same test suite. No separate FreeBSD-specific POSIX bc test corpus
was found during import.

Only a curated POSIX-compatible subset is imported here. Candidates were
screened with GNU bc standard compile mode and then compared against GNU bc as
the runtime oracle. Tests that depend on Gavin-specific extensions, extra
libraries, random behavior, or unsupported diagnostics are intentionally omitted.

Files ending in `.mathlib` are empty harness markers. They tell
`scripts/run_eval_tests.sh` to run the corresponding `.b` file with `-l` for
both GNU `bc` and `bc-lean`.
