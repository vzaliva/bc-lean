.PHONY: all lean-build lean-build-file run lean-clean clean cache cache-refresh distclean parser parser-test parser-all config.json parser-clean test ast-test ast-test-update eval-test eval-test-big eval-test-small

all: lean-build

BIG_STEP_FUEL ?= 200000
SMALL_STEP_FUEL ?= 100000000

# --- tree-sitter bc parser (standalone; no Lean dependency) ---

config.json:
	rm -f config.json
	@printf '%s\n' '{' \
	  '  "parser-directories": [ "./parser" ]' \
	  '}' > config.json

parser: config.json
	$(MAKE) -C parser

parser-test: parser
	./scripts/parse_all_tests.sh

parser-all: parser parser-test

test: ast-test eval-test

ast-test: lean-build parser config.json
	./scripts/run_ast_tests.sh

ast-test-update: lean-build parser config.json
	./scripts/update_ast_tests.sh

eval-test: eval-test-big eval-test-small

eval-test-big: lean-build parser config.json
	BC_LEAN_ASSUME_BUILT=1 BC_LEAN_FUEL=$(BIG_STEP_FUEL) ./scripts/run_eval_tests.sh --semantics big

eval-test-small: lean-build parser config.json
	BC_LEAN_ASSUME_BUILT=1 BC_LEAN_FUEL=$(SMALL_STEP_FUEL) ./scripts/run_eval_tests.sh --semantics small

parser-clean:
	$(MAKE) -C parser clean

# The project has no external dependencies (only the Lean toolchain's `Std` and
# core tactics), so there is no mathlib cache to download. `cache` is kept as a
# no-op so dependent targets and existing workflows keep working.
cache:
	@:

# Force a clean rebuild (e.g. after a toolchain bump).
cache-refresh:
	lake clean

lean-build: cache
	lake build

# Build a single Lean file. FILE = module name (e.g. Bc.BigStep) or path (e.g. Bc/BigStep.lean).
# Example: make lean-build-file FILE=Bc/BigStep.lean
lean-build-file: cache
	@if [ -z "$(FILE)" ]; then echo "Usage: make lean-build-file FILE=Bc/BigStep.lean"; exit 1; fi
	@MODULE=$$(echo "$(FILE)" | sed 's|/|.|g' | sed 's|\.lean$$||'); lake build $$MODULE

# Run a .bc file. BC = path to the .bc source file.
# Example: make run BC=examples/hello.bc
run: cache
	@if [ -z "$(BC)" ]; then echo "Usage: make run BC=path/to/file.bc"; exit 1; fi
	lake build bc-lean && lake exe bc-lean "$(BC)"

lean-clean:
	lake clean

clean: lean-clean

# Reset everything, including the lock file.
distclean: clean
	rm -rf .lake
	rm -f lake-manifest.json
