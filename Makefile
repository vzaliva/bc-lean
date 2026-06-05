.PHONY: all lean-build lean-build-file run lean-clean clean cache cache-refresh distclean parser parser-test parser-all config.json parser-clean test ast-test ast-test-update eval-test

all: lean-build

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

test: ast-test
	BC_LEAN_ASSUME_BUILT=1 ./scripts/run_eval_tests.sh

ast-test: lean-build parser config.json
	./scripts/run_ast_tests.sh

ast-test-update: lean-build parser config.json
	./scripts/update_ast_tests.sh

eval-test: lean-build parser config.json
	BC_LEAN_ASSUME_BUILT=1 ./scripts/run_eval_tests.sh

parser-clean:
	$(MAKE) -C parser clean

# Download precompiled Lean caches for mathlib/upstreams (idempotent).
# Uses a sentinel file to avoid re-downloading if the cache already exists.
.lake/.cache-downloaded:
	@mkdir -p .lake
	@echo "Downloading Lean cache..."
	@lake exe cache get && touch .lake/.cache-downloaded

cache: .lake/.cache-downloaded

# Force a fresh cache (good after toolchain/mathlib bumps).
cache-refresh:
	lake clean
	rm -rf .lake
	mkdir -p .lake
	lake exe cache get!
	touch .lake/.cache-downloaded

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
