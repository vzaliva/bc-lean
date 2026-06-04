ifeq ($(OS),Windows_NT)
$(error Windows is not supported)
endif

TS ?= tree-sitter

.PHONY: all clean test

all:
	cd tree-sitter-bc && $(TS) generate && $(TS) build

clean:
	$(RM) -f tree-sitter-bc/*.so tree-sitter-bc/*.wasm

test:
	$(TS) test
