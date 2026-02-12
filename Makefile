# seT5 — Top-level Makefile
# Integrates the Ternary-C-compiler submodule and builds seT5 kernel code.

CC       = gcc
CFLAGS   = -Wall -Wextra -Iinclude -Itools/compiler/include
COMPILER = tools/compiler/ternary_compiler

# Source files (all kernel modules)
SET5_SRCS = src/init.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c

# ---- Compiler submodule ----
.PHONY: build-compiler
build-compiler:
	$(MAKE) -C tools/compiler clean
	$(MAKE) -C tools/compiler all

# Ensure the compiler binary exists (build only if missing)
$(COMPILER):
	$(MAKE) build-compiler

# ---- seT5 native build (standard gcc, for host testing) ----
set5_native: $(SET5_SRCS)
	$(CC) $(CFLAGS) -o $@ $(SET5_SRCS)

# ---- seT5 ternary bytecode build (via submodule compiler) ----
set5.bytecode: $(COMPILER) $(SET5_SRCS)
	$(COMPILER) -o $@ $(SET5_SRCS)

# ---- Convenience targets ----
.PHONY: build-set5
build-set5: build-compiler set5.bytecode

.PHONY: run-native
run-native: set5_native
	./set5_native

# ---- Demo programs ----
.PHONY: demos
demos:
	$(CC) $(CFLAGS) -o demo/trit_demo demo/trit_demo.c
	$(CC) $(CFLAGS) -o demo/trit_type_demo demo/trit_type_demo.c
	$(CC) $(CFLAGS) -o demo/trit_emu_bench demo/trit_emu_bench.c

# ---- Integration test ----
TEST_INT_SRCS = tests/test_integration.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
test_integration: $(TEST_INT_SRCS)
	$(CC) $(CFLAGS) -Wno-unused-variable -o $@ $(TEST_INT_SRCS)

# ---- seL4 Ternary Moonshot test ----
TEST_SEL4_SRCS = tests/test_sel4_ternary.c src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
test_sel4_ternary: $(TEST_SEL4_SRCS)
	$(CC) $(CFLAGS) -o $@ $(TEST_SEL4_SRCS)

# ---- Clang trit demo ----
clang_trit_demo: demo/clang_trit_demo.c src/multiradix.c
	$(CC) $(CFLAGS) -o demo/clang_trit_demo $^

# ---- Benchmark ----
bench_unroll: tests/bench_unroll.c src/multiradix.c
	$(CC) -O2 $(CFLAGS) -o $@ $^

# ---- Test ----
.PHONY: test
test: build-compiler
	@echo "=== Compiler tests ==="
	$(MAKE) -C tools/compiler $(addprefix run-,test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays) 2>/dev/null || \
	  (cd tools/compiler && for t in test_trit test_parser test_codegen test_vm test_typechecker test_linker test_selfhost test_arrays test_hardware test_basic; do \
	    if [ -f ./$$t ]; then echo "[RUN] $$t"; ./$$t && echo "[PASS] $$t" || echo "[FAIL] $$t"; fi; \
	  done)
	@echo "=== seT5 native test ==="
	$(MAKE) set5_native
	./set5_native
	@echo "=== seT5 integration test ==="
	$(MAKE) test_integration
	./test_integration
	@echo "=== seL4 Ternary Moonshot test ==="
	$(MAKE) test_sel4_ternary
	./test_sel4_ternary
	@echo "=== All tests complete ==="

# ---- Clean ----
.PHONY: clean
clean:
	$(MAKE) -C tools/compiler clean
	rm -f set5_native set5.bytecode
	rm -f demo/trit_demo demo/trit_type_demo demo/trit_emu_bench demo/clang_trit_demo
	rm -f test_integration test_sel4_ternary bench_unroll

.PHONY: all
all: build-set5
