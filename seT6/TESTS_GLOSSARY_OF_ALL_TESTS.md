# TESTS_GLOSSARY_OF_ALL_TESTS.md

## seT6 Comprehensive Test Glossary

**Total Runtime Assertions**: 6603
**Total Source-Level Test Entries**: 6208
**Test Suites**: 101 (101 actively running; 3 disabled compiler suites)
**Overall Pass Rate**: 100% (0 failures across all active suites)
**Last Updated**: 2026-02-20 — Sigma 11: Added 18 batch suites (92–119), fixed 10 ALU assertions, wired all batches into grand summary
**Generated**: Auto-extracted from source code

---

## How to Read This Glossary

Each suite section contains:
- **Source**: Path to the test source file
- **Harness**: The assertion macro/pattern used
- **Output Reading**: How to interpret the test output
- **Table**: Every test assertion with line number, description, section, expression, and category

**Category Legend**:
- **Functional**: Core correctness of an operation
- **Boundary**: Overflow, underflow, min/max, clamping
- **Negative/error**: Invalid inputs, rejection, error paths
- **Arithmetic**: Addition, subtraction, multiplication, division
- **Logic**: Boolean/Kleene logic operations (AND, OR, NOT, etc.)
- **Encoding**: Encode/decode, compression, serialization
- **Memory**: Allocation, freeing, pools, pages
- **Access control**: Capabilities, permissions, isolation
- **IPC**: Inter-process communication, messaging
- **Scheduling**: Thread priority, preemption, context switches
- **Initialization**: Boot, setup, configuration
- **Transformation**: Type conversion, round-trip, mapping
- **Performance**: Benchmarks, throughput, latency
- **Stress**: Fuzzing, chaos, adversarial, exhaustion
- **Consensus**: Voting, majority, quorum
- **Hardware/ALU**: Opcodes, pipeline, register operations
- **Parsing**: Lexer, tokens, AST, syntax
- **Type system**: Type checking, inference, coercion
- **Linking**: Symbol resolution, linking

**Note**: Some source-level assertions run inside `for`-loops and expand to multiple runtime assertions.
The *runtime* count reflects the total assertions executed; the *source-level* count reflects unique assertion lines.

---

## Suite Index

| # | Suite | Source | Runtime | Source Entries | Status |
|---|-------|--------|---------|---------------|--------|
| 1 | Compiler: Trit Operations | `tools/compiler/tests/test_trit.c` | 22 | 22 | ✅ |
| 2 | Compiler: Parser | `tools/compiler/tests/test_parser.c` | 14 | 14 | ✅ |
| 3 | Compiler: Code Generator | `tools/compiler/tests/test_codegen.c` | 9 | 9 | ✅ |
| 4 | Compiler: VM Execution | `tools/compiler/tests/test_vm.c` | 37 | 37 | ✅ |
| 5 | Compiler: TypeChecker | `tools/compiler/tests/test_typechecker.c` | 15 | 15 | ✅ |
| 6 | Compiler: Linker | `tools/compiler/tests/test_linker.c` | 13 | 13 | ✅ |
| 7 | Compiler: Self-Hosting | `tools/compiler/tests/test_selfhost.c` | 13 | 13 | ✅ |
| 8 | Compiler: Arrays | `tools/compiler/tests/test_arrays.c` | 12 | 12 | ✅ |
| 9 | Compiler: Ternary Hardware | `tools/compiler/tests/test_hardware.c` | 22 | 22 | ✅ |
| 10 | seT6 Boot (Native) | `src/init.c` | 178 | 174 | ✅ |
| 11 | Integration | `tests/test_integration.c` | 56 | 48 | ✅ |
| 12 | seL4 Ternary Extensions | `tests/test_sel4_ternary.c` | 142 | 137 | ✅ |
| 13 | Memory Safety | `tests/test_memory_safety.c` | 28 | 28 | ✅ |
| 14 | Scheduler Concurrency | `tests/test_scheduler_concurrency.c` | 27 | 18 | ✅ |
| 15 | TBE Bootstrap Engine | `tests/test_tbe.c` | 31 | 31 | ✅ |
| 16 | Huawei CN119652311A ALU | `tests/test_huawei_cn119652311a.c` | 47 | 47 | ✅ |
| 17 | Samsung US11170290B2 ZID | `tests/test_samsung_us11170290b2.c` | 60 | 60 | ✅ |
| 18 | Samsung CN105745888A Correlator | `tests/test_samsung_cn105745888a.c` | 61 | 61 | ✅ |
| 19 | TSMC TMD / Intel PAM3 / Hynix TCAM | `tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c` | 80 | 80 | ✅ |
| 20 | Ternary Database & Storage ⭐NEW | `tests/test_ternary_database.c` | 32 | 32 | ✅ |
| 21 | Ingole WO2016199157A1 TALU ⭐NEW | `tests/test_ingole_wo2016199157a1.c` | 32 | 32 | ✅ |
| 22 | AI Acceleration Framework ⭐NEW | `tests/test_ai_acceleration.c` | 24 | 24 | ✅ |
| 23 | Fault-Tolerant Networking ⭐NEW | `tests/test_fault_tolerant_network.c` | 25 | 25 | ✅ |
| 24 | Adversarial / Negative-Path ⭐NEW | `tests/test_adversarial.c` | 34 | 34 | ✅ |
| 25 | Crown Jewel Reversion Guard ⭐NEW | `tests/test_ternary_reversion_guard.c` | 37 | 37 | ✅ |
| 26 | LEGO Modular Architecture | `tests/test_modular.c` | 49 | 47 | ✅ |
| 27 | Secure IPC | `tests/test_ipc_secure.c` | 40 | 38 | ✅ |
| 28 | Time Synchronization | `tests/test_time.c` | 42 | 50 | ✅ |
| 29 | System Hardening | `tests/test_hardening.c` | 55 | 38 | ✅ |
| 30 | Sigma 9 Validation | `tests/test_sigma9.c` | 337 | 358 | ✅ |
| 31 | RNS Standalone | `tests/test_rns.c` | 278 | 216 | ✅ |
| 32 | Paper-Derived Modules | `tests/test_papers.c` | 200 | 220 | ✅ |
| 33 | Paper2-Derived Modules | `tests/test_papers2.c` | 200 | 216 | ✅ |
| 34 | DLT + CNTFET | `tests/test_dlt_cntfet.c` | 60 | 60 | ✅ |
| 35 | ART-9 RISC Pipeline | `tests/test_art9.c` | 60 | 60 | ✅ |
| 36 | Ternary PDF-Derived | `tests/test_ternary_pdfs.c` | 192 | 192 | ✅ |
| 37 | Peirce Semiotic Engine | `tests/test_peirce_semiotic.c` | 200 | 100 | ✅ |
| 38 | TriLang | `tests/test_trilang.c` | 100 | 92 | ✅ |
| 39 | Sigma 9 MCP | `tests/test_sigma9_mcp.c` | 197 | 197 | ✅ |
| 40 | Hybrid AI Integration | `tests/test_hybrid_ai.c` | 282 | 282 | ✅ |
| 41 | Red-Team Stress & Performance | `tests/test_stress.c` | 512 | 144 | ✅ |
| 42 | Trithon Self-Test | `trithon/trithon.py` | 99 | 86 | ✅ |
| 43 | TJSON (Python) | `tests/test_tjson.py` | 346 | 76 | ✅ |
| 44 | TerNumPy (Python) | `tests/test_ternumpy.py` | 42 | 42 | ✅ |
| 45 | Functional Utility | `tests/test_functional_utility.c` | 202 | 233 | ✅ |
| 46 | Friday Updates | `tests/test_friday_updates.c` | 135 | 138 | ✅ |
| 47 | Trit Linux Architecture | `tests/test_trit_linux.c` | 98 | 96 | ✅ |
| 48 | Gödel Machine ⭐NEW | `tests/test_godel_machine.c` | 39 | 39 | ✅ |
| 49 | SIMD Regression ⭐NEW | `tests/test_trit_simd_regression.c` | 10 | 10 | ✅ |
| 50 | Binary Sentinel ⭐NEW | `tests/test_binary_sentinel.c` | 12 | 12 | ✅ |
| 51 | Ternary Compiler Integration ⭐NEW | `tests/test_ternary_compiler_integration.c` | 19 | 19 | ✅ |
| 52 | Compiler: Basic Integration ⭐NEW | `tools/compiler/tests/test_basic.c` | 26 | 4 | ✅ |
| 53 | Compiler: Bootstrap Self-Host ⭐NEW | `tools/compiler/tests/test_bootstrap.c` | 33 | 21 | ✅ |
| 54 | Compiler: Hardware Simulation ⭐NEW | `tools/compiler/tests/test_hardware_simulation.c` | 10 | 7 | ✅ |
| 55 | Compiler: IR / Constant Folding ⭐NEW | `tools/compiler/tests/test_ir.c` | 49 | 20 | ✅ |
| 56 | Compiler: Lexer / Tokenizer ⭐NEW | `tools/compiler/tests/test_lexer.c` | 87 | 20 | ✅ |
| 57 | Compiler: Logger ⭐NEW | `tools/compiler/tests/test_logger.c` | 33 | 14 | ✅ |
| 58 | Compiler: Memory Model ⭐NEW | `tools/compiler/tests/test_memory.c` | 46 | 19 | ✅ |
| 59 | Compiler: Parser Fuzz ⭐NEW | `tools/compiler/tests/test_parser_fuzz.c` | 0 | 5 | ✅ crash-absence |
| 60 | Compiler: Performance ⭐NEW | `tools/compiler/tests/test_performance.c` | 4 | 4 | ✅ |
| 61 | Compiler: seL4 Stubs ⭐NEW | `tools/compiler/tests/test_sel4.c` | 15 | 4 | ✅ |
| 62 | Compiler: seL4 Verify ⭐NEW | `tools/compiler/tests/test_sel4_verify.c` | 51 | 18 | ✅ |
| 63 | Compiler: seT5 Syscalls ⭐NEW | `tools/compiler/tests/test_set5.c` | 23 | 13 | ✅ |
| 64 | Compiler: Ternary Arithmetic Comprehensive ⭐NEW | `tools/compiler/tests/test_ternary_arithmetic_comprehensive.c` | 32 | 5 | ✅ |
| 65 | Compiler: Ternary Edge Cases ⭐NEW | `tools/compiler/tests/test_ternary_edge_cases.c` | 19 | 5 | ✅ |
| 66 | Compiler: Trit Edge Cases ⭐NEW | `tools/compiler/tests/test_trit_edge_cases.c` | 13 | 10 | ✅ |
| 67 | Compiler: Integration Tests | `tools/compiler/tests/test_integration.c` | 24 | 16 | ✅ |
| 68 | Compiler: Test Runner Script | `tools/compiler/tests/test_all.sh` | — | — | ⚙️ script |
| 69 | Multi-Radix Unit ⭐NEW | `tests/test_multi_radix_unit.c` | 3 | 3 | ✅ |
| 70 | Ternary Wallace Tree ⭐NEW | `tests/test_ternary_wallace_tree.c` | 2 | 2 | ✅ |
| 71 | Ternary Sense Amp ⭐NEW | `tests/test_ternary_sense_amp.c` | 3 | 3 | ✅ |
| 72 | T-IPC Compressor ⭐NEW | `tests/test_tipc_compressor.c` | 2 | 2 | ✅ |
| 73 | Samsung Correlator ⭐NEW | `tests/test_samsung_cn105745888a_correlator.c` | 2 | 2 | ✅ |
| 74 | Ternary Full Adder ⭐NEW | `tests/test_ternary_full_adder.c` | 10 | 5 | ✅ |
| 100 | Hardware ALU/TALU Operations | `tests/test_batch_5352_5401.c` | 50 | 50 | ✅ |
| 101 | Side-Channel Resistance | `tests/test_batch_5402_5451.c` | 50 | 50 | ✅ |
| 102 | Side-Channel Resistance Advanced | `tests/test_batch_5452_5501.c` | 50 | 50 | ✅ |
| 103 | Epistemic Logic & Hesitation | `tests/test_batch_5502_5551.c` | 50 | 50 | ✅ |
| 104 | Epistemic Logic & Hesitation Advanced | `tests/test_batch_5552_5601.c` | 50 | 50 | ✅ |
| 105 | Guardian Trit Mechanisms | `tests/test_batch_5602_5651.c` | 50 | 50 | ✅ |
| 106 | Guardian Trit Mechanisms Advanced | `tests/test_batch_5652_5701.c` | 50 | 50 | ✅ |
| 107 | RSI Flywheel Safety | `tests/test_batch_6202_6251.c` | 50 | 50 | ✅ |
| 108 | Curiosity Gradient | `tests/test_batch_6252_6301.c` | 50 | 50 | ✅ |
| 109 | Beauty Symmetry | `tests/test_batch_6302_6351.c` | 50 | 50 | ✅ |
| 110 | Eudaimonic Optimization | `tests/test_batch_6352_6401.c` | 50 | 50 | ✅ |
| 111 | Balanced Ternary Arithmetic | `tests/test_batch_6402_6451.c` | 50 | 50 | ✅ |
| 112 | Mixed-Radix & Packed64 SIMD | `tests/test_batch_6452_6501.c` | 50 | 50 | ✅ |
| 113 | Heptavint Multi-Radix Encoding | `tests/test_batch_6502_6551.c` | 50 | 50 | ✅ |
| 114 | Ternary Floating-Point Basics | `tests/test_batch_6552_6601.c` | 50 | 50 | ✅ |
| 115 | Ternary Error Correction GF(3) Hamming | `tests/test_batch_6602_6651.c` | 50 | 50 | ✅ |
| 116 | Ternary Capability Access Control | `tests/test_batch_6652_6701.c` | 50 | 50 | ✅ |
| 117 | Ternary State Machine & Protocol | `tests/test_batch_6702_6751.c` | 50 | 50 | ✅ |
| — | Trit Enhancements *(not building)* | `tests/test_trit_enhancements.c` | — | 214 | ⚠️ needs `tcore_env_t` rebuild |
| — | Compiler: Codegen Bugs *(disabled)* | `tools/compiler/tests/test_compiler_code_generation_bugs.c` | 39 | 19 | ⚠️ commented out in compiler Makefile |
| — | Compiler: Error Recovery *(disabled)* | `tools/compiler/tests/test_error_recovery.c` | 26 | 11 | ⚠️ commented out in compiler Makefile |
| — | Compiler: Parser/Lexer Fuzz *(disabled)* | `tools/compiler/tests/test_parser_lexer_fuzz.c` | 18 | 10 | ⚠️ commented out in compiler Makefile |
| | **TOTAL (active, running)** | | **5037** | **4692** | |
| | **TOTAL (incl. disabled)** | | **5120** | **4732** | |

---

## Suite 1: Compiler: Trit Operations

**Source**: `tools/compiler/tests/test_trit.c`
**Runtime Assertions**: 22
**Source-Level Entries**: 22
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L13 | test_mul_pos_pos | trit_mul tests | `trit_mul(TRIT_P, TRIT_P), TRIT_P);   //  1 *  1 =  1` | Arithmetic |
| 2 | L17 | test_mul_pos_neg | trit_mul tests | `trit_mul(TRIT_P, TRIT_N), TRIT_N);    //  1 * -1 = -1` | Arithmetic |
| 3 | L21 | test_mul_neg_neg | trit_mul tests | `trit_mul(TRIT_N, TRIT_N), TRIT_P);    // -1 * -1 =  1` | Arithmetic |
| 4 | L25 | test_mul_zero_any | trit_mul tests | `trit_mul(TRIT_Z, TRIT_P), TRIT_Z);    //  0 *  1 =  0` | Arithmetic |
| 5 | L31 | test_mul_neg_pos | trit_mul tests | `trit_mul(TRIT_N, TRIT_P), TRIT_N);    // -1 *  1 = -1` | Arithmetic |
| 6 | L37 | test_add_no_carry_basic | trit_add tests | `trit_add(TRIT_P, TRIT_Z, &carry), TRIT_P` | Arithmetic |
| 7 | L55 | test_add_cancel | trit_add tests | `trit_add(TRIT_P, TRIT_N, &carry), TRIT_Z` | Arithmetic |
| 8 | L63 | test_add_positive_overflow | trit_add tests | `result, TRIT_N` | Boundary |
| 9 | L72 | test_add_negative_overflow | trit_add tests | `result, TRIT_P` | Boundary |
| 10 | L81 | test_add_with_carry_in | trit_add tests | `result, TRIT_Z` | Arithmetic |
| 11 | L90 | test_add_with_negative_carry_in | trit_add tests | `result, TRIT_Z` | Negative/error |
| 12 | L101 | test_min_basic | trit_min / trit_max tests | `trit_min(TRIT_N, TRIT_P), TRIT_N` | Boundary |
| 13 | L108 | test_min_equal | trit_min / trit_max tests | `trit_min(TRIT_P, TRIT_P), TRIT_P` | Boundary |
| 14 | L114 | test_max_basic | trit_min / trit_max tests | `trit_max(TRIT_N, TRIT_P), TRIT_P` | Boundary |
| 15 | L121 | test_max_equal | trit_min / trit_max tests | `trit_max(TRIT_P, TRIT_P), TRIT_P` | Boundary |
| 16 | L129 | test_add_exhaustive | Full trit_add truth table | `—` | Arithmetic |
| 17 | L157 | test_int_to_trit_word_basic | Trit word operations (TASK-002) | `trit_word_to_int(w), 0` | Functional |
| 18 | L172 | test_trit_word_add_simple | Trit word operations (TASK-002) | `trit_word_to_int(res), 5` | Arithmetic |
| 19 | L180 | test_trit_word_add_carry | Trit word operations (TASK-002) | `trit_word_to_int(res), 300` | Arithmetic |
| 20 | L188 | test_trit_word_mul_simple | Trit word operations (TASK-002) | `trit_word_to_int(res), 12` | Arithmetic |
| 21 | L196 | test_trit_word_mul_negative | Trit word operations (TASK-002) | `trit_word_to_int(res), -21` | Negative/error |
| 22 | L204 | test_trit_word_roundtrip | Trit word operations (TASK-002) | `trit_word_to_int(w), vals[i]` | Transformation |

---

## Suite 2: Compiler: Parser

**Source**: `tools/compiler/tests/test_parser.c`
**Runtime Assertions**: 14
**Source-Level Entries**: 14
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L15 | test_parse_simple_main | Parse simple main() | `prog->type, NODE_PROGRAM` | Parsing |
| 2 | L38 | test_parse_return_expr | Parse return with arithmetic expressio | `ret->type, NODE_RETURN` | Parsing |
| 3 | L59 | test_parse_func_with_param | Parse function with parameter | `fn->type, NODE_FUNC_DEF` | Parsing |
| 4 | L80 | test_parse_func_call | Parse function call | `ret->type, NODE_RETURN` | Parsing |
| 5 | L100 | test_parse_multi_func | Parse multiple functions | `prog->type, NODE_PROGRAM` | Arithmetic |
| 6 | L128 | test_parse_invalid_func | Parse invalid function (missing closing paren) | `—` | Negative/error |
| 7 | L135 | test_parse_return_precedence | Parse return with operator precedence (* > +) | `expr->type, NODE_BINOP` | Parsing |
| 8 | L162 | test_parse_if_simple | Parse if statement | `fn->type, NODE_FUNC_DEF` | Parsing |
| 9 | L188 | test_parse_if_else | Parse if-else | `—` | Parsing |
| 10 | L220 | test_parse_while | Parse while loop | `—` | Parsing |
| 11 | L242 | test_parse_for | Parse for loop | `—` | Parsing |
| 12 | L264 | test_parse_comparison_eq | Parse comparison operators | `ret->type, NODE_RETURN` | Parsing |
| 13 | L276 | test_parse_comparison_lt | Parse comparison operators | `ret->left->type, NODE_BINOP` | Parsing |
| 14 | L287 | test_parse_comparison_gt | Parse comparison operators | `ret->left->type, NODE_BINOP` | Parsing |

---

## Suite 3: Compiler: Code Generator

**Source**: `tools/compiler/tests/test_codegen.c`
**Runtime Assertions**: 7
**Source-Level Entries**: 7
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L15 | test_codegen_single_int | Single integer | `bc_idx, 3` | Functional |
| 2 | L29 | test_codegen_addition | Simple additio | `bc_idx, 6` | Arithmetic |
| 3 | L46 | test_codegen_multiplication | Simple multiplicatio | `bc_idx, 6` | Arithmetic |
| 4 | L63 | test_codegen_precedence | Precedence: * before + | `bc_idx, 9` | Functional |
| 5 | L83 | test_codegen_chained_add | Chained additio | `bc_idx, 9` | Arithmetic |
| 6 | L103 | test_codegen_chained_mul | Chained multiplicatio | `bc_idx, 9` | Arithmetic |
| 7 | L123 | test_codegen_halt_termination | Bytecode always ends with HALT | `bc_idx > 0` | Boundary |

---

## Suite 4: Compiler: VM Execution

**Source**: `tools/compiler/tests/test_vm.c`
**Runtime Assertions**: 31
**Source-Level Entries**: 31
**Harness**: Mixed CHECK/ASSERT harness
**Output Reading**: `[PASS]`/`[FAIL]` per assertion. Summary at end.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L48 | test_vm_push_halt | PUSH + HALT | `—` | Functional |
| 2 | L55 | test_vm_push_zero | PUSH + HALT | `—` | Functional |
| 3 | L64 | test_vm_simple_add | PUSH + HALT | `—` | Arithmetic |
| 4 | L71 | test_vm_add_zero | PUSH + HALT | `—` | Arithmetic |
| 5 | L80 | test_vm_simple_mul | PUSH + HALT | `—` | Arithmetic |
| 6 | L87 | test_vm_mul_zero | PUSH + HALT | `—` | Arithmetic |
| 7 | L94 | test_vm_mul_one | PUSH + HALT | `—` | Arithmetic |
| 8 | L103 | test_vm_expression_1_plus_2_mul_3 | Combined: 1 + 2 * 3 = 7 | `—` | Arithmetic |
| 9 | L119 | test_vm_chained_add | Chained ADD: 1 + 2 + 3 = 6 | `—` | Arithmetic |
| 10 | L135 | test_vm_chained_mul | Chained MUL: 2 * 3 * 4 = 24 | `—` | Arithmetic |
| 11 | L151 | test_vm_jmp | JMP: unconditional jump (TASK-003) | `—` | Functional |
| 12 | L166 | test_vm_cond_jmp_true | COND_JMP: jump if top of stack == 0 (TASK-003) | `—` | Functional |
| 13 | L180 | test_vm_cond_jmp_false | COND_JMP: jump if top of stack == 0 (TASK-003) | `—` | Functional |
| 14 | L196 | test_vm_dup | Phase 3: Stack manipulation tests (Setun-70 postfix) | `—` | Functional |
| 15 | L204 | test_vm_drop | Phase 3: Stack manipulation tests (Setun-70 postfix) | `—` | Functional |
| 16 | L212 | test_vm_swap | Phase 3: Stack manipulation tests (Setun-70 postfix) | `—` | Functional |
| 17 | L220 | test_vm_over | Phase 3: Stack manipulation tests (Setun-70 postfix) | `—` | Functional |
| 18 | L229 | test_vm_rot | Phase 3: Stack manipulation tests (Setun-70 postfix) | `—` | Functional |
| 19 | L239 | test_vm_return_stack | Phase 3: Return stack tests (two-stack model) | `—` | Memory |
| 20 | L252 | test_vm_r_fetch | Phase 3: Return stack tests (two-stack model) | `—` | Functional |
| 21 | L267 | test_vm_cmp_eq_true | Phase 3: Comparison ops | `—` | Functional |
| 22 | L274 | test_vm_cmp_eq_false | Phase 3: Comparison ops | `—` | Functional |
| 23 | L281 | test_vm_cmp_lt | Phase 3: Comparison ops | `—` | Functional |
| 24 | L289 | test_vm_cmp_gt | Phase 3: Comparison ops | `—` | Functional |
| 25 | L299 | test_vm_ternary_neg | Phase 3: Ternary logic gates (Brusentsov/Jones) | `vm_get_result(), -5` | Functional |
| 26 | L307 | test_vm_consensus | Phase 3: Ternary logic gates (Brusentsov/Jones) | `vm_get_result(), -4` | Consensus |
| 27 | L317 | test_vm_accept_any | Phase 3: Ternary logic gates (Brusentsov/Jones) | `vm_get_result(), 12` | Functional |
| 28 | L329 | test_vm_brz_taken | Phase 3: BRZ/BRN/BRP structured branching | `—` | Functional |
| 29 | L343 | test_vm_brz_not_taken | Phase 3: BRZ/BRN/BRP structured branching | `—` | Functional |
| 30 | L357 | test_vm_enter_leave | Phase 3: ENTER/LEAVE scope | `—` | Functional |
| 31 | L375 | test_vm_loop | Phase 3: LOOP_BEGIN/LOOP_END | `—` | Functional |

---

## Suite 5: Compiler: TypeChecker

**Source**: `tools/compiler/tests/test_typechecker.c`
**Runtime Assertions**: 15
**Source-Level Entries**: 15
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L15 | test_const_is_int | Basic type inference | `t.kind, TYPE_INT` | Functional |
| 2 | L24 | test_var_declared | Basic type inference | `t.kind, TYPE_INT` | Functional |
| 3 | L36 | test_var_undeclared | Basic type inference | `t.kind, TYPE_UNKNOWN` | Functional |
| 4 | L46 | test_binop_int | Basic type inference | `t.kind, TYPE_INT` | Functional |
| 5 | L56 | test_comparison_returns_int | Basic type inference | `t.kind, TYPE_INT` | Functional |
| 6 | L67 | test_addr_of_returns_ptr | Pointer type checking | `t.kind, TYPE_PTR` | Arithmetic |
| 7 | L79 | test_deref_ptr | Pointer type checking | `t.kind, TYPE_INT` | Functional |
| 8 | L93 | test_deref_non_ptr_error | Pointer type checking | `tc.error_count, 1); /* deref of non-pointer */` | Negative/error |
| 9 | L107 | test_array_access_valid | Array type checking | `t.kind, TYPE_INT` | Access control |
| 10 | L120 | test_array_bounds_error | Array type checking | `tc.error_count, 1); /* out of bounds */` | Boundary |
| 11 | L132 | test_array_negative_index_error | Array type checking | `tc.error_count, 1); /* negative index */` | Negative/error |
| 12 | L144 | test_non_array_access_error | Array type checking | `tc.error_count >= 1); /* not an array */` | Negative/error |
| 13 | L158 | test_check_simple_program | Full program type checking | `errs, 0` | Type system |
| 14 | L171 | test_check_array_program | Full program type checking | `errs, 0` | Type system |
| 15 | L184 | test_too_many_initializers | Full program type checking | `—` | Initialization |

---

## Suite 6: Compiler: Linker

**Source**: `tools/compiler/tests/test_linker.c`
**Runtime Assertions**: 13
**Source-Level Entries**: 13
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L15 | test_linker_init | Basic module management | `lnk.module_count, 0` | Initialization |
| 2 | L23 | test_add_module | Basic module management | `id, 0` | Arithmetic |
| 3 | L33 | test_add_multiple_modules | Basic module management | `id1, 0` | Arithmetic |
| 4 | L47 | test_add_export_symbol | Symbol management | `rc, 0` | Arithmetic |
| 5 | L57 | test_add_import_symbol | Symbol management | `lnk.modules[0].sym_count, 1` | Arithmetic |
| 6 | L69 | test_link_single_module | Single-module linking | `errs, 0` | Linking |
| 7 | L88 | test_link_two_modules | Multi-module linking | `—` | Linking |
| 8 | L114 | test_relocation_patches_call | Relocatio | `—` | Functional |
| 9 | L139 | test_duplicate_symbol_error | Error detectio | `—` | Negative/error |
| 10 | L153 | test_undefined_symbol_error | Error detectio | `errs >= 1); /* undefined symbol */` | Negative/error |
| 11 | L165 | test_unresolved_import_error | Error detectio | `errs >= 1); /* unresolved import */` | Negative/error |
| 12 | L179 | test_resolve_after_link | Symbol resolutio | `—` | Linking |
| 13 | L199 | test_local_symbol_not_global | Local symbols | `—` | Linking |

---

## Suite 7: Compiler: Self-Hosting

**Source**: `tools/compiler/tests/test_selfhost.c`
**Runtime Assertions**: 13
**Source-Level Entries**: 13
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L16 | test_selfhost_identity | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test("int main() { return 42; }\n", 42), 0` | Functional |
| 2 | L21 | test_selfhost_arithmetic | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Arithmetic |
| 3 | L33 | test_selfhost_subtraction | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Arithmetic |
| 4 | L42 | test_selfhost_nested_arithmetic | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Arithmetic |
| 5 | L52 | test_selfhost_while_loop | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Functional |
| 6 | L66 | test_selfhost_if_true | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Functional |
| 7 | L80 | test_selfhost_if_false | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Functional |
| 8 | L94 | test_selfhost_multiple_vars | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Arithmetic |
| 9 | L108 | test_selfhost_factorial_like | Roundtrip tests: compile seT6-C → bytecode → run on VM → ver | `selfhost_roundtrip_test(` | Functional |
| 10 | L124 | test_selfhost_tokenizer_compiles | Tokenizer compilation tests | `bytecode[len - 1], OP_HALT` | Parsing |
| 11 | L133 | test_selfhost_tokenizer_bytecode_reasonable | Tokenizer compilation tests | `—` | Parsing |
| 12 | L145 | test_selfhost_verify | Self-hosting verification test | `result.compilation_ok, 1` | Functional |
| 13 | L155 | test_bootstrap_self_test | Bootstrap self-test | `bootstrap_self_test(), 0` | Initialization |

---

## Suite 8: Compiler: Arrays

**Source**: `tools/compiler/tests/test_arrays.c`
**Runtime Assertions**: 12
**Source-Level Entries**: 12
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L16 | test_create_array_decl | IR-level array tests | `e->type, NODE_ARRAY_DECL` | Functional |
| 2 | L26 | test_create_array_decl_with_init | IR-level array tests | `e->array_size, 3` | Initialization |
| 3 | L41 | test_create_array_access | IR-level array tests | `e->type, NODE_ARRAY_ACCESS` | Access control |
| 4 | L51 | test_create_array_assign | IR-level array tests | `e->type, NODE_ARRAY_ASSIGN` | Functional |
| 5 | L65 | test_parse_array_decl | Parser-level array tests | `prog->type, NODE_PROGRAM` | Parsing |
| 6 | L74 | test_parse_array_decl_init | Parser-level array tests | `—` | Initialization |
| 7 | L81 | test_parse_array_access | Parser-level array tests | `—` | Access control |
| 8 | L88 | test_parse_array_assign | Parser-level array tests | `—` | Parsing |
| 9 | L97 | test_compile_array_init_and_access | Bootstrap compilation of array code | `—` | Access control |
| 10 | L115 | test_compile_array_assign_and_read | Bootstrap compilation of array code | `—` | Functional |
| 11 | L135 | test_compile_array_with_loop | Bootstrap compilation of array code | `—` | Functional |
| 12 | L159 | test_optimize_array_const_index | Optimizer tests for arrays | `access->type, NODE_ARRAY_ACCESS` | Functional |

---

## Suite 9: Compiler: Ternary Hardware

**Source**: `tools/compiler/tests/test_hardware.c`
**Runtime Assertions**: 22
**Source-Level Entries**: 22
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L15 | test_trit_add_basic | Single-trit gate tests | `trit_add(TRIT_P, TRIT_N, &carry), TRIT_Z` | Arithmetic |
| 2 | L32 | test_trit_add_carry | Single-trit gate tests | `trit_add(TRIT_P, TRIT_P, &carry), TRIT_N` | Arithmetic |
| 3 | L49 | test_trit_mul | Single-trit gate tests | `trit_mul(TRIT_P, TRIT_P), TRIT_P);   /*  1 *  1 =  1 */` | Arithmetic |
| 4 | L60 | test_trit_min | Single-trit gate tests | `trit_min(TRIT_P, TRIT_N), TRIT_N` | Boundary |
| 5 | L70 | test_trit_max | Single-trit gate tests | `trit_max(TRIT_P, TRIT_N), TRIT_P` | Boundary |
| 6 | L80 | test_trit_inverter | Single-trit gate tests | `(trit)(-(int)TRIT_P), TRIT_N` | Functional |
| 7 | L89 | test_trit_word_add | Word-level tests | `trit_word_to_int(res), 2` | Arithmetic |
| 8 | L111 | test_trit_word_mul | Word-level tests | `trit_word_to_int(res), 9` | Arithmetic |
| 9 | L133 | test_trit_word_conversion_roundtrip | Word-level tests | `trit_word_to_int(w), test_values[i]` | Transformation |
| 10 | L145 | test_trit_word_sub_via_negate | Word-level tests | `—` | Arithmetic |
| 11 | L173 | test_alu_sim_add | ALU simulation tests (C equivalent of Verilog ALU) | `alu_sim(1, 1, 0), 2` | Arithmetic |
| 12 | L179 | test_alu_sim_sub | ALU simulation tests (C equivalent of Verilog ALU) | `alu_sim(1, 1, 1), 0` | Arithmetic |
| 13 | L185 | test_alu_sim_mul | ALU simulation tests (C equivalent of Verilog ALU) | `alu_sim(3, 3, 2), 9` | Arithmetic |
| 14 | L298 | test_proc_sim_push_halt | Phase 4: Full processor simulation (C software model) | `p.halted, 1` | Functional |
| 15 | L308 | test_proc_sim_arithmetic | Phase 4: Full processor simulation (C software model) | `proc_sim_tos(&p), 13` | Arithmetic |
| 16 | L338 | test_proc_sim_stack_ops | Phase 4: Full processor simulation (C software model) | `—` | Memory |
| 17 | L378 | test_proc_sim_return_stack | Phase 4: Full processor simulation (C software model) | `proc_sim_tos(&p), 42` | Memory |
| 18 | L390 | test_proc_sim_memory | Phase 4: Full processor simulation (C software model) | `—` | Memory |
| 19 | L404 | test_proc_sim_compare | Phase 4: Full processor simulation (C software model) | `—` | Functional |
| 20 | L435 | test_proc_sim_neg | Phase 4: Full processor simulation (C software model) | `proc_sim_tos(&p), -5` | Functional |
| 21 | L446 | test_proc_sim_complex_program | Phase 4: Full processor simulation (C software model) | `—` | Parsing |
| 22 | L461 | test_verilog_emit_full | Phase 4: Full processor simulation (C software model) | `emit_verilog_testbench_full(code, 8, "/tmp/test_auto_full.v"), 0` | Functional |

---

## Suite 10: seT6 Boot (Native)

**Source**: `src/init.c`
**Runtime Assertions**: 178
**Source-Level Entries**: 174
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

> **Note**: 4 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L69 | mem_init: 32 pages total | 1. Full kernel init | `total == 32` | Memory |
| 2 | L70 | mem_init: 32 pages free | 1. Full kernel init | `free_pg == 32` | Memory |
| 3 | L71 | mem_init: 0 pages allocated | 1. Full kernel init | `alloc == 0` | Memory |
| 4 | L78 | mem_alloc: pg0 >= 0 | Memory Manager | `pg0 >= 0` | Memory |
| 5 | L79 | mem_alloc: pg1 >= 0 | Memory Manager | `pg1 >= 0` | Memory |
| 6 | L80 | mem_alloc: pg0 != pg1 | Memory Manager | `pg0 != pg1` | Memory |
| 7 | L83 | mem_stats: 30 free after 2 allocs | Memory Manager | `free_pg == 30` | Memory |
| 8 | L84 | mem_stats: 2 allocated | Memory Manager | `alloc == 2` | Memory |
| 9 | L88 | mem_read: freshly allocated = Unknown | Memory Manager | `v == TRIT_UNKNOWN` | Memory |
| 10 | L92 | mem_write: succeeds on allocated page | Memory Manager | `wr == 0` | Memory |
| 11 | L94 | mem_read: reads back True | Memory Manager | `v == TRIT_TRUE` | Functional |
| 12 | L99 | mem_write: fails on read-only page | Memory Manager | `wr == -1` | Negative/error |
| 13 | L104 | mem_free: succeeds | Memory Manager | `fr == 0` | Memory |
| 14 | L106 | mem_free: scrubbed (reads Unknown from freed) | Memory Manager | `v == TRIT_UNKNOWN` | Memory |
| 15 | L109 | mem_stats: 31 free after free | Memory Manager | `free_pg == 31` | Memory |
| 16 | L113 | mem_free: double-free returns -1 | Memory Manager | `fr == -1` | Memory |
| 17 | L117 | mem_reserve: succeeds | Memory Manager | `rsv == 0` | Functional |
| 18 | L120 | mem_alloc: does not return reserved page | Memory Manager | `pg_rsv != 30` | Logic |
| 19 | L126 | cap_create: root cap >= 0 | Capabilities | `root >= 0` | Access control |
| 20 | L127 | cap_check: root has READ | Capabilities | `kernel_cap_check(&ks, root, 1) == TRIT_TRUE` | Access control |
| 21 | L128 | cap_check: root has WRITE | Capabilities | `kernel_cap_check(&ks, root, 2) == TRIT_TRUE` | Access control |
| 22 | L129 | cap_check: root has GRANT | Capabilities | `kernel_cap_check(&ks, root, 4) == TRIT_TRUE` | Access control |
| 23 | L133 | cap_grant: ro cap >= 0 | Capabilities | `ro >= 0` | Access control |
| 24 | L134 | cap_check: ro has READ | Capabilities | `kernel_cap_check(&ks, ro, 1) == TRIT_TRUE` | Access control |
| 25 | L135 | cap_check: ro denies WRITE | Capabilities | `kernel_cap_check(&ks, ro, 2) != TRIT_TRUE` | Access control |
| 26 | L136 | cap_check: ro denies GRANT | Capabilities | `kernel_cap_check(&ks, ro, 4) != TRIT_TRUE` | Access control |
| 27 | L140 | cap_revoke: succeeds | Capabilities | `rv == 0` | Access control |
| 28 | L141 | cap_check: revoked denies READ | Capabilities | `kernel_cap_check(&ks, ro, 1) != TRIT_TRUE` | Access control |
| 29 | L148 | thread_create: high prio tid >= 0 | Scheduler | `sr.retval >= 0` | Scheduling |
| 30 | L152 | thread_create: normal prio tid >= 0 | Scheduler | `sr.retval >= 0` | Logic |
| 31 | L155 | thread_create: low prio tid >= 0 | Scheduler | `sr.retval >= 0` | Scheduling |
| 32 | L158 | yield: picks highest priority | Scheduler | `sr.retval == tid_hi` | Scheduling |
| 33 | L162 | sched_stats: 3 threads total | Scheduler | `total_t == 3` | Scheduling |
| 34 | L163 | sched_stats: 1 context switch | Scheduler | `ctx_sw == 1` | Scheduling |
| 35 | L168 | yield after block: picks next thread | Scheduler | `sr.retval != tid_hi` | Memory |
| 36 | L172 | yield after unblock: picks high prio again | Scheduler | `sr.retval == tid_hi` | Memory |
| 37 | L177 | yield after demote: picks different thread | Scheduler | `sr.retval != tid_hi` | Scheduling |
| 38 | L183 | endpoint_create: ep >= 0 | IPC Endpoints | `ep >= 0` | IPC |
| 39 | L189 | msg_build: length = 3 | IPC Endpoints | `msg.length == 3` | Functional |
| 40 | L190 | msg_build: badge = 42 | IPC Endpoints | `msg.sender_badge == 42` | Negative/error |
| 41 | L191 | msg_build: word[0] = True | IPC Endpoints | `msg.words[0] == TRIT_TRUE` | Functional |
| 42 | L192 | msg_build: word[1] = Unknown | IPC Endpoints | `msg.words[1] == TRIT_UNKNOWN` | Functional |
| 43 | L193 | msg_build: word[2] = False | IPC Endpoints | `msg.words[2] == TRIT_FALSE` | Functional |
| 44 | L197 | ipc_send: blocks (no receiver) | IPC Endpoints | `send_r == 1` | Memory |
| 45 | L202 | ipc_recv: immediate (sender was waiting) | IPC Endpoints | `recv_r == 0` | IPC |
| 46 | L203 | ipc_recv: word[0] = True | IPC Endpoints | `recv_msg.words[0] == TRIT_TRUE` | IPC |
| 47 | L204 | ipc_recv: badge = 42 | IPC Endpoints | `recv_msg.sender_badge == 42` | Negative/error |
| 48 | L208 | ipc_recv: blocks (no sender) | IPC Endpoints | `recv_r == 1` | Memory |
| 49 | L212 | ipc_send: immediate (receiver waiting) | IPC Endpoints | `send_r == 0` | IPC |
| 50 | L216 | endpoint_destroy: succeeds | IPC Endpoints | `ed == 0` | IPC |
| 51 | L218 | ipc_send: fails on destroyed ep | IPC Endpoints | `send_r == -1` | Negative/error |
| 52 | L224 | notification_create: notif >= 0 | IPC Notifications | `notif >= 0` | IPC |
| 53 | L228 | ipc_wait: blocks (no signal) | IPC Notifications | `wait_r == 1` | Memory |
| 54 | L232 | ipc_signal: succeeds | IPC Notifications | `sig_r == 0` | IPC |
| 55 | L236 | ipc_wait: immediate (signal pending) | IPC Notifications | `wait_r == 0` | IPC |
| 56 | L240 | ipc_wait: blocks (signal consumed) | IPC Notifications | `wait_r == 1` | Arithmetic |
| 57 | L246 | MMAP syscall: page >= 0 | Syscall Integratio | `sr.retval >= 0` | Memory |
| 58 | L247 | MMAP syscall: result = True | Syscall Integratio | `sr.result_trit == TRIT_TRUE` | Transformation |
| 59 | L250 | LOAD_BALANCE: succeeds | Syscall Integratio | `sr.retval == 0` | Functional |
| 60 | L253 | DOT_TRIT: unknown regs dot = 0 | Syscall Integratio | `sr.retval == 0` | Functional |
| 61 | L256 | FFT_STEP syscall: succeeds | Syscall Integratio | `sr.retval >= 0` | Functional |
| 62 | L259 | RADIX_CONV syscall: converts 42 | Syscall Integratio | `sr.retval > 0` | Transformation |
| 63 | L262 | Unknown syscall: returns -1 | Syscall Integratio | `sr.retval == -1` | Functional |
| 64 | L273 | stack: pop = False (LIFO) | Two-Stack Model | `popped == TRIT_FALSE` | Memory |
| 65 | L275 | stack: pop = True (LIFO) | Two-Stack Model | `popped == TRIT_TRUE` | Memory |
| 66 | L277 | stack: underflow = Unknown | Two-Stack Model | `popped == TRIT_UNKNOWN` | Boundary |
| 67 | L283 | return_stack: pop = 0xFF | Two-Stack Model | `ret == 0xFF` | Memory |
| 68 | L285 | return_stack: pop = 0x42 | Two-Stack Model | `ret == 0x42` | Memory |
| 69 | L290 | AND(T, U) = U | Kleene Logic | `trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 70 | L291 | AND(T, F) = F | Kleene Logic | `trit_and(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE` | Functional |
| 71 | L292 | AND(T, T) = T | Kleene Logic | `trit_and(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE` | Functional |
| 72 | L293 | OR(T, U) = T | Kleene Logic | `trit_or(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_TRUE` | Functional |
| 73 | L294 | OR(F, U) = U | Kleene Logic | `trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 74 | L295 | NOT(T) = F | Kleene Logic | `trit_not(TRIT_TRUE) == TRIT_FALSE` | Functional |
| 75 | L296 | NOT(F) = T | Kleene Logic | `trit_not(TRIT_FALSE) == TRIT_TRUE` | Functional |
| 76 | L297 | NOT(U) = U | Kleene Logic | `trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 77 | L300 | inc(-1) = 0 | Kleene Logic | `trit_inc(TRIT_FALSE) == TRIT_UNKNOWN` | Functional |
| 78 | L301 | inc(0) = +1 | Kleene Logic | `trit_inc(TRIT_UNKNOWN) == TRIT_TRUE` | Functional |
| 79 | L302 | inc(+1) = -1 | Kleene Logic | `trit_inc(TRIT_TRUE) == TRIT_FALSE` | Functional |
| 80 | L327 | zero_count(U_all) = 32 | SIMD Packed Ops | `zc == 32` | Functional |
| 81 | L328 | is_sparse(U_all) = 1 | SIMD Packed Ops | `trit2_reg32_is_sparse(rb)` | Parsing |
| 82 | L329 | is_sparse(T_all) = 0 | SIMD Packed Ops | `!trit2_reg32_is_sparse(ra)` | Parsing |
| 83 | L334 | has_fault: detects injected fault | SIMD Packed Ops | `trit2_reg32_has_fault(rf)` | Functional |
| 84 | L335 | has_fault: clean register = 0 | SIMD Packed Ops | `!trit2_reg32_has_fault(ra)` | Hardware/ALU |
| 85 | L338 | trit_to_trit2(T) = 0x03 | SIMD Packed Ops | `trit_to_trit2(TRIT_TRUE) == TRIT2_TRUE` | Functional |
| 86 | L339 | trit_to_trit2(U) = 0x01 | SIMD Packed Ops | `trit_to_trit2(TRIT_UNKNOWN) == TRIT2_UNKNOWN` | Functional |
| 87 | L340 | trit_to_trit2(F) = 0x00 | SIMD Packed Ops | `trit_to_trit2(TRIT_FALSE) == TRIT2_FALSE` | Functional |
| 88 | L341 | trit2_to_trit(0x03) = T | SIMD Packed Ops | `trit2_to_trit(TRIT2_TRUE) == TRIT_TRUE` | Functional |
| 89 | L342 | trit2_to_trit(0x01) = U | SIMD Packed Ops | `trit2_to_trit(TRIT2_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 90 | L343 | trit2_to_trit(0x02) = U (fault->safe) | SIMD Packed Ops | `trit2_to_trit(TRIT2_FAULT) == TRIT_UNKNOWN` | Functional |
| 91 | L353 | dot_trit: all-unknown = 0 | DOT_TRIT | `dp == 0` | Functional |
| 92 | L359 | dot_trit: T??T = 32 | DOT_TRIT | `dp == 32` | Functional |
| 93 | L364 | dot_trit: T??F = -32 | DOT_TRIT | `dp == -32` | Functional |
| 94 | L372 | dot_trit: mixed = -30 | DOT_TRIT | `dp == -30` | Functional |
| 95 | L381 | dot_trit: sparse path = 2 | DOT_TRIT | `dp == 2` | Parsing |
| 96 | L382 | dot_trit: sparse_skip > 0 | DOT_TRIT | `mr.dot_sparse_skip > 0` | Parsing |
| 97 | L390 | dot_trit_sparse: 2:4 = 16 | DOT_TRIT | `dps == 16` | Parsing |
| 98 | L393 | dot_trit: acc = last result | DOT_TRIT | `mr.dot_acc == 16` | Parsing |
| 99 | L394 | dot_trit: total_ops > 0 | DOT_TRIT | `mr.dot_total_ops > 0` | Functional |
| 100 | L398 | dot_trit: invalid reg_a = 0 | DOT_TRIT | `dp == 0` | Negative/error |
| 101 | L400 | dot_trit: invalid reg_b = 0 | DOT_TRIT | `dp == 0` | Negative/error |
| 102 | L415 | fft_step: groups > 0 | FFT_STEP | `groups > 0` | Functional |
| 103 | L416 | fft_step: stage incremented | FFT_STEP | `mr.fft_stage == 1` | Arithmetic |
| 104 | L419 | fft_step: no faults in output | FFT_STEP | `!trit2_reg32_has_fault(mr.regs[1])` | Functional |
| 105 | L426 | fft_step: uniform input groups | FFT_STEP | `groups > 0` | Functional |
| 106 | L432 | fft_step: out[0] defined | FFT_STEP | `out0 != TRIT2_FAULT` | Functional |
| 107 | L433 | fft_step: out[1] defined | FFT_STEP | `out1 != TRIT2_FAULT` | Functional |
| 108 | L434 | fft_step: out[2] defined | FFT_STEP | `out2 != TRIT2_FAULT` | Functional |
| 109 | L438 | fft_step: stride=3 groups | FFT_STEP | `g2 >= 0` | Functional |
| 110 | L439 | fft_step: stage = 2 after two steps | FFT_STEP | `mr.fft_stage == 2` | Functional |
| 111 | L443 | fft_step: bad reg_in = -1 | FFT_STEP | `bad == -1` | Negative/error |
| 112 | L445 | fft_step: stride=0 = -1 | FFT_STEP | `bad == -1` | Functional |
| 113 | L454 | radix_conv: 0 → 0 non-zero trits | RADIX_CONV | `nz == 0` | Functional |
| 114 | L456 | radix_conv: 0 roundtrip | RADIX_CONV | `back == 0` | Transformation |
| 115 | L460 | radix_conv: 1 → 1 non-zero trit | RADIX_CONV | `nz == 1` | Functional |
| 116 | L462 | radix_conv: 1 roundtrip | RADIX_CONV | `back == 1` | Transformation |
| 117 | L467 | radix_conv: 42 → multiple non-zero | RADIX_CONV | `nz > 0` | Arithmetic |
| 118 | L469 | radix_conv: 42 roundtrip | RADIX_CONV | `back == 42` | Transformation |
| 119 | L473 | radix_conv: -13 → non-zero | RADIX_CONV | `nz > 0` | Functional |
| 120 | L475 | radix_conv: -13 roundtrip | RADIX_CONV | `back == -13` | Transformation |
| 121 | L479 | radix_conv: 729 → non-zero | RADIX_CONV | `nz > 0` | Functional |
| 122 | L481 | radix_conv: 729 roundtrip | RADIX_CONV | `back == 729` | Transformation |
| 123 | L486 | radix_conv: 364 (tryte max) roundtrip | RADIX_CONV | `back == 364` | Boundary |
| 124 | L490 | radix_conv: -364 (tryte min) roundtrip | RADIX_CONV | `back == -364` | Boundary |
| 125 | L494 | radix_conv: bad reg = -1 | RADIX_CONV | `nz == -1` | Negative/error |
| 126 | L510 | trit_lb: total_insns = 4 | TRIT_LB Telemetry | `snap.total_insns == 4` | Functional |
| 127 | L511 | trit_lb: trit_ratio = 100% | TRIT_LB Telemetry | `snap.trit_ratio_pct == 100` | Functional |
| 128 | L512 | trit_lb: affinity = trit core | TRIT_LB Telemetry | `snap.suggested_affinity == 1` | Initialization |
| 129 | L517 | trit_lb: diluted ratio < 100% | TRIT_LB Telemetry | `snap.trit_ratio_pct < 100` | Functional |
| 130 | L522 | trit_lb: reset total = 0 | TRIT_LB Telemetry | `snap.total_insns == 0` | Initialization |
| 131 | L532 | trit_lb: sparse_hits = 1 | TRIT_LB Telemetry | `snap.sparse_ratio_pct > 0` | Parsing |
| 132 | L544 | mem_exhaust: all 4 pages allocated | Edge Cases | `p0>=0 && p1>=0 && p2>=0 && p3>=0` | Memory |
| 133 | L546 | mem_exhaust: 5th alloc fails | Edge Cases | `p4 == -1` | Negative/error |
| 134 | L552 | cap: grant without G right fails | Edge Cases | `derived == -1` | Negative/error |
| 135 | L556 | cap: first revoke succeeds | Edge Cases | `rv2 == 0` | Access control |
| 136 | L558 | cap: re-revoke succeeds (idempotent) | Edge Cases | `rv2 == 0` | Access control |
| 137 | L559 | cap: revoked cap denies read | Edge Cases | `kernel_cap_check(&ks2, rw_cap, 1) != TRIT_TRUE` | Access control |
| 138 | L564 | sched: create tid >= 0 | Edge Cases | `tid >= 0` | Scheduling |
| 139 | L566 | sched: destroy succeeds | Edge Cases | `dr == 0` | Scheduling |
| 140 | L569 | sched: 0 ready threads after destroy | Edge Cases | `rt == 0` | Scheduling |
| 141 | L574 | trit_checked(1) = T | Edge Cases | `valid_t == TRIT_TRUE` | Type system |
| 142 | L575 | trit_checked(1): no fault | Edge Cases | `fault_flag == 0` | Type system |
| 143 | L577 | trit_checked(5) = U (clamped) | Edge Cases | `invalid_t == TRIT_UNKNOWN` | Boundary |
| 144 | L578 | trit_checked(5): fault set | Edge Cases | `fault_flag == 1` | Type system |
| 145 | L587 | bulk AND[0] = U | Edge Cases | `trit2_reg32_get(&bulk_dst[0], 0) == TRIT2_UNKNOWN` | Functional |
| 146 | L588 | bulk AND[1] = F | Edge Cases | `trit2_reg32_get(&bulk_dst[1], 0) == TRIT2_FALSE` | Functional |
| 147 | L597 | census: 1 false | Edge Cases | `nf == 1` | Functional |
| 148 | L598 | census: 1 unknown | Edge Cases | `nu == 1` | Functional |
| 149 | L599 | census: 30 true | Edge Cases | `nt == 30` | Functional |
| 150 | L600 | census: 0 faults | Edge Cases | `nx == 0` | Functional |
| 151 | L613 | wcet: 5 probes registered | WCET Analysis | `wcet.probe_count == 5` | Hardware/ALU |
| 152 | L623 | wcet: no violations (within budget) | WCET Analysis | `wcet_check(&wcet) == 0` | Functional |
| 153 | L624 | wcet: alloc max = 280 | WCET Analysis | `wcet.probes[w_alloc].observed_max == 280` | Boundary |
| 154 | L625 | wcet: alloc util < 100% | WCET Analysis | `wcet_utilization_pct(&wcet, w_alloc) < 100` | Memory |
| 155 | L626 | wcet: alloc avg > 0 | WCET Analysis | `wcet_average(&wcet, w_alloc) > 0` | Memory |
| 156 | L630 | wcet: 1 violation after overrun | WCET Analysis | `wcet_check(&wcet) == 1` | Functional |
| 157 | L631 | wcet: dot utilization > 100% | WCET Analysis | `wcet_utilization_pct(&wcet, w_dot) > 100` | Functional |
| 158 | L632 | wcet: global_tick accumulated | WCET Analysis | `wcet.global_tick > 0` | Arithmetic |
| 159 | L640 | qemu: init NONE model | QEMU Ternary Noise Simulatio | `qn.model == NOISE_NONE` | Initialization |
| 160 | L645 | qemu: NONE preserves TRUE | QEMU Ternary Noise Simulatio | `noised == TRIT_TRUE` | Functional |
| 161 | L647 | qemu: NONE preserves FALSE | QEMU Ternary Noise Simulatio | `noised == TRIT_FALSE` | Functional |
| 162 | L656 | qemu: UNIFORM flips some trits | QEMU Ternary Noise Simulatio | `flipped > 0` | Functional |
| 163 | L657 | qemu: UNIFORM flip rate < 20% | QEMU Ternary Noise Simulatio | `flipped < 2000` | Functional |
| 164 | L666 | qemu: GAUSSIAN flips some trits | QEMU Ternary Noise Simulatio | `flipped > 0` | Functional |
| 165 | L667 | qemu: GAUSSIAN flip rate < 15% | QEMU Ternary Noise Simulatio | `flipped < 1500` | Functional |
| 166 | L676 | qemu: MEMRISTIVE flips some trits | QEMU Ternary Noise Simulatio | `flipped > 0` | Functional |
| 167 | L686 | qemu: reg32 noise injects diffs | QEMU Ternary Noise Simulatio | `diffs > 0` | Functional |
| 168 | L687 | qemu: reg32 injected count matches | QEMU Ternary Noise Simulatio | `injected == diffs` | Functional |
| 169 | L690 | qemu: total_reads > 0 | QEMU Ternary Noise Simulatio | `qn.total_reads > 0` | Functional |
| 170 | L691 | qemu: faults_injected > 0 | QEMU Ternary Noise Simulatio | `qn.faults_injected > 0` | Functional |
| 171 | L693 | qemu: flip rate reasonable | QEMU Ternary Noise Simulatio | `rate > 0.001 && rate < 0.5` | Functional |
| 172 | L697 | qemu: reset zeroes total_reads | QEMU Ternary Noise Simulatio | `qn.total_reads == 0` | Initialization |
| 173 | L698 | qemu: reset zeroes faults | QEMU Ternary Noise Simulatio | `qn.faults_injected == 0` | Initialization |
| 174 | L707 | qemu: COSMIC flips < 1% | QEMU Ternary Noise Simulatio | `flipped < 1000` | Functional |

---

## Suite 11: Integration

**Source**: `tests/test_integration.c`
**Runtime Assertions**: 56
**Source-Level Entries**: 48
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

> **Note**: 8 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L52 | test_producer_consumer | Scenario: Producer-Consumer with Shared Memory | `function-level test` | Arithmetic |
| 2 | L62 | producer thread created | Phase 1: Thread Creatio | `producer >= 0` | Scheduling |
| 3 | L63 | consumer thread created | Phase 1: Thread Creatio | `consumer >= 0` | Arithmetic |
| 4 | L71 | shared page allocated | Phase 2: Memory Allocatio | `shared_page >= 0` | Memory |
| 5 | L78 | write to shared page succeeds | Phase 2: Memory Allocatio | `w == 0` | Memory |
| 6 | L85 | shared page: slot 0 = True | Phase 2: Memory Allocatio | `r0 == TRIT_TRUE` | Memory |
| 7 | L86 | shared page: slot 1 = Unknown | Phase 2: Memory Allocatio | `r1 == TRIT_UNKNOWN` | Memory |
| 8 | L87 | shared page: slot 2 = False | Phase 2: Memory Allocatio | `r2 == TRIT_FALSE` | Memory |
| 9 | L92 | root cap created | Phase 3: Capability Setup | `root_cap >= 0` | Access control |
| 10 | L96 | consumer cap granted | Phase 3: Capability Setup | `consumer_cap >= 0` | Arithmetic |
| 11 | L97 | consumer can read | Phase 3: Capability Setup | `kernel_cap_check(&ks, consumer_cap, 1) == TRIT_TRUE` | Arithmetic |
| 12 | L98 | consumer cannot write | Phase 3: Capability Setup | `kernel_cap_check(&ks, consumer_cap, 2) != TRIT_TRUE` | Arithmetic |
| 13 | L103 | endpoint created | Phase 4: IPC Communicatio | `ep >= 0` | IPC |
| 14 | L115 | producer send (blocks) | Phase 4: IPC Communicatio | `send_r == 1` | Memory |
| 15 | L124 | consumer recv success | Phase 4: IPC Communicatio | `recv_r == 0` | Arithmetic |
| 16 | L125 | recv badge = 100 | Phase 4: IPC Communicatio | `recv_msg.sender_badge == 100` | Negative/error |
| 17 | L126 | recv msg[0] = True | Phase 4: IPC Communicatio | `recv_msg.words[0] == TRIT_TRUE` | IPC |
| 18 | L127 | recv msg[1] = Unknown | Phase 4: IPC Communicatio | `recv_msg.words[1] == TRIT_UNKNOWN` | IPC |
| 19 | L128 | recv msg[2] = False | Phase 4: IPC Communicatio | `recv_msg.words[2] == TRIT_FALSE` | IPC |
| 20 | L133 | yield picks producer (high prio) | Phase 5: Scheduling | `next == producer` | Scheduling |
| 21 | L155 | DOT_TRIT on received data = +1 | Phase 6: Multi-Radix Compute | `dp == 1` | Functional |
| 22 | L160 | RADIX_CONV roundtrip of dot result | Phase 6: Multi-Radix Compute | `back == dp` | Transformation |
| 23 | L164 | telemetry: 2 trit instructions | Phase 6: Multi-Radix Compute | `snap.total_insns >= 2` | Hardware/ALU |
| 24 | L171 | consumer cap revoked | Phase 7: Teardow | `rev == 0` | Arithmetic |
| 25 | L172 | consumer cap no longer valid | Phase 7: Teardow | `kernel_cap_check(&ks, consumer_cap, 1) != TRIT_TRUE` | Arithmetic |
| 26 | L176 | shared page freed | Phase 7: Teardow | `fr == 0` | Memory |
| 27 | L180 | freed page scrubbed to Unknown | Phase 7: Teardow | `scrubbed == TRIT_UNKNOWN` | Memory |
| 28 | L185 | producer destroyed | Phase 7: Teardow | `dp1 == 0` | Functional |
| 29 | L186 | consumer destroyed | Phase 7: Teardow | `dc1 == 0` | Arithmetic |
| 30 | L190 | endpoint destroyed | Phase 7: Teardow | `ed == 0` | IPC |
| 31 | L196 | all pages freed after teardown | Phase 8: Clean State Verificatio | `alloc == 0` | Memory |
| 32 | L200 | no ready threads after teardown | Phase 8: Clean State Verificatio | `ready_t == 0` | Scheduling |
| 33 | L201 | no blocked threads after teardown | Phase 8: Clean State Verificatio | `blocked_t == 0` | Memory |
| 34 | L206 | test_notification_event_loop | Scenario: Notification-Driven Event Loop | `function-level test` | IPC |
| 35 | L215 | handler thread created | Scenario: Notification Event Loop | `handler >= 0` | Scheduling |
| 36 | L219 | notification created | Scenario: Notification Event Loop | `notif >= 0` | IPC |
| 37 | L225 | signal succeeds | Scenario: Notification Event Loop | `sig == 0` | Functional |
| 38 | L229 | wait immediate after signal | Scenario: Notification Event Loop | `wait == 0` | Functional |
| 39 | L234 | wait blocks (no pending signal) | Scenario: Notification Event Loop | `wait == 1` | Memory |
| 40 | L241 | handler dead after destroy | Scenario: Notification Event Loop | `ready_t == 0` | Functional |
| 41 | L246 | test_radix_dot_pipeline | Scenario: Full RADIX_CONV + DOT_TRIT Pipeline | `function-level test` | IPC |
| 42 | L259 | reg0 = 13 | Scenario: Radix→Dot Pipeline | `v0 == 13` | Functional |
| 43 | L260 | reg1 = -13 | Scenario: Radix→Dot Pipeline | `v1 == -13` | Functional |
| 44 | L265 | dot(x, -x) <= 0 | Scenario: Radix→Dot Pipeline | `dp <= 0` | Functional |
| 45 | L269 | dot(x, x) > 0 | Scenario: Radix→Dot Pipeline | `norm > 0` | Functional |
| 46 | L274 | FFT on radix-converted data | Scenario: Radix→Dot Pipeline | `groups > 0` | Transformation |
| 47 | L278 | pipeline: telemetry total > 0 | Scenario: Radix→Dot Pipeline | `snap.total_insns > 0` | IPC |
| 48 | L279 | pipeline: trit ratio >= 50% | Scenario: Radix→Dot Pipeline | `snap.trit_ratio_pct >= 50` | IPC |

---

## Suite 12: seL4 Ternary Extensions

**Source**: `tests/test_sel4_ternary.c`
**Runtime Assertions**: 142
**Source-Level Entries**: 137
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

> **Note**: 5 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L46 | kernel init: tick = 0 | Kernel Init | `k.tick == 0` | Initialization |
| 2 | L47 | kernel init: no threads | Kernel Init | `k.tcb_count == 0` | Scheduling |
| 3 | L48 | kernel init: no endpoints | Kernel Init | `k.ep_count == 0` | IPC |
| 4 | L49 | kernel init: cnodes valid | Kernel Init | `k.cnodes[0].validity == TRIT_TRUE` | Initialization |
| 5 | L50 | kernel init: irq control valid | Kernel Init | `k.irq_control.validity == TRIT_TRUE` | Initialization |
| 6 | L51 | kernel init: mdb empty | Kernel Init | `k.mdb.count == 0` | Negative/error |
| 7 | L57 | cap: root is valid | Capabilities | `root_cap.validity == TRIT_TRUE` | Access control |
| 8 | L58 | cap: root can read | Capabilities | `cap_has_right(&root_cap, root_cap.can_read) == TRIT_TRUE` | Access control |
| 9 | L59 | cap: root can write | Capabilities | `cap_has_right(&root_cap, root_cap.can_write) == TRIT_TRUE` | Access control |
| 10 | L63 | cap: child read = T | Capabilities | `child_cap.can_read == TRIT_TRUE` | Access control |
| 11 | L64 | cap: child write = F (reduced) | Capabilities | `child_cap.can_write == TRIT_FALSE` | Access control |
| 12 | L65 | cap: child grant = F (reduced) | Capabilities | `child_cap.can_grant == TRIT_FALSE` | Access control |
| 13 | L66 | cap: child badge = 42 | Capabilities | `child_cap.badge == 42` | Negative/error |
| 14 | L67 | cap: monotonicity (write) | Capabilities | `child_cap.can_write <= root_cap.can_write` | Access control |
| 15 | L71 | cap: pending read = U | Capabilities | `pending_cap.can_read == TRIT_UNKNOWN` | Access control |
| 16 | L75 | cap: revoked validity = F | Capabilities | `child_cap.validity == TRIT_FALSE` | Access control |
| 17 | L76 | cap: revoked read scrubbed to U | Capabilities | `child_cap.can_read == TRIT_UNKNOWN` | Access control |
| 18 | L80 | cap: null type = NONE | Capabilities | `null_cap.type == KOBJ_NONE` | Negative/error |
| 19 | L81 | cap: null validity = F | Capabilities | `null_cap.validity == TRIT_FALSE` | Negative/error |
| 20 | L87 | cnode: valid | CNode | `cn->validity == TRIT_TRUE` | Functional |
| 21 | L88 | cnode: slot_count = 0 | CNode | `cn->slot_count == 0` | Functional |
| 22 | L92 | cnode: insert slot 0 ok | CNode | `cnode_insert(cn, 0, cap1) == 0` | Functional |
| 23 | L93 | cnode: insert slot 1 ok | CNode | `cnode_insert(cn, 1, root_cap) == 0` | Functional |
| 24 | L94 | cnode: slot_count = 2 | CNode | `cn->slot_count == 2` | Functional |
| 25 | L98 | cnode: lookup slot 0 type = ENDPOINT | CNode | `looked && looked->type == KOBJ_ENDPOINT` | IPC |
| 26 | L99 | cnode: lookup slot 255 is null | CNode | `cnode_lookup(cn, 255)->type == KOBJ_NONE` | Negative/error |
| 27 | L102 | cnode: double insert fails | CNode | `cnode_insert(cn, 0, cap1) == -2` | Negative/error |
| 28 | L105 | cnode: delete slot 0 ok | CNode | `cnode_delete(cn, 0) == 0` | Functional |
| 29 | L106 | cnode: deleted slot is null | CNode | `cnode_lookup(cn, 0)->type == KOBJ_NONE` | Negative/error |
| 30 | L109 | cnode: OOB lookup returns NULL | CNode | `cnode_lookup(cn, -1) == NULL` | Negative/error |
| 31 | L110 | cnode: OOB lookup returns NULL (256) | CNode | `cnode_lookup(cn, 256) == NULL` | Negative/error |
| 32 | L119 | tcb: 3 threads created | CNode | `k.tcb_count == 3` | Scheduling |
| 33 | L120 | tcb: t0 is running | CNode | `k.tcbs[t0].state == THREAD_RUNNING` | Functional |
| 34 | L121 | tcb: t0 priority = T | CNode | `k.tcbs[t0].priority == TRIT_TRUE` | Scheduling |
| 35 | L122 | tcb: t1 priority = U | CNode | `k.tcbs[t1].priority == TRIT_UNKNOWN` | Scheduling |
| 36 | L123 | tcb: t2 domain = F | CNode | `k.tcbs[t2].domain == TRIT_FALSE` | Functional |
| 37 | L127 | tcb: t0 cspace_root = 0 | CNode | `k.tcbs[t0].cspace_root == 0` | Functional |
| 38 | L131 | tcb: t1 suspended (blocked) | CNode | `k.tcbs[t1].state == THREAD_BLOCKED` | Memory |
| 39 | L133 | tcb: t1 resumed (running) | CNode | `k.tcbs[t1].state == THREAD_RUNNING` | Arithmetic |
| 40 | L137 | tcb: t2 destroyed (inactive) | CNode | `k.tcbs[t2].state == THREAD_INACTIVE` | Functional |
| 41 | L138 | tcb: t2 validity = F | CNode | `k.tcbs[t2].validity == TRIT_FALSE` | Functional |
| 42 | L148 | sched: picks a thread | Scheduling | `sched_result >= 0` | Scheduling |
| 43 | L149 | sched: picks T-domain first | Scheduling | `k.tcbs[sched_result].domain == TRIT_TRUE` | Scheduling |
| 44 | L150 | sched: current_domain = T | Scheduling | `k.current_domain == TRIT_TRUE` | Scheduling |
| 45 | L151 | sched: tick incremented | Scheduling | `k.tick > 0` | Arithmetic |
| 46 | L165 | ep: created | Endpoints | `ep >= 0` | Functional |
| 47 | L166 | ep: valid | Endpoints | `k.endpoints[ep].validity == TRIT_TRUE` | Functional |
| 48 | L167 | ep: idle state | Endpoints | `k.endpoints[ep].queue_state == EP_IDLE` | Functional |
| 49 | L170 | ep: send enqueue ok | Endpoints | `endpoint_send_enqueue(&k.endpoints[ep], t0) == TRIT_TRUE` | IPC |
| 50 | L171 | ep: state = SEND_BLOCKED | Endpoints | `k.endpoints[ep].queue_state == EP_SEND_BLOCKED` | Memory |
| 51 | L175 | ep: dequeue = t0 | Endpoints | `dequeued == t0` | Functional |
| 52 | L176 | ep: back to idle | Endpoints | `k.endpoints[ep].queue_state == EP_IDLE` | Functional |
| 53 | L180 | ep: transfer ok | Endpoints | `endpoint_transfer(&k.endpoints[ep], &msg) == TRIT_TRUE` | Functional |
| 54 | L181 | ep: msg badge preserved | Endpoints | `k.endpoints[ep].last_msg.badge == 42` | Negative/error |
| 55 | L182 | ep: msg[0] = T | Endpoints | `k.endpoints[ep].last_msg.msg[0] == TRIT_TRUE` | Functional |
| 56 | L185 | ipc: kernel send ok | Endpoints | `set6_ipc_send(&k, ep, &msg) == TRIT_TRUE` | IPC |
| 57 | L191 | ntf: created | Notifications | `ntf >= 0` | Functional |
| 58 | L192 | ntf: valid | Notifications | `k.notifications[ntf].validity == TRIT_TRUE` | Functional |
| 59 | L193 | ntf: poll = 0 (no signals) | Notifications | `notification_poll(&k.notifications[ntf]) == 0` | Functional |
| 60 | L196 | ntf: signal bit 5 | Notifications | `notification_signal(&k.notifications[ntf], 5) == TRIT_TRUE` | Functional |
| 61 | L197 | ntf: signal bit 10 | Notifications | `notification_signal(&k.notifications[ntf], 10) == TRIT_TRUE` | Functional |
| 62 | L198 | ntf: poll = 2 | Notifications | `notification_poll(&k.notifications[ntf]) == 2` | Functional |
| 63 | L202 | ntf: consumed 2 signals | Notifications | `consumed == 2` | Arithmetic |
| 64 | L203 | ntf: poll after consume = 0 | Notifications | `notification_poll(&k.notifications[ntf]) == 0` | Arithmetic |
| 65 | L210 | ut: initial watermark = 0 | Untyped Memory | `ut->watermark == 0` | Initialization |
| 66 | L214 | ut: retype TCB ok | Untyped Memory | `child_idx >= 0` | Type system |
| 67 | L215 | ut: children_count = 1 | Untyped Memory | `ut->children_count == 1` | Functional |
| 68 | L216 | ut: child type = TCB | Untyped Memory | `ut->children[0] == KOBJ_TCB` | Type system |
| 69 | L220 | ut: retype EP ok | Untyped Memory | `child_idx >= 0` | Type system |
| 70 | L221 | ut: children_count = 2 | Untyped Memory | `ut->children_count == 2` | Functional |
| 71 | L225 | ut: revoke resets watermark | Untyped Memory | `ut->watermark == 0` | Initialization |
| 72 | L226 | ut: revoke resets children | Untyped Memory | `ut->children_count == 0` | Initialization |
| 73 | L227 | ut: revoke sets validity = U | Untyped Memory | `ut->validity == TRIT_UNKNOWN` | Functional |
| 74 | L233 | frame: valid | Frames | `fr->validity == TRIT_TRUE` | Functional |
| 75 | L234 | frame: unmapped | Frames | `fr->mapped_vaddr == -1` | Transformation |
| 76 | L237 | frame: map ok | Frames | `frame_map(fr, 0x1000, 0) == TRIT_TRUE` | Transformation |
| 77 | L238 | frame: mapped_vaddr = 0x1000 | Frames | `fr->mapped_vaddr == 0x1000` | Arithmetic |
| 78 | L239 | frame: mapped_asid = 0 | Frames | `fr->mapped_asid == 0` | Transformation |
| 79 | L242 | frame: double map = U | Frames | `frame_map(fr, 0x2000, 0) == TRIT_UNKNOWN` | Transformation |
| 80 | L245 | frame: unmap ok | Frames | `frame_unmap(fr) == TRIT_TRUE` | Transformation |
| 81 | L246 | frame: unmapped after unmap | Frames | `fr->mapped_vaddr == -1` | Transformation |
| 82 | L252 | pt: valid | Page Tables | `pt->validity == TRIT_TRUE` | Functional |
| 83 | L253 | pt: no mappings | Page Tables | `pt->mapped_count == 0` | Transformation |
| 84 | L258 | pt: mapped_count = 1 | Page Tables | `pt->mapped_count == 1` | Transformation |
| 85 | L261 | pt: lookup 0 = frame 0 | Page Tables | `page_table_lookup(pt, 0) == 0` | Functional |
| 86 | L262 | pt: lookup 1 = -1 (unmapped) | Page Tables | `page_table_lookup(pt, 1) == -1` | Transformation |
| 87 | L269 | pt: entry 0 writable = T | Page Tables | `pt->entries[0].writable == TRIT_TRUE` | Functional |
| 88 | L270 | pt: entry 0 executable = F | Page Tables | `pt->entries[0].executable == TRIT_FALSE` | Functional |
| 89 | L271 | pt: entry 0 user_access = T | Page Tables | `pt->entries[0].user_access == TRIT_TRUE` | Access control |
| 90 | L274 | pt: unmap entry 0 | Page Tables | `page_table_unmap(pt, 0) == TRIT_TRUE` | Transformation |
| 91 | L275 | pt: mapped_count = 0 | Page Tables | `pt->mapped_count == 0` | Transformation |
| 92 | L276 | pt: lookup 0 = -1 after unmap | Page Tables | `page_table_lookup(pt, 0) == -1` | Transformation |
| 93 | L281 | irq: control valid | IRQ Control | `k.irq_control.validity == TRIT_TRUE` | Functional |
| 94 | L284 | irq: set handler 0 | IRQ Control | `irq_handler_set(&k.irq_control, 0, ntf, t0) == TRIT_TRUE` | Functional |
| 95 | L285 | irq: handler 0 valid | IRQ Control | `k.irq_control.handlers[0].validity == TRIT_TRUE` | Functional |
| 96 | L286 | irq: handler 0 bound to ntf | IRQ Control | `k.irq_control.handlers[0].notif_index == ntf` | Boundary |
| 97 | L289 | irq: ack 0 | IRQ Control | `irq_handler_ack(&k.irq_control, 0) == TRIT_TRUE` | Functional |
| 98 | L290 | irq: trigger_count = 1 | IRQ Control | `k.irq_control.handlers[0].trigger_count == 1` | Functional |
| 99 | L293 | irq: set handler OOB | IRQ Control | `irq_handler_set(&k.irq_control, 99, 0, 0) == TRIT_FALSE` | Functional |
| 100 | L299 | asid: pool valid | ASID Pools | `pool->validity == TRIT_TRUE` | Memory |
| 101 | L300 | asid: initially empty | ASID Pools | `pool->allocated_count == 0` | Negative/error |
| 102 | L305 | asid: alloc 0 | ASID Pools | `asid0 == 0` | Memory |
| 103 | L306 | asid: alloc 1 | ASID Pools | `asid1 == 1` | Memory |
| 104 | L307 | asid: count = 2 | ASID Pools | `pool->allocated_count == 2` | Functional |
| 105 | L308 | asid: slot 0 = T | ASID Pools | `pool->asids[0] == TRIT_TRUE` | Functional |
| 106 | L311 | asid: free 0 ok | ASID Pools | `asid_pool_free(pool, 0) == TRIT_TRUE` | Memory |
| 107 | L312 | asid: count = 1 | ASID Pools | `pool->allocated_count == 1` | Functional |
| 108 | L313 | asid: slot 0 = F after free | ASID Pools | `pool->asids[0] == TRIT_FALSE` | Memory |
| 109 | L319 | mdb: root inserted | MDB (Mapping Database) | `mdb_root == 0` | Functional |
| 110 | L320 | mdb: root valid | MDB (Mapping Database) | `k.mdb.entries[0].validity == TRIT_TRUE` | Functional |
| 111 | L324 | mdb: child1 inserted | MDB (Mapping Database) | `mdb_c1 == 1` | Functional |
| 112 | L325 | mdb: child2 inserted | MDB (Mapping Database) | `mdb_c2 == 2` | Functional |
| 113 | L326 | mdb: root has child | MDB (Mapping Database) | `k.mdb.entries[mdb_root].first_child == mdb_c1` | Functional |
| 114 | L327 | mdb: child1 sibling = child2 | MDB (Mapping Database) | `k.mdb.entries[mdb_c1].next_sibling == mdb_c2` | Functional |
| 115 | L331 | mdb: grandchild inserted | MDB (Mapping Database) | `mdb_gc == 3` | Functional |
| 116 | L332 | mdb: child1 has grandchild | MDB (Mapping Database) | `k.mdb.entries[mdb_c1].first_child == mdb_gc` | Functional |
| 117 | L336 | mdb: child1 revoked | MDB (Mapping Database) | `k.mdb.entries[mdb_c1].validity == TRIT_FALSE` | Functional |
| 118 | L337 | mdb: grandchild revoked | MDB (Mapping Database) | `k.mdb.entries[mdb_gc].validity == TRIT_FALSE` | Functional |
| 119 | L338 | mdb: child2 still valid | MDB (Mapping Database) | `k.mdb.entries[mdb_c2].validity == TRIT_TRUE` | Functional |
| 120 | L343 | posix: errno(0) = T | POSIX Translatio | `posix_errno_to_trit(0) == TRIT_TRUE` | Functional |
| 121 | L344 | posix: errno(-11) = U (EAGAIN) | POSIX Translatio | `posix_errno_to_trit(-11) == TRIT_UNKNOWN` | Functional |
| 122 | L345 | posix: errno(-1) = F | POSIX Translatio | `posix_errno_to_trit(-1) == TRIT_FALSE` | Functional |
| 123 | L346 | posix: trit_to_errno(T) = 0 | POSIX Translatio | `trit_to_posix_errno(TRIT_TRUE) == 0` | Functional |
| 124 | L347 | posix: trit_to_errno(U) = -11 | POSIX Translatio | `trit_to_posix_errno(TRIT_UNKNOWN) == -11` | Functional |
| 125 | L349 | posix: nice(-10) = T | POSIX Translatio | `posix_nice_to_trit_priority(-10) == TRIT_TRUE` | Functional |
| 126 | L350 | posix: nice(0) = U | POSIX Translatio | `posix_nice_to_trit_priority(0) == TRIT_UNKNOWN` | Functional |
| 127 | L351 | posix: nice(10) = F | POSIX Translatio | `posix_nice_to_trit_priority(10) == TRIT_FALSE` | Functional |
| 128 | L356 | posix: stdin valid | POSIX Translatio | `posix_fd_check(&fdt, 0) == TRIT_TRUE` | Functional |
| 129 | L357 | posix: fd 99 invalid | POSIX Translatio | `posix_fd_check(&fdt, 99) == TRIT_FALSE` | Negative/error |
| 130 | L360 | posix: open fd = 3 | POSIX Translatio | `fd == 3` | Functional |
| 131 | L361 | posix: close fd 3 | POSIX Translatio | `posix_fd_close(&fdt, 3) == 0` | Functional |
| 132 | L362 | posix: closed fd invalid | POSIX Translatio | `posix_fd_check(&fdt, 3) == TRIT_FALSE` | Negative/error |
| 133 | L371 | cnode2: 2 caps inserted | CNode Revoke All | `cn2.slot_count == 2` | Access control |
| 134 | L374 | cnode2: validity = F after revoke | CNode Revoke All | `cn2.validity == TRIT_FALSE` | Functional |
| 135 | L375 | cnode2: slot[0] revoked | CNode Revoke All | `cn2.slots[0].validity == TRIT_FALSE` | Functional |
| 136 | L376 | cnode2: slot[1] revoked | CNode Revoke All | `cn2.slots[1].validity == TRIT_FALSE` | Functional |
| 137 | L379 | cnode2: lookup on revoked = NULL | CNode Revoke All | `cnode_lookup(&cn2, 0) == NULL` | Negative/error |

---

## Suite 13: Memory Safety

**Source**: `tests/test_memory_safety.c`
**Runtime Assertions**: 28
**Source-Level Entries**: 28
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L42 | Allocate page 1 | Memory Safety Tests | `page1 >= 0` | Memory |
| 2 | L45 | Allocate page 2 | Memory Safety Tests | `page2 >= 0` | Memory |
| 3 | L49 | Free page 1 | Memory Safety Tests | `r1 == 0` | Memory |
| 4 | L52 | Free page 2 | Memory Safety Tests | `r2 == 0` | Memory |
| 5 | L56 | Double free returns error | Memory Safety Tests | `r3 == -1` | Negative/error |
| 6 | L66 | Allocate page for read/write | Memory Safety Tests | `page >= 0` | Logic |
| 7 | L70 | Write within bounds | Memory Safety Tests | `wr == 0` | Boundary |
| 8 | L74 | Read matches write | Memory Safety Tests | `val == TRIT_TRUE` | Functional |
| 9 | L78 | Write at max offset | Memory Safety Tests | `wr == 0` | Boundary |
| 10 | L82 | Read at max offset | Memory Safety Tests | `val == TRIT_FALSE` | Boundary |
| 11 | L86 | Out-of-bounds write rejected | Memory Safety Tests | `wr == -1` | Boundary |
| 12 | L90 | Out-of-bounds read returns Unknown | Memory Safety Tests | `val == TRIT_UNKNOWN` | Boundary |
| 13 | L102 | Allocate page | Memory Safety Tests | `page >= 0` | Memory |
| 14 | L110 | Pattern written | Memory Safety Tests | `val == TRIT_TRUE` | Functional |
| 15 | L114 | Scrub succeeds | Memory Safety Tests | `sr == 0` | Functional |
| 16 | L124 | Scrub clears to Unknown | Memory Safety Tests | `all_unknown` | Functional |
| 17 | L143 | Allocate all pages | Memory Safety Tests | `all_ok` | Memory |
| 18 | L147 | OOM returns -1 | Memory Safety Tests | `oom == -1` | Functional |
| 19 | L152 | Re-allocate after free | Memory Safety Tests | `reuse >= 0` | Memory |
| 20 | L169 | Initial total correct | Memory Safety Tests | `total == 16` | Initialization |
| 21 | L170 | Initial all free | Memory Safety Tests | `free_count == 16` | Memory |
| 22 | L171 | Initial none allocated | Memory Safety Tests | `alloc_count == 0` | Memory |
| 23 | L175 | After alloc: 1 allocated | Memory Safety Tests | `alloc_count == 1` | Memory |
| 24 | L176 | After alloc: 15 free | Memory Safety Tests | `free_count == 15` | Memory |
| 25 | L180 | After free: 0 allocated | Memory Safety Tests | `alloc_count == 0` | Memory |
| 26 | L181 | After free: 16 free | Memory Safety Tests | `free_count == 16` | Memory |
| 27 | L192 | Reserve page 0 | Memory Safety Tests | `rr == 0` | Memory |
| 28 | L196 | Allocation skips reserved page | Memory Safety Tests | `page != 0 && page >= 0` | Memory |

---

## Suite 14: Scheduler Concurrency

**Source**: `tests/test_scheduler_concurrency.c`
**Runtime Assertions**: 27
**Source-Level Entries**: 18
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

> **Note**: 9 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L39 | Create high-priority thread | Scheduler Tests | `t1 >= 0` | Scheduling |
| 2 | L42 | Create normal-priority thread | Scheduler Tests | `t2 >= 0` | Logic |
| 3 | L45 | Create low-priority thread | Scheduler Tests | `t3 >= 0` | Scheduling |
| 4 | L48 | Set priority succeeds | Scheduler Tests | `sched_set_priority(&sched, t1, TRIT_TRUE) == 0` | Scheduling |
| 5 | L49 | Set priority succeeds | Scheduler Tests | `sched_set_priority(&sched, t2, TRIT_FALSE) == 0` | Scheduling |
| 6 | L69 | Picks high-priority first | Scheduler Tests | `next == high` | Scheduling |
| 7 | L87 | Yield returns valid tid | Scheduler Tests | `next == t1 ∣∣ next == t2` | Scheduling |
| 8 | L92 | Repeated yield stable | Scheduler Tests | `next == t1 ∣∣ next == t2` | Scheduling |
| 9 | L109 | Block thread | Scheduler Tests | `sched_block(&sched, t1, 0) == 0` | Memory |
| 10 | L113 | pick_next skips blocked thread | Scheduler Tests | `next == t2` | Memory |
| 11 | L116 | Unblock thread | Scheduler Tests | `sched_unblock(&sched, t1) == 0` | Memory |
| 12 | L120 | Double unblock returns error | Scheduler Tests | `r == -1` | Negative/error |
| 13 | L134 | Initial: 0 threads | Scheduler Tests | `total == 0` | Scheduling |
| 14 | L140 | After create: 2 threads | Scheduler Tests | `total == 2` | Scheduling |
| 15 | L141 | After create: 2 ready | Scheduler Tests | `ready == 2` | Functional |
| 16 | L145 | After block: 1 blocked | Scheduler Tests | `blocked == 1` | Memory |
| 17 | L165 | Created max threads | Scheduler Tests | `count == SCHED_MAX_THREADS` | Boundary |
| 18 | L169 | Overflow create returns -1 | Scheduler Tests | `overflow == -1` | Boundary |

---

## Suite 15: TBE Bootstrap Engine

**Source**: `tests/test_tbe.c`
**Runtime Assertions**: 31
**Source-Level Entries**: 31
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L171 | test_env_init_seeds | General | `function-level test` | Initialization |
| 2 | L181 | test_env_set_new | General | `function-level test` | Functional |
| 3 | L194 | test_env_set_overwrite | General | `function-level test` | Functional |
| 4 | L205 | test_env_zero_value | General | `function-level test` | Hardware/ALU |
| 5 | L217 | test_env_negative_value | General | `function-level test` | Negative/error |
| 6 | L233 | test_env_find_nonexistent | General | `function-level test` | Functional |
| 7 | L241 | test_env_full | General | `function-level test` | Functional |
| 8 | L257 | test_env_validity_flags | General | `function-level test` | Functional |
| 9 | L269 | test_bt_encode_1 | General | `function-level test` | Encoding |
| 10 | L280 | test_bt_encode_2 | General | `function-level test` | Encoding |
| 11 | L293 | test_bt_encode_3 | General | `function-level test` | Encoding |
| 12 | L306 | test_bt_encode_13 | General | `function-level test` | Encoding |
| 13 | L322 | test_consensus_all_T | General | `function-level test` | Consensus |
| 14 | L334 | test_consensus_mixed | General | `function-level test` | Consensus |
| 15 | L346 | test_consensus_with_unknowns | General | `function-level test` | Consensus |
| 16 | L359 | test_accept_any_all_F | General | `function-level test` | Functional |
| 17 | L371 | test_accept_any_one_T | General | `function-level test` | Functional |
| 18 | L383 | test_accept_any_unknowns | General | `function-level test` | Functional |
| 19 | L398 | test_kernel_init_works | General | `function-level test` | Initialization |
| 20 | L407 | test_syscall_push_pop | General | `function-level test` | Functional |
| 21 | L420 | test_syscall_alloc_free | General | `function-level test` | Memory |
| 22 | L434 | test_syscall_cap_create | General | `function-level test` | Access control |
| 23 | L445 | test_syscall_cap_revoke | General | `function-level test` | Access control |
| 24 | L457 | test_trit_inc_from_zero | General | `function-level test` | Functional |
| 25 | L478 | test_trit_dec_from_zero | General | `function-level test` | Functional |
| 26 | L500 | test_wcet_register_and_observe | General | `function-level test` | Hardware/ALU |
| 27 | L513 | test_wcet_violation | General | `function-level test` | Functional |
| 28 | L527 | test_fft_step_output_verified | General | `function-level test` | Functional |
| 29 | L544 | test_dot_all_T | General | `function-level test` | Functional |
| 30 | L557 | test_dot_orthogonal | General | `function-level test` | Functional |
| 31 | L572 | test_noise_init | General | `function-level test` | Initialization |

---

## Suite 16: Huawei CN119652311A ALU

**Source**: `tests/test_huawei_cn119652311a.c`
**Runtime Assertions**: 47
**Source-Level Entries**: 47
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L67 | test_hw_from_balanced | General | `function-level test` | Functional |
| 2 | L79 | test_hw_to_balanced | General | `function-level test` | Functional |
| 3 | L91 | test_roundtrip_translation | General | `function-level test` | Transformation |
| 4 | L105 | test_trit2_conversion | General | `function-level test` | Functional |
| 5 | L126 | test_gate_inc_truth_table | General | `function-level test` | Logic |
| 6 | L138 | test_gate_dec_truth_table | General | `function-level test` | Logic |
| 7 | L150 | test_inc_dec_inverse | General | `function-level test` | Functional |
| 8 | L163 | test_gate_nti_truth_table | General | `function-level test` | Logic |
| 9 | L175 | test_gate_pti_truth_table | General | `function-level test` | Logic |
| 10 | L187 | test_gate_pb_truth_table | General | `function-level test` | Logic |
| 11 | L199 | test_gate_nb_truth_table | General | `function-level test` | Logic |
| 12 | L217 | test_alu_inc_balanced | General | `function-level test` | Hardware/ALU |
| 13 | L229 | test_alu_dec_balanced | General | `function-level test` | Hardware/ALU |
| 14 | L241 | test_alu_nti_balanced | General | `function-level test` | Hardware/ALU |
| 15 | L253 | test_alu_pti_balanced | General | `function-level test` | Hardware/ALU |
| 16 | L269 | test_tsum_exhaustive | General | `function-level test` | Arithmetic |
| 17 | L311 | test_half_adder_exhaustive | General | `function-level test` | Arithmetic |
| 18 | L354 | test_half_adder_consistency | General | `function-level test` | Arithmetic |
| 19 | L378 | test_full_adder_exhaustive | General | `function-level test` | Arithmetic |
| 20 | L405 | test_full_adder_specific | General | `function-level test` | Arithmetic |
| 21 | L431 | test_mul1_exhaustive | General | `function-level test` | Arithmetic |
| 22 | L459 | test_mul2x2_exact_simple | General | `function-level test` | Arithmetic |
| 23 | L486 | test_mul2x2_reconstruction | General | `function-level test` | Arithmetic |
| 24 | L514 | test_mul2x2_compensation_plus6 | General | `function-level test` | Arithmetic |
| 25 | L534 | test_mul2x2_compensation_plus9 | General | `function-level test` | Arithmetic |
| 26 | L551 | test_mul6x6_simple | General | `function-level test` | Arithmetic |
| 27 | L570 | test_mul6x6_max_range | General | `function-level test` | Boundary |
| 28 | L588 | test_mul6x6_trits_width | General | `function-level test` | Arithmetic |
| 29 | L603 | test_word_add_simple | General | `function-level test` | Arithmetic |
| 30 | L624 | test_word_add_negative | General | `function-level test` | Negative/error |
| 31 | L643 | test_word_add_carry_propagation | General | `function-level test` | Arithmetic |
| 32 | L667 | test_dot_product_simple | General | `function-level test` | Arithmetic |
| 33 | L680 | test_dot_product_mixed | General | `function-level test` | Arithmetic |
| 34 | L694 | test_dot_product_orthogonal | General | `function-level test` | Arithmetic |
| 35 | L711 | test_fft_butterfly_all_zero | General | `function-level test` | Functional |
| 36 | L727 | test_fft_butterfly_return_code | General | `function-level test` | Functional |
| 37 | L737 | test_fft_butterfly_identity | General | `function-level test` | Functional |
| 38 | L765 | test_hal_init_emulated | General | `function-level test` | Arithmetic |
| 39 | L779 | test_hal_caps_populated | General | `function-level test` | Access control |
| 40 | L800 | test_hal_features | General | `function-level test` | Functional |
| 41 | L819 | test_hal_shutdown | General | `function-level test` | Functional |
| 42 | L835 | test_hal_mode_query | General | `function-level test` | Functional |
| 43 | L853 | test_mul_word_dispatch | General | `function-level test` | Arithmetic |
| 44 | L879 | test_triple_inc_is_identity | General | `function-level test` | Functional |
| 45 | L892 | test_triple_dec_is_identity | General | `function-level test` | Functional |
| 46 | L904 | test_nti_pti_pb_nb_composition | General | `function-level test` | Functional |
| 47 | L933 | test_transistor_threshold_constraint | General | `function-level test` | Functional |

---

## Suite 17: Samsung US11170290B2 ZID

**Source**: `tests/test_samsung_us11170290b2.c`
**Runtime Assertions**: 60
**Source-Level Entries**: 60
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L68 | test_weight_valid | General | `function-level test` | Functional |
| 2 | L79 | test_synapse_program_pos | General | `function-level test` | Functional |
| 3 | L90 | test_synapse_program_neg | General | `function-level test` | Functional |
| 4 | L101 | test_synapse_read_weight | General | `function-level test` | Functional |
| 5 | L118 | test_encode_input_neg | General | `function-level test` | Encoding |
| 6 | L129 | test_encode_input_pos | General | `function-level test` | Encoding |
| 7 | L140 | test_encode_input_zero | General | `function-level test` | Encoding |
| 8 | L151 | test_is_zero_input | General | `function-level test` | Functional |
| 9 | L171 | test_cell_conducts_erased_vread | General | `function-level test` | Functional |
| 10 | L180 | test_cell_programmed_vread | General | `function-level test` | Functional |
| 11 | L189 | test_cell_any_vpass | General | `function-level test` | Functional |
| 12 | L226 | test_synapse_case1 | General | `function-level test` | Functional |
| 13 | L237 | test_synapse_case2 | General | `function-level test` | Functional |
| 14 | L248 | test_synapse_case3 | General | `function-level test` | Functional |
| 15 | L259 | test_synapse_case4 | General | `function-level test` | Functional |
| 16 | L270 | test_synapse_case5 | General | `function-level test` | Functional |
| 17 | L281 | test_synapse_case6 | General | `function-level test` | Functional |
| 18 | L296 | test_zid_count_no_zeros | General | `function-level test` | Functional |
| 19 | L306 | test_zid_count_some_zeros | General | `function-level test` | Functional |
| 20 | L316 | test_zid_count_all_zeros | General | `function-level test` | Functional |
| 21 | L326 | test_zid_bitmap_pattern | General | `function-level test` | Transformation |
| 22 | L341 | test_zid_bitmap_empty | General | `function-level test` | Negative/error |
| 23 | L357 | test_bnn_dot_all_match | General | `function-level test` | Functional |
| 24 | L379 | test_bnn_dot_all_mismatch | General | `function-level test` | Functional |
| 25 | L399 | test_bnn_dot_mixed | General | `function-level test` | Functional |
| 26 | L421 | test_bnn_dot_single | General | `function-level test` | Functional |
| 27 | L457 | test_tbn_dot_no_zeros | General | `function-level test` | Functional |
| 28 | L479 | test_tbn_dot_with_zeros | General | `function-level test` | Functional |
| 29 | L509 | test_tbn_dot_all_zeros | General | `function-level test` | Functional |
| 30 | L529 | test_tbn_dot_single_zero | General | `function-level test` | Functional |
| 31 | L553 | test_tbn_dot_asymmetric | General | `function-level test` | Functional |
| 32 | L581 | test_tbn_dot_negative_result | General | `function-level test` | Negative/error |
| 33 | L610 | test_dot_auto_bnn_mode | General | `function-level test` | Functional |
| 34 | L629 | test_dot_auto_tbn_mode | General | `function-level test` | Functional |
| 35 | L654 | test_matmul_identity_like | General | `function-level test` | Arithmetic |
| 36 | L680 | test_matmul_3x4_tbn | General | `function-level test` | Arithmetic |
| 37 | L713 | test_matmul_1x1 | General | `function-level test` | Arithmetic |
| 38 | L732 | test_matmul_null_guard | General | `function-level test` | Negative/error |
| 39 | L750 | test_activation_sign | General | `function-level test` | Functional |
| 40 | L761 | test_activation_ternary | General | `function-level test` | Functional |
| 41 | L779 | test_dnn_two_layers | General | `function-level test` | Functional |
| 42 | L836 | test_hal_init_shutdown | General | `function-level test` | Initialization |
| 43 | L853 | test_hal_null_guard | General | `function-level test` | Negative/error |
| 44 | L865 | test_hal_default_caps | General | `function-level test` | Access control |
| 45 | L888 | test_set_mode_bnn | General | `function-level test` | Functional |
| 46 | L904 | test_set_mode_tbn | General | `function-level test` | Functional |
| 47 | L921 | test_set_mode_uninitialized | General | `function-level test` | Initialization |
| 48 | L937 | test_set_parallelism_sequential | General | `function-level test` | Functional |
| 49 | L952 | test_set_parallelism_multi_block | General | `function-level test` | Arithmetic |
| 50 | L967 | test_set_parallelism_pipelined | General | `function-level test` | IPC |
| 51 | L986 | test_program_weights_emulated | General | `function-level test` | Arithmetic |
| 52 | L1001 | test_read_weights_emulated | General | `function-level test` | Arithmetic |
| 53 | L1018 | test_program_weights_null_guard | General | `function-level test` | Negative/error |
| 54 | L1040 | test_patent_eq1_formula | General | `function-level test` | Arithmetic |
| 55 | L1064 | test_patent_eq2_formula | General | `function-level test` | Arithmetic |
| 56 | L1098 | test_xnor_property | General | `function-level test` | Logic |
| 57 | L1126 | test_large_vector_dot | General | `function-level test` | Functional |
| 58 | L1165 | test_tbn_large_sparse | General | `function-level test` | Parsing |
| 59 | L1198 | test_mmio_constants | General | `function-level test` | Functional |
| 60 | L1218 | test_topology_packing | General | `function-level test` | Encoding |

---

## Suite 18: Samsung CN105745888A Correlator

**Source**: `tests/test_samsung_cn105745888a.c`
**Runtime Assertions**: 61
**Source-Level Entries**: 61
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L91 | test_trit_compat | General | `function-level test` | Functional |
| 2 | L107 | test_weight_all_nonzero | General | `function-level test` | Functional |
| 3 | L115 | test_weight_with_zeros | General | `function-level test` | Functional |
| 4 | L123 | test_weight_all_zero | General | `function-level test` | Functional |
| 5 | L135 | test_perfect_square_yes | General | `function-level test` | Performance |
| 6 | L146 | test_perfect_square_no | General | `function-level test` | Performance |
| 7 | L160 | test_mseq_degree3 | General | `function-level test` | Functional |
| 8 | L174 | test_mseq_degree4 | General | `function-level test` | Functional |
| 9 | L186 | test_mseq_degree5 | General | `function-level test` | Functional |
| 10 | L196 | test_mseq_maximal_length | General | `function-level test` | Boundary |
| 11 | L225 | test_complement | General | `function-level test` | Functional |
| 12 | L240 | test_double_complement | General | `function-level test` | Functional |
| 13 | L256 | test_cross_corr_self | General | `function-level test` | Functional |
| 14 | L270 | test_cross_corr_orthogonal | General | `function-level test` | Functional |
| 15 | L287 | test_gen_perfect_basic | General | `function-level test` | Performance |
| 16 | L310 | test_gen_near_perfect | General | `function-level test` | Performance |
| 17 | L330 | test_near_perfect_msac_reduced | General | `function-level test` | Performance |
| 18 | L351 | test_msac_zero_seq | General | `function-level test` | Functional |
| 19 | L360 | test_msac_unit_impulse | General | `function-level test` | Functional |
| 20 | L371 | test_msac_positive | General | `function-level test` | Functional |
| 21 | L388 | test_aperiodic_autocorr_zero | General | `function-level test` | Functional |
| 22 | L398 | test_aperiodic_autocorr_k1 | General | `function-level test` | Functional |
| 23 | L412 | test_gen_base_inserts_value | General | `function-level test` | Hardware/ALU |
| 24 | L426 | test_gen_base_comp_inserts_one | General | `function-level test` | Functional |
| 25 | L444 | test_table3_family_3_8 | General | `function-level test` | Functional |
| 26 | L457 | test_table3_family_4_16 | General | `function-level test` | Functional |
| 27 | L467 | test_table3_family_5_32 | General | `function-level test` | Functional |
| 28 | L477 | test_table3_invalid | General | `function-level test` | Negative/error |
| 29 | L490 | test_cyclic_shift_zero | General | `function-level test` | Functional |
| 30 | L501 | test_cyclic_shift_one | General | `function-level test` | Functional |
| 31 | L515 | test_cyclic_shift_full | General | `function-level test` | Functional |
| 32 | L530 | test_abs_project | General | `function-level test` | Functional |
| 33 | L548 | test_codeset_count | General | `function-level test` | Functional |
| 34 | L559 | test_codeset_shift0_is_base | General | `function-level test` | Functional |
| 35 | L571 | test_codeset_all_distinct | General | `function-level test` | Functional |
| 36 | L597 | test_decimal_map_round_trip | General | `function-level test` | Transformation |
| 37 | L612 | test_gray_map_values | General | `function-level test` | Transformation |
| 38 | L623 | test_gray_map_round_trip | General | `function-level test` | Transformation |
| 39 | L638 | test_modem_init_3_8 | General | `function-level test` | Initialization |
| 40 | L653 | test_modem_init_4_16 | General | `function-level test` | Initialization |
| 41 | L666 | test_modem_init_invalid | General | `function-level test` | Negative/error |
| 42 | L679 | test_modulate_symbol_0 | General | `function-level test` | Linking |
| 43 | L697 | test_modulate_symbol_distinct | General | `function-level test` | Linking |
| 44 | L715 | test_modulate_out_of_range | General | `function-level test` | Boundary |
| 45 | L732 | test_demod_coherent_clean | General | `function-level test` | Functional |
| 46 | L750 | test_demod_coherent_all_symbols | General | `function-level test` | Linking |
| 47 | L771 | test_demod_non_coherent_clean | General | `function-level test` | Functional |
| 48 | L790 | test_frame_modulate | General | `function-level test` | Functional |
| 49 | L806 | test_frame_round_trip | General | `function-level test` | Functional |
| 50 | L831 | test_round_trip_all_families | General | `function-level test` | Functional |
| 51 | L856 | test_round_trip_low_noise | General | `function-level test` | Functional |
| 52 | L882 | test_snr_clean | General | `function-level test` | Functional |
| 53 | L902 | test_family_descriptors | General | `function-level test` | Functional |
| 54 | L930 | test_emu_regs_init | General | `function-level test` | Initialization |
| 55 | L945 | test_emu_regs_buffers | General | `function-level test` | Functional |
| 56 | L962 | test_correlation_manual | General | `function-level test` | Functional |
| 57 | L973 | test_correlation_self_energy | General | `function-level test` | Functional |
| 58 | L986 | test_correlation_shifted | General | `function-level test` | Functional |
| 59 | L1016 | test_gray_round_trip_4_16 | General | `function-level test` | Functional |
| 60 | L1037 | test_non_coherent_round_trip_all | General | `function-level test` | Functional |
| 61 | L1062 | test_custom_base_modem | General | `function-level test` | Functional |

---

## Suite 19: TSMC TMD / Intel PAM3 / Hynix TCAM

**Source**: `tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c`
**Runtime Assertions**: 80
**Source-Level Entries**: 80
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L84 | test_tmd_monolayer_mos2 | 1.1 Monolayer Creatio | `function-level test` | Functional |
| 2 | L97 | test_tmd_monolayer_hbn | 1.1 Monolayer Creatio | `function-level test` | Functional |
| 3 | L109 | test_tmd_monolayer_ws2 | 1.1 Monolayer Creatio | `function-level test` | Functional |
| 4 | L120 | test_tmd_monolayer_mose2 | 1.1 Monolayer Creatio | `function-level test` | Functional |
| 5 | L130 | test_tmd_monolayer_wse2 | 1.1 Monolayer Creatio | `function-level test` | Functional |
| 6 | L140 | test_tmd_monolayer_mote2 | 1.1 Monolayer Creatio | `function-level test` | Functional |
| 7 | L150 | test_tmd_monolayer_graphene | 1.1 Monolayer Creatio | `function-level test` | Functional |
| 8 | L160 | test_tmd_monolayer_null_ptr | 1.1 Monolayer Creatio | `function-level test` | Negative/error |
| 9 | L170 | test_tmd_is_semiconductor | 1.2 Material Classificatio | `function-level test` | Functional |
| 10 | L183 | test_tmd_is_dielectric | 1.2 Material Classificatio | `function-level test` | Functional |
| 11 | L194 | test_tmd_stack_init | 1.3 Heterostack Operations | `function-level test` | Memory |
| 12 | L206 | test_tmd_stack_add_single_layer | 1.3 Heterostack Operations | `function-level test` | Arithmetic |
| 13 | L222 | test_tmd_stack_hbn_mos2_hbn_sandwich | 1.3 Heterostack Operations | `function-level test` | Memory |
| 14 | L244 | test_tmd_stack_not_sandwich | 1.3 Heterostack Operations | `function-level test` | Memory |
| 15 | L263 | test_tmd_stack_total_thickness | 1.3 Heterostack Operations | `function-level test` | Memory |
| 16 | L286 | test_tmd_bond_params_valid | 1.4 Bonding Parameters | `function-level test` | Functional |
| 17 | L298 | test_tmd_bond_params_boundary_low | 1.4 Bonding Parameters | `function-level test` | Boundary |
| 18 | L309 | test_tmd_bond_params_boundary_high | 1.4 Bonding Parameters | `function-level test` | Boundary |
| 19 | L320 | test_tmd_bond_params_out_of_range | 1.4 Bonding Parameters | `function-level test` | Boundary |
| 20 | L338 | test_tmd_carrier_attach_remove | 1.5 Carrier Film | `function-level test` | Functional |
| 21 | L360 | test_tmd_substrate_attach | 1.5 Carrier Film | `function-level test` | Arithmetic |
| 22 | L379 | test_tmd_quality_score_perfect | 1.6 Quality Score | `function-level test` | Performance |
| 23 | L397 | test_tmd_quality_score_range | 1.6 Quality Score | `function-level test` | Boundary |
| 24 | L415 | test_tmd_fet_init | 1.7 TMD FET Operations | `function-level test` | Initialization |
| 25 | L444 | test_tmd_fet_evaluate_low | 1.7 TMD FET Operations | `function-level test` | Hardware/ALU |
| 26 | L469 | test_tmd_fet_evaluate_mid | 1.7 TMD FET Operations | `function-level test` | Hardware/ALU |
| 27 | L494 | test_tmd_fet_evaluate_high | 1.7 TMD FET Operations | `function-level test` | Hardware/ALU |
| 28 | L519 | test_tmd_fet_ternary_not | 1.7 TMD FET Operations | `function-level test` | Functional |
| 29 | L545 | test_tmd_fet_ternary_and | 1.7 TMD FET Operations | `function-level test` | Functional |
| 30 | L572 | test_tmd_fet_ternary_or | 1.7 TMD FET Operations | `function-level test` | Functional |
| 31 | L599 | test_tmd_fet_on_current | 1.7 TMD FET Operations | `function-level test` | Functional |
| 32 | L626 | test_tmd_3d_init | 1.8 3D Monolithic Model | `function-level test` | Initialization |
| 33 | L639 | test_tmd_3d_density | 1.8 3D Monolithic Model | `function-level test` | Functional |
| 34 | L650 | test_tmd_3d_validate | 1.8 3D Monolithic Model | `function-level test` | Functional |
| 35 | L666 | test_pam3d_init | 2.1 Decoder Initializatio | `function-level test` | Initialization |
| 36 | L681 | test_pam3d_init_null | 2.1 Decoder Initializatio | `function-level test` | Negative/error |
| 37 | L688 | test_pam3d_set_thresholds | 2.1 Decoder Initializatio | `function-level test` | Functional |
| 38 | L708 | test_pam3d_dc_correction_toggle | 2.1 Decoder Initializatio | `function-level test` | Functional |
| 39 | L724 | test_pam3d_generate_signal_basic | 2.2 Test Signal Generatio | `function-level test` | Functional |
| 40 | L746 | test_pam3d_generate_signal_with_noise | 2.2 Test Signal Generatio | `function-level test` | Functional |
| 41 | L768 | test_pam3d_generate_signal_empty | 2.2 Test Signal Generatio | `function-level test` | Negative/error |
| 42 | L779 | test_pam3d_load_samples | 2.3 Sample Loading | `function-level test` | Functional |
| 43 | L795 | test_pam3d_load_samples_overflow | 2.3 Sample Loading | `function-level test` | Boundary |
| 44 | L809 | test_pam3d_full_decode_clean | 2.4 Full Pipeline Decode | `function-level test` | Encoding |
| 45 | L839 | test_pam3d_full_decode_noisy | 2.4 Full Pipeline Decode | `function-level test` | Encoding |
| 46 | L863 | test_pam3d_dc_correction_stage | 2.5 Individual Pipeline Stages | `function-level test` | Functional |
| 47 | L882 | test_pam3d_level_detection_stage | 2.5 Individual Pipeline Stages | `function-level test` | Functional |
| 48 | L909 | test_pam3d_spike_filter_stage | 2.5 Individual Pipeline Stages | `function-level test` | Functional |
| 49 | L929 | test_pam3d_edge_detection_stage | 2.5 Individual Pipeline Stages | `function-level test` | Functional |
| 50 | L951 | test_pam3d_stats_accumulate | 2.5 Individual Pipeline Stages | `function-level test` | Arithmetic |
| 51 | L976 | test_tcam_crossbar_init | 3.1 TCAM Crossbar Init | `function-level test` | Initialization |
| 52 | L989 | test_tcam_crossbar_init_null | 3.1 TCAM Crossbar Init | `function-level test` | Negative/error |
| 53 | L998 | test_tcam_add_edge | 3.2 TCAM Add Edge | `function-level test` | Arithmetic |
| 54 | L1013 | test_tcam_add_multiple_edges | 3.2 TCAM Add Edge | `function-level test` | Arithmetic |
| 55 | L1029 | test_tcam_add_edge_overflow | 3.2 TCAM Add Edge | `function-level test` | Boundary |
| 56 | L1048 | test_tcam_search_dst_single_hit | 3.3 TCAM Search by Destinatio | `function-level test` | Functional |
| 57 | L1067 | test_tcam_search_dst_multiple_hits | 3.3 TCAM Search by Destinatio | `function-level test` | Arithmetic |
| 58 | L1089 | test_tcam_search_dst_no_hits | 3.3 TCAM Search by Destinatio | `function-level test` | Functional |
| 59 | L1107 | test_tcam_search_vtx_layer | 3.4 TCAM Search by Vertex + Layer | `function-level test` | Functional |
| 60 | L1126 | test_tcam_search_vtx_layer_dont_care | 3.4 TCAM Search by Vertex + Layer | `function-level test` | Functional |
| 61 | L1143 | test_tcam_search_stats | 3.4 TCAM Search by Vertex + Layer | `function-level test` | Functional |
| 62 | L1165 | test_mac_crossbar_init | 3.5 MAC Crossbar | `function-level test` | Initialization |
| 63 | L1177 | test_mac_add_features | 3.5 MAC Crossbar | `function-level test` | Arithmetic |
| 64 | L1193 | test_mac_accumulate_with_hit_vector | 3.5 MAC Crossbar | `function-level test` | Arithmetic |
| 65 | L1225 | test_mac_accumulate_empty_hit | 3.5 MAC Crossbar | `function-level test` | Negative/error |
| 66 | L1250 | test_dfp_encode_group0 | 3.6 Dynamic Fixed-Point | `function-level test` | Encoding |
| 67 | L1269 | test_dfp_encode_group1 | 3.6 Dynamic Fixed-Point | `function-level test` | Encoding |
| 68 | L1288 | test_dfp_encode_null | 3.6 Dynamic Fixed-Point | `function-level test` | Negative/error |
| 69 | L1295 | test_dfp_decode_basic | 3.6 Dynamic Fixed-Point | `function-level test` | Encoding |
| 70 | L1307 | test_dfp_mac_basic | 3.6 Dynamic Fixed-Point | `function-level test` | Functional |
| 71 | L1324 | test_dfp_mac_null_returns_zero | 3.6 Dynamic Fixed-Point | `function-level test` | Negative/error |
| 72 | L1334 | test_gnn_init | 3.7 GNN Pipeline | `function-level test` | Initialization |
| 73 | L1347 | test_gnn_init_null | 3.7 GNN Pipeline | `function-level test` | Negative/error |
| 74 | L1354 | test_gnn_load_graph | 3.7 GNN Pipeline | `function-level test` | Functional |
| 75 | L1388 | test_gnn_sample_batch | 3.7 GNN Pipeline | `function-level test` | Functional |
| 76 | L1420 | test_gnn_aggregate | 3.7 GNN Pipeline | `function-level test` | Logic |
| 77 | L1461 | test_gnn_update | 3.7 GNN Pipeline | `function-level test` | Functional |
| 78 | L1499 | test_gnn_train_epoch | 3.7 GNN Pipeline | `function-level test` | Functional |
| 79 | L1535 | test_gnn_train_multiple_epochs | 3.7 GNN Pipeline | `function-level test` | Arithmetic |
| 80 | L1565 | test_gnn_get_features_invalid_node | 3.7 GNN Pipeline | `function-level test` | Negative/error |

---

## Suite 20: Functional Utility

**Source**: `tests/test_functional_utility.c`
**Runtime Assertions**: 202
**Source-Level Entries**: 233
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L60 | test_twq_config_defaults | Test harness | `function-level test` | Initialization |
| 2 | L76 | test_twq_quantize_basic | TWQ: Config Defaults | `function-level test` | Functional |
| 3 | L87 | quantize returns 0 | TWQ: Basic Quantizatio | `rc == 0` | Functional |
| 4 | L88 | layer count matches | TWQ: Basic Quantizatio | `layer.count == count` | Functional |
| 5 | L91 | weight 1000 → +1 | TWQ: Basic Quantizatio | `layer.weights[0] == TRIT_TRUE` | Functional |
| 6 | L93 | weight -1000 → -1 | TWQ: Basic Quantizatio | `layer.weights[2] == TRIT_FALSE` | Functional |
| 7 | L95 | weight 0 → 0 | TWQ: Basic Quantizatio | `layer.weights[3] == TRIT_UNKNOWN` | Functional |
| 8 | L98 | stats total = 8 | TWQ: Basic Quantizatio | `layer.stats.total_weights == 8` | Functional |
| 9 | L99 | stats positive > 0 | TWQ: Basic Quantizatio | `layer.stats.positive_count > 0` | Functional |
| 10 | L100 | stats negative > 0 | TWQ: Basic Quantizatio | `layer.stats.negative_count > 0` | Negative/error |
| 11 | L101 | stats mean_abs > 0 | TWQ: Basic Quantizatio | `layer.stats.mean_abs_x1000 > 0` | Functional |
| 12 | L102 | stats threshold > 0 | TWQ: Basic Quantizatio | `layer.stats.threshold_x1000 > 0` | Functional |
| 13 | L105 | test_twq_quantize_all_zero | TWQ: Basic Quantizatio | `function-level test` | Functional |
| 14 | L113 | all-zero quantize succeeds | TWQ: All-Zero Quantizatio | `rc == 0` | Functional |
| 15 | L114 | all zeroed | TWQ: All-Zero Quantizatio | `layer.stats.zero_count == 4` | Functional |
| 16 | L115 | sparsity 100% | TWQ: All-Zero Quantizatio | `layer.stats.sparsity_permille == 1000` | Functional |
| 17 | L118 | test_twq_ternary_dot | TWQ: All-Zero Quantizatio | `function-level test` | Functional |
| 18 | L124 | dot product = -1 | TWQ: Ternary Dot Product | `dot == -1` | Arithmetic |
| 19 | L128 | self dot = 3 (3 non-zero) | TWQ: Ternary Dot Product | `self_dot == 3` | Functional |
| 20 | L131 | test_twq_matvec | TWQ: Ternary Dot Product | `function-level test` | Functional |
| 21 | L137 | matvec row = -1 | TWQ: Matrix-Vector Row | `result == -1` | Functional |
| 22 | L140 | test_twq_sparsity | TWQ: Matrix-Vector Row | `function-level test` | Functional |
| 23 | L150 | sparsity enforcement zeroed some | TWQ: N:M Sparsity Enforcement | `zeroed >= 0` | Functional |
| 24 | L158 | block 0: <= 2 non-zero | TWQ: N:M Sparsity Enforcement | `nz_block0 <= 2` | Memory |
| 25 | L159 | block 1: <= 2 non-zero | TWQ: N:M Sparsity Enforcement | `nz_block1 <= 2` | Memory |
| 26 | L162 | test_twq_energy | TWQ: N:M Sparsity Enforcement | `function-level test` | Functional |
| 27 | L172 | energy ratio > 0 | TWQ: Energy Ratio | `ratio > 0` | Functional |
| 28 | L173 | energy ratio < 1000 (ternary is cheaper) | TWQ: Energy Ratio | `ratio < 1000` | Memory |
| 29 | L176 | test_twq_overflow_guard | TWQ: Energy Ratio | `function-level test` | Boundary |
| 30 | L186 | overflow returns -1 | TWQ: Overflow Guard | `rc == -1` | Boundary |
| 31 | L193 | test_dlfet_tnot | TWQ: Overflow Guard | `function-level test` | Functional |
| 32 | L198 | TNOT(0) = 2 | DLFET: Ternary NOT | `dlfet_tnot(&st, 0) == 2` | Functional |
| 33 | L199 | TNOT(1) = 1 | DLFET: Ternary NOT | `dlfet_tnot(&st, 1) == 1` | Functional |
| 34 | L200 | TNOT(2) = 0 | DLFET: Ternary NOT | `dlfet_tnot(&st, 2) == 0` | Functional |
| 35 | L201 | 3 transitions counted | DLFET: Ternary NOT | `st.total_transitions == 3` | Functional |
| 36 | L204 | test_dlfet_tnand | DLFET: Ternary NOT | `function-level test` | Logic |
| 37 | L209 | TNAND(0,0) = 2 | DLFET: Ternary NAND | `dlfet_tnand(&st, 0, 0) == 2` | Logic |
| 38 | L210 | TNAND(0,1) = 2 | DLFET: Ternary NAND | `dlfet_tnand(&st, 0, 1) == 2` | Logic |
| 39 | L211 | TNAND(0,2) = 2 | DLFET: Ternary NAND | `dlfet_tnand(&st, 0, 2) == 2` | Logic |
| 40 | L212 | TNAND(1,1) = 1 | DLFET: Ternary NAND | `dlfet_tnand(&st, 1, 1) == 1` | Logic |
| 41 | L213 | TNAND(2,2) = 0 | DLFET: Ternary NAND | `dlfet_tnand(&st, 2, 2) == 0` | Logic |
| 42 | L214 | TNAND(1,2) = 1 | DLFET: Ternary NAND | `dlfet_tnand(&st, 1, 2) == 1` | Logic |
| 43 | L215 | TNAND(2,1) = 1 | DLFET: Ternary NAND | `dlfet_tnand(&st, 2, 1) == 1` | Logic |
| 44 | L218 | test_dlfet_derived_gates | DLFET: Ternary NAND | `function-level test` | Logic |
| 45 | L230 | MIN(0,2) = 0 | DLFET: Derived Gates | `dlfet_tmin(&st, 0, 2) == 0` | Boundary |
| 46 | L231 | MAX(0,2) = 2 | DLFET: Derived Gates | `dlfet_tmax(&st, 0, 2) == 2` | Boundary |
| 47 | L232 | MIN(1,2) = 1 | DLFET: Derived Gates | `dlfet_tmin(&st, 1, 2) == 1` | Boundary |
| 48 | L233 | MAX(1,0) = 1 | DLFET: Derived Gates | `dlfet_tmax(&st, 1, 0) == 1` | Boundary |
| 49 | L236 | test_dlfet_half_adder | DLFET: Derived Gates | `function-level test` | Arithmetic |
| 50 | L243 | HA(0,0): sum=0, carry=0 | DLFET: Half Adder | `sum == 0 && carry == 0` | Arithmetic |
| 51 | L246 | HA(1,1): sum=2, carry=0 | DLFET: Half Adder | `sum == 2 && carry == 0` | Arithmetic |
| 52 | L249 | HA(2,1): sum=0, carry=1 | DLFET: Half Adder | `sum == 0 && carry == 1` | Arithmetic |
| 53 | L252 | HA(2,2): sum=1, carry=1 | DLFET: Half Adder | `sum == 1 && carry == 1` | Arithmetic |
| 54 | L255 | test_dlfet_full_adder | DLFET: Half Adder | `function-level test` | Arithmetic |
| 55 | L262 | FA(0,0,0): sum=0, cout=0 | DLFET: Full Adder | `sum == 0 && cout == 0` | Arithmetic |
| 56 | L265 | FA(1,1,1): sum=0, cout=1 | DLFET: Full Adder | `sum == 0 && cout == 1` | Arithmetic |
| 57 | L268 | FA(2,2,2): sum=0, cout=2 | DLFET: Full Adder | `sum == 0 && cout == 2` | Arithmetic |
| 58 | L271 | FA(2,2,1): sum=2, cout=1 | DLFET: Full Adder | `sum == 2 && cout == 1` | Arithmetic |
| 59 | L274 | test_dlfet_multi_add | DLFET: Full Adder | `function-level test` | Arithmetic |
| 60 | L286 | multi-add: result[0] = 0 | DLFET: Multi-Trit Additio | `result[0] == 0` | Arithmetic |
| 61 | L287 | multi-add: result[1] = 1 | DLFET: Multi-Trit Additio | `result[1] == 1` | Arithmetic |
| 62 | L288 | multi-add: carry = 1 | DLFET: Multi-Trit Additio | `carry == 1` | Arithmetic |
| 63 | L291 | test_dlfet_balanced_conversion | DLFET: Multi-Trit Additio | `function-level test` | Functional |
| 64 | L308 | test_dlfet_pdp | DLFET: Balanced ↔ Unbalanced | `function-level test` | Functional |
| 65 | L310 | PDP TNOT = 3 aJ | DLFET: Power-Delay Product | `dlfet_pdp_estimate(0) == DLFET_PDP_TNOT_AJ` | Logic |
| 66 | L311 | PDP TNAND = 8 aJ | DLFET: Power-Delay Product | `dlfet_pdp_estimate(1) == DLFET_PDP_TNAND_AJ` | Logic |
| 67 | L312 | PDP TFA = 11 aJ | DLFET: Power-Delay Product | `dlfet_pdp_estimate(4) == DLFET_PDP_TFA_AJ` | Functional |
| 68 | L315 | test_dlfet_energy_tracking | DLFET: Power-Delay Product | `function-level test` | Functional |
| 69 | L319 | initial energy = 0 | DLFET: Energy Tracking | `st.energy_aj == 0` | Initialization |
| 70 | L322 | energy after TNOT > 0 | DLFET: Energy Tracking | `st.energy_aj > 0` | Logic |
| 71 | L326 | energy after TNAND increases | DLFET: Energy Tracking | `st.energy_aj > e1` | Logic |
| 72 | L333 | test_rtc_roundtrip | DLFET: Energy Tracking | `function-level test` | Transformation |
| 73 | L352 | test_rtc_zero | RTC: Roundtrip Conversio | `function-level test` | Functional |
| 74 | L356 | zero has 0 non-zero trits | RTC: Zero Conversio | `nz == 0` | Functional |
| 75 | L358 | all trits are 0 | RTC: Zero Conversio | `trits[i] == TRIT_UNKNOWN` | Functional |
| 76 | L362 | test_rtc_batch | RTC: Zero Conversio | `function-level test` | Functional |
| 77 | L370 | batch to ternary succeeds | RTC: Batch Conversio | `rc == 0` | Functional |
| 78 | L373 | batch to int succeeds | RTC: Batch Conversio | `rc == 0` | Functional |
| 79 | L379 | batch roundtrip matches | RTC: Batch Conversio | `all_match` | Transformation |
| 80 | L382 | test_rtc_pack_unpack | RTC: Batch Conversio | `function-level test` | Encoding |
| 81 | L388 | pack produces words > 0 | RTC: Pack/Unpack | `words > 0` | Encoding |
| 82 | L389 | stream trit count = 8 | RTC: Pack/Unpack | `stream.trit_count == 8` | Functional |
| 83 | L393 | unpack count = 8 | RTC: Pack/Unpack | `count == 8` | Encoding |
| 84 | L399 | pack/unpack roundtrip matches | RTC: Pack/Unpack | `match` | Encoding |
| 85 | L402 | test_rtc_bandwidth | RTC: Pack/Unpack | `function-level test` | Functional |
| 86 | L405 | bandwidth efficiency > 0 | RTC: Bandwidth Efficiency | `eff > 0` | Functional |
| 87 | L406 | bandwidth efficiency <= 1000 | RTC: Bandwidth Efficiency | `eff <= 1000` | Functional |
| 88 | L408 | efficiency ~ 792 (≈79%) | RTC: Bandwidth Efficiency | `eff > 700 && eff < 900` | Functional |
| 89 | L411 | test_rtc_stats_tracking | RTC: Bandwidth Efficiency | `function-level test` | Functional |
| 90 | L415 | initial conversions = 0 | RTC: Stats Tracking | `stats.conversions == 0` | Initialization |
| 91 | L419 | conversions incremented | RTC: Stats Tracking | `stats.conversions == 1` | Arithmetic |
| 92 | L420 | total trits tracked | RTC: Stats Tracking | `stats.total_trits == 8` | Functional |
| 93 | L427 | test_srbc_init | RTC: Stats Tracking | `function-level test` | Initialization |
| 94 | L431 | initial status = STABLE | SRBC: Initializatio | `st.status == SRBC_STABLE` | Initialization |
| 95 | L432 | ref cells = 4 | SRBC: Initializatio | `st.num_ref_cells == SRBC_NUM_REF_CELLS` | Functional |
| 96 | L433 | v_target = 400 mV | SRBC: Initializatio | `st.v_target_mv == SRBC_V_TARGET_MV` | Functional |
| 97 | L434 | total calibrations = 0 | SRBC: Initializatio | `st.total_calibrations == 0` | Functional |
| 98 | L435 | tamper events = 0 | SRBC: Initializatio | `st.tamper_events == 0` | Functional |
| 99 | L438 | test_srbc_stable_tick | SRBC: Initializatio | `function-level test` | Functional |
| 100 | L444 | stable tick returns STABLE | SRBC: Stable Tick | `s == SRBC_STABLE` | Functional |
| 101 | L445 | ticks = 1 | SRBC: Stable Tick | `st.ticks == 1` | Functional |
| 102 | L446 | stable_ticks = 1 | SRBC: Stable Tick | `st.stable_ticks == 1` | Functional |
| 103 | L449 | test_srbc_thermal_drift | SRBC: Stable Tick | `function-level test` | Functional |
| 104 | L456 | temperature updated | SRBC: Thermal Drift | `st.temperature_mc == 60000 + 25000` | Functional |
| 105 | L465 | test_srbc_tamper_detection | SRBC: Thermal Drift | `function-level test` | Functional |
| 106 | L472 | large fault detected as tamper | SRBC: Tamper Detectio | `detected == 1` | Functional |
| 107 | L473 | status = TAMPERED | SRBC: Tamper Detectio | `st.status == SRBC_TAMPERED` | Functional |
| 108 | L474 | tamper events = 1 | SRBC: Tamper Detectio | `st.tamper_events == 1` | Functional |
| 109 | L477 | test_srbc_small_fault_absorbed | SRBC: Tamper Detectio | `function-level test` | Functional |
| 110 | L483 | small fault absorbed | SRBC: Small Fault Absorbed | `detected == 0` | Functional |
| 111 | L486 | test_srbc_voltage_to_trit | SRBC: Small Fault Absorbed | `function-level test` | Functional |
| 112 | L488 | 200mV → FALSE | SRBC: Voltage → Trit | `srbc_voltage_to_trit(200) == TRIT_FALSE` | Functional |
| 113 | L489 | 400mV → UNKNOWN (state 1) | SRBC: Voltage → Trit | `srbc_voltage_to_trit(400) == TRIT_UNKNOWN` | Functional |
| 114 | L490 | 700mV → TRUE | SRBC: Voltage → Trit | `srbc_voltage_to_trit(700) == TRIT_TRUE` | Functional |
| 115 | L493 | test_srbc_snm | SRBC: Voltage → Trit | `function-level test` | Functional |
| 116 | L499 | initial SNM > 0 | SRBC: Signal-to-Noise Margi | `snm > 0` | Initialization |
| 117 | L502 | test_srbc_stability | SRBC: Signal-to-Noise Margi | `function-level test` | Functional |
| 118 | L512 | stability >= 90% | SRBC: Stability Percentage | `pct >= 90` | Functional |
| 119 | L515 | test_srbc_reset_refs | SRBC: Stability Percentage | `function-level test` | Initialization |
| 120 | L530 | test_crypto_hash_deterministic | SRBC: Reset References | `function-level test` | Boundary |
| 121 | L543 | hash is deterministic | Crypto: Hash Deterministic | `match` | Boundary |
| 122 | L546 | test_crypto_hash_avalanche | Crypto: Hash Deterministic | `function-level test` | Functional |
| 123 | L564 | test_crypto_keygen | Crypto: Hash Avalanche | `function-level test` | Functional |
| 124 | L570 | same seed → same key | Crypto: Key Generatio | `tcrypto_key_compare(&k1, &k2) == 0` | Initialization |
| 125 | L573 | different seed → different key | Crypto: Key Generatio | `tcrypto_key_compare(&k1, &k2) != 0` | Initialization |
| 126 | L576 | test_crypto_encrypt_decrypt | Crypto: Key Generatio | `function-level test` | Functional |
| 127 | L598 | ciphertext differs from plaintext | Crypto: Encrypt/Decrypt Roundtrip | `changed > 0` | Functional |
| 128 | L608 | decrypt recovers original | Crypto: Encrypt/Decrypt Roundtrip | `match` | Functional |
| 129 | L611 | test_crypto_mac | Crypto: Encrypt/Decrypt Roundtrip | `function-level test` | Functional |
| 130 | L622 | MAC verifies correctly | Crypto: MAC Compute/Verify | `valid == 1` | Functional |
| 131 | L627 | MAC fails on corrupted msg | Crypto: MAC Compute/Verify | `valid == 0` | Negative/error |
| 132 | L630 | test_crypto_lattice | Crypto: MAC Compute/Verify | `function-level test` | Functional |
| 133 | L646 | test_crypto_constant_time | Crypto: Lattice Operations | `function-level test` | Functional |
| 134 | L653 | identical keys compare equal | Crypto: Constant-Time Key Compare | `tcrypto_key_compare(&a, &b) == 0` | Functional |
| 135 | L658 | flipped key differs | Crypto: Constant-Time Key Compare | `diff != 0` | Functional |
| 136 | L665 | test_pdelay_nominal | Crypto: Constant-Time Key Compare | `function-level test` | Boundary |
| 137 | L667 | 0→1 = 120 ps | PropDelay: Nominal Values | `pdelay_get_nominal(0, 1) == PDELAY_0_TO_1_PS` | Functional |
| 138 | L668 | 1→2 = 80 ps | PropDelay: Nominal Values | `pdelay_get_nominal(1, 2) == PDELAY_1_TO_2_PS` | Functional |
| 139 | L669 | 0→2 = 60 ps | PropDelay: Nominal Values | `pdelay_get_nominal(0, 2) == PDELAY_0_TO_2_PS` | Functional |
| 140 | L670 | 2→1 = 130 ps | PropDelay: Nominal Values | `pdelay_get_nominal(2, 1) == PDELAY_2_TO_1_PS` | Functional |
| 141 | L671 | 1→0 = 90 ps | PropDelay: Nominal Values | `pdelay_get_nominal(1, 0) == PDELAY_1_TO_0_PS` | Functional |
| 142 | L672 | 2→0 = 55 ps | PropDelay: Nominal Values | `pdelay_get_nominal(2, 0) == PDELAY_2_TO_0_PS` | Functional |
| 143 | L673 | 1→1 = 0 ps | PropDelay: Nominal Values | `pdelay_get_nominal(1, 1) == PDELAY_NO_CHANGE_PS` | Functional |
| 144 | L676 | test_pdelay_pvt_adjustment | PropDelay: Nominal Values | `function-level test` | Functional |
| 145 | L683 | nominal conditions = nominal delay | PropDelay: PVT Adjustment | `adj == PDELAY_0_TO_1_PS` | Boundary |
| 146 | L688 | hot corner slows delay | PropDelay: PVT Adjustment | `adj > PDELAY_0_TO_1_PS` | Functional |
| 147 | L694 | low voltage slows delay | PropDelay: PVT Adjustment | `adj > PDELAY_0_TO_1_PS` | Functional |
| 148 | L700 | slow corner adds 20% | PropDelay: PVT Adjustment | `adj > PDELAY_0_TO_1_PS` | Arithmetic |
| 149 | L705 | fast corner subtracts 15% | PropDelay: PVT Adjustment | `adj < PDELAY_0_TO_1_PS` | Arithmetic |
| 150 | L708 | test_pdelay_chain_analysis | PropDelay: PVT Adjustment | `function-level test` | Functional |
| 151 | L716 | chain analysis succeeds | PropDelay: Chain Analysis | `rc == 0` | Functional |
| 152 | L717 | num_transitions = 5 | PropDelay: Chain Analysis | `result.num_transitions == 5` | Functional |
| 153 | L718 | total_delay > 0 | PropDelay: Chain Analysis | `result.total_delay_ps > 0` | Functional |
| 154 | L719 | worst >= best | PropDelay: Chain Analysis | `result.worst_transition_ps >= result.best_transition_ps` | Functional |
| 155 | L720 | critical index valid | PropDelay: Chain Analysis | `result.critical_index >= 0 && result.critical_index < 5` | Functional |
| 156 | L721 | max frequency > 0 | PropDelay: Chain Analysis | `result.max_frequency_mhz > 0` | Boundary |
| 157 | L724 | test_pdelay_classify | PropDelay: Chain Analysis | `function-level test` | Functional |
| 158 | L726 | classify 0→1 | PropDelay: Transition Classificatio | `pdelay_classify(0, 1) == PDELAY_TRANS_0_1` | Functional |
| 159 | L727 | classify 2→0 | PropDelay: Transition Classificatio | `pdelay_classify(2, 0) == PDELAY_TRANS_2_0` | Functional |
| 160 | L728 | classify 1→1 | PropDelay: Transition Classificatio | `pdelay_classify(1, 1) == PDELAY_TRANS_NONE` | Functional |
| 161 | L731 | test_pdelay_pdp | PropDelay: Transition Classificatio | `function-level test` | Functional |
| 162 | L737 | PDP > 0 for real transition | PropDelay: Power-Delay Product | `pdp > 0` | Logic |
| 163 | L740 | PDP = 0 for no change | PropDelay: Power-Delay Product | `pdp_none == 0` | Logic |
| 164 | L743 | test_pdelay_clock_period | PropDelay: Power-Delay Product | `function-level test` | Functional |
| 165 | L750 | clock period > total delay | PropDelay: Clock Period | `period > 0` | Functional |
| 166 | L755 | clock >= total delay | PropDelay: Clock Period | `period >= an.total_delay_ps` | Functional |
| 167 | L762 | test_ttl_init_and_register | PropDelay: Clock Period | `function-level test` | Initialization |
| 168 | L766 | initial props = 0 | TTL: Init & Register | `st.num_props == 0` | Initialization |
| 169 | L767 | current step = 0 | TTL: Init & Register | `st.current_step == 0` | Functional |
| 170 | L770 | register returns 0 | TTL: Init & Register | `p0 == 0` | Hardware/ALU |
| 171 | L772 | register returns 1 | TTL: Init & Register | `p1 == 1` | Hardware/ALU |
| 172 | L773 | num_props = 2 | TTL: Init & Register | `st.num_props == 2` | Functional |
| 173 | L776 | test_ttl_always | TTL: Init & Register | `function-level test` | Functional |
| 174 | L786 | ALWAYS(all TRUE) = TRUE | TTL: ALWAYS Operator | `ttl_always(&st, p) == TRIT_TRUE` | Functional |
| 175 | L789 | test_ttl_always_with_unknown | TTL: ALWAYS Operator | `function-level test` | Functional |
| 176 | L798 | ALWAYS(T,U,T) = UNKNOWN | TTL: ALWAYS with Unknow | `ttl_always(&st, p) == TRIT_UNKNOWN` | Functional |
| 177 | L801 | test_ttl_always_with_false | TTL: ALWAYS with Unknow | `function-level test` | Functional |
| 178 | L810 | ALWAYS(T,F,T) = FALSE | TTL: ALWAYS with False | `ttl_always(&st, p) == TRIT_FALSE` | Functional |
| 179 | L813 | test_ttl_eventually | TTL: ALWAYS with False | `function-level test` | Functional |
| 180 | L822 | EVENTUALLY(F,U,T) = TRUE | TTL: EVENTUALLY Operator | `ttl_eventually(&st, p) == TRIT_TRUE` | Functional |
| 181 | L830 | EVENTUALLY(F,F) = FALSE | TTL: EVENTUALLY Operator | `ttl_eventually(&st2, p2) == TRIT_FALSE` | Functional |
| 182 | L833 | test_ttl_never | TTL: EVENTUALLY Operator | `function-level test` | Functional |
| 183 | L841 | NEVER(F,F) = TRUE | TTL: NEVER Operator | `ttl_never(&st, p) == TRIT_TRUE` | Functional |
| 184 | L844 | NEVER after TRUE = FALSE | TTL: NEVER Operator | `ttl_never(&st, p) == TRIT_FALSE` | Functional |
| 185 | L847 | test_ttl_safety | TTL: NEVER Operator | `function-level test` | Functional |
| 186 | L855 | SAFETY(T,T) = SAFE | TTL: SAFETY Check | `ttl_safety(&st, p) == TTL_SAFE` | Functional |
| 187 | L858 | SAFETY(T,T,U) = UNCERTAIN | TTL: SAFETY Check | `ttl_safety(&st, p) == TTL_UNCERTAIN` | Functional |
| 188 | L865 | SAFETY(F) = VIOLATED | TTL: SAFETY Check | `ttl_safety(&st2, p2) == TTL_VIOLATED` | Functional |
| 189 | L868 | test_ttl_decide | TTL: SAFETY Check | `function-level test` | Functional |
| 190 | L878 | decide after TTT = ACT | TTL: Decision Logic | `ttl_decide(&st, p) == TTL_DECIDE_ACT` | Functional |
| 191 | L881 | test_ttl_decide_abort | TTL: Decision Logic | `function-level test` | Functional |
| 192 | L890 | decide with FALSE = ABORT | TTL: Decision Abort | `ttl_decide(&st, p) == TTL_DECIDE_ABORT` | Functional |
| 193 | L893 | test_ttl_evaluate | TTL: Decision Abort | `function-level test` | Hardware/ALU |
| 194 | L906 | true_count = 2 | TTL: Full Evaluatio | `result.true_count == 2` | Functional |
| 195 | L907 | unknown_count = 1 | TTL: Full Evaluatio | `result.unknown_count == 1` | Functional |
| 196 | L908 | false_count = 0 | TTL: Full Evaluatio | `result.false_count == 0` | Functional |
| 197 | L909 | confidence < 100 | TTL: Full Evaluatio | `result.confidence_pct < 100` | Functional |
| 198 | L910 | safety = UNCERTAIN | TTL: Full Evaluatio | `result.safety == TTL_UNCERTAIN` | Functional |
| 199 | L913 | test_ttl_majority_vote | TTL: Full Evaluatio | `function-level test` | Consensus |
| 200 | L928 | majority of (T,T,F) = TRUE | TTL: Majority Vote | `vote == TRIT_TRUE` | Consensus |
| 201 | L935 | test_pam3_encode_decode | TTL: Majority Vote | `function-level test` | Encoding |
| 202 | L944 | encode produces 8 symbols | PAM-3: Encode/Decode Roundtrip | `nsym == 8` | Encoding |
| 203 | L948 | decode produces 8 trits | PAM-3: Encode/Decode Roundtrip | `ndec == 8` | Encoding |
| 204 | L954 | PAM-3 roundtrip matches | PAM-3: Encode/Decode Roundtrip | `match` | Transformation |
| 205 | L957 | test_pam3_voltage_levels | PAM-3: Encode/Decode Roundtrip | `function-level test` | Functional |
| 206 | L963 | +1 → +400 mV | PAM-3: Voltage Levels | `frame.symbols[0].voltage_mv == PAM3_V_HIGH_MV` | Functional |
| 207 | L964 |  0 →    0 mV | PAM-3: Voltage Levels | `frame.symbols[1].voltage_mv == PAM3_V_MID_MV` | Functional |
| 208 | L965 | -1 → -400 mV | PAM-3: Voltage Levels | `frame.symbols[2].voltage_mv == PAM3_V_LOW_MV` | Functional |
| 209 | L968 | test_pam3_noise | PAM-3: Voltage Levels | `function-level test` | Functional |
| 210 | L977 | small noise corrupts few/none | PAM-3: Noise Injectio | `corrupted >= 0` | Negative/error |
| 211 | L980 | symbol 0 voltage defined | PAM-3: Noise Injectio | `frame.symbols[0].voltage_mv != 0 ∣∣ frame.symbols[0].trit_value == TRIT_UNKNOWN` | Linking |
| 212 | L983 | test_pam3_pre_emphasis | PAM-3: Noise Injectio | `function-level test` | Functional |
| 213 | L997 | test_pam3_eye_diagram | PAM-3: Pre-Emphasis | `function-level test` | Functional |
| 214 | L1006 | eye height > 0 | PAM-3: Eye Diagram | `height > 0` | Functional |
| 215 | L1007 | eye margin >= 0 | PAM-3: Eye Diagram | `margin >= 0` | Functional |
| 216 | L1010 | test_pam3_bandwidth_gain | PAM-3: Eye Diagram | `function-level test` | Functional |
| 217 | L1013 | bandwidth gain > 0 | PAM-3: Bandwidth Gai | `gain > 0` | Functional |
| 218 | L1015 | gain ~ 58% (±margin) | PAM-3: Bandwidth Gai | `gain > 400 && gain < 700` | Functional |
| 219 | L1018 | test_pam3_pam4_interop | PAM-3: Bandwidth Gai | `function-level test` | Functional |
| 220 | L1024 | PAM-4 encodes trits | PAM-3: PAM-4 Interop | `nsym > 0` | Encoding |
| 221 | L1028 | PAM-4 decodes trits | PAM-3: PAM-4 Interop | `ndec > 0` | Encoding |
| 222 | L1032 | PAM-4 decode count matches symbols | PAM-3: PAM-4 Interop | `ndec == nsym` | Encoding |
| 223 | L1035 | test_pam3_stats | PAM-3: PAM-4 Interop | `function-level test` | Functional |
| 224 | L1039 | initial symbols_sent = 0 | PAM-3: Stats Tracking | `stats.symbols_sent == 0` | Initialization |
| 225 | L1044 | stats symbols_sent = 3 | PAM-3: Stats Tracking | `stats.symbols_sent == 3` | Linking |
| 226 | L1045 | stats trits_encoded = 3 | PAM-3: Stats Tracking | `stats.trits_encoded == 3` | Encoding |
| 227 | L1052 | test_cross_twq_to_dlfet | PAM-3: Stats Tracking | `function-level test` | Functional |
| 228 | L1073 | TWQ→DLFET half add works | Cross: TWQ → DLFET Simulatio | `sum <= 2 && carry <= 2` | Arithmetic |
| 229 | L1076 | test_cross_rtc_pam3_pipeline | Cross: TWQ → DLFET Simulatio | `function-level test` | IPC |
| 230 | L1090 | RTC→PAM-3→RTC pipeline preserves value | Cross: Radix Transcode → PAM-3 Pipeline | `recovered == original` | IPC |
| 231 | L1093 | test_cross_srbc_pdelay | Cross: Radix Transcode → PAM-3 Pipeline | `function-level test` | Functional |
| 232 | L1104 | SRBC-informed delay computed | Cross: SRBC + PropDelay | `delay > 0` | Functional |
| 233 | L1107 | test_cross_crypto_ttl | Cross: SRBC + PropDelay | `function-level test` | Functional |

---

## Suite 21: Friday Updates

**Source**: `tests/test_friday_updates.c`
**Runtime Assertions**: 135
**Source-Level Entries**: 138
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L43 | test_stt_mram | General | `function-level test` | Functional |
| 2 | L50 | mram_init succeeds | Phase 1: Initializatio | `rc == 0` | Initialization |
| 3 | L51 | mram rows set | Phase 1: Initializatio | `arr.rows == 8` | Functional |
| 4 | L52 | mram cols set | Phase 1: Initializatio | `arr.cols == 8` | Functional |
| 5 | L53 | mram total_cells | Phase 1: Initializatio | `arr.total_cells == 64` | Functional |
| 6 | L60 | write +1 succeeds | Phase 2: Write / Read round-trip | `rc == 0` | Functional |
| 7 | L62 | read back +1 | Phase 2: Write / Read round-trip | `v == TRIT_TRUE` | Functional |
| 8 | L65 | write -1 succeeds | Phase 2: Write / Read round-trip | `rc == 0` | Functional |
| 9 | L67 | read back -1 | Phase 2: Write / Read round-trip | `v == TRIT_FALSE` | Functional |
| 10 | L70 | write 0 succeeds | Phase 2: Write / Read round-trip | `rc == 0` | Functional |
| 11 | L72 | read back 0 | Phase 2: Write / Read round-trip | `v == TRIT_UNKNOWN` | Functional |
| 12 | L78 | packed value < 243 | Phase 3: Pack / Unpack (5 trits → byte → 5 trits) | `packed < MRAM_PACK_BASE` | Encoding |
| 13 | L86 | unpack matches original | Phase 3: Pack / Unpack (5 trits → byte → 5 trits) | `pack_ok` | Encoding |
| 14 | L91 | all-zero pack gives 0+1 base values | Phase 3: Pack / Unpack (5 trits → byte → 5 trits) | `pz == (1+3+9+27+81)` | Encoding |
| 15 | L97 | xor succeeds | Phase 4: XOR at Sense Amplifier | `rc == 0` | Logic |
| 16 | L99 | (+1 xor +1) is balanced mod-3 result | Phase 4: XOR at Sense Amplifier | `v == TRIT_FALSE ∣∣ v == TRIT_UNKNOWN ∣∣ v == TRIT_TRUE` | Logic |
| 17 | L102 | (+1 xor +1) = -1 in balanced ternary | Phase 4: XOR at Sense Amplifier | `v == TRIT_FALSE` | Logic |
| 18 | L106 | R_LOW for state 0 | Phase 5: Nominal Resistance | `mram_nominal_resistance(MTJ_STATE_0) == MRAM_R_LOW_X10` | Logic |
| 19 | L107 | R_MID for state 1 | Phase 5: Nominal Resistance | `mram_nominal_resistance(MTJ_STATE_1) == MRAM_R_MID_X10` | Logic |
| 20 | L108 | R_HIGH for state 2 | Phase 5: Nominal Resistance | `mram_nominal_resistance(MTJ_STATE_2) == MRAM_R_HIGH_X10` | Logic |
| 21 | L113 | ecs_scan with no drift succeeds | Phase 6: ECS Scan (no drift) | `rc == 0` | Functional |
| 22 | L114 | ECS status stays STABLE | Phase 6: ECS Scan (no drift) | `arr.ecs_status == MRAM_ECS_STABLE` | Functional |
| 23 | L120 | inject_drift succeeds | Phase 7: Drift Injection & Detectio | `rc == 0` | Functional |
| 24 | L122 | ecs_scan detects drift and recalibrates | Phase 7: Drift Injection & Detectio | `rc == 0 ∣∣ rc == 1` | Logic |
| 25 | L127 | stabilize succeeds | Phase 8: Stabilize | `rc >= 0` | Functional |
| 26 | L132 | STABLE string not NULL | Phase 9: ECS Status String | `s != NULL` | Negative/error |
| 27 | L133 | STABLE string correct | Phase 9: ECS Status String | `strcmp(s, "STABLE") == 0` | Functional |
| 28 | L138 | out-of-bounds write returns error | Phase 10: Boundary checks | `rc != 0` | Boundary |
| 29 | L140 | out-of-bounds read returns Unknown | Phase 10: Boundary checks | `v == TRIT_UNKNOWN` | Boundary |
| 30 | L146 | test_tipc | Phase 10: Boundary checks | `function-level test` | IPC |
| 31 | L153 | channel active_count == 0 | Phase 1: Channel Initializatio | `ch.active_count == 0` | IPC |
| 32 | L154 | channel radix_violations == 0 | Phase 1: Channel Initializatio | `ch.radix_violations == 0` | IPC |
| 33 | L160 | endpoint 0 created | Phase 2: Endpoint Creatio | `ep0 == 0` | IPC |
| 34 | L161 | endpoint 1 created | Phase 2: Endpoint Creatio | `ep1 == 1` | IPC |
| 35 | L162 | active_count now 2 | Phase 2: Endpoint Creatio | `ch.active_count == 2` | Functional |
| 36 | L172 | compress succeeds | Phase 3: Huffman Compress / Decompress | `rc > 0` | Encoding |
| 37 | L173 | original_trits preserved | Phase 3: Huffman Compress / Decompress | `comp.original_trits == msg_len` | Functional |
| 38 | L174 | bit_count > 0 | Phase 3: Huffman Compress / Decompress | `comp.bit_count > 0` | Functional |
| 39 | L175 | bit_count <= 18 (worst case 9×2) | Phase 3: Huffman Compress / Decompress | `comp.bit_count <= 18` | Functional |
| 40 | L179 | decompress returns correct count | Phase 3: Huffman Compress / Decompress | `dc == msg_len` | Encoding |
| 41 | L184 | decompress matches original | Phase 3: Huffman Compress / Decompress | `dec_ok` | Encoding |
| 42 | L189 | guardian is valid trit | Phase 4: Guardian Trit | `g >= TRIT_FALSE && g <= TRIT_TRUE` | Functional |
| 43 | L193 | guardian is deterministic | Phase 4: Guardian Trit | `g == g2` | Boundary |
| 44 | L198 | send succeeds | Phase 5: Send / Receive | `rc == 0` | IPC |
| 45 | L202 | recv returns correct count | Phase 5: Send / Receive | `rlen == msg_len` | IPC |
| 46 | L207 | recv data matches sent data | Phase 5: Send / Receive | `recv_ok` | IPC |
| 47 | L221 | xor_diff succeeds | Phase 6: XOR Differential Update | `rc == 0` | Logic |
| 48 | L222 | guardian recomputed after diff | Phase 6: XOR Differential Update | `tipc_guardian_validate(&m) == TIPC_GUARDIAN_OK` | Functional |
| 49 | L228 | no violations for bytes < 243 | Phase 7: Radix Guard | `violations == 0` | Logic |
| 50 | L232 | detects violations for bytes >= 243 | Phase 7: Radix Guard | `violations == 1` | Logic |
| 51 | L237 | compression ratio > 0 | Phase 8: Compression Ratio | `ratio > 0` | Encoding |
| 52 | L238 | compression ratio <= 1000000 (≤100%) | Phase 8: Compression Ratio | `ratio <= 1000000` | Encoding |
| 53 | L243 | freq total = msg_len | Phase 9: Frequency Analysis | `freq.freq_neg + freq.freq_zero + freq.freq_pos == msg_len` | Functional |
| 54 | L251 | all-zero: 32 trits → 32 bits (1 bit each) | Phase 10: All-zero compression efficiency | `comp_z.bit_count == 32` | Functional |
| 55 | L257 | test_tfs | Phase 10: All-zero compression efficiency | `function-level test` | Functional |
| 56 | L264 | superblock magic[0] = T | Phase 1: Initializatio | `fs.magic[0] == TRIT_TRUE` | Memory |
| 57 | L265 | superblock magic[1] = F | Phase 1: Initializatio | `fs.magic[1] == TRIT_FALSE` | Memory |
| 58 | L266 | superblock magic[2] = T | Phase 1: Initializatio | `fs.magic[2] == TRIT_TRUE` | Memory |
| 59 | L270 | initial files == 0 | Phase 1: Initializatio | `files == 0` | Initialization |
| 60 | L271 | initial free_blocks == TFS_MAX_BLOCKS | Phase 1: Initializatio | `free_blocks == TFS_MAX_BLOCKS` | Boundary |
| 61 | L272 | initial reads == 0 | Phase 1: Initializatio | `reads == 0` | Initialization |
| 62 | L273 | initial writes == 0 | Phase 1: Initializatio | `writes == 0` | Initialization |
| 63 | L279 | open for write succeeds | Phase 2: File Open / Write / Read / Close | `rc == 0` | Logic |
| 64 | L283 | write 10 trits succeeds | Phase 2: File Open / Write / Read / Close | `rc == 10` | Functional |
| 65 | L289 | open for read succeeds | Phase 2: File Open / Write / Read / Close | `rc == 0` | Logic |
| 66 | L293 | read returns 10 trits | Phase 2: File Open / Write / Read / Close | `rlen == 10` | Functional |
| 67 | L298 | read data matches written data | Phase 2: File Open / Write / Read / Close | `data_ok` | Functional |
| 68 | L307 | huffman encode succeeds | Phase 3: Huffman Encode / Decode | `rc > 0` | Encoding |
| 69 | L308 | compressed bit_count > 0 | Phase 3: Huffman Encode / Decode | `cblk.bit_count > 0` | Encoding |
| 70 | L309 | compressed bit_count <= 32 (16×2 worst) | Phase 3: Huffman Encode / Decode | `cblk.bit_count <= 32` | Encoding |
| 71 | L310 | original_trits preserved | Phase 3: Huffman Encode / Decode | `cblk.original_trits == 16` | Functional |
| 72 | L314 | huffman decode returns 16 | Phase 3: Huffman Encode / Decode | `hlen == 16` | Encoding |
| 73 | L319 | huffman decode matches original | Phase 3: Huffman Encode / Decode | `huff_ok` | Encoding |
| 74 | L324 | guardian is valid trit | Phase 4: Guardian Compute | `guard >= -1 && guard <= 1` | Functional |
| 75 | L326 | guardian is deterministic | Phase 4: Guardian Compute | `guard == guard2` | Boundary |
| 76 | L331 | open for sync succeeds | Phase 5: Sync (guardian verification) | `rc == 0` | Logic |
| 77 | L333 | sync succeeds (guardians valid) | Phase 5: Sync (guardian verification) | `rc >= 0` | Functional |
| 78 | L339 | compress file succeeds | Phase 6: File Compressio | `rc >= 0` | Encoding |
| 79 | L342 | compression count > 0 | Phase 6: File Compressio | `compressions > 0` | Encoding |
| 80 | L347 | create append.trit succeeds | Phase 7: Append Mode | `rc == 0` | Functional |
| 81 | L353 | open for append succeeds | Phase 7: Append Mode | `rc == 0` | Logic |
| 82 | L356 | append write succeeds | Phase 7: Append Mode | `rc == 5` | Functional |
| 83 | L360 | reopen for read succeeds | Phase 7: Append Mode | `rc == 0` | Logic |
| 84 | L363 | appended file has 10 trits | Phase 7: Append Mode | `rlen == 10` | Functional |
| 85 | L369 | appended data correct | Phase 7: Append Mode | `app_ok` | Functional |
| 86 | L375 | unlink succeeds | Phase 8: Unlink | `rc == 0` | Linking |
| 87 | L377 | open after unlink creates new file | Phase 8: Unlink | `rc == 0` | Linking |
| 88 | L380 | reopen new file for read | Phase 8: Unlink | `rc == 0` | Logic |
| 89 | L382 | new file is empty | Phase 8: Unlink | `rlen == 0` | Negative/error |
| 90 | L388 | density gain >= 150 (1.5×) | Phase 9: Density & Area Metrics | `density >= 150` | Functional |
| 91 | L389 | density gain <= 200 (2.0×) | Phase 9: Density & Area Metrics | `density <= 200` | Functional |
| 92 | L392 | area reduction >= 50 (50%) | Phase 9: Density & Area Metrics | `area >= 50` | Functional |
| 93 | L393 | area reduction <= 80 (80%) | Phase 9: Density & Area Metrics | `area <= 80` | Functional |
| 94 | L398 | freq total = 10 | Phase 10: Frequency Analysis | `freq.freq_neg + freq.freq_zero + freq.freq_pos == 10` | Functional |
| 95 | L407 | open bigfile succeeds | Phase 11: Multi-block file (large write) | `rc == 0` | Functional |
| 96 | L409 | write 500 trits succeeds | Phase 11: Multi-block file (large write) | `rc == 500` | Functional |
| 97 | L413 | reopen bigfile succeeds | Phase 11: Multi-block file (large write) | `rc == 0` | Functional |
| 98 | L416 | read 500 trits back | Phase 11: Multi-block file (large write) | `rlen == 500` | Functional |
| 99 | L421 | 500-trit roundtrip matches | Phase 11: Multi-block file (large write) | `big_ok` | Transformation |
| 100 | L428 | test_cross_module | Phase 11: Multi-block file (large write) | `function-level test` | Functional |
| 101 | L455 | MRAM data sent via T-IPC | Phase 1: MRAM → T-IPC pipeline | `rc == 0` | IPC |
| 102 | L459 | T-IPC delivers MRAM data | Phase 1: MRAM → T-IPC pipeline | `rlen == 9` | IPC |
| 103 | L465 | MRAM→IPC data integrity | Phase 1: MRAM → T-IPC pipeline | `pipe_ok` | IPC |
| 104 | L474 | TFS file created for IPC dump | Phase 2: T-IPC → TFS storage | `rc == 0` | Logic |
| 105 | L477 | IPC data written to TFS | Phase 2: T-IPC → TFS storage | `rc == rlen` | IPC |
| 106 | L484 | TFS read back succeeds | Phase 2: T-IPC → TFS storage | `tlen == 9` | Functional |
| 107 | L490 | MRAM→IPC→TFS full pipeline integrity | Phase 2: T-IPC → TFS storage | `cross_ok` | IPC |
| 108 | L516 | TIPC and TFS Huffman decode match | Phase 3: Shared Huffman scheme consistency | `huff_match` | Logic |
| 109 | L523 | TIPC and TFS guardians match | Phase 4: Guardian scheme consistency | `tipc_g == tfs_g` | Logic |
| 110 | L529 | packed byte < 243 (radix-safe) | Phase 5: Pack trits from MRAM, send via IPC, store in TFS | `packed < 243` | Encoding |
| 111 | L533 | radix guard accepts packed trit byte | Phase 5: Pack trits from MRAM, send via IPC, store in TFS | `viol == 0` | Encoding |
| 112 | L546 | full pipeline: 5 trits round-trip | Phase 5: Pack trits from MRAM, send via IPC, store in TFS | `flen == 5` | IPC |
| 113 | L551 | full pipeline data integrity | Phase 5: Pack trits from MRAM, send via IPC, store in TFS | `final_ok` | IPC |
| 114 | L558 | test_spec_compliance | Phase 5: Pack trits from MRAM, send via IPC, store in TFS | `function-level test` | Functional |
| 115 | L563 | MRAM_TRITS_PER_BYTE == 5 | STT-MRAM Constants | `MRAM_TRITS_PER_BYTE == 5` | Functional |
| 116 | L564 | MRAM_PACK_BASE == 243 (3^5) | STT-MRAM Constants | `MRAM_PACK_BASE == 243` | Encoding |
| 117 | L565 | R_LOW (Parallel) = 50 | STT-MRAM Constants | `MRAM_R_LOW_X10 == 50` | Functional |
| 118 | L566 | R_MID (Orthogonal) = 120 | STT-MRAM Constants | `MRAM_R_MID_X10 == 120` | Functional |
| 119 | L567 | R_HIGH (Anti-Parallel) = 250 | STT-MRAM Constants | `MRAM_R_HIGH_X10 == 250` | Functional |
| 120 | L568 | ECS drift threshold = 20 | STT-MRAM Constants | `MRAM_ECS_DRIFT_THRESHOLD_X10 == 20` | Functional |
| 121 | L569 | Max recalibrations = 8 | STT-MRAM Constants | `MRAM_ECS_MAX_RECAL == 8` | Boundary |
| 122 | L573 | TIPC_MAX_TRITS == 512 | T-IPC Constants | `TIPC_MAX_TRITS == 512` | Boundary |
| 123 | L574 | TIPC_HUFF_ZERO_BITS == 1 | T-IPC Constants | `TIPC_HUFF_ZERO_BITS == 1` | IPC |
| 124 | L575 | TIPC_HUFF_POS_BITS == 2 | T-IPC Constants | `TIPC_HUFF_POS_BITS == 2` | IPC |
| 125 | L576 | TIPC_HUFF_NEG_BITS == 2 | T-IPC Constants | `TIPC_HUFF_NEG_BITS == 2` | IPC |
| 126 | L577 | TIPC_CMD_SEND == 0x10 | T-IPC Constants | `TIPC_CMD_SEND == 0x10` | IPC |
| 127 | L578 | TIPC_CMD_RECV == 0x11 | T-IPC Constants | `TIPC_CMD_RECV == 0x11` | IPC |
| 128 | L579 | TIPC_CMD_XOR_DIFF == 0x12 | T-IPC Constants | `TIPC_CMD_XOR_DIFF == 0x12` | Logic |
| 129 | L580 | TIPC_CMD_GUARD == 0x13 | T-IPC Constants | `TIPC_CMD_GUARD == 0x13` | IPC |
| 130 | L584 | TFS_BLOCK_TRITS == 243 (3^5) | TFS Constants | `TFS_BLOCK_TRITS == 243` | Memory |
| 131 | L585 | TFS_MAX_BLOCKS == 1024 | TFS Constants | `TFS_MAX_BLOCKS == 1024` | Boundary |
| 132 | L586 | TFS_MAX_FILES == 128 | TFS Constants | `TFS_MAX_FILES == 128` | Boundary |
| 133 | L587 | TFS_DENSITY_GAIN >= 158 | TFS Constants | `TFS_DENSITY_GAIN_X100 >= 158` | Functional |
| 134 | L588 | TFS_AREA_REDUCTION >= 60 | TFS Constants | `TFS_AREA_REDUCTION_X100 >= 60` | Functional |
| 135 | L596 | Unknown encodes to 1 bit | Huffman code lengths spec compliance | `c1.bit_count == 1` | Encoding |
| 136 | L602 | True encodes to 2 bits | Huffman code lengths spec compliance | `c2.bit_count == 2` | Encoding |
| 137 | L608 | False encodes to 2 bits | Huffman code lengths spec compliance | `c3.bit_count == 2` | Encoding |
| 138 | L615 | Huffman overhead <= 10% | Huffman code lengths spec compliance | `overhead_x100 <= 10` | Encoding |

---

## Suite 22: Trit Linux Architecture

**Source**: `tests/test_trit_linux.c`
**Runtime Assertions**: 98
**Source-Level Entries**: 96
**Harness**: Mixed CHECK/ASSERT harness
**Output Reading**: `[PASS]`/`[FAIL]` per assertion. Summary at end.

> **Note**: 2 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L141 | zero roundtrip | 1: Ternary Address Types | `trit_addr_to_int(a) == 0` | Transformation |
| 2 | L147 | 42 roundtrip | 1: Ternary Address Types | `trit_addr_to_int(a) == 42` | Transformation |
| 3 | L153 | -13 roundtrip | 1: Ternary Address Types | `trit_addr_to_int(a) == -13` | Transformation |
| 4 | L159 | 729 roundtrip | 1: Ternary Address Types | `trit_addr_to_int(a) == 729` | Transformation |
| 5 | L167 | 10+32=42 | 1: Ternary Address Types | `trit_addr_to_int(c) == 42` | Functional |
| 6 | L175 | 50+(-20)=30 | 1: Ternary Address Types | `trit_addr_to_int(c) == 30` | Functional |
| 7 | L183 | addr 0 → page 0 | 1: Ternary Address Types | `page == 0` | Arithmetic |
| 8 | L190 | addr 0 → offset 0 | 1: Ternary Address Types | `off == 0` | Arithmetic |
| 9 | L196 | 3^12 = 531441 | 1: Ternary Address Types | `TRIT_ADDR_SPACE == 531441` | Functional |
| 10 | L206 | boot with 64 pages | 2: Boot Sequence | `result == 0` | Memory |
| 11 | L210 | memory initialized | 2: Boot Sequence | `trit_boot_mem_ok()` | Memory |
| 12 | L213 | scheduler initialized | 2: Boot Sequence | `trit_boot_sched_ok()` | Scheduling |
| 13 | L216 | multi-radix initialized | 2: Boot Sequence | `trit_boot_mr_ok()` | Arithmetic |
| 14 | L219 | Kleene logic self-check | 2: Boot Sequence | `trit_boot_logic_ok()` | Logic |
| 15 | L222 | page manager initialized | 2: Boot Sequence | `trit_boot_pages_ok()` | Memory |
| 16 | L227 | kernel state pointer | 2: Boot Sequence | `ks != NULL` | Functional |
| 17 | L233 | emulation fallback OK | 2: Boot Sequence | `result == 0` | Arithmetic |
| 18 | L243 | tryte page size | 3: Tryte Page Allocator | `TRYTE_PAGE_SIZE == 729` | Memory |
| 19 | L250 | 32 pages, all free | 3: Tryte Page Allocator | `total == 32 && free_count == 32` | Memory |
| 20 | L256 | valid page index | 3: Tryte Page Allocator | `pg >= 0 && pg < 32` | Memory |
| 21 | L263 | free count decremented | 3: Tryte Page Allocator | `free_count == 31` | Arithmetic |
| 22 | L270 | distinct pages | 3: Tryte Page Allocator | `pg2 >= 0 && pg3 >= 0 && pg2 != pg3` | Memory |
| 23 | L278 | free then realloc | 3: Tryte Page Allocator | `freed == 0 && pg2 >= 0` | Memory |
| 24 | L288 | virt 5 → phys | 3: Tryte Page Allocator | `translated == phys` | Functional |
| 25 | L296 | unmapped → -1 | 3: Tryte Page Allocator | `translated == -1` | Transformation |
| 26 | L306 | unmap returns phys | 3: Tryte Page Allocator | `unmapped_phys == phys` | Transformation |
| 27 | L308 | unmap clears mapping | 3: Tryte Page Allocator | `t == -1` | Transformation |
| 28 | L319 | write T, read T | 3: Tryte Page Allocator | `v == TRIT_TRUE` | Functional |
| 29 | L329 | fresh page reads Unknown | 3: Tryte Page Allocator | `v == TRIT_UNKNOWN` | Memory |
| 30 | L339 | readonly write rejected | 3: Tryte Page Allocator | `r == -2` | Negative/error |
| 31 | L349 | fault counted | 3: Tryte Page Allocator | `faults >= 1` | Functional |
| 32 | L359 | clean slate | 4: IRQ Subsystem | `trit_irq_total_dispatched() == 0` | Functional |
| 33 | L365 | register success | 4: IRQ Subsystem | `r == 0` | Hardware/ALU |
| 34 | L369 | irq 0 registered | 4: IRQ Subsystem | `trit_irq_is_registered(0)` | Hardware/ALU |
| 35 | L375 | handler called | 4: IRQ Subsystem | `r == 0 && test_irq_fired == 1` | Functional |
| 36 | L379 | count = 1 | 4: IRQ Subsystem | `trit_irq_get_count(0) == 1` | Functional |
| 37 | L385 | count = 3 | 4: IRQ Subsystem | `trit_irq_get_count(0) == 3` | Functional |
| 38 | L392 | masked irq rejected | 4: IRQ Subsystem | `r == -2` | Negative/error |
| 39 | L399 | re-enabled irq fires | 4: IRQ Subsystem | `r == 0` | Functional |
| 40 | L405 | unregistered | 4: IRQ Subsystem | `!trit_irq_is_registered(0)` | Hardware/ALU |
| 41 | L411 | out of range rejected | 4: IRQ Subsystem | `r == -1` | Boundary |
| 42 | L421 | starts at 0 | 5: Timer | `trit_timer_get_ticks() == 0` | Initialization |
| 43 | L427 | tick = 1 | 5: Timer | `trit_timer_get_ticks() == 1` | Functional |
| 44 | L450 | stopped at 1 | 5: Timer | `trit_timer_get_ticks() == 1` | Functional |
| 45 | L457 | restarted, tick = 2 | 5: Timer | `trit_timer_get_ticks() == 2` | Initialization |
| 46 | L467 | features detected | 6: CPU Features | `trit_cpu_features() != 0` | Functional |
| 47 | L471 | SIMD available | 6: CPU Features | `trit_cpu_has_feature(TRIT_FEAT_SIMD)` | Functional |
| 48 | L474 | FFT available | 6: CPU Features | `trit_cpu_has_feature(TRIT_FEAT_FFT)` | Functional |
| 49 | L477 | dot product available | 6: CPU Features | `trit_cpu_has_feature(TRIT_FEAT_DOTPROD)` | Arithmetic |
| 50 | L480 | sparsity available | 6: CPU Features | `trit_cpu_has_feature(TRIT_FEAT_SPARSE)` | Functional |
| 51 | L483 | radix conv available | 6: CPU Features | `trit_cpu_has_feature(TRIT_FEAT_RADIXCONV)` | Functional |
| 52 | L486 | 32-trit width | 6: CPU Features | `trit_cpu_trit_width() == 32` | Functional |
| 53 | L489 | 32 SIMD lanes | 6: CPU Features | `trit_cpu_simd_lanes() == 32` | Functional |
| 54 | L494 | full arch setup | 6: CPU Features | `r == 0` | Initialization |
| 55 | L506 | net driver init | 7: Multi-Radix Network Driver | `r == 0` | Initialization |
| 56 | L510 | driver ready | 7: Multi-Radix Network Driver | `trit_net_is_ready()` | Functional |
| 57 | L516 | send success | 7: Multi-Radix Network Driver | `r == 0` | IPC |
| 58 | L523 | tx = 1 | 7: Multi-Radix Network Driver | `tx == 1` | Functional |
| 59 | L529 | loopback delivered 1 pkt | 7: Multi-Radix Network Driver | `looped == 1` | Functional |
| 60 | L544 | no more packets | 7: Multi-Radix Network Driver | `r == -1` | Encoding |
| 61 | L555 | packet marked valid | 7: Multi-Radix Network Driver | `pkt.valid == 1` | Encoding |
| 62 | L563 | dot([T,T,T,T], [T,T,T,T]) = 4 | 7: Multi-Radix Network Driver | `dot == 4` | Functional |
| 63 | L571 | dot([1,-1,0,1],[-1,1,1,0]) = -2 | 7: Multi-Radix Network Driver | `dot == -2` | Functional |
| 64 | L578 | FFT encode ok | 7: Multi-Radix Network Driver | `r == 0` | Encoding |
| 65 | L591 | 10 packets sent | 7: Multi-Radix Network Driver | `tx == 10` | Encoding |
| 66 | L597 | 10 packets looped back | 7: Multi-Radix Network Driver | `looped == 10` | Encoding |
| 67 | L609 | idle + init threads | 8: Scheduler via Boot Kernel | `total >= 2` | Scheduling |
| 68 | L616 | picked a thread | 8: Scheduler via Boot Kernel | `tid >= 0` | Scheduling |
| 69 | L624 | priority changed | 8: Scheduler via Boot Kernel | `tid >= 0 && r == 0` | Scheduling |
| 70 | L631 | yield success | 8: Scheduler via Boot Kernel | `r >= 0` | Scheduling |
| 71 | L640 | block then unblock | 8: Scheduler via Boot Kernel | `r1 == 0 && r2 == 0` | Memory |
| 72 | L651 | endpoint created | 9: IPC via Boot Kernel | `ep >= 0` | IPC |
| 73 | L666 | send+recv | 9: IPC via Boot Kernel | `r == 0` | IPC |
| 74 | L674 | notification signalled | 9: IPC via Boot Kernel | `notif >= 0 && r == 0` | IPC |
| 75 | L685 | mmap via syscall | 10: Syscall Dispatch | `r.retval >= 0` | Transformation |
| 76 | L692 | thread create via syscall | 10: Syscall Dispatch | `r.retval >= 0` | Scheduling |
| 77 | L699 | dot trit via syscall | 10: Syscall Dispatch | `r.retval >= -32 && r.retval <= 32` | Functional |
| 78 | L706 | radix conv via syscall | 10: Syscall Dispatch | `r.retval >= 0` | Functional |
| 79 | L717 | capability created | 11: Capability System | `cap >= 0` | Access control |
| 80 | L725 | capability check pass | 11: Capability System | `ok == TRIT_TRUE` | Access control |
| 81 | L734 | revoked cap fails check | 11: Capability System | `r == 0 && ok != TRIT_TRUE` | Negative/error |
| 82 | L749 | all 3 values roundtrip | 12: Emulation Layer (trit2) | `ok` | Transformation |
| 83 | L759 | all 32 trits = T | 12: Emulation Layer (trit2) | `ok` | Functional |
| 84 | L769 | census: 1F, 30U, 1T | 12: Emulation Layer (trit2) | `nf == 1 && nt == 1 && nu == 30` | Functional |
| 85 | L782 | bulk AND(T,F) = F | 12: Emulation Layer (trit2) | `ok` | Functional |
| 86 | L795 | 42 → ternary → 42 | 13: Multi-Radix Engine | `back == 42` | Functional |
| 87 | L805 | dot(T,T) = 32 | 13: Multi-Radix Engine | `d == 32` | Functional |
| 88 | L814 | FFT step success | 13: Multi-Radix Engine | `r >= 0` | Functional |
| 89 | L824 | 2 instructions recorded | 13: Multi-Radix Engine | `snap.total_insns == 2` | Hardware/ALU |
| 90 | L839 | full alloc→map→write→read | 14: Full Stack Integratio | `v == TRIT_TRUE` | Memory |
| 91 | L853 | ipc_recv succeeds | 14: Full Stack Integratio | `r == 0` | IPC |
| 92 | L854 | received msg[0] = TRUE | 14: Full Stack Integratio | `recv.words[0] == TRIT_TRUE` | Functional |
| 93 | L855 | sched+ipc roundtrip | 14: Full Stack Integratio | `tid >= 0` | IPC |
| 94 | L870 | send→loopback→dot match | 14: Full Stack Integratio | `dot == 4` | IPC |
| 95 | L878 | cap protects memory access | 14: Full Stack Integratio | `ok == TRIT_TRUE` | Memory |
| 96 | L892 | ternary addr → page write/read | 14: Full Stack Integratio | `v == TRIT_FALSE` | Arithmetic |

---

## Suite 23: Trit Enhancements

**Source**: `tests/test_trit_enhancements.c`
**Runtime Assertions**: 252
**Source-Level Entries**: 214
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

> **Note**: 38 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L100 | test_posix_coreutils | General | `function-level test` | Functional |
| 2 | L109 | init should succeed | 1.1 Environment Initializatio | `tcore_init(&env) == TCORE_OK` | Initialization |
| 3 | L112 | initialized flag | 1.1 Environment Initializatio | `env.initialized == 1` | Initialization |
| 4 | L115 | cmd_count should be 0 | 1.1 Environment Initializatio | `env.cmd_count == 0` | Functional |
| 5 | L118 | errors should be 0 | 1.1 Environment Initializatio | `env.errors == 0` | Negative/error |
| 6 | L121 | NULL init should fail | 1.1 Environment Initializatio | `tcore_init(NULL) == TCORE_ERR_IO` | Negative/error |
| 7 | L129 | echo OK | 1.2 trit-echo (File Writing) | `tcore_echo(&env, "hello.t", data1, 5) == TCORE_OK` | Functional |
| 8 | L132 | cmd_count incremented | 1.2 trit-echo (File Writing) | `env.cmd_count > 0` | Arithmetic |
| 9 | L135 | NULL env | 1.2 trit-echo (File Writing) | `tcore_echo(NULL, "x.t", data1, 5) == TCORE_ERR_IO` | Negative/error |
| 10 | L138 | NULL path | 1.2 trit-echo (File Writing) | `tcore_echo(&env, NULL, data1, 5) == TCORE_ERR_IO` | Negative/error |
| 11 | L141 | zero len | 1.2 trit-echo (File Writing) | `tcore_echo(&env, "z.t", data1, 0) == TCORE_ERR_IO` | Functional |
| 12 | L151 | should read 5 trits | 1.3 trit-cat (File Reading) | `nread == 5` | Functional |
| 13 | L154 | trit[0] == 1 | 1.3 trit-cat (File Reading) | `buf[0] == 1` | Functional |
| 14 | L157 | trit[1] == 0 | 1.3 trit-cat (File Reading) | `buf[1] == 0` | Functional |
| 15 | L160 | trit[2] == -1 | 1.3 trit-cat (File Reading) | `buf[2] == -1` | Functional |
| 16 | L163 | trit[3] == 1 | 1.3 trit-cat (File Reading) | `buf[3] == 1` | Functional |
| 17 | L166 | trit[4] == -1 | 1.3 trit-cat (File Reading) | `buf[4] == -1` | Functional |
| 18 | L173 | NULL env | 1.3 trit-cat (File Reading) | `tcore_cat(NULL, "hello.t", buf, 64) == TCORE_ERR_IO` | Negative/error |
| 19 | L179 | cp OK | 1.4 trit-cp (File Copy) | `tcore_cp(&env, "hello.t", "copy.t") == TCORE_OK` | Functional |
| 20 | L184 | copy matches | 1.4 trit-cp (File Copy) | `nc == 5 && cpbuf[0] == 1 && cpbuf[4] == -1` | Functional |
| 21 | L187 | no src | 1.4 trit-cp (File Copy) | `tcore_cp(&env, "nope.t", "dst.t") == TCORE_ERR_NOTFOUND` | Functional |
| 22 | L195 | ls OK | 1.5 trit-ls (Directory Listing) | `tcore_ls(&env, &ls) == TCORE_OK` | Functional |
| 23 | L198 | at least hello.t and copy.t | 1.5 trit-ls (Directory Listing) | `ls.count >= 2` | Logic |
| 24 | L201 | non-zero total trits | 1.5 trit-ls (Directory Listing) | `ls.total_trits > 0` | Functional |
| 25 | L204 | NULL result | 1.5 trit-ls (Directory Listing) | `tcore_ls(&env, NULL) == TCORE_ERR_IO` | Negative/error |
| 26 | L218 | at least one match | 1.6 trit-grep (Pattern Search) | `grc >= 1` | Parsing |
| 27 | L221 | match_count >= 1 | 1.6 trit-grep (Pattern Search) | `grep.match_count >= 1` | Functional |
| 28 | L226 | no matches | 1.6 trit-grep (Pattern Search) | `grep.match_count == 0` | Functional |
| 29 | L240 | 5 trits | 1.7 trit-wc (Word Count) | `wc_trits == 5` | Functional |
| 30 | L243 | at least one word | 1.7 trit-wc (Word Count) | `wc_words > 0` | Parsing |
| 31 | L253 | rm OK | 1.8 trit-rm (File Removal) | `tcore_rm(&env, "copy.t") == TCORE_OK` | Functional |
| 32 | L260 | rm missing | 1.8 trit-rm (File Removal) | `tcore_rm(&env, "copy.t") == TCORE_ERR_NOTFOUND` | Functional |
| 33 | L268 | head 3 trits | 1.9 trit-head / trit-tail | `hn == 3 && hbuf[0] == 1 && hbuf[2] == -1` | Functional |
| 34 | L273 | tail 2 trits | 1.9 trit-head / trit-tail | `tn == 2 && tbuf[0] == 1 && tbuf[1] == -1` | Functional |
| 35 | L276 | head 0 = 0 | 1.9 trit-head / trit-tail | `tcore_head(&env, "hello.t", hbuf, 0) == 0` | Functional |
| 36 | L288 | transcode init | 1.10 Binary-to-Ternary Transcoding | `tcore_transcode_init(&tc) == TCORE_OK` | Initialization |
| 37 | L291 | guard clean | 1.10 Binary-to-Ternary Transcoding | `tc.guard.guard_status == TRIT_TRUE` | Functional |
| 38 | L298 | output trits > 0 | 1.10 Binary-to-Ternary Transcoding | `tc_len > 0` | Functional |
| 39 | L301 | 4 ints * 32 trits/int | 1.10 Binary-to-Ternary Transcoding | `tc_len == 4 * MR_REG_WIDTH` | Functional |
| 40 | L304 | binary cycles > 0 | 1.10 Binary-to-Ternary Transcoding | `tc.cycles_binary > 0` | Performance |
| 41 | L311 | valid data | 1.11 Radix Integrity Guard | `tcore_radix_validate(&tc, good_data, 6) == TCORE_OK` | Functional |
| 42 | L319 | guard compromised | 1.11 Radix Integrity Guard | `tc.guard.guard_status == TRIT_FALSE` | Functional |
| 43 | L322 | violations > 0 | 1.11 Radix Integrity Guard | `tc.guard.violations > 0` | Functional |
| 44 | L331 | uninit env ls | 1.12 Edge Cases | `tcore_ls(&uninit, &ls) == TCORE_ERR_IO` | Initialization |
| 45 | L334 | NULL data | 1.12 Edge Cases | `tcore_echo(&env, "x.t", NULL, 5) == TCORE_ERR_IO` | Negative/error |
| 46 | L351 | test_networking_stack | 1.12 Edge Cases | `function-level test` | Memory |
| 47 | L361 | 42 roundtrip | 2.1 Address Utilities | `tnet_addr_to_int(&addr1) == 42` | Transformation |
| 48 | L365 | 0 roundtrip | 2.1 Address Utilities | `tnet_addr_to_int(&addr1) == 0` | Transformation |
| 49 | L369 | -13 roundtrip | 2.1 Address Utilities | `tnet_addr_to_int(&addr1) == -13` | Transformation |
| 50 | L374 | different addrs | 2.1 Address Utilities | `tnet_addr_equal(&addr1, &addr2) == 0` | Arithmetic |
| 51 | L378 | same addr | 2.1 Address Utilities | `tnet_addr_equal(&addr1, &addr2) == 1` | Arithmetic |
| 52 | L385 | port 80 | 2.1 Address Utilities | `tnet_port_to_int(&port1) == 80` | Functional |
| 53 | L389 | port 0 | 2.1 Address Utilities | `tnet_port_to_int(&port1) == 0` | Functional |
| 54 | L399 | init OK | 2.2 Stack Initializatio | `tnet_init(&stack, &local) == TNET_OK` | Initialization |
| 55 | L402 | initialized | 2.2 Stack Initializatio | `stack.initialized == 1` | Initialization |
| 56 | L405 | local addr 100 | 2.2 Stack Initializatio | `tnet_addr_to_int(&stack.local_addr) == 100` | Arithmetic |
| 57 | L408 | NULL stack | 2.2 Stack Initializatio | `tnet_init(NULL, &local) == TNET_ERR_INIT` | Negative/error |
| 58 | L411 | NULL addr | 2.2 Stack Initializatio | `tnet_init(&stack, NULL) == TNET_ERR_INIT` | Negative/error |
| 59 | L433 | valid | 2.3 Packet Building | `pkt.valid == 1` | Functional |
| 60 | L436 | payload len 4 | 2.3 Packet Building | `pkt.header.payload_len == 4` | Functional |
| 61 | L439 | proto DATA | 2.3 Packet Building | `pkt.header.protocol == TNET_PROTO_DATA` | Functional |
| 62 | L447 | checksum present | 2.3 Packet Building | `has_checksum ∣∣ pkt.header.payload_len > 0` | Arithmetic |
| 63 | L454 | checksum valid | 2.4 Checksum Verificatio | `tnet_checksum_verify(&pkt) == TRIT_TRUE` | Arithmetic |
| 64 | L460 | checksum invalid | 2.4 Checksum Verificatio | `tnet_checksum_verify(&bad_pkt) == TRIT_FALSE` | Negative/error |
| 65 | L468 | send OK | 2.5 Send / Receive / Loopback | `snd == TNET_OK` | IPC |
| 66 | L471 | tx count | 2.5 Send / Receive / Loopback | `stack.total_tx >= 1` | Functional |
| 67 | L475 | 1 packet looped | 2.5 Send / Receive / Loopback | `looped == 1` | Encoding |
| 68 | L479 | recv OK | 2.5 Send / Receive / Loopback | `tnet_recv(&stack, &rxpkt) == TNET_OK` | IPC |
| 69 | L486 | empty queue | 2.5 Send / Receive / Loopback | `tnet_recv(&stack, &rxpkt) == TNET_ERR_NOCONN` | Negative/error |
| 70 | L494 | no loopback for other addr | 2.5 Send / Receive / Loopback | `looped2 == 0` | Arithmetic |
| 71 | L528 | deny result | 2.6 Kleene Firewall | `result == TRIT_FALSE` | Negative/error |
| 72 | L537 | allow result | 2.6 Kleene Firewall | `result == TRIT_TRUE` | Functional |
| 73 | L546 | inspect result | 2.6 Kleene Firewall | `result == TRIT_UNKNOWN` | Functional |
| 74 | L553 | at least 1 denied | 2.6 Kleene Firewall | `denied >= 1` | Parsing |
| 75 | L562 | all denied | 2.6 Kleene Firewall | `tnet_loopback(&stack) == 0` | Functional |
| 76 | L574 | conn id >= 0 | 2.7 Connection Management | `cid >= 0` | Functional |
| 77 | L577 | established | 2.7 Connection Management | `tnet_conn_state(&stack, cid) == TRIT_TRUE` | Functional |
| 78 | L580 | disconnect OK | 2.7 Connection Management | `tnet_disconnect(&stack, cid) == TNET_OK` | Functional |
| 79 | L583 | closed | 2.7 Connection Management | `tnet_conn_state(&stack, cid) == TRIT_FALSE` | Functional |
| 80 | L586 | already closed | 2.7 Connection Management | `tnet_disconnect(&stack, cid) == TNET_ERR_NOCONN` | Functional |
| 81 | L589 | invalid id | 2.7 Connection Management | `tnet_conn_state(&stack, 999) == TRIT_FALSE` | Negative/error |
| 82 | L597 | arp add | 2.8 ARP Cache | `tnet_arp_update(&stack, &dst, 0xAB) == TNET_OK` | Arithmetic |
| 83 | L600 | arp lookup | 2.8 ARP Cache | `tnet_arp_lookup(&stack, &dst) == 0xAB` | Functional |
| 84 | L605 | arp miss | 2.8 ARP Cache | `tnet_arp_lookup(&stack, &unknown) == -1` | Functional |
| 85 | L609 | arp overwrite | 2.8 ARP Cache | `tnet_arp_lookup(&stack, &dst) == 0xCD` | Functional |
| 86 | L617 | ping self OK | 2.9 Ping Utility | `tnet_ping(&stack, &local) == 1` | Functional |
| 87 | L620 | ping other = 0 | 2.9 Ping Utility | `tnet_ping(&stack, &other) == 0` | Functional |
| 88 | L629 | stats returned | 2.10 Statistics | `tx >= 0 && rx >= 0` | Functional |
| 89 | L639 | test_gui_framework | 2.10 Statistics | `function-level test` | Functional |
| 90 | L648 | init OK | 3.1 Compositor Initializatio | `tgui_init(&comp) == 0` | Initialization |
| 91 | L651 | initialized | 3.1 Compositor Initializatio | `comp.initialized == 1` | Initialization |
| 92 | L654 | no windows | 3.1 Compositor Initializatio | `comp.window_count == 0` | Functional |
| 93 | L657 | NULL init fails | 3.1 Compositor Initializatio | `tgui_init(NULL) == -1` | Negative/error |
| 94 | L671 | pixel is gray | 3.2 Framebuffer Operations | `px.r == 0 && px.g == 0 && px.b == 0` | Functional |
| 95 | L675 | set pixel OK | 3.2 Framebuffer Operations | `tgui_set_pixel(&comp, 10, 5, red) == 0` | Functional |
| 96 | L680 | pixel is red | 3.2 Framebuffer Operations | `px.r == 1 && px.g == -1 && px.b == -1` | Functional |
| 97 | L684 | negative x | 3.2 Framebuffer Operations | `tgui_set_pixel(&comp, -1, 0, red) == -1` | Negative/error |
| 98 | L685 | big x | 3.2 Framebuffer Operations | `tgui_set_pixel(&comp, 999, 0, red) == -1` | Functional |
| 99 | L686 | negative y | 3.2 Framebuffer Operations | `tgui_set_pixel(&comp, 0, -1, red) == -1` | Negative/error |
| 100 | L687 | big y | 3.2 Framebuffer Operations | `tgui_set_pixel(&comp, 0, 999, red) == -1` | Functional |
| 101 | L692 | OOB = black | 3.2 Framebuffer Operations | `px.r == -1 && px.g == -1 && px.b == -1` | Functional |
| 102 | L717 | vline blue | 3.3 Drawing Primitives | `px0.b == 1 && px2.b == 1` | Functional |
| 103 | L725 | corner is red | 3.3 Drawing Primitives | `corner.r == 1` | Functional |
| 104 | L734 | fill rect green inside | 3.3 Drawing Primitives | `pxIn.g == 1 && pxOut.g == -1` | Functional |
| 105 | L766 | window created | 3.5 Window Management | `wid >= 0` | Functional |
| 106 | L769 | 1 window | 3.5 Window Management | `comp.window_count == 1` | Functional |
| 107 | L773 | second window | 3.5 Window Management | `wid2 >= 0 && wid2 != wid` | Functional |
| 108 | L780 | move OK | 3.5 Window Management | `tgui_window_move(&comp, wid, 5, 5) == 0` | Functional |
| 109 | L783 | hide OK | 3.5 Window Management | `tgui_window_set_visible(&comp, wid2, 0) == 0` | Functional |
| 110 | L786 | destroy OK | 3.5 Window Management | `tgui_window_destroy(&comp, wid2) == 0` | Functional |
| 111 | L787 | 1 window left | 3.5 Window Management | `comp.window_count == 1` | Functional |
| 112 | L790 | double destroy | 3.5 Window Management | `tgui_window_destroy(&comp, wid2) == -1` | Functional |
| 113 | L796 | composite OK | 3.6 Compositing | `tgui_composite(&comp) == 0` | Functional |
| 114 | L799 | 1 frame | 3.6 Compositing | `comp.frames_rendered == 1` | Functional |
| 115 | L811 | push OK | 3.7 Event Handling | `tgui_event_push(&comp, &evt) == 0` | Functional |
| 116 | L814 | 1 event | 3.7 Event Handling | `tgui_event_count(&comp) == 1` | Functional |
| 117 | L818 | pop OK | 3.7 Event Handling | `tgui_event_pop(&comp, &out) == 0` | Functional |
| 118 | L821 | key down | 3.7 Event Handling | `out.type == TGUI_EVT_KEY_DOWN` | Functional |
| 119 | L824 | key A | 3.7 Event Handling | `out.key_code == 65` | Functional |
| 120 | L827 | empty queue | 3.7 Event Handling | `tgui_event_pop(&comp, &out) == -1` | Negative/error |
| 121 | L836 | stats non-zero | 3.8 Statistics | `frames >= 1 && pixels > 0 && events >= 1` | Functional |
| 122 | L849 | test_package_manager | 3.8 Statistics | `function-level test` | Encoding |
| 123 | L858 | init OK | 4.1 Repository Initializatio | `tpkg_init(&repo) == TPKG_OK` | Initialization |
| 124 | L861 | initialized | 4.1 Repository Initializatio | `repo.initialized == 1` | Initialization |
| 125 | L864 | 0 packages | 4.1 Repository Initializatio | `repo.package_count == 0` | Encoding |
| 126 | L867 | NULL init | 4.1 Repository Initializatio | `tpkg_init(NULL) == TPKG_ERR_IO` | Negative/error |
| 127 | L884 | 2 packages | 4.2 Package Additio | `repo.package_count == 2` | Encoding |
| 128 | L916 | install OK | 4.4 Dependency Resolutio | `tpkg_install(&repo, "trit-utils") == TPKG_OK` | Functional |
| 129 | L919 | deps OK | 4.4 Dependency Resolutio | `tpkg_resolve_deps(&repo, "trit-crypto") == TPKG_OK` | Functional |
| 130 | L925 | install crypto | 4.5 Install / Remove | `tpkg_install(&repo, "trit-crypto") == TPKG_OK` | Functional |
| 131 | L928 | 2 installed | 4.5 Install / Remove | `repo.installed_count == 2` | Functional |
| 132 | L935 | is installed | 4.5 Install / Remove | `tpkg_is_installed(&repo, "trit-crypto") == 1` | Functional |
| 133 | L938 | remove OK | 4.5 Install / Remove | `tpkg_remove(&repo, "trit-crypto") == TPKG_OK` | Functional |
| 134 | L941 | 1 installed | 4.5 Install / Remove | `repo.installed_count == 1` | Functional |
| 135 | L944 | not installed | 4.5 Install / Remove | `tpkg_is_installed(&repo, "trit-crypto") == 0` | Logic |
| 136 | L947 | no such pkg | 4.5 Install / Remove | `tpkg_remove(&repo, "nope") == TPKG_ERR_NOTFOUND` | Functional |
| 137 | L971 | found results | 4.7 Search | `tpkg_search(&repo, "trit", &sr) >= 1` | Functional |
| 138 | L974 | at least 2 matches | 4.7 Search | `sr.count >= 2` | Parsing |
| 139 | L977 | 0 matches | 4.7 Search | `tpkg_search(&repo, "zzz_no_match", &sr) == 0` | Functional |
| 140 | L983 | 1 installed | 4.7 Search | `n == 1 && ins.count == 1` | Functional |
| 141 | L990 | verify OK | 4.8 Integrity Verificatio | `tpkg_verify(&repo, "trit-utils") == TPKG_OK` | Functional |
| 142 | L1007 | could not find trit-crypto | 4.8 Integrity Verificatio | `0` | Logic |
| 143 | L1018 | at least 3 packages | 4.9 Statistics | `total >= 3` | Encoding |
| 144 | L1019 | at least 1 installed | 4.9 Statistics | `installed >= 1` | Parsing |
| 145 | L1045 | test_ai_integration | 4.10 Optional Dependencies | `function-level test` | Functional |
| 146 | L1054 | init OK | 5.1 Model Initializatio | `tai_model_init(&model) == TAI_OK` | Initialization |
| 147 | L1057 | initialized | 5.1 Model Initializatio | `model.initialized == 1` | Initialization |
| 148 | L1060 | 0 layers | 5.1 Model Initializatio | `model.layer_count == 0` | Functional |
| 149 | L1063 | NULL init | 5.1 Model Initializatio | `tai_model_init(NULL) == TAI_ERR_INIT` | Negative/error |
| 150 | L1069 | layer 1 added | 5.2 Layer Management | `tai_add_layer(&model, 4, 3) == TAI_OK` | Arithmetic |
| 151 | L1072 | layer 2 added | 5.2 Layer Management | `tai_add_layer(&model, 3, 2) == TAI_OK` | Arithmetic |
| 152 | L1075 | 2 layers | 5.2 Layer Management | `model.layer_count == 2` | Functional |
| 153 | L1078 | zero input | 5.2 Layer Management | `tai_add_layer(&model, 0, 3) == TAI_ERR_DIM` | Functional |
| 154 | L1079 | zero output | 5.2 Layer Management | `tai_add_layer(&model, 3, 0) == TAI_ERR_DIM` | Functional |
| 155 | L1086 | w[0][0]=+1 | 5.3 Weight Setting | `tai_set_weight(&model, 0, 0, 0, TRIT_TRUE) == TAI_OK` | Functional |
| 156 | L1089 | w[1][1]=+1 | 5.3 Weight Setting | `tai_set_weight(&model, 0, 1, 1, TRIT_TRUE) == TAI_OK` | Functional |
| 157 | L1092 | w[2][2]=-1 | 5.3 Weight Setting | `tai_set_weight(&model, 0, 2, 2, TRIT_FALSE) == TAI_OK` | Functional |
| 158 | L1095 | OOB row | 5.3 Weight Setting | `tai_set_weight(&model, 0, 99, 0, TRIT_TRUE) == TAI_ERR_DIM` | Functional |
| 159 | L1111 | bias OK | 5.4 Bias Setting | `tai_set_bias(&model, 0, 0, 0) == TAI_OK` | Functional |
| 160 | L1114 | OOB bias | 5.4 Bias Setting | `tai_set_bias(&model, 0, 99, 0) == TAI_ERR_DIM` | Functional |
| 161 | L1138 | matvec OK | 5.5 Matrix-Vector Multiplicatio | `tai_matvec(&mat, &vec, &result) == TAI_OK` | Functional |
| 162 | L1142 | row 0 = 2 | 5.5 Matrix-Vector Multiplicatio | `result.data[0] == 2` | Functional |
| 163 | L1146 | row 1 = -1 | 5.5 Matrix-Vector Multiplicatio | `result.data[1] == -1` | Functional |
| 164 | L1153 | dim err | 5.5 Matrix-Vector Multiplicatio | `tai_matvec(&mat, &short_vec, &result) == TAI_ERR_DIM` | Functional |
| 165 | L1168 | dot = 1 | 5.6 Dot Product | `tai_dot(&va, &vb) == 1` | Functional |
| 166 | L1171 | dot self = 3 | 5.6 Dot Product | `tai_dot(&va, &va) == 3` | Functional |
| 167 | L1187 | infer OK | 5.7 Inference | `tai_infer(&model, &input, &output) == TAI_OK` | Type system |
| 168 | L1190 | output dim 2 | 5.7 Inference | `output.len == 2` | Functional |
| 169 | L1193 | inferences tracked | 5.7 Inference | `model.inferences >= 1` | Type system |
| 170 | L1205 | argmax = 1 | 5.8 Argmax | `tai_argmax(&av) == 1` | Boundary |
| 171 | L1213 | first wins tie | 5.8 Argmax | `tai_argmax(&av2) == 0` | Functional |
| 172 | L1216 | NULL = -1 | 5.8 Argmax | `tai_argmax(NULL) == -1` | Negative/error |
| 173 | L1228 | mr row0 matches | 5.9 Multi-Radix MatVec | `mr_result.data[0] == result.data[0]` | Functional |
| 174 | L1237 | sparsity >= 0 | 5.10 Sparsity Analysis | `sp >= 0` | Functional |
| 175 | L1241 | invalid layer | 5.10 Sparsity Analysis | `tai_sparsity(&model, 99) == 0` | Negative/error |
| 176 | L1253 | train OK | 5.11 Training | `tai_train_step(&model, &input, 0, &tcfg) == TAI_OK` | Functional |
| 177 | L1257 | inference count grew from training | 5.11 Training | `model.inferences >= 2` | Type system |
| 178 | L1266 | stats non-zero | 5.12 Statistics | `inf > 0 && macs > 0` | Functional |
| 179 | L1276 | test_security_auditing | 5.12 Statistics | `function-level test` | Functional |
| 180 | L1285 | init OK | 6.1 Security Module Initializatio | `tsec_init(&sec) == TSEC_OK` | Initialization |
| 181 | L1288 | initialized | 6.1 Security Module Initializatio | `sec.initialized == 1` | Initialization |
| 182 | L1291 | channel secure | 6.1 Security Module Initializatio | `sec.sidechannel.channel_status == TRIT_TRUE` | IPC |
| 183 | L1294 | NULL init | 6.1 Security Module Initializatio | `tsec_init(NULL) == TSEC_ERR_INIT` | Negative/error |
| 184 | L1305 | 1 log entry | 6.2 Audit Logging | `sec.log_count == 1` | Functional |
| 185 | L1310 | 1 denial | 6.2 Audit Logging | `sec.total_denials == 1` | Functional |
| 186 | L1315 | 1 escalation | 6.2 Audit Logging | `sec.total_escalations == 1` | Functional |
| 187 | L1318 | 3 total events | 6.2 Audit Logging | `sec.log_total == 3` | Functional |
| 188 | L1327 | 3 recent entries | 6.3 Audit Retrieval | `n == 3` | Functional |
| 189 | L1330 | most recent | 6.3 Audit Retrieval | `recent[0].event_type == TSEC_EVT_ESCALATION` | Functional |
| 190 | L1333 | 1 syscall | 6.3 Audit Retrieval | `tsec_audit_count_type(&sec, TSEC_EVT_SYSCALL) == 1` | Functional |
| 191 | L1336 | 1 file event | 6.3 Audit Retrieval | `tsec_audit_count_type(&sec, TSEC_EVT_FILE) == 1` | Functional |
| 192 | L1339 | 1 escalation | 6.3 Audit Retrieval | `tsec_audit_count_escalations(&sec) == 1` | Functional |
| 193 | L1363 | deny | 6.4 Policy Enforcement | `r == TRIT_FALSE` | Negative/error |
| 194 | L1369 | allow | 6.4 Policy Enforcement | `r == TRIT_TRUE` | Functional |
| 195 | L1375 | audit | 6.4 Policy Enforcement | `r == TRIT_UNKNOWN` | Functional |
| 196 | L1381 | default allow | 6.4 Policy Enforcement | `r == TRIT_TRUE` | Functional |
| 197 | L1396 | enforcement logged | 6.5 Enforce | `sec.log_total >= 5` | Functional |
| 198 | L1405 | sandbox created | 6.6 Sandboxing | `sb_id >= 0` | Functional |
| 199 | L1408 | 1 sandbox | 6.6 Sandboxing | `sec.sandbox_count == 1` | Functional |
| 200 | L1436 | sb2 created | 6.6 Sandboxing | `sb_id2 >= 0` | Functional |
| 201 | L1437 | 2 sandboxes | 6.6 Sandboxing | `sec.sandbox_count == 2` | Functional |
| 202 | L1440 | sb2 destroyed | 6.6 Sandboxing | `tsec_sandbox_destroy(&sec, sb_id2) == TSEC_OK` | Functional |
| 203 | L1441 | 1 sandbox left | 6.6 Sandboxing | `sec.sandbox_count == 1` | Functional |
| 204 | L1451 | sample OK | 6.7 Side-Channel Monitoring | `tsec_timing_sample(&sec, 100) == TSEC_OK` | Functional |
| 205 | L1456 | still secure | 6.7 Side-Channel Monitoring | `tsec_sidechannel_status(&sec) == TRIT_TRUE` | Functional |
| 206 | L1459 | emi alert 1 | 6.7 Side-Channel Monitoring | `tsec_emi_alert(&sec) == TSEC_OK` | Functional |
| 207 | L1463 | 2 alerts | 6.7 Side-Channel Monitoring | `sec.sidechannel.emi_alerts == 2` | Functional |
| 208 | L1467 | compromised | 6.7 Side-Channel Monitoring | `tsec_sidechannel_status(&sec) == TRIT_FALSE` | Functional |
| 209 | L1473 | fault detected | 6.7 Side-Channel Monitoring | `tsec_fault_detected(&sec) == TSEC_OK` | Functional |
| 210 | L1474 | fault → compromised | 6.7 Side-Channel Monitoring | `tsec_sidechannel_status(&sec) == TRIT_FALSE` | Functional |
| 211 | L1477 | escalation from fault | 6.7 Side-Channel Monitoring | `sec.total_escalations >= 1` | Functional |
| 212 | L1490 | count capped at max | 6.8 Log Buffer Wraparound | `sec.log_count == TSEC_MAX_LOG_ENTRIES` | Boundary |
| 213 | L1491 | total not capped | 6.8 Log Buffer Wraparound | `sec.log_total == TSEC_MAX_LOG_ENTRIES + 10` | Logic |
| 214 | L1501 | events > 0 | 6.9 Statistics | `total > 0` | Functional |

---

## Suite 24: LEGO Modular Architecture

**Source**: `tests/test_modular.c`
**Runtime Assertions**: 49
**Source-Level Entries**: 47
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

> **Note**: 2 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L58 | test_init | General | `function-level test` | Initialization |
| 2 | L64 | init failed | Framework Initializatio | `tmod_init(&fw) == TMOD_OK` | Negative/error |
| 3 | L67 | expected 0 modules | Framework Initializatio | `tmod_count(&fw) == 0` | Functional |
| 4 | L70 | expected TRIT_TRUE | Framework Initializatio | `fw.radix_guard.guard_status == TRIT_TRUE` | Functional |
| 5 | L73 | expected ERR_INIT | Framework Initializatio | `tmod_init(NULL) == TMOD_ERR_INIT` | Initialization |
| 6 | L76 | expected initialized=1 | Framework Initializatio | `fw.initialized == 1` | Initialization |
| 7 | L83 | test_registration | Framework Initializatio | `function-level test` | Functional |
| 8 | L91 | expected id 0 | Module Registratio | `id == 0` | Functional |
| 9 | L94 | expected 1 | Module Registratio | `tmod_count(&fw) == 1` | Functional |
| 10 | L98 | expected id 1 | Module Registratio | `id == 1` | Functional |
| 11 | L102 | expected id 2 | Module Registratio | `id == 2` | Functional |
| 12 | L105 | expected 3 | Module Registratio | `tmod_count(&fw) == 3` | Functional |
| 13 | L113 | not found or wrong purity | Module Registratio | `m != NULL && m->radix_purity == TMOD_RADIX_TERNARY` | Logic |
| 14 | L116 | expected NULL | Module Registratio | `tmod_find(&fw, "nonexistent") == NULL` | Negative/error |
| 15 | L127 | test_dependencies | Module Registratio | `function-level test` | Functional |
| 16 | L139 | expected satisfied | Dependency Management | `tmod_deps_satisfied(&fw, "core") == 1` | Functional |
| 17 | L143 | add dep failed | Dependency Management | `tmod_add_dependency(&fw, "net", "core") == TMOD_OK` | Negative/error |
| 18 | L146 | expected not satisfied | Dependency Management | `tmod_deps_satisfied(&fw, "net") == 0` | Logic |
| 19 | L150 | load core failed | Dependency Management | `tmod_load(&fw, "core") == TMOD_OK` | Negative/error |
| 20 | L153 | expected satisfied | Dependency Management | `tmod_deps_satisfied(&fw, "net") == 1` | Functional |
| 21 | L157 | add dep failed | Dependency Management | `tmod_add_dependency(&fw, "app", "net") == TMOD_OK` | Negative/error |
| 22 | L160 | expected not satisfied | Dependency Management | `tmod_deps_satisfied(&fw, "app") == 0` | Logic |
| 23 | L163 | load net failed | Dependency Management | `tmod_load(&fw, "net") == TMOD_OK` | Negative/error |
| 24 | L166 | expected satisfied | Dependency Management | `tmod_deps_satisfied(&fw, "app") == 1` | Functional |
| 25 | L169 | load app failed | Dependency Management | `tmod_load(&fw, "app") == TMOD_OK` | Negative/error |
| 26 | L180 | test_configs | Dependency Management | `function-level test` | Initialization |
| 27 | L193 | expected 5:8 | Drop-in Configuratio | `v != NULL && strcmp(v, "5:8") == 0` | Functional |
| 28 | L205 | expected 9:14 after override | Drop-in Configuratio | `v != NULL && strcmp(v, "9:14") == 0` | Functional |
| 29 | L212 | expected NULL | Drop-in Configuratio | `tmod_get_config(&fw, "tipc", "NoSuchKey") == NULL` | Negative/error |
| 30 | L219 | test_radix_guard | Drop-in Configuratio | `function-level test` | Functional |
| 31 | L230 | expected 0 violations | Radix Integrity Guard | `v == 0` | Functional |
| 32 | L233 | expected clean | Radix Integrity Guard | `fw.radix_guard.guard_status == TRIT_TRUE` | Functional |
| 33 | L236 | expected 2 cleared | Radix Integrity Guard | `fw.radix_guard.modules_cleared == 2` | Functional |
| 34 | L243 | expected 1 violation | Radix Integrity Guard | `v == 1` | Functional |
| 35 | L246 | expected impure | Radix Integrity Guard | `fw.radix_guard.guard_status == TRIT_FALSE` | Functional |
| 36 | L249 | strip failed | Radix Integrity Guard | `tmod_strip_binary_emu(&fw, "legacy_bin") == TMOD_OK` | Negative/error |
| 37 | L253 | expected 0 violations after strip | Radix Integrity Guard | `v == 0` | Functional |
| 38 | L256 | expected clean | Radix Integrity Guard | `fw.radix_guard.guard_status == TRIT_TRUE` | Functional |
| 39 | L259 | expected 3 scans | Radix Integrity Guard | `fw.radix_guard.scans_performed == 3` | Functional |
| 40 | L266 | test_lifecycle | Radix Integrity Guard | `function-level test` | Performance |
| 41 | L277 | expected dep error | Module Load / Unload Lifecycle | `tmod_load(&fw, "net") == TMOD_ERR_DEPENDENCY` | Negative/error |
| 42 | L281 | expected FAILED | Module Load / Unload Lifecycle | `m && m->state == TMOD_STATE_FAILED` | Negative/error |
| 43 | L284 | load core failed | Module Load / Unload Lifecycle | `tmod_load(&fw, "core") == TMOD_OK` | Negative/error |
| 44 | L288 | expected ACTIVE | Module Load / Unload Lifecycle | `m && m->state == TMOD_STATE_ACTIVE` | Functional |
| 45 | L291 | load net failed | Module Load / Unload Lifecycle | `tmod_load(&fw, "net") == TMOD_OK` | Negative/error |
| 46 | L294 | unload failed | Module Load / Unload Lifecycle | `tmod_unload(&fw, "core") == TMOD_OK` | Negative/error |
| 47 | L298 | expected UNLOADED | Module Load / Unload Lifecycle | `m && m->state == TMOD_STATE_UNLOADED` | Functional |

---

## Suite 25: Secure IPC

**Source**: `tests/test_ipc_secure.c`
**Runtime Assertions**: 40
**Source-Level Entries**: 38
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

> **Note**: 2 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L59 | test_init | General | `function-level test` | Initialization |
| 2 | L65 | init failed | Secure IPC Initializatio | `tipc_sec_init(&sec) == TIPC_SEC_OK` | Negative/error |
| 3 | L68 | expected 0 | Secure IPC Initializatio | `sec.socket_count == 0` | Functional |
| 4 | L71 | expected 0 | Secure IPC Initializatio | `sec.ns_count == 0` | Functional |
| 5 | L74 | expected 0 | Secure IPC Initializatio | `sec.cap_count == 0` | Functional |
| 6 | L77 | expected ERR_INIT | Secure IPC Initializatio | `tipc_sec_init(NULL) == TIPC_SEC_ERR_INIT` | Initialization |
| 7 | L84 | test_sockets | Secure IPC Initializatio | `function-level test` | Functional |
| 8 | L92 | expected socket id 0 | Ternary Socket Activatio | `sid == 0` | Functional |
| 9 | L95 | expected LISTENING | Ternary Socket Activatio | `sec.sockets[0].state == TSOCK_STATE_LISTENING` | Functional |
| 10 | L98 | expected UNKNOWN | Ternary Socket Activatio | `sec.sockets[0].activation_status == TRIT_UNKNOWN` | Functional |
| 11 | L101 | activate failed | Ternary Socket Activatio | `tipc_socket_activate(&sec, 0) == TIPC_SEC_OK` | Negative/error |
| 12 | L104 | expected ACTIVATED | Ternary Socket Activatio | `sec.sockets[0].state == TSOCK_STATE_ACTIVATED` | Functional |
| 13 | L107 | expected TRUE | Ternary Socket Activatio | `sec.sockets[0].activation_status == TRIT_TRUE` | Functional |
| 14 | L111 | expected 2 sockets | Ternary Socket Activatio | `sid == 1 && sec.socket_count == 2` | Functional |
| 15 | L122 | test_send_recv | Ternary Socket Activatio | `function-level test` | IPC |
| 16 | L138 | expected 5 trits sent | Socket Send / Recv with Capabilities | `sent == 5` | Functional |
| 17 | L141 | expected 1 unknown pause | Socket Send / Recv with Capabilities | `sec.unknown_pauses == 1` | Functional |
| 18 | L146 | expected 5 trits received | Socket Send / Recv with Capabilities | `recvd == 5` | Functional |
| 19 | L153 | expected empty buffer | Socket Send / Recv with Capabilities | `tipc_socket_recv(&sec, 0, out, 16) == 0` | Negative/error |
| 20 | L156 | expected 1 message | Socket Send / Recv with Capabilities | `sec.total_messages == 1` | IPC |
| 21 | L163 | test_namespaces | Socket Send / Recv with Capabilities | `function-level test` | Functional |
| 22 | L171 | expected ns id 0 | Namespace Isolatio | `ns_user == 0` | Functional |
| 23 | L175 | expected ns id 1 | Namespace Isolatio | `ns_full == 1` | Functional |
| 24 | L178 | expected 2 | Namespace Isolatio | `sec.ns_count == 2` | Functional |
| 25 | L181 | enter failed | Namespace Isolatio | `tipc_namespace_enter(&sec, ns_user) == TIPC_SEC_OK` | Negative/error |
| 26 | L184 | expected active | Namespace Isolatio | `sec.namespaces[ns_user].active == 1` | Functional |
| 27 | L187 | leave failed | Namespace Isolatio | `tipc_namespace_leave(&sec, ns_user) == TIPC_SEC_OK` | Negative/error |
| 28 | L190 | expected inactive | Namespace Isolatio | `sec.namespaces[ns_user].active == 0` | Functional |
| 29 | L201 | test_capabilities | Namespace Isolatio | `function-level test` | Access control |
| 30 | L212 | expected has cap | Trit Capabilities | `tipc_cap_check(&sec, 0, TCAP_IPC_SEND) == 1` | Access control |
| 31 | L215 | expected has cap | Trit Capabilities | `tipc_cap_check(&sec, 0, TCAP_IPC_LOCK) == 1` | Access control |
| 32 | L218 | expected no cap | Trit Capabilities | `tipc_cap_check(&sec, 0, TCAP_SYS_ADMIN) == 0` | Access control |
| 33 | L221 | expected no cap | Trit Capabilities | `tipc_cap_check(&sec, 1, TCAP_IPC_SEND) == 0` | Access control |
| 34 | L228 | expected has cap | Trit Capabilities | `tipc_cap_check(&sec, 1, TCAP_NET_RAW) == 1` | Access control |
| 35 | L235 | test_injection | Trit Capabilities | `function-level test` | Functional |
| 36 | L252 | expected 1 attempt | Injection Attack Detectio | `sec.inject_attempts == 1` | Functional |
| 37 | L255 | expected 1 blocked | Injection Attack Detectio | `sec.inject_blocked == 1` | Memory |
| 38 | L265 | expected 1 blocked total | Injection Attack Detectio | `tipc_inject_stats(&sec) == 1` | Memory |

---

## Suite 26: Time Synchronization

**Source**: `tests/test_time.c`
**Runtime Assertions**: 42
**Source-Level Entries**: 50
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L59 | test_init | General | `function-level test` | Initialization |
| 2 | L65 | init failed | Time Daemon Initializatio | `ttime_init(&ts) == TTIME_OK` | Negative/error |
| 3 | L68 | expected UNKNOWN | Time Daemon Initializatio | `ttime_get_status(&ts) == TRIT_UNKNOWN` | Functional |
| 4 | L71 | expected 0 | Time Daemon Initializatio | `ts.source_count == 0` | Functional |
| 5 | L74 | expected not valid | Time Daemon Initializatio | `ts.mram_record.valid == 0` | Logic |
| 6 | L77 | expected ERR_INIT | Time Daemon Initializatio | `ttime_init(NULL) == TTIME_ERR_INIT` | Initialization |
| 7 | L84 | test_sources | Time Daemon Initializatio | `function-level test` | Functional |
| 8 | L94 | expected source id 0 | Time Source Management | `id == 0` | Functional |
| 9 | L97 | expected HIGH | Time Source Management | `ts.sources[0].quality == TTIME_QUALITY_HIGH` | Functional |
| 10 | L100 | expected authenticated | Time Source Management | `ts.sources[0].authenticated == 1` | Functional |
| 11 | L104 | expected source id 1 | Time Source Management | `id == 1` | Functional |
| 12 | L107 | expected MEDIUM | Time Source Management | `ts.sources[1].quality == TTIME_QUALITY_MEDIUM` | Functional |
| 13 | L110 | expected not auth | Time Source Management | `ts.sources[1].authenticated == 0` | Logic |
| 14 | L113 | expected 2 | Time Source Management | `ts.source_count == 2` | Functional |
| 15 | L120 | test_sync | Time Source Management | `function-level test` | Functional |
| 16 | L137 | sync failed | Time Synchronizatio | `ttime_sync(&ts) == TTIME_OK` | Negative/error |
| 17 | L140 | expected TRUE | Time Synchronizatio | `ttime_get_status(&ts) == TRIT_TRUE` | Functional |
| 18 | L143 | expected 10500 | Time Synchronizatio | `ts.synced_time_us_x10 == 10500` | Functional |
| 19 | L146 | expected 1 | Time Synchronizatio | `ts.sync_count == 1` | Functional |
| 20 | L152 | expected ERR_NOTFOUND | Time Synchronizatio | `ttime_sync(&ts2) == TTIME_ERR_NOTFOUND` | Functional |
| 21 | L159 | test_skew | Time Synchronizatio | `function-level test` | Functional |
| 22 | L169 | expected 10 | Skew Detection & History | `skew == 10` | Functional |
| 23 | L172 | record failed | Skew Detection & History | `ttime_record_skew(&ts, 10) == TTIME_OK` | Negative/error |
| 24 | L175 | expected 1 | Skew Detection & History | `ts.skew.count == 1` | Functional |
| 25 | L178 | expected 10 | Skew Detection & History | `ts.skew.avg_skew_us_x10 == 10` | Functional |
| 26 | L185 | expected ERR_SKEW | Skew Detection & History | `ttime_check_skew(&ts) == TTIME_ERR_SKEW` | Functional |
| 27 | L188 | expected FALSE | Skew Detection & History | `ttime_get_status(&ts) == TRIT_FALSE` | Functional |
| 28 | L195 | test_mram | Skew Detection & History | `function-level test` | Functional |
| 29 | L202 | expected ERR_NOTFOUND | MRAM Persistent Timestamps | `ttime_mram_restore(&ts) == TTIME_ERR_NOTFOUND` | Functional |
| 30 | L205 | store failed | MRAM Persistent Timestamps | `ttime_mram_store(&ts, 99999) == TTIME_OK` | Negative/error |
| 31 | L208 | expected valid | MRAM Persistent Timestamps | `ts.mram_record.valid == 1` | Functional |
| 32 | L211 | expected 99999 | MRAM Persistent Timestamps | `ttime_mram_restore(&ts) == 99999` | Functional |
| 33 | L214 | expected 1 | MRAM Persistent Timestamps | `ts.mram_record.sequence_number == 1` | Functional |
| 34 | L221 | test_events | MRAM Persistent Timestamps | `function-level test` | Functional |
| 35 | L229 | expected event id 0 | Priority Event Queue | `id == 0` | Functional |
| 36 | L233 | expected event id 1 | Priority Event Queue | `id == 1` | Functional |
| 37 | L237 | expected event id 2 | Priority Event Queue | `id == 2` | Functional |
| 38 | L241 | expected event 0 (high priority) | Priority Event Queue | `dispatched == 0` | Scheduling |
| 39 | L245 | expected event 2 (medium priority) | Priority Event Queue | `dispatched == 2` | Scheduling |
| 40 | L249 | expected 1 missed (event 1 deadline=500) | Priority Event Queue | `missed == 1` | Functional |
| 41 | L256 | test_replay | Priority Event Queue | `function-level test` | Functional |
| 42 | L266 | expected OK | Replay Attack Detectio | `ttime_detect_replay(&ts, 2) == TTIME_OK` | Functional |
| 43 | L269 | expected REPLAY | Replay Attack Detectio | `ttime_detect_replay(&ts, 1) == TTIME_ERR_REPLAY` | Functional |
| 44 | L272 | expected REPLAY | Replay Attack Detectio | `ttime_detect_replay(&ts, 0) == TTIME_ERR_REPLAY` | Functional |
| 45 | L275 | expected 2 replay attempts | Replay Attack Detectio | `ts.replay_attempts == 2` | Functional |
| 46 | L282 | test_clock | Replay Attack Detectio | `function-level test` | Functional |
| 47 | L289 | expected 0 | Clock Management | `ts.local_time_us_x10 == 0` | Functional |
| 48 | L292 | advance failed | Clock Management | `ttime_clock_advance(&ts, 5000) == TTIME_OK` | Negative/error |
| 49 | L295 | expected 5000 | Clock Management | `ts.local_time_us_x10 == 5000` | Functional |
| 50 | L299 | expected 8000 | Clock Management | `ts.local_time_us_x10 == 8000` | Functional |

---

## Suite 27: System Hardening

**Source**: `tests/test_hardening.c`
**Runtime Assertions**: 55
**Source-Level Entries**: 38
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

> **Note**: 17 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L57 | test_init | General | `function-level test` | Initialization |
| 2 | L63 | init failed | Hardening Initializatio | `thard_init(&hs) == THARD_OK` | Negative/error |
| 3 | L66 | expected UNKNOWN | Hardening Initializatio | `hs.hardening_status == TRIT_UNKNOWN` | Functional |
| 4 | L69 | expected 0 | Hardening Initializatio | `hs.param_count == 0` | Functional |
| 5 | L72 | expected 0 | Hardening Initializatio | `hs.mount_count == 0` | Functional |
| 6 | L75 | expected ERR_INIT | Hardening Initializatio | `thard_init(NULL) == THARD_ERR_INIT` | Initialization |
| 7 | L82 | test_kparams | Hardening Initializatio | `function-level test` | Functional |
| 8 | L93 | expected 2 | Kernel Parameter Emulatio | `thard_get_kparam(&hs, TKPARAM_KPTR_RESTRICT) == 2` | Functional |
| 9 | L116 | expected 6 | Kernel Parameter Emulatio | `hs.param_count == 6` | Functional |
| 10 | L123 | expected 1 | Kernel Parameter Emulatio | `thard_get_kparam(&hs, TKPARAM_KPTR_RESTRICT) == 1` | Functional |
| 11 | L126 | expected -1 | Kernel Parameter Emulatio | `thard_get_kparam(&hs, 99) == -1` | Functional |
| 12 | L133 | test_mounts | Kernel Parameter Emulatio | `function-level test` | Functional |
| 13 | L152 | expected 3 | Restrictive Mount Options | `hs.mount_count == 3` | Functional |
| 14 | L179 | expected 3 violations | Restrictive Mount Options | `hs.mounts[0].violations == 3` | Functional |
| 15 | L186 | test_firewall | Restrictive Mount Options | `function-level test` | Functional |
| 16 | L205 | expected 3 | Ternary Firewall | `hs.fw_rule_count == 3` | Functional |
| 17 | L224 | expected 1 dropped | Ternary Firewall | `thard_fw_dropped(&hs) == 1` | Functional |
| 18 | L227 | expected 2 accepted | Ternary Firewall | `hs.fw_packets_accepted == 2` | Functional |
| 19 | L230 | expected 1 logged | Ternary Firewall | `hs.fw_packets_logged == 1` | Functional |
| 20 | L237 | test_audit | Ternary Firewall | `function-level test` | Functional |
| 21 | L244 | audit failed | SUID Audit & Vulnerability Sca | `thard_audit_module(&hs, 0, 0) == THARD_OK` | Negative/error |
| 22 | L247 | expected clean | SUID Audit & Vulnerability Sca | `hs.audit[0].status == TRIT_TRUE` | Functional |
| 23 | L250 | audit failed | SUID Audit & Vulnerability Sca | `thard_audit_module(&hs, 1, 1) == THARD_OK` | Negative/error |
| 24 | L253 | expected vulnerable | SUID Audit & Vulnerability Sca | `hs.audit[1].status == TRIT_FALSE` | Functional |
| 25 | L256 | expected CRIT | SUID Audit & Vulnerability Sca | `hs.audit[1].severity == TAUDIT_SEV_CRIT` | Functional |
| 26 | L259 | audit failed | SUID Audit & Vulnerability Sca | `thard_audit_module(&hs, 2, 0) == THARD_OK` | Negative/error |
| 27 | L262 | audit failed | SUID Audit & Vulnerability Sca | `thard_audit_module(&hs, 3, 1) == THARD_OK` | Negative/error |
| 28 | L265 | expected 2 | SUID Audit & Vulnerability Sca | `hs.suid_found == 2` | Functional |
| 29 | L268 | expected 2 vulns | SUID Audit & Vulnerability Sca | `thard_audit_scan(&hs) == 2` | Functional |
| 30 | L271 | expected 2 | SUID Audit & Vulnerability Sca | `hs.vulnerabilities == 2` | Functional |
| 31 | L278 | test_score | SUID Audit & Vulnerability Sca | `function-level test` | Functional |
| 32 | L285 | expected 0 | Hardening Score Computatio | `thard_compute_score(&hs) == 0` | Functional |
| 33 | L294 | expected 30 | Hardening Score Computatio | `score == 30` | Functional |
| 34 | L301 | expected 40 | Hardening Score Computatio | `score == 40` | Functional |
| 35 | L308 | expected 46 | Hardening Score Computatio | `score == 46` | Functional |
| 36 | L316 | expected 66 | Hardening Score Computatio | `score == 66` | Functional |
| 37 | L334 | expected 131 | Hardening Score Computatio | `score == 131` | Functional |
| 38 | L337 | expected TRUE | Hardening Score Computatio | `hs.hardening_status == TRIT_TRUE` | Functional |

---

## Suite 28: Sigma 9 Validation

**Source**: `tests/test_sigma9.c`
**Runtime Assertions**: 337
**Source-Level Entries**: 358
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L64 | test_tstab_init | Test Harness | `function-level test` | Initialization |
| 2 | L69 | expected 0 | Trit Stability: Initializatio | `tstab_init(&st) == 0` | Functional |
| 3 | L72 | expected 1 | Trit Stability: Initializatio | `st.initialized == 1` | Functional |
| 4 | L75 | expected 0 | Trit Stability: Initializatio | `st.total_trits_tested == 0` | Functional |
| 5 | L78 | expected 9999 | Trit Stability: Initializatio | `st.worst_snm_mv == 9999` | Functional |
| 6 | L81 | expected 1000000 | Trit Stability: Initializatio | `st.stability_ppm == 1000000` | Functional |
| 7 | L84 | expected -1 | Trit Stability: Initializatio | `tstab_init(NULL) == -1` | Functional |
| 8 | L87 | test_tstab_noise_config | Trit Stability: Initializatio | `function-level test` | Initialization |
| 9 | L97 | expected THERMAL | Trit Stability: Noise Configuratio | `st.noise_types == TSTAB_NOISE_THERMAL` | Functional |
| 10 | L100 | expected 10 | Trit Stability: Noise Configuratio | `st.noise_amplitude_mv == 10` | Functional |
| 11 | L103 | expected 42 | Trit Stability: Noise Configuratio | `st.rng_seed == 42` | Functional |
| 12 | L110 | expected 0x07 | Trit Stability: Noise Configuratio | `st.noise_types == TSTAB_NOISE_ALL` | Functional |
| 13 | L117 | test_tstab_pvt_sweep | Trit Stability: Noise Configuratio | `function-level test` | Functional |
| 14 | L123 | expected 27 | Trit Stability: PVT Sweep Generatio | `tstab_generate_pvt_sweep(&st) == 27` | Functional |
| 15 | L126 | expected 27 | Trit Stability: PVT Sweep Generatio | `st.pvt_config_count == 27` | Functional |
| 16 | L133 | expected 700 | Trit Stability: PVT Sweep Generatio | `st.pvt_configs[0].voltage_mv == 700` | Functional |
| 17 | L136 | expected -40000 | Trit Stability: PVT Sweep Generatio | `st.pvt_configs[0].temperature_mc == -40000` | Functional |
| 18 | L143 | expected 900 | Trit Stability: PVT Sweep Generatio | `st.pvt_configs[26].voltage_mv == 900` | Functional |
| 19 | L146 | expected 125000 | Trit Stability: PVT Sweep Generatio | `st.pvt_configs[26].temperature_mc == 125000` | Functional |
| 20 | L149 | test_tstab_single_pvt | Trit Stability: PVT Sweep Generatio | `function-level test` | Functional |
| 21 | L159 | expected 0 | Trit Stability: Single PVT Test | `tstab_test_trit_pvt(&st, TRIT_TRUE, &cfg, &res) == 0` | Functional |
| 22 | L162 | expected TRUE | Trit Stability: Single PVT Test | `res.output == TRIT_TRUE` | Functional |
| 23 | L165 | expected 0 | Trit Stability: Single PVT Test | `res.flipped == 0` | Functional |
| 24 | L168 | expected > 0 | Trit Stability: Single PVT Test | `res.snm_mv > 0` | Functional |
| 25 | L171 | expected 1 | Trit Stability: Single PVT Test | `st.total_trits_tested == 1` | Functional |
| 26 | L175 | expected UNKNOWN | Trit Stability: Single PVT Test | `res.output == TRIT_UNKNOWN` | Functional |
| 27 | L179 | expected FALSE | Trit Stability: Single PVT Test | `res.output == TRIT_FALSE` | Functional |
| 28 | L182 | test_tstab_full_sweep | Trit Stability: Single PVT Test | `function-level test` | Functional |
| 29 | L191 | expected >= 0 | Trit Stability: Full PVT Sweep | `flips >= 0` | Functional |
| 30 | L194 | expected 81 | Trit Stability: Full PVT Sweep | `st.total_trits_tested == 81` | Functional |
| 31 | L197 | expected 1 | Trit Stability: Full PVT Sweep | `st.pvt_sweep_done == 1` | Functional |
| 32 | L201 | expected > 0 | Trit Stability: Full PVT Sweep | `ppm > 0` | Functional |
| 33 | L205 | expected reasonable SNM | Trit Stability: Full PVT Sweep | `snm >= 0 && snm < 9999` | Functional |
| 34 | L208 | test_tstab_seu | Trit Stability: Full PVT Sweep | `function-level test` | Functional |
| 35 | L220 | expected >= 0 | Trit Stability: SEU (Cosmic Ray) Injectio | `flips >= 0` | Functional |
| 36 | L223 | expected >= 0 | Trit Stability: SEU (Cosmic Ray) Injectio | `st.flip_count >= 0` | Functional |
| 37 | L227 | expected >= 0 | Trit Stability: SEU (Cosmic Ray) Injectio | `recovered >= 0` | Functional |
| 38 | L234 | expected all match | Trit Stability: SEU (Cosmic Ray) Injectio | `match == 1` | Functional |
| 39 | L237 | test_tstab_metastable | Trit Stability: SEU (Cosmic Ray) Injectio | `function-level test` | Parsing |
| 40 | L247 | expected >= 2 near 200mV and 600mV | Trit Stability: Meta-Stable Detectio | `meta >= 2` | Logic |
| 41 | L250 | expected >= 2 | Trit Stability: Meta-Stable Detectio | `st.metastable_events >= 2` | Functional |
| 42 | L253 | expected -1 | Trit Stability: Meta-Stable Detectio | `tstab_detect_metastable(&st, NULL, 5) == -1` | Functional |
| 43 | L260 | test_tmvm_init | Trit Stability: Meta-Stable Detectio | `function-level test` | Initialization |
| 44 | L265 | expected 0 | TMVM: Initializatio | `tmvm_init(&st) == 0` | Functional |
| 45 | L268 | expected 1 | TMVM: Initializatio | `st.initialized == 1` | Functional |
| 46 | L271 | expected 0 | TMVM: Initializatio | `st.total_macs == 0` | Functional |
| 47 | L274 | expected -1 | TMVM: Initializatio | `tmvm_init(NULL) == -1` | Functional |
| 48 | L277 | test_tmvm_compressor | TMVM: Initializatio | `function-level test` | Encoding |
| 49 | L285 | expected carry=1 sum=0 | TMVM: (3;2) Compressor | `comp.carry == 1 && comp.sum == 0` | Arithmetic |
| 50 | L291 | expected carry=-1 sum=0 | TMVM: (3;2) Compressor | `comp.carry == -1 && comp.sum == 0` | Arithmetic |
| 51 | L297 | expected carry=0 sum=0 | TMVM: (3;2) Compressor | `comp.carry == 0 && comp.sum == 0` | Arithmetic |
| 52 | L303 | expected carry=1 sum=-1 | TMVM: (3;2) Compressor | `comp.carry == 1 && comp.sum == -1` | Arithmetic |
| 53 | L309 | expected carry=-1 sum=1 | TMVM: (3;2) Compressor | `comp.carry == -1 && comp.sum == 1` | Arithmetic |
| 54 | L312 | expected 1 | TMVM: (3;2) Compressor | `comp.stages_used == 1` | Functional |
| 55 | L315 | test_tmvm_dot_sparse | TMVM: (3;2) Compressor | `function-level test` | Parsing |
| 56 | L324 | expected -1 | TMVM: Sparse Dot Product | `dot == -1` | Functional |
| 57 | L327 | expected 2 | TMVM: Sparse Dot Product | `skips == 2` | Functional |
| 58 | L333 | expected 0 and 4 skips | TMVM: Sparse Dot Product | `dot == 0 && skips == 4` | Logic |
| 59 | L339 | expected 3 | TMVM: Sparse Dot Product | `dot == 3` | Functional |
| 60 | L342 | test_tmvm_matvec | TMVM: Sparse Dot Product | `function-level test` | Functional |
| 61 | L355 | expected 0 | TMVM: Matrix-Vector Multiply | `tmvm_load_matrix(&st, mat, 2, 3) == 0` | Functional |
| 62 | L358 | expected 0 | TMVM: Matrix-Vector Multiply | `tmvm_load_vector(&st, vec, 3) == 0` | Functional |
| 63 | L361 | expected 0 | TMVM: Matrix-Vector Multiply | `tmvm_execute(&st) == 0` | Functional |
| 64 | L365 | expected 1 | TMVM: Matrix-Vector Multiply | `st.result[0] == 1` | Functional |
| 65 | L369 | expected -1 | TMVM: Matrix-Vector Multiply | `st.result[1] == -1` | Functional |
| 66 | L372 | expected 2 | TMVM: Matrix-Vector Multiply | `st.result_len == 2` | Functional |
| 67 | L375 | expected > 0 | TMVM: Matrix-Vector Multiply | `st.sparse_skips > 0` | Functional |
| 68 | L378 | expected > 0 | TMVM: Matrix-Vector Multiply | `tmvm_get_pdp_gain(&st) > 0` | Functional |
| 69 | L381 | expected > 0 | TMVM: Matrix-Vector Multiply | `tmvm_get_sparsity(&st) > 0` | Functional |
| 70 | L384 | test_tmvm_energy | TMVM: Matrix-Vector Multiply | `function-level test` | Functional |
| 71 | L396 | expected > 0 | TMVM: Energy Model | `st.energy_aj > 0` | Functional |
| 72 | L399 | expected binary > ternary | TMVM: Energy Model | `st.energy_binary_aj > st.energy_aj` | Functional |
| 73 | L402 | expected > 50% | TMVM: Energy Model | `st.pdp_gain_pct > 50` | Functional |
| 74 | L406 | expected -1 | TMVM: Energy Model | `tmvm_load_vector(&st, bad_vec, 3) == -1` | Functional |
| 75 | L413 | test_ecs_init | TMVM: Energy Model | `function-level test` | Initialization |
| 76 | L418 | expected 0 | ECS Gauge-Block: Initializatio | `ecs_init(&st) == 0` | Functional |
| 77 | L421 | expected TRUE | ECS Gauge-Block: Initializatio | `ecs_get_health(&st) == TRIT_TRUE` | Functional |
| 78 | L424 | expected 0 | ECS Gauge-Block: Initializatio | `st.monitor_count == 0` | Functional |
| 79 | L427 | expected 0 | ECS Gauge-Block: Initializatio | `ecs_audit_count(&st) == 0` | Functional |
| 80 | L430 | expected -1 | ECS Gauge-Block: Initializatio | `ecs_init(NULL) == -1` | Functional |
| 81 | L433 | test_ecs_channel_register | ECS Gauge-Block: Initializatio | `function-level test` | IPC |
| 82 | L440 | expected 0 | ECS Gauge-Block: Channel Registratio | `ch0 == 0` | Functional |
| 83 | L444 | expected 1 | ECS Gauge-Block: Channel Registratio | `ch1 == 1` | Functional |
| 84 | L448 | expected 2 | ECS Gauge-Block: Channel Registratio | `ch2 == 2` | Functional |
| 85 | L451 | expected 3 | ECS Gauge-Block: Channel Registratio | `st.monitor_count == 3` | Functional |
| 86 | L454 | expected TRACKING | ECS Gauge-Block: Channel Registratio | `st.monitors[0].status == ECS_MON_TRACKING` | Functional |
| 87 | L457 | expected TRUE | ECS Gauge-Block: Channel Registratio | `st.monitors[0].reference == TRIT_TRUE` | Functional |
| 88 | L460 | test_ecs_healthy_tick | ECS Gauge-Block: Channel Registratio | `function-level test` | Functional |
| 89 | L468 | expected 0 | ECS Gauge-Block: Healthy Tick | `ecs_tick(&st) == 0` | Functional |
| 90 | L471 | expected TRUE | ECS Gauge-Block: Healthy Tick | `ecs_get_health(&st) == TRIT_TRUE` | Functional |
| 91 | L474 | expected 0 | ECS Gauge-Block: Healthy Tick | `ecs_audit_count(&st) == 0` | Functional |
| 92 | L477 | test_ecs_drift_detection | ECS Gauge-Block: Healthy Tick | `function-level test` | Functional |
| 93 | L485 | expected 0 | ECS Gauge-Block: Drift Detectio | `ecs_update_reading(&st, ch, 770) == 0` | Functional |
| 94 | L489 | expected >= 1 audit entry | ECS Gauge-Block: Drift Detectio | `ecs_audit_count(&st) >= 1` | Functional |
| 95 | L492 | expected UNKNOWN | ECS Gauge-Block: Drift Detectio | `ecs_get_health(&st) == TRIT_UNKNOWN` | Functional |
| 96 | L495 | test_ecs_flip_detection | ECS Gauge-Block: Drift Detectio | `function-level test` | Functional |
| 97 | L506 | expected >= 1 | ECS Gauge-Block: Trit Flip Detectio | `needs >= 1` | Functional |
| 98 | L509 | expected FALSE | ECS Gauge-Block: Trit Flip Detectio | `ecs_get_health(&st) == TRIT_FALSE` | Functional |
| 99 | L512 | expected >= 1 | ECS Gauge-Block: Trit Flip Detectio | `st.total_flips >= 1` | Functional |
| 100 | L517 | expected CRITICAL | ECS Gauge-Block: Trit Flip Detectio | `entry.severity == ECS_SEV_CRITICAL` | Functional |
| 101 | L520 | test_ecs_irq_recovery | ECS Gauge-Block: Trit Flip Detectio | `function-level test` | Functional |
| 102 | L530 | expected >= 1 | ECS Gauge-Block: IRQ Emergency Recalibratio | `corrected >= 1` | Functional |
| 103 | L533 | expected TRUE | ECS Gauge-Block: IRQ Emergency Recalibratio | `ecs_get_health(&st) == TRIT_TRUE` | Functional |
| 104 | L536 | expected >= 1 | ECS Gauge-Block: IRQ Emergency Recalibratio | `st.total_recovered >= 1` | Functional |
| 105 | L539 | expected TRACKING | ECS Gauge-Block: IRQ Emergency Recalibratio | `st.monitors[ch].status == ECS_MON_TRACKING` | Functional |
| 106 | L542 | test_ecs_hesitation | ECS Gauge-Block: IRQ Emergency Recalibratio | `function-level test` | Functional |
| 107 | L559 | expected >= 1 | ECS Gauge-Block: Hesitation (Unknown-State Pause) | `ecs_get_hesitation_count(&st) >= 1` | Functional |
| 108 | L562 | expected HESITATING | ECS Gauge-Block: Hesitation (Unknown-State Pause) | `st.monitors[ch].status == ECS_MON_HESITATING` | Functional |
| 109 | L565 | test_ecs_audit_log | ECS Gauge-Block: Hesitation (Unknown-State Pause) | `function-level test` | Functional |
| 110 | L574 | expected > 0 | ECS Gauge-Block: T-Audit Log | `ecs_audit_count(&st) > 0` | Functional |
| 111 | L578 | expected 0 | ECS Gauge-Block: T-Audit Log | `ecs_audit_get(&st, 0, &entry) == 0` | Functional |
| 112 | L581 | expected channel 0 | ECS Gauge-Block: T-Audit Log | `entry.channel == ch` | IPC |
| 113 | L584 | expected > 0 | ECS Gauge-Block: T-Audit Log | `entry.tick > 0` | Functional |
| 114 | L587 | expected -1 | ECS Gauge-Block: T-Audit Log | `ecs_audit_get(&st, 999, &entry) == -1` | Functional |
| 115 | L594 | test_tcamn_init | ECS Gauge-Block: T-Audit Log | `function-level test` | Initialization |
| 116 | L599 | expected 0 | TCAM Net: Initializatio | `tcamn_init(&st) == 0` | Functional |
| 117 | L602 | expected 0 | TCAM Net: Initializatio | `st.entry_count == 0` | Functional |
| 118 | L605 | expected 0 | TCAM Net: Initializatio | `st.total_searches == 0` | Functional |
| 119 | L608 | expected -1 | TCAM Net: Initializatio | `tcamn_init(NULL) == -1` | Functional |
| 120 | L611 | test_tcamn_add_search | TCAM Net: Initializatio | `function-level test` | Arithmetic |
| 121 | L624 | expected 0 | TCAM Net: Add Entry & Exact Search | `idx == 0` | Functional |
| 122 | L627 | expected 1 | TCAM Net: Add Entry & Exact Search | `st.entry_count == 1` | Functional |
| 123 | L636 | expected match | TCAM Net: Add Entry & Exact Search | `result.matched == 1` | Functional |
| 124 | L639 | expected EXACT | TCAM Net: Add Entry & Exact Search | `result.match_type == TCAMN_MATCH_EXACT` | Functional |
| 125 | L642 | expected FORWARD | TCAM Net: Add Entry & Exact Search | `result.action == TCAMN_ACT_FORWARD` | Functional |
| 126 | L645 | expected 42 | TCAM Net: Add Entry & Exact Search | `result.action_data == 42` | Functional |
| 127 | L648 | test_tcamn_wildcard | TCAM Net: Add Entry & Exact Search | `function-level test` | Functional |
| 128 | L668 | expected match | TCAM Net: Wildcard Search | `result.matched == 1` | Functional |
| 129 | L671 | expected WILDCARD | TCAM Net: Wildcard Search | `result.match_type == TCAMN_MATCH_WILDCARD` | Functional |
| 130 | L677 | expected no match | TCAM Net: Wildcard Search | `result.matched == 0` | Functional |
| 131 | L680 | test_tcamn_priority | TCAM Net: Wildcard Search | `function-level test` | Scheduling |
| 132 | L701 | expected FORWARD (prio 5) | TCAM Net: Priority-Ordered Search | `result.action == TCAMN_ACT_FORWARD` | Functional |
| 133 | L704 | expected 2 | TCAM Net: Priority-Ordered Search | `result.action_data == 2` | Functional |
| 134 | L707 | test_tcamn_similarity | TCAM Net: Priority-Ordered Search | `function-level test` | Functional |
| 135 | L728 | expected 3 | TCAM Net: Similarity Search | `n == 3` | Functional |
| 136 | L731 | expected 0 | TCAM Net: Similarity Search | `results[0].trit_distance == 0` | Functional |
| 137 | L734 | expected 1 | TCAM Net: Similarity Search | `results[1].trit_distance == 1` | Functional |
| 138 | L737 | expected 2 | TCAM Net: Similarity Search | `results[2].trit_distance == 2` | Functional |
| 139 | L740 | test_tcamn_trit_distance | TCAM Net: Similarity Search | `function-level test` | Functional |
| 140 | L746 | expected 2 | TCAM Net: Trit Distance | `tcamn_trit_distance(a, b, 4) == 2` | Functional |
| 141 | L750 | expected 0 | TCAM Net: Trit Distance | `tcamn_trit_distance(c, c, 4) == 0` | Functional |
| 142 | L755 | expected 0 (Unknown ignored) | TCAM Net: Trit Distance | `tcamn_trit_distance(a, d, 4) == 0` | Logic |
| 143 | L758 | test_tcamn_energy | TCAM Net: Trit Distance | `function-level test` | Functional |
| 144 | L773 | expected 2 | TCAM Net: Energy & Statistics | `st.total_searches == 2` | Functional |
| 145 | L776 | expected 2 | TCAM Net: Energy & Statistics | `st.total_hits == 2` | Functional |
| 146 | L779 | expected 100 | TCAM Net: Energy & Statistics | `tcamn_get_hit_rate(&st) == 100` | Functional |
| 147 | L782 | expected 100 | TCAM Net: Energy & Statistics | `tcamn_get_energy(&st) == 100` | Functional |
| 148 | L785 | expected 800ps | TCAM Net: Energy & Statistics | `result.latency_ps == TCAMN_SEARCH_LATENCY_PS` | Functional |
| 149 | L788 | test_tcamn_delete | TCAM Net: Energy & Statistics | `function-level test` | Functional |
| 150 | L800 | expected 0 | TCAM Net: Entry Deletio | `tcamn_delete_entry(&st, 0) == 0` | Functional |
| 151 | L806 | expected no match | TCAM Net: Entry Deletio | `result.matched == 0` | Functional |
| 152 | L813 | test_radix_guard | TCAM Net: Entry Deletio | `function-level test` | Functional |
| 153 | L825 | expected 1 | Radix Integrity Guard: Zero-Binary Directive | `violations == 1` | Functional |
| 154 | L828 | expected FALSE | Radix Integrity Guard: Zero-Binary Directive | `fw.radix_guard.guard_status == TRIT_FALSE` | Functional |
| 155 | L831 | expected 0 | Radix Integrity Guard: Zero-Binary Directive | `tmod_strip_binary_emu(&fw, "legacy") == 0` | Functional |
| 156 | L835 | expected 0 | Radix Integrity Guard: Zero-Binary Directive | `violations == 0` | Functional |
| 157 | L838 | expected TRUE | Radix Integrity Guard: Zero-Binary Directive | `fw.radix_guard.guard_status == TRIT_TRUE` | Functional |
| 158 | L841 | test_radix_guard_mixed | Radix Integrity Guard: Zero-Binary Directive | `function-level test` | Functional |
| 159 | L852 | expected 2 | Radix Integrity Guard: Mixed Radix Detectio | `tmod_radix_scan(&fw) == 2` | Functional |
| 160 | L855 | expected 2 | Radix Integrity Guard: Mixed Radix Detectio | `fw.radix_guard.modules_cleared == 2` | Functional |
| 161 | L858 | expected 1 | Radix Integrity Guard: Mixed Radix Detectio | `fw.radix_guard.scans_performed == 1` | Functional |
| 162 | L862 | strip completed | Radix Integrity Guard: Mixed Radix Detectio | `1` | Functional |
| 163 | L865 | expected 1 | Radix Integrity Guard: Mixed Radix Detectio | `tmod_radix_scan(&fw) == 1` | Functional |
| 164 | L868 | test_radix_guard_enforcement | Radix Integrity Guard: Mixed Radix Detectio | `function-level test` | Functional |
| 165 | L879 | expected TRUE | Radix Integrity Guard: Load Refusal | `fw.radix_guard.guard_status == TRIT_TRUE` | Functional |
| 166 | L887 | expected FALSE after binary | Radix Integrity Guard: Load Refusal | `fw.radix_guard.guard_status == TRIT_FALSE` | Functional |
| 167 | L892 | expected TRUE after strip | Radix Integrity Guard: Load Refusal | `fw.radix_guard.guard_status == TRIT_TRUE` | Functional |
| 168 | L895 | expected 3 | Radix Integrity Guard: Load Refusal | `fw.radix_guard.scans_performed == 3` | Functional |
| 169 | L898 | test_radix_guard_all_ternary | Radix Integrity Guard: Load Refusal | `function-level test` | Functional |
| 170 | L910 | expected 0 | Radix Integrity Guard: Full Ternary Compliance | `tmod_radix_scan(&fw) == 0` | Functional |
| 171 | L913 | expected 8 | Radix Integrity Guard: Full Ternary Compliance | `fw.radix_guard.modules_cleared == 8` | Functional |
| 172 | L916 | expected TRUE | Radix Integrity Guard: Full Ternary Compliance | `fw.radix_guard.guard_status == TRIT_TRUE` | Functional |
| 173 | L923 | test_side_channel | Radix Integrity Guard: Full Ternary Compliance | `function-level test` | IPC |
| 174 | L941 | expected constant | Side-Channel: Timing Consistency | `consistent == 1` | Functional |
| 175 | L951 | expected constant | Side-Channel: Timing Consistency | `consistent == 1` | Functional |
| 176 | L959 | expected constant | Side-Channel: Timing Consistency | `consistent == 1` | Functional |
| 177 | L962 | test_side_channel_didt | Side-Channel: Timing Consistency | `function-level test` | IPC |
| 178 | L989 | expected 0 for self-transitions | Side-Channel: dI/dt Spike Emulatio | `all_zero_self == 1` | Logic |
| 179 | L996 | expected 2 for -1↔+1 | Side-Channel: dI/dt Spike Emulatio | `transitions[0][2] == 2` | Logic |
| 180 | L1007 | expected sum 8 for 3×3 transitions | Side-Channel: dI/dt Spike Emulatio | `ternary_sum == 8` | Arithmetic |
| 181 | L1010 | test_side_channel_unknown_masking | Side-Channel: dI/dt Spike Emulatio | `function-level test` | IPC |
| 182 | L1022 | AND(TRUE, UNK) = UNK | Side-Channel: Unknown State as Side-Channel Blocker | `r == TRIT_UNKNOWN` | Functional |
| 183 | L1029 | OR(FALSE, UNK) = UNK — no leakage | Side-Channel: Unknown State as Side-Channel Blocker | `r == TRIT_UNKNOWN` | Functional |
| 184 | L1032 | expected UNK | Side-Channel: Unknown State as Side-Channel Blocker | `trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 185 | L1037 | expected UNK | Side-Channel: Unknown State as Side-Channel Blocker | `imp == TRIT_UNKNOWN` | Functional |
| 186 | L1042 | expected UNK | Side-Channel: Unknown State as Side-Channel Blocker | `eq == TRIT_UNKNOWN` | Functional |
| 187 | L1049 | test_epistemic_k3 | Side-Channel: Unknown State as Side-Channel Blocker | `function-level test` | Functional |
| 188 | L1054 | expected T | Epistemic K3: Kleene Truth Table Verificatio | `trit_and(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE` | Functional |
| 189 | L1057 | expected U | Epistemic K3: Kleene Truth Table Verificatio | `trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 190 | L1060 | expected F | Epistemic K3: Kleene Truth Table Verificatio | `trit_and(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE` | Functional |
| 191 | L1063 | expected U | Epistemic K3: Kleene Truth Table Verificatio | `trit_and(TRIT_UNKNOWN, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 192 | L1066 | expected F | Epistemic K3: Kleene Truth Table Verificatio | `trit_and(TRIT_FALSE, TRIT_TRUE) == TRIT_FALSE` | Functional |
| 193 | L1070 | expected F | Epistemic K3: Kleene Truth Table Verificatio | `trit_or(TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE` | Functional |
| 194 | L1073 | expected U | Epistemic K3: Kleene Truth Table Verificatio | `trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 195 | L1076 | expected T | Epistemic K3: Kleene Truth Table Verificatio | `trit_or(TRIT_TRUE, TRIT_FALSE) == TRIT_TRUE` | Functional |
| 196 | L1090 | all 9 combinations satisfy De Morgan | Epistemic K3: Kleene Truth Table Verificatio | `dm_ok == 1` | Functional |
| 197 | L1094 | test_epistemic_involution | Epistemic K3: Kleene Truth Table Verificatio | `function-level test` | Functional |
| 198 | L1103 | expected involution holds | Epistemic K3: Involution & Absorptio | `ok == 1` | Functional |
| 199 | L1115 | expected absorption holds for all 9 combos | Epistemic K3: Involution & Absorptio | `ok == 1` | Logic |
| 200 | L1128 | test_epistemic_confidence | Epistemic K3: Involution & Absorptio | `function-level test` | Functional |
| 201 | L1133 | expected 1 | Epistemic K3: Confidence & Definiteness | `trit_is_definite(TRIT_TRUE) == 1` | Functional |
| 202 | L1136 | expected 1 | Epistemic K3: Confidence & Definiteness | `trit_is_definite(TRIT_FALSE) == 1` | Functional |
| 203 | L1139 | expected 0 | Epistemic K3: Confidence & Definiteness | `trit_is_definite(TRIT_UNKNOWN) == 0` | Functional |
| 204 | L1150 | expected 5 definite trits | Epistemic K3: Confidence & Definiteness | `definite_count == 5` | Initialization |
| 205 | L1154 | expected 1 | Epistemic K3: Confidence & Definiteness | `trit_to_bool_safe(TRIT_TRUE) == 1` | Functional |
| 206 | L1157 | expected 0 | Epistemic K3: Confidence & Definiteness | `trit_to_bool_safe(TRIT_UNKNOWN) == 0` | Functional |
| 207 | L1160 | expected 0 | Epistemic K3: Confidence & Definiteness | `trit_to_bool_safe(TRIT_FALSE) == 0` | Functional |
| 208 | L1163 | test_epistemic_hesitation_reactor | Epistemic K3: Confidence & Definiteness | `function-level test` | Functional |
| 209 | L1185 | expected 1 pause | Epistemic K3: Hesitation Reactor (Pause on Unknown) | `pauses == 1` | Functional |
| 210 | L1188 | expected 4 decisions | Epistemic K3: Hesitation Reactor (Pause on Unknown) | `decisions == 4` | Functional |
| 211 | L1196 | expected UNKNOWN after chain | Epistemic K3: Hesitation Reactor (Pause on Unknown) | `chain == TRIT_UNKNOWN` | Functional |
| 212 | L1201 | expected FALSE overrides UNKNOWN | Epistemic K3: Hesitation Reactor (Pause on Unknown) | `chain == TRIT_FALSE` | Functional |
| 213 | L1208 | test_guardian_trit_checksum | Epistemic K3: Hesitation Reactor (Pause on Unknown) | `function-level test` | Arithmetic |
| 214 | L1226 | expected TRUE | Guardian Trit: Checksum Computatio | `expected_guardian == TRIT_TRUE` | Functional |
| 215 | L1236 | expected UNKNOWN | Guardian Trit: Checksum Computatio | `(trit)sum == TRIT_UNKNOWN` | Functional |
| 216 | L1246 | expected UNKNOWN for balanced | Guardian Trit: Checksum Computatio | `(trit)sum == TRIT_UNKNOWN` | Logic |
| 217 | L1249 | test_guardian_trit_tamper | Guardian Trit: Checksum Computatio | `function-level test` | Functional |
| 218 | L1263 | expected UNKNOWN for {1,1,1} | Guardian Trit: Tamper Detectio | `g_before == TRIT_UNKNOWN` | Logic |
| 219 | L1274 | expected guardian changed | Guardian Trit: Tamper Detectio | `g_after != g_before` | Functional |
| 220 | L1277 | expected TRUE for {-1,1,1} | Guardian Trit: Tamper Detectio | `g_after == TRIT_TRUE` | Logic |
| 221 | L1280 | test_guardian_drift_monitor | Guardian Trit: Tamper Detectio | `function-level test` | Functional |
| 222 | L1308 | expected initial guardian = 0 | Guardian Trit: Drift Monitor | `guardian_history[0] == 0` | Initialization |
| 223 | L1317 | expected >= 0 changes | Guardian Trit: Drift Monitor | `changes >= 0` | Functional |
| 224 | L1330 | expected majority > 0 | Guardian Trit: Drift Monitor | `counts[majority_idx] > 0` | Consensus |
| 225 | L1333 | test_guardian_packed_integrity | Guardian Trit: Drift Monitor | `function-level test` | Encoding |
| 226 | L1351 | expected 0x01 | Guardian Trit: Packed Register Integrity | `trit_pack(TRIT_TRUE) == 0x01` | Functional |
| 227 | L1354 | expected 0x00 | Guardian Trit: Packed Register Integrity | `trit_pack(TRIT_UNKNOWN) == 0x00` | Functional |
| 228 | L1357 | expected 0x02 | Guardian Trit: Packed Register Integrity | `trit_pack(TRIT_FALSE) == 0x02` | Functional |
| 229 | L1365 | test_rns_init_basic | Guardian Trit: Packed Register Integrity | `function-level test` | Initialization |
| 230 | L1370 | expected 0 | RNS: Initialization & CRT Constants | `trit_rns_init(&ctx) == 0` | Functional |
| 231 | L1373 | expected 3 | RNS: Initialization & CRT Constants | `ctx.count == 3` | Functional |
| 232 | L1376 | expected 105 | RNS: Initialization & CRT Constants | `ctx.M == 105` | Functional |
| 233 | L1379 | expected 35 | RNS: Initialization & CRT Constants | `ctx.Mi[0] == 35` | Functional |
| 234 | L1382 | expected 21 | RNS: Initialization & CRT Constants | `ctx.Mi[1] == 21` | Functional |
| 235 | L1385 | expected 15 | RNS: Initialization & CRT Constants | `ctx.Mi[2] == 15` | Functional |
| 236 | L1388 | expected 2 | RNS: Initialization & CRT Constants | `ctx.Mi_inv[0] == 2` | Functional |
| 237 | L1391 | expected 1 | RNS: Initialization & CRT Constants | `ctx.Mi_inv[1] == 1` | Functional |
| 238 | L1394 | expected 1 | RNS: Initialization & CRT Constants | `ctx.Mi_inv[2] == 1` | Functional |
| 239 | L1397 | expected -1 | RNS: Initialization & CRT Constants | `trit_rns_init(NULL) == -1` | Functional |
| 240 | L1400 | test_rns_forward_inverse | RNS: Initialization & CRT Constants | `function-level test` | Functional |
| 241 | L1412 | expected 0 | RNS: trit2_reg32 → RNS → CRT Roundtrip | `trit2_decode(trit2_reg32_get(&out_z, 0)) == 0` | Functional |
| 242 | L1422 | expected +1 | RNS: trit2_reg32 → RNS → CRT Roundtrip | `trit2_decode(trit2_reg32_get(&out1, 0)) == 1` | Functional |
| 243 | L1432 | expected -1 | RNS: trit2_reg32 → RNS → CRT Roundtrip | `trit2_decode(trit2_reg32_get(&outn1, 0)) == -1` | Functional |
| 244 | L1475 | test_rns_arithmetic | RNS: trit2_reg32 → RNS → CRT Roundtrip | `function-level test` | Arithmetic |
| 245 | L1518 | expected zero | RNS: Carry-Free Arithmetic (output-param API) | `rns_is_zero(&zero, &ctx)` | Functional |
| 246 | L1521 | expected non-zero | RNS: Carry-Free Arithmetic (output-param API) | `!rns_is_zero(&a, &ctx)` | Functional |
| 247 | L1524 | test_rns_mrc_crt_agree | RNS: Carry-Free Arithmetic (output-param API) | `function-level test` | Functional |
| 248 | L1535 | all 105 residue tuples pass validation | RNS: Validate All 105 Residue Tuples | `ok == 1` | Functional |
| 249 | L1538 | test_rns_montgomery | RNS: Validate All 105 Residue Tuples | `function-level test` | Functional |
| 250 | L1571 | expected 0 | RNS: Montgomery Per-Channel REDC | `mn.residues[0] == 0` | Functional |
| 251 | L1589 | extended channel REDC in range | RNS: Montgomery Per-Channel REDC | `em.residues[3] < 11` | Boundary |
| 252 | L1599 | test_rns_from_trits | RNS: Montgomery Per-Channel REDC | `function-level test` | Functional |
| 253 | L1638 | expected zero | RNS: Trit2-to-RNS Conversion & Extensio | `rns_is_zero(&rz, &ctx)` | Functional |
| 254 | L1642 | expected success and M=1155 | RNS: Trit2-to-RNS Conversion & Extensio | `ext_ok` | Logic |
| 255 | L1647 | expected -1 | RNS: Trit2-to-RNS Conversion & Extensio | `rns_extend_moduli(&ctx2, 6) == -1` | Functional |
| 256 | L1653 | expected valid | RNS: Trit2-to-RNS Conversion & Extensio | `rns_validate(&v42, &v_ctx) == 0` | Functional |
| 257 | L1657 | expected invalid | RNS: Trit2-to-RNS Conversion & Extensio | `rns_validate(&vbad, &v_ctx) == -1` | Negative/error |
| 258 | L1678 | expected zero | RNS: Trit2-to-RNS Conversion & Extensio | `rns_is_zero(&z33, &v_ctx)` | Functional |
| 259 | L1702 | test_resonance_basic | RNS: Trit2-to-RNS Conversion & Extensio | `function-level test` | Functional |
| 260 | L1711 | expected 1000 | Resonance: Ternary q = τ sin(t) + cos(t) Convergence | `(int)(q * 1000) == 1000` | Functional |
| 261 | L1716 | expected 1000 | Resonance: Ternary q = τ sin(t) + cos(t) Convergence | `(int)(q * 1000) == 1000` | Functional |
| 262 | L1721 | expected ≈-1000 | Resonance: Ternary q = τ sin(t) + cos(t) Convergence | `(int)(q * 1000) <= -990` | Functional |
| 263 | L1736 | expected avg=1.0 at t=0 | Resonance: Ternary q = τ sin(t) + cos(t) Convergence | `(int)(avg * 1000) == 1000` | Functional |
| 264 | L1739 | test_resonance_period | Resonance: Ternary q = τ sin(t) + cos(t) Convergence | `function-level test` | Functional |
| 265 | L1753 | expected 1000 | Resonance: Period and Phase Analysis | `(int)(A * 1000) == 1000` | Functional |
| 266 | L1765 | expected q(0) ≈ q(2π) | Resonance: Period and Phase Analysis | `diff < 5` | Functional |
| 267 | L1771 | expected ≈0 | Resonance: Period and Phase Analysis | `(int)fabs(qzero * 1000) < 5` | Functional |
| 268 | L1785 | test_resonance_divergence | Resonance: Period and Phase Analysis | `function-level test` | Arithmetic |
| 269 | L1801 | expected growth | Resonance: Divergence Detection in Ternary Streams | `accumulated[1] > accumulated[0]` | Functional |
| 270 | L1804 | expected > 3.0 | Resonance: Divergence Detection in Ternary Streams | `accumulated[4] > 3.0` | Functional |
| 271 | L1816 | expected no false divergence with correct τ | Resonance: Divergence Detection in Ternary Streams | `diverged == 0` | Arithmetic |
| 272 | L1832 | test_resonance_ternary_advantage | Resonance: Divergence Detection in Ternary Streams | `function-level test` | Functional |
| 273 | L1856 | ternary should have wider dynamic range | Resonance: Ternary vs Binary Compariso | `ter_max >= bin_max` | Boundary |
| 274 | L1859 | expected ≈√2 | Resonance: Ternary vs Binary Compariso | `(int)(ter_max * 1000) >= 1410` | Functional |
| 275 | L1878 | expected 3 distinct values | Resonance: Ternary vs Binary Compariso | `all_distinct == 1` | Hardware/ALU |
| 276 | L1885 | test_em_ndr_transitions | Resonance: Ternary vs Binary Compariso | `function-level test` | Functional |
| 277 | L1915 | 0→1:1 + 1→0:1 | EM Side-Channel: NDR Transition Models | `binary_transitions == 2` | Functional |
| 278 | L1918 | expected 12 | EM Side-Channel: NDR Transition Models | `ternary_transitions == 12` | Functional |
| 279 | L1923 | expected 133 | EM Side-Channel: NDR Transition Models | `avg_ter_x100 == 133` | Functional |
| 280 | L1927 | expected 50 | EM Side-Channel: NDR Transition Models | `avg_bin_x100 == 50` | Functional |
| 281 | L1937 | test_em_ndr_spike_profile | EM Side-Channel: NDR Transition Models | `function-level test` | Functional |
| 282 | L1959 | expected 0 for self-transitions | EM Side-Channel: dI/dt Spike Profile per IEDM | `all_zero == 1` | Logic |
| 283 | L1966 | expected 2 for -1→+1 | EM Side-Channel: dI/dt Spike Profile per IEDM | `spike_profile[0][2] == 2` | Logic |
| 284 | L1973 | half-step splits energy | EM Side-Channel: dI/dt Spike Profile per IEDM | `half_peak * 2 == full_peak` | Functional |
| 285 | L1989 | expected 7 NDR-safe transitions | EM Side-Channel: dI/dt Spike Profile per IEDM | `ndr_safe == 7` | Functional |
| 286 | L1992 | test_em_unknown_masking_extended | EM Side-Channel: dI/dt Spike Profile per IEDM | `function-level test` | Functional |
| 287 | L2000 | expected UNK | EM Side-Channel: Unknown Masking as EM Countermeasure | `trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 288 | L2007 | expected UNK | EM Side-Channel: Unknown Masking as EM Countermeasure | `trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 289 | L2023 | expected 1 leaked (FALSE only, absorbing) | EM Side-Channel: Unknown Masking as EM Countermeasure | `leaked == 1` | Functional |
| 290 | L2037 | expected UNK | EM Side-Channel: Unknown Masking as EM Countermeasure | `imp == TRIT_UNKNOWN` | Functional |
| 291 | L2040 | test_em_constant_time | EM Side-Channel: Unknown Masking as EM Countermeasure | `function-level test` | Functional |
| 292 | L2053 | expected -a for all inputs | EM Side-Channel: Constant-Time Verificatio | `consistent == 1` | Logic |
| 293 | L2065 | expected min semantics | EM Side-Channel: Constant-Time Verificatio | `ok == 1` | Boundary |
| 294 | L2077 | expected max semantics | EM Side-Channel: Constant-Time Verificatio | `ok == 1` | Boundary |
| 295 | L2084 | expected non-zero result for mixed packed AND | EM Side-Channel: Constant-Time Verificatio | `pr != 0` | Logic |
| 296 | L2088 | expected non-zero result for mixed packed OR | EM Side-Channel: Constant-Time Verificatio | `pr != 0` | Logic |
| 297 | L2092 | expected non-zero result for packed NOT | EM Side-Channel: Constant-Time Verificatio | `pr != 0` | Logic |
| 298 | L2099 | test_tmd_thermal_sweep | EM Side-Channel: Constant-Time Verificatio | `function-level test` | Functional |
| 299 | L2126 | expected all 8 stable | TMD Drift: Thermal Sweep Stability | `stable_count == 8` | Functional |
| 300 | L2142 | expected all 8 stable | TMD Drift: Thermal Sweep Stability | `stable_count == 8` | Functional |
| 301 | L2158 | expected all 8 stable | TMD Drift: Thermal Sweep Stability | `stable_count == 8` | Functional |
| 302 | L2161 | test_tmd_voltage_corners | TMD Drift: Thermal Sweep Stability | `function-level test` | Functional |
| 303 | L2184 | expected all 7 stable | TMD Drift: Voltage Corner Robustness | `stable_count == 7` | Functional |
| 304 | L2208 | expected stable at HVT | TMD Drift: Voltage Corner Robustness | `hvt_res.output == TRIT_TRUE` | Functional |
| 305 | L2214 | expected sum < V_DD | TMD Drift: Voltage Corner Robustness | `lvt_mv + mvt_mv < vdd_mv` | Arithmetic |
| 306 | L2217 | test_tmd_endurance | TMD Drift: Voltage Corner Robustness | `function-level test` | Functional |
| 307 | L2245 | expected <1% flip rate | TMD Drift: Endurance & WSe₂ Monolayer Drift | `flips < 10` | Functional |
| 308 | L2259 | expected <2% at elevated temp | TMD Drift: Endurance & WSe₂ Monolayer Drift | `hot_flips < 20` | Functional |
| 309 | L2268 | expected drift well within SNM | TMD Drift: Endurance & WSe₂ Monolayer Drift | `total_drift_mv < 50` | Functional |
| 310 | L2287 | expected all corners pass under drift | TMD Drift: Endurance & WSe₂ Monolayer Drift | `pvt_pass == 1` | Functional |
| 311 | L2290 | test_tmd_seu_tmd_interaction | TMD Drift: Endurance & WSe₂ Monolayer Drift | `function-level test` | Functional |
| 312 | L2307 | expected non-negative injection count | TMD Drift: SEU/TMD Interactio | `injected >= 0` | Negative/error |
| 313 | L2310 | expected non-negative flip count | TMD Drift: SEU/TMD Interactio | `st.flip_count >= 0` | Negative/error |
| 314 | L2334 | test_hesitation_init | TMD Drift: SEU/TMD Interactio | `function-level test` | Initialization |
| 315 | L2339 | expected 0 | Hesitation Reactor: Initializatio | `thes_init(&reactor) == 0` | Functional |
| 316 | L2342 | expected 1 | Hesitation Reactor: Initializatio | `reactor.initialized == 1` | Functional |
| 317 | L2345 | expected 0 | Hesitation Reactor: Initializatio | `reactor.channel_count == 0` | Functional |
| 318 | L2348 | expected 0 | Hesitation Reactor: Initializatio | `reactor.total_pauses == 0` | Functional |
| 319 | L2351 | expected -1 | Hesitation Reactor: Initializatio | `thes_init(NULL) == -1` | Functional |
| 320 | L2354 | test_hesitation_channel | Hesitation Reactor: Initializatio | `function-level test` | IPC |
| 321 | L2360 | expected 0 | Hesitation Reactor: Channel Registratio | `thes_register_channel(&reactor) == 0` | Functional |
| 322 | L2363 | expected 1 | Hesitation Reactor: Channel Registratio | `thes_register_channel(&reactor) == 1` | Functional |
| 323 | L2366 | expected 2 | Hesitation Reactor: Channel Registratio | `reactor.channel_count == 2` | Functional |
| 324 | L2374 | expected -1 | Hesitation Reactor: Channel Registratio | `thes_register_channel(&reactor) == -1` | Functional |
| 325 | L2377 | test_hesitation_observe | Hesitation Reactor: Channel Registratio | `function-level test` | Functional |
| 326 | L2386 | expected RUNNING | Hesitation Reactor: Observation & State Transitions | `state == THES_STATE_RUNNING` | Functional |
| 327 | L2390 | expected RUNNING | Hesitation Reactor: Observation & State Transitions | `state == THES_STATE_RUNNING` | Functional |
| 328 | L2398 | expected HESITATING | Hesitation Reactor: Observation & State Transitions | `state == THES_STATE_HESITATING` | Functional |
| 329 | L2401 | expected ≥1 pause | Hesitation Reactor: Observation & State Transitions | `thes_get_total_pauses(&reactor) >= 1` | Functional |
| 330 | L2404 | test_hesitation_confidence | Hesitation Reactor: Observation & State Transitions | `function-level test` | Functional |
| 331 | L2419 | expected 0 | Hesitation Reactor: Confidence Metrics | `thes_get_confidence(&reactor, ch, &conf) == 0` | Functional |
| 332 | L2430 | expected 2 | Hesitation Reactor: Confidence Metrics | `conf.streak_unknown == 2` | Functional |
| 333 | L2433 | test_hesitation_kl_divergence | Hesitation Reactor: Confidence Metrics | `function-level test` | Arithmetic |
| 334 | L2444 | expected ≈0 | Hesitation Reactor: KL Divergence | `kl >= 0 && kl <= 10` | Functional |
| 335 | L2452 | expected positive KL divergence | Hesitation Reactor: KL Divergence | `kl > 50` | Arithmetic |
| 336 | L2461 | expected slight < strong | Hesitation Reactor: KL Divergence | `kl_slight < kl_strong` | Functional |
| 337 | L2464 | test_hesitation_yield | Hesitation Reactor: KL Divergence | `function-level test` | Scheduling |
| 338 | L2475 | expected near 1000 | Hesitation Reactor: Yield B = exp(-D_KL) | `y >= 900` | Functional |
| 339 | L2483 | expected lower yield for mismatch | Hesitation Reactor: Yield B = exp(-D_KL) | `y_biased < y` | Logic |
| 340 | L2486 | expected non-negative yield | Hesitation Reactor: Yield B = exp(-D_KL) | `y_biased >= 0` | Negative/error |
| 341 | L2489 | test_hesitation_b4 | Hesitation Reactor: Yield B = exp(-D_KL) | `function-level test` | Functional |
| 342 | L2496 | expected 0 | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(&only_true) == 0` | Functional |
| 343 | L2502 | expected 0 | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(&only_false) == 0` | Functional |
| 344 | L2508 | expected 1 (B4 Both) | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(&both) == 1` | Functional |
| 345 | L2514 | expected 1 | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(&marginal) == 1` | Functional |
| 346 | L2520 | expected 0 | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(&sub) == 0` | Functional |
| 347 | L2524 | expected 0 | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(NULL) == 0` | Functional |
| 348 | L2530 | expected 0 | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(&empty) == 0` | Functional |
| 349 | L2536 | expected 1 | Hesitation Reactor: B4 Inconsistency Detectio | `thes_b4_check(&half) == 1` | Functional |
| 350 | L2539 | test_hesitation_recalibrate | Hesitation Reactor: B4 Inconsistency Detectio | `function-level test` | Functional |
| 351 | L2551 | expected 0 | Hesitation Reactor: Recalibratio | `thes_recalibrate(&reactor, ch) == 0` | Functional |
| 352 | L2554 | expected RECAL | Hesitation Reactor: Recalibratio | `reactor.channels[ch].state == THES_STATE_RECAL` | Functional |
| 353 | L2557 | expected 0 | Hesitation Reactor: Recalibratio | `reactor.channels[ch].dist.total == 0` | Functional |
| 354 | L2560 | expected 1 | Hesitation Reactor: Recalibratio | `reactor.channels[ch].recalibrations == 1` | Functional |
| 355 | L2563 | expected -1 | Hesitation Reactor: Recalibratio | `thes_recalibrate(&reactor, 99) == -1` | Functional |
| 356 | L2566 | test_hesitation_drift | Hesitation Reactor: Recalibratio | `function-level test` | Functional |
| 357 | L2587 | expected ~30% | Hesitation Reactor: Global Drift Monitoring | `drift >= 20 && drift <= 40` | Functional |
| 358 | L2590 | expected >0 | Hesitation Reactor: Global Drift Monitoring | `thes_get_total_decisions(&reactor) > 0` | Functional |

---

## Suite 29: RNS Standalone

**Source**: `tests/test_rns.c`
**Runtime Assertions**: 278
**Source-Level Entries**: 216
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

> **Note**: 62 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L52 | test_init_and_crt | Test Harness | `function-level test` | Initialization |
| 2 | L57 | expected 0 | RNS: Init & CRT Constants | `trit_rns_init(&ctx) == 0` | Functional |
| 3 | L60 | expected 3 | RNS: Init & CRT Constants | `ctx.count == 3` | Functional |
| 4 | L63 | expected 105 | RNS: Init & CRT Constants | `ctx.M == 105` | Functional |
| 5 | L66 | expected 35 | RNS: Init & CRT Constants | `ctx.Mi[0] == 35` | Functional |
| 6 | L69 | expected 21 | RNS: Init & CRT Constants | `ctx.Mi[1] == 21` | Functional |
| 7 | L72 | expected 15 | RNS: Init & CRT Constants | `ctx.Mi[2] == 15` | Functional |
| 8 | L76 | expected 2 | RNS: Init & CRT Constants | `ctx.Mi_inv[0] == 2` | Functional |
| 9 | L80 | expected 1 | RNS: Init & CRT Constants | `ctx.Mi_inv[1] == 1` | Functional |
| 10 | L84 | expected 1 | RNS: Init & CRT Constants | `ctx.Mi_inv[2] == 1` | Functional |
| 11 | L87 | expected -1 | RNS: Init & CRT Constants | `trit_rns_init(NULL) == -1` | Functional |
| 12 | L94 | test_trit_to_rns | RNS: Init & CRT Constants | `function-level test` | Functional |
| 13 | L151 | expected 0 | RNS: trit2_reg32 → RNS Conversio | `rn.residues[0] == 0` | Functional |
| 14 | L156 | expected 0 | RNS: trit2_reg32 → RNS Conversio | `rn2.residues[0] == 0` | Functional |
| 15 | L163 | test_crt_reconstruction | RNS: trit2_reg32 → RNS Conversio | `function-level test` | Functional |
| 16 | L176 | expected trit[0]=0 | RNS: CRT Reconstruction → trit2_reg32 | `v0 == 0` | Functional |
| 17 | L186 | expected +1 | RNS: CRT Reconstruction → trit2_reg32 | `trit2_decode(trit2_reg32_get(&out1, 0)) == 1` | Functional |
| 18 | L219 | expected 0 | RNS: CRT Reconstruction → trit2_reg32 | `trit2_decode(trit2_reg32_get(&null_out, 0)) == 0` | Functional |
| 19 | L226 | test_arithmetic | RNS: CRT Reconstruction → trit2_reg32 | `function-level test` | Arithmetic |
| 20 | L279 | expected zero | RNS: Carry-Free Arithmetic | `rns_is_zero(&zero, &ctx)` | Functional |
| 21 | L284 | expected 0 | RNS: Carry-Free Arithmetic | `rn.residues[0] == 0` | Functional |
| 22 | L291 | test_montgomery | RNS: Carry-Free Arithmetic | `function-level test` | Functional |
| 23 | L337 | expected 0 | RNS: Montgomery Modular Multiplicatio | `mn.residues[0] == 0` | Functional |
| 24 | L344 | test_zero_sparsity | RNS: Montgomery Modular Multiplicatio | `function-level test` | Functional |
| 25 | L351 | expected true | RNS: Zero & Sparsity Detectio | `rns_is_zero(&z, &ctx) == true` | Functional |
| 26 | L355 | expected false | RNS: Zero & Sparsity Detectio | `rns_is_zero(&nz1, &ctx) == false` | Functional |
| 27 | L359 | expected false | RNS: Zero & Sparsity Detectio | `rns_is_zero(&nz2, &ctx) == false` | Functional |
| 28 | L362 | expected false | RNS: Zero & Sparsity Detectio | `rns_is_zero(NULL, &ctx) == false` | Functional |
| 29 | L367 | expected sparse | RNS: Zero & Sparsity Detectio | `trit2_reg32_is_sparse(sparse_reg) == 1` | Parsing |
| 30 | L372 | expected not sparse | RNS: Zero & Sparsity Detectio | `trit2_reg32_is_sparse(dense_reg) == 0` | Logic |
| 31 | L379 | test_validate | RNS: Zero & Sparsity Detectio | `function-level test` | Functional |
| 32 | L387 | expected valid | RNS: Validate & Round-Trip Consistency | `rns_validate(&v42, &ctx) == 0` | Functional |
| 33 | L392 | expected valid | RNS: Validate & Round-Trip Consistency | `rns_validate(&v0, &ctx) == 0` | Functional |
| 34 | L397 | expected -1 | RNS: Validate & Round-Trip Consistency | `rns_validate(&bad, &ctx) == -1` | Functional |
| 35 | L402 | expected -1 | RNS: Validate & Round-Trip Consistency | `rns_validate(&bad2, &ctx) == -1` | Functional |
| 36 | L411 | forward residues valid | RNS: Validate & Round-Trip Consistency | `rns_validate(&rns1, &ctx) == 0` | Functional |
| 37 | L424 | expected -1 | RNS: Validate & Round-Trip Consistency | `rns_validate(&v0, NULL) == -1` | Functional |
| 38 | L427 | expected -1 | RNS: Validate & Round-Trip Consistency | `rns_validate(NULL, &ctx) == -1` | Functional |
| 39 | L434 | test_extend_moduli | RNS: Validate & Round-Trip Consistency | `function-level test` | Functional |
| 40 | L441 | expected 0 | RNS: Dynamic Moduli Extensio | `rns_extend_moduli(&ctx, 11) == 0` | Functional |
| 41 | L444 | expected 4 | RNS: Dynamic Moduli Extensio | `ctx.count == 4` | Functional |
| 42 | L447 | expected 1155 | RNS: Dynamic Moduli Extensio | `ctx.M == 1155` | Functional |
| 43 | L450 | expected 105 | RNS: Dynamic Moduli Extensio | `ctx.Mi[3] == 105` | Functional |
| 44 | L453 | expected 2 | RNS: Dynamic Moduli Extensio | `ctx.Mi_inv[3] == 2` | Functional |
| 45 | L457 | expected 385 | RNS: Dynamic Moduli Extensio | `ctx.Mi[0] == 385` | Functional |
| 46 | L461 | expected -1 | RNS: Dynamic Moduli Extensio | `rns_extend_moduli(&ctx, 6) == -1` | Functional |
| 47 | L465 | expected -1 | RNS: Dynamic Moduli Extensio | `rns_extend_moduli(&ctx, 1) == -1` | Functional |
| 48 | L469 | expected 0 | RNS: Dynamic Moduli Extensio | `rns_extend_moduli(&ctx, 13) == 0` | Functional |
| 49 | L472 | expected 0 | RNS: Dynamic Moduli Extensio | `rns_extend_moduli(&ctx, 17) == 0` | Functional |
| 50 | L475 | expected 6 | RNS: Dynamic Moduli Extensio | `ctx.count == 6` | Functional |
| 51 | L478 | expected -1 | RNS: Dynamic Moduli Extensio | `rns_extend_moduli(&ctx, 19) == -1` | Functional |
| 52 | L481 | expected -1 | RNS: Dynamic Moduli Extensio | `rns_extend_moduli(NULL, 11) == -1` | Functional |
| 53 | L488 | test_pvt_resilience | RNS: Dynamic Moduli Extensio | `function-level test` | Functional |
| 54 | L505 | a + 0 = a for all values | RNS: PVT-Style Resilience | `ok == 1` | Logic |
| 55 | L516 | a - a = 0 for all values | RNS: PVT-Style Resilience | `ok == 1` | Logic |
| 56 | L525 | all 105 residue tuples valid | RNS: PVT-Style Resilience | `ok == 1` | Functional |
| 57 | L560 | test_crypto_integration | RNS: PVT-Style Resilience | `function-level test` | Functional |
| 58 | L618 | extended residue valid | RNS: Crypto Integration — Modular Chains | `rns_validate(&esum, &ext_ctx) == 0` | Functional |
| 59 | L625 | test_noise_injection | RNS: Crypto Integration — Modular Chains | `function-level test` | Functional |
| 60 | L654 | did not crash | RNS: PVT Noise Injection (rns_apply_noise) | `1` | Logic |
| 61 | L660 | did not crash | RNS: PVT Noise Injection (rns_apply_noise) | `1` | Logic |
| 62 | L684 | starts valid | RNS: PVT Noise Injection (rns_apply_noise) | `rns_validate(&valid, &ctx) == 0` | Initialization |
| 63 | L699 | expected noise to change residues | RNS: PVT Noise Injection (rns_apply_noise) | `any_changed == 1` | Functional |
| 64 | L706 | test_conversions_extended | RNS: PVT Noise Injection (rns_apply_noise) | `function-level test` | Functional |
| 65 | L713 | expected 0 | Custom init with default {3,5,7} | `trit_rns_init_custom(&ctx, mod357, 3) == 0` | Functional |
| 66 | L716 | expected 105 | Custom init with default {3,5,7} | `ctx.M == 105` | Functional |
| 67 | L719 | expected 3 | Custom init with default {3,5,7} | `ctx.count == 3` | Functional |
| 68 | L725 | expected 0 | Custom init with Mersenne-4: {3,4,5} | `trit_rns_init_custom(&m4, mod_m4, 3) == 0` | Functional |
| 69 | L728 | expected 60 | Custom init with Mersenne-4: {3,4,5} | `m4.M == 60` | Functional |
| 70 | L731 | expected 4 | Custom init with Mersenne-4: {3,4,5} | `m4.moduli[1] == 4` | Functional |
| 71 | L737 | expected 0 | Custom init with Mersenne-8: {7,8,9} | `trit_rns_init_custom(&m8, mod_m8, 3) == 0` | Functional |
| 72 | L740 | expected 504 | Custom init with Mersenne-8: {7,8,9} | `m8.M == 504` | Functional |
| 73 | L746 | expected 0 | Custom init with ternary {3,13,37} | `trit_rns_init_custom(&tc, mod_tc, 3) == 0` | Functional |
| 74 | L749 | expected 1443 | Custom init with ternary {3,13,37} | `tc.M == 1443` | Functional |
| 75 | L755 | expected -1 non-coprime | Custom init with abundant {3,4,5,15} → should fail (3 and 15 | `trit_rns_init_custom(&ab, mod_ab, 4) == -1` | Functional |
| 76 | L761 | expected 0 | Coprime abundant alternative: {4,5,9,11} | `trit_rns_init_custom(&ab2, mod_ab2, 4) == 0` | Functional |
| 77 | L764 | expected 1980 | Coprime abundant alternative: {4,5,9,11} | `ab2.M == 1980` | Functional |
| 78 | L770 | expected 0 | Custom init with crypto {11,13,17,19,23} | `trit_rns_init_custom(&cry, mod_cry, 5) == 0` | Functional |
| 79 | L773 | expected 1062347 | Custom init with crypto {11,13,17,19,23} | `cry.M == 1062347` | Functional |
| 80 | L777 | expected -1 | Custom init error cases | `trit_rns_init_custom(NULL, mod357, 3) == -1` | Functional |
| 81 | L780 | expected -1 | Custom init error cases | `trit_rns_init_custom(&ctx, NULL, 3) == -1` | Functional |
| 82 | L783 | expected -1 | Custom init error cases | `trit_rns_init_custom(&ctx, mod357, 0) == -1` | Functional |
| 83 | L786 | expected -1 | Custom init error cases | `trit_rns_init_custom(&ctx, mod357, RNS_MAX_MODULI + 1) == -1` | Functional |
| 84 | L790 | expected -1 | Custom init error cases | `trit_rns_init_custom(&ctx, bad_mod, 3) == -1` | Functional |
| 85 | L798 | expected 0 | MRS conversion: value 42 in {3,5,7} | `rns_to_mrs(&r42, digits, &mrs_ctx) == 0` | Functional |
| 86 | L803 | expected 42 | MRS conversion: value 42 in {3,5,7} | `reconstructed == 42` | Functional |
| 87 | L808 | expected 0 | MRS roundtrip | `rns_from_mrs(digits, &r42_back, &mrs_ctx) == 0` | Functional |
| 88 | L821 | all digits zero | MRS for value 0 | `d0[0] == 0 && d0[1] == 0 && d0[2] == 0` | Functional |
| 89 | L850 | MRS roundtrip all values | MRS for all values 0..104 | `mrs_ok == 1` | Transformation |
| 90 | L854 | expected -1 | MRS error cases | `rns_to_mrs(NULL, digits, &mrs_ctx) == -1` | Functional |
| 91 | L857 | expected -1 | MRS error cases | `rns_to_mrs(&r42, NULL, &mrs_ctx) == -1` | Functional |
| 92 | L860 | expected -1 | MRS error cases | `rns_to_mrs(&r42, digits, NULL) == -1` | Functional |
| 93 | L863 | expected -1 | MRS error cases | `rns_from_mrs(NULL, &r42_back, &mrs_ctx) == -1` | Functional |
| 94 | L866 | expected -1 | MRS error cases | `rns_from_mrs(digits, NULL, &mrs_ctx) == -1` | Functional |
| 95 | L869 | expected -1 | MRS error cases | `rns_from_mrs(digits, &r42_back, NULL) == -1` | Functional |
| 96 | L885 | expected 4 | GCD public wrapper | `rns_gcd_public(12, 8) == 4` | Functional |
| 97 | L888 | expected 1 (coprime) | GCD public wrapper | `rns_gcd_public(17, 13) == 1` | Functional |
| 98 | L891 | expected 5 | GCD public wrapper | `rns_gcd_public(0, 5) == 5` | Functional |
| 99 | L897 | mod 11 correct | Crypto moduli: conversion roundtrip for value 999000 | `rc.residues[0] == 999000 % 11` | Functional |
| 100 | L930 | CRT identity holds for all Mersenne-8 channels | Additional conversion tests | `m8_ok == 1` | Logic |
| 101 | L937 | CRT identity holds for all ternary channels | Additional conversion tests | `tc_ok == 1` | Logic |
| 102 | L944 | CRT identity holds for all crypto channels | Additional conversion tests | `cry_ok == 1` | Logic |
| 103 | L947 | d[0] < m[0] | Additional conversion tests | `digits[0] < mrs_ctx.moduli[0]` | Functional |
| 104 | L950 | d[1] < m[1] | Additional conversion tests | `digits[1] < mrs_ctx.moduli[1]` | Functional |
| 105 | L953 | d[2] < m[2] | Additional conversion tests | `digits[2] < mrs_ctx.moduli[2]` | Functional |
| 106 | L960 | test_low_power_sim | Additional conversion tests | `function-level test` | Functional |
| 107 | L969 | expected 0 | TMVM-RNS init | `tmvm_rns_init(&st, &ctx) == 0` | Functional |
| 108 | L972 | expected -1 | TMVM-RNS init | `tmvm_rns_init(NULL, &ctx) == -1` | Functional |
| 109 | L975 | expected -1 | TMVM-RNS init | `tmvm_rns_init(&st, NULL) == -1` | Functional |
| 110 | L980 | expected 0 | Load 2x2 identity matrix: [[1,0],[0,1]] | `tmvm_rns_load_matrix(&st, id_mat, 2, 2) == 0` | Functional |
| 111 | L985 | expected 0 | Load vector [1, -1] | `tmvm_rns_load_vector(&st, vec, 2) == 0` | Functional |
| 112 | L989 | expected 0 | Execute identity × [1,-1] = [1,-1] | `tmvm_rns_execute(&st) == 0` | Functional |
| 113 | L992 | expected 1 | Execute identity × [1,-1] = [1,-1] | `st.result[0] == 1` | Functional |
| 114 | L995 | expected -1 | Execute identity × [1,-1] = [1,-1] | `st.result[1] == -1` | Functional |
| 115 | L998 | expected 2 | Execute identity × [1,-1] = [1,-1] | `st.result_len == 2` | Functional |
| 116 | L1008 | expected 0 | Load 2x3 matrix: [[1,1,0],[-1,0,1]] × [1,1,-1] = [2, -2] | `tmvm_rns_execute(&st2) == 0` | Functional |
| 117 | L1011 | expected 2 | Load 2x3 matrix: [[1,1,0],[-1,0,1]] × [1,1,-1] = [2, -2] | `st2.result[0] == 2` | Functional |
| 118 | L1014 | expected -2 | Load 2x3 matrix: [[1,1,0],[-1,0,1]] × [1,1,-1] = [2, -2] | `st2.result[1] == -2` | Functional |
| 119 | L1018 | expected > 0 | Energy model | `tmvm_rns_get_energy(&st2) > 0` | Functional |
| 120 | L1028 | expected 0 | Truncatio | `tmvm_rns_set_truncation(&st3, 2) == 0` | Functional |
| 121 | L1031 | expected -1 | Truncatio | `tmvm_rns_set_truncation(&st3, 0) == -1` | Functional |
| 122 | L1034 | expected -1 | Truncatio | `tmvm_rns_set_truncation(&st3, 99) == -1` | Functional |
| 123 | L1046 | expected 0 | RNS dot product | `tmvm_rns_dot(a_rns, b_rns, 2, &dot_out, &ctx) == 0` | Functional |
| 124 | L1055 | expected -1 | tmvm_rns_dot NULL cases | `tmvm_rns_dot(NULL, b_rns, 2, &dot_out, &ctx) == -1` | Functional |
| 125 | L1058 | expected -1 | tmvm_rns_dot NULL cases | `tmvm_rns_dot(a_rns, b_rns, 2, NULL, &ctx) == -1` | Functional |
| 126 | L1064 | expected -1 | Load errors | `tmvm_rns_load_matrix(&st_err, NULL, 2, 2) == -1` | Functional |
| 127 | L1070 | expected -1 | Load errors | `tmvm_rns_load_vector(&st_err, err_vec, 3) == -1` | Functional |
| 128 | L1077 | expected 0 | ResISC init | `resisc_init(&rs, &ctx) == 0` | Functional |
| 129 | L1080 | expected -1 | ResISC init | `resisc_init(NULL, &ctx) == -1` | Functional |
| 130 | L1085 | expected 0 | Encode pixels | `resisc_encode_pixels(&rs, pixels, 4) == 0` | Functional |
| 131 | L1088 | expected all-ones | Encode pixels | `rs.pixels[0].stream == 0xFFFFFFFFu` | Functional |
| 132 | L1091 | expected all-zeros | Encode pixels | `rs.pixels[2].stream == 0x00000000u` | Functional |
| 133 | L1094 | expected alternating | Encode pixels | `rs.pixels[1].stream == 0x55555555u` | Functional |
| 134 | L1099 | expected 0 | Load weights & execute | `resisc_load_weights(&rs, wt, 2) == 0` | Functional |
| 135 | L1102 | expected 0 | Load weights & execute | `resisc_execute(&rs) == 0` | Functional |
| 136 | L1108 | expected 1 | Load weights & execute | `rs.results[0] == 1` | Functional |
| 137 | L1111 | expected 1 | Load weights & execute | `rs.results[1] == 1` | Functional |
| 138 | L1114 | expected -2 | Load weights & execute | `rs.results[2] == -2` | Functional |
| 139 | L1117 | expected 3 | Load weights & execute | `rs.result_count == 3` | Functional |
| 140 | L1121 | expected > 0 | Energy metrics | `resisc_get_energy(&rs) > 0` | Functional |
| 141 | L1124 | expected > 0 | Energy metrics | `resisc_get_energy_saved(&rs) > 0` | Functional |
| 142 | L1127 | expected > 0 | Energy metrics | `resisc_get_snr(&rs) > 0` | Functional |
| 143 | L1132 | expected 0 errors | Noise injectio | `resisc_inject_noise(&rs, 0.0) == 0` | Negative/error |
| 144 | L1135 | expected -1 | Noise injectio | `resisc_inject_noise(&rs, -0.1) == -1` | Functional |
| 145 | L1138 | expected -1 | Noise injectio | `resisc_inject_noise(NULL, 0.5) == -1` | Functional |
| 146 | L1142 | expected -1 | Additional low-power tests | `resisc_encode_pixels(&rs, NULL, 4) == -1` | Functional |
| 147 | L1145 | expected -1 | Additional low-power tests | `resisc_encode_pixels(&rs, pixels, 0) == -1` | Functional |
| 148 | L1148 | expected -1 | Additional low-power tests | `resisc_load_weights(&rs, NULL, 2) == -1` | Functional |
| 149 | L1151 | expected -1 | Additional low-power tests | `resisc_load_weights(&rs, wt, 0) == -1` | Functional |
| 150 | L1154 | expected > 0 | Additional low-power tests | `rs.energy_sense_fj > 0` | Functional |
| 151 | L1157 | expected 4 | Additional low-power tests | `rs.pixel_count == 4` | Functional |
| 152 | L1172 | expected 3 | TMVM-RNS: 3x3 all-ones matrix × all-ones vector | `st_ones.crt_reconstructions == 3` | Functional |
| 153 | L1175 | expected > 0 | TMVM-RNS: 3x3 all-ones matrix × all-ones vector | `st_ones.total_channel_macs > 0` | Functional |
| 154 | L1182 | test_crypto_extended | TMVM-RNS: 3x3 all-ones matrix × all-ones vector | `function-level test` | Functional |
| 155 | L1192 | expected 0 | Montgomery exp: base^0 = 1 (identity) | `rns_montgomery_exp(&base, 0, &result, &ctx) == 0` | Functional |
| 156 | L1203 | expected 0 | Montgomery exp: base^1 = base (via REDC) | `rns_montgomery_exp(&base, 1, &exp1, &ctx) == 0` | Functional |
| 157 | L1259 | expected -1 | Montgomery exp NULL cases | `rns_montgomery_exp(NULL, 5, &result, &ctx) == -1` | Functional |
| 158 | L1262 | expected -1 | Montgomery exp NULL cases | `rns_montgomery_exp(&base, 5, NULL, &ctx) == -1` | Functional |
| 159 | L1265 | expected -1 | Montgomery exp NULL cases | `rns_montgomery_exp(&base, 5, &result, NULL) == -1` | Functional |
| 160 | L1273 | expected 0 | RNS: Crypto — Extended Moduli Exponentiatio | `trit_rns_init_custom(&cry, mod_cry, 5) == 0` | Functional |
| 161 | L1283 | all residues in range | RNS: Crypto — Extended Moduli Exponentiatio | `cry_ok == 1` | Boundary |
| 162 | L1292 | all residues in range | RNS: Crypto — Extended Moduli Exponentiatio | `cry_ok == 1` | Boundary |
| 163 | L1300 | expected 0 | Redundant check: extend {3,5,7} with auto-detected prime | `rns_add_redundant_check(&red_ctx) == 0` | Functional |
| 164 | L1303 | expected 4 | Redundant check: extend {3,5,7} with auto-detected prime | `red_ctx.count == 4` | Functional |
| 165 | L1313 | coprime verified | Redundant check: extend {3,5,7} with auto-detected prime | `cop == 1` | Functional |
| 166 | L1322 | new modulus is prime | Redundant check: extend {3,5,7} with auto-detected prime | `is_p == 1` | Functional |
| 167 | L1325 | expected -1 | Redundant check: extend {3,5,7} with auto-detected prime | `rns_add_redundant_check(NULL) == -1` | Functional |
| 168 | L1334 | expected 0 | Fill to max and try agai | `rns_add_redundant_check(&full_ctx) == 0` | Functional |
| 169 | L1337 | expected 6 | Fill to max and try agai | `full_ctx.count == 6` | Functional |
| 170 | L1340 | expected -1 | Fill to max and try agai | `rns_add_redundant_check(&full_ctx) == -1` | Functional |
| 171 | L1353 | expected 0 | Detect/correct: no error | `rns_detect_correct(&clean, &corrected, &dc_ctx) == 0` | Functional |
| 172 | L1363 | expected -1 | detect_correct NULL cases | `rns_detect_correct(NULL, &corrected, &dc_ctx) == -1` | Functional |
| 173 | L1366 | expected -1 | detect_correct NULL cases | `rns_detect_correct(&clean, NULL, &dc_ctx) == -1` | Functional |
| 174 | L1369 | expected -1 | detect_correct NULL cases | `rns_detect_correct(&clean, &corrected, NULL) == -1` | Functional |
| 175 | L1376 | expected -1 | detect_correct: too few moduli | `rns_detect_correct(&clean, &corrected, &tiny) == -1` | Functional |
| 176 | L1407 | crypto exp^10 in range | Montgomery exp with crypto moduli: various exponents | `cry_r == 1` | Boundary |
| 177 | L1417 | 0^0 in range across crypto channels | Montgomery exp with crypto moduli: various exponents | `cry_r == 1` | Boundary |
| 178 | L1424 | extended M > original 105 | Montgomery exp with crypto moduli: various exponents | `red_ctx.M > 105` | Functional |
| 179 | L1431 | test_multi_radix_extended | Montgomery exp with crypto moduli: various exponents | `function-level test` | Arithmetic |
| 180 | L1469 | expected true | RNS: Multi-Radix — Mersenne-4 {3,4,5} | `rns_is_zero(&z4, &m4) == true` | Functional |
| 181 | L1477 | all 60 values valid | RNS: Multi-Radix — Mersenne-4 {3,4,5} | `ok_m4 == 1` | Hardware/ALU |
| 182 | L1527 | expected zero | RNS: Multi-Radix — Mersenne-8 {7,8,9} | `rns_is_zero(&d0, &m8)` | Functional |
| 183 | L1535 | all 504 values valid | RNS: Multi-Radix — Mersenne-8 {7,8,9} | `ok_m8 == 1` | Hardware/ALU |
| 184 | L1607 | expected valid | RNS: Multi-Radix — Ternary {3,13,37} | `rns_validate(&rmax, &tc) == 0` | Functional |
| 185 | L1642 | expected zero | RNS: Multi-Radix — Crypto {11,13,17,19,23} | `rns_is_zero(&c_zero, &cry)` | Functional |
| 186 | L1660 | expected valid | RNS: Multi-Radix — Crypto {11,13,17,19,23} | `rns_validate(&c_sum, &cry) == 0` | Functional |
| 187 | L1683 | expected 15 | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn.M == 15` | Functional |
| 188 | L1686 | expected 0 | RNS: Multi-Radix — Dynamic Extension Patterns | `rns_extend_moduli(&dyn, 7) == 0` | Functional |
| 189 | L1689 | expected 105 | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn.M == 105` | Functional |
| 190 | L1692 | expected 0 | RNS: Multi-Radix — Dynamic Extension Patterns | `rns_extend_moduli(&dyn, 11) == 0` | Functional |
| 191 | L1695 | expected 1155 | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn.M == 1155` | Functional |
| 192 | L1698 | expected 0 | RNS: Multi-Radix — Dynamic Extension Patterns | `rns_extend_moduli(&dyn, 13) == 0` | Functional |
| 193 | L1701 | expected 15015 | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn.M == 15015` | Functional |
| 194 | L1704 | expected 0 | RNS: Multi-Radix — Dynamic Extension Patterns | `rns_extend_moduli(&dyn, 17) == 0` | Functional |
| 195 | L1707 | expected 255255 | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn.M == 255255` | Functional |
| 196 | L1710 | expected 6 | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn.count == 6` | Functional |
| 197 | L1724 | 6-moduli add correct | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn_ok == 1` | Arithmetic |
| 198 | L1737 | 6-moduli mul correct | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn_ok == 1` | Arithmetic |
| 199 | L1751 | 6-moduli MRS roundtrip matches | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn_ok == 1` | Transformation |
| 200 | L1754 | expected valid | RNS: Multi-Radix — Dynamic Extension Patterns | `rns_validate(&d1e5, &dyn) == 0` | Functional |
| 201 | L1766 | 6-moduli Montgomery exp in range | RNS: Multi-Radix — Dynamic Extension Patterns | `dyn_ok == 1` | Boundary |
| 202 | L1796 | expected -1 | RNS: Multi-Radix — Cross-Domain Consistency | `trit_rns_init_custom(&nc1, nc_mods1, 3) == -1` | Functional |
| 203 | L1801 | expected -1 | RNS: Multi-Radix — Cross-Domain Consistency | `trit_rns_init_custom(&nc2, nc_mods2, 3) == -1` | Functional |
| 204 | L1806 | expected 0 | RNS: Multi-Radix — Cross-Domain Consistency | `trit_rns_init_custom(&cp, cp_mods, 3) == 0` | Functional |
| 205 | L1809 | expected 1800 | RNS: Multi-Radix — Cross-Domain Consistency | `cp.M == 1800` | Functional |
| 206 | L1870 | expected 0 | RNS: Multi-Radix — Cross-Domain Consistency | `trit_rns_init_custom(&s1, one_m, 1) == 0` | Functional |
| 207 | L1873 | expected M=5 | RNS: Multi-Radix — Cross-Domain Consistency | `s1.M == 5` | Functional |
| 208 | L1880 | expected 2 (7 mod 5) | RNS: Multi-Radix — Cross-Domain Consistency | `s_sum.residues[0] == 2` | Functional |
| 209 | L1885 | expected 2 (12 mod 5) | RNS: Multi-Radix — Cross-Domain Consistency | `s_prod.residues[0] == 2` | Functional |
| 210 | L1892 | expected M=21 | RNS: Multi-Radix — Cross-Domain Consistency | `t2.M == 21` | Functional |
| 211 | L1908 | expected 0 | RNS: Multi-Radix — Cross-Domain Consistency | `trit_rns_init_custom(&lg, lg_mods, 3) == 0` | Functional |
| 212 | L1911 | expected product | RNS: Multi-Radix — Cross-Domain Consistency | `lg.M == 97u * 101u * 103u` | Arithmetic |
| 213 | L1949 | redundant context arithmetic correct | RNS: Multi-Radix — Cross-Domain Consistency | `rd_ok == 1` | Arithmetic |
| 214 | L1964 | valid in extended context | Final boundary and edge tests | `rns_validate(&rd_val, &rd) == 0` | Scheduling |
| 215 | L1968 | zero in two-moduli | Final boundary and edge tests | `rns_is_zero(&t2_zero, &t2)` | Functional |
| 216 | L1981 | expected valid | Final boundary and edge tests | `rns_validate(&lg_prod, &lg) == 0` | Functional |

---

## Suite 30: Paper-Derived Modules

**Source**: `tests/test_papers.c`
**Runtime Assertions**: 200
**Source-Level Entries**: 220
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L62 | test_art9_init | Test Harness | `function-level test` | Initialization |
| 2 | L67 | expected 0 | ART-9: Initialization & Constants | `art9_init(&st) == 0` | Functional |
| 3 | L70 | expected 1 | ART-9: Initialization & Constants | `st.initialized == 1` | Functional |
| 4 | L73 | expected -1 | ART-9: Initialization & Constants | `art9_init(NULL) == -1` | Functional |
| 5 | L79 | expected all regs 0 | ART-9: Initialization & Constants | `all_zero` | Functional |
| 6 | L82 | expected 27 | ART-9: Initialization & Constants | `ART9_NUM_REGS == 27` | Functional |
| 7 | L85 | expected 9841 | ART-9: Initialization & Constants | `ART9_WORD_MAX == 9841` | Functional |
| 8 | L88 | expected 5 | ART-9: Initialization & Constants | `ART9_PIPELINE_STAGES == 5` | Functional |
| 9 | L91 | expected 24 | ART-9: Initialization & Constants | `ART9_OP_COUNT == 24` | Functional |
| 10 | L94 | test_art9_alu_ops | ART-9: Initialization & Constants | `function-level test` | Hardware/ALU |
| 11 | L109 | expected 150 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 150` | Functional |
| 12 | L113 | expected 50 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 50` | Functional |
| 13 | L117 | expected 5000 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 5000` | Functional |
| 14 | L121 | expected -100 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == -100` | Functional |
| 15 | L125 | expected -30 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == -30` | Functional |
| 16 | L129 | expected 100 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 100` | Functional |
| 17 | L133 | expected -100 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == -100` | Functional |
| 18 | L137 | expected 300 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 300` | Functional |
| 19 | L141 | expected 33 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 33` | Functional |
| 20 | L145 | expected -10 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == -10` | Functional |
| 21 | L149 | expected 1 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 1` | Functional |
| 22 | L153 | expected -1 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == -1` | Functional |
| 23 | L157 | expected 0 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 0` | Functional |
| 24 | L161 | expected 142 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 142` | Functional |
| 25 | L165 | expected 777 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 777` | Functional |
| 26 | L169 | expected 30 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 30` | Functional |
| 27 | L173 | expected -30 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == -30` | Functional |
| 28 | L177 | expected 50 | ART-9: ALU Instruction Executio | `art9_execute_alu(&st, &inst) == 50` | Functional |
| 29 | L180 | test_art9_clamp_overflow | ART-9: ALU Instruction Executio | `function-level test` | Boundary |
| 30 | L186 | expected 0 | ART-9: Overflow Clamping & Word Boundaries | `art9_clamp(0) == 0` | Functional |
| 31 | L189 | expected 9841 | ART-9: Overflow Clamping & Word Boundaries | `art9_clamp(ART9_WORD_MAX) == ART9_WORD_MAX` | Functional |
| 32 | L192 | expected -9841 | ART-9: Overflow Clamping & Word Boundaries | `art9_clamp(ART9_WORD_MIN) == ART9_WORD_MIN` | Functional |
| 33 | L195 | expected 9841 | ART-9: Overflow Clamping & Word Boundaries | `art9_clamp(99999) == ART9_WORD_MAX` | Functional |
| 34 | L198 | expected -9841 | ART-9: Overflow Clamping & Word Boundaries | `art9_clamp(-99999) == ART9_WORD_MIN` | Functional |
| 35 | L203 | clamped to 9841 | ART-9: Overflow Clamping & Word Boundaries | `art9_execute_alu(&st, &inst) == ART9_WORD_MAX` | Boundary |
| 36 | L206 | test_art9_mem_ops | ART-9: Overflow Clamping & Word Boundaries | `function-level test` | Functional |
| 37 | L218 | expected mem[10] = 42 | ART-9: Load/Store Memory Operations | `st.memory[10] == 42` | Functional |
| 38 | L222 | expected 42 | ART-9: Load/Store Memory Operations | `art9_execute_alu(&st, &inst) == 42` | Functional |
| 39 | L226 | expected 0 | ART-9: Load/Store Memory Operations | `art9_execute_alu(&st, &inst) == 0` | Functional |
| 40 | L229 | test_art9_pipeline_run | ART-9: Load/Store Memory Operations | `function-level test` | IPC |
| 41 | L243 | expected 0 | ART-9: Pipeline Execution & Statistics | `art9_load_program(&st, prog, 4) == 0` | Functional |
| 42 | L247 | expected positive cycles | ART-9: Pipeline Execution & Statistics | `cycles > 0` | Performance |
| 43 | L250 | expected 30 | ART-9: Pipeline Execution & Statistics | `st.regs[2] == 30` | Functional |
| 44 | L253 | expected 10 | ART-9: Pipeline Execution & Statistics | `st.regs[0] == 10` | Functional |
| 45 | L256 | expected 20 | ART-9: Pipeline Execution & Statistics | `st.regs[1] == 20` | Functional |
| 46 | L259 | expected > 0 | ART-9: Pipeline Execution & Statistics | `st.instructions_retired > 0` | Functional |
| 47 | L263 | expected CPI < 5.0 | ART-9: Pipeline Execution & Statistics | `cpi > 0 && cpi < 5000` | Performance |
| 48 | L266 | expected energy > 0 | ART-9: Pipeline Execution & Statistics | `st.energy_fj > 0` | Functional |
| 49 | L269 | expected -1 | ART-9: Pipeline Execution & Statistics | `art9_load_program(&st, NULL, 4) == -1` | Functional |
| 50 | L272 | expected -1 | ART-9: Pipeline Execution & Statistics | `art9_load_program(&st, prog, 0) == -1` | Functional |
| 51 | L275 | test_art9_radix_economy | ART-9: Pipeline Execution & Statistics | `function-level test` | Functional |
| 52 | L281 | expected 1000 | ART-9: Radix Economy & DMIPS | `art9_radix_economy(1) == 1000` | Functional |
| 53 | L285 | expected reasonable economy | ART-9: Radix Economy & DMIPS | `econ > 0 && econ <= 1200` | Functional |
| 54 | L289 | expected < 1200 | ART-9: Radix Economy & DMIPS | `econ > 0 && econ < 1200` | Functional |
| 55 | L292 | expected 0 | ART-9: Radix Economy & DMIPS | `art9_get_dmips(&st, 100) == 0` | Functional |
| 56 | L295 | expected 158 | ART-9: Radix Economy & DMIPS | `ART9_DENSITY_RATIO_PCT == 158` | Functional |
| 57 | L298 | expected 729 | ART-9: Radix Economy & DMIPS | `ART9_MEM_SIZE == 729` | Functional |
| 58 | L301 | expected 256 | ART-9: Radix Economy & DMIPS | `ART9_MAX_PROGRAM == 256` | Functional |
| 59 | L304 | expected 9 | ART-9: Radix Economy & DMIPS | `ART9_TRITS_PER_WORD == 9` | Functional |
| 60 | L307 | expected 12 | ART-9: Radix Economy & DMIPS | `ART9_ENERGY_PER_INST_FJ == 12` | Functional |
| 61 | L315 | expected memory zeroed | ART-9: Radix Economy & DMIPS | `mem_zero` | Memory |
| 62 | L318 | expected 1000 | ART-9: Radix Economy & DMIPS | `art9_radix_economy(0) == 1000` | Functional |
| 63 | L321 | expected 1 | ART-9: Radix Economy & DMIPS | `art9_clamp(1) == 1` | Functional |
| 64 | L324 | expected -1 | ART-9: Radix Economy & DMIPS | `art9_clamp(-1) == -1` | Functional |
| 65 | L332 | test_dlt_init | ART-9: Radix Economy & DMIPS | `function-level test` | Initialization |
| 66 | L337 | expected 0 | DLT: Initialization & Layer Setup | `dlt_init(&st) == 0` | Functional |
| 67 | L340 | expected -1 | DLT: Initialization & Layer Setup | `dlt_init(NULL) == -1` | Functional |
| 68 | L343 | expected 1 | DLT: Initialization & Layer Setup | `st.initialized == 1` | Functional |
| 69 | L346 | expected 0 | DLT: Initialization & Layer Setup | `dlt_add_layer(&st) == 0` | Functional |
| 70 | L349 | expected 1 | DLT: Initialization & Layer Setup | `dlt_add_layer(&st) == 1` | Functional |
| 71 | L352 | expected 500 | DLT: Initialization & Layer Setup | `st.layers[0].wp == DLT_DEFAULT_WP` | Functional |
| 72 | L355 | expected -500 | DLT: Initialization & Layer Setup | `st.layers[0].wn == DLT_DEFAULT_WN` | Functional |
| 73 | L358 | expected 0 | DLT: Initialization & Layer Setup | `st.layers[0].delta == DLT_DEFAULT_DELTA` | Functional |
| 74 | L361 | expected 2 | DLT: Initialization & Layer Setup | `st.layer_count == 2` | Functional |
| 75 | L364 | test_dlt_quantize | DLT: Initialization & Layer Setup | `function-level test` | Functional |
| 76 | L375 | expected 0 | DLT: Weight Quantizatio | `dlt_quantize(&st, layer, weights, out, 10) == 0` | Functional |
| 77 | L378 | expected +1 | DLT: Weight Quantizatio | `out[0] == TRIT_TRUE` | Functional |
| 78 | L381 | expected -1 | DLT: Weight Quantizatio | `out[1] == TRIT_FALSE` | Functional |
| 79 | L384 | expected 0 | DLT: Weight Quantizatio | `out[2] == TRIT_UNKNOWN` | Functional |
| 80 | L387 | expected +1 | DLT: Weight Quantizatio | `out[3] == TRIT_TRUE` | Functional |
| 81 | L390 | expected -1 | DLT: Weight Quantizatio | `out[4] == TRIT_FALSE` | Functional |
| 82 | L393 | expected 0 | DLT: Weight Quantizatio | `out[5] == TRIT_UNKNOWN` | Functional |
| 83 | L396 | expected 0 | DLT: Weight Quantizatio | `out[6] == TRIT_UNKNOWN` | Functional |
| 84 | L399 | expected 0 | DLT: Weight Quantizatio | `out[7] == TRIT_UNKNOWN` | Functional |
| 85 | L402 | expected 2 | DLT: Weight Quantizatio | `st.layers[layer].count_pos == 2` | Functional |
| 86 | L405 | expected 2 | DLT: Weight Quantizatio | `st.layers[layer].count_neg == 2` | Functional |
| 87 | L408 | expected 6 | DLT: Weight Quantizatio | `st.layers[layer].count_zero == 6` | Functional |
| 88 | L411 | expected -1 | DLT: Weight Quantizatio | `dlt_quantize(&st, layer, NULL, out, 10) == -1` | Functional |
| 89 | L414 | expected -1 | DLT: Weight Quantizatio | `dlt_quantize(&st, 99, weights, out, 10) == -1` | Functional |
| 90 | L417 | test_dlt_trapping | DLT: Weight Quantizatio | `function-level test` | Functional |
| 91 | L432 | expected trapped > 0 | DLT: Deadzone Trapping Detection & Escape | `trap_count > 0` | Functional |
| 92 | L435 | trapped <= zeros | DLT: Deadzone Trapping Detection & Escape | `trap_count <= st.layers[layer].count_zero` | Functional |
| 93 | L440 | expected 0 | DLT: Deadzone Trapping Detection & Escape | `rc == 0` | Functional |
| 94 | L445 | expected width < 1000 (shrunk from default) | DLT: Deadzone Trapping Detection & Escape | `new_width < 1000` | Functional |
| 95 | L448 | expected 1 | DLT: Deadzone Trapping Detection & Escape | `st.iterations == 1` | Functional |
| 96 | L451 | expected -1 | DLT: Deadzone Trapping Detection & Escape | `dlt_update_thresholds(&st, layer, NULL, 16) == -1` | Functional |
| 97 | L454 | expected 0 | DLT: Deadzone Trapping Detection & Escape | `dlt_detect_trapped(&st, 99, trapped_weights, 16) == 0` | Functional |
| 98 | L457 | test_dlt_sparsity_accuracy | DLT: Deadzone Trapping Detection & Escape | `function-level test` | Functional |
| 99 | L468 | expected 800 | DLT: Sparsity & Quantization Accuracy | `dlt_get_sparsity(&st, layer) == 800` | Functional |
| 100 | L471 | expected 0 | DLT: Sparsity & Quantization Accuracy | `dlt_get_sparsity(&st, 99) == 0` | Functional |
| 101 | L480 | expected 1000 (100%) | DLT: Sparsity & Quantization Accuracy | `acc == 1000` | Functional |
| 102 | L483 | expected 0 | DLT: Sparsity & Quantization Accuracy | `dlt_quant_accuracy(NULL, pos_out, 4) == 0` | Functional |
| 103 | L491 | thresholds shifted | DLT: Sparsity & Quantization Accuracy | `out[0] == TRIT_TRUE && out[1] == TRIT_FALSE` | Functional |
| 104 | L494 | test_dlt_edge_cases | DLT: Sparsity & Quantization Accuracy | `function-level test` | Functional |
| 105 | L504 | expected max-1 | DLT: Edge Cases & Stress | `last_ok == DLT_MAX_LAYERS - 1` | Boundary |
| 106 | L507 | expected -1 | DLT: Edge Cases & Stress | `dlt_add_layer(&st) == -1` | Functional |
| 107 | L516 | expected +1 | DLT: Edge Cases & Stress | `t == TRIT_TRUE` | Functional |
| 108 | L521 | expected 0 (at boundary, not above) | DLT: Edge Cases & Stress | `t == TRIT_UNKNOWN` | Boundary |
| 109 | L526 | expected 0 (at neg boundary, not below) | DLT: Edge Cases & Stress | `t == TRIT_UNKNOWN` | Boundary |
| 110 | L531 | expected -1 | DLT: Edge Cases & Stress | `t == TRIT_FALSE` | Functional |
| 111 | L536 | expected +1 | DLT: Edge Cases & Stress | `t == TRIT_TRUE` | Functional |
| 112 | L539 | expected 1000 | DLT: Edge Cases & Stress | `DLT_FP_SCALE == 1000` | Functional |
| 113 | L542 | expected 500 | DLT: Edge Cases & Stress | `DLT_DEFAULT_WP == 500` | Functional |
| 114 | L545 | expected 10 | DLT: Edge Cases & Stress | `DLT_LEARN_RATE == 10` | Functional |
| 115 | L548 | expected 50 | DLT: Edge Cases & Stress | `DLT_TRAP_WINDOW == 50` | Functional |
| 116 | L556 | test_off_init | DLT: Edge Cases & Stress | `function-level test` | Initialization |
| 117 | L561 | expected 0 | OFF: Initialization & Temperature | `off_init(&st) == 0` | Functional |
| 118 | L564 | expected -1 | OFF: Initialization & Temperature | `off_init(NULL) == -1` | Functional |
| 119 | L567 | expected 1000 | OFF: Initialization & Temperature | `st.temperature == OFF_DEFAULT_TEMP` | Functional |
| 120 | L570 | expected 0 | OFF: Initialization & Temperature | `off_set_temperature(&st, 2000) == 0` | Functional |
| 121 | L573 | expected 2000 | OFF: Initialization & Temperature | `st.temperature == 2000` | Functional |
| 122 | L576 | expected -1 | OFF: Initialization & Temperature | `off_set_temperature(&st, 0) == -1` | Functional |
| 123 | L579 | expected -1 | OFF: Initialization & Temperature | `off_set_temperature(NULL, 1000) == -1` | Functional |
| 124 | L582 | test_off_cosine_sim | OFF: Initialization & Temperature | `function-level test` | Functional |
| 125 | L591 | expected ~1000 | OFF: Cosine Similarity | `cs >= 990 && cs <= 1000` | Functional |
| 126 | L598 | expected ~-1000 | OFF: Cosine Similarity | `cs <= -990 && cs >= -1000` | Functional |
| 127 | L606 | expected 0 | OFF: Cosine Similarity | `cs == 0` | Functional |
| 128 | L613 | expected 0 | OFF: Cosine Similarity | `cs == 0` | Functional |
| 129 | L616 | expected 0 | OFF: Cosine Similarity | `off_cosine_similarity(NULL, vb, 4) == 0` | Functional |
| 130 | L619 | expected 0 | OFF: Cosine Similarity | `off_cosine_similarity(va, vb, 0) == 0` | Functional |
| 131 | L627 | expected between 0 and 1000 | OFF: Cosine Similarity | `cs > 0 && cs < 1000` | Logic |
| 132 | L635 | expected ~1000 | OFF: Cosine Similarity | `cs >= 999` | Functional |
| 133 | L638 | test_off_mutual_info | OFF: Cosine Similarity | `function-level test` | Functional |
| 134 | L642 | expected 7000 | OFF: Mutual Information Estimatio | `off_estimate_mi(1000) == 7000` | Functional |
| 135 | L645 | expected 0 | OFF: Mutual Information Estimatio | `off_estimate_mi(0) == 0` | Functional |
| 136 | L650 | expected monotonic | OFF: Mutual Information Estimatio | `mi_900 > mi_500` | Functional |
| 137 | L654 | expected equal | OFF: Mutual Information Estimatio | `mi_neg == mi_900` | Functional |
| 138 | L658 | expected >= 0 | OFF: Mutual Information Estimatio | `mi_100 >= 0` | Functional |
| 139 | L661 | expected > 0 | OFF: Mutual Information Estimatio | `off_estimate_mi(500) > 0` | Functional |
| 140 | L664 | expected monotonic | OFF: Mutual Information Estimatio | `off_estimate_mi(100) <= off_estimate_mi(500)` | Functional |
| 141 | L674 | expected monotonic increase | OFF: Mutual Information Estimatio | `monotonic` | Functional |
| 142 | L677 | test_off_distill_step | OFF: Mutual Information Estimatio | `function-level test` | Functional |
| 143 | L687 | expected 0 | OFF: Distillation Step & Outliers | `idx == 0` | Functional |
| 144 | L690 | expected positive cos_sim | OFF: Distillation Step & Outliers | `st.layers[0].cos_sim > 0` | Functional |
| 145 | L693 | expected off_loss | OFF: Distillation Step & Outliers | `st.layers[0].off_loss == 1000 - st.layers[0].cos_sim` | Functional |
| 146 | L696 | expected MI > 0 | OFF: Distillation Step & Outliers | `st.layers[0].mutual_info > 0` | Functional |
| 147 | L699 | expected 1 | OFF: Distillation Step & Outliers | `st.layer_count == 1` | Functional |
| 148 | L706 | expected >= 1 outlier | OFF: Distillation Step & Outliers | `outliers >= 1` | Functional |
| 149 | L710 | expected 0 | OFF: Distillation Step & Outliers | `off_count_outliers(uniform, 4) == 0` | Functional |
| 150 | L713 | expected 0 | OFF: Distillation Step & Outliers | `off_count_outliers(NULL, 4) == 0` | Functional |
| 151 | L719 | expected 3 | OFF: Distillation Step & Outliers | `st.layer_count == 3` | Functional |
| 152 | L722 | expected positive avg | OFF: Distillation Step & Outliers | `st.avg_cos_sim > 0` | Functional |
| 153 | L725 | test_off_retention | OFF: Distillation Step & Outliers | `function-level test` | Functional |
| 154 | L731 | expected 0 | OFF: Information Retentio | `off_get_retention(&st) == 0` | Functional |
| 155 | L740 | expected positive retention | OFF: Information Retentio | `ret > 0` | Functional |
| 156 | L743 | expected <= 1000 | OFF: Information Retentio | `ret <= 1000` | Functional |
| 157 | L746 | expected -1 | OFF: Information Retentio | `off_distill_step(&st, NULL, s, 4) == -1` | Functional |
| 158 | L749 | expected -1 | OFF: Information Retentio | `off_distill_step(NULL, t, s, 4) == -1` | Functional |
| 159 | L752 | expected -1 | OFF: Information Retentio | `off_distill_step(&st, t, s, 0) == -1` | Functional |
| 160 | L755 | expected 800 | OFF: Information Retentio | `OFF_INFO_THRESHOLD == 800` | Functional |
| 161 | L758 | expected 1024 | OFF: Information Retentio | `OFF_MAX_DIM == 1024` | Functional |
| 162 | L761 | expected 1000 | OFF: Information Retentio | `OFF_FP_SCALE == 1000` | Functional |
| 163 | L764 | expected 0 | OFF: Information Retentio | `off_get_retention(NULL) == 0` | Functional |
| 164 | L770 | expected ~1000 (proportional) | OFF: Information Retentio | `cs >= 999` | Functional |
| 165 | L778 | test_tps_init | OFF: Information Retentio | `function-level test` | Initialization |
| 166 | L783 | expected 0 | TPS: Initialization & Constants | `tps_init(&st) == 0` | Functional |
| 167 | L786 | expected -1 | TPS: Initialization & Constants | `tps_init(NULL) == -1` | Functional |
| 168 | L789 | expected 1580 | TPS: Initialization & Constants | `TPS_BITS_PER_TERNARY == 1580` | Functional |
| 169 | L792 | expected 16000 | TPS: Initialization & Constants | `TPS_BITS_PER_FLOAT == 16000` | Functional |
| 170 | L795 | expected 99 | TPS: Initialization & Constants | `TPS_SPECTRA_99M == 99` | Functional |
| 171 | L798 | expected 3900 | TPS: Initialization & Constants | `TPS_SPECTRA_3B9 == 3900` | Functional |
| 172 | L801 | test_tps_bit_equivalent | TPS: Initialization & Constants | `function-level test` | Functional |
| 173 | L806 | expected ~9-10 | TPS: Bit-Equivalent Parameter Count | `be >= 9 && be <= 10` | Functional |
| 174 | L810 | expected 100 | TPS: Bit-Equivalent Parameter Count | `be == 100` | Functional |
| 175 | L814 | expected ~98 | TPS: Bit-Equivalent Parameter Count | `be >= 95 && be <= 100` | Functional |
| 176 | L817 | expected 0 | TPS: Bit-Equivalent Parameter Count | `tps_bit_equivalent(0, TPS_BITS_PER_TERNARY) == 0` | Functional |
| 177 | L820 | expected 0 | TPS: Bit-Equivalent Parameter Count | `tps_bit_equivalent(100, 0) == 0` | Functional |
| 178 | L825 | expected ~6 | TPS: Bit-Equivalent Parameter Count | `be >= 5 && be <= 7` | Functional |
| 179 | L828 | test_tps_loss_ppl | TPS: Bit-Equivalent Parameter Count | `function-level test` | Functional |
| 180 | L833 | expected positive loss | TPS: Loss Estimation & Perplexity | `loss > 0` | Functional |
| 181 | L838 | expected larger model ≤ loss | TPS: Loss Estimation & Perplexity | `loss_small >= loss_large` | Functional |
| 182 | L841 | expected >= E | TPS: Loss Estimation & Perplexity | `loss >= TPS_CHINCHILLA_E` | Functional |
| 183 | L844 | expected E | TPS: Loss Estimation & Perplexity | `tps_estimate_loss(0, 300) == TPS_CHINCHILLA_E` | Functional |
| 184 | L848 | expected positive PPL | TPS: Loss Estimation & Perplexity | `ppl > 0` | Functional |
| 185 | L853 | expected higher loss → higher PPL | TPS: Loss Estimation & Perplexity | `ppl_high >= ppl_low` | Functional |
| 186 | L856 | expected 100 | TPS: Loss Estimation & Perplexity | `tps_loss_to_ppl(0) == 100` | Functional |
| 187 | L859 | test_tps_memory_bandwidth | TPS: Loss Estimation & Perplexity | `function-level test` | Memory |
| 188 | L864 | expected ~19 | TPS: Memory & Bandwidth Savings | `mem >= 18 && mem <= 20` | Functional |
| 189 | L868 | expected 200 | TPS: Memory & Bandwidth Savings | `mem == 200` | Functional |
| 190 | L873 | expected ~10x savings | TPS: Memory & Bandwidth Savings | `mem_f / mem_t >= 9` | Functional |
| 191 | L877 | expected ~10.1x | TPS: Memory & Bandwidth Savings | `saving >= 10000 && saving <= 11000` | Functional |
| 192 | L880 | expected 1000 | TPS: Memory & Bandwidth Savings | `tps_bandwidth_saving(TPS_BITS_PER_FLOAT) == 1000` | Functional |
| 193 | L883 | expected 0 | TPS: Memory & Bandwidth Savings | `tps_estimate_memory(0, TPS_BITS_PER_TERNARY) == 0` | Functional |
| 194 | L886 | test_tps_configs | TPS: Memory & Bandwidth Savings | `function-level test` | Initialization |
| 195 | L893 | expected 0 | TPS: Configuration & Spectra Suite | `idx == 0` | Functional |
| 196 | L896 | expected loss > 0 | TPS: Configuration & Spectra Suite | `st.configs[0].estimated_loss > 0` | Functional |
| 197 | L899 | expected PPL > 0 | TPS: Configuration & Spectra Suite | `st.configs[0].estimated_ppl > 0` | Functional |
| 198 | L902 | expected memory > 0 | TPS: Configuration & Spectra Suite | `st.configs[0].memory_mb > 0` | Memory |
| 199 | L905 | expected FLOPs > 0 | TPS: Configuration & Spectra Suite | `st.configs[0].flops > 0` | Functional |
| 200 | L909 | expected 1 | TPS: Configuration & Spectra Suite | `idx2 == 1` | Functional |
| 201 | L920 | expected 2 | TPS: Configuration & Spectra Suite | `st.config_count == 2` | Functional |
| 202 | L923 | expected -1 | TPS: Configuration & Spectra Suite | `tps_add_config(&st, 0, 300, TPS_BITS_PER_TERNARY) == -1` | Functional |
| 203 | L926 | expected -1 | TPS: Configuration & Spectra Suite | `tps_add_config(NULL, 100, 300, TPS_BITS_PER_TERNARY) == -1` | Functional |
| 204 | L929 | test_tps_crossover_flops | TPS: Configuration & Spectra Suite | `function-level test` | Functional |
| 205 | L936 | expected positive crossover | TPS: Crossover & FLOPs | `cross > 0` | Functional |
| 206 | L939 | expected stored | TPS: Crossover & FLOPs | `st.crossover_params_m > 0` | Functional |
| 207 | L942 | expected 0 | TPS: Crossover & FLOPs | `tps_find_crossover(NULL, 300) == 0` | Functional |
| 208 | L946 | expected positive FLOPs | TPS: Crossover & FLOPs | `flops > 0` | Functional |
| 209 | L950 | expected more FLOPs | TPS: Crossover & FLOPs | `flops_big > flops` | Functional |
| 210 | L953 | expected 0 | TPS: Crossover & FLOPs | `tps_estimate_flops(0, 300) == 0` | Functional |
| 211 | L958 | expected MAC-free 1/3 | TPS: Crossover & FLOPs | `flops == expected` | Memory |
| 212 | L961 | expected 16 | TPS: Crossover & FLOPs | `TPS_MAX_CONFIGS == 16` | Functional |
| 213 | L964 | expected 340 | TPS: Crossover & FLOPs | `TPS_CHINCHILLA_ALPHA == 340` | Functional |
| 214 | L967 | expected 280 | TPS: Crossover & FLOPs | `TPS_CHINCHILLA_BETA == 280` | Functional |
| 215 | L970 | expected 1000 | TPS: Crossover & FLOPs | `TPS_FP_SCALE == 1000` | Functional |
| 216 | L973 | expected 197 | TPS: Crossover & FLOPs | `TPS_SPECTRA_197M == 197` | Functional |
| 217 | L976 | expected 394 | TPS: Crossover & FLOPs | `TPS_SPECTRA_394M == 394` | Functional |
| 218 | L979 | expected 830 | TPS: Crossover & FLOPs | `TPS_SPECTRA_830M == 830` | Functional |
| 219 | L982 | expected 1700 | TPS: Crossover & FLOPs | `TPS_SPECTRA_1B7 == 1700` | Functional |
| 220 | L985 | expected 0 | TPS: Crossover & FLOPs | `tps_bandwidth_saving(0) == 0` | Functional |

---

## Suite 31: Paper2-Derived Modules

**Source**: `tests/test_papers2.c`
**Runtime Assertions**: 200
**Source-Level Entries**: 216
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L61 | test_smi_init | Test Harness | `function-level test` | Initialization |
| 2 | L66 | expected 0 | SMI: Initialization & Constants | `smi_init(&st) == 0` | Functional |
| 3 | L69 | expected 1 | SMI: Initialization & Constants | `st.initialized == 1` | Functional |
| 4 | L72 | expected -1 | SMI: Initialization & Constants | `smi_init(NULL) == -1` | Functional |
| 5 | L75 | expected 0 | SMI: Initialization & Constants | `st.layer_count == 0` | Functional |
| 6 | L78 | expected 0 | SMI: Initialization & Constants | `st.avg_mi == 0` | Functional |
| 7 | L81 | expected 0 | SMI: Initialization & Constants | `st.total_info_bits == 0` | Functional |
| 8 | L84 | expected 1585 | SMI: Initialization & Constants | `SMI_INFO_PER_TRIT == 1585` | Functional |
| 9 | L87 | expected 1443 | SMI: Initialization & Constants | `SMI_LOG2_E_X1000 == 1443` | Functional |
| 10 | L90 | expected 64 | SMI: Initialization & Constants | `SMI_MAX_BINS == 64` | Functional |
| 11 | L93 | expected 32 | SMI: Initialization & Constants | `SMI_MAX_LAYERS == 32` | Functional |
| 12 | L96 | test_smi_shannon_entropy | SMI: Initialization & Constants | `function-level test` | Functional |
| 13 | L103 | expected ~1585 | SMI: Shannon Entropy | `h >= 1400 && h <= 1700` | Functional |
| 14 | L108 | expected 0 | SMI: Shannon Entropy | `h == 0` | Functional |
| 15 | L113 | expected 0 | SMI: Shannon Entropy | `h == 0` | Functional |
| 16 | L118 | expected 0 | SMI: Shannon Entropy | `h == 0` | Functional |
| 17 | L123 | expected ~1000 | SMI: Shannon Entropy | `h >= 900 && h <= 1100` | Functional |
| 18 | L128 | expected 0 < H < 1000 | SMI: Shannon Entropy | `h > 0 && h < 1000` | Functional |
| 19 | L133 | expected 0 < H < 1585 | SMI: Shannon Entropy | `h > 0 && h < 1585` | Functional |
| 20 | L138 | expected H < 200 | SMI: Shannon Entropy | `h >= 0 && h < 200` | Functional |
| 21 | L141 | test_smi_differential_entropy | SMI: Shannon Entropy | `function-level test` | Functional |
| 22 | L148 | expected ~2047 | SMI: Differential Entropy | `h >= 1800 && h <= 2300` | Functional |
| 23 | L153 | expected H < 2100 | SMI: Differential Entropy | `h < 2100` | Functional |
| 24 | L158 | expected H > 1800 | SMI: Differential Entropy | `h > 1800` | Functional |
| 25 | L161 | test_smi_histogram | SMI: Differential Entropy | `function-level test` | Functional |
| 26 | L167 | expected 0 | SMI: Histogram & Histogram Entropy | `smi_build_histogram(&hist, weights, 10, 4) == 0` | Functional |
| 27 | L170 | expected 10 | SMI: Histogram & Histogram Entropy | `hist.total == 10` | Functional |
| 28 | L173 | expected 4 | SMI: Histogram & Histogram Entropy | `hist.num_bins == 4` | Functional |
| 29 | L177 | expected > 0 | SMI: Histogram & Histogram Entropy | `he > 0` | Functional |
| 30 | L180 | expected -1 | SMI: Histogram & Histogram Entropy | `smi_build_histogram(NULL, weights, 10, 4) == -1` | Functional |
| 31 | L183 | expected -1 | SMI: Histogram & Histogram Entropy | `smi_build_histogram(&hist, NULL, 10, 4) == -1` | Functional |
| 32 | L186 | test_smi_mi_and_alignment | SMI: Histogram & Histogram Entropy | `function-level test` | Functional |
| 33 | L197 | expected >= 0 | SMI: MI Estimation & Feature Alignment | `idx >= 0` | Functional |
| 34 | L200 | expected >= 0 | SMI: MI Estimation & Feature Alignment | `st.layers[idx].mutual_info >= 0` | Functional |
| 35 | L208 | expected >= 0 | SMI: MI Estimation & Feature Alignment | `idx2 >= 0` | Functional |
| 36 | L211 | expected 2 | SMI: MI Estimation & Feature Alignment | `st.layer_count == 2` | Functional |
| 37 | L216 | expected >= 0 | SMI: MI Estimation & Feature Alignment | `align >= 0` | Functional |
| 38 | L219 | expected > 500 | SMI: MI Estimation & Feature Alignment | `align > 500` | Functional |
| 39 | L224 | expected lower or non-negative | SMI: MI Estimation & Feature Alignment | `align2 < align ∣∣ align2 >= 0` | Negative/error |
| 40 | L227 | test_smi_graded_truth | SMI: MI Estimation & Feature Alignment | `function-level test` | Functional |
| 41 | L232 | expected 1000 | SMI: Graded Truth & Info Sufficiency | `smi_graded_truth(1000, 1000) == 1000` | Functional |
| 42 | L236 | expected 0 | SMI: Graded Truth & Info Sufficiency | `smi_graded_truth(0, 1000) == 0` | Functional |
| 43 | L241 | expected ~500 | SMI: Graded Truth & Info Sufficiency | `g >= 400 && g <= 600` | Functional |
| 44 | L245 | expected 1 | SMI: Graded Truth & Info Sufficiency | `smi_info_sufficient(3900, 5000) == 1` | Functional |
| 45 | L249 | expected 0 | SMI: Graded Truth & Info Sufficiency | `smi_info_sufficient(10, 5000) == 0` | Functional |
| 46 | L255 | expected 500 | SMI: Graded Truth & Info Sufficiency | `ib == 500` | Functional |
| 47 | L260 | expected 200 | SMI: Graded Truth & Info Sufficiency | `ib2 == 200` | Functional |
| 48 | L268 | test_chi_init | SMI: Graded Truth & Info Sufficiency | `function-level test` | Initialization |
| 49 | L273 | expected 0 | CHI: Initialization & Constants | `chi_init(&st) == 0` | Functional |
| 50 | L276 | expected 1 | CHI: Initialization & Constants | `st.initialized == 1` | Functional |
| 51 | L279 | expected -1 | CHI: Initialization & Constants | `chi_init(NULL) == -1` | Functional |
| 52 | L282 | expected 0 | CHI: Initialization & Constants | `st.phase_count == 0` | Functional |
| 53 | L285 | expected 0 | CHI: Initialization & Constants | `st.spectra_count == 0` | Functional |
| 54 | L288 | expected 185000 | CHI: Initialization & Constants | `CHI_TRILM_A == 185000` | Functional |
| 55 | L291 | expected 260 | CHI: Initialization & Constants | `CHI_TRILM_ALPHA == 260` | Functional |
| 56 | L294 | expected 1760 | CHI: Initialization & Constants | `CHI_TRILM_EPS == 1760` | Functional |
| 57 | L297 | expected 159000 | CHI: Initialization & Constants | `CHI_FLOAT_A == 159000` | Functional |
| 58 | L300 | expected 1670 | CHI: Initialization & Constants | `CHI_FLOAT_EPS == 1670` | Functional |
| 59 | L303 | test_chi_scaling_laws | CHI: Initialization & Constants | `function-level test` | Functional |
| 60 | L312 | expected monotonic decrease | CHI: Scaling Laws (TriLM vs FloatLM) | `tl_100 > tl_1000` | Functional |
| 61 | L315 | expected monotonic decrease | CHI: Scaling Laws (TriLM vs FloatLM) | `tl_1000 > tl_3900` | Functional |
| 62 | L319 | expected near 1760 | CHI: Scaling Laws (TriLM vs FloatLM) | `tl_3900 >= 1760 && tl_3900 < 2500` | Functional |
| 63 | L327 | expected monotonic decrease | CHI: Scaling Laws (TriLM vs FloatLM) | `fl_100 > fl_1000` | Functional |
| 64 | L330 | expected monotonic decrease | CHI: Scaling Laws (TriLM vs FloatLM) | `fl_1000 > fl_3900` | Functional |
| 65 | L333 | expected near 1670 | CHI: Scaling Laws (TriLM vs FloatLM) | `fl_3900 >= 1670 && fl_3900 < 2500` | Functional |
| 66 | L340 | expected gap narrows | CHI: Scaling Laws (TriLM vs FloatLM) | `gap_100 > gap_3900` | Functional |
| 67 | L343 | expected < 300 (gap converges to ~90) | CHI: Scaling Laws (TriLM vs FloatLM) | `gap_3900 < 300` | Functional |
| 68 | L347 | TriLM >= FloatLM | CHI: Scaling Laws (TriLM vs FloatLM) | `tl_100 >= fl_100` | Functional |
| 69 | L350 | TriLM >= FloatLM | CHI: Scaling Laws (TriLM vs FloatLM) | `tl_3900 >= fl_3900` | Functional |
| 70 | L353 | test_chi_schedule | CHI: Scaling Laws (TriLM vs FloatLM) | `function-level test` | Scheduling |
| 71 | L360 | expected 3 phases | CHI: Training Schedule (3-phase) | `np == 3` | Functional |
| 72 | L363 | expected 3 | CHI: Training Schedule (3-phase) | `st.phase_count == 3` | Functional |
| 73 | L366 | expected 0 | CHI: Training Schedule (3-phase) | `st.schedule[0].start_step == 0` | Functional |
| 74 | L369 | expected 1 | CHI: Training Schedule (3-phase) | `st.schedule[0].weight_decay == 1` | Functional |
| 75 | L372 | expected 1 | CHI: Training Schedule (3-phase) | `st.schedule[1].weight_decay == 1` | Functional |
| 76 | L375 | expected 0 | CHI: Training Schedule (3-phase) | `st.schedule[2].weight_decay == 0` | Functional |
| 77 | L380 | expected >= 0 | CHI: Training Schedule (3-phase) | `lr0 >= 0` | Functional |
| 78 | L384 | expected LR increased after warmup | CHI: Training Schedule (3-phase) | `lr_warm > lr0` | Functional |
| 79 | L388 | expected 1 | CHI: Training Schedule (3-phase) | `chi_weight_decay_active(&st, 1) == 1` | Functional |
| 80 | L392 | expected 0 | CHI: Training Schedule (3-phase) | `chi_weight_decay_active(&st, late_step) == 0` | Functional |
| 81 | L400 | expected >= 0 | CHI: Training Schedule (3-phase) | `dlt_lr >= 0` | Functional |
| 82 | L407 | test_chi_spectra | CHI: Training Schedule (3-phase) | `function-level test` | Functional |
| 83 | L413 | expected 0 | CHI: Spectra Suite (9 configurations) | `chi_populate_spectra(&st) == 0` | Functional |
| 84 | L416 | expected 9 | CHI: Spectra Suite (9 configurations) | `st.spectra_count == 9` | Functional |
| 85 | L419 | expected 99 | CHI: Spectra Suite (9 configurations) | `st.spectra[0].params_m == 99` | Functional |
| 86 | L422 | expected 3900 | CHI: Spectra Suite (9 configurations) | `st.spectra[8].params_m == 3900` | Functional |
| 87 | L429 | expected monotonic increase | CHI: Spectra Suite (9 configurations) | `mono == 1` | Functional |
| 88 | L436 | expected > 0 | CHI: Spectra Suite (9 configurations) | `st.spectra[0].hidden_dim > 0` | Functional |
| 89 | L439 | expected > 0 | CHI: Spectra Suite (9 configurations) | `st.spectra[0].layers > 0` | Functional |
| 90 | L448 | expected > 0 params_m | CHI: Spectra Suite (9 configurations) | `conv > 0` | Functional |
| 91 | L456 | test_ppl_init | CHI: Spectra Suite (9 configurations) | `function-level test` | Initialization |
| 92 | L461 | expected 0 | PPL: Initialization & Constants | `ppl_init(&st) == 0` | Functional |
| 93 | L464 | expected 1 | PPL: Initialization & Constants | `st.initialized == 1` | Functional |
| 94 | L467 | expected -1 | PPL: Initialization & Constants | `ppl_init(NULL) == -1` | Functional |
| 95 | L470 | expected 0 | PPL: Initialization & Constants | `st.model_count == 0` | Functional |
| 96 | L473 | expected 0 | PPL: Initialization & Constants | `st.result_count == 0` | Functional |
| 97 | L476 | expected 6100 | PPL: Initialization & Constants | `PPL_REF_FP16_WIKI == 6100` | Functional |
| 98 | L479 | expected 11220 | PPL: Initialization & Constants | `PPL_REF_DLT_OFF_WIKI == 11220` | Functional |
| 99 | L482 | expected 6300 | PPL: Initialization & Constants | `PPL_REF_TRILM_LAMBADA == 6300` | Functional |
| 100 | L485 | expected 6700 | PPL: Initialization & Constants | `PPL_REF_FLOAT_LAMBADA == 6700` | Functional |
| 101 | L488 | expected 4 | PPL: Initialization & Constants | `PPL_NUM_DATASETS == 4` | Functional |
| 102 | L491 | test_ppl_math | PPL: Initialization & Constants | `function-level test` | Functional |
| 103 | L497 | expected ~2718 | PPL: Math Primitives | `ppl1 >= 2500 && ppl1 <= 2900` | Functional |
| 104 | L502 | expected 1000 | PPL: Math Primitives | `ppl0 == 1000` | Functional |
| 105 | L507 | expected ~7389 | PPL: Math Primitives | `ppl2 >= 6800 && ppl2 <= 7800` | Functional |
| 106 | L512 | expected 693 | PPL: Math Primitives | `ce == 693` | Functional |
| 107 | L516 | expected 1386 | PPL: Math Primitives | `ce2 == 1386` | Functional |
| 108 | L521 | expected ~1839 | PPL: Math Primitives | `ratio1 >= 1700 && ratio1 <= 1950` | Functional |
| 109 | L526 | expected 1000 | PPL: Math Primitives | `ratio_same == 1000` | Functional |
| 110 | L529 | test_ppl_evaluation | PPL: Math Primitives | `function-level test` | Hardware/ALU |
| 111 | L537 | expected 0 | PPL: Model Registration & Evaluatio | `fp16 == 0` | Functional |
| 112 | L542 | expected 1 | PPL: Model Registration & Evaluatio | `dlt == 1` | Functional |
| 113 | L556 | expected 0 | PPL: Model Registration & Evaluatio | `ppl_evaluate(&st, fp16, PPL_DATASET_WIKITEXT2, &r_fp16) == 0` | Functional |
| 114 | L559 | expected 6100 | PPL: Model Registration & Evaluatio | `r_fp16.ppl_x1000 == PPL_REF_FP16_WIKI` | Functional |
| 115 | L562 | expected 0 | PPL: Model Registration & Evaluatio | `ppl_evaluate(&st, dlt, PPL_DATASET_WIKITEXT2, &r_dlt) == 0` | Functional |
| 116 | L565 | expected 11220 | PPL: Model Registration & Evaluatio | `r_dlt.ppl_x1000 == PPL_REF_DLT_OFF_WIKI` | Functional |
| 117 | L569 | expected 5120 | PPL: Model Registration & Evaluatio | `r_dlt.gap_to_fp16_x1000 == 5120` | Functional |
| 118 | L573 | expected 1 | PPL: Model Registration & Evaluatio | `ppl_gap_acceptable(5120) == 1` | Functional |
| 119 | L576 | expected 0 | PPL: Model Registration & Evaluatio | `ppl_gap_acceptable(9000) == 0` | Functional |
| 120 | L580 | expected 2 | PPL: Model Registration & Evaluatio | `st.result_count == 2` | Functional |
| 121 | L583 | test_ppl_trilm_achievement | PPL: Model Registration & Evaluatio | `function-level test` | Functional |
| 122 | L598 | expected 6300 | PPL: TriLM Beats Float (LAMBADA achievement) | `r_tri.ppl_x1000 == 6300` | Functional |
| 123 | L602 | expected 6700 | PPL: TriLM Beats Float (LAMBADA achievement) | `r_flt.ppl_x1000 == 6700` | Functional |
| 124 | L605 | expected 1 (remarkable!) | PPL: TriLM Beats Float (LAMBADA achievement) | `ppl_ternary_beats_float(6300, 6700) == 1` | Functional |
| 125 | L608 | expected 0 | PPL: TriLM Beats Float (LAMBADA achievement) | `ppl_ternary_beats_float(11220, 6100) == 0` | Functional |
| 126 | L611 | expected 6300 | PPL: TriLM Beats Float (LAMBADA achievement) | `ppl_best_ternary(&st, PPL_DATASET_LAMBADA) == 6300` | Functional |
| 127 | L614 | expected -1 | PPL: TriLM Beats Float (LAMBADA achievement) | `ppl_best_ternary(&st, PPL_DATASET_WIKITEXT2) == -1` | Functional |
| 128 | L618 | expected -1 | PPL: TriLM Beats Float (LAMBADA achievement) | `ppl_add_model(&st, -1, 100, 1000) == -1` | Functional |
| 129 | L621 | expected -1 | PPL: TriLM Beats Float (LAMBADA achievement) | `ppl_set_reference(&st, 99, 0, 1000) == -1` | Functional |
| 130 | L625 | expected -1 | PPL: TriLM Beats Float (LAMBADA achievement) | `ppl_evaluate(&st, 0, 99, &r) == -1` | Functional |
| 131 | L633 | test_olh_init | PPL: TriLM Beats Float (LAMBADA achievement) | `function-level test` | Initialization |
| 132 | L638 | expected 0 | OLH: Initialization & Constants | `olh_init(&st, 4, OLH_MODE_SHIFT_SCALE) == 0` | Functional |
| 133 | L641 | expected 1 | OLH: Initialization & Constants | `st.initialized == 1` | Functional |
| 134 | L644 | expected -1 | OLH: Initialization & Constants | `olh_init(NULL, 4, OLH_MODE_CLAMP) == -1` | Functional |
| 135 | L647 | expected -1 | OLH: Initialization & Constants | `olh_init(&st, 0, OLH_MODE_CLAMP) == -1` | Functional |
| 136 | L650 | expected -1 | OLH: Initialization & Constants | `olh_init(&st, OLH_MAX_CHANNELS + 1, OLH_MODE_CLAMP) == -1` | Functional |
| 137 | L653 | expected -1 | OLH: Initialization & Constants | `olh_init(&st, 4, 99) == -1` | Functional |
| 138 | L657 | expected 8 | OLH: Initialization & Constants | `st.num_channels == 8` | Functional |
| 139 | L660 | expected 3000 | OLH: Initialization & Constants | `st.sigma_threshold_x1000 == OLH_SIGMA_THRESHOLD` | Functional |
| 140 | L663 | expected 9841 | OLH: Initialization & Constants | `OLH_TRIT_RANGE_MAX == 9841` | Functional |
| 141 | L666 | expected 700 | OLH: Initialization & Constants | `OLH_DLT_THRESHOLD_K == 700` | Functional |
| 142 | L669 | test_olh_clamp | OLH: Initialization & Constants | `function-level test` | Boundary |
| 143 | L673 | expected 0 | OLH: Clamping & DLT Threshold | `olh_clamp_trit(0) == 0` | Functional |
| 144 | L676 | expected 9841 | OLH: Clamping & DLT Threshold | `olh_clamp_trit(9841) == 9841` | Functional |
| 145 | L679 | expected -9841 | OLH: Clamping & DLT Threshold | `olh_clamp_trit(-9841) == -9841` | Functional |
| 146 | L682 | expected 9841 (clamped) | OLH: Clamping & DLT Threshold | `olh_clamp_trit(20000) == 9841` | Boundary |
| 147 | L685 | expected -9841 (clamped) | OLH: Clamping & DLT Threshold | `olh_clamp_trit(-20000) == -9841` | Boundary |
| 148 | L688 | expected 5000 | OLH: Clamping & DLT Threshold | `olh_clamp_trit(5000) == 5000` | Functional |
| 149 | L692 | Δ = 0.7 × 1000 | OLH: Clamping & DLT Threshold | `olh_dlt_threshold(1000) == 700` | Functional |
| 150 | L695 | Δ = 0.7 × 2000 | OLH: Clamping & DLT Threshold | `olh_dlt_threshold(2000) == 1400` | Functional |
| 151 | L698 | Δ = 0.7 × 0 | OLH: Clamping & DLT Threshold | `olh_dlt_threshold(0) == 0` | Functional |
| 152 | L701 | test_olh_stats | OLH: Clamping & DLT Threshold | `function-level test` | Functional |
| 153 | L711 | expected >= 0 | OLH: Statistics & Outlier Detectio | `out >= 0` | Functional |
| 154 | L714 | expected 10 | OLH: Statistics & Outlier Detectio | `st.total_samples == 10` | Functional |
| 155 | L721 | expected >= 0 | OLH: Statistics & Outlier Detectio | `out2 >= 0` | Functional |
| 156 | L724 | expected 20 | OLH: Statistics & Outlier Detectio | `st.total_samples == 20` | Functional |
| 157 | L729 | expected >= 0 | OLH: Statistics & Outlier Detectio | `rate >= 0` | Functional |
| 158 | L733 | expected -1 | OLH: Statistics & Outlier Detectio | `olh_update_stats(NULL, 0, normal_vals, 10) == -1` | Functional |
| 159 | L736 | expected -1 | OLH: Statistics & Outlier Detectio | `olh_update_stats(&st, 0, NULL, 10) == -1` | Functional |
| 160 | L739 | expected -1 | OLH: Statistics & Outlier Detectio | `olh_update_stats(&st, 99, normal_vals, 10) == -1` | Functional |
| 161 | L742 | test_olh_rescale | OLH: Statistics & Outlier Detectio | `function-level test` | Functional |
| 162 | L752 | expected 0 | OLH: Rescaling & Info Loss | `olh_compute_rescale(&st, 0, &params) == 0` | Functional |
| 163 | L755 | expected SHIFT_SCALE | OLH: Rescaling & Info Loss | `params.mode == OLH_MODE_SHIFT_SCALE` | Functional |
| 164 | L758 | expected > 0 | OLH: Rescaling & Info Loss | `params.scale_x1000 > 0` | Functional |
| 165 | L761 | expected > 0 | OLH: Rescaling & Info Loss | `params.dlt_delta > 0` | Functional |
| 166 | L771 | expected near 0 | OLH: Rescaling & Info Loss | `rescaled_zero >= -5000 && rescaled_zero <= 5000` | Functional |
| 167 | L777 | expected 0 | OLH: Rescaling & Info Loss | `olh_info_loss(orig, resc, 5) == 0` | Functional |
| 168 | L782 | expected > 0 | OLH: Rescaling & Info Loss | `loss > 0` | Functional |
| 169 | L786 | expected 0 (ok) | OLH: Rescaling & Info Loss | `olh_info_loss_status(&st) == 0` | Functional |
| 170 | L790 | expected -1 | OLH: Rescaling & Info Loss | `olh_info_loss(NULL, resc, 5) == -1` | Functional |
| 171 | L793 | expected -1 | OLH: Rescaling & Info Loss | `olh_info_loss(orig, resc, 0) == -1` | Functional |
| 172 | L796 | test_olh_stall_recal | OLH: Rescaling & Info Loss | `function-level test` | Functional |
| 173 | L806 | expected 0 | OLH: Pipeline Stall Recalibratio | `olh_compute_rescale(&st, 0, &params) == 0` | Functional |
| 174 | L809 | expected 4 | OLH: Pipeline Stall Recalibratio | `params.stalls_injected == OLH_RECAL_CYCLES` | Functional |
| 175 | L812 | expected 4 | OLH: Pipeline Stall Recalibratio | `st.total_stalls == OLH_RECAL_CYCLES` | Functional |
| 176 | L815 | expected 0 (normal) | OLH: Pipeline Stall Recalibratio | `olh_is_outlier(&st, 0, 100) == 0` | Logic |
| 177 | L818 | expected -1 | OLH: Pipeline Stall Recalibratio | `olh_is_outlier(NULL, 0, 100) == -1` | Functional |
| 178 | L826 | test_smi_extras | OLH: Pipeline Stall Recalibratio | `function-level test` | Functional |
| 179 | L834 | expected ~1000 | SMI: Extended Coverage | `h2 >= 900 && h2 <= 1100` | Functional |
| 180 | L840 | expected uniform > skewed | SMI: Extended Coverage | `h_unif > h_skew` | Functional |
| 181 | L848 | expected 0 | SMI: Extended Coverage | `hconst == 0` | Functional |
| 182 | L852 | expected 1000 | SMI: Extended Coverage | `smi_graded_truth(2000, 1000) == 1000` | Functional |
| 183 | L856 | expected 0 | SMI: Extended Coverage | `smi_graded_truth(-500, 1000) == 0` | Functional |
| 184 | L860 | expected 1 | SMI: Extended Coverage | `smi_info_sufficient(3155, 5000) == 1` | Functional |
| 185 | L864 | expected 500 | SMI: Extended Coverage | `smi_info_bottleneck(500, 300, 0) == 500` | Functional |
| 186 | L869 | expected -1 | SMI: Extended Coverage | `smi_estimate_mi(NULL, xs, xs, 4) == -1` | Functional |
| 187 | L873 | expected -1 | SMI: Extended Coverage | `smi_feature_alignment(NULL, xs, xs, 4) == -1` | Functional |
| 188 | L877 | test_chi_extras | SMI: Extended Coverage | `function-level test` | Functional |
| 189 | L884 | expected 500M < 100M | CHI: Extended Coverage | `chi_trilm_loss(500) < chi_trilm_loss(100)` | Functional |
| 190 | L887 | expected 500M < 100M | CHI: Extended Coverage | `chi_float_loss(500) < chi_float_loss(100)` | Functional |
| 191 | L891 | expected ≥ 1760 | CHI: Extended Coverage | `chi_trilm_loss(3900) >= CHI_TRILM_EPS` | Functional |
| 192 | L894 | expected ≥ 1670 | CHI: Extended Coverage | `chi_float_loss(3900) >= CHI_FLOAT_EPS` | Functional |
| 193 | L898 | expected > 0 | CHI: Extended Coverage | `chi_loss_gap(500) > 0` | Functional |
| 194 | L908 | expected < peak | CHI: Extended Coverage | `lr_first >= 0 && lr_first < CHI_LR_3B9_PEAK` | Functional |
| 195 | L914 | expected tight ≥ loose | CHI: Extended Coverage | `tight >= loose` | Functional |
| 196 | L919 | expected > 0 | CHI: Extended Coverage | `st.spectra[4].params_m > 0` | Functional |
| 197 | L923 | test_ppl_extras | CHI: Extended Coverage | `function-level test` | Functional |
| 198 | L932 | expected exp(2) > exp(1) | PPL: Extended Coverage | `p2 > p1` | Functional |
| 199 | L938 | expected 3× > 1× | PPL: Extended Coverage | `ce3 > ce1` | Functional |
| 200 | L943 | expected < 1000 (better model) | PPL: Extended Coverage | `inv < 1000` | Functional |
| 201 | L947 | expected 1000 | PPL: Extended Coverage | `ppl_from_cross_entropy(-1000) == 1000` | Functional |
| 202 | L955 | expected 4 | PPL: Extended Coverage | `st.model_count == 4` | Functional |
| 203 | L959 | expected 9200 | PPL: Extended Coverage | `PPL_REF_FP16_C4 == 9200` | Functional |
| 204 | L962 | expected 13380 | PPL: Extended Coverage | `PPL_REF_DLT_OFF_C4 == 13380` | Functional |
| 205 | L965 | expected 16290 | PPL: Extended Coverage | `PPL_REF_DLT_OFF_PTB == 16290` | Functional |
| 206 | L968 | expected 3000 | PPL: Extended Coverage | `PPL_EXCELLENT_GAP == 3000` | Functional |
| 207 | L972 | test_olh_extras | PPL: Extended Coverage | `function-level test` | Functional |
| 208 | L985 | expected CLAMP | OLH: Extended Coverage | `params.mode == OLH_MODE_CLAMP` | Boundary |
| 209 | L988 | expected 0 | OLH: Extended Coverage | `params.stalls_injected == 0` | Functional |
| 210 | L993 | expected in range | OLH: Extended Coverage | `clamped >= -9841 && clamped <= 9841` | Boundary |
| 211 | L998 | expected >= 0 | OLH: Extended Coverage | `olh_update_stats(&st, 1, ch2_vals, 5) >= 0` | Functional |
| 212 | L1001 | expected >= 0 | OLH: Extended Coverage | `olh_update_stats(&st, 2, ch2_vals, 5) >= 0` | Functional |
| 213 | L1004 | expected 18 | OLH: Extended Coverage | `st.total_samples == 18` | Functional |
| 214 | L1008 | expected 4 | OLH: Extended Coverage | `OLH_RECAL_CYCLES == 4` | Functional |
| 215 | L1012 | expected 100 | OLH: Extended Coverage | `OLH_INFO_LOSS_WARN == 100` | Functional |
| 216 | L1015 | expected 250 | OLH: Extended Coverage | `OLH_INFO_LOSS_CRIT == 250` | Functional |

---

## Suite 32: DLT + CNTFET

**Source**: `tests/test_dlt_cntfet.c`
**Runtime Assertions**: 107
**Source-Level Entries**: 100
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

> **Note**: 7 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L56 | test_dlt_expansion | Section 1: DLT Tequila Expansion (20 tests) | `function-level test` | Functional |
| 2 | L63 | init failed | Section 1: DLT Tequila Expansion (20 tests) | `dlt_init(&dlt) == 0` | Negative/error |
| 3 | L67 | add_layer failed | Section 1: DLT Tequila Expansion (20 tests) | `layer == 0` | Negative/error |
| 4 | L71 | sp not 0 | Section 1: DLT Tequila Expansion (20 tests) | `dlt.layers[0].sp == 0` | Logic |
| 5 | L74 | sn not 0 | Section 1: DLT Tequila Expansion (20 tests) | `dlt.layers[0].sn == 0` | Logic |
| 6 | L81 | asymmetric failed | Section 1: DLT Tequila Expansion (20 tests) | `dlt_compute_asymmetric(&dlt, 0, weights, count) == 0` | Negative/error |
| 7 | L84 | delta_p should be positive | Section 1: DLT Tequila Expansion (20 tests) | `dlt.layers[0].delta_p > 0` | Functional |
| 8 | L87 | delta_n should be positive | Section 1: DLT Tequila Expansion (20 tests) | `dlt.layers[0].delta_n > 0` | Functional |
| 9 | L98 | quantize failed | Section 1: DLT Tequila Expansion (20 tests) | `dlt_quantize(&dlt, 0, weights, out, count) == 0` | Negative/error |
| 10 | L104 | ste_gradient failed | Section 1: DLT Tequila Expansion (20 tests) | `passthrough >= 0` | Negative/error |
| 11 | L110 | should detect trapped weights | Section 1: DLT Tequila Expansion (20 tests) | `trapped > 0` | Functional |
| 12 | L115 | trapping rate negative | Section 1: DLT Tequila Expansion (20 tests) | `trap_rate >= 0` | Negative/error |
| 13 | L127 | reactivate failed | Section 1: DLT Tequila Expansion (20 tests) | `freed >= 0` | Negative/error |
| 14 | L131 | wp should not increase | Section 1: DLT Tequila Expansion (20 tests) | `dlt.layers[0].wp <= 500` | Logic |
| 15 | L135 | should reject NULL | Section 1: DLT Tequila Expansion (20 tests) | `dlt_compute_asymmetric(NULL, 0, weights, count) == -1` | Negative/error |
| 16 | L138 | should return 0 | Section 1: DLT Tequila Expansion (20 tests) | `dlt_ste_gradient(NULL, 0, weights, grads, count) == 0` | Functional |
| 17 | L141 | should reject NULL | Section 1: DLT Tequila Expansion (20 tests) | `dlt_reactivate(NULL, 0, weights, count) == -1` | Negative/error |
| 18 | L144 | should return 0 | Section 1: DLT Tequila Expansion (20 tests) | `dlt_get_trapping_rate(&dlt, 99) == 0` | Functional |
| 19 | L152 | reactivated should be non-negative | Section 1: DLT Tequila Expansion (20 tests) | `dlt.layers[0].reactivated >= 0` | Negative/error |
| 20 | L157 | test_cntfet_emulation | Section 2: CNTFET Emulation (30 tests) | `function-level test` | Arithmetic |
| 21 | L163 | init failed | Section 2: CNTFET Emulation (30 tests) | `cntfet_init(&cst) == 0` | Negative/error |
| 22 | L166 | should reject NULL | Section 2: CNTFET Emulation (30 tests) | `cntfet_init(NULL) == -1` | Negative/error |
| 23 | L171 | add LVT failed | Section 2: CNTFET Emulation (30 tests) | `d0 == 0` | Negative/error |
| 24 | L176 | add MVT failed | Section 2: CNTFET Emulation (30 tests) | `d1 == 1` | Negative/error |
| 25 | L181 | add HVT failed | Section 2: CNTFET Emulation (30 tests) | `d2 == 2` | Negative/error |
| 26 | L185 | LVT V_TH wrong | Section 2: CNTFET Emulation (30 tests) | `cntfet_compute_vth(CNTFET_DIAM_LVT, 10, 0) == 200` | Functional |
| 27 | L188 | MVT V_TH wrong | Section 2: CNTFET Emulation (30 tests) | `cntfet_compute_vth(CNTFET_DIAM_MVT, 12, 0) == 300` | Functional |
| 28 | L191 | HVT V_TH wrong | Section 2: CNTFET Emulation (30 tests) | `cntfet_compute_vth(CNTFET_DIAM_HVT, 14, 0) == 400` | Functional |
| 29 | L195 | stored V_TH wrong | Section 2: CNTFET Emulation (30 tests) | `cst.devices[0].vth_mv == 200` | Functional |
| 30 | L198 | stored V_TH wrong | Section 2: CNTFET Emulation (30 tests) | `cst.devices[1].vth_mv == 300` | Functional |
| 31 | L202 | TNAND(1,1) | Section 2: CNTFET Emulation (30 tests) | `cntfet_tnand(TRIT_TRUE, TRIT_TRUE) == TRIT_FALSE` | Logic |
| 32 | L205 | TNAND(1,-1) | Section 2: CNTFET Emulation (30 tests) | `cntfet_tnand(TRIT_TRUE, TRIT_FALSE) == TRIT_TRUE` | Logic |
| 33 | L208 | TNAND(-1,-1) | Section 2: CNTFET Emulation (30 tests) | `cntfet_tnand(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE` | Logic |
| 34 | L211 | TNAND(0,1) | Section 2: CNTFET Emulation (30 tests) | `cntfet_tnand(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN` | Logic |
| 35 | L215 | TNOR(1,1) | Section 2: CNTFET Emulation (30 tests) | `cntfet_tnor(TRIT_TRUE, TRIT_TRUE) == TRIT_FALSE` | Logic |
| 36 | L218 | TNOR(-1,-1) | Section 2: CNTFET Emulation (30 tests) | `cntfet_tnor(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE` | Logic |
| 37 | L221 | TNOR(0,-1) | Section 2: CNTFET Emulation (30 tests) | `cntfet_tnor(TRIT_UNKNOWN, TRIT_FALSE) == TRIT_UNKNOWN` | Logic |
| 38 | L226 | drift should be non-negative | Section 2: CNTFET Emulation (30 tests) | `drift >= 0` | Negative/error |
| 39 | L229 | drift should accumulate | Section 2: CNTFET Emulation (30 tests) | `cst.devices[d0].drift_mv > 0` | Arithmetic |
| 40 | L232 | cycle count wrong | Section 2: CNTFET Emulation (30 tests) | `cst.devices[d0].cycle_count == 1000` | Performance |
| 41 | L238 | stabilize should reduce drift | Section 2: CNTFET Emulation (30 tests) | `residual >= 0 && residual <= pre_drift` | Functional |
| 42 | L242 | should be within endurance | Section 2: CNTFET Emulation (30 tests) | `cntfet_check_endurance(&cst, d0) == 1` | Functional |
| 43 | L246 | should be LVT | Section 2: CNTFET Emulation (30 tests) | `cntfet_huawei_class(200) == 0` | Functional |
| 44 | L249 | should be MVT | Section 2: CNTFET Emulation (30 tests) | `cntfet_huawei_class(400) == 1` | Functional |
| 45 | L252 | should be HVT | Section 2: CNTFET Emulation (30 tests) | `cntfet_huawei_class(650) == 2` | Functional |
| 46 | L255 | should be below min | Section 2: CNTFET Emulation (30 tests) | `cntfet_huawei_class(100) == -1` | Boundary |
| 47 | L259 | avg v_th wrong | Section 2: CNTFET Emulation (30 tests) | `cntfet_get_avg_vth(&cst) == 300` | Functional |
| 48 | L264 | chirality should increase V_TH | Section 2: CNTFET Emulation (30 tests) | `vth_chiral > 300` | Functional |
| 49 | L268 | chirality should increase V_TH | Section 2: CNTFET Emulation (30 tests) | `vth_chiral2 > 300` | Functional |
| 50 | L274 | large cycles should add more drift | Section 2: CNTFET Emulation (30 tests) | `drift_large > pre_drift_large` | Arithmetic |
| 51 | L278 | drift should be < 0.1V | Section 2: CNTFET Emulation (30 tests) | `drift_1e6 < 100` | Functional |
| 52 | L282 | drift should be < 0.1V | Section 2: CNTFET Emulation (30 tests) | `drift_1e7 < 100` | Functional |
| 53 | L289 | should withstand 10^6 cycles | Section 2: CNTFET Emulation (30 tests) | `cntfet_check_endurance(&cst, d0) == 1` | Logic |
| 54 | L295 | stabilize should reduce or maintain drift | Section 2: CNTFET Emulation (30 tests) | `post_stab <= pre_stab` | Logic |
| 55 | L299 | should reject NULL | Section 2: CNTFET Emulation (30 tests) | `cntfet_add_device(NULL, 1000, 10, 0) == -1` | Negative/error |
| 56 | L302 | should reject NULL | Section 2: CNTFET Emulation (30 tests) | `cntfet_simulate_drift(NULL, 0, 100, 0) == -1` | Negative/error |
| 57 | L306 | should reject NULL | Section 2: CNTFET Emulation (30 tests) | `cntfet_stabilize(NULL, 0, 10) == -1` | Negative/error |
| 58 | L311 | test_integration | Section 3: Module Integration (10 tests) | `function-level test` | Functional |
| 59 | L321 | should be 10 + 5 = 15 | Section 3: Module Integration (10 tests) | `new_amp == 15` | Functional |
| 60 | L324 | should reject NULL | Section 3: Module Integration (10 tests) | `tstab_apply_cntfet_drift(NULL, 5) == -1` | Negative/error |
| 61 | L340 | should return trapped count | Section 3: Module Integration (10 tests) | `trapped >= 0` | Functional |
| 62 | L343 | not all weights should be trapped | Section 3: Module Integration (10 tests) | `trapped < 16` | Logic |
| 63 | L357 | endurance check failed | Section 3: Module Integration (10 tests) | `ecs_cntfet_endurance(&ecs, &ok, &warn) == 0` | Negative/error |
| 64 | L360 | both monitors should be within endurance | Section 3: Module Integration (10 tests) | `ok == 2` | Functional |
| 65 | L363 | should reject NULL | Section 3: Module Integration (10 tests) | `ecs_cntfet_endurance(NULL, &ok, &warn) == -1` | Negative/error |
| 66 | L384 | test_phase9_expansion | Section 4: Phase 9 Expansion (50 tests) | `function-level test` | Functional |
| 67 | L401 | channel_quantize returned negative | DLT Channel Quantize | `cq_rc >= 0` | Negative/error |
| 68 | L407 | invalid trit detected | DLT Channel Quantize | `valid_trits` | Negative/error |
| 69 | L424 | bin sum mismatch | DLT Gradient Histogram | `hsum == 10` | Arithmetic |
| 70 | L439 | invalid convergence value | DLT Convergence | `conv == 0 ∣∣ conv == 1` | Negative/error |
| 71 | L456 | balance out of range | DLT Balance | `bal >= 0 && bal <= 1000` | Boundary |
| 72 | L459 | should reject OOB | DLT Balance | `dlt_get_balance(&ds, 99) < 0` | Negative/error |
| 73 | L462 | should reject NULL | DLT Balance | `dlt_get_balance(NULL, 0) < 0` | Negative/error |
| 74 | L467 | effective bits should be positive | DLT Effective Bits | `eff > 0` | Functional |
| 75 | L470 | too many bits | DLT Effective Bits | `eff <= 2000` | Functional |
| 76 | L473 | should reject OOB | DLT Effective Bits | `dlt_effective_bits(&ds, 99) < 0` | Negative/error |
| 77 | L476 | should reject NULL | DLT Effective Bits | `dlt_effective_bits(NULL, 0) < 0` | Negative/error |
| 78 | L480 | txor same nonzero should be -1 | CNTFET TXOR Gate | `cntfet_txor(1, 1) == -1` | Logic |
| 79 | L483 | txor same nonzero should be -1 | CNTFET TXOR Gate | `cntfet_txor(-1, -1) == -1` | Logic |
| 80 | L486 | txor different nonzero should be +1 | CNTFET TXOR Gate | `cntfet_txor(1, -1) == 1` | Logic |
| 81 | L489 | txor zeros should be 0 | CNTFET TXOR Gate | `cntfet_txor(0, 0) == 0` | Logic |
| 82 | L494 | vth should be positive | CNTFET Temperature V_TH | `vth25 > 0` | Functional |
| 83 | L498 | vth should change with temp | CNTFET Temperature V_TH | `vth85 != vth25` | Functional |
| 84 | L502 | neg temp coeff means higher vth at low temp | CNTFET Temperature V_TH | `vthn40 > vth85` | Functional |
| 85 | L506 | majority of +1s | CNTFET Majority Gate | `cntfet_tmaj(1, 1, 1) == 1` | Consensus |
| 86 | L509 | majority of -1s | CNTFET Majority Gate | `cntfet_tmaj(-1, -1, 1) == -1` | Consensus |
| 87 | L512 | majority with zeros | CNTFET Majority Gate | `cntfet_tmaj(0, 0, 1) == 0` | Consensus |
| 88 | L515 | no majority -> 0 | CNTFET Majority Gate | `cntfet_tmaj(1, -1, 0) == 0` | Consensus |
| 89 | L525 | batch drift should be >= 0 | CNTFET Batch Drift | `bd >= 0` | Functional |
| 90 | L528 | max drift unreasonably large | CNTFET Batch Drift | `bd < 200` | Boundary |
| 91 | L531 | should reject NULL | CNTFET Batch Drift | `cntfet_batch_drift(NULL, 10000, 0) < 0` | Negative/error |
| 92 | L536 | active count out of range | CNTFET Active Count | `ac >= 0 && ac <= 4` | Boundary |
| 93 | L539 | NULL should return 0 | CNTFET Active Count | `cntfet_active_count(NULL) == 0` | Negative/error |
| 94 | L544 | stddev should be non-negative | CNTFET V_TH Stddev | `sd >= 0` | Negative/error |
| 95 | L547 | NULL should return 0 | CNTFET V_TH Stddev | `cntfet_vth_stddev(NULL) == 0` | Negative/error |
| 96 | L551 | reset should succeed | CNTFET Reset Drift | `cntfet_reset_drift(&bcst) == 0` | Initialization |
| 97 | L557 | all devices should have 0 drift | CNTFET Reset Drift | `all_zero` | Functional |
| 98 | L560 | should reject NULL | CNTFET Reset Drift | `cntfet_reset_drift(NULL) < 0` | Negative/error |
| 99 | L565 | leakage should be >= 0 | CNTFET Leakage | `leak >= 0` | Functional |
| 100 | L569 | leakage increases with temperature | CNTFET Leakage | `leak85 >= leak` | Functional |

---

## Suite 33: ART-9 RISC Pipeline

**Source**: `tests/test_art9.c`
**Runtime Assertions**: 122
**Source-Level Entries**: 40
**Harness**: `TEST(condition, "message")` — inline check, prints `[PASS]`/`[FAIL]` per line
**Output Reading**: Summary: `N passed, M failed (of T)`. Exit code 1 if failures.

> **Note**: 82 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L151 | TADDI: 50 + (-7) = 43 | Test harness (same style as other seT6 test files) | `st.regs[0] == 43` | Arithmetic |
| 2 | L164 | art9_init returns 0 | Test harness (same style as other seT6 test files) | `art9_init(&st) == 0` | Initialization |
| 3 | L174 | art9_run returns positive cycle count | Test harness (same style as other seT6 test files) | `c > 0` | Performance |
| 4 | L175 | pipeline halted after THALT | Test harness (same style as other seT6 test files) | `st.halted == 1` | IPC |
| 5 | L176 | R0 = 42 after TMOVI | Test harness (same style as other seT6 test files) | `st.regs[0] == 42` | Functional |
| 6 | L190 | RAW hazard detected (stalls > 0) | Test harness (same style as other seT6 test files) | `st.stalls > 0` | Hardware/ALU |
| 7 | L208 | Branch taken count > 0 | Test harness (same style as other seT6 test files) | `st.branches_taken > 0` | Functional |
| 8 | L229 | TSTORE: mem[5] = 42 | Test harness (same style as other seT6 test files) | `st.memory[5] == 42` | Functional |
| 9 | L230 | TLOAD: R3 = mem[5] = 42 | Test harness (same style as other seT6 test files) | `st.regs[3] == 42` | Functional |
| 10 | L264 | Multiple RAW hazards detected | Test harness (same style as other seT6 test files) | `st.stalls >= 2` | Arithmetic |
| 11 | L265 | Chain resolved: R3 = 0 | Test harness (same style as other seT6 test files) | `st.regs[3] == 0` | Linking |
| 12 | L281 | Branch not taken | Test harness (same style as other seT6 test files) | `st.branches_taken == 0` | Logic |
| 13 | L282 | R1 set after branch not taken | Test harness (same style as other seT6 test files) | `st.regs[1] == 10` | Logic |
| 14 | L283 | R2 set after branch not taken | Test harness (same style as other seT6 test files) | `st.regs[2] == 20` | Logic |
| 15 | L298 | Store completed | Test harness (same style as other seT6 test files) | `st.memory[1] == 1` | Functional |
| 16 | L299 | Load got stored value | Test harness (same style as other seT6 test files) | `st.regs[1] == 1` | Hardware/ALU |
| 17 | L315 | CPI > 1.0 with RAW hazards | Test harness (same style as other seT6 test files) | `cpi > 1000` | Performance |
| 18 | L330 | One branch taken | Test harness (same style as other seT6 test files) | `st.branches_taken == 1` | Functional |
| 19 | L331 | Skipped instruction not executed | Test harness (same style as other seT6 test files) | `st.regs[1] != 99` | Logic |
| 20 | L335 | art9_init(NULL) → -1 | Test harness (same style as other seT6 test files) | `art9_init(NULL) == -1` | Negative/error |
| 21 | L336 | art9_run(NULL) → -1 | Test harness (same style as other seT6 test files) | `art9_run(NULL, 100) == -1` | Negative/error |
| 22 | L349 | Dhrystone program loaded (24 instructions) | Test harness (same style as other seT6 test files) | `prog_len == 24` | Hardware/ALU |
| 23 | L352 | Dhrystone completed with positive cycle count | Test harness (same style as other seT6 test files) | `cycles > 0` | Performance |
| 24 | L353 | Dhrystone halted via THALT | Test harness (same style as other seT6 test files) | `st.halted == 1` | Functional |
| 25 | L362 | Stall count >= 0 (hazards tracked) | Test harness (same style as other seT6 test files) | `st.stalls >= 0` | Hardware/ALU |
| 26 | L365 | Energy consumed > 0 fJ | Test harness (same style as other seT6 test files) | `st.energy_fj > 0` | Arithmetic |
| 27 | L376 | DMIPS(100MHz) > 0 | Test harness (same style as other seT6 test files) | `dmips > 0` | Performance |
| 28 | L554 | Chain: R3 = 10 + 20 = 30 | Test harness (same style as other seT6 test files) | `st.regs[3] == 30` | Functional |
| 29 | L555 | Chain: R4 = 30 + 30 = 60 | Test harness (same style as other seT6 test files) | `st.regs[4] == 60` | Functional |
| 30 | L577 | Multi-store: mem[0] = 111 | Test harness (same style as other seT6 test files) | `st.memory[0] == 111` | Arithmetic |
| 31 | L578 | Multi-store: mem[1] = 222 | Test harness (same style as other seT6 test files) | `st.memory[1] == 222` | Arithmetic |
| 32 | L579 | Multi-load: R2 = mem[0] = 111 | Test harness (same style as other seT6 test files) | `st.regs[2] == 111` | Arithmetic |
| 33 | L580 | Multi-load: R3 = mem[1] = 222 | Test harness (same style as other seT6 test files) | `st.regs[3] == 222` | Arithmetic |
| 34 | L592 | Clamp(0) = 0 | Test harness (same style as other seT6 test files) | `art9_clamp(0) == 0` | Boundary |
| 35 | L593 | Clamp(MAX) = MAX | Test harness (same style as other seT6 test files) | `art9_clamp(9841) == 9841` | Boundary |
| 36 | L594 | Clamp(MIN) = MIN | Test harness (same style as other seT6 test files) | `art9_clamp(-9841) == -9841` | Boundary |
| 37 | L595 | Clamp(20000) = MAX | Test harness (same style as other seT6 test files) | `art9_clamp(20000) == 9841` | Boundary |
| 38 | L596 | Clamp(-20000) = MIN | Test harness (same style as other seT6 test files) | `art9_clamp(-20000) == -9841` | Boundary |
| 39 | L609 | Pipeline drains within budget | Test harness (same style as other seT6 test files) | `cycles > 0 && cycles <= 50` | IPC |
| 40 | L610 | Pipeline halted properly | Test harness (same style as other seT6 test files) | `st.halted == 1` | IPC |

---

## Suite 34: Ternary PDF-Derived

**Source**: `tests/test_ternary_pdfs.c`
**Runtime Assertions**: 478
**Source-Level Entries**: 360
**Harness**: `TEST(condition, "message")` — inline check, prints `[PASS]`/`[FAIL]` per line
**Output Reading**: Summary: `N passed, M failed (of T)`. Exit code 1 if failures.

> **Note**: 118 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L77 | tekum_init width=8 succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_init(&st, 8) == 0` | Initialization |
| 2 | L78 | default_width is 8 | Section 1: Tekum Tapered Precision Floats (50 tests) | `st.default_width == 8` | Functional |
| 3 | L79 | trunc_is_round property set | Section 1: Tekum Tapered Precision Floats (50 tests) | `st.trunc_is_round == 1` | Functional |
| 4 | L82 | tekum_init width=16 succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_init(&st2, 16) == 0` | Initialization |
| 5 | L83 | tekum_init width=7 (odd) rejects | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_init(&st2, 7) == -1` | Negative/error |
| 6 | L84 | tekum_init width=6 (<8) rejects | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_init(&st2, 6) == -1` | Negative/error |
| 7 | L85 | tekum_init NULL rejects | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_init(NULL, 8) == -1` | Negative/error |
| 8 | L89 | tekum_encode(0) succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_encode(&st, 0, &zero) == 0` | Encoding |
| 9 | L92 | zero word is all-zero trits | Section 1: Tekum Tapered Precision Floats (50 tests) | `all_zero` | Functional |
| 10 | L95 | tekum_decode zero succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_decode(&st, &zero, &dzero) == 0` | Encoding |
| 11 | L96 | decoded zero.is_zero flag | Section 1: Tekum Tapered Precision Floats (50 tests) | `dzero.is_zero == 1` | Encoding |
| 12 | L97 | decoded zero.value_x1000 == 0 | Section 1: Tekum Tapered Precision Floats (50 tests) | `dzero.value_x1000 == 0` | Encoding |
| 13 | L101 | tekum_encode(NAR) succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_encode(&st, TEKUM_NAR, &nar) == 0` | Encoding |
| 14 | L104 | NaR word is all T trits | Section 1: Tekum Tapered Precision Floats (50 tests) | `all_neg` | Functional |
| 15 | L108 | decoded NaR.is_nar flag | Section 1: Tekum Tapered Precision Floats (50 tests) | `dnar.is_nar == 1` | Encoding |
| 16 | L112 | tekum_encode(INF) succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_encode(&st, TEKUM_INF, &inf) == 0` | Encoding |
| 17 | L115 | INF word is all +1 trits | Section 1: Tekum Tapered Precision Floats (50 tests) | `all_pos` | Functional |
| 18 | L119 | decoded INF.is_inf flag | Section 1: Tekum Tapered Precision Floats (50 tests) | `dinf.is_inf == 1` | Encoding |
| 19 | L124 | tekum_negate succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_negate(&val1, &neg1) == 0` | Logic |
| 20 | L128 | negation flips all trit signs | Section 1: Tekum Tapered Precision Floats (50 tests) | `neg_ok` | Functional |
| 21 | L136 | double negation = identity | Section 1: Tekum Tapered Precision Floats (50 tests) | `dbl_neg_ok` | Functional |
| 22 | L142 | compare 1.0 <= 3.0 | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_compare(&a, &b) <= 0` | Functional |
| 23 | L143 | compare 3.0 >= 1.0 | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_compare(&b, &a) >= 0` | Functional |
| 24 | L144 | compare self == 0 | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_compare(&a, &a) == 0` | Functional |
| 25 | L145 | compare 0 <= 1.0 | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_compare(&zero, &a) <= 0` | Functional |
| 26 | L156 | encode/decode 1.0 round-trip err < 2.0 | Section 1: Tekum Tapered Precision Floats (50 tests) | `err1 < 2000` | Encoding |
| 27 | L164 | encode/decode 3.0 round-trip err < 5.0 | Section 1: Tekum Tapered Precision Floats (50 tests) | `err3 < 5000` | Encoding |
| 28 | L173 | tekum_truncate 32→16 succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `trc == 0` | Functional |
| 29 | L174 | truncated word has 16 trits | Section 1: Tekum Tapered Precision Floats (50 tests) | `wtrunc.n == 16` | Functional |
| 30 | L177 | truncation_error non-negative | Section 1: Tekum Tapered Precision Floats (50 tests) | `trunc_err >= 0` | Negative/error |
| 31 | L178 | CORE: trunc error < 0.5 ulp (trunc=round) | Section 1: Tekum Tapered Precision Floats (50 tests) | `trunc_err < 500` | Negative/error |
| 32 | L182 | tekum_add(0, x) succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_add(&st, &zero, &a, &sum) == 0` | Arithmetic |
| 33 | L183 | ops_performed incremented | Section 1: Tekum Tapered Precision Floats (50 tests) | `st.ops_performed > 0` | Arithmetic |
| 34 | L190 | NaR + x = NaR | Section 1: Tekum Tapered Precision Floats (50 tests) | `dnar2.is_nar == 1` | Functional |
| 35 | L194 | tekum_mul(x, 0) succeeds | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_mul(&st, &a, &zero, &prod) == 0` | Arithmetic |
| 36 | L200 | NaR * x = NaR | Section 1: Tekum Tapered Precision Floats (50 tests) | `dnar3.is_nar == 1` | Functional |
| 37 | L204 | radix_economy(10) positive | Section 1: Tekum Tapered Precision Floats (50 tests) | `re_small > 0` | Functional |
| 38 | L207 | radix_economy(1000000) positive | Section 1: Tekum Tapered Precision Floats (50 tests) | `re_large > 0` | Functional |
| 39 | L208 | radix_economy ternary <= binary at large N | Section 1: Tekum Tapered Precision Floats (50 tests) | `re_large <= 1000` | Functional |
| 40 | L211 | ops_performed tracks add+mul | Section 1: Tekum Tapered Precision Floats (50 tests) | `st.ops_performed >= 2` | Arithmetic |
| 41 | L212 | nar_produced tracks NaR results | Section 1: Tekum Tapered Precision Floats (50 tests) | `st.nar_produced >= 2` | Functional |
| 42 | L216 | truncate to odd trits rejects | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_truncate(&wfull, 7, &w_bad) == -1` | Negative/error |
| 43 | L217 | truncate to <8 rejects | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_truncate(&wfull, 6, &w_bad) == -1` | Negative/error |
| 44 | L218 | truncate to same width rejects | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_truncate(&wfull, 32, &w_bad) == -1` | Negative/error |
| 45 | L225 | negative encode → negative decode | Section 1: Tekum Tapered Precision Floats (50 tests) | `dneg.value_x1000 < 0 ∣∣ dneg.is_zero` | Negative/error |
| 46 | L235 | truncation 24→12 error < 0.5 ulp | Section 1: Tekum Tapered Precision Floats (50 tests) | `te2 < 500` | Negative/error |
| 47 | L243 | truncation of zero is zero | Section 1: Tekum Tapered Precision Floats (50 tests) | `dz16.is_zero == 1` | Functional |
| 48 | L249 | compare: negative <= zero | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_compare(&wneg2, &zero) <= 0` | Negative/error |
| 49 | L250 | compare: zero <= positive | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_compare(&zero, &wpos) <= 0` | Functional |
| 50 | L251 | compare: negative <= positive | Section 1: Tekum Tapered Precision Floats (50 tests) | `tekum_compare(&wneg2, &wpos) <= 0` | Negative/error |
| 51 | L262 | dlt_init succeeds | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt_init(&dlt) == 0` | Initialization |
| 52 | L263 | dlt_init NULL rejects | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt_init(NULL) == -1` | Negative/error |
| 53 | L267 | first layer index = 0 | Section 2: DLT Trapping-Free Quantization (40 tests) | `l0 == 0` | Functional |
| 54 | L269 | second layer index = 1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `l1 == 1` | Functional |
| 55 | L270 | layer_count == 2 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layer_count == 2` | Functional |
| 56 | L277 | w=1.0 → +1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `quant_out[0] == 1` | Functional |
| 57 | L278 | w=-1.0 → -1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `quant_out[1] == -1` | Functional |
| 58 | L279 | w=0.0 → 0 | Section 2: DLT Trapping-Free Quantization (40 tests) | `quant_out[2] == 0` | Functional |
| 59 | L282 | count_pos >= 1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].count_pos >= 1` | Functional |
| 60 | L283 | count_neg >= 1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].count_neg >= 1` | Functional |
| 61 | L284 | count_zero >= 1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].count_zero >= 1` | Functional |
| 62 | L285 | total_weights = 8 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].total_weights == 8` | Functional |
| 63 | L290 | dlt_detect_trapped returns >= 0 | Section 2: DLT Trapping-Free Quantization (40 tests) | `trapped >= 0` | Functional |
| 64 | L291 | trapped_count tracked | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].trapped_count >= 0` | Functional |
| 65 | L296 | wp remains non-negative | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].wp >= 0` | Negative/error |
| 66 | L297 | wn remains non-positive | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].wn <= 0` | Functional |
| 67 | L302 | delta_p > 0 (positive weights exist) | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].delta_p > 0` | Functional |
| 68 | L303 | delta_n > 0 (negative weights exist) | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[0].delta_n > 0` | Negative/error |
| 69 | L307 | sparsity in [0,1000] | Section 2: DLT Trapping-Free Quantization (40 tests) | `sparsity >= 0 && sparsity <= 1000` | Functional |
| 70 | L314 | accuracy > 50% for well-separated weights | Section 2: DLT Trapping-Free Quantization (40 tests) | `acc > 500` | Logic |
| 71 | L319 | dlt_ste_gradient returns >= 0 | Section 2: DLT Trapping-Free Quantization (40 tests) | `ste_count >= 0` | Functional |
| 72 | L331 | dlt_reactivate returns >= 0 | Section 2: DLT Trapping-Free Quantization (40 tests) | `reactivated >= 0` | Functional |
| 73 | L335 | trapping_rate layer 0 in [0,1000] | Section 2: DLT Trapping-Free Quantization (40 tests) | `rate0 >= 0 && rate0 <= 1000` | Functional |
| 74 | L337 | trapping_rate layer 1 in [0,1000] | Section 2: DLT Trapping-Free Quantization (40 tests) | `rate1 >= 0 && rate1 <= 1000` | Functional |
| 75 | L350 | add third layer succeeds | Section 2: DLT Trapping-Free Quantization (40 tests) | `l2 >= 0` | Arithmetic |
| 76 | L353 | total_weights == 64 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[l2].total_weights == 64` | Functional |
| 77 | L356 | large scale: some +1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[l2].count_pos > 0` | Functional |
| 78 | L357 | large scale: some -1 | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[l2].count_neg > 0` | Functional |
| 79 | L358 | large scale: zero count valid | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.layers[l2].count_zero >= 0` | Functional |
| 80 | L362 | iterations field writable | Section 2: DLT Trapping-Free Quantization (40 tests) | `dlt.iterations == 100` | Functional |
| 81 | L384 | off_init succeeds | Section 3: OFF Graded L-inf Distillation (40 tests) | `off_init(&off) == 0` | Initialization |
| 82 | L385 | off_init NULL rejects | Section 3: OFF Graded L-inf Distillation (40 tests) | `off_init(NULL) == -1` | Negative/error |
| 83 | L388 | set temperature=2.0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off_set_temperature(&off, 2000) == 0` | Functional |
| 84 | L389 | temperature stored correctly | Section 3: OFF Graded L-inf Distillation (40 tests) | `off.temperature == 2000` | Functional |
| 85 | L394 | cos_sim(x,x) ≈ 1.0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `cs >= 990` | Functional |
| 86 | L400 | cos_sim orthogonal ≈ 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `cs_orth >= -100 && cs_orth <= 100` | Functional |
| 87 | L405 | cos_sim(x, -x) ≈ -1.0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `cs_anti <= -900` | Functional |
| 88 | L409 | MI(cos=0.95) > 1.0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `mi_hi > 1000` | Functional |
| 89 | L412 | MI(cos=0.1) < MI(cos=0.95) | Section 3: OFF Graded L-inf Distillation (40 tests) | `mi_lo < mi_hi` | Functional |
| 90 | L415 | MI(cos=0) = 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `mi_zero == 0` | Functional |
| 91 | L421 | distill_step returns valid layer | Section 3: OFF Graded L-inf Distillation (40 tests) | `lidx >= 0` | Functional |
| 92 | L422 | distill cos_sim > 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off.layers[lidx].cos_sim > 0` | Functional |
| 93 | L423 | distill off_loss >= 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off.layers[lidx].off_loss >= 0` | Functional |
| 94 | L428 | outlier detected (5000 >> mean) | Section 3: OFF Graded L-inf Distillation (40 tests) | `oc >= 1` | Functional |
| 95 | L432 | no outliers in normal distribution | Section 3: OFF Graded L-inf Distillation (40 tests) | `oc2 == 0` | Logic |
| 96 | L436 | retention >= 0 after distill step | Section 3: OFF Graded L-inf Distillation (40 tests) | `ret >= 0` | Functional |
| 97 | L441 | graded_truth at max element = 1.0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `gt == 1000` | Boundary |
| 98 | L444 | graded_truth at half-max = 0.5 | Section 3: OFF Graded L-inf Distillation (40 tests) | `gt_half == 500` | Boundary |
| 99 | L447 | graded_truth at zero element = 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `gt_zero == 0` | Functional |
| 100 | L450 | graded_truth NULL → 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off_graded_truth(NULL, 5, 0) == 0` | Negative/error |
| 101 | L451 | graded_truth dim=0 → 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off_graded_truth(feat_gt, 0, 0) == 0` | Functional |
| 102 | L452 | graded_truth OOB idx → 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off_graded_truth(feat_gt, 5, 10) == 0` | Functional |
| 103 | L458 | graded_truth out of range [0,1000] | Section 3: OFF Graded L-inf Distillation (40 tests) | `0` | Boundary |
| 104 | L461 | all graded_truth values in [0, 1000] | Section 3: OFF Graded L-inf Distillation (40 tests) | `1` | Hardware/ALU |
| 105 | L467 | graded_mi high for similar vectors | Section 3: OFF Graded L-inf Distillation (40 tests) | `gmi_hi > 0` | Logic |
| 106 | L472 | graded_mi non-negative for anti-parallel | Section 3: OFF Graded L-inf Distillation (40 tests) | `gmi_lo >= 0` | Negative/error |
| 107 | L478 | graded MI non-negative (general property) | Section 3: OFF Graded L-inf Distillation (40 tests) | `gmi_hi >= 0` | Negative/error |
| 108 | L484 | second distill_step returns valid layer | Section 3: OFF Graded L-inf Distillation (40 tests) | `l2 >= 0` | Functional |
| 109 | L485 | layer_count >= 2 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off.layer_count >= 2` | Functional |
| 110 | L486 | avg_cos_sim > 0 after 2 layers | Section 3: OFF Graded L-inf Distillation (40 tests) | `off.avg_cos_sim > 0` | Functional |
| 111 | L487 | avg_mutual_info >= 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off.avg_mutual_info >= 0` | Functional |
| 112 | L495 | graded MI: better match → higher MI | Section 3: OFF Graded L-inf Distillation (40 tests) | `gmi_strong >= gmi_weak` | Functional |
| 113 | L499 | graded_mi zeros → 0 | Section 3: OFF Graded L-inf Distillation (40 tests) | `off_graded_mi(zeros, zeros, 4) == 0` | Functional |
| 114 | L512 | tps_init succeeds | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `tps_init(&tps) == 0` | Initialization |
| 115 | L513 | tps_init NULL rejects | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `tps_init(NULL) == -1` | Negative/error |
| 116 | L517 | bit_equiv(1B, ternary) < 1B | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `beq > 0 && beq < 1000` | Functional |
| 117 | L520 | bit_equiv(1B, float16) = 1B | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `beq_float == 1000` | Functional |
| 118 | L522 | ternary bit_equiv < float bit_equiv | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `beq < beq_float` | Functional |
| 119 | L527 | loss(100M) > irreducible | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `loss_small > TPS_CHINCHILLA_E` | Functional |
| 120 | L528 | loss(3.9B) > irreducible | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `loss_big > TPS_CHINCHILLA_E` | Functional |
| 121 | L529 | loss decreases with scale | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `loss_small > loss_big` | Functional |
| 122 | L533 | ppl(2.0) > 6.5 (×100) | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `ppl > 650` | Functional |
| 123 | L534 | ppl(2.0) < 8.0 (×100) | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `ppl < 800` | Functional |
| 124 | L538 | memory(1B, ternary) > 0 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `mem > 0` | Memory |
| 125 | L540 | ternary memory < float memory | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `mem < mem_f` | Memory |
| 126 | L544 | bandwidth saving > 9× vs FP16 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `bw > 9000` | Functional |
| 127 | L545 | bandwidth saving < 12× vs FP16 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `bw < 12000` | Functional |
| 128 | L549 | add_config(1B) succeeds | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `ci >= 0` | Arithmetic |
| 129 | L550 | stored params_m | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `tps.configs[ci].params_m == 1000` | Functional |
| 130 | L551 | estimated_loss > 0 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `tps.configs[ci].estimated_loss > 0` | Functional |
| 131 | L552 | estimated_ppl > 0 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `tps.configs[ci].estimated_ppl > 0` | Functional |
| 132 | L553 | memory_mb > 0 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `tps.configs[ci].memory_mb > 0` | Memory |
| 133 | L557 | find_crossover returns >= 0 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `cross >= 0` | Functional |
| 134 | L561 | estimate_flops > 0 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `flops > 0` | Functional |
| 135 | L563 | more params+tokens → more FLOPs | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `flops_big > flops` | Parsing |
| 136 | L567 | bitsize_scaling(1000M) > ε | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `bsl_1000 > TPS_CHINCHILLA_E` | Functional |
| 137 | L570 | bitsize_scaling(10000M) > ε | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `bsl_10000 > TPS_CHINCHILLA_E` | Functional |
| 138 | L571 | bitsize_scaling decreases with more bits | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `bsl_10000 < bsl_1000` | Functional |
| 139 | L574 | bitsize_scaling(0) = A (max loss) | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `bsl_zero == TPS_CHINCHILLA_A` | Boundary |
| 140 | L578 | crossover_bits(loss_at_1000M) > 0 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `cb > 0` | Functional |
| 141 | L579 | crossover_bits <= 1000M bits | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `cb <= 1000` | Functional |
| 142 | L582 | crossover_bits(ε) = 0 (impossible target) | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `cb_lo == 0` | Functional |
| 143 | L586 | add_config(3.9B) succeeds | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `ci2 >= 0` | Arithmetic |
| 144 | L587 | config_count >= 2 | Section 4: TriLMs Pretrain Scaling Laws (30 tests) | `tps.config_count >= 2` | Initialization |
| 145 | L599 | tmul_init(9,3) succeeds | Section 5: Truncated Ternary Multipliers (20 tests) | `tmul_init(&tm, 9, 3) == 0` | Arithmetic |
| 146 | L600 | operand_trits = 9 | Section 5: Truncated Ternary Multipliers (20 tests) | `tm.operand_trits == 9` | Functional |
| 147 | L601 | truncate_trits = 3 | Section 5: Truncated Ternary Multipliers (20 tests) | `tm.truncate_trits == 3` | Functional |
| 148 | L603 | tmul_init NULL rejects | Section 5: Truncated Ternary Multipliers (20 tests) | `tmul_init(NULL, 9, 3) == -1` | Negative/error |
| 149 | L604 | tmul_init trits<2 rejects | Section 5: Truncated Ternary Multipliers (20 tests) | `tmul_init(&tm, 1, 0) == -1` | Negative/error |
| 150 | L605 | tmul_init truncate>=operand rejects | Section 5: Truncated Ternary Multipliers (20 tests) | `tmul_init(&tm, 9, 9) == -1` | Negative/error |
| 151 | L612 | tmul_full(100,50) = 5000 | Section 5: Truncated Ternary Multipliers (20 tests) | `full == 5000` | Arithmetic |
| 152 | L613 | tmul_full(-10,10) = -100 | Section 5: Truncated Ternary Multipliers (20 tests) | `tmul_full(-10, 10) == -100` | Arithmetic |
| 153 | L614 | tmul_full(0,x) = 0 | Section 5: Truncated Ternary Multipliers (20 tests) | `tmul_full(0, 999) == 0` | Arithmetic |
| 154 | L619 | truncation error non-negative | Section 5: Truncated Ternary Multipliers (20 tests) | `err >= 0` | Negative/error |
| 155 | L631 | CORE: max error < 1.0 ulp (balanced ternary bound) | Section 5: Truncated Ternary Multipliers (20 tests) | `max_err < 1000` | Boundary |
| 156 | L632 | max_error non-negative | Section 5: Truncated Ternary Multipliers (20 tests) | `max_err >= 0` | Boundary |
| 157 | L637 | avg_error non-negative | Section 5: Truncated Ternary Multipliers (20 tests) | `avg_err >= 0` | Negative/error |
| 158 | L638 | avg_error <= max_error | Section 5: Truncated Ternary Multipliers (20 tests) | `avg_err <= max_err ∣∣ max_err == 0` | Boundary |
| 159 | L639 | CORE: avg error < 0.5 ulp (zero-bias property) | Section 5: Truncated Ternary Multipliers (20 tests) | `avg_err < 500` | Negative/error |
| 160 | L643 | area_savings > 0 | Section 5: Truncated Ternary Multipliers (20 tests) | `savings > 0` | Functional |
| 161 | L645 | area_savings >= 10% | Section 5: Truncated Ternary Multipliers (20 tests) | `savings >= 100` | Functional |
| 162 | L653 | 16-trit truncated error bounded | Section 5: Truncated Ternary Multipliers (20 tests) | `e16 < (int64_t)500 * 243` | Boundary |
| 163 | L656 | total_muls = 11×11 = 121 | Section 5: Truncated Ternary Multipliers (20 tests) | `tm2.total_muls == 121` | Arithmetic |
| 164 | L705 | negate(T) = F | Section 6: K3 Kleene Logic Gates (20 tests) | `k3_negate(K3_TRUE) == K3_FALSE` | Logic |
| 165 | L706 | negate(F) = T | Section 6: K3 Kleene Logic Gates (20 tests) | `k3_negate(K3_FALSE) == K3_TRUE` | Logic |
| 166 | L707 | negate(U) = U | Section 6: K3 Kleene Logic Gates (20 tests) | `k3_negate(K3_UNKNOWN) == K3_UNKNOWN` | Logic |
| 167 | L720 | negation distributes: ⊠(¬a,¬b) = ¬⊠(a,b) | Section 6: K3 Kleene Logic Gates (20 tests) | `neg_dist_ok` | Functional |
| 168 | L735 | tstab_init succeeds | Section 7: Trit Stability Engine (30 tests) | `tstab_init(&st) == 0` | Initialization |
| 169 | L736 | tstab_init NULL rejects | Section 7: Trit Stability Engine (30 tests) | `tstab_init(NULL) == -1` | Negative/error |
| 170 | L741 | noise amplitude set | Section 7: Trit Stability Engine (30 tests) | `st.noise_amplitude_mv == 50` | Functional |
| 171 | L742 | RNG seed set | Section 7: Trit Stability Engine (30 tests) | `st.rng_seed == 12345` | Initialization |
| 172 | L745 | configure SEU succeeds | Section 7: Trit Stability Engine (30 tests) | `tstab_configure_seu(&st, 100) == 0` | Initialization |
| 173 | L746 | SEU probability set | Section 7: Trit Stability Engine (30 tests) | `st.seu_prob_ppm == 100` | Functional |
| 174 | L750 | 27 PVT configs generated | Section 7: Trit Stability Engine (30 tests) | `configs == 27` | Initialization |
| 175 | L751 | pvt_config_count == 27 | Section 7: Trit Stability Engine (30 tests) | `st.pvt_config_count == 27` | Initialization |
| 176 | L757 | result input matches | Section 7: Trit Stability Engine (30 tests) | `result.input == TRIT_TRUE` | Functional |
| 177 | L758 | recovery cycles valid | Section 7: Trit Stability Engine (30 tests) | `result.recovery_cycles >= 0` | Performance |
| 178 | L762 | full sweep returns valid flip count | Section 7: Trit Stability Engine (30 tests) | `flips >= 0` | Functional |
| 179 | L763 | sweep marked done | Section 7: Trit Stability Engine (30 tests) | `st.pvt_sweep_done == 1` | Functional |
| 180 | L764 | 81 trits tested (3×27) | Section 7: Trit Stability Engine (30 tests) | `st.total_trits_tested == 81` | Functional |
| 181 | L768 | stability PPM in range | Section 7: Trit Stability Engine (30 tests) | `ppm >= 0 && ppm <= 1000000` | Boundary |
| 182 | L770 | worst SNM reasonable | Section 7: Trit Stability Engine (30 tests) | `snm >= -1000 && snm <= 1000` | Functional |
| 183 | L775 | SEU injection returns valid count | Section 7: Trit Stability Engine (30 tests) | `seu_flips >= 0` | Functional |
| 184 | L780 | SEU recovery returns valid count | Section 7: Trit Stability Engine (30 tests) | `recovered >= 0` | Functional |
| 185 | L785 | meta-stable detection returns valid count | Section 7: Trit Stability Engine (30 tests) | `meta >= 0` | Functional |
| 186 | L789 | CNTFET drift adds to noise (50+25=75) | Section 7: Trit Stability Engine (30 tests) | `new_noise == 75` | Arithmetic |
| 187 | L790 | new noise amplitude positive | Section 7: Trit Stability Engine (30 tests) | `new_noise > 0` | Functional |
| 188 | L794 | CNTFET sweep returns valid drift | Section 7: Trit Stability Engine (30 tests) | `drift >= 0` | Functional |
| 189 | L795 | CORE: drift < 0.1V (100 mV) for 1M cycles | Section 7: Trit Stability Engine (30 tests) | `drift < 100` | Logic |
| 190 | L799 | CNTFET sweep different chirality succeeds | Section 7: Trit Stability Engine (30 tests) | `drift2 >= 0` | Functional |
| 191 | L800 | CORE: drift < 0.1V for 10M cycles | Section 7: Trit Stability Engine (30 tests) | `drift2 < 100` | Logic |
| 192 | L812 | tekum taper returns valid error | Section 7: Trit Stability Engine (30 tests) | `taper_err >= 0` | Negative/error |
| 193 | L813 | CORE: tekum taper error < 0.5 ulp | Section 7: Trit Stability Engine (30 tests) | `taper_err < 500` | Negative/error |
| 194 | L816 | taper to larger width rejects | Section 7: Trit Stability Engine (30 tests) | `tstab_tekum_taper(&st, 8, 16) == -1` | Negative/error |
| 195 | L817 | odd width rejects | Section 7: Trit Stability Engine (30 tests) | `tstab_tekum_taper(&st, 7, 8) == -1` | Negative/error |
| 196 | L818 | NULL state rejects | Section 7: Trit Stability Engine (30 tests) | `tstab_tekum_taper(NULL, 16, 8) == -1` | Negative/error |
| 197 | L821 | total_trits_tested >= 81 | Section 7: Trit Stability Engine (30 tests) | `st.total_trits_tested >= 81` | Functional |
| 198 | L822 | metastable_events >= 0 | Section 7: Trit Stability Engine (30 tests) | `st.metastable_events >= 0` | Parsing |
| 199 | L823 | flip_count >= 0 | Section 7: Trit Stability Engine (30 tests) | `st.flip_count >= 0` | Functional |
| 200 | L826 | noise amplitude non-negative | Section 7: Trit Stability Engine (30 tests) | `st.noise_amplitude_mv >= 0` | Negative/error |
| 201 | L837 | all PVT configs valid | Section 7: Trit Stability Engine (30 tests) | `1` | Initialization |
| 202 | L845 | drift increases with more cycles | Section 7: Trit Stability Engine (30 tests) | `drift3 >= drift` | Performance |
| 203 | L846 | CORE: even high cycles drift < 0.1V | Section 7: Trit Stability Engine (30 tests) | `drift3 < 100` | Performance |
| 204 | L863 | TXOR(+1,+1) = -1 (same nonzero) | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_txor(1, 1) == -1` | Logic |
| 205 | L864 | TXOR(-1,-1) = -1 (same nonzero) | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_txor(-1, -1) == -1` | Logic |
| 206 | L865 | TXOR(+1,-1) = +1 (different) | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_txor(1, -1) == 1` | Logic |
| 207 | L866 | TXOR(-1,+1) = +1 (different) | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_txor(-1, 1) == 1` | Logic |
| 208 | L867 | TXOR(0,0) = 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_txor(0, 0) == 0` | Logic |
| 209 | L868 | TXOR(+1,0) = +1 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_txor(1, 0) == 1` | Logic |
| 210 | L869 | TXOR(0,+1) = +1 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_txor(0, 1) == 1` | Logic |
| 211 | L875 | Vth at 25C > 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `vth25 > 0` | Functional |
| 212 | L876 | Vth changes with temperature | Section 8: Phase 9 CNTFET Expansion (35 tests) | `vth85 != vth25` | Functional |
| 213 | L877 | Vth at -40C > Vth at 85C (neg temp coeff) | Section 8: Phase 9 CNTFET Expansion (35 tests) | `vthn40 > vth85` | Functional |
| 214 | L878 | Vth at 25C in 100-800mV range | Section 8: Phase 9 CNTFET Expansion (35 tests) | `vth25 > 100 && vth25 < 800` | Boundary |
| 215 | L882 | batch_drift max drift >= 0 mV | Section 8: Phase 9 CNTFET Expansion (35 tests) | `max_drift >= 0` | Boundary |
| 216 | L883 | batch_drift max drift < 100 mV | Section 8: Phase 9 CNTFET Expansion (35 tests) | `max_drift < 100` | Boundary |
| 217 | L887 | active_count >= 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `active >= 0` | Functional |
| 218 | L888 | active_count <= total devices | Section 8: Phase 9 CNTFET Expansion (35 tests) | `active <= 8` | Functional |
| 219 | L892 | Vth stddev >= 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `stddev >= 0` | Functional |
| 220 | L896 | reset_drift succeeds | Section 8: Phase 9 CNTFET Expansion (35 tests) | `rc_reset == 0` | Initialization |
| 221 | L898 | device drift reset to 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cst.devices[i].drift_mv == 0` | Initialization |
| 222 | L902 | TMAJ(+1,+1,+1) = +1 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_tmaj(1, 1, 1) == 1` | Functional |
| 223 | L903 | TMAJ(-1,-1,-1) = -1 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_tmaj(-1, -1, -1) == -1` | Functional |
| 224 | L904 | TMAJ(+1,+1,-1) = +1 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_tmaj(1, 1, -1) == 1` | Functional |
| 225 | L905 | TMAJ(-1,-1,+1) = -1 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_tmaj(-1, -1, 1) == -1` | Functional |
| 226 | L906 | TMAJ(+1,-1,0) = 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_tmaj(1, -1, 0) == 0` | Functional |
| 227 | L907 | TMAJ(0,0,0) = 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_tmaj(0, 0, 0) == 0` | Functional |
| 228 | L911 | leakage >= 0 | Section 8: Phase 9 CNTFET Expansion (35 tests) | `leakage >= 0` | Functional |
| 229 | L912 | leakage within reasonable bounds | Section 8: Phase 9 CNTFET Expansion (35 tests) | `leakage < 1000000` | Boundary |
| 230 | L915 | batch_drift NULL safe | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_batch_drift(NULL, 100, 0) < 0` | Negative/error |
| 231 | L916 | active_count NULL safe | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_active_count(NULL) == 0` | Negative/error |
| 232 | L917 | vth_stddev NULL safe | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_vth_stddev(NULL) == 0` | Negative/error |
| 233 | L918 | reset_drift NULL safe | Section 8: Phase 9 CNTFET Expansion (35 tests) | `cntfet_reset_drift(NULL) < 0` | Negative/error |
| 234 | L929 | dlt_init succeeds | Section 9: Phase 9 DLT Expansion (35 tests) | `dlt_init(&ds) == 0` | Initialization |
| 235 | L941 | channel_quantize returns >= 0 trapped | Section 9: Phase 9 DLT Expansion (35 tests) | `trapped >= 0` | IPC |
| 236 | L946 | channel_quantize output trits in {-1,0,+1} | Section 9: Phase 9 DLT Expansion (35 tests) | `valid` | IPC |
| 237 | L955 | histogram bins sum to gradient count | Section 9: Phase 9 DLT Expansion (35 tests) | `total_bin == 8` | Arithmetic |
| 238 | L956 | histogram bin[0] >= 0 | Section 9: Phase 9 DLT Expansion (35 tests) | `bins[0] >= 0` | Functional |
| 239 | L957 | histogram bin[4] >= 0 | Section 9: Phase 9 DLT Expansion (35 tests) | `bins[4] >= 0` | Functional |
| 240 | L967 | convergence returns 0 or 1 | Section 9: Phase 9 DLT Expansion (35 tests) | `conv == 0 ∣∣ conv == 1` | Logic |
| 241 | L971 | convergence with loose threshold | Section 9: Phase 9 DLT Expansion (35 tests) | `conv_loose == 1` | Functional |
| 242 | L975 | balance >= 0 | Section 9: Phase 9 DLT Expansion (35 tests) | `bal >= 0` | Functional |
| 243 | L976 | balance <= 1000 | Section 9: Phase 9 DLT Expansion (35 tests) | `bal <= 1000` | Functional |
| 244 | L980 | effective_bits > 0 | Section 9: Phase 9 DLT Expansion (35 tests) | `eff > 0` | Functional |
| 245 | L981 | effective_bits <= 2.0 (ternary max ~1.58) | Section 9: Phase 9 DLT Expansion (35 tests) | `eff <= 2000` | Boundary |
| 246 | L992 | layer 1 balance in range | Section 9: Phase 9 DLT Expansion (35 tests) | `bal1 >= 0 && bal1 <= 1000` | Boundary |
| 247 | L1001 | get_balance NULL safe | Section 9: Phase 9 DLT Expansion (35 tests) | `dlt_get_balance(NULL, 0) < 0` | Negative/error |
| 248 | L1002 | effective_bits NULL safe | Section 9: Phase 9 DLT Expansion (35 tests) | `dlt_effective_bits(NULL, 0) < 0` | Negative/error |
| 249 | L1012 | large histogram sums correctly | Section 9: Phase 9 DLT Expansion (35 tests) | `big_total == 64` | Arithmetic |
| 250 | L1020 | balance stable after iters | Section 9: Phase 9 DLT Expansion (35 tests) | `bal_after >= 0 && bal_after <= 1000` | Functional |
| 251 | L1024 | tight threshold valid | Section 9: Phase 9 DLT Expansion (35 tests) | `conv_tight == 0 ∣∣ conv_tight == 1` | Functional |
| 252 | L1027 | OOB layer rejects | Section 9: Phase 9 DLT Expansion (35 tests) | `dlt_check_convergence(&ds, 99, 500) < 0` | Negative/error |
| 253 | L1028 | negative layer rejects | Section 9: Phase 9 DLT Expansion (35 tests) | `dlt_get_balance(&ds, -1) < 0` | Negative/error |
| 254 | L1029 | OOB effective_bits rejects | Section 9: Phase 9 DLT Expansion (35 tests) | `dlt_effective_bits(&ds, 99) < 0` | Negative/error |
| 255 | L1033 | layer 1 effective_bits in range | Section 9: Phase 9 DLT Expansion (35 tests) | `eff1 > 0 && eff1 <= 2000` | Boundary |
| 256 | L1044 | off_init succeeds | Section 10: Phase 9 OFF Expansion (35 tests) | `off_init(&os) == 0` | Initialization |
| 257 | L1053 | KL divergence >= 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `kl >= 0` | Arithmetic |
| 258 | L1055 | KL(T, T) = 0 (self) | Section 10: Phase 9 OFF Expansion (35 tests) | `kl_self == 0` | Functional |
| 259 | L1056 | KL(T,S) >= KL(T,T) | Section 10: Phase 9 OFF Expansion (35 tests) | `kl_self <= kl ∣∣ kl == 0` | Functional |
| 260 | L1062 | KL divergence of orthogonal > 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `kl_ortho > 0` | Arithmetic |
| 261 | L1069 | batch_distill processed 2 layers | Section 10: Phase 9 OFF Expansion (35 tests) | `batch_rc == 2` | Functional |
| 262 | L1070 | layer_count = 2 after batch | Section 10: Phase 9 OFF Expansion (35 tests) | `os.layer_count == 2` | Functional |
| 263 | L1071 | layer 0 cos_sim > 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `os.layers[0].cos_sim > 0` | Functional |
| 264 | L1072 | layer 1 cos_sim > 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `os.layers[1].cos_sim > 0` | Functional |
| 265 | L1077 | layer 0 importance >= 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `imp0 >= 0` | Functional |
| 266 | L1078 | layer 1 importance >= 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `imp1 >= 0` | Functional |
| 267 | L1079 | OOB importance returns -1 | Section 10: Phase 9 OFF Expansion (35 tests) | `off_layer_importance(&os, -1) == -1` | Functional |
| 268 | L1080 | OOB importance returns -1 | Section 10: Phase 9 OFF Expansion (35 tests) | `off_layer_importance(&os, 99) == -1` | Functional |
| 269 | L1087 | temp=1.0: soft[0] = teacher[0] | Section 10: Phase 9 OFF Expansion (35 tests) | `soft_out[0] == teacher1[0]` | Functional |
| 270 | L1093 | temp=2.0: soft[0] = teacher[0]/2 | Section 10: Phase 9 OFF Expansion (35 tests) | `soft_out[0] == teacher1[0] / 2` | Functional |
| 271 | L1094 | temp=2.0: soft[2] = teacher[2]/2 | Section 10: Phase 9 OFF Expansion (35 tests) | `soft_out[2] == teacher1[2] / 2` | Functional |
| 272 | L1101 | feature_mse >= 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `mse >= 0` | Functional |
| 273 | L1103 | MSE(T, T) = 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `mse_self == 0` | Functional |
| 274 | L1104 | MSE(T, S) > MSE(T, T) | Section 10: Phase 9 OFF Expansion (35 tests) | `mse > mse_self` | Functional |
| 275 | L1108 | cos_sim T1-S1 > 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `cos_sim > 0` | Functional |
| 276 | L1110 | either MSE or high cos_sim | Section 10: Phase 9 OFF Expansion (35 tests) | `mse > 0 ∣∣ cos_sim > 900` | Logic |
| 277 | L1118 | batch_distill skips NULL layer | Section 10: Phase 9 OFF Expansion (35 tests) | `batch2 == 1` | Negative/error |
| 278 | L1121 | KL NULL teacher = 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `off_kl_divergence(NULL, student1, 5) == 0` | Negative/error |
| 279 | L1122 | KL NULL student = 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `off_kl_divergence(teacher1, NULL, 5) == 0` | Negative/error |
| 280 | L1123 | KL dim=0 = 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `off_kl_divergence(teacher1, student1, 0) == 0` | Functional |
| 281 | L1126 | MSE NULL teacher = 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `off_feature_mse(NULL, student1, 5) == 0` | Negative/error |
| 282 | L1127 | MSE dim=0 = 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `off_feature_mse(teacher1, student1, 0) == 0` | Functional |
| 283 | L1136 | MSE large dim >= 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `big_mse >= 0` | Functional |
| 284 | L1138 | KL large dim >= 0 | Section 10: Phase 9 OFF Expansion (35 tests) | `big_kl >= 0` | Functional |
| 285 | L1155 | tps_init succeeds | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_init(&ts) == 0` | Initialization |
| 286 | L1160 | ternary efficiency > 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `eff_tern > 0` | Functional |
| 287 | L1161 | fp16 efficiency > 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `eff_fp16 > 0` | Functional |
| 288 | L1162 | ternary more efficient per bit than fp16 | Section 11: Phase 9 TPS Expansion (35 tests) | `eff_tern > eff_fp16` | Functional |
| 289 | L1165 | efficiency(0 params) = 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_efficiency_ratio(0, 20, 1580) == 0` | Functional |
| 290 | L1166 | efficiency(0 tokens) = 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_efficiency_ratio(1000, 0, 1580) == 0` | Parsing |
| 291 | L1167 | efficiency(0 bits) = 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_efficiency_ratio(1000, 20, 0) == 0` | Functional |
| 292 | L1171 | optimal_tokens > 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `opt > 0` | Parsing |
| 293 | L1173 | optimal_tokens fp16 > 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `opt_fp > 0` | Parsing |
| 294 | L1175 | ternary needs >= fp16 tokens (bit-adjusted) | Section 11: Phase 9 TPS Expansion (35 tests) | `opt >= opt_fp` | Parsing |
| 295 | L1178 | optimal(0 params) = 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_optimal_tokens(0, 1580) == 0` | Functional |
| 296 | L1179 | optimal(0 bits) = 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_optimal_tokens(1000, 0) == 0` | Functional |
| 297 | L1183 | spectra_add_all adds 6 configs | Section 11: Phase 9 TPS Expansion (35 tests) | `added == 6` | Arithmetic |
| 298 | L1184 | config_count = 6 | Section 11: Phase 9 TPS Expansion (35 tests) | `ts.config_count == 6` | Initialization |
| 299 | L1187 | spectra[0] = 99M | Section 11: Phase 9 TPS Expansion (35 tests) | `ts.configs[0].params_m == 99` | Functional |
| 300 | L1188 | spectra[1] = 197M | Section 11: Phase 9 TPS Expansion (35 tests) | `ts.configs[1].params_m == 197` | Functional |
| 301 | L1189 | spectra[2] = 394M | Section 11: Phase 9 TPS Expansion (35 tests) | `ts.configs[2].params_m == 394` | Functional |
| 302 | L1190 | spectra[3] = 830M | Section 11: Phase 9 TPS Expansion (35 tests) | `ts.configs[3].params_m == 830` | Functional |
| 303 | L1191 | spectra[4] = 1.7B | Section 11: Phase 9 TPS Expansion (35 tests) | `ts.configs[4].params_m == 1700` | Functional |
| 304 | L1192 | spectra[5] = 3.9B | Section 11: Phase 9 TPS Expansion (35 tests) | `ts.configs[5].params_m == 3900` | Functional |
| 305 | L1196 | 3.9B params better loss than 99M | Section 11: Phase 9 TPS Expansion (35 tests) | `better == 5` | Functional |
| 306 | L1198 | compare same config returns it | Section 11: Phase 9 TPS Expansion (35 tests) | `same == 2` | Initialization |
| 307 | L1201 | compare OOB idx rejects | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_compare_configs(&ts, -1, 0) == -1` | Negative/error |
| 308 | L1202 | compare OOB idx rejects | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_compare_configs(&ts, 0, 99) == -1` | Negative/error |
| 309 | L1203 | compare NULL rejects | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_compare_configs(NULL, 0, 1) == -1` | Negative/error |
| 310 | L1208 | post-quant loss > base loss | Section 11: Phase 9 TPS Expansion (35 tests) | `quant_loss > base_loss` | Functional |
| 311 | L1210 | fp16 quant loss > base | Section 11: Phase 9 TPS Expansion (35 tests) | `quant_fp16 > base_loss` | Functional |
| 312 | L1211 | ternary quant penalty > fp16 | Section 11: Phase 9 TPS Expansion (35 tests) | `quant_loss > quant_fp16` | Functional |
| 313 | L1214 | quant(0 loss) = 0 | Section 11: Phase 9 TPS Expansion (35 tests) | `tps_quant_degradation(0, 1580) <= 0` | Functional |
| 314 | L1223 | two spectra batches = 12 configs | Section 11: Phase 9 TPS Expansion (35 tests) | `ts2.config_count == 12` | Initialization |
| 315 | L1230 | config_count capped at max | Section 11: Phase 9 TPS Expansion (35 tests) | `ts3.config_count <= TPS_MAX_CONFIGS` | Boundary |
| 316 | L1241 | tmul_init(6,2) succeeds | Section 12: Phase 9 TMUL Expansion (30 tests) | `tmul_init(&ms, 6, 2) == 0` | Arithmetic |
| 317 | L1245 | error_bound > 0 | Section 12: Phase 9 TMUL Expansion (30 tests) | `bound > 0` | Boundary |
| 318 | L1246 | error_bound = (3^2-1)/2 = 4 | Section 12: Phase 9 TMUL Expansion (30 tests) | `bound == (9 - 1) / 2` | Boundary |
| 319 | L1253 | batch processed 5 pairs | Section 12: Phase 9 TMUL Expansion (30 tests) | `batch_rc == 5` | Functional |
| 320 | L1254 | batch: 0 × 100 = 0 | Section 12: Phase 9 TMUL Expansion (30 tests) | `out_arr[4] == 0` | Functional |
| 321 | L1260 | batch error within extended bound | Section 12: Phase 9 TMUL Expansion (30 tests) | `err <= bound * 9` | Boundary |
| 322 | L1267 | compensated result nonzero | Section 12: Phase 9 TMUL Expansion (30 tests) | `comp != 0` | Functional |
| 323 | L1270 | compensated error measurable | Section 12: Phase 9 TMUL Expansion (30 tests) | `err_comp >= 0` | Negative/error |
| 324 | L1275 | MAC: acc nonzero after 3×4 | Section 12: Phase 9 TMUL Expansion (30 tests) | `acc != 0` | Functional |
| 325 | L1278 | MAC: acc changes after second op | Section 12: Phase 9 TMUL Expansion (30 tests) | `acc != first` | Functional |
| 326 | L1281 | muls tracked before reset | Section 12: Phase 9 TMUL Expansion (30 tests) | `ms.total_muls > 0` | Arithmetic |
| 327 | L1282 | reset_stats succeeds | Section 12: Phase 9 TMUL Expansion (30 tests) | `tmul_reset_stats(&ms) == 0` | Initialization |
| 328 | L1283 | total_muls = 0 after reset | Section 12: Phase 9 TMUL Expansion (30 tests) | `ms.total_muls == 0` | Arithmetic |
| 329 | L1284 | max_error = 0 after reset | Section 12: Phase 9 TMUL Expansion (30 tests) | `ms.max_error == 0` | Boundary |
| 330 | L1285 | avg_error = 0 after reset | Section 12: Phase 9 TMUL Expansion (30 tests) | `ms.avg_error == 0` | Negative/error |
| 331 | L1289 | muls = 1 after post-reset op | Section 12: Phase 9 TMUL Expansion (30 tests) | `ms.total_muls == 1` | Arithmetic |
| 332 | L1303 | error_bound(k=3) = (3^3-1)/2 = 13 | Section 12: Phase 9 TMUL Expansion (30 tests) | `bound2 == (27 - 1) / 2` | Boundary |
| 333 | L1308 | error_bound(k=1) = (3^1-1)/2 = 1 | Section 12: Phase 9 TMUL Expansion (30 tests) | `bound3 == (3 - 1) / 2` | Boundary |
| 334 | L1311 | compensated NULL safe | Section 12: Phase 9 TMUL Expansion (30 tests) | `tmul_compensated(NULL, 1, 1) == 0` | Negative/error |
| 335 | L1312 | mac NULL safe | Section 12: Phase 9 TMUL Expansion (30 tests) | `tmul_mac(NULL, &acc, 1, 1) == 0` | Negative/error |
| 336 | L1313 | reset_stats NULL rejects | Section 12: Phase 9 TMUL Expansion (30 tests) | `tmul_reset_stats(NULL) == -1` | Negative/error |
| 337 | L1314 | error_bound NULL = 0 | Section 12: Phase 9 TMUL Expansion (30 tests) | `tmul_error_bound(NULL) == 0` | Boundary |
| 338 | L1325 | tstab_init succeeds | Section 13: Phase 9 Stabilize Expansion (30 tests) | `tstab_init(&ss) == 0` | Initialization |
| 339 | L1335 | histogram sums to nsamples | Section 13: Phase 9 Stabilize Expansion (30 tests) | `hist_total == 1000` | Arithmetic |
| 340 | L1336 | center bin populated (noise distributed) | Section 13: Phase 9 Stabilize Expansion (30 tests) | `bins[5] > 0` | Functional |
| 341 | L1338 | edge bins < total | Section 13: Phase 9 Stabilize Expansion (30 tests) | `bins[0] + bins[10] < hist_total` | Functional |
| 342 | L1342 | flip rate = 0 before testing | Section 13: Phase 9 Stabilize Expansion (30 tests) | `rate0 == 0` | Functional |
| 343 | L1347 | flip rate >= 0 after sweep | Section 13: Phase 9 Stabilize Expansion (30 tests) | `rate1 >= 0` | Functional |
| 344 | L1348 | flip rate <= 1M PPM | Section 13: Phase 9 Stabilize Expansion (30 tests) | `rate1 <= 1000000` | Functional |
| 345 | L1353 | aging increases noise | Section 13: Phase 9 Stabilize Expansion (30 tests) | `amp_aged > amp_before` | Functional |
| 346 | L1355 | more aging = more noise | Section 13: Phase 9 Stabilize Expansion (30 tests) | `amp_aged2 > amp_aged` | Functional |
| 347 | L1358 | aging NULL rejects | Section 13: Phase 9 Stabilize Expansion (30 tests) | `tstab_aging_model(NULL, 1000) == -1` | Negative/error |
| 348 | L1359 | aging negative hours rejects | Section 13: Phase 9 Stabilize Expansion (30 tests) | `tstab_aging_model(&ss, -1) == -1` | Negative/error |
| 349 | L1361 | aging 0 hours = no change | Section 13: Phase 9 Stabilize Expansion (30 tests) | `amp_zero >= 0` | Functional |
| 350 | L1365 | guard band > 0 | Section 13: Phase 9 Stabilize Expansion (30 tests) | `guard > 0` | Logic |
| 351 | L1366 | guard >= noise amplitude | Section 13: Phase 9 Stabilize Expansion (30 tests) | `guard >= (int)ss.noise_amplitude_mv` | Functional |
| 352 | L1367 | guard >= 2× metastable threshold | Section 13: Phase 9 Stabilize Expansion (30 tests) | `guard >= 2 * TSTAB_METASTABLE_MV` | Parsing |
| 353 | L1370 | guard band NULL = 0 | Section 13: Phase 9 Stabilize Expansion (30 tests) | `tstab_voltage_guard_band(NULL) == 0` | Negative/error |
| 354 | L1376 | batch_pvt_sweep >= 0 flips | Section 13: Phase 9 Stabilize Expansion (30 tests) | `batch_flips >= 0` | Functional |
| 355 | L1377 | total tested increased after batch | Section 13: Phase 9 Stabilize Expansion (30 tests) | `ss.total_trits_tested > 81` | Functional |
| 356 | L1389 | stability PPM >= 0 | Section 13: Phase 9 Stabilize Expansion (30 tests) | `ppm >= 0` | Functional |
| 357 | L1390 | stability PPM <= 1M | Section 13: Phase 9 Stabilize Expansion (30 tests) | `ppm <= 1000000` | Functional |
| 358 | L1394 | flip rate after batch >= 0 | Section 13: Phase 9 Stabilize Expansion (30 tests) | `rate2 >= 0` | Functional |
| 359 | L1398 | worst SNM >= 0 | Section 13: Phase 9 Stabilize Expansion (30 tests) | `snm >= 0` | Functional |
| 360 | L1399 | worst SNM < 400 mV (realistic) | Section 13: Phase 9 Stabilize Expansion (30 tests) | `snm < 400` | Functional |

---

## Suite 35: Peirce Semiotic Engine

**Source**: `tests/test_peirce_semiotic.c`
**Runtime Assertions**: 200
**Source-Level Entries**: 100
**Harness**: `TEST(condition, "message")` — inline check, prints `[PASS]`/`[FAIL]` per line
**Output Reading**: Summary: `N passed, M failed (of T)`. Exit code 1 if failures.

> **Note**: 100 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L47 | 1.1  psm_init succeeds | Section 1: Initialization & Basics | `psm_init(&st) == 0` | Initialization |
| 2 | L50 | 1.2  initialized flag set | Section 1: Initialization & Basics | `st.initialized == 1` | Initialization |
| 3 | L53 | 1.3  chain_len starts at 0 | Section 1: Initialization & Basics | `st.chain_len == 0` | Initialization |
| 4 | L56 | 1.4  NULL init returns -1 | Section 1: Initialization & Basics | `psm_init(NULL) == -1` | Negative/error |
| 5 | L59 | 1.5  PSM_FIRSTNESS == -1 | Section 1: Initialization & Basics | `PSM_FIRSTNESS == -1` | Functional |
| 6 | L62 | 1.6  PSM_SECONDNESS == 0 | Section 1: Initialization & Basics | `PSM_SECONDNESS == 0` | Functional |
| 7 | L65 | 1.7  PSM_THIRDNESS == +1 | Section 1: Initialization & Basics | `PSM_THIRDNESS == 1` | Functional |
| 8 | L68 | 1.8  QUALISIGN == FIRSTNESS | Section 1: Initialization & Basics | `PSM_QUALISIGN == PSM_FIRSTNESS` | Functional |
| 9 | L71 | 1.9  SINSIGN == SECONDNESS | Section 1: Initialization & Basics | `PSM_SINSIGN == PSM_SECONDNESS` | Functional |
| 10 | L74 | 1.10 LEGISIGN == THIRDNESS | Section 1: Initialization & Basics | `PSM_LEGISIGN == PSM_THIRDNESS` | Functional |
| 11 | L77 | 1.11 ICON == FIRSTNESS | Section 1: Initialization & Basics | `PSM_ICON == PSM_FIRSTNESS` | Functional |
| 12 | L80 | 1.12 INDEX == SECONDNESS | Section 1: Initialization & Basics | `PSM_INDEX == PSM_SECONDNESS` | Functional |
| 13 | L83 | 1.13 SYMBOL == THIRDNESS | Section 1: Initialization & Basics | `PSM_SYMBOL == PSM_THIRDNESS` | Linking |
| 14 | L86 | 1.14 RHEME == FIRSTNESS | Section 1: Initialization & Basics | `PSM_RHEME == PSM_FIRSTNESS` | Functional |
| 15 | L89 | 1.15 DICISIGN == SECONDNESS | Section 1: Initialization & Basics | `PSM_DICISIGN == PSM_SECONDNESS` | Functional |
| 16 | L92 | 1.16 ARGUMENT == THIRDNESS | Section 1: Initialization & Basics | `PSM_ARGUMENT == PSM_THIRDNESS` | Functional |
| 17 | L95 | 1.17 NUM_VALID_CLASSES == 10 | Section 1: Initialization & Basics | `PSM_NUM_VALID_CLASSES == 10` | Functional |
| 18 | L98 | 1.18 NUM_TRICHOTOMIES == 3 | Section 1: Initialization & Basics | `PSM_NUM_TRICHOTOMIES == 3` | Functional |
| 19 | L101 | 1.19 PSM_MAX_CHAIN == 64 | Section 1: Initialization & Basics | `PSM_MAX_CHAIN == 64` | Boundary |
| 20 | L165 | 2.15 Exactly 10 of 27 combos valid | Section 2: Sign Classificatio | `valid_count == 10` | Functional |
| 21 | L170 | 2.16 is_valid_class on valid → 1 | Section 2: Sign Classificatio | `psm_is_valid_class(&cls) == 1` | Functional |
| 22 | L173 | 2.17 is_valid_class(NULL) → 0 | Section 2: Sign Classificatio | `psm_is_valid_class(NULL) == 0` | Negative/error |
| 23 | L178 | 2.18 Manually invalid → 0 | Section 2: Sign Classificatio | `psm_is_valid_class(&bad) == 0` | Negative/error |
| 24 | L184 | 2.19 class_id on invalid → 0 | Section 2: Sign Classificatio | `psm_class_id(&bad) == 0` | Negative/error |
| 25 | L188 | Qualisign | Section 2: Sign Classificatio | `strstr(psm_class_name(1)` | Functional |
| 26 | L190 | Argument | Section 2: Sign Classificatio | `strstr(psm_class_name(10)` | Functional |
| 27 | L194 | Invalid | Section 2: Sign Classificatio | `strcmp(psm_class_name(0)` | Negative/error |
| 28 | L196 | Invalid | Section 2: Sign Classificatio | `strcmp(psm_class_name(11)` | Negative/error |
| 29 | L203 | 2.24 enumerate returns 10 classes | Section 2: Sign Classificatio | `n == 10` | Functional |
| 30 | L210 | 2.25 enumerate with max=5 returns 5 | Section 2: Sign Classificatio | `n == 5` | Boundary |
| 31 | L214 | 2.26 enumerate(NULL) → 0 | Section 2: Sign Classificatio | `psm_enumerate_classes(NULL, 10) == 0` | Negative/error |
| 32 | L236 | 2.29 All symbols are legisigns (VIII–X) | Section 2: Sign Classificatio | `ok` | Linking |
| 33 | L245 | 2.30 Classes V–X all contain 'Legisign' | Section 2: Sign Classificatio | `ok` | Functional |
| 34 | L249 | 2.31 classify(NULL) → -1 | Section 2: Sign Classificatio | `psm_classify(NULL, 0, 0, 0) == -1` | Negative/error |
| 35 | L252 | 2.32 classify(2,0,0) → -1 | Section 2: Sign Classificatio | `psm_classify(&cls, 2, 0, 0) == -1` | Functional |
| 36 | L256 | Dicent | Section 2: Sign Classificatio | `strstr(psm_class_name(psm_class_id(&cls))` | Functional |
| 37 | L261 | Rhematic Symbol | Section 2: Sign Classificatio | `strstr(psm_class_name(psm_class_id(&cls))` | Linking |
| 38 | L275 | 2.35 Each class has unique ID 1–10 | Section 2: Sign Classificatio | `ok` | Functional |
| 39 | L299 | 3.1  First relation at index 0 | Section 3: Semiosis Chains | `idx == 0` | Functional |
| 40 | L302 | 3.2  chain_len == 1 | Section 3: Semiosis Chains | `st.chain_len == 1` | Functional |
| 41 | L305 | 3.3  sign_value == 1000 | Section 3: Semiosis Chains | `st.chain[0].sign_value == 1000` | Hardware/ALU |
| 42 | L319 | 3.6  class_id == 9 (IX) | Section 3: Semiosis Chains | `st.chain[0].class_id == 9` | Functional |
| 43 | L325 | 3.7  Extended chain at index 1 | Section 3: Semiosis Chains | `idx == 1` | Functional |
| 44 | L332 | 3.9  chain_len == 2 | Section 3: Semiosis Chains | `st.chain_len == 2` | Functional |
| 45 | L335 | 3.10 Second relation class X | Section 3: Semiosis Chains | `st.chain[1].class_id == 10` | Functional |
| 46 | L387 | 3.16 Built 8-step semiosis chain | Section 3: Semiosis Chains | `cst.chain_len == 8` | Functional |
| 47 | L394 | 3.17 Chain converges toward final interp | Section 3: Semiosis Chains | `d_last < d_first` | Functional |
| 48 | L398 | 3.18 Convergence metric > 0 | Section 3: Semiosis Chains | `conv > 0` | Functional |
| 49 | L401 | 3.19 Convergence > 800 for approaching chain | Section 3: Semiosis Chains | `conv > 800` | Logic |
| 50 | L408 | 3.20 Convergence on empty → 0 | Section 3: Semiosis Chains | `psm_convergence(&one) == 0` | Negative/error |
| 51 | L412 | 3.21 Convergence(NULL) → 0 | Section 3: Semiosis Chains | `psm_convergence(NULL) == 0` | Negative/error |
| 52 | L480 | 4.7  Large values don't overflow to negative | Section 4: Information Theory | `info > 0` | Boundary |
| 53 | L604 | 5.4  Large deviation → low coherence | Section 5: Triadic Determinatio | `coh < 500` | Functional |
| 54 | L618 | 5.6  I = avg(O,S) → max coherence | Section 5: Triadic Determinatio | `coh == 1000` | Boundary |
| 55 | L625 | 5.7  I further from avg(O,S) → lower coh | Section 5: Triadic Determinatio | `c1 > c2` | Functional |
| 56 | L631 | 5.8  Identical large values → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Hardware/ALU |
| 57 | L635 | 5.9  Identical negative values → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Negative/error |
| 58 | L639 | 5.10 I = avg(1000,-1000)=0 → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Functional |
| 59 | L643 | 5.11 I = avg(1000,500)=750 → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Functional |
| 60 | L649 | 5.12 Coherence bounded [0, 1000] | Section 5: Triadic Determinatio | `c >= 0 && c <= 1000` | Boundary |
| 61 | L662 | 5.14 I=avg(O,S)=500 with S=1000 → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Functional |
| 62 | L666 | 5.15 I=avg(O,S) in small range → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Boundary |
| 63 | L672 | 5.16 I=avg(-400,-200)=-300 → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Functional |
| 64 | L681 | 5.17 Closer to avg → higher coherence (0 vs 100) | Section 5: Triadic Determinatio | `c0 >= c1` | Functional |
| 65 | L682 | 5.18 Closer to avg → higher coherence (100 vs 300) | Section 5: Triadic Determinatio | `c1 >= c2` | Functional |
| 66 | L683 | 5.19 Closer → higher (300 vs 500) | Section 5: Triadic Determinatio | `c2 >= c3` | Functional |
| 67 | L684 | 5.20 Even max deviation has non-negative coh | Section 5: Triadic Determinatio | `c3 >= 0` | Boundary |
| 68 | L690 | 5.21 I=avg(300,400)=350 → 1000 | Section 5: Triadic Determinatio | `c == 1000` | Functional |
| 69 | L696 | 5.22 Extreme outlier → coherence ≥ 0 | Section 5: Triadic Determinatio | `c >= 0` | Functional |
| 70 | L704 | 5.23 Moving object away from sign reduces coherence | Section 5: Triadic Determinatio | `c1 >= c2` | Functional |
| 71 | L710 | 5.24 Moving sign reduces coherence | Section 5: Triadic Determinatio | `c1 >= c2` | Functional |
| 72 | L716 | 5.25 Moving interpretant reduces coherence | Section 5: Triadic Determinatio | `c1 >= c2` | Functional |
| 73 | L730 | 6.1  Genuine triad (100,500,900) → loss > 0 | Section 6: Reduction Thesis | `loss > 0` | Functional |
| 74 | L736 | 6.2  Degenerate (all equal) → loss ≥ 0 | Section 6: Reduction Thesis | `loss >= 0` | Functional |
| 75 | L750 | 6.4  Loss bounded ≤ 1000 | Section 6: Reduction Thesis | `loss <= 1000` | Boundary |
| 76 | L756 | 6.5  Loss always ≥ 0 | Section 6: Reduction Thesis | `loss >= 0` | Functional |
| 77 | L763 | 6.6  Tetradic reduction succeeds | Section 6: Reduction Thesis | `r == 0` | Functional |
| 78 | L807 | 6.12 Pure mediation has significant loss | Section 6: Reduction Thesis | `loss > 100` | Functional |
| 79 | L823 | 6.14 Balanced triad (-500,0,500) → loss ≥ 0 | Section 6: Reduction Thesis | `loss >= 0` | Functional |
| 80 | L827 | 6.15 Decreasing triad → loss > 0 | Section 6: Reduction Thesis | `loss > 0` | Functional |
| 81 | L831 | 6.16 Mixed triad → loss ≥ 0 | Section 6: Reduction Thesis | `loss >= 0` | Functional |
| 82 | L838 | 6.17 Large tetradic still reduces | Section 6: Reduction Thesis | `r == 0` | Functional |
| 83 | L865 | 6.20 5-ary reducible via chained tetradic | Section 6: Reduction Thesis | `tri1[0][0] == 10` | Functional |
| 84 | L873 | 6.21 Monadic (all same) → minimal loss | Section 6: Reduction Thesis | `loss < 200` | Boundary |
| 85 | L887 | 6.23 Triadic irreducibility confirmed (loss > 0) | Section 6: Reduction Thesis | `loss > 0` | Functional |
| 86 | L916 | 7.1  Immediate interp = sign value (500) | Section 7: Interpretant Analysis | `it.immediate == 500` | Hardware/ALU |
| 87 | L922 | 7.2  Dynamic = (500+800)/2 = 650 | Section 7: Interpretant Analysis | `it.dynamic == 650` | Functional |
| 88 | L928 | 7.3  Final = object value (800) | Section 7: Interpretant Analysis | `it.final_ == 800` | Hardware/ALU |
| 89 | L959 | 7.7  Dynamic between immediate and final | Section 7: Interpretant Analysis | `dyn_between` | Logic |
| 90 | L972 | 7.9  Dynamic = midpoint (0,1000) = 500 | Section 7: Interpretant Analysis | `it.dynamic == 500` | Functional |
| 91 | L986 | 7.11 Immediate = sign's quality (42) | Section 7: Interpretant Analysis | `it.immediate == 42` | Functional |
| 92 | L990 | 7.12 Immediate preserves sign (-999) | Section 7: Interpretant Analysis | `it.immediate == -999` | Functional |
| 93 | L994 | 7.13 Immediate preserves zero | Section 7: Interpretant Analysis | `it.immediate == 0` | Functional |
| 94 | L1006 | 7.15 dyn = (100+300)/2 = 200 | Section 7: Interpretant Analysis | `it.dynamic == 200` | Functional |
| 95 | L1010 | 7.16 dyn = (1+3)/2 = 2 | Section 7: Interpretant Analysis | `it.dynamic == 2` | Functional |
| 96 | L1034 | 7.19 Gap imm→fin = 1000 for (0,1000) | Section 7: Interpretant Analysis | `gap == 1000` | Logic |
| 97 | L1041 | 7.20 Gap = 0 when sign equals object | Section 7: Interpretant Analysis | `gap == 0` | Functional |
| 98 | L1073 | 7.22 dyn(-500,500) = 0 (balanced) | Section 7: Interpretant Analysis | `it.dynamic == 0` | Functional |
| 99 | L1079 | 7.23 dyn(1,2) = 1 (integer division) | Section 7: Interpretant Analysis | `it.dynamic == 1` | Arithmetic |
| 100 | L1094 | 7.25 Positive immediate → Firstness +1 | Section 7: Interpretant Analysis | `cat == TRIT_TRUE` | Functional |

---

## Suite 36: TriLang

**Source**: `tests/test_trilang.c`
**Runtime Assertions**: 100
**Source-Level Entries**: 92
**Harness**: `TEST(condition, "message")` — inline check, prints `[PASS]`/`[FAIL]` per line
**Output Reading**: Summary: `N passed, M failed (of T)`. Exit code 1 if failures.

> **Note**: 8 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L44 | 1.1  neg(T) == P | Section 1: Triadic Arithmetic | `tri_neg(TRI_T) == TRI_P` | Functional |
| 2 | L45 | 1.2  neg(O) == O | Section 1: Triadic Arithmetic | `tri_neg(TRI_O) == TRI_O` | Functional |
| 3 | L46 | 1.3  neg(P) == T | Section 1: Triadic Arithmetic | `tri_neg(TRI_P) == TRI_T` | Functional |
| 4 | L51 | 1.4  add(O,O) = O, carry O | Section 1: Triadic Arithmetic | `r.value == TRI_O && r.state == TRI_O` | Arithmetic |
| 5 | L53 | 1.5  add(P,O) = P, carry O | Section 1: Triadic Arithmetic | `r.value == TRI_P && r.state == TRI_O` | Arithmetic |
| 6 | L55 | 1.6  add(T,O) = T, carry O | Section 1: Triadic Arithmetic | `r.value == TRI_T && r.state == TRI_O` | Arithmetic |
| 7 | L57 | 1.7  add(P,P) = T, carry P (overflow) | Section 1: Triadic Arithmetic | `r.value == TRI_T && r.state == TRI_P` | Boundary |
| 8 | L59 | 1.8  add(T,T) = P, carry T (borrow) | Section 1: Triadic Arithmetic | `r.value == TRI_P && r.state == TRI_T` | Arithmetic |
| 9 | L63 | 1.9  add(P,O) interpretant is P (no carry) | Section 1: Triadic Arithmetic | `r.interpretant == TRI_P` | Arithmetic |
| 10 | L65 | 1.10 add(P,P) interpretant is O (carry present) | Section 1: Triadic Arithmetic | `r.interpretant == TRI_O` | Arithmetic |
| 11 | L69 | 1.11 sub(P,P) = O | Section 1: Triadic Arithmetic | `r.value == TRI_O` | Arithmetic |
| 12 | L71 | 1.12 sub(P,T) = T with carry P | Section 1: Triadic Arithmetic | `r.value == TRI_T && r.state == TRI_P` | Arithmetic |
| 13 | L73 | 1.13 sub(T,P) = P with carry T | Section 1: Triadic Arithmetic | `r.value == TRI_P && r.state == TRI_T` | Arithmetic |
| 14 | L76 | 1.14 mul(P,P) = P | Section 1: Triadic Arithmetic | `tri_mul(TRI_P, TRI_P) == TRI_P` | Arithmetic |
| 15 | L77 | 1.15 mul(T,T) = P | Section 1: Triadic Arithmetic | `tri_mul(TRI_T, TRI_T) == TRI_P` | Arithmetic |
| 16 | L78 | 1.16 mul(P,T) = T | Section 1: Triadic Arithmetic | `tri_mul(TRI_P, TRI_T) == TRI_T` | Arithmetic |
| 17 | L79 | 1.17 mul(O,P) = O (absorbing) | Section 1: Triadic Arithmetic | `tri_mul(TRI_O, TRI_P) == TRI_O` | Arithmetic |
| 18 | L82 | 1.18 min(P,T) = T | Section 1: Triadic Arithmetic | `tri_min(TRI_P, TRI_T) == TRI_T` | Boundary |
| 19 | L83 | 1.19 min(O,T) = T | Section 1: Triadic Arithmetic | `tri_min(TRI_O, TRI_T) == TRI_T` | Boundary |
| 20 | L84 | 1.20 min(P,P) = P | Section 1: Triadic Arithmetic | `tri_min(TRI_P, TRI_P) == TRI_P` | Boundary |
| 21 | L87 | 1.21 max(T,P) = P | Section 1: Triadic Arithmetic | `tri_max(TRI_T, TRI_P) == TRI_P` | Boundary |
| 22 | L88 | 1.22 max(O,P) = P | Section 1: Triadic Arithmetic | `tri_max(TRI_O, TRI_P) == TRI_P` | Boundary |
| 23 | L89 | 1.23 max(T,T) = T | Section 1: Triadic Arithmetic | `tri_max(TRI_T, TRI_T) == TRI_T` | Boundary |
| 24 | L92 | 1.24 consensus(P,P,P) = P | Section 1: Triadic Arithmetic | `tri_consensus(TRI_P, TRI_P, TRI_P) == TRI_P` | Consensus |
| 25 | L93 | 1.25 consensus(P,T,O) = O (no agreement) | Section 1: Triadic Arithmetic | `tri_consensus(TRI_P, TRI_T, TRI_O) == TRI_O` | Consensus |
| 26 | L104 | 2.1  K3 AND(P,P) = P | Section 2: Kleene K3 Logic | `tri_kleene_and(TRI_P, TRI_P) == TRI_P` | Functional |
| 27 | L105 | 2.2  K3 AND(P,O) = O (unknown propagates) | Section 2: Kleene K3 Logic | `tri_kleene_and(TRI_P, TRI_O) == TRI_O` | Logic |
| 28 | L106 | 2.3  K3 AND(P,T) = T (false dominates) | Section 2: Kleene K3 Logic | `tri_kleene_and(TRI_P, TRI_T) == TRI_T` | Boundary |
| 29 | L107 | 2.4  K3 AND(O,O) = O | Section 2: Kleene K3 Logic | `tri_kleene_and(TRI_O, TRI_O) == TRI_O` | Functional |
| 30 | L108 | 2.5  K3 AND(O,T) = T (false dominates) | Section 2: Kleene K3 Logic | `tri_kleene_and(TRI_O, TRI_T) == TRI_T` | Boundary |
| 31 | L109 | 2.6  K3 AND(T,T) = T | Section 2: Kleene K3 Logic | `tri_kleene_and(TRI_T, TRI_T) == TRI_T` | Functional |
| 32 | L112 | 2.7  K3 OR(P,P) = P | Section 2: Kleene K3 Logic | `tri_kleene_or(TRI_P, TRI_P) == TRI_P` | Functional |
| 33 | L113 | 2.8  K3 OR(P,O) = P (true dominates) | Section 2: Kleene K3 Logic | `tri_kleene_or(TRI_P, TRI_O) == TRI_P` | Boundary |
| 34 | L114 | 2.9  K3 OR(P,T) = P | Section 2: Kleene K3 Logic | `tri_kleene_or(TRI_P, TRI_T) == TRI_P` | Functional |
| 35 | L115 | 2.10 K3 OR(O,O) = O | Section 2: Kleene K3 Logic | `tri_kleene_or(TRI_O, TRI_O) == TRI_O` | Functional |
| 36 | L116 | 2.11 K3 OR(O,T) = O (unknown propagates) | Section 2: Kleene K3 Logic | `tri_kleene_or(TRI_O, TRI_T) == TRI_O` | Logic |
| 37 | L117 | 2.12 K3 OR(T,T) = T | Section 2: Kleene K3 Logic | `tri_kleene_or(TRI_T, TRI_T) == TRI_T` | Functional |
| 38 | L120 | 2.13 K3 NOT(P) = T | Section 2: Kleene K3 Logic | `tri_kleene_not(TRI_P) == TRI_T` | Functional |
| 39 | L121 | 2.14 K3 NOT(O) = O (unknown fixed point) | Section 2: Kleene K3 Logic | `tri_kleene_not(TRI_O) == TRI_O` | Functional |
| 40 | L122 | 2.15 K3 NOT(T) = P | Section 2: Kleene K3 Logic | `tri_kleene_not(TRI_T) == TRI_P` | Functional |
| 41 | L125 | 2.16 K3 P→P = P | Section 2: Kleene K3 Logic | `tri_kleene_implies(TRI_P, TRI_P) == TRI_P` | Functional |
| 42 | L126 | 2.17 K3 P→T = T | Section 2: Kleene K3 Logic | `tri_kleene_implies(TRI_P, TRI_T) == TRI_T` | Functional |
| 43 | L127 | 2.18 K3 T→P = P (ex falso quodlibet) | Section 2: Kleene K3 Logic | `tri_kleene_implies(TRI_T, TRI_P) == TRI_P` | Functional |
| 44 | L128 | 2.19 K3 O→P = P | Section 2: Kleene K3 Logic | `tri_kleene_implies(TRI_O, TRI_P) == TRI_P` | Functional |
| 45 | L129 | 2.20 K3 O→O = O | Section 2: Kleene K3 Logic | `tri_kleene_implies(TRI_O, TRI_O) == TRI_O` | Functional |
| 46 | L148 | 3.4  firstness(O) = 1 | Section 3: Peirce Categories | `tri_firstness(TRI_O) == 1` | Functional |
| 47 | L149 | 3.5  firstness(P) = 0 | Section 3: Peirce Categories | `tri_firstness(TRI_P) == 0` | Functional |
| 48 | L150 | 3.6  secondness(T) = 1 | Section 3: Peirce Categories | `tri_secondness(TRI_T) == 1` | Functional |
| 49 | L151 | 3.7  secondness(O) = 0 | Section 3: Peirce Categories | `tri_secondness(TRI_O) == 0` | Functional |
| 50 | L152 | 3.8  thirdness(P) = 1 | Section 3: Peirce Categories | `tri_thirdness(TRI_P) == 1` | Functional |
| 51 | L153 | 3.9  thirdness(T) = 0 | Section 3: Peirce Categories | `tri_thirdness(TRI_T) == 0` | Functional |
| 52 | L156 | 3.10 clamp(-5) = T | Section 3: Peirce Categories | `tri_clamp(-5) == TRI_T` | Boundary |
| 53 | L157 | 3.11 clamp(0) = O | Section 3: Peirce Categories | `tri_clamp(0) == TRI_O` | Boundary |
| 54 | L158 | 3.12 clamp(99) = P | Section 3: Peirce Categories | `tri_clamp(99) == TRI_P` | Boundary |
| 55 | L171 | 4.1  tryte(0) roundtrip | Section 4: Tryte Operations | `tri_tryte_to_int(&t) == 0` | Transformation |
| 56 | L173 | 4.2  tryte(1) roundtrip | Section 4: Tryte Operations | `tri_tryte_to_int(&t) == 1` | Transformation |
| 57 | L175 | 4.3  tryte(-1) roundtrip | Section 4: Tryte Operations | `tri_tryte_to_int(&t) == -1` | Transformation |
| 58 | L177 | 4.4  tryte(42) roundtrip | Section 4: Tryte Operations | `tri_tryte_to_int(&t) == 42` | Transformation |
| 59 | L179 | 4.5  tryte(-42) roundtrip | Section 4: Tryte Operations | `tri_tryte_to_int(&t) == -42` | Transformation |
| 60 | L181 | 4.6  tryte(364) max value | Section 4: Tryte Operations | `tri_tryte_to_int(&t) == 364` | Boundary |
| 61 | L183 | 4.7  tryte(-364) min value | Section 4: Tryte Operations | `tri_tryte_to_int(&t) == -364` | Boundary |
| 62 | L187 | 4.8  tryte(100) is valid | Section 4: Tryte Operations | `tri_tryte_valid(&t) == 1` | Functional |
| 63 | L193 | 4.9  tryte_neg(13) = -13 | Section 4: Tryte Operations | `tri_tryte_to_int(&b) == -13` | Functional |
| 64 | L200 | 4.10 tryte_add(10,20) = 30 | Section 4: Tryte Operations | `tri_tryte_to_int(&out) == 30` | Arithmetic |
| 65 | L205 | 4.11 tryte_add(200,-50) = 150 | Section 4: Tryte Operations | `tri_tryte_to_int(&out) == 150` | Arithmetic |
| 66 | L210 | 4.12 tryte_scale(7, P) = 7 | Section 4: Tryte Operations | `tri_tryte_to_int(&out) == 7` | Functional |
| 67 | L212 | 4.13 tryte_scale(7, T) = -7 | Section 4: Tryte Operations | `tri_tryte_to_int(&out) == -7` | Functional |
| 68 | L223 | 5.1  hesitate(O) = 1 (epistemic pause) | Section 5: Epistemic Features | `tri_hesitate(TRI_O) == 1` | Functional |
| 69 | L224 | 5.2  hesitate(P) = 0 (definite) | Section 5: Epistemic Features | `tri_hesitate(TRI_P) == 0` | Initialization |
| 70 | L225 | 5.3  hesitate(T) = 0 (definite) | Section 5: Epistemic Features | `tri_hesitate(TRI_T) == 0` | Initialization |
| 71 | L240 | 5.7  flux(T,P) delta = P (positive change) | Section 5: Epistemic Features | `r.value == TRI_P` | Functional |
| 72 | L241 | 5.8  flux(T,P) state = O (disagreement) | Section 5: Epistemic Features | `r.state == TRI_O` | Functional |
| 73 | L242 | 5.9  flux(T,P) interpretant = T (degraded) | Section 5: Epistemic Features | `r.interpretant == TRI_T` | Functional |
| 74 | L245 | 5.10 flux(O,P) interpretant = O (partial) | Section 5: Epistemic Features | `r.interpretant == TRI_O` | Functional |
| 75 | L268 | 6.3  rns_inverse({1,0,3}) = 10 | Section 6: RNS Integratio | `tri_rns_inverse(ra) == 10` | Functional |
| 76 | L271 | 6.4  rns_inverse({0,0,0}) = 0 | Section 6: RNS Integratio | `tri_rns_inverse(ra) == 0` | Functional |
| 77 | L277 | 6.5  rns_add(7,8) = 15 (carry-free) | Section 6: RNS Integratio | `tri_rns_inverse(rc) == 15` | Arithmetic |
| 78 | L283 | 6.6  rns_mul(3,4) = 12 (carry-free) | Section 6: RNS Integratio | `tri_rns_inverse(rc) == 12` | Arithmetic |
| 79 | L286 | 6.7  moduli[0] = 3 | Section 6: RNS Integratio | `TRI_RNS_MODULI[0] == 3` | Functional |
| 80 | L287 | 6.8  moduli[1] = 5 | Section 6: RNS Integratio | `TRI_RNS_MODULI[1] == 5` | Functional |
| 81 | L288 | 6.9  moduli[2] = 7 | Section 6: RNS Integratio | `TRI_RNS_MODULI[2] == 7` | Functional |
| 82 | L292 | 6.10 rns roundtrip(42) = 42 | Section 6: RNS Integratio | `tri_rns_inverse(ra) == 42` | Transformation |
| 83 | L306 | 7.1  lex 'T' → TK_TRIT_T | Section 7: Lexer | `n >= 3 && tokens[0].type == TK_TRIT_T` | Parsing |
| 84 | L307 | 7.2  lex 'O' → TK_TRIT_O | Section 7: Lexer | `tokens[1].type == TK_TRIT_O` | Parsing |
| 85 | L308 | 7.3  lex 'P' → TK_TRIT_P | Section 7: Lexer | `tokens[2].type == TK_TRIT_P` | Parsing |
| 86 | L312 | 7.4  lex 'let' → TK_LET | Section 7: Lexer | `n >= 6 && tokens[0].type == TK_LET` | Parsing |
| 87 | L313 | 7.5  lex '+' → TK_PLUS | Section 7: Lexer | `tokens[4].type == TK_PLUS` | Parsing |
| 88 | L333 | 8.1  eval 'P + T' = O (1 + -1 = 0) | Section 8: Parser + Evaluator | `r.value == TRI_O` | Functional |
| 89 | L342 | 8.2  eval 'let x = P; x' → P | Section 8: Parser + Evaluator | `r.value == TRI_P` | Functional |
| 90 | L351 | 8.3  eval 'P & T' = T (Kleene AND) | Section 8: Parser + Evaluator | `r.value == TRI_T` | Logic |
| 91 | L360 | 8.4  eval 'if(O)' → mediate branch (Thirdness) | Section 8: Parser + Evaluator | `r.value == TRI_O` | Functional |
| 92 | L361 | 8.5  mediation_count = 1 | Section 8: Parser + Evaluator | `env.mediation_count == 1` | Functional |

---

## Suite 37: Sigma 9 MCP

**Source**: `tests/test_sigma9_mcp.c`
**Runtime Assertions**: 259
**Source-Level Entries**: 309
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L57 | test_aecc_channel_init | Test Harness | `function-level test` | IPC |
| 2 | L63 | expected 0 | Abductive ECC: Channel Initializatio | `aecc_channel_init_balanced(&ch) == 0` | Functional |
| 3 | L66 | N→Z | Abductive ECC: Channel Initializatio | `ch.trans[0][1] == AECC_TRANS_POSSIBLE` | Functional |
| 4 | L69 | P→Z | Abductive ECC: Channel Initializatio | `ch.trans[2][1] == AECC_TRANS_POSSIBLE` | Functional |
| 5 | L72 | N→P | Abductive ECC: Channel Initializatio | `ch.trans[0][2] == AECC_TRANS_IMPOSSIBLE` | Functional |
| 6 | L75 | P→N | Abductive ECC: Channel Initializatio | `ch.trans[2][0] == AECC_TRANS_IMPOSSIBLE` | Functional |
| 7 | L78 | Z→N | Abductive ECC: Channel Initializatio | `ch.trans[1][0] == AECC_TRANS_IMPOSSIBLE` | Functional |
| 8 | L81 | Z→P | Abductive ECC: Channel Initializatio | `ch.trans[1][2] == AECC_TRANS_IMPOSSIBLE` | Functional |
| 9 | L84 | N→N | Abductive ECC: Channel Initializatio | `ch.trans[0][0] == AECC_TRANS_POSSIBLE` | Functional |
| 10 | L87 | Z→Z | Abductive ECC: Channel Initializatio | `ch.trans[1][1] == AECC_TRANS_POSSIBLE` | Functional |
| 11 | L90 | P→P | Abductive ECC: Channel Initializatio | `ch.trans[2][2] == AECC_TRANS_POSSIBLE` | Functional |
| 12 | L93 | null guard | Abductive ECC: Channel Initializatio | `aecc_channel_init_balanced(NULL) == -1` | Negative/error |
| 13 | L96 | test_aecc_distances | Abductive ECC: Channel Initializatio | `function-level test` | Functional |
| 14 | L108 | expected 0 | Abductive ECC: Modified Hamming Distance | `aecc_modified_hamming_distance(&ch, w1, w1, 3) == 0` | Functional |
| 15 | L112 | expected 1 | Abductive ECC: Modified Hamming Distance | `d == 1` | Functional |
| 16 | L116 | expected ≥ 2 | Abductive ECC: Modified Hamming Distance | `d >= 2` | Functional |
| 17 | L120 | expected very large (impossible transitions) | Abductive ECC: Modified Hamming Distance | `d >= 99` | Functional |
| 18 | L125 | returned some value (graceful) | Abductive ECC: Modified Hamming Distance | `d >= 0 ∣∣ d < 0` | Hardware/ALU |
| 19 | L131 | non-negative | Abductive ECC: Modified Hamming Separatio | `s >= 0` | Negative/error |
| 20 | L135 | non-negative separation | Abductive ECC: Modified Hamming Separatio | `s >= 0` | Negative/error |
| 21 | L138 | test_aecc_codebook | Abductive ECC: Modified Hamming Separatio | `function-level test` | Functional |
| 22 | L147 | expected ≥ 2 codewords | Abductive ECC: Codebook Generatio | `n >= 2` | Functional |
| 23 | L150 | expected init=1 | Abductive ECC: Codebook Generatio | `book.initialized == 1` | Initialization |
| 24 | L153 | expected 3 | Abductive ECC: Codebook Generatio | `book.codeword_len == 3` | Functional |
| 25 | L156 | mismatch | Abductive ECC: Codebook Generatio | `book.num_codewords == n` | Functional |
| 26 | L159 | null guard | Abductive ECC: Codebook Generatio | `aecc_generate_codebook(NULL, &ch, 3, 3, 2) == -1` | Negative/error |
| 27 | L162 | test_aecc_encode_decode | Abductive ECC: Codebook Generatio | `function-level test` | Encoding |
| 28 | L172 | skipped | Abductive ECC: Encode / Decode | `1` | Functional |
| 29 | L179 | encode ok | Abductive ECC: Encode / Decode | `aecc_encode(&book, 0, encoded) == 0` | Encoding |
| 30 | L183 | expected no_error | Abductive ECC: Encode / Decode | `dr.no_error == 1` | Negative/error |
| 31 | L186 | expected dataword 0 | Abductive ECC: Encode / Decode | `dr.dataword == 0` | Functional |
| 32 | L189 | encode ok | Abductive ECC: Encode / Decode | `aecc_encode(&book, 1, encoded) == 0` | Encoding |
| 33 | L193 | expected dataword 1 | Abductive ECC: Encode / Decode | `dr.dataword == 1` | Functional |
| 34 | L196 | out of range | Abductive ECC: Encode / Decode | `aecc_encode(&book, 9999, encoded) == -1` | Boundary |
| 35 | L200 | at least 1 data bit | Abductive ECC: Encode / Decode | `bits >= 1` | Parsing |
| 36 | L204 | non-negative overhead | Abductive ECC: Encode / Decode | `ovh >= 0.0` | Negative/error |
| 37 | L207 | test_aecc_zero_exclusion | Abductive ECC: Encode / Decode | `function-level test` | Functional |
| 38 | L217 | boolean result | Abductive ECC: Zero-Trit Exclusio | `excl == 0 ∣∣ excl == 1` | Logic |
| 39 | L224 | test_tcam_init | Abductive ECC: Zero-Trit Exclusio | `function-level test` | Initialization |
| 40 | L230 | init ok | TS-Memristor TCAM: Initializatio | `tstcam_init(&arr, 16, 12, TSTCAM_CELL_TERNARY, TSTCAM_TS_DIFFUSIVE) == 0` | Initialization |
| 41 | L233 | init flag | TS-Memristor TCAM: Initializatio | `arr.initialized == 1` | Initialization |
| 42 | L236 | 16 rows | TS-Memristor TCAM: Initializatio | `arr.num_rows == 16` | Functional |
| 43 | L239 | 12 trits | TS-Memristor TCAM: Initializatio | `arr.word_width == 12` | Functional |
| 44 | L242 | volatile | TS-Memristor TCAM: Initializatio | `arr.ts_device.is_volatile == 1` | Functional |
| 45 | L245 | null guard | TS-Memristor TCAM: Initializatio | `tstcam_init(NULL, 16, 12, 0, 0) == -1` | Negative/error |
| 46 | L248 | 0 rows guard | TS-Memristor TCAM: Initializatio | `tstcam_init(&arr, 0, 12, 0, 0) == -1` | Functional |
| 47 | L251 | overflow guard | TS-Memristor TCAM: Initializatio | `tstcam_init(&arr, 999, 12, 0, 0) == -1` | Boundary |
| 48 | L254 | test_tcam_write_search | TS-Memristor TCAM: Initializatio | `function-level test` | Functional |
| 49 | L264 | write ok | TS-Memristor TCAM: Write + Search | `tstcam_write(&arr, 0, word1, NULL, 10) == 0` | Functional |
| 50 | L267 | write ok | TS-Memristor TCAM: Write + Search | `tstcam_write(&arr, 1, word2, NULL, 5) == 0` | Functional |
| 51 | L271 | found match | TS-Memristor TCAM: Write + Search | `res.matched == 1` | Functional |
| 52 | L274 | row 0 | TS-Memristor TCAM: Write + Search | `res.matched_row == 0` | Functional |
| 53 | L278 | found match | TS-Memristor TCAM: Write + Search | `res.matched == 1` | Functional |
| 54 | L281 | row 1 | TS-Memristor TCAM: Write + Search | `res.matched_row == 1` | Functional |
| 55 | L286 | no match | TS-Memristor TCAM: Write + Search | `res.matched == 0` | Functional |
| 56 | L289 | bounds | TS-Memristor TCAM: Write + Search | `tstcam_write(&arr, -1, word1, NULL, 1) == -1` | Boundary |
| 57 | L292 | bounds | TS-Memristor TCAM: Write + Search | `tstcam_write(&arr, 8, word1, NULL, 1) == -1` | Boundary |
| 58 | L295 | test_tcam_wildcard | TS-Memristor TCAM: Write + Search | `function-level test` | Functional |
| 59 | L305 | write ok | TS-Memristor TCAM: Wildcard Matching | `tstcam_write(&arr, 0, word, wc, 10) == 0` | Functional |
| 60 | L310 | wildcard match | TS-Memristor TCAM: Wildcard Matching | `res.matched == 1` | Functional |
| 61 | L313 | 1 wildcard | TS-Memristor TCAM: Wildcard Matching | `res.wildcard_count == 1` | Functional |
| 62 | L316 | test_tcam_lpm | TS-Memristor TCAM: Wildcard Matching | `function-level test` | Functional |
| 63 | L336 | specific row | TS-Memristor TCAM: Longest Prefix Match | `res.matched == 1 && res.matched_row == 1` | Functional |
| 64 | L339 | both match | TS-Memristor TCAM: Longest Prefix Match | `res.num_matches >= 2` | Functional |
| 65 | L342 | test_tcam_cap_lookup | TS-Memristor TCAM: Longest Prefix Match | `function-level test` | Access control |
| 66 | L356 | cap found | TS-Memristor TCAM: Capability Lookup | `res.matched == 1` | Access control |
| 67 | L360 | not found | TS-Memristor TCAM: Capability Lookup | `res.matched == 0` | Logic |
| 68 | L363 | test_tcam_stats | TS-Memristor TCAM: Capability Lookup | `function-level test` | Functional |
| 69 | L376 | 1 programmed | TS-Memristor TCAM: Statistics | `prog == 1` | Functional |
| 70 | L379 | 1 search | TS-Memristor TCAM: Statistics | `searches == 1` | Functional |
| 71 | L382 | 1 match | TS-Memristor TCAM: Statistics | `matches == 1` | Functional |
| 72 | L385 | test_tcam_read_invalidate | TS-Memristor TCAM: Statistics | `function-level test` | Negative/error |
| 73 | L395 | read ok | TS-Memristor TCAM: Read + Invalidate | `tstcam_read(&arr, 0, readback, NULL) == 0` | Functional |
| 74 | L402 | invalidate ok | TS-Memristor TCAM: Read + Invalidate | `tstcam_invalidate(&arr, 0) == 0` | Negative/error |
| 75 | L405 | invalid row | TS-Memristor TCAM: Read + Invalidate | `tstcam_read(&arr, 0, readback, NULL) == -1` | Negative/error |
| 76 | L412 | test_peirce_law_eval | TS-Memristor TCAM: Read + Invalidate | `function-level test` | Functional |
| 77 | L417 | T | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE` | Functional |
| 78 | L420 | T | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_TRUE, TRIT_FALSE) == TRIT_TRUE` | Functional |
| 79 | L423 | T | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_TRUE` | Functional |
| 80 | L426 | T | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_FALSE, TRIT_TRUE) == TRIT_TRUE` | Functional |
| 81 | L429 | T | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE` | Functional |
| 82 | L432 | T | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_TRUE` | Functional |
| 83 | L435 | U | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN` | Functional |
| 84 | L438 | U | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_UNKNOWN, TRIT_FALSE) == TRIT_UNKNOWN` | Functional |
| 85 | L441 | U | Peirce Logic: Peirce's Law Evaluatio | `peirce_law(TRIT_UNKNOWN, TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 86 | L444 | test_peirce_decidability | Peirce Logic: Peirce's Law Evaluatio | `function-level test` | Functional |
| 87 | L449 | decided | Peirce Logic: Decidability Detectio | `peirce_is_decided(TRIT_TRUE) == 1` | Functional |
| 88 | L452 | decided | Peirce Logic: Decidability Detectio | `peirce_is_decided(TRIT_FALSE) == 1` | Functional |
| 89 | L455 | undecided | Peirce Logic: Decidability Detectio | `peirce_is_decided(TRIT_UNKNOWN) == 0` | Functional |
| 90 | L458 | test_peirce_double_negation | Peirce Logic: Decidability Detectio | `function-level test` | Functional |
| 91 | L463 | T | Peirce Logic: Double Negation Translatio | `peirce_double_negation(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE` | Functional |
| 92 | L466 | T | Peirce Logic: Double Negation Translatio | `peirce_double_negation(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE` | Functional |
| 93 | L470 | U | Peirce Logic: Double Negation Translatio | `dn == TRIT_UNKNOWN` | Functional |
| 94 | L473 | test_peirce_modus_ponens | Peirce Logic: Double Negation Translatio | `function-level test` | Functional |
| 95 | L478 | T | Peirce Logic: Modus Ponens | `peirce_modus_ponens(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE` | Functional |
| 96 | L481 | F | Peirce Logic: Modus Ponens | `peirce_modus_ponens(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE` | Functional |
| 97 | L484 | U | Peirce Logic: Modus Ponens | `peirce_modus_ponens(TRIT_FALSE, TRIT_TRUE) == TRIT_UNKNOWN` | Functional |
| 98 | L487 | U | Peirce Logic: Modus Ponens | `peirce_modus_ponens(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN` | Functional |
| 99 | L490 | test_peirce_abduction | Peirce Logic: Modus Ponens | `function-level test` | Functional |
| 100 | L496 | init ok | Peirce Logic: Abductive Reasoning | `peirce_engine_init(&eng, PEIRCE_MODE_TERNARY) == 0` | Initialization |
| 101 | L501 | props added | Peirce Logic: Abductive Reasoning | `p1 >= 0 && p2 >= 0` | Arithmetic |
| 102 | L505 | impl added | Peirce Logic: Abductive Reasoning | `im >= 0` | Arithmetic |
| 103 | L510 | hyps added | Peirce Logic: Abductive Reasoning | `h1 >= 0 && h2 >= 0` | Arithmetic |
| 104 | L514 | obs added | Peirce Logic: Abductive Reasoning | `o1 >= 0` | Arithmetic |
| 105 | L518 | at least 1 viable | Peirce Logic: Abductive Reasoning | `res.num_viable >= 1` | Parsing |
| 106 | L521 | has name | Peirce Logic: Abductive Reasoning | `strlen(res.best.name) > 0` | Functional |
| 107 | L524 | non-negative quality | Peirce Logic: Abductive Reasoning | `res.total_quality >= 0` | Negative/error |
| 108 | L527 | test_peirce_hw_diagnose | Peirce Logic: Abductive Reasoning | `function-level test` | Functional |
| 109 | L538 | viable diagnoses | Peirce Logic: Hardware Diagnosis | `res.num_viable >= 1` | Functional |
| 110 | L541 | trit range | Peirce Logic: Hardware Diagnosis | `res.confidence >= -1 && res.confidence <= 1` | Boundary |
| 111 | L544 | test_peirce_subjective | Peirce Logic: Hardware Diagnosis | `function-level test` | Arithmetic |
| 112 | L549 | T | Peirce Logic: Subjective Logic Abductio | `peirce_subjective_abduce(0.8, 0.1, 0.1, 0.33) == TRIT_TRUE` | Functional |
| 113 | L552 | F | Peirce Logic: Subjective Logic Abductio | `peirce_subjective_abduce(0.1, 0.8, 0.1, 0.33) == TRIT_FALSE` | Functional |
| 114 | L555 | U | Peirce Logic: Subjective Logic Abductio | `peirce_subjective_abduce(0.4, 0.4, 0.2, 0.33) == TRIT_UNKNOWN` | Functional |
| 115 | L562 | test_bct_encode_decode | Peirce Logic: Subjective Logic Abductio | `function-level test` | Encoding |
| 116 | L568 | 0x01 | BCT: Encode / Decode Trits | `b.code == BCT_NEG` | Functional |
| 117 | L572 | 0x03 | BCT: Encode / Decode Trits | `b.code == BCT_ZERO` | Functional |
| 118 | L576 | 0x02 | BCT: Encode / Decode Trits | `b.code == BCT_POS` | Functional |
| 119 | L580 | 0x00 | BCT: Encode / Decode Trits | `b.code == BCT_FAULT_CODE` | Functional |
| 120 | L583 | -1 | BCT: Encode / Decode Trits | `mrbct_decode_trit(mrbct_encode_trit(-1)) == -1` | Functional |
| 121 | L586 | 0 | BCT: Encode / Decode Trits | `mrbct_decode_trit(mrbct_encode_trit(0)) == 0` | Functional |
| 122 | L589 | +1 | BCT: Encode / Decode Trits | `mrbct_decode_trit(mrbct_encode_trit(1)) == 1` | Functional |
| 123 | L594 | -2 fault | BCT: Encode / Decode Trits | `mrbct_decode_trit(fault) == -2` | Functional |
| 124 | L597 | test_bct_sti | BCT: Encode / Decode Trits | `function-level test` | Functional |
| 125 | L604 | +1 | BCT: STI (Cross-Wiring Inversion) | `mrbct_decode_trit(out) == 1` | Functional |
| 126 | L609 | -1 | BCT: STI (Cross-Wiring Inversion) | `mrbct_decode_trit(out) == -1` | Functional |
| 127 | L614 | 0 | BCT: STI (Cross-Wiring Inversion) | `mrbct_decode_trit(out) == 0` | Functional |
| 128 | L617 | test_bct_pack_unpack | BCT: STI (Cross-Wiring Inversion) | `function-level test` | Encoding |
| 129 | L625 | pack ok | BCT: Pack / Unpack Words | `mrbct_pack_word(&word, trits, 5) == 0` | Encoding |
| 130 | L628 | len 5 | BCT: Pack / Unpack Words | `word.length == 5` | Functional |
| 131 | L632 | unpack ok | BCT: Pack / Unpack Words | `mrbct_unpack_word(&word, unpacked, 5) == 5` | Encoding |
| 132 | L638 | data matches | BCT: Pack / Unpack Words | `match` | Functional |
| 133 | L641 | test_radix_conversion | BCT: Pack / Unpack Words | `function-level test` | Functional |
| 134 | L647 | zero | BCT: Radix Conversio | `r.valid && r.trit_count == 0` | Functional |
| 135 | L651 | 1 | BCT: Radix Conversio | `r.valid && r.trits[0] == 1` | Functional |
| 136 | L655 | -1 | BCT: Radix Conversio | `r.valid && r.trits[0] == -1` | Functional |
| 137 | L658 | round trip | BCT: Radix Conversio | `mrbct_round_trip_b2t2b(13, 8) == 1` | Functional |
| 138 | L661 | round trip | BCT: Radix Conversio | `mrbct_round_trip_b2t2b(-7, 8) == 1` | Functional |
| 139 | L664 | round trip | BCT: Radix Conversio | `mrbct_round_trip_b2t2b(100, 12) == 1` | Functional |
| 140 | L668 | t2b2t | BCT: Radix Conversio | `mrbct_round_trip_t2b2t(t, 3) == 1` | Functional |
| 141 | L672 | overflow | BCT: Radix Conversio | `r.overflow == 1` | Boundary |
| 142 | L675 | test_heptavintimal | BCT: Radix Conversio | `function-level test` | Functional |
| 143 | L681 | char 0 | BCT: Heptavintimal Notatio | `h == '0'` | Functional |
| 144 | L685 | char D | BCT: Heptavintimal Notatio | `h == 'D'` | Functional |
| 145 | L689 | char Q | BCT: Heptavintimal Notatio | `h == 'Q'` | Functional |
| 146 | L693 | decode ok | BCT: Heptavintimal Notatio | `mrbct_heptv_to_trits('D', &t2, &t1, &t0) == 0` | Encoding |
| 147 | L694 | trits match | BCT: Heptavintimal Notatio | `t2 == 0 && t1 == 0 && t0 == 0` | Functional |
| 148 | L700 | 2 characters | BCT: Heptavintimal Notatio | `n == 2` | Functional |
| 149 | L701 | 0D | BCT: Heptavintimal Notatio | `out[0] == '0' && out[1] == 'D'` | Functional |
| 150 | L704 | test_radix_economy | BCT: Heptavintimal Notatio | `function-level test` | Functional |
| 151 | L710 | valid | BCT: Radix Economy Analysis | `e2.radix == 2 && e2.digits_for_range > 0` | Functional |
| 152 | L714 | valid | BCT: Radix Economy Analysis | `e3.radix == 3 && e3.digits_for_range > 0` | Functional |
| 153 | L717 | log2(3) > log2(2) | BCT: Radix Economy Analysis | `e3.info_per_digit > e2.info_per_digit` | Functional |
| 154 | L722 | radices correct | BCT: Radix Economy Analysis | `r2.radix == 2 && r3.radix == 3` | Functional |
| 155 | L725 | test_mrcs_synthesis | BCT: Radix Economy Analysis | `function-level test` | Functional |
| 156 | L732 | at least 1 gate | BCT: MRCS Gate-Level Synthesis | `n >= 1` | Logic |
| 157 | L735 | I/O | BCT: MRCS Gate-Level Synthesis | `ckt.num_inputs == 1 && ckt.num_outputs == 1` | Functional |
| 158 | L738 | 0 transistors | BCT: MRCS Gate-Level Synthesis | `mrcs_gate_cost(MRCS_GATE_STI) == 0` | Functional |
| 159 | L741 | 6 transistors | BCT: MRCS Gate-Level Synthesis | `mrcs_gate_cost(MRCS_GATE_MUX21) == 6` | Functional |
| 160 | L745 | at least 1 gate | BCT: MRCS Gate-Level Synthesis | `n >= 1` | Logic |
| 161 | L748 | null guard | BCT: MRCS Gate-Level Synthesis | `mrcs_synthesize(NULL, "N0P", 1, 1) == -1` | Negative/error |
| 162 | L751 | test_bct_engine_init | BCT: MRCS Gate-Level Synthesis | `function-level test` | Initialization |
| 163 | L757 | init ok | BCT: Engine Init | `mrbct_init(&eng, 6, 10) == 0` | Initialization |
| 164 | L760 | init | BCT: Engine Init | `eng.initialized == 1` | Initialization |
| 165 | L763 | 6 | BCT: Engine Init | `eng.default_trit_width == 6` | Functional |
| 166 | L766 | null guard | BCT: Engine Init | `mrbct_init(NULL, 6, 10) == -1` | Negative/error |
| 167 | L773 | test_rebel2_init | BCT: Engine Init | `function-level test` | Initialization |
| 168 | L779 | init ok | REBEL-2 ISA: CPU Initializatio | `rebel2_init(&cpu) == 0` | Initialization |
| 169 | L782 | init | REBEL-2 ISA: CPU Initializatio | `cpu.initialized == 1` | Initialization |
| 170 | L785 | pc 0 | REBEL-2 ISA: CPU Initializatio | `cpu.pc == 0` | Functional |
| 171 | L788 | not halted | REBEL-2 ISA: CPU Initializatio | `cpu.halted == 0` | Logic |
| 172 | L791 | 0 cycles | REBEL-2 ISA: CPU Initializatio | `cpu.cycle_count == 0` | Performance |
| 173 | L794 | null guard | REBEL-2 ISA: CPU Initializatio | `rebel2_init(NULL) == -1` | Negative/error |
| 174 | L797 | test_rebel2_alu | REBEL-2 ISA: CPU Initializatio | `function-level test` | Hardware/ALU |
| 175 | L809 | 8 | REBEL-2 ISA: ALU Operations | `rebel2_trits_to_int(r, 6) == 8` | Functional |
| 176 | L815 | 0 | REBEL-2 ISA: ALU Operations | `rebel2_trits_to_int(r, 6) == 0` | Functional |
| 177 | L821 | 0 | REBEL-2 ISA: ALU Operations | `rebel2_trits_to_int(r, 6) == 0` | Functional |
| 178 | L826 | +1 | REBEL-2 ISA: ALU Operations | `rebel2_alu_comp(a, b, 6) == R2_CMP_POSITIVE` | Functional |
| 179 | L829 | -1 | REBEL-2 ISA: ALU Operations | `rebel2_alu_comp(b, a, 6) == R2_CMP_NEGATIVE` | Functional |
| 180 | L832 | 0 | REBEL-2 ISA: ALU Operations | `rebel2_alu_comp(a, a, 6) == R2_CMP_ZERO` | Functional |
| 181 | L837 | -5 | REBEL-2 ISA: ALU Operations | `rebel2_trits_to_int(r, 6) == -5` | Functional |
| 182 | L845 | in range | REBEL-2 ISA: ALU Operations | `min_val >= -364 && min_val <= 364` | Boundary |
| 183 | L850 | in range | REBEL-2 ISA: ALU Operations | `max_val >= -364 && max_val <= 364` | Boundary |
| 184 | L853 | test_rebel2_int_trits | REBEL-2 ISA: ALU Operations | `function-level test` | Functional |
| 185 | L864 | zeros | REBEL-2 ISA: Int ↔ Trits Conversio | `all_zero` | Functional |
| 186 | L868 | 1 | REBEL-2 ISA: Int ↔ Trits Conversio | `rebel2_trits_to_int(trits, 6) == 1` | Functional |
| 187 | L872 | -1 | REBEL-2 ISA: Int ↔ Trits Conversio | `rebel2_trits_to_int(trits, 6) == -1` | Functional |
| 188 | L876 | 42 | REBEL-2 ISA: Int ↔ Trits Conversio | `rebel2_trits_to_int(trits, 6) == 42` | Functional |
| 189 | L880 | -100 | REBEL-2 ISA: Int ↔ Trits Conversio | `rebel2_trits_to_int(trits, 6) == -100` | Functional |
| 190 | L883 | test_rebel2_program | REBEL-2 ISA: Int ↔ Trits Conversio | `function-level test` | Functional |
| 191 | L897 | load ok | REBEL-2 ISA: Program Executio | `rebel2_load_program(&cpu, prog, 1) == 0` | Functional |
| 192 | L901 | step ok | REBEL-2 ISA: Program Executio | `rebel2_step(&cpu, &trace) == 0` | Functional |
| 193 | L904 | 8 | REBEL-2 ISA: Program Executio | `rebel2_get_reg(&cpu, 2) == 8` | Functional |
| 194 | L907 | pc=1 | REBEL-2 ISA: Program Executio | `cpu.pc == 1` | Functional |
| 195 | L910 | halted | REBEL-2 ISA: Program Executio | `cpu.halted == 1` | Functional |
| 196 | L913 | ADD | REBEL-2 ISA: Program Executio | `trace.opcode == R2_OP_ADD` | Arithmetic |
| 197 | L916 | rd=2 | REBEL-2 ISA: Program Executio | `trace.reg_written == 2` | Functional |
| 198 | L919 | test_rebel2_multi_instr | REBEL-2 ISA: Program Executio | `function-level test` | Arithmetic |
| 199 | L936 | 3 cycles | REBEL-2 ISA: Multi-Instruction Ru | `cycles == 3` | Performance |
| 200 | L939 | 17 | REBEL-2 ISA: Multi-Instruction Ru | `rebel2_get_reg(&cpu, 2) == 17` | Functional |
| 201 | L942 | -17 | REBEL-2 ISA: Multi-Instruction Ru | `rebel2_get_reg(&cpu, 3) == -17` | Functional |
| 202 | L945 | +1 | REBEL-2 ISA: Multi-Instruction Ru | `rebel2_get_reg(&cpu, 4) == 1` | Functional |
| 203 | L948 | halted | REBEL-2 ISA: Multi-Instruction Ru | `cpu.halted == 1` | Functional |
| 204 | L951 | test_rebel2_set_get_reg | REBEL-2 ISA: Multi-Instruction Ru | `function-level test` | Functional |
| 205 | L958 | set ok | REBEL-2 ISA: Register Access | `rebel2_set_reg(&cpu, 0, 42) == 0` | Functional |
| 206 | L961 | 42 | REBEL-2 ISA: Register Access | `rebel2_get_reg(&cpu, 0) == 42` | Functional |
| 207 | L965 | -33 | REBEL-2 ISA: Register Access | `rebel2_get_reg(&cpu, 1) == -33` | Functional |
| 208 | L968 | bounds | REBEL-2 ISA: Register Access | `rebel2_set_reg(&cpu, 100, 0) == -1` | Boundary |
| 209 | L975 | test_mmem_init | REBEL-2 ISA: Register Access | `function-level test` | Initialization |
| 210 | L981 | init ok | Memristive Memory: Initializatio | `mmem_init(&arr, 8, 4, 1) == 0` | Initialization |
| 211 | L984 | init | Memristive Memory: Initializatio | `arr.initialized == 1` | Initialization |
| 212 | L987 | 8 words | Memristive Memory: Initializatio | `arr.num_words == 8` | Functional |
| 213 | L990 | 4 trits | Memristive Memory: Initializatio | `arr.word_width == 4` | Functional |
| 214 | L993 | 1 check trit | Memristive Memory: Initializatio | `arr.ecc_width == 1` | Type system |
| 215 | L996 | null guard | Memristive Memory: Initializatio | `mmem_init(NULL, 8, 4, 1) == -1` | Negative/error |
| 216 | L999 | 0 words | Memristive Memory: Initializatio | `mmem_init(&arr, 0, 4, 1) == -1` | Functional |
| 217 | L1002 | 0 width | Memristive Memory: Initializatio | `mmem_init(&arr, 8, 0, 1) == -1` | Functional |
| 218 | L1005 | test_mmem_write_read | Memristive Memory: Initializatio | `function-level test` | Functional |
| 219 | L1014 | write ok | Memristive Memory: Write + Read | `mmem_write(&arr, 0, data, 4) == 0` | Functional |
| 220 | L1018 | valid | Memristive Memory: Write + Read | `res.valid == 1` | Functional |
| 221 | L1025 | 4 trits | Memristive Memory: Write + Read | `res.length == 4` | Functional |
| 222 | L1028 | bounds | Memristive Memory: Write + Read | `mmem_write(&arr, -1, data, 4) == -1` | Boundary |
| 223 | L1029 | bounds | Memristive Memory: Write + Read | `mmem_write(&arr, 100, data, 4) == -1` | Boundary |
| 224 | L1032 | test_mmem_resistance_mapping | Memristive Memory: Write + Read | `function-level test` | Transformation |
| 225 | L1038 | LRS range | Memristive Memory: Resistance ↔ Trit Mapping | `r < 3000.0` | Boundary |
| 226 | L1042 | HRS range | Memristive Memory: Resistance ↔ Trit Mapping | `r > 7500.0` | Boundary |
| 227 | L1046 | IRS range | Memristive Memory: Resistance ↔ Trit Mapping | `r >= 3000.0 && r <= 7500.0` | Boundary |
| 228 | L1049 | +1 | Memristive Memory: Resistance ↔ Trit Mapping | `mmem_resistance_to_trit(1000.0) == 1` | Functional |
| 229 | L1052 | 0 | Memristive Memory: Resistance ↔ Trit Mapping | `mmem_resistance_to_trit(5000.0) == 0` | Functional |
| 230 | L1055 | -1 | Memristive Memory: Resistance ↔ Trit Mapping | `mmem_resistance_to_trit(10000.0) == -1` | Functional |
| 231 | L1058 | test_mmem_drift | Memristive Memory: Resistance ↔ Trit Mapping | `function-level test` | Functional |
| 232 | L1068 | 4 drifted | Memristive Memory: Drift Simulatio | `drifted == 4` | Functional |
| 233 | L1072 | drift count | Memristive Memory: Drift Simulatio | `arr.drift_simulated >= 4` | Functional |
| 234 | L1083 | some drifted to zero | Memristive Memory: Drift Simulatio | `zeros >= 2` | Functional |
| 235 | L1086 | test_mmem_stuck | Memristive Memory: Drift Simulatio | `function-level test` | Functional |
| 236 | L1095 | stuck ok | Memristive Memory: Stuck-At Fault | `mmem_simulate_stuck(&arr, 0, 2) == 0` | Functional |
| 237 | L1099 | stuck at 0 | Memristive Memory: Stuck-At Fault | `res.data[2] == 0` | Functional |
| 238 | L1102 | ok | Memristive Memory: Stuck-At Fault | `res.data[0] == 1 && res.data[1] == 1 && res.data[3] == 1` | Functional |
| 239 | L1105 | test_mmem_ecc | Memristive Memory: Stuck-At Fault | `function-level test` | Functional |
| 240 | L1119 | non-negative corrections | Memristive Memory: ECC Stabilizatio | `corrections >= 0` | Negative/error |
| 241 | L1124 | writes tracked | Memristive Memory: ECC Stabilizatio | `tw >= 1` | Functional |
| 242 | L1127 | test_mmem_stats | Memristive Memory: ECC Stabilizatio | `function-level test` | Functional |
| 243 | L1140 | 1 write | Memristive Memory: Statistics | `tw == 1` | Functional |
| 244 | L1143 | 1 read | Memristive Memory: Statistics | `tr == 1` | Functional |
| 245 | L1146 | 0 corrections | Memristive Memory: Statistics | `ec == 0` | Functional |
| 246 | L1153 | test_mcp_server_init | Memristive Memory: Statistics | `function-level test` | Initialization |
| 247 | L1159 | init ok | MCP Server: Initializatio | `mcp_server_init(&srv) == 0` | Initialization |
| 248 | L1162 | init | MCP Server: Initializatio | `srv.initialized == 1` | Initialization |
| 249 | L1165 | 14 tools | MCP Server: Initializatio | `mcp_list_tools(&srv) == 14` | Functional |
| 250 | L1168 | 10 resources | MCP Server: Initializatio | `mcp_list_resources(&srv) == 10` | Functional |
| 251 | L1171 | shutdown ok | MCP Server: Initializatio | `mcp_server_shutdown(&srv) == 0` | Functional |
| 252 | L1174 | null guard | MCP Server: Initializatio | `mcp_server_init(NULL) == -1` | Negative/error |
| 253 | L1177 | test_mcp_trit_ops | MCP Server: Initializatio | `function-level test` | Functional |
| 254 | L1192 | status T | MCP Server: Trit Operations (K₃) | `r.status == MCP_STATUS_TRUE` | Functional |
| 255 | L1195 | F | MCP Server: Trit Operations (K₃) | `r.has_trit && r.result_trit == TRIT_FALSE` | Functional |
| 256 | L1207 | U | MCP Server: Trit Operations (K₃) | `r.has_trit && r.result_trit == TRIT_UNKNOWN` | Functional |
| 257 | L1219 | T | MCP Server: Trit Operations (K₃) | `r.has_trit && r.result_trit == TRIT_TRUE` | Functional |
| 258 | L1230 | F | MCP Server: Trit Operations (K₃) | `r.has_trit && r.result_trit == TRIT_FALSE` | Functional |
| 259 | L1241 | U | MCP Server: Trit Operations (K₃) | `r.has_trit && r.result_trit == TRIT_UNKNOWN` | Functional |
| 260 | L1247 | test_mcp_bct | MCP Server: Trit Operations (K₃) | `function-level test` | Functional |
| 261 | L1259 | status T | MCP Server: BCT Encode / Decode | `r.status == MCP_STATUS_TRUE` | Functional |
| 262 | L1262 | 0x02 | MCP Server: BCT Encode / Decode | `r.has_int && r.result_int == BCT_POS` | Functional |
| 263 | L1271 | -1 | MCP Server: BCT Encode / Decode | `r.has_trit && r.result_trit == -1` | Functional |
| 264 | L1280 | fault | MCP Server: BCT Encode / Decode | `r.status == MCP_STATUS_FALSE` | Functional |
| 265 | L1286 | test_mcp_radix | MCP Server: BCT Encode / Decode | `function-level test` | Functional |
| 266 | L1298 | status T | MCP Server: Radix Conversion + Economy | `r.status == MCP_STATUS_TRUE` | Functional |
| 267 | L1301 | has content | MCP Server: Radix Conversion + Economy | `r.content_len > 0` | Functional |
| 268 | L1313 | status T | MCP Server: Radix Conversion + Economy | `r.status == MCP_STATUS_TRUE` | Functional |
| 269 | L1316 | efficiency > 0 | MCP Server: Radix Conversion + Economy | `r.has_double && r.result_double > 0.0` | Functional |
| 270 | L1329 | status T | MCP Server: Radix Conversion + Economy | `r.status == MCP_STATUS_TRUE` | Functional |
| 271 | L1332 | D | MCP Server: Radix Conversion + Economy | `r.has_int && r.result_int == (int32_t)'D'` | Functional |
| 272 | L1338 | test_mcp_peirce | MCP Server: Radix Conversion + Economy | `function-level test` | Functional |
| 273 | L1353 | status T | MCP Server: Peirce's Law + Decidability | `r.status == MCP_STATUS_TRUE` | Functional |
| 274 | L1356 | T | MCP Server: Peirce's Law + Decidability | `r.has_trit && r.result_trit == TRIT_TRUE` | Functional |
| 275 | L1368 | status U | MCP Server: Peirce's Law + Decidability | `r.status == MCP_STATUS_UNKNOWN` | Functional |
| 276 | L1371 | U | MCP Server: Peirce's Law + Decidability | `r.has_trit && r.result_trit == TRIT_UNKNOWN` | Functional |
| 277 | L1380 | status T | MCP Server: Peirce's Law + Decidability | `r.status == MCP_STATUS_TRUE` | Functional |
| 278 | L1383 | decided | MCP Server: Peirce's Law + Decidability | `r.has_int && r.result_int == 1` | Functional |
| 279 | L1392 | status U | MCP Server: Peirce's Law + Decidability | `r.status == MCP_STATUS_UNKNOWN` | Functional |
| 280 | L1395 | undecided | MCP Server: Peirce's Law + Decidability | `r.has_int && r.result_int == 0` | Functional |
| 281 | L1401 | test_mcp_hardware | MCP Server: Peirce's Law + Decidability | `function-level test` | Functional |
| 282 | L1416 | status T | MCP Server: Hardware Tools (ECC + REBEL-2) | `r.status == MCP_STATUS_TRUE` | Functional |
| 283 | L1419 | dist 1 | MCP Server: Hardware Tools (ECC + REBEL-2) | `r.has_int && r.result_int == 1` | Functional |
| 284 | L1431 | status T | MCP Server: Hardware Tools (ECC + REBEL-2) | `r.status == MCP_STATUS_TRUE` | Functional |
| 285 | L1434 | 17 | MCP Server: Hardware Tools (ECC + REBEL-2) | `r.has_int && r.result_int == 17` | Functional |
| 286 | L1442 | status U | MCP Server: Hardware Tools (ECC + REBEL-2) | `r.status == MCP_STATUS_UNKNOWN` | Functional |
| 287 | L1450 | status U | MCP Server: Hardware Tools (ECC + REBEL-2) | `r.status == MCP_STATUS_UNKNOWN` | Functional |
| 288 | L1456 | test_mcp_stats | MCP Server: Hardware Tools (ECC + REBEL-2) | `function-level test` | Functional |
| 289 | L1475 | 3 calls | MCP Server: K₃ Statistics | `total == 3` | Functional |
| 290 | L1478 | 1 T | MCP Server: K₃ Statistics | `tc == 1` | Functional |
| 291 | L1481 | 1 U | MCP Server: K₃ Statistics | `uc == 1` | Functional |
| 292 | L1484 | 1 F | MCP Server: K₃ Statistics | `fc == 1` | Functional |
| 293 | L1489 | test_mcp_tool_not_found | MCP Server: K₃ Statistics | `function-level test` | Functional |
| 294 | L1497 | F | MCP Server: Tool Not Found | `r.status == MCP_STATUS_FALSE` | Functional |
| 295 | L1500 | error msg | MCP Server: Tool Not Found | `strstr(r.content, "not found") != NULL` | Negative/error |
| 296 | L1505 | test_mcp_params | MCP Server: Tool Not Found | `function-level test` | Functional |
| 297 | L1511 | name correct | MCP Server: Parameter Helpers | `strcmp(pi.name, "value") == 0` | Functional |
| 298 | L1514 | 42 | MCP Server: Parameter Helpers | `pi.has_int && pi.int_value == 42` | Functional |
| 299 | L1518 | name correct | MCP Server: Parameter Helpers | `strcmp(pt.name, "flag") == 0` | Functional |
| 300 | L1521 | +1 | MCP Server: Parameter Helpers | `pt.has_trit && pt.trit_value == 1` | Functional |
| 301 | L1524 | test_mcp_register_custom | MCP Server: Parameter Helpers | `function-level test` | Hardware/ALU |
| 302 | L1535 | registered | MCP Server: Custom Tool + Resource Registratio | `idx >= 0` | Hardware/ALU |
| 303 | L1538 | count+1 | MCP Server: Custom Tool + Resource Registratio | `mcp_list_tools(&srv) == initial_tools + 1` | Functional |
| 304 | L1545 | registered | MCP Server: Custom Tool + Resource Registratio | `idx >= 0` | Hardware/ALU |
| 305 | L1548 | count+1 | MCP Server: Custom Tool + Resource Registratio | `mcp_list_resources(&srv) == initial_res + 1` | Functional |
| 306 | L1553 | test_mcp_missing_params | MCP Server: Custom Tool + Resource Registratio | `function-level test` | Functional |
| 307 | L1561 | F | MCP Server: Missing Parameter Guards | `r.status == MCP_STATUS_FALSE` | Functional |
| 308 | L1566 | F | MCP Server: Missing Parameter Guards | `r.status == MCP_STATUS_FALSE` | Functional |
| 309 | L1571 | F | MCP Server: Missing Parameter Guards | `r.status == MCP_STATUS_FALSE` | Functional |

---

## Suite 38: Hybrid AI Integration

**Source**: `tests/test_hybrid_ai.c`
**Runtime Assertions**: 280
**Source-Level Entries**: 292
**Harness**: Named `test_*()` functions — each runs independently
**Output Reading**: Each function prints PASS/FAIL. Summary: N passed, M failed.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L58 | test_trq_init | Test Harness | `function-level test` | Initialization |
| 2 | L63 | trq_init failed | Test Harness | `trq_init(&st) == 0` | Negative/error |
| 3 | L66 | initialized not set | Test Harness | `st.initialized == 1` | Logic |
| 4 | L69 | should reject NULL | Test Harness | `trq_init(NULL) == -1` | Negative/error |
| 5 | L72 | dim should start at 0 | Test Harness | `st.dim == 0` | Initialization |
| 6 | L75 | num_stages should start at 0 | Test Harness | `st.num_stages == 0` | Initialization |
| 7 | L78 | test_trq_load_weights | Test Harness | `function-level test` | Functional |
| 8 | L85 | load failed | Test Harness | `trq_load_weights(&st, w, 4) == 0` | Negative/error |
| 9 | L88 | dim not set | Test Harness | `st.dim == 4` | Logic |
| 10 | L91 | wrong original[0] | Test Harness | `st.original[0] == 500` | Functional |
| 11 | L94 | wrong original[3] | Test Harness | `st.original[3] == -800` | Functional |
| 12 | L97 | should reject NULL | Test Harness | `trq_load_weights(NULL, w, 4) == -1` | Negative/error |
| 13 | L100 | test_trq_quantize | Test Harness | `function-level test` | Functional |
| 14 | L108 | quantize failed | Test Harness | `trq_quantize_basic(&st, 100) == 0` | Negative/error |
| 15 | L111 | expected +1 | Test Harness | `st.stages[0].ternary[0] == 1` | Functional |
| 16 | L114 | expected -1 | Test Harness | `st.stages[0].ternary[1] == -1` | Functional |
| 17 | L121 | alpha should be positive | Test Harness | `st.stages[0].alpha > 0` | Functional |
| 18 | L124 | threshold should be non-negative | Test Harness | `st.stages[0].threshold >= 0` | Negative/error |
| 19 | L128 | counts don't sum to dim | Test Harness | `sum == 4` | Arithmetic |
| 20 | L131 | test_trq_iterative_fit | Test Harness | `function-level test` | Functional |
| 21 | L143 | ITF failed | Test Harness | `itf_mse >= 0` | Negative/error |
| 22 | L148 | MSE should be non-negative | Test Harness | `mse_after >= 0` | Negative/error |
| 23 | L151 | threshold should be non-negative | Test Harness | `st.stages[st.num_stages - 1].threshold >= 0` | Negative/error |
| 24 | L156 | test_trq_residual | Test Harness | `function-level test` | Functional |
| 25 | L165 | add_residual failed | Test Harness | `trq_add_residual(&st) >= 0` | Negative/error |
| 26 | L168 | should have at least 2 stages | Test Harness | `st.num_stages >= 2` | Parsing |
| 27 | L171 | reconstruct failed | Test Harness | `trq_reconstruct(&st) == 0` | Negative/error |
| 28 | L178 | test_trq_salient | Test Harness | `function-level test` | Functional |
| 29 | L187 | salient smooth should return count | Test Harness | `ns > 0` | Functional |
| 30 | L192 | expected 3 salient channels | Test Harness | `mask_sum == 3` | IPC |
| 31 | L195 | 900 should be salient | Test Harness | `st.salient_mask[0] == 1` | Functional |
| 32 | L198 | test_trq_compression | Test Harness | `function-level test` | Encoding |
| 33 | L212 | should have positive bits/weight | Test Harness | `bits_x100 > 0` | Functional |
| 34 | L215 | sparsity should be 0-100 | Test Harness | `sparsity >= 0 && sparsity <= 100` | Functional |
| 35 | L222 | test_tissue_create | Test Harness | `function-level test` | Functional |
| 36 | L230 | create failed | Test Harness | `tissue_create(&t, 0, 3, 2, 8, &pop) == 0` | Negative/error |
| 37 | L233 | wrong neuron count | Test Harness | `t.num_neurons == 8` | Functional |
| 38 | L236 | wrong input count | Test Harness | `t.num_inputs == 3` | Functional |
| 39 | L239 | wrong output count | Test Harness | `t.num_outputs == 2` | Functional |
| 40 | L242 | should have connections | Test Harness | `t.num_connections > 0` | Functional |
| 41 | L245 | too many connections | Test Harness | `t.num_connections <= TISSUE_MAX_CONNECTIONS` | Functional |
| 42 | L248 | should reject NULL | Test Harness | `tissue_create(NULL, 0, 3, 2, 8, &pop) == -1` | Negative/error |
| 43 | L251 | should reject 0 inputs | Test Harness | `tissue_create(&t, 0, 0, 2, 8, &pop) == -2` | Negative/error |
| 44 | L265 | invalid connection indices | Test Harness | `valid` | Negative/error |
| 45 | L273 | weights must be {-1,0,+1} | Test Harness | `ternary_ok` | Functional |
| 46 | L276 | test_tissue_forward | Test Harness | `function-level test` | Functional |
| 47 | L289 | forward failed | Test Harness | `tissue_forward(&t, input, output) == 0` | Negative/error |
| 48 | L296 | outputs must be {-1,0,+1} | Test Harness | `ok` | Functional |
| 49 | L299 | input neuron 0 should match | Test Harness | `t.activation[0] == (int)input[0]` | Functional |
| 50 | L302 | should reject NULL | Test Harness | `tissue_forward(NULL, input, output) == -1` | Negative/error |
| 51 | L305 | should reject NULL inputs | Test Harness | `tissue_forward(&t, NULL, output) == -1` | Negative/error |
| 52 | L308 | test_tissue_mutate | Test Harness | `function-level test` | Functional |
| 53 | L324 | mutate should return mutation count | Test Harness | `mc >= 0` | Functional |
| 54 | L333 | mutations occurred (may be 0 rarely) | Test Harness | `changes >= 0` | Functional |
| 55 | L341 | weights must stay {-1,0,+1} | Test Harness | `ternary_ok` | Functional |
| 56 | L344 | should reject NULL | Test Harness | `tissue_mutate(NULL, &pop) == -1` | Negative/error |
| 57 | L347 | test_tissue_crossover | Test Harness | `function-level test` | Functional |
| 58 | L359 | crossover failed | Test Harness | `nc >= 0` | Negative/error |
| 59 | L362 | input count mismatch | Test Harness | `child.num_inputs == 3` | Functional |
| 60 | L365 | output count mismatch | Test Harness | `child.num_outputs == 2` | Functional |
| 61 | L368 | child should have connections | Test Harness | `child.num_connections > 0` | Functional |
| 62 | L376 | child weights must be {-1,0,+1} | Test Harness | `ok` | Functional |
| 63 | L379 | should reject NULL | Test Harness | `tissue_crossover(NULL, &p2, &child, &pop) == -1` | Negative/error |
| 64 | L382 | test_tissue_evaluate | Test Harness | `function-level test` | Hardware/ALU |
| 65 | L404 | fitness should be non-negative | Test Harness | `fitness >= 0` | Negative/error |
| 66 | L407 | stored fitness should match return | Test Harness | `t.fitness_x1000 == fitness` | Functional |
| 67 | L410 | fitness is accuracy×1000, max 1000 | Test Harness | `fitness <= 1000` | Boundary |
| 68 | L421 | test_tissue_population | Test Harness | `function-level test` | Functional |
| 69 | L426 | pop init failed | Test Harness | `tissue_pop_init(&pop, 8, 3, 2, 8) == 0` | Negative/error |
| 70 | L429 | wrong pop size | Test Harness | `pop.pop_size == 8` | Functional |
| 71 | L435 | individuals should have 8 neurons | Test Harness | `ok` | Arithmetic |
| 72 | L441 | individuals should have 3 inputs | Test Harness | `ok` | Arithmetic |
| 73 | L456 | evolve should return best fitness >= 0 | Test Harness | `best >= 0` | Functional |
| 74 | L459 | generation should be 1 | Test Harness | `pop.generation == 1` | Functional |
| 75 | L467 | best should not be NULL | Test Harness | `best_t != NULL` | Negative/error |
| 76 | L470 | fitness should be non-negative | Test Harness | `best_t->fitness_x1000 >= 0` | Negative/error |
| 77 | L474 | stats failed | Test Harness | `tissue_pop_stats(&pop, &avg_f, &max_f, &avg_conn) == 0` | Negative/error |
| 78 | L477 | max should be >= avg | Test Harness | `max_f >= avg_f` | Boundary |
| 79 | L480 | avg connections should be non-negative | Test Harness | `avg_conn >= 0` | Negative/error |
| 80 | L487 | test_rpl_operations | Test Harness | `function-level test` | Functional |
| 81 | L491 | 1→1 = 1 | Test Harness | `rpl_implies(1000, 1000) == 1000` | Functional |
| 82 | L494 | 1→0 = 0 | Test Harness | `rpl_implies(1000, 0) == 0` | Functional |
| 83 | L497 | 0→1 = 1 | Test Harness | `rpl_implies(0, 1000) == 1000` | Functional |
| 84 | L500 | 0→0 = 1 | Test Harness | `rpl_implies(0, 0) == 1000` | Functional |
| 85 | L503 | 0.7→0.3 = 0.6 | Test Harness | `rpl_implies(700, 300) == 600` | Functional |
| 86 | L506 | ¬1 = 0 | Test Harness | `rpl_negate(1000) == 0` | Functional |
| 87 | L509 | ¬0 = 1 | Test Harness | `rpl_negate(0) == 1000` | Functional |
| 88 | L512 | ¬0.5 = 0.5 | Test Harness | `rpl_negate(500) == 500` | Functional |
| 89 | L515 | 1⊗1 = 1 | Test Harness | `rpl_strong_and(1000, 1000) == 1000` | Functional |
| 90 | L518 | 1⊗0.5 = 0.5 | Test Harness | `rpl_strong_and(1000, 500) == 500` | Functional |
| 91 | L521 | 0.6⊗0.6 = 0.2 | Test Harness | `rpl_strong_and(600, 600) == 200` | Functional |
| 92 | L524 | 0.3⊗0.3 = max(0,-0.4)=0 | Test Harness | `rpl_strong_and(300, 300) == 0` | Boundary |
| 93 | L527 | 0⊕0 = 0 | Test Harness | `rpl_strong_or(0, 0) == 0` | Functional |
| 94 | L530 | 0.5⊕0.5 = 1.0 | Test Harness | `rpl_strong_or(500, 500) == 1000` | Functional |
| 95 | L533 | clamped to 1000 | Test Harness | `rpl_strong_or(700, 800) == 1000` | Boundary |
| 96 | L536 | min(0.3,0.7) = 0.3 | Test Harness | `rpl_weak_and(300, 700) == 300` | Boundary |
| 97 | L539 | max(0.3,0.7) = 0.7 | Test Harness | `rpl_weak_or(300, 700) == 700` | Boundary |
| 98 | L542 | 0.5↔0.5 = 1.0 | Test Harness | `rpl_equiv(500, 500) == 1000` | Functional |
| 99 | L545 | 0↔1 = 0 | Test Harness | `rpl_equiv(0, 1000) == 0` | Functional |
| 100 | L548 | test_rpl_trit_bridge | Test Harness | `function-level test` | Functional |
| 101 | L552 | +1 → 1000 | Test Harness | `rpl_from_trit(TRIT_TRUE) == 1000` | Functional |
| 102 | L555 | 0 → 500 | Test Harness | `rpl_from_trit(TRIT_UNKNOWN) == 500` | Functional |
| 103 | L558 | -1 → 0 | Test Harness | `rpl_from_trit(TRIT_FALSE) == 0` | Functional |
| 104 | L561 | 900 → +1 | Test Harness | `rpl_to_trit(900) == TRIT_TRUE` | Functional |
| 105 | L564 | 500 → 0 | Test Harness | `rpl_to_trit(500) == TRIT_UNKNOWN` | Functional |
| 106 | L567 | 100 → -1 | Test Harness | `rpl_to_trit(100) == TRIT_FALSE` | Functional |
| 107 | L570 | test_rpl_context | Test Harness | `function-level test` | Scheduling |
| 108 | L575 | init failed | Test Harness | `rpl_init(&ctx) == 0` | Negative/error |
| 109 | L582 | should have 3 props | Test Harness | `ctx.num_props == 3` | Functional |
| 110 | L585 | rain should be 800 | Test Harness | `rpl_get_truth(&ctx, p0) == 800` | Functional |
| 111 | L593 | should have 2 rules | Test Harness | `ctx.num_rules == 2` | Functional |
| 112 | L597 | should take some steps | Test Harness | `steps > 0` | Functional |
| 113 | L600 | wet should be 700 | Test Harness | `rpl_get_truth(&ctx, p1) == 700` | Functional |
| 114 | L603 | umbrella should be 400 | Test Harness | `rpl_get_truth(&ctx, p2) == 400` | Functional |
| 115 | L606 | should converge | Test Harness | `ctx.converged == 1` | Functional |
| 116 | L609 | axiom provability | Test Harness | `rpl_get_provability(&ctx, p0) == 800` | Functional |
| 117 | L612 | wet should be provable | Test Harness | `rpl_get_provability(&ctx, p1) > 0` | Functional |
| 118 | L619 | test_rpl_mv_algebra | Test Harness | `function-level test` | Functional |
| 119 | L623 | ∣800-300∣ = 500 | Test Harness | `rpl_mv_distance(800, 300) == 500` | Functional |
| 120 | L626 | ∣300-800∣ = 500 | Test Harness | `rpl_mv_distance(300, 800) == 500` | Functional |
| 121 | L629 | 1×0.5 = 0.5 | Test Harness | `rpl_mv_ntimes(500, 1) == 500` | Functional |
| 122 | L632 | 0.5⊗0.5 = 0 | Test Harness | `rpl_mv_ntimes(500, 2) == 0` | Functional |
| 123 | L635 | 0.8⊗0.8 = 0.6 | Test Harness | `rpl_mv_ntimes(800, 2) == 600` | Functional |
| 124 | L638 | 1⊗1⊗... = 1 | Test Harness | `rpl_mv_ntimes(1000, 5) == 1000` | Functional |
| 125 | L641 | 800 ≥ 700 so implies=1000 | Test Harness | `rpl_at_least(800, 700) == 1` | Functional |
| 126 | L644 | 500 < 700 so implies<1000 | Test Harness | `rpl_at_least(500, 700) == 0` | Functional |
| 127 | L651 | test_epist_model | Test Harness | `function-level test` | Functional |
| 128 | L656 | init failed | Test Harness | `epist_init(&m) == 0` | Negative/error |
| 129 | L663 | should have 3 worlds | Test Harness | `m.num_worlds == 3` | Functional |
| 130 | L669 | should have 2 props | Test Harness | `m.num_props == 2` | Functional |
| 131 | L675 | should have 2 agents | Test Harness | `m.num_agents == 2` | Functional |
| 132 | L686 | should be true | Test Harness | `epist_get_val(&m, w0, p0) == TRIT_TRUE` | Functional |
| 133 | L689 | should be false | Test Harness | `epist_get_val(&m, w0, p1) == TRIT_FALSE` | Functional |
| 134 | L702 | actual_world = 0 | Test Harness | `m.actual_world == 0` | Functional |
| 135 | L732 | test_epist_distributed | Test Harness | `function-level test` | Functional |
| 136 | L763 | test_epist_common | Test Harness | `function-level test` | Functional |
| 137 | L794 | test_epist_hybrid | Test Harness | `function-level test` | Functional |
| 138 | L810 | no treasure here | Test Harness | `epist_at_nominal(&m, n0, p) == TRIT_FALSE` | Functional |
| 139 | L813 | treasure there | Test Harness | `epist_at_nominal(&m, n1, p) == TRIT_TRUE` | Functional |
| 140 | L816 | should have 2 nominals | Test Harness | `m.num_nominals == 2` | Boundary |
| 141 | L821 | test_epist_kd45 | Test Harness | `function-level test` | Functional |
| 142 | L838 | should be valid KD45 | Test Harness | `epist_check_kd45(&m, a) == 1` | Functional |
| 143 | L845 | should fail D axiom | Test Harness | `epist_check_kd45(&m, a) == 0` | Negative/error |
| 144 | L854 | test_del_announce | Test Harness | `function-level test` | Functional |
| 145 | L878 | del init failed | Test Harness | `del_init(&ctx, &m) == 0` | Negative/error |
| 146 | L887 | should remove w2 | Test Harness | `removed == 1` | Functional |
| 147 | L895 | should have 1 history entry | Test Harness | `ctx.history_len == 1` | Functional |
| 148 | L899 | should record prop | Test Harness | `h && h->prop == p` | Functional |
| 149 | L902 | should record removal count | Test Harness | `h && h->worlds_removed == 1` | Functional |
| 150 | L905 | 2 worlds should remain | Test Harness | `del_active_worlds(&ctx) == 2` | Functional |
| 151 | L910 | test_del_conditional | Test Harness | `function-level test` | Functional |
| 152 | L938 | test_del_event_model | Test Harness | `function-level test` | Functional |
| 153 | L943 | event init failed | Test Harness | `del_event_init(&em) == 0` | Negative/error |
| 154 | L949 | should have 2 events | Test Harness | `em.num_events == 2` | Functional |
| 155 | L964 | set designated failed | Test Harness | `del_event_set_designated(&em, e0) == 0` | Negative/error |
| 156 | L967 | should be event 0 | Test Harness | `em.designated_event == 0` | Functional |
| 157 | L972 | test_del_product_update | Test Harness | `function-level test` | Arithmetic |
| 158 | L1006 | should create product worlds | Test Harness | `nw > 0` | Arithmetic |
| 159 | L1009 | too many product worlds | Test Harness | `nw <= m.num_worlds * em.num_events` | Arithmetic |
| 160 | L1013 | should have 1 world | Test Harness | `nw == 1` | Functional |
| 161 | L1016 | coin should be TRUE | Test Harness | `epist_get_val(&out, 0, p) == TRIT_TRUE` | Functional |
| 162 | L1021 | test_del_belief_revision | Test Harness | `function-level test` | Functional |
| 163 | L1050 | should change plausibility | Test Harness | `changed > 0` | Functional |
| 164 | L1055 | should have at least 1 most plausible | Test Harness | `nbest >= 1` | Parsing |
| 165 | L1058 | w0 should be most plausible after revising toward TRUE | Test Harness | `best[0] == w0` | Functional |
| 166 | L1067 | test_council_setup | Test Harness | `function-level test` | Initialization |
| 167 | L1072 | init failed | Test Harness | `council_init(&c) == 0` | Negative/error |
| 168 | L1078 | should have 2 props | Test Harness | `c.num_props == 2` | Functional |
| 169 | L1087 | should have 4 agents | Test Harness | `c.num_agents == 4` | Functional |
| 170 | L1090 | Sensor confidence = 900 | Test Harness | `c.agents[a0].confidence == 900` | Logic |
| 171 | L1104 | Sensor climate = 900 | Test Harness | `c.agents[a0].truth[p0] == 900` | Logic |
| 172 | L1109 | test_council_deliberate | Test Harness | `function-level test` | Functional |
| 173 | L1125 | should produce audit entries | Test Harness | `entries > 0` | Functional |
| 174 | L1128 | should complete all phases | Test Harness | `c.phase == SABHA_NUM_PHASES` | Functional |
| 175 | L1131 | should converge | Test Harness | `c.converged == 1` | Functional |
| 176 | L1135 | consensus should be > 0 | Test Harness | `cons > 0` | Consensus |
| 177 | L1138 | consensus should be [0,1000] | Test Harness | `cons >= 0 && cons <= 1000` | Consensus |
| 178 | L1142 | C should have been revised up | Test Harness | `c.agents[a2].truth[p0] > 200` | Functional |
| 179 | L1146 | verdict should not be NULL | Test Harness | `v != NULL` | Negative/error |
| 180 | L1149 | valid mode | Test Harness | `v->mode >= 0 && v->mode < COUNCIL_SYAD_VALUES` | Functional |
| 181 | L1155 | verdict trits must be {-1,0,+1} | Test Harness | `trit_ok` | Functional |
| 182 | L1160 | test_council_syad | Test Harness | `function-level test` | Functional |
| 183 | L1165 | should be asti | Test Harness | `v1.mode == SYAD_ASTI` | Parsing |
| 184 | L1169 | should be nasti | Test Harness | `v2.mode == SYAD_NASTI` | Parsing |
| 185 | L1173 | should be asti_nasti | Test Harness | `v3.mode == SYAD_ASTI_NASTI` | Parsing |
| 186 | L1177 | should be avaktavya | Test Harness | `v4.mode == SYAD_AVAKTAVYA` | Functional |
| 187 | L1181 | should be all | Test Harness | `v5.mode == SYAD_ALL` | Functional |
| 188 | L1192 | avaktavya inexpressible | Test Harness | `v4.t_inexpressible == TRIT_TRUE` | Functional |
| 189 | L1196 | should return name | Test Harness | `name != NULL && strlen(name) > 0` | Functional |
| 190 | L1203 | all modes should have names | Test Harness | `all_named` | Functional |
| 191 | L1206 | test_council_badha | Test Harness | `function-level test` | Negative/error |
| 192 | L1225 | low conf should move more | Test Harness | `delta1 >= delta0` | Functional |
| 193 | L1228 | should increase toward 500 | Test Harness | `c.agents[a0].truth[p] > 100` | Functional |
| 194 | L1231 | should decrease toward 500 | Test Harness | `c.agents[a1].truth[p] < (int)old_a1` | Functional |
| 195 | L1236 | test_council_agreement | Test Harness | `function-level test` | Functional |
| 196 | L1252 | should be 1000 | Test Harness | `council_agreement(&c, p) == 1000` | Functional |
| 197 | L1261 | should be less than 1000 | Test Harness | `agree < 1000` | Functional |
| 198 | L1264 | should be non-negative | Test Harness | `agree >= 0` | Negative/error |
| 199 | L1269 | test_council_audit | Test Harness | `function-level test` | Functional |
| 200 | L1280 | should have audit entries | Test Harness | `c.audit_len > 0` | Functional |
| 201 | L1284 | should have first entry | Test Harness | `a != NULL` | Functional |
| 202 | L1287 | first entry step should be 0 | Test Harness | `a->step == 0` | Functional |
| 203 | L1290 | should return NULL | Test Harness | `council_get_audit(&c, -1) == NULL` | Negative/error |
| 204 | L1291 | should return NULL | Test Harness | `council_get_audit(&c, 9999) == NULL` | Negative/error |
| 205 | L1299 | test_trq_multi_stage | TRQ Extended | `function-level test` | Arithmetic |
| 206 | L1312 | should have 3 stages | TRQ Extended | `st.num_stages == 3` | Functional |
| 207 | L1316 | alpha should be positive | TRQ Extended | `st.stages[s].alpha > 0` | Functional |
| 208 | L1320 | MSE should be non-negative | TRQ Extended | `mse3 >= 0` | Negative/error |
| 209 | L1327 | should have non-zero reconstructed values | TRQ Extended | `any_nz` | Hardware/ALU |
| 210 | L1336 | ternary values must be {-1,0,+1} | TRQ Extended | `ok` | Hardware/ALU |
| 211 | L1343 | counts should sum to dim | TRQ Extended | `sum == 8` | Arithmetic |
| 212 | L1348 | test_tissue_topology | Tissue Extended | `function-level test` | Functional |
| 213 | L1358 | id should be 100 | Tissue Extended | `t.id == 100` | Functional |
| 214 | L1361 | should have 16 neurons | Tissue Extended | `t.num_neurons == 16` | Functional |
| 215 | L1368 | all connections should be feed-forward | Tissue Extended | `ff_ok` | Functional |
| 216 | L1371 | should have active connections | Tissue Extended | `t.active_connections > 0` | Functional |
| 217 | L1374 | valid sparsity | Tissue Extended | `t.sparsity_pct >= 0 && t.sparsity_pct <= 100` | Functional |
| 218 | L1377 | initial generation = 0 | Tissue Extended | `t.generation == 0` | Initialization |
| 219 | L1380 | initial fitness = 0 | Tissue Extended | `t.fitness_x1000 == 0` | Initialization |
| 220 | L1383 | initial mutations = 0 | Tissue Extended | `t.mutations == 0` | Initialization |
| 221 | L1395 | same input should give same output | Tissue Extended | `same` | Functional |
| 222 | L1398 | test_tissue_stress | Tissue Extended | `function-level test` | Stress |
| 223 | L1407 | create minimal | Tissue Extended | `tissue_create(&mini, 0, 1, 1, 2, &pop) == 0` | Boundary |
| 224 | L1412 | forward minimal | Tissue Extended | `tissue_forward(&mini, in1, out1) == 0` | Boundary |
| 225 | L1417 | should reject | Tissue Extended | `tissue_create(&bad, 0, 10, 10, 8, &pop) == -2` | Negative/error |
| 226 | L1426 | should have connections | Tissue Extended | `maxt.num_connections > 0` | Functional |
| 227 | L1433 | accumulated mutations >= 0 | Tissue Extended | `total_mut >= 0` | Arithmetic |
| 228 | L1434 | tracked mutations >= returned | Tissue Extended | `mini.mutations >= total_mut` | Functional |
| 229 | L1438 | test_rpl_inference_chain | RPL Extended | `function-level test` | Type system |
| 230 | L1453 | should converge within 20 steps | RPL Extended | `steps >= 0 && steps <= 20` | Functional |
| 231 | L1457 | B should have positive truth | RPL Extended | `bval > 0` | Functional |
| 232 | L1461 | C should have positive truth from chain | RPL Extended | `cval > 0` | Functional |
| 233 | L1464 | chain should attenuate truth values | RPL Extended | `bval >= cval` | Hardware/ALU |
| 234 | L1467 | provability of B > 0 | RPL Extended | `rpl_entailment_degree(&ctx, B) > 0` | Functional |
| 235 | L1470 | provability of C > 0 | RPL Extended | `rpl_entailment_degree(&ctx, C) > 0` | Functional |
| 236 | L1479 | axiom provability should match truth | RPL Extended | `aprov >= 900` | Functional |
| 237 | L1483 | test_epist_s5_model | Epistemic Extended | `function-level test` | Functional |
| 238 | L1512 | should know p | Epistemic Extended | `epist_knows(&m, a, w0, p) == TRIT_TRUE` | Functional |
| 239 | L1515 | CK of p should be true | Epistemic Extended | `epist_common(&m, w0, p) == TRIT_TRUE` | Functional |
| 240 | L1521 | should not know p | Epistemic Extended | `epist_knows(&m, a, w0, p) != TRIT_TRUE` | Logic |
| 241 | L1529 | S5 ⊃ KD45 | Epistemic Extended | `epist_check_kd45(&m, a) == 1` | Functional |
| 242 | L1535 | should be uncertain | Epistemic Extended | `k == TRIT_UNKNOWN ∣∣ k == TRIT_FALSE` | Functional |
| 243 | L1539 | test_del_history | DEL Extended | `function-level test` | Functional |
| 244 | L1558 | no history yet | DEL Extended | `dc.history_len == 0` | Functional |
| 245 | L1563 | one history entry | DEL Extended | `dc.history_len == 1` | Functional |
| 246 | L1567 | should have entry | DEL Extended | `h != NULL` | Functional |
| 247 | L1570 | should record prop | DEL Extended | `h->prop == p` | Functional |
| 248 | L1575 | two history entries | DEL Extended | `dc.history_len == 2` | Functional |
| 249 | L1578 | reject negative | DEL Extended | `del_get_history(&dc, -1) == NULL` | Negative/error |
| 250 | L1579 | reject out of bounds | DEL Extended | `del_get_history(&dc, 100) == NULL` | Boundary |
| 251 | L1582 | test_del_plausibility | DEL Extended | `function-level test` | Functional |
| 252 | L1611 | should find most plausible | DEL Extended | `n >= 1` | Functional |
| 253 | L1612 | w0 is most plausible | DEL Extended | `best[0] == w0` | Functional |
| 254 | L1618 | w0 should remain most plausible | DEL Extended | `n >= 1 && best[0] == w0` | Functional |
| 255 | L1622 | should have active worlds | DEL Extended | `n >= 1` | Functional |
| 256 | L1626 | test_council_multi_prop | Council Extended | `function-level test` | Arithmetic |
| 257 | L1644 | should produce audit entries | Council Extended | `audits > 0` | Functional |
| 258 | L1648 | should have verdict for p0 | Council Extended | `v0 != NULL` | Logic |
| 259 | L1652 | should have verdict for p1 | Council Extended | `v1 != NULL` | Logic |
| 260 | L1655 | should agree on weather | Council Extended | `council_agreement(&c, p0) > 500` | Functional |
| 261 | L1664 | p0 consensus > 0 | Council Extended | `cons_p0 > 0` | Consensus |
| 262 | L1668 | p1 consensus > 0 | Council Extended | `cons_p1 > 0` | Consensus |
| 263 | L1671 | valid syad mode | Council Extended | `v0->mode >= 0 && v0->mode <= 6` | Functional |
| 264 | L1672 | valid syad mode | Council Extended | `v1->mode >= 0 && v1->mode <= 6` | Functional |
| 265 | L1677 | test_council_edge_cases | Council Extended | `function-level test` | Functional |
| 266 | L1689 | should still produce audits | Council Extended | `audits > 0` | Functional |
| 267 | L1692 | 1 agent = perfect agreement | Council Extended | `council_agreement(&c, p) == 1000` | Performance |
| 268 | L1696 | should have verdict | Council Extended | `v != NULL` | Functional |
| 269 | L1709 | identical truths = agreement | Council Extended | `council_agreement(&c2, p2) == 1000` | Functional |
| 270 | L1714 | should be asti-nasti | Council Extended | `v2 != NULL && v2->mode == SYAD_ASTI_NASTI` | Parsing |
| 271 | L1723 | test_trq_tissue_integration | Council Extended | `function-level test` | Functional |
| 272 | L1739 | TRQ ternary values are valid trits | Council Extended | `ok` | Hardware/ALU |
| 273 | L1752 | forward ok | Council Extended | `tissue_forward(&t, tissue_in, tissue_out) == 0` | Functional |
| 274 | L1755 | valid output[0] | Council Extended | `tissue_out[0] >= -1 && tissue_out[0] <= 1` | Functional |
| 275 | L1756 | valid output[1] | Council Extended | `tissue_out[1] >= -1 && tissue_out[1] <= 1` | Functional |
| 276 | L1759 | test_rpl_epistemic_integration | Council Extended | `function-level test` | Functional |
| 277 | L1774 | wet should be positive | Council Extended | `wet_truth > 0` | Functional |
| 278 | L1794 | rain 800 → TRUE | Council Extended | `rain_trit == TRIT_TRUE` | Functional |
| 279 | L1797 | wet inferred | Council Extended | `wet_trit == TRIT_TRUE ∣∣ wet_trit == TRIT_UNKNOWN` | Type system |
| 280 | L1801 | should match RPL-derived value | Council Extended | `val == wet_trit` | Hardware/ALU |
| 281 | L1806 | test_del_council_integration | Council Extended | `function-level test` | Functional |
| 282 | L1829 | elimination count >= 0 | Council Extended | `elim >= 0` | Boundary |
| 283 | L1845 | should have verdict | Council Extended | `v != NULL` | Functional |
| 284 | L1849 | disagreement expected post-announcement | Council Extended | `agree < 1000` | Functional |
| 285 | L1850 | some agreement expected | Council Extended | `agree > 0` | Functional |
| 286 | L1855 | test_full_pipeline | Council Extended | `function-level test` | IPC |
| 287 | L1866 | should have at least 1 stage | Council Extended | `st.num_stages >= 1` | Parsing |
| 288 | L1881 | evolution should return fitness | Council Extended | `bf >= 0` | Functional |
| 289 | L1892 | deploy truth defined | Council Extended | `rpl_get_truth(&ctx, deploy) >= 0` | Functional |
| 290 | L1906 | should produce verdict | Council Extended | `v != NULL` | Functional |
| 291 | L1907 | valid syad mode | Council Extended | `v->mode >= 0 && v->mode <= 6` | Functional |
| 292 | L1910 | agents should have measurable agreement | Council Extended | `council_agreement(&c, dp) > 0` | Functional |

---

## Suite 39: Red-Team Stress & Performance

**Source**: `tests/test_stress.c`
**Runtime Assertions**: 979
**Source-Level Entries**: 144
**Harness**: `CHECK("desc", expr)` — prints `[PASS]`/`[FAIL]` with description
**Output Reading**: Summary: `passed N/T`. Section headers precede groups. Exit code 1 if failures.

> **Note**: 835 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L68 | alloc page succeeds | MEM: Full Allocation Sweep (256 pages) | `pages[i] >= 0` | Memory |
| 2 | L73 | OOM returns -1 | MEM: Full Allocation Sweep (256 pages) | `oom == -1` | Functional |
| 3 | L78 | total == 256 | MEM: Full Allocation Sweep (256 pages) | `total == SET6_MAX_PAGES` | Functional |
| 4 | L79 | free == 0 at OOM | MEM: Full Allocation Sweep (256 pages) | `fr == 0` | Memory |
| 5 | L80 | alloc == 256 at OOM | MEM: Full Allocation Sweep (256 pages) | `alloc == SET6_MAX_PAGES` | Memory |
| 6 | L85 | free page succeeds | MEM: Full Allocation Sweep (256 pages) | `rc == 0` | Memory |
| 7 | L88 | all pages freed | MEM: Full Allocation Sweep (256 pages) | `fr == SET6_MAX_PAGES` | Memory |
| 8 | L89 | alloc == 0 after free all | MEM: Full Allocation Sweep (256 pages) | `alloc == 0` | Memory |
| 9 | L97 | alloc ok | MEM: Double-Free Detectio | `p >= 0` | Memory |
| 10 | L99 | first free ok | MEM: Double-Free Detectio | `rc1 == 0` | Memory |
| 11 | L101 | double-free returns -1 | MEM: Double-Free Detectio | `rc2 == -1` | Memory |
| 12 | L108 | free(-1) fails | MEM: Invalid Index Boundary | `mem_free(&mem, -1) == -1` | Negative/error |
| 13 | L109 | free(16) fails | MEM: Invalid Index Boundary | `mem_free(&mem, 16) == -1` | Negative/error |
| 14 | L110 | free(9999) fails | MEM: Invalid Index Boundary | `mem_free(&mem, 9999) == -1` | Negative/error |
| 15 | L111 | read(-1) returns UNKNOWN | MEM: Invalid Index Boundary | `mem_read(&mem, -1, 0) == TRIT_UNKNOWN` | Functional |
| 16 | L112 | write(-1) fails | MEM: Invalid Index Boundary | `mem_write(&mem, -1, 0, TRIT_TRUE) == -1` | Negative/error |
| 17 | L120 | alloc ok | MEM: Offset Boundary | `p >= 0` | Memory |
| 18 | L124 | write at max offset ok | MEM: Offset Boundary | `w1 == 0` | Boundary |
| 19 | L126 | read at max offset = TRUE | MEM: Offset Boundary | `r1 == TRIT_TRUE` | Boundary |
| 20 | L129 | write at PAGE_TRITS fails | MEM: Offset Boundary | `mem_write(&mem, p, SET6_PAGE_TRITS, TRIT_TRUE) == -1` | Negative/error |
| 21 | L130 | write at -1 offset fails | MEM: Offset Boundary | `mem_write(&mem, p, -1, TRIT_TRUE) == -1` | Negative/error |
| 22 | L131 | read at PAGE_TRITS returns UNKNOWN | MEM: Offset Boundary | `mem_read(&mem, p, SET6_PAGE_TRITS) == TRIT_UNKNOWN` | Memory |
| 23 | L145 | re-alloc succeeds | MEM: Scrub-on-Free Guarantee | `p2 >= 0` | Memory |
| 24 | L150 | page is all-UNKNOWN after re-alloc (scrub guarantee) | MEM: Scrub-on-Free Guarantee | `clean` | Memory |
| 25 | L158 | reserve page 0 ok | MEM: Reserve and Allocation Interactio | `rc == 0` | Memory |
| 26 | L161 | alloc skips reserved page | MEM: Reserve and Allocation Interactio | `p != 0 && p >= 0` | Memory |
| 27 | L163 | write to reserved page fails | MEM: Reserve and Allocation Interactio | `mem_write(&mem, 0, 0, TRIT_TRUE) == -1` | Negative/error |
| 28 | L177 | 1000 alloc/free cycles stable | MEM: Rapid Alloc/Free Cycling | `ok` | Memory |
| 29 | L180 | all pages free after cycle | MEM: Rapid Alloc/Free Cycling | `alloc == 0` | Memory |
| 30 | L195 | create thread ok | SCHED: Create All 64 Threads | `tid >= 0` | Scheduling |
| 31 | L199 | 65th thread creation fails | SCHED: Create All 64 Threads | `overflow == -1` | Negative/error |
| 32 | L204 | total == 64 | SCHED: Create All 64 Threads | `total == SCHED_MAX_THREADS` | Functional |
| 33 | L217 | destroy ok | SCHED: Destroy All Then Re-Create | `rc == 0` | Functional |
| 34 | L223 | ready == 0 after destroy all | SCHED: Destroy All Then Re-Create | `ready == 0` | Functional |
| 35 | L230 | destroy(-1) fails | SCHED: Invalid TID Operations | `sched_destroy(&sched, -1) == -1` | Negative/error |
| 36 | L231 | destroy(64) fails | SCHED: Invalid TID Operations | `sched_destroy(&sched, SCHED_MAX_THREADS) == -1` | Negative/error |
| 37 | L232 | destroy(999) fails | SCHED: Invalid TID Operations | `sched_destroy(&sched, 999) == -1` | Negative/error |
| 38 | L233 | block(-1) fails | SCHED: Invalid TID Operations | `sched_block(&sched, -1, 0) == -1` | Negative/error |
| 39 | L234 | unblock(-1) fails | SCHED: Invalid TID Operations | `sched_unblock(&sched, -1) == -1` | Negative/error |
| 40 | L235 | set_priority(-1) fails | SCHED: Invalid TID Operations | `sched_set_priority(&sched, -1, TRIT_TRUE) == -1` | Negative/error |
| 41 | L247 | three threads created | SCHED: Priority Inversion Scenario | `lo >= 0 && mid >= 0 && hi >= 0` | Scheduling |
| 42 | L251 | high-priority picked first | SCHED: Priority Inversion Scenario | `next == hi` | Scheduling |
| 43 | L258 | normal picked when high blocked | SCHED: Priority Inversion Scenario | `next == mid` | Logic |
| 44 | L263 | high picked after unblock | SCHED: Priority Inversion Scenario | `next == hi` | Memory |
| 45 | L283 | 100 yields stable | SCHED: Yield Storm (100 yields) | `ok` | Scheduling |
| 46 | L289 | context switches counted | SCHED: Yield Storm (100 yields) | `cswitch >= 0` | Scheduling |
| 47 | L309 | pick_next with all blocked returns -1 | SCHED: Block All Then Pick | `next == -1` | Memory |
| 48 | L317 | create ok | SCHED: Priority Mutation Sweep | `tid >= 0` | Functional |
| 49 | L324 | set_priority ok | SCHED: Priority Mutation Sweep | `rc == 0` | Scheduling |
| 50 | L325 | priority matches | SCHED: Priority Mutation Sweep | `sched.threads[tid].priority == prios[i]` | Scheduling |
| 51 | L341 | create endpoint ok | IPC: Endpoint Saturation (32 endpoints) | `ep >= 0` | IPC |
| 52 | L345 | 33rd endpoint fails | IPC: Endpoint Saturation (32 endpoints) | `overflow == -1` | Negative/error |
| 53 | L354 | create notification ok | IPC: Notification Saturation (16 notifications) | `n >= 0` | IPC |
| 54 | L357 | 17th notification fails | IPC: Notification Saturation (16 notifications) | `overflow == -1` | Negative/error |
| 55 | L372 | send without receiver returns 1 (sender blocks) | IPC: Send Without Receiver | `rc == 1` | Memory |
| 56 | L383 | recv without sender returns 1 (receiver blocks) | IPC: Recv Without Sender | `rc == 1` | Memory |
| 57 | L398 | send on destroyed ep fails | IPC: send/recv on destroyed endpoint | `rc_send == -1` | Negative/error |
| 58 | L402 | recv on destroyed ep fails | IPC: send/recv on destroyed endpoint | `rc_recv == -1` | Negative/error |
| 59 | L414 | wait after signal returns 0 (already pending) | IPC: Notification Signal/Wait Cycle | `rc == 0` | Functional |
| 60 | L418 | wait without signal returns 1 (must block) | IPC: Notification Signal/Wait Cycle | `rc2 == 1` | Memory |
| 61 | L430 | send(-1) fails | IPC: Invalid Endpoint Indices | `ipc_send(&ipc, -1, &msg, 0) == -1` | Negative/error |
| 62 | L431 | send(32) fails | IPC: Invalid Endpoint Indices | `ipc_send(&ipc, IPC_MAX_ENDPOINTS, &msg, 0) == -1` | Negative/error |
| 63 | L432 | recv(-1) fails | IPC: Invalid Endpoint Indices | `ipc_recv(&ipc, -1, &msg, 0) == -1` | Negative/error |
| 64 | L433 | destroy(-1) fails | IPC: Invalid Endpoint Indices | `ipc_endpoint_destroy(&ipc, -1) == -1` | Negative/error |
| 65 | L452 | send without receiver returns 1 (buffered) | IPC: Message Integrity (Ternary Payload) | `rc_send == 1` | IPC |
| 66 | L457 | recv with buffered msg returns 0 (immediate) | IPC: Message Integrity (Ternary Payload) | `rc_recv == 0` | IPC |
| 67 | L464 | all 16 trit words delivered correctly | IPC: Message Integrity (Ternary Payload) | `match` | Functional |
| 68 | L465 | badge preserved | IPC: Message Integrity (Ternary Payload) | `recv_msg.sender_badge == 99` | Negative/error |
| 69 | L466 | sender_tid preserved | IPC: Message Integrity (Ternary Payload) | `recv_msg.sender_tid == 5` | IPC |
| 70 | L482 | cap create ok | CAPS: Fill All 64 Capabilities | `idx >= 0` | Access control |
| 71 | L486 | 65th cap fails | CAPS: Fill All 64 Capabilities | `overflow == -1` | Negative/error |
| 72 | L494 | cap created | CAPS: Revoke and Check | `c >= 0` | Access control |
| 73 | L506 | revoke ok | CAPS: Revoke and Check | `rc == 0` | Functional |
| 74 | L510 | check R after revoke != TRUE | CAPS: Revoke and Check | `post != TRIT_TRUE` | Type system |
| 75 | L518 | parent created | CAPS: Grant Narrows Rights | `parent >= 0` | Functional |
| 76 | L522 | child granted | CAPS: Grant Narrows Rights | `child >= 0` | Functional |
| 77 | L525 | child has R | CAPS: Grant Narrows Rights | `kernel_cap_check(&ks, child, 1) == TRIT_TRUE` | Functional |
| 78 | L526 | child lacks W | CAPS: Grant Narrows Rights | `kernel_cap_check(&ks, child, 2) != TRIT_TRUE` | Functional |
| 79 | L527 | child lacks G | CAPS: Grant Narrows Rights | `kernel_cap_check(&ks, child, 4) != TRIT_TRUE` | Functional |
| 80 | L539 | revoke(-1) fails | CAPS: Invalid Index Checks | `kernel_cap_revoke(&ks, -1) == -1` | Negative/error |
| 81 | L540 | grant(-1) fails | CAPS: Invalid Index Checks | `kernel_cap_grant(&ks, -1, 1) == -1` | Negative/error |
| 82 | L549 | parent + child created | CAPS: Revoke Cascade (revoke parent, check child) | `parent >= 0 && child >= 0` | Functional |
| 83 | L552 | child R valid | CAPS: Revoke Cascade (revoke parent, check child) | `kernel_cap_check(&ks, child, 1) == TRIT_TRUE` | Functional |
| 84 | L556 | parent revoked | CAPS: Revoke Cascade (revoke parent, check child) | `kernel_cap_check(&ks, parent, 1) != TRIT_TRUE` | Functional |
| 85 | L592 | syscall -1 returns error | SYSCALL: Out-of-Range Syscall Numbers | `r1.retval != 0` | Negative/error |
| 86 | L595 | syscall SYSCALL_COUNT returns error | SYSCALL: Out-of-Range Syscall Numbers | `r2.retval != 0` | Negative/error |
| 87 | L598 | syscall 9999 returns error | SYSCALL: Out-of-Range Syscall Numbers | `r3.retval != 0` | Negative/error |
| 88 | L601 | syscall -100 returns error | SYSCALL: Out-of-Range Syscall Numbers | `r4.retval != 0` | Negative/error |
| 89 | L612 | stack pointer at 64 | SYSCALL: Operand Stack Overflow / Underflow | `ks.operand_sp == 64` | Memory |
| 90 | L616 | stack pointer clamped at 64 | SYSCALL: Operand Stack Overflow / Underflow | `ks.operand_sp <= 64` | Boundary |
| 91 | L624 | underflow pop returns UNKNOWN | SYSCALL: Operand Stack Overflow / Underflow | `v == TRIT_UNKNOWN` | Boundary |
| 92 | L625 | sp never goes negative | SYSCALL: Operand Stack Overflow / Underflow | `ks.operand_sp >= 0` | Negative/error |
| 93 | L637 | MMAP dispatch succeeds | SYSCALL: MMAP page allocation via dispatch | `r.retval >= 0` | Transformation |
| 94 | L653 | DOT_TRIT dispatch ok | SYSCALL: DOT_TRIT computatio | `r.retval == 0 ∣∣ r.retval >= 0` | Functional |
| 95 | L654 | dot_acc updated | SYSCALL: DOT_TRIT computatio | `ks.mr.dot_total_ops > 0` | Functional |
| 96 | L666 | RADIX_CONV dispatch ok | SYSCALL: RADIX_CONV balanced ternary conversio | `r.retval == 0 ∣∣ r.retval >= 0` | Functional |
| 97 | L683 | thread 0 created | CROSS: Full Boot→Load→IPC→Teardown Cycle | `t0 >= 0` | Scheduling |
| 98 | L684 | thread 1 created | CROSS: Full Boot→Load→IPC→Teardown Cycle | `t1 >= 0` | Scheduling |
| 99 | L692 | pages for both threads | CROSS: Full Boot→Load→IPC→Teardown Cycle | `p0 >= 0 && p1 >= 0` | Logic |
| 100 | L701 | caps created | CROSS: Full Boot→Load→IPC→Teardown Cycle | `cap0 >= 0 && cap1 >= 0` | Access control |
| 101 | L705 | endpoint created | CROSS: Full Boot→Load→IPC→Teardown Cycle | `ep >= 0` | IPC |
| 102 | L718 | caps revoked | CROSS: Full Boot→Load→IPC→Teardown Cycle | `kernel_cap_check(&ks, cap0, 1) != TRIT_TRUE` | Access control |
| 103 | L724 | pages freed | CROSS: Full Boot→Load→IPC→Teardown Cycle | `alloc == 0` | Memory |
| 104 | L730 | no ready threads after destroy | CROSS: Full Boot→Load→IPC→Teardown Cycle | `rdy == 0` | Scheduling |
| 105 | L748 | 500 syscall storm survived | CROSS: Rapid Syscall Storm (500 dispatches) | `ok` | Functional |
| 106 | L758 | page + cap created | CROSS: Cap-Guarded Memory Access Patter | `page >= 0 && cap >= 0` | Memory |
| 107 | L762 | read cap = TRUE | CROSS: Cap-Guarded Memory Access Patter | `can_read == TRIT_TRUE` | Access control |
| 108 | L766 | guarded write ok | CROSS: Cap-Guarded Memory Access Patter | `mem_read(&ks.mem, page, 0) == TRIT_TRUE` | Functional |
| 109 | L772 | read right revoked | CROSS: Cap-Guarded Memory Access Patter | `denied != TRIT_TRUE` | Functional |
| 110 | L785 | different pages for different threads | CROSS: Multi-Thread Memory Isolatio | `p0 != p1` | Logic |
| 111 | L792 | t0 page has TRUE | CROSS: Multi-Thread Memory Isolatio | `mem_read(&ks.mem, p0, 0) == TRIT_TRUE` | Memory |
| 112 | L793 | t1 page has FALSE | CROSS: Multi-Thread Memory Isolatio | `mem_read(&ks.mem, p1, 0) == TRIT_FALSE` | Memory |
| 113 | L796 | p0 owned by t0 | CROSS: Multi-Thread Memory Isolatio | `ks.mem.pages[p0].owner_tid == t0` | Functional |
| 114 | L797 | p1 owned by t1 | CROSS: Multi-Thread Memory Isolatio | `ks.mem.pages[p1].owner_tid == t1` | Functional |
| 115 | L817 | AND truth table entry | TRIT: Kleene K₃ Full Truth Table Verificatio | `a_and == expected_and` | Logic |
| 116 | L822 | OR truth table entry | TRIT: Kleene K₃ Full Truth Table Verificatio | `a_or == expected_or` | Logic |
| 117 | L827 | NOT(T) = F | TRIT: Kleene K₃ Full Truth Table Verificatio | `trit_not(TRIT_TRUE) == TRIT_FALSE` | Functional |
| 118 | L828 | NOT(U) = U | TRIT: Kleene K₃ Full Truth Table Verificatio | `trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN` | Functional |
| 119 | L829 | NOT(F) = T | TRIT: Kleene K₃ Full Truth Table Verificatio | `trit_not(TRIT_FALSE) == TRIT_TRUE` | Functional |
| 120 | L841 | De Morgan AND->OR | TRIT: De Morgan's Law for Kleene Logic | `lhs == rhs` | Functional |
| 121 | L846 | De Morgan OR->AND | TRIT: De Morgan's Law for Kleene Logic | `lhs == rhs` | Functional |
| 122 | L855 | NOT(NOT(x)) == x | TRIT: Double Negatio | `trit_not(trit_not(vals[i])) == vals[i]` | Functional |
| 123 | L863 | x AND TRUE = x | TRIT: Identity Laws | `trit_and(vals[i], TRIT_TRUE) == vals[i]` | Logic |
| 124 | L864 | x OR FALSE = x | TRIT: Identity Laws | `trit_or(vals[i], TRIT_FALSE) == vals[i]` | Logic |
| 125 | L865 | x AND FALSE = FALSE | TRIT: Identity Laws | `trit_and(vals[i], TRIT_FALSE) == TRIT_FALSE` | Logic |
| 126 | L866 | x OR TRUE = TRUE | TRIT: Identity Laws | `trit_or(vals[i], TRIT_TRUE) == TRIT_TRUE` | Logic |
| 127 | L879 | implies = OR(NOT a, b) | TRIT: Implies & Equiv Consistency | `imp == exp_imp` | Logic |
| 128 | L885 | equiv identity | TRIT: Implies & Equiv Consistency | `eq == exp_eq` | Functional |
| 129 | L896 | pack/unpack roundtrip | TRIT: 2-Bit Pack/Unpack Roundtrip | `v == vals[i]` | Encoding |
| 130 | L921 | packed64 AND matches scalar | TRIT: Packed64 SIMD AND/OR | `ok` | Logic |
| 131 | L941 | DOT_TRIT on all-T ok | MRADX: DOT_TRIT on All-True Vectors | `r.retval >= 0` | Functional |
| 132 | L943 | dot_acc == 32 | MRADX: DOT_TRIT on All-True Vectors | `ks.mr.dot_acc == 32` | Functional |
| 133 | L957 | DOT_TRIT on unknown vec ok | MRADX: DOT_TRIT on Orthogonal (all-Unknown) | `r.retval >= 0` | Functional |
| 134 | L959 | dot_acc == 0 for unknown × true | MRADX: DOT_TRIT on Orthogonal (all-Unknown) | `ks.mr.dot_acc == 0` | Logic |
| 135 | L973 | FFT_STEP dispatch ok | MRADX: FFT_STEP Dispatch | `r.retval >= 0` | Functional |
| 136 | L989 | RADIX_CONV dispatch ok | MRADX: RADIX_CONV Roundtrip | `r.retval >= 0` | Functional |
| 137 | L1019 | alloc/free perf measured | PERF: mem_alloc/free throughput (10000 ops) | `ms >= 0` | Memory |
| 138 | L1038 | yield perf measured | PERF: sched_yield throughput (10000 yields) | `ms >= 0` | Scheduling |
| 139 | L1056 | syscall perf measured | PERF: syscall_dispatch throughput (10000 calls) | `ms >= 0` | Performance |
| 140 | L1075 | DOT_TRIT perf measured | PERF: DOT_TRIT throughput (10000 dot products) | `ms >= 0` | Performance |
| 141 | L1091 | cap_check perf measured | PERF: kernel_cap_check throughput (100000 checks) | `ms >= 0` | Access control |
| 142 | L1108 | packed64 AND perf measured | PERF: Kleene trit_and_packed64 throughput (1M packed ops) | `ms >= 0` | Logic |
| 143 | L1131 | IPC roundtrip perf measured | PERF: IPC send/recv roundtrip (1000 messages) | `ms >= 0` | IPC |
| 144 | L1150 | page write perf measured | PERF: Full page write (729 trits) | `ms >= 0` | Memory |

---

## Suite 40: Trithon Self-Test

**Source**: `trithon/trithon.py`
**Runtime Assertions**: 99
**Source-Level Entries**: 86
**Harness**: `check(condition, label)` — counted assertion, prints `[FAIL]` on failure
**Output Reading**: Summary: `Trithon: N passed, M failed (of T assertions)`. Exit 1 if failures.

> **Note**: 13 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L928 | Kleene: T&T==T | Kleene logic | `(T & T) == T` | Logic |
| 2 | L929 | Kleene: T&U==U | Kleene logic | `(T & U) == U` | Logic |
| 3 | L930 | Kleene: T&F==F | Kleene logic | `(T & F) == F` | Logic |
| 4 | L931 | Kleene: T∣U==T | Kleene logic | `(T ∣ U) == T` | Logic |
| 5 | L932 | Kleene: U∣F==U | Kleene logic | `(U ∣ F) == U` | Logic |
| 6 | L933 | Kleene: ~T==F | Kleene logic | `(~T) == F` | Logic |
| 7 | L934 | Kleene: ~U==U | Kleene logic | `(~U) == U` | Logic |
| 8 | L935 | Kleene: ~F==T | Kleene logic | `(~F) == T` | Logic |
| 9 | L938 | Mul: F*F==T | Multiplication | `(F * F) == T` | Arithmetic |
| 10 | L939 | Mul: F*T==F | Multiplication | `(F * T) == F` | Arithmetic |
| 11 | L940 | Mul: U*T==U | Multiplication | `(U * T) == U` | Arithmetic |
| 12 | L943 | Inc: T→F | Inc / Dec (cyclic | `T.inc() == F` | Functional |
| 13 | L944 | Inc: F→U | Inc / Dec (cyclic | `F.inc() == U` | Functional |
| 14 | L945 | Inc: U→T | Inc / Dec (cyclic | `U.inc() == T` | Functional |
| 15 | L946 | Dec: T→U | Inc / Dec (cyclic | `T.dec() == U` | Functional |
| 16 | L947 | Dec: U→F | Inc / Dec (cyclic | `U.dec() == F` | Functional |
| 17 | L948 | Dec: F→T | Inc / Dec (cyclic | `F.dec() == T` | Functional |
| 18 | L951 | Consensus: T,T→T | Consensus / Accept-any (named aliases | `T.consensus(T) == T` | Consensus |
| 19 | L952 | Consensus: T,F→F | Consensus / Accept-any (named aliases | `T.consensus(F) == F` | Consensus |
| 20 | L953 | Consensus: T,U→U | Consensus / Accept-any (named aliases | `T.consensus(U) == U` | Consensus |
| 21 | L954 | AcceptAny: T,F→T | Consensus / Accept-any (named aliases | `T.accept_any(F) == T` | Functional |
| 22 | L955 | AcceptAny: F,F→F | Consensus / Accept-any (named aliases | `F.accept_any(F) == F` | Functional |
| 23 | L956 | AcceptAny: U,F→U | Consensus / Accept-any (named aliases | `U.accept_any(F) == U` | Functional |
| 24 | L964 | Dot: 5-elem dot product | Dot product | `dot == (1*1 + 0*1 + (-1)*1 + 1*(-1) + 0*0)` | Arithmetic |
| 25 | L968 | Sparse dot: returns int | Sparse dot | `isinstance(dot_s, int)` | Parsing |
| 26 | L972 | Array Kleene AND: c[0]==T | Kleene ops | `c[0] == Trit.TRUE` | Logic |
| 27 | L973 | Array Kleene AND: c[1]==U | Kleene ops | `c[1] == Trit.UNKNOWN` | Logic |
| 28 | L976 | Array Kleene OR: d[0]==T | Kleene ops | `d[0] == Trit.TRUE` | Logic |
| 29 | L977 | Array Kleene OR: d[2]==T | Kleene ops | `d[2] == Trit.TRUE` | Logic |
| 30 | L981 | Int conv: 42 roundtrip | Integer conversion | `arr.to_int() == 42` | Transformation |
| 31 | L984 | Int conv: -13 roundtrip | Integer conversion | `arr.to_int() == -13` | Transformation |
| 32 | L989 | Pack: roundtrip | Packing | `restored == a` | Encoding |
| 33 | L993 | Sparsity: all-zero==1.0 | Sparsity | `sparse.sparsity() == 1.0` | Functional |
| 34 | L995 | Sparsity: all-T==0.0 | Sparsity | `dense.sparsity() == 0.0` | Functional |
| 35 | L1000 | FFT: output length | Sparsity | `len(fft_out) == 3` | Functional |
| 36 | L1008 | QEMUnoise: flips occur | QEMU noise | `flipped > 0` | Functional |
| 37 | L1011 | Div: T/T==T | Division | `Trit(1) / Trit(1) == Trit.TRUE` | Arithmetic |
| 38 | L1012 | Div: T/F==F | Division | `Trit(1) / Trit(-1) == Trit.FALSE` | Arithmetic |
| 39 | L1013 | Div: F/F==T | Division | `Trit(-1) / Trit(-1) == Trit.TRUE` | Arithmetic |
| 40 | L1014 | Div: U/T==U | Division | `Trit(0) / Trit(1) == Trit.UNKNOWN` | Arithmetic |
| 41 | L1015 | Div: T/U==U (div-by-zero) | Division | `Trit(1) / Trit(0) == Trit.UNKNOWN` | Arithmetic |
| 42 | L1018 | Exp: T^T==T | Exponentiation | `Trit(1) ** Trit(1) == Trit.TRUE` | Functional |
| 43 | L1019 | Exp: T^U==T | Exponentiation | `Trit(1) ** Trit(0) == Trit.TRUE` | Functional |
| 44 | L1020 | Exp: F^T==F | Exponentiation | `Trit(-1) ** Trit(1) == Trit.FALSE` | Functional |
| 45 | L1021 | Exp: F^U==T | Exponentiation | `Trit(-1) ** Trit(0) == Trit.TRUE` | Functional |
| 46 | L1022 | Exp: U^T==U | Exponentiation | `Trit(0) ** Trit(1) == Trit.UNKNOWN` | Functional |
| 47 | L1023 | Exp: U^U==T | Exponentiation | `Trit(0) ** Trit(0) == Trit.TRUE` | Functional |
| 48 | L1036 | Implies: T→T==T | IMPLIES | `_lib.trithon_implies(1, 1) == 1` | Functional |
| 49 | L1037 | Implies: T→F==F | IMPLIES | `_lib.trithon_implies(1, -1) == -1` | Functional |
| 50 | L1038 | Implies: F→T==T | IMPLIES | `_lib.trithon_implies(-1, 1) == 1` | Functional |
| 51 | L1039 | Equiv: T≡T==T | IMPLIES | `_lib.trithon_equiv(1, 1) == 1` | Functional |
| 52 | L1040 | Equiv: T≡F==F | IMPLIES | `_lib.trithon_equiv(1, -1) == -1` | Functional |
| 53 | L1050 | TWQ: large positive → +1 | IMPLIES | `q._data[0] == 1` | Functional |
| 54 | L1051 | TWQ: large negative → -1 | IMPLIES | `q._data[1] == -1` | Negative/error |
| 55 | L1052 | TWQ: zero → 0 | IMPLIES | `q._data[2] == 0` | Functional |
| 56 | L1056 | DLFET: TNOT(0)==2 | IMPLIES | `DLFETSim.tnot(0) == 2` | Functional |
| 57 | L1057 | DLFET: TNOT(2)==0 | IMPLIES | `DLFETSim.tnot(2) == 0` | Functional |
| 58 | L1058 | DLFET: TNAND(0,0)==2 | IMPLIES | `DLFETSim.tnand(0, 0) == 2` | Logic |
| 59 | L1059 | DLFET: TNAND(2,2)==0 | IMPLIES | `DLFETSim.tnand(2, 2) == 0` | Logic |
| 60 | L1061 | DLFET: FA(1,1,1)==(0,1) | IMPLIES | `s == 0 and c == 1` | Functional |
| 61 | L1073 | SRBC: stability in range | Radix Transcode | `stab >= 0 and stab <= 100` | Boundary |
| 62 | L1080 | Crypto: hash is deterministic | Crypto | `d1._data == d2._data` | Boundary |
| 63 | L1081 | Crypto: encrypt/decrypt roundtrip | Crypto | `TritCrypto.roundtrip_test(msg)` | Transformation |
| 64 | L1085 | PropDelay: 0→1==120ps | PropDelay | `PropDelay.nominal(0, 1) == 120` | Functional |
| 65 | L1086 | PropDelay: 2→0==55ps | PropDelay | `PropDelay.nominal(2, 0) == 55` | Functional |
| 66 | L1090 | TTL: ALWAYS(T,T,T)==T | PropDelay | `TTL.always([1, 1, 1]) == Trit.TRUE` | Functional |
| 67 | L1091 | TTL: ALWAYS(T,U,T)==U | PropDelay | `TTL.always([1, 0, 1]) == Trit.UNKNOWN` | Functional |
| 68 | L1092 | TTL: ALWAYS(T,F,T)==F | PropDelay | `TTL.always([1, -1, 1]) == Trit.FALSE` | Functional |
| 69 | L1093 | TTL: EVENTUALLY(F,F,T)==T | PropDelay | `TTL.eventually([-1, -1, 1]) == Trit.TRUE` | Functional |
| 70 | L1098 | PAM-3: roundtrip lossless | PropDelay | `PAM3.roundtrip(data)` | Transformation |
| 71 | L1100 | PAM-3: bandwidth gain positive | PropDelay | `gain > 0` | Functional |
| 72 | L1115 | MRAM: pack/unpack roundtrip | STT-MRAM | `MRAMArray.roundtrip(mram_trits)` | Encoding |
| 73 | L1116 | MRAM: write/read +1 | STT-MRAM | `MRAMArray.write_read(1) == 1` | Functional |
| 74 | L1117 | MRAM: write/read -1 | STT-MRAM | `MRAMArray.write_read(-1) == -1` | Functional |
| 75 | L1118 | MRAM: write/read 0 | STT-MRAM | `MRAMArray.write_read(0) == 0` | Functional |
| 76 | L1119 | MRAM: R_LOW==50 | STT-MRAM | `MRAMArray.nominal_resistance(0) == 50` | Functional |
| 77 | L1120 | MRAM: R_MID==120 | STT-MRAM | `MRAMArray.nominal_resistance(1) == 120` | Functional |
| 78 | L1121 | MRAM: R_HIGH==250 | STT-MRAM | `MRAMArray.nominal_resistance(2) == 250` | Functional |
| 79 | L1126 | TIPC: compress/decompress roundtrip | STT-MRAM | `TIPCChannel.roundtrip(tipc_data)` | Encoding |
| 80 | L1128 | TIPC: guardian in valid range | STT-MRAM | `-1 <= g <= 1` | Boundary |
| 81 | L1130 | TIPC: compression ratio positive | STT-MRAM | `ratio > 0` | Encoding |
| 82 | L1135 | TFS: Huffman roundtrip | STT-MRAM | `TFS.roundtrip(tfs_data)` | Encoding |
| 83 | L1137 | TFS: guardian in valid range | STT-MRAM | `-1 <= tg <= 1` | Boundary |
| 84 | L1138 | TFS: density gain >= 1.5x | STT-MRAM | `TFS.density_gain() >= 150` | Functional |
| 85 | L1139 | TFS: area reduction >= 50% | STT-MRAM | `TFS.area_reduction() >= 50` | Functional |
| 86 | L1140 | TFS: file write/read roundtrip | STT-MRAM | `TFS.file_roundtrip(tfs_data)` | Transformation |

---

## Suite 41: TJSON (Python)

**Source**: `tests/test_tjson.py`
**Runtime Assertions**: 346
**Source-Level Entries**: 76
**Harness**: `def test_*()` functions with `assert` — each function is one test case
**Output Reading**: pytest: `.` = pass, `F` = fail. Summary shows passed/failed/total.

> **Note**: 270 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L109 | test_ternary_basics | = | `test function` | Functional |
| 2 | L141 | test_ternary_from_value | = | `test function` | Hardware/ALU |
| 3 | L178 | test_kleene_and | = | `test function` | Logic |
| 4 | L194 | test_kleene_or | = | `test function` | Logic |
| 5 | L210 | test_kleene_not | = | `test function` | Logic |
| 6 | L220 | test_kleene_implies | = | `test function` | Logic |
| 7 | L236 | test_kleene_equiv | = | `test function` | Logic |
| 8 | L246 | test_kleene_properties | = | `test function` | Logic |
| 9 | L277 | test_lukasiewicz | = | `test function` | Functional |
| 10 | L305 | test_encoder_ternary | = | `test function` | Encoding |
| 11 | L312 | test_encoder_dict | = | `test function` | Encoding |
| 12 | L322 | test_decoder_ternary | = | `test function` | Encoding |
| 13 | L332 | test_roundtrip_simple | = | `test function` | Transformation |
| 14 | L344 | test_roundtrip_nested | = | `test function` | Transformation |
| 15 | L360 | test_dump_load_file | = | `test function` | Functional |
| 16 | L375 | test_epistemic_create | = | `test function` | Functional |
| 17 | L385 | test_epistemic_unknown | = | `test function` | Functional |
| 18 | L393 | test_epistemic_roundtrip | = | `test function` | Transformation |
| 19 | L406 | test_epistemic_merge | = | `test function` | Functional |
| 20 | L419 | test_epistemic_merge_both_true | = | `test function` | Functional |
| 21 | L428 | test_epistemic_equality | = | `test function` | Functional |
| 22 | L437 | test_epistemic_confidence_clamp | = | `test function` | Boundary |
| 23 | L445 | test_epistemic_to_dict | = | `test function` | Functional |
| 24 | L464 | test_tarray_create | = | `test function` | Functional |
| 25 | L475 | test_tarray_kleene_and | = | `test function` | Logic |
| 26 | L486 | test_tarray_kleene_or | = | `test function` | Logic |
| 27 | L496 | test_tarray_kleene_not | = | `test function` | Logic |
| 28 | L505 | test_tarray_census | = | `test function` | Functional |
| 29 | L514 | test_tarray_agreement | = | `test function` | Functional |
| 30 | L527 | test_tarray_consensus | = | `test function` | Consensus |
| 31 | L539 | test_tarray_json | = | `test function` | Functional |
| 32 | L548 | test_tarray_setitem | = | `test function` | Functional |
| 33 | L557 | test_tarray_equality | = | `test function` | Functional |
| 34 | L566 | test_tarray_length_mismatch | = | `test function` | Functional |
| 35 | L581 | test_diff_identical | = | `test function` | Functional |
| 36 | L588 | test_diff_value_change | = | `test function` | Hardware/ALU |
| 37 | L598 | test_diff_add_remove | = | `test function` | Arithmetic |
| 38 | L609 | test_diff_unk_propagation | = | `test function` | Functional |
| 39 | L618 | test_diff_nested | = | `test function` | Functional |
| 40 | L627 | test_diff_array | = | `test function` | Functional |
| 41 | L636 | test_diff_compare_values | = | `test function` | Hardware/ALU |
| 42 | L653 | test_merge_conservative | = | `test function` | Functional |
| 43 | L662 | test_merge_optimistic | = | `test function` | Functional |
| 44 | L671 | test_merge_overlay | = | `test function` | Functional |
| 45 | L681 | test_merge_nested | = | `test function` | Functional |
| 46 | L691 | test_merge_epistemic | = | `test function` | Functional |
| 47 | L702 | test_merge_no_mutate | = | `test function` | Functional |
| 48 | L715 | test_schema_ternary_type | = | `test function` | Type system |
| 49 | L725 | test_schema_basic_types | = | `test function` | Type system |
| 50 | L739 | test_schema_numeric_constraints | = | `test function` | Functional |
| 51 | L747 | test_schema_string_constraints | = | `test function` | Functional |
| 52 | L755 | test_schema_required | = | `test function` | Functional |
| 53 | L767 | test_schema_additional_properties | = | `test function` | Arithmetic |
| 54 | L778 | test_schema_epistemic | = | `test function` | Functional |
| 55 | L794 | test_schema_array_items | = | `test function` | Functional |
| 56 | L808 | test_schema_enum | = | `test function` | Functional |
| 57 | L815 | test_schema_allOf | = | `test function` | Functional |
| 58 | L828 | test_schema_anyOf | = | `test function` | Functional |
| 59 | L841 | test_schema_not | = | `test function` | Functional |
| 60 | L848 | test_schema_union_type | = | `test function` | Type system |
| 61 | L856 | test_schema_unk_uncertainty | = | `test function` | Functional |
| 62 | L863 | test_schema_sensor_reading | = | `test function` | Functional |
| 63 | L882 | test_validation_result_merge | = | `test function` | Functional |
| 64 | L891 | test_validation_result_properties | = | `test function` | Functional |
| 65 | L902 | test_trithon_interop | = | `test function` | Functional |
| 66 | L931 | test_empty_document | = | `test function` | Negative/error |
| 67 | L939 | test_deeply_nested | = | `test function` | Functional |
| 68 | L947 | test_large_ternary_array | = | `test function` | Functional |
| 69 | L959 | test_ternary_array_de_morgan | = | `test function` | Functional |
| 70 | L969 | test_merge_idempotent | = | `test function` | Functional |
| 71 | L978 | test_diff_epistemic | = | `test function` | Functional |
| 72 | L987 | test_schema_nested_object | = | `test function` | Functional |
| 73 | L1009 | test_ternary_iter | = | `test function` | Functional |
| 74 | L1016 | test_schema_oneOf | = | `test function` | Functional |
| 75 | L1029 | test_exclusive_constraints | = | `test function` | Functional |
| 76 | L1037 | test_additional_properties_schema | = | `test function` | Arithmetic |

---

## Suite 42: TerNumPy (Python)

**Source**: `tests/test_ternumpy.py`
**Runtime Assertions**: 240
**Source-Level Entries**: 174
**Harness**: `assert_eq(actual, expected, label)` / `assert_true(cond, label)` — counted assertions
**Output Reading**: Summary: `TerNumPy tests: N passed, M failed`. Exit 1 if failures.

> **Note**: 66 additional runtime assertions are generated by loop expansion or multi-line macro calls.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L88 | array shape | 1. Array Creation | `a.shape == (3,)` | Functional |
| 2 | L89 | array size | 1. Array Creation | `a.size == 3` | Functional |
| 3 | L90 | array ndim | 1. Array Creation | `a.ndim == 1` | Functional |
| 4 | L91 | dtype | 1. Array Creation | `a.dtype == 'trit'` | Type system |
| 5 | L92 | flat list | 1. Array Creation | `a.flat == [1, -1, 0]` | Functional |
| 6 | L95 | zeros(4) | 1. Array Creation | `z.flat == [0, 0, 0, 0]` | Functional |
| 7 | L96 | zeros shape | 1. Array Creation | `z.shape == (4,)` | Functional |
| 8 | L99 | ones(3) | 1. Array Creation | `o.flat == [1, 1, 1]` | Functional |
| 9 | L102 | falses(2) | 1. Array Creation | `f.flat == [-1, -1]` | Functional |
| 10 | L105 | unknowns == zeros | 1. Array Creation | `u.flat == [0, 0, 0]` | Functional |
| 11 | L108 | full shape | 1. Array Creation | `fl.shape == (2, 2)` | Functional |
| 12 | L109 | full size | 1. Array Creation | `fl.size == 4` | Functional |
| 13 | L110 | full data | 1. Array Creation | `fl.flat == [1, 1, 1, 1]` | Functional |
| 14 | L113 | eye shape | 1. Array Creation | `e.shape == (3, 3)` | Functional |
| 15 | L114 | eye diag 0 | 1. Array Creation | `e[0 == 0], 1` | Functional |
| 16 | L115 | eye diag 1 | 1. Array Creation | `e[1 == 1], 1` | Functional |
| 17 | L116 | eye diag 2 | 1. Array Creation | `e[2 == 2], 1` | Functional |
| 18 | L117 | eye off-diag | 1. Array Creation | `e[0 == 1], 0` | Functional |
| 19 | L118 | eye off-diag 2 | 1. Array Creation | `e[1 == 0], 0` | Functional |
| 20 | L121 | arange(3) balanced | 1. Array Creation | `ar.flat == [0, 1, -1]` | Boundary |
| 21 | L124 | zeros 2D shape | 1. Array Creation | `z2d.shape == (2, 3)` | Functional |
| 22 | L125 | zeros 2D size | 1. Array Creation | `z2d.size == 6` | Functional |
| 23 | L126 | zeros 2D ndim | 1. Array Creation | `z2d.ndim == 2` | Functional |
| 24 | L130 | nested list shape | 1. Array Creation | `m.shape == (2, 2)` | Functional |
| 25 | L131 | nested [0,0] | 1. Array Creation | `m[0 == 0], 1` | Functional |
| 26 | L132 | nested [1,1] | 1. Array Creation | `m[1 == 1], 1` | Functional |
| 27 | L133 | nested [0,1] | 1. Array Creation | `m[0 == 1], -1` | Functional |
| 28 | L134 | nested [1,0] | 1. Array Creation | `m[1 == 0], 0` | Functional |
| 29 | L142 | roundtrip +13 | 2. Int Conversion (Avizienis) | `to_int(t13) == 13` | Transformation |
| 30 | L145 | roundtrip -7 | 2. Int Conversion (Avizienis) | `to_int(tn7) == -7` | Transformation |
| 31 | L148 | roundtrip 0 | 2. Int Conversion (Avizienis) | `to_int(t0) == 0` | Transformation |
| 32 | L151 | roundtrip 1 | 2. Int Conversion (Avizienis) | `to_int(t1) == 1` | Transformation |
| 33 | L154 | roundtrip -1 | 2. Int Conversion (Avizienis) | `to_int(tn1) == -1` | Transformation |
| 34 | L157 | roundtrip 100 | 2. Int Conversion (Avizienis) | `to_int(t100) == 100` | Transformation |
| 35 | L160 | roundtrip -100 | 2. Int Conversion (Avizienis) | `to_int(tn100) == -100` | Transformation |
| 36 | L168 | idx 0 | 3. Indexing & Slicing | `a[0] == 1` | Functional |
| 37 | L169 | idx 2 | 3. Indexing & Slicing | `a[2] == -1` | Functional |
| 38 | L170 | idx -1 | 3. Indexing & Slicing | `a[-1] == -1` | Functional |
| 39 | L173 | slice 1:4 | 3. Indexing & Slicing | `s.flat == [0, -1, 1]` | Functional |
| 40 | L174 | slice shape | 3. Indexing & Slicing | `s.shape == (3,)` | Functional |
| 41 | L179 | 2D row 0 | 3. Indexing & Slicing | `row0.flat == [1, -1, 0]` | Functional |
| 42 | L181 | 2D row 1 | 3. Indexing & Slicing | `row1.flat == [0, 1, -1]` | Functional |
| 43 | L182 | 2D scalar idx | 3. Indexing & Slicing | `m[0 == 2], 0` | Functional |
| 44 | L183 | 2D scalar idx 2 | 3. Indexing & Slicing | `m[1 == 0], 0` | Functional |
| 45 | L188 | setitem 1D | 3. Indexing & Slicing | `b.flat == [0, 1, 0]` | Functional |
| 46 | L193 | setitem 2D [0,0] | 3. Indexing & Slicing | `m2[0 == 0], 1` | Functional |
| 47 | L194 | setitem 2D [1,1] | 3. Indexing & Slicing | `m2[1 == 1], -1` | Functional |
| 48 | L195 | setitem 2D unchanged | 3. Indexing & Slicing | `m2[0 == 1], 0` | Functional |
| 49 | L207 | neg | 4. Element-wise Arithmetic | `na.flat == [-1, 1, 0, -1]` | Functional |
| 50 | L211 | abs | 4. Element-wise Arithmetic | `ab.flat == [1, 1, 0, 1]` | Functional |
| 51 | L215 | add clamped | 4. Element-wise Arithmetic | `c.flat == [1, 0, 1, 0]` | Boundary |
| 52 | L218 | T+T=T (clamped) | 4. Element-wise Arithmetic | `(array([1]) + array([1])).flat == [1]` | Boundary |
| 53 | L220 | F+F=F (clamped) | 4. Element-wise Arithmetic | `(array([-1]) + array([-1])).flat == [-1]` | Boundary |
| 54 | L224 | sub | 4. Element-wise Arithmetic | `d.flat == [0, -1, -1, 1]` | Arithmetic |
| 55 | L228 | mul | 4. Element-wise Arithmetic | `e.flat == [1, -1, 0, -1]` | Arithmetic |
| 56 | L230 | F*F=T | 4. Element-wise Arithmetic | `(array([-1]) * array([-1])).flat == [1]` | Functional |
| 57 | L232 | U*T=U | 4. Element-wise Arithmetic | `(array([0]) * array([1])).flat == [0]` | Functional |
| 58 | L236 | floordiv | 4. Element-wise Arithmetic | `fd.flat == [1, -1, 0, -1]` | Arithmetic |
| 59 | L238 | T//U=U | 4. Element-wise Arithmetic | `(array([1]) // array([0])).flat == [0]` | Functional |
| 60 | L242 | balanced_add | 4. Element-wise Arithmetic | `ba.flat == [-1, 0, 1, 0]` | Arithmetic |
| 61 | L252 | carry digits | 4. Element-wise Arithmetic | `digs.flat == [-1, 1]` | Functional |
| 62 | L253 | carry values | 4. Element-wise Arithmetic | `crs.flat == [1, -1]` | Hardware/ALU |
| 63 | L265 | T&T=T | 5. Kleene K₃ Logic | `(T & T).flat == [1]` | Functional |
| 64 | L266 | T&U=U | 5. Kleene K₃ Logic | `(T & U).flat == [0]` | Functional |
| 65 | L267 | T&F=F | 5. Kleene K₃ Logic | `(T & F).flat == [-1]` | Functional |
| 66 | L268 | U&U=U | 5. Kleene K₃ Logic | `(U & U).flat == [0]` | Functional |
| 67 | L269 | U&F=F | 5. Kleene K₃ Logic | `(U & F).flat == [-1]` | Functional |
| 68 | L270 | F&F=F | 5. Kleene K₃ Logic | `(F & F).flat == [-1]` | Functional |
| 69 | L273 | T∣T=T | 5. Kleene K₃ Logic | `(T ∣ T).flat == [1]` | Functional |
| 70 | L274 | T∣U=T | 5. Kleene K₃ Logic | `(T ∣ U).flat == [1]` | Functional |
| 71 | L275 | T∣F=T | 5. Kleene K₃ Logic | `(T ∣ F).flat == [1]` | Functional |
| 72 | L276 | U∣U=U | 5. Kleene K₃ Logic | `(U ∣ U).flat == [0]` | Functional |
| 73 | L277 | U∣F=U | 5. Kleene K₃ Logic | `(U ∣ F).flat == [0]` | Functional |
| 74 | L278 | F∣F=F | 5. Kleene K₃ Logic | `(F ∣ F).flat == [-1]` | Functional |
| 75 | L281 | ~T=F | 5. Kleene K₃ Logic | `(~T).flat == [-1]` | Functional |
| 76 | L282 | ~U=U | 5. Kleene K₃ Logic | `(~U).flat == [0]` | Functional |
| 77 | L283 | ~F=T | 5. Kleene K₃ Logic | `(~F).flat == [1]` | Functional |
| 78 | L286 | T^F=T | 5. Kleene K₃ Logic | `(T ^ F).flat == [1]` | Functional |
| 79 | L287 | T^T=F | 5. Kleene K₃ Logic | `(T ^ T).flat == [-1]` | Functional |
| 80 | L288 | F^F=F | 5. Kleene K₃ Logic | `(F ^ F).flat == [-1]` | Functional |
| 81 | L289 | T^U=U | 5. Kleene K₃ Logic | `(T ^ U).flat == [0]` | Functional |
| 82 | L292 | T→T=T | 5. Kleene K₃ Logic | `T.implies(T).flat == [1]` | Functional |
| 83 | L293 | T→F=F | 5. Kleene K₃ Logic | `T.implies(F).flat == [-1]` | Functional |
| 84 | L294 | T→U=U | 5. Kleene K₃ Logic | `T.implies(U).flat == [0]` | Functional |
| 85 | L295 | F→T=T | 5. Kleene K₃ Logic | `F.implies(T).flat == [1]` | Functional |
| 86 | L296 | F→F=T | 5. Kleene K₃ Logic | `F.implies(F).flat == [1]` | Functional |
| 87 | L297 | F→U=T | 5. Kleene K₃ Logic | `F.implies(U).flat == [1]` | Functional |
| 88 | L298 | U→T=T | 5. Kleene K₃ Logic | `U.implies(T).flat == [1]` | Functional |
| 89 | L299 | U→U=U | 5. Kleene K₃ Logic | `U.implies(U).flat == [0]` | Functional |
| 90 | L300 | U→F=U | 5. Kleene K₃ Logic | `U.implies(F).flat == [0]` | Functional |
| 91 | L303 | T↔T=T | 5. Kleene K₃ Logic | `T.equiv(T).flat == [1]` | Functional |
| 92 | L304 | T↔F=F | 5. Kleene K₃ Logic | `T.equiv(F).flat == [-1]` | Functional |
| 93 | L305 | U↔U=U | 5. Kleene K₃ Logic | `U.equiv(U).flat == [0]` | Functional |
| 94 | L310 | vector AND | 5. Kleene K₃ Logic | `(v1 & v2).flat == [1, 0, -1, -1]` | Logic |
| 95 | L311 | vector OR | 5. Kleene K₃ Logic | `(v1 ∣ v2).flat == [1, 1, 0, 1]` | Logic |
| 96 | L323 | eq_trit | 6. Ternary Comparison | `eq.flat == [1, 0, 1, -1]` | Functional |
| 97 | L326 | ne_trit | 6. Ternary Comparison | `ne.flat == [-1, 0, -1, 1]` | Functional |
| 98 | L329 | U==U → U (epistemic) | 6. Ternary Comparison | `array([0]).eq_trit(array([0])).flat == [0]` | Functional |
| 99 | L337 | trit_sum | 7. Reductions | `a.trit_sum() == 2` | Arithmetic |
| 100 | L338 | trit_min | 7. Reductions | `a.trit_min() == -1` | Boundary |
| 101 | L339 | trit_max | 7. Reductions | `a.trit_max() == 1` | Boundary |
| 102 | L341 | consensus (AND-fold) | 7. Reductions | `a.consensus() == -1` | Consensus |
| 103 | L342 | dissent (OR-fold) | 7. Reductions | `a.dissent() == 1` | Functional |
| 104 | L344 | any_true | 7. Reductions | `a.any_true()` | Functional |
| 105 | L345 | not all_true | 7. Reductions | `not a.all_true()` | Logic |
| 106 | L346 | all_true: all T | 7. Reductions | `ones(5).all_true()` | Functional |
| 107 | L348 | count_true | 7. Reductions | `a.count_true() == 3` | Functional |
| 108 | L349 | count_false | 7. Reductions | `a.count_false() == 1` | Functional |
| 109 | L350 | count_unknown | 7. Reductions | `a.count_unknown() == 1` | Functional |
| 110 | L353 | census T | 7. Reductions | `c['T'] == 3` | Functional |
| 111 | L354 | census U | 7. Reductions | `c['U'] == 1` | Functional |
| 112 | L355 | census F | 7. Reductions | `c['F'] == 1` | Functional |
| 113 | L357 | sparsity ~0.2 | 7. Reductions | `0.15 < a.sparsity() < 0.25` | Functional |
| 114 | L358 | sparsity all-U = 1.0 | 7. Reductions | `zeros(4).sparsity() == 1.0` | Functional |
| 115 | L362 | consensus all-T = T | 7. Reductions | `all_t.consensus() == 1` | Consensus |
| 116 | L364 | dissent all-F = F | 7. Reductions | `all_f.dissent() == -1` | Functional |
| 117 | L373 | reshape 2x3 | 8. Shape Manipulation | `m.shape == (2, 3)` | Functional |
| 118 | L374 | reshaped ndim | 8. Shape Manipulation | `m.ndim == 2` | Functional |
| 119 | L375 | reshaped [0,0] | 8. Shape Manipulation | `m[0 == 0], 1` | Functional |
| 120 | L376 | reshaped [1,2] | 8. Shape Manipulation | `m[1 == 2], 0` | Functional |
| 121 | L379 | flatten shape | 8. Shape Manipulation | `flat.shape == (6,)` | Functional |
| 122 | L380 | flatten data | 8. Shape Manipulation | `flat.flat == [1, -1, 0, 1, -1, 0]` | Functional |
| 123 | L384 | transpose shape | 8. Shape Manipulation | `t.shape == (3, 2)` | Functional |
| 124 | L385 | transpose [0,0] | 8. Shape Manipulation | `t[0 == 0], 1` | Functional |
| 125 | L386 | transpose [0,1] | 8. Shape Manipulation | `t[0 == 1], 1` | Functional |
| 126 | L387 | transpose [2,0] | 8. Shape Manipulation | `t[2 == 0], 0` | Functional |
| 127 | L388 | transpose [2,1] | 8. Shape Manipulation | `t[2 == 1], 0` | Functional |
| 128 | L393 | squeeze shape | 8. Shape Manipulation | `sq.shape == (3,)` | Functional |
| 129 | L394 | squeeze data | 8. Shape Manipulation | `sq.flat == [1, -1, 0]` | Functional |
| 130 | L398 | copy data | 8. Shape Manipulation | `cp.flat == a.flat` | Functional |
| 131 | L400 | copy is independent | 8. Shape Manipulation | `a[0] == 1` | Functional |
| 132 | L411 | 1D & scalar | 9. Broadcasting | `r.flat == [1, 0, -1]` | Functional |
| 133 | L414 | 1D ∣ scalar | 9. Broadcasting | `r2.flat == [1, 1, 1]` | Functional |
| 134 | L417 | broadcast shape result | 9. Broadcasting | `r.shape == (3,)` | Transformation |
| 135 | L423 | 2D broadcast shape | 9. Broadcasting | `result.shape == (2, 3)` | Transformation |
| 136 | L424 | 2D broadcast [0,0] | 9. Broadcasting | `result[0 == 0], 1` | Transformation |
| 137 | L425 | 2D broadcast [0,2] | 9. Broadcasting | `result[0 == 2], -1` | Transformation |
| 138 | L426 | 2D broadcast [1,0] | 9. Broadcasting | `result[1 == 0], -1` | Transformation |
| 139 | L427 | 2D broadcast [1,1] | 9. Broadcasting | `result[1 == 1], 1` | Transformation |
| 140 | L441 | dot product | 10. Dot Product | `dot(a == b), -1` | Arithmetic |
| 141 | L443 | dot all-T | 10. Dot Product | `dot(ones(4) == ones(4)), 4` | Functional |
| 142 | L444 | dot T·F | 10. Dot Product | `dot(ones(4) == falses(4)), -4` | Functional |
| 143 | L445 | dot U·T = 0 | 10. Dot Product | `dot(zeros(4) == ones(4)), 0` | Functional |
| 144 | L460 | where T→x, F→y, U→U | 11. Where (Ternary Select) | `result.flat == [1, -1, 0]` | Functional |
| 145 | L463 | where all-T = x | 11. Where (Ternary Select) | `where(ones(3) == x, y).flat, [1, 1, 1]` | Functional |
| 146 | L465 | where all-F = y | 11. Where (Ternary Select) | `where(falses(3) == x, y).flat, [-1, -1, -1]` | Functional |
| 147 | L467 | where all-U = U | 11. Where (Ternary Select) | `where(zeros(3) == x, y).flat, [0, 0, 0]` | Functional |
| 148 | L477 | stack shape | 12. Stack & Concatenate | `s.shape == (2, 2)` | Memory |
| 149 | L478 | stack row 0 | 12. Stack & Concatenate | `s[0].flat == [1, 0]` | Memory |
| 150 | L479 | stack row 1 | 12. Stack & Concatenate | `s[1].flat == [-1, 1]` | Memory |
| 151 | L482 | concat shape | 12. Stack & Concatenate | `c.shape == (4,)` | Functional |
| 152 | L483 | concat data | 12. Stack & Concatenate | `c.flat == [1, 0, -1, 1]` | Functional |
| 153 | L486 | concat 3 arrays | 12. Stack & Concatenate | `c3.flat == [1, 0, -1, 1, 0]` | Functional |
| 154 | L495 | clip default no-op | 13. Clip | `clip(a).flat == [1, 0, -1, 1, -1]` | Functional |
| 155 | L499 | clip lo=0 | 13. Clip | `c.flat == [1, 0, 0, 1, 0]` | Functional |
| 156 | L503 | clip hi=0 | 13. Clip | `c2.flat == [0, 0, -1, 0, -1]` | Functional |
| 157 | L511 | to_list 2D | 14. to_list & Conversion | `a.to_list() == [[1, -1], [0, 1]]` | Functional |
| 158 | L514 | to_list 1D | 14. to_list & Conversion | `b.to_list() == [1, 0, -1]` | Functional |
| 159 | L521 | to_trithon type | 14. to_list & Conversion | `isinstance(ta, TA)` | Type system |
| 160 | L523 | from_trithon roundtrip | 14. to_list & Conversion | `rt.flat == [1, -1, 0]` | Transformation |
| 161 | L631 | eye row0 · row0 = 1 | 18. Eye & Dot Matrix Patterns | `dot(row0 == row0), 1` | Functional |
| 162 | L632 | eye row0 · row1 = 0 | 18. Eye & Dot Matrix Patterns | `dot(row0 == row1), 0` | Functional |
| 163 | L651 | repr contains TritNDArray | 19. Repr & Len | `'TritNDArray' in r` | Functional |
| 164 | L652 | repr contains symbols | 19. Repr & Len | `'TFU' in r` | Linking |
| 165 | L653 | len 1D | 19. Repr & Len | `len(a) == 3` | Functional |
| 166 | L656 | len 2D = first dim | 19. Repr & Len | `len(m) == 2` | Functional |
| 167 | L664 | 1000 elem size | 20. Large Array Smoke Test | `big.size == 1000` | Functional |
| 168 | L665 | sum 1000 ones | 20. Large Array Smoke Test | `big.trit_sum() == 1000` | Arithmetic |
| 169 | L666 | dot 1000 ones | 20. Large Array Smoke Test | `dot(big == big), 1000` | Functional |
| 170 | L667 | 1000 all true | 20. Large Array Smoke Test | `big.all_true()` | Functional |
| 171 | L670 | mixed 1000 size | 20. Large Array Smoke Test | `mixed.size == 1000` | Functional |
| 172 | L671 | mixed count_true | 20. Large Array Smoke Test | `mixed.count_true() == 334` | Functional |
| 173 | L672 | mixed count_unknown | 20. Large Array Smoke Test | `mixed.count_unknown() == 333` | Functional |
| 174 | L673 | mixed count_false | 20. Large Array Smoke Test | `mixed.count_false() == 333` | Functional |

---

---

## Suite 20: Ternary Database & Storage ⭐NEW

**Source**: `tests/test_ternary_database.c`
**Runtime Assertions**: 32
**Source-Level Entries**: 32
**Harness**: `ASSERT_EQ/ASSERT_TRUE(cond, msg)` + `PASS()` per function — same structure as suites 16-19
**Output Reading**: `test_name  [PASS]` per test; final `=== Results: N passed, 0 failed ===`
**What it tests**: Three-valued SQL-style NULL logic (STRICT/PROPAGATE/LENIENT modes), ternary CAM (content-addressable memory), run-length and Huffman compression, and a ternary relational DB layer.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L38 | null_and_strict_mode | 1. Null AND Semantics | `ternary_null_and(F,T,STRICT)==F; ternary_null_and(NULL,T,STRICT)==NULL` | Logic |
| 2 | L64 | null_or_strict_mode | 1. Null OR Semantics | `ternary_null_or(F,F,STRICT)==F; ternary_null_or(NULL,F,STRICT)==NULL` | Logic |
| 3 | L49 | null_and_propagate_mode | 1. Null AND Semantics | `ternary_null_and(NULL,T,PROPAGATE)==NULL` | Logic |
| 4 | L74 | null_or_propagate_mode | 1. Null OR Semantics | `ternary_null_or(NULL,F,PROPAGATE)==NULL` | Logic |
| 5 | L57 | null_and_lenient_mode | 1. Null AND Semantics | `ternary_null_and(T,T,LENIENT)==T` | Logic |
| 6 | L81 | null_or_lenient_mode | 1. Null OR Semantics | `ternary_null_or(T,F,LENIENT)==T` | Logic |
| 7 | L88 | null_equals_all_combos | 2. Null Equality | `ternary_null_equals(T,T)==T; ternary_null_equals(NULL,T)==NULL` | Logic |
| 8 | L99 | null_count_aggregation | 2. Aggregation | `count(3 non-null)==T; count(0 non-null)==U` | Functional |
| 9 | L113 | null_sum_aggregation | 2. Aggregation | `sum(+1,-1,skip,+1)==T; sum(+1,-1)==U` | Arithmetic |
| 10 | L127 | null_and_commutativity | 3. Algebraic Laws | `AND(a,b)==AND(b,a) for all 9 pairs` | Logic |
| 11 | L140 | null_or_commutativity | 3. Algebraic Laws | `OR(a,b)==OR(b,a) for all 9 pairs` | Logic |
| 12 | L157 | cam_init | 4. CAM Operations | `cam.num_entries==0 after init` | Initialization |
| 13 | L165 | cam_add_and_search | 4. CAM Operations | `cam_add(key1,data1,mask1)==0; search hits==1` | Functional |
| 14 | L192 | cam_delete_and_verify | 4. CAM Operations | `cam_delete(key1)==0; search hits==0` | Functional |
| 15 | L211 | cam_delete_nonexistent | 4. CAM Operations | `cam_delete(missing)==-1` | Negative/error |
| 16 | L221 | cam_multiple_matches | 4. CAM Operations | `search with don't-care mask hits>=3` | Functional |
| 17 | L245 | cam_search_empty_table | 4. CAM Operations | `search on empty table==0 hits` | Boundary |
| 18 | L257 | cam_null_mask_defaults_to_all_care | 4. CAM Operations | `NULL mask → exact match only` | Functional |
| 19 | L283 | rle_basic_compress_decompress | 5. RLE Compression | `compress then decompress recovers original` | Encoding |
| 20 | L308 | rle_single_element | 5. RLE Compression | `single-elem RLE roundtrip` | Boundary |
| 21 | L325 | rle_alternating_pattern | 5. RLE Compression | `alternating T/F/U RLE roundtrip` | Encoding |
| 22 | L343 | rle_uniform_data | 5. RLE Compression | `all-T run encodes compactly` | Encoding |
| 23 | L361 | huffman_basic_compress | 6. Huffman Compression | `Huffman compress non-empty result` | Encoding |
| 24 | L382 | huffman_all_same_value | 6. Huffman Compression | `all-T input compresses` | Boundary |
| 25 | L398 | huffman_three_distinct_values | 6. Huffman Compression | `T/F/U freq distribution compresses` | Encoding |
| 26 | L418 | db_init | 7. Ternary DB | `db initialises with 0 rows` | Initialization |
| 27 | L428 | db_insert_and_select | 7. Ternary DB | `insert(row) then select finds it` | Functional |
| 28 | L453 | db_insert_no_null_indicators | 7. Ternary DB | `row with no NULLs selects correctly` | Functional |
| 29 | L467 | db_empty_select | 7. Ternary DB | `select from empty table returns 0` | Boundary |
| 30 | L478 | db_multiple_rows_select | 7. Ternary DB | `3 rows inserted; select finds all` | Functional |
| 31 | L501 | db_null_mode_propagate | 7. Ternary DB | `NULL propagation mode affects WHERE result` | Functional |
| 32 | L517 | db_select_false_value | 7. Ternary DB | `row with FALSE trit value selects correctly` | Functional |

---

## Suite 21: Ingole WO2016199157A1 TALU ⭐NEW

**Source**: `tests/test_ingole_wo2016199157a1.c`
**Runtime Assertions**: 32
**Source-Level Entries**: 32
**Harness**: `ASSERT_EQ(actual, expected, msg)` + `PASS()` — same pattern as patent HAL suites
**Output Reading**: `test_name  [PASS]`; final `=== Results: 32 passed, 0 failed ===`
**What it tests**: Full coverage of the Ingole WO2016199157A1 Ternary ALU patent — unbalanced/balanced encoding conversions, all unary/binary ternary opcodes (TNOT, CWC, CCWC, TAND, TNAND, TOR, TNOR, XTOR, comparator), half-adder, full-adder, multi-trit arithmetic, status flags, and HAL lifecycle.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L59 | ig_from_balanced_all_values | 1. Encoding | `ig_from_balanced(-1)==0; (0)==1; (+1)==2` | Encoding |
| 2 | L68 | ig_to_balanced_all_values | 1. Encoding | `ig_to_balanced(0)==-1; (1)==0; (2)==+1` | Encoding |
| 3 | L77 | roundtrip_balanced_unbalanced | 1. Encoding | `ig_to_balanced(ig_from_balanced(v))==v for all 3` | Transformation |
| 4 | L92 | tnot_truth_table | 2. Unary Ops | `TNOT(-1)=+1; TNOT(0)=0; TNOT(+1)=-1` | Logic |
| 5 | L102 | cwc_truth_table | 2. Unary Ops | `CWC(-1)=-1; CWC(0)=+1; CWC(+1)=0` | Logic |
| 6 | L112 | ccwc_truth_table | 2. Unary Ops | `CCWC(-1)=0; CCWC(0)=-1; CCWC(+1)=+1` | Logic |
| 7 | L122 | add1carry_truth_table | 2. Arithmetic | `A1C(-1).sum=0,carry=-1; A1C(0).sum=+1,carry=-1; A1C(+1).sum=-1,carry=0` | Arithmetic |
| 8 | L150 | tand_full_truth_table | 3. Binary Ops | `TAND(a,b)==min(a,b) for all 9 pairs` | Logic |
| 9 | L164 | tnand_full_truth_table | 3. Binary Ops | `TNAND(a,b)==NOT(AND(a,b)) for all 9 pairs` | Logic |
| 10 | L177 | tor_full_truth_table | 3. Binary Ops | `TOR(a,b)==max(a,b) for all 9 pairs` | Logic |
| 11 | L190 | tnor_full_truth_table | 3. Binary Ops | `TNOR(a,b)==NOT(OR(a,b)) for all 9 pairs` | Logic |
| 12 | L203 | xtor_full_truth_table | 3. Binary Ops | `XTOR(a,b) verified for all 9 pairs (mod-3 sum)` | Logic |
| 13 | L229 | comparator_full_truth_table | 3. Binary Ops | `comparator(a,b) returns {-1,0,+1} sign` | Logic |
| 14 | L249 | half_adder_all_9_pairs | 4. Adders | `half_adder(a,b).sum and .carry for all 9 input pairs` | Arithmetic |
| 15 | L288 | full_adder_all_27_triples | 4. Adders | `full_adder(a,b,cin) for all 27 input triples` | Arithmetic |
| 16 | L326 | talu_add_2trit | 5. TALU Opcodes | `TALU ADD: 2-trit addition result and carry` | Hardware/ALU |
| 17 | L348 | talu_add_zero_word | 5. TALU Opcodes | `TALU ADD zero word returns zero` | Hardware/ALU |
| 18 | L681 | talu_add_4trit_chain | 5. TALU Opcodes | `TALU ADD 4-trit chain with carry propagation` | Arithmetic |
| 19 | L390 | talu_sub_ab_identity | 5. TALU Opcodes | `TALU SUB a-a==0 identity` | Arithmetic |
| 20 | L415 | talu_sub_ba_simple | 5. TALU Opcodes | `TALU SUB b-a with known result` | Arithmetic |
| 21 | L452 | talu_opcode_tand_tnand | 5. TALU Opcodes | `TALU TAND and TNAND opcodes produce correct output` | Hardware/ALU |
| 22 | L467 | talu_opcode_tor_tnor | 5. TALU Opcodes | `TALU TOR and TNOR opcodes produce correct output` | Hardware/ALU |
| 23 | L482 | talu_opcode_xtor_comparator | 5. TALU Opcodes | `TALU XTOR and COMPARATOR opcodes` | Hardware/ALU |
| 24 | L498 | talu_opcode_nop | 5. TALU Opcodes | `TALU NOP leaves result unchanged` | Hardware/ALU |
| 25 | L519 | talu_all_inclusive_tor_tnor | 5. TALU Opcodes | `TALU AI-TOR (all-inclusive OR/NOR)` | Hardware/ALU |
| 26 | L540 | parity_flag_computation | 6. Status Flags | `parity flag correct for mixed/uniform trit word` | Hardware/ALU |
| 27 | L562 | all_zero_flag | 6. Status Flags | `all-zero flag set iff every trit is 0` | Hardware/ALU |
| 28 | L579 | overflow_flag | 6. Status Flags | `overflow flag set on carry-out` | Hardware/ALU |
| 29 | L647 | cwc_ccwc_are_involutions | 7. Involution Laws | `CWC(CWC(v))==v and CCWC(CCWC(v))==v for all v` | Logic |
| 30 | L666 | tnot_involution | 7. Involution Laws | `TNOT(TNOT(v))==v for all v` | Logic |
| 31 | L604 | hal_init_caps_shutdown | 8. HAL Lifecycle | `hal_init(), capability setup, hal_shutdown()` | Initialization |
| 32 | L707 | patent_id_and_constants | 8. HAL Lifecycle | `patent ID string and constant values match spec` | Functional |

---

## Suite 22: AI Acceleration Framework ⭐NEW

**Source**: `tests/test_ai_acceleration.c`
**Runtime Assertions**: 24
**Source-Level Entries**: 24
**Harness**: `ASSERT_EQ/ASSERT_TRUE(cond, msg)` + `PASS()` per function
**Output Reading**: `test_name  [PASS]`; final `=== Results: 24 passed, 0 failed ===`
**What it tests**: BitNet-style ternary weight quantisation, DLFET (dual-level FET) logic gates and full-adder, sparse ternary matrix operations, ternary linear layers, and activation functions.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L90 | bitnet_quantize_basic | 1. BitNet Quantisation | `0.9→+1, -0.8→-1, scale>0` | Functional |
| 2 | L109 | bitnet_quantize_all_zero | 1. BitNet Quantisation | `all zero weights → all UNKNOWN` | Boundary |
| 3 | L124 | bitnet_quantize_uniform_positive | 1. BitNet Quantisation | `uniform positive → all TRUE` | Functional |
| 4 | L139 | bitnet_quantize_scale_factor | 1. BitNet Quantisation | `large-magnitude inputs produce correct scale>0` | Functional |
| 5 | L422 | bitnet_quantize_single_weight | 1. BitNet Quantisation | `single positive weight quantises to +1` | Boundary |
| 6 | L159 | bitnet_forward_identity_2x2 | 2. BitNet Forward | `identity-like 2×2 matrix forward pass` | Functional |
| 7 | L174 | bitnet_forward_negation | 2. BitNet Forward | `negation weight matrix forward pass` | Functional |
| 8 | L188 | bitnet_forward_with_scale | 2. BitNet Forward | `scaled forward output ≈ expected float` | Functional |
| 9 | L205 | dlfet_not_truth_table | 3. DLFET Gates | `DLFET NOT: NOT(+1)=-1, NOT(-1)=+1, NOT(0)=0` | Logic |
| 10 | L214 | dlfet_not_involution | 3. DLFET Gates | `NOT(NOT(v))==v for all 3 trit values` | Logic |
| 11 | L223 | dlfet_nand_truth_table | 3. DLFET Gates | `DLFET NAND gate truth table verified` | Logic |
| 12 | L242 | dlfet_full_adder_zero_carry | 3. DLFET Adder | `0+0+0 sum=0, carry=0` | Arithmetic |
| 13 | L258 | dlfet_full_adder_carry_generation | 3. DLFET Adder | `+1+1+0 carry=+1, sum=-1` | Arithmetic |
| 14 | L275 | dlfet_full_adder_all_positive | 3. DLFET Adder | `+1+1+1 carry=+1, sum=0` | Arithmetic |
| 15 | L460 | dlfet_full_adder_all_27_combinations | 3. DLFET Adder | `all 27 input triples produce valid trit output` | Arithmetic |
| 16 | L290 | sparse_matrix_create_and_free | 4. Sparse Matrix | `allocate 4×4 matrix: rows=4, nnz=0` | Memory |
| 17 | L301 | dense_to_sparse_conversion | 4. Sparse Matrix | `dense→sparse: nnz in [1,4]` | Transformation |
| 18 | L317 | sparse_mvm_identity_like | 4. Sparse MVM | `identity-like sparse MVM: result[0]=+1 result[1]=-1` | Functional |
| 19 | L336 | sparse_mvm_zero_matrix | 4. Sparse MVM | `zero matrix MVM → all UNKNOWN output` | Boundary |
| 20 | L432 | sparse_large_matrix_8x8 | 4. Sparse Matrix | `8×8 sparse matrix alloc and MVM completes` | Functional |
| 21 | L358 | ternary_linear_layer_create | 5. Linear Layer | `ternary_linear_create: layer not NULL` | Initialization |
| 22 | L373 | ternary_linear_forward_pass | 5. Linear Layer | `forward pass through 2-input, 2-output layer` | Functional |
| 23 | L397 | ternary_activation_relu | 5. Activations | `ternary ReLU: -1→0, 0→0, +1→+1` | Functional |
| 24 | L406 | ternary_activation_idempotent | 5. Activations | `activation applied twice == once (idempotent)` | Functional |

---

## Suite 23: Fault-Tolerant Networking ⭐NEW

**Source**: `tests/test_fault_tolerant_network.c`
**Runtime Assertions**: 25
**Source-Level Entries**: 25
**Harness**: `ASSERT_EQ/ASSERT_TRUE(cond, msg)` + `PASS()` per function
**Output Reading**: `test_name  [PASS]`; final `=== Results: 25 passed, 0 failed ===`
**What it tests**: Ternary Hamming ECC (encode/decode/correct), multi-radix routing table, ternary Byzantine-fault-tolerant consensus (unanimous/majority/no-majority), ternary network packet encode/tamper-detect/decode, and FTNIC NIC driver send/receive/fault tracking.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L95 | hamming_encode_basic | 1. Hamming ECC | `encode 4-trit data → codeword[0..3] correct` | Encoding |
| 2 | L115 | hamming_encode_decode_roundtrip | 1. Hamming ECC | `encode then decode with no error: decoded==original` | Encoding |
| 3 | L131 | hamming_single_error_correction | 1. Hamming ECC | `introduce 1-trit error → decode corrects it` | Functional |
| 4 | L153 | hamming_all_zero_data | 1. Hamming ECC | `all-UNKNOWN data roundtrips cleanly` | Boundary |
| 5 | L169 | hamming_all_positive_data | 1. Hamming ECC | `all-TRUE data roundtrips cleanly` | Boundary |
| 6 | L185 | hamming_all_negative_data | 1. Hamming ECC | `all-FALSE data roundtrips cleanly` | Boundary |
| 7 | L201 | hamming_error_at_every_position | 1. Hamming ECC | `single error injected at each position is corrected` | Functional |
| 8 | L230 | hamming_all_81_data_patterns | 1. Hamming ECC | `all 81 (3^4) data patterns encode/correct correctly` | Stress |
| 9 | L261 | multi_radix_route_basic | 2. Routing | `routing table lookup returns correct next_hop and cost` | Functional |
| 10 | L278 | multi_radix_route_empty_table | 2. Routing | `empty routing table returns no-hop sentinel` | Boundary |
| 11 | L293 | multi_radix_route_selects_lowest_cost | 2. Routing | `lowest-cost route selected among multiple entries` | Functional |
| 12 | L320 | consensus_unanimous_agreement | 3. BFT Consensus | `all 3 nodes vote TRUE → decided=TRUE` | Consensus |
| 13 | L335 | consensus_2_of_3_majority | 3. BFT Consensus | `2/3 TRUE votes → decided=TRUE` | Consensus |
| 14 | L351 | consensus_no_majority_ongoing | 3. BFT Consensus | `no majority → state remains ONGOING (UNKNOWN)` | Consensus |
| 15 | L366 | consensus_false_majority_decides | 3. BFT Consensus | `2/3 FALSE votes → decided=FALSE` | Consensus |
| 16 | L382 | consensus_unknown_supermajority | 3. BFT Consensus | `UNKNOWN supermajority → decided=UNKNOWN` | Consensus |
| 17 | L403 | packet_encode_decode_roundtrip | 4. Packet ECC | `packet encode then decode with no error` | Encoding |
| 18 | L422 | packet_checksum_tamper_detection | 4. Packet ECC | `corrupt one trit → decode returns -1 (tamper)` | Negative/error |
| 19 | L441 | packet_zero_payload | 4. Packet ECC | `zero-trit payload encodes and decodes cleanly` | Boundary |
| 20 | L456 | packet_full_payload | 4. Packet ECC | `full-size payload encodes and decodes cleanly` | Boundary |
| 21 | L475 | packet_header_preserved_through_ecc | 4. Packet ECC | `version, src, dst, type preserved through ECC` | Functional |
| 22 | L499 | ftnic_send_packet | 5. FTNIC Driver | `FTNIC send: returns 0, updates tx_count` | IPC |
| 23 | L518 | ftnic_receive_valid | 5. FTNIC Driver | `FTNIC receive valid packet: returns 0` | IPC |
| 24 | L536 | ftnic_receive_corrupted_packet | 5. FTNIC Driver | `FTNIC receive corrupted packet: returns -1, faults++` | Negative/error |
| 25 | L554 | ftnic_fault_status_tracking | 5. FTNIC Driver | `fault status trit reflects pending fault` | Functional |

---

## Suite 24: Adversarial / Negative-Path ⭐NEW

**Source**: `tests/test_adversarial.c`
**Runtime Assertions**: 34
**Source-Level Entries**: 34
**Harness**: `ASSERT_EQ/ASSERT_TRUE(cond, msg)` + `PASS()` per function
**Output Reading**: `test_name  [PASS]`; final `=== Results: 34 passed, 0 failed ===`
**What it tests**: Exhaustive negative-path coverage — every API in memory, IPC, capabilities, syscall, scheduler, and trit encoding is attacked with out-of-range inputs, double-free/destroy, exhaustion, use-after-free, readonly violations, and invalid opcodes. All must be rejected cleanly.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L43 | mem_read_write_out_of_range_page | 1. Memory Safety | `mem_read(page=-1)==UNKNOWN; mem_write(page=999)==-1` | Negative/error |
| 2 | L58 | mem_read_write_out_of_range_offset | 1. Memory Safety | `mem_read(offset=-1)==UNKNOWN; offset=MAX==-1` | Negative/error |
| 3 | L72 | mem_double_free_rejected | 1. Memory Safety | `mem_free(p)==0 first; mem_free(p)==-1 second` | Negative/error |
| 4 | L82 | mem_use_after_free_returns_unknown | 1. Memory Safety | `mem_read after free==UNKNOWN; mem_write==-1` | Negative/error |
| 5 | L100 | mem_oom_exhaustion | 1. Memory Safety | `alloc until OOM: final alloc returns -1` | Negative/error |
| 6 | L115 | mem_write_to_readonly_page | 1. Memory Safety | `mem_write to readonly page returns -1` | Access control |
| 7 | L128 | mem_reserve_already_allocated_page | 1. Memory Safety | `mem_reserve on allocated page returns -1` | Negative/error |
| 8 | L139 | mem_free_reserved_page | 1. Memory Safety | `mem_free on reserved page returns -1` | Negative/error |
| 9 | L150 | mem_init_clamps_page_count | 1. Memory Safety | `negative/huge page counts clamped to valid range` | Boundary |
| 10 | L167 | ipc_send_on_destroyed_endpoint | 2. IPC Hardening | `send on destroyed endpoint returns -1` | Negative/error |
| 11 | L181 | ipc_recv_on_destroyed_endpoint | 2. IPC Hardening | `recv on destroyed endpoint returns -1` | Negative/error |
| 12 | L195 | ipc_double_destroy_endpoint | 2. IPC Hardening | `destroy twice: second returns -1` | Negative/error |
| 13 | L205 | ipc_endpoint_exhaustion | 2. IPC Hardening | `create until full: final create returns -1` | Negative/error |
| 14 | L218 | ipc_send_recv_out_of_range | 2. IPC Hardening | `send/recv ep=-1 and ep=999 return -1` | Negative/error |
| 15 | L233 | ipc_msg_build_length_clamped | 2. IPC Hardening | `msg.length clamped to IPC_MSG_MAX_WORDS` | Boundary |
| 16 | L244 | ipc_notification_exhaustion | 2. IPC Hardening | `notification slots exhausted: final create returns -1` | Negative/error |
| 17 | L255 | ipc_signal_wait_out_of_range | 2. IPC Hardening | `signal/wait idx=-1 and idx=999 return -1` | Negative/error |
| 18 | L270 | cap_grant_without_GRANT_right | 3. Capability Hardening | `grant without G-right returns -1` | Access control |
| 19 | L284 | cap_grant_from_revoked_cap | 3. Capability Hardening | `grant from revoked cap returns -1` | Access control |
| 20 | L298 | cap_grant_rights_monotonically_narrow | 3. Capability Hardening | `granted rights ⊆ parent rights (monotone narrowing)` | Access control |
| 21 | L312 | cap_table_exhaustion | 3. Capability Hardening | `cap table exhausted: final create returns -1` | Negative/error |
| 22 | L323 | cap_double_revoke | 3. Capability Hardening | `second revoke returns -1` | Negative/error |
| 23 | L334 | cap_check_invalid_index_denied | 3. Capability Hardening | `cap_check(idx=-1) and (idx=999) denied` | Negative/error |
| 24 | L345 | syscall_dispatch_invalid_sysno | 4. Syscall | `syscall dispatch with unknown sysno returns error` | Negative/error |
| 25 | L357 | operand_stack_overflow_and_underflow | 4. VM Stack | `push beyond capacity → overflow; pop empty → underflow` | Negative/error |
| 26 | L370 | sched_thread_exhaustion | 5. Scheduler | `create threads until MAX_THREADS: final returns -1` | Negative/error |
| 27 | L384 | sched_double_destroy_thread | 5. Scheduler | `destroy same thread twice: second returns -1` | Negative/error |
| 28 | L395 | sched_ops_invalid_tid | 5. Scheduler | `block/unblock/set-priority with tid=-1 return -1` | Negative/error |
| 29 | L408 | sched_unblock_non_blocked_rejected | 5. Scheduler | `unblock thread not in BLOCKED state returns -1` | Negative/error |
| 30 | L418 | sched_set_invalid_priority | 5. Scheduler | `set_priority with out-of-range value returns -1` | Negative/error |
| 31 | L428 | sched_yield_no_threads | 5. Scheduler | `yield with no threads returns gracefully` | Negative/error |
| 32 | L436 | sched_pick_next_all_dead | 5. Scheduler | `pick_next when all threads dead returns NULL` | Boundary |
| 33 | L445 | trit_pack_unpack_roundtrip | 6. Trit Encoding | `pack then unpack all 3 values: F→0x02, U→0x00, T→0x01` | Encoding |
| 34 | L457 | trit_unpack_fault_code_returns_unknown | 6. Trit Encoding | `unpack invalid code (0xFF) returns UNKNOWN` | Negative/error |

---

## Suite 25: Crown Jewel Reversion Guard ⭐NEW

**Source**: `tests/test_ternary_reversion_guard.c`
**Runtime Assertions**: 37
**Source-Level Entries**: 37
**Harness**: `ASSERT_EQ(actual, expected, msg)` + `PASS()` per function
**Output Reading**: `test_name  [PASS]`; final `=== Results: 37 passed, 0 failed ===`
**What it tests**: The "Crown Jewel" regression guard — exhaustive Kleene logic laws, SIMD packed-64 operations vs scalar equivalence, trit XOR/crypto primitives, FFT butterfly correctness, Avizienis balanced-ternary, Ingole patent cross-checks, Hamming ECC, trit conversion APIs, and NULL-logic propagation. Failure here indicates binary reversion of core ternary invariants.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L89 | kleene_and_complete_truth_table | 1. Kleene Laws | `trit_and(a,b) for all 9 pairs matches Kleene AND` | Logic |
| 2 | L106 | kleene_or_complete_truth_table | 1. Kleene Laws | `trit_or(a,b) for all 9 pairs matches Kleene OR` | Logic |
| 3 | L120 | kleene_not_involution | 1. Kleene Laws | `trit_not: 3 values correct + NOT(NOT(v))==v` | Logic |
| 4 | L132 | kleene_implies_complete_truth_table | 1. Kleene Laws | `trit_implies for all 9 pairs (Kleene implication)` | Logic |
| 5 | L147 | kleene_equiv_complete_truth_table | 1. Kleene Laws | `trit_equiv for all 6 distinct pairs` | Logic |
| 6 | L162 | kleene_de_morgan_laws | 1. Kleene Laws | `NOT(AND(a,b))==OR(NOT(a),NOT(b)) for all 9 pairs` | Logic |
| 7 | L183 | kleene_commutativity_associativity_absorption | 1. Kleene Laws | `commutativity, idempotence, AND-OR absorption for all pairs` | Logic |
| 8 | L215 | packed64_and_matches_scalar | 2. SIMD Guard | `packed64 AND == scalar AND for all trit pair combinations` | Logic |
| 9 | L224 | packed64_or_matches_scalar | 2. SIMD Guard | `packed64 OR == scalar OR for all trit pair combinations` | Logic |
| 10 | L237 | packed64_not_involution | 2. SIMD Guard | `packed64 NOT(NOT(x))==x` | Logic |
| 11 | L248 | packed64_per_position_matches_scalar_ops | 2. SIMD Guard | `each of 32 positions in packed64 matches scalar result` | Logic |
| 12 | L262 | pack_unpack_all_values_roundtrip | 3. Encoding Guard | `trit_pack then trit_unpack roundtrip for F/U/T` | Encoding |
| 13 | L283 | trit_xor_balanced_mod3_addition | 3. Crypto Guard | `trit_xor == mod-3 addition for all 9 pairs` | Encoding |
| 14 | L298 | trit_xor_inv_balanced_mod3_subtraction | 3. Crypto Guard | `trit_xor_inv == mod-3 subtraction for all 9 pairs` | Encoding |
| 15 | L313 | trit_xor_xor_inv_is_identity | 3. Crypto Guard | `XOR then XOR_INV with same key == identity` | Encoding |
| 16 | L328 | encrypt_then_decrypt_recovers_plaintext | 3. Crypto Guard | `encrypt then decrypt returns original trit sequence` | Encoding |
| 17 | L347 | keygen_same_seed_same_key | 3. Crypto Guard | `same seed produces identical key stream` | Functional |
| 18 | L361 | hash_deterministic_and_full_range | 3. Crypto Guard | `hash is deterministic and outputs all 3 trit values` | Encoding |
| 19 | L379 | mac_sign_verify_roundtrip | 3. Crypto Guard | `MAC sign then verify returns TRIT_TRUE` | Encoding |
| 20 | L397 | fft_step_radix3_butterfly | 4. Transform Guard | `radix-3 FFT butterfly produces expected output values` | Functional |
| 21 | L415 | avizienis_ternary_binary_roundtrip | 4. Transform Guard | `Avizienis binary→ternary roundtrip recovers original` | Transformation |
| 22 | L430 | avizienis_output_includes_minus_one | 4. Transform Guard | `Avizienis output set includes -1 (full ternary range)` | Functional |
| 23 | L447 | ingole_tnot_matches_kleene | 5. Patent Cross-Check | `Ingole TNOT matches Kleene NOT for all 3 values` | Logic |
| 24 | L460 | ingole_cwc_ccwc_cyclic_rotations | 5. Patent Cross-Check | `CWC and CCWC are cyclic-rotation inverses` | Logic |
| 25 | L474 | ingole_tand_tor_via_patent | 5. Patent Cross-Check | `Ingole TAND/TOR match Kleene min/max` | Logic |
| 26 | L490 | ingole_xtor_mod3_addition | 5. Patent Cross-Check | `Ingole XTOR matches mod-3 addition` | Logic |
| 27 | L505 | ingole_half_adder_all_pairs | 5. Patent Cross-Check | `Ingole half-adder all 9 pairs match expected` | Arithmetic |
| 28 | L520 | ingole_full_adder_all_triples | 5. Patent Cross-Check | `Ingole full-adder all 27 triples match expected` | Arithmetic |
| 29 | L539 | hamming_encode_decode_no_error | 6. Hamming Guard | `Hamming encode then decode with no error` | Encoding |
| 30 | L555 | hamming_corrects_single_trit_error | 6. Hamming Guard | `Hamming corrects single-trit error` | Functional |
| 31 | L575 | trit_from_bool_mapping | 7. Conversion Guard | `trit_from_bool(false)==FALSE, (true)==TRUE` | Transformation |
| 32 | L588 | trit_to_bool_strict_definite_only | 7. Conversion Guard | `trit_to_bool only defined for TRUE/FALSE, not UNKNOWN` | Negative/error |
| 33 | L601 | trit_from_int_range_and_clamping | 7. Conversion Guard | `trit_from_int(-1)==FALSE, (0)==UNKNOWN, (+1)==TRUE; clamps` | Boundary |
| 34 | L616 | trit_to_trit2_and_back_roundtrip | 7. Conversion Guard | `trit↔trit2 roundtrip for all 3 values` | Transformation |
| 35 | L631 | kleene_null_and_propagation | 8. NULL Propagation | `NULL AND T==NULL, NULL AND F==NULL (strict mode)` | Logic |
| 36 | L645 | kleene_null_or_propagation | 8. NULL Propagation | `NULL OR F==NULL, NULL OR T==T (strict mode)` | Logic |
| 37 | L660 | kleene_null_equals_three_valued | 8. NULL Propagation | `NULL==T==NULL, NULL==NULL==NULL (three-value equality)` | Logic |

---

## Suite 48: Gödel Machine ⭐NEW

**Source**: `tests/test_godel_machine.c`
**Runtime Assertions**: 21
**Source-Level Entries**: 21
**Harness**: `if (condition) PASS(); else FAIL(msg)` — function-level, ternary utility metric
**Output Reading**: `test_name  [PASS]`; final `=== Results: 21 passed, 0 failed ===`
**What it tests**: seT6 Gödel Machine — self-modifying system that applies inference rules (modus ponens, conjunction, trit-eval) to theorems, tracks utility with binary-reversion penalty, and only accepts switch-programs that increase the utility score.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L111 | godel_init_succeeds | 1. Init | `godel_init(&gm)==0; gm.initialized==TRUE; gm.n_axioms==6` | Initialization |
| 2 | L119 | godel_init_null_returns_error | 1. Init | `godel_init(NULL)==-1` | Negative/error |
| 3 | L127 | get_axiom_returns_valid_axiom | 2. Axioms | `get_axiom(0): verified==TRUE, active==TRUE, name non-empty` | Functional |
| 4 | L136 | get_axiom_oob_returns_null | 2. Axioms | `get_axiom(999)==NULL` | Negative/error |
| 5 | L144 | axioms_cover_all_5_types | 2. Axioms | `6 axioms cover all 5 GODEL_AXIOM_* type constants` | Functional |
| 6 | L160 | apply_rule_modus_ponens | 3. Inference Rules | `apply MODUS_PONENS → theorem id>=0, active==T, verified==T` | Functional |
| 7 | L169 | apply_rule_conjunction | 3. Inference Rules | `apply CONJUNCTION → theorem id>=0, active==T` | Functional |
| 8 | L178 | apply_rule_trit_eval | 3. Inference Rules | `apply TRIT_EVAL → theorem id>=0, verified==T` | Functional |
| 9 | L190 | delete_theorem_deactivates | 4. Theorem Lifecycle | `delete_theorem(id)==0; theorem.active==FALSE` | Functional |
| 10 | L200 | delete_theorem_oob_returns_error | 4. Theorem Lifecycle | `delete_theorem(999)==-1` | Negative/error |
| 11 | L211 | set_switchprog_stores_diff | 5. Self-Modification | `set_switchprog: id>=0, n_switchprogs==1, applied==UNKNOWN` | Functional |
| 12 | L224 | check_returns_0_when_no_delta | 6. Utility Check | `godel_check with no pending delta returns 0` | Functional |
| 13 | L232 | check_returns_1_when_delta_positive | 6. Utility Check | `godel_check after utility-increasing switch returns 1` | Functional |
| 14 | L248 | state2theorem_encodes_runtime_state | 7. State Encoding | `state2theorem creates theorem with type==GODEL_AXIOM_STATE` | Functional |
| 15 | L263 | utility_perfect_score_equals_1 | 8. Utility Metric | `utility==1.0 when all tests pass, no reversions` | Functional |
| 16 | L273 | utility_zero_when_no_tests | 8. Utility Metric | `utility==0.0 when total_tests==0` | Boundary |
| 17 | L283 | utility_decreases_with_reversions | 8. Utility Metric | `utility(dirty) < utility(clean) when reversions > 0` | Functional |
| 18 | L295 | delta_utility_tracked_correctly | 8. Utility Metric | `delta_utility == new_u − old_u within 1e-10` | Functional |
| 19 | L313 | no_accept_when_utility_decreases | 6. Utility Check | `godel_check rejects switch-prog that decreases utility` | Negative/error |
| 20 | L329 | multiple_derivations_chain_correctly | 3. Inference Rules | `t2.derived_from[0]==t1 (chained inference)` | Functional |
| 21 | L343 | biops_search_fraction_default | 5. Self-Modification | `search_fraction in (0, 1]` | Functional |

---

## Suite 49: SIMD Regression ⭐NEW

**Source**: `tests/test_trit_simd_regression.c`
**Runtime Assertions**: 10
**Source-Level Entries**: 10
**Harness**: `if (ok) PASS(); else FAIL(msg)` — exhaustive loop over all trit encodings
**Output Reading**: `test_name  [PASS]`; final `=== Results: 10 passed, 0 failed ===`
**What it tests**: Regression guard for the `trit_and_packed64` / `trit_or_packed64` / `trit_not_packed64` SIMD operations — each is verified against scalar Kleene operations over all possible 2-bit trit encodings, positions, and algebraic law checks.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L59 | simd_and_all_9_pairs | 1. AND Correctness | `packed64_and matches scalar for all 9 trit-pair combos` | Logic |
| 2 | L80 | simd_or_all_9_pairs | 1. OR Correctness | `packed64_or matches scalar for all 9 trit-pair combos` | Logic |
| 3 | L101 | simd_not_all_32_positions | 2. NOT Correctness | `packed64_not correct at each of 32 positions` | Logic |
| 4 | L121 | simd_not_involution_all_encodings | 2. NOT Correctness | `NOT(NOT(x))==x for all valid 2-bit encodings` | Logic |
| 5 | L141 | simd_and_all_true_identity | 3. Algebraic Laws | `AND(x, all-TRUE)==x for all x (identity)` | Logic |
| 6 | L159 | simd_or_all_false_identity | 3. Algebraic Laws | `OR(x, all-FALSE)==x for all x (identity)` | Logic |
| 7 | L177 | simd_demorgan_law_100_patterns | 3. Algebraic Laws | `NOT(AND(a,b))==OR(NOT(a),NOT(b)) for 100 random packed patterns` | Logic |
| 8 | L199 | simd_outputs_contain_full_trit_range | 4. Range Guard | `AND/OR outputs include all 3 trit values (no binary flattening)` | Functional |
| 9 | L227 | simd_and_or_commutativity | 3. Algebraic Laws | `AND(a,b)==AND(b,a) and OR(a,b)==OR(b,a)` | Logic |
| 10 | L247 | simd_absorption_laws | 3. Algebraic Laws | `AND(a,OR(a,b))==a and OR(a,AND(a,b))==a` | Logic |

---

## Suite 50: Binary Sentinel ⭐NEW

**Source**: `tests/test_binary_sentinel.c`
**Runtime Assertions**: 12
**Source-Level Entries**: 12
**Harness**: `if (ok) PASS(); else FAIL(msg)` — range-exhaustive sentinel checks
**Output Reading**: `sentinel_* [PASS]`; final `=== Results: 12 passed, 0 failed ===`
**What it tests**: Binary-reversion detection — every major subsystem (Kleene logic, SIMD, crypto XOR, hash, encryption, trit-cast, pack/unpack, FFT, Avizienis, implication/equivalence) must produce all 3 trit values. A failure means the subsystem has collapsed to binary and the core ternary invariant is broken.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L60 | sentinel_kleene_ops_produce_all_3_values | 1. Kleene | `AND/OR/NOT outputs contain F, U, and T` | Functional |
| 2 | L86 | sentinel_simd_packed64_full_trit_range | 2. SIMD | `packed64 AND/OR outputs contain all 3 trit values` | Functional |
| 3 | L130 | sentinel_crypto_xor_produces_all_trits | 3. Crypto | `trit_xor over varied keys/plaintext yields F, U, T` | Encoding |
| 4 | L148 | sentinel_hash_output_full_trit_range | 3. Crypto | `tcrypto_hash over varied inputs yields F, U, T` | Encoding |
| 5 | L167 | sentinel_encrypt_decrypt_preserves_trit_range | 3. Crypto | `encrypt then decrypt returns original; ciphertext has all 3 values` | Encoding |
| 6 | L203 | sentinel_trit_cast_bool_roundtrip | 4. Encoding | `trit_cast(false)==FALSE and trit_cast(true)==TRUE; range intact` | Transformation |
| 7 | L225 | sentinel_pack_unpack_roundtrip_all_3_values | 4. Encoding | `trit_pack/unpack roundtrip and all 3 pack codes seen` | Encoding |
| 8 | L242 | sentinel_fft_butterfly_ternary_output | 5. Transforms | `radix-3 FFT butterfly outputs contain F, U, T` | Functional |
| 9 | L270 | sentinel_avizienis_balanced_ternary_full_range | 5. Transforms | `Avizienis conversion output includes -1, 0, +1` | Functional |
| 10 | L297 | sentinel_no_implicit_bool_to_trit_flattening | 6. Type Guard | `bool-valued comparison does not flatten to {0,1}; -1 present` | Negative/error |
| 11 | L318 | sentinel_ternary_mac_not_boolean | 6. Type Guard | `ternary MAC accumulates to -2 (not clamped to binary range)` | Functional |
| 12 | L335 | sentinel_implies_equiv_full_range | 1. Kleene | `trit_implies / trit_equiv outputs contain all 3 values` | Logic |

---

## Suite 51: Ternary Compiler Integration ⭐NEW

**Source**: `tests/test_ternary_compiler_integration.c`
**Runtime Assertions**: 19
**Source-Level Entries**: 19 (+ 1 `[DIAG]` note — not a failure)
**Harness**: `if (len>0) PASS()` for compile-roundtrip tests; `if (result==expected) PASS()` for VM execution tests
**Output Reading**: `test_name  [PASS]` or `  [DIAG] message`; final `=== Results: 19 passed, 0 failed ===`
**What it tests**: End-to-end seT6 ternary-first compiler — parsing and compiling Kleene logic, trit variable/array declarations, trit negation, capability init, 3-level scheduler priority, IPC endpoints, Gödel utility metric, Gödel axiom check, search fraction, Huffman encoding, SIMD concept, radix-3 conversion, multi-function programs, Verilog emission, consensus and accept-any VM opcodes.

| # | Line | Test Name | Section | Assertion / Expression | Category |
|---|------|-----------|---------|----------------------|----------|
| 1 | L81 | kleene_and_true_true | 1. Kleene Execution | `compile "trit x=T AND T" → VM result==TRUE` | Functional |
| 2 | L94 | kleene_and_true_unknown | 1. Kleene Execution | `compile "trit x=T AND U" → VM result==UNKNOWN` | Functional |
| 3 | L104 | kleene_or_false_true | 1. Kleene Execution | `compile "trit x=F OR T" → VM result==TRUE` | Functional |
| 4 | L119 | trit_var_decl_compiles | 2. Declaration | `"trit x" compiles to non-empty bytecode` | Parsing |
| 5 | L127 | trit_array_decl_compiles | 2. Declaration | `"trit arr[4]" compiles to non-empty bytecode` | Parsing |
| 6 | L140 | trit_negation_minus_one | 2. Operators | `compile trit negation "-(+1)" → VM result==-1` | Functional |
| 7 | L154 | cap_init_function_compiles | 3. System Patterns | `cap_init(…) pattern compiles cleanly` | Parsing |
| 8 | L164 | scheduler_3level_priority | 3. System Patterns | `3-level priority schedule pattern compiles and runs` | Functional |
| 9 | L180 | ipc_endpoint_send_recv | 3. System Patterns | `IPC send/recv pattern compiles cleanly` | Parsing |
| 10 | L198 | godel_utility_sigma9_metric | 4. Gödel Integration | `Gödel utility computation compiles and returns value` | Functional |
| 11 | L215 | godel_axiom_consistency_check | 4. Gödel Integration | `Gödel axiom consistency check compiles` | Parsing |
| 12 | L235 | godel_biops_search_fraction | 4. Gödel Integration | `Gödel BIOPS search fraction pattern compiles` | Parsing |
| 13 | L255 | ternary_huffman_encoding | 5. Algorithms | `Huffman encoding pattern compiles and emits bytecode` | Parsing |
| 14 | L273 | packed_simd_32_trits_concept | 5. Algorithms | `SIMD 32-trit packed concept compiles; [DIAG] VM lacks native SIMD ops` | Hardware/ALU |
| 15 | L296 | radix3_conversion_concept | 5. Algorithms | `radix-3 conversion pattern compiles` | Parsing |
| 16 | L314 | multi_function_program | 6. Program Structure | `multi-function program (3 functions) compiles and runs` | Functional |
| 17 | L340 | verilog_emit_kleene_and | 6. Program Structure | `Verilog emission of Kleene AND compiles cleanly` | Functional |
| 18 | L356 | vm_consensus_opcode_exists | 7. VM Opcodes | `CONSENSUS opcode accepted by VM dispatch` | Hardware/ALU |
| 19 | L370 | vm_accept_any_opcode_exists | 7. VM Opcodes | `ACCEPT_ANY opcode accepted by VM dispatch` | Hardware/ALU |

---

## Suite 52: Compiler: Basic Integration ⭐NEW

**Source**: `tools/compiler/tests/test_basic.c`
**Runtime Assertions**: 26
**Source-Level Entries**: 4
**Harness**: `void test_name(void) { assert(...); }` — function-level, abort on fail via libc `assert()`
**Output Reading**: Manual printf per function. Final: `=== All tests passed! ===`

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L9 | test_trit_operations | Trit ops | `assert(trit_mul(P,P)==P); assert(trit_mul(P,N)==N); assert(trit_mul(N,N)==P); assert(trit_mul(Z,P)==Z); assert(trit_add(P,P,&c)==N); assert(carry==P); assert(trit_add(P,Z,&c)==P); assert(carry==Z); assert(trit_min(N,P)==N); assert(trit_max(N,P)==P)` | Arithmetic |
| 2 | L34 | test_tokenizer | Tokenizer | `assert(tokens[0].type==TOK_INT && tokens[0].value==1); assert(tokens[1].type==TOK_PLUS); assert(tokens[2].type==TOK_INT && tokens[2].value==2); assert(tokens[3].type==TOK_MUL); assert(tokens[4].type==TOK_INT && tokens[4].value==3); assert(tokens[5].type==TOK_EOF)` | Parsing |
| 3 | L48 | test_codegen | Codegen | `assert(bytecode[0]==OP_PUSH); assert(bytecode[1]==1); ... assert(bytecode[8]==OP_HALT); assert(bc_idx==9)` | Functional |
| 4 | L70 | test_vm_execution | VM exec | `vm_run(bytecode, bc_idx)` (implicit — expects "Result: 7") | Integration |

---

## Suite 53: Compiler: Bootstrap Self-Host (TASK-018) ⭐NEW

**Source**: `tools/compiler/tests/test_bootstrap.c`
**Runtime Assertions**: 33
**Source-Level Entries**: 21
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L15 | test_symtab_init | Symbol table | `ASSERT_EQ(tab.count, 0); ASSERT_EQ(tab.next_offset, 0)` | Initialization |
| 2 | L22 | test_symtab_add | Symbol table | `ASSERT_EQ(off, 0); ASSERT_EQ(tab.count, 1); ASSERT_EQ(off2, 1); ASSERT_EQ(tab.count, 2)` | Functional |
| 3 | L33 | test_symtab_lookup | Symbol table | `ASSERT_EQ(symtab_lookup(&tab,"alpha"), 0); ASSERT_EQ(…,"beta"), 1); ASSERT_EQ(…,"gamma"), -1)` | Functional |
| 4 | L43 | test_symtab_full | Symbol table | `ASSERT_TRUE(symtab_add(&tab, name, 0) >= 0); ASSERT_EQ(symtab_add(&tab,"overflow",0), -1)` | Boundary |
| 5 | L58 | test_bootstrap_simple_const | Compilation | `ASSERT_TRUE(len > 0); ASSERT_TRUE(len >= 3)` | Bootstrap |
| 6 | L66 | test_bootstrap_addition | Compilation | `ASSERT_TRUE(len > 0); ASSERT_TRUE(len >= 3)` | Bootstrap |
| 7 | L75 | test_bootstrap_var_decl | Compilation | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 8 | L81 | test_bootstrap_multi_var | Compilation | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 9 | L90 | test_bootstrap_self_test | Self-test | `ASSERT_EQ(result, 0)` | Bootstrap |
| 10 | L95 | test_bootstrap_subtraction | Compilation | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 11 | L102 | test_bootstrap_nested_expr | Compilation | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 12 | L111 | test_bootstrap_pointer_syntax | Compilation | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 13 | L121 | test_bootstrap_roundtrip | Compilation | `ASSERT_TRUE(len1 > 0); ASSERT_EQ(len1, len2); ASSERT_EQ(code1[i], code2[i])` | Bootstrap |
| 14 | L134 | test_bootstrap_error_handling | Compilation | `ASSERT_TRUE(len == -1 \|\| len > 0)` | Error handling |
| 15 | L144 | test_bootstrap_if_simple | Control flow | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 16 | L154 | test_bootstrap_if_else | Control flow | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 17 | L162 | test_bootstrap_while_loop | Control flow | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 18 | L170 | test_bootstrap_for_loop | Control flow | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 19 | L178 | test_bootstrap_comparison_eq | Control flow | `ASSERT_TRUE(len > 0)` | Bootstrap |
| 20 | L187 | test_bootstrap_comparison_ops | Control flow | `ASSERT_TRUE(len > 0)` ×2 | Bootstrap |
| 21 | L198 | test_bootstrap_nested_if | Control flow | `ASSERT_TRUE(len > 0)` | Bootstrap |

---

## Suite 54: Compiler: Hardware Simulation ⭐NEW

**Source**: `tools/compiler/tests/test_hardware_simulation.c`
**Runtime Assertions**: 10
**Source-Level Entries**: 7
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_NEQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L14 | test_alu_add_accuracy | ALU ops | `ASSERT_EQ(software_result, a + b)` (loop) | Hardware/ALU |
| 2 | L31 | test_alu_mul_accuracy | ALU ops | `ASSERT_EQ(software_result, a * b)` (loop) | Hardware/ALU |
| 3 | L47 | test_alu_overflow_handling | ALU ops | `ASSERT_NEQ(result, max_val+1); ASSERT_TRUE(result >= -max_val && result <= max_val)` | Boundary |
| 4 | L70 | test_register_behavior | Registers | `ASSERT_EQ(trit_word_to_int(reg[i]), 42)` (loop) | Hardware/ALU |
| 5 | L87 | test_alu_timing_consistency | Timing | `ASSERT_EQ(trit_word_to_int(res), va + vb)` (100 random) | Hardware/ALU |
| 6 | L100 | test_verilog_emission | Verilog | `ASSERT_EQ(trit_word_to_int(circuit[i]), i * 13)` (loop) | Hardware/ALU |
| 7 | L114 | test_pipeline_hazards | Pipeline | `ASSERT_EQ(result1, result2); ASSERT_EQ(result1, 150)` | Hardware/ALU |

---

## Suite 55: Compiler: IR / Constant Folding ⭐NEW

**Source**: `tools/compiler/tests/test_ir.c`
**Runtime Assertions**: 49
**Source-Level Entries**: 20
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_NOT_NULL/ASSERT_NULL/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L14 | test_fold_add | Const folding | `ASSERT_EQ(e->type, NODE_CONST); ASSERT_EQ(e->val, 3)` | IR/Optimization |
| 2 | L25 | test_fold_mul | Const folding | `ASSERT_EQ(e->type, NODE_CONST); ASSERT_EQ(e->val, 12)` | IR/Optimization |
| 3 | L36 | test_no_fold_vars | Const folding | `ASSERT_EQ(e->type, NODE_BINOP) … ASSERT_EQ(e->right->val, 2)` | IR/Optimization |
| 4 | L49 | test_fold_nested | Const folding | `ASSERT_EQ(e->type, NODE_CONST); ASSERT_EQ(e->val, 21)` | IR/Optimization |
| 5 | L62 | test_fold_partial | Const folding | `ASSERT_EQ(e->left->val, 3); ASSERT_EQ(e->right->type, NODE_VAR)` | IR/Optimization |
| 6 | L76 | test_single_const | Const folding | `ASSERT_EQ(e->type, NODE_CONST); ASSERT_EQ(e->val, 42)` | IR/Optimization |
| 7 | L86 | test_single_var | Const folding | `ASSERT_EQ(e->type, NODE_VAR)` | IR/Optimization |
| 8 | L95 | test_fold_add_zero | Const folding | `ASSERT_EQ(e->type, NODE_CONST); ASSERT_EQ(e->val, 5)` | Boundary |
| 9 | L104 | test_fold_mul_zero | Const folding | `ASSERT_EQ(e->type, NODE_CONST); ASSERT_EQ(e->val, 0)` | Boundary |
| 10 | L115 | test_fold_deep_chain | Const folding | `ASSERT_EQ(e->type, NODE_CONST); ASSERT_EQ(e->val, 27)` | IR/Optimization |
| 11 | L129 | test_optimize_null | NULL safety | `ASSERT_TRUE(1)` (no crash) | Boundary |
| 12 | L137 | test_fold_cmp_eq_true | Cmp folding | `ASSERT_EQ(e->val, 1)` | IR/Optimization |
| 13 | L146 | test_fold_cmp_eq_false | Cmp folding | `ASSERT_EQ(e->val, 0)` | IR/Optimization |
| 14 | L155 | test_fold_cmp_lt | Cmp folding | `ASSERT_EQ(e->val, 1)` | IR/Optimization |
| 15 | L164 | test_fold_cmp_gt | Cmp folding | `ASSERT_EQ(e->val, 1)` | IR/Optimization |
| 16 | L175 | test_create_if | Control flow nodes | `ASSERT_EQ(e->type, NODE_IF); ASSERT_NOT_NULL(e->condition)` | IR/Optimization |
| 17 | L186 | test_create_if_else | Control flow nodes | `ASSERT_EQ(e->type, NODE_IF); ASSERT_NOT_NULL(e->else_body)` | IR/Optimization |
| 18 | L196 | test_create_while | Control flow nodes | `ASSERT_EQ(e->type, NODE_WHILE)` | IR/Optimization |
| 19 | L207 | test_create_for | Control flow nodes | `ASSERT_EQ(e->type, NODE_FOR)` | IR/Optimization |
| 20 | L222 | test_create_block | Control flow nodes | `ASSERT_EQ(block->type, NODE_BLOCK)` | IR/Optimization |

---

## Suite 56: Compiler: Lexer / Tokenizer ⭐NEW

**Source**: `tools/compiler/tests/test_lexer.c`
**Runtime Assertions**: 87
**Source-Level Entries**: 20
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_STR_EQ; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L14 | test_single_integer | Basic tokenization | `ASSERT_EQ(tokens[0].type, TOK_INT); ASSERT_EQ(tokens[0].value, 42)` | Parsing |
| 2 | L21 | test_simple_addition | Basic tokenization | `ASSERT_EQ(tokens[0..3].type/value)` | Parsing |
| 3 | L31 | test_simple_multiplication | Basic tokenization | `ASSERT_EQ(tokens[0..3].type/value)` | Parsing |
| 4 | L41 | test_mixed_operators | Basic tokenization | `ASSERT_EQ(tokens[0..5].type/value)` | Parsing |
| 5 | L56 | test_no_spaces | Whitespace | `ASSERT_EQ(tokens[0..3].type/value)` | Parsing |
| 6 | L66 | test_extra_spaces | Whitespace | `ASSERT_EQ(tokens[0..3].type/value)` | Parsing |
| 7 | L76 | test_tabs_and_newlines | Whitespace | `ASSERT_EQ(tokens[0..3].type/value)` | Parsing |
| 8 | L88 | test_multi_digit | Multi-digit ints | `ASSERT_EQ(tokens[0].value, 123)` | Parsing |
| 9 | L98 | test_zero | Multi-digit ints | `ASSERT_EQ(tokens[0].value, 0)` | Boundary |
| 10 | L107 | test_long_expression | Complex exprs | `ASSERT_EQ(tokens[0..7].type/value)` | Parsing |
| 11 | L123 | test_chained_multiplication | Complex exprs | `ASSERT_EQ(tokens[0..5].type/value)` | Parsing |
| 12 | L138 | test_empty_string | Edge cases | `ASSERT_EQ(tokens[0].type, TOK_EOF)` | Boundary |
| 13 | L143 | test_whitespace_only | Edge cases | `ASSERT_EQ(tokens[0].type, TOK_EOF)` | Boundary |
| 14 | L150 | test_for_keyword | Keywords | `ASSERT_EQ(tokens[0].type, TOK_FOR)` | Parsing |
| 15 | L156 | test_while_keyword | Keywords | `ASSERT_EQ(tokens[0].type, TOK_WHILE)` | Parsing |
| 16 | L162 | test_for_loop_structure | Keywords | `ASSERT_EQ(tokens[0..16].type/value)` (17 assertions) | Parsing |
| 17 | L185 | test_invalid_loop_keyword | Keywords | `ASSERT_EQ(tokens[0].type, TOK_IDENT)` | Negative/error |
| 18 | L193 | test_return_keyword | Keywords | `ASSERT_EQ(tokens[0].type, TOK_RETURN)` | Parsing |
| 19 | L199 | test_comma_token | Keywords | `ASSERT_EQ(tokens[0..6].type/value)` | Parsing |
| 20 | L212 | test_ident_name_storage | Identifiers | `ASSERT_STR_EQ(token_names[0], "myVar")` | Parsing |

---

## Suite 57: Compiler: Logger ⭐NEW

**Source**: `tools/compiler/tests/test_logger.c`
**Runtime Assertions**: 33
**Source-Level Entries**: 14
**Harness**: `TEST(name) { ASSERT_STR_EQ/ASSERT_EQ/ASSERT_TRUE/ASSERT_NOT_NULL; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L33 | test_level_str_debug | log_level_str | `ASSERT_STR_EQ(log_level_str(LOG_DEBUG), "DEBUG")` | Functional |
| 2 | L37 | test_level_str_info | log_level_str | `ASSERT_STR_EQ(log_level_str(LOG_INFO), "INFO")` | Functional |
| 3 | L41 | test_level_str_warn | log_level_str | `ASSERT_STR_EQ(log_level_str(LOG_WARN), "WARN")` | Functional |
| 4 | L45 | test_level_str_error | log_level_str | `ASSERT_STR_EQ(log_level_str(LOG_ERROR), "ERROR")` | Functional |
| 5 | L51 | test_init_null | Init/close | `ASSERT_EQ(result, 0)` | Initialization |
| 6 | L58 | test_init_file | Init/close | `ASSERT_EQ(result, 0); ASSERT_NOT_NULL(fp)` | Initialization |
| 7 | L76 | test_log_entry_format | Output format | `ASSERT_TRUE(strstr(…,"[INFO]")!=NULL)` | Infrastructure |
| 8 | L100 | test_log_level_filter | Level filtering | `ASSERT_TRUE(strstr(…,"debug msg")==NULL); ASSERT_TRUE(…,"warn msg")!=NULL)` | Functional |
| 9 | L128 | test_log_multiple_entries | Multiple entries | `ASSERT_TRUE(strstr(…,"first")!=NULL); ASSERT_EQ(lines, 3)` | Functional |
| 10 | L160 | test_log_null_params | NULL defaults | `ASSERT_TRUE(strstr(…,"[System]")!=NULL)` | Boundary |
| 11 | L183 | test_log_in_lexer | Src integration | `ASSERT_TRUE(strstr(…,"[Lexer]")!=NULL)` | Integration |
| 12 | L202 | test_log_in_codegen | Src integration | `ASSERT_TRUE(strstr(…,"[Codegen]")!=NULL)` | Integration |
| 13 | L223 | test_log_in_vm | Src integration | `ASSERT_TRUE(strstr(…,"[VM]")!=NULL)` | Integration |
| 14 | L255 | test_log_in_parser | Src integration | `ASSERT_TRUE(strstr(…,"[Parser]")!=NULL)` | Integration |

---

## Suite 58: Compiler: Memory Model (TASK-015) ⭐NEW

**Source**: `tools/compiler/tests/test_memory.c`
**Runtime Assertions**: 46
**Source-Level Entries**: 19
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_NOT_NULL/ASSERT_STR_EQ; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L17 | test_addr_zero | Ternary address | `ASSERT_EQ(idx, MEMORY_SIZE / 2)` | Encoding |
| 2 | L24 | test_addr_positive | Ternary address | `ASSERT_EQ(idx, MEMORY_SIZE / 2 + 1)` | Encoding |
| 3 | L31 | test_addr_negative | Ternary address | `ASSERT_EQ(idx, MEMORY_SIZE / 2 - 1)` | Encoding |
| 4 | L38 | test_addr_roundtrip | Ternary address | `ASSERT_EQ(trit_word_to_int(addr), trit_word_to_int(addr2))` | Encoding |
| 5 | L48 | test_tmem_write_read | Ternary memory | `ASSERT_EQ(tmem_read(addr), 99)` | Memory |
| 6 | L56 | test_tmem_zero_addr | Ternary memory | `ASSERT_EQ(tmem_read(addr), -7)` | Memory |
| 7 | L64 | test_tmem_negative_addr | Ternary memory | `ASSERT_EQ(tmem_read(addr), 123)` | Memory |
| 8 | L74 | test_vm_store_load | VM memory ops | `ASSERT_EQ(vm_memory_read(10), 42)` | Memory |
| 9 | L90 | test_vm_store_multiple | VM memory ops | `ASSERT_EQ(vm_memory_read(0), 11); …(1), 22); …(2), 33)` | Memory |
| 10 | L105 | test_vm_sub | VM memory ops | `vm_run for SUB opcode` | Functional |
| 11 | L119 | test_ir_deref | IR pointer nodes | `ASSERT_NOT_NULL(d); ASSERT_EQ(d->type, NODE_DEREF)` | IR/Optimization |
| 12 | L129 | test_ir_addr_of | IR pointer nodes | `ASSERT_EQ(a->type, NODE_ADDR_OF)` | IR/Optimization |
| 13 | L139 | test_ir_assign | IR pointer nodes | `ASSERT_EQ(a->type, NODE_ASSIGN); ASSERT_EQ(a->right->val, 5)` | IR/Optimization |
| 14 | L151 | test_ir_var_decl | IR pointer nodes | `ASSERT_STR_EQ(d->name, "count"); ASSERT_EQ(d->left->val, 42)` | IR/Optimization |
| 15 | L164 | test_parse_var_decl | Parser pointer syntax | `ASSERT_EQ(prog->type, NODE_PROGRAM)` | Parsing |
| 16 | L176 | test_parse_addr_of | Parser pointer syntax | `ASSERT_EQ(fn->body->left->type, NODE_ADDR_OF)` | Parsing |
| 17 | L191 | test_parse_deref | Parser pointer syntax | `ASSERT_EQ(fn->body->left->type, NODE_DEREF)` | Parsing |
| 18 | L200 | test_parse_subtraction | Parser pointer syntax | `ASSERT_EQ(fn->body->left->op, OP_IR_SUB)` | Parsing |
| 19 | L211 | test_fold_subtraction | IR subtraction | `ASSERT_EQ(e->val, 7)` | IR/Optimization |

---

## Suite 59: Compiler: Parser Fuzz ⭐NEW

**Source**: `tools/compiler/tests/test_parser_fuzz.c`
**Runtime Assertions**: 0 (crash-absence tests)
**Source-Level Entries**: 5
**Harness**: `TEST(name) { /* no-crash */; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L42 | test_parser_random_input | Fuzz | 100 random inputs — parser must not crash | Fuzz/Robustness |
| 2 | L58 | test_parser_malformed_functions | Fuzz | 10 malformed function patterns — no crash | Fuzz/Robustness |
| 3 | L79 | test_parser_edge_cases | Fuzz | 12 edge-case strings — no crash | Fuzz/Robustness |
| 4 | L102 | test_parser_large_input | Fuzz | 50 variable declarations — no crash | Stress |
| 5 | L126 | test_parser_unicode_input | Fuzz | Unicode input — no crash | Fuzz/Robustness |

---

## Suite 60: Compiler: Performance Benchmarks ⭐NEW

**Source**: `tools/compiler/tests/test_performance.c`
**Runtime Assertions**: 4
**Source-Level Entries**: 4
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_NOT_NULL; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L14 | test_trit_arithmetic_perf | Trit arithmetic | `ASSERT_EQ(result, TRIT_Z)` (100k iterations) | Performance |
| 2 | L32 | test_trit_word_perf | Trit word ops | `ASSERT_EQ(trit_word_to_int(check), final_val)` (50k iterations) | Performance |
| 3 | L53 | test_parser_perf | Parser | `ASSERT_NOT_NULL(ast)` (1000 iterations) | Performance |
| 4 | L67 | test_scaling_perf | Scaling | `ASSERT_EQ(trit_word_to_int(words[size-2]), expected)` | Performance |

---

## Suite 61: Compiler: seL4 Stubs ⭐NEW

**Source**: `tools/compiler/tests/test_sel4.c`
**Runtime Assertions**: 15
**Source-Level Entries**: 4
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_NOT_NULL/ASSERT_STR_EQ; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L47 | test_sel4_cap_init | seL4 stubs | `ASSERT_NOT_NULL(prog); ASSERT_STR_EQ(fn->name, "init_cap")` | seL4/Verification |
| 2 | L65 | test_sel4_compile_simple | seL4 stubs | `ASSERT_STR_EQ(sel4_out, "Result: 1\n")` | seL4/Verification |
| 3 | L73 | test_sel4_multi_cap | seL4 stubs | `ASSERT_EQ(prog->param_count, 2); ASSERT_STR_EQ(prog->params[0]->name, "cap_a")` | seL4/Verification |
| 4 | L92 | test_sel4_cap_arithmetic | seL4 stubs | `ASSERT_STR_EQ(sel4_out, "Result: 30\n")` | seL4/Verification |

---

## Suite 62: Compiler: seL4 Verify (TASK-019) ⭐NEW

**Source**: `tools/compiler/tests/test_sel4_verify.c`
**Runtime Assertions**: 51
**Source-Level Entries**: 18
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_NOT_NULL/ASSERT_NULL/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L14 | test_cap_tree_create | Capability tree | `ASSERT_NOT_NULL(root); ASSERT_EQ(root->cap.object_id, 1)` | Access control |
| 2 | L24 | test_cap_derive_single | Capability tree | `ASSERT_EQ(child->cap.rights, CAP_RIGHT_READ)` | Access control |
| 3 | L35 | test_cap_derive_ternary_branching | Capability tree | `ASSERT_EQ(root->child_count, 3); ASSERT_NULL(c4)` | Boundary |
| 4 | L50 | test_cap_no_escalation | Capability tree | `ASSERT_TRUE(verify_no_escalation(root))` | Access control |
| 5 | L58 | test_cap_revoke_tree | Capability tree | `ASSERT_EQ(c1->cap.rights, 0); ASSERT_TRUE(verify_revocation(c1))` | Access control |
| 6 | L77 | test_cap_tree_count | Capability tree | `ASSERT_EQ(cap_tree_count(root), 4)` | Functional |
| 7 | L88 | test_endpoint_init | Endpoints | `ASSERT_EQ(ep.ep_id, 42); ASSERT_EQ(ep.msg_count, 0)` | IPC |
| 8 | L96 | test_endpoint_send_recv | Endpoints | `ASSERT_EQ(endpoint_send/recv)` | IPC |
| 9 | L111 | test_endpoint_full | Endpoints | `ASSERT_EQ(endpoint_send(&ep, 99), -1)` | Boundary |
| 10 | L121 | test_endpoint_empty | Endpoints | `ASSERT_EQ(endpoint_recv(&ep, &msg), -1)` | Boundary |
| 11 | L131 | test_tcb_init | Thread control | `ASSERT_EQ(tcb.tid, 1); ASSERT_EQ(tcb.priority, 0)` | Scheduling |
| 12 | L141 | test_tcb_multiple | Thread control | `ASSERT_EQ(threads[0].tid, 0)` | Scheduling |
| 13 | L153 | test_sel4_compile_simple_expr | Compile pipeline | `ASSERT_TRUE(len > 0)` | Integration |
| 14 | L163 | test_sel4_compile_cap_arithmetic | Compile pipeline | `ASSERT_TRUE(len > 0)` | Integration |
| 15 | L172 | test_sel4_compile_mul_chain | Compile pipeline | `ASSERT_TRUE(len > 0)` | Integration |
| 16 | L183 | test_verify_escalation_holds | Verification | `ASSERT_TRUE(verify_no_escalation(root))` | seL4/Verification |
| 17 | L191 | test_verify_revocation_holds | Verification | `ASSERT_TRUE(verify_revocation(root))` | seL4/Verification |
| 18 | L201 | test_verify_full_tree | Verification | `ASSERT_EQ(cap_tree_count(root), 6); ASSERT_TRUE(verify_no_escalation)` | seL4/Verification |

---

## Suite 63: Compiler: seT5 Syscalls (TASK-016) ⭐NEW

**Source**: `tools/compiler/tests/test_set5.c`
**Runtime Assertions**: 23
**Source-Level Entries**: 13
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L14 | test_syscall_exit | VM syscall dispatch | `ASSERT_TRUE(1)` (SYS_EXIT) | Functional |
| 2 | L26 | test_syscall_write | VM syscall dispatch | `ASSERT_EQ(vm_get_result(), 5)` | Functional |
| 3 | L42 | test_syscall_read | VM syscall dispatch | `ASSERT_EQ(vm_get_result(), 0)` | Functional |
| 4 | L57 | test_syscall_mmap | VM syscall dispatch | `ASSERT_EQ(vm_get_result(), 364)` | Memory |
| 5 | L70 | test_syscall_cap_send | VM syscall dispatch | `ASSERT_EQ(vm_get_result(), 0)` | IPC |
| 6 | L84 | test_syscall_cap_recv | VM syscall dispatch | `ASSERT_EQ(vm_get_result(), 42)` | IPC |
| 7 | L97 | test_syscall_unknown | VM syscall dispatch | `ASSERT_EQ(vm_get_result(), -1)` | Negative/error |
| 8 | L111 | test_cap_grant_restricts_rights | Capability API | `ASSERT_EQ(dest.rights, CAP_RIGHT_READ)` | Access control |
| 9 | L120 | test_cap_grant_no_escalation | Capability API | `ASSERT_EQ(dest.rights, CAP_RIGHT_READ)` | Access control |
| 10 | L128 | test_cap_revoke | Capability API | `ASSERT_EQ(cap.rights, 0)` | Access control |
| 11 | L135 | test_cap_rights_bitmask_encoding | Capability API | `ASSERT_EQ(CAP_RIGHT_READ, 1); ASSERT_EQ(CAP_RIGHT_ALL, 7)` | Encoding |
| 12 | L143 | test_cap_obj_types | Capability API | `ASSERT_EQ(OBJ_ENDPOINT, 0); ASSERT_EQ(OBJ_CNODE, 4)` | Encoding |
| 13 | L153 | test_store_then_write_syscall | Combined | `ASSERT_EQ(vm_memory_read(50), 65)` | Integration |

---

## Suite 64: Compiler: Ternary Arithmetic Comprehensive ⭐NEW

**Source**: `tools/compiler/tests/test_ternary_arithmetic_comprehensive.c`
**Runtime Assertions**: 32
**Source-Level Entries**: 5
**Harness**: `TEST(name) { ASSERT_EQ; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L7 | test_trit_overflow_scenarios | Overflow | `ASSERT_EQ(result, TRIT_N); ASSERT_EQ(carry, TRIT_P)` | Boundary |
| 2 | L31 | test_trit_multiplication_edge_cases | Multiplication | `ASSERT_EQ(trit_mul(P,P), P); ASSERT_EQ(trit_mul(Z,Z), Z)` | Arithmetic |
| 3 | L79 | test_balanced_ternary_mathematical_properties | Math properties | `trit_not, additive identity/inverse, multiplicative identity, annihilation` | Arithmetic |
| 4 | L115 | test_ternary_arithmetic_commutativity | Commutativity | `ASSERT_EQ(r1, r2); ASSERT_EQ(carry1, carry2)` | Arithmetic |
| 5 | L125 | test_ternary_arithmetic_associativity | Associativity | `ASSERT_EQ(result1, result2)` | Arithmetic |

---

## Suite 65: Compiler: Ternary Edge Cases ⭐NEW

**Source**: `tools/compiler/tests/test_ternary_edge_cases.c`
**Runtime Assertions**: 19
**Source-Level Entries**: 5
**Harness**: `TEST(name) { ASSERT_EQ; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L7 | test_trit_overflow | Overflow | `ASSERT_EQ(result, TRIT_N); ASSERT_EQ(carry, TRIT_P); ASSERT_EQ(trit_mul)` | Boundary |
| 2 | L32 | test_trit_underflow | Underflow | `ASSERT_EQ(result, TRIT_P); ASSERT_EQ(carry, TRIT_N)` | Boundary |
| 3 | L48 | test_precision_loss | Precision | `ASSERT_EQ(back, vals[i])` (loop: 7,13,19,31,43,100,−100,364,−364) | Arithmetic |
| 4 | L66 | test_extreme_values | Extreme values | `ASSERT_EQ(trit_add(t_max, t_zero, &c), t_max)` | Boundary |
| 5 | L83 | test_balanced_ternary_properties | Math properties | `ASSERT_EQ(sum, TRIT_Z)` | Arithmetic |

---

## Suite 66: Compiler: Trit Edge Cases ⭐NEW

**Source**: `tools/compiler/tests/test_trit_edge_cases.c`
**Runtime Assertions**: 13
**Source-Level Entries**: 10
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_NEQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 1 | L13 | test_trit_word_max_value | Extreme values | `ASSERT_EQ(trit_word_to_int(w), 9841)` | Boundary |
| 2 | L21 | test_trit_word_min_value | Extreme values | `ASSERT_EQ(trit_word_to_int(w), −9841)` | Boundary |
| 3 | L29 | test_trit_word_overflow | Overflow | `ASSERT_NEQ(result, max_val+1)` | Boundary |
| 4 | L41 | test_trit_word_underflow | Underflow | `ASSERT_NEQ(result, min_val-1)` | Boundary |
| 5 | L55 | test_trit_precision_loss | Precision | `ASSERT_EQ(back, vals[i])` (loop) | Arithmetic |
| 6 | L66 | test_trit_large_mul_precision | Multiplication | `ASSERT_EQ(trit_word_to_int(res), 100)` | Arithmetic |
| 7 | L76 | test_trit_add_carry_chain | Carry chain | `ASSERT_EQ(trit_word_to_int(res), 365)` | Arithmetic |
| 8 | L85 | test_trit_sub_carry_chain | Borrow chain | `ASSERT_EQ(trit_word_to_int(res), 364)` | Arithmetic |
| 9 | L95 | test_trit_zero_operations | Zero ops | `ASSERT_EQ(trit_word_to_int(res), 42)` | Boundary |
| 10 | L107 | test_trit_identity_operations | Identity | `ASSERT_EQ(trit_word_to_int(res), 42)` | Arithmetic |

---

## Disabled Suite: Compiler: Codegen Bugs ⚠️

**Source**: `tools/compiler/tests/test_compiler_code_generation_bugs.c`
**Status**: Commented out in `tools/compiler/Makefile` — 39 runtime assertions, 19 tests
**Reason**: Advanced codegen patterns (templates, lambdas, coroutines) not yet implemented

---

## Disabled Suite: Compiler: Error Recovery ⚠️

**Source**: `tools/compiler/tests/test_error_recovery.c`
**Status**: Commented out in `tools/compiler/Makefile` — 26 runtime assertions, 11 tests
**Reason**: Error recovery infrastructure pending implementation

---

## Disabled Suite: Compiler: Parser/Lexer Fuzz ⚠️

**Source**: `tools/compiler/tests/test_parser_lexer_fuzz.c`
**Status**: Commented out in `tools/compiler/Makefile` — 18 runtime assertions, 10 tests
**Reason**: Extended fuzz harness pending parser stabilization

---

## Rule: Future Test Documentation

## Suite 67: Compiler: Integration Tests

**Source**: `tools/compiler/tests/test_integration.c`
**Runtime Assertions**: 24
**Source-Level Entries**: 16
**Harness**: `TEST(name) { ASSERT_EQ/ASSERT_TRUE; PASS(); }` — function-level, abort on fail
**Output Reading**: Each test prints `[PASS] name` or `[FAIL] name (file:line)`. Final summary.

Brief: This suite exercises cross-component compiler integration (parser→IR→codegen→vm) and validates round-trip correctness for representative programs. Add new assertions to this section following the same table format used elsewhere.

## Suite 68: Compiler: Test Runner Script

**Source**: `tools/compiler/tests/test_all.sh`
**Runtime Assertions**: —
**Source-Level Entries**: —
**Harness**: Shell script (utility) — not a test harness; included for completeness in the glossary as the canonical compiler-suite runner.
**Note**: This script orchestrates building/running compiler test binaries and reporting summaries; changes to test invocation must be reflected here and in the Makefile.

**MANDATORY**: For every new test added to the seT5/seT6 project, the following
steps MUST be completed before the pull request / commit is considered valid:

### Step 1: Document in this glossary

Append a corresponding entry to this file (`TESTS_GLOSSARY_OF_ALL_TESTS.md`).

Each new entry must include:
1. **Suite assignment** — which suite the test belongs to (or create a new suite section)
2. **Line number** — source file line
3. **Test Description** — the assertion description string
4. **Section** — the logical grouping within the suite
5. **Assertion Expression** — the condition being checked
6. **Category** — use the category legend at top of this file

If creating a **new suite**, also:
- Add a row to the **Suite Index** table (with suite number, source path, runtime/source counts, status)
- Update the **TOTAL** rows at the bottom of the index table
- Update the header statistics (Total Runtime Assertions, Total Source-Level Entries, Test Suites count)

### Step 2: Register in the Makefile

For **seT5 kernel/module tests** (`tests/test_*.c`):
- Add a build rule target in `/Makefile` (e.g., `test_my_new_suite: tests/test_my_new_suite.c $(DEPS)`)
- Add the binary name to the `SET5_TEST_BINS` variable
- Add a `##BEGIN##` execution block in the `_run-test-suites` target
- Add the binary name to the `clean` target's `rm -f` list

For **compiler tests** (`tools/compiler/tests/test_*.c`):
- Add the binary name to `TEST_BINS` in `tools/compiler/Makefile`
- The master Makefile's `_run-test-suites` auto-discovers compiler test binaries

For **Python tests** (`tests/test_*.py`):
- Add a phony target in the Makefile (e.g., `test_my_python: tests/test_my_python.py`)
- Add a `##BEGIN##` execution block in `_run-test-suites`

### Step 3: Update run_all_tests.sh

Add the new suite to the `SET5_SUITES` variable in `run_all_tests.sh` so it is
included in the standalone test runner.

### Step 4: Verify with `make alltest`

Run `make alltest` (or equivalently `make test`) to confirm:
- The new test compiles without warnings
- The new test passes 100%
- The grand summary includes the new suite
- Zero regressions in all other suites

**Failure to complete ANY of these 4 steps is a blocking review issue.**

### Quick Reference: Where to update

| What | File | Section |
|------|------|---------|
| Test glossary | `seT6/TESTS_GLOSSARY_OF_ALL_TESTS.md` | Suite Index + new Suite section |
| Build rule | `Makefile` | New target + `SET5_TEST_BINS` + `_run-test-suites` + `clean` |
| Shell runner | `run_all_tests.sh` | `SET5_SUITES` variable |
| Compiler tests | `tools/compiler/Makefile` | `TEST_BINS` variable |

## Suite 69: Multi-Radix Unit

**Source**: `tests/test_multi_radix_unit.c`
**Runtime Assertions**: 3
**Source-Level Entries**: 3
**Harness**: `TEST(name) { ... ASSERT_EQ(a, b); PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (expected b)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 69 | L29 | radix3_add | Radix-3 Addition | `multi_radix_add(1, 1, RADIX3) == 2` | Arithmetic |
| 69 | L39 | radix4_add | Radix-4 Addition | `multi_radix_add(3, 1, RADIX4) == 4` | Arithmetic |
| 69 | L49 | fft_8point | 8-Point FFT | `multi_radix_fft(data, 8)` | Transformation |

---

## Suite 70: Ternary Wallace Tree

**Source**: `tests/test_ternary_wallace_tree.c`
**Runtime Assertions**: 2
**Source-Level Entries**: 2
**Harness**: `TEST(name) { ... ASSERT_EQ(a, b); PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (expected b)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 70 | L29 | multiply_basic | Basic Multiplication | `ternary_wallace_multiply(2, 3) == 6` | Arithmetic |
| 70 | L39 | multiply_zero | Zero Multiplication | `ternary_wallace_multiply(0, 5) == 0` | Arithmetic |

---

## Suite 71: Ternary Sense Amp

**Source**: `tests/test_ternary_sense_amp.c`
**Runtime Assertions**: 3
**Source-Level Entries**: 3
**Harness**: `TEST(name) { ... ASSERT_EQ(a, b); PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (expected b)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 71 | L29 | sense_low | Low Current Sensing | `ternary_sense_amp_read(5) == 0` | Hardware/ALU |
| 71 | L39 | sense_mid | Mid Current Sensing | `ternary_sense_amp_read(30) == 1` | Hardware/ALU |
| 71 | L49 | sense_high | High Current Sensing | `ternary_sense_amp_read(60) == 2` | Hardware/ALU |

---

## Suite 72: T-IPC Compressor

**Source**: `tests/test_tipc_compressor.c`
**Runtime Assertions**: 2
**Source-Level Entries**: 2
**Harness**: `TEST(name) { ... ASSERT_EQ(a, b); PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (expected b)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 72 | L29 | compress_decompress | Round-Trip Compression | `tipc_decompress(...) == original` | Encoding |
| 72 | L39 | all_zeros | All Zeros Compression | `tipc_compress([0,0,...]) == 9 bits` | Encoding |

---

## Suite 73: Samsung Correlator

**Source**: `tests/test_samsung_cn105745888a_correlator.c`
**Runtime Assertions**: 2
**Source-Level Entries**: 2
**Harness**: `TEST(name) { ... ASSERT_EQ(a, b); PASS(); }` — function-level, abort on fail
**Output Reading**: Each test: `[PASS] name` or `[FAIL] name (expected b)`. Final summary.

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 73 | L29 | correlate_identical | Identical Sequences | `samsung_correlate([1,2,0,1], [1,2,0,1]) == 3` | Arithmetic |
| 73 | L39 | correlate_orthogonal | Orthogonal Sequences | `samsung_correlate([1,1,1,1], [2,2,2,2]) == -4` | Arithmetic |

---

## Suite 74: Ternary Full Adder

**Source**: `tests/test_ternary_full_adder.c`
**Runtime Assertions**: 10
**Source-Level Entries**: 5
**Harness**: `TEST(name) { ... ASSERT_EQ(a, b, msg); }` — per-assertion pass/fail with final summary
**Output Reading**: Each assertion: `[PASS] name` or `[FAIL] name (expected b)`. Final: "=== Results: P passed, F failed ===".

| # | Line | Test Description | Section | Assertion / Expression | Category |
|---|------|-----------------|---------|----------------------|----------|
| 74 | L25 | TFA: 1 + 1 + 0 = 2, carry 0 | Basic Addition | `sum == 2` | Arithmetic |
| 74 | L26 | TFA: 1 + 1 + 0 = 2, carry 0 | Basic Addition | `cout == 0` | Arithmetic |
| 74 | L30 | TFA: 1 + 1 + 1 = 0, carry 1 | Carry Propagation | `sum == 0` | Arithmetic |
| 74 | L31 | TFA: 1 + 1 + 1 = 0, carry 1 | Carry Propagation | `cout == 1` | Arithmetic |
| 74 | L35 | TFA: 2 + 2 + 2 = 0, carry 2 | Max Values | `sum == 0` | Boundary |
| 74 | L36 | TFA: 2 + 2 + 2 = 0, carry 2 | Max Values | `cout == 2` | Boundary |
| 74 | L40 | TFA: 0 + 0 + 0 = 0, carry 0 | Zero Addition | `sum == 0` | Arithmetic |
| 74 | L41 | TFA: 0 + 0 + 0 = 0, carry 0 | Zero Addition | `cout == 0` | Arithmetic |
| 74 | L45 | TFA: 2 + 1 + 0 = 0, carry 1 | Mixed Values | `sum == 0` | Arithmetic |
| 74 | L46 | TFA: 2 + 1 + 0 = 0, carry 1 | Mixed Values | `cout == 1` | Arithmetic |


---

## Suite 99 — Mixed-Radix Bos Thesis Enhancements (Tests 6702–6751)

**Source**: `tests/test_mixed_radix_bos.c` | **Assertions**: 50 | **Sigma 9**: ✅ ALL PASS

**Purpose**: Verifies in C the key properties from Steven Bos, "Mixed-Radix Circuit
Synthesis" (PhD thesis, TU Eindhoven, 2024). Exercises four new header APIs:
`trit_mrcs.h`, `trit_qdr.h`, `trit_rebel2.h`, `trit_rram.h`.

**New Isabelle Theories**: `proof/TritMRCS.thy` (mrcs_synthesis_sound, mrcs_bet_kleene_equiv),
`proof/TritQDR.thy` (qdr_edge_soundness, qdr_power_reduction_75pct, qdr_no_fault_output).
**Extended**: `LatticeCrypto.thy` (rebel2_isa_ternary_error_full), `TCAMSearch.thy`
(tcam_heptavintimal_soundness). No `sorry` stubs.

| Section | Tests | Headers Exercised | Isabelle Coverage |
|---------|------:|-------------------|-------------------|
| A: MRCS BET Encoding | 10 (6702–6711) | `trit_mrcs.h` | `TritMRCS.thy` §mrcs_bet_kleene_equiv |
| B: QDR Flip-Flop | 10 (6712–6721) | `trit_qdr.h` | `TritQDR.thy` §qdr_edge_soundness |
| C: REBEL-2 ISA | 10 (6722–6731) | `trit_rebel2.h` | `LatticeCrypto.thy` §rebel2_isa |
| D: Heptavintimal Gates | 10 (6732–6741) | `trit_mrcs.h` | `TCAMSearch.thy` §tcam_heptavintimal |
| E: Integration | 10 (6742–6751) | All four headers | All four theories |

**Key properties verified:**
- BET encode/decode/pack32/unpack32 roundtrip lossless for all {-1, 0, +1} trits
- QDR: exactly 4 active clock edges (RISE_POS, FALL_POS, FALL_NEG, RISE_NEG)
- QDR power model ≤ 25% of SDR baseline (75% CTN power reduction, Bos Fig. G.15)
- REBEL-2 radix LUT: binary {0..15} ↔ balanced ternary, integer value correct
- REBEL-2 RSET/RMOV/HALT ISA instructions execute correctly
- RRAM HRS/MRS/LRS ↔ FALSE/UNKNOWN/TRUE conversion exact
- RRAM write_cycles tracked; endurance degradation model (200 cycles)
- Heptavintimal gate names: SUM(7PB), CONS(RDC), MIN(PC0), MAX(ZRP), MLE(H51),
  NTI(2), BUF(K), INC(7), DEC(B) all correct; unknown index → "UNKNOWN"
- Sigma 9 integration: BET+QDR+REBEL-2+RRAM all properties hold simultaneously

---

### Current Totals (as of 2026-02-19)

| Metric | Active | Including Disabled |
|--------|-------:|-------------------:|
| **Test Suites** | **70** | **74** |
| **Runtime Assertions** | **5037** | **5120** |
| **Source-Level Entries** | **4692** | **4732** |
| **Test Source Files** | **75** | **78** |

---

## Suite 75 (Batch 99): Kleene K₃ Unknown Propagation

**Source**: `tests/test_batch_5702_5751.c`
**Tests**: 5702–5751 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary
**Output**: `=== Results: P/50 passed, F failed ===`

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5702–5720 | L80–L210 | AND/OR/NOT truth tables | Full K₃ table verification | Logic |
| 5721–5730 | L215–L290 | De Morgan laws | `¬(A∧B)=¬A∨¬B` with Unknown | Logic |
| 5731–5740 | L295–L365 | Distributivity | Unknown through and/or nesting | Logic |
| 5741–5751 | L370–L440 | Chain propagation | Unknown dominance in long chains | Logic |

---

## Suite 76 (Batch 100): Multi-Radix Neural Inference

**Source**: `tests/test_batch_5752_5801.c`
**Tests**: 5752–5801 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5752–5765 | L80–L180 | Balanced ternary round-trips | `int_to_bt / bt_to_int` identity | Encoding |
| 5766–5780 | L185–L280 | BitNet quantization | -1/0/+1 quantisation steps | Neural |
| 5781–5790 | L285–L355 | RNS/CRT | Residue number system mod-3 | Arithmetic |
| 5791–5801 | L360–L430 | Neural inference | Trit-weight dot products | Neural |

---

## Suite 77 (Batch 101): Unknown-Safe IPC

**Source**: `tests/test_batch_5802_5851.c`
**Tests**: 5802–5851 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5802–5815 | L80–L180 | Message validity | Unknown validity propagation | IPC |
| 5816–5830 | L185–L285 | AND/OR reduce | Kleene reduce over payload arrays | IPC |
| 5831–5840 | L290–L360 | Round-trip | Build+validate message cycle | IPC |
| 5841–5851 | L365–L435 | Edge cases | Empty, max-len, all-Unknown payloads | IPC |

---

## Suite 78 (Batch 102): Curiosity Simulation

**Source**: `tests/test_batch_5852_5901.c`
**Tests**: 5852–5901 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5852–5865 | L80–L180 | Flip cycle | U→T→F→U 3-step ternary flip | AI |
| 5866–5880 | L185–L285 | State array | `curiosity_t` multi-slot exploration | AI |
| 5881–5890 | L290–L360 | Reversibility | Flip ×3 returns to start | AI |
| 5891–5901 | L365–L435 | Saturation | All-True / all-False boundary | AI |

---

## Suite 79 (Batch 103): Eudaimonic Scheduling

**Source**: `tests/test_batch_5902_5951.c`
**Tests**: 5902–5951 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5902–5915 | L80–L180 | Priority selection | `sched_select` by trit priority | Scheduling |
| 5916–5930 | L185–L290 | Eudaimonic count | `sched_count_eudaimonic` over queues | Scheduling |
| 5931–5940 | L295–L360 | Mixed priorities | False/Unknown/True priority ordering | Scheduling |
| 5941–5951 | L365–L435 | Boundary | Empty queue, all-same-priority | Scheduling |

---

## Suite 80 (Batch 104): Fault-Tolerant Reversion Guards

**Source**: `tests/test_batch_5952_6001.c`
**Tests**: 5952–6001 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Milestone**: test_6000 — "Checkpoint revert after multi-bit corruption restores all 8 trits exactly"
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5952–5965 | L80–L185 | Save/restore | `checkpoint_save / checkpoint_revert` | Fault-tolerance |
| 5966–5980 | L190–L290 | Corruption detection | `checkpoint_corrupt` + revert cycle | Fault-tolerance |
| 5981–5990 | L295–L360 | Multi-checkpoint | Sequential save/corrupt/revert | Fault-tolerance |
| 5991–6001 | L365–L440 | Edge / milestone | Boundary + test_6000 milestone | Fault-tolerance |

---

## Suite 81 (Batch 105): Symbiotic AI-Human Interface

**Source**: `tests/test_batch_6002_6051.c`
**Tests**: 6002–6051 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6002–6015 | L80–L180 | Basic resolution | `symbiotic_resolve(ai, human)` all 9 pairs | AI-Human |
| 6016–6030 | L185–L285 | Human override | True/False authoritative; Unknown defers | AI-Human |
| 6031–6040 | L290–L360 | Convergence | Multi-round chains stabilise | AI-Human |
| 6041–6051 | L365–L435 | Veto & audit | Veto propagation; auditability | AI-Human |

---

## Suite 82 (Batch 106): Ternary Cryptographic Uncertainty

**Source**: `tests/test_batch_6052_6101.c`
**Tests**: 6052–6101 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6052–6065 | L90–L185 | Commit-reveal | `commit_create / commit_reveal / commit_verify` | Crypto |
| 6066–6080 | L190–L290 | Hash properties | `trit_hash3` distinctness, sensitivity | Crypto |
| 6081–6090 | L295–L360 | Chain commits | Sequential commitment chains | Crypto |
| 6091–6101 | L365–L435 | Struct/edge | Size bounds, signature space, cycles | Crypto |

---

## Suite 83 (Batch 107): PAM3/Multi-Radix Interconnect

**Source**: `tests/test_batch_6102_6151.c`
**Tests**: 6102–6151 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6102–6115 | L80–L180 | PAM3 encode/decode | `pam3_encode(trit)→int` round-trips | Interconnect |
| 6116–6130 | L185–L285 | 4B3T | `encode_4b3t` symbol mapping | Encoding |
| 6131–6140 | L290–L355 | Exhaustive symbols | All valid 4B3T symbols | Encoding |
| 6141–6151 | L360–L430 | Edge | Boundary trits, invalid guard | Interconnect |

---

## Suite 84 (Batch 108): Gödel Machine Self-Reference

**Source**: `tests/test_batch_6152_6201.c`
**Tests**: 6152–6201 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Milestone**: test_6201 — "seT6 Corner 3 Pledge: Gödel machine rejects self-mod without proof, accepts with proof — civilisational alignment"
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6152–6165 | L80–L180 | Init & state | `gm_init / gm_verify` baseline | Self-reference |
| 6166–6180 | L185–L285 | Proof-gated mod | `gm_self_modify` blocked without proof | Self-reference |
| 6181–6190 | L290–L360 | Accepted mod | Modification accepted when proof=True | Self-reference |
| 6191–6201 | L365–L440 | Milestone | Corner 3 pledge test_6201 | Alignment |

---

## Suite 85: Symbiotic AI Module

**Source**: `tests/test_symbiotic_ai.c`
**Tests**: 50 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Module Under Test**: `src/symbiotic_ai.c` (`include/set5/symbiotic_ai.h`)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Section | Coverage | Category |
|---|---------|----------|----------|
| 1–14 | CuriosityProbe | `trit_curiosity_probe`: ≥50% Unknown→True, any→Unknown, none→False | AI |
| 15–28 | BeautySymmetry | `trit_beauty_symmetry`: palindrome check with Unknown-tolerance | AI |
| 29–43 | EudaimWeight | `trit_eudaimonic_weight(effort, engagement, impact)`: eudaimonic scoring | AI |
| 44–50 | Integration | Cross-function interaction; Corner 3 combined behaviour | AI-Human |

---

## Suite 86: Symbiotic Curiosity Prover

**Source**: `tests/test_symbiotic_curiosity.c`
**Runtime Assertions**: 52 | **Status**: ✅ Sigma 9 (52/52)
**Module Under Test**: `src/symbiotic_ai.c` — `CuriosityProver`, `prove_curiosity`, `explore_hypothesis`
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| CuriosityProver: cp_init | Zero-state initialisation; level=Unknown | AI |
| prove_curiosity: Unknown input escalation | Unknown→True after threshold | AI |
| prove_curiosity: Known True/False input | Known inputs are preserved | AI |
| explore_hypothesis: resolution | Hypothesis slots resolved honestly | AI |
| explore_hypothesis: idempotent/no-side-effects | Repeat calls stable | AI |
| Integration: trit_curiosity_probe | `trit_curiosity_probe` linking | AI |
| RSI gradient | Level stays in {U,T}; cannot exceed True | AI |
| Edge cases / Re-init idempotency | Boundary and re-initialisation safety | AI |

---

## Suite 87: Symbiotic Beauty Appreciator

**Source**: `tests/test_symbiotic_beauty.c`
**Runtime Assertions**: 40 | **Status**: ✅ Sigma 9 (40/40)
**Module Under Test**: `src/symbiotic_ai.c` — `BeautyAppreciator`, `appreciate_beauty`, `trit_beauty_symmetry`
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| BeautyAppreciator: ba_init | Zero-state; score=Unknown | AI |
| appreciate_beauty: True — perfect palindrome | Even/odd palindromes → True | AI |
| appreciate_beauty: False — asymmetric | Asymmetric vectors → False | AI |
| appreciate_beauty: Unknown — partial symmetry | UNKNOWN pairs → Unknown | AI |
| Pure trit_beauty_symmetry | Underlying function exhaustive | AI |
| Lattice copy / length boundary | Struct copy safety; boundary lengths | AI |
| Re-init & repeated use | Idempotency after re-init | AI |
| Result range invariant | Output always in {-1,0,+1} | AI |

---

## Suite 88: Symbiotic Eudaimonic Optimizer

**Source**: `tests/test_symbiotic_eudaimonia.c`
**Runtime Assertions**: 52 | **Status**: ✅ Sigma 9 (52/52)
**Module Under Test**: `src/symbiotic_ai.c` — `EudaimonicOptimizer`, `optimize_eudaimonia`, `trit_eudaimonic_weight`
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| EudaimonicOptimizer: eo_init | Zero-state initialisation | AI |
| optimize_eudaimonia: human True override | Human True is authoritative | AI-Human |
| optimize_eudaimonia: human False veto | Human False vetoes flourishing | AI-Human |
| optimize_eudaimonia: human Unknown defers to AI | AI fills epistemic gap | AI-Human |
| trit_eudaimonic_weight: all True | Perfect flourishing = True | AI |
| trit_eudaimonic_weight: any False disqualifies | False dominates weight | AI |
| trit_eudaimonic_weight: Unknown paths | Partial knowledge → Unknown | AI |
| Corner: curiosity/beauty False/Unknown | Each component gates flourishing | AI |
| 9-pair truth table | All (level, score) combos for weight | AI |
| RSI flywheel: multi-round convergence | Multi-round stability | AI |
| Cross-module integration / Scaling | Full stack integration test | AI |

---

## Suite 89: Red-Team Trit Range Integrity

**Source**: `tests/test_red_team_trit_range.c`
**Tests**: 6202–6251 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Adversarial verification that every trit operation stays within {-1,0,+1}; no out-of-range value can propagate.
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| TRIT_RANGE_CHECK macro | Macro rejects out-of-range values | Red-Team |
| pack/unpack round-trip | `trit_pack / trit_unpack` lossless | Red-Team |
| Kleene operators | AND/OR/NOT/IMPLIES/EQUIV stay in range | Red-Team |
| Clamp bridge | Binary→ternary clamp never escapes range | Red-Team |
| NOT chains (100/1000 deep) | Deep chaining stays in range | Red-Team |
| Packed64 extraction | All 32 slots extract to valid trits | Red-Team |
| RUNTIME_VALIDATE | Runtime invariant assertion | Red-Team |
| Absorptive properties | a AND FALSE = FALSE; a OR TRUE = TRUE | Red-Team |
| Predicates | `trit_is_true / trit_is_false / trit_is_unknown` | Red-Team |

---

## Suite 90: Red-Team Binary Reversion Attack

**Source**: `tests/test_red_team_binary_reversion.c`
**Tests**: 6252–6301 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Verify the ternary system never collapses to binary {0,1}; UNKNOWN propagates correctly and cannot be silently promoted.
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| UNKNOWN propagation | UNKNOWN propagates through AND/OR chains | Red-Team |
| Binary reversion guard | All 9 (a,b) combos; no collapse to {0,1} | Red-Team |
| NOT chains | NOT(NOT(U)) = U; deep chaining stable | Red-Team |
| IMPLIES/EQUIV | U→F=U; equiv(U,U)=U; Kleene K3 correct | Red-Team |
| Pack/unpack with U | UNKNOWN survives pack/unpack cycle | Red-Team |
| Mixed-value arrays | Bulk operations preserve all 3 values | Red-Team |

---

## Suite 91: Red-Team Packed64 SIMD Adversarial

**Source**: `tests/test_red_team_simd.c`
**Tests**: 6302–6351 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Adversarial attack on the packed-64 SIMD substrate; inject fault (0b11) patterns, verify range invariants and document real attack vectors.
**Attack Finding**: fault-encoding `0b11` OR FALSE `0b10` = TRUE `0b01` — lo-bit of fault survives the OR formula (attack vector documented, not suppressed).
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| Fault injection | 0b11 fault patterns injected into packed words | Red-Team |
| Fault OR attack | Documents: fault OR FALSE = TRUE (lo-bit attack) | Security |
| Range after ops | Valid-trit words stay in range after ops | Red-Team |
| Distributivity (valid trits only) | AND/OR distributivity holds for {0b00,0b01,0b10} words | Red-Team |
| Packed64 slot extraction | All 32 slots round-trip correctly | Red-Team |
| Bulk SIMD stress | 1M-op bulk packed-word stress | Performance |

---

## Suite 92: Red-Team Cryptographic Hardening

**Source**: `tests/test_red_team_crypto.c`
**Tests**: 6352–6401 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Self-contained GF(3) LFSR degree-4 cryptographic hardening; distribution, period, sensitivity, and Kleene correctness under adversarial conditions.
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| GF(3) LFSR init & step | Degree-4 LFSR in GF(3) with `mod3_bal()` | Crypto |
| Distribution (10000 steps) | All 3 values appear; no bias collapse | Crypto |
| Period / seed sensitivity | Different seeds → different streams | Crypto |
| Kleene K3 correctness | `equiv(F,F)=T, equiv(U,U)=U, equiv(T,T)=T` | Crypto |
| Uncertainty propagation | UNKNOWN in LFSR stays as U; doesn't promote | Crypto |
| Commit-reveal adversarial | Hash sensitivity; tamper detection | Crypto |

---

## Suite 93: Red-Team Symbiotic AI Adversarial

**Source**: `tests/test_red_team_symbiotic.c`
**Tests**: 6402–6451 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Adversarial corner cases for CuriosityProver, BeautyAppreciator, and EudaimonicOptimizer; boundary inputs designed to expose covert binary collapse.
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| CuriosityProver adversarial | All-False / all-Unknown / all-True edge inputs | Red-Team |
| beauty_symmetry adversarial | `{T,U,U,T}` → UNKNOWN (not TRUE); asymmetric → FALSE | Red-Team |
| optimize_eudaimonia adversarial | `optimize(U,T)` = UNKNOWN when cp/ba uninitialised | Red-Team |
| Human-override injection | False veto wins over internal flourishing | AI-Human |
| Range invariants | All outputs stay in {-1,0,+1} under adversarial inputs | Red-Team |
| RSI loop adversarial | Multi-round adversarial exploration chains | AI |

---

## Suite 94: Red-Team Gödel Machine Invariants

**Source**: `tests/test_red_team_godel.c`
**Tests**: 6452–6501 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Attack the Gödel machine proof-gate, utility monotonicity, rollback, decomposability, and transitivity using adversarial trit inputs.
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| Proof-gate invariant | Self-modify rejected without proof | Self-reference |
| Utility monotonicity | Utility never decreases by accepted modification | Self-reference |
| Rollback | State restored correctly after rejection | Self-reference |
| Kleene K3 proof logic | `equiv(U,U)=U`; `U→F=U`, `U→U=U` (not Łukasiewicz) | Self-reference |
| Decomposability | Proof gate: compound proof = all sub-proofs pass | Self-reference |
| Transitivity | `proof(a,b) AND proof(b,c) → proof(a,c)` | Self-reference |
| Adversarial inputs | All boundary and UNKNOWN proof values tested | Red-Team |

---

## Suite 95: Red-Team Type Confusion & Integer Safety

**Source**: `tests/test_red_team_type.c`
**Tests**: 6502–6551 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Force type confusion, int8_t boundary violations, implicit integer promotion, and casting errors; verify trit API is immune.
**Note**: `trit_get_packed64` / `trit_set_packed64` defined as inline helpers (not in public API).
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| int8_t boundaries | Values ±127 clamped/rejected; no overflow | Type-Safety |
| Implicit promotion | `int`-promoted operations still produce valid trits | Type-Safety |
| Cast injection | `(trit)(int)` cast chain stays in {-1,0,+1} | Type-Safety |
| Packed64 type safety | Slot get/set with inline helpers; no aliasing | Type-Safety |
| Struct size invariant | `sizeof(trit)` = 1; no padding surprise | Type-Safety |
| Array bulk type | 64-element trit array: no spill into adjacent memory | Type-Safety |

---

## Suite 96: Red-Team Deep Chain Stress

**Source**: `tests/test_red_team_deep.c`
**Tests**: 6552–6601 | **Runtime Assertions**: 52 | **Status**: ✅ Sigma 9 (52/52)
**Purpose**: 256-deep operation chains, 1024-element bulk arrays, RSI flywheel 512-cycle stress, and 50 000-operation random-walk stress test.
**Note**: Walk orbit assertion changed to range-invariant only (orbit may converge to limit cycle).
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Category |
|---------|----------|----------|
| 256-deep NOT chain | NOT^256(x) = x; no drift | Stress |
| 256-deep AND chain | Deep AND chain terminates in FALSE correctly | Stress |
| 256-deep OR chain | Deep OR chain terminates in TRUE correctly | Stress |
| 1024-array bulk ops | 1024-element array: all results in range | Stress |
| RSI flywheel 512 cycles | 512 curiosity-probe rounds; range stable | Stress |
| 50000-op random walk | Random trit ops: all outputs in {-1,0,+1} | Stress |
| Packed64 deep stress | 32-slot packed word: deep get/set cycles | Stress |

---

## Suite 97: Red-Team Packed64 Fault-Hardening Verification

**Source**: `tests/test_red_team_packed_hardened.c`
**Tests**: 6602–6651 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Directly verify the T-SEC fault-hardening mitigations added to `include/set5/trit.h` in response to the Suite 91 attack finding: packed64 fault-encoding `0b11 OR FALSE = TRUE`.
**Proof**: `proof/PackedFaultSemantics.thy` — machine-checked Isabelle proofs of attack theorem and hardening correctness.
**New API under test**: `has_fault_packed64`, `trit_sanitize_packed64`, `trit_or_packed64_hardened`, `trit_and_packed64_hardened`, `trit_not_packed64_hardened`, `TRIT_PACKED_VALID`
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| Section | Coverage | Key Assertions | Category |
|---------|----------|----------------|----------|
| A: Fault Detection | `has_fault_packed64` and `TRIT_PACKED_VALID` | All-fault/valid/single-slot detection; macro correctness | Security |
| B: Sanitization | `trit_sanitize_packed64` | fault→UNKNOWN; valid preserved; idempotent; range invariant | Security |
| C: Hardened OR | `trit_or_packed64_hardened` | Attack blocked: fault+FALSE=UNKNOWN not TRUE; 4×4 range; valid==plain | Security |
| D: Hardened AND | `trit_and_packed64_hardened` | No fault output; De Morgan; valid==plain; 4×4 range | Security |
| E: Hardened NOT + Integration | `trit_not_packed64_hardened` + combined | Double-NOT identity; De Morgan; sanitize+plain==hardened; Sigma 9 summary | Security |

**Attack blocked** (test_6622 control assertion + main assertion):
```
trit_or_packed64(0xFFFF…, 0xAAAA…)           = 0x5555… = all-TRUE  ← attack
trit_or_packed64_hardened(0xFFFF…, 0xAAAA…)  = 0x0000… = all-UNKNOWN  ← blocked
```

---

## Suite 98: Formal-Verification-Driven Ternary Improvements

**Source**: `tests/test_ternary_formal_suite.c`
**Tests**: 6652–6701 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 9 (50/50)
**Purpose**: Translate research-proven improvements from three new Isabelle theories into
verified C tests: Symbolic Ternary Trajectory Evaluation (STE), Triple Modular Redundancy
(TMR), and Abstract Interpretation with widening/narrowing.
**New theories**: `proof/TritSTE.thy`, `proof/TritTMR.thy`, `proof/TritAbsInterp.thy`
**Fixed sorry stubs**: `proof/LatticeCrypto.thy` (ternary_error_full), `proof/TCAMSearch.thy` (tcam_search_first)
**New C API**: `include/set5/trit_tmr.h` — `trit_tmr_vote3`, `trit_tmr_vote_packed64`, `trit_tmr_run`, `trit_tmr_divergence_packed64`

| Section | Coverage | Key Assertions | Formal Basis |
|---------|----------|----------------|--------------|
| A: Scalar TMR | `trit_tmr_vote3`, `trit_tmr_agree` | Idempotence, single-fault masking, TMR-7 symmetry | `TritTMR.thy` §TMR-2,6,7 |
| B: Packed-64 TMR | `trit_tmr_vote_packed64`, `TRIT_PACKED_VALID` | No-fault-output, fault recovery, divergence detection | `TritTMR.thy` §TMR-4,5 |
| C: STE Guard | Kleene AND/OR properties | Unk containment, guard transparency, STE monotonicity | `TritSTE.thy` §STE-1,2,4,6 |
| D: Abstract Interp | Lattice boundary ops | AI-6 Unk boundary, AI-7 widening ≥ prev, AI-8 conservative safety | `TritAbsInterp.thy` §AI-3,6,7,8 |
| E: Garner CRT + Integration | Multi-radix RNS, combined pipeline | CRT roundtrip, carry-free RNS, T-SEC+TMR+STE+AI simultaneously | `TritAbsInterp.thy` + RNS |

**Key improvements delivered this session:**
- 3 new Isabelle theories (0 `sorry`): **TritSTE** (10 theorems), **TritTMR** (20 theorems), **TritAbsInterp** (12 theorems)
- 2 sorry stubs fixed: `LatticeCrypto.thy::ternary_error_full`, `TCAMSearch.thy::tcam_search_first`
- 1 new C header: `trit_tmr.h` with packed64 TMR voting (proof: no 0b11 output slot possible)
- TMR security theorem: fault `0b11` sanitized to `0b00` before vote; single-fault recovery guaranteed

---

### Current Totals (as of 2026-02-20, Sigma 11 Complete)

| Metric | Active | Including Disabled |
|--------|-------:|-------------------:|
| **Test Suites** | **101** | **104** |
| **Runtime Assertions** | **6603** | **6636** |
| **Source-Level Entries** | **6208** | **6248** |
| **Test Source Files** | **107** | **109** |

> **Corner 3 Milestone**: Batches 99–108 (500 assertions, tests 5702–6201) added.
> test_6201 marks the seT6 Gödel Machine civilisational-alignment pledge.
>
> **Red-Team Batch (Suites 86–96, 596 assertions)**: 11 adversarial suites — trit range,
> binary reversion, SIMD packed64 fault injection, GF(3) LFSR crypto, symbiotic AI,
> Gödel proof-gate, type confusion, integer safety, deep chain stress. All Sigma 9.
>
> **Fault-Hardening (Suite 97, 50 assertions)**: T-SEC mitigations verified — `has_fault_packed64`,
> `trit_sanitize_packed64`, and three hardened SIMD ops. Attack vector (Suite 91 / test_6304)
> confirmed in control assertion and blocked in hardened path. `proof/PackedFaultSemantics.thy`
> contains machine-checkable Isabelle proofs of every key property.
> Attack finding: packed64 fault `0b11` OR FALSE `0b10` = TRUE `0b01` (lo-bit survives OR formula).
> Mitigation: sanitize fault→UNKNOWN before any OR — provably blocks masquerade.
>
> **Formal-Verification Suite (Suite 98, 50 assertions)**: STE + TMR + Abstract Interpretation
> improvements derived from formal verification research. Three new Isabelle theories with zero
> `sorry` stubs. Two existing `sorry` stubs eliminated (LatticeCrypto, TCAMSearch). New `trit_tmr.h`
> API with proved no-fault-output property. Garner/CRT multi-radix reconstruction verified in C.
>
> **Sigma 10 Batches (109–114, 300 assertions)**: RSI Flywheel Safety, Curiosity Gradient,
> Beauty Symmetry, Eudaimonic Optimization, Balanced Ternary Arithmetic, Mixed-Radix Packed64 SIMD.
>
> **Sigma 11 Batches (115–119, 250 assertions)**: Heptavint Multi-Radix Encoding, Ternary
> Floating-Point Basics, GF(3) Hamming Error Correction, Capability Access Control, State Machine
> & Protocol Verification.
>
> **Early Batches Wired (92–98, 350 assertions)**: Hardware ALU/TALU, Side-Channel Resistance
> (basic + advanced), Epistemic Logic & Hesitation (basic + advanced), Guardian Trit Mechanisms
> (basic + advanced). All 10 ALU assertion mismatches fixed (carry init corrections).

---

## Suite 100 (Batch 92): Hardware ALU/TALU Operations

**Source**: `tests/test_batch_5352_5401.c`
**Tests**: 5352–5401 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(name) / ASSERT_EQ / ASSERT_TRUE / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5352–5365 | L20–L150 | Basic ALU add/sub/mul/div | Core arithmetic operations | Arithmetic |
| 5366–5375 | L155–L280 | Carry/overflow/underflow | Carry propagation, overflow detection | Boundary |
| 5376–5385 | L285–L420 | Shift/rotate operations | Shift left/right, rotate, barrel shift | Hardware/ALU |
| 5386–5395 | L425–L600 | Comparison operators | Compare, min, max, abs, sign, clamp | Functional |
| 5396–5401 | L605–L700 | Flags and counting | Zero/carry/borrow flags, LZC, TZC, popcount | Hardware/ALU |

---

## Suite 101 (Batch 93): Side-Channel Resistance

**Source**: `tests/test_batch_5402_5451.c`
**Tests**: 5402–5451 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(name) / ASSERT_TRUE / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5402–5415 | L70–L200 | Constant-time operations | Branchless AND/OR/NOT/add/sub/mul/compare | Security |
| 5416–5430 | L205–L370 | Power/EM resistance | DPA, CPA, EM emission, power uniformity | Security |
| 5431–5440 | L375–L470 | Speculative execution | Spectre, Meltdown, cache timing mitigation | Security |
| 5441–5451 | L475–L570 | Fault injection | Glitch, laser, voltage, row hammer resistance | Security |

---

## Suite 102 (Batch 94): Side-Channel Resistance Advanced

**Source**: `tests/test_batch_5452_5501.c`
**Tests**: 5452–5501 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(name) / ASSERT_TRUE / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5452–5470 | L70–L230 | Microarchitectural attacks | Flush+Reload, Prime+Probe, MDS, L1TF, LVI | Security |
| 5471–5485 | L235–L380 | Speculative store bypass | Spectre v4, RIDL, Fallout, ZombieLoad | Security |
| 5486–5495 | L385–L470 | Key protection | HSM, blinding, masking, resistant S-box | Security |
| 5496–5501 | L475–L530 | Boot attestation | Secure boot, random trit gen, hash hardening | Security |

---

## Suite 103 (Batch 95): Epistemic Logic & Hesitation

**Source**: `tests/test_batch_5502_5551.c`
**Tests**: 5502–5551 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(name) / ASSERT_TRUE / ASSERT_EQ / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5502–5520 | L70–L250 | K₃ truth tables | AND/OR/NOT commutativity, associativity, De Morgan | Logic |
| 5521–5535 | L255–L400 | Epistemic hesitation | Pause on Unknown, pipeline stall, confidence tracking | Scheduling |
| 5536–5545 | L405–L490 | Hesitation reactor | Channel registration, drift monitoring, recalibration | Initialization |
| 5546–5551 | L495–L560 | KL divergence | Distribution tracking, divergence computation, yield | Performance |

---

## Suite 104 (Batch 96): Epistemic Logic & Hesitation Advanced

**Source**: `tests/test_batch_5552_5601.c`
**Tests**: 5552–5601 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(name) / ASSERT_TRUE / ASSERT_EQ / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5552–5570 | L70–L250 | State transitions | IDLE→RUNNING→HESITATING, state machine | Functional |
| 5571–5585 | L255–L400 | Multi-channel stress | Concurrent channels, drift per-channel | Stress |
| 5586–5595 | L405–L490 | Recalibration | Confidence reset, distribution reset, B4 flags | Functional |
| 5596–5601 | L495–L560 | Yield computation | Divergence penalty, sensitivity, bounds | Performance |

---

## Suite 105 (Batch 97): Guardian Trit Mechanisms

**Source**: `tests/test_batch_5602_5651.c`
**Tests**: 5602–5651 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(name) / ASSERT_TRUE / ASSERT_EQ / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5602–5615 | L70–L200 | Guardian trit computation | Buffer hash, tamper detection, stability | Security |
| 5616–5630 | L205–L350 | Compression | Bit count, byte count, ratio, round-trip | Encoding |
| 5631–5640 | L355–L460 | T-IPC channels | Channel init, endpoint create, send/receive | IPC |
| 5641–5651 | L465–L570 | Validation | Message validation, NULL handling, tamper sensitivity | Security |

---

## Suite 106 (Batch 98): Guardian Trit Mechanisms Advanced

**Source**: `tests/test_batch_5652_5701.c`
**Tests**: 5652–5701 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(name) / ASSERT_TRUE / ASSERT_EQ / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 5652–5670 | L70–L250 | Cryptographic properties | Avalanche, collision resistance, preimage | Security |
| 5671–5685 | L255–L400 | Advanced attack resistance | Replay, bit flip, differential, length extension | Security |
| 5686–5695 | L405–L490 | Performance & stress | Benchmark, max buffer, concurrent access | Performance |
| 5696–5701 | L495–L560 | Integration | T-IPC failure recovery, radix guard, chaining | IPC |

---

## Suite 107 (Batch 109): RSI Flywheel Safety

**Source**: `tests/test_batch_6202_6251.c`
**Tests**: 6202–6251 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6202–6215 | L80–L200 | Trit guard logic | Guard approve/deny/query, bounds enforcement | Security |
| 6216–6230 | L205–L320 | Session management | Init, iterate, bounded loop (max 10), summary | Functional |
| 6231–6240 | L325–L400 | Mutation proposals | Proposal approval, rejection, beauty threshold | Security |
| 6241–6251 | L405–L480 | Eudaimonic metrics | Flourishing score, compaction, convergence | Performance |

---

## Suite 108 (Batch 110): Curiosity Gradient

**Source**: `tests/test_batch_6252_6301.c`
**Tests**: 6252–6301 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6252–6270 | L80–L220 | Curiosity prover | Gradient escalation, saturation, novelty scoring | Functional |
| 6271–6285 | L225–L340 | Gradient arithmetic | Step accumulation, decay, normalization | Arithmetic |
| 6286–6295 | L345–L420 | Integration | Curiosity + beauty combined scoring | Functional |
| 6296–6301 | L425–L480 | Edge cases | Zero gradient, max gradient, negative gradient | Boundary |

---

## Suite 109 (Batch 111): Beauty Symmetry

**Source**: `tests/test_batch_6302_6351.c`
**Tests**: 6302–6351 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6302–6320 | L80–L220 | Palindrome detection | Trit sequence palindrome check, scoring | Functional |
| 6321–6335 | L225–L340 | Symmetry metrics | Left-right mirror, rotational, translational | Functional |
| 6336–6345 | L345–L420 | Beauty scoring | Composite score, normalization, threshold | Performance |
| 6346–6351 | L425–L480 | Appreciation | Beauty above/below threshold, edge patterns | Boundary |

---

## Suite 110 (Batch 112): Eudaimonic Optimization

**Source**: `tests/test_batch_6352_6401.c`
**Tests**: 6352–6401 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6352–6370 | L80–L220 | Eudaimonic weight | Weight function, domain scoring, human override | Functional |
| 6371–6385 | L225–L340 | Flourishing metrics | Combined curiosity+beauty+eudaimonia vector | Performance |
| 6386–6395 | L345–L420 | Override semantics | Trit guard override, deny-all, approve-all | Security |
| 6396–6401 | L425–L480 | Convergence | Optimization convergence, stability criteria | Performance |

---

## Suite 111 (Batch 113): Balanced Ternary Arithmetic

**Source**: `tests/test_batch_6402_6451.c`
**Tests**: 6402–6451 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6402–6420 | L80–L220 | Encode/decode | int↔balanced ternary round-trip, range [-13..+13] | Encoding |
| 6421–6435 | L225–L340 | Carry arithmetic | Addition with carry, overflow wrap, multi-trit | Arithmetic |
| 6436–6445 | L345–L420 | Comparison | Trit-by-trit compare, lexicographic order | Functional |
| 6446–6451 | L425–L480 | Edge cases | Zero encoding, max/min value, sign detection | Boundary |

---

## Suite 112 (Batch 114): Mixed-Radix & Packed64 SIMD

**Source**: `tests/test_batch_6452_6501.c`
**Tests**: 6452–6501 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6452–6470 | L80–L220 | Packed64 encode/decode | 2-bit trit encoding, pack/unpack 32 slots | Encoding |
| 6471–6485 | L225–L340 | Trit get/set | Individual slot access, boundary slots 0 and 31 | Functional |
| 6486–6495 | L345–L420 | Fault detection | has_fault_packed64, sanitize, valid macro | Security |
| 6496–6501 | L425–L480 | SIMD Kleene ops | Packed AND/OR/NOT, De Morgan, round-trip | Logic |

---

## Suite 113 (Batch 115): Heptavint Multi-Radix Encoding

**Source**: `tests/test_batch_6502_6551.c`
**Tests**: 6502–6551 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6502–6515 | L80–L200 | Heptavint encode/decode | Balanced base-7 using 2 trits, range [-3..+3] | Encoding |
| 6516–6530 | L205–L320 | Round-trip & arithmetic | All 7 values round-trip, heptavint addition | Arithmetic |
| 6531–6540 | L325–L400 | Radix conversion | Base-3↔base-7 conversion, mixed-radix vectors | Encoding |
| 6541–6551 | L405–L480 | Overflow & packing | Overflow detection, multi-digit packing, zero repr | Boundary |

---

## Suite 114 (Batch 116): Ternary Floating-Point Basics

**Source**: `tests/test_batch_6552_6601.c`
**Tests**: 6552–6601 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6552–6570 | L80–L230 | tfloat encoding | Sign+4-mantissa+2-exponent, encode 0/±1/small values | Encoding |
| 6571–6585 | L235–L350 | Arithmetic | tfloat_add, tfloat_negate, simple cases | Arithmetic |
| 6586–6595 | L355–L430 | Comparison & check | tfloat_is_zero, tfloat_compare, round-trip integers | Functional |
| 6596–6601 | L435–L480 | Edge cases | Mantissa normalization, exponent overflow detection | Boundary |

---

## Suite 115 (Batch 117): Ternary Error Correction GF(3) Hamming

**Source**: `tests/test_batch_6602_6651.c`
**Tests**: 6602–6651 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6602–6615 | L80–L200 | GF(3) arithmetic | mod-3 add/mul, field properties | Arithmetic |
| 6616–6630 | L205–L320 | Hamming [4,2] encode | Encode all 9 inputs, parity check, syndrome | Encoding |
| 6631–6640 | L325–L400 | Error correction | Single-error correction for all 8 error patterns | Security |
| 6641–6651 | L405–L480 | Round-trip & limits | Encode→corrupt→correct→decode, double-error detection | Functional |

---

## Suite 116 (Batch 118): Ternary Capability Access Control

**Source**: `tests/test_batch_6652_6701.c`
**Tests**: 6652–6701 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6652–6670 | L80–L230 | Capability check | Grant+grant=grant, deny+any=deny, inherit resolution | Access control |
| 6671–6685 | L235–L350 | Combine & derive | Kleene AND semantics, child cannot escalate | Access control |
| 6686–6695 | L355–L430 | Revoke & special | Revoke by -1, null capability, full capability | Security |
| 6696–6701 | L435–L480 | Exhaustive | All 27 (read,write,exec) capability combinations | Access control |

---

## Suite 117 (Batch 119): Ternary State Machine & Protocol Verification

**Source**: `tests/test_batch_6702_6751.c`
**Tests**: 6702–6751 | **Runtime Assertions**: 50 | **Status**: ✅ Sigma 11 (50/50)
**Harness**: `TEST(d) / ASSERT(c, m) / PASS()` — per-test, abort on fail, final summary

| # | Range | Section | Coverage | Category |
|---|-------|---------|----------|----------|
| 6702–6715 | L80–L200 | State machine init | 3-trit state (27 states), init to {0,0,0} | Initialization |
| 6716–6730 | L205–L320 | Transitions | State advance rules, transition counting | Functional |
| 6731–6740 | L325–L400 | Reachability | All 27 states reachable, deadlock detection | Functional |
| 6741–6751 | L405–L480 | Protocol | 3-phase handshake, violation detection, reset | IPC |

---

## Rule: Future Test Documentation

> **⚠️ MANDATORY**: For every test created, a corresponding entry MUST be added
> to this glossary BEFORE the commit is considered valid.
>
> **4-Step Checklist**:
> 1. **Glossary entry** — Add a `## Suite N` section here with Source, Tests range,
>    Runtime Assertions, Status, Harness, and coverage table
> 2. **Makefile registration** — Add build target, `_run-test-suites` echo+run entry,
>    ALL_TESTS list entry, clean entry
> 3. **Grand summary** — Add suite name to `tools/test_grand_summary.sh` BATCH_DEFS
> 4. **Verify** — Run `make alltest` and confirm 100% pass rate
>
> **Index table** — Also add a row to the Suite Index table at the top of this file
>
> This protocol applies to ALL test types: batch tests, integration tests,
> red-team suites, formal verification suites, and any new test file.
