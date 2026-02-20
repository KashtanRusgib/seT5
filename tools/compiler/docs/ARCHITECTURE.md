# Architecture of Ternary Compiler

## High-Level Design (Non-Negotiable)
This compiler **MUST** follow a classic pipeline: Frontend -> IR -> Backend -> VM. **NO SHORTCUTS**. Built in C for bootstrapping. Target: Balanced ternary (-1,0,1) ops, per Huawei patent insights. Expand from expressions to full C (loops, functions, pointers) modularly.

### Components (Implement One at a Time, with Tests)
1. **Frontend**:
   - Lexer: Tokenize C source. **MUST** handle keywords, ints, ops (`if`, `else`, `while`, `for`, `return`, `int`). File: `src/parser.c`. Test: 100% coverage for valid/invalid inputs.
   - Parser: Build AST. Recursive descent with precedence climbing. Parses functions, parameters, variable declarations, assignments, pointer ops, `if/else`, `while`, `for`, comparison operators (`==`, `<`, `>`).

2. **Intermediate Representation (IR)**:
   - AST nodes as structs in `include/ir.h` / `src/ir.c`.
   - Node types: `NODE_CONST`, `NODE_VAR`, `NODE_BINOP`, `NODE_FUNC_DEF`, `NODE_FUNC_CALL`, `NODE_RETURN`, `NODE_PROGRAM`, `NODE_DEREF`, `NODE_ADDR_OF`, `NODE_ASSIGN`, `NODE_VAR_DECL`, `NODE_IF`, `NODE_WHILE`, `NODE_FOR`, `NODE_BLOCK`.
   - Operators: `OP_IR_ADD`, `OP_IR_MUL`, `OP_IR_SUB`, `OP_IR_CMP_EQ`, `OP_IR_CMP_LT`, `OP_IR_CMP_GT`, `OP_IR_NEG`.
   - Optimizations: Constant folding for arithmetic and comparison ops. Pass for each new feature.
   - **Postfix IR** (`include/postfix_ir.h`, `src/postfix_ir.c`): POLIZ-style flat instruction sequence (Setun-70 inspired). Converts AST → linear postfix form for peephole optimization before bytecode emission.

3. **Backend**:
   - Codegen (token-based): `src/codegen.c` — simple arithmetic expression codegen.
   - Bootstrap codegen (AST-based): `src/bootstrap.c` — full-featured AST-to-bytecode emitter with control flow, scoping, symbol table.
   - Emits structured control flow: `OP_BRZ` with forward patching, `OP_LOOP_BEGIN`/`OP_LOOP_END` for loops, `OP_ENTER`/`OP_LEAVE` for scope frames.

4. **VM Simulator (Setun-70 Inspired Two-Stack Model)**:
   - **Operand stack**: Expression evaluation, data manipulation.
   - **Return stack**: Control flow, function calls, loop addresses, scope frames.
   - 36 opcodes organized by phase:
     - **Phase 1 (Core)**: PUSH, ADD, MUL, SUB, JMP, COND_JMP, HALT, LOAD, STORE, SYSCALL.
     - **Phase 3 (Stack manip)**: DUP, DROP, SWAP, OVER, ROT.
     - **Phase 3 (Return stack)**: TO_R, FROM_R, R_FETCH.
     - **Phase 3 (Functions)**: CALL, RET, ENTER, LEAVE.
     - **Phase 3 (Structured flow)**: BRZ, BRN, BRP, LOOP_BEGIN, LOOP_END, BREAK.
     - **Phase 3 (Comparisons)**: CMP_EQ, CMP_LT, CMP_GT.
     - **Phase 3 (Ternary logic)**: NEG, CONSENSUS, ACCEPT_ANY.
     - **Phase 3 (Extended data)**: PUSH_TRYTE, PUSH_WORD.
   - Memory: 729 cells (3^6), ternary-addressable.
   - File: `vm/ternary_vm.c`.

5. **Data Types**:
   - Trit: `signed char` (-1=N, 0=Z, 1=P). File: `include/ternary.h`.
   - Word: 9-trit array with add/mul/sub/neg/consensus/accept_any ops.
   - **Tryte** (Setun-70 syllable): 6-trit array (729 states). Basic addressing unit. Includes add, neg, consensus, accept_any, cmp operations.
   - Trit-level logic gates: `trit_consensus` (AND), `trit_accept_any` (OR), `trit_not` (negation), `trit_sub` (subtraction with borrow).

### Design Principles (Setun-70 / ALGOL-60 Inspired)
- **Two-stack model**: Operand stack for data, return stack for control flow (Setun-70).
- **Structured programming enforced at ISA level**: No unstructured GOTOs. All control flow uses BRZ/BRN/BRP + LOOP_BEGIN/END + ENTER/LEAVE.
- **Postfix evaluation**: Stack-machine bytecode in reverse Polish notation (DSSP/Forth-like).
- **Tryte-aligned instructions**: 6-trit syllables as basic unit (Setun-70 format).
- **Balanced ternary arithmetic**: Symmetric negation, natural signed representation without sign bit.
- **Frame markers**: ENTER pushes -1 sentinel, LEAVE pops to it — enforces scoped nesting.
- **Ternary logic at ISA level**: CONSENSUS (AND-like), ACCEPT_ANY (OR-like), NEG — native balanced ternary gates (Brusentsov/Jones).

### Scalability for seT5
- Phase 1: Expressions. ✅
- Phase 2: Control flow, pointers, memory, syscalls. ✅
- Phase 3: Setun-70 ISA, two-stack VM, structured control flow, ternary logic gates, postfix IR. ✅
- **VERIFICATION**: Each phase **MUST** compile sample seL4 code to ternary.

**AGENT RULE**: Implement exactly as described. If deviating, log reason and revert if tests fail. Update TODO after each task.
