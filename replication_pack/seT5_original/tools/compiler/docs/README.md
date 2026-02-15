# Ternary Compiler in C

## Overview
This is a balanced ternary compiler written in C, targeting a ternary VM for a subset of C (expanding to full C for seT5 microkernel). **NO DEVIATIONS ALLOWED**: Follow ARCHITECTURE.md exactly. All code **MUST** be modular, with unit tests covering 100% of functions. Faking code is forbidden—verify via `make test` before any commit.

## Setup
1. Clone repo: `git clone <your-private-repo>`.
2. Build: `make all`.
3. Run: `./ternary_compiler <source.c>`.
4. Test: `make test`—**MUST** pass all before pushing.

## Key Principles (Enforced in No Uncertain Terms)
- **Modularity**: Every component (lexer, parser, codegen, VM) in separate files/modules.
- **Testing**: Use the built-in test harness for unit tests. **NO CODE WITHOUT TESTS**. Agents **MUST** write tests first (TDD).
- **Logging**: Follow LOGGING.md schema. Log every action.
- **Verification**: Agents **MUST** run `git diff` and log it; if tests fail, **REVERT IMMEDIATELY**.
- **Parallelism**: Use TODO locks (e.g., claim in TODOLIST.md by adding [LOCKED: AgentX]).
- **Best Practices**: Commit atomic changes. No merge conflicts without resolution logs.

## Directories
- `src/`: Core compiler code.
- `include/`: Headers.
- `vm/`: Ternary VM simulator.
- `tests/`: Unit tests.
- `docs/`: All .md files here.
- `logs/`: Agent and CI logs.

**AGENT DIRECTIVE**: If you're an agent, read AGENT_PROMPT.md first. Update this README only if architecture changes, and verify with tests.
