# Best Practices

## Non-Negotiable SOPs
- Modular: <500 LOC per file.
- Comments: 30% code.
- Naming: snake_case.
- Error Handling: Return codes, log.
- Performance: Profile trit ops.
- Security: No buffer overflows—use safe funcs.
- Docs: Update .md per change.
- **VERIFY**: Lint with cppcheck in CI.
