# Logging System and Schema

## Directive (In No Uncertain Terms)
**ALL AGENTS MUST LOG EVERY ACTION**. No exceptions. Faking logs = immediate revert. Use structured format for grep-ability. Logs **MUST** go to `logs/agent_<commit>.log`. Aggregate summaries in `logs/summary.log`.

### Schema (Strict JSON-like, One Line Per Entry)
Each log entry **MUST** be:

```
[LEVEL] [TIMESTAMP] [AGENT_ROLE] [TASK_ID] [MESSAGE] [DETAILS]
```

- LEVEL: ERROR|WARN|INFO|DEBUG. **ERROR** for failures—grep and fix immediately.
- TIMESTAMP: ISO 8601 (use `strftime`).
- AGENT_ROLE: e.g., ParserAgent.
- TASK_ID: From TODOLIST.md (e.g., TASK-001).
- MESSAGE: Concise action (e.g., "Parsed expression").
- DETAILS: JSON blob { "diff": "git diff output", "test_result": "PASS/FAIL" }.

### Implementation
- Header: `include/logger.h`.
- Source: `src/logger.c`.
- Functions:
  - `void logger_init(const char* logfile);`
  - `void logger_close(void);`
  - `void log_entry(LogLevel level, const char* role, const char* task, const char* msg, const char* details);`
  - **MUST** append to logfile.
  - **VERIFY**: Unit tests for each level, parse logs in CI.

### Best Practices
- Log before/after each function.
- In VM: Log stack state on errors.
- **NO POLLUTION**: Keep logs clean—agents **MUST** read summaries, not full logs unless needed.
- **CI Integration**: Script to check logs for ERRORs; fail build if any unresolved.

**AGENT ENFORCEMENT**: Every code change **MUST** include log calls. Test: Grep for logs in commits.
