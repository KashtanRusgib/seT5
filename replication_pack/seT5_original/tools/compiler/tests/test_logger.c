/*
 * test_logger.c - Unit tests for the logging system
 *
 * Tests: logger_init, logger_close, log_entry, log_level_str
 * Coverage: all log levels, file output, format verification
 */

#include "../include/test_harness.h"
#include "../include/logger.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"
#include "../include/ir.h"
#include <string.h>
#include <unistd.h>

/* Helper: Read a file's contents into a buffer */
static char file_buf[4096];

static void read_file_contents(const char *path) {
    FILE *fp = fopen(path, "r");
    if (fp == NULL) {
        file_buf[0] = '\0';
        return;
    }
    size_t n = fread(file_buf, 1, sizeof(file_buf) - 1, fp);
    file_buf[n] = '\0';
    fclose(fp);
}

/* ---- log_level_str ---- */

TEST(test_level_str_debug) {
    ASSERT_STR_EQ(log_level_str(LOG_DEBUG), "DEBUG");
}

TEST(test_level_str_info) {
    ASSERT_STR_EQ(log_level_str(LOG_INFO), "INFO");
}

TEST(test_level_str_warn) {
    ASSERT_STR_EQ(log_level_str(LOG_WARN), "WARN");
}

TEST(test_level_str_error) {
    ASSERT_STR_EQ(log_level_str(LOG_ERROR), "ERROR");
}

/* ---- logger_init / logger_close ---- */

TEST(test_init_null) {
    /* Should succeed with NULL (stderr-only mode) */
    int result = logger_init(NULL);
    ASSERT_EQ(result, 0);
    logger_close();
}

TEST(test_init_file) {
    const char *tmplog = "/tmp/test_logger_init.log";
    unlink(tmplog);  /* Clean up first */

    int result = logger_init(tmplog);
    ASSERT_EQ(result, 0);

    /* File should be created */
    FILE *fp = fopen(tmplog, "r");
    ASSERT_NOT_NULL(fp);
    fclose(fp);

    logger_close();
    unlink(tmplog);
}

/* ---- Log output format ---- */

TEST(test_log_entry_format) {
    const char *tmplog = "/tmp/test_logger_format.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_DEBUG);
    log_entry(LOG_INFO, "TestAgent", "TASK-001", "Test message",
              "{\"test_result\":\"PASS\"}");
    logger_close();

    read_file_contents(tmplog);

    /* Verify format: [LEVEL] [TIMESTAMP] [ROLE] [TASK] [MSG] [DETAILS] */
    ASSERT_TRUE(strstr(file_buf, "[INFO]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "[TestAgent]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "[TASK-001]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "[Test message]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "{\"test_result\":\"PASS\"}") != NULL);

    unlink(tmplog);
}

/* ---- Log level filtering ---- */

TEST(test_log_level_filter) {
    const char *tmplog = "/tmp/test_logger_filter.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_WARN);

    /* DEBUG and INFO should be suppressed */
    log_entry(LOG_DEBUG, "Agent", "T1", "debug msg", NULL);
    log_entry(LOG_INFO, "Agent", "T1", "info msg", NULL);
    /* WARN and ERROR should appear */
    log_entry(LOG_WARN, "Agent", "T1", "warn msg", NULL);
    log_entry(LOG_ERROR, "Agent", "T1", "error msg", NULL);

    logger_close();

    read_file_contents(tmplog);

    ASSERT_TRUE(strstr(file_buf, "debug msg") == NULL);
    ASSERT_TRUE(strstr(file_buf, "info msg") == NULL);
    ASSERT_TRUE(strstr(file_buf, "warn msg") != NULL);
    ASSERT_TRUE(strstr(file_buf, "error msg") != NULL);

    unlink(tmplog);
}

/* ---- Multiple entries ---- */

TEST(test_log_multiple_entries) {
    const char *tmplog = "/tmp/test_logger_multi.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_DEBUG);

    log_entry(LOG_INFO, "A1", "T1", "first", NULL);
    log_entry(LOG_INFO, "A2", "T2", "second", NULL);
    log_entry(LOG_INFO, "A3", "T3", "third", NULL);

    logger_close();

    read_file_contents(tmplog);

    /* All three should be present */
    ASSERT_TRUE(strstr(file_buf, "first") != NULL);
    ASSERT_TRUE(strstr(file_buf, "second") != NULL);
    ASSERT_TRUE(strstr(file_buf, "third") != NULL);

    /* Count newlines to verify 3 entries */
    int lines = 0;
    for (char *p = file_buf; *p; p++) {
        if (*p == '\n') lines++;
    }
    ASSERT_EQ(lines, 3);

    unlink(tmplog);
}

/* ---- NULL parameter defaults ---- */

TEST(test_log_null_params) {
    const char *tmplog = "/tmp/test_logger_null.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_DEBUG);

    log_entry(LOG_INFO, NULL, NULL, NULL, NULL);

    logger_close();

    read_file_contents(tmplog);

    /* Should use defaults: "System", "NONE", "", "{}" */
    ASSERT_TRUE(strstr(file_buf, "[System]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "[NONE]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "[{}]") != NULL);

    unlink(tmplog);
}

/* ---- TASK-006: Verify logging appears in src functions ---- */

TEST(test_log_in_lexer) {
    const char *tmplog = "/tmp/test_logger_lexer.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_DEBUG);

    /* tokenize will call LOG_DEBUG_MSG("Lexer", ...) */
    tokenize("42");

    logger_close();

    read_file_contents(tmplog);
    ASSERT_TRUE(strstr(file_buf, "[Lexer]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "tokenize complete") != NULL);

    unlink(tmplog);
}

TEST(test_log_in_codegen) {
    const char *tmplog = "/tmp/test_logger_codegen.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_DEBUG);

    tokenize("1 + 2");
    parse();
    codegen();

    logger_close();

    read_file_contents(tmplog);
    ASSERT_TRUE(strstr(file_buf, "[Codegen]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "codegen entered") != NULL);
    ASSERT_TRUE(strstr(file_buf, "codegen complete") != NULL);

    unlink(tmplog);
}

TEST(test_log_in_vm) {
    const char *tmplog = "/tmp/test_logger_vm.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_DEBUG);

    /* Build simple bytecode: PUSH 5, HALT */
    unsigned char bc[] = { 0 /* OP_PUSH */, 5, 5 /* OP_HALT */ };
    /* Redirect stdout so Result: doesn't pollute test */
    FILE *devnull = fopen("/dev/null", "w");
    int saved = dup(fileno(stdout));
    fflush(stdout);
    dup2(fileno(devnull), fileno(stdout));

    vm_run(bc, sizeof(bc));

    fflush(stdout);
    dup2(saved, fileno(stdout));
    close(saved);
    fclose(devnull);

    logger_close();

    read_file_contents(tmplog);
    ASSERT_TRUE(strstr(file_buf, "[VM]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "vm_run entered") != NULL);
    ASSERT_TRUE(strstr(file_buf, "vm_run HALT") != NULL);

    unlink(tmplog);
}

TEST(test_log_in_parser) {
    const char *tmplog = "/tmp/test_logger_parser.log";
    unlink(tmplog);

    logger_init(tmplog);
    logger_set_level(LOG_DEBUG);

    /* parse_program logs "parse_program entered" */
    Expr *prog = parse_program("int main() { return 1; }");
    if (prog) expr_free(prog);

    logger_close();

    read_file_contents(tmplog);
    ASSERT_TRUE(strstr(file_buf, "[Parser]") != NULL);
    ASSERT_TRUE(strstr(file_buf, "parse_program entered") != NULL);

    unlink(tmplog);
}

int main(void) {
    TEST_SUITE_BEGIN("Logger");

    RUN_TEST(test_level_str_debug);
    RUN_TEST(test_level_str_info);
    RUN_TEST(test_level_str_warn);
    RUN_TEST(test_level_str_error);
    RUN_TEST(test_init_null);
    RUN_TEST(test_init_file);
    RUN_TEST(test_log_entry_format);
    RUN_TEST(test_log_level_filter);
    RUN_TEST(test_log_multiple_entries);
    RUN_TEST(test_log_null_params);
    RUN_TEST(test_log_in_lexer);
    RUN_TEST(test_log_in_codegen);
    RUN_TEST(test_log_in_vm);
    RUN_TEST(test_log_in_parser);

    TEST_SUITE_END();
}
