#!/usr/bin/env bash
# T-054: Gödel Machine Diagnostic Engine
#
# DGM-inspired diagnostic tool. Parses `make test6` failure logs and
# `isabelle build` error output to identify improvement candidates.
#
# Output: JSON with structured failure analysis
#
# Usage: tools/godel_diagnose.sh [--output FILE]
#
# SPDX-License-Identifier: GPL-2.0
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUTPUT="${1:---}"

# ── Run the test suite and capture output ──
test_output=$(make -C "$ROOT" test6 2>&1 || true)

# ── Extract failing tests ──
failing_tests=()
while IFS= read -r line; do
    failing_tests+=("$line")
done < <(echo "$test_output" | grep -i '\[FAIL\]' | head -20 || true)

# ── Check for compilation errors ──
compile_errors=()
while IFS= read -r line; do
    compile_errors+=("$line")
done < <(echo "$test_output" | grep -E 'error:|undefined reference' | head -20 || true)

# ── Check for binary reversions ──
binary_reversions=()
# Look for functions that only produce {0, 1} instead of {-1, 0, +1}
for src in "$ROOT"/src/*.c; do
    basename=$(basename "$src")
    # Check if file uses trit type but might have binary patterns
    if grep -q 'trit' "$src" 2>/dev/null; then
        # Look for suspicious patterns: return 0 or 1 without -1
        has_neg=$(grep -c 'TRIT_FALSE\|return.*-1\|= -1' "$src" 2>/dev/null || echo 0)
        if [[ "$has_neg" -eq 0 ]]; then
            binary_reversions+=("$basename: no TRIT_FALSE usage detected")
        fi
    fi
done

# ── Check Isabelle proofs ──
proof_files=()
proof_sorrys=()
for thy in "$ROOT"/proof/*.thy; do
    if [[ -f "$thy" ]]; then
        proof_files+=("$(basename "$thy")")
        sorry_count=$(grep -c 'sorry' "$thy" 2>/dev/null || echo 0)
        if [[ "$sorry_count" -gt 0 ]]; then
            proof_sorrys+=("$(basename "$thy"): $sorry_count sorry obligations")
        fi
    fi
done

# ── Coverage gaps ──
uncovered_headers=()
for hdr in "$ROOT"/include/set5/*.h; do
    basename_h=$(basename "$hdr" .h)
    if ! grep -rl "$basename_h" "$ROOT"/tests/ >/dev/null 2>&1; then
        uncovered_headers+=("$basename_h: no test coverage found")
    fi
done

# ── Priority scoring ──
n_fail=${#failing_tests[@]}
n_compile=${#compile_errors[@]}
n_revert=${#binary_reversions[@]}
n_sorry=${#proof_sorrys[@]}
n_uncovered=${#uncovered_headers[@]}

priority_score=$(( n_compile * 10 + n_fail * 5 + n_revert * 8 + n_sorry * 3 + n_uncovered * 1 ))

# ── Output JSON ──
json_output() {
    echo "{"
    echo "  \"timestamp\": \"$(date -Iseconds)\","
    echo "  \"log_summary\": {"
    echo "    \"total_lines\": $(echo "$test_output" | wc -l),"
    echo "    \"failing_count\": $n_fail,"
    echo "    \"compile_errors\": $n_compile,"
    echo "    \"binary_reversions\": $n_revert,"
    echo "    \"proof_sorrys\": $n_sorry,"
    echo "    \"uncovered_headers\": $n_uncovered"
    echo "  },"

    echo "  \"failing_tests\": ["
    for i in "${!failing_tests[@]}"; do
        comma=$([[ $i -lt $((n_fail - 1)) ]] && echo "," || echo "")
        echo "    \"${failing_tests[$i]//\"/\\\"}\"$comma"
    done
    echo "  ],"

    echo "  \"compile_errors\": ["
    for i in "${!compile_errors[@]}"; do
        comma=$([[ $i -lt $((n_compile - 1)) ]] && echo "," || echo "")
        echo "    \"${compile_errors[$i]//\"/\\\"}\"$comma"
    done
    echo "  ],"

    echo "  \"binary_reversions\": ["
    for i in "${!binary_reversions[@]}"; do
        comma=$([[ $i -lt $((n_revert - 1)) ]] && echo "," || echo "")
        echo "    \"${binary_reversions[$i]//\"/\\\"}\"$comma"
    done
    echo "  ],"

    echo "  \"proof_sorrys\": ["
    for i in "${!proof_sorrys[@]}"; do
        comma=$([[ $i -lt $((n_sorry - 1)) ]] && echo "," || echo "")
        echo "    \"${proof_sorrys[$i]//\"/\\\"}\"$comma"
    done
    echo "  ],"

    echo "  \"improvement_candidates\": ["
    # Top priority items
    if [[ $n_compile -gt 0 ]]; then
        echo "    \"Fix compilation errors (blocks all testing)\","
    fi
    if [[ $n_revert -gt 0 ]]; then
        echo "    \"Address binary reversions in trit functions\","
    fi
    if [[ $n_fail -gt 0 ]]; then
        echo "    \"Fix failing test cases\","
    fi
    if [[ $n_sorry -gt 0 ]]; then
        echo "    \"Complete Isabelle proof obligations (sorry)\","
    fi
    echo "    \"Increase test coverage for uncovered headers\""
    echo "  ],"

    echo "  \"priority_score\": $priority_score"
    echo "}"
}

if [[ "$OUTPUT" == "--" ]] || [[ -z "$OUTPUT" ]]; then
    json_output
else
    json_output > "$OUTPUT"
    echo "Diagnostic output written to: $OUTPUT"
fi
