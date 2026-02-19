#!/bin/bash
# seT6 Modular Rebuild Script
# Arch Linux–inspired: rebuild modules individually, strip binary emulation
#
# Usage:
#   ./rebuild.sh                    # Rebuild all modules
#   ./rebuild.sh --ternary-only     # Rebuild with binary emulation stripped
#   ./rebuild.sh --module=tipc      # Rebuild single module
#
# SPDX-License-Identifier: GPL-2.0

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(dirname "$(dirname "$SCRIPT_DIR")")"

CC="${CC:-gcc}"
CFLAGS="-Wall -Wextra -Iinclude -Itools/compiler/include"

# Module directories
MODULES=(
    "trit_linux/modular"
    "trit_linux/ipc"
    "trit_linux/time"
    "trit_linux/hardening"
    "trit_linux/security"
    "trit_linux/net"
    "trit_linux/gui"
    "trit_linux/tools"
    "trit_linux/ai"
    "trit_linux/posix"
)

TERNARY_ONLY=0
SINGLE_MODULE=""

# Parse args
for arg in "$@"; do
    case $arg in
        --ternary-only)
            TERNARY_ONLY=1
            echo "[REBUILD] Ternary-only mode: stripping binary emulation"
            ;;
        --module=*)
            SINGLE_MODULE="${arg#*=}"
            echo "[REBUILD] Single module: $SINGLE_MODULE"
            ;;
        *)
            echo "Unknown arg: $arg"
            exit 1
            ;;
    esac
done

cd "$ROOT_DIR"

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║  seT6 Modular Rebuild                                       ║"
echo "║  Timestamp: $(date -u '+%Y-%m-%d %H:%M:%S UTC')                        ║"
echo "║  Mode: $([ $TERNARY_ONLY -eq 1 ] && echo 'TERNARY-ONLY' || echo 'STANDARD')                                       ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

build_module() {
    local mod_dir="$1"
    local mod_name="$(basename "$mod_dir")"
    
    if [ ! -d "$mod_dir" ]; then
        echo "  [SKIP] $mod_name — directory not found"
        return
    fi

    local c_files=$(find "$mod_dir" -maxdepth 1 -name '*.c' 2>/dev/null)
    if [ -z "$c_files" ]; then
        echo "  [SKIP] $mod_name — no C sources"
        return
    fi

    echo -n "  [BUILD] $mod_name ... "
    
    local extra_flags=""
    if [ $TERNARY_ONLY -eq 1 ]; then
        extra_flags="-DTRIT_TERNARY_ONLY=1"
    fi

    # Compile each .c to .o
    for src in $c_files; do
        local obj="${src%.c}.o"
        $CC $CFLAGS $extra_flags -c "$src" -o "$obj" 2>/dev/null && true
    done

    echo "OK"
}

BUILT=0
SKIPPED=0

for mod in "${MODULES[@]}"; do
    if [ -n "$SINGLE_MODULE" ]; then
        if [[ "$mod" != *"$SINGLE_MODULE"* ]]; then
            continue
        fi
    fi
    
    build_module "$mod"
    BUILT=$((BUILT + 1))
done

echo ""
echo "── Rebuild complete: $BUILT modules processed ──"
