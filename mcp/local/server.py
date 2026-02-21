#!/usr/bin/env python3
"""
seT5/seT6 Ternary Microkernel — Local STDIO MCP Server

This server exposes the full seT5 build/test toolchain as MCP tools
over the STDIO transport, suitable for use with Claude Desktop,
VS Code Copilot, or any MCP-compatible client.

Usage:
    cd mcp/local
    pip install -r requirements.txt
    python server.py

Claude Desktop config (~/.config/claude/claude_desktop_config.json):
    {
      "mcpServers": {
        "seT5": {
          "command": "python",
          "args": ["/absolute/path/to/mcp/local/server.py"],
          "env": { "SET5_ROOT": "/absolute/path/to/seT5" }
        }
      }
    }
"""

import asyncio
import json
import os
import subprocess
import sys
from pathlib import Path

from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import TextContent, Tool

# ── Resolve project root ─────────────────────────────────────────────

SET5_ROOT = Path(os.environ.get("SET5_ROOT", Path(__file__).resolve().parents[2]))

if not (SET5_ROOT / "Makefile").exists():
    print(f"WARNING: SET5_ROOT={SET5_ROOT} does not contain a Makefile", file=sys.stderr)


# ── Helpers ───────────────────────────────────────────────────────────

def _run(cmd: list[str], cwd: Path | None = None, timeout: int = 120) -> dict:
    """Run a subprocess and return structured output."""
    try:
        result = subprocess.run(
            cmd,
            cwd=cwd or SET5_ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return {
            "exit_code": result.returncode,
            "stdout": result.stdout[-8000:] if len(result.stdout) > 8000 else result.stdout,
            "stderr": result.stderr[-4000:] if len(result.stderr) > 4000 else result.stderr,
        }
    except subprocess.TimeoutExpired:
        return {"exit_code": -1, "stdout": "", "stderr": f"Command timed out after {timeout}s"}
    except FileNotFoundError:
        return {"exit_code": -1, "stdout": "", "stderr": f"Command not found: {cmd[0]}"}


def _read_file(rel_path: str, max_bytes: int = 32000) -> str:
    """Read a file relative to the project root, safely."""
    target = (SET5_ROOT / rel_path).resolve()
    # Prevent path traversal
    if not str(target).startswith(str(SET5_ROOT)):
        return f"ERROR: Path traversal blocked: {rel_path}"
    if not target.exists():
        return f"ERROR: File not found: {rel_path}"
    if not target.is_file():
        return f"ERROR: Not a file: {rel_path}"
    try:
        content = target.read_text(errors="replace")
        if len(content) > max_bytes:
            return content[:max_bytes] + f"\n\n... [TRUNCATED — {len(content)} bytes total]"
        return content
    except Exception as e:
        return f"ERROR reading {rel_path}: {e}"


def _list_dir(rel_path: str = ".") -> str:
    """List a directory relative to the project root."""
    target = (SET5_ROOT / rel_path).resolve()
    if not str(target).startswith(str(SET5_ROOT)):
        return f"ERROR: Path traversal blocked: {rel_path}"
    if not target.exists():
        return f"ERROR: Directory not found: {rel_path}"
    if not target.is_dir():
        return f"ERROR: Not a directory: {rel_path}"
    entries = sorted(target.iterdir())
    lines = []
    for e in entries[:200]:
        suffix = "/" if e.is_dir() else ""
        lines.append(f"  {e.name}{suffix}")
    result = f"{rel_path}/ ({len(entries)} entries):\n" + "\n".join(lines)
    if len(entries) > 200:
        result += f"\n  ... and {len(entries) - 200} more"
    return result


# ── MCP Server ────────────────────────────────────────────────────────

server = Server("seT5-mcp")


@server.list_tools()
async def list_tools() -> list[Tool]:
    return [
        Tool(
            name="build_compiler",
            description="Build the seT5 ternary C compiler from source (make build-compiler)",
            inputSchema={"type": "object", "properties": {}, "required": []},
        ),
        Tool(
            name="run_tests",
            description=(
                "Run seT5 test suites. Specify a suite name for a single suite, "
                "or leave empty to run the full test battery (66+ suites, ~5280 assertions)."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "suite": {
                        "type": "string",
                        "description": "Test suite name (e.g. 'test_sigma9', 'test_trit_linux'). Empty = all.",
                    },
                    "timeout": {
                        "type": "integer",
                        "description": "Timeout in seconds (default: 300 for all, 60 for single suite)",
                    },
                },
                "required": [],
            },
        ),
        Tool(
            name="build_native",
            description="Build the seT5 native kernel binary (make set5_native)",
            inputSchema={"type": "object", "properties": {}, "required": []},
        ),
        Tool(
            name="read_source",
            description="Read a source file from the repository (relative path)",
            inputSchema={
                "type": "object",
                "properties": {
                    "path": {
                        "type": "string",
                        "description": "Relative file path (e.g. 'src/memory.c', 'include/ternary.h')",
                    },
                },
                "required": ["path"],
            },
        ),
        Tool(
            name="list_directory",
            description="List files in a directory (relative path)",
            inputSchema={
                "type": "object",
                "properties": {
                    "path": {
                        "type": "string",
                        "description": "Relative directory path (e.g. 'src', 'tests', 'trit_linux/hw')",
                    },
                },
                "required": [],
            },
        ),
        Tool(
            name="search_code",
            description="Search for a pattern in the codebase using grep",
            inputSchema={
                "type": "object",
                "properties": {
                    "pattern": {
                        "type": "string",
                        "description": "Search pattern (grep -rn)",
                    },
                    "path": {
                        "type": "string",
                        "description": "Subdirectory to search in (default: entire repo)",
                    },
                },
                "required": ["pattern"],
            },
        ),
        Tool(
            name="get_test_results",
            description="Get the latest test results from TEST_RESULTS/ directory",
            inputSchema={"type": "object", "properties": {}, "required": []},
        ),
        Tool(
            name="get_architecture",
            description="Get the seT5/seT6 architecture summary (ARCHITECTURE.md)",
            inputSchema={"type": "object", "properties": {}, "required": []},
        ),
        Tool(
            name="make_target",
            description="Run an arbitrary make target",
            inputSchema={
                "type": "object",
                "properties": {
                    "target": {
                        "type": "string",
                        "description": "Make target name (e.g. 'clean', 'demos', 'build-set5')",
                    },
                },
                "required": ["target"],
            },
        ),
        Tool(
            name="get_deployment_info",
            description="Get info about all 3 MCP deployment options (Local, Cloudflare, Cloud Run)",
            inputSchema={"type": "object", "properties": {}, "required": []},
        ),
    ]


@server.call_tool()
async def call_tool(name: str, arguments: dict) -> list[TextContent]:
    match name:
        case "build_compiler":
            result = _run(["make", "build-compiler"], timeout=180)
            return [TextContent(type="text", text=json.dumps(result, indent=2))]

        case "build_native":
            result = _run(["make", "set5_native"], timeout=120)
            return [TextContent(type="text", text=json.dumps(result, indent=2))]

        case "run_tests":
            suite = arguments.get("suite", "")
            timeout = arguments.get("timeout")
            if suite:
                timeout = timeout or 60
                result = _run(["make", suite], timeout=timeout)
            else:
                timeout = timeout or 300
                result = _run(["bash", "run_all_tests.sh"], timeout=timeout)
            return [TextContent(type="text", text=json.dumps(result, indent=2))]

        case "read_source":
            content = _read_file(arguments["path"])
            return [TextContent(type="text", text=content)]

        case "list_directory":
            path = arguments.get("path", ".")
            content = _list_dir(path)
            return [TextContent(type="text", text=content)]

        case "search_code":
            pattern = arguments["pattern"]
            search_path = arguments.get("path", ".")
            result = _run(
                ["grep", "-rn", "--include=*.c", "--include=*.h", "--include=*.py",
                 "--include=*.md", "--include=*.sh", "-I", pattern, search_path],
                timeout=30,
            )
            output = result["stdout"] or result["stderr"] or "No matches found."
            return [TextContent(type="text", text=output)]

        case "get_test_results":
            results_dir = SET5_ROOT / "TEST_RESULTS"
            if not results_dir.exists():
                return [TextContent(type="text", text="No TEST_RESULTS/ directory found. Run tests first.")]
            files = sorted(results_dir.iterdir(), key=lambda f: f.stat().st_mtime, reverse=True)
            if not files:
                return [TextContent(type="text", text="TEST_RESULTS/ is empty. Run tests first.")]
            # Return the latest result file
            latest = files[0]
            content = _read_file(f"TEST_RESULTS/{latest.name}")
            return [TextContent(type="text", text=f"Latest result ({latest.name}):\n\n{content}")]

        case "get_architecture":
            content = _read_file("ARCHITECTURE.md")
            return [TextContent(type="text", text=content)]

        case "make_target":
            target = arguments["target"]
            # Block dangerous targets
            if any(x in target for x in [";", "|", "&", "`", "$", "(", ")"]):
                return [TextContent(type="text", text="ERROR: Shell metacharacters not allowed in target name")]
            result = _run(["make", target], timeout=180)
            return [TextContent(type="text", text=json.dumps(result, indent=2))]

        case "get_deployment_info":
            info = [
                "seT5 MCP Server — 3 Deployment Options (all $0):",
                "",
                "1. LOCAL (STDIO) — Full build/test [THIS SERVER]",
                f"   Root: {SET5_ROOT}",
                "   Start: cd mcp/local && python server.py",
                "   Tools: build, test, search, read — full capabilities",
                "",
                "2. CLOUDFLARE WORKERS (SSE) — Read-only reference",
                "   Start: cd mcp/cloudflare && npm install && npm run deploy",
                "   URL: https://<worker>.workers.dev/sse",
                "   Free: 100,000 requests/day",
                "   Tools: architecture, test list, ternary reference",
                "",
                "3. GOOGLE CLOUD RUN (HTTP+SSE) — Full build/test in container",
                "   Start: cd mcp/cloudrun && gcloud run deploy --source .",
                "   Free: 2M requests/month (Always Free tier)",
                "   Tools: same as Local, runs inside Docker container",
            ]
            return [TextContent(type="text", text="\n".join(info))]

        case _:
            return [TextContent(type="text", text=f"Unknown tool: {name}")]


# ── Entrypoint ────────────────────────────────────────────────────────

async def main():
    async with stdio_server() as (read_stream, write_stream):
        await server.run(read_stream, write_stream, server.create_initialization_options())


if __name__ == "__main__":
    asyncio.run(main())
