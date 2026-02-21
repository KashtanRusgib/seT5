#!/usr/bin/env python3
"""
seT5/seT6 Ternary Microkernel — Google Cloud Run MCP Server (HTTP + SSE)

This server wraps the full seT5 build/test toolchain inside a Docker container
and exposes it as an MCP server over HTTP with Server-Sent Events transport.

The container includes gcc, make, and the full C source tree, so all build and
test tools work natively — unlike the Cloudflare Workers deployment which is
limited to read-only reference tools.

Deploy:
    cd mcp/cloudrun
    gcloud run deploy set5-mcp --source . --allow-unauthenticated

Or build and run locally:
    docker build -t set5-mcp-cloudrun .
    docker run -p 8080:8080 set5-mcp-cloudrun
"""

import asyncio
import json
import os
import subprocess
import sys
from pathlib import Path

from mcp.server import Server
from mcp.server.sse import SseServerTransport
from mcp.types import TextContent, Tool
from starlette.applications import Starlette
from starlette.requests import Request
from starlette.responses import JSONResponse
from starlette.routing import Mount, Route

# ── Configuration ────────────────────────────────────────────────────

SET5_ROOT = Path(os.environ.get("SET5_ROOT", "/seT5"))
PORT = int(os.environ.get("PORT", "8080"))
API_KEY = os.environ.get("API_KEY", "")  # Optional: set to require X-API-Key header


# ── Helpers ──────────────────────────────────────────────────────────

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
    if not str(target).startswith(str(SET5_ROOT.resolve())):
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
    if not str(target).startswith(str(SET5_ROOT.resolve())):
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


# ── MCP Server ───────────────────────────────────────────────────────

mcp_server = Server("seT5-mcp-cloudrun")


@mcp_server.list_tools()
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
    ]


@mcp_server.call_tool()
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
            latest = files[0]
            content = _read_file(f"TEST_RESULTS/{latest.name}")
            return [TextContent(type="text", text=f"Latest result ({latest.name}):\n\n{content}")]

        case "get_architecture":
            content = _read_file("ARCHITECTURE.md")
            return [TextContent(type="text", text=content)]

        case "make_target":
            target = arguments["target"]
            if any(x in target for x in [";", "|", "&", "`", "$", "(", ")"]):
                return [TextContent(type="text", text="ERROR: Shell metacharacters not allowed in target name")]
            result = _run(["make", target], timeout=180)
            return [TextContent(type="text", text=json.dumps(result, indent=2))]

        case _:
            return [TextContent(type="text", text=f"Unknown tool: {name}")]


# ── Starlette app with SSE transport ────────────────────────────────

sse_transport = SseServerTransport("/messages/")


async def handle_sse(request: Request):
    """SSE endpoint — clients connect here for the MCP event stream."""
    # Optional API key check
    if API_KEY:
        provided = request.headers.get("X-API-Key") or request.query_params.get("api_key")
        if provided != API_KEY:
            return JSONResponse({"error": "Unauthorized", "hint": "Set X-API-Key header"}, status_code=401)

    async with sse_transport.connect_sse(
        request.scope, request.receive, request._send
    ) as streams:
        await mcp_server.run(
            streams[0], streams[1], mcp_server.create_initialization_options()
        )


async def handle_messages(request: Request):
    """Message POST endpoint for SSE transport."""
    await sse_transport.handle_post_message(request.scope, request.receive, request._send)


async def health(request: Request):
    """Health check endpoint for Cloud Run."""
    return JSONResponse({
        "status": "ok",
        "server": "seT5-mcp-cloudrun",
        "version": "1.0.0",
        "transport": "sse",
        "endpoints": {
            "sse": "/sse",
            "messages": "/messages/",
            "health": "/health",
        },
    })


app = Starlette(
    routes=[
        Route("/health", health),
        Route("/", health),
        Route("/sse", handle_sse),
        Mount("/messages/", app=handle_messages),
    ],
)


# ── Entrypoint ──────────────────────────────────────────────────────

if __name__ == "__main__":
    import uvicorn
    print(f"seT5 MCP Server (Cloud Run) starting on port {PORT}", file=sys.stderr)
    print(f"  SSE endpoint: http://0.0.0.0:{PORT}/sse", file=sys.stderr)
    print(f"  Health check: http://0.0.0.0:{PORT}/health", file=sys.stderr)
    uvicorn.run(app, host="0.0.0.0", port=PORT)
