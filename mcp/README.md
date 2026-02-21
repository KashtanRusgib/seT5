# seT5 MCP Server — Deployment Guide

Remote and local MCP (Model Context Protocol) server for the **seT5/seT6 Ternary Microkernel**.
All three hosting options cost **$0** within free-tier limits.

---

## Quick Start

```bash
# Check prerequisites
./mcp/deploy.sh check

# Option 1: Local STDIO (full capabilities)
./mcp/deploy.sh local

# Option 2: Cloudflare Workers (read-only reference, global edge)
./mcp/deploy.sh cloudflare

# Option 3: Google Cloud Run (full capabilities, containerized)
./mcp/deploy.sh cloudrun

# Option 3b: Test Cloud Run locally with Docker
./mcp/deploy.sh docker
```

---

## Architecture

```
mcp/
├── deploy.sh              # One-command deploy script for all targets
├── README.md              # This file
├── local/                 # STDIO transport (Python)
│   ├── server.py          # Full MCP server with build/test/search tools
│   └── requirements.txt
├── cloudflare/            # SSE transport (Cloudflare Workers)
│   ├── src/index.ts       # Read-only reference MCP server
│   ├── package.json
│   ├── tsconfig.json
│   └── wrangler.toml
└── cloudrun/              # HTTP+SSE transport (Docker → Cloud Run)
    ├── server.py          # Full MCP server (same tools as local)
    ├── Dockerfile          # Ubuntu 24.04 + gcc + make + Python
    ├── requirements.txt
    └── cloudbuild.yaml     # CI/CD for Cloud Build
```

---

## Option Comparison

| Feature | Local (STDIO) | Cloudflare Workers | Google Cloud Run |
|---|---|---|---|
| **Transport** | STDIO | SSE | HTTP + SSE |
| **Cost** | $0 | $0 (100K req/day) | $0 (2M req/month) |
| **Build/Test** | ✅ Full | ❌ Read-only | ✅ Full |
| **Code Search** | ✅ grep | ❌ N/A | ✅ grep |
| **Architecture** | Python | TypeScript | Python + Docker |
| **Persistent** | No (on-demand) | Yes (edge) | Yes (serverless) |
| **Latency** | Instant | ~50ms (edge) | ~200ms (cold start) |
| **Best For** | Personal dev | Mobile/shared access | CI/CD, team use |

---

## I. Local STDIO Server

The most capable option — runs directly on your machine with full access to `gcc`, `make`, and the C toolchain.

### Setup

```bash
cd mcp/local
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

### Claude Desktop Configuration

Add to `~/.config/claude/claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "seT5": {
      "command": "/path/to/mcp/local/.venv/bin/python",
      "args": ["/path/to/mcp/local/server.py"],
      "env": {
        "SET5_ROOT": "/path/to/seT5"
      }
    }
  }
}
```

### VS Code / Copilot Configuration

Add to `.vscode/mcp.json`:

```json
{
  "servers": {
    "seT5": {
      "type": "stdio",
      "command": "python",
      "args": ["mcp/local/server.py"],
      "env": {
        "SET5_ROOT": "${workspaceFolder}"
      }
    }
  }
}
```

### Available Tools

| Tool | Description |
|---|---|
| `build_compiler` | Build the ternary C compiler |
| `build_native` | Build seT5 native kernel binary |
| `run_tests` | Run one or all 66+ test suites |
| `read_source` | Read any source file |
| `list_directory` | List directory contents |
| `search_code` | Grep the codebase |
| `get_test_results` | Get latest test results |
| `get_architecture` | Read ARCHITECTURE.md |
| `make_target` | Run any make target |
| `get_deployment_info` | MCP deployment info |

---

## II. Cloudflare Workers (SSE)

Global edge deployment — read-only reference tools (architecture, test lists, ternary reference). C toolchain cannot run inside V8 isolates, so build/test requires Local or Cloud Run.

### Deploy

```bash
cd mcp/cloudflare
npm install
npx wrangler login     # First time only
npx wrangler deploy
```

Your server is live at: `https://set5-mcp-server.<subdomain>.workers.dev/sse`

### Auto-Deploy on Push

Connect your GitHub repo in the [Cloudflare Dashboard](https://dash.cloudflare.com/) → Workers & Pages → Create → Connect to Git.

### Secure with API Key

```bash
npx wrangler secret put API_KEY
# Enter your secret key when prompted
```

Clients must then include `X-API-Key: <your-key>` header.

### Available Tools

| Tool | Description |
|---|---|
| `get_architecture` | Architecture summary |
| `list_test_suites` | All 66+ test suite names |
| `list_kernel_modules` | Core kernel modules |
| `balanced_ternary_reference` | K₃ logic and arithmetic tables |
| `search_test_suites` | Search suites by keyword |
| `get_deployment_info` | Deployment options |

---

## III. Google Cloud Run (HTTP + SSE)

Full build/test capabilities inside a Docker container. Scales to **zero** when idle — no cost when not in use.

### Prerequisites

```bash
# Install gcloud CLI: https://cloud.google.com/sdk/docs/install
gcloud auth login
gcloud config set project YOUR_PROJECT_ID
```

### Deploy

```bash
# From repo root:
gcloud run deploy set5-mcp \
  --source . \
  --dockerfile mcp/cloudrun/Dockerfile \
  --region us-central1 \
  --allow-unauthenticated \
  --memory 1Gi \
  --min-instances 0 \
  --max-instances 2

# Or use the script:
./mcp/deploy.sh cloudrun
```

### Secure with API Key

```bash
gcloud run services update set5-mcp \
  --region us-central1 \
  --set-env-vars API_KEY=your-secret-key
```

### Test Locally with Docker

```bash
docker build -t set5-mcp-cloudrun -f mcp/cloudrun/Dockerfile .
docker run -p 8080:8080 set5-mcp-cloudrun

# Test:
curl http://localhost:8080/health
```

### CI/CD with Cloud Build

The included `cloudbuild.yaml` auto-builds and deploys on push. Set up a trigger in the [Cloud Build Console](https://console.cloud.google.com/cloud-build/triggers).

---

## V. Security Checklist

- [ ] **Never** hardcode API keys, PATs, or secrets in the repository
- [ ] Set `API_KEY` via platform-native secrets management:
  - Cloudflare: `wrangler secret put API_KEY`
  - Cloud Run: `--set-env-vars API_KEY=...` or Secret Manager
- [ ] Both servers validate `X-API-Key` header when `API_KEY` env var is set
- [ ] The Local STDIO server has no network exposure (runs in-process)
- [ ] Path traversal protection: all file reads are confined to `SET5_ROOT`
- [ ] Shell metacharacter injection blocked in `make_target` tool
- [ ] Cloud Run scales to zero — no idle compute costs
- [ ] Monitor usage: Cloudflare Dashboard / Cloud Run Console

---

## Connecting MCP Clients

### SSE Clients (Cloudflare / Cloud Run)

Any MCP client that supports SSE transport can connect:

```
URL: https://your-deployment-url/sse
Headers: X-API-Key: <your-key>  (if API_KEY is set)
```

### STDIO Clients (Local)

Configure your MCP client to spawn the Python process directly. See the Claude Desktop and VS Code examples above.
