#!/usr/bin/env bash
# ──────────────────────────────────────────────────────────────────────
# seT5 MCP Server — Deployment Script
# Deploys to any of the 3 supported platforms ($0 each)
# ──────────────────────────────────────────────────────────────────────

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
NC='\033[0m'

usage() {
    cat <<EOF
${CYAN}seT5 MCP Server — Deploy${NC}

Usage: $0 <target>

Targets:
  ${GREEN}local${NC}        Start the Local STDIO MCP server (Python)
  ${GREEN}cloudflare${NC}   Deploy to Cloudflare Workers (SSE, 100K req/day free)
  ${GREEN}cloudrun${NC}     Deploy to Google Cloud Run (SSE, 2M req/month free)
  ${GREEN}docker${NC}       Build and run the Cloud Run image locally
  ${GREEN}check${NC}        Verify all prerequisites are installed

Examples:
  $0 local                    # Start local STDIO server
  $0 cloudflare               # Deploy to Cloudflare Workers
  $0 cloudrun                 # Deploy to Google Cloud Run
  $0 docker                   # Test Cloud Run image locally

EOF
    exit 1
}

check_prerequisites() {
    echo -e "${CYAN}Checking prerequisites...${NC}"
    local ok=true

    # Always needed
    for cmd in python3 pip3 git make gcc; do
        if command -v "$cmd" &>/dev/null; then
            echo -e "  ${GREEN}✓${NC} $cmd"
        else
            echo -e "  ${RED}✗${NC} $cmd — REQUIRED"
            ok=false
        fi
    done

    # Cloudflare
    for cmd in node npm npx; do
        if command -v "$cmd" &>/dev/null; then
            echo -e "  ${GREEN}✓${NC} $cmd (Cloudflare Workers)"
        else
            echo -e "  ${YELLOW}○${NC} $cmd (needed for Cloudflare Workers only)"
        fi
    done

    if command -v wrangler &>/dev/null; then
        echo -e "  ${GREEN}✓${NC} wrangler (Cloudflare CLI)"
    else
        echo -e "  ${YELLOW}○${NC} wrangler (install: npm i -g wrangler)"
    fi

    # Cloud Run
    if command -v gcloud &>/dev/null; then
        echo -e "  ${GREEN}✓${NC} gcloud (Google Cloud CLI)"
    else
        echo -e "  ${YELLOW}○${NC} gcloud (needed for Cloud Run only)"
    fi

    if command -v docker &>/dev/null; then
        echo -e "  ${GREEN}✓${NC} docker"
    else
        echo -e "  ${YELLOW}○${NC} docker (needed for Cloud Run / local Docker)"
    fi

    if [ "$ok" = false ]; then
        echo -e "\n${RED}Missing required prerequisites.${NC}"
        exit 1
    fi
    echo -e "\n${GREEN}All core prerequisites met.${NC}"
}

deploy_local() {
    echo -e "${CYAN}Starting Local STDIO MCP Server...${NC}"
    cd "$SCRIPT_DIR/local"

    # Create venv if needed
    if [ ! -d ".venv" ]; then
        echo -e "  Creating virtual environment..."
        python3 -m venv .venv
    fi
    source .venv/bin/activate
    pip install -q -r requirements.txt

    echo -e "${GREEN}Server ready. Starting STDIO transport...${NC}"
    echo -e "${YELLOW}Configure your MCP client with:${NC}"
    echo -e "  command: $SCRIPT_DIR/local/.venv/bin/python"
    echo -e "  args: [\"$SCRIPT_DIR/local/server.py\"]"
    echo -e "  env: {\"SET5_ROOT\": \"$REPO_ROOT\"}"
    echo ""
    SET5_ROOT="$REPO_ROOT" exec python server.py
}

deploy_cloudflare() {
    echo -e "${CYAN}Deploying to Cloudflare Workers...${NC}"
    cd "$SCRIPT_DIR/cloudflare"

    if ! command -v npm &>/dev/null; then
        echo -e "${RED}npm is required for Cloudflare Workers. Install Node.js first.${NC}"
        exit 1
    fi

    echo -e "  Installing dependencies..."
    npm install

    echo -e "  Deploying (requires Cloudflare login)..."
    npx wrangler deploy

    echo -e "\n${GREEN}Deployed!${NC}"
    echo -e "${YELLOW}Set an API key:${NC}  npx wrangler secret put API_KEY"
    echo -e "${YELLOW}SSE endpoint:${NC}   https://set5-mcp-server.<your-subdomain>.workers.dev/sse"
}

deploy_cloudrun() {
    echo -e "${CYAN}Deploying to Google Cloud Run...${NC}"

    if ! command -v gcloud &>/dev/null; then
        echo -e "${RED}gcloud CLI is required. Install: https://cloud.google.com/sdk/docs/install${NC}"
        exit 1
    fi

    echo -e "  Building and deploying from source..."
    cd "$REPO_ROOT"
    gcloud run deploy set5-mcp \
        --source . \
        --dockerfile mcp/cloudrun/Dockerfile \
        --region us-central1 \
        --allow-unauthenticated \
        --memory 1Gi \
        --cpu 1 \
        --min-instances 0 \
        --max-instances 2 \
        --port 8080 \
        --timeout 300s

    echo -e "\n${GREEN}Deployed!${NC}"
    echo -e "${YELLOW}Set an API key:${NC}  gcloud run services update set5-mcp --set-env-vars API_KEY=your-secret"
    echo -e "${YELLOW}SSE endpoint:${NC}   <your-cloud-run-url>/sse"
}

deploy_docker() {
    echo -e "${CYAN}Building and running Cloud Run image locally...${NC}"

    if ! command -v docker &>/dev/null; then
        echo -e "${RED}docker is required.${NC}"
        exit 1
    fi

    cd "$REPO_ROOT"
    echo -e "  Building image..."
    docker build -t set5-mcp-cloudrun -f mcp/cloudrun/Dockerfile .

    echo -e "  Starting container on port 8080..."
    echo -e "${GREEN}SSE endpoint: http://localhost:8080/sse${NC}"
    echo -e "${GREEN}Health check: http://localhost:8080/health${NC}"
    docker run --rm -p 8080:8080 set5-mcp-cloudrun
}

# ── Main ─────────────────────────────────────────────────────────────

case "${1:-}" in
    local)       deploy_local ;;
    cloudflare)  deploy_cloudflare ;;
    cloudrun)    deploy_cloudrun ;;
    docker)      deploy_docker ;;
    check)       check_prerequisites ;;
    *)           usage ;;
esac
