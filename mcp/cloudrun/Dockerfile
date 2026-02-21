# seT5 MCP Server — Google Cloud Run
# Full build/test capabilities inside a container.
#
# Build:   docker build -t set5-mcp-cloudrun .
# Run:     docker run -p 8080:8080 set5-mcp-cloudrun
# Deploy:  gcloud run deploy set5-mcp --source . --allow-unauthenticated
#
# Free tier: 2M requests/month, scales to zero when idle.

FROM ubuntu:24.04

LABEL maintainer="seT5 Project" \
    description="seT5 Ternary Microkernel — MCP Server for Cloud Run" \
    version="1.0.0"

ENV DEBIAN_FRONTEND=noninteractive
ENV SET5_ROOT=/seT5
ENV PORT=8080

# Install build + runtime dependencies
RUN apt-get update -qq && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    make \
    python3 \
    python3-pip \
    python3-venv \
    python3-numpy \
    git \
    device-tree-compiler \
    iverilog \
    ca-certificates \
    grep \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /seT5

# Copy the full repository (build context must be repo root)
# Build with: docker build -t set5-mcp-cloudrun -f mcp/cloudrun/Dockerfile .
COPY . .

# Install Python MCP dependencies
COPY mcp/cloudrun/requirements.txt /tmp/mcp-requirements.txt
RUN python3 -m venv /opt/mcp-venv && \
    /opt/mcp-venv/bin/pip install --no-cache-dir -r /tmp/mcp-requirements.txt

# Copy the MCP server
COPY mcp/cloudrun/server.py /opt/mcp-server/server.py

# Build the compiler (cached layer — only rebuilds if source changes)
RUN git config --global --add safe.directory /seT5 && \
    git submodule update --init --recursive 2>/dev/null || true && \
    make build-compiler 2>/dev/null || true

EXPOSE 8080

# Health check for Cloud Run
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s \
    CMD python3 -c "import urllib.request; urllib.request.urlopen('http://localhost:8080/health')" || exit 1

CMD ["/opt/mcp-venv/bin/python3", "/opt/mcp-server/server.py"]
