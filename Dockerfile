# seT6 Reproducible Build Environment
# T-010: Dockerfile for reproducible builds
# Usage:
#   docker build -t set6 .
#   docker run --rm set6 make test
#
# Guarantees identical build environment across all contributors.

FROM ubuntu:24.04

LABEL maintainer="seT6 Project" \
      description="seT6 Ternary Microkernel — Reproducible Build & Test" \
      version="1.0"

# Prevent interactive prompts
ENV DEBIAN_FRONTEND=noninteractive

# Install all build + test dependencies
RUN apt-get update -qq && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    make \
    python3 \
    python3-pip \
    python3-numpy \
    git \
    device-tree-compiler \
    iverilog \
    lcov \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# Set working directory
WORKDIR /seT6

# Copy entire repository
COPY . .

# Ensure submodules are initialized (for local builds without --recursive)
RUN git config --global --add safe.directory /seT6 && \
    git submodule update --init --recursive 2>/dev/null || true

# Build the compiler
RUN make build-compiler

# Default: run the full test suite
CMD ["make", "test"]
