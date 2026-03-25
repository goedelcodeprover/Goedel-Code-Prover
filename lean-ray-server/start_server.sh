#!/bin/bash
# Lean Verifier Server startup script
# All configurations are loaded from .env file and config.py

set -e
cd "$(dirname "$0")"

echo "🚀 Starting Lean Verifier Server..."
echo "⚠️  Make sure Ray cluster is running first!"
echo "Press Ctrl+C to stop"
echo ""

export LEANSERVER_REPL_MEMORY_LIMIT_GB=8
export LEANSERVER_SERVE_NUM_REPLICAS=32     # HTTP replicas
export LEANSERVER_WORKER_POOL_SIZE=32     # Global worker pool size

exec python -m lean_verifier
