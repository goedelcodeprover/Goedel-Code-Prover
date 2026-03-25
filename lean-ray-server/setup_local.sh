#!/usr/bin/env bash
set -euxo pipefail

# Install elan and Lean to local disk instead of NFS for better performance
# This will significantly improve build and verification speed

LEAN_VERSION="v4.22.0"
# Set local disk path (not NFS)
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
LOCAL_ELAN_HOME="$SCRIPT_DIR/../.elan"

command -v curl > /dev/null 2>&1 || { echo "Error: curl is not installed." >&2; exit 1; }
command -v git > /dev/null 2>&1 || { echo "Error: git is not installed." >&2; exit 1; }

# Check if elan is already installed locally
if [ -d "$LOCAL_ELAN_HOME" ]; then
    echo "WARNING: Local elan already exists at: $LOCAL_ELAN_HOME"
    echo "To reinstall, first remove it: rm -rf $LOCAL_ELAN_HOME"
    # Use existing installation
    export ELAN_HOME="$LOCAL_ELAN_HOME"
    export PATH="$ELAN_HOME/bin:$PATH"
else
    # Install Lean to local disk
    echo "Installing Lean ${LEAN_VERSION} to local disk: $LOCAL_ELAN_HOME"
    export ELAN_HOME="$LOCAL_ELAN_HOME"
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain ${LEAN_VERSION} -y --no-modify-path
    
    # Add to PATH
    export PATH="$ELAN_HOME/bin:$PATH"
    
    echo ""
    echo "Elan installed successfully!"
    echo ""
fi

# Install REPL
echo "Installing REPL..."
if [ ! -d "repl" ]; then
    git clone https://github.com/leanprover-community/repl.git 
fi
pushd repl
git checkout ${LEAN_VERSION}
lake build
popd

# Install Mathlib
echo "Installing Mathlib..."
if [ ! -d "mathlib4" ]; then
    git clone https://github.com/leanprover-community/mathlib4.git
fi
pushd mathlib4
git checkout ${LEAN_VERSION}
lake exe cache get && lake build
popd

echo ""
echo "================================================"
echo "Installation completed successfully!"
echo "================================================"
echo ""


