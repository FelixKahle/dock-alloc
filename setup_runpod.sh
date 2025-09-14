#!/usr/bin/env bash
# setup_rust_runpod.sh
# Sets up Rust in a plain Runpod Ubuntu container.
# - Updates packages; installs build tools, Git, Curl
# - Installs rustup (non-interactive), rustc, cargo
# - Persists PATH
# - (Optional) relocates CARGO_HOME/RUSTUP_HOME to /workspace for persistent caches
# - Verifies installation
# Idempotent: safe to run multiple times.

set -euo pipefail

### Configuration ################################################################
# If true and /workspace exists, store Cargo/Rustup under /workspace (persistent).
PERSIST_TO_WORKSPACE=true
# Extra tools you may want:
INSTALL_CLANG_AND_CMAKE=true
##################################################################################

# Use sudo only if not running as root
if [[ "${EUID:-$(id -u)}" -ne 0 ]]; then
  SUDO="sudo"
else
  SUDO=""
fi

echo "==> Updating package lists & installing base tools..."
$SUDO apt-get update -y
$SUDO apt-get upgrade -y

PKGS=(ca-certificates curl build-essential pkg-config libssl-dev)
[[ "$INSTALL_CLANG_AND_CMAKE" == "true" ]] && PKGS+=(clang cmake)

# Install Git only if missing
if ! command -v git >/dev/null 2>&1; then
  PKGS+=(git)
fi

$SUDO apt-get install -y --no-install-recommends "${PKGS[@]}"
$SUDO apt-get autoremove -y
$SUDO apt-get clean

# Install rustup if missing
if ! command -v rustup >/dev/null 2>&1; then
  echo "==> Installing rustup (non-interactive)..."
  # Default profile: installs rustc, cargo, rustup (stable)
  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
else
  echo "==> rustup already present — skipping install."
fi

# Activate PATH in current shell
if [[ -f "$HOME/.cargo/env" ]]; then
  # shellcheck disable=SC1090
  source "$HOME/.cargo/env"
fi

# Optional: persist Cargo/Rustup to /workspace
if [[ "$PERSIST_TO_WORKSPACE" == "true" && -d "/workspace" ]]; then
  echo "==> Relocating Cargo/Rustup to /workspace (persistent caches)..."
  CARGO_HOME_TARGET="/workspace/.cargo"
  RUSTUP_HOME_TARGET="/workspace/.rustup"

  mkdir -p "$CARGO_HOME_TARGET" "$RUSTUP_HOME_TARGET"

  # Move current contents if they exist (and are not symlinks)
  if [[ -d "$HOME/.cargo" && ! -L "$HOME/.cargo" ]]; then
    rsync -a --delete "$HOME/.cargo/" "$CARGO_HOME_TARGET/" || true
    rm -rf "$HOME/.cargo"
  fi
  if [[ -d "$HOME/.rustup" && ! -L "$HOME/.rustup" ]]; then
    rsync -a --delete "$HOME/.rustup/" "$RUSTUP_HOME_TARGET/" || true
    rm -rf "$HOME/.rustup"
  fi

  # Symlink into $HOME
  ln -sfn "$CARGO_HOME_TARGET" "$HOME/.cargo"
  ln -sfn "$RUSTUP_HOME_TARGET" "$HOME/.rustup"
fi

# Persist PATH (if not already present)
if ! grep -q 'export PATH="$HOME/.cargo/bin:$PATH"' "$HOME/.bashrc" 2>/dev/null; then
  echo 'export PATH="$HOME/.cargo/bin:$PATH"' >> "$HOME/.bashrc"
fi
if [[ -f "$HOME/.profile" ]] && ! grep -q 'export PATH="$HOME/.cargo/bin:$PATH"' "$HOME/.profile"; then
  echo 'export PATH="$HOME/.cargo/bin:$PATH"' >> "$HOME/.profile"
fi

# Components (idempotent)
echo "==> Installing/updating Rust components (rustfmt, clippy)..."
rustup toolchain install stable -q || true
rustup default stable -q || true
rustup component add rustfmt clippy -q || true

# Verify installation
echo "==> Verifying installation..."
set +e
rustc --version
cargo --version
rustup --version
set -e

# Optional mini build test
if [[ -w "/workspace" ]]; then
  TEST_DIR="/workspace/_rust_ok"
else
  TEST_DIR="$HOME/_rust_ok"
fi
if [[ ! -d "$TEST_DIR" ]]; then
  mkdir -p "$TEST_DIR"
  pushd "$TEST_DIR" >/dev/null
  cargo new --bin hello_world >/dev/null 2>&1 || true
  pushd hello_world >/dev/null
  echo 'fn main(){ println!("Rust OK"); }' > src/main.rs
  cargo build --quiet || true
  popd >/dev/null
  popd >/dev/null
fi

echo "==> Done. Rust is installed and configured."
echo "    Start a new shell or: source \$HOME/.cargo/env"
