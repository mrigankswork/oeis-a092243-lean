#!/usr/bin/env bash
# Reproduce the verification of the kernel-only proof (Lean v4.35.0-rc2 and Mathlib, pinned in lean-toolchain and
# lake-manifest.json). Needs elan and git. Downloads the prebuilt Mathlib cache (a few GB) on first run.
# A clean build takes about 4-5 minutes and peaks at about 3.5 GB of memory.
set -euo pipefail
cd "$(dirname "$0")"
lake exe cache get
lake build
lake env lean scripts/axioms.lean
# Expected: every theorem depends only on [propext, Classical.choice, Quot.sound] (certs_ok: [propext]).
