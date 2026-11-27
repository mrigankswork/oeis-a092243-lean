#!/usr/bin/env bash
# LEGACY (v0.1, native_decide proof). Reproduce its verification: build the upstream statement module of google-deepmind/formal-conjectures at the pinned
# commit, unchanged, then compile OeisA92243.lean against it and print the axioms.
# Needs elan (Lean toolchain manager) and git; downloads the prebuilt Mathlib cache (a few GB) on first run.
set -euo pipefail
FC_COMMIT=9097e2f90e66d2f6244209cb1c07f7120d17ec53
here="$(cd "$(dirname "$0")" && pwd)"
if [ ! -d "$here/formal-conjectures" ]; then
  git clone https://github.com/google-deepmind/formal-conjectures.git "$here/formal-conjectures"
fi
cd "$here/formal-conjectures"
git checkout -q "$FC_COMMIT"
lake exe cache get
lake build 'FormalConjectures.OEIS.«92243»'
mkdir -p Attempts
cp "$here/OeisA92243_native_decide.lean" Attempts/OeisA92243.lean
lake env lean Attempts/OeisA92243.lean
