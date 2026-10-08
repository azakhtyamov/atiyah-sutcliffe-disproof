#!/usr/bin/env bash
# Verify the proof inside a checkout of google-deepmind/formal-conjectures (Lean 4.33.1, Mathlib v4.33.1):
#   FC=/path/to/formal-conjectures ./verify.sh
# Prints the axioms of `AtiyahSutcliffe.conjecture_one_false`; expected: [propext, Classical.choice, Quot.sound].
set -euo pipefail
FC=${FC:?set FC to a formal-conjectures checkout}
cp "$(dirname "$0")/AtiyahSutcliffeDisproof.lean" "$FC/"
cd "$FC"
lake build 'FormalConjectures.Arxiv.«1102.4662».AtiyahSutcliffe'
lake env lean AtiyahSutcliffeDisproof.lean | grep -v "^warning" || true
