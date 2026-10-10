#!/usr/bin/env bash
# Verify the proof inside a checkout of google-deepmind/formal-conjectures (Lean 4.33.1, Mathlib v4.33.1):
#   FC=/path/to/formal-conjectures ./verify.sh
# Verified at formal-conjectures c53326acbefd6b337ef4a610bc9aa0c6aa59ebde (the base of PR #6966) and at the head
# of that PR; any commit with the same definitions in FormalConjectures/Arxiv/1102.4662/AtiyahSutcliffe.lean works
# (logs in logs/). The script exits with Lean's status, and the last line it prints must be
#   'AtiyahSutcliffeDisproof.conjecture_one_false' depends on axioms: [propext, Classical.choice, Quot.sound]
# Expect about ten minutes and 16 GB of memory (kernel evaluation of the certificate).
set -euo pipefail
FC=${FC:?set FC to a formal-conjectures checkout}
here=$(cd "$(dirname "$0")" && pwd)
cd "$FC"
echo "formal-conjectures at $(git rev-parse HEAD)"
lean --version
lake build 'FormalConjectures.Arxiv.«1102.4662».AtiyahSutcliffe'
lake env lean "$here/AtiyahSutcliffeDisproof.lean"
