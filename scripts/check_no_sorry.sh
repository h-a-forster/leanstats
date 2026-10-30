#!/usr/bin/env sh
# Fail if any Lean source contains `sorry`, `admit`, `native_decide` or an `axiom` declaration.
# `lake build` additionally checks the axioms of the main theorems (LeanStatsTest/Axioms.lean).
set -eu
cd "$(dirname "$0")/.."
files=$(find LeanStats LeanStatsTest LeanStats.lean LeanStatsTest.lean -name '*.lean')
status=0
if grep -nwE 'sorry|admit|native_decide' $files; then
  echo "error: sorry, admit or native_decide found" >&2
  status=1
fi
if grep -nE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|public|noncomputable|unsafe)[[:space:]]+)*axiom[[:space:]]' $files; then
  echo "error: axiom declaration found" >&2
  status=1
fi
[ "$status" -eq 0 ] && echo "ok: no sorry, admit, native_decide or axiom declarations"
exit "$status"
