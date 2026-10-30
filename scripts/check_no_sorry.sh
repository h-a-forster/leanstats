#!/usr/bin/env sh
# Fail if any Lean source contains `sorry`, `admit`, `native_decide`, an `axiom` declaration, or
# a way around the kernel (`debug.skipKernelTC`, `implemented_by`, `extern`, `unsafe`,
# `ofReduceBool`). `lake build` additionally audits the axioms of every declaration
# (LeanStatsTest/Axioms.lean), and CI replays the environment through the kernel (leanchecker).
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
if grep -nwE 'skipKernelTC|implemented_by|extern|unsafe|ofReduceBool' $files; then
  echo "error: kernel bypass (skipKernelTC, implemented_by, extern, unsafe, ofReduceBool) found" >&2
  status=1
fi
[ "$status" -eq 0 ] && echo "ok: no sorry, admit, native_decide, axiom declarations or kernel bypasses"
exit "$status"
