#!/usr/bin/env sh
# Check scripts/check_no_sorry.sh: it must pass on the sources as they are and fail on each
# planted pattern below. Each plant goes into a fresh scratch copy; the repository is untouched.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
fresh() {
  rm -rf "$work/t"
  mkdir -p "$work/t/scripts"
  cp -R "$root/LeanStats" "$root/LeanStatsTest" "$root/LeanStats.lean" "$root/LeanStatsTest.lean" \
    "$root/lakefile.toml" "$work/t/"
  cp "$root/scripts/check_no_sorry.sh" "$work/t/scripts/"
}
scan() { sh "$work/t/scripts/check_no_sorry.sh" >/dev/null 2>&1; }
fail=0
fresh
scan || { echo "FAIL: the unmodified sources are rejected"; fail=1; }
# plant FILE LINE: append LINE to FILE in a fresh copy and expect the scan to fail.
plant() {
  fresh
  printf '\n%s\n' "$2" >> "$work/t/$1"
  if scan; then echo "FAIL: not rejected in $1: $2"; fail=1; fi
}
while IFS= read -r line; do plant LeanStats/PValue.lean "$line"; done <<'PLANTS'
theorem planted : False := sorry
theorem planted : False := by admit
theorem planted : 2 + 2 = 4 := by native_decide
axiom planted : False
private axiom planted : False
  noncomputable axiom planted : False
set_option debug.skipKernelTC true in
@[implemented_by id] def planted (n : Nat) : Nat := n
@[extern "planted"] opaque planted : Nat
unsafe def planted : Nat := 0
#check Lean.ofReduceBool
#check sorryAx
#check Lean.Environment.addDeclWithoutChecking
#check Lean.Kernel.Environment.addDeclCore
#check Lean.Environment.addConstAsync
#eval Lean.modifyEnv id
#eval do let e ← Lean.getEnv; Lean.setEnv e
run_cmd pure ()
run_elab pure ()
run_meta pure ()
initialize pure ()
builtin_initialize pure ()
PLANTS
plant lakefile.toml 'debug.skipKernelTC = true'
plant lakefile.toml '[leanOptions.debug]'
fresh
touch "$work/t/lakefile.lean"
if scan; then echo "FAIL: lakefile.lean not rejected"; fail=1; fi
[ "$fail" -eq 0 ] && echo "ok: the source scan rejects every planted pattern"
exit "$fail"
