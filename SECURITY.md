# Security policy

leanstats is a library of formal proofs. It has no runtime, network access or data handling of
its own, so the security-relevant failure is a **soundness problem**: a theorem that appears
proved but is not.

## Reporting

Report problems privately through the repository's **Security** tab ("Report a
vulnerability"). Include the commit, the Lean and mathlib versions, and a minimal file that
shows the problem.

## In scope

- A proof that is accepted by CI but relies on `sorry`, a new `axiom`, `native_decide`,
  `implemented_by`/`extern`, `debug.skipKernelTC` or any other way around the kernel, without
  the axiom audit (`LeanStatsTest/Axioms.lean`), `scripts/check_no_sorry.sh` or the leanchecker
  kernel replay in CI catching it.
- A definition that does not mean what the README and docs/DESIGN.md say it means (for
  example, a Clopper–Pearson interval that is trivially `[0, 1]`).
- CI configuration that runs untrusted code or uses an unpinned action.

## Out of scope

- Bugs in Lean, Lake or mathlib themselves (report those upstream).
