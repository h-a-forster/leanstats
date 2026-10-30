# Report: leanstats v0.1.0

Date: 2026-10-30. Lean v4.35.0, mathlib `v4.35.0`
(commit `56a005855ea17e0b0958f73ec801ae140b0a1679`).

## 1. Result

All three targets are proved with no `sorry`, `admit`, `native_decide` or new axiom.

| Target | Main theorem | Status |
|---|---|---|
| Holm controls FWER at level `α`, finite family, arbitrary dependence | `holm_fwer_le` | proved |
| Bonferroni (corollary) | `bonferroni_fwer_le` | proved |
| Holm definition = sorted step-down procedure, any tie-breaking | `holmRejects_iff_stepDownRejects` | proved |
| Clopper–Pearson coverage `≥ 1 - α` for every `n`, every `p ∈ [0, 1]` | `one_sub_le_binomial_clopperPearson`, `binomial_clopperPearson_not_mem_le`, `HasLaw.one_sub_le_clopperPearson` | proved |
| Ville's inequality (stretch) | `Supermartingale.mul_measure_exists_le`, `Supermartingale.measure_exists_le_le_div` | proved |

Size: 636 lines in `LeanStats/` (35 definitions and theorems), plus 128 lines of examples and
audit in `LeanStatsTest/`.

A formal proof has no sampling error, so there are no intervals to report for the theorems
themselves. The quantities below are measurements of the checks.

## 2. Checks

| Check | Command | Outcome |
|---|---|---|
| Kernel-checked build, warnings as errors, mathlib standard linters | `lake build --wfail` | passes (3129 jobs) |
| Axioms of the 11 main theorems | `LeanStatsTest/Axioms.lean` (`#guard_msgs` on `#print axioms`) | each is `[propext, Classical.choice, Quot.sound]` |
| Audit catches a gap | replaced the proof of `bonferroni_fwer_le` by `sorry` and rebuilt | build failed: `depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]` |
| Source scan | `sh scripts/check_no_sorry.sh` | passes. Verified to fail on a planted `sorry` and on a planted `axiom` |
| Definitions mean what they say | `LeanStatsTest/Examples.lean` | Holm rejects all of `(0.01, 0.02, 0.04)` at `α = 0.05` while Bonferroni misses `0.02`. Holm stops at `0.03 > 0.05/2` in `(0.01, 0.03, 0.04)` and does not reject `0.04`. `cpUpper 1 0.05 0 = 0.975`. `cpLower 10 0.05 10 = 0.025^(1/10)` |

The Clopper–Pearson closed forms agree with standard tables:
`cpLower 10 0.05 10 = 0.025^(1/10) = 0.6915`, `cpUpper 10 0.05 0 = 0.3085` and
`cpUpper 30 0.05 0 = 0.1157` (decimals computed outside Lean from the proved formulas).

## 3. Build measurements (this machine, shared and heavily loaded)

| Step | Wall time |
|---|---|
| `lake update` + `lake exe cache get` (toolchain, mathlib sources, 9031 cache files) | 28 min |
| Clean build of leanstats (`rm -rf .lake/build; lake build --wfail`, mathlib cached) | 96 s |
| Incremental rebuild after editing every file | 2 min 10 s |

Most of the per-file time is loading mathlib `.olean` files. For iteration, a persistent Lean
language server, which keeps imports loaded, re-checks a file in 1–3 s.

## 4. Limitations

- **Endpoint characterisation not formalised.** The Clopper–Pearson endpoints are defined as
  the infimum/supremum of the accepted parameters. That they equal the roots of
  `P_θ(X ≥ x) = α/2` (equivalently, Beta quantiles) needs monotonicity and continuity of the
  binomial tail in `θ`, which is not proved here. Coverage does not depend on it. The closed
  forms for `x = 0` and `x = n` are proved and match the textbook values.
- **Holm is stated for a fixed set of true nulls `I₀`.** This is the standard frequentist
  statement (it holds for every `I₀`). Data-dependent or random hypotheses are not modelled.
- **No closed-testing proof.** Holm's procedure is proved directly, not as a closed testing
  procedure, so general closed testing is not available as a by-product.
- **Ville is discrete-time.** The filtration is indexed by `ℕ` and the measure is finite.
  There is no continuous-time version and no e-process generalisation.
- **Not yet in mathlib.** The code follows mathlib style and builds with mathlib's linters, but
  it has not been reviewed by mathlib maintainers. docs/PR.md lists the expected renames.
- **Prior art search was limited** to mathlib's source and a web search. No novelty claim is
  made for other proof assistants.
