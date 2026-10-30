# Report: leanstats v0.1.0

Date: 2026-10-30. Lean v4.35.0, mathlib `v4.35.0`
(commit `56a005855ea17e0b0958f73ec801ae140b0a1679`).

## 1. Result

All three targets are proved with no `sorry`, `admit`, `native_decide` or new axiom.
Revised after an external review (section 5).

| Target | Main theorem | Status |
|---|---|---|
| Holm controls FWER at level `α` (strong control: every set of true nulls `I₀`), finite family, arbitrary dependence, any real `α` | `holm_fwer_le` | proved |
| Bonferroni (corollary) | `bonferroni_fwer_le` | proved |
| Holm definition = sorted step-down procedure, any tie-breaking | `holmRejects_iff_stepDownRejects` | proved |
| Clopper–Pearson coverage `≥ 1 - α` for every `n`, every `p ∈ [0, 1]` | `one_sub_le_binomial_clopperPearson`, `binomial_clopperPearson_not_mem_le`, `HasLaw.one_sub_le_clopperPearson` | proved |
| Clopper–Pearson endpoints solve `P_θ(X ≥ x) = α/2` (`1 ≤ x ≤ n`) and `P_θ(X ≤ x) = α/2` (`x < n`), `0 < α ≤ 2`; interval non-empty for `α ≤ 1` | `binomial_real_Ici_cpLower`, `binomial_real_Iic_cpUpper`, `cpLower_le_cpUpper` | proved |
| Ville's inequality (stretch), `∃ k` and `sup_k` forms | `Supermartingale.mul_measure_exists_le`, `Supermartingale.measure_exists_le_le_div`, `Supermartingale.mul_measure_le_iSup` | proved |

Size: 789 lines in `LeanStats/` (44 definitions and theorems), plus 203 lines of examples and
audit in `LeanStatsTest/`.

A formal proof has no sampling error, so there are no intervals to report for the theorems
themselves. The quantities below are measurements of the checks.

## 2. Checks

| Check | Command | Outcome |
|---|---|---|
| Kernel-checked build, warnings as errors, mathlib standard linters | `lake build --wfail` | passes (3129 jobs) |
| Axioms of every declaration | `LeanStatsTest/Axioms.lean`: `#audit_leanstats_axioms` sweeps the `LeanStats` namespace; 11 main theorems are also listed by name | 47 declarations (44 source declarations and 3 equation lemmas), each within `[propext, Classical.choice, Quot.sound]`. Verified to fail on a planted `sorry` theorem in the namespace |
| Audit catches a gap | replaced the proof of `bonferroni_fwer_le` by `sorry` and rebuilt | build failed: `depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]` |
| Source scan | `sh scripts/check_no_sorry.sh` | passes. Verified to fail on a planted `sorry`, a planted `axiom`, and planted `set_option debug.skipKernelTC`, `implemented_by`, `extern` and `unsafe` (the previous scan passed the `skipKernelTC` plant) |
| Kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker LeanStats LeanStatsTest` (also in CI) | passes, 169 s on this machine. Without module arguments leanchecker looks for a module named after the package (`Leanstats`) and fails, so CI passes them explicitly |
| Definitions mean what they say | `LeanStatsTest/Examples.lean` | Holm rejects all of `(0.01, 0.02, 0.04)` at `α = 0.05` while Bonferroni misses `0.02`. Holm stops at `0.03 > 0.05/2` in `(0.01, 0.03, 0.04)` and does not reject `0.04`. Holm rejects neither tied value in `(0.02, 0.02, 0.5)` (a strict-count variant would reject both; checked separately). `cpUpper 1 0.05 0 = 0.975`. `cpLower 10 0.05 10 = 0.025^(1/10)`. `0.308 < cpUpper 10 0.05 0 < 0.309` and `0.115 < cpUpper 30 0.05 0 < 0.116`. Interior: `cpUpper 2 α 1 = √(1 - α/2)` from the definition, and `P(X ≥ 1) = 0.025` at `cpLower 2 0.05 1` |

The Clopper–Pearson closed forms agree with standard tables:
`cpLower 10 0.05 10 = 0.025^(1/10) = 0.6915`, `cpUpper 10 0.05 0 = 0.3085` and
`cpUpper 30 0.05 0 = 0.1157`. The last two are pinned to three decimals in Lean.

## 3. Build measurements (this machine, shared and heavily loaded)

| Step | Wall time |
|---|---|
| `lake update` + `lake exe cache get` (toolchain, mathlib sources, 9031 cache files) | 28 min |
| Clean build of leanstats (`rm -rf .lake/build; lake build --wfail`, mathlib cached) | 96 s |
| Incremental rebuild after editing every file | 2 min 10 s |

Most of the per-file time is loading mathlib `.olean` files. For iteration, a persistent Lean
language server, which keeps imports loaded, re-checks a file in 1–3 s.

## 4. Limitations

- **Endpoint uniqueness not formalised.** The Clopper–Pearson endpoints are defined as the
  infimum/supremum of the accepted parameters. Coverage alone cannot tell them from a wider
  interval, so their meaning rests on the characterisations: the closed forms for `x = 0` and
  `x = n`, and, for interior `x`, the proof that each endpoint solves its tail equation with a
  smaller tail beyond it (the smallest/largest root). That this root is unique, and so equals
  the Beta quantile, needs monotonicity of the tail in `θ`, which is not proved here.
- **CI has not run on GitHub.** The workflow runs on pull requests and manual dispatch only,
  and no run has happened yet. Every step it runs (source scan, `lake build --wfail`,
  leanchecker with the same arguments) was run locally.
- **Real-line distribution-function lemma not proved.** `measure_setOf_measure_Iic_le` is
  stated for countable linear orders, which covers the binomial case but not the general
  `P(F(X) ≤ t) ≤ t` for real random variables.
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

## 5. Review follow-up (2026-10-30)

An external review found no correctness errors. Changes made in response:

- Clopper–Pearson endpoints are characterised as roots of the tail equations for interior `x`
  (continuity of the tails suffices), and the interval is non-empty for `α ≤ 1`.
- `holm_fwer_le` and `bonferroni_fwer_le` no longer assume `0 ≤ α`.
- Ville's inequality also in the `sup_k M k ≥ ε` form.
- The axiom audit covers every declaration in the namespace, the source scan rejects kernel
  bypasses, and CI replays the environment through leanchecker.
- New examples: a tie case for Holm, an interior Clopper–Pearson value, decimal bounds.
- Docstrings: strong FWER control; the outer-measure convention of `IsValidPValue`.

Not changed: the real-line distribution-function lemma (planned before upstreaming, docs/PR.md
PR 1), and the third-party `axiom-audit` action input (the in-repo sweep covers the same check
without running external code).
