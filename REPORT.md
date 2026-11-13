# Report: leanstats 0.1.0 (untagged)

Date: 2026-10-30. Lean v4.35.0, mathlib `v4.35.0`
(commit `56a005855ea17e0b0958f73ec801ae140b0a1679`).

## 1. Result

All three targets are proved with no `sorry`, `admit`, `native_decide` or new axiom.
Revised after external reviews (section 5).

| Target | Main theorem | Status |
|---|---|---|
| Holm controls FWER at level `α` (strong control: every set of true nulls `I₀`), finite family, arbitrary dependence, any real `α` | `holm_fwer_le` | proved |
| Holm FWER as a real probability (`μ.real`), `α ≥ 0` | `holm_fwer_le_real` | proved |
| Bonferroni (corollary) | `bonferroni_fwer_le` | proved |
| Holm definition = sorted step-down procedure, any tie-breaking, for `α ≥ 0` | `holmRejects_iff_stepDownRejects` | proved |
| Clopper–Pearson coverage `≥ 1 - α` for every `n`, every `p ∈ [0, 1]` | `one_sub_le_binomial_clopperPearson`, `binomial_clopperPearson_not_mem_le`, `HasLaw.one_sub_le_clopperPearson` | proved |
| Clopper–Pearson endpoints solve `P_θ(X ≥ x) = α/2` (`1 ≤ x ≤ n`) and `P_θ(X ≤ x) = α/2` (`x < n`), `0 < α ≤ 2`; interval non-empty for `α ≤ 1` | `binomial_real_Ici_cpLower`, `binomial_real_Iic_cpUpper`, `cpLower_le_cpUpper` | proved |
| Tails strictly monotone in `θ`, so each endpoint is the unique root of its tail equation | `strictMono_binomial_real_Ici`, `strictAnti_binomial_real_Iic`, `binomial_real_Ici_eq_iff`, `binomial_real_Iic_eq_iff` | proved |
| Distribution function is super-uniform for any measure on `ℝ`: `P(F(X) ≤ t) ≤ t` | `measure_cdf_le`, `measure_setOf_measure_Iic_le_real`, `measure_setOf_measure_Ici_le_real` | proved |
| Ville's inequality, `∃ k` and `sup_k` forms | `Supermartingale.mul_measure_exists_le`, `Supermartingale.measure_exists_le_le_div`, `Supermartingale.mul_measure_le_iSup` | proved |

Size: 946 lines in `LeanStats/` (54 definitions and theorems), plus 218 lines of examples and
audit in `LeanStatsTest/`.

A formal proof has no sampling error, so there are no intervals to report for the theorems
themselves. The quantities below are measurements of the checks.

## 2. Checks

| Check | Command | Outcome |
|---|---|---|
| Kernel-checked build, warnings as errors, mathlib standard linters | `lake build --wfail` | passes (3146 jobs) |
| Axioms of every declaration | `LeanStatsTest/Axioms.lean`: `#audit_leanstats_axioms` sweeps every non-internal declaration made in a `LeanStats` module, whatever its namespace, and requires 15 named main theorems to be among the audited declarations | 57 declarations (54 source declarations and 3 equation lemmas), each within `[propext, Classical.choice, Quot.sound]`. Verified to fail on a planted `sorry` theorem in the namespace, an unknown name and a listed name outside the library, and on a planted `sorry` theorem in the root namespace inside a `LeanStats` module (the previous namespace-only sweep passed it) |
| Audit catches a gap | replaced the proof of `bonferroni_fwer_le` by `sorry` and rebuilt | build failed: `depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]` |
| Source scan | `sh scripts/check_no_sorry.sh` | passes. Verified to fail on a planted `sorry`, a planted `axiom`, and planted `set_option debug.skipKernelTC`, `implemented_by`, `extern` and `unsafe` (the previous scan passed the `skipKernelTC` plant). Also fails on each of `sorryAx`, `addDeclWithoutChecking`, `addDeclCore`, `modifyEnv`, `run_cmd`, `run_elab`, `run_meta` and on `debug.skipKernelTC` in `lakefile.toml`, all of which the previous scan passed. Also fails on `setEnv`, `addConstAsync`, `initialize`, `builtin_initialize`, a `[leanOptions.debug]` table and a `lakefile.lean`, which the previous scan passed. `sh scripts/test_check_no_sorry.sh` (also in CI) plants every pattern in a scratch copy and checks that the scan fails on each. Commands that edit the environment are only caught reliably by the kernel replay |
| Kernel replay | `LEAN_NUM_THREADS=1 lake env leanchecker LeanStats LeanStatsTest` (also in CI) | passes in 169–372 s (six local runs across revisions: 169, 204, 254, 330, 344 and 372 s; load varies; 254 s on the current sources). Without module arguments leanchecker looks for a module named after the package (`Leanstats`) and fails, so CI passes them explicitly |
| Definitions mean what they say | `LeanStatsTest/Examples.lean` | Holm rejects all of `(0.01, 0.02, 0.04)` at `α = 0.05` while Bonferroni misses `0.02`. Holm stops at `0.03 > 0.05/2` in `(0.01, 0.03, 0.04)` and does not reject `0.04`. Holm rejects neither tied value in `(0.02, 0.02, 0.5)` (a strict-count variant would reject both; checked separately). `cpUpper 1 0.05 0 = 0.975`. `cpLower 10 0.05 10 = 0.025^(1/10)`. `0.308 < cpUpper 10 0.05 0 < 0.309` and `0.115 < cpUpper 30 0.05 0 < 0.116`. Interior: `cpUpper 2 α 1 = √(1 - α/2)` from the definition, `P(X ≥ 1) = 0.025` at `cpLower 2 0.05 1`, and `cpLower 2 0.05 1 = 1 - √0.975` from uniqueness of the root. A uniform variable on `[0, 1]` satisfies `IsValidPValue` (the hypothesis is satisfiable). For `α = -2` and p-values `(-1, -1)` Holm and the sorted procedure disagree, so the `0 ≤ α` hypothesis of the equivalence is needed |

The Clopper–Pearson closed forms agree with standard tables:
`cpLower 10 0.05 10 = 0.025^(1/10) = 0.6915`, `cpUpper 10 0.05 0 = 0.3085` and
`cpUpper 30 0.05 0 = 0.1157`. The last two are pinned to three decimals in Lean.

## 3. Build measurements (one development machine, under varying load)

| Step | Wall time |
|---|---|
| `lake update` + `lake exe cache get` (toolchain, mathlib sources, 9031 cache files) | 28 min |
| Clean build of leanstats (`rm -rf .lake/build; lake build --wfail`, mathlib cached) | 96 s (one run) |
| Incremental rebuild after editing every file | 2 min 10 s |

Disk after setup: 6.8 GB in `.lake`, 3.2 GB in the elan toolchain directory.

Most of the per-file time is loading mathlib `.olean` files. For iteration, a persistent Lean
language server, which keeps imports loaded, re-checks a file in 1–3 s.

## 4. Limitations

- **Beta-quantile form not formalised.** The Clopper–Pearson endpoints are defined as the
  infimum/supremum of the accepted parameters. Coverage alone cannot tell them from a wider
  interval, so their meaning rests on the characterisations: the closed forms for `x = 0` and
  `x = n`, and, for interior `x`, the proof that each endpoint is the unique root of its tail
  equation (the textbook definition). The identification of that root with a quantile of the
  Beta distribution is not proved.
- **The kernel replay is a separate step.** It is the only check that catches a declaration
  added without kernel checking, and `lake build` does not run it, so README and CONTRIBUTING
  list it as a local step. CI runs it after the source scan and `lake build --wfail`, on pushes
  to `main`, pull requests and manual dispatch (first green run on 2026-11-06).
- **Holm is stated for a fixed set of true nulls `I₀`.** This is the standard frequentist
  statement (it holds for every `I₀`). Data-dependent or random hypotheses are not modelled.
- **No closed-testing proof.** Holm's procedure is proved directly, not as a closed testing
  procedure, so general closed testing is not available as a by-product.
- **Ville is discrete-time.** The filtration is indexed by `ℕ` and the measure is finite.
  There is no continuous-time version and no e-process generalisation.
- **Not yet in mathlib.** The code follows mathlib style and builds with mathlib's linters, but
  it has not been reviewed by mathlib maintainers. docs/PR.md lists the expected renames.
- **Not new outside mathlib.** Holm, a one-sided Clopper–Pearson bound and Ville each exist in
  other Lean 4 projects (docs/DESIGN.md section 3). No novelty claim is made, in Lean or in
  other proof assistants, which were not searched exhaustively.
- **The interval can be empty for `α > 1`.** `cpLower_le_cpUpper` covers `α ≤ 1`; see
  docs/DESIGN.md section 2. Coverage is trivial at those levels.

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

A second review (mathematics and checks) found no correctness errors. Changes made in response:

- The README and the `Holm.lean` docstring state the equivalence with the sorted procedure for
  `α ≥ 0`, as the theorem does; an example shows it fails for `α < 0`.
- New example: a uniform p-value satisfies `IsValidPValue`.
- The source scan rejects more bypasses (section 2), and the README build step runs it with `sh`.
- The axiom audit requires the main theorems by name instead of pinning the declaration count.
- A broken table in docs/PR.md.

Not changed: monotonicity of the binomial tails and uniqueness of the endpoint roots, the
real-line distribution-function lemma and a `μ.real` corollary for measurable p-values (all
planned before upstreaming, AGENTS.md and docs/PR.md), and running CI on GitHub (metered
minutes).

A third pass handled the review findings that the earlier follow-ups had not reached:

- The tails are strictly monotone in `θ`, so the endpoints are the unique roots of the tail
  equations; new example `cpLower 2 0.05 1 = 1 - √0.975`.
- The distribution-function lemma holds for any measure on `ℝ` (`measure_cdf_le`).
- `holm_fwer_le_real`: the Holm bound as a real probability.
- The axiom sweep covers every public declaration made in a `LeanStats` module, not only those
  in the namespace (private declarations are checked through the public theorems that use them). The source scan rejects `setEnv`, `addConstAsync`, `initialize`, a
  `[leanOptions.debug]` table and a `lakefile.lean`, and a self-test checks every pattern.
- Documentation: `α ≥ 0` for the step-down equivalence in this report and docs/PR.md; DESIGN
  edge cases; machine-specific wording; 0.1.0 marked as not yet tagged; private reporting.

Both have since been done: CI first ran green on GitHub on 2026-11-06, and `v0.1.0` was tagged
on 2026-11-07.

## 6. Release audit (2026-11-06)

Nothing was rebuilt: the Lean toolchain and `.lake` are not on the audit machine, and CI was not
run. The only Lean change since the checks in section 2 is a sentence in the module docstring of
`LeanStats/ClopperPearson.lean`. The checks that did run:

- Source scan and its self-test pass.
- The statements in docs/release-notes-0.1.0.md match the sources, and every name in the
  `leanstats` column of docs/PR.md is declared. `LeanStats/` has 946 lines and 54 declarations,
  none private; `LeanStatsTest/` has 218 lines.
- The action SHAs in `ci.yml` match their tags, and the manifest's mathlib commit matches tag
  `v4.35.0`. lean-action v1.6.2 passes `leanchecker-args` to `lake env leanchecker`.

Corrected: docs/DESIGN.md said the interval is empty only for `α > 2`, and that no formalisation
was found outside mathlib. Neither holds (section 4). The first was checked numerically from the
binomial tails: `n = 2`, `x = 1` gives endpoints `0.50503` and `0.49497` at `α = 1.51`.
