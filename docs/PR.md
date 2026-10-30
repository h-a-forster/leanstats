# Draft: upstreaming to mathlib

This is a plan for splitting leanstats into mathlib pull requests. Mathlib prefers small PRs
that each add one coherent piece with its API, so the order below goes from general measure
theory to statistics. Nothing here has been submitted yet.

## Changes needed for any PR

- **Module system.** Mathlib files start with `module`, use `public import`, and wrap the
  contents in `public section`; definitions whose bodies other files unfold need `@[expose]`.
- **Licence header.** Mathlib requires the Apache 2.0 header
  (`Released under Apache 2.0 license as described in the file LICENSE.`) and real author
  names. leanstats is MIT; the authors relicense their own code when contributing.
- **Namespaces.** Replace `LeanStats` with the mathlib namespace listed per item.
- **Style.** The files already build with `weak.linter.mathlibStandardSet = true`. Run
  `lake exe lint-style` and `#lint` in a mathlib checkout before opening a PR.

## PR 1: super-uniformity of distribution functions on countable orders

File: `Mathlib/MeasureTheory/Measure/Continuity.lean`, next to `measure_biUnion_eq_iSup`.

| leanstats | proposed mathlib name |
|---|---|
| `measure_setOf_measure_Iic_le` | `MeasureTheory.measure_setOf_measure_Iic_le` |
| `measure_setOf_measure_Ici_le` | `MeasureTheory.measure_setOf_measure_Ici_le` |

Reviewers will likely ask for the version on `ℝ` (`P(F(X) ≤ t) ≤ t` for
`ProbabilityTheory.cdf`), which needs right-continuity of the cdf (or the fact that
`{x | ν (Iic x) ≤ t}` is an initial segment). Prove it before opening this PR, in
`Mathlib/Probability/CDF.lean`, and keep the countable version as a corollary.

## PR 2: binomial tails

File: `Mathlib/Probability/Distributions/Binomial.lean`.

| leanstats | proposed mathlib name |
|---|---|
| `binomial_Iic_compl` | `ProbabilityTheory.binomial_compl_Iic` |
| `binomial_real_Iic` | `ProbabilityTheory.binomial_real_Iic` |
| `binomial_real_Ici` | `ProbabilityTheory.binomial_real_Ici` |

| `continuous_binomial_real_Ici`, `continuous_binomial_real_Iic` | `ProbabilityTheory.continuous_binomial_real_Ici`, `ProbabilityTheory.continuous_binomial_real_Iic` |

Natural additions for the same PR: monotonicity of `θ ↦ Bin(n, θ).real (Ici x)` (stochastic
ordering in `θ`), which makes the Clopper–Pearson endpoint roots unique and gives the
Beta-quantile form.

## PR 3: valid p-values and Holm's procedure

New directory `Mathlib/Probability/HypothesisTesting/`. Mathlib has no hypothesis-testing files
yet, so this PR will need a design discussion on Zulip (#mathlib4 > probability) first. That
thread should also settle the outer-measure convention of `IsValidPValue` (it agrees with the
usual definition for measurable `p`) and whether to add a `Measure.real` form for measurable
p-values.

`Mathlib/Probability/HypothesisTesting/PValue.lean`:

| leanstats | proposed mathlib name |
|---|---|
| `IsValidPValue` | `ProbabilityTheory.IsSuperUniform` (the property is about a random variable, not a test; "valid p-value" goes in the docstring) |
| `IsValidPValue.measure_le_le` | `ProbabilityTheory.IsSuperUniform.measure_le_le` |

`Mathlib/Probability/HypothesisTesting/Holm.lean`:

| leanstats | proposed mathlib name |
|---|---|
| `HolmRejects` | `ProbabilityTheory.HolmRejects` |
| `BonferroniRejects` | `ProbabilityTheory.BonferroniRejects` |
| `HolmRejects.of_le`, `.le_div`, `.mono` | same, under `ProbabilityTheory.HolmRejects` |
| `BonferroniRejects.holmRejects` | `ProbabilityTheory.BonferroniRejects.holmRejects` |
| `HolmRejects.exists_le_div_card` | `ProbabilityTheory.HolmRejects.exists_le_div_card` |
| `holm_fwer_le` | `ProbabilityTheory.measure_exists_holmRejects_le` (mathlib names describe the statement) |
| `bonferroni_fwer_le` | `ProbabilityTheory.measure_exists_bonferroniRejects_le` |
| `StepDownRejects` | `ProbabilityTheory.StepDownRejects` |
| `holmRejects_iff_stepDownRejects` | `ProbabilityTheory.holmRejects_iff_stepDownRejects` |
| `exists_monotone_comp_equiv` | `Tuple.exists_monotone_comp_equiv` in `Mathlib/Data/Fin/Tuple/Sort.lean` |
| `measure_exists_le_zero` | private, or `ProbabilityTheory.IsSuperUniform.measure_le_zero` for one p-value |
| `card_sub_le_card_filter` | private, or inlined |

## PR 4: Clopper–Pearson

`Mathlib/Probability/HypothesisTesting/ClopperPearson.lean` (depends on PRs 1 and 2).

| leanstats | proposed mathlib name |
|---|---|
| `cpLower`, `cpUpper` | `ProbabilityTheory.clopperPearsonLower`, `ProbabilityTheory.clopperPearsonUpper` (mathlib avoids abbreviations in names) |
| `clopperPearson` | `ProbabilityTheory.clopperPearson` |
| `binomial_Ici_le_of_lt_cpLower` | `ProbabilityTheory.binomial_Ici_le_of_lt_clopperPearsonLower` |
| `binomial_Iic_le_of_cpUpper_lt` | `ProbabilityTheory.binomial_Iic_le_of_clopperPearsonUpper_lt` |
| `binomial_clopperPearson_not_mem_le` | `ProbabilityTheory.binomial_setOf_notMem_clopperPearson_le` (mathlib now spells `∉` as `notMem`) |
| `one_sub_le_binomial_clopperPearson` | `ProbabilityTheory.one_sub_le_binomial_real_setOf_mem_clopperPearson` |
| `HasLaw.one_sub_le_clopperPearson` | `ProbabilityTheory.HasLaw.one_sub_le_measureReal_mem_clopperPearson` |
| `cpLower_zero`, `cpUpper_self` | `ProbabilityTheory.clopperPearsonLower_zero`, `ProbabilityTheory.clopperPearsonUpper_self` |
| `coe_cpUpper_zero`, `coe_cpLower_self` | `ProbabilityTheory.coe_clopperPearsonUpper_zero`, `ProbabilityTheory.coe_clopperPearsonLower_self` |
| `binomial_real_Ici_lt_of_lt_cpLower`, `binomial_real_Iic_lt_of_cpUpper_lt` | `ProbabilityTheory.binomial_real_Ici_lt_of_lt_clopperPearsonLower`, `ProbabilityTheory.binomial_real_Iic_lt_of_clopperPearsonUpper_lt` |
| `binomial_real_Ici_cpLower`, `binomial_real_Iic_cpUpper` | `ProbabilityTheory.binomial_real_Ici_clopperPearsonLower`, `ProbabilityTheory.binomial_real_Iic_clopperPearsonUpper` |
| `cpLower_le_cpUpper` | `ProbabilityTheory.clopperPearsonLower_le_clopperPearsonUpper` |

## PR 5: Ville's inequality

File: `Mathlib/Probability/Martingale/OptionalStopping.lean`, after `maximal_ineq`.

| leanstats | proposed mathlib name |
|---|---|
| `Supermartingale.mul_measure_exists_le_le` | `MeasureTheory.Supermartingale.mul_measure_exists_le_le` |
| `Supermartingale.mul_measure_exists_le` | `MeasureTheory.Supermartingale.mul_measure_exists_le` (docstring: "Ville's inequality") |
| `Supermartingale.measure_exists_le_le_div` | `MeasureTheory.Supermartingale.measure_exists_le_le_div` |
| `Supermartingale.mul_measure_le_iSup` | `MeasureTheory.Supermartingale.mul_measure_le_iSup` |

Once these are in the `MeasureTheory.Supermartingale` namespace, dot notation
(`hM.mul_measure_exists_le hnonneg ε`) works. In leanstats it does not, because the lemmas
live in `LeanStats`.

## Suggested PR description (PR 3)

> feat(Probability/HypothesisTesting): super-uniform p-values and Holm's procedure
>
> Adds `ProbabilityTheory.IsSuperUniform` and Holm's step-down procedure, with
> family-wise error control at level `α` under arbitrary dependence
> (`measure_exists_holmRejects_le`), Bonferroni as a corollary, and the equivalence of the
> sort-free definition with the textbook sorted procedure for every tie-breaking order.
