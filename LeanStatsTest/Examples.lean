/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
import LeanStats

/-!
# Worked examples

Concrete instances that pin down the definitions: they would fail if `HolmRejects`,
`BonferroniRejects` or the Clopper–Pearson bounds encoded a different procedure.
-/

open LeanStats Finset

namespace LeanStatsTest

/-- Counting a filter over `Fin 3` by cases, to evaluate step-down thresholds. -/
theorem card_filter_fin_three (P : Fin 3 → Prop) [DecidablePred P] :
    #{x | P x} = (if P 0 then 1 else 0) + (if P 1 then 1 else 0) + (if P 2 then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_three]

/-- Three p-values `(0.01, 0.02, 0.04)` at `α = 0.05`: the thresholds are `0.05 / 3`, `0.05 / 2`
and `0.05`, all passed, so Holm rejects every hypothesis. -/
example : ∀ i, HolmRejects 0.05 ![0.01, 0.02, 0.04] i := by
  intro i j _
  fin_cases j <;> simp only [card_filter_fin_three] <;> norm_num

/-- Bonferroni at `α = 0.05` does not reject the hypothesis with p-value `0.02 > 0.05 / 3`, which
Holm does reject (previous example). -/
example : ¬ BonferroniRejects 0.05 ![0.01, 0.02, 0.04] 1 := by
  simp [BonferroniRejects]
  norm_num

/-- Step-down stops at the first failure: for `(0.01, 0.03, 0.04)` the second-smallest p-value
fails `0.03 ≤ 0.05 / 2`, so the largest is not rejected although `0.04 ≤ 0.05 / 1`. -/
example : ¬ HolmRejects 0.05 ![0.01, 0.03, 0.04] 2 := by
  intro h
  have := h 1 (by simp; norm_num)
  simp only [card_filter_fin_three] at this
  norm_num at this

/-- The smallest p-value is rejected in the same family. -/
example : HolmRejects 0.05 ![0.01, 0.03, 0.04] 0 := by
  intro j hj
  fin_cases j
  · simp only [card_filter_fin_three]
    norm_num
  all_goals norm_num at hj

/-- One trial, no success, `α = 0.05`: the Clopper–Pearson upper bound is `1 - 0.025 = 0.975`. -/
example : (cpUpper 1 0.05 0 : ℝ) = 0.975 := by
  rw [coe_cpUpper_zero one_pos (by norm_num) (by norm_num)]
  norm_num

/-- Ten trials, all successes, `α = 0.05`: the lower bound is `0.025 ^ (1 / 10) ≈ 0.6915`. -/
example : (cpLower 10 0.05 10 : ℝ) = 0.025 ^ ((10 : ℝ)⁻¹) := by
  rw [coe_cpLower_self (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end LeanStatsTest
