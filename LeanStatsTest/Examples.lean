/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
module

public import LeanStats

/-!
# Worked examples

Concrete instances that pin down the definitions: they would fail if `HolmRejects`,
`BonferroniRejects` or the Clopper–Pearson bounds encoded a different procedure.
-/

public section

open LeanStats Finset ProbabilityTheory

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

/-- Tied p-values share a threshold: in `(0.02, 0.02, 0.5)` both tied values face
`0.05 / #{k | 0.02 ≤ p k} = 0.05 / 3 < 0.02`, so Holm rejects nothing, as the sorted procedure
does for either tie-breaking order. A variant counting `#{k | p j < p k} + 1` would use
`0.05 / 2` and reject. -/
example : ¬ HolmRejects 0.05 ![0.02, 0.02, 0.5] 0 := by
  intro h
  have := h.le_div
  simp only [card_filter_fin_three] at this
  norm_num at this

/-- One trial, no success, `α = 0.05`: the Clopper–Pearson upper bound is `1 - 0.025 = 0.975`. -/
example : (cpUpper 1 0.05 0 : ℝ) = 0.975 := by
  rw [coe_cpUpper_zero one_pos (by norm_num) (by norm_num)]
  norm_num

/-- Ten trials, all successes, `α = 0.05`: the lower bound is `0.025 ^ (1 / 10) ≈ 0.6915`. -/
example : (cpLower 10 0.05 10 : ℝ) = 0.025 ^ ((10 : ℝ)⁻¹) := by
  rw [coe_cpLower_self (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Ten trials, no success, `α = 0.05`: the upper bound is `1 - 0.025 ^ (1 / 10) ≈ 0.3085`. -/
example : 0.308 < (cpUpper 10 0.05 0 : ℝ) ∧ (cpUpper 10 0.05 0 : ℝ) < 0.309 := by
  rw [coe_cpUpper_zero (by norm_num) (by norm_num) (by norm_num)]
  push_cast
  have hhi : (0.05 / 2 : ℝ) ^ (10 : ℝ)⁻¹ < 0.692 := by
    rw [Real.rpow_inv_lt_iff_of_pos (by norm_num) (by norm_num) (by norm_num),
      show (10 : ℝ) = (10 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  have hlo : 0.691 < (0.05 / 2 : ℝ) ^ (10 : ℝ)⁻¹ := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num),
      show (10 : ℝ) = (10 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  constructor <;> linarith

/-- Thirty trials, no success, `α = 0.05`: the upper bound is `1 - 0.025 ^ (1 / 30) ≈ 0.1157`. -/
example : 0.115 < (cpUpper 30 0.05 0 : ℝ) ∧ (cpUpper 30 0.05 0 : ℝ) < 0.116 := by
  rw [coe_cpUpper_zero (by norm_num) (by norm_num) (by norm_num)]
  push_cast
  have hhi : (0.05 / 2 : ℝ) ^ (30 : ℝ)⁻¹ < 0.885 := by
    rw [Real.rpow_inv_lt_iff_of_pos (by norm_num) (by norm_num) (by norm_num),
      show (30 : ℝ) = (30 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  have hlo : 0.884 < (0.05 / 2 : ℝ) ^ (30 : ℝ)⁻¹ := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by norm_num),
      show (30 : ℝ) = (30 : ℕ) by norm_num, Real.rpow_natCast]
    norm_num
  constructor <;> linarith

/-- An interior observation, straight from the definition: one success in two trials gives
`P_θ(X ≤ 1) = 1 - θ ^ 2`, so the upper bound is `√(1 - α / 2)` (`≈ 0.9874` at `α = 0.05`). -/
example {α : ℝ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) : (cpUpper 2 α 1 : ℝ) = √(1 - α / 2) := by
  have hS : {θ : unitInterval | α / 2 ≤ Bin(2, θ).real (Set.Iic 1)} =
      Set.Iic ⟨√(1 - α / 2), Real.sqrt_nonneg _,
        Real.sqrt_le_one.2 (by linarith)⟩ := by
    ext θ
    rw [Set.mem_ofPred_eq, Set.mem_Iic, binomial_real_Iic, ← Subtype.coe_le_coe,
      Real.le_sqrt θ.2.1 (by linarith)]
    rw [show Finset.Iic 1 = {0, 1} by decide, Finset.sum_pair zero_ne_one]
    norm_num
    constructor <;> intro h <;> nlinarith
  rw [cpUpper, hS, csSup_Iic]

/-- The lower bound solves the upper-tail equation at an interior observation. -/
example : Bin(2, cpLower 2 0.05 1).real (Set.Ici 1) = 0.025 := by
  rw [binomial_real_Ici_cpLower le_rfl (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end LeanStatsTest
