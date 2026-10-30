/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Ville's inequality

For a non-negative supermartingale `M` and `ε > 0`,
`P(∃ n, M n ≥ ε) ≤ E[M 0] / ε`.
This is the time-uniform analogue of Markov's inequality and the basis of anytime-valid
inference with test supermartingales and e-processes.

The proof stops `M` at its first passage above `ε` before a horizon `n`, applies the optional
stopping theorem to the submartingale `-M`, and lets `n → ∞` by continuity from below.

## Main statements

* `LeanStats.Supermartingale.mul_measure_exists_le_le`: the finite-horizon bound
  `ε * P(∃ k ≤ n, M k ≥ ε) ≤ E[M 0]`.
* `LeanStats.Supermartingale.mul_measure_exists_le`: Ville's inequality,
  `ε * P(∃ k, M k ≥ ε) ≤ E[M 0]`.
* `LeanStats.Supermartingale.measure_exists_le_le_div`: the same, divided by `ε ≠ 0`.
* `LeanStats.Supermartingale.mul_measure_le_iSup`: the supremum form,
  `ε * P(sup_k M k ≥ ε) ≤ E[M 0]`.

## References

* J. Ville, *Étude critique de la notion de collectif*, Gauthier-Villars, Paris (1939).
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace LeanStats

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {M : ℕ → Ω → ℝ}

/-- **Finite-horizon Ville inequality.** For a non-negative supermartingale `M`, `ε ≥ 0` and a
horizon `n`, `ε * P(∃ k ≤ n, M k ≥ ε) ≤ E[M 0]`. -/
theorem Supermartingale.mul_measure_exists_le_le [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) (ε : ℝ≥0) (n : ℕ) :
    ε * μ {ω | ∃ k ≤ n, (ε : ℝ) ≤ M k ω} ≤ ENNReal.ofReal (μ[M 0]) := by
  set A := {ω | ∃ k ≤ n, (ε : ℝ) ≤ M k ω}
  set τ : Ω → WithTop ℕ := fun ω ↦ (hittingBtwn M {y : ℝ | ε ≤ y} 0 n ω : ℕ)
  have hτ : IsStoppingTime 𝒢 τ :=
    hM.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hτn : ∀ ω, τ ω ≤ n := fun ω ↦
    WithTop.coe_le_coe.2 (hittingBtwn_le (u := M) (s := {y : ℝ | ε ≤ y}) (n := 0) ω)
  have hA : MeasurableSet A := by
    have : A = ⋃ k ∈ Finset.range (n + 1), {ω | (ε : ℝ) ≤ M k ω} := by
      ext ω
      simp [A]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun k _ ↦ measurableSet_le measurable_const
      ((hM.stronglyMeasurable k).measurable.mono (𝒢.le k) le_rfl)
  have hint : Integrable (stoppedValue M τ) μ := integrable_stoppedValue ℕ hτ hM.integrable hτn
  -- The stopped process is at least `ε` on `A` and non-negative elsewhere.
  have hpt : A.indicator (fun _ ↦ (ε : ℝ)) ≤ stoppedValue M τ := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      obtain ⟨k, hk, hεk⟩ := hω
      exact stoppedValue_hittingBtwn_mem (s := {y : ℝ | ε ≤ y}) ⟨k, ⟨Nat.zero_le _, hk⟩, hεk⟩
    · rw [Set.indicator_of_notMem hω]
      exact hnonneg _ _
  have h1 : (ε : ℝ) * μ.real A ≤ μ[stoppedValue M τ] := by
    have := integral_mono ((integrable_const (ε : ℝ)).indicator hA) hint hpt
    rwa [integral_indicator_const _ hA, smul_eq_mul, mul_comm] at this
  -- Optional stopping for the submartingale `-M` between the times `0` and `τ`.
  have h2 : μ[stoppedValue M τ] ≤ μ[M 0] := by
    have := hM.neg.expected_stoppedValue_mono (isStoppingTime_const 𝒢 0) hτ
      (fun ω ↦ by simp [τ]) hτn
    have e : stoppedValue (-M) τ = -stoppedValue M τ := rfl
    simp only [stoppedValue_const, e, Pi.neg_apply, integral_neg] at this
    linarith
  calc ε * μ A = ENNReal.ofReal ((ε : ℝ) * μ.real A) := by
        rw [ENNReal.ofReal_mul ε.coe_nonneg, ENNReal.ofReal_coe_nnreal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (μ[M 0]) := ENNReal.ofReal_le_ofReal (h1.trans h2)

/-- **Ville's inequality.** For a non-negative supermartingale `M` and `ε ≥ 0`,
`ε * P(∃ k, M k ≥ ε) ≤ E[M 0]`. -/
theorem Supermartingale.mul_measure_exists_le [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) (ε : ℝ≥0) :
    ε * μ {ω | ∃ k, (ε : ℝ) ≤ M k ω} ≤ ENNReal.ofReal (μ[M 0]) := by
  have hU : {ω | ∃ k, (ε : ℝ) ≤ M k ω} = ⋃ n, {ω | ∃ k ≤ n, (ε : ℝ) ≤ M k ω} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, k, le_rfl, hk⟩, fun ⟨_, k, _, hk⟩ ↦ ⟨k, hk⟩⟩
  have hmono : Monotone fun n ↦ {ω | ∃ k ≤ n, (ε : ℝ) ≤ M k ω} :=
    fun _ _ hab _ ⟨k, hk, h⟩ ↦ ⟨k, hk.trans hab, h⟩
  rw [hU, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n ↦ Supermartingale.mul_measure_exists_le_le hM hnonneg ε n

/-- **Ville's inequality**, divided form: for a non-negative supermartingale `M` and `ε > 0`,
`P(∃ k, M k ≥ ε) ≤ E[M 0] / ε`. -/
theorem Supermartingale.measure_exists_le_le_div [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ {ω | ∃ k, (ε : ℝ) ≤ M k ω} ≤ ENNReal.ofReal (μ[M 0]) / ε := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hε)) (by simp), mul_comm]
  exact Supermartingale.mul_measure_exists_le hM hnonneg ε

/-- **Ville's inequality, supremum form.** For a non-negative supermartingale `M` and `ε ≥ 0`,
`ε * P(sup_k M k ≥ ε) ≤ E[M 0]`, the supremum taken in `[0, ∞]`. The event is larger than
`{∃ k, M k ≥ ε}`: it also contains the paths whose supremum `ε` is approached but not attained. -/
theorem Supermartingale.mul_measure_le_iSup [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ k, ENNReal.ofReal (M k ω)} ≤ ENNReal.ofReal (μ[M 0]) := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_
  lift a to ℝ≥0 using ha.ne_top
  rw [← mul_assoc, ← ENNReal.coe_mul]
  refine le_trans (mul_le_mul_right (measure_mono fun ω hω ↦ ?_) _)
    (Supermartingale.mul_measure_exists_le hM hnonneg (a * ε))
  rcases eq_or_ne ε 0 with rfl | hε
  · exact ⟨0, by simpa using hnonneg 0 ω⟩
  have hlt : ((a * ε : ℝ≥0) : ℝ≥0∞) < ⨆ k, ENNReal.ofReal (M k ω) :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (mul_lt_of_lt_one_left (pos_iff_ne_zero.2 hε)
      (ENNReal.coe_lt_one_iff.1 ha))) hω
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hlt
  exact ⟨k, ((ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top).1 hk).le⟩

end LeanStats
