/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
module

public import LeanStats.Holm
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Holm's procedure as a sorted step-down procedure

This file shows that `LeanStats.HolmRejects` is the textbook step-down procedure. Fix an
ordering `σ : Fin m ≃ ι` of the hypotheses under which the p-values are non-decreasing (any
tie-breaking is allowed). Using `0`-based positions, the step-down procedure rejects the
hypothesis at position `r` iff `p (σ s) ≤ α / (m - s)` for every position `s ≤ r`.

## Main definitions

* `LeanStats.StepDownRejects α p σ r`: the sorted step-down procedure with ordering `σ` rejects
  the hypothesis at position `r`.

## Main statements

* `LeanStats.exists_monotone_comp_equiv`: every family of p-values admits a sorting order.
* `LeanStats.holmRejects_iff_stepDownRejects`: for every sorting order and `α ≥ 0`, the
  step-down procedure and `HolmRejects` reject the same hypotheses. In particular the
  step-down procedure does not depend on how ties are broken.
-/

@[expose] public section

open Finset

namespace LeanStats

variable {ι : Type*} [Fintype ι]

/-- The sorted step-down procedure at level `α` with ordering `σ` rejects the hypothesis at
(`0`-based) position `r` iff every position `s ≤ r` passes `p (σ s) ≤ α / (m - s)`, where `m` is
the number of hypotheses. -/
def StepDownRejects (α : ℝ) (p : ι → ℝ) (σ : Fin (Fintype.card ι) ≃ ι)
    (r : Fin (Fintype.card ι)) : Prop :=
  ∀ s ≤ r, p (σ s) ≤ α / (Fintype.card ι - s : ℕ)

/-- Every family of p-values can be listed in non-decreasing order. -/
theorem exists_monotone_comp_equiv (p : ι → ℝ) :
    ∃ σ : Fin (Fintype.card ι) ≃ ι, Monotone (p ∘ σ) := by
  set e := Fintype.equivFin ι
  exact ⟨(Tuple.sort (p ∘ e.symm)).trans e.symm, Tuple.monotone_sort (p ∘ e.symm)⟩

/-- In a non-decreasing ordering, the hypotheses whose p-value is at least that at position
`s` include all positions `≥ s`, so there are at least `m - s` of them. -/
theorem card_sub_le_card_filter {p : ι → ℝ} {σ : Fin (Fintype.card ι) ≃ ι}
    (hσ : Monotone (p ∘ σ)) (s : Fin (Fintype.card ι)) :
    Fintype.card ι - s ≤ #{k | p (σ s) ≤ p k} := by
  rw [← Fin.card_Ici]
  refine card_le_card_of_injOn σ (fun t ht ↦ ?_) σ.injective.injOn
  simp only [coe_Ici, Set.mem_Ici, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
  exact hσ ht

/-- **Holm's procedure is the sorted step-down procedure.** For any ordering `σ` under which the
p-values are non-decreasing and any `α ≥ 0`, the step-down procedure rejects the hypothesis at
position `r` iff `HolmRejects` rejects `σ r`. -/
theorem holmRejects_iff_stepDownRejects {α : ℝ} (hα : 0 ≤ α) {p : ι → ℝ}
    {σ : Fin (Fintype.card ι) ≃ ι} (hσ : Monotone (p ∘ σ)) (r : Fin (Fintype.card ι)) :
    HolmRejects α p (σ r) ↔ StepDownRejects α p σ r := by
  constructor
  · intro h s hs
    have hle := h (σ s) (hσ hs)
    rcases lt_or_ge (p (σ s)) 0 with hneg | hnn
    · exact hneg.le.trans (by positivity)
    have hpos : (0 : ℝ) < (Fintype.card ι - s : ℕ) := by
      have := s.2
      exact Nat.cast_pos.2 (by omega)
    exact hle.trans (div_le_div_of_nonneg_left hα hpos
      (Nat.cast_le.2 (card_sub_le_card_filter hσ s)))
  · intro h j hj
    -- `s₀` is the first position whose p-value is at least `p j`.
    set F : Finset (Fin (Fintype.card ι)) := {t | p j ≤ p (σ t)} with hF
    have hjF : σ.symm j ∈ F := by simp [F]
    set s₀ := F.min' ⟨_, hjF⟩
    have hs₀F : s₀ ∈ F := F.min'_mem _
    have hs₀r : s₀ ≤ r := F.min'_le r (by simpa [F] using hj)
    have hps₀ : p (σ s₀) = p j := by
      refine le_antisymm ?_ (by simpa [F] using hs₀F)
      simpa using hσ (F.min'_le _ hjF)
    have hcard : #{k | p j ≤ p k} = Fintype.card ι - s₀ := by
      rw [← Fin.card_Ici, ← hps₀]
      refine card_nbij σ.symm (fun k hk ↦ ?_) σ.symm.injective.injOn (fun t ht ↦ ?_)
      · have hk' : p j ≤ p k := hps₀ ▸ (mem_filter.1 hk).2
        exact mem_Ici.2 (F.min'_le _ (by simpa [F] using hk'))
      · exact ⟨σ t, by simpa using hσ (mem_Ici.1 ht), by simp⟩
    rw [hcard, ← hps₀]
    exact h s₀ hs₀r

end LeanStats
