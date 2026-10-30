/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
module

public import LeanStats.PValue
public import Mathlib.Data.Fintype.Card

/-!
# Holm's step-down procedure controls the family-wise error rate

Let `p : ι → ℝ` be p-values for a finite family of hypotheses. Holm's step-down procedure at
level `α` sorts the p-values, `p₍₁₎ ≤ ⋯ ≤ p₍ₘ₎`, and rejects `H₍₁₎, …, H₍ₖ₎` where `k` is the
largest index with `p₍ⱼ₎ ≤ α / (m - j + 1)` for every `j ≤ k`.

We use an equivalent description that does not mention a sorting permutation: hypothesis `i`
is rejected iff every `j` with `p j ≤ p i` satisfies `p j ≤ α / #{k | p j ≤ p k}`. Here
`#{k | p j ≤ p k}` is `m - r + 1`, where `r` is the first sorted position holding the value
`p j`. Tied p-values are therefore rejected together, which is what the sorted procedure does
for every tie-breaking order (a later tied position has a larger threshold). The equivalence
with the sorted formulation is `LeanStats.holmRejects_iff_stepDownRejects` in
`LeanStats.HolmStepDown`.

## Main definitions

* `LeanStats.HolmRejects α p i`: Holm's procedure at level `α` rejects hypothesis `i`.
* `LeanStats.BonferroniRejects α p i`: the Bonferroni procedure rejects hypothesis `i`,
  i.e. `p i ≤ α / m`.

## Main statements

* `LeanStats.HolmRejects.exists_le_div_card`: the deterministic core. If Holm rejects some
  hypothesis in a set `I₀`, then some `j ∈ I₀` has `p j ≤ α / #I₀`.
* `LeanStats.holm_fwer_le`: if the p-values of the true null hypotheses `I₀` are valid, Holm's
  procedure rejects at least one true null with probability at most `α`, whatever the joint
  dependence between the p-values (strong FWER control).
* `LeanStats.bonferroni_fwer_le`: the same for Bonferroni, as a corollary.

## References

* S. Holm, *A simple sequentially rejective multiple test procedure*, Scandinavian Journal of
  Statistics 6 (1979), 65–70.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace LeanStats

variable {ι : Type*} [Fintype ι]

/-- Holm's step-down procedure at level `α`, applied to the p-values `p`, rejects hypothesis
`i`: every hypothesis `j` whose p-value is at most `p i` passes its step-down threshold
`p j ≤ α / #{k | p j ≤ p k}`. -/
def HolmRejects (α : ℝ) (p : ι → ℝ) (i : ι) : Prop :=
  ∀ j, p j ≤ p i → p j ≤ α / #{k | p j ≤ p k}

/-- The Bonferroni procedure at level `α` rejects hypothesis `i` when `p i ≤ α / m`, where `m`
is the number of hypotheses. -/
def BonferroniRejects (α : ℝ) (p : ι → ℝ) (i : ι) : Prop :=
  p i ≤ α / Fintype.card ι

/-- Holm's rejections are closed downwards: if `i` is rejected, so is every hypothesis with a
smaller or equal p-value. -/
theorem HolmRejects.of_le {α : ℝ} {p : ι → ℝ} {i j : ι} (hi : HolmRejects α p i)
    (hji : p j ≤ p i) : HolmRejects α p j :=
  fun k hk ↦ hi k (hk.trans hji)

/-- A hypothesis rejected by Holm passes its own step-down threshold. -/
theorem HolmRejects.le_div {α : ℝ} {p : ι → ℝ} {i : ι} (hi : HolmRejects α p i) :
    p i ≤ α / #{k | p i ≤ p k} :=
  hi i le_rfl

/-- Holm's procedure is monotone in the level. -/
theorem HolmRejects.mono {α β : ℝ} (hαβ : α ≤ β) {p : ι → ℝ} {i : ι} (hi : HolmRejects α p i) :
    HolmRejects β p i :=
  fun j hj ↦ (hi j hj).trans (div_le_div_of_nonneg_right hαβ (Nat.cast_nonneg _))

/-- Holm's procedure rejects every hypothesis that Bonferroni rejects. -/
theorem BonferroniRejects.holmRejects {α : ℝ} (hα : 0 ≤ α) {p : ι → ℝ} {i : ι}
    (hi : BonferroniRejects α p i) : HolmRejects α p i := by
  intro j hj
  have hpos : (0 : ℝ) < #{k | p j ≤ p k} :=
    Nat.cast_pos.2 (card_pos.2 ⟨j, mem_filter.2 ⟨mem_univ _, le_rfl⟩⟩)
  calc p j ≤ p i := hj
    _ ≤ α / Fintype.card ι := hi
    _ ≤ α / #{k | p j ≤ p k} :=
      div_le_div_of_nonneg_left hα hpos (Nat.cast_le.2 (card_le_univ _))

/-- **Deterministic core of Holm's theorem.** If Holm's procedure at level `α ≥ 0` rejects some
hypothesis in `I₀`, then the smallest p-value in `I₀` is at most `α / #I₀`. -/
theorem HolmRejects.exists_le_div_card {α : ℝ} (hα : 0 ≤ α) {p : ι → ℝ} {I₀ : Finset ι}
    {i : ι} (hi : i ∈ I₀) (h : HolmRejects α p i) : ∃ j ∈ I₀, p j ≤ α / #I₀ := by
  obtain ⟨j, hj, hmin⟩ := I₀.exists_min_image p ⟨i, hi⟩
  refine ⟨j, hj, ?_⟩
  rcases lt_or_ge (p j) 0 with hneg | hnn
  · exact hneg.le.trans (by positivity)
  have hpos : (0 : ℝ) < #I₀ := Nat.cast_pos.2 (card_pos.2 ⟨i, hi⟩)
  have hcard : #I₀ ≤ #{k | p j ≤ p k} :=
    card_le_card fun k hk ↦ mem_filter.2 ⟨mem_univ _, hmin k hk⟩
  calc p j ≤ α / #{k | p j ≤ p k} := h j (hmin i hi)
    _ ≤ α / #I₀ := div_le_div_of_nonneg_left hα hpos (Nat.cast_le.2 hcard)

variable {Ω : Type*} [MeasurableSpace Ω]

omit [Fintype ι] in
/-- Valid p-values are almost surely positive: with probability one no `p i`, `i ∈ I₀`, is
`≤ 0`. This handles levels `α < 0`, where both procedures reject only non-positive p-values. -/
theorem measure_exists_le_zero (μ : Measure Ω) {p : ι → Ω → ℝ} {I₀ : Finset ι}
    (hp : ∀ i ∈ I₀, IsValidPValue μ (p i)) : μ {ω | ∃ i ∈ I₀, p i ω ≤ 0} = 0 := by
  refine le_antisymm ?_ bot_le
  calc μ {ω | ∃ i ∈ I₀, p i ω ≤ 0} = μ (⋃ i ∈ I₀, {ω | p i ω ≤ 0}) := by
        congr 1
        ext ω
        simp
    _ ≤ ∑ i ∈ I₀, μ {ω | p i ω ≤ 0} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ I₀, ENNReal.ofReal 0 :=
        sum_le_sum fun i hi ↦ hp i hi 0 ⟨le_rfl, zero_le_one⟩
    _ = 0 := by simp

/-- **Holm (1979).** Let `I₀` be the set of true null hypotheses and suppose each `p i`,
`i ∈ I₀`, is a valid p-value. Then Holm's step-down procedure at level `α` rejects at least one
true null hypothesis with probability at most `α`. Since `I₀` is arbitrary, this is strong
control of the family-wise error rate. No assumption is made on the joint law of the p-values,
and they need not be measurable. -/
theorem holm_fwer_le (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ι → Ω → ℝ} {I₀ : Finset ι}
    (hp : ∀ i ∈ I₀, IsValidPValue μ (p i)) (α : ℝ) :
    μ {ω | ∃ i ∈ I₀, HolmRejects α (fun j ↦ p j ω) i} ≤ ENNReal.ofReal α := by
  rcases lt_or_ge α 0 with hα | hα
  · refine (measure_mono (t := {ω | ∃ i ∈ I₀, p i ω ≤ 0}) ?_).trans
      ((measure_exists_le_zero μ hp).trans_le bot_le)
    rintro ω ⟨i, hi, h⟩
    exact ⟨i, hi, h.le_div.trans (div_nonpos_of_nonpos_of_nonneg hα.le (Nat.cast_nonneg _))⟩
  rcases I₀.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpos : (0 : ℝ) < #I₀ := Nat.cast_pos.2 (card_pos.2 hne)
  calc μ {ω | ∃ i ∈ I₀, HolmRejects α (fun j ↦ p j ω) i}
      ≤ μ (⋃ j ∈ I₀, {ω | p j ω ≤ α / #I₀}) := by
        refine measure_mono fun ω ⟨i, hi, h⟩ ↦ ?_
        obtain ⟨j, hj, hle⟩ := h.exists_le_div_card hα hi
        exact Set.mem_biUnion hj hle
    _ ≤ ∑ j ∈ I₀, μ {ω | p j ω ≤ α / #I₀} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ I₀, ENNReal.ofReal (α / #I₀) :=
        sum_le_sum fun j hj ↦ (hp j hj).measure_le_le (by positivity)
    _ = ENNReal.ofReal α := by
        rw [sum_const, ← ENNReal.ofReal_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ hpos.ne']

/-- **Bonferroni.** Under the hypotheses of `holm_fwer_le`, the Bonferroni procedure rejects at
least one true null hypothesis with probability at most `α`. -/
theorem bonferroni_fwer_le (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ι → Ω → ℝ}
    {I₀ : Finset ι} (hp : ∀ i ∈ I₀, IsValidPValue μ (p i)) (α : ℝ) :
    μ {ω | ∃ i ∈ I₀, BonferroniRejects α (fun j ↦ p j ω) i} ≤ ENNReal.ofReal α := by
  rcases lt_or_ge α 0 with hα | hα
  · refine (measure_mono (t := {ω | ∃ i ∈ I₀, p i ω ≤ 0}) ?_).trans
      ((measure_exists_le_zero μ hp).trans_le bot_le)
    rintro ω ⟨i, hi, h⟩
    exact ⟨i, hi, h.trans (div_nonpos_of_nonpos_of_nonneg hα.le (Nat.cast_nonneg _))⟩
  exact (measure_mono (fun _ ⟨i, hi, h⟩ ↦ ⟨i, hi, h.holmRejects hα⟩ :
    {ω | ∃ i ∈ I₀, BonferroniRejects α (fun j ↦ p j ω) i} ⊆
      {ω | ∃ i ∈ I₀, HolmRejects α (fun j ↦ p j ω) i})).trans (holm_fwer_le μ hp α)

end LeanStats
