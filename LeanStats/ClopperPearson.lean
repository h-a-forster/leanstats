/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.HasLaw
public import Mathlib.Order.CompleteLatticeIntervals

/-!
# Coverage of the Clopper–Pearson interval

For `X ~ Bin(n, p)` and a level `α`, the Clopper–Pearson interval is obtained by inverting two
one-sided binomial tests of size `α / 2`:

* the lower bound `cpLower n α x` is the infimum of the `θ ∈ [0, 1]` for which
  `P_θ(X ≥ x) ≥ α / 2`;
* the upper bound `cpUpper n α x` is the supremum of the `θ ∈ [0, 1]` for which
  `P_θ(X ≤ x) ≥ α / 2`.

The tails are continuous in `θ`, so for `1 ≤ x ≤ n` and `0 < α ≤ 2` the lower bound is the
smallest root of `P_θ(X ≥ x) = α / 2`: the tail equals `α / 2` there and is smaller for every
smaller `θ`. The same holds for the upper bound and `P_θ(X ≤ x)` when `x < n`. The tails are
also increasing (resp. decreasing), which makes the root unique and equal to the `α / 2`
quantile of `Beta(x, n - x + 1)`; that last step is not formalised here. The coverage proof
does not depend on how the endpoints are computed, only on the fact that they bound the
accepted parameters.

The bounds take values in `unitInterval`, which is a complete lattice, so the infimum and
supremum always exist. The interval is the closed interval `Set.Icc (cpLower n α x)
(cpUpper n α x)` in `unitInterval`.

## Main statements

* `LeanStats.measure_setOf_measure_Iic_le` and `LeanStats.measure_setOf_measure_Ici_le`: for
  any measure `ν` on a countable linear order, `ν {x | ν (Iic x) ≤ t} ≤ t` (the distribution
  function evaluated at the observation is super-uniform), and the same for upper tails.
* `LeanStats.binomial_clopperPearson_not_mem_le`: for every `p ∈ [0, 1]`, the interval misses
  `p` with probability at most `α`.
* `LeanStats.one_sub_le_binomial_clopperPearson`: coverage is at least `1 - α`, for every `n`
  and every `p ∈ [0, 1]`.
* `LeanStats.HasLaw.one_sub_le_clopperPearson`: the same for any random variable with law
  `Bin(n, p)`.
* `LeanStats.binomial_real_Ici_cpLower` and `LeanStats.binomial_real_Iic_cpUpper`: the
  endpoints solve the tail equations `P_θ(X ≥ x) = α / 2` and `P_θ(X ≤ x) = α / 2`.
* `LeanStats.cpLower_le_cpUpper`: for `α ≤ 1` the interval is non-empty.

## References

* C. J. Clopper and E. S. Pearson, *The use of confidence or fiducial limits illustrated in
  the case of the binomial*, Biometrika 26 (1934), 404–413.
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory Function
open scoped ENNReal unitInterval

namespace LeanStats

section Tail

variable {β : Type*} [LinearOrder β] [Countable β] [MeasurableSpace β]

/-- For any measure `ν` on a countable linear order, `ν {x | ν (Iic x) ≤ t} ≤ t`. In
probabilistic terms, if `F` is the distribution function of `X` then `P(F(X) ≤ t) ≤ t`. -/
theorem measure_setOf_measure_Iic_le (ν : Measure β) (t : ℝ≥0∞) :
    ν {x | ν (Iic x) ≤ t} ≤ t := by
  set A := {x | ν (Iic x) ≤ t}
  have hd : DirectedOn ((· ⊆ ·) on Iic) A := by
    intro x hx y hy
    rcases le_total x y with h | h
    · exact ⟨y, hy, Iic_subset_Iic.2 h, subset_rfl⟩
    · exact ⟨x, hx, subset_rfl, Iic_subset_Iic.2 h⟩
  calc ν A ≤ ν (⋃ x ∈ A, Iic x) := measure_mono fun x hx ↦ mem_biUnion hx (mem_Iic.2 le_rfl)
    _ = ⨆ x ∈ A, ν (Iic x) := measure_biUnion_eq_iSup A.to_countable hd
    _ ≤ t := iSup₂_le fun _ hx ↦ hx

/-- For any measure `ν` on a countable linear order, `ν {x | ν (Ici x) ≤ t} ≤ t`. -/
theorem measure_setOf_measure_Ici_le (ν : Measure β) (t : ℝ≥0∞) :
    ν {x | ν (Ici x) ≤ t} ≤ t := by
  set A := {x | ν (Ici x) ≤ t}
  have hd : DirectedOn ((· ⊆ ·) on Ici) A := by
    intro x hx y hy
    rcases le_total x y with h | h
    · exact ⟨x, hx, subset_rfl, Ici_subset_Ici.2 h⟩
    · exact ⟨y, hy, Ici_subset_Ici.2 h, subset_rfl⟩
  calc ν A ≤ ν (⋃ x ∈ A, Ici x) := measure_mono fun x hx ↦ mem_biUnion hx (mem_Ici.2 le_rfl)
    _ = ⨆ x ∈ A, ν (Ici x) := measure_biUnion_eq_iSup A.to_countable hd
    _ ≤ t := iSup₂_le fun _ hx ↦ hx

end Tail

/-- The Clopper–Pearson lower confidence bound at level `α` after observing `x` successes in
`n` trials: the infimum of the `θ ∈ [0, 1]` with `P_θ(X ≥ x) ≥ α / 2`, `X ~ Bin(n, θ)`. -/
noncomputable def cpLower (n : ℕ) (α : ℝ) (x : ℕ) : I :=
  sInf {θ : I | α / 2 ≤ Bin(n, θ).real (Ici x)}

/-- The Clopper–Pearson upper confidence bound at level `α` after observing `x` successes in
`n` trials: the supremum of the `θ ∈ [0, 1]` with `P_θ(X ≤ x) ≥ α / 2`, `X ~ Bin(n, θ)`. -/
noncomputable def cpUpper (n : ℕ) (α : ℝ) (x : ℕ) : I :=
  sSup {θ : I | α / 2 ≤ Bin(n, θ).real (Iic x)}

/-- The Clopper–Pearson confidence interval `[cpLower n α x, cpUpper n α x] ⊆ [0, 1]`. -/
noncomputable def clopperPearson (n : ℕ) (α : ℝ) (x : ℕ) : Set I :=
  Icc (cpLower n α x) (cpUpper n α x)

/-- If the true parameter lies below the lower bound, the observation is in the upper tail of
size less than `α / 2`. -/
theorem binomial_Ici_le_of_lt_cpLower {n : ℕ} {α : ℝ} {p : I} {x : ℕ} (h : p < cpLower n α x) :
    Bin(n, p) (Ici x) ≤ ENNReal.ofReal (α / 2) := by
  by_contra hlt
  have : α / 2 ≤ Bin(n, p).real (Ici x) :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (not_le.1 hlt).le
  exact h.not_ge (sInf_le this)

/-- If the true parameter lies above the upper bound, the observation is in the lower tail of
size less than `α / 2`. -/
theorem binomial_Iic_le_of_cpUpper_lt {n : ℕ} {α : ℝ} {p : I} {x : ℕ} (h : cpUpper n α x < p) :
    Bin(n, p) (Iic x) ≤ ENNReal.ofReal (α / 2) := by
  by_contra hlt
  have : α / 2 ≤ Bin(n, p).real (Iic x) :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 (not_le.1 hlt).le
  exact h.not_ge (le_sSup this)

/-- **Clopper–Pearson (1934).** For every `n`, every level `α` and every `p ∈ [0, 1]`, the
Clopper–Pearson interval misses `p` with probability at most `α` under `Bin(n, p)`. -/
theorem binomial_clopperPearson_not_mem_le (n : ℕ) (α : ℝ) (p : I) :
    Bin(n, p) {x | p ∉ clopperPearson n α x} ≤ ENNReal.ofReal α := by
  set t := ENNReal.ofReal (α / 2)
  calc Bin(n, p) {x | p ∉ clopperPearson n α x}
      ≤ Bin(n, p) ({x | Bin(n, p) (Ici x) ≤ t} ∪ {x | Bin(n, p) (Iic x) ≤ t}) := by
        refine measure_mono fun x hx ↦ ?_
        simp only [clopperPearson, mem_ofPred_eq, mem_Icc, not_and_or, not_le] at hx
        rcases hx with h | h
        · exact Or.inl (binomial_Ici_le_of_lt_cpLower h)
        · exact Or.inr (binomial_Iic_le_of_cpUpper_lt h)
    _ ≤ t + t := (measure_union_le _ _).trans
        (add_le_add (measure_setOf_measure_Ici_le _ _) (measure_setOf_measure_Iic_le _ _))
    _ = ENNReal.ofReal α := by
        rcases le_total 0 α with hα | hα
        · rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]
        · simp [t, ENNReal.ofReal_of_nonpos hα, ENNReal.ofReal_of_nonpos (by linarith : α / 2 ≤ 0)]

/-- **Clopper–Pearson coverage.** For every `n`, every level `α ≥ 0` and every `p ∈ [0, 1]`,
the Clopper–Pearson interval contains `p` with probability at least `1 - α` under
`Bin(n, p)`. -/
theorem one_sub_le_binomial_clopperPearson (n : ℕ) {α : ℝ} (hα : 0 ≤ α) (p : I) :
    1 - α ≤ Bin(n, p).real {x | p ∈ clopperPearson n α x} := by
  have hmiss : Bin(n, p).real {x | p ∈ clopperPearson n α x}ᶜ ≤ α :=
    ENNReal.toReal_le_of_le_ofReal hα (binomial_clopperPearson_not_mem_le n α p)
  rw [probReal_compl_eq_one_sub (.of_discrete)] at hmiss
  linarith

/-- **Clopper–Pearson coverage for a random variable.** If `X` has law `Bin(n, p)` under a
measure `P`, then `P (p ∈ clopperPearson n α X) ≥ 1 - α`. -/
theorem HasLaw.one_sub_le_clopperPearson {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} {n : ℕ} {p : I} (hX : HasLaw X Bin(n, p) P) {α : ℝ} (hα : 0 ≤ α) :
    1 - α ≤ P.real {ω | p ∈ clopperPearson n α (X ω)} :=
  (one_sub_le_binomial_clopperPearson n hα p).trans_eq
    (hX.measureReal_eq (p := fun x ↦ p ∈ clopperPearson n α x) .of_discrete).symm

/-! ### Tail probabilities and boundary values

These lemmas tie `cpLower` and `cpUpper` to the textbook formulas. -/

/-- `Bin(n, θ)` puts no mass above `n`. -/
theorem binomial_Iic_compl (n : ℕ) (θ : I) : Bin(n, θ) (Iic n)ᶜ = 0 := by
  have h := ae_le_of_hasLaw_binomial (X := id) (P := Bin(n, θ)) ⟨aemeasurable_id, Measure.map_id⟩
  rwa [ae_iff] at h

/-- The lower tail of `Bin(n, θ)`: `P_θ(X ≤ x) = ∑_{k ≤ x} (n choose k) θ^k (1 - θ)^(n - k)`. -/
theorem binomial_real_Iic (n x : ℕ) (θ : I) :
    Bin(n, θ).real (Iic x) =
      ∑ k ∈ Finset.Iic x, (n.choose k : ℝ) * θ ^ k * (1 - θ) ^ (n - k) := by
  rw [← Finset.coe_Iic, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun k _ ↦ binomial_real_singleton n k θ

/-- The upper tail of `Bin(n, θ)`: `P_θ(X ≥ x) = ∑_{x ≤ k ≤ n} (n choose k) θ^k (1 - θ)^(n - k)`. -/
theorem binomial_real_Ici (n x : ℕ) (θ : I) :
    Bin(n, θ).real (Ici x) =
      ∑ k ∈ Finset.Icc x n, (n.choose k : ℝ) * θ ^ k * (1 - θ) ^ (n - k) := by
  rw [measureReal_def, ← measure_inter_conull (binomial_Iic_compl n θ), Ici_inter_Iic,
    ← Finset.coe_Icc, ← measureReal_def, ← sum_measureReal_singleton]
  exact Finset.sum_congr rfl fun k _ ↦ binomial_real_singleton n k θ

/-- With zero successes the lower bound is `0` (for `α ≤ 2`). -/
theorem cpLower_zero (n : ℕ) {α : ℝ} (hα : α ≤ 2) : cpLower n α 0 = 0 := by
  have h0 : (Ici 0 : Set ℕ) = univ := eq_univ_of_forall fun _ ↦ Nat.zero_le _
  have : 0 ∈ {θ : I | α / 2 ≤ Bin(n, θ).real (Ici 0)} := by
    rw [mem_ofPred_eq, h0, probReal_univ]
    linarith
  exact le_antisymm (sInf_le this) unitInterval.nonneg'

/-- With `n` successes out of `n` the upper bound is `1` (for `α ≤ 2`). -/
theorem cpUpper_self (n : ℕ) {α : ℝ} (hα : α ≤ 2) : cpUpper n α n = 1 := by
  have h1 : Bin(n, (1 : I)).real (Iic n) = 1 := by
    have h := probReal_compl_eq_one_sub (μ := Bin(n, (1 : I))) (s := Iic n) .of_discrete
    rw [measureReal_def, binomial_Iic_compl] at h
    simp at h
    linarith
  have : (1 : I) ∈ {θ : I | α / 2 ≤ Bin(n, θ).real (Iic n)} := by
    rw [mem_ofPred_eq, h1]
    linarith
  exact le_antisymm unitInterval.le_one' (le_sSup this)

/-- **Zero successes.** For `n ≥ 1` and `0 ≤ α ≤ 2` the upper bound after observing no
successes is `1 - (α / 2) ^ (1 / n)`. -/
theorem coe_cpUpper_zero {n : ℕ} (hn : 0 < n) {α : ℝ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) :
    (cpUpper n α 0 : ℝ) = 1 - (α / 2) ^ (n⁻¹ : ℝ) := by
  set c := (α / 2) ^ (n⁻¹ : ℝ)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by linarith) _
  have hc1 : c ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by positivity)
  have hS : {θ : I | α / 2 ≤ Bin(n, θ).real (Iic 0)} =
      Iic ⟨1 - c, by constructor <;> linarith⟩ := by
    ext θ
    have hθ : 0 ≤ 1 - (θ : ℝ) := unitInterval.one_sub_nonneg θ
    rw [mem_ofPred_eq, mem_Iic, binomial_real_Iic, ← Subtype.coe_le_coe]
    rw [show Finset.Iic 0 = {0} by ext; simp, Finset.sum_singleton]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero]
    rw [← Real.rpow_natCast, ← Real.rpow_inv_le_iff_of_pos (by linarith) hθ (by positivity)]
    constructor <;> intro h <;> linarith
  rw [cpUpper, hS, csSup_Iic]

/-- **All successes.** For `n ≥ 1` and `0 ≤ α ≤ 2` the lower bound after observing `n`
successes out of `n` is `(α / 2) ^ (1 / n)`. -/
theorem coe_cpLower_self {n : ℕ} (hn : 0 < n) {α : ℝ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) :
    (cpLower n α n : ℝ) = (α / 2) ^ (n⁻¹ : ℝ) := by
  set c := (α / 2) ^ (n⁻¹ : ℝ)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by linarith) _
  have hc1 : c ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by positivity)
  have hS : {θ : I | α / 2 ≤ Bin(n, θ).real (Ici n)} = Ici ⟨c, hc0, hc1⟩ := by
    ext θ
    rw [mem_ofPred_eq, mem_Ici, binomial_real_Ici, ← Subtype.coe_le_coe, Finset.Icc_self,
      Finset.sum_singleton]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one]
    rw [← Real.rpow_natCast, ← Real.rpow_inv_le_iff_of_pos (by linarith) θ.2.1 (by positivity)]
  rw [cpLower, hS, csInf_Ici]

/-! ### Endpoints as roots of the tail equations

For `1 ≤ x ≤ n` the lower bound solves `P_θ(X ≥ x) = α / 2`, and every smaller `θ` has a
smaller tail; for `x < n` the upper bound solves `P_θ(X ≤ x) = α / 2`, and every larger `θ`
has a smaller lower tail. Only continuity of the tails in `θ` is used. -/

/-- The upper tail `θ ↦ P_θ(X ≥ x)` is continuous. -/
theorem continuous_binomial_real_Ici (n x : ℕ) :
    Continuous fun θ : I ↦ Bin(n, θ).real (Ici x) := by
  simp_rw [binomial_real_Ici]
  fun_prop

/-- The lower tail `θ ↦ P_θ(X ≤ x)` is continuous. -/
theorem continuous_binomial_real_Iic (n x : ℕ) :
    Continuous fun θ : I ↦ Bin(n, θ).real (Iic x) := by
  simp_rw [binomial_real_Iic]
  fun_prop

/-- Below the lower bound the upper tail is strictly less than `α / 2`. -/
theorem binomial_real_Ici_lt_of_lt_cpLower {n : ℕ} {α : ℝ} {x : ℕ} {θ : I}
    (h : θ < cpLower n α x) : Bin(n, θ).real (Ici x) < α / 2 :=
  lt_of_not_ge fun h' ↦ h.not_ge (sInf_le h')

/-- Above the upper bound the lower tail is strictly less than `α / 2`. -/
theorem binomial_real_Iic_lt_of_cpUpper_lt {n : ℕ} {α : ℝ} {x : ℕ} {θ : I}
    (h : cpUpper n α x < θ) : Bin(n, θ).real (Iic x) < α / 2 :=
  lt_of_not_ge fun h' ↦ h.not_ge (le_sSup h')

/-- **The lower bound is a root.** For `1 ≤ x ≤ n` and `0 < α ≤ 2`,
`P_θ(X ≥ x) = α / 2` at `θ = cpLower n α x`. -/
theorem binomial_real_Ici_cpLower {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {α : ℝ} (hα₀ : 0 < α)
    (hα₂ : α ≤ 2) : Bin(n, cpLower n α x).real (Ici x) = α / 2 := by
  have hg := continuous_binomial_real_Ici n x
  have h1 : Bin(n, (1 : I)).real (Ici x) = 1 := by
    rw [binomial_real_Ici, Finset.sum_eq_single n]
    · simp
    · intro k hk hkn
      have : n - k ≠ 0 := by have := (Finset.mem_Icc.1 hk).2; omega
      simp [this]
    · exact fun h ↦ absurd (Finset.mem_Icc.2 ⟨hxn, le_rfl⟩) h
  have h0 : Bin(n, (0 : I)).real (Ici x) = 0 := by
    rw [binomial_real_Ici]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
    simp [this]
  set c := cpLower n α x
  have hmem : α / 2 ≤ Bin(n, c).real (Ici x) :=
    (isClosed_le continuous_const hg).csInf_mem ⟨1, by simp only [mem_ofPred_eq, h1]; linarith⟩
      (OrderBot.bddBelow _)
  have hc : (0 : I) < c := by
    refine lt_of_le_of_ne unitInterval.nonneg' fun h ↦ ?_
    rw [← h, h0] at hmem
    linarith
  have hle : c ∈ {θ : I | Bin(n, θ).real (Ici x) ≤ α / 2} :=
    closure_minimal (s := Iio c) (fun θ hθ ↦ (binomial_real_Ici_lt_of_lt_cpLower hθ).le)
      (isClosed_le hg continuous_const)
      (by rw [closure_Iio' (a := c) ⟨0, hc⟩]; exact mem_Iic.2 le_rfl)
  exact le_antisymm hle hmem

/-- **The upper bound is a root.** For `x < n` and `0 < α ≤ 2`, `P_θ(X ≤ x) = α / 2` at
`θ = cpUpper n α x`. -/
theorem binomial_real_Iic_cpUpper {n x : ℕ} (hxn : x < n) {α : ℝ} (hα₀ : 0 < α)
    (hα₂ : α ≤ 2) : Bin(n, cpUpper n α x).real (Iic x) = α / 2 := by
  have hg := continuous_binomial_real_Iic n x
  have h0 : Bin(n, (0 : I)).real (Iic x) = 1 := by
    rw [binomial_real_Iic, Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have h1 : Bin(n, (1 : I)).real (Iic x) = 0 := by
    rw [binomial_real_Iic]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have : n - k ≠ 0 := by have := Finset.mem_Iic.1 hk; omega
    simp [this]
  set c := cpUpper n α x
  have hmem : α / 2 ≤ Bin(n, c).real (Iic x) :=
    (isClosed_le continuous_const hg).csSup_mem ⟨0, by simp only [mem_ofPred_eq, h0]; linarith⟩
      (OrderTop.bddAbove _)
  have hc : c < 1 := by
    refine lt_of_le_of_ne unitInterval.le_one' fun h ↦ ?_
    rw [h, h1] at hmem
    linarith
  have hle : c ∈ {θ : I | Bin(n, θ).real (Iic x) ≤ α / 2} :=
    closure_minimal (s := Ioi c) (fun θ hθ ↦ (binomial_real_Iic_lt_of_cpUpper_lt hθ).le)
      (isClosed_le hg continuous_const)
      (by rw [closure_Ioi' (a := c) ⟨1, hc⟩]; exact mem_Ici.2 le_rfl)
  exact le_antisymm hle hmem

/-- For `α ≤ 1` the lower bound is at most the upper bound, so the interval is non-empty. -/
theorem cpLower_le_cpUpper (n : ℕ) {α : ℝ} (hα : α ≤ 1) (x : ℕ) :
    cpLower n α x ≤ cpUpper n α x := by
  by_contra! h
  obtain ⟨θ, hu, hl⟩ := exists_between h
  have h1 : 1 ≤ Bin(n, θ).real (Iic x) + Bin(n, θ).real (Ici x) := by
    rw [← probReal_univ (μ := Bin(n, θ)), ← Iic_union_Ici (a := x)]
    exact measureReal_union_le _ _
  linarith [binomial_real_Ici_lt_of_lt_cpLower hl, binomial_real_Iic_lt_of_cpUpper_lt hu]

end LeanStats
