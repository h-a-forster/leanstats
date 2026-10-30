/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Valid p-values

A real-valued random variable `p` is a *valid* (or *super-uniform*) p-value for a null
hypothesis under the probability measure `μ` if `μ {p ≤ t} ≤ t` for every `t ∈ [0, 1]`. No
measurability, independence or continuity is assumed: the definition is stated with the
(outer) measure of the event, so it applies verbatim to discrete and randomised tests.

## Main definitions

* `LeanStats.IsValidPValue μ p`: `p` is super-uniform under `μ`.

## Main statements

* `LeanStats.IsValidPValue.measure_le_le`: under a probability measure the bound
  `μ {p ≤ t} ≤ t` extends to every `t ≥ 0`.
-/

open MeasureTheory
open scoped ENNReal

namespace LeanStats

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A random variable `p : Ω → ℝ` is a *valid p-value* under `μ` if it is super-uniform:
`μ {ω | p ω ≤ t} ≤ t` for every `t ∈ [0, 1]`. -/
def IsValidPValue (μ : Measure Ω) (p : Ω → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, μ {ω | p ω ≤ t} ≤ ENNReal.ofReal t

/-- Under a probability measure, a valid p-value satisfies `μ {p ≤ t} ≤ t` for all `t ≥ 0`
(for `t > 1` the bound is trivial). -/
theorem IsValidPValue.measure_le_le {μ : Measure Ω} [IsProbabilityMeasure μ] {p : Ω → ℝ}
    (hp : IsValidPValue μ p) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | p ω ≤ t} ≤ ENNReal.ofReal t := by
  rcases le_total t 1 with h1 | h1
  · exact hp t ⟨ht, h1⟩
  · calc μ {ω | p ω ≤ t} ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal t := by simpa using ENNReal.ofReal_le_ofReal h1

end LeanStats
