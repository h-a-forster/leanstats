# leanstats 0.1.0

First release (2026-10-30). Not tagged yet: the tag follows the first green CI run on
GitHub, which needs the owner (metered minutes). Lean v4.35.0, mathlib tag `v4.35.0`
(commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, locked in `lake-manifest.json`).

Machine-checked proofs of Holm's family-wise error control (with Bonferroni and the
equivalence with the sorted step-down procedure), Clopper–Pearson coverage, and Ville's
inequality: 946 lines in `LeanStats/` (54 definitions and theorems), plus 218 lines of
worked examples and the axiom audit in `LeanStatsTest/`. There is no executable code and no
data.

## Axioms and checks

Every public declaration made in a `LeanStats` module depends only on `propext`,
`Classical.choice` and `Quot.sound` (private lemmas are covered through the theorems that
use them). `#audit_leanstats_axioms` in `LeanStatsTest/Axioms.lean` checks this on every
build for all 57 declarations (54 source declarations and 3 equation lemmas) and requires
15 main theorems by name. There is no
`sorry`, `admit`, `native_decide` or new `axiom`; `scripts/check_no_sorry.sh` also rejects
kernel bypasses and environment edits, and `scripts/test_check_no_sorry.sh` plants each
pattern to check that the scan catches it.

The last local runs passed `lake build --wfail` (3146 jobs, mathlib's standard linters),
the axiom audit, the source scan with its self-test, and the leanchecker kernel replay
(`LEAN_NUM_THREADS=1 lake env leanchecker LeanStats LeanStatsTest`, 254 s on these
sources). Measurements and the checks that were shown to fail on planted gaps are in
[REPORT.md](../REPORT.md). Nothing was rebuilt for these notes.

## What is proved

All names are in the `LeanStats` namespace. `ι` is a finite type of hypotheses
(`[Fintype ι]`), `I` is mathlib's `unitInterval`, and `Bin(n, θ)` is mathlib's
`ProbabilityTheory.binomial`. The statements below are copied from the sources.

### Valid p-values

```lean
def IsValidPValue (μ : Measure Ω) (p : Ω → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, μ {ω | p ω ≤ t} ≤ ENNReal.ofReal t
```

Measurability, continuity and independence are not assumed; for a non-measurable `p` the
measure acts as an outer measure, so hypothesis and conclusions are outer-measure bounds.
A uniform variable on `[0, 1]` satisfies the definition (`LeanStatsTest/Examples.lean`).

### Holm and Bonferroni: strong FWER control under arbitrary dependence

```lean
def HolmRejects (α : ℝ) (p : ι → ℝ) (i : ι) : Prop :=
  ∀ j, p j ≤ p i → p j ≤ α / #{k | p j ≤ p k}

def BonferroniRejects (α : ℝ) (p : ι → ℝ) (i : ι) : Prop :=
  p i ≤ α / Fintype.card ι

theorem holm_fwer_le (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ι → Ω → ℝ} {I₀ : Finset ι}
    (hp : ∀ i ∈ I₀, IsValidPValue μ (p i)) (α : ℝ) :
    μ {ω | ∃ i ∈ I₀, HolmRejects α (fun j ↦ p j ω) i} ≤ ENNReal.ofReal α

theorem holm_fwer_le_real (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ι → Ω → ℝ}
    {I₀ : Finset ι} (hp : ∀ i ∈ I₀, IsValidPValue μ (p i)) {α : ℝ} (hα : 0 ≤ α) :
    μ.real {ω | ∃ i ∈ I₀, HolmRejects α (fun j ↦ p j ω) i} ≤ α

theorem bonferroni_fwer_le (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ι → Ω → ℝ}
    {I₀ : Finset ι} (hp : ∀ i ∈ I₀, IsValidPValue μ (p i)) (α : ℝ) :
    μ {ω | ∃ i ∈ I₀, BonferroniRejects α (fun j ↦ p j ω) i} ≤ ENNReal.ofReal α
```

`I₀` is the unknown set of true nulls; the bounds hold for every `I₀` (strong control) and
every real `α`. Only the null p-values must be valid, and their joint law is arbitrary.

### Holm is the sorted step-down procedure (for `α ≥ 0`)

```lean
def StepDownRejects (α : ℝ) (p : ι → ℝ) (σ : Fin (Fintype.card ι) ≃ ι)
    (r : Fin (Fintype.card ι)) : Prop :=
  ∀ s ≤ r, p (σ s) ≤ α / (Fintype.card ι - s : ℕ)

theorem holmRejects_iff_stepDownRejects {α : ℝ} (hα : 0 ≤ α) {p : ι → ℝ}
    {σ : Fin (Fintype.card ι) ≃ ι} (hσ : Monotone (p ∘ σ)) (r : Fin (Fintype.card ι)) :
    HolmRejects α p (σ r) ↔ StepDownRejects α p σ r
```

The equivalence holds for every sorting order `σ`, so ties do not matter;
`exists_monotone_comp_equiv` shows a sorting order exists. For `α < 0` the two procedures
can differ (counterexample in `LeanStatsTest/Examples.lean`), which does not affect the
FWER bounds.

### Clopper–Pearson coverage

```lean
noncomputable def cpLower (n : ℕ) (α : ℝ) (x : ℕ) : I :=
  sInf {θ : I | α / 2 ≤ Bin(n, θ).real (Ici x)}

noncomputable def cpUpper (n : ℕ) (α : ℝ) (x : ℕ) : I :=
  sSup {θ : I | α / 2 ≤ Bin(n, θ).real (Iic x)}

noncomputable def clopperPearson (n : ℕ) (α : ℝ) (x : ℕ) : Set I :=
  Icc (cpLower n α x) (cpUpper n α x)

theorem binomial_clopperPearson_not_mem_le (n : ℕ) (α : ℝ) (p : I) :
    Bin(n, p) {x | p ∉ clopperPearson n α x} ≤ ENNReal.ofReal α

theorem one_sub_le_binomial_clopperPearson (n : ℕ) {α : ℝ} (hα : 0 ≤ α) (p : I) :
    1 - α ≤ Bin(n, p).real {x | p ∈ clopperPearson n α x}

theorem HasLaw.one_sub_le_clopperPearson {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} {n : ℕ} {p : I} (hX : HasLaw X Bin(n, p) P) {α : ℝ} (hα : 0 ≤ α) :
    1 - α ≤ P.real {ω | p ∈ clopperPearson n α (X ω)}
```

### The endpoints are the textbook ones

```lean
theorem coe_cpUpper_zero {n : ℕ} (hn : 0 < n) {α : ℝ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) :
    (cpUpper n α 0 : ℝ) = 1 - (α / 2) ^ (n⁻¹ : ℝ)

theorem coe_cpLower_self {n : ℕ} (hn : 0 < n) {α : ℝ} (hα₀ : 0 ≤ α) (hα₂ : α ≤ 2) :
    (cpLower n α n : ℝ) = (α / 2) ^ (n⁻¹ : ℝ)

theorem binomial_real_Ici_eq_iff {n x : ℕ} (hx : 1 ≤ x) (hxn : x ≤ n) {α : ℝ} (hα₀ : 0 < α)
    (hα₂ : α ≤ 2) {θ : I} : Bin(n, θ).real (Ici x) = α / 2 ↔ θ = cpLower n α x

theorem binomial_real_Iic_eq_iff {n x : ℕ} (hxn : x < n) {α : ℝ} (hα₀ : 0 < α)
    (hα₂ : α ≤ 2) {θ : I} : Bin(n, θ).real (Iic x) = α / 2 ↔ θ = cpUpper n α x

theorem cpLower_le_cpUpper (n : ℕ) {α : ℝ} (hα : α ≤ 1) (x : ℕ) :
    cpLower n α x ≤ cpUpper n α x
```

For `α > 1` the interval can be empty (`n = 2`, `x = 1`, `α > 3/2`); coverage is trivial
there. For interior `x` each endpoint is the unique root of its tail equation, which rests on
`strictMono_binomial_real_Ici` and `strictAnti_binomial_real_Iic` (the tails are strictly
monotone in `θ`); `binomial_real_Ici_cpLower` and `binomial_real_Iic_cpUpper` state the root
property directly. The examples pin concrete values, for instance `cpUpper 1 0.05 0 =
0.975`, `cpUpper 2 α 1 = √(1 - α/2)` and `cpLower 2 0.05 1 = 1 - √0.975`.

The probabilistic core is that a distribution function evaluated at the observation is
super-uniform, without continuity assumptions: `measure_setOf_measure_Iic_le` (countable
linear orders), `measure_setOf_measure_Iic_le_real` (`ℝ`) and, with mathlib's `cdf`,

```lean
theorem measure_cdf_le (ν : Measure ℝ) [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 ≤ t) :
    ν {x | cdf ν x ≤ t} ≤ ENNReal.ofReal t
```

### Ville's inequality

For `M : ℕ → Ω → ℝ`, a filtration `𝒢 : Filtration ℕ m0` and a finite measure `μ`:

```lean
theorem Supermartingale.mul_measure_exists_le [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) (ε : ℝ≥0) :
    ε * μ {ω | ∃ k, (ε : ℝ) ≤ M k ω} ≤ ENNReal.ofReal (μ[M 0])

theorem Supermartingale.measure_exists_le_le_div [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ {ω | ∃ k, (ε : ℝ) ≤ M k ω} ≤ ENNReal.ofReal (μ[M 0]) / ε

theorem Supermartingale.mul_measure_le_iSup [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) (ε : ℝ≥0) :
    ε * μ {ω | (ε : ℝ≥0∞) ≤ ⨆ k, ENNReal.ofReal (M k ω)} ≤ ENNReal.ofReal (μ[M 0])
```

plus the finite-horizon form `Supermartingale.mul_measure_exists_le_le` (`∃ k ≤ n`). The
supremum form also counts paths that approach `ε` without reaching it.

## What is not proved

- **The Beta-quantile link.** The Clopper–Pearson endpoints are not identified with
  quantiles of mathlib's Beta distribution; that needs
  `P_θ(X ≥ x) = ∫₀^θ betaPDF x (n - x + 1)`. Their meaning rests on the closed forms for
  `x = 0` and `x = n` and on the unique-root theorems above.
- **Holm as closed testing.** Holm is proved directly, so general closed testing, weighted
  Holm and Benjamini–Hochberg are not available.
- **Random hypotheses.** The set of true nulls is a fixed `Finset`; data-dependent
  hypotheses are not modelled.
- **Continuous time.** Ville's inequality is for `ℕ`-indexed filtrations and finite
  measures; there is no continuous-time or e-process version.
- **The step-down equivalence for `α < 0`**, which is false (see above).

## Not done yet

- CI has not run on GitHub (it runs on pull requests and manual dispatch only); every step
  it runs was run locally. The tag waits for the first green run.
- Nothing is in mathlib; [docs/PR.md](PR.md) plans the pull requests and renames.

## Corrections from the audit of 2026-11-06

Nothing was rebuilt and the only Lean change is one sentence in the `ClopperPearson` module
docstring (which Beta quantile each endpoint is), so these are not code changes.
[REPORT.md](../REPORT.md) section 6 lists what was checked.

- docs/DESIGN.md: the interval can be empty for `1 < α ≤ 2`, not only for `α > 2`.
- docs/DESIGN.md and REPORT.md: Holm, a one-sided Clopper–Pearson bound and Ville exist in
  other Lean 4 projects, so the claim that a web search found none is withdrawn.
- docs/DESIGN.md: monotone tails and unique roots are no longer listed as out of scope.
- docs/PR.md: mathlib's rules on AI-written code and the closed Ville pull requests.
- README.md: setup takes about 7 GB for mathlib, not 5 GB.

The full list of additions is in [CHANGELOG.md](../CHANGELOG.md).
