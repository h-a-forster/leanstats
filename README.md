# leanstats

Machine-checked proofs, in Lean 4 with mathlib, of three guarantees that applied statistics
relies on:

1. **Holm's step-down procedure controls the family-wise error rate** at level `α` for a
   finite family of hypotheses under arbitrary dependence between the p-values, whatever the
   set of true nulls (strong control). Bonferroni follows as a corollary.
2. **Clopper–Pearson intervals have coverage at least `1 - α`** for every success probability
   `p ∈ [0, 1]` and every number of trials `n`.
3. **Ville's inequality**: a non-negative supermartingale exceeds `ε` at any time with
   probability at most `E[M₀] / ε`.

There is no `sorry`, `admit` or new `axiom`. Every declaration depends only on Lean's three
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). `LeanStatsTest/Axioms.lean`
checks this on every build.

## What is proved

All names are in the `LeanStats` namespace.

### Valid p-values ([LeanStats/PValue.lean](LeanStats/PValue.lean))

```lean
def IsValidPValue (μ : Measure Ω) (p : Ω → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, μ {ω | p ω ≤ t} ≤ ENNReal.ofReal t
```

A p-value is a real random variable that is *super-uniform* under the null. Continuity,
measurability and independence are not assumed, so discrete and conservative tests are
covered.

### Holm and Bonferroni ([LeanStats/Holm.lean](LeanStats/Holm.lean), [LeanStats/HolmStepDown.lean](LeanStats/HolmStepDown.lean))

```lean
def HolmRejects (α : ℝ) (p : ι → ℝ) (i : ι) : Prop :=
  ∀ j, p j ≤ p i → p j ≤ α / #{k | p j ≤ p k}

theorem holm_fwer_le (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ι → Ω → ℝ}
    {I₀ : Finset ι} (hp : ∀ i ∈ I₀, IsValidPValue μ (p i)) (α : ℝ) :
    μ {ω | ∃ i ∈ I₀, HolmRejects α (fun j ↦ p j ω) i} ≤ ENNReal.ofReal α

theorem bonferroni_fwer_le ... :
    μ {ω | ∃ i ∈ I₀, BonferroniRejects α (fun j ↦ p j ω) i} ≤ ENNReal.ofReal α
```

`ι` is any finite type of hypotheses and `I₀` is the (unknown) set of true nulls. Only the
null p-values need to be valid; their joint law, and everything about the non-null p-values,
is arbitrary. Because the bound holds for every `I₀`, this is strong control of the FWER. The
level `α` may be any real number (for `α < 0` both procedures reject only p-values `≤ 0`, an
event of probability zero). `holm_fwer_le_real` states the bound as a real probability,
`μ.real {…} ≤ α`, for `α ≥ 0`.

`HolmRejects` describes Holm's procedure without a sorting permutation. Theorem
`holmRejects_iff_stepDownRejects` proves that it agrees with the textbook procedure ("sort
the p-values, reject while `p₍ⱼ₎ ≤ α / (m - j + 1)`, stop at the first failure") for every
sorting order when `α ≥ 0`. The outcome therefore does not depend on how ties are broken. For
`α < 0` the two can differ (a counterexample is in `LeanStatsTest/Examples.lean`), which does
not affect the FWER bound.
`exists_monotone_comp_equiv` shows that a sorting order always exists.

### Clopper–Pearson ([LeanStats/ClopperPearson.lean](LeanStats/ClopperPearson.lean))

```lean
noncomputable def cpLower (n : ℕ) (α : ℝ) (x : ℕ) : I :=
  sInf {θ : I | α / 2 ≤ Bin(n, θ).real (Ici x)}      -- P_θ(X ≥ x) ≥ α/2
noncomputable def cpUpper (n : ℕ) (α : ℝ) (x : ℕ) : I :=
  sSup {θ : I | α / 2 ≤ Bin(n, θ).real (Iic x)}      -- P_θ(X ≤ x) ≥ α/2
noncomputable def clopperPearson (n : ℕ) (α : ℝ) (x : ℕ) : Set I :=
  Icc (cpLower n α x) (cpUpper n α x)

theorem binomial_clopperPearson_not_mem_le (n : ℕ) (α : ℝ) (p : I) :
    Bin(n, p) {x | p ∉ clopperPearson n α x} ≤ ENNReal.ofReal α

theorem one_sub_le_binomial_clopperPearson (n : ℕ) {α : ℝ} (hα : 0 ≤ α) (p : I) :
    1 - α ≤ Bin(n, p).real {x | p ∈ clopperPearson n α x}

theorem HasLaw.one_sub_le_clopperPearson (hX : HasLaw X Bin(n, p) P) (hα : 0 ≤ α) :
    1 - α ≤ P.real {ω | p ∈ clopperPearson n α (X ω)}
```

`I` is mathlib's `unitInterval` and `Bin(n, θ)` is mathlib's `ProbabilityTheory.binomial`.
The supporting lemmas `binomial_real_Iic` and `binomial_real_Ici` give the tails as the
familiar finite sums. `coe_cpUpper_zero` and `coe_cpLower_self` give the closed forms
`1 - (α/2)^(1/n)` for zero successes and `(α/2)^(1/n)` for `n` successes.
For interior observations, `binomial_real_Ici_cpLower` (`1 ≤ x ≤ n`) and
`binomial_real_Iic_cpUpper` (`x < n`) show that the endpoints solve the textbook equations
`P_θ(X ≥ x) = α/2` and `P_θ(X ≤ x) = α/2` for `0 < α ≤ 2`, and that the tail is strictly
smaller beyond them, and `cpLower_le_cpUpper` shows that the interval is non-empty for
`α ≤ 1`. The upper tail is strictly increasing in `θ` and the lower tail strictly decreasing
(`strictMono_binomial_real_Ici`, `strictAnti_binomial_real_Iic`), so each endpoint is the
unique root of its equation (`binomial_real_Ici_eq_iff`, `binomial_real_Iic_eq_iff`), which is
the textbook definition. `LeanStatsTest/Examples.lean` checks concrete values, including
`cpUpper 2 α 1 = √(1 - α/2)` computed from the definition.

The probabilistic core is `measure_setOf_measure_Iic_le`: for any measure on a countable
linear order, `ν {x | ν (Iic x) ≤ t} ≤ t`. In words, the distribution function evaluated at
the observation is super-uniform. It holds without any continuity assumption. The same holds
for any measure on `ℝ` (`measure_setOf_measure_Iic_le_real`), and `measure_cdf_le` states it
as `P(F(X) ≤ t) ≤ t` with mathlib's `cdf`.

### Ville ([LeanStats/Ville.lean](LeanStats/Ville.lean))

```lean
theorem Supermartingale.mul_measure_exists_le [IsFiniteMeasure μ]
    (hM : Supermartingale M 𝒢 μ) (hnonneg : 0 ≤ M) (ε : ℝ≥0) :
    ε * μ {ω | ∃ k, (ε : ℝ) ≤ M k ω} ≤ ENNReal.ofReal (μ[M 0])
```

with a finite-horizon version, a divided form `μ {∃ k, ε ≤ M k} ≤ E[M 0] / ε`, and the
supremum form `ε * μ {ε ≤ sup_k M k} ≤ E[M 0]` (`Supermartingale.mul_measure_le_iSup`, supremum
in `[0, ∞]`), whose event also contains paths that approach `ε` without reaching it.

## Modelling choices

| Choice | Why |
|---|---|
| p-values are real random variables with `μ {p ≤ t} ≤ t` on `[0, 1]` | Standard definition. It covers discrete tests. For measurable `p` it is the usual definition; for non-measurable `p`, `μ` is the outer measure, so the hypothesis and the conclusions are outer-measure bounds and measurability is never needed. |
| Holm is defined sort-free and proved equal to the sorted procedure | The sort-free form makes the FWER proof short. The equivalence theorem shows it is the textbook procedure. |
| The true nulls `I₀` are a fixed `Finset` | This is the frequentist set-up: the truth is fixed and unknown. The theorem holds for every `I₀`. |
| Clopper–Pearson endpoints are the inf/sup of the accepted parameters | Continuity and strict monotonicity of the tail in `θ` make them the unique root of `P_θ(X ≥ x) = α/2` (`P_θ(X ≤ x) = α/2`), which is proved. Neither is needed for coverage. The identification with a Beta quantile is not formalised. |
| Endpoints live in `unitInterval` | `unitInterval` is a complete lattice, so the endpoints always exist with no side conditions. |
| Probabilities are in `ℝ≥0∞` (miss probability) and `ℝ` (coverage) | The `ℝ≥0∞` statement holds for every `α`. The coverage form needs `0 ≤ α`. |

## Building

You need [elan](https://github.com/leanprover/elan). Then:

```sh
lake exe cache get   # downloads prebuilt mathlib (about 7 GB); never build mathlib from source
lake build           # builds LeanStats and LeanStatsTest (examples and axiom audit)
sh scripts/check_no_sorry.sh
LEAN_NUM_THREADS=1 lake env leanchecker LeanStats LeanStatsTest   # kernel replay, minutes
```

The kernel replay is the only check that catches a declaration added to the environment
without kernel checking, so run it before relying on a change.

The toolchain is pinned in `lean-toolchain` (Lean v4.35.0) and mathlib in `lakefile.toml`
(tag `v4.35.0`, locked in `lake-manifest.json`).

## Documents

- [docs/DESIGN.md](docs/DESIGN.md): statements, proof strategies, prior art.
- [docs/PR.md](docs/PR.md): draft plan for upstreaming to mathlib.
- [REPORT.md](REPORT.md): what was checked, build measurements, limitations.
- [docs/release-notes-0.1.0.md](docs/release-notes-0.1.0.md): notes for the first release.
- [AGENTS.md](AGENTS.md): conventions.

## Licence

MIT. See [LICENSE](LICENSE).
