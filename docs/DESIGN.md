# Design

This document fixes what leanstats proves (the "estimands" of a formalisation: the exact
statements), how the proofs go, and what came before. Read it before changing a definition.

## 1. Statements

Notation: `Ω` is a measurable space with measure `μ`; `ι` is a finite type of hypotheses with
`m = Fintype.card ι`; `I` is mathlib's `unitInterval`; `Bin(n, θ)` is
`ProbabilityTheory.binomial n θ : Measure ℕ`.

### 1.1 Valid p-values

`IsValidPValue μ p :⇔ ∀ t ∈ [0, 1], μ {ω | p ω ≤ t} ≤ t`, with `μ` evaluated on arbitrary sets
(outer measure). Under a probability measure the bound extends to every `t ≥ 0`
(`IsValidPValue.measure_le_le`).

### 1.2 Holm (S1)

For every `α : ℝ`, every `I₀ : Finset ι` (the true nulls) and every family `p : ι → Ω → ℝ` whose
null coordinates are valid p-values:

    μ {ω | ∃ i ∈ I₀, HolmRejects α (p · ω) i} ≤ α                 (holm_fwer_le)

No assumption is made on the joint law of `p`, on the non-null coordinates, or on
measurability. Bonferroni (`p i ≤ α / m`) is a corollary (`bonferroni_fwer_le`), because
Bonferroni's rejections are a subset of Holm's for `α ≥ 0` (`BonferroniRejects.holmRejects`).
Since `I₀` is arbitrary this is strong FWER control. For `α < 0` both procedures reject only
p-values `≤ 0`, and `measure_exists_le_zero` shows that no null p-value is `≤ 0` except on a
null set.

**Definition.** `HolmRejects α p i :⇔ ∀ j, p j ≤ p i → p j ≤ α / #{k | p j ≤ p k}`.

**Faithfulness.** `holmRejects_iff_stepDownRejects`: for every bijection
`σ : Fin m ≃ ι` with `p ∘ σ` monotone and `α ≥ 0`, `HolmRejects α p (σ r)` iff every position
`s ≤ r` satisfies `p (σ s) ≤ α / (m - s)` (0-based positions; this is
`p₍ⱼ₎ ≤ α / (m - j + 1)` with 1-based `j`). The right-hand side is the textbook procedure.
Since the left-hand side does not mention `σ`, the textbook procedure is independent of
tie-breaking. `exists_monotone_comp_equiv` gives such a `σ` (via `Tuple.sort`).

**Proof of S1.** Let `j₀` minimise `p` over `I₀`. If Holm rejects some `i ∈ I₀` then it
rejects `j₀` (rejections are closed downwards), so `p j₀ ≤ α / #{k | p j₀ ≤ p k}`. Every
`k ∈ I₀` satisfies `p j₀ ≤ p k`, hence `#{k | p j₀ ≤ p k} ≥ #I₀` and `p j₀ ≤ α / #I₀` (the case
`p j₀ < 0` is immediate). So the error event is contained in `⋃_{j ∈ I₀} {p j ≤ α / #I₀}`, and
a union bound with validity gives `#I₀ · α / #I₀ = α`
(`HolmRejects.exists_le_div_card`). This is Holm's original argument; it never uses the
sorting order.

### 1.3 Clopper–Pearson (S2)

    cpLower n α x = sInf {θ : I | α/2 ≤ P_θ(X ≥ x)}
    cpUpper n α x = sSup {θ : I | α/2 ≤ P_θ(X ≤ x)}
    clopperPearson n α x = Icc (cpLower n α x) (cpUpper n α x) ⊆ I

For every `n`, `α` and `p ∈ I`:

    Bin(n, p) {x | p ∉ clopperPearson n α x} ≤ α        (binomial_clopperPearson_not_mem_le)
    1 - α ≤ Bin(n, p).real {x | p ∈ clopperPearson n α x}   if 0 ≤ α
    1 - α ≤ P.real {ω | p ∈ clopperPearson n α (X ω)}      if X has law Bin(n, p)

**Faithfulness.** The tails are the textbook sums (`binomial_real_Iic`,
`binomial_real_Ici`). The closed forms `cpUpper n α 0 = 1 - (α/2)^(1/n)` and
`cpLower n α n = (α/2)^(1/n)` (for `n ≥ 1`, `0 ≤ α ≤ 2`) match the standard formulas, and
`cpLower n α 0 = 0`, `cpUpper n α n = 1` for `α ≤ 2`. For interior observations the tails are
continuous in `θ` (`continuous_binomial_real_Ici`, `continuous_binomial_real_Iic`), which
alone gives the root form: for `1 ≤ x ≤ n` and `0 < α ≤ 2`, `P_θ(X ≥ x) = α/2` at
`θ = cpLower n α x` and `< α/2` below it (`binomial_real_Ici_cpLower`,
`binomial_real_Ici_lt_of_lt_cpLower`), and symmetrically for `cpUpper` when `x < n`. The
accepted set is closed, so its infimum is accepted; the tail vanishes at `θ = 0`, so the
infimum is positive, and continuity from the left forces equality. For `α ≤ 1` the interval is
non-empty (`cpLower_le_cpUpper`: between the endpoints both tails would be `< α/2`, but they
sum to at least 1). Monotonicity of the tail, which makes the root unique and gives the
Beta-quantile form, is not formalised. None of this affects the coverage theorem, which holds
for the endpoints exactly as defined (and would hold for any wider interval, which is why
these characterisations matter).

**Proof of S2.** If `p < cpLower n α x` then `p` is not in the set whose infimum is
`cpLower`, so `P_p(X ≥ x) < α/2`; symmetrically for the upper bound. So the miss event is
contained in `{x | P_p(X ≥ x) ≤ α/2} ∪ {x | P_p(X ≤ x) ≤ α/2}`. Each part has probability at
most `α/2` by the lemma below, and the union bound finishes.

**Lemma (super-uniform distribution function).** For any measure `ν` on a countable linear
order and any `t`, `ν {x | ν (Iic x) ≤ t} ≤ t` (`measure_setOf_measure_Iic_le`; also for
`Ici`). Proof: the set `A` is covered by the directed union `⋃_{x ∈ A} Iic x`, whose measure is
the supremum of `ν (Iic x) ≤ t` over `x ∈ A` (`measure_biUnion_eq_iSup`). No continuity is
needed, which is exactly why the discrete Clopper–Pearson interval is conservative rather than
exact.

### 1.4 Ville (S3, stretch)

For a non-negative supermartingale `M` with respect to a filtration on `ℕ`, a finite measure
`μ` and `ε : ℝ≥0`:

    ε · μ {ω | ∃ k ≤ n, ε ≤ M k ω} ≤ E[M 0]      (Supermartingale.mul_measure_exists_le_le)
    ε · μ {ω | ∃ k, ε ≤ M k ω} ≤ E[M 0]          (Supermartingale.mul_measure_exists_le)
    μ {ω | ∃ k, ε ≤ M k ω} ≤ E[M 0] / ε  (ε ≠ 0) (Supermartingale.measure_exists_le_le_div)
    ε · μ {ω | ε ≤ ⨆ k, M k ω} ≤ E[M 0]          (Supermartingale.mul_measure_le_iSup)

The supremum is taken in `[0, ∞]` (of `ENNReal.ofReal (M k ω)`); a real-valued `⨆` would be
`0` on unbounded paths. Its event is larger than `{∃ k, ε ≤ M k}` and follows from it by
applying the `∃` form at every `ε' < ε`.

**Proof.** Let `τ` be the first time in `[0, n]` with `M ≥ ε` (`hittingBtwn`, a bounded
stopping time). Then `ε · 1_A ≤ M_τ` pointwise (non-negativity off `A`), and optional
stopping for the submartingale `-M` between `0` and `τ` gives `E[M_τ] ≤ E[M 0]`. Let `n → ∞`
by continuity from below.

## 2. Modelling decisions and alternatives considered

- **p-values as random variables, not test families.** A test at level `α` is
  `{p ≤ α}`; this is the form used by Holm. Randomised tests are covered because `Ω` may carry
  auxiliary randomness.
- **Outer measure.** All bounds use `μ` on arbitrary sets (`measure_mono`,
  `measure_biUnion_finset_le` need no measurability), so non-measurable p-values do not need
  separate treatment. If the p-values are measurable the statements are the usual ones.
- **Sort-free Holm.** Defining Holm through `List.mergeSort` or a rank function makes the
  FWER proof depend on permutation bookkeeping. The sort-free characterisation keeps the FWER
  proof to a dozen lines and moves the bookkeeping into a separate equivalence theorem.
- **Endpoints in `unitInterval`.** With `ℝ`-valued `sInf`/`sSup` the empty-set and
  unboundedness conventions (`sInf ∅ = 0`) would need side conditions; `unitInterval` is a
  complete linear order, so `sInf_le`/`le_sSup` apply directly. An empty accepted set (only for
  `α > 2`) gives the empty interval, which is the right convention.
- **Level convention.** Each tail gets `α/2` (the equal-tailed Clopper–Pearson interval).
  Coverage is `≥ 1 - α` for all `α`; for `α ≥ 1` it is trivial.

## 3. Prior art

- S. Holm (1979), *A simple sequentially rejective multiple test procedure*, Scand. J.
  Statist. 6, 65–70. https://www.jstor.org/stable/4615733
- C. J. Clopper and E. S. Pearson (1934), *The use of confidence or fiducial limits
  illustrated in the case of the binomial*, Biometrika 26, 404–413.
  https://doi.org/10.1093/biomet/26.4.404
- J. Ville (1939), *Étude critique de la notion de collectif*. Modern statement and use:
  A. Ramdas, P. Grünwald, V. Vovk, G. Shafer (2023), *Game-theoretic statistics and safe
  anytime-valid inference*, Statist. Sci. 38(4). https://arxiv.org/abs/2210.01948
- Holm as a closed testing procedure with Bonferroni local tests: Marcus, Peritz and Gabriel
  (1976), Biometrika 63, 655–660. https://doi.org/10.1093/biomet/63.3.655
- mathlib: `ProbabilityTheory.binomial` (Mathlib/Probability/Distributions/Binomial.lean),
  `PMF.binomial`, optional stopping and Doob's maximal inequality `maximal_ineq`
  (Mathlib/Probability/Martingale/OptionalStopping.lean), hitting times
  (Mathlib/Probability/Process/HittingTime.lean). https://github.com/leanprover-community/mathlib4
- Formal statistics elsewhere: no formalisation of Holm, Clopper–Pearson or Ville was found in
  mathlib v4.35.0 (source search) or by a web search (October 2026). The Isabelle Archive of
  Formal Proofs (https://www.isa-afp.org) and Coq libraries were not searched exhaustively,
  so no novelty claim is made beyond mathlib.

## 4. Out of scope (v0.1)

- Monotonicity of binomial tails in `θ`, uniqueness of the endpoint roots and the
  Beta-quantile form, and exactness of the closed interval at the endpoints.
- Holm's procedure via closed testing, weighted Holm, Hochberg/Hommel (which need dependence
  assumptions), and FDR procedures (Benjamini–Hochberg).
- Continuous-time Ville and e-process generalisations.
