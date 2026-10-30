# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). This
project uses [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.1.0 - unreleased

Not tagged yet: the tag follows the first green CI run on GitHub.

### Added

- `IsValidPValue`: super-uniform p-values.
- Holm's step-down procedure (`HolmRejects`) with strong family-wise error control under
  arbitrary dependence for every real level `α` (`holm_fwer_le`; `holm_fwer_le_real` as a real
  probability for `α ≥ 0`), Bonferroni as a corollary (`bonferroni_fwer_le`), and the
  equivalence with the sorted step-down procedure for every tie-breaking order and `α ≥ 0`
  (`holmRejects_iff_stepDownRejects`). `measure_exists_le_zero`: valid p-values are almost
  surely positive.
- Clopper–Pearson interval (`cpLower`, `cpUpper`, `clopperPearson`) with coverage at least
  `1 - α` for every `n` and `p ∈ [0, 1]` (`binomial_clopperPearson_not_mem_le`,
  `one_sub_le_binomial_clopperPearson`, `HasLaw.one_sub_le_clopperPearson`), binomial tail
  formulas, and closed forms for zero and all successes.
- Clopper–Pearson endpoints as the unique roots of the tail equations:
  `binomial_real_Ici_cpLower` (`1 ≤ x ≤ n`) and `binomial_real_Iic_cpUpper` (`x < n`), strict
  tail bounds beyond the endpoints, continuity and strict monotonicity of the tails in `θ`
  (`strictMono_binomial_real_Ici`, `strictAnti_binomial_real_Iic`), uniqueness
  (`binomial_real_Ici_eq_iff`, `binomial_real_Iic_eq_iff`), and `cpLower_le_cpUpper` for
  `α ≤ 1`.
- Super-uniformity of the distribution function on countable linear orders
  (`measure_setOf_measure_Iic_le`, `measure_setOf_measure_Ici_le`) and on `ℝ`
  (`measure_setOf_measure_Iic_le_real`, `measure_setOf_measure_Ici_le_real`, and
  `measure_cdf_le` for mathlib's `cdf`).
- Ville's inequality for non-negative supermartingales, finite-horizon, infinite-horizon,
  divided and supremum (`Supermartingale.mul_measure_le_iSup`) forms.
- Worked examples (`LeanStatsTest/Examples.lean`): Holm against Bonferroni, stopping at the
  first failure, tied p-values, Clopper–Pearson closed forms, decimal bounds and interior
  values, a uniform p-value satisfying `IsValidPValue`, and a counterexample showing that
  `holmRejects_iff_stepDownRejects` needs `0 ≤ α`.
- Checks: an axiom audit of every declaration made in a `LeanStats` module, which also requires
  the main theorems by name (`LeanStatsTest/Axioms.lean`); a source scan
  (`scripts/check_no_sorry.sh`) rejecting `sorry`, `admit`, `native_decide`, `axiom`
  declarations, kernel bypasses, `setEnv`/`addConstAsync` environment edits, `initialize` code, `debug` options in
  `lakefile.toml` and a `lakefile.lean`, with a self-test (`scripts/test_check_no_sorry.sh`);
  CI with the official `lean-action`, `--wfail` and a leanchecker kernel replay.
