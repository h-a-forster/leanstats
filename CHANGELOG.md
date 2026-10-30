# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). This
project uses [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

### Added

- Clopper–Pearson endpoints solve the tail equations: `binomial_real_Ici_cpLower`
  (`1 ≤ x ≤ n`), `binomial_real_Iic_cpUpper` (`x < n`), with strict tail bounds beyond the
  endpoints, continuity of the tails in `θ`, and `cpLower_le_cpUpper` for `α ≤ 1`.
- Ville's inequality in supremum form (`Supermartingale.mul_measure_le_iSup`).
- `measure_exists_le_zero`: valid p-values are almost surely positive.
- Axiom audit of every declaration in the `LeanStats` namespace; leanchecker kernel replay in
  CI; the source scan rejects `debug.skipKernelTC`, `implemented_by`, `extern`, `unsafe` and
  `ofReduceBool`.
- Examples: tied p-values, an interior Clopper–Pearson value, decimal bounds for
  `cpUpper 10 0.05 0` and `cpUpper 30 0.05 0`, a uniform p-value satisfying `IsValidPValue`,
  and a counterexample showing that `holmRejects_iff_stepDownRejects` needs `0 ≤ α`.

### Changed

- The source scan also rejects `sorryAx`, `addDeclWithoutChecking`, `addDeclCore`, `modifyEnv`,
  `run_cmd`, `run_elab`, `run_meta` and `debug.` options in `lakefile.toml`.
- The axiom audit checks that the main theorems are among the audited declarations instead of
  pinning the declaration count.
- Documentation: the equivalence with the sorted procedure is stated for `α ≥ 0`.
- `holm_fwer_le` and `bonferroni_fwer_le` take the level `α` explicitly and no longer assume
  `0 ≤ α`.

## 0.1.0 - 2026-10-30

### Added

- `IsValidPValue`: super-uniform p-values.
- Holm's step-down procedure (`HolmRejects`) with family-wise error control under arbitrary
  dependence (`holm_fwer_le`), Bonferroni as a corollary (`bonferroni_fwer_le`), and the
  equivalence with the sorted step-down procedure for every tie-breaking order and `α ≥ 0`
  (`holmRejects_iff_stepDownRejects`).
- Clopper–Pearson interval (`cpLower`, `cpUpper`, `clopperPearson`) with coverage at least
  `1 - α` for every `n` and `p ∈ [0, 1]` (`binomial_clopperPearson_not_mem_le`,
  `one_sub_le_binomial_clopperPearson`, `HasLaw.one_sub_le_clopperPearson`), binomial tail
  formulas, and closed forms for zero and all successes.
- Super-uniformity of the distribution function on countable linear orders
  (`measure_setOf_measure_Iic_le`, `measure_setOf_measure_Ici_le`).
- Ville's inequality for non-negative supermartingales, finite-horizon, infinite-horizon and
  divided forms.
- Worked examples and an axiom audit (`LeanStatsTest`), a `sorry`/`axiom` check script, and CI
  with the official `lean-action`.
