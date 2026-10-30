# Changelog

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/). This
project uses [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased

## 0.1.0 - 2026-10-30

### Added

- `IsValidPValue`: super-uniform p-values.
- Holm's step-down procedure (`HolmRejects`) with family-wise error control under arbitrary
  dependence (`holm_fwer_le`), Bonferroni as a corollary (`bonferroni_fwer_le`), and the
  equivalence with the sorted step-down procedure for every tie-breaking order
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
