# AGENTS.md

Guide for coding agents (and humans) working on leanstats. Read `docs/DESIGN.md` before
changing a definition or a statement: it fixes the statements, the modelling choices and the
proof strategies.

## What this is

Lean 4 + mathlib proofs of Holm's FWER control (with Bonferroni and the step-down
equivalence), Clopper–Pearson coverage, and Ville's inequality. There is no executable code
and no data.

## Conventions

- Lake project. Toolchain in `lean-toolchain`, mathlib pinned to a release tag in
  `lakefile.toml` and locked in `lake-manifest.json`. Bump both together to a tag at least a
  week old, in a separate commit.
- **Never build mathlib from source.** Run `lake exe cache get` after cloning or after a bump.
- Files are Lean modules: `module`, `public import`, `@[expose] public section`. Namespace
  `LeanStats`. MIT header with `Authors: leanstats contributors` (the header linter is
  configured for MIT in `lakefile.toml`).
- No `sorry`, `admit`, `native_decide`, `axiom` or kernel bypass (`scripts/check_no_sorry.sh`).
  `#audit_leanstats_axioms` in `LeanStatsTest/Axioms.lean` audits every public declaration; add every
  new main theorem to the names it lists. Run the leanchecker replay locally before pushing
  (CI has not run yet).
- Every new definition gets evidence that it is faithful: a characterisation theorem, a
  closed form or a worked example in `LeanStatsTest/Examples.lean`.
- mathlib style and naming. `lake build --wfail` must pass with the standard linter set.
  Search mathlib (`exact?`, Loogle, the docs) before writing a helper lemma.
- CI (`.github/workflows/ci.yml`) runs on pull requests and manual dispatch only (metered
  private minutes): the source scan and its self-test, then `leanprover/lean-action` (pinned by SHA) with
  `--wfail` and a leanchecker replay (`LEAN_NUM_THREADS=1`, modules passed explicitly).
- Scratch files go in `tmp/` (gitignored). Commits end with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. No personal names, local paths or
  machine details in committed files.

## Architecture map

| Path | Content |
|---|---|
| `LeanStats/PValue.lean` | `IsValidPValue` (super-uniform p-values) |
| `LeanStats/Holm.lean` | `HolmRejects`, `BonferroniRejects`, deterministic core, `holm_fwer_le`, `bonferroni_fwer_le` |
| `LeanStats/HolmStepDown.lean` | `StepDownRejects`, `holmRejects_iff_stepDownRejects`, existence of a sorting order |
| `LeanStats/ClopperPearson.lean` | super-uniform distribution function (countable orders and `ℝ`), binomial tails, `cpLower`/`cpUpper`/`clopperPearson`, coverage, boundary values, closed forms, monotone tails, endpoints as unique roots of the tail equations |
| `LeanStats/Ville.lean` | finite- and infinite-horizon Ville inequality, `∃` and `sup` forms |
| `LeanStatsTest/Examples.lean` | worked examples pinning down the definitions |
| `LeanStatsTest/Axioms.lean` | axiom audit of every public declaration in the `LeanStats` modules, plus the main theorems by name |
| `scripts/check_no_sorry.sh` | source scan used by CI; `scripts/test_check_no_sorry.sh` plants each pattern and checks the scan rejects it |
| `docs/PR.md` | mathlib upstreaming plan and renames |

## Working with mathlib locally

Importing mathlib can cost minutes per `lean` process, and each process holds several GB of
memory. Do not open many files at once. For fast iteration keep a single Lean language
server running (`lake serve`) with one open document: re-checks then take seconds. Run
`lake build` sequentially rather than in parallel shells.

## Status and next steps (2026-10-30)

Done (0.1.0, not yet tagged): Holm FWER (strong control, any real `α`; also as `μ.real`)
under arbitrary dependence, Bonferroni corollary, sort-free definition proved equal to the
sorted step-down procedure for `α ≥ 0`; Clopper–Pearson coverage `≥ 1 - α` for every `n` and
`p ∈ [0, 1]`, tail formulas, closed forms for `x = 0` and `x = n`, strictly monotone tails and
endpoints as the unique roots of the tail equations for interior `x`, non-empty interval for
`α ≤ 1`; super-uniform distribution function on countable orders and on `ℝ` (`cdf`); Ville's
inequality in `∃` and `sup` forms. `lake build --wfail`, the axiom sweep, the source scan and
leanchecker pass locally. CI has not run yet on GitHub (no pull request opened, no dispatch);
tag 0.1.0 after the first green run.

Next, in order of value:

1. Run CI once on GitHub (owner's call: metered minutes), then tag 0.1.0.
2. Upstream PR 1 and PR 2 of docs/PR.md (small, no design discussion needed).
3. The Clopper–Pearson endpoints as quantiles of mathlib's Beta distribution (`betaPDF`): needs
   `P_θ(X ≥ x) = ∫₀^θ betaPDF x (n - x + 1)`.
4. Holm as closed testing with Bonferroni local tests; weighted Holm.
5. Benjamini–Hochberg FDR control under independence/PRDS (a larger project).
