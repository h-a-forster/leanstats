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
- No `sorry`, `admit`, `native_decide` or `axiom` (`scripts/check_no_sorry.sh`). Every new main
  theorem gets a `#guard_msgs`/`#print axioms` entry in `LeanStatsTest/Axioms.lean`.
- Every new definition gets evidence that it is faithful: a characterisation theorem, a
  closed form or a worked example in `LeanStatsTest/Examples.lean`.
- mathlib style and naming. `lake build --wfail` must pass with the standard linter set.
  Search mathlib (`exact?`, Loogle, the docs) before writing a helper lemma.
- CI (`.github/workflows/ci.yml`) runs on pull requests and manual dispatch only (metered
  private minutes): the source scan, then `leanprover/lean-action` (pinned by SHA) with
  `--wfail`.
- Scratch files go in `tmp/` (gitignored). Commits end with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. No personal names, local paths or
  machine details in committed files.

## Architecture map

| Path | Content |
|---|---|
| `LeanStats/PValue.lean` | `IsValidPValue` (super-uniform p-values) |
| `LeanStats/Holm.lean` | `HolmRejects`, `BonferroniRejects`, deterministic core, `holm_fwer_le`, `bonferroni_fwer_le` |
| `LeanStats/HolmStepDown.lean` | `StepDownRejects`, `holmRejects_iff_stepDownRejects`, existence of a sorting order |
| `LeanStats/ClopperPearson.lean` | super-uniform distribution function, binomial tails, `cpLower`/`cpUpper`/`clopperPearson`, coverage, boundary values, closed forms |
| `LeanStats/Ville.lean` | finite- and infinite-horizon Ville inequality |
| `LeanStatsTest/Examples.lean` | worked examples pinning down the definitions |
| `LeanStatsTest/Axioms.lean` | axiom audit of the main theorems |
| `scripts/check_no_sorry.sh` | source scan used by CI |
| `docs/PR.md` | mathlib upstreaming plan and renames |

## Working on this machine

Importing mathlib costs 1–4 minutes per `lean` process here, and each process holds several
GB of memory. Do not open many files at once. For fast iteration keep a single Lean language
server running (`lake serve`) with one open document: re-checks then take seconds. Run
`lake build` sequentially rather than in parallel shells.

## Status and next steps (2026-10-30)

Done (v0.1.0): Holm FWER under arbitrary dependence, Bonferroni corollary, sort-free
definition proved equal to the sorted step-down procedure; Clopper–Pearson coverage
`≥ 1 - α` for every `n` and `p ∈ [0, 1]`, tail formulas, closed forms for `x = 0` and `x = n`;
Ville's inequality (stretch). `lake build --wfail` passes, the axiom audit passes, the source
scan passes. CI has not run yet on GitHub (no pull request opened).

Next, in order of value:

1. **Monotonicity of binomial tails in `θ`** (`θ ↦ Bin(n, θ).real (Ici x)` is monotone and
   continuous), then the root characterisation `P_{cpLower}(X ≥ x) = α/2` for `x ≥ 1`. This
   turns the inf/sup definition into the textbook "solve for θ" form. Route: derivative of the
   tail sum is `n · C(n-1, x-1) θ^(x-1) (1-θ)^(n-x) ≥ 0`, or a coupling `Bin(n, θ) ≤st Bin(n, θ')`
   via mathlib's `setBernoulli` construction.
2. Real-line version of the distribution-function lemma (`P(F(X) ≤ t) ≤ t` for
   `ProbabilityTheory.cdf`), the natural mathlib generalisation (docs/PR.md, PR 1).
3. Upstream PR 1 and PR 2 of docs/PR.md (small, no design discussion needed).
4. Holm as closed testing with Bonferroni local tests; weighted Holm.
5. Benjamini–Hochberg FDR control under independence/PRDS (a larger project).
