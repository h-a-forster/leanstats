# Contributing

Corrections, generalisations and new results are welcome. Read
[docs/DESIGN.md](docs/DESIGN.md) first: it fixes the statements and the modelling choices.

## Setup

Install [elan](https://github.com/leanprover/elan) (the Lean toolchain manager). From a clone:

```sh
lake exe cache get   # prebuilt mathlib; do not build mathlib from source
lake build --wfail
sh scripts/check_no_sorry.sh
```

The toolchain (`lean-toolchain`) and mathlib (`lakefile.toml`, `lake-manifest.json`) are
pinned. Bump them together, deliberately, in their own pull request, to a mathlib release tag
that is at least a week old.

## Rules for proofs

- No `sorry`, `admit`, new `axiom` or `native_decide` in `LeanStats/` or `LeanStatsTest/`. Every
  new main theorem gets an entry in `LeanStatsTest/Axioms.lean`.
- mathlib style: naming conventions, a module docstring with "Main statements", a docstring on
  every definition and main theorem, lines at most 100 characters. The build enables mathlib's
  standard linter set and CI treats warnings as errors.
- Search mathlib before writing a helper lemma (`exact?`, `apply?`, Loogle, the mathlib docs).
- A new definition comes with evidence that it means what it says: a characterisation theorem,
  a closed form, or a worked example in `LeanStatsTest/Examples.lean`.
- Keep statements as general as the proof allows, but do not weaken readability for generality
  nobody needs.

## Pull requests

CI runs on pull requests (and manual dispatch): the `sorry`/`axiom` check, then `lake build
--wfail` through `leanprover/lean-action`, which also builds the examples and the axiom audit.
Describe what is proved, and update README.md, docs/DESIGN.md and CHANGELOG.md when a statement
changes.
