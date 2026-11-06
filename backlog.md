# Backlog

## In progress

## Waiting on me

- First green CI run: open a pull request from `polish-2026-10-30` to `main` (metered minutes; the workflow has never run on GitHub).
- Merge the pull request and tag v0.1.0 once CI is green.
- Make the repository public after the first green run, then enable private vulnerability reporting (SECURITY.md relies on it).
- Decide whether to rewrite history before going public to drop the `Co-Authored-By` trailers on 21 commits (no tags exist yet, so this is the cheapest moment).
- Decide whether to send mathlib PRs under a real name, given mathlib's rules on AI-written code (docs/PR.md).

## Decided

- 2026-10-30: CI runs on pull requests and dispatch only while the repository is private.
- 2026-11-06: no AI attribution trailers on new commits.

## Proposed

- CI also runs on pushes to `main` once the repository is public (minutes are free there).
- `LeanStatsTest/Examples.lean` pins an empty interval (`n = 2`, `x = 1`, `α = 2`) so the claim in docs/DESIGN.md is machine-checked.
- Clopper–Pearson endpoints are identified with Beta quantiles (needs `P_θ(X ≥ x) = ∫₀^θ betaPDF x (n - x + 1)`).
- mathlib PR 1 and PR 2 of docs/PR.md are submitted.
- Holm follows from closed testing, with weighted Holm; atlas-lean already has the closed-testing form, so build only for mathlib.
- Benjamini–Hochberg FDR control under independence or PRDS; atlas-lean has a version, so check it first.
