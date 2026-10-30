/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
module

public import LeanStats

/-!
# Axiom audit

The main theorems use only the three standard axioms of Lean and mathlib (`propext`,
`Classical.choice`, `Quot.sound`). An unfinished proof would add a fourth axiom and break the
check. `#audit_leanstats_axioms` checks every declaration made in a `LeanStats` module
(whatever its namespace), so a new declaration is audited without being listed here. The main
theorems are named as well, so the audit fails if one of them is renamed or moved.
-/

public section

open Lean Elab Command in
/-- Fail unless every non-internal declaration made in a `LeanStats` module depends only on
`propext`, `Classical.choice` and `Quot.sound`, and each listed name is one of the audited
declarations; report how many declarations were checked. -/
elab "#audit_leanstats_axioms" required:(ppSpace ident)* : command => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ ↦
    match env.getModuleIdxFor? n with
    | some i => if (`LeanStats).isPrefixOf env.header.moduleNames[i]! && !n.isInternal then
        acc.push n else acc
    | none => acc
  for id in required do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    unless names.contains n do
      throwError m!"{n} is not a declaration of the LeanStats library"
  for n in names do
    for a in ← collectAxioms n do
      unless allowed.contains a do
        throwError m!"{n} depends on the axiom {a}"
  logInfo m!"{names.size} declarations in LeanStats use only the standard axioms"

#audit_leanstats_axioms
  LeanStats.holm_fwer_le
  LeanStats.bonferroni_fwer_le
  LeanStats.holmRejects_iff_stepDownRejects
  LeanStats.binomial_clopperPearson_not_mem_le
  LeanStats.one_sub_le_binomial_clopperPearson
  LeanStats.HasLaw.one_sub_le_clopperPearson
  LeanStats.coe_cpUpper_zero
  LeanStats.coe_cpLower_self
  LeanStats.Supermartingale.mul_measure_exists_le_le
  LeanStats.Supermartingale.mul_measure_exists_le
  LeanStats.Supermartingale.measure_exists_le_le_div
