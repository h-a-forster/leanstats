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
check. `#audit_leanstats_axioms` checks every declaration in the `LeanStats` namespace, so a
new declaration is audited without being listed here. The main theorems are named as well, so
the audit fails if one of them is renamed or leaves the namespace.
-/

public section

open Lean Elab Command in
/-- Fail unless every non-internal declaration in the `LeanStats` namespace depends only on
`propext`, `Classical.choice` and `Quot.sound`, and each listed name is one of the audited
declarations; report how many declarations were checked. -/
elab "#audit_leanstats_axioms" required:(ppSpace ident)* : command => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let names := (← getEnv).constants.fold (init := #[]) fun acc n _ ↦
    if (`LeanStats).isPrefixOf n && !n.isInternal then acc.push n else acc
  for id in required do
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    unless names.contains n do
      throwError m!"{n} is not a declaration in the LeanStats namespace"
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
