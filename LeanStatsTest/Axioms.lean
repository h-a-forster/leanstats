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
`Classical.choice`, `Quot.sound`). An unfinished proof would add `sorryAx` and break these
checks. `#audit_leanstats_axioms` extends the check to every declaration in the `LeanStats`
namespace, so a new declaration is audited without being listed here.
-/

public section

open Lean Elab Command in
/-- Fail unless every non-internal declaration in the `LeanStats` namespace depends only on
`propext`, `Classical.choice` and `Quot.sound`; report how many declarations were checked. -/
elab "#audit_leanstats_axioms" : command => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let names := (← getEnv).constants.fold (init := #[]) fun acc n _ ↦
    if (`LeanStats).isPrefixOf n && !n.isInternal then acc.push n else acc
  for n in names do
    for a in ← collectAxioms n do
      unless allowed.contains a do
        throwError m!"{n} depends on the axiom {a}"
  logInfo m!"{names.size} declarations in LeanStats use only the standard axioms"

/-- info: 47 declarations in LeanStats use only the standard axioms -/
#guard_msgs in
#audit_leanstats_axioms

/-- info: 'LeanStats.holm_fwer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.holm_fwer_le

/-- info: 'LeanStats.bonferroni_fwer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.bonferroni_fwer_le

/-- info: 'LeanStats.holmRejects_iff_stepDownRejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.holmRejects_iff_stepDownRejects

/-- info: 'LeanStats.binomial_clopperPearson_not_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.binomial_clopperPearson_not_mem_le

/-- info: 'LeanStats.one_sub_le_binomial_clopperPearson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.one_sub_le_binomial_clopperPearson

/-- info: 'LeanStats.HasLaw.one_sub_le_clopperPearson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.HasLaw.one_sub_le_clopperPearson

/-- info: 'LeanStats.coe_cpUpper_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.coe_cpUpper_zero

/-- info: 'LeanStats.coe_cpLower_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.coe_cpLower_self

/-- info: 'LeanStats.Supermartingale.mul_measure_exists_le_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.Supermartingale.mul_measure_exists_le_le

/-- info: 'LeanStats.Supermartingale.mul_measure_exists_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.Supermartingale.mul_measure_exists_le

/-- info: 'LeanStats.Supermartingale.measure_exists_le_le_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanStats.Supermartingale.measure_exists_le_le_div
