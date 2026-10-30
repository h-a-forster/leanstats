/-
Copyright (c) 2026 leanstats contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: leanstats contributors
-/
import LeanStats

/-!
# Axiom audit

The main theorems use only the three standard axioms of Lean and mathlib (`propext`,
`Classical.choice`, `Quot.sound`). A `sorry` would add `sorryAx` and break these checks.
-/

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
