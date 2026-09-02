module

public meta import Mathlib.Util.AssertNoSorry

/-!
# CLRS-Lean Axiom Audit

This module provides the native command used by the v1 flagship trust gate.
It accepts exactly Lean's three standard logical axioms used by this project
and rejects every other transitive axiom dependency.
-/

public meta section

open Lean Elab Command

/-- The only axioms admitted by the CLRS-Lean v1 trust policy. -/
private def allowedAxioms : Array Name :=
  #[``propext, ``Classical.choice, ``Quot.sound]

/-- Stable comma-separated rendering for an axiom diagnostic. -/
private def formatAxioms (names : Array Name) : String :=
  String.intercalate ", " (names.toList.map toString)

/--
Fail unless the named declaration's transitive axiom dependencies are all
admitted by the CLRS-Lean v1 trust policy.
-/
elab "#assert_axioms " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let axioms ← liftCoreM <| Lean.collectAxioms name
  let unexpected :=
    (axioms.filter fun axiomName => !allowedAxioms.contains axiomName).qsort
      fun left right => (compare (toString left) (toString right)).isLT
  unless unexpected.isEmpty do
    throwError "{n} depends on unexpected axioms: {formatAxioms unexpected}"
