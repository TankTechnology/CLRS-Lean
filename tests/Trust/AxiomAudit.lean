import CLRSLean.Audit.Axioms

/-!
# Native axiom audit command tests

The positive cases cover a theorem with no axioms and each axiom admitted by
the CLRS-Lean v1 trust policy.
-/

#assert_axioms Nat.add_comm
#assert_axioms propext
#assert_axioms Classical.choice
#assert_axioms Quot.sound

/--
error: Lean.ofReduceBool depends on unexpected axioms: Lean.ofReduceBool, Lean.trustCompiler
-/
#guard_msgs in
#assert_axioms Lean.ofReduceBool
