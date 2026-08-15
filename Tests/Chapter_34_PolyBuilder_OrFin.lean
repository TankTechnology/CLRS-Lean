import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder
open StateTransition

#check CircuitBuilder.disjunctionGateTrace
#check CircuitBuilder.disjunction_gates_eq
#check CircuitBuilder.disjunction_wire_eq_trace
#check AffineOrFinPairFrame
#check encodeAffineOrFinFrames
#check affineOrFinCanonicalFrames
#check affineOrFinCanonicalGateStream_eq_trace
#check affineOrFin_runToFinish
#check affineOrFinCanonical_run
#check affineOrFinRev_steps_le
#check AffineOrFinGroup
#check encodeAffineOrFinGroups
#check affineOrFinFamilyGateStream
#check affineOrFinCanonicalGroupsFrom
#check affineOrFinCanonicalFamilyGateStream_eq_trace
#check affineOrFinFamily_runToFinish
#check affineOrFinFamilyCanonical_run
#check affineOrFinFamilyRev_steps_le

example : affineOrFinCanonicalFrames 10 [2, 4, 9] =
    [{ left := 9, right := 10 },
     { left := 4, right := 11 },
     { left := 2, right := 12 }] := by
  native_decide

example : affineOrFinGateStream
      (affineOrFinCanonicalFrames 10 [2, 4, 9]) =
    (CircuitBuilder.disjunctionGateTrace 10 [2, 4, 9]).gates.flatMap
      encodeCircuitGate := by
  exact affineOrFinCanonicalGateStream_eq_trace 10 [2, 4, 9]

example : affineOrFinRevSteps
      (affineOrFinCanonicalFrames 10 [2, 4, 9]) ≤
    100 * (encodeAffineOrFinFrames
      (affineOrFinCanonicalFrames 10 [2, 4, 9])).length + 3 := by
  exact affineOrFinRev_steps_le _

def sampleOrFamilies : List (List CircuitBuilder.Wire) :=
  [[2, 4], [9], []]

example : affineOrFinFamilyGateStream
      (affineOrFinCanonicalGroupsFrom 10 sampleOrFamilies) =
    (CircuitBuilder.disjunctionFamilyGateTrace 10 sampleOrFamilies).flatMap
      encodeCircuitGate := by
  exact affineOrFinCanonicalFamilyGateStream_eq_trace 10 sampleOrFamilies

example (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinFamilyLoopCfg
        (encodeAffineOrFinGroups
          (affineOrFinCanonicalGroupsFrom 10 sampleOrFamilies)) output)
      (some (haltCfg affineOrFinRevProgram
        (((CircuitBuilder.disjunctionFamilyGateTrace 10 sampleOrFamilies).flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineOrFinFamilyRevSteps
        (affineOrFinCanonicalGroupsFrom 10 sampleOrFamilies)) := by
  exact affineOrFinFamilyCanonical_run 10 sampleOrFamilies output

example : affineOrFinFamilyRevSteps
      (affineOrFinCanonicalGroupsFrom 10 sampleOrFamilies) ≤
    100 * (encodeAffineOrFinGroups
      (affineOrFinCanonicalGroupsFrom 10 sampleOrFamilies)).length + 2 := by
  exact affineOrFinFamilyRev_steps_le _

#print axioms CircuitBuilder.disjunction_gates_eq
#print axioms affineOrFinCanonicalGateStream_eq_trace
#print axioms affineOrFin_runToFinish
#print axioms affineOrFinCanonical_run
#print axioms affineOrFinRev_steps_le
#print axioms affineOrFinCanonicalFamilyGateStream_eq_trace
#print axioms affineOrFinFamily_runToFinish
#print axioms affineOrFinFamilyCanonical_run
#print axioms affineOrFinFamilyRev_steps_le
