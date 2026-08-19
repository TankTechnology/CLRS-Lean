import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPredicate

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin
open CLRS.Chapter34.Turing.PolyBuilder

#check oneHotPredicateWires
#check oneHotPredicate_gates_eq
#check oneHotPredicate_wire_eq_trace
#check affineOneHotPredicateCanonicalFrames
#check affineOneHotPredicateGateStream_eq_trace
#check affineOneHotPredicate_run
#check affineOneHotPredicate_steps_le

def predicateSource : Fin 4 → CircuitBuilder.Wire := fun i => i.val
def mixedPredicate : Fin 4 → Bool := fun i => decide (i.val % 2 = 0)
def falsePredicate : Fin 4 → Bool := fun _ => false

example : affineOrFinGateStream
      (affineOneHotPredicateCanonicalFrames 9 predicateSource
        mixedPredicate) =
    (CircuitBuilder.disjunctionGateTrace 9
      (oneHotPredicateWires predicateSource mixedPredicate)).gates.flatMap
        encodeCircuitGate := by
  exact affineOneHotPredicateGateStream_eq_trace 9 _ _

example : affineOrFinGateStream
      (affineOneHotPredicateCanonicalFrames 9 predicateSource
        falsePredicate) =
    (CircuitBuilder.disjunctionGateTrace 9 []).gates.flatMap
      encodeCircuitGate := by
  simpa [oneHotPredicateWires, oneHotTruePreimage, falsePredicate] using
    affineOneHotPredicateGateStream_eq_trace 9 predicateSource falsePredicate

example : affineOrFinRevSteps
      (affineOneHotPredicateCanonicalFrames 9 predicateSource
        mixedPredicate) ≤
    100 * (encodeAffineOrFinFrames
      (affineOneHotPredicateCanonicalFrames 9 predicateSource
        mixedPredicate)).length + 3 := by
  exact affineOneHotPredicate_steps_le 9 _ _

#print axioms oneHotPredicate_gates_eq
#print axioms oneHotPredicate_wire_eq_trace
#print axioms affineOneHotPredicateGateStream_eq_trace
#print axioms affineOneHotPredicate_run
#print axioms affineOneHotPredicate_steps_le
