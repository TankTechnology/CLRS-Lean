import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Batch edge lookup: aggregate projection

The enriched batch controller exposes one Boolean per query.  This fixed
streaming projection retains the leading aggregate bit, preserving the older
singleton-output interface used by the CLIQUE verifier pipeline.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup.HeadProjection

open PolyBuilder

/-- Pure stream contract of the leading-bit projection. -/
def stream : List Bool → List Bool
  | [] => []
  | bit :: _ => [bit]

/-- `false` means that the first input symbol has not yet been seen. -/
def spec : StatefulFlatMapSpec Bool Bool Bool where
  initial := false
  action seen bit := if seen then ([], true) else ([bit], true)
  finish _ := []

private theorem rewrite_from_seen (input : List Bool) :
    rewriteStatefulFlatMapFrom spec true input = [] := by
  induction input with
  | nil => rfl
  | cons bit tail ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [] ++ rewriteStatefulFlatMapFrom spec true tail = []
      simpa using ih

theorem rewrite_eq_stream (input : List Bool) :
    rewriteStatefulFlatMap spec input = stream input := by
  cases input with
  | nil => rfl
  | cons bit tail =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom]
      change [bit] ++ rewriteStatefulFlatMapFrom spec true tail = [bit]
      rw [rewrite_from_seen]
      rfl

/-- A fixed linear-time TM2 retains only the leading Boolean. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id stream := by
  let machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa only [rewrite_eq_stream] using output }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup.HeadProjection
