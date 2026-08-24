import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Fixed streaming head deletion

A reusable finite-state transducer drops exactly the first input symbol and
copies the remaining stream.  It is used when a controller returns a summary
symbol before a pointwise answer stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.DropHead

open PolyBuilder

def stream {Γ : Type} : List Γ → List Γ
  | [] => []
  | _ :: tail => tail

def spec (Γ : Type) : StatefulFlatMapSpec Bool Γ Γ where
  initial := false
  action seen symbol := if seen then ([symbol], true) else ([], true)
  finish _ := []

private theorem rewrite_from_seen {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMapFrom (spec Γ) true input = input := by
  induction input with
  | nil => rfl
  | cons symbol tail ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [symbol] ++
        rewriteStatefulFlatMapFrom (spec Γ) true tail = symbol :: tail
      rw [ih]
      rfl

theorem rewrite_eq_stream {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMap (spec Γ) input = stream input := by
  cases input with
  | nil => rfl
  | cons symbol tail =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom]
      change [] ++ rewriteStatefulFlatMapFrom (spec Γ) true tail = tail
      exact rewrite_from_seen tail

noncomputable def computableInPolyTime (Γ : Type) [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id (@stream Γ) := by
  let machine := statefulFlatMap_computableInPolyTime (spec Γ)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa only [rewrite_eq_stream] using output }

end CLRS.Chapter34.Turing.PolyBuilder.DropHead
