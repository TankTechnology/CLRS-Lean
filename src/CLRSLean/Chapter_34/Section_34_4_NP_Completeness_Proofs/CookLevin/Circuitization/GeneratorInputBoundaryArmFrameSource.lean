import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmStartsSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmWireReverseSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameValueMarkedRows

/-!
# Complete conjunction-frame source for verifier-input arms

The exact start coordinate is prepended to each tail-first wire row.  The
outer row boundary is then precisely the `frameEnd` of one
`AffineConjunctionFrame` encoding.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One marked start-coordinate field per candidate-length arm. -/
def verifierInputArmStartFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  unaryFrameFullValueMarkedRows
    (List.ofFn fun arm :
        Fin (W.certificateBound.eval input.length + 1) =>
      (verifierInputArmArithmeticFrame W input arm).start)

@[simp] theorem verifierInputArmStartFamily_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmStartFamily W input).rows.length =
      W.certificateBound.eval input.length + 1 := by
  simp [verifierInputArmStartFamily]

/-- Marking the existing start progression gives a concrete typed source. -/
noncomputable def verifierInputArmStartFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmStartFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  let source := verifierInputArmStartFrames_computableInPolyTime W
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      (markUnaryFrameFixedFieldRows_computableInPolyTime 1)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_apply, id_eq] at run
        rw [verifierInputArmStartFrames_eq_encode W input,
          markUnaryFrameSingleFieldRows_encode] at run
        simpa only [id_eq, verifierInputArmStartFamily] using run }

/-- Start and tail-first wire sources have the same candidate-arm index. -/
theorem verifierInputArmStart_reversedWires_aligned
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmStartFamily W input).rows.length =
      (verifierInputArmArithmeticWireReversedFamily W input).rows.length := by
  rw [verifierInputArmArithmeticWireReversedFamily_rows]
  simp

/-- Typed family whose marked stream is a sequence of complete conjunction
frame encodings. -/
def verifierInputArmArithmeticFrameFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  UnaryFrameMarkedRowParallelConcat.concatenatedFamily
    (verifierInputArmStart_reversedWires_aligned W) input

private theorem concat_ofFn_rows
    {count : Nat}
    (left right : Fin count → List UnaryFrameSym) :
    concatUnaryFrameMarkedRows (List.ofFn left) (List.ofFn right) =
      List.ofFn fun index => left index ++ right index := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [concatUnaryFrameMarkedRows]
      congr 1
      exact ih (fun index => left index.succ)
        (fun index => right index.succ)

private theorem flatMap_ofFn_apply
    {α β : Type} {count : Nat} (items : Fin count → α)
    (emit : α → List β) :
    (List.ofFn items).flatMap emit =
      (List.ofFn fun index => emit (items index)).flatten := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [List.flatMap_cons, List.flatten_cons]
      congr 1
      exact ih (fun index => items index.succ)

/-- Every marked row is the payload of the corresponding concrete
`AffineConjunctionFrame`. -/
theorem verifierInputArmArithmeticFrameFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputArmArithmeticFrameFamily W input).rows =
      List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        encodeUnaryFrameBlock
            (verifierInputArmArithmeticFrame W input arm).start ++
          encodeAffineConjunctionSources
            (verifierInputArmArithmeticFrame W input arm).wires.reverse := by
  change concatUnaryFrameMarkedRows
      ((List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        (verifierInputArmArithmeticFrame W input arm).start).map
          (fun value => encodeUnaryFrame [value]))
      (verifierInputArmArithmeticWireReversedFamily W input).rows = _
  rw [verifierInputArmArithmeticWireReversedFamily_rows]
  rw [List.map_ofFn]
  rw [concat_ofFn_rows]
  apply List.ofFn_inj.mpr
  funext arm
  unfold verifierInputArmArithmeticFrame
    encodeAffineConjunctionSources
  simp [encodeUnaryFrame, encodeUnaryFrameBlock]

/-- The public stream is exactly the established frame encoding, including
one terminal marker per frame. -/
theorem verifierInputArmArithmeticFrameFamily_encode
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierInputArmArithmeticFrameFamily W input) =
      (List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        verifierInputArmArithmeticFrame W input arm).flatMap
          encodeAffineConjunctionFrame := by
  unfold encodeUnaryFrameMarkedRowFamily
  rw [verifierInputArmArithmeticFrameFamily_rows]
  rw [flatMap_ofFn_apply, flatMap_ofFn_apply]
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext arm
  rfl

/-- One fixed polynomial-time TM2 emits the exact complete conjunction-frame
sequence for all verifier-input arms. -/
noncomputable def
    verifierInputArmArithmeticFrameFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierInputArmArithmeticFrameFamily W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact UnaryFrameMarkedRowParallelConcat.computableInPolyTime
    (verifierInputArmStartFamily_computableInPolyTime W)
    (verifierInputArmArithmeticWireReversedFamily_computableInPolyTime W)
    (verifierInputArmStart_reversedWires_aligned W)

end CLRS.Chapter34.Turing.CookLevin
