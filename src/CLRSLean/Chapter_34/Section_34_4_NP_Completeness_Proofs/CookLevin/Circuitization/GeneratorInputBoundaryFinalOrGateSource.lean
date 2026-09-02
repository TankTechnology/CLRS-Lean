import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryFinalOrPairRowsSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedOrPairFormatRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFinRuntime

/-!
# Concrete final-disjunction gate source for the verifier input boundary

This module turns the aligned arithmetic operand rows into the canonical
finite-OR frames, proves agreement with `disjunctionGateTrace`, and packages
the complete raw-input-to-circuit-byte pipeline as one fixed polynomial-time
TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Explicit tail-first frames assembled from the generated left and carry
channels. -/
def verifierInputFinalOrFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineOrFinPairFrame :=
  List.zipWith
    (fun left right => ({ left := left, right := right } :
      AffineOrFinPairFrame))
    (verifierInputFinalOrWires W input).reverse
    (verifierInputFinalOrRightValues W input)

private theorem concatUnaryFrameFullValueRows_eq_pairs
    (lefts rights : List Nat) :
    concatUnaryFrameMarkedRows
        (lefts.map fun left => encodeUnaryFrame [left])
        (rights.map fun right => encodeUnaryFrame [right]) =
      (List.zipWith
        (fun left right => ({ left := left, right := right } :
          AffineOrFinPairFrame)) lefts rights).map
        (fun frame => encodeUnaryFrame [frame.left, frame.right]) := by
  induction lefts generalizing rights with
  | nil => rfl
  | cons left lefts ih =>
      cases rights with
      | nil => rfl
      | cons right rights =>
          simp only [List.map_cons, concatUnaryFrameMarkedRows,
            List.zipWith_cons_cons]
          rw [ih]
          congr 1
          simp [encodeUnaryFrame, encodeUnaryFrameBlock,
            List.append_assoc]

/-- The generic aligned-row source has exactly the marked encoding of the
typed concrete OR frames. -/
theorem verifierInputFinalOrPairFamily_encode_eq_frames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierInputFinalOrPairFamily W input) =
      encodeAffineOrFinMarkedPairFrames
        (verifierInputFinalOrFrames W input) := by
  letI : Fintype Γ := W.alphabetFintype
  unfold encodeUnaryFrameMarkedRowFamily
    encodeAffineOrFinMarkedPairFrames
    verifierInputFinalOrFrames
  unfold verifierInputFinalOrPairFamily
  rw [UnaryFrameMarkedRowParallelConcat.concatenatedFamily_rows]
  change (concatUnaryFrameMarkedRows
      ((verifierInputFinalOrWires W input).map
        (fun value => encodeUnaryFrame [value])).reverse
      ((verifierInputFinalOrRightValues W input).map
        (fun value => encodeUnaryFrame [value]))).flatMap
        (fun row => row ++ [.frameEnd]) = _
  rw [← List.map_reverse]
  rw [concatUnaryFrameFullValueRows_eq_pairs]
  rw [List.flatMap_map]
  rfl

/-- The aligned source can therefore be exposed directly at the typed frame
interface required by the formatter. -/
noncomputable def verifierInputFinalOrFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineOrFinMarkedPairFrames
      (verifierInputFinalOrFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  let raw := verifierInputFinalOrPairFamily_computableInPolyTime W
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun input => by
        have run := raw.outputsFun input
        rw [verifierInputFinalOrPairFamily_encode_eq_frames W input] at run
        simpa only [id_eq] using run }

private theorem disjunctionGateTrace_wire_eq_start_add_length
    (start : Nat) : ∀ wires : List CircuitBuilder.Wire,
    (CircuitBuilder.disjunctionGateTrace start wires).wire =
      start + wires.length := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [CircuitBuilder.disjunctionGateTrace,
        CircuitBuilder.disjunctionGateTrace_length]

private theorem affineOrFinCanonicalFrames_eq_zipRange
    (start : Nat) : ∀ wires : List CircuitBuilder.Wire,
    affineOrFinCanonicalFrames start wires =
      List.zipWith
        (fun left offset =>
          ({ left := left, right := start + offset } :
            AffineOrFinPairFrame))
        wires.reverse (List.range wires.length) := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp only [affineOrFinCanonicalFrames, List.reverse_cons,
        List.length_cons]
      rw [List.range_succ]
      rw [List.zipWith_append (by simp)]
      rw [ih]
      simp [disjunctionGateTrace_wire_eq_start_add_length]

private theorem ofFn_add_eq_range_map (start count : Nat) :
    List.ofFn (fun offset : Fin count => start + offset.val) =
      (List.range count).map (fun offset => start + offset) := by
  apply List.ext_get
  · simp
  · intro index hleft hright
    rw [List.get_ofFn]
    simp

private theorem verifierInputFinalOrRightValues_eq_range
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrRightValues W input =
      (List.range (verifierInputFinalOrWires W input).length).map
        (fun offset => verifierInputFinalOrStart W input + offset) := by
  unfold verifierInputFinalOrRightValues
  have hlength : (verifierInputFinalOrWires W input).length =
      W.certificateBound.eval input.length + 1 := by
    simp [verifierInputFinalOrWires]
  rw [hlength]
  exact ofFn_add_eq_range_map _ _

/-- The generated arithmetic frames are precisely the canonical tail-first
frames of the semantic disjunction builder. -/
theorem verifierInputFinalOrFrames_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrFrames W input =
      affineOrFinCanonicalFrames
        (verifierInputFinalOrStart W input)
        (verifierInputFinalOrWires W input) := by
  unfold verifierInputFinalOrFrames
  rw [verifierInputFinalOrRightValues_eq_range]
  rw [List.zipWith_map_right]
  exact (affineOrFinCanonicalFrames_eq_zipRange
    (verifierInputFinalOrStart W input)
    (verifierInputFinalOrWires W input)).symm

/-- Exact delimiter-bearing input consumed by the final OR controller. -/
def verifierInputFinalOrFrameInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineOrFinFrames (verifierInputFinalOrFrames W input)

theorem verifierInputFinalOrFrameInput_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrFrameInput W input =
      encodeAffineOrFinFrames (affineOrFinCanonicalFrames
        (verifierInputFinalOrStart W input)
        (verifierInputFinalOrWires W input)) := by
  unfold verifierInputFinalOrFrameInput
  rw [verifierInputFinalOrFrames_eq_canonical]

/-- A fixed polynomial-time TM2 emits the complete canonical final-OR frame
input from the original verifier word. -/
noncomputable def verifierInputFinalOrFrameInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputFinalOrFrameInput W) := by
  letI : Fintype Γ := W.alphabetFintype
  let frames := verifierInputFinalOrFrames_computableInPolyTime W
  let formattedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch frames
      unaryFrameMarkedOrPairFormat_computableInPolyTime
  let formatted := Classical.choice formattedExists
  exact
    { tm := formatted.tm
      inputAlphabet := formatted.inputAlphabet
      outputAlphabet := formatted.outputAlphabet
      time := formatted.time
      outputsFun := fun input => by
        have run := formatted.outputsFun input
        simpa [Function.comp_def, verifierInputFinalOrFrameInput] using run }

/-- Literal circuit-byte stream of the final input-arm disjunction. -/
def verifierInputFinalOrGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List CircuitSym :=
  affineOrFinGateStream (verifierInputFinalOrFrames W input)

/-- Exact agreement with the final disjunction in the canonical semantic
input-boundary script. -/
theorem verifierInputFinalOrGateStream_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierInputFinalOrGateStream W input =
      (CircuitBuilder.disjunctionGateTrace
        (verifierInputBoundaryScript W input).finalOrStart
        (verifierInputBoundaryScript W input).finalOrWires).gates.flatMap
          encodeCircuitGate := by
  unfold verifierInputFinalOrGateStream
  rw [verifierInputFinalOrFrames_eq_canonical]
  rw [affineOrFinCanonicalGateStream_eq_trace]
  rw [verifierInputBoundaryScript_finalOrStart_eq_arithmetic]
  rw [verifierInputBoundaryScript_finalOrWires_eq_arithmetic]

/-- End-to-end fixed polynomial-time TM2 from the original verifier word to
the exact serialized final-disjunction gates. -/
noncomputable def verifierInputFinalOrGateStream_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierInputFinalOrGateStream W) := by
  letI : Fintype Γ := W.alphabetFintype
  let formatted := verifierInputFinalOrFrameInput_computableInPolyTime W
  let formattedTyped :
      _root_.Turing.TM2ComputableInPolyTime id encodeAffineOrFinFrames
        (verifierInputFinalOrFrames W) :=
    { tm := formatted.tm
      inputAlphabet := formatted.inputAlphabet
      outputAlphabet := formatted.outputAlphabet
      time := formatted.time
      outputsFun := fun input => by
        have run := formatted.outputsFun input
        simpa [verifierInputFinalOrFrameInput] using run }
  let gatesExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch formattedTyped
      affineOrFinGateStream_computableInPolyTime
  let gates := Classical.choice gatesExists
  exact
    { tm := gates.tm
      inputAlphabet := gates.inputAlphabet
      outputAlphabet := gates.outputAlphabet
      time := gates.time
      outputsFun := fun input => by
        have run := gates.outputsFun input
        simpa [Function.comp_def, verifierInputFinalOrGateStream] using run }

end CLRS.Chapter34.Turing.CookLevin
