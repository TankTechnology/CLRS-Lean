import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.FieldStream
import CLRSLean.Chapter_34.BinaryNat.Machine
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Decision-TSP verifier: compact field counts

The certificate branch counts every vertex field.  The instance branch skips
the vertex-count and budget fields and counts only matrix weights.  Both unary
counts are then converted by the shared fixed binary encoder, so later checks
compare compact words without expanding a potentially huge malformed header.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.FieldCount

open PolyBuilder

def certificateTicks (input : List TSPSym) : List Bool :=
  input.flatMap fun symbol => if symbol = .fieldEnd then [true] else []

private def certificateSpec :
    StatefulFlatMapSpec Unit TSPSym Bool where
  initial := ()
  action _ symbol :=
    (if symbol = .fieldEnd then [true] else [], ())
  finish _ := []

private theorem certificateRewriteFrom (input : List TSPSym) :
    rewriteStatefulFlatMapFrom certificateSpec () input =
      certificateTicks input := by
  induction input with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [certificateSpec, certificateTicks] using
        congrArg ((if symbol = TSPSym.fieldEnd then [true] else []) ++ ·) ih

theorem certificateRewrite (input : List TSPSym) :
    rewriteStatefulFlatMap certificateSpec input = certificateTicks input :=
  certificateRewriteFrom input

private theorem certificateTicks_append (left right : List TSPSym) :
    certificateTicks (left ++ right) =
      certificateTicks left ++ certificateTicks right := by
  simp [certificateTicks, List.flatMap_append]

private theorem certificateTicks_bits (bits : List Bool) :
    certificateTicks (bits.map TSPSym.bit) = [] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [List.map_cons]
      change (if TSPSym.bit bit = .fieldEnd then [true] else []) ++
          certificateTicks (bits.map TSPSym.bit) = []
      rw [ih]
      cases bit <;> rfl

private theorem certificateTicks_field (value : Nat) :
    certificateTicks (encodeTSPField value) = [true] := by
  rw [encodeTSPField]
  change certificateTicks
      (.numberMark :: ((encodeBinaryNat value).map .bit ++ [.fieldEnd])) = _
  rw [show certificateTicks (.numberMark ::
        ((encodeBinaryNat value).map .bit ++ [.fieldEnd])) =
      certificateTicks ((encodeBinaryNat value).map .bit ++ [.fieldEnd]) by
    rfl]
  rw [certificateTicks_append, certificateTicks_bits]
  rfl

private theorem certificateTicks_fields (values : List Nat) :
    certificateTicks (encodeTSPFields values) =
      List.replicate values.length true := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [encodeTSPFields, List.flatMap_cons]
      rw [certificateTicks_append, certificateTicks_field]
      change [true] ++ certificateTicks (encodeTSPFields values) = _
      rw [ih]
      simp [List.replicate_succ]

@[simp] theorem certificateTicks_encode (vertices : List Nat) :
    certificateTicks (encodeTSPCertificate vertices) =
      List.replicate vertices.length true := by
  rw [encodeTSPCertificate]
  rw [show certificateTicks
        (.certificateMark :: (encodeTSPFields vertices ++ [.recordEnd])) =
      certificateTicks (encodeTSPFields vertices ++ [.recordEnd]) by rfl]
  rw [certificateTicks_append, certificateTicks_fields]
  simp [certificateTicks]

inductive WeightMode
  | beforeVertexCount
  | beforeBudget
  | weights
deriving DecidableEq, Fintype

private def nextWeightMode (mode : WeightMode) (symbol : TSPSym) : WeightMode :=
  match mode, symbol with
  | .beforeVertexCount, .fieldEnd => .beforeBudget
  | .beforeBudget, .fieldEnd => .weights
  | _, _ => mode

private def weightChunk (mode : WeightMode) (symbol : TSPSym) : List Bool :=
  match mode, symbol with
  | .weights, .fieldEnd => [true]
  | _, _ => []

def weightTicksFrom : WeightMode → List TSPSym → List Bool
  | _, [] => []
  | mode, symbol :: rest =>
      weightChunk mode symbol ++
        weightTicksFrom (nextWeightMode mode symbol) rest

def weightTicks (input : List TSPSym) : List Bool :=
  weightTicksFrom .beforeVertexCount input

private def weightSpec :
    StatefulFlatMapSpec WeightMode TSPSym Bool where
  initial := .beforeVertexCount
  action mode symbol :=
    (weightChunk mode symbol, nextWeightMode mode symbol)
  finish _ := []

private theorem weightRewriteFrom (mode : WeightMode)
    (input : List TSPSym) :
    rewriteStatefulFlatMapFrom weightSpec mode input =
      weightTicksFrom mode input := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [weightSpec, weightTicksFrom] using
        congrArg (weightChunk mode symbol ++ ·)
          (ih (nextWeightMode mode symbol))

theorem weightRewrite (input : List TSPSym) :
    rewriteStatefulFlatMap weightSpec input = weightTicks input :=
  weightRewriteFrom .beforeVertexCount input

private theorem weightTicksFrom_field (mode : WeightMode) (value : Nat)
    (rest : List TSPSym) :
    weightTicksFrom mode (encodeTSPField value ++ rest) =
      (match mode with
       | .beforeVertexCount => weightTicksFrom .beforeBudget rest
       | .beforeBudget => weightTicksFrom .weights rest
       | .weights => true :: weightTicksFrom .weights rest) := by
  unfold encodeTSPField
  induction encodeBinaryNat value generalizing mode with
  | nil => cases mode <;> rfl
  | cons bit bits ih =>
      cases mode with
      | beforeVertexCount =>
          simpa [weightTicksFrom, weightChunk, nextWeightMode] using
            ih (mode := .beforeVertexCount)
      | beforeBudget =>
          simpa [weightTicksFrom, weightChunk, nextWeightMode] using
            ih (mode := .beforeBudget)
      | weights =>
          simpa [weightTicksFrom, weightChunk, nextWeightMode] using
            ih (mode := .weights)

private theorem weightTicksFrom_weights (values : List Nat)
    (suffix : List TSPSym) :
    weightTicksFrom .weights (encodeTSPFields values ++ suffix) =
      List.replicate values.length true ++
        weightTicksFrom .weights suffix := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [encodeTSPFields, List.flatMap_cons, List.append_assoc,
        weightTicksFrom_field]
      change true :: weightTicksFrom .weights
          (encodeTSPFields values ++ suffix) = _
      rw [ih]
      simp [List.replicate_succ]

@[simp] theorem weightTicks_encode (data : TSPData) :
    weightTicks (encodeTSPData data) =
      List.replicate data.weights.length true := by
  unfold weightTicks encodeTSPData
  simp only [weightTicksFrom, weightChunk, nextWeightMode,
    List.nil_append]
  have hfields : encodeTSPFields
      (data.vertexCount :: data.budget :: data.weights) =
      encodeTSPField data.vertexCount ++
        (encodeTSPField data.budget ++ encodeTSPFields data.weights) := rfl
  rw [hfields, List.append_assoc, weightTicksFrom_field,
    List.append_assoc, weightTicksFrom_field, weightTicksFrom_weights]
  simp [weightTicksFrom, weightChunk]

noncomputable def certificateTicksComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id certificateTicks := by
  have machine := statefulFlatMap_computableInPolyTime certificateSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [certificateRewrite] at output
        exact output }

noncomputable def weightTicksComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id weightTicks := by
  have machine := statefulFlatMap_computableInPolyTime weightSpec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [weightRewrite] at output
        exact output }

def certificateCountBits (input : List TSPSym) : List Bool :=
  encodeBinaryNat (certificateTicks input).length

def weightCountBits (input : List TSPSym) : List Bool :=
  encodeBinaryNat (weightTicks input).length

noncomputable def certificateCountBitsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id certificateCountBits := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    certificateTicksComputableInPolyTime
    Turing.BinaryNat.encoderComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [certificateCountBits, Function.comp_def] using output }

noncomputable def weightCountBitsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id weightCountBits := by
  let composed := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    weightTicksComputableInPolyTime
    Turing.BinaryNat.encoderComputableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [weightCountBits, Function.comp_def] using output }

@[simp] theorem certificateCountBits_encode (vertices : List Nat) :
    certificateCountBits (encodeTSPCertificate vertices) =
      encodeBinaryNat vertices.length := by
  simp [certificateCountBits]

@[simp] theorem weightCountBits_encode (data : TSPData) :
    weightCountBits (encodeTSPData data) =
      encodeBinaryNat data.weights.length := by
  simp [weightCountBits]

end CLRS.Chapter34.Turing.TSPVerifier.FieldCount
