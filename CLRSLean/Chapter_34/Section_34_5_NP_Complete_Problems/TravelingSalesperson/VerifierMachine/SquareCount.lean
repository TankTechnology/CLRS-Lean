import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.VerifierMachine.FieldCount
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialClock
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# Decision-TSP verifier: square the certificate field count

Instead of multiplying a compact and possibly malicious binary header, this
branch squares the physically present certificate-field clock.  Once the
separate cardinality check identifies that count with `vertexCount`, equality
with the matrix-weight count is exactly the honest `n × n` well-formedness
condition.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPVerifier.SquareCount

open PolyBuilder FieldCount

def squareTicks (input : List TSPSym) : List Bool :=
  (exactMonomialClock 2 (certificateTicks input)).map fun _ => true

@[simp] theorem squareTicks_length (input : List TSPSym) :
    (squareTicks input).length = (certificateTicks input).length ^ 2 := by
  simp [squareTicks]

@[simp] theorem squareTicks_encode (vertices : List Nat) :
    (squareTicks (encodeTSPCertificate vertices)).length =
      vertices.length ^ 2 := by
  simp

noncomputable def squareTicksComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id squareTicks := by
  let squareExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      certificateTicksComputableInPolyTime
      (exactMonomialClock_computableInPolyTime (Γ := Bool) 2)
  let square := Classical.choice squareExists
  let boolExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch square
      (listMap_computableInPolyTime (fun _ : Unit => true))
  let machine := Classical.choice boolExists
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [squareTicks, Function.comp_def] using output }

def squareCountBits (input : List TSPSym) : List Bool :=
  encodeBinaryNat (squareTicks input).length

noncomputable def squareCountBitsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id squareCountBits := by
  let encodedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      squareTicksComputableInPolyTime
      Turing.BinaryNat.encoderComputableInPolyTime
  let machine := Classical.choice encodedExists
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [squareCountBits, Function.comp_def] using output }

@[simp] theorem squareCountBits_encode (vertices : List Nat) :
    squareCountBits (encodeTSPCertificate vertices) =
      encodeBinaryNat (vertices.length ^ 2) := by
  simp [squareCountBits]

end CLRS.Chapter34.Turing.TSPVerifier.SquareCount
