import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorCompleteBodyCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.ReductionMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-!
# Complete raw-input compiler for the Cook--Levin circuit encoding

The independently generated header/input/pool prefix and verifier body are
transported through a fixed two-symbol code for `CircuitSym`, concatenated by
the verified same-input closure construction, and decoded back to the exact
canonical circuit encoding.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The nine circuit symbols occupy the nine ordered pairs of unary-frame
symbols. -/
def circuitSymPairEncode : CircuitSym → UnaryFrameSym × UnaryFrameSym
  | .inputMark => (.tick, .tick)
  | .constFalseMark => (.tick, .separator)
  | .constTrueMark => (.tick, .frameEnd)
  | .notMark => (.separator, .tick)
  | .andMark => (.separator, .separator)
  | .orMark => (.separator, .frameEnd)
  | .outputMark => (.frameEnd, .tick)
  | .argMark => (.frameEnd, .separator)
  | .endMark => (.frameEnd, .frameEnd)

/-- Total inverse table for the circuit-symbol pair code. -/
def circuitSymPairDecode : UnaryFrameSym → UnaryFrameSym → CircuitSym
  | .tick, .tick => .inputMark
  | .tick, .separator => .constFalseMark
  | .tick, .frameEnd => .constTrueMark
  | .separator, .tick => .notMark
  | .separator, .separator => .andMark
  | .separator, .frameEnd => .orMark
  | .frameEnd, .tick => .outputMark
  | .frameEnd, .separator => .argMark
  | .frameEnd, .frameEnd => .endMark

@[simp] theorem circuitSymPairDecode_encode (symbol : CircuitSym) :
    circuitSymPairDecode (circuitSymPairEncode symbol).1
      (circuitSymPairEncode symbol).2 = symbol := by
  cases symbol <;> rfl

/-- One fixed polynomial-time TM2 emits the complete canonical verifier
circuit encoding directly from the original source word. -/
noncomputable def verifierCircuitEncoding_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input => encodeCircuit (verifierCircuit W input)) := by
  letI : Fintype Γ := W.alphabetFintype
  let prefixMachine := verifierCircuitPoolPrefix_computableInPolyTime W
  let bodyMachine := verifierCircuitBodyGateStream_computableInPolyTime W
  let completeMachine := fixedPairSameInputConcat_computableInPolyTime
    circuitSymPairEncode circuitSymPairDecode
    circuitSymPairDecode_encode prefixMachine bodyMachine
  exact
    { tm := completeMachine.tm
      inputAlphabet := completeMachine.inputAlphabet
      outputAlphabet := completeMachine.outputAlphabet
      time := completeMachine.time
      outputsFun := fun input => by
        have run := completeMachine.outputsFun input
        have hsemantic :
            verifierCircuitPoolPrefix W input ++
                verifierCircuitBodyGateStream W input =
              encodeCircuit (verifierCircuit W input) := by
          rw [← compileVerifierBodyScript_gateStream_eq]
          exact verifierCircuitPoolPrefix_append_body W input
        rw [hsemantic] at run
        simpa only [id_eq] using run }

/-- The explicit Cook--Levin reduction map is computed by a fixed
polynomial-time TM2. -/
noncomputable def cookLevinMap_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id (cookLevinMap W) := by
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => encodeCircuit (verifierCircuit W input))
  exact verifierCircuitEncoding_computableInPolyTime W

/-- Public chapter-level computability wrapper for the explicit map. -/
theorem cookLevinMap_polyTimeComputable
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    PolyTimeComputable (id : List Γ → List Γ)
      (id : List CircuitSym → List CircuitSym) (cookLevinMap W) :=
  ⟨cookLevinMap_computableInPolyTime W⟩

end CLRS.Chapter34.Turing.CookLevin
