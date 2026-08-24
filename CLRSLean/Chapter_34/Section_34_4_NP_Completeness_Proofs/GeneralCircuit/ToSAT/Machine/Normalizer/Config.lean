import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Basic

/-!
# Guarded circuit normalizer: named configurations
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

/-- Concrete stack family used by all phase specifications. -/
abbrev stackContents (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    ∀ stack : Stack, List (Alphabet stack)
  | .input => input
  | .output => output
  | .rows => rows
  | .inputCount => List.replicate inputCount ()
  | .gateCount => List.replicate gateCount ()
  | .operand => List.replicate operand ()
  | .saved => List.replicate saved ()
  | .outputIndex => List.replicate outputIndex ()

/-- Named constructor for configurations in exact run lemmas. -/
def cfg (label : Option Label) (state : State)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) : machine.Cfg :=
  ⟨label, state, stackContents input output rows inputCount gateCount operand saved outputIndex⟩

/-- Short name for the normalizer transition function. -/
def step : machine.Cfg → Option machine.Cfg := machine.step

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
