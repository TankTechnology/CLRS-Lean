import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open _root_.Turing

def runFuel : Nat → machine.Cfg → machine.Cfg
  | 0, cfg => cfg
  | fuel + 1, cfg =>
      match step cfg with
      | none => cfg
      | some next => runFuel fuel next

def runInput (fuel : Nat) (input : List (Option CircuitSym)) : machine.Cfg :=
  runFuel fuel (initList machine input)

def cleanResult (cfg : machine.Cfg) (answer : Bool) : Bool :=
  cfg.l.isNone &&
    decide (cfg.var = initialState) &&
    (cfg.stk .input).isEmpty &&
    decide (cfg.stk .output = [answer]) &&
    (cfg.stk .certificate).isEmpty &&
    (cfg.stk .values).isEmpty &&
    (cfg.stk .scratch).isEmpty &&
    (cfg.stk .gateCount).isEmpty &&
    (cfg.stk .index).isEmpty &&
    (cfg.stk .saved).isEmpty

private def trueConstant : Circuit :=
  { inputCount := 0, gates := [.const true], output := 0 }

private def inputIdentity : Circuit :=
  { inputCount := 1, gates := [.input 0], output := 0 }

private def twoInputOr : Circuit :=
  { inputCount := 2, gates := [.input 1, .input 0, .or 0 1], output := 2 }

example :
    cleanResult (runInput 200 (pairEncoding [] (encodeCircuit trueConstant)))
      true = true := by native_decide

example :
    cleanResult (runInput 200
        (pairEncoding [.constFalseMark] (encodeCircuit inputIdentity)))
      false = true := by native_decide

example :
    cleanResult (runInput 200
        (pairEncoding [.constTrueMark] (encodeCircuit inputIdentity)))
      true = true := by native_decide

example :
    cleanResult (runInput 500
        (pairEncoding [.constTrueMark, .constFalseMark]
          (encodeCircuit twoInputOr)))
      true = true := by native_decide

example :
    cleanResult (runInput 200
        (pairEncoding [.inputMark] (encodeCircuit inputIdentity)))
      false = true := by native_decide

example :
    cleanResult (runInput 200 [some .argMark, none, some .outputMark])
      false = true := by native_decide

#check verifier_run
#check successfulSteps_le
#check generalCircuitVerifierComputable

#print axioms verifier_run
#print axioms successfulSteps_le
#print axioms generalCircuitVerifierComputable

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
