import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OrFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Trace

/-!
# Executable Cook--Levin stack-pop trace

Width-zero pop emits no gate.  Positive-width pop emits exactly the one OR
that merges height coordinates zero and one.  Both cases run through the same
seed-free arbitrary-OR controller.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Runtime OR frames for the zero/one-gate pop trace. -/
def affinePopFrames {tm : _root_.Turing.FinTM2} {H : Nat}
    (source : CfgWires tm H) (k : tm.K) : List AffineOrFinPairFrame :=
  match H with
  | 0 => []
  | _ + 1 =>
      [{ left := (source.stack k).height 0
         right := (source.stack k).height 1 }]

/-- Exact delimiter-bearing pop-controller input. -/
def encodeAffinePopInput {tm : _root_.Turing.FinTM2} {H : Nat}
    (source : CfgWires tm H) (k : tm.K) : List UnaryFrameSym :=
  encodeAffineOrFinFrames (affinePopFrames source k)

/-- The seed-free controller stream is exactly the semantic pop trace. -/
theorem affinePopGateStream_eq_trace
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (source : CfgWires tm H) (k : tm.K) :
    affineOrFinNoSeedGateStream (affinePopFrames source k) =
      (popCfgGateTrace source k).flatMap encodeCircuitGate := by
  cases H with
  | zero => rfl
  | succ H => simp [affinePopFrames, affineOrFinNoSeedGateStream,
      popCfgGateTrace, affineOrGateStream]

/-- One fixed machine executes zero-height and positive-height pop traces. -/
def affinePop_run {tm : _root_.Turing.FinTM2} {H : Nat}
    (source : CfgWires tm H) (k : tm.K) (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinCheckCfg (encodeAffinePopInput source k) output)
      (some (haltCfg affineOrFinRevProgram
        (((popCfgGateTrace source k).flatMap encodeCircuitGate).reverse ++
          output)))
      (affineOrFinNoSeedRevSteps (affinePopFrames source k)) := by
  simpa [encodeAffinePopInput, affinePopGateStream_eq_trace] using
    affineOrFinNoSeed_run (affinePopFrames source k) output

/-- Pop serialization is linear in its exact explicit input. -/
theorem affinePop_steps_le {tm : _root_.Turing.FinTM2} {H : Nat}
    (source : CfgWires tm H) (k : tm.K) :
    affineOrFinNoSeedRevSteps (affinePopFrames source k) ≤
      100 * (encodeAffinePopInput source k).length + 2 := by
  simpa [encodeAffinePopInput] using
    affineOrFinNoSeedRev_steps_le (affinePopFrames source k)

end CLRS.Chapter34.Turing.PolyBuilder
