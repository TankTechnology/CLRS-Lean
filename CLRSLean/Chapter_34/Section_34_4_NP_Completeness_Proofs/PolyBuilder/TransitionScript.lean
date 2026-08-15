import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DispatchController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Narrowing
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.EqFin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolPool
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Trace

/-!
# Runtime script for one local Cook--Levin transition check

This module freezes the exact five semantic phases as operand-bearing runtime
data.  It proves byte-for-byte agreement with `transitionCircuitGateTrace`
before the outer finite controller is introduced.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Runtime data for the five phases of one local transition check. -/
structure AffineTransitionScript where
  dispatch : List AffineStmtPhase
  narrowFrames : List AffineOrFinPairFrame
  narrowSource : Nat
  eqFrames : List AffineEqFinPairFrame
  finalAnd : AffineAndFinPairFrame

/-- Pure-unary suffix consumed after the statement/dispatch subcontroller.
The two `tick` markers are phase boundaries: narrowing-to-equality and
equality-to-final-conjunction. -/
def encodeAffineTransitionTail (script : AffineTransitionScript) :
    List UnaryFrameSym :=
  encodeAffineOrThenNotInput script.narrowFrames script.narrowSource ++
    [.tick] ++ encodeAffineEqFinFrames script.eqFrames ++
    [.tick] ++ encodeAffineAndFinFrames [script.finalAnd]

/-- Complete runtime input, including the reserved clean exit from the
statement/dispatch subcontroller. -/
def encodeAffineTransitionScript (script : AffineTransitionScript) :
    List AffineStmtScriptSym :=
  encodeAffineStmtTransitionInput script.dispatch
    (encodeAffineTransitionTail script)

/-- Exact forward gate bytes represented by the five runtime phases. -/
def affineTransitionGateStream (script : AffineTransitionScript) :
    List CircuitSym :=
  boolPoolGateStream ++
    affineStmtScriptGateStream script.dispatch ++
    affineOrThenNotGateStream script.narrowFrames script.narrowSource ++
    affineEqFinGateStream script.eqFrames ++
    affineAndFinGateStream [script.finalAnd]

/-- Canonical operand script extracted structurally from one semantic local
transition builder. -/
def compileTransitionScript (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    AffineTransitionScript :=
  let widened := widenCfg base current hcurrent
  let dispatched := dispatchLabels tm H widened.builder widened.constants
    widened.wires widened.valid
  let narrowed := narrowCfg dispatched.builder dispatched.wires dispatched.valid
  let prefixExtension := widened.extension.trans
    (dispatched.extension.trans narrowed.extension)
  let hnextNarrowed : next.ValidIn narrowed.builder :=
    hnext.mono prefixExtension
  let equal := cfgEq narrowed.builder narrowed.wires next narrowed.valid
    hnextNarrowed
  let disjunction := CircuitBuilder.disjunctionGateTrace
    dispatched.builder.gates.length (narrowCfgOverflowWires dispatched.wires)
  { dispatch := compileDispatchScript tm H widened.builder widened.constants
      widened.wires widened.valid
    narrowFrames := affineNarrowCfgFrames dispatched.builder.gates.length
      dispatched.wires
    narrowSource := disjunction.wire
    eqFrames := affineEqFinCanonicalFrames narrowed.builder.gates.length _
      (fun i => narrowed.wires ((cfgSlotEquivFin tm H).symm i))
      (fun i => next ((cfgSlotEquivFin tm H).symm i))
    finalAnd :=
      { right := equal.wire
        left := narrowed.fit } }

/-- Interpreting the canonical operand script yields exactly the five-phase
semantic local-transition trace, byte for byte. -/
theorem compileTransitionScript_gateStream_eq_trace
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    affineTransitionGateStream
        (compileTransitionScript tm H base current next hcurrent hnext) =
      (transitionCircuitGateTrace tm H base current next hcurrent hnext).gates.flatMap
        encodeCircuitGate := by
  simp only [compileTransitionScript, affineTransitionGateStream,
    transitionCircuitGateTrace]
  rw [compileDispatchScript_gateStream_eq_trace]
  rw [affineNarrowCfgGateStream_eq_trace]
  rw [affineEqFinCanonicalGateStream_eq_trace]
  simp [boolPoolGateStream, affineAndFinGateStream, affineAndGateStream,
    List.flatMap_append, encodeCircuitGate, List.append_assoc]

end CLRS.Chapter34.Turing.PolyBuilder
