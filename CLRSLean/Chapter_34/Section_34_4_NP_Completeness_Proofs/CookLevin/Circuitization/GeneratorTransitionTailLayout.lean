import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailCoordinates
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyScript

/-!
# Row-seed bridge for Cook--Levin transition tails

The transition-family builder is prefix recursive, whereas the concrete seed
source is row major.  This file proves that both enumerate exactly the same
local starts.  Consequently each raw-input transition seed reconstructs all
fresh post-dispatch coordinates of the corresponding canonical runtime script.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- All post-dispatch coordinates that do not depend on the dispatched row
payload itself.  Source operands are deliberately retained in the canonical
script; this layout records its complete fresh-wire skeleton. -/
structure TransitionTailLayout where
  narrowRights : List Nat
  narrowSource : Nat
  eqCoordinates : List (Nat × Nat × Nat)
  finalAnd : AffineAndFinPairFrame
deriving DecidableEq, Repr

/-- Extract the fresh-wire skeleton from an actual runtime script. -/
def transitionScriptTailLayout
    (script : AffineTransitionScript) : TransitionTailLayout :=
  { narrowRights := script.narrowFrames.map (fun frame => frame.right)
    narrowSource := script.narrowSource
    eqCoordinates := script.eqFrames.map fun frame =>
      (frame.eqStart, frame.matched, frame.previous)
    finalAnd := script.finalAnd }

/-- Closed post-dispatch skeleton at one local transition start. -/
def transitionTailLayoutAt (tm : _root_.Turing.FinTM2)
    (height start : Nat) : TransitionTailLayout :=
  { narrowRights :=
      (List.range (Fintype.card tm.K * maxPushesPerStep tm)).map
        (fun offset => transitionNarrowStart tm height start + offset)
    narrowSource := transitionNarrowSourceWire tm height start
    eqCoordinates :=
      List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
        (transitionEqStart tm height start + 1 + 6 * coordinate.val,
          transitionEqStart tm height start + 5 + 6 * coordinate.val,
          transitionEqStart tm height start + 6 * coordinate.val)
    finalAnd := transitionFinalAndFrame tm height start }

/-- Every canonical local script has precisely the closed fresh-wire skeleton
at its input builder's current gate length. -/
theorem compileTransitionScript_tailLayout_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    transitionScriptTailLayout
        (compileTransitionScript tm height base current next hcurrent hnext) =
      transitionTailLayoutAt tm height base.gates.length := by
  unfold transitionScriptTailLayout transitionTailLayoutAt
  rw [compileTransitionScript_narrowFrameRights,
    compileTransitionScript_narrowSource_eq,
    compileTransitionScript_eqFrameCoordinates,
    compileTransitionScript_finalAnd_eq]

/-- Prefix recursion enumerates local starts in increasing row order, paying
the exact local transition cost between consecutive scripts. -/
theorem compileTransitionFamilyScripts_tailLayouts_eq_ofFn
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (T : Nat)
    (rows : Fin (T + 1) → CfgWires tm height)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (compileTransitionFamilyScripts tm height base T rows hrows).map
        transitionScriptTailLayout =
      List.ofFn fun step : Fin T =>
        transitionTailLayoutAt tm height
          (base.gates.length +
            step.val * transitionCircuitGateCost tm height) := by
  induction T generalizing base with
  | zero => rfl
  | succ T ih =>
      simp only [compileTransitionFamilyScripts, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [compileTransitionScript_tailLayout_eq]
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1
      rw [transitionCircuitFamily_gate_delta]
      simp

/-- Expand one raw-input row seed to the skeleton expected by the verified
local transition controller. -/
def expandTransitionRowSeedTailLayout
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionTailLayout :=
  transitionTailLayoutAt tm seed.height seed.start

/-- Raw-input seed order is byte-for-byte aligned with the canonical
transition-family script order at the level of all fresh tail coordinates. -/
theorem verifierTransitionRowSeeds_expand_tailLayouts_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowSeeds W input).map
        (expandTransitionRowSeedTailLayout W.machine.tm) =
      (compileTransitionFamilyScriptsAt W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length)).map
          transitionScriptTailLayout := by
  unfold verifierTransitionRowSeeds
  rw [verifierTransitionRowSeedTriples_eq_ofFn, List.map_map,
    List.map_ofFn]
  unfold compileTransitionFamilyScriptsAt
  rw [compileTransitionFamilyScripts_tailLayouts_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext row
  rw [verifierTransitionStartPolynomial_eval_eq_validity_length]
  rfl

end CLRS.Chapter34.Turing.CookLevin
