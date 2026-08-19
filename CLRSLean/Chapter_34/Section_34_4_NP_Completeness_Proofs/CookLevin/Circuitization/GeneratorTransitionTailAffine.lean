import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleMapSource
import Mathlib.Tactic

/-!
# Affine source coordinates for the Cook--Levin transition tail

For one fixed verifier machine, every structural statement cost is affine in
the positive workspace height.  This file packages that fact in a reusable
two-coefficient representation, closes the final dispatch mux offset, and
turns its absolute gate index into a concrete affine unary-triple source form.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A natural affine function `constant + coefficient * input`. -/
structure TransitionAffineNat where
  constant : Nat
  coefficient : Nat
deriving DecidableEq, Repr

/-- Evaluate a natural affine function. -/
def TransitionAffineNat.eval
    (form : TransitionAffineNat) (input : Nat) : Nat :=
  form.constant + form.coefficient * input

/-- Constant affine function. -/
def TransitionAffineNat.const (value : Nat) : TransitionAffineNat :=
  { constant := value, coefficient := 0 }

/-- Pointwise sum of affine functions. -/
def TransitionAffineNat.add
    (left right : TransitionAffineNat) : TransitionAffineNat :=
  { constant := left.constant + right.constant
    coefficient := left.coefficient + right.coefficient }

/-- Constant multiple of an affine function. -/
def TransitionAffineNat.scale
    (factor : Nat) (form : TransitionAffineNat) : TransitionAffineNat :=
  { constant := factor * form.constant
    coefficient := factor * form.coefficient }

/-- Substitute `input + shift` into an affine function. -/
def TransitionAffineNat.shiftInput
    (form : TransitionAffineNat) (shift : Nat) : TransitionAffineNat :=
  { constant := form.constant + form.coefficient * shift
    coefficient := form.coefficient }

@[simp] theorem TransitionAffineNat.eval_const
    (value input : Nat) :
    (TransitionAffineNat.const value).eval input = value := by
  simp [TransitionAffineNat.const, TransitionAffineNat.eval]

@[simp] theorem TransitionAffineNat.eval_add
    (left right : TransitionAffineNat) (input : Nat) :
    (left.add right).eval input = left.eval input + right.eval input := by
  simp [TransitionAffineNat.add, TransitionAffineNat.eval]
  ring

@[simp] theorem TransitionAffineNat.eval_scale
    (factor : Nat) (form : TransitionAffineNat) (input : Nat) :
    (form.scale factor).eval input = factor * form.eval input := by
  simp [TransitionAffineNat.scale, TransitionAffineNat.eval]
  ring

@[simp] theorem TransitionAffineNat.eval_shiftInput
    (form : TransitionAffineNat) (shift input : Nat) :
    (form.shiftInput shift).eval input = form.eval (input + shift) := by
  simp [TransitionAffineNat.shiftInput, TransitionAffineNat.eval]
  ring

/-- Exact affine row-width form of one fixed machine. -/
noncomputable def transitionCfgBitAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat := by
  letI : Fintype tm.K := tm.kFin
  exact
    { constant :=
        1 + (labelCount tm + 1) + stateCount tm + Fintype.card tm.K
      coefficient :=
        ∑ k : tm.K, ((reachableAlphabet tm k).card + 2) }

/-- The affine row-width form is exact at every height. -/
@[simp] theorem transitionCfgBitAffine_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (transitionCfgBitAffine tm).eval height = cfgBitCount tm height := by
  letI : Fintype tm.K := tm.kFin
  unfold transitionCfgBitAffine TransitionAffineNat.eval cfgBitCount
  rw [show (∑ k : tm.K,
      ((height + 1) +
        height * ((reachableAlphabet tm k).card + 1))) =
      Fintype.card tm.K +
        height * (∑ k : tm.K,
          ((reachableAlphabet tm k).card + 2)) by
    calc
      (∑ k : tm.K,
          ((height + 1) +
            height * ((reachableAlphabet tm k).card + 1))) =
          ∑ k : tm.K,
            (1 + height * ((reachableAlphabet tm k).card + 2)) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = Fintype.card tm.K +
          height * (∑ k : tm.K,
            ((reachableAlphabet tm k).card + 2)) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · simp
            · symm
              exact Finset.mul_sum Finset.univ
                (fun k : tm.K => (reachableAlphabet tm k).card + 2)
                height]
  ring

/-- Exact affine structural cost of a fixed bundled statement at positive
height.  A pop contributes one gate in this regime. -/
noncomputable def compileStmtGateAffine
    (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → TransitionAffineNat
  | .push k _ continuation =>
      (TransitionAffineNat.const
        (stateCount tm + (reachableAlphabet tm k).card)).add
          (compileStmtGateAffine tm continuation)
  | .peek k _ continuation =>
      (TransitionAffineNat.const
        (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
          stateCount tm)).add
          (compileStmtGateAffine tm continuation)
  | .pop k _ continuation =>
      (TransitionAffineNat.const
        (1 + 2 * stateCount tm *
          ((reachableAlphabet tm k).card + 1) + stateCount tm)).add
          (compileStmtGateAffine tm continuation)
  | .load _ continuation =>
      (TransitionAffineNat.const (stateCount tm + stateCount tm)).add
        (compileStmtGateAffine tm continuation)
  | .branch test whenTrue whenFalse =>
      (TransitionAffineNat.const
          ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1)).add
        ((compileStmtGateAffine tm whenTrue).add
          ((compileStmtGateAffine tm whenFalse).add
            (((transitionCfgBitAffine tm).scale 3).add
              (TransitionAffineNat.const 1))))
  | .goto _ =>
      TransitionAffineNat.const (stateCount tm + (labelCount tm + 1))
  | .halt => TransitionAffineNat.const 0

/-- At positive height the affine statement form equals the exact compiler
gate count, including the one-gate nonempty pop branch. -/
theorem compileStmtGateAffine_eval
    (tm : _root_.Turing.FinTM2)
    (stmt : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (height : Nat) (hheight : 0 < height) :
    (compileStmtGateAffine tm stmt).eval height =
      compileStmtGateCost tm height stmt := by
  induction stmt with
  | halt => simp [compileStmtGateAffine, compileStmtGateCost]
  | goto label => simp [compileStmtGateAffine, compileStmtGateCost]
  | load update continuation ih =>
      simp [compileStmtGateAffine, compileStmtGateCost, ih]
  | push k emit continuation ih =>
      simp [compileStmtGateAffine, compileStmtGateCost, ih]
  | peek k update continuation ih =>
      simp [compileStmtGateAffine, compileStmtGateCost, ih]
  | pop k update continuation ih =>
      cases height with
      | zero => omega
      | succ height =>
          simp [compileStmtGateAffine, compileStmtGateCost, ih,
            popStackWireGateCost]
          ring
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [compileStmtGateAffine, compileStmtGateCost,
        ihTrue, ihFalse]
      ring

/-- Affine mux cost after substituting the positive workspace height. -/
noncomputable def transitionDispatchMuxGateAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  ((((transitionCfgBitAffine tm).scale 3).add
      (TransitionAffineNat.const 1)).shiftInput
        (maxPushesPerStep tm))

/-- Affine statement cost after substituting the workspace height. -/
noncomputable def transitionDispatchStmtGateAffine
    (tm : _root_.Turing.FinTM2)
    (label : tm.Λ) : TransitionAffineNat :=
  (compileStmtGateAffine tm (tm.m label)).shiftInput
    (maxPushesPerStep tm)

@[simp] theorem transitionDispatchMuxGateAffine_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (transitionDispatchMuxGateAffine tm).eval height =
      3 * cfgBitCount tm (workHeight tm height) + 1 := by
  simp [transitionDispatchMuxGateAffine, workHeight]

theorem transitionDispatchStmtGateAffine_eval
    (tm : _root_.Turing.FinTM2) (label : tm.Λ) (height : Nat)
    (hwork : 0 < workHeight tm height) :
    (transitionDispatchStmtGateAffine tm label).eval height =
      compileStmtGateCost tm (workHeight tm height) (tm.m label) := by
  rw [transitionDispatchStmtGateAffine,
    TransitionAffineNat.eval_shiftInput]
  simpa [workHeight] using
    compileStmtGateAffine_eval tm (tm.m label)
      (workHeight tm height) hwork

/-- Affine offset of the final mux in a fixed nonempty dispatch suffix. -/
noncomputable def transitionDispatchListFinalMuxOffsetAffine
    (tm : _root_.Turing.FinTM2) : List tm.Λ → TransitionAffineNat
  | [] => TransitionAffineNat.const 0
  | label :: labels =>
      match labels with
      | [] => transitionDispatchStmtGateAffine tm label
      | _ :: _ =>
          (transitionDispatchStmtGateAffine tm label).add
            ((transitionDispatchMuxGateAffine tm).add
              (transitionDispatchListFinalMuxOffsetAffine tm labels))

/-- The affine final-mux offset evaluates to the exact structural recurrence. -/
theorem transitionDispatchListFinalMuxOffsetAffine_eval
    (tm : _root_.Turing.FinTM2) (labels : List tm.Λ) (height : Nat)
    (hwork : 0 < workHeight tm height) :
    (transitionDispatchListFinalMuxOffsetAffine tm labels).eval height =
      transitionDispatchListFinalMuxOffset tm height labels := by
  induction labels with
  | nil => simp [transitionDispatchListFinalMuxOffsetAffine,
      transitionDispatchListFinalMuxOffset]
  | cons label labels ih =>
      cases labels with
      | nil =>
          exact transitionDispatchStmtGateAffine_eval tm label height hwork
      | cons next rest =>
          change ((transitionDispatchStmtGateAffine tm label).add
              ((transitionDispatchMuxGateAffine tm).add
                (transitionDispatchListFinalMuxOffsetAffine tm
                  (next :: rest)))).eval height =
            compileStmtGateCost tm (workHeight tm height) (tm.m label) +
              (3 * cfgBitCount tm (workHeight tm height) + 1) +
              transitionDispatchListFinalMuxOffset tm height
                (next :: rest)
          rw [TransitionAffineNat.eval_add,
            transitionDispatchStmtGateAffine_eval tm label height hwork,
            TransitionAffineNat.eval_add,
            transitionDispatchMuxGateAffine_eval, ih]
          omega

/-- Generic affine-triple seed corresponding to a transition row seed. -/
def transitionTailAffineSeed
    (seed : TransitionRowSeed) : AffineUnaryTripleSeed :=
  { first := seed.height
    second := seed.start
    third := seed.rowBase }

/-- One fixed affine source form for the absolute start of the final dispatch
mux.  The public row base deliberately has coefficient zero. -/
noncomputable def transitionFinalMuxStartForm
    (tm : _root_.Turing.FinTM2) : AffineUnaryTripleForm :=
  let offset := transitionDispatchListFinalMuxOffsetAffine tm
    (programLabels tm)
  { constant := 2 + offset.constant
    first := offset.coefficient
    second := 1
    third := 0 }

/-- The fixed affine source form emits the exact final mux start for every
transition seed whose workspace height is positive. -/
theorem transitionFinalMuxStartForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleFormValue (transitionFinalMuxStartForm tm)
        (transitionTailAffineSeed seed) =
      seed.start + 2 +
        transitionDispatchListFinalMuxOffset tm seed.height
          (programLabels tm) := by
  have hoffset := transitionDispatchListFinalMuxOffsetAffine_eval
    tm (programLabels tm) seed.height hwork
  unfold TransitionAffineNat.eval at hoffset
  unfold transitionFinalMuxStartForm transitionTailAffineSeed
    affineUnaryTripleFormValue
  simp only
  omega

/-- Final dispatched-row coordinates are therefore generated by one fixed
affine unary-triple form before the canonical arithmetic mux projection. -/
theorem transitionDispatchOutputWires_eq_affineFinalMux
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchOutputWires tm seed =
      arithmeticMuxCfgWires tm (workHeight tm seed.height)
        (affineUnaryTripleFormValue (transitionFinalMuxStartForm tm)
          (transitionTailAffineSeed seed)) := by
  rw [transitionDispatchOutputWires_eq_finalMux,
    transitionFinalMuxStartForm_value tm seed hwork]

/-! ## Concrete verifier-family source -/

/-- Transition seeds in the reusable affine source representation. -/
def verifierTransitionTailAffineSeeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineUnaryTripleSeed :=
  (verifierTransitionRowSeeds W input).map transitionTailAffineSeed

/-- Every emitted transition seed carries the common verifier height. -/
theorem verifierTransitionRowSeeds_height_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    seed.height = (verifierHeight W).eval input.length := by
  unfold verifierTransitionRowSeeds at hseed
  rw [verifierTransitionRowSeedTriples_eq_ofFn, List.map_ofFn] at hseed
  simp only [List.mem_ofFn] at hseed
  rcases hseed with ⟨index, hindex⟩
  rw [← hindex]
  simp

/-- The generic affine source consumes literally the already verified raw
transition-seed stream. -/
theorem verifierTransitionTailAffineSeedEncoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineUnaryTripleSeedFamily
        (verifierTransitionTailAffineSeeds W input) =
      verifierTransitionRowSeedFrames W input := by
  rw [verifierTransitionRowSeedFrames_eq_seeds]
  unfold verifierTransitionTailAffineSeeds
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp only [List.map_cons, encodeAffineUnaryTripleSeedFamily,
        List.flatMap_cons]
      rw [ih]
      rfl

/-- Delimiter-bearing final-mux starts for every verifier transition row. -/
noncomputable def verifierTransitionFinalMuxStartFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily [transitionFinalMuxStartForm W.machine.tm]
      (verifierTransitionTailAffineSeeds W input))

/-- The concrete frame stream contains exactly one final-mux start per
canonical transition row. -/
theorem verifierTransitionFinalMuxStartFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionFinalMuxStartFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).map fun seed =>
          seed.start + 2 +
            transitionDispatchListFinalMuxOffset W.machine.tm seed.height
              (programLabels W.machine.tm)) := by
  unfold verifierTransitionFinalMuxStartFrames
    verifierTransitionTailAffineSeeds affineUnaryTripleMapFamily
  rw [List.flatMap_map]
  congr 1
  rw [show List.flatMap
        (fun seed => affineUnaryTripleMap
          [transitionFinalMuxStartForm W.machine.tm]
          (transitionTailAffineSeed seed))
        (verifierTransitionRowSeeds W input) =
      List.flatMap
        (fun seed =>
          [seed.start + 2 +
            transitionDispatchListFinalMuxOffset W.machine.tm seed.height
              (programLabels W.machine.tm)])
        (verifierTransitionRowSeeds W input) by
    apply List.flatMap_congr
    intro seed hseed
    simp only [affineUnaryTripleMap, List.map_singleton]
    congr 1
    apply transitionFinalMuxStartForm_value
    rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
    exact Nat.add_pos_left
      (verifierHeight_eval_pos W input.length)
      (maxPushesPerStep W.machine.tm)]
  generalize verifierTransitionRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih => simp [ih]

/-- A fixed polynomial-time TM2 emits every transition row's final mux start
directly from the raw verifier word. -/
noncomputable def
    verifierTransitionFinalMuxStartFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionFinalMuxStartFrames W) := by
  let seedSource : _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineUnaryTripleSeedFamily
      (verifierTransitionTailAffineSeeds W) :=
    { tm :=
        (verifierTransitionRowSeedFrames_computableInPolyTime W).tm
      inputAlphabet :=
        (verifierTransitionRowSeedFrames_computableInPolyTime W).inputAlphabet
      outputAlphabet :=
        (verifierTransitionRowSeedFrames_computableInPolyTime W).outputAlphabet
      time :=
        (verifierTransitionRowSeedFrames_computableInPolyTime W).time
      outputsFun := fun input => by
        have run :=
          (verifierTransitionRowSeedFrames_computableInPolyTime W).outputsFun
            input
        simpa only [id_eq,
          verifierTransitionTailAffineSeedEncoding_eq W input] using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch seedSource
      (affineUnaryTripleMapFamily_computableInPolyTime
        [transitionFinalMuxStartForm W.machine.tm])
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionFinalMuxStartFrames] using run }

end CLRS.Chapter34.Turing.CookLevin
