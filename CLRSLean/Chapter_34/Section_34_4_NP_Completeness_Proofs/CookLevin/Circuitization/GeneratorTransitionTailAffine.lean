import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailCoordinates
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

/-- Exact affine cost of a complete fixed dispatch suffix. -/
noncomputable def transitionDispatchListGateAffine
    (tm : _root_.Turing.FinTM2) : List tm.Λ → TransitionAffineNat
  | [] => TransitionAffineNat.const 0
  | label :: labels =>
      (transitionDispatchStmtGateAffine tm label).add
        ((transitionDispatchMuxGateAffine tm).add
          (transitionDispatchListGateAffine tm labels))

/-- The affine suffix cost evaluates to the exact dispatch recurrence. -/
theorem transitionDispatchListGateAffine_eval
    (tm : _root_.Turing.FinTM2) (labels : List tm.Λ) (height : Nat)
    (hwork : 0 < workHeight tm height) :
    (transitionDispatchListGateAffine tm labels).eval height =
      dispatchListGateCost tm height labels := by
  induction labels with
  | nil => simp [transitionDispatchListGateAffine, dispatchListGateCost]
  | cons label labels ih =>
      rw [transitionDispatchListGateAffine,
        TransitionAffineNat.eval_add,
        transitionDispatchStmtGateAffine_eval tm label height hwork,
        TransitionAffineNat.eval_add,
        transitionDispatchMuxGateAffine_eval, ih]
      simp only [dispatchListGateCost]
      omega

/-- Exact affine cost of the complete canonical label dispatch. -/
noncomputable def transitionDispatchGateAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  transitionDispatchListGateAffine tm (programLabels tm)

@[simp] theorem transitionDispatchGateAffine_eval
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (hwork : 0 < workHeight tm height) :
    (transitionDispatchGateAffine tm).eval height =
      dispatchGateCost tm height := by
  exact transitionDispatchListGateAffine_eval tm (programLabels tm)
    height hwork

/-- Generic affine-triple seed corresponding to a transition row seed. -/
def transitionTailAffineSeed
    (seed : TransitionRowSeed) : AffineUnaryTripleSeed :=
  { first := seed.height
    second := seed.start
    third := seed.rowBase }

/-- Embed a height-affine offset as an absolute gate index by adding the row
seed's local start field. -/
def transitionAbsoluteStartForm
    (offset : TransitionAffineNat) : AffineUnaryTripleForm :=
  { constant := offset.constant
    first := offset.coefficient
    second := 1
    third := 0 }

/-- Evaluating an absolute-start form adds the runtime local gate start. -/
theorem transitionAbsoluteStartForm_value
    (offset : TransitionAffineNat) (seed : TransitionRowSeed) :
    affineUnaryTripleFormValue (transitionAbsoluteStartForm offset)
        (transitionTailAffineSeed seed) =
      seed.start + offset.eval seed.height := by
  simp [transitionAbsoluteStartForm, transitionTailAffineSeed,
    affineUnaryTripleFormValue, TransitionAffineNat.eval]
  ring

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

/-! ## Complete affine phase boundaries -/

/-- Offset from the local transition start to the first narrowing gate. -/
noncomputable def transitionNarrowStartOffsetAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  (TransitionAffineNat.const 2).add (transitionDispatchGateAffine tm)

/-- Offset to the final overflow-disjunction carry. -/
noncomputable def transitionNarrowSourceOffsetAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  (transitionNarrowStartOffsetAffine tm).add
    (TransitionAffineNat.const
      (Fintype.card tm.K * maxPushesPerStep tm))

/-- Offset to the overflow-fit negation output. -/
noncomputable def transitionFitWireOffsetAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  (transitionNarrowSourceOffsetAffine tm).add
    (TransitionAffineNat.const 1)

/-- Offset to the first public-row equality gate. -/
noncomputable def transitionEqStartOffsetAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  (transitionNarrowSourceOffsetAffine tm).add
    (TransitionAffineNat.const 2)

/-- Offset to the complete public-row equality output. -/
noncomputable def transitionEqWireOffsetAffine
    (tm : _root_.Turing.FinTM2) : TransitionAffineNat :=
  (transitionEqStartOffsetAffine tm).add
    ((transitionCfgBitAffine tm).scale 6)

/-- Absolute source forms for the five post-dispatch phase boundaries. -/
noncomputable def transitionNarrowStartForm
    (tm : _root_.Turing.FinTM2) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm (transitionNarrowStartOffsetAffine tm)

noncomputable def transitionNarrowSourceForm
    (tm : _root_.Turing.FinTM2) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm (transitionNarrowSourceOffsetAffine tm)

noncomputable def transitionFitWireForm
    (tm : _root_.Turing.FinTM2) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm (transitionFitWireOffsetAffine tm)

noncomputable def transitionEqStartForm
    (tm : _root_.Turing.FinTM2) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm (transitionEqStartOffsetAffine tm)

noncomputable def transitionEqWireForm
    (tm : _root_.Turing.FinTM2) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm (transitionEqWireOffsetAffine tm)

/-- Fixed affine table emitted once for every transition row. -/
noncomputable def transitionTailPhaseBoundaryForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  [ transitionNarrowStartForm tm,
    transitionNarrowSourceForm tm,
    transitionEqStartForm tm,
    transitionFitWireForm tm,
    transitionEqWireForm tm ]

theorem transitionNarrowStartForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleFormValue (transitionNarrowStartForm tm)
        (transitionTailAffineSeed seed) =
      transitionNarrowStart tm seed.height seed.start := by
  rw [transitionNarrowStartForm, transitionAbsoluteStartForm_value,
    transitionNarrowStartOffsetAffine, TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_const,
    transitionDispatchGateAffine_eval tm seed.height hwork]
  simp [transitionNarrowStart]
  omega

theorem transitionNarrowSourceForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleFormValue (transitionNarrowSourceForm tm)
        (transitionTailAffineSeed seed) =
      transitionNarrowSourceWire tm seed.height seed.start := by
  rw [transitionNarrowSourceForm, transitionAbsoluteStartForm_value,
    transitionNarrowSourceOffsetAffine, TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_const, transitionNarrowStartOffsetAffine,
    TransitionAffineNat.eval_add, TransitionAffineNat.eval_const,
    transitionDispatchGateAffine_eval tm seed.height hwork]
  simp [transitionNarrowSourceWire, transitionNarrowStart]
  ring

theorem transitionFitWireForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleFormValue (transitionFitWireForm tm)
        (transitionTailAffineSeed seed) =
      transitionFitWire tm seed.height seed.start := by
  rw [transitionFitWireForm, transitionAbsoluteStartForm_value,
    transitionFitWireOffsetAffine, TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_const]
  have hsource : seed.start +
      (transitionNarrowSourceOffsetAffine tm).eval seed.height =
      transitionNarrowSourceWire tm seed.height seed.start := by
    calc
      seed.start +
          (transitionNarrowSourceOffsetAffine tm).eval seed.height =
          affineUnaryTripleFormValue (transitionNarrowSourceForm tm)
            (transitionTailAffineSeed seed) := by
        symm
        simpa [transitionNarrowSourceForm] using
          transitionAbsoluteStartForm_value
            (transitionNarrowSourceOffsetAffine tm) seed
      _ = transitionNarrowSourceWire tm seed.height seed.start :=
        transitionNarrowSourceForm_value tm seed hwork
  unfold transitionFitWire
  omega

theorem transitionEqStartForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleFormValue (transitionEqStartForm tm)
        (transitionTailAffineSeed seed) =
      transitionEqStart tm seed.height seed.start := by
  rw [transitionEqStartForm, transitionAbsoluteStartForm_value,
    transitionEqStartOffsetAffine, TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_const]
  have hsource : seed.start +
      (transitionNarrowSourceOffsetAffine tm).eval seed.height =
      transitionNarrowSourceWire tm seed.height seed.start := by
    calc
      seed.start +
          (transitionNarrowSourceOffsetAffine tm).eval seed.height =
          affineUnaryTripleFormValue (transitionNarrowSourceForm tm)
            (transitionTailAffineSeed seed) := by
        symm
        simpa [transitionNarrowSourceForm] using
          transitionAbsoluteStartForm_value
            (transitionNarrowSourceOffsetAffine tm) seed
      _ = transitionNarrowSourceWire tm seed.height seed.start :=
        transitionNarrowSourceForm_value tm seed hwork
  rw [transitionNarrowSourceWire] at hsource
  unfold transitionEqStart
  omega

theorem transitionEqWireForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleFormValue (transitionEqWireForm tm)
        (transitionTailAffineSeed seed) =
      transitionEqWire tm seed.height seed.start := by
  rw [transitionEqWireForm, transitionAbsoluteStartForm_value,
    transitionEqWireOffsetAffine, TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_scale, transitionCfgBitAffine_eval]
  have heqStart : seed.start +
      (transitionEqStartOffsetAffine tm).eval seed.height =
      transitionEqStart tm seed.height seed.start := by
    calc
      seed.start +
          (transitionEqStartOffsetAffine tm).eval seed.height =
          affineUnaryTripleFormValue (transitionEqStartForm tm)
            (transitionTailAffineSeed seed) := by
        symm
        simpa [transitionEqStartForm] using
          transitionAbsoluteStartForm_value
            (transitionEqStartOffsetAffine tm) seed
      _ = transitionEqStart tm seed.height seed.start :=
        transitionEqStartForm_value tm seed hwork
  unfold transitionEqWire
  omega

/-- The five-form affine table is value-exact for every positive-workspace
transition seed. -/
theorem transitionTailPhaseBoundaryForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionTailPhaseBoundaryForms tm)
        (transitionTailAffineSeed seed) =
      [ transitionNarrowStart tm seed.height seed.start,
        transitionNarrowSourceWire tm seed.height seed.start,
        transitionEqStart tm seed.height seed.start,
        transitionFitWire tm seed.height seed.start,
        transitionEqWire tm seed.height seed.start ] := by
  simp [transitionTailPhaseBoundaryForms, affineUnaryTripleMap,
    transitionNarrowStartForm_value tm seed hwork,
    transitionNarrowSourceForm_value tm seed hwork,
    transitionEqStartForm_value tm seed hwork,
    transitionFitWireForm_value tm seed hwork,
    transitionEqWireForm_value tm seed hwork]

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

/-- Generic fixed-form affine image of every verifier transition seed. -/
noncomputable def verifierTransitionAffineMapFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame
    (affineUnaryTripleMapFamily forms
      (verifierTransitionTailAffineSeeds W input))

/-- Any verifier-fixed affine form table can be evaluated over the complete
transition seed family by one fixed polynomial-time TM2. -/
noncomputable def verifierTransitionAffineMapFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineMapFrames W forms) := by
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
      (affineUnaryTripleMapFamily_computableInPolyTime forms)
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_apply, id_eq,
          verifierTransitionAffineMapFrames] using run }

/-- Delimiter-bearing final-mux starts for every verifier transition row. -/
noncomputable def verifierTransitionFinalMuxStartFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    [transitionFinalMuxStartForm W.machine.tm] input

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
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
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
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    [transitionFinalMuxStartForm W.machine.tm]

/-- Delimiter-bearing five-coordinate phase skeleton for every verifier
transition row. -/
noncomputable def verifierTransitionTailPhaseBoundaryFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionTailPhaseBoundaryForms W.machine.tm) input

/-- The generic affine map emits the exact semantic phase coordinates in row
major order. -/
theorem verifierTransitionTailPhaseBoundaryFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionTailPhaseBoundaryFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          [ transitionNarrowStart W.machine.tm seed.height seed.start,
            transitionNarrowSourceWire W.machine.tm seed.height seed.start,
            transitionEqStart W.machine.tm seed.height seed.start,
            transitionFitWire W.machine.tm seed.height seed.start,
            transitionEqWire W.machine.tm seed.height seed.start ]) := by
  unfold verifierTransitionTailPhaseBoundaryFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  apply transitionTailPhaseBoundaryForms_value
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

/-- A fixed polynomial-time TM2 emits the complete five-coordinate tail
phase skeleton directly from the raw verifier word. -/
noncomputable def
    verifierTransitionTailPhaseBoundaryFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionTailPhaseBoundaryFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionTailPhaseBoundaryForms W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin
