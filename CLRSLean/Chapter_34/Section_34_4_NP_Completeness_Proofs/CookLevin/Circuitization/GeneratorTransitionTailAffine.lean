import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailCoordinates
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeed
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowTailSource
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

/-! ## Fixed overflow operands of the narrowing phase -/

/-- Canonical stack/local-overflow coordinate represented by one flattened
narrowing index. -/
noncomputable def transitionOverflowCoordinate
    (tm : _root_.Turing.FinTM2)
    (index : Fin (Fintype.card tm.K * maxPushesPerStep tm)) :
    Fin (Fintype.card tm.K) × Fin (maxPushesPerStep tm) :=
  (finProdFinEquiv (m := Fintype.card tm.K)
    (n := maxPushesPerStep tm)).symm index

/-- Fixed machine stack selected by a flattened overflow coordinate. -/
noncomputable def transitionOverflowStack
    (tm : _root_.Turing.FinTM2)
    (index : Fin (Fintype.card tm.K * maxPushesPerStep tm)) : tm.K := by
  letI : Fintype tm.K := tm.kFin
  exact (Fintype.equivFin tm.K).symm
    (transitionOverflowCoordinate tm index).1

/-- Constant part of the workspace slot number inspected by narrowing. -/
noncomputable def transitionOverflowSlotConstant
    (tm : _root_.Turing.FinTM2)
    (index : Fin (Fintype.card tm.K * maxPushesPerStep tm)) : Nat :=
  let k := transitionOverflowStack tm index
  let localIndex := (transitionOverflowCoordinate tm index).2.val
  1 + (labelCount tm + 1) + stateCount tm +
    arithmeticStackOrdinal tm k +
    cfgStackBitOffsetHeightCoeff tm k * maxPushesPerStep tm +
    1 + localIndex

/-- Height coefficient of the same workspace slot number. -/
noncomputable def transitionOverflowSlotHeightCoeff
    (tm : _root_.Turing.FinTM2)
    (index : Fin (Fintype.card tm.K * maxPushesPerStep tm)) : Nat :=
  cfgStackBitOffsetHeightCoeff tm
      (transitionOverflowStack tm index) + 1

/-- The flattened overflow slot number is affine in public height. -/
theorem transitionOverflowSlot_eq_affine
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (index : Fin (Fintype.card tm.K * maxPushesPerStep tm)) :
    transitionOverflowSlotConstant tm index +
        transitionOverflowSlotHeightCoeff tm index * height =
      (cfgSlotEquivFin tm (workHeight tm height)
        (CfgSlot.stackHeight (transitionOverflowStack tm index)
          ⟨height + 1 + (transitionOverflowCoordinate tm index).2.val,
            by simp only [workHeight];
               have hlocal :=
                 (transitionOverflowCoordinate tm index).2.isLt
               omega⟩)).val := by
  rw [cfgSlotEquivFin_stackHeight_val]
  rw [cfgStackBitOffset_eq_affine]
  unfold transitionOverflowSlotConstant
    transitionOverflowSlotHeightCoeff
  simp only [workHeight]
  ring

/-- Affine wire form for a slot whose arithmetic mux-row index is itself
affine in public height. -/
noncomputable def transitionFinalMuxWireForm
    (tm : _root_.Turing.FinTM2)
    (slotConstant slotHeightCoeff : Nat) : AffineUnaryTripleForm :=
  let mux := transitionFinalMuxStartForm tm
  { constant := mux.constant + 3 + 3 * slotConstant
    first := mux.first + 3 * slotHeightCoeff
    second := 1
    third := 0 }

/-- The mux-wire form emits the exact arithmetic wire selected by an affine
slot index. -/
theorem transitionFinalMuxWireForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (slotConstant slotHeightCoeff : Nat) :
    affineUnaryTripleFormValue
        (transitionFinalMuxWireForm tm slotConstant slotHeightCoeff)
        (transitionTailAffineSeed seed) =
      affineUnaryTripleFormValue (transitionFinalMuxStartForm tm)
          (transitionTailAffineSeed seed) + 3 +
        3 * (slotConstant + slotHeightCoeff * seed.height) := by
  unfold transitionFinalMuxWireForm transitionTailAffineSeed
    affineUnaryTripleFormValue
  simp [transitionFinalMuxStartForm]
  ring

/-- One fixed affine form for every overflow-height source wire, in the
canonical pre-reversal order of `narrowCfgOverflowWires`. -/
noncomputable def transitionNarrowOverflowWireForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  List.ofFn fun index :
      Fin (Fintype.card tm.K * maxPushesPerStep tm) =>
    transitionFinalMuxWireForm tm
      (transitionOverflowSlotConstant tm index)
      (transitionOverflowSlotHeightCoeff tm index)

/-- The fixed affine table recovers every dispatched overflow wire before the
OR compiler reverses their consumption order. -/
theorem transitionNarrowOverflowWireForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionNarrowOverflowWireForms tm)
        (transitionTailAffineSeed seed) =
      narrowCfgOverflowWires
        (transitionDispatchOutputWires tm seed) := by
  rw [transitionDispatchOutputWires_eq_affineFinalMux tm seed hwork]
  unfold transitionNarrowOverflowWireForms affineUnaryTripleMap
    narrowCfgOverflowWires
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  simp only [Function.comp_apply]
  rw [transitionFinalMuxWireForm_value tm seed]
  rw [transitionOverflowSlot_eq_affine]
  rfl

/-- Forms in the actual OR-frame consumption order. -/
noncomputable def transitionNarrowLeftForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (transitionNarrowOverflowWireForms tm).reverse

/-- The source table emits exactly the narrowing frames' left operands. -/
theorem transitionNarrowLeftForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionNarrowLeftForms tm)
        (transitionTailAffineSeed seed) =
      (narrowCfgOverflowWires
        (transitionDispatchOutputWires tm seed)).reverse := by
  unfold transitionNarrowLeftForms affineUnaryTripleMap
  rw [List.map_reverse]
  exact congrArg List.reverse
    (transitionNarrowOverflowWireForms_value tm seed hwork)

/-- The OR loader stores `right + 1`; every such value is an absolute affine
form because the number of overflow coordinates is fixed by the machine. -/
noncomputable def transitionNarrowRightSuccForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  List.ofFn fun index :
      Fin (Fintype.card tm.K * maxPushesPerStep tm) =>
    transitionAbsoluteStartForm
      ((transitionNarrowStartOffsetAffine tm).add
        (TransitionAffineNat.const (index.val + 1)))

/-- The fixed table emits exactly the narrowing carry operands in their unary
loader representation. -/
theorem transitionNarrowRightSuccForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionNarrowRightSuccForms tm)
        (transitionTailAffineSeed seed) =
      List.ofFn fun index :
          Fin (Fintype.card tm.K * maxPushesPerStep tm) =>
        transitionNarrowStart tm seed.height seed.start + index.val + 1 := by
  unfold transitionNarrowRightSuccForms affineUnaryTripleMap
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  simp only [Function.comp_apply]
  rw [transitionAbsoluteStartForm_value,
    TransitionAffineNat.eval_add, TransitionAffineNat.eval_const]
  have hnarrow : seed.start +
      (transitionNarrowStartOffsetAffine tm).eval seed.height =
      transitionNarrowStart tm seed.height seed.start := by
    calc
      seed.start +
          (transitionNarrowStartOffsetAffine tm).eval seed.height =
          affineUnaryTripleFormValue (transitionNarrowStartForm tm)
            (transitionTailAffineSeed seed) := by
        symm
        simpa [transitionNarrowStartForm] using
          transitionAbsoluteStartForm_value
            (transitionNarrowStartOffsetAffine tm) seed
      _ = transitionNarrowStart tm seed.height seed.start :=
        transitionNarrowStartForm_value tm seed hwork
  omega

/-! ## Complete narrowing invocation protocol -/

/-- Zero-valued affine field used at fixed protocol positions. -/
def transitionZeroForm : AffineUnaryTripleForm :=
  { constant := 0, first := 0, second := 0, third := 0 }

/-- Five ordinary unary fields per OR frame.  The delimiter pass below turns
them into `frameEnd ; left ; 0 ; right+1 ; frameEnd`. -/
noncomputable def transitionNarrowInvocationForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  (List.zipWith
    (fun left rightSucc =>
      [transitionZeroForm, left, transitionZeroForm, rightSucc,
        transitionZeroForm])
    (transitionNarrowLeftForms tm)
    (transitionNarrowRightSuccForms tm)).flatten

/-- Semantic ordinary values represented by the fixed invocation form table. -/
def transitionNarrowInvocationValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  (List.zipWith
    (fun left rightSucc => [0, left, 0, rightSucc, 0])
    (narrowCfgOverflowWires
      (transitionDispatchOutputWires tm seed)).reverse
    (List.ofFn fun index :
        Fin (Fintype.card tm.K * maxPushesPerStep tm) =>
      transitionNarrowStart tm seed.height seed.start + index.val + 1)).flatten

private theorem affineUnaryTripleMap_invocation_zip
    (leftForms rightForms : List AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap
        ((List.zipWith
          (fun left right =>
            [transitionZeroForm, left, transitionZeroForm, right,
              transitionZeroForm])
          leftForms rightForms).flatten) seed =
      (List.zipWith
        (fun left right => [0, left, 0, right, 0])
        (affineUnaryTripleMap leftForms seed)
        (affineUnaryTripleMap rightForms seed)).flatten := by
  induction leftForms generalizing rightForms with
  | nil => simp [affineUnaryTripleMap]
  | cons left leftForms ih =>
      cases rightForms with
      | nil => simp [affineUnaryTripleMap]
      | cons right rightForms =>
          simp [affineUnaryTripleMap, transitionZeroForm,
            affineUnaryTripleFormValue]

/-- The interleaved fixed form table is byte-value exact for all narrowing
frames of one positive-workspace transition seed. -/
theorem transitionNarrowInvocationForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionNarrowInvocationForms tm)
        (transitionTailAffineSeed seed) =
      transitionNarrowInvocationValues tm seed := by
  unfold transitionNarrowInvocationForms
    transitionNarrowInvocationValues
  rw [affineUnaryTripleMap_invocation_zip]
  rw [transitionNarrowLeftForms_value tm seed hwork,
    transitionNarrowRightSuccForms_value tm seed hwork]

/-- Fixed five-position delimiter cycle for one OR invocation. -/
def transitionNarrowInvocationDelimiterTable : List UnaryFrameSym :=
  [.frameEnd, .separator, .separator, .separator, .frameEnd]

@[simp] theorem transitionNarrowInvocationDelimiterTable_length :
    transitionNarrowInvocationDelimiterTable.length = 5 := rfl

theorem transitionNarrowInvocationDelimiterTable_nonempty :
    0 < transitionNarrowInvocationDelimiterTable.length := by simp

private theorem transitionNarrowInvocationDelimiter_frames
    (frames : List AffineOrFinPairFrame) :
    encodeUnaryFrameWithDelimiterCycle
        transitionNarrowInvocationDelimiterTable
        transitionNarrowInvocationDelimiterTable_nonempty
        (frames.flatMap fun frame =>
          [0, frame.left, 0, frame.right + 1, 0]) =
      encodeAffineOrFinFrames frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
      simp [encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithDelimiterCycleFrom,
        transitionNarrowInvocationDelimiterTable,
        unaryFrameDelimiterNext, encodeAffineOrFinFrames,
        encodeAffineOrFinPairFrame, encodeUnaryFrame,
        encodeUnaryFrameBlock, List.append_assoc]
      change encodeUnaryFrameWithDelimiterCycle
          transitionNarrowInvocationDelimiterTable
          transitionNarrowInvocationDelimiterTable_nonempty
          (frames.flatMap fun frame =>
            [0, frame.left, 0, frame.right + 1, 0]) =
        encodeAffineOrFinFrames frames
      exact ih

theorem transitionNarrowInvocationValues_eq_script
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (nextRowBase : Nat) :
    transitionNarrowInvocationValues tm seed =
      (transitionScriptFromSeed tm seed nextRowBase).narrowFrames.flatMap
        fun frame => [0, frame.left, 0, frame.right + 1, 0] := by
  have map_finRange_val (n : Nat) :
      (List.finRange n).map (fun index => index.val) = List.range n := by
    rw [← List.ofFn_eq_map, List.ofFn_eq_pmap]
    simp
  have zipWith_invocation_eq_map_frames
      (lefts rights : List Nat) :
      List.zipWith (fun left rightSucc => [0, left, 0, rightSucc, 0])
          lefts (rights.map fun right => right + 1) =
        (List.zipWith
          (fun left right =>
            ({ left := left, right := right } : AffineOrFinPairFrame))
          lefts rights).map
            (fun frame => [0, frame.left, 0, frame.right + 1, 0]) := by
    induction lefts generalizing rights with
    | nil => rfl
    | cons left lefts ih =>
        cases rights with
        | nil => rfl
        | cons right rights =>
            simp only [List.map_cons, List.zipWith_cons_cons,
              List.cons.injEq, true_and]
            exact ih rights
  unfold transitionNarrowInvocationValues transitionScriptFromSeed
    transitionScriptOfDecomposition transitionScriptDecompositionFromSeed
    transitionDispatchOperandLayoutFromSeed transitionDispatchOperandLayout
    transitionTailLayoutAt
  simp only
  congr 1
  rw [List.ofFn_eq_map]
  have hrightSucc :
      (List.finRange (Fintype.card tm.K * maxPushesPerStep tm)).map
          (fun index =>
            transitionNarrowStart tm seed.height seed.start + index.val + 1) =
        ((List.range (Fintype.card tm.K * maxPushesPerStep tm)).map
          (fun offset =>
            transitionNarrowStart tm seed.height seed.start + offset)).map
          (fun right => right + 1) := by
    calc
      _ = ((List.finRange
            (Fintype.card tm.K * maxPushesPerStep tm)).map
              (fun index => index.val)).map
            (fun offset =>
              transitionNarrowStart tm seed.height seed.start + offset + 1) := by
          rw [List.map_map]
          congr 1
      _ = _ := by
        rw [map_finRange_val, List.map_map]
        congr 1
  rw [hrightSucc]
  rw [zipWith_invocation_eq_map_frames]

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

/-- Delimiter-bearing dispatched overflow operands for every verifier
transition row, already in the OR controller's reverse consumption order. -/
noncomputable def verifierTransitionNarrowLeftFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionNarrowLeftForms W.machine.tm) input

/-- The fixed affine source emits exactly the semantic narrowing-left operand
families reconstructed from the canonical dispatch output. -/
theorem verifierTransitionNarrowLeftFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionNarrowLeftFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (narrowCfgOverflowWires
            (transitionDispatchOutputWires W.machine.tm seed)).reverse) := by
  unfold verifierTransitionNarrowLeftFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  apply transitionNarrowLeftForms_value
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

/-- A fixed polynomial-time TM2 emits all dispatched overflow operands
directly from the raw verifier word. -/
noncomputable def
    verifierTransitionNarrowLeftFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionNarrowLeftFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionNarrowLeftForms W.machine.tm)

/-- Delimiter-bearing `right + 1` narrowing operands for every verifier row. -/
noncomputable def verifierTransitionNarrowRightSuccFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineMapFrames W
    (transitionNarrowRightSuccForms W.machine.tm) input

/-- Exact row-major carry operands expected by the OR unary loader. -/
theorem verifierTransitionNarrowRightSuccFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionNarrowRightSuccFrames W input =
      encodeUnaryFrame
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          List.ofFn fun index : Fin
              (Fintype.card W.machine.tm.K *
                maxPushesPerStep W.machine.tm) =>
            transitionNarrowStart W.machine.tm seed.height seed.start +
              index.val + 1) := by
  unfold verifierTransitionNarrowRightSuccFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  rw [List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro seed hseed
  apply transitionNarrowRightSuccForms_value
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

/-- A fixed polynomial-time TM2 emits all narrowing carry operands directly
from the raw verifier word. -/
noncomputable def
    verifierTransitionNarrowRightSuccFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionNarrowRightSuccFrames W) := by
  exact verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionNarrowRightSuccForms W.machine.tm)

/-! ## Complete narrowing source -/

/-- Complete delimiter-exact OR invocation stream for every transition row.
The first fixed machine evaluates the interleaved affine operand forms; the
second fixed machine rewrites the five cyclic separators into the exact
`frameEnd/separator` protocol consumed by `affineOrFinProgram`. -/
noncomputable def verifierTransitionNarrowInvocationInput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters
    transitionNarrowInvocationDelimiterTable
    transitionNarrowInvocationDelimiterTable_nonempty
    (verifierTransitionAffineMapFrames W
      (transitionNarrowInvocationForms W.machine.tm) input)

/-- Byte-exact semantics of the concrete narrowing source: its output is the
canonical ordered-OR frame encoding of every seed-derived transition script,
in row-major order. -/
theorem verifierTransitionNarrowInvocationInput_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionNarrowInvocationInput W input =
      encodeAffineOrFinFrames
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase +
              cfgBitCount W.machine.tm seed.height)).narrowFrames) := by
  unfold verifierTransitionNarrowInvocationInput
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
    affineUnaryTripleMapFamily
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame, List.flatMap_map]
  have hvalues :
      List.flatMap
          (fun seed => affineUnaryTripleMap
            (transitionNarrowInvocationForms W.machine.tm)
            (transitionTailAffineSeed seed))
          (verifierTransitionRowSeeds W input) =
        (verifierTransitionRowSeeds W input).flatMap
          (transitionNarrowInvocationValues W.machine.tm) := by
    apply List.flatMap_congr
    intro seed hseed
    apply transitionNarrowInvocationForms_value
    rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
    exact Nat.add_pos_left
      (verifierHeight_eval_pos W input.length)
      (maxPushesPerStep W.machine.tm)
  rw [hvalues]
  have hscripts :
      (verifierTransitionRowSeeds W input).flatMap
          (transitionNarrowInvocationValues W.machine.tm) =
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase +
              cfgBitCount W.machine.tm seed.height)).narrowFrames).flatMap
            (fun frame => [0, frame.left, 0, frame.right + 1, 0]) := by
    rw [List.flatMap_assoc]
    apply List.flatMap_congr
    intro seed _
    exact transitionNarrowInvocationValues_eq_script W.machine.tm seed
      (seed.rowBase + cfgBitCount W.machine.tm seed.height)
  rw [hscripts]
  exact transitionNarrowInvocationDelimiter_frames _

/-- A single fixed polynomial-time TM2 compiles the complete narrowing OR
input stream directly from the raw verifier word. -/
noncomputable def
    verifierTransitionNarrowInvocationInput_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionNarrowInvocationInput W) := by
  let valueSource := verifierTransitionAffineMapFrames_computableInPolyTime W
    (transitionNarrowInvocationForms W.machine.tm)
  let delimiterSource := unaryFrameDelimiterMap_computableInPolyTime
    transitionNarrowInvocationDelimiterTable
    transitionNarrowInvocationDelimiterTable_nonempty
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      valueSource delimiterSource
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simpa only [Function.comp_def,
          verifierTransitionNarrowInvocationInput] using run }

end CLRS.Chapter34.Turing.CookLevin
