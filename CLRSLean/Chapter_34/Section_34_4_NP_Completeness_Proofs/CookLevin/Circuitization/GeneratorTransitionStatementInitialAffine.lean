import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineStmtScriptTotal
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementHeadAffine

/-!
# Complete initial primitive blocks of dispatch statements

The first-phase compiler leaves one immediate gap for `pop`: the statement
controller always emits the pop OR and its state/head pair lookup as one
two-phase primitive block.  Both phases inspect only the original widened
state, cell zero, and the first two height bits, so the whole block is affine.
This file compiles those complete initial blocks for every program label.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- The complete first primitive block of a statement.  Every constructor has
zero or one phase except `pop`, whose primitive block contains its pop phase
and the immediately following pair lookup. -/
def transitionStmtInitialPhaseBlock
    (tm : _root_.Turing.FinTM2) (height start : Nat)
    (falseWire trueWire : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    List AffineStmtPhase :=
  match q with
  | pop k update _ =>
      let popped := arithmeticPopCfgWires tm height k falseWire trueWire
        start source
      let head := arithmeticPopHeadWires tm k falseWire trueWire height
        (source.stack k)
      let pairStart := start + popStackWireGateCost height
      [ .pop (affinePopFrames source k),
        .oneHotPairMap
          (affineOneHotPairMapAndFrames popped.state head)
          (affineOneHotPairMapOrGroups pairStart popped.state head
            (stmtHeadStateTable tm k update)) ]
  | halt =>
      (transitionStmtHeadPhase tm height start falseWire trueWire source .halt
        hsupport).toList
  | goto jump =>
      (transitionStmtHeadPhase tm height start falseWire trueWire source
        (.goto jump) hsupport).toList
  | load update continuation =>
      (transitionStmtHeadPhase tm height start falseWire trueWire source
        (.load update continuation) hsupport).toList
  | push k emit continuation =>
      (transitionStmtHeadPhase tm height start falseWire trueWire source
        (.push k emit continuation) hsupport).toList
  | peek k update continuation =>
      (transitionStmtHeadPhase tm height start falseWire trueWire source
        (.peek k update continuation) hsupport).toList
  | branch test whenTrue whenFalse =>
      (transitionStmtHeadPhase tm height start falseWire trueWire source
        (.branch test whenTrue whenFalse) hsupport).toList

/-- The initial primitive block is a literal prefix of the real recursive
statement script. -/
theorem transitionStmtInitialPhaseBlock_prefix
    (tm : _root_.Turing.FinTM2) (height start : Nat)
    (falseWire trueWire : Nat) (source : CfgWires tm height)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    transitionStmtInitialPhaseBlock tm height start falseWire trueWire source q
        hsupport <+:
      transitionStmtScript tm height falseWire trueWire start source q
        hsupport := by
  cases q <;> simp [transitionStmtInitialPhaseBlock, transitionStmtHeadPhase,
    transitionStmtScript]

/-- Symbolic affine form of the same complete initial primitive block. -/
noncomputable def transitionStmtInitialPhaseForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    List TransitionAffineStmtPhaseForm :=
  match q with
  | pop k update _ =>
      let state := transitionWidenedStateForm tm
      let head := transitionWidenedStackCellZeroForm tm k
      let pairStart := transitionAbsoluteStartForm
        (labelOffset.add (TransitionAffineNat.const 1))
      [ .pop
          [{ left := transitionWidenedStackHeightForm tm k 0
             right := transitionWidenedStackHeightForm tm k 1 }],
        .oneHotPairMap
          (transitionOneHotPairAndForms state head)
          (transitionAffineOneHotPairCanonicalGroups pairStart
            (stmtHeadStateTable tm k update)) ]
  | halt =>
      (transitionStmtHeadPhaseForm tm labelOffset .halt hsupport).toList
  | goto jump =>
      (transitionStmtHeadPhaseForm tm labelOffset (.goto jump)
        hsupport).toList
  | load update continuation =>
      (transitionStmtHeadPhaseForm tm labelOffset (.load update continuation)
        hsupport).toList
  | push k emit continuation =>
      (transitionStmtHeadPhaseForm tm labelOffset (.push k emit continuation)
        hsupport).toList
  | peek k update continuation =>
      (transitionStmtHeadPhaseForm tm labelOffset (.peek k update continuation)
        hsupport).toList
  | branch test whenTrue whenFalse =>
      (transitionStmtHeadPhaseForm tm labelOffset
        (.branch test whenTrue whenFalse) hsupport).toList

private theorem optionToList_map {A B : Type} (f : A → B)
    (value : Option A) :
    value.toList.map f = (value.map f).toList := by
  cases value <;> rfl

/-- Positive-height pop returns the original cell-zero head. -/
theorem arithmeticPopHeadWires_eq_cell_zero
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseWire trueWire : Nat) (height : Nat) (hheight : 0 < height)
    (source : StackWires tm height k) :
    arithmeticPopHeadWires tm k falseWire trueWire height source =
      source.cell ⟨0, hheight⟩ := by
  cases height with
  | zero => omega
  | succ height => rfl

/-- Affine evaluation recovers the complete real primitive block. -/
theorem transitionStmtInitialPhaseForms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hheight : 0 < seed.height) :
    (transitionStmtInitialPhaseForms tm labelOffset q hsupport).map
        (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionStmtInitialPhaseBlock tm (workHeight tm seed.height)
        (seed.start + labelOffset.eval seed.height)
        seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        q hsupport := by
  let source := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  have hwork : 0 < workHeight tm seed.height :=
    Nat.add_pos_left hheight (maxPushesPerStep tm)
  cases q with
  | pop k update continuation =>
      let start := seed.start + labelOffset.eval seed.height
      let popped := arithmeticPopCfgWires tm (workHeight tm seed.height) k
        seed.start (seed.start + 1) start source
      let head := arithmeticPopHeadWires tm k seed.start (seed.start + 1)
        (workHeight tm seed.height) (source.stack k)
      have hfirst := transitionStmtHeadPhaseForm_eval tm seed labelOffset
        (.pop k update continuation) hsupport hheight
      have hstate :
          (fun state => affineUnaryTripleFormValue
            (transitionWidenedStateForm tm state)
            (transitionTailAffineSeed seed)) = popped.state := by
        funext stateCode
        rw [transitionWidenedStateForm_value]
        rfl
      have hhead :
          (fun code => affineUnaryTripleFormValue
            (transitionWidenedStackCellZeroForm tm k code)
            (transitionTailAffineSeed seed)) = head := by
        funext code
        change affineUnaryTripleFormValue
            (transitionWidenedStackCellZeroForm tm k code)
            (transitionTailAffineSeed seed) =
          arithmeticPopHeadWires tm k seed.start (seed.start + 1)
            (workHeight tm seed.height) (source.stack k) code
        rw [arithmeticPopHeadWires_eq_cell_zero tm k seed.start
          (seed.start + 1) (workHeight tm seed.height) hwork]
        exact transitionWidenedStackCellZeroForm_value tm seed k code hheight
      have hpairStart :
          affineUnaryTripleFormValue
              (transitionAbsoluteStartForm
                (labelOffset.add (TransitionAffineNat.const 1)))
              (transitionTailAffineSeed seed) =
            start + popStackWireGateCost (workHeight tm seed.height) := by
        rw [transitionAbsoluteStartForm_value,
          TransitionAffineNat.eval_add, TransitionAffineNat.eval_const]
        cases hworkspace : workHeight tm seed.height with
        | zero => omega
        | succ workspace =>
            simp [popStackWireGateCost, start]
            omega
      have hfirstPhase :
          (TransitionAffineStmtPhaseForm.pop
              [{ left := transitionWidenedStackHeightForm tm k 0
                 right := transitionWidenedStackHeightForm tm k 1 }]).eval
              (transitionTailAffineSeed seed) =
            AffineStmtPhase.pop (affinePopFrames source k) := by
        simpa [transitionStmtHeadPhaseForm, transitionStmtHeadPhase, source]
          using hfirst
      have hfirstFrames :
          [(({ left := transitionWidenedStackHeightForm tm k 0
               right := transitionWidenedStackHeightForm tm k 1 } :
              TransitionAffineOrPairForm).eval
                (transitionTailAffineSeed seed))] =
            affinePopFrames source k := by
        simpa [TransitionAffineStmtPhaseForm.eval] using hfirstPhase
      simp only [transitionStmtInitialPhaseForms, List.map_cons, List.map_nil,
        TransitionAffineStmtPhaseForm.eval,
        transitionStmtInitialPhaseBlock]
      rw [hfirstFrames, transitionAffineOneHotPairAndFrames_eval,
        transitionAffineOneHotPairOrGroups_eval,
        hpairStart, hstate, hhead]
  | halt =>
      simpa [transitionStmtInitialPhaseForms,
        transitionStmtInitialPhaseBlock, optionToList_map] using
        congrArg Option.toList
          (transitionStmtHeadPhaseForm_eval tm seed labelOffset .halt
            hsupport hheight)
  | goto jump =>
      simpa [transitionStmtInitialPhaseForms,
        transitionStmtInitialPhaseBlock, optionToList_map] using
        congrArg Option.toList
          (transitionStmtHeadPhaseForm_eval tm seed labelOffset (.goto jump)
            hsupport hheight)
  | load update continuation =>
      simpa [transitionStmtInitialPhaseForms,
        transitionStmtInitialPhaseBlock, optionToList_map] using
        congrArg Option.toList
          (transitionStmtHeadPhaseForm_eval tm seed labelOffset
            (.load update continuation) hsupport hheight)
  | push k emit continuation =>
      simpa [transitionStmtInitialPhaseForms,
        transitionStmtInitialPhaseBlock, optionToList_map] using
        congrArg Option.toList
          (transitionStmtHeadPhaseForm_eval tm seed labelOffset
            (.push k emit continuation) hsupport hheight)
  | peek k update continuation =>
      simpa [transitionStmtInitialPhaseForms,
        transitionStmtInitialPhaseBlock, optionToList_map] using
        congrArg Option.toList
          (transitionStmtHeadPhaseForm_eval tm seed labelOffset
            (.peek k update continuation) hsupport hheight)
  | branch test whenTrue whenFalse =>
      simpa [transitionStmtInitialPhaseForms,
        transitionStmtInitialPhaseBlock, optionToList_map] using
        congrArg Option.toList
          (transitionStmtHeadPhaseForm_eval tm seed labelOffset
            (.branch test whenTrue whenFalse) hsupport hheight)

/-! ## Complete fixed-label family -/

noncomputable def transitionDispatchStatementInitialFormsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ → List TransitionAffineStmtPhaseForm
  | _, [] => []
  | labelOffset, label :: labels =>
      transitionStmtInitialPhaseForms tm labelOffset (tm.m label)
          (stmtPushSet_program_subset tm label) ++
        transitionDispatchStatementInitialFormsForLabels tm
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm)) labels

noncomputable def transitionDispatchStatementInitialForms
    (tm : _root_.Turing.FinTM2) : List TransitionAffineStmtPhaseForm :=
  transitionDispatchStatementInitialFormsForLabels tm
    (TransitionAffineNat.const 2) (programLabels tm)

def transitionDispatchStatementInitialBlocksForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    Nat → List tm.Λ → List AffineStmtPhase
  | _, [] => []
  | start, label :: labels =>
      transitionStmtInitialPhaseBlock tm (workHeight tm seed.height) start
          seed.start (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
          (tm.m label) (stmtPushSet_program_subset tm label) ++
        transitionDispatchStatementInitialBlocksForLabels tm seed
          (start +
            compileStmtGateCost tm (workHeight tm seed.height) (tm.m label) +
            (3 * cfgBitCount tm (workHeight tm seed.height) + 1)) labels

def transitionDispatchStatementInitialBlocks
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List AffineStmtPhase :=
  transitionDispatchStatementInitialBlocksForLabels tm seed (seed.start + 2)
    (programLabels tm)

theorem transitionDispatchStatementInitialFormsForLabels_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hheight : 0 < seed.height) :
    ∀ (labelOffset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchStatementInitialFormsForLabels tm labelOffset
          labels).map
          (fun phase => phase.eval (transitionTailAffineSeed seed)) =
        transitionDispatchStatementInitialBlocksForLabels tm seed
          (seed.start + labelOffset.eval seed.height) labels := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchStatementInitialFormsForLabels,
        List.map_append, transitionDispatchStatementInitialBlocksForLabels]
      rw [transitionStmtInitialPhaseForms_eval tm seed labelOffset
        (tm.m label) (stmtPushSet_program_subset tm label) hheight]
      rw [ih]
      congr 2
      rw [TransitionAffineNat.eval_add, TransitionAffineNat.eval_add,
        transitionDispatchStmtGateAffine_eval tm label seed.height
          (Nat.add_pos_left hheight (maxPushesPerStep tm)),
        transitionDispatchMuxGateAffine_eval]
      omega

theorem transitionDispatchStatementInitialForms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hheight : 0 < seed.height) :
    (transitionDispatchStatementInitialForms tm).map
        (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionDispatchStatementInitialBlocks tm seed := by
  unfold transitionDispatchStatementInitialForms
    transitionDispatchStatementInitialBlocks
  simpa using transitionDispatchStatementInitialFormsForLabels_eval tm seed
    hheight (TransitionAffineNat.const 2) (programLabels tm)

/-- Raw verifier target containing every complete initial primitive block. -/
def verifierTransitionDispatchStatementInitialBlockTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    encodeAffineStmtControllerScript
      (transitionDispatchStatementInitialBlocks W.machine.tm seed)

theorem verifierTransitionAffineStmtScriptTarget_initial_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionAffineStmtScriptTarget W
        (transitionDispatchStatementInitialForms W.machine.tm) input =
      verifierTransitionDispatchStatementInitialBlockTarget W input := by
  unfold verifierTransitionAffineStmtScriptTarget
    verifierTransitionDispatchStatementInitialBlockTarget
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchStatementInitialForms_eval]
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact verifierHeight_eval_pos W input.length

/-- One fixed polynomial-time TM2 emits all complete initial primitive blocks
directly from the verifier input. -/
noncomputable def
    verifierTransitionDispatchStatementInitialBlockTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchStatementInitialBlockTarget W) := by
  let base := verifierTransitionAffineStmtScriptTarget_computableInPolyTime W
    (transitionDispatchStatementInitialForms W.machine.tm)
  exact
    { tm := base.tm
      inputAlphabet := base.inputAlphabet
      outputAlphabet := base.outputAlphabet
      time := base.time
      outputsFun := fun input => by
        have run := base.outputsFun input
        rw [verifierTransitionAffineStmtScriptTarget_initial_eq W input]
          at run
        simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin
