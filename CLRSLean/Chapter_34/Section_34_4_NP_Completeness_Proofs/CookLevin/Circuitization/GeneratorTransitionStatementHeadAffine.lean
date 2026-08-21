import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineStmtScript
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementHead
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackAffine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-!
# Affine compilers for the real dispatch statement heads

Every program-label arm starts from the same widened tableau row.  At a
positive verifier height, all operands inspected by its first statement phase
are fixed affine functions of the transition seed `(height, start, rowBase)`:
state bits, the top stack cell, and the first two stack-height bits.  This file
turns those formulas into the complete tagged controller phases and proves
exact agreement with `transitionDispatchStatementHeadsFromSeed`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-! ## Widened source forms used by first phases -/

/-- Affine public-row coordinate of one state bit. -/
def transitionWidenedStateForm (tm : _root_.Turing.FinTM2)
    (state : Fin (stateCount tm)) : AffineUnaryTripleForm :=
  transitionAbsoluteRowBaseForm
    (TransitionAffineNat.const
      (1 + (labelCount tm + 1) + state.val))

/-- Affine public-row coordinate of one copied stack-height bit. -/
noncomputable def transitionWidenedStackHeightForm
    (tm : _root_.Turing.FinTM2) (k : tm.K) (index : Nat) :
    AffineUnaryTripleForm :=
  transitionAbsoluteRowBaseForm
    (((TransitionAffineNat.const (transitionEqPrefixWidth tm)).add
      (transitionStackBitOffsetAffine tm k)).add
        (TransitionAffineNat.const index))

/-- Affine public-row coordinate of one symbol bit in stack cell zero. -/
noncomputable def transitionWidenedStackCellZeroForm
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (code : Fin ((reachableAlphabet tm k).card + 1)) :
    AffineUnaryTripleForm :=
  let heightSucc : TransitionAffineNat :=
    { constant := 1, coefficient := 1 }
  transitionAbsoluteRowBaseForm
    ((((TransitionAffineNat.const (transitionEqPrefixWidth tm)).add
      (transitionStackBitOffsetAffine tm k)).add heightSucc).add
        (TransitionAffineNat.const code.val))

@[simp] theorem transitionWidenedStateForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (state : Fin (stateCount tm)) :
    affineUnaryTripleFormValue (transitionWidenedStateForm tm state)
        (transitionTailAffineSeed seed) =
      (arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).state state := by
  rw [transitionWidenedStateForm, transitionAbsoluteRowBaseForm_value]
  change seed.rowBase + _ =
    (arithmeticCfgWires tm seed.height seed.rowBase).state state
  rw [arithmeticCfgWires_state]
  simp

theorem transitionWidenedStackHeightForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (index : Fin (workHeight tm seed.height + 1))
    (hcopied : index.val < seed.height + 1) :
    affineUnaryTripleFormValue
        (transitionWidenedStackHeightForm tm k index.val)
        (transitionTailAffineSeed seed) =
      (arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stackHeight k index := by
  rw [transitionWidenedStackHeightForm,
    transitionAbsoluteRowBaseForm_value]
  change seed.rowBase + _ =
    dite (index.val < seed.height + 1)
      (fun h => (arithmeticCfgWires tm seed.height seed.rowBase).stackHeight k
        ⟨index.val, h⟩)
      (fun _ => seed.start)
  simp only [hcopied, dite_true]
  rw [arithmeticCfgWires_stackHeight]
  simp only [TransitionAffineNat.eval_add, TransitionAffineNat.eval_const,
    transitionStackBitOffsetAffine_eval]
  simp [transitionEqPrefixWidth]

theorem transitionWidenedStackCellZeroForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (code : Fin ((reachableAlphabet tm k).card + 1))
    (hheight : 0 < seed.height) :
    affineUnaryTripleFormValue
        (transitionWidenedStackCellZeroForm tm k code)
        (transitionTailAffineSeed seed) =
      (arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stackCell k
          ⟨0, Nat.add_pos_left hheight (maxPushesPerStep tm)⟩ code := by
  rw [transitionWidenedStackCellZeroForm,
    transitionAbsoluteRowBaseForm_value]
  change seed.rowBase + _ =
    dite (0 < seed.height)
      (fun h => (arithmeticCfgWires tm seed.height seed.rowBase).stackCell k
        ⟨0, h⟩ code)
      (fun _ => _)
  simp only [hheight, dite_true]
  rw [arithmeticCfgWires_stackCell]
  simp only [TransitionAffineNat.eval_add, TransitionAffineNat.eval_const,
    transitionStackBitOffsetAffine_eval]
  simp [transitionEqPrefixWidth, TransitionAffineNat.eval]
  omega

/-- At positive height a builder-free peek is literally cell zero. -/
theorem arithmeticPeekCfgWires_eq_cell_zero
    (tm : _root_.Turing.FinTM2) (height : Nat) (hheight : 0 < height)
    (falseWire trueWire : Nat) (source : CfgWires tm height) (k : tm.K) :
    arithmeticPeekCfgWires tm height falseWire trueWire source k =
      (source.stack k).cell ⟨0, hheight⟩ := by
  cases height with
  | zero => omega
  | succ height => rfl

/-- At positive height the pop phase contains exactly its one height OR. -/
theorem affinePopFrames_eq_single_of_pos
    {tm : _root_.Turing.FinTM2} {height : Nat} (hheight : 0 < height)
    (source : CfgWires tm height) (k : tm.K) :
    affinePopFrames source k =
      [{ left := (source.stack k).height 0
         right := (source.stack k).height 1 }] := by
  cases height with
  | zero => omega
  | succ height => rfl

/-! ## One real leading phase -/

/-- Symbolic first phase of one fixed statement at a height-affine dispatch
offset. -/
noncomputable def transitionStmtHeadPhaseForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    Option TransitionAffineStmtPhaseForm :=
  let start := transitionAbsoluteStartForm labelOffset
  let state := transitionWidenedStateForm tm
  match q with
  | halt => none
  | goto jump =>
      some (.oneHotMap
        (transitionAffineOneHotCanonicalGroups start state
          (stmtLabelTable tm jump)))
  | load update _ =>
      some (.oneHotMap
        (transitionAffineOneHotCanonicalGroups start state
          (stmtStateTable tm update)))
  | push k emit _ =>
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code),
          by
            apply hsupport k
            simp [stmtPushSet]⟩
      some (.oneHotMap
        (transitionAffineOneHotCanonicalGroups start state
          (fun code => encodeSupportedSymbol (symbolAt code))))
  | peek k update _ =>
      let head := transitionWidenedStackCellZeroForm tm k
      some (.oneHotPairMap
        (transitionOneHotPairAndForms state head)
        (transitionAffineOneHotPairCanonicalGroups start
          (stmtHeadStateTable tm k update)))
  | pop k _ _ =>
      some (.pop
        [{ left := transitionWidenedStackHeightForm tm k 0
           right := transitionWidenedStackHeightForm tm k 1 }])
  | branch test _ _ =>
      some (.oneHotPredicate
        (transitionAffineOneHotPredicateCanonicalFrames start state
          (stmtPredicateTable tm test)))

/-- Evaluating the symbolic head yields the literal first phase of the real
statement compiler. -/
theorem transitionStmtHeadPhaseForm_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hheight : 0 < seed.height) :
    Option.map (fun phase => phase.eval (transitionTailAffineSeed seed))
        (transitionStmtHeadPhaseForm tm labelOffset q hsupport) =
      transitionStmtHeadPhase tm (workHeight tm seed.height)
        (seed.start + labelOffset.eval seed.height)
        seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        q hsupport := by
  let source := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  have hstart :
      affineUnaryTripleFormValue (transitionAbsoluteStartForm labelOffset)
          (transitionTailAffineSeed seed) =
        seed.start + labelOffset.eval seed.height :=
    transitionAbsoluteStartForm_value labelOffset seed
  have hstate :
      (fun state => affineUnaryTripleFormValue
        (transitionWidenedStateForm tm state)
        (transitionTailAffineSeed seed)) = source.state := by
    funext state
    exact transitionWidenedStateForm_value tm seed state
  cases q with
  | halt => rfl
  | goto jump =>
      simp only [transitionStmtHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotCanonicalGroups_eval, hstart, hstate]
  | load update continuation =>
      simp only [transitionStmtHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotCanonicalGroups_eval, hstart, hstate]
  | push k emit continuation =>
      simp only [transitionStmtHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotCanonicalGroups_eval, hstart, hstate]
  | peek k update continuation =>
      have hhead :
          (fun code => affineUnaryTripleFormValue
            (transitionWidenedStackCellZeroForm tm k code)
            (transitionTailAffineSeed seed)) =
            arithmeticPeekCfgWires tm (workHeight tm seed.height)
              seed.start (seed.start + 1) source k := by
        funext code
        rw [arithmeticPeekCfgWires_eq_cell_zero tm
          (workHeight tm seed.height)
          (Nat.add_pos_left hheight (maxPushesPerStep tm))]
        exact transitionWidenedStackCellZeroForm_value tm seed k code hheight
      simp only [transitionStmtHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotPairAndFrames_eval,
        transitionAffineOneHotPairOrGroups_eval, hstart, hstate, hhead]
  | pop k update continuation =>
      have hwork : 0 < workHeight tm seed.height :=
        Nat.add_pos_left hheight (maxPushesPerStep tm)
      let zeroIndex : Fin (workHeight tm seed.height + 1) :=
        ⟨0, by omega⟩
      have hzero := transitionWidenedStackHeightForm_value tm seed k
        zeroIndex (by simp [zeroIndex])
      have hzeroIndex : zeroIndex = 0 := by
        apply Fin.ext
        simp [zeroIndex]
      rw [hzeroIndex] at hzero
      let oneIndex : Fin (workHeight tm seed.height + 1) :=
        ⟨1, by omega⟩
      have hone := transitionWidenedStackHeightForm_value tm seed k
        oneIndex (by simp [oneIndex]; omega)
      have hbound : 1 < workHeight tm seed.height + 1 := by omega
      have honeIndex : oneIndex = 1 := by
        apply Fin.ext
        change 1 = 1 % (workHeight tm seed.height + 1)
        rw [Nat.mod_eq_of_lt hbound]
      rw [honeIndex] at hone
      simp only [transitionStmtHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [affinePopFrames_eq_single_of_pos hwork]
      simp only [List.map_cons, List.map_nil]
      have hframe :
          ({ left := transitionWidenedStackHeightForm tm k 0
             right := transitionWidenedStackHeightForm tm k 1 } :
              TransitionAffineOrPairForm).eval
                (transitionTailAffineSeed seed) =
            ({ left := (source.stack k).height 0
               right := (source.stack k).height 1 } :
              AffineOrFinPairFrame) := by
        simp only [TransitionAffineOrPairForm.eval]
        apply congrArg₂ AffineOrFinPairFrame.mk
        · simpa [source, CfgBundle.stack] using hzero
        · simpa [source, CfgBundle.stack, oneIndex,
            Nat.mod_eq_of_lt hbound] using hone
      rw [hframe]
  | branch test whenTrue whenFalse =>
      simp only [transitionStmtHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotPredicateCanonicalFrames_eval,
        hstart, hstate]

/-! ## Complete fixed-label head family -/

/-- Symbolic leading phases for a fixed label suffix. -/
noncomputable def transitionDispatchStatementHeadFormsForLabels
    (tm : _root_.Turing.FinTM2) :
    TransitionAffineNat → List tm.Λ →
      List (Option TransitionAffineStmtPhaseForm)
  | _, [] => []
  | labelOffset, label :: labels =>
      transitionStmtHeadPhaseForm tm labelOffset (tm.m label)
          (stmtPushSet_program_subset tm label) ::
        transitionDispatchStatementHeadFormsForLabels tm
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm)) labels

/-- Symbolic head table of the complete canonical dispatch. -/
noncomputable def transitionDispatchStatementHeadForms
    (tm : _root_.Turing.FinTM2) :
    List (Option TransitionAffineStmtPhaseForm) :=
  transitionDispatchStatementHeadFormsForLabels tm
    (TransitionAffineNat.const 2) (programLabels tm)

theorem transitionDispatchStatementHeadFormsForLabels_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hheight : 0 < seed.height) :
    ∀ (labelOffset : TransitionAffineNat) (labels : List tm.Λ),
      (transitionDispatchStatementHeadFormsForLabels tm labelOffset labels).map
          (Option.map fun phase => phase.eval (transitionTailAffineSeed seed)) =
        transitionDispatchStatementHeads tm seed.height seed.start
          (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
          (seed.start + labelOffset.eval seed.height) labels := by
  intro labelOffset labels
  induction labels generalizing labelOffset with
  | nil => rfl
  | cons label labels ih =>
      simp only [transitionDispatchStatementHeadFormsForLabels,
        List.map_cons, transitionDispatchStatementHeads]
      rw [transitionStmtHeadPhaseForm_eval tm seed labelOffset
        (tm.m label) (stmtPushSet_program_subset tm label) hheight]
      rw [ih]
      congr 2
      rw [TransitionAffineNat.eval_add,
        TransitionAffineNat.eval_add,
        transitionDispatchStmtGateAffine_eval tm label seed.height
          (Nat.add_pos_left hheight (maxPushesPerStep tm)),
        transitionDispatchMuxGateAffine_eval]
      omega

/-- The fixed symbolic table evaluates exactly to every actual dispatch
statement head in label order. -/
theorem transitionDispatchStatementHeadForms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hheight : 0 < seed.height) :
    (transitionDispatchStatementHeadForms tm).map
        (Option.map fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionDispatchStatementHeadsFromSeed tm seed := by
  unfold transitionDispatchStatementHeadForms
    transitionDispatchStatementHeadsFromSeed
  simpa using transitionDispatchStatementHeadFormsForLabels_eval tm seed
    hheight (TransitionAffineNat.const 2) (programLabels tm)

/-- Remove the absent phase contributed by a `halt` arm. -/
noncomputable def transitionDispatchStatementHeadPhaseForms
    (tm : _root_.Turing.FinTM2) : List TransitionAffineStmtPhaseForm :=
  (transitionDispatchStatementHeadForms tm).filterMap id

private theorem map_filterMap_id_option
    {A B : Type} (f : A → B) : ∀ xs : List (Option A),
    (xs.filterMap id).map f =
      (xs.map (Option.map f)).filterMap id := by
  intro xs
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | none =>
          simpa [id] using ih
      | some value =>
          simpa [id] using congrArg (List.cons (f value)) ih

/-- Evaluating the present symbolic heads gives exactly the present actual
head phases. -/
theorem transitionDispatchStatementHeadPhaseForms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hheight : 0 < seed.height) :
    (transitionDispatchStatementHeadPhaseForms tm).map
        (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      (transitionDispatchStatementHeadsFromSeed tm seed).filterMap id := by
  unfold transitionDispatchStatementHeadPhaseForms
  rw [map_filterMap_id_option]
  rw [transitionDispatchStatementHeadForms_eval tm seed hheight]

/-! ## Raw verifier input compiler -/

/-- Complete tagged leading-phase stream for every verifier transition row.
The nonempty premise is machine-static and is needed only because the generic
fixed-delimiter source must have at least one output column. -/
noncomputable def verifierTransitionDispatchStatementHeadFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hnonempty : transitionDispatchStatementHeadPhaseForms W.machine.tm ≠ [])
    (input : List Γ) : List UnaryFrameSym :=
  verifierTransitionAffineStmtScript W
    (transitionDispatchStatementHeadPhaseForms W.machine.tm) hnonempty input

/-- The concrete head source emits the literal real dispatch heads, not a
tag-only surrogate. -/
theorem verifierTransitionDispatchStatementHeadFrames_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hnonempty : transitionDispatchStatementHeadPhaseForms W.machine.tm ≠ [])
    (input : List Γ) :
    verifierTransitionDispatchStatementHeadFrames W hnonempty input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeAffineStmtControllerScript
          ((transitionDispatchStatementHeadsFromSeed W.machine.tm seed).filterMap
            id) := by
  unfold verifierTransitionDispatchStatementHeadFrames
  rw [verifierTransitionAffineStmtScript_eq_rows]
  apply List.flatMap_congr
  intro seed hseed
  rw [transitionDispatchStatementHeadPhaseForms_eval]
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact verifierHeight_eval_pos W input.length

/-- One fixed polynomial-time TM2 compiles all real dispatch heads directly
from the original verifier input. -/
noncomputable def
    verifierTransitionDispatchStatementHeadFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hnonempty : transitionDispatchStatementHeadPhaseForms W.machine.tm ≠ []) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchStatementHeadFrames W hnonempty) :=
  verifierTransitionAffineStmtScript_computableInPolyTime W
    (transitionDispatchStatementHeadPhaseForms W.machine.tm) hnonempty

/-! ## Unconditional source, including the all-halt machine -/

/-- Canonical head-phase target without a nonempty side condition. -/
def verifierTransitionDispatchStatementHeadTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    encodeAffineStmtControllerScript
      ((transitionDispatchStatementHeadsFromSeed W.machine.tm seed).filterMap
        id)

/-- If the fixed symbolic table is empty, every real verifier head script is
empty as well. -/
theorem verifierTransitionDispatchStatementHeadTarget_eq_nil_of_forms_eq_nil
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hforms : transitionDispatchStatementHeadPhaseForms W.machine.tm = [])
    (input : List Γ) :
    verifierTransitionDispatchStatementHeadTarget W input = [] := by
  unfold verifierTransitionDispatchStatementHeadTarget
  rw [List.flatMap_eq_nil_iff]
  intro seed hseed
  have heval := transitionDispatchStatementHeadPhaseForms_eval W.machine.tm
    seed (by
      rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
      exact verifierHeight_eval_pos W input.length)
  rw [hforms] at heval
  simp only [List.map_nil] at heval
  rw [← heval]
  rfl

/-- Symbol-local eraser used only for the degenerate empty head schedule. -/
def transitionDispatchStatementHeadEraseBody (Γ : Type) :
    LoopBody Γ UnaryFrameSym where
  emit _ := []
  cost _ := 0
  emit_length_le_cost _ := le_rfl

/-- The verified bounded loop gives a concrete machine for the constant empty
output on the verifier alphabet. -/
private noncomputable def
    verifierTransitionDispatchStatementHeadEmpty_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun _ : List Γ => ([] : List UnaryFrameSym)) := by
  letI : Fintype Γ := W.alphabetFintype
  let base := boundedLoop_computableInPolyTime
    (transitionDispatchStatementHeadEraseBody Γ)
  exact
    { tm := base.tm
      inputAlphabet := base.inputAlphabet
      outputAlphabet := base.outputAlphabet
      time := base.time
      outputsFun := fun input => by
        have run := base.outputsFun input
        have hempty : input.flatMap
            (transitionDispatchStatementHeadEraseBody Γ).emit = [] := by
          simp [transitionDispatchStatementHeadEraseBody]
        rw [hempty] at run
        simpa only [id_eq, List.map_nil] using run }

/-- A concrete raw-input polynomial-time TM2 emits every real dispatch head
phase for an arbitrary verifier, including the degenerate all-halt case. -/
noncomputable def
    verifierTransitionDispatchStatementHeadTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchStatementHeadTarget W) := by
  by_cases hforms :
      transitionDispatchStatementHeadPhaseForms W.machine.tm = []
  · let base :=
      verifierTransitionDispatchStatementHeadEmpty_computableInPolyTime W
    exact
      { tm := base.tm
        inputAlphabet := base.inputAlphabet
        outputAlphabet := base.outputAlphabet
        time := base.time
        outputsFun := fun input => by
          have run := base.outputsFun input
          rw [verifierTransitionDispatchStatementHeadTarget_eq_nil_of_forms_eq_nil
            W hforms input]
          simpa only [id_eq] using run }
  · let base :=
      verifierTransitionDispatchStatementHeadFrames_computableInPolyTime W
        hforms
    exact
      { tm := base.tm
        inputAlphabet := base.inputAlphabet
        outputAlphabet := base.outputAlphabet
        time := base.time
        outputsFun := fun input => by
          have run := base.outputsFun input
          rw [verifierTransitionDispatchStatementHeadFrames_eq W hforms input]
            at run
          simpa only [id_eq,
            verifierTransitionDispatchStatementHeadTarget] using run }

end CLRS.Chapter34.Turing.CookLevin
