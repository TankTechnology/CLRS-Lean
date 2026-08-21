import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextSemantics

/-!
# Statement head phases from an affine prefix context

Unlike the initial-head compiler, this construction may be invoked after an
arbitrary fixed statement prefix.  State operands come from the context's
normalized state family, while `peek` and `pop` operands come from the front
of its compact stack route.  The resulting phase table is still entirely
verifier-fixed and affine in the transition-row seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Runtime continuation configuration denoted by a context on one transition
row seed. -/
def TransitionStmtAffineContext.rowWires
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) :
    CfgWires tm (workHeight tm seed.height) :=
  context.wires tm (seed.start + labelOffset.eval seed.height)
    (workHeight tm seed.height) seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)

/-- One symbol coordinate at the routed top cell.  Every route produced by a
statement context has the canonical row width; `getD` keeps the form total
before that invariant is discharged. -/
def TransitionStmtAffineContext.stackCellFrontForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (code : Fin ((reachableAlphabet tm k).card + 1)) :
    AffineUnaryTripleForm :=
  (context.stackRoute tm labelOffset k).cellFrontFormRow tm k 0
    |>.getD code.val transitionZeroForm

/-- One routed height coordinate used by a later pop. -/
def TransitionStmtAffineContext.stackHeightFrontForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (position : Nat) : AffineUnaryTripleForm :=
  (context.stackRoute tm labelOffset k).heightFrontForm tm k position

/-- Symbolic first phase of a statement starting from an arbitrary affine
prefix context. -/
noncomputable def transitionStmtContextHeadPhaseForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    Option TransitionAffineStmtPhaseForm :=
  let start := context.startForm tm labelOffset
  let state := context.stateForm tm labelOffset
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
      let head := context.stackCellFrontForm tm labelOffset k
      some (.oneHotPairMap
        (transitionOneHotPairAndForms state head)
        (transitionAffineOneHotPairCanonicalGroups start
          (stmtHeadStateTable tm k update)))
  | pop k _ _ =>
      some (.pop
        [{ left := context.stackHeightFrontForm tm labelOffset k 0
           right := context.stackHeightFrontForm tm labelOffset k 1 }])
  | branch test _ _ =>
      some (.oneHotPredicate
        (transitionAffineOneHotPredicateCanonicalFrames start state
          (stmtPredicateTable tm test)))

/-- Evaluation of a context head is the literal ordinary statement head once
the two routed-front interfaces are instantiated.  Later verifier-row lemmas
derive these interfaces from the compact-route capacity and public-coordinate
bounds. -/
theorem transitionStmtContextHeadPhaseForm_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hhead : ∀ k,
      (fun code => affineUnaryTripleFormValue
        (context.stackCellFrontForm tm labelOffset k code)
        (transitionTailAffineSeed seed)) =
      arithmeticPeekCfgWires tm (workHeight tm seed.height)
        seed.start (seed.start + 1) (context.rowWires tm seed labelOffset) k)
    (hpop : ∀ k,
      [(({ left := context.stackHeightFrontForm tm labelOffset k 0
           right := context.stackHeightFrontForm tm labelOffset k 1 } :
          TransitionAffineOrPairForm).eval
            (transitionTailAffineSeed seed))] =
        affinePopFrames (context.rowWires tm seed labelOffset) k) :
    Option.map (fun phase => phase.eval (transitionTailAffineSeed seed))
        (transitionStmtContextHeadPhaseForm tm labelOffset context q
          hsupport) =
      transitionStmtHeadPhase tm (workHeight tm seed.height)
        ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height))
        seed.start (seed.start + 1)
        (context.rowWires tm seed labelOffset) q hsupport := by
  have hstart := context.startForm_value tm seed labelOffset
  have hstate :
      (fun state => affineUnaryTripleFormValue
        (context.stateForm tm labelOffset state)
        (transitionTailAffineSeed seed)) =
        (context.rowWires tm seed labelOffset).state := by
    funext state
    exact context.stateForm_eq_wires tm seed labelOffset state
  cases q with
  | halt => rfl
  | goto jump =>
      simp only [transitionStmtContextHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotCanonicalGroups_eval, hstart, hstate]
  | load update continuation =>
      simp only [transitionStmtContextHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotCanonicalGroups_eval, hstart, hstate]
  | push k emit continuation =>
      simp only [transitionStmtContextHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotCanonicalGroups_eval, hstart, hstate]
  | peek k update continuation =>
      simp only [transitionStmtContextHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotPairAndFrames_eval,
        transitionAffineOneHotPairOrGroups_eval, hstart, hstate, hhead]
  | pop k update continuation =>
      simp only [transitionStmtContextHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      exact congrArg (fun frames => some (AffineStmtPhase.pop frames))
        (hpop k)
  | branch test whenTrue whenFalse =>
      simp only [transitionStmtContextHeadPhaseForm, Option.map_some,
        TransitionAffineStmtPhaseForm.eval, transitionStmtHeadPhase]
      rw [transitionAffineOneHotPredicateCanonicalFrames_eval,
        hstart, hstate]

end CLRS.Chapter34.Turing.CookLevin
