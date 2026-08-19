import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction
import Mathlib.Tactic

/-!
# Runtime source for stack-cell output wires

The final conjunction of a Cook--Levin validity row refers to the last gate
of every six-gate stack-cell block.  The stack count is fixed by the verifier,
but the tableau height and the base wire are runtime data.  This module
implements the missing two-field source directly, without placing either
runtime value in finite control.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Runtime data for the stack-output source. -/
structure AffineStackOutputSourceFrame where
  height : Nat
  base : Nat
deriving DecidableEq, Repr

/-- Canonical two-field invocation. -/
def encodeAffineStackOutputSourceInvocation
    (frame : AffineStackOutputSourceFrame) : List UnaryFrameSym :=
  encodeUnaryFrame [frame.height, frame.base]

/-- Descending cell outputs of one stack, beginning with its last cell. -/
def affineStackOutputDescendingCells : Nat → Nat → List Nat
  | _, 0 => []
  | current, height + 1 =>
      current :: affineStackOutputDescendingCells (current - 6) height

/-- Descending stack/cell traversal used by the reverse-output controller. -/
def affineStackOutputDescendingWires : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | stackCount + 1, height, current =>
      affineStackOutputDescendingCells current height ++
        affineStackOutputDescendingWires stackCount height
          (current - (7 * height + 1))

/-- The last stack-cell output wire.  For empty dimensions its value is only
an internal counter seed and no wire is emitted. -/
def affineStackOutputLastWire
    (stackCount height base : Nat) : Nat :=
  base + 7 * stackCount * height + (stackCount - 1)

/-- Stack-cell output wires in public stack-major/cell-major order. -/
def affineStackOutputWires
    (stackCount height base : Nat) : List Nat :=
  (affineStackOutputDescendingWires stackCount height
    (affineStackOutputLastWire stackCount height base)).reverse

/-- Finite control.  `remainingStacks` is bounded by the fixed stack count;
the runtime height is a literal tick stack. -/
inductive AffineStackOutputFamilySourceLabel (stackCount : Nat)
  | loadHeight | saveHeight
  | addHeight (remaining : Fin (7 * stackCount + 1))
  | loadBase | incBase
  | addOffset (remaining : Fin (stackCount + 1))
  | cells (remainingStacks : Fin (stackCount + 1))
  | emitCurrent (remainingStacks : Fin (stackCount + 1))
  | saveCurrent (remainingStacks : Fin (stackCount + 1))
  | pushCurrentTick (remainingStacks : Fin (stackCount + 1))
  | pushCurrentSeparator (remainingStacks : Fin (stackCount + 1))
  | restoreCurrent (remainingStacks : Fin (stackCount + 1))
  | restoreCurrentInc (remainingStacks : Fin (stackCount + 1))
  | decCurrent (remainingStacks : Fin (stackCount + 1))
      (remaining : Fin 7)
  | afterCells (remainingStacks : Fin (stackCount + 1))
  | restoreHeight (remainingStacks : Fin (stackCount + 1))
  | decGap (remainingStacks : Fin (stackCount + 1))
  | decGapOne (remainingStacks : Fin (stackCount + 1))
  | resetGap (remainingStacks : Fin (stackCount + 1))
  | clearWork₂ | clearWork₁ | clearCurrent | clearSaved
  | finish | invalid
deriving DecidableEq, Fintype

private def affineStackOutputPred {bound : Nat}
    (remaining : Fin (bound + 1)) (_hpositive : remaining.val ≠ 0) :
    Fin (bound + 1) :=
  ⟨remaining.val - 1, by omega⟩

private def affineStackOutputDecPred
    (remaining : Fin 7) (_hpositive : remaining.val ≠ 0) : Fin 7 :=
  ⟨remaining.val - 1, by omega⟩

private def affineStackOutputSix : Fin 7 := ⟨6, by omega⟩

/-- Fixed reverse-output controller for every runtime height and base. -/
def affineStackOutputFamilySourceRevProgram (stackCount : Nat) :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineStackOutputFamilySourceLabel stackCount
  main := .loadHeight
  op
    | .loadHeight => .popInput .invalid fun
        | .tick => .saveHeight
        | .separator => .loadBase
        | .frameEnd => .invalid
    | .saveHeight => .pushWork₁ .tick
        (.addHeight ⟨7 * stackCount, by omega⟩)
    | .addHeight remaining =>
        if h : remaining.val = 0 then
          .jump .loadHeight
        else
          .inc₁ (.addHeight (affineStackOutputPred remaining h))
    | .loadBase => .popInput .invalid fun
        | .tick => .incBase
        | .separator =>
            .addOffset ⟨stackCount - 1, by omega⟩
        | .frameEnd => .invalid
    | .incBase => .inc₁ .loadBase
    | .addOffset remaining =>
        if h : remaining.val = 0 then
          .jump (.cells ⟨stackCount, by omega⟩)
        else
          .inc₁ (.addOffset (affineStackOutputPred remaining h))
    | .cells remainingStacks =>
        if h : remainingStacks.val = 0 then
          .jump .clearWork₂
        else
          .moveWork₁Work₂ (.afterCells remainingStacks) fun
            | .tick => .emitCurrent remainingStacks
            | _ => .invalid
    | .emitCurrent remainingStacks =>
        .dec₁ (.pushCurrentSeparator remainingStacks)
          (.saveCurrent remainingStacks)
    | .saveCurrent remainingStacks =>
        .inc₃ (.pushCurrentTick remainingStacks)
    | .pushCurrentTick remainingStacks =>
        .pushOutput .tick (.emitCurrent remainingStacks)
    | .pushCurrentSeparator remainingStacks =>
        .pushOutput .separator (.restoreCurrent remainingStacks)
    | .restoreCurrent remainingStacks =>
        .dec₃ (.decCurrent remainingStacks affineStackOutputSix)
          (.restoreCurrentInc remainingStacks)
    | .restoreCurrentInc remainingStacks =>
        .inc₁ (.restoreCurrent remainingStacks)
    | .decCurrent remainingStacks remaining =>
        if h : remaining.val = 0 then
          .dec₂ (.cells remainingStacks) (.cells remainingStacks)
        else
          .dec₁
            (.decCurrent remainingStacks
              (affineStackOutputDecPred remaining h))
            (.decCurrent remainingStacks
              (affineStackOutputDecPred remaining h))
    | .afterCells remainingStacks =>
        if hzero : remainingStacks.val = 0 then
          .jump .invalid
        else if hlast : remainingStacks.val = 1 then
          .jump .clearWork₂
        else
          .jump (.restoreHeight remainingStacks)
    | .restoreHeight remainingStacks =>
        .moveWork₂Work₁ (.decGapOne remainingStacks) fun
          | .tick => .decGap remainingStacks
          | _ => .invalid
    | .decGap remainingStacks =>
        .dec₁ (.restoreHeight remainingStacks)
          (.restoreHeight remainingStacks)
    | .decGapOne remainingStacks =>
        .dec₁ (.resetGap remainingStacks) (.resetGap remainingStacks)
    | .resetGap remainingStacks =>
        if h : remainingStacks.val = 0 then
          .jump .invalid
        else
          .dec₂
            (.cells (affineStackOutputPred remainingStacks h))
            (.cells (affineStackOutputPred remainingStacks h))
    | .clearWork₂ => .popWork₂ .clearWork₁ fun _ => .clearWork₂
    | .clearWork₁ => .popWork₁ .clearCurrent fun _ => .clearWork₁
    | .clearCurrent => .dec₁ .clearSaved .clearCurrent
    | .clearSaved => .dec₃ .finish .clearSaved
    | .finish => .halt
    | .invalid => .halt

private def affineStackOutputFamilySourceCfg {stackCount : Nat}
    (label : AffineStackOutputFamilySourceLabel stackCount)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    BuilderCfg (affineStackOutputFamilySourceRevProgram stackCount) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := current
  counter₂ := []
  counter₃ := saved

/-- Clean source entry. -/
def affineStackOutputFamilySourceLoopCfg (stackCount : Nat)
    (input output : List UnaryFrameSym) :
    BuilderCfg (affineStackOutputFamilySourceRevProgram stackCount) :=
  affineStackOutputFamilySourceCfg .loadHeight none none false
    input output [] [] [] []

/-- Clean redirectable exit. -/
def affineStackOutputFamilySourceFinishCfg (stackCount : Nat)
    (tail output : List UnaryFrameSym) :
    BuilderCfg (affineStackOutputFamilySourceRevProgram stackCount) :=
  affineStackOutputFamilySourceCfg .finish none none false
    tail output [] [] [] []

private theorem stackOutput_replicate_append_cons {α : Type}
    (value : α) (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem stackOutput_flip_bind_some {σ : Type}
    (f : σ → Option σ) (cfg : σ) :
    flip bind f (some cfg) = f cfg := rfl

private theorem stackOutput_iterate_bind_eq {σ : Type}
    (f : σ → Option σ) (steps : Nat) (cfg : Option σ) :
    (flip bind f)^[steps] cfg =
      (flip Option.bind f)^[steps] cfg := by
  have hfun : flip bind f = flip Option.bind f := by
    funext option
    cases option <;> rfl
  rw [hfun]

private theorem affineStackOutput_addHeightFrom_eval
    (stackCount remaining : Nat)
    (hremaining : remaining < 7 * stackCount + 1)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[remaining + 1]
      (some (affineStackOutputFamilySourceCfg
        (.addHeight ⟨remaining, hremaining⟩) buffer₁ buffer₂ test
        input output work₁ work₂ current saved)) =
      some (affineStackOutputFamilySourceCfg .loadHeight
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate remaining () ++ current) saved) := by
  induction remaining generalizing current with
  | zero => rfl
  | succ remaining ih =>
      rw [show remaining + 1 + 1 = (remaining + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineStackOutputFamilySourceRevProgram stackCount)))^[remaining + 1]
          (some (affineStackOutputFamilySourceCfg
            (.addHeight ⟨remaining, by omega⟩) buffer₁ buffer₂ test
            input output work₁ work₂ (() :: current) saved)) = _
      simpa only [List.replicate_succ, stackOutput_replicate_append_cons,
        List.cons_append, Nat.add_assoc] using
        ih (by omega) (() :: current)

private def affineStackOutput_loadHeight_one
    (stackCount : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (rest output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg .loadHeight buffer₁ buffer₂ test
        (.tick :: rest) output work₁ work₂ current saved)
      (some (affineStackOutputFamilySourceCfg .loadHeight
        (some .tick) buffer₂ test rest output (.tick :: work₁) work₂
        (List.replicate (7 * stackCount) () ++ current) saved))
      (7 * stackCount + 3) := by
  let afterPop := affineStackOutputFamilySourceCfg
    (stackCount := stackCount) .saveHeight (some .tick) buffer₂ test
    rest output work₁ work₂ current saved
  let beforeAdd := affineStackOutputFamilySourceCfg
    (stackCount := stackCount)
    (.addHeight ⟨7 * stackCount, by omega⟩)
    (some .tick) buffer₂ test rest output (.tick :: work₁) work₂
    current saved
  have hprefix : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg .loadHeight buffer₁ buffer₂ test
        (.tick :: rest) output work₁ work₂ current saved)
      (some beforeAdd) 2 := by
    exact ⟨⟨2, rfl⟩, le_rfl⟩
  have hadd : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      beforeAdd
      (some (affineStackOutputFamilySourceCfg .loadHeight
        (some .tick) buffer₂ test rest output (.tick :: work₁) work₂
        (List.replicate (7 * stackCount) () ++ current) saved))
      (7 * stackCount + 1) := by
    exact ⟨⟨7 * stackCount + 1, by
      simpa [beforeAdd] using
        affineStackOutput_addHeightFrom_eval stackCount (7 * stackCount)
          (by omega) (some .tick) buffer₂ test rest output
          (.tick :: work₁) work₂ current saved⟩, le_rfl⟩
  convert EvalsToInTime.trans
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      2 (7 * stackCount + 1) _ beforeAdd _ hprefix hadd using 1

private def affineStackOutputHeightLoadSteps
    (stackCount height : Nat) : Nat :=
  (7 * stackCount + 3) * height + 1

private def affineStackOutput_loadHeight
    (stackCount height : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg .loadHeight buffer₁ buffer₂ test
        (encodeUnaryFrameBlock height ++ tail) output work₁ work₂
        current saved)
      (some (affineStackOutputFamilySourceCfg .loadBase
        (some .separator) buffer₂ test tail output
        (List.replicate height .tick ++ work₁) work₂
        (List.replicate (7 * stackCount * height) () ++ current) saved))
      (affineStackOutputHeightLoadSteps stackCount height) := by
  induction height generalizing buffer₁ work₁ current with
  | zero => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | succ height ih =>
      let rest := encodeUnaryFrameBlock height ++ tail
      let nextCurrent := List.replicate (7 * stackCount) () ++ current
      let nextWork := .tick :: work₁
      have hone := affineStackOutput_loadHeight_one stackCount buffer₁ buffer₂
        test rest output work₁ work₂ current saved
      have hrest := ih (some .tick) nextWork nextCurrent
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        (7 * stackCount + 3)
        (affineStackOutputHeightLoadSteps stackCount height)
        _ (affineStackOutputFamilySourceCfg .loadHeight
          (some .tick) buffer₂ test rest output nextWork work₂
          nextCurrent saved) _ hone hrest
      convert full using 1
      · simp [encodeUnaryFrameBlock, rest, List.replicate_succ]
      · simp only [List.replicate_succ, nextWork, nextCurrent,
          stackOutput_replicate_append_cons, List.cons_append]
        simp only [← List.append_assoc, ← List.replicate_add]
        congr 3
      · simp [affineStackOutputHeightLoadSteps]
        ring

private theorem affineStackOutput_addOffsetFrom_eval
    (stackCount remaining : Nat)
    (hremaining : remaining < stackCount + 1)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[remaining + 1]
      (some (affineStackOutputFamilySourceCfg
        (.addOffset ⟨remaining, hremaining⟩) buffer₁ buffer₂ test
        input output work₁ work₂ current saved)) =
      some (affineStackOutputFamilySourceCfg
        (.cells ⟨stackCount, by omega⟩) buffer₁ buffer₂ test
        input output work₁ work₂
        (List.replicate remaining () ++ current) saved) := by
  induction remaining generalizing current with
  | zero => rfl
  | succ remaining ih =>
      rw [show remaining + 1 + 1 = (remaining + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineStackOutputFamilySourceRevProgram stackCount)))^[remaining + 1]
          (some (affineStackOutputFamilySourceCfg
            (.addOffset ⟨remaining, by omega⟩) buffer₁ buffer₂ test
            input output work₁ work₂ (() :: current) saved)) = _
      simpa only [List.replicate_succ, stackOutput_replicate_append_cons,
        List.cons_append, Nat.add_assoc] using
        ih (by omega) (() :: current)

private def affineStackOutput_loadBase
    (stackCount base : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg .loadBase buffer₁ buffer₂ test
        (encodeUnaryFrameBlock base ++ tail) output work₁ work₂
        current saved)
      (some (affineStackOutputFamilySourceCfg
        (.addOffset ⟨stackCount - 1, by omega⟩)
        (some .separator) buffer₂ test tail output work₁ work₂
        (List.replicate base () ++ current) saved))
      (2 * base + 1) := by
  induction base generalizing buffer₁ current with
  | zero => exact ⟨⟨1, rfl⟩, le_rfl⟩
  | succ base ih =>
      let rest := encodeUnaryFrameBlock base ++ tail
      let nextCurrent := () :: current
      have hone : EvalsToInTime
          (step (affineStackOutputFamilySourceRevProgram stackCount))
          (affineStackOutputFamilySourceCfg .loadBase buffer₁ buffer₂ test
            (.tick :: rest) output work₁ work₂ current saved)
          (some (affineStackOutputFamilySourceCfg .loadBase
            (some .tick) buffer₂ test rest output work₁ work₂
            nextCurrent saved)) 2 := by
        exact ⟨⟨2, rfl⟩, le_rfl⟩
      have hrest := ih (some .tick) nextCurrent
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        2 (2 * base + 1) _
        (affineStackOutputFamilySourceCfg .loadBase
          (some .tick) buffer₂ test rest output work₁ work₂
          nextCurrent saved) _ hone hrest
      convert full using 1
      · simp [encodeUnaryFrameBlock, rest, List.replicate_succ]
      · simp only [List.replicate_succ, nextCurrent,
          stackOutput_replicate_append_cons, List.cons_append]
      · omega

private theorem affineStackOutput_emitCurrent_eval
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym)
    (saved : List Unit) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[3 * value + 1]
      (some (affineStackOutputFamilySourceCfg
        (.emitCurrent remainingStacks) buffer₁ buffer₂ test
        input output work₁ work₂ (List.replicate value ()) saved)) =
      some (affineStackOutputFamilySourceCfg
        (.pushCurrentSeparator remainingStacks) buffer₁ buffer₂ false
        input (List.replicate value .tick ++ output) work₁ work₂ []
        (List.replicate value () ++ saved)) := by
  induction value generalizing test output saved with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 1 = (3 * value + 1) + 1 + 1 + 1 by
          omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineStackOutputFamilySourceRevProgram stackCount)))^[3 * value + 1]
          (some (affineStackOutputFamilySourceCfg
            (.emitCurrent remainingStacks) buffer₁ buffer₂ true input
            (.tick :: output) work₁ work₂ (List.replicate value ())
            (() :: saved))) = _
      simpa only [List.replicate_succ, stackOutput_replicate_append_cons,
        List.cons_append] using ih true (.tick :: output) (() :: saved)

private theorem affineStackOutput_restoreCurrent_eval
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym)
    (current : List Unit) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[2 * value + 1]
      (some (affineStackOutputFamilySourceCfg
        (.restoreCurrent remainingStacks) buffer₁ buffer₂ test
        input output work₁ work₂ current (List.replicate value ()))) =
      some (affineStackOutputFamilySourceCfg
        (.decCurrent remainingStacks affineStackOutputSix)
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate value () ++ current) []) := by
  induction value generalizing test current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineStackOutputFamilySourceRevProgram stackCount)))^[2 * value + 1]
          (some (affineStackOutputFamilySourceCfg
            (.restoreCurrent remainingStacks) buffer₁ buffer₂ true input
            output work₁ work₂ (() :: current) (List.replicate value ()))) = _
      simpa only [List.replicate_succ, stackOutput_replicate_append_cons,
        List.cons_append] using ih true (() :: current)

private theorem affineStackOutput_restoreCurrentClean_eval
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[2 * value + 1]
      (some (affineStackOutputFamilySourceCfg
        (.restoreCurrent remainingStacks) buffer₁ buffer₂ test
        input output work₁ work₂ [] (List.replicate value ()))) =
      some (affineStackOutputFamilySourceCfg
        (.decCurrent remainingStacks affineStackOutputSix)
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate value ()) []) := by
  simpa only [List.append_nil] using
    affineStackOutput_restoreCurrent_eval remainingStacks value
      buffer₁ buffer₂ test input output work₁ work₂ []

private theorem affineStackOutput_decCurrentFrom_eval
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (remaining : Nat) (hremaining : remaining < 7)
    (current : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[remaining + 1]
      (some (affineStackOutputFamilySourceCfg
        (.decCurrent remainingStacks ⟨remaining, hremaining⟩)
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate current ()) [])) =
      some (affineStackOutputFamilySourceCfg
        (.cells remainingStacks) buffer₁ buffer₂ false
        input output work₁ work₂
        (List.replicate (current - remaining) ()) []) := by
  induction remaining generalizing current test with
  | zero => rfl
  | succ remaining ih =>
      rw [show remaining + 1 + 1 = (remaining + 1) + 1 by omega,
        Function.iterate_succ_apply]
      cases current with
      | zero =>
          change
            (flip Option.bind
              (step (affineStackOutputFamilySourceRevProgram stackCount)))^[remaining + 1]
              (some (affineStackOutputFamilySourceCfg
                (.decCurrent remainingStacks ⟨remaining, by omega⟩)
                buffer₁ buffer₂ false input output work₁ work₂ [] [])) = _
          simpa using ih (by omega) 0 false
      | succ current =>
          change
            (flip Option.bind
              (step (affineStackOutputFamilySourceRevProgram stackCount)))^[remaining + 1]
              (some (affineStackOutputFamilySourceCfg
                (.decCurrent remainingStacks ⟨remaining, by omega⟩)
                buffer₁ buffer₂ true input output work₁ work₂
                (List.replicate current ()) [])) = _
          simpa [List.replicate_succ] using ih (by omega) current true

private theorem affineStackOutput_decCurrentSix_eval
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (current : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[7]
      (some (affineStackOutputFamilySourceCfg
        (.decCurrent remainingStacks affineStackOutputSix)
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate current ()) [])) =
      some (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate (current - 6) ()) []) := by
  simpa [affineStackOutputSix] using
    affineStackOutput_decCurrentFrom_eval remainingStacks 6 (by omega)
      current buffer₁ buffer₂ test input output work₁ work₂

private def affineStackOutput_restoreCurrentClean_run
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg
        (.restoreCurrent remainingStacks) buffer₁ buffer₂ test
        input output work₁ work₂ [] (List.replicate value ()))
      (some (affineStackOutputFamilySourceCfg
        (.decCurrent remainingStacks affineStackOutputSix)
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate value ()) []))
      (2 * value + 1) :=
  ⟨⟨2 * value + 1,
    affineStackOutput_restoreCurrentClean_eval remainingStacks value
      buffer₁ buffer₂ test input output work₁ work₂⟩, le_rfl⟩

private def affineStackOutput_decCurrentSix_run
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (current : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg
        (.decCurrent remainingStacks affineStackOutputSix)
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate current ()) [])
      (some (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ false input output work₁ work₂
        (List.replicate (current - 6) ()) [])) 7 :=
  ⟨⟨7, affineStackOutput_decCurrentSix_eval remainingStacks current
    buffer₁ buffer₂ test input output work₁ work₂⟩, le_rfl⟩

/-- Exact productive cost from a nonempty cell loop to the next loop test. -/
def affineStackOutputFamilySourceCellSteps (current : Nat) : Nat :=
  5 * current + 11

private theorem affineStackOutputFamilySource_op_cells
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0) :
    (affineStackOutputFamilySourceRevProgram stackCount).op
        (.cells remainingStacks) =
      .moveWork₁Work₂ (.afterCells remainingStacks) (fun
        | .tick => .emitCurrent remainingStacks
        | _ => .invalid) := by
  simp [affineStackOutputFamilySourceRevProgram, hpositive]

private theorem affineStackOutputFamilySource_cells_tick_step
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output restWork₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    step (affineStackOutputFamilySourceRevProgram stackCount)
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ test input output (.tick :: restWork₁) work₂
        current saved) =
      some (affineStackOutputFamilySourceCfg (.emitCurrent remainingStacks)
        (some .tick) buffer₂ test input output restWork₁ (.tick :: work₂)
        current saved) := by
  unfold step
  change some (stepOp
    ((affineStackOutputFamilySourceRevProgram stackCount).op
      (.cells remainingStacks))
    (affineStackOutputFamilySourceCfg (.cells remainingStacks)
      buffer₁ buffer₂ test input output (.tick :: restWork₁) work₂
      current saved)) = _
  rw [affineStackOutputFamilySource_op_cells remainingStacks hpositive]
  rfl

private theorem affineStackOutputFamilySource_cells_empty_step
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    step (affineStackOutputFamilySourceRevProgram stackCount)
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ test input output [] work₂ current saved) =
      some (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
        none buffer₂ test input output [] work₂ current saved) := by
  unfold step
  change some (stepOp
    ((affineStackOutputFamilySourceRevProgram stackCount).op
      (.cells remainingStacks))
    (affineStackOutputFamilySourceCfg (.cells remainingStacks)
      buffer₁ buffer₂ test input output [] work₂ current saved)) = _
  rw [affineStackOutputFamilySource_op_cells remainingStacks hpositive]
  rfl

private def affineStackOutputFamilySource_runCell
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0)
    (current : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output restWork₁ work₂ : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ test input output (.tick :: restWork₁) work₂
        (List.replicate current ()) [])
      (some (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        (some .tick) buffer₂ false input
        ((encodeUnaryFrameBlock current).reverse ++ output)
        restWork₁ (.tick :: work₂)
        (List.replicate (current - 6) ()) []))
      (affineStackOutputFamilySourceCellSteps current) := by
  let afterMove := affineStackOutputFamilySourceCfg
    (stackCount := stackCount) (.emitCurrent remainingStacks)
    (some .tick) buffer₂ test input output restWork₁ (.tick :: work₂)
    (List.replicate current ()) []
  let afterEmit := affineStackOutputFamilySourceCfg
    (stackCount := stackCount) (.pushCurrentSeparator remainingStacks)
    (some .tick) buffer₂ false input
    (List.replicate current .tick ++ output) restWork₁ (.tick :: work₂)
    [] (List.replicate current ())
  have hmove : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ test input output (.tick :: restWork₁) work₂
        (List.replicate current ()) [])
      (some afterMove) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step (affineStackOutputFamilySourceRevProgram stackCount)
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ test input output (.tick :: restWork₁) work₂
        (List.replicate current ()) []) = some afterMove
    simpa only [afterMove] using
      affineStackOutputFamilySource_cells_tick_step remainingStacks
        hpositive buffer₁ buffer₂ test input output restWork₁ work₂
        (List.replicate current ()) []
  have hemit : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      afterMove (some afterEmit) (3 * current + 1) := by
    exact ⟨⟨3 * current + 1, by
      simpa [afterMove, afterEmit] using
        affineStackOutput_emitCurrent_eval remainingStacks current
          (some .tick) buffer₂ test input output restWork₁
          (.tick :: work₂) []⟩, le_rfl⟩
  have hseparator : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      afterEmit
      (some (affineStackOutputFamilySourceCfg
        (.restoreCurrent remainingStacks) (some .tick) buffer₂ false input
        (.separator :: (List.replicate current .tick ++ output))
        restWork₁ (.tick :: work₂) [] (List.replicate current ()))) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore := affineStackOutput_restoreCurrentClean_run
    remainingStacks current (some .tick) buffer₂ false input
    (.separator :: (List.replicate current .tick ++ output))
    restWork₁ (.tick :: work₂)
  have hdecrement := affineStackOutput_decCurrentSix_run
    remainingStacks current (some .tick) buffer₂ false input
    (.separator :: (List.replicate current .tick ++ output))
    restWork₁ (.tick :: work₂)
  let h₁ := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    1 (3 * current + 1) _ afterMove _ hmove hemit
  let h₂ := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    ((3 * current + 1) + 1) 1 _ afterEmit _ h₁ hseparator
  let h₃ := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    (1 + ((3 * current + 1) + 1)) (2 * current + 1)
    _ (affineStackOutputFamilySourceCfg
      (.restoreCurrent remainingStacks) (some .tick) buffer₂ false input
      (.separator :: (List.replicate current .tick ++ output))
      restWork₁ (.tick :: work₂) [] (List.replicate current ()))
    _ h₂ hrestore
  let full := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    ((2 * current + 1) + (1 + ((3 * current + 1) + 1))) 7
    _ (affineStackOutputFamilySourceCfg
      (.decCurrent remainingStacks affineStackOutputSix)
      (some .tick) buffer₂ false input
      (.separator :: (List.replicate current .tick ++ output))
      restWork₁ (.tick :: work₂) (List.replicate current ()) [])
    _ h₃ hdecrement
  convert full using 1
  · simp [encodeUnaryFrameBlock]
  · simp [affineStackOutputFamilySourceCellSteps]
    omega

private def affineStackOutputFamilySourceCellFamilySteps :
    Nat → Nat → Nat
  | _, 0 => 1
  | current, height + 1 =>
      affineStackOutputFamilySourceCellSteps current +
        affineStackOutputFamilySourceCellFamilySteps (current - 6) height

private def affineStackOutputFamilySource_runCells
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0)
    (height current : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym)
    (input output work₂ : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ false input output
        (List.replicate height .tick) work₂
        (List.replicate current ()) [])
      (some (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
        none buffer₂ false input
        ((encodeAffineConjunctionSources
          (affineStackOutputDescendingCells current height)).reverse ++ output)
        [] (List.replicate height .tick ++ work₂)
        (List.replicate (current - 6 * height) ()) []))
      (affineStackOutputFamilySourceCellFamilySteps current height) := by
  induction height generalizing current buffer₁ output work₂ with
  | zero =>
      simp only [affineStackOutputFamilySourceCellFamilySteps,
        affineStackOutputDescendingCells,
        encodeAffineConjunctionSources, List.reverse_nil, List.nil_append,
        Nat.mul_zero, Nat.sub_zero, List.replicate_zero]
      refine ⟨⟨1, ?_⟩, le_rfl⟩
      change step (affineStackOutputFamilySourceRevProgram stackCount)
        (affineStackOutputFamilySourceCfg (.cells remainingStacks)
          buffer₁ buffer₂ false input output [] work₂
          (List.replicate current ()) []) = _
      simpa using
        affineStackOutputFamilySource_cells_empty_step remainingStacks
          hpositive buffer₁ buffer₂ false input output work₂
          (List.replicate current ()) []
  | succ height ih =>
      let nextOutput := (encodeUnaryFrameBlock current).reverse ++ output
      let nextWork₂ := .tick :: work₂
      have hcell := affineStackOutputFamilySource_runCell remainingStacks
        hpositive current buffer₁ buffer₂ false input output
        (List.replicate height .tick) work₂
      have hrest := ih (current - 6) (some .tick)
        nextOutput nextWork₂
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        (affineStackOutputFamilySourceCellSteps current)
        (affineStackOutputFamilySourceCellFamilySteps (current - 6) height)
        _
        (affineStackOutputFamilySourceCfg (.cells remainingStacks)
          (some .tick) buffer₂ false input nextOutput
          (List.replicate height .tick) nextWork₂
          (List.replicate (current - 6) ()) [])
        _ hcell hrest
      convert full using 1
      · simp [List.replicate_succ]
      · simp only [affineStackOutputDescendingCells,
          encodeAffineConjunctionSources, List.flatMap_cons,
          List.reverse_append, nextOutput, nextWork₂, List.append_assoc,
          List.replicate_succ, stackOutput_replicate_append_cons,
          List.cons_append]
        congr 3
        omega
      · simp [affineStackOutputFamilySourceCellFamilySteps, Nat.add_comm]

private theorem affineStackOutputFamilySource_op_resetGap
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0) :
    (affineStackOutputFamilySourceRevProgram stackCount).op
        (.resetGap remainingStacks) =
      .dec₂
        (.cells (affineStackOutputPred remainingStacks hpositive))
        (.cells (affineStackOutputPred remainingStacks hpositive)) := by
  simp [affineStackOutputFamilySourceRevProgram, hpositive]

private theorem affineStackOutputFamilySource_resetGap_step
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    step (affineStackOutputFamilySourceRevProgram stackCount)
      (affineStackOutputFamilySourceCfg (.resetGap remainingStacks)
        buffer₁ buffer₂ test input output work₁ work₂ current saved) =
      some (affineStackOutputFamilySourceCfg
        (.cells (affineStackOutputPred remainingStacks hpositive))
        buffer₁ buffer₂ false input output work₁ work₂ current saved) := by
  unfold step
  change some (stepOp
    ((affineStackOutputFamilySourceRevProgram stackCount).op
      (.resetGap remainingStacks))
    (affineStackOutputFamilySourceCfg (.resetGap remainingStacks)
      buffer₁ buffer₂ test input output work₁ work₂ current saved)) = _
  rw [affineStackOutputFamilySource_op_resetGap remainingStacks hpositive]
  rfl

/-- Exact cost of restoring the runtime height and crossing one stack gap. -/
def affineStackOutputFamilySourceRestoreHeightSteps (height : Nat) : Nat :=
  2 * height + 3

private def affineStackOutputDecTest : Nat → Bool
  | 0 => false
  | _ + 1 => true

private def affineStackOutputFamilySource_restoreHeight_run
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0)
    (height current : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg (.restoreHeight remainingStacks)
        buffer₁ buffer₂ test input output work₁
        (List.replicate height .tick) (List.replicate current ()) [])
      (some (affineStackOutputFamilySourceCfg
        (.cells (affineStackOutputPred remainingStacks hpositive))
        buffer₁ none false input output
        (List.replicate height .tick ++ work₁) []
        (List.replicate (current - height - 1) ()) []))
      (affineStackOutputFamilySourceRestoreHeightSteps height) := by
  induction height generalizing current buffer₂ test work₁ with
  | zero =>
      have hprefix : EvalsToInTime
          (step (affineStackOutputFamilySourceRevProgram stackCount))
          (affineStackOutputFamilySourceCfg (.restoreHeight remainingStacks)
            buffer₁ buffer₂ test input output work₁ []
            (List.replicate current ()) [])
          (some (affineStackOutputFamilySourceCfg (.resetGap remainingStacks)
            buffer₁ none (affineStackOutputDecTest current)
            input output work₁ []
            (List.replicate (current - 1) ()) [])) 2 := by
        cases current with
        | zero => exact ⟨⟨2, rfl⟩, le_rfl⟩
        | succ current =>
            change EvalsToInTime _ _
              (some (affineStackOutputFamilySourceCfg
                (.resetGap remainingStacks) buffer₁ none true
                input output work₁ [] (List.replicate current ()) [])) 2
            refine ⟨⟨2, ?_⟩, le_rfl⟩
            simp only [List.replicate_succ]
            rfl
      have hreset : EvalsToInTime
          (step (affineStackOutputFamilySourceRevProgram stackCount))
          (affineStackOutputFamilySourceCfg (.resetGap remainingStacks)
            buffer₁ none (affineStackOutputDecTest current)
            input output work₁ []
            (List.replicate (current - 1) ()) [])
          (some (affineStackOutputFamilySourceCfg
            (.cells (affineStackOutputPred remainingStacks hpositive))
            buffer₁ none false input output work₁ []
            (List.replicate (current - 1) ()) [])) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step (affineStackOutputFamilySourceRevProgram stackCount)
          (affineStackOutputFamilySourceCfg (.resetGap remainingStacks)
            buffer₁ none (affineStackOutputDecTest current)
            input output work₁ []
            (List.replicate (current - 1) ()) []) = _
        exact affineStackOutputFamilySource_resetGap_step remainingStacks
          hpositive buffer₁ none (affineStackOutputDecTest current)
          input output work₁ []
          (List.replicate (current - 1) ()) []
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        2 1 _
        (affineStackOutputFamilySourceCfg (.resetGap remainingStacks)
          buffer₁ none (affineStackOutputDecTest current)
          input output work₁ []
          (List.replicate (current - 1) ()) []) _ hprefix hreset
      simpa [affineStackOutputFamilySourceRestoreHeightSteps] using full
  | succ height ih =>
      let nextWork₁ := .tick :: work₁
      have hprefix : EvalsToInTime
          (step (affineStackOutputFamilySourceRevProgram stackCount))
          (affineStackOutputFamilySourceCfg (.restoreHeight remainingStacks)
            buffer₁ buffer₂ test input output work₁
            (.tick :: List.replicate height .tick)
            (List.replicate current ()) [])
          (some (affineStackOutputFamilySourceCfg
            (.restoreHeight remainingStacks) buffer₁ (some .tick)
            (affineStackOutputDecTest current)
            input output nextWork₁ (List.replicate height .tick)
            (List.replicate (current - 1) ()) [])) 2 := by
        cases current with
        | zero => exact ⟨⟨2, rfl⟩, le_rfl⟩
        | succ current =>
            change EvalsToInTime _ _
              (some (affineStackOutputFamilySourceCfg
                (.restoreHeight remainingStacks) buffer₁ (some .tick) true
                input output nextWork₁ (List.replicate height .tick)
                (List.replicate current ()) [])) 2
            refine ⟨⟨2, ?_⟩, le_rfl⟩
            simp only [List.replicate_succ]
            rfl
      have hrest := ih (current - 1) (some .tick)
        (affineStackOutputDecTest current) nextWork₁
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        2 (affineStackOutputFamilySourceRestoreHeightSteps height)
        _
        (affineStackOutputFamilySourceCfg (.restoreHeight remainingStacks)
          buffer₁ (some .tick) (affineStackOutputDecTest current)
          input output nextWork₁
          (List.replicate height .tick)
          (List.replicate (current - 1) ()) []) _ hprefix hrest
      convert full using 1
      · simp [List.replicate_succ]
      · simp only [List.replicate_succ, nextWork₁,
          stackOutput_replicate_append_cons, List.cons_append]
        congr 3
        omega
      · simp [affineStackOutputFamilySourceRestoreHeightSteps]
        omega

private theorem affineStackOutput_clearWork₂_eval
    {stackCount : Nat} (count : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ : List UnaryFrameSym) (current saved : List Unit) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[count + 1]
      (some (affineStackOutputFamilySourceCfg .clearWork₂
        buffer₁ buffer₂ test input output work₁
        (List.replicate count .tick) current saved)) =
      some (affineStackOutputFamilySourceCfg .clearWork₁
        buffer₁ none test input output work₁ [] current saved) := by
  induction count generalizing buffer₂ with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineStackOutputFamilySourceRevProgram stackCount)))^[count + 1]
          (some (affineStackOutputFamilySourceCfg .clearWork₂
            buffer₁ (some .tick) test input output work₁
            (List.replicate count .tick) current saved)) = _
      simpa using ih (some .tick)

private theorem affineStackOutput_clearWork₁_eval
    {stackCount : Nat} (count : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) (current saved : List Unit) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[count + 1]
      (some (affineStackOutputFamilySourceCfg .clearWork₁
        buffer₁ buffer₂ test input output
        (List.replicate count .tick) [] current saved)) =
      some (affineStackOutputFamilySourceCfg .clearCurrent
        none buffer₂ test input output [] [] current saved) := by
  induction count generalizing buffer₁ with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineStackOutputFamilySourceRevProgram stackCount)))^[count + 1]
          (some (affineStackOutputFamilySourceCfg .clearWork₁
            (some .tick) buffer₂ test input output
            (List.replicate count .tick) [] current saved)) = _
      simpa using ih (some .tick)

private theorem affineStackOutput_clearCurrent_eval
    {stackCount : Nat} (count : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) (saved : List Unit) :
    (flip Option.bind
      (step (affineStackOutputFamilySourceRevProgram stackCount)))^[count + 1]
      (some (affineStackOutputFamilySourceCfg .clearCurrent
        buffer₁ buffer₂ test input output [] []
        (List.replicate count ()) saved)) =
      some (affineStackOutputFamilySourceCfg .clearSaved
        buffer₁ buffer₂ false input output [] [] [] saved) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step (affineStackOutputFamilySourceRevProgram stackCount)))^[count + 1]
          (some (affineStackOutputFamilySourceCfg .clearCurrent
            buffer₁ buffer₂ true input output [] []
            (List.replicate count ()) saved)) = _
      simpa using ih true

private def affineStackOutputFamilySource_cleanup_run
    (stackCount work₁Count work₂Count current : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg .clearWork₂
        buffer₁ buffer₂ test input output
        (List.replicate work₁Count .tick)
        (List.replicate work₂Count .tick)
        (List.replicate current ()) [])
      (some (affineStackOutputFamilySourceFinishCfg stackCount input output))
      (work₁Count + work₂Count + current + 4) := by
  have hwork₂ : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount)) _
      (some (affineStackOutputFamilySourceCfg .clearWork₁
        buffer₁ none test input output
        (List.replicate work₁Count .tick) []
        (List.replicate current ()) [])) (work₂Count + 1) :=
    ⟨⟨work₂Count + 1,
      affineStackOutput_clearWork₂_eval work₂Count buffer₁ buffer₂ test
        input output (List.replicate work₁Count .tick)
        (List.replicate current ()) []⟩, le_rfl⟩
  have hwork₁ : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount)) _
      (some (affineStackOutputFamilySourceCfg .clearCurrent
        none none test input output [] [] (List.replicate current ()) []))
      (work₁Count + 1) :=
    ⟨⟨work₁Count + 1,
      affineStackOutput_clearWork₁_eval work₁Count buffer₁ none test
        input output (List.replicate current ()) []⟩, le_rfl⟩
  have hcurrent : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount)) _
      (some (affineStackOutputFamilySourceCfg .clearSaved
        none none false input output [] [] [] [])) (current + 1) :=
    ⟨⟨current + 1,
      affineStackOutput_clearCurrent_eval current none none test
        input output []⟩, le_rfl⟩
  have hsaved : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg .clearSaved
        none none false input output [] [] [] [])
      (some (affineStackOutputFamilySourceFinishCfg stackCount input output))
      1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    (work₂Count + 1) (work₁Count + 1) _ _ _ hwork₂ hwork₁
  let h₂ := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    ((work₁Count + 1) + (work₂Count + 1)) (current + 1)
    _ _ _ h₁ hcurrent
  let full := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    ((current + 1) + ((work₁Count + 1) + (work₂Count + 1))) 1
    _ _ _ h₂ hsaved
  convert full using 1
  omega

private theorem affineStackOutputFamilySource_cells_zero_step
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hzero : remainingStacks.val = 0)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    step (affineStackOutputFamilySourceRevProgram stackCount)
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ buffer₂ test input output work₁ work₂ current saved) =
      some (affineStackOutputFamilySourceCfg .clearWork₂
        buffer₁ buffer₂ test input output work₁ work₂ current saved) := by
  unfold step
  change some (stepOp
    ((affineStackOutputFamilySourceRevProgram stackCount).op
      (.cells remainingStacks))
    (affineStackOutputFamilySourceCfg (.cells remainingStacks)
      buffer₁ buffer₂ test input output work₁ work₂ current saved)) = _
  simp [affineStackOutputFamilySourceRevProgram,
    affineStackOutputFamilySourceCfg, hzero, stepOp]

private theorem affineStackOutputFamilySource_afterCells_last_step
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hlast : remainingStacks.val = 1)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    step (affineStackOutputFamilySourceRevProgram stackCount)
      (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
        buffer₁ buffer₂ test input output work₁ work₂ current saved) =
      some (affineStackOutputFamilySourceCfg .clearWork₂
        buffer₁ buffer₂ test input output work₁ work₂ current saved) := by
  unfold step
  change some (stepOp
    ((affineStackOutputFamilySourceRevProgram stackCount).op
      (.afterCells remainingStacks))
    (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
      buffer₁ buffer₂ test input output work₁ work₂ current saved)) = _
  have hpositive : remainingStacks.val ≠ 0 := by omega
  simp [affineStackOutputFamilySourceRevProgram,
    affineStackOutputFamilySourceCfg, hpositive, hlast, stepOp]

private theorem affineStackOutputFamilySource_afterCells_more_step
    {stackCount : Nat} (remainingStacks : Fin (stackCount + 1))
    (hpositive : remainingStacks.val ≠ 0)
    (hmore : remainingStacks.val ≠ 1)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (current saved : List Unit) :
    step (affineStackOutputFamilySourceRevProgram stackCount)
      (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
        buffer₁ buffer₂ test input output work₁ work₂ current saved) =
      some (affineStackOutputFamilySourceCfg (.restoreHeight remainingStacks)
        buffer₁ buffer₂ test input output work₁ work₂ current saved) := by
  unfold step
  change some (stepOp
    ((affineStackOutputFamilySourceRevProgram stackCount).op
      (.afterCells remainingStacks))
    (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
      buffer₁ buffer₂ test input output work₁ work₂ current saved)) = _
  simp [affineStackOutputFamilySourceRevProgram,
    affineStackOutputFamilySourceCfg, hpositive, hmore, stepOp]

/-- Counter value after all descending stack traversals. -/
def affineStackOutputFamilySourceFinalCurrent : Nat → Nat → Nat → Nat
  | 0, _, current => current
  | 1, height, current => current - 6 * height
  | remaining + 2, height, current =>
      affineStackOutputFamilySourceFinalCurrent (remaining + 1) height
        (current - (7 * height + 1))

/-- Exact body cost, before the final cleanup. -/
def affineStackOutputFamilySourceBodySteps : Nat → Nat → Nat → Nat
  | 0, _, _ => 1
  | 1, height, current =>
      affineStackOutputFamilySourceCellFamilySteps current height + 1
  | remaining + 2, height, current =>
      affineStackOutputFamilySourceCellFamilySteps current height + 1 +
        affineStackOutputFamilySourceRestoreHeightSteps height +
        affineStackOutputFamilySourceBodySteps (remaining + 1) height
          (current - (7 * height + 1))

private def affineStackOutputFamilySource_runPositiveBody
    {stackCount : Nat} (remaining : Nat)
    (remainingStacks : Fin (stackCount + 1))
    (hvalue : remainingStacks.val = remaining + 1)
    (height current : Nat) (buffer₁ : Option UnaryFrameSym)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg (.cells remainingStacks)
        buffer₁ none false input output
        (List.replicate height .tick) [] (List.replicate current ()) [])
      (some (affineStackOutputFamilySourceCfg .clearWork₂
        none none false input
        ((encodeAffineConjunctionSources
          (affineStackOutputDescendingWires (remaining + 1)
            height current)).reverse ++ output)
        [] (List.replicate height .tick)
        (List.replicate
          (affineStackOutputFamilySourceFinalCurrent
            (remaining + 1) height current) ()) []))
      (affineStackOutputFamilySourceBodySteps
        (remaining + 1) height current) := by
  induction remaining generalizing remainingStacks current buffer₁ output with
  | zero =>
      have hpositive : remainingStacks.val ≠ 0 := by omega
      have hcells := affineStackOutputFamilySource_runCells remainingStacks
        hpositive height current buffer₁ none input output []
      simp only [List.append_nil] at hcells
      have hlast : EvalsToInTime
          (step (affineStackOutputFamilySourceRevProgram stackCount))
          (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
            none none false input
            ((encodeAffineConjunctionSources
              (affineStackOutputDescendingCells current height)).reverse ++
                output)
            [] (List.replicate height .tick)
            (List.replicate (current - 6 * height) ()) [])
          (some (affineStackOutputFamilySourceCfg .clearWork₂
            none none false input
            ((encodeAffineConjunctionSources
              (affineStackOutputDescendingCells current height)).reverse ++
                output)
            [] (List.replicate height .tick)
            (List.replicate (current - 6 * height) ()) [])) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        rw [Function.iterate_one]
        rw [stackOutput_flip_bind_some]
        change step (affineStackOutputFamilySourceRevProgram stackCount) _ = _
        exact affineStackOutputFamilySource_afterCells_last_step
          remainingStacks hvalue none none false input
          ((encodeAffineConjunctionSources
            (affineStackOutputDescendingCells current height)).reverse ++
              output)
          [] (List.replicate height .tick)
          (List.replicate (current - 6 * height) ()) []
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        (affineStackOutputFamilySourceCellFamilySteps current height) 1 _ _ _
        hcells hlast
      simpa [affineStackOutputDescendingWires,
        affineStackOutputFamilySourceFinalCurrent,
        affineStackOutputFamilySourceBodySteps, Nat.add_comm] using full
  | succ remaining ih =>
      have hpositive : remainingStacks.val ≠ 0 := by omega
      have hmore : remainingStacks.val ≠ 1 := by omega
      have hcells := affineStackOutputFamilySource_runCells remainingStacks
        hpositive height current buffer₁ none input output []
      simp only [List.append_nil] at hcells
      let firstOutput :=
        (encodeAffineConjunctionSources
          (affineStackOutputDescendingCells current height)).reverse ++ output
      let afterCellsCurrent := current - 6 * height
      have hbridge : EvalsToInTime
          (step (affineStackOutputFamilySourceRevProgram stackCount))
          (affineStackOutputFamilySourceCfg (.afterCells remainingStacks)
            none none false input firstOutput []
            (List.replicate height .tick)
            (List.replicate afterCellsCurrent ()) [])
          (some (affineStackOutputFamilySourceCfg
            (.restoreHeight remainingStacks) none none false input
            firstOutput [] (List.replicate height .tick)
            (List.replicate afterCellsCurrent ()) [])) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        rw [Function.iterate_one]
        rw [stackOutput_flip_bind_some]
        change step (affineStackOutputFamilySourceRevProgram stackCount) _ = _
        exact affineStackOutputFamilySource_afterCells_more_step
          remainingStacks hpositive hmore none none false input firstOutput
          [] (List.replicate height .tick)
          (List.replicate afterCellsCurrent ()) []
      have hrestore := affineStackOutputFamilySource_restoreHeight_run
        remainingStacks hpositive height afterCellsCurrent none none false
        input firstOutput []
      let nextStacks := affineStackOutputPred remainingStacks hpositive
      have hnext : nextStacks.val = remaining + 1 := by
        simp [nextStacks, affineStackOutputPred]
        omega
      have hrest := ih nextStacks hnext
        (current - (7 * height + 1)) none firstOutput
      have hcurrent : afterCellsCurrent - height - 1 =
          current - (7 * height + 1) := by
        simp [afterCellsCurrent]
        omega
      rw [hcurrent] at hrestore
      simp only [List.append_nil] at hrestore
      simp only [nextStacks, List.append_nil] at hrest
      let h₁ := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        (affineStackOutputFamilySourceCellFamilySteps current height) 1
        _ _ _ hcells hbridge
      let h₂ := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        (1 + affineStackOutputFamilySourceCellFamilySteps current height)
        (affineStackOutputFamilySourceRestoreHeightSteps height)
        _ _ _ h₁ hrestore
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram stackCount))
        (affineStackOutputFamilySourceRestoreHeightSteps height +
          (1 + affineStackOutputFamilySourceCellFamilySteps current height))
        (affineStackOutputFamilySourceBodySteps (remaining + 1) height
          (current - (7 * height + 1))) _ _ _ h₂ hrest
      convert full using 1
      · simp [affineStackOutputDescendingWires,
          encodeAffineConjunctionSources, firstOutput,
          List.reverse_append, List.append_assoc,
          affineStackOutputFamilySourceFinalCurrent]
      · simp [affineStackOutputFamilySourceBodySteps]
        omega

/-- Exact successful runtime, including loading and cleanup. -/
def affineStackOutputFamilySourceSteps
    (stackCount : Nat) (frame : AffineStackOutputSourceFrame) : Nat :=
  affineStackOutputHeightLoadSteps stackCount frame.height +
    (2 * frame.base + 1) + (stackCount - 1 + 1) +
    affineStackOutputFamilySourceBodySteps stackCount frame.height
      (affineStackOutputLastWire stackCount frame.height frame.base) +
    frame.height +
    affineStackOutputFamilySourceFinalCurrent stackCount frame.height
      (affineStackOutputLastWire stackCount frame.height frame.base) + 4

/-- The fixed source consumes exactly the two-field invocation, preserves its
tail, and prepends the reverse encoding required by a conjunction frame. -/
def affineStackOutputFamilySource_runToFinish
    (stackCount : Nat) (frame : AffineStackOutputSourceFrame)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceLoopCfg stackCount
        (encodeAffineStackOutputSourceInvocation frame ++ tail) output)
      (some (affineStackOutputFamilySourceFinishCfg stackCount tail
        ((encodeAffineConjunctionSources
          (affineStackOutputWires stackCount frame.height
            frame.base).reverse).reverse ++ output)))
      (affineStackOutputFamilySourceSteps stackCount frame) := by
  rcases frame with ⟨height, base⟩
  have hheight := affineStackOutput_loadHeight stackCount height
    none none false (encodeUnaryFrameBlock base ++ tail) output [] [] [] []
  simp only [List.append_nil] at hheight
  have hbaseRaw := affineStackOutput_loadBase stackCount base
    (some .separator) none false tail output
    (List.replicate height .tick) []
    (List.replicate (7 * stackCount * height) ()) []
  have hbase : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg .loadBase
        (some .separator) none false
        (encodeUnaryFrameBlock base ++ tail) output
        (List.replicate height .tick) []
        (List.replicate (7 * stackCount * height) ()) [])
      (some (affineStackOutputFamilySourceCfg
        (.addOffset ⟨stackCount - 1, by omega⟩)
        (some .separator) none false tail output
        (List.replicate height .tick) []
        (List.replicate (base + 7 * stackCount * height) ()) []))
      (2 * base + 1) := by
    convert hbaseRaw using 1
    simp only [← List.replicate_add]
  have hoffsetRaw := affineStackOutput_addOffsetFrom_eval
    stackCount (stackCount - 1) (by omega)
    (some .separator) none false tail output
    (List.replicate height .tick) []
    (List.replicate (base + 7 * stackCount * height) ()) []
  have hoffset : EvalsToInTime
      (step (affineStackOutputFamilySourceRevProgram stackCount))
      (affineStackOutputFamilySourceCfg
        (.addOffset ⟨stackCount - 1, by omega⟩)
        (some .separator) none false tail output
        (List.replicate height .tick) []
        (List.replicate (base + 7 * stackCount * height) ()) [])
      (some (affineStackOutputFamilySourceCfg
        (.cells ⟨stackCount, by omega⟩)
        (some .separator) none false tail output
        (List.replicate height .tick) []
        (List.replicate
          (affineStackOutputLastWire stackCount height base) ()) []))
      (stackCount - 1 + 1) := by
    have hcurrent :
        List.replicate (stackCount - 1) () ++
            List.replicate (base + 7 * stackCount * height) () =
          List.replicate
            (affineStackOutputLastWire stackCount height base) () := by
      rw [← List.replicate_add]
      congr 1
      simp [affineStackOutputLastWire]
      omega
    refine ⟨⟨stackCount - 1 + 1, ?_⟩, le_rfl⟩
    rw [stackOutput_iterate_bind_eq]
    simpa only [hcurrent] using hoffsetRaw
  let h₁ := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    (affineStackOutputHeightLoadSteps stackCount height)
    (2 * base + 1) _ _ _ hheight hbase
  let hprefix := EvalsToInTime.trans
    (step (affineStackOutputFamilySourceRevProgram stackCount))
    ((2 * base + 1) + affineStackOutputHeightLoadSteps stackCount height)
    (stackCount - 1 + 1) _ _ _ h₁ hoffset
  cases stackCount with
  | zero =>
      simp [affineStackOutputLastWire] at hprefix
      let zeroStacks : Fin (0 + 1) := ⟨0, by omega⟩
      have hbody : EvalsToInTime
          (step (affineStackOutputFamilySourceRevProgram 0))
          (affineStackOutputFamilySourceCfg (.cells zeroStacks)
            (some .separator) none false tail output
            (List.replicate height .tick) []
            (List.replicate base ()) [])
          (some (affineStackOutputFamilySourceCfg .clearWork₂
            (some .separator) none false tail output
            (List.replicate height .tick) []
            (List.replicate base ()) [])) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        rw [Function.iterate_one, stackOutput_flip_bind_some]
        exact affineStackOutputFamilySource_cells_zero_step zeroStacks rfl
          (some .separator) none false tail output
          (List.replicate height .tick) [] (List.replicate base ()) []
      have hcleanup := affineStackOutputFamilySource_cleanup_run
        0 height 0 base (some .separator) none false tail output
      let h₂ := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram 0))
        ((0 - 1 + 1) +
          ((2 * base + 1) +
            affineStackOutputHeightLoadSteps 0 height))
        1 _ _ _ hprefix hbody
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram 0))
        (1 + ((0 - 1 + 1) +
          ((2 * base + 1) +
            affineStackOutputHeightLoadSteps 0 height)))
        (height + 0 + base + 4) _ _ _ h₂ hcleanup
      convert full using 1
      · simp [encodeAffineStackOutputSourceInvocation, encodeUnaryFrame,
          affineStackOutputFamilySourceLoopCfg]
      · simp [affineStackOutputWires, affineStackOutputDescendingWires,
          affineStackOutputLastWire, encodeAffineConjunctionSources]
      · simp [affineStackOutputFamilySourceSteps,
          affineStackOutputFamilySourceBodySteps,
          affineStackOutputFamilySourceFinalCurrent,
          affineStackOutputLastWire]
        omega
  | succ remaining =>
      let allStacks : Fin (remaining + 1 + 1) :=
        ⟨remaining + 1, by omega⟩
      let lastWire := affineStackOutputLastWire
        (remaining + 1) height base
      have hbody := affineStackOutputFamilySource_runPositiveBody remaining
        allStacks rfl height lastWire (some .separator) tail output
      let finalCurrent := affineStackOutputFamilySourceFinalCurrent
        (remaining + 1) height lastWire
      have hcleanup := affineStackOutputFamilySource_cleanup_run
        (remaining + 1) 0 height finalCurrent none none false tail
        ((encodeAffineConjunctionSources
          (affineStackOutputDescendingWires (remaining + 1)
            height lastWire)).reverse ++ output)
      let h₂ := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram (remaining + 1)))
        ((remaining + 1 - 1 + 1) +
          ((2 * base + 1) +
            affineStackOutputHeightLoadSteps (remaining + 1) height))
        (affineStackOutputFamilySourceBodySteps (remaining + 1)
          height lastWire) _ _ _ hprefix hbody
      let full := EvalsToInTime.trans
        (step (affineStackOutputFamilySourceRevProgram (remaining + 1)))
        (affineStackOutputFamilySourceBodySteps (remaining + 1)
          height lastWire +
          ((remaining + 1 - 1 + 1) +
            ((2 * base + 1) +
              affineStackOutputHeightLoadSteps (remaining + 1) height)))
        (0 + height + finalCurrent + 4) _ _ _ h₂ hcleanup
      convert full using 1
      · simp [encodeAffineStackOutputSourceInvocation, encodeUnaryFrame,
          affineStackOutputFamilySourceLoopCfg]
      · simp [affineStackOutputWires, lastWire,
          encodeAffineConjunctionSources]
      · simp [affineStackOutputFamilySourceSteps, lastWire, finalCurrent]
        omega

private theorem affineStackOutputFamilySourceCellFamilySteps_le
    (current height : Nat) :
    affineStackOutputFamilySourceCellFamilySteps current height ≤
      height * (5 * current + 11) + 1 := by
  induction height generalizing current with
  | zero => simp [affineStackOutputFamilySourceCellFamilySteps]
  | succ height ih =>
      simp only [affineStackOutputFamilySourceCellFamilySteps]
      have hrest := ih (current - 6)
      have hsub : 5 * (current - 6) + 11 ≤ 5 * current + 11 := by
        omega
      have hmul := Nat.mul_le_mul_left height hsub
      simp [affineStackOutputFamilySourceCellSteps]
      nlinarith

private theorem affineStackOutputFamilySourceFinalCurrent_le
    (stackCount height current : Nat) :
    affineStackOutputFamilySourceFinalCurrent stackCount height current ≤
      current := by
  induction stackCount generalizing current with
  | zero => simp [affineStackOutputFamilySourceFinalCurrent]
  | succ stackCount ih =>
      cases stackCount with
      | zero =>
          simp [affineStackOutputFamilySourceFinalCurrent]
      | succ stackCount =>
          simp only [affineStackOutputFamilySourceFinalCurrent]
          exact (ih (current - (7 * height + 1))).trans
            (Nat.sub_le current (7 * height + 1))

private theorem affineStackOutputFamilySourceBodySteps_le
    (stackCount height current : Nat) :
    affineStackOutputFamilySourceBodySteps stackCount height current ≤
      stackCount *
        (height * (5 * current + 11) + 2 * height + 5) + 1 := by
  induction stackCount generalizing current with
  | zero => simp [affineStackOutputFamilySourceBodySteps]
  | succ stackCount ih =>
      cases stackCount with
      | zero =>
          simp only [affineStackOutputFamilySourceBodySteps, Nat.one_mul]
          have hcells :=
            affineStackOutputFamilySourceCellFamilySteps_le current height
          omega
      | succ stackCount =>
          simp only [affineStackOutputFamilySourceBodySteps]
          have hcells :=
            affineStackOutputFamilySourceCellFamilySteps_le current height
          have hrest := ih (current - (7 * height + 1))
          have hsub :
              height * (5 * (current - (7 * height + 1)) + 11) +
                  2 * height + 5 ≤
                height * (5 * current + 11) + 2 * height + 5 := by
            have : 5 * (current - (7 * height + 1)) + 11 ≤
                5 * current + 11 := by omega
            exact Nat.add_le_add_right
              (Nat.add_le_add_right (Nat.mul_le_mul_left height this)
                (2 * height)) 5
          have hmul := Nat.mul_le_mul_left (stackCount + 1) hsub
          simp [affineStackOutputFamilySourceRestoreHeightSteps] at hrest ⊢
          nlinarith

private theorem encodeAffineStackOutputSourceInvocation_length
    (frame : AffineStackOutputSourceFrame) :
    (encodeAffineStackOutputSourceInvocation frame).length =
      frame.height + frame.base + 2 := by
  simp [encodeAffineStackOutputSourceInvocation]
  omega

/-- Uniform quadratic bound.  The coefficient is quadratic in the fixed
stack count, matching the unary size of the emitted wire family. -/
theorem affineStackOutputFamilySource_steps_le
    (stackCount : Nat) (frame : AffineStackOutputSourceFrame) :
    affineStackOutputFamilySourceSteps stackCount frame ≤
      (400 * (stackCount + 1) ^ 2) *
        (encodeAffineStackOutputSourceInvocation frame).length ^ 2 + 100 := by
  rcases frame with ⟨height, base⟩
  let n := height + base + 2
  let q := stackCount + 1
  let lastWire := affineStackOutputLastWire stackCount height base
  have hn : 2 ≤ n := by simp [n]
  have hq : 1 ≤ q := by simp [q]
  have hheight : height ≤ n := by
    dsimp [n]
    omega
  have hbase : base ≤ n := by
    dsimp [n]
    omega
  have hstack : stackCount ≤ q := by simp [q]
  have hstackHeight : stackCount * height ≤ q * n :=
    Nat.mul_le_mul hstack hheight
  have hqn : q ≤ q * n := by nlinarith
  have hnqn : n ≤ q * n := by nlinarith
  have hbaseQ : base ≤ q * n := hbase.trans hnqn
  have hoffsetQ : stackCount - 1 ≤ q * n :=
    (Nat.sub_le stackCount 1).trans (hstack.trans hqn)
  have hseven : 7 * stackCount * height ≤ 7 * (q * n) := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 7 hstackHeight
  have hlast' : lastWire ≤ 9 * (q * n) := by
    simp [lastWire, affineStackOutputLastWire]
    omega
  have hlast : lastWire ≤ 10 * q * n := by
    calc
      _ ≤ 9 * (q * n) := hlast'
      _ ≤ 10 * q * n := by nlinarith
  have hfactor :
      height * (5 * lastWire + 11) + 2 * height + 5 ≤
        70 * q * n ^ 2 := by
    have hfive : 5 * lastWire + 11 ≤ 50 * q * n + 11 := by
      nlinarith
    have hmul := Nat.mul_le_mul hheight hfive
    have hnSq : n ≤ n ^ 2 := by nlinarith
    have hqnSq : q * n ≤ q * n ^ 2 :=
      Nat.mul_le_mul_left q hnSq
    nlinarith
  have hbodyRaw := affineStackOutputFamilySourceBodySteps_le
    stackCount height lastWire
  have hbody :
      affineStackOutputFamilySourceBodySteps stackCount height lastWire ≤
        70 * q ^ 2 * n ^ 2 + 1 := by
    calc
      _ ≤ stackCount *
          (height * (5 * lastWire + 11) + 2 * height + 5) + 1 :=
        hbodyRaw
      _ ≤ q * (70 * q * n ^ 2) + 1 := by
        exact Nat.add_le_add_right (Nat.mul_le_mul hstack hfactor) 1
      _ = 70 * q ^ 2 * n ^ 2 + 1 := by ring
  have hfinal := affineStackOutputFamilySourceFinalCurrent_le
    stackCount height lastWire
  rw [encodeAffineStackOutputSourceInvocation_length]
  change affineStackOutputFamilySourceSteps stackCount
      { height := height, base := base } ≤
    400 * q ^ 2 * n ^ 2 + 100
  simp only [affineStackOutputFamilySourceSteps]
  have hloader :
      affineStackOutputHeightLoadSteps stackCount height ≤ 10 * q * n := by
    simp [affineStackOutputHeightLoadSteps, q]
    nlinarith
  have hbaseLoad : 2 * base + 1 ≤ 3 * q * n := by nlinarith
  have hoffset : stackCount - 1 + 1 ≤ q * n := by omega
  have hheight' : height ≤ q * n := hheight.trans hnqn
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
