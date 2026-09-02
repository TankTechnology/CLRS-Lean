import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationLabelPacketPrepare
import Mathlib.Tactic

/-!
# Loading stack-ready dispatch-mux label packets

This is the first execution layer of the final dispatch-mux source assembler.
One fixed controller retains the selector in a unary counter, restores the
prepared coordinate row on `work₁`, restores the prepared true-arm row on
`work₂`, and leaves the false-arm row at the input head.  Later small modules
prove the coordinate zipper and whole-family execution of the same program.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Finite control for the stack-ready label-packet assembler. -/
inductive TransitionDispatchMuxInvocationLabelPacketAssemblerLabel
  | loadSelector | incSelector | selectorBoundary
  | loadCoordinates | saveCoordinate (symbol : UnaryFrameSym)
  | loadTrue | saveTrue (symbol : UnaryFrameSym)
  | coordinateCheck (first : Bool)
  | loadSelectorNot (first : Bool) | incSelectorNot (first : Bool)
  | emitSelector (first : Bool) | saveSelector (first : Bool)
  | emitSelectorTick (first : Bool) | emitSelectorBoundary (first : Bool)
  | restoreSelector (first : Bool) | restoreSelectorInc (first : Bool)
  | emitSelectorNot (first : Bool) | emitSelectorNotTick (first : Bool)
  | emitSelectorNotBoundary (first : Bool)
  | emitHeaderFlag (first : Bool) | emitHeaderBoundary
  | loadTrueValue | emitTrueTick | emitTrueBoundary
  | loadFalseValue | emitFalseTick | emitFalseBoundary
  | loadTrueArm | emitTrueArmTick | emitTrueArmBoundary
  | discardFalseArm | emitSegmentBoundary
  | checkTrueEmpty (first : Bool) | checkFalseBoundary (first : Bool)
  | emitEmptySelector | emitEmptySelectorTick | emitEmptySelectorBoundary
  | emitEmptyZeroBoundary | emitEmptyFlagTick | emitEmptyFlagBoundary
  | emitEmptyFrameEnd
  | clearSelector | resetBuffer | finish | invalid
deriving DecidableEq, Fintype

/-- One fixed assembler for every verifier, input, label count, and mux width.
The output stack is prepend-only, so this program emits the reverse of the
desired source; the standard verified reverse machine will be composed later.
-/
def transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := TransitionDispatchMuxInvocationLabelPacketAssemblerLabel
  main := .loadSelector
  op
    | .loadSelector => .popInput .finish fun
        | .tick => .incSelector
        | .separator => .selectorBoundary
        | .frameEnd => .invalid
    | .incSelector => .inc₁ .loadSelector
    | .selectorBoundary => .popInput .invalid fun
        | .frameEnd => .loadCoordinates
        | _ => .invalid
    | .loadCoordinates => .popInput .invalid fun symbol =>
        if symbol = .frameEnd then .loadTrue else .saveCoordinate symbol
    | .saveCoordinate symbol => .pushWork₁ symbol .loadCoordinates
    | .loadTrue => .popInput .invalid fun symbol =>
        if symbol = .frameEnd then .coordinateCheck true
        else .saveTrue symbol
    | .saveTrue symbol => .pushWork₂ symbol .loadTrue
    | .coordinateCheck first => .jump (.loadSelectorNot first)
    | .loadSelectorNot first => .popWork₁ (.checkTrueEmpty first) fun
        | .tick => .incSelectorNot first
        | .separator => .emitSelector first
        | .frameEnd => .invalid
    | .incSelectorNot first => .inc₂ (.loadSelectorNot first)
    | .emitSelector first =>
        .dec₁ (.emitSelectorBoundary first) (.saveSelector first)
    | .saveSelector first => .inc₃ (.emitSelectorTick first)
    | .emitSelectorTick first => .pushOutput .tick (.emitSelector first)
    | .emitSelectorBoundary first =>
        .pushOutput .separator (.restoreSelector first)
    | .restoreSelector first =>
        .dec₃ (.emitSelectorNot first) (.restoreSelectorInc first)
    | .restoreSelectorInc first => .inc₁ (.restoreSelector first)
    | .emitSelectorNot first =>
        .dec₂ (.emitSelectorNotBoundary first) (.emitSelectorNotTick first)
    | .emitSelectorNotTick first =>
        .pushOutput .tick (.emitSelectorNot first)
    | .emitSelectorNotBoundary first =>
        .pushOutput .separator (.emitHeaderFlag first)
    | .emitHeaderFlag true => .pushOutput .tick .emitHeaderBoundary
    | .emitHeaderFlag false => .jump .emitHeaderBoundary
    | .emitHeaderBoundary => .pushOutput .separator .loadTrueValue
    | .loadTrueValue => .popWork₂ .invalid fun
        | .tick => .emitTrueTick
        | .separator => .emitTrueBoundary
        | .frameEnd => .invalid
    | .emitTrueTick => .pushOutput .tick .loadTrueValue
    | .emitTrueBoundary => .pushOutput .separator .loadFalseValue
    | .loadFalseValue => .popInput .invalid fun
        | .tick => .emitFalseTick
        | .separator => .emitFalseBoundary
        | .frameEnd => .invalid
    | .emitFalseTick => .pushOutput .tick .loadFalseValue
    | .emitFalseBoundary => .pushOutput .separator .loadTrueArm
    | .loadTrueArm => .popWork₁ .invalid fun
        | .tick => .emitTrueArmTick
        | .separator => .emitTrueArmBoundary
        | .frameEnd => .invalid
    | .emitTrueArmTick => .pushOutput .tick .loadTrueArm
    | .emitTrueArmBoundary => .pushOutput .separator .discardFalseArm
    | .discardFalseArm => .popWork₁ .invalid fun
        | .tick => .discardFalseArm
        | .separator => .emitSegmentBoundary
        | .frameEnd => .invalid
    | .emitSegmentBoundary =>
        .pushOutput .frameEnd (.coordinateCheck false)
    | .checkTrueEmpty first =>
        .popWork₂ (.checkFalseBoundary first) (fun _ => .invalid)
    | .checkFalseBoundary first => .popInput .invalid fun
        | .frameEnd => if first then .emitEmptySelector else .clearSelector
        | _ => .invalid
    | .emitEmptySelector =>
        .dec₁ .emitEmptySelectorBoundary .emitEmptySelectorTick
    | .emitEmptySelectorTick => .pushOutput .tick .emitEmptySelector
    | .emitEmptySelectorBoundary =>
        .pushOutput .separator .emitEmptyZeroBoundary
    | .emitEmptyZeroBoundary =>
        .pushOutput .separator .emitEmptyFlagTick
    | .emitEmptyFlagTick => .pushOutput .tick .emitEmptyFlagBoundary
    | .emitEmptyFlagBoundary =>
        .pushOutput .separator .emitEmptyFrameEnd
    | .emitEmptyFrameEnd => .pushOutput .frameEnd .resetBuffer
    | .clearSelector => .dec₁ .resetBuffer .clearSelector
    | .resetBuffer => .popWork₁ .loadSelector (fun _ => .invalid)
    | .finish => .halt
    | .invalid => .halt

/-- Fully explicit assembler configuration, kept public for the later small
execution modules. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (label : TransitionDispatchMuxInvocationLabelPacketAssemblerLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (selector selectorNot scratch : List Unit) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  { label := some label
    buffer₁ := buffer₁
    buffer₂ := buffer₂
    test := test
    input := input
    output := output
    work₁ := work₁
    work₂ := work₂
    counter₁ := selector
    counter₂ := selectorNot
    counter₃ := scratch }

/-- Clean boundary before the selector row of the next label packet. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  transitionDispatchMuxInvocationLabelPacketAssemblerCfg .loadSelector
    none none false input output [] [] [] [] []

/-- Boundary after the selector, coordinate, and true-arm rows have loaded.
The false-arm row remains forward at the input head. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
    (view : TransitionDispatchMuxInvocationView)
    (tail output : List UnaryFrameSym) :
    BuilderCfg transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram :=
  transitionDispatchMuxInvocationLabelPacketAssemblerCfg
    (.coordinateCheck true) (some .frameEnd) none false
    (encodeUnaryFrame view.whenFalse ++ .frameEnd :: tail) output
    (transitionDispatchMuxCoordinateRowFrames view.coordinates)
    (encodeUnaryFrame view.whenTrue)
    (List.replicate view.selector ()) [] []

/-- Exact transition count of the three-row loading prelude. -/
def transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps
    (view : TransitionDispatchMuxInvocationView) : Nat :=
  2 * view.selector +
    2 * (transitionDispatchMuxCoordinateRowFrames view.coordinates).length +
    2 * (encodeUnaryFrame view.whenTrue).length + 4

private def assemblerLastBuffer (initial : Option UnaryFrameSym)
    (symbols : List UnaryFrameSym) : Option UnaryFrameSym :=
  symbols.foldl (fun _ symbol => some symbol) initial

private theorem assembler_replicate_append_cons (count : Nat)
    (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ()) ih

private theorem assembler_loadSelector_eval
    (selector : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (tail output work₁ work₂ : List UnaryFrameSym)
    (currentSelector selectorNot scratch : List Unit) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * selector + 1]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadSelector buffer₁ buffer₂ test
        (encodeUnaryFrameBlock selector ++ tail) output work₁ work₂
        currentSelector selectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .selectorBoundary (some .separator) buffer₂ test tail output
        work₁ work₂ (List.replicate selector () ++ currentSelector)
        selectorNot scratch) := by
  induction selector generalizing buffer₁ currentSelector with
  | zero => rfl
  | succ selector ih =>
      rw [show 2 * (selector + 1) + 1 =
          (2 * selector + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * selector + 1]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadSelector (some .tick) buffer₂ test
            (encodeUnaryFrameBlock selector ++ tail) output work₁ work₂
            (() :: currentSelector) selectorNot scratch)) = _
      simpa only [List.replicate_succ,
        assembler_replicate_append_cons, List.cons_append] using
        ih (buffer₁ := some .tick)
          (currentSelector := () :: currentSelector)

private theorem assembler_scanCoordinates_eval
    (row tail output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (selector selectorNot scratch : List Unit)
    (hfree : UnaryFrameSym.frameEnd ∉ row) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * row.length]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadCoordinates buffer₁ buffer₂ test (row ++ tail) output
        work₁ work₂ selector selectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadCoordinates (assemblerLastBuffer buffer₁ row) buffer₂ test
        tail output (row.reverse ++ work₁) work₂ selector selectorNot
        scratch) := by
  induction row generalizing buffer₁ work₁ with
  | nil => rfl
  | cons symbol row ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd := by
        intro heq
        apply hfree
        simpa [heq]
      have htail : UnaryFrameSym.frameEnd ∉ row := by
        intro hmem
        exact hfree (by simp [hmem])
      rw [show 2 * (symbol :: row).length =
          2 * row.length + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [flip, Option.bind_some]
      rw [show step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
          (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadCoordinates buffer₁ buffer₂ test
            (symbol :: row ++ tail) output work₁ work₂ selector selectorNot
            scratch) =
          some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            (.saveCoordinate symbol) (some symbol) buffer₂ test
            (row ++ tail) output work₁ work₂ selector selectorNot scratch) by
        simp [step,
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram,
          transitionDispatchMuxInvocationLabelPacketAssemblerCfg, stepOp,
          hsymbol]]
      simp only [Option.bind_some]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * row.length]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadCoordinates (some symbol) buffer₂ test (row ++ tail)
            output (symbol :: work₁) work₂ selector selectorNot scratch)) = _
      simpa [assemblerLastBuffer, List.reverse_cons,
        List.append_assoc] using
        ih (buffer₁ := some symbol) (work₁ := symbol :: work₁) htail

private theorem assembler_scanTrue_eval
    (row tail output work₁ work₂ : List UnaryFrameSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (selector selectorNot scratch : List Unit)
    (hfree : UnaryFrameSym.frameEnd ∉ row) :
    (flip Option.bind (step
      transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
        2 * row.length]
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadTrue buffer₁ buffer₂ test (row ++ tail) output work₁ work₂
        selector selectorNot scratch)) =
      some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
        .loadTrue (assemblerLastBuffer buffer₁ row) buffer₂ test tail output
        work₁ (row.reverse ++ work₂) selector selectorNot scratch) := by
  induction row generalizing buffer₁ work₂ with
  | nil => rfl
  | cons symbol row ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd := by
        intro heq
        apply hfree
        simpa [heq]
      have htail : UnaryFrameSym.frameEnd ∉ row := by
        intro hmem
        exact hfree (by simp [hmem])
      rw [show 2 * (symbol :: row).length =
          2 * row.length + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [flip, Option.bind_some]
      rw [show step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
          (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadTrue buffer₁ buffer₂ test (symbol :: row ++ tail) output
            work₁ work₂ selector selectorNot scratch) =
          some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            (.saveTrue symbol) (some symbol) buffer₂ test (row ++ tail)
            output work₁ work₂ selector selectorNot scratch) by
        simp [step,
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram,
          transitionDispatchMuxInvocationLabelPacketAssemblerCfg, stepOp,
          hsymbol]]
      simp only [Option.bind_some]
      change
        (flip Option.bind (step
          transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram))^[
            2 * row.length]
          (some (transitionDispatchMuxInvocationLabelPacketAssemblerCfg
            .loadTrue (some symbol) buffer₂ test (row ++ tail) output work₁
            (symbol :: work₂) selector selectorNot scratch)) = _
      simpa [assemblerLastBuffer, List.reverse_cons,
        List.append_assoc] using
        ih (buffer₁ := some symbol) (work₂ := symbol :: work₂) htail

private theorem assembler_encodeUnaryFrame_frameEnd_not_mem
    (values : List Nat) : UnaryFrameSym.frameEnd ∉ encodeUnaryFrame values := by
  induction values with
  | nil => simp [encodeUnaryFrame]
  | cons value values ih =>
      change UnaryFrameSym.frameEnd ∉
        encodeUnaryFrameBlock value ++ encodeUnaryFrame values
      simp [encodeUnaryFrameBlock, ih]

private theorem assembler_coordinateFrames_frameEnd_not_mem
    (coordinates : List (Nat × Nat × Nat)) :
    UnaryFrameSym.frameEnd ∉
      transitionDispatchMuxCoordinateRowFrames coordinates := by
  induction coordinates with
  | nil => simp [transitionDispatchMuxCoordinateRowFrames]
  | cons coordinate coordinates ih =>
      change UnaryFrameSym.frameEnd ∉
        encodeUnaryFrame [coordinate.1, coordinate.2.1, coordinate.2.2] ++
          transitionDispatchMuxCoordinateRowFrames coordinates
      simp [assembler_encodeUnaryFrame_frameEnd_not_mem, ih]

private theorem assembler_frameEnd_not_mem_reverse
    (row : List UnaryFrameSym) (hfree : UnaryFrameSym.frameEnd ∉ row) :
    UnaryFrameSym.frameEnd ∉ row.reverse := by
  simpa only [List.mem_reverse] using hfree

/-- Loading one explicit stack-ready packet is an exact execution theorem of
the fixed assembler, not a semantic/native computation shortcut. -/
def transitionDispatchMuxInvocationLabelPacketAssembler_load
    (view : TransitionDispatchMuxInvocationView)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (view.preparedLabelPacketFrames ++ tail) output)
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
        view tail output))
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps view) := by
  let coordinateRow := transitionDispatchMuxCoordinateRowFrames view.coordinates
  let trueRow := encodeUnaryFrame view.whenTrue
  let falseTail := encodeUnaryFrame view.whenFalse ++ .frameEnd :: tail
  let afterSelector :=
    transitionDispatchMuxInvocationLabelPacketAssemblerCfg
      .selectorBoundary (some .separator) none false
      (.frameEnd :: coordinateRow.reverse ++ .frameEnd ::
        trueRow.reverse ++ .frameEnd :: falseTail)
      output [] [] (List.replicate view.selector ()) [] []
  let beforeCoordinates :=
    transitionDispatchMuxInvocationLabelPacketAssemblerCfg
      .loadCoordinates (some .frameEnd) none false
      (coordinateRow.reverse ++ .frameEnd :: trueRow.reverse ++
        .frameEnd :: falseTail)
      output [] [] (List.replicate view.selector ()) [] []
  let afterCoordinates :=
    transitionDispatchMuxInvocationLabelPacketAssemblerCfg
      .loadCoordinates (assemblerLastBuffer (some .frameEnd)
        coordinateRow.reverse) none false
      (.frameEnd :: trueRow.reverse ++ .frameEnd :: falseTail)
      output coordinateRow [] (List.replicate view.selector ()) [] []
  let beforeTrue :=
    transitionDispatchMuxInvocationLabelPacketAssemblerCfg
      .loadTrue (some .frameEnd) none false
      (trueRow.reverse ++ .frameEnd :: falseTail)
      output coordinateRow [] (List.replicate view.selector ()) [] []
  let afterTrue :=
    transitionDispatchMuxInvocationLabelPacketAssemblerCfg
      .loadTrue (assemblerLastBuffer (some .frameEnd) trueRow.reverse)
      none false (.frameEnd :: falseTail) output coordinateRow trueRow
      (List.replicate view.selector ()) [] []
  have hselector : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      (transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg
        (view.preparedLabelPacketFrames ++ tail) output)
      (some afterSelector) (2 * view.selector + 1) :=
    ⟨⟨2 * view.selector + 1, by
      simpa [afterSelector,
        transitionDispatchMuxInvocationLabelPacketAssemblerLoopCfg,
        TransitionDispatchMuxInvocationView.preparedLabelPacketFrames,
        coordinateRow, trueRow, falseTail, encodeUnaryFrame,
        List.append_assoc] using
        assembler_loadSelector_eval view.selector none none false
          (.frameEnd :: coordinateRow.reverse ++ .frameEnd ::
            trueRow.reverse ++ .frameEnd :: falseTail)
          output [] [] [] [] []⟩, le_rfl⟩
  have hselectorBoundary : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterSelector (some beforeCoordinates) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hcoordinateFree : UnaryFrameSym.frameEnd ∉ coordinateRow := by
    dsimp [coordinateRow]
    exact assembler_coordinateFrames_frameEnd_not_mem view.coordinates
  have hcoordinates : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeCoordinates (some afterCoordinates)
      (2 * coordinateRow.length) :=
    ⟨⟨2 * coordinateRow.length, by
      simpa [beforeCoordinates, afterCoordinates] using
        assembler_scanCoordinates_eval coordinateRow.reverse
          (.frameEnd :: trueRow.reverse ++ .frameEnd :: falseTail)
          output [] [] (some .frameEnd) none false
          (List.replicate view.selector ()) [] []
          (assembler_frameEnd_not_mem_reverse coordinateRow
            hcoordinateFree)⟩,
      le_rfl⟩
  have hcoordinateBoundary : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterCoordinates (some beforeTrue) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
      afterCoordinates = some beforeTrue
    rfl
  have htrueFree : UnaryFrameSym.frameEnd ∉ trueRow := by
    dsimp [trueRow]
    exact assembler_encodeUnaryFrame_frameEnd_not_mem view.whenTrue
  have htrue : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      beforeTrue (some afterTrue) (2 * trueRow.length) :=
    ⟨⟨2 * trueRow.length, by
      simpa [beforeTrue, afterTrue] using
        assembler_scanTrue_eval trueRow.reverse
          (.frameEnd :: falseTail) output coordinateRow []
          (some .frameEnd) none false (List.replicate view.selector ()) [] []
          (assembler_frameEnd_not_mem_reverse trueRow htrueFree)⟩,
      le_rfl⟩
  have htrueBoundary : EvalsToInTime
      (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
      afterTrue
      (some (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
        view tail output)) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram
      afterTrue =
        some (transitionDispatchMuxInvocationLabelPacketAssemblerLoadedCfg
          view tail output)
    rfl
  let h₁ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    (2 * view.selector + 1) 1 _ afterSelector _ hselector
      hselectorBoundary
  let h₂ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (2 * coordinateRow.length) _ beforeCoordinates _ h₁ hcoordinates
  let h₃ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ 1 _ afterCoordinates _ h₂ hcoordinateBoundary
  let h₄ := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ (2 * trueRow.length) _ beforeTrue _ h₃ htrue
  let full := EvalsToInTime.trans
    (step transitionDispatchMuxInvocationLabelPacketAssemblerRevProgram)
    _ 1 _ afterTrue _ h₄ htrueBoundary
  convert full using 1 <;>
    simp [transitionDispatchMuxInvocationLabelPacketAssemblerLoadSteps,
      coordinateRow, trueRow] <;> omega

end CLRS.Chapter34.Turing.CookLevin
