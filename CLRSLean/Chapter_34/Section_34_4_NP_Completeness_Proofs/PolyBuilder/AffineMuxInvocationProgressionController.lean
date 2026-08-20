import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineMuxInvocationProgressionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Streaming expansion of affine mux invocation progressions

The arithmetic source supplies one metadata triple followed by a sequence of
`(whenTrue, whenFalse, trueArm)` rows and a segment marker.  This controller
stores the shared selector and selector-negation in two unary counters, then
expands every data row to the exact three-call `AffineMuxFinPairFrame` byte
protocol.  The third value is copied once and replayed with two additional
ticks: the first reaches the canonical `falseArm = trueArm + 1`, and the
second is the loader's successor encoding of that wire.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Finite control of the mux invocation source expander. -/
inductive AffineMuxInvocationProgressionControllerLabel
  | loadSelector | incSelector
  | loadSelectorNot | incSelectorNot
  | loadHeaderFlag | scanHeaderFlag
  | headerSeparator₁ | headerSeparator₂
  | headerCopySelector | headerSaveSelector | headerEmitSelectorTick
  | headerSelectorSeparator | headerRestoreSelector
  | headerRestoreSelectorInc | headerFrameEnd
  | dataCheck
  | trueLeadTick | trueLeadSeparator
  | trueEmitFirstTick | trueScan | trueEmitTick
  | trueSeparator₁ | trueSeparator₂
  | trueCopySelector | trueSaveSelector | trueEmitSelectorTick
  | trueSelectorSeparator | trueRestoreSelector
  | trueRestoreSelectorInc | trueFrameEnd
  | falseScan | falseEmitTick
  | falseSeparator₁ | falseSeparator₂
  | falseCopySelectorNot | falseSaveSelectorNot
  | falseEmitSelectorNotTick | falseSelectorNotSeparator
  | falseRestoreSelectorNot | falseRestoreSelectorNotInc
  | falseFrameEnd
  | freshScan | freshSaveTick | freshEmitTick
  | freshSeparator₁ | freshSeparator₂
  | freshReplay | freshReplayTick | freshExtraTick | freshSecondExtraTick
  | freshFinalSeparator | freshFrameEnd
  | clearSelector | clearSelectorNot
  | finish | invalid
deriving DecidableEq, Fintype

/-- One fixed program expands every family length, selector value, and affine
segment length.  Runtime natural values live only on the input and counters.
-/
def affineMuxInvocationProgressionControllerRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineMuxInvocationProgressionControllerLabel
  main := .loadSelector
  op
    | .loadSelector => .popInput .finish fun
        | .tick => .incSelector
        | .separator => .loadSelectorNot
        | .frameEnd => .invalid
    | .incSelector => .inc₁ .loadSelector
    | .loadSelectorNot => .popInput .invalid fun
        | .tick => .incSelectorNot
        | .separator => .loadHeaderFlag
        | .frameEnd => .invalid
    | .incSelectorNot => .inc₂ .loadSelectorNot
    | .loadHeaderFlag => .popInput .invalid fun
        | .tick => .scanHeaderFlag
        | .separator => .dataCheck
        | .frameEnd => .invalid
    | .scanHeaderFlag => .popInput .invalid fun
        | .tick => .scanHeaderFlag
        | .separator => .headerSeparator₁
        | .frameEnd => .invalid
    | .headerSeparator₁ => .pushOutput .separator .headerSeparator₂
    | .headerSeparator₂ => .pushOutput .separator .headerCopySelector
    | .headerCopySelector =>
        .dec₁ .headerSelectorSeparator .headerSaveSelector
    | .headerSaveSelector => .pushWork₁ .tick .headerEmitSelectorTick
    | .headerEmitSelectorTick => .pushOutput .tick .headerCopySelector
    | .headerSelectorSeparator =>
        .pushOutput .separator .headerRestoreSelector
    | .headerRestoreSelector =>
        .popWork₁ .headerFrameEnd fun
          | .tick => .headerRestoreSelectorInc
          | _ => .invalid
    | .headerRestoreSelectorInc => .inc₁ .headerRestoreSelector
    | .headerFrameEnd => .pushOutput .frameEnd .dataCheck
    | .dataCheck => .popInput .finish fun
        | .tick => .trueLeadTick
        | .separator => .trueLeadSeparator
        | .frameEnd => .clearSelector
    | .trueLeadTick => .pushOutput .frameEnd .trueEmitFirstTick
    | .trueEmitFirstTick => .pushOutput .tick .trueScan
    | .trueLeadSeparator => .pushOutput .frameEnd .trueSeparator₁
    | .trueScan => .popInput .invalid fun
        | .tick => .trueEmitTick
        | .separator => .trueSeparator₁
        | .frameEnd => .invalid
    | .trueEmitTick => .pushOutput .tick .trueScan
    | .trueSeparator₁ => .pushOutput .separator .trueSeparator₂
    | .trueSeparator₂ => .pushOutput .separator .trueCopySelector
    | .trueCopySelector =>
        .dec₁ .trueSelectorSeparator .trueSaveSelector
    | .trueSaveSelector => .pushWork₁ .tick .trueEmitSelectorTick
    | .trueEmitSelectorTick => .pushOutput .tick .trueCopySelector
    | .trueSelectorSeparator =>
        .pushOutput .separator .trueRestoreSelector
    | .trueRestoreSelector =>
        .popWork₁ .trueFrameEnd fun
          | .tick => .trueRestoreSelectorInc
          | _ => .invalid
    | .trueRestoreSelectorInc => .inc₁ .trueRestoreSelector
    | .trueFrameEnd => .pushOutput .frameEnd .falseScan
    | .falseScan => .popInput .invalid fun
        | .tick => .falseEmitTick
        | .separator => .falseSeparator₁
        | .frameEnd => .invalid
    | .falseEmitTick => .pushOutput .tick .falseScan
    | .falseSeparator₁ => .pushOutput .separator .falseSeparator₂
    | .falseSeparator₂ =>
        .pushOutput .separator .falseCopySelectorNot
    | .falseCopySelectorNot =>
        .dec₂ .falseSelectorNotSeparator .falseSaveSelectorNot
    | .falseSaveSelectorNot =>
        .pushWork₁ .tick .falseEmitSelectorNotTick
    | .falseEmitSelectorNotTick =>
        .pushOutput .tick .falseCopySelectorNot
    | .falseSelectorNotSeparator =>
        .pushOutput .separator .falseRestoreSelectorNot
    | .falseRestoreSelectorNot =>
        .popWork₁ .falseFrameEnd fun
          | .tick => .falseRestoreSelectorNotInc
          | _ => .invalid
    | .falseRestoreSelectorNotInc =>
        .inc₂ .falseRestoreSelectorNot
    | .falseFrameEnd => .pushOutput .frameEnd .freshScan
    | .freshScan => .popInput .invalid fun
        | .tick => .freshSaveTick
        | .separator => .freshSeparator₁
        | .frameEnd => .invalid
    | .freshSaveTick => .pushWork₁ .tick .freshEmitTick
    | .freshEmitTick => .pushOutput .tick .freshScan
    | .freshSeparator₁ => .pushOutput .separator .freshSeparator₂
    | .freshSeparator₂ => .pushOutput .separator .freshReplay
    | .freshReplay => .popWork₁ .freshExtraTick fun
        | .tick => .freshReplayTick
        | _ => .invalid
    | .freshReplayTick => .pushOutput .tick .freshReplay
    | .freshExtraTick => .pushOutput .tick .freshSecondExtraTick
    | .freshSecondExtraTick => .pushOutput .tick .freshFinalSeparator
    | .freshFinalSeparator => .pushOutput .separator .freshFrameEnd
    | .freshFrameEnd => .pushOutput .frameEnd .dataCheck
    | .clearSelector => .dec₁ .clearSelectorNot .clearSelector
    | .clearSelectorNot => .dec₂ .loadSelector .clearSelectorNot
    | .finish => .halt
    | .invalid => .halt

def affineMuxInvocationProgressionControllerCfg
    (label : AffineMuxInvocationProgressionControllerLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (selector selectorNot scratch : List Unit) :
    BuilderCfg affineMuxInvocationProgressionControllerRevProgram :=
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

/-- Standard loop boundary between invocation segments. -/
def affineMuxInvocationProgressionControllerLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineMuxInvocationProgressionControllerRevProgram :=
  affineMuxInvocationProgressionControllerCfg .loadSelector none none false
    input output [] [] [] [] []

/-- Public pre-halt configuration of the reversed controller. -/
def affineMuxInvocationProgressionControllerFinishCfg
    (output : List UnaryFrameSym) :
    BuilderCfg affineMuxInvocationProgressionControllerRevProgram :=
  affineMuxInvocationProgressionControllerCfg .finish none none false
    [] output [] [] [] [] []

@[simp] theorem affineMuxInvocationProgressionController_initialCfg_eq_loop
    (input : List UnaryFrameSym) :
    initialCfg affineMuxInvocationProgressionControllerRevProgram input =
      affineMuxInvocationProgressionControllerLoopCfg input [] := rfl

@[simp] theorem affineMuxInvocationProgressionControllerFinishCfg_eq
    (output : List UnaryFrameSym) :
    affineMuxInvocationProgressionControllerFinishCfg output =
      ({ label := some
          AffineMuxInvocationProgressionControllerLabel.finish
         buffer₁ := none
         buffer₂ := none
         test := false
         input := []
         output := output
         work₁ := []
         work₂ := []
         counter₁ := []
         counter₂ := []
         counter₃ := [] } :
        BuilderCfg affineMuxInvocationProgressionControllerRevProgram) := rfl

/-- Intended complete forward output of a segment family. -/
def affineMuxInvocationProgressionFamilyFrames
    (segments : List AffineMuxInvocationProgression) :
    List UnaryFrameSym :=
  segments.flatMap AffineMuxInvocationProgression.invocationFrames

private theorem muxInvocation_replicate_append_cons {alpha : Type}
    (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

theorem muxInvocation_loadSelector_eval
    (selector : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (tail output work₁ work₂ : List UnaryFrameSym)
    (currentSelector selectorNot scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * selector + 1]
      (some (affineMuxInvocationProgressionControllerCfg .loadSelector
        buffer₁ buffer₂ test (encodeUnaryFrameBlock selector ++ tail)
        output work₁ work₂ currentSelector selectorNot scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .loadSelectorNot
        (some .separator) buffer₂ test tail output work₁ work₂
        (List.replicate selector () ++ currentSelector) selectorNot
        scratch) := by
  induction selector generalizing buffer₁ currentSelector with
  | zero => rfl
  | succ selector ih =>
      rw [show 2 * (selector + 1) + 1 =
          (2 * selector + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * selector + 1]
          (some (affineMuxInvocationProgressionControllerCfg .loadSelector
            (some .tick) buffer₂ test
            (encodeUnaryFrameBlock selector ++ tail) output work₁ work₂
            (() :: currentSelector) selectorNot scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: currentSelector)

theorem muxInvocation_loadSelectorNot_eval
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output work₁ work₂ : List UnaryFrameSym)
    (currentSelectorNot scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * selectorNot + 1]
      (some (affineMuxInvocationProgressionControllerCfg .loadSelectorNot
        buffer₁ buffer₂ test
        (encodeUnaryFrameBlock selectorNot ++ tail) output work₁ work₂
        (List.replicate selector ()) currentSelectorNot scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .loadHeaderFlag
        (some .separator) buffer₂ test tail output work₁ work₂
        (List.replicate selector ())
        (List.replicate selectorNot () ++ currentSelectorNot) scratch) := by
  induction selectorNot generalizing buffer₁ currentSelectorNot with
  | zero => rfl
  | succ selectorNot ih =>
      rw [show 2 * (selectorNot + 1) + 1 =
          (2 * selectorNot + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * selectorNot + 1]
          (some (affineMuxInvocationProgressionControllerCfg .loadSelectorNot
            (some .tick) buffer₂ test
            (encodeUnaryFrameBlock selectorNot ++ tail) output work₁ work₂
            (List.replicate selector ()) (() :: currentSelectorNot)
            scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: currentSelectorNot)

theorem muxInvocation_headerFlag_false_eval
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[1]
      (some (affineMuxInvocationProgressionControllerCfg .loadHeaderFlag
        buffer₁ buffer₂ test (.separator :: tail) output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])) =
      some (affineMuxInvocationProgressionControllerCfg .dataCheck
        (some .separator) buffer₂ test tail output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) []) := by
  rfl

theorem muxInvocation_headerFlag_true_eval
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[2]
      (some (affineMuxInvocationProgressionControllerCfg .loadHeaderFlag
        buffer₁ buffer₂ test (.tick :: .separator :: tail) output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])) =
      some (affineMuxInvocationProgressionControllerCfg .headerSeparator₁
        (some .separator) buffer₂ test tail output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) []) := by
  rfl

private theorem muxInvocation_headerCopySelector_eval
    (selector : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₁ work₂ : List UnaryFrameSym)
    (selectorNot scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        3 * selector + 1]
      (some (affineMuxInvocationProgressionControllerCfg .headerCopySelector
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate selector ()) selectorNot scratch)) =
      some (affineMuxInvocationProgressionControllerCfg
        .headerSelectorSeparator buffer₁ buffer₂ false input
        (List.replicate selector .tick ++ output)
        (List.replicate selector .tick ++ work₁) work₂ [] selectorNot
        scratch) := by
  induction selector generalizing test output work₁ with
  | zero => rfl
  | succ selector ih =>
      rw [show 3 * (selector + 1) + 1 =
          (3 * selector + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            3 * selector + 1]
          (some (affineMuxInvocationProgressionControllerCfg
            .headerCopySelector buffer₁ buffer₂ true input
            (.tick :: output) (.tick :: work₁) work₂
            (List.replicate selector ()) selectorNot scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih true (.tick :: output) (.tick :: work₁)

private theorem muxInvocation_headerRestoreSelector_eval
    (selector : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₂ : List UnaryFrameSym)
    (currentSelector selectorNot scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * selector + 1]
      (some (affineMuxInvocationProgressionControllerCfg
        .headerRestoreSelector buffer₁ buffer₂ test input output
        (List.replicate selector .tick) work₂ currentSelector selectorNot
        scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .headerFrameEnd none
        buffer₂ test input output [] work₂
        (List.replicate selector () ++ currentSelector) selectorNot scratch) := by
  induction selector generalizing buffer₁ currentSelector with
  | zero => rfl
  | succ selector ih =>
      rw [show 2 * (selector + 1) + 1 =
          (2 * selector + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * selector + 1]
          (some (affineMuxInvocationProgressionControllerCfg
            .headerRestoreSelector (some .tick) buffer₂ test input output
            (List.replicate selector .tick) work₂ (() :: currentSelector)
            selectorNot scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: currentSelector)

def muxInvocation_header_emit
    (selector selectorNot : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .headerSeparator₁
        buffer₁ buffer₂ test input output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
        buffer₂ false input
        ((encodeAffineMuxFinHeader selector).reverse ++ output) [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) []))
      (5 * selector + 6) := by
  let afterSeparators :=
    affineMuxInvocationProgressionControllerCfg .headerCopySelector buffer₁
      buffer₂ test input (.separator :: .separator :: output) [] []
      (List.replicate selector ()) (List.replicate selectorNot ()) []
  have hseparators : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .headerSeparator₁
        buffer₁ buffer₂ test input output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some afterSeparators) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  let afterCopy :=
    affineMuxInvocationProgressionControllerCfg .headerSelectorSeparator
      buffer₁ buffer₂ false input
      (List.replicate selector .tick ++
        (.separator :: .separator :: output))
      (List.replicate selector .tick) [] []
      (List.replicate selectorNot ()) []
  have hcopy : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterSeparators (some afterCopy) (3 * selector + 1) := by
    exact ⟨⟨3 * selector + 1, by
      simpa [afterSeparators, afterCopy, List.append_assoc] using
        muxInvocation_headerCopySelector_eval selector buffer₁ buffer₂
          test input (.separator :: .separator :: output) [] []
          (List.replicate selectorNot ()) []⟩, le_rfl⟩
  let beforeRestore :=
    affineMuxInvocationProgressionControllerCfg .headerRestoreSelector
      buffer₁ buffer₂ false input
      (.separator ::
        (List.replicate selector .tick ++
          (.separator :: .separator :: output)))
      (List.replicate selector .tick) [] []
      (List.replicate selectorNot ()) []
  have hseparator : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterCopy (some beforeRestore) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeFrameEnd :=
    affineMuxInvocationProgressionControllerCfg .headerFrameEnd none buffer₂
      false input
      (.separator ::
        (List.replicate selector .tick ++
          (.separator :: .separator :: output)))
      [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hrestore : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeRestore (some beforeFrameEnd) (2 * selector + 1) := by
    exact ⟨⟨2 * selector + 1, by
      simpa [beforeRestore, beforeFrameEnd] using
        muxInvocation_headerRestoreSelector_eval selector buffer₁ buffer₂
          false input
          (.separator ::
            (List.replicate selector .tick ++
              (.separator :: .separator :: output)))
          [] [] (List.replicate selectorNot ()) []⟩, le_rfl⟩
  have hframeEnd : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeFrameEnd
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
        buffer₂ false input
        (.frameEnd :: .separator ::
          (List.replicate selector .tick ++
            (.separator :: .separator :: output)))
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let first := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    2 (3 * selector + 1) _ _ _ hseparators hcopy
  let second := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ 1 _ _ _ first hseparator
  let third := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (2 * selector + 1) _ _ _ second hrestore
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ 1 _ _ _ third hframeEnd
  convert full using 1
  · simp [encodeAffineMuxFinHeader, encodeUnaryFrame,
      encodeUnaryFrameBlock, List.reverse_append, List.append_assoc]
  · omega

private theorem muxInvocation_trueScan_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (tail output : List UnaryFrameSym)
    (selector selectorNot : Nat) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * value + 3]
      (some (affineMuxInvocationProgressionControllerCfg .trueScan
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) =
      some (affineMuxInvocationProgressionControllerCfg .trueCopySelector
        (some .separator) buffer₂ test tail
        (.separator ::
          ((encodeUnaryFrameBlock value).reverse ++ output))
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []) := by
  induction value generalizing buffer₁ output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 3 =
          (2 * value + 3) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * value + 3]
          (some (affineMuxInvocationProgressionControllerCfg .trueScan
            (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) (.tick :: output) [] []
            (List.replicate selector ())
            (List.replicate selectorNot ()) [])) = _
      simpa only [encodeUnaryFrameBlock, List.reverse_append,
        List.reverse_replicate, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, List.append_assoc,
        List.replicate_succ, muxInvocation_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: output)

private theorem muxInvocation_truePrefix_eval
    (value selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * value + 4]
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) =
      some (affineMuxInvocationProgressionControllerCfg .trueCopySelector
        (some .separator) buffer₂ test tail
        (([UnaryFrameSym.frameEnd] ++ encodeUnaryFrameBlock value ++
            [UnaryFrameSym.separator]).reverse ++ output)
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []) := by
  cases value with
  | zero => rfl
  | succ value =>
      rw [show 2 * (value + 1) + 4 =
          (2 * value + 3) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * value + 3]
          (some (affineMuxInvocationProgressionControllerCfg .trueScan
            (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail)
            (.tick :: .frameEnd :: output) [] []
            (List.replicate selector ())
            (List.replicate selectorNot ()) [])) = _
      simpa only [encodeUnaryFrameBlock, List.reverse_append,
        List.reverse_replicate, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, List.append_assoc,
        List.replicate_succ, muxInvocation_replicate_append_cons,
        List.cons_append] using
        muxInvocation_trueScan_eval value (some .tick) buffer₂ test tail
          (.tick :: .frameEnd :: output) selector selectorNot

private theorem muxInvocation_trueCopySelector_eval
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        3 * selector + 1]
      (some (affineMuxInvocationProgressionControllerCfg .trueCopySelector
        buffer₁ buffer₂ test input output work₁ work₂
        (List.replicate selector ()) (List.replicate selectorNot ())
        scratch)) =
      some (affineMuxInvocationProgressionControllerCfg
        .trueSelectorSeparator buffer₁ buffer₂ false input
        (List.replicate selector .tick ++ output)
        (List.replicate selector .tick ++ work₁) work₂ []
        (List.replicate selectorNot ()) scratch) := by
  induction selector generalizing test output work₁ with
  | zero => rfl
  | succ selector ih =>
      rw [show 3 * (selector + 1) + 1 =
          (3 * selector + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            3 * selector + 1]
          (some (affineMuxInvocationProgressionControllerCfg .trueCopySelector
            buffer₁ buffer₂ true input (.tick :: output)
            (.tick :: work₁) work₂ (List.replicate selector ())
            (List.replicate selectorNot ()) scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih true (.tick :: output) (.tick :: work₁)

private theorem muxInvocation_trueRestoreSelector_eval
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (currentSelector scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * selector + 1]
      (some (affineMuxInvocationProgressionControllerCfg .trueRestoreSelector
        buffer₁ buffer₂ test input output
        (List.replicate selector .tick) work₂ currentSelector
        (List.replicate selectorNot ()) scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .trueFrameEnd none
        buffer₂ test input output [] work₂
        (List.replicate selector () ++ currentSelector)
        (List.replicate selectorNot ()) scratch) := by
  induction selector generalizing buffer₁ currentSelector with
  | zero => rfl
  | succ selector ih =>
      rw [show 2 * (selector + 1) + 1 =
          (2 * selector + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * selector + 1]
          (some (affineMuxInvocationProgressionControllerCfg
            .trueRestoreSelector (some .tick) buffer₂ test input output
            (List.replicate selector .tick) work₂ (() :: currentSelector)
            (List.replicate selectorNot ()) scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: currentSelector)

private def muxInvocation_trueSuffix_emit
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .trueCopySelector
        buffer₁ buffer₂ test input output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .falseScan none
        buffer₂ false input
        ((encodeUnaryFrameBlock selector ++
            [UnaryFrameSym.frameEnd]).reverse ++ output)
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []))
      (5 * selector + 4) := by
  let afterCopy :=
    affineMuxInvocationProgressionControllerCfg .trueSelectorSeparator
      buffer₁ buffer₂ false input
      (List.replicate selector .tick ++ output)
      (List.replicate selector .tick) [] []
      (List.replicate selectorNot ()) []
  have hcopy : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .trueCopySelector
        buffer₁ buffer₂ test input output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some afterCopy) (3 * selector + 1) := by
    exact ⟨⟨3 * selector + 1, by
      simpa [afterCopy] using
        muxInvocation_trueCopySelector_eval selector selectorNot buffer₁
          buffer₂ test input output [] [] []⟩, le_rfl⟩
  let beforeRestore :=
    affineMuxInvocationProgressionControllerCfg .trueRestoreSelector
      buffer₁ buffer₂ false input
      (.separator :: (List.replicate selector .tick ++ output))
      (List.replicate selector .tick) [] []
      (List.replicate selectorNot ()) []
  have hseparator : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterCopy (some beforeRestore) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeFrameEnd :=
    affineMuxInvocationProgressionControllerCfg .trueFrameEnd none buffer₂
      false input (.separator :: (List.replicate selector .tick ++ output))
      [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hrestore : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeRestore (some beforeFrameEnd) (2 * selector + 1) :=
    ⟨⟨2 * selector + 1, by
      simpa [beforeRestore, beforeFrameEnd] using
        muxInvocation_trueRestoreSelector_eval selector selectorNot buffer₁
          buffer₂ false input
          (.separator :: (List.replicate selector .tick ++ output)) [] [] []⟩,
      le_rfl⟩
  have hframeEnd : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeFrameEnd
      (some (affineMuxInvocationProgressionControllerCfg .falseScan none
        buffer₂ false input
        (.frameEnd :: .separator ::
          (List.replicate selector .tick ++ output))
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let first := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    (3 * selector + 1) 1 _ _ _ hcopy hseparator
  let second := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (2 * selector + 1) _ _ _ first hrestore
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ 1 _ _ _ second hframeEnd
  convert full using 1
  · simp [encodeUnaryFrameBlock, List.reverse_append, List.append_assoc]
  · omega

private theorem muxInvocation_falseScan_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (tail output : List UnaryFrameSym)
    (selector selectorNot : Nat) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * value + 3]
      (some (affineMuxInvocationProgressionControllerCfg .falseScan
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) =
      some (affineMuxInvocationProgressionControllerCfg
        .falseCopySelectorNot (some .separator) buffer₂ test tail
        (.separator ::
          ((encodeUnaryFrameBlock value).reverse ++ output))
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []) := by
  induction value generalizing buffer₁ output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 3 =
          (2 * value + 3) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * value + 3]
          (some (affineMuxInvocationProgressionControllerCfg .falseScan
            (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) (.tick :: output) [] []
            (List.replicate selector ())
            (List.replicate selectorNot ()) [])) = _
      simpa only [encodeUnaryFrameBlock, List.reverse_append,
        List.reverse_replicate, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, List.append_assoc,
        List.replicate_succ, muxInvocation_replicate_append_cons,
        List.cons_append] using ih (some .tick) (.tick :: output)

private theorem muxInvocation_falseCopySelectorNot_eval
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        3 * selectorNot + 1]
      (some (affineMuxInvocationProgressionControllerCfg
        .falseCopySelectorNot buffer₁ buffer₂ test input output
        work₁ work₂ (List.replicate selector ())
        (List.replicate selectorNot ()) scratch)) =
      some (affineMuxInvocationProgressionControllerCfg
        .falseSelectorNotSeparator buffer₁ buffer₂ false input
        (List.replicate selectorNot .tick ++ output)
        (List.replicate selectorNot .tick ++ work₁) work₂
        (List.replicate selector ()) [] scratch) := by
  induction selectorNot generalizing test output work₁ with
  | zero => rfl
  | succ selectorNot ih =>
      rw [show 3 * (selectorNot + 1) + 1 =
          (3 * selectorNot + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            3 * selectorNot + 1]
          (some (affineMuxInvocationProgressionControllerCfg
            .falseCopySelectorNot buffer₁ buffer₂ true input
            (.tick :: output) (.tick :: work₁) work₂
            (List.replicate selector ()) (List.replicate selectorNot ())
            scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih true (.tick :: output) (.tick :: work₁)

private theorem muxInvocation_falseRestoreSelectorNot_eval
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₂ : List UnaryFrameSym)
    (currentSelectorNot scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * selectorNot + 1]
      (some (affineMuxInvocationProgressionControllerCfg
        .falseRestoreSelectorNot buffer₁ buffer₂ test input output
        (List.replicate selectorNot .tick) work₂
        (List.replicate selector ()) currentSelectorNot scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .falseFrameEnd none
        buffer₂ test input output [] work₂
        (List.replicate selector ())
        (List.replicate selectorNot () ++ currentSelectorNot) scratch) := by
  induction selectorNot generalizing buffer₁ currentSelectorNot with
  | zero => rfl
  | succ selectorNot ih =>
      rw [show 2 * (selectorNot + 1) + 1 =
          (2 * selectorNot + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * selectorNot + 1]
          (some (affineMuxInvocationProgressionControllerCfg
            .falseRestoreSelectorNot (some .tick) buffer₂ test input output
            (List.replicate selectorNot .tick) work₂
            (List.replicate selector ()) (() :: currentSelectorNot)
            scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: currentSelectorNot)

private def muxInvocation_falseSuffix_emit
    (selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg
        .falseCopySelectorNot buffer₁ buffer₂ test input output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .freshScan none
        buffer₂ false input
        ((encodeUnaryFrameBlock selectorNot ++
            [UnaryFrameSym.frameEnd]).reverse ++ output)
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []))
      (5 * selectorNot + 4) := by
  let afterCopy :=
    affineMuxInvocationProgressionControllerCfg
      .falseSelectorNotSeparator buffer₁ buffer₂ false input
      (List.replicate selectorNot .tick ++ output)
      (List.replicate selectorNot .tick) []
      (List.replicate selector ()) [] []
  have hcopy : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg
        .falseCopySelectorNot buffer₁ buffer₂ test input output [] []
        (List.replicate selector ()) (List.replicate selectorNot ()) [])
      (some afterCopy) (3 * selectorNot + 1) := by
    exact ⟨⟨3 * selectorNot + 1, by
      simpa [afterCopy] using
        muxInvocation_falseCopySelectorNot_eval selector selectorNot buffer₁
          buffer₂ test input output [] [] []⟩, le_rfl⟩
  let beforeRestore :=
    affineMuxInvocationProgressionControllerCfg
      .falseRestoreSelectorNot buffer₁ buffer₂ false input
      (.separator :: (List.replicate selectorNot .tick ++ output))
      (List.replicate selectorNot .tick) []
      (List.replicate selector ()) [] []
  have hseparator : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterCopy (some beforeRestore) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeFrameEnd :=
    affineMuxInvocationProgressionControllerCfg .falseFrameEnd none buffer₂
      false input
      (.separator :: (List.replicate selectorNot .tick ++ output))
      [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hrestore : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeRestore (some beforeFrameEnd) (2 * selectorNot + 1) :=
    ⟨⟨2 * selectorNot + 1, by
      simpa [beforeRestore, beforeFrameEnd] using
        muxInvocation_falseRestoreSelectorNot_eval selector selectorNot
          buffer₁ buffer₂ false input
          (.separator :: (List.replicate selectorNot .tick ++ output))
          [] [] []⟩, le_rfl⟩
  have hframeEnd : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeFrameEnd
      (some (affineMuxInvocationProgressionControllerCfg .freshScan none
        buffer₂ false input
        (.frameEnd :: .separator ::
          (List.replicate selectorNot .tick ++ output))
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let first := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    (3 * selectorNot + 1) 1 _ _ _ hcopy hseparator
  let second := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (2 * selectorNot + 1) _ _ _ first hrestore
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ 1 _ _ _ second hframeEnd
  convert full using 1
  · simp [encodeUnaryFrameBlock, List.reverse_append, List.append_assoc]
  · omega

private theorem muxInvocation_freshScan_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (tail output work₁ : List UnaryFrameSym)
    (selector selectorNot : Nat) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        3 * value + 3]
      (some (affineMuxInvocationProgressionControllerCfg .freshScan
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail)
        output work₁ [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) =
      some (affineMuxInvocationProgressionControllerCfg .freshReplay
        (some .separator) buffer₂ test tail
        (.separator ::
          ((encodeUnaryFrameBlock value).reverse ++ output))
        (List.replicate value .tick ++ work₁) []
        (List.replicate selector ()) (List.replicate selectorNot ()) []) := by
  induction value generalizing buffer₁ output work₁ with
  | zero => rfl
  | succ value ih =>
      rw [show 3 * (value + 1) + 3 =
          (3 * value + 3) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            3 * value + 3]
          (some (affineMuxInvocationProgressionControllerCfg .freshScan
            (some .tick) buffer₂ test
            (encodeUnaryFrameBlock value ++ tail) (.tick :: output)
            (.tick :: work₁) [] (List.replicate selector ())
            (List.replicate selectorNot ()) [])) = _
      simpa only [encodeUnaryFrameBlock, List.reverse_append,
        List.reverse_replicate, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.singleton_append, List.append_assoc,
        List.replicate_succ, muxInvocation_replicate_append_cons,
        List.cons_append] using
        ih (some .tick) (.tick :: output) (.tick :: work₁)

private theorem muxInvocation_freshReplay_eval
    (value : Nat) (buffer₁ buffer₂ : Option UnaryFrameSym)
    (test : Bool) (input output work₂ : List UnaryFrameSym)
    (selector selectorNot : Nat) (scratch : List Unit) :
    (flip Option.bind
      (step affineMuxInvocationProgressionControllerRevProgram))^[
        2 * value + 1]
      (some (affineMuxInvocationProgressionControllerCfg .freshReplay
        buffer₁ buffer₂ test input output
        (List.replicate value .tick) work₂
        (List.replicate selector ()) (List.replicate selectorNot ())
        scratch)) =
      some (affineMuxInvocationProgressionControllerCfg .freshExtraTick none
        buffer₂ test input (List.replicate value .tick ++ output) [] work₂
        (List.replicate selector ()) (List.replicate selectorNot ())
        scratch) := by
  induction value generalizing buffer₁ output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 =
          (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineMuxInvocationProgressionControllerRevProgram))^[
            2 * value + 1]
          (some (affineMuxInvocationProgressionControllerCfg .freshReplay
            (some .tick) buffer₂ test input (.tick :: output)
            (List.replicate value .tick) work₂
            (List.replicate selector ()) (List.replicate selectorNot ())
            scratch)) = _
      simpa only [List.replicate_succ,
        muxInvocation_replicate_append_cons, List.cons_append] using
        ih (some .tick) (.tick :: output)

private def muxInvocation_fresh_emit
    (value selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .freshScan
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
        buffer₂ test tail
        ((encodeUnaryFrame [value, 0, value + 2] ++
            [UnaryFrameSym.frameEnd]).reverse ++ output)
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []))
      (5 * value + 8) := by
  let afterScan :=
    affineMuxInvocationProgressionControllerCfg .freshReplay
      (some .separator) buffer₂ test tail
      (.separator :: ((encodeUnaryFrameBlock value).reverse ++ output))
      (List.replicate value .tick) [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hscan : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .freshScan
        buffer₁ buffer₂ test (encodeUnaryFrameBlock value ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])
      (some afterScan) (3 * value + 3) :=
    ⟨⟨3 * value + 3, by
      simpa [afterScan] using
        muxInvocation_freshScan_eval value buffer₁ buffer₂ test tail
          output [] selector selectorNot⟩, le_rfl⟩
  let beforeExtras :=
    affineMuxInvocationProgressionControllerCfg .freshExtraTick none buffer₂
      test tail
      (List.replicate value .tick ++
        (.separator :: ((encodeUnaryFrameBlock value).reverse ++ output)))
      [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hreplay : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterScan (some beforeExtras) (2 * value + 1) :=
    ⟨⟨2 * value + 1, by
      simpa [afterScan, beforeExtras] using
        muxInvocation_freshReplay_eval value (some .separator) buffer₂ test
          tail (.separator ::
            ((encodeUnaryFrameBlock value).reverse ++ output)) []
          selector selectorNot []⟩, le_rfl⟩
  have hextras : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      beforeExtras
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
        buffer₂ test tail
        (.frameEnd :: .separator :: .tick :: .tick ::
          (List.replicate value .tick ++
            (.separator ::
              ((encodeUnaryFrameBlock value).reverse ++ output))))
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])) 4 := ⟨⟨4, rfl⟩, le_rfl⟩
  let first := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    (3 * value + 3) (2 * value + 1) _ _ _ hscan hreplay
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ 4 _ _ _ first hextras
  convert full using 1
  · simp [encodeUnaryFrame, encodeUnaryFrameBlock,
      List.reverse_append, List.append_assoc, List.replicate_add]
  · omega

/-- Exact execution for one source triple.  The output is definitionally the
existing mux-controller frame, including the successor encoding of the
canonical adjacent false-arm wire. -/
def affineMuxInvocationProgressionController_row_emit
    (whenTrue whenFalse trueArm selector selectorNot : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .dataCheck
        buffer₁ buffer₂ test
        (encodeUnaryFrame [whenTrue, whenFalse, trueArm] ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])
      (some (affineMuxInvocationProgressionControllerCfg .dataCheck none
        buffer₂ false tail
        ((encodeAffineMuxFinPairFrame
          { whenTrue := whenTrue
            whenFalse := whenFalse
            selector := selector
            selectorNot := selectorNot
            trueArm := trueArm
            falseArm := trueArm + 1 }).reverse ++ output)
        [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) []))
      (2 * whenTrue + 2 * whenFalse + 5 * trueArm +
        5 * selector + 5 * selectorNot + 23) := by
  let falseAndFreshInput :=
    encodeUnaryFrameBlock whenFalse ++
      encodeUnaryFrameBlock trueArm ++ tail
  let afterTruePrefixOutput :=
    (([UnaryFrameSym.frameEnd] ++ encodeUnaryFrameBlock whenTrue ++
        [UnaryFrameSym.separator]).reverse ++ output)
  let afterTruePrefix :=
    affineMuxInvocationProgressionControllerCfg .trueCopySelector
      (some .separator) buffer₂ test falseAndFreshInput
      afterTruePrefixOutput [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have htruePrefix : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      (affineMuxInvocationProgressionControllerCfg .dataCheck
        buffer₁ buffer₂ test
        (encodeUnaryFrame [whenTrue, whenFalse, trueArm] ++ tail)
        output [] [] (List.replicate selector ())
        (List.replicate selectorNot ()) [])
      (some afterTruePrefix) (2 * whenTrue + 4) :=
    ⟨⟨2 * whenTrue + 4, by
      simpa [afterTruePrefix, afterTruePrefixOutput, falseAndFreshInput,
        encodeUnaryFrame, List.append_assoc] using
        muxInvocation_truePrefix_eval whenTrue selector selectorNot buffer₁
          buffer₂ test falseAndFreshInput output⟩, le_rfl⟩
  let afterTrueOutput :=
    ((encodeUnaryFrameBlock selector ++ [UnaryFrameSym.frameEnd]).reverse ++
      afterTruePrefixOutput)
  let afterTrue :=
    affineMuxInvocationProgressionControllerCfg .falseScan none buffer₂ false
      falseAndFreshInput afterTrueOutput [] []
      (List.replicate selector ()) (List.replicate selectorNot ()) []
  have htrueSuffix : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterTruePrefix (some afterTrue) (5 * selector + 4) := by
    simpa [afterTruePrefix, afterTrue, afterTrueOutput] using
      muxInvocation_trueSuffix_emit selector selectorNot (some .separator)
        buffer₂ test falseAndFreshInput afterTruePrefixOutput
  let freshInput := encodeUnaryFrameBlock trueArm ++ tail
  let afterFalsePrefixOutput :=
    (.separator ::
      ((encodeUnaryFrameBlock whenFalse).reverse ++ afterTrueOutput))
  let afterFalsePrefix :=
    affineMuxInvocationProgressionControllerCfg .falseCopySelectorNot
      (some .separator) buffer₂ false freshInput afterFalsePrefixOutput
      [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hfalsePrefix : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterTrue (some afterFalsePrefix) (2 * whenFalse + 3) :=
    ⟨⟨2 * whenFalse + 3, by
      simpa [afterTrue, afterFalsePrefix, afterFalsePrefixOutput,
        falseAndFreshInput, freshInput, List.append_assoc] using
        muxInvocation_falseScan_eval whenFalse none buffer₂ false freshInput
          afterTrueOutput selector selectorNot⟩, le_rfl⟩
  let afterFalseOutput :=
    ((encodeUnaryFrameBlock selectorNot ++
        [UnaryFrameSym.frameEnd]).reverse ++ afterFalsePrefixOutput)
  let afterFalse :=
    affineMuxInvocationProgressionControllerCfg .freshScan none buffer₂ false
      freshInput afterFalseOutput [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hfalseSuffix : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterFalsePrefix (some afterFalse) (5 * selectorNot + 4) := by
    simpa [afterFalsePrefix, afterFalse, afterFalseOutput] using
      muxInvocation_falseSuffix_emit selector selectorNot (some .separator)
        buffer₂ false freshInput afterFalsePrefixOutput
  let finalOutput :=
    ((encodeUnaryFrame [trueArm, 0, trueArm + 2] ++
        [UnaryFrameSym.frameEnd]).reverse ++ afterFalseOutput)
  let finalCfg :=
    affineMuxInvocationProgressionControllerCfg .dataCheck none buffer₂ false
      tail finalOutput [] [] (List.replicate selector ())
      (List.replicate selectorNot ()) []
  have hfresh : EvalsToInTime
      (step affineMuxInvocationProgressionControllerRevProgram)
      afterFalse (some finalCfg) (5 * trueArm + 8) := by
    simpa [afterFalse, finalCfg, finalOutput, freshInput] using
      muxInvocation_fresh_emit trueArm selector selectorNot none buffer₂ false
        tail afterFalseOutput
  let first := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    (2 * whenTrue + 4) (5 * selector + 4) _ _ _
    htruePrefix htrueSuffix
  let second := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (2 * whenFalse + 3) _ _ _ first hfalsePrefix
  let third := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (5 * selectorNot + 4) _ _ _ second hfalseSuffix
  let full := EvalsToInTime.trans
    (step affineMuxInvocationProgressionControllerRevProgram)
    _ (5 * trueArm + 8) _ _ _ third hfresh
  convert full using 1
  · simp [finalCfg, finalOutput, afterFalseOutput, afterFalsePrefixOutput,
      afterTrueOutput, afterTruePrefixOutput, encodeAffineMuxFinPairFrame,
      encodeUnaryFrame, encodeUnaryFrameBlock, List.reverse_append,
      List.append_assoc, Nat.add_assoc]
  · omega

end CLRS.Chapter34.Turing.PolyBuilder
