import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneMarkedRowInvocationSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Normalizing seed-carrier exactly-one rows

The seed-carrier projector emits each row as its genuine output-source
invocations followed by two synthetic carrier invocations.  The next source
stage needs the seed first, so it can derive the fixed validity-tail operands
before handing the genuine invocations to the final-conjunction source.

This module performs that reordering with one fixed TM2.  It scans one row to
a work stack, decodes `(height, start, rowBase)` from the carrier suffix, emits
the ordinary three-field seed, and restores the genuine invocation payload
byte-for-byte.  Runtime values remain unary tape data throughout.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Genuine output-source invocations of one structured exactly-one row. -/
def affineExactlyOneSeedCarrierRawInvocations
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : List UnaryFrameSym :=
  encodeAffineExactlyOneOutputSourceInvocationFamily
    (affineExactlyOneStructuredRowFrames labelWidth stateWidth cellCounts
      seed.height seed.start seed.rowBase).reverse

/-- Canonical normalized packet: ordinary seed bytes, an internal boundary,
the genuine output-source invocations, and the row boundary. -/
def encodeAffineExactlyOneSeedCarrierNormalizedRow
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : List UnaryFrameSym :=
  encodeAffineExactlyOneStructuredRowSeed seed ++ [.frameEnd] ++
    affineExactlyOneSeedCarrierRawInvocations
      labelWidth stateWidth cellCounts seed ++ [.frameEnd]

/-- Row-major normalized family. -/
def encodeAffineExactlyOneSeedCarrierNormalizedFamily
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → List UnaryFrameSym
  | [] => []
  | seed :: rest =>
      encodeAffineExactlyOneSeedCarrierNormalizedRow
          labelWidth stateWidth cellCounts seed ++
        encodeAffineExactlyOneSeedCarrierNormalizedFamily
          labelWidth stateWidth cellCounts rest

/-- Finite control of the carrier normalizer. -/
inductive AffineExactlyOneSeedCarrierNormalizeLabel
  | scan | save (symbol : UnaryFrameSym)
  | expectFinalZero | expectStartSeparator
  | loadStart | incStart
  | loadHeight | incHeight
  | expectBaseZero₁ | expectBaseZero₂
  | loadBase | incBase | restoreRawSeparator
  | emitHeight | pushHeightTick | pushHeightSeparator
  | emitStart | pushStartTick | pushStartSeparator
  | emitBase | pushBaseTick | pushBaseSeparator
  | pushSeedEnd
  | reverseRaw | emitRaw | pushRaw (symbol : UnaryFrameSym)
  | pushRowEnd | halt | invalid
deriving DecidableEq, Fintype

/-- Fixed reverse-output normalizer.  Its control graph is independent of all
row widths and runtime values. -/
def affineExactlyOneSeedCarrierNormalizeRevProgram :
    Program UnaryFrameSym UnaryFrameSym where
  Label := AffineExactlyOneSeedCarrierNormalizeLabel
  main := .scan
  op
    | .scan => .popInput .halt fun
        | .frameEnd => .expectFinalZero
        | symbol => .save symbol
    | .save symbol => .pushWork₁ symbol .scan
    | .expectFinalZero => .popWork₁ .invalid fun
        | .separator => .expectStartSeparator
        | _ => .invalid
    | .expectStartSeparator => .popWork₁ .invalid fun
        | .separator => .loadStart
        | _ => .invalid
    | .loadStart => .popWork₁ .invalid fun
        | .tick => .incStart
        | .separator => .loadHeight
        | .frameEnd => .invalid
    | .incStart => .inc₂ .loadStart
    | .loadHeight => .popWork₁ .invalid fun
        | .tick => .incHeight
        | .separator => .expectBaseZero₁
        | .frameEnd => .invalid
    | .incHeight => .inc₁ .loadHeight
    | .expectBaseZero₁ => .popWork₁ .invalid fun
        | .separator => .expectBaseZero₂
        | _ => .invalid
    | .expectBaseZero₂ => .popWork₁ .invalid fun
        | .separator => .loadBase
        | _ => .invalid
    | .loadBase => .popWork₁ .invalid fun
        | .tick => .incBase
        | .separator => .restoreRawSeparator
        | .frameEnd => .invalid
    | .incBase => .inc₃ .loadBase
    | .restoreRawSeparator => .pushWork₁ .separator .emitHeight
    | .emitHeight => .dec₁ .pushHeightSeparator .pushHeightTick
    | .pushHeightTick => .pushOutput .tick .emitHeight
    | .pushHeightSeparator => .pushOutput .separator .emitStart
    | .emitStart => .dec₂ .pushStartSeparator .pushStartTick
    | .pushStartTick => .pushOutput .tick .emitStart
    | .pushStartSeparator => .pushOutput .separator .emitBase
    | .emitBase => .dec₃ .pushBaseSeparator .pushBaseTick
    | .pushBaseTick => .pushOutput .tick .emitBase
    | .pushBaseSeparator => .pushOutput .separator .pushSeedEnd
    | .pushSeedEnd => .pushOutput .frameEnd .reverseRaw
    | .reverseRaw => .moveWork₁Work₂ .emitRaw fun _ => .reverseRaw
    | .emitRaw => .popWork₂ .pushRowEnd fun symbol => .pushRaw symbol
    | .pushRaw symbol => .pushOutput symbol .emitRaw
    | .pushRowEnd => .pushOutput .frameEnd .scan
    | .halt => .halt
    | .invalid => .halt

private def affineExactlyOneSeedCarrierNormalizeCfg
    (label : AffineExactlyOneSeedCarrierNormalizeLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start rowBase : List Unit) :
    BuilderCfg affineExactlyOneSeedCarrierNormalizeRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := height
  counter₂ := start
  counter₃ := rowBase

/-- Clean row boundary used both initially and after every normalized row. -/
def affineExactlyOneSeedCarrierNormalizeLoopCfg
    (input output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneSeedCarrierNormalizeRevProgram :=
  affineExactlyOneSeedCarrierNormalizeCfg .scan none none false
    input output [] [] [] [] []

/-- Halted configuration of the reverse-output normalizer. -/
def affineExactlyOneSeedCarrierNormalizeHaltCfg
    (output : List UnaryFrameSym) :
    BuilderCfg affineExactlyOneSeedCarrierNormalizeRevProgram :=
  { affineExactlyOneSeedCarrierNormalizeLoopCfg [] output with label := none }

private theorem carrierNormalize_encodeUnaryFrame_no_frameEnd
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, hvalue, hsymbol⟩
  simp [encodeUnaryFrameBlock] at hsymbol
  rcases hsymbol with (⟨hvalue, rfl⟩ | rfl) <;> simp

private theorem carrierNormalize_raw_no_frameEnd
    (frames : List AffineExactlyOneFrame) :
    ∀ symbol ∈ encodeAffineExactlyOneOutputSourceInvocationFamily frames,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  simp only [encodeAffineExactlyOneOutputSourceInvocationFamily,
    List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨frame, hframe, hsymbol⟩
  exact carrierNormalize_encodeUnaryFrame_no_frameEnd _ symbol hsymbol

/-- Every genuine structured row payload is nonempty and ends in an ordinary
separator.  The parser borrows that separator while recognizing the reversed
`rowBase` block, then restores it before emitting anything. -/
theorem affineExactlyOneSeedCarrierRawInvocations_eq_append_separator
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) :
    ∃ head : List UnaryFrameSym,
      affineExactlyOneSeedCarrierRawInvocations
          labelWidth stateWidth cellCounts seed =
        head ++ [.separator] := by
  let row := affineExactlyOneSeedCarrierRawInvocations
    labelWidth stateWidth cellCounts seed
  have hrow : row ≠ [] := by
    simp [row, affineExactlyOneSeedCarrierRawInvocations,
      affineExactlyOneStructuredRowFrames, affineExactlyOnePrefixFrames,
      encodeAffineExactlyOneOutputSourceInvocationFamily,
      encodeAffineExactlyOneOutputSourceInvocation,
      encodeUnaryFrame, encodeUnaryFrameBlock, List.flatMap_append]
  have hlast : row.getLast hrow = .separator := by
    simp [row, affineExactlyOneSeedCarrierRawInvocations,
      affineExactlyOneStructuredRowFrames, affineExactlyOnePrefixFrames,
      encodeAffineExactlyOneOutputSourceInvocationFamily,
      encodeAffineExactlyOneOutputSourceInvocation,
      encodeUnaryFrame, encodeUnaryFrameBlock, List.flatMap_append]
  refine ⟨row.dropLast, ?_⟩
  change row = row.dropLast ++ [.separator]
  rw [← hlast, List.dropLast_append_getLast]

private theorem carrierNormalize_replicate_append_cons
    {alpha : Type} (value : alpha) (count : Nat) (tail : List alpha) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private def affineExactlyOneSeedCarrierNormalize_scan_run
    (row tail output work₁ : List UnaryFrameSym)
    (buffer₁ : Option UnaryFrameSym)
    (hrow : ∀ symbol ∈ row, symbol ≠ UnaryFrameSym.frameEnd) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .scan buffer₁ none false
        (row ++ .frameEnd :: tail) output work₁ [] [] [] [])
      (some (affineExactlyOneSeedCarrierNormalizeCfg .expectFinalZero
        (some .frameEnd) none false tail output
        (row.reverse ++ work₁) [] [] [] []))
      (2 * row.length + 1) := by
  induction row generalizing buffer₁ work₁ with
  | nil =>
      refine ⟨⟨1, ?_⟩, le_rfl⟩
      rfl
  | cons symbol rest ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hrow symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hrow item (by simp [hitem])
      let afterHead := affineExactlyOneSeedCarrierNormalizeCfg .scan
        (some symbol) none false (rest ++ .frameEnd :: tail) output
        (symbol :: work₁) [] [] [] []
      have hhead : EvalsToInTime
          (step affineExactlyOneSeedCarrierNormalizeRevProgram)
          (affineExactlyOneSeedCarrierNormalizeCfg .scan buffer₁ none false
            ((symbol :: rest) ++ .frameEnd :: tail) output work₁ [] [] [] [])
          (some afterHead) 2 := by
        cases symbol with
        | tick => exact ⟨⟨2, rfl⟩, le_rfl⟩
        | separator => exact ⟨⟨2, rfl⟩, le_rfl⟩
        | frameEnd => exact (hsymbol rfl).elim
      have htail := ih (work₁ := symbol :: work₁)
        (buffer₁ := some symbol) hrest
      let full := EvalsToInTime.trans
        (step affineExactlyOneSeedCarrierNormalizeRevProgram)
        2 (2 * rest.length + 1) _ afterHead _ hhead
        (by simpa [afterHead] using htail)
      convert full using 1 <;>
        simp [List.reverse_cons, List.append_assoc] <;> omega

private theorem carrierNormalize_loadStart_eval (value : Nat)
    (input output tail work₂ : List UnaryFrameSym)
    (buffer₁ : Option UnaryFrameSym)
    (height current rowBase : List Unit) :
    (flip Option.bind
      (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[2 * value + 1]
      (some (affineExactlyOneSeedCarrierNormalizeCfg .loadStart
        buffer₁ none false input output
        (List.replicate value .tick ++ .separator :: tail) work₂
        height current rowBase)) =
      some (affineExactlyOneSeedCarrierNormalizeCfg .loadHeight
        (some .separator) none false input output tail work₂
        height (List.replicate value () ++ current) rowBase) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[
            2 * value + 1]
          (some (affineExactlyOneSeedCarrierNormalizeCfg .loadStart
            (some .tick) none false input output
            (List.replicate value .tick ++ .separator :: tail) work₂
            height (() :: current) rowBase)) = _
      simpa only [List.replicate_succ,
        carrierNormalize_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: current)

private theorem carrierNormalize_loadHeight_eval (value : Nat)
    (input output tail work₂ : List UnaryFrameSym)
    (buffer₁ : Option UnaryFrameSym)
    (current start rowBase : List Unit) :
    (flip Option.bind
      (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[2 * value + 1]
      (some (affineExactlyOneSeedCarrierNormalizeCfg .loadHeight
        buffer₁ none false input output
        (List.replicate value .tick ++ .separator :: tail) work₂
        current start rowBase)) =
      some (affineExactlyOneSeedCarrierNormalizeCfg .expectBaseZero₁
        (some .separator) none false input output tail work₂
        (List.replicate value () ++ current) start rowBase) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[
            2 * value + 1]
          (some (affineExactlyOneSeedCarrierNormalizeCfg .loadHeight
            (some .tick) none false input output
            (List.replicate value .tick ++ .separator :: tail) work₂
            (() :: current) start rowBase)) = _
      simpa only [List.replicate_succ,
        carrierNormalize_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: current)

private theorem carrierNormalize_loadBase_eval (value : Nat)
    (input output tail work₂ : List UnaryFrameSym)
    (buffer₁ : Option UnaryFrameSym)
    (height start current : List Unit) :
    (flip Option.bind
      (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[2 * value + 1]
      (some (affineExactlyOneSeedCarrierNormalizeCfg .loadBase
        buffer₁ none false input output
        (List.replicate value .tick ++ .separator :: tail) work₂
        height start current)) =
      some (affineExactlyOneSeedCarrierNormalizeCfg .restoreRawSeparator
        (some .separator) none false input output tail work₂
        height start (List.replicate value () ++ current)) := by
  induction value generalizing buffer₁ current with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 1 = (2 * value + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[
            2 * value + 1]
          (some (affineExactlyOneSeedCarrierNormalizeCfg .loadBase
            (some .tick) none false input output
            (List.replicate value .tick ++ .separator :: tail) work₂
            height start (() :: current))) = _
      simpa only [List.replicate_succ,
        carrierNormalize_replicate_append_cons, List.cons_append] using
        ih (some .tick) (() :: current)

private def affineExactlyOneSeedCarrierNormalize_parse_run
    (rawHead input output : List UnaryFrameSym)
    (seed : AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .expectFinalZero
        (some .frameEnd) none false input output
        ((rawHead ++ [UnaryFrameSym.separator] ++
          encodeUnaryFrame [seed.rowBase, 0, 0] ++
          encodeUnaryFrame [seed.height, seed.start, 0]).reverse)
        [] [] [] [])
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitHeight
        (some .separator) none false input output
        (rawHead ++ [UnaryFrameSym.separator]).reverse []
        (List.replicate seed.height ())
        (List.replicate seed.start ())
        (List.replicate seed.rowBase ())))
      (2 * (seed.height + seed.start + seed.rowBase) + 8) := by
  let startTail :=
    List.replicate seed.height .tick ++
      .separator :: .separator :: .separator ::
        (List.replicate seed.rowBase .tick ++
          .separator :: rawHead.reverse)
  let beforeStart := affineExactlyOneSeedCarrierNormalizeCfg .loadStart
    (some .separator) none false input output
    (List.replicate seed.start .tick ++ .separator :: startTail)
    [] [] [] []
  have hprefix : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .expectFinalZero
        (some .frameEnd) none false input output
        ((rawHead ++ [UnaryFrameSym.separator] ++
          encodeUnaryFrame [seed.rowBase, 0, 0] ++
          encodeUnaryFrame [seed.height, seed.start, 0]).reverse)
        [] [] [] [])
      (some beforeStart) 2 := by
    have hrun : EvalsToInTime
        (step affineExactlyOneSeedCarrierNormalizeRevProgram)
        (affineExactlyOneSeedCarrierNormalizeCfg .expectFinalZero
          (some .frameEnd) none false input output
          (.separator :: .separator ::
            (List.replicate seed.start .tick ++ .separator :: startTail))
          [] [] [] [])
        (some beforeStart) 2 := by
      refine ⟨⟨2, ?_⟩, le_rfl⟩
      rfl
    simpa [beforeStart, startTail, encodeUnaryFrame, encodeUnaryFrameBlock,
      List.reverse_append, List.append_assoc] using hrun
  let beforeHeight := affineExactlyOneSeedCarrierNormalizeCfg .loadHeight
    (some .separator) none false input output
    (List.replicate seed.height .tick ++
      .separator :: .separator :: .separator ::
        (List.replicate seed.rowBase .tick ++
          .separator :: rawHead.reverse))
    [] [] (List.replicate seed.start ()) []
  have hstart : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      beforeStart (some beforeHeight) (2 * seed.start + 1) := by
    refine ⟨⟨2 * seed.start + 1, ?_⟩, le_rfl⟩
    simpa [beforeStart, beforeHeight, startTail] using
      carrierNormalize_loadStart_eval seed.start input output startTail []
        (some .separator) [] [] []
  let beforeZero₁ := affineExactlyOneSeedCarrierNormalizeCfg .expectBaseZero₁
    (some .separator) none false input output
    (.separator :: .separator ::
      (List.replicate seed.rowBase .tick ++
        .separator :: rawHead.reverse))
    [] (List.replicate seed.height ())
    (List.replicate seed.start ()) []
  have hheight : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      beforeHeight (some beforeZero₁) (2 * seed.height + 1) := by
    refine ⟨⟨2 * seed.height + 1, ?_⟩, le_rfl⟩
    simpa [beforeHeight, beforeZero₁] using
      carrierNormalize_loadHeight_eval seed.height input output
        (.separator :: .separator ::
          (List.replicate seed.rowBase .tick ++
            .separator :: rawHead.reverse)) []
        (some .separator) [] (List.replicate seed.start ()) []
  let beforeBase := affineExactlyOneSeedCarrierNormalizeCfg .loadBase
    (some .separator) none false input output
    (List.replicate seed.rowBase .tick ++
      .separator :: rawHead.reverse)
    [] (List.replicate seed.height ())
    (List.replicate seed.start ()) []
  have hzeros : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      beforeZero₁ (some beforeBase) 2 := by
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    rfl
  let beforeRestore := affineExactlyOneSeedCarrierNormalizeCfg
    .restoreRawSeparator (some .separator) none false input output
    rawHead.reverse [] (List.replicate seed.height ())
    (List.replicate seed.start ()) (List.replicate seed.rowBase ())
  have hbase : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      beforeBase (some beforeRestore) (2 * seed.rowBase + 1) := by
    refine ⟨⟨2 * seed.rowBase + 1, ?_⟩, le_rfl⟩
    simpa [beforeBase, beforeRestore] using
      carrierNormalize_loadBase_eval seed.rowBase input output
        rawHead.reverse [] (some .separator)
        (List.replicate seed.height ())
        (List.replicate seed.start ()) []
  have hrestore : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      beforeRestore
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitHeight
        (some .separator) none false input output
        (.separator :: rawHead.reverse) []
        (List.replicate seed.height ())
        (List.replicate seed.start ())
        (List.replicate seed.rowBase ()))) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) 2
      (2 * seed.start + 1) _ beforeStart _ hprefix hstart
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _
      (2 * seed.height + 1) _ beforeHeight _ h₁ hheight
  let h₃ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _ 2 _
      beforeZero₁ _ h₂ hzeros
  let h₄ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _
      (2 * seed.rowBase + 1) _ beforeBase _ h₃ hbase
  let full := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _ 1 _
      beforeRestore _ h₄ hrestore
  convert full using 1
  · simp [List.reverse_append]
  omega

private theorem carrierNormalize_emitHeight_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym)
    (input output work₁ work₂ : List UnaryFrameSym)
    (start rowBase : List Unit) :
    (flip Option.bind
      (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[2 * value + 2]
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitHeight
        buffer₁ none false input output work₁ work₂
        (List.replicate value ()) start rowBase)) =
      some (affineExactlyOneSeedCarrierNormalizeCfg .emitStart
        buffer₁ none false input
        ((encodeUnaryFrameBlock value).reverse ++ output) work₁ work₂
        [] start rowBase) := by
  induction value generalizing output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 = (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[
            2 * value + 2]
          (some (affineExactlyOneSeedCarrierNormalizeCfg .emitHeight
            buffer₁ none false input (.tick :: output) work₁ work₂
            (List.replicate value ()) start rowBase)) = _
      simpa [encodeUnaryFrameBlock, List.reverse_append,
        List.replicate_succ, carrierNormalize_replicate_append_cons,
        List.append_assoc] using ih (.tick :: output)

private theorem carrierNormalize_emitStart_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height rowBase : List Unit) :
    (flip Option.bind
      (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[2 * value + 2]
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitStart
        buffer₁ none false input output work₁ work₂
        height (List.replicate value ()) rowBase)) =
      some (affineExactlyOneSeedCarrierNormalizeCfg .emitBase
        buffer₁ none false input
        ((encodeUnaryFrameBlock value).reverse ++ output) work₁ work₂
        height [] rowBase) := by
  induction value generalizing output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 = (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[
            2 * value + 2]
          (some (affineExactlyOneSeedCarrierNormalizeCfg .emitStart
            buffer₁ none false input (.tick :: output) work₁ work₂
            height (List.replicate value ()) rowBase)) = _
      simpa [encodeUnaryFrameBlock, List.reverse_append,
        List.replicate_succ, carrierNormalize_replicate_append_cons,
        List.append_assoc] using ih (.tick :: output)

private theorem carrierNormalize_emitBase_eval (value : Nat)
    (buffer₁ : Option UnaryFrameSym)
    (input output work₁ work₂ : List UnaryFrameSym)
    (height start : List Unit) :
    (flip Option.bind
      (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[2 * value + 2]
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitBase
        buffer₁ none false input output work₁ work₂
        height start (List.replicate value ()))) =
      some (affineExactlyOneSeedCarrierNormalizeCfg .pushSeedEnd
        buffer₁ none false input
        ((encodeUnaryFrameBlock value).reverse ++ output) work₁ work₂
        height start []) := by
  induction value generalizing output with
  | zero => rfl
  | succ value ih =>
      rw [show 2 * (value + 1) + 2 = (2 * value + 2) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind
          (step affineExactlyOneSeedCarrierNormalizeRevProgram))^[
            2 * value + 2]
          (some (affineExactlyOneSeedCarrierNormalizeCfg .emitBase
            buffer₁ none false input (.tick :: output) work₁ work₂
            height start (List.replicate value ()))) = _
      simpa [encodeUnaryFrameBlock, List.reverse_append,
        List.replicate_succ, carrierNormalize_replicate_append_cons,
        List.append_assoc] using ih (.tick :: output)

private def affineExactlyOneSeedCarrierNormalize_emitSeed_run
    (raw input output : List UnaryFrameSym)
    (seed : AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .emitHeight
        (some .separator) none false input output raw.reverse []
        (List.replicate seed.height ())
        (List.replicate seed.start ())
        (List.replicate seed.rowBase ()))
      (some (affineExactlyOneSeedCarrierNormalizeCfg .reverseRaw
        (some .separator) none false input
        (.frameEnd ::
          (encodeAffineExactlyOneStructuredRowSeed seed).reverse ++ output)
        raw.reverse [] [] [] []))
      (2 * (seed.height + seed.start + seed.rowBase) + 7) := by
  let afterHeight := affineExactlyOneSeedCarrierNormalizeCfg .emitStart
    (some .separator) none false input
    ((encodeUnaryFrameBlock seed.height).reverse ++ output)
    raw.reverse [] [] (List.replicate seed.start ())
    (List.replicate seed.rowBase ())
  have hheight : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .emitHeight
        (some .separator) none false input output raw.reverse []
        (List.replicate seed.height ())
        (List.replicate seed.start ())
        (List.replicate seed.rowBase ()))
      (some afterHeight) (2 * seed.height + 2) := by
    refine ⟨⟨2 * seed.height + 2, ?_⟩, le_rfl⟩
    simpa [afterHeight] using carrierNormalize_emitHeight_eval seed.height
      (some .separator) input output raw.reverse []
      (List.replicate seed.start ()) (List.replicate seed.rowBase ())
  let afterStart := affineExactlyOneSeedCarrierNormalizeCfg .emitBase
    (some .separator) none false input
    ((encodeUnaryFrameBlock seed.start).reverse ++
      (encodeUnaryFrameBlock seed.height).reverse ++ output)
    raw.reverse [] [] [] (List.replicate seed.rowBase ())
  have hstart : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      afterHeight (some afterStart) (2 * seed.start + 2) := by
    refine ⟨⟨2 * seed.start + 2, ?_⟩, le_rfl⟩
    simpa [afterHeight, afterStart, List.append_assoc] using
      carrierNormalize_emitStart_eval seed.start (some .separator) input
        ((encodeUnaryFrameBlock seed.height).reverse ++ output)
        raw.reverse [] [] (List.replicate seed.rowBase ())
  let beforeEnd := affineExactlyOneSeedCarrierNormalizeCfg .pushSeedEnd
    (some .separator) none false input
    ((encodeUnaryFrameBlock seed.rowBase).reverse ++
      (encodeUnaryFrameBlock seed.start).reverse ++
      (encodeUnaryFrameBlock seed.height).reverse ++ output)
    raw.reverse [] [] [] []
  have hbase : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      afterStart (some beforeEnd) (2 * seed.rowBase + 2) := by
    refine ⟨⟨2 * seed.rowBase + 2, ?_⟩, le_rfl⟩
    simpa [afterStart, beforeEnd, List.append_assoc] using
      carrierNormalize_emitBase_eval seed.rowBase (some .separator) input
        ((encodeUnaryFrameBlock seed.start).reverse ++
          (encodeUnaryFrameBlock seed.height).reverse ++ output)
        raw.reverse [] [] []
  have hend : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      beforeEnd
      (some (affineExactlyOneSeedCarrierNormalizeCfg .reverseRaw
        (some .separator) none false input
        (.frameEnd ::
          (encodeUnaryFrameBlock seed.rowBase).reverse ++
            (encodeUnaryFrameBlock seed.start).reverse ++
            (encodeUnaryFrameBlock seed.height).reverse ++ output)
        raw.reverse [] [] [] [])) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    rfl
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram)
    (2 * seed.height + 2) (2 * seed.start + 2) _ afterHeight _
    hheight hstart
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _
    (2 * seed.rowBase + 2) _ afterStart _ h₁ hbase
  let full := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _ 1 _
    beforeEnd _ h₂ hend
  convert full using 1
  · simp [encodeAffineExactlyOneStructuredRowSeed, encodeUnaryFrame,
      List.reverse_append, List.append_assoc]
  omega

private def affineExactlyOneSeedCarrierNormalize_reverseRaw_run
    (raw current input output : List UnaryFrameSym)
    (buffer₁ : Option UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .reverseRaw
        buffer₁ none false input output raw current [] [] [])
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitRaw
        none none false input output [] (raw.reverse ++ current) [] [] []))
      (raw.length + 1) := by
  induction raw generalizing buffer₁ current with
  | nil =>
      refine ⟨⟨1, ?_⟩, le_rfl⟩
      rfl
  | cons symbol rest ih =>
      have hhead : EvalsToInTime
          (step affineExactlyOneSeedCarrierNormalizeRevProgram)
          (affineExactlyOneSeedCarrierNormalizeCfg .reverseRaw
            buffer₁ none false input output (symbol :: rest) current
            [] [] [])
          (some (affineExactlyOneSeedCarrierNormalizeCfg .reverseRaw
            (some symbol) none false input output rest (symbol :: current)
            [] [] [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
      have htail := ih (current := symbol :: current)
        (buffer₁ := some symbol)
      let full := EvalsToInTime.trans
        (step affineExactlyOneSeedCarrierNormalizeRevProgram)
        1 (rest.length + 1) _ _ _ hhead htail
      convert full using 1 <;>
        simp [List.reverse_cons, List.append_assoc]

private def affineExactlyOneSeedCarrierNormalize_emitRaw_run
    (raw input output : List UnaryFrameSym)
    (buffer₂ : Option UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .emitRaw
        none buffer₂ false input output [] raw [] [] [])
      (some (affineExactlyOneSeedCarrierNormalizeLoopCfg input
        (.frameEnd :: raw.reverse ++ output)))
      (2 * raw.length + 2) := by
  induction raw generalizing output buffer₂ with
  | nil =>
      refine ⟨⟨2, ?_⟩, le_rfl⟩
      rfl
  | cons symbol rest ih =>
      let afterHead := affineExactlyOneSeedCarrierNormalizeCfg .emitRaw
        none (some symbol) false input (symbol :: output) [] rest [] [] []
      have hhead : EvalsToInTime
          (step affineExactlyOneSeedCarrierNormalizeRevProgram)
          (affineExactlyOneSeedCarrierNormalizeCfg .emitRaw
            none buffer₂ false input output [] (symbol :: rest) [] [] [])
          (some afterHead) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
      have htail := ih (symbol :: output) (some symbol)
      let full := EvalsToInTime.trans
        (step affineExactlyOneSeedCarrierNormalizeRevProgram)
        2 (2 * rest.length + 2) _ afterHead _ hhead
        (by simpa [afterHead] using htail)
      convert full using 1 <;>
        simp [List.reverse_cons, List.append_assoc] <;> omega

/-- Exact productive cost of one normalized carrier row. -/
def affineExactlyOneSeedCarrierNormalizeOneSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) : Nat :=
  5 * (affineExactlyOneSeedCarrierRawInvocations
      labelWidth stateWidth cellCounts seed).length +
    6 * (seed.height + seed.start + seed.rowBase) + 31

private def affineExactlyOneSeedCarrierNormalize_one_run
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeLoopCfg
        (encodeAffineExactlyOneSeedCarrierOutputInvocation
          labelWidth stateWidth cellCounts seed ++ tail) output)
      (some (affineExactlyOneSeedCarrierNormalizeLoopCfg tail
        ((encodeAffineExactlyOneSeedCarrierNormalizedRow
          labelWidth stateWidth cellCounts seed).reverse ++ output)))
      (affineExactlyOneSeedCarrierNormalizeOneSteps
        labelWidth stateWidth cellCounts seed) := by
  let raw := affineExactlyOneSeedCarrierRawInvocations
    labelWidth stateWidth cellCounts seed
  let carrier := encodeUnaryFrame [seed.rowBase, 0, 0] ++
    encodeUnaryFrame [seed.height, seed.start, 0]
  have hrawNoEnd : ∀ symbol ∈ raw,
      symbol ≠ UnaryFrameSym.frameEnd := by
    intro symbol hsymbol
    exact carrierNormalize_raw_no_frameEnd _ symbol hsymbol
  have hcarrierNoEnd : ∀ symbol ∈ carrier,
      symbol ≠ UnaryFrameSym.frameEnd := by
    intro symbol hsymbol
    simp only [carrier, List.mem_append] at hsymbol
    exact hsymbol.elim
      (carrierNormalize_encodeUnaryFrame_no_frameEnd _ symbol)
      (carrierNormalize_encodeUnaryFrame_no_frameEnd _ symbol)
  have hprefixNoEnd : ∀ symbol ∈ raw ++ carrier,
      symbol ≠ UnaryFrameSym.frameEnd := by
    intro symbol hsymbol
    simp only [List.mem_append] at hsymbol
    exact hsymbol.elim (hrawNoEnd symbol) (hcarrierNoEnd symbol)
  have hscan : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeLoopCfg
        (encodeAffineExactlyOneSeedCarrierOutputInvocation
          labelWidth stateWidth cellCounts seed ++ tail) output)
      (some (affineExactlyOneSeedCarrierNormalizeCfg .expectFinalZero
        (some .frameEnd) none false tail output
        ((raw ++ carrier).reverse) [] [] [] []))
      (2 * (raw ++ carrier).length + 1) := by
    simpa [affineExactlyOneSeedCarrierNormalizeLoopCfg,
      encodeAffineExactlyOneSeedCarrierOutputInvocation_eq,
      raw, affineExactlyOneSeedCarrierRawInvocations, carrier,
      List.append_assoc] using
      affineExactlyOneSeedCarrierNormalize_scan_run
        (raw ++ carrier) tail output [] none hprefixNoEnd
  let rawHead := raw.dropLast
  have hrawNonempty : raw ≠ [] := by
    simp [raw, affineExactlyOneSeedCarrierRawInvocations,
      affineExactlyOneStructuredRowFrames, affineExactlyOnePrefixFrames,
      encodeAffineExactlyOneOutputSourceInvocationFamily,
      encodeAffineExactlyOneOutputSourceInvocation,
      encodeUnaryFrame, encodeUnaryFrameBlock, List.flatMap_append]
  have hrawLast : raw.getLast hrawNonempty = .separator := by
    simp [raw, affineExactlyOneSeedCarrierRawInvocations,
      affineExactlyOneStructuredRowFrames, affineExactlyOnePrefixFrames,
      encodeAffineExactlyOneOutputSourceInvocationFamily,
      encodeAffineExactlyOneOutputSourceInvocation,
      encodeUnaryFrame, encodeUnaryFrameBlock, List.flatMap_append]
  have hrawShape : raw = rawHead ++ [.separator] := by
    change raw = raw.dropLast ++ [.separator]
    rw [← hrawLast, List.dropLast_append_getLast]
  have hparse : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .expectFinalZero
        (some .frameEnd) none false tail output
        ((raw ++ carrier).reverse) [] [] [] [])
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitHeight
        (some .separator) none false tail output raw.reverse []
        (List.replicate seed.height ())
        (List.replicate seed.start ())
        (List.replicate seed.rowBase ())))
      (2 * (seed.height + seed.start + seed.rowBase) + 8) := by
    simpa [raw, carrier, hrawShape, List.append_assoc] using
      affineExactlyOneSeedCarrierNormalize_parse_run
        rawHead tail output seed
  have hemit := affineExactlyOneSeedCarrierNormalize_emitSeed_run
    raw tail output seed
  let seedOutput := .frameEnd ::
    (encodeAffineExactlyOneStructuredRowSeed seed).reverse ++ output
  have hreverse : EvalsToInTime
      (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeCfg .reverseRaw
        (some .separator) none false tail seedOutput raw.reverse [] [] [] [])
      (some (affineExactlyOneSeedCarrierNormalizeCfg .emitRaw
        none none false tail seedOutput [] raw [] [] []))
      (raw.length + 1) := by
    simpa [seedOutput] using
      affineExactlyOneSeedCarrierNormalize_reverseRaw_run
        raw.reverse [] tail seedOutput (some .separator)
  have hemitRaw := affineExactlyOneSeedCarrierNormalize_emitRaw_run
    raw tail seedOutput none
  let h₁ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram)
    (2 * (raw ++ carrier).length + 1)
    (2 * (seed.height + seed.start + seed.rowBase) + 8)
    _ _ _ hscan hparse
  let h₂ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _
    (2 * (seed.height + seed.start + seed.rowBase) + 7)
    _ _ _ h₁ hemit
  let h₃ := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _
    (raw.length + 1) _ _ _ h₂ hreverse
  let full := EvalsToInTime.trans
    (step affineExactlyOneSeedCarrierNormalizeRevProgram) _
    (2 * raw.length + 2) _ _ _ h₃ hemitRaw
  convert full using 1
  · simp [encodeAffineExactlyOneSeedCarrierNormalizedRow, raw, seedOutput,
      List.reverse_append, List.append_assoc]
  · simp [affineExactlyOneSeedCarrierNormalizeOneSteps, raw, carrier,
      encodeUnaryFrame_length]
    omega

/-- Exact cost for normalizing a complete carrier family, including the two
final empty-input halt steps. -/
def affineExactlyOneSeedCarrierNormalizeRevSteps
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    List AffineExactlyOneStructuredRowSeed → Nat
  | [] => 2
  | seed :: rest =>
      affineExactlyOneSeedCarrierNormalizeOneSteps
          labelWidth stateWidth cellCounts seed +
        affineExactlyOneSeedCarrierNormalizeRevSteps
          labelWidth stateWidth cellCounts rest

private def affineExactlyOneSeedCarrierNormalize_rows_runFrom
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (affineExactlyOneSeedCarrierNormalizeLoopCfg
        (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts seeds) output)
      (some (affineExactlyOneSeedCarrierNormalizeHaltCfg
        ((encodeAffineExactlyOneSeedCarrierNormalizedFamily
          labelWidth stateWidth cellCounts seeds).reverse ++ output)))
      (affineExactlyOneSeedCarrierNormalizeRevSteps
        labelWidth stateWidth cellCounts seeds) := by
  induction seeds generalizing output with
  | nil =>
      refine ⟨⟨2, ?_⟩, le_rfl⟩
      rfl
  | cons seed rest ih =>
      let rowOutput :=
        (encodeAffineExactlyOneSeedCarrierNormalizedRow
          labelWidth stateWidth cellCounts seed).reverse ++ output
      have hfirst := affineExactlyOneSeedCarrierNormalize_one_run
        labelWidth stateWidth cellCounts seed
        (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts rest) output
      have hrest := ih rowOutput
      let full := EvalsToInTime.trans
        (step affineExactlyOneSeedCarrierNormalizeRevProgram)
        (affineExactlyOneSeedCarrierNormalizeOneSteps
          labelWidth stateWidth cellCounts seed)
        (affineExactlyOneSeedCarrierNormalizeRevSteps
          labelWidth stateWidth cellCounts rest)
        _ (affineExactlyOneSeedCarrierNormalizeLoopCfg
          (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
            labelWidth stateWidth cellCounts rest) rowOutput)
        _ hfirst hrest
      convert full using 1
      · simp [encodeAffineExactlyOneSeedCarrierOutputInvocationFamily]
      · simp [encodeAffineExactlyOneSeedCarrierNormalizedFamily,
          rowOutput, List.reverse_append, List.append_assoc]
      · simp [affineExactlyOneSeedCarrierNormalizeRevSteps]
        omega

/-- Exact run of the fixed reverse-output normalizer. -/
def affineExactlyOneSeedCarrierNormalizeRev_run
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    EvalsToInTime (step affineExactlyOneSeedCarrierNormalizeRevProgram)
      (initialCfg affineExactlyOneSeedCarrierNormalizeRevProgram
        (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts seeds))
      (some (haltCfg affineExactlyOneSeedCarrierNormalizeRevProgram
        (encodeAffineExactlyOneSeedCarrierNormalizedFamily
          labelWidth stateWidth cellCounts seeds).reverse))
      (affineExactlyOneSeedCarrierNormalizeRevSteps
        labelWidth stateWidth cellCounts seeds) := by
  have hinit : affineExactlyOneSeedCarrierNormalizeLoopCfg
      (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
        labelWidth stateWidth cellCounts seeds) [] =
      initialCfg affineExactlyOneSeedCarrierNormalizeRevProgram
        (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
          labelWidth stateWidth cellCounts seeds) := rfl
  have hhalt : affineExactlyOneSeedCarrierNormalizeHaltCfg
      (encodeAffineExactlyOneSeedCarrierNormalizedFamily
        labelWidth stateWidth cellCounts seeds).reverse =
      haltCfg affineExactlyOneSeedCarrierNormalizeRevProgram
        (encodeAffineExactlyOneSeedCarrierNormalizedFamily
          labelWidth stateWidth cellCounts seeds).reverse := rfl
  rw [← hinit, ← hhalt]
  simpa only [List.append_nil] using
    affineExactlyOneSeedCarrierNormalize_rows_runFrom
      labelWidth stateWidth cellCounts seeds []

/-- One normalized row costs at most six steps per input symbol. -/
theorem affineExactlyOneSeedCarrierNormalizeOneSteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seed : AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneSeedCarrierNormalizeOneSteps
        labelWidth stateWidth cellCounts seed ≤
      6 * (encodeAffineExactlyOneSeedCarrierOutputInvocation
        labelWidth stateWidth cellCounts seed).length := by
  rw [encodeAffineExactlyOneSeedCarrierOutputInvocation_eq]
  simp [affineExactlyOneSeedCarrierNormalizeOneSteps,
    affineExactlyOneSeedCarrierRawInvocations, encodeUnaryFrame_length]
  omega

/-- The exact family runtime is linear in the concrete carrier stream. -/
theorem affineExactlyOneSeedCarrierNormalizeRevSteps_le
    (labelWidth stateWidth : Nat) (cellCounts : List Nat)
    (seeds : List AffineExactlyOneStructuredRowSeed) :
    affineExactlyOneSeedCarrierNormalizeRevSteps
        labelWidth stateWidth cellCounts seeds ≤
      6 * (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
        labelWidth stateWidth cellCounts seeds).length + 2 := by
  induction seeds with
  | nil =>
      simp [affineExactlyOneSeedCarrierNormalizeRevSteps,
        encodeAffineExactlyOneSeedCarrierOutputInvocationFamily]
  | cons seed rest ih =>
      have hseed := affineExactlyOneSeedCarrierNormalizeOneSteps_le
        labelWidth stateWidth cellCounts seed
      simp only [affineExactlyOneSeedCarrierNormalizeRevSteps,
        encodeAffineExactlyOneSeedCarrierOutputInvocationFamily,
        List.length_append]
      omega

/-- The compiled fixed controller computes the reverse of the normalized
seed-first stream in linear time. -/
noncomputable def
    affineExactlyOneSeedCarrierNormalizeRev_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
        labelWidth stateWidth cellCounts)
      id
      (fun seeds : List AffineExactlyOneStructuredRowSeed =>
        (encodeAffineExactlyOneSeedCarrierNormalizedFamily
          labelWidth stateWidth cellCounts seeds).reverse) where
  tm := compile affineExactlyOneSeedCarrierNormalizeRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.C 6 * Polynomial.X + 2
  outputsFun := fun seeds => by
    have builderRun := affineExactlyOneSeedCarrierNormalizeRev_run
      labelWidth stateWidth cellCounts seeds
    have compiledRun := compile_evalsToInTime
      affineExactlyOneSeedCarrierNormalizeRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneSeedCarrierNormalizeRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneSeedCarrierNormalizeRevProgram)
          (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneSeedCarrierNormalizeRevProgram)
          (encodeAffineExactlyOneSeedCarrierNormalizedFamily
            labelWidth stateWidth cellCounts seeds).reverse))
        (affineExactlyOneSeedCarrierNormalizeRevSteps
          labelWidth stateWidth cellCounts seeds) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime : affineExactlyOneSeedCarrierNormalizeRevSteps
          labelWidth stateWidth cellCounts seeds ≤
        (Polynomial.C 6 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat] using
        affineExactlyOneSeedCarrierNormalizeRevSteps_le
          labelWidth stateWidth cellCounts seeds
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile affineExactlyOneSeedCarrierNormalizeRevProgram).step
        (_root_.Turing.initList
          (compile affineExactlyOneSeedCarrierNormalizeRevProgram)
          (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds))
        (some (_root_.Turing.haltList
          (compile affineExactlyOneSeedCarrierNormalizeRevProgram)
          (encodeAffineExactlyOneSeedCarrierNormalizedFamily
            labelWidth stateWidth cellCounts seeds).reverse))
        ((Polynomial.C 6 * Polynomial.X + 2).eval
          (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
            labelWidth stateWidth cellCounts seeds).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the prepend-order result gives the canonical seed-first family.
This is the forward typed boundary consumed by later validity sources. -/
noncomputable def affineExactlyOneSeedCarrierNormalize_computableInPolyTime
    (labelWidth stateWidth : Nat) (cellCounts : List Nat) :
    _root_.Turing.TM2ComputableInPolyTime
      (encodeAffineExactlyOneSeedCarrierOutputInvocationFamily
        labelWidth stateWidth cellCounts)
      id
      (encodeAffineExactlyOneSeedCarrierNormalizedFamily
        labelWidth stateWidth cellCounts) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (affineExactlyOneSeedCarrierNormalizeRev_computableInPolyTime
        labelWidth stateWidth cellCounts)
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
