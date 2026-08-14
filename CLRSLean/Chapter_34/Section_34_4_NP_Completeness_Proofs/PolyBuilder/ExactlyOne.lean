import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Encoding
import Mathlib.Tactic

/-!
# Streaming a sequential exactly-one constraint

This file is the first concrete serializer used by the Cook--Levin validity
phase.  On a unary clock of length `n`, it emits the exact general-circuit
encoding of `exactlyOneGateTrace 0 [0, ..., n - 1]`.  The reversed builder is
counter based; a final verified reversal exposes the public gate order.

The zero bases are intentional at this layer.  Keeping this primitive small
isolates the counter-preserving unary encoder and the tail-first exactly-one
scan before the later affine-base wrapper supplies tableau-global wire and
gate offsets.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Exact forward encoding of the zero-based sequential exactly-one trace. -/
def sequentialExactlyOneGateStream (count : Nat) : List CircuitSym :=
  (exactlyOneGateTrace 0 (List.range count)).gates.flatMap encodeCircuitGate

/-- The public stream is definitionally the semantic exactly-one trace. -/
theorem sequentialExactlyOneGateStream_eq_trace (count : Nat) :
    sequentialExactlyOneGateStream count =
      (exactlyOneGateTrace 0 (List.range count)).gates.flatMap
        encodeCircuitGate := by
  rfl

/-! ## Counter program -/

/-- The three live unary registers used by the serializer. -/
inductive SequentialExactlyOneRegister
  | seen | next | wire
deriving DecidableEq, Fintype

/-- Finite return points of the counter-preserving unary encoder. -/
inductive SequentialExactlyOneCont
  | firstASeen | firstAWire | firstBDuplicate | firstBNext
  | firstCSeen | firstCWire
  | laterASeen | laterAWire | laterBDuplicate | laterBNext
  | laterCSeen | laterCWire
  | finalZeroDuplicate | finalSomeDuplicate | finalSeen | finalNext
  | boolEqNotLeft | boolEqNotRight
  | boolEqAndLeft | boolEqAndRight
  | boolEqAndStart | boolEqAndNext
  | boolEqOrStart | boolEqOrNext
deriving DecidableEq, Fintype

/-- Fixed finite-control phases of contextual Boolean equality. -/
inductive SequentialBoolEqLabel
  | notLeft | notRight | andLeft
  | clearLeft | clearRight
  | copyStart | copyPush | copyInc
  | restoreStart | restoreInc | incNext
  | andStart | incSeen₁ | incSeen₂ | incNext₁ | incNext₂
  | orStart
deriving DecidableEq, Fintype

/-- Finite control for the reversed sequential exactly-one serializer. -/
inductive SequentialExactlyOneLabel
  | scan | countWire | initNext₁ | initNext₂
  | pushFalse₁ | pushFalse₂ | nextFirst | nextLater
  | decFirstWire | decLaterWire | pushFirstAnd | pushLaterAnd
  | encode (register : SequentialExactlyOneRegister)
      (cont : SequentialExactlyOneCont)
  | save (register : SequentialExactlyOneRegister)
      (cont : SequentialExactlyOneCont)
  | pushArg (register : SequentialExactlyOneRegister)
      (cont : SequentialExactlyOneCont)
  | pushEnd (register : SequentialExactlyOneRegister)
      (cont : SequentialExactlyOneCont)
  | restore (register : SequentialExactlyOneRegister)
      (cont : SequentialExactlyOneCont)
  | restoreInc (register : SequentialExactlyOneRegister)
      (cont : SequentialExactlyOneCont)
  | resume (cont : SequentialExactlyOneCont)
  | incFirstDuplicate | restoreFirstDuplicate
  | decLaterDuplicate | restoreLaterDuplicate
  | clearSeen | copyNext | saveNext | incSeenFromNext
  | restoreNext | restoreNextInc
  | incSeen₁ | incSeen₂ | incNext₁ | incNext₂ | incNext₃
  | finalZero | finalSome | incFinalZeroDuplicate
  | decFinalSomeDuplicate | restoreFinalZeroDuplicate
  | restoreFinalSomeDuplicate | pushFinalAnd
  | boolEq (phase : SequentialBoolEqLabel)
  | clear₁ | clear₂ | clear₃ | halt | invalid
deriving DecidableEq, Fintype

private def encodeRegisterOp (register : SequentialExactlyOneRegister)
    (zero succ : SequentialExactlyOneLabel) :
    Op Unit CircuitSym SequentialExactlyOneLabel :=
  match register with
  | .seen => .dec₁ zero succ
  | .next => .dec₂ zero succ
  | .wire => .dec₃ zero succ

private def restoreRegisterOp (register : SequentialExactlyOneRegister)
    (next : SequentialExactlyOneLabel) :
    Op Unit CircuitSym SequentialExactlyOneLabel :=
  match register with
  | .seen => .inc₁ next
  | .next => .inc₂ next
  | .wire => .inc₃ next

/-- Concrete prepend-oriented counter program.  Register `seen` stores the
current scan's seen wire, `next` stores the next fresh gate index, and `wire`
walks the source range downward.  `work₂` is empty outside the unary encoder. -/
def sequentialExactlyOneRevProgram : Program Unit CircuitSym where
  Label := SequentialExactlyOneLabel
  main := .scan
  op
    | .scan => .moveInputWork₁ .initNext₁ (fun _ => .countWire)
    | .countWire => .inc₃ .scan
    | .initNext₁ => .inc₂ .initNext₂
    | .initNext₂ => .inc₂ .pushFalse₁
    | .pushFalse₁ => .pushOutput .constFalseMark .pushFalse₂
    | .pushFalse₂ => .pushOutput .constFalseMark .nextFirst
    | .nextFirst => .popWork₁ .finalZero (fun _ => .decFirstWire)
    | .nextLater => .popWork₁ .finalSome (fun _ => .decLaterWire)
    | .decFirstWire => .dec₃ .invalid .pushFirstAnd
    | .decLaterWire => .dec₃ .invalid .pushLaterAnd
    | .pushFirstAnd => .pushOutput .andMark (.encode .seen .firstASeen)
    | .pushLaterAnd => .pushOutput .andMark (.encode .seen .laterASeen)
    | .encode register cont =>
        encodeRegisterOp register (.pushEnd register cont) (.save register cont)
    | .save register cont => .pushWork₂ () (.pushArg register cont)
    | .pushArg register cont => .pushOutput .argMark (.encode register cont)
    | .pushEnd register cont => .pushOutput .endMark (.restore register cont)
    | .restore register cont =>
        .popWork₂ (.resume cont) (fun _ => .restoreInc register cont)
    | .restoreInc register cont =>
        restoreRegisterOp register (.restore register cont)
    | .resume .firstASeen => .jump (.encode .wire .firstAWire)
    | .resume .firstAWire => .pushOutput .orMark .incFirstDuplicate
    | .resume .firstBDuplicate =>
        .dec₁ .invalid (.encode .next .firstBNext)
    | .resume .firstBNext =>
        .pushOutput .orMark (.encode .seen .firstCSeen)
    | .resume .firstCSeen => .jump (.encode .wire .firstCWire)
    | .resume .firstCWire => .jump .clearSeen
    | .resume .laterASeen => .jump (.encode .wire .laterAWire)
    | .resume .laterAWire => .pushOutput .orMark .decLaterDuplicate
    | .resume .laterBDuplicate =>
        .inc₁ (.encode .next .laterBNext)
    | .resume .laterBNext =>
        .pushOutput .orMark (.encode .seen .laterCSeen)
    | .resume .laterCSeen => .jump (.encode .wire .laterCWire)
    | .resume .laterCWire => .jump .clearSeen
    | .resume .finalZeroDuplicate => .jump .restoreFinalZeroDuplicate
    | .resume .finalSomeDuplicate => .jump .restoreFinalSomeDuplicate
    | .resume .finalSeen => .jump (.encode .next .finalNext)
    | .resume .finalNext => .jump .clear₁
    | .resume .boolEqNotLeft => .jump (.boolEq .notRight)
    | .resume .boolEqNotRight => .jump (.boolEq .andLeft)
    | .resume .boolEqAndLeft => .jump (.encode .wire .boolEqAndRight)
    | .resume .boolEqAndRight => .jump (.boolEq .clearLeft)
    | .resume .boolEqAndStart => .jump (.encode .next .boolEqAndNext)
    | .resume .boolEqAndNext => .jump (.boolEq .incSeen₁)
    | .resume .boolEqOrStart => .jump (.encode .next .boolEqOrNext)
    | .resume .boolEqOrNext => .jump .clear₁
    | .incFirstDuplicate => .inc₁ (.encode .seen .firstBDuplicate)
    | .restoreFirstDuplicate => .jump .invalid
    | .decLaterDuplicate =>
        .dec₁ .invalid (.encode .seen .laterBDuplicate)
    | .restoreLaterDuplicate => .jump .invalid
    | .clearSeen => .dec₁ .copyNext .clearSeen
    | .copyNext => .dec₂ .restoreNext .saveNext
    | .saveNext => .pushWork₂ () .incSeenFromNext
    | .incSeenFromNext => .inc₁ .copyNext
    | .restoreNext => .popWork₂ .incSeen₁ (fun _ => .restoreNextInc)
    | .restoreNextInc => .inc₂ .restoreNext
    | .incSeen₁ => .inc₁ .incSeen₂
    | .incSeen₂ => .inc₁ .incNext₁
    | .incNext₁ => .inc₂ .incNext₂
    | .incNext₂ => .inc₂ .incNext₃
    | .incNext₃ => .inc₂ .nextLater
    | .finalZero => .pushOutput .notMark .incFinalZeroDuplicate
    | .finalSome => .pushOutput .notMark .decFinalSomeDuplicate
    | .incFinalZeroDuplicate =>
        .inc₁ (.encode .seen .finalZeroDuplicate)
    | .decFinalSomeDuplicate =>
        .dec₁ .invalid (.encode .seen .finalSomeDuplicate)
    | .restoreFinalZeroDuplicate => .dec₁ .invalid .pushFinalAnd
    | .restoreFinalSomeDuplicate => .inc₁ .pushFinalAnd
    | .pushFinalAnd => .pushOutput .andMark (.encode .seen .finalSeen)
    | .boolEq .notLeft =>
        .pushOutput .notMark (.encode .next .boolEqNotLeft)
    | .boolEq .notRight =>
        .pushOutput .notMark (.encode .wire .boolEqNotRight)
    | .boolEq .andLeft =>
        .pushOutput .andMark (.encode .next .boolEqAndLeft)
    | .boolEq .clearLeft =>
        .dec₂ (.boolEq .clearRight) (.boolEq .clearLeft)
    | .boolEq .clearRight =>
        .dec₃ (.boolEq .copyStart) (.boolEq .clearRight)
    | .boolEq .copyStart =>
        .dec₁ (.boolEq .restoreStart) (.boolEq .copyPush)
    | .boolEq .copyPush => .pushWork₁ () (.boolEq .copyInc)
    | .boolEq .copyInc => .inc₂ (.boolEq .copyStart)
    | .boolEq .restoreStart =>
        .popWork₁ (.boolEq .incNext) (fun _ => .boolEq .restoreInc)
    | .boolEq .restoreInc => .inc₁ (.boolEq .restoreStart)
    | .boolEq .incNext => .inc₂ (.boolEq .andStart)
    | .boolEq .andStart =>
        .pushOutput .andMark (.encode .seen .boolEqAndStart)
    | .boolEq .incSeen₁ => .inc₁ (.boolEq .incSeen₂)
    | .boolEq .incSeen₂ => .inc₁ (.boolEq .incNext₁)
    | .boolEq .incNext₁ => .inc₂ (.boolEq .incNext₂)
    | .boolEq .incNext₂ => .inc₂ (.boolEq .orStart)
    | .boolEq .orStart =>
        .pushOutput .orMark (.encode .seen .boolEqOrStart)
    | .clear₁ => .dec₁ .clear₂ .clear₁
    | .clear₂ => .dec₂ .clear₃ .clear₂
    | .clear₃ => .dec₃ .halt .clear₃
    | .halt => .halt
    | .invalid => .halt

/-! ## Exact counter-preserving unary emission -/

/-- Independent program configuration with explicit unary register contents.
This is the contextual entry surface used by larger serializer phases. -/
def sequentialExactlyOneCfg (label : SequentialExactlyOneLabel)
    (buffer₁ buffer₂ : Option Unit) (test : Bool)
    (input : List Unit) (output : List CircuitSym)
    (work₁ work₂ : List Unit) (seen next wire : List Unit) :
    BuilderCfg sequentialExactlyOneRevProgram where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := seen
  counter₂ := next
  counter₃ := wire

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem encodeSeen_consume_eval (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ saved next wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
      (some (sequentialExactlyOneCfg (.encode .seen cont)
        buffer₁ buffer₂ test input output work₁ saved
        (List.replicate count ()) next wire)) =
      some (sequentialExactlyOneCfg (.pushEnd .seen cont)
        buffer₁ buffer₂ false input
        (List.replicate count .argMark ++ output) work₁
        (List.replicate count () ++ saved) [] next wire) := by
  induction count generalizing test output saved with
  | zero => rfl
  | succ count ih =>
      rw [show 3 * (count + 1) + 1 = (3 * count + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
          (some (sequentialExactlyOneCfg (.encode .seen cont)
            buffer₁ buffer₂ true input (.argMark :: output) work₁
            (() :: saved) (List.replicate count ()) next wire)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using
        ih true (.argMark :: output) (() :: saved)

private theorem encodeSeen_restore_eval (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ restored next wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
      (some (sequentialExactlyOneCfg (.restore .seen cont)
        buffer₁ buffer₂ test input output work₁ (List.replicate count ())
        restored next wire)) =
      some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none test input output work₁ []
        (List.replicate count () ++ restored) next wire) := by
  induction count generalizing buffer₂ test restored with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
          (some (sequentialExactlyOneCfg (.restore .seen cont)
            buffer₁ (some ()) test input output work₁
            (List.replicate count ()) (() :: restored) next wire)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some ()) test (() :: restored)

/-- Emitting `encNat seen` preserves the live seen register and empties the
scratch stack in exactly `5*seen+3` builder steps. -/
def encodeSeen_run (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ next wire : List Unit) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.encode .seen cont)
        buffer₁ none test input output work₁ []
        (List.replicate count ()) next wire)
      (some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none false input
        ((encNat count).reverse ++ output) work₁ []
        (List.replicate count ()) next wire))
      (5 * count + 3) := by
  let afterConsume := sequentialExactlyOneCfg (.pushEnd .seen cont)
    buffer₁ none false input
    (List.replicate count .argMark ++ output) work₁
    (List.replicate count ()) [] next wire
  let afterEnd := sequentialExactlyOneCfg (.restore .seen cont)
    buffer₁ none false input
    (.endMark :: (List.replicate count .argMark ++ output)) work₁
    (List.replicate count ()) [] next wire
  have hconsume : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.encode .seen cont)
        buffer₁ none test input output work₁ []
        (List.replicate count ()) next wire)
      (some afterConsume) (3 * count + 1) := by
    exact ⟨⟨3 * count + 1, by
      simpa [afterConsume] using encodeSeen_consume_eval count cont
        buffer₁ none test input output work₁ [] next wire⟩, le_rfl⟩
  have hend : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterConsume (some afterEnd) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterEnd
      (some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none false input
        (.endMark :: (List.replicate count .argMark ++ output)) work₁ []
        (List.replicate count ()) next wire))
      (2 * count + 1) := by
    exact ⟨⟨2 * count + 1, by
      simpa [afterEnd] using encodeSeen_restore_eval count cont buffer₁ none
        false input (.endMark :: (List.replicate count .argMark ++ output))
        work₁ [] next wire⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (3 * count + 1) 1 _ afterConsume _ hconsume hend
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (3 * count + 1)) (2 * count + 1) _ afterEnd _ h₁ hrestore
  have hsteps : (2 * count + 1) + (1 + (3 * count + 1)) =
      5 * count + 3 := by omega
  rw [← hsteps]
  simpa [encNat, List.reverse_append, List.append_assoc] using full

private theorem encodeNext_consume_eval (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ saved seen wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
      (some (sequentialExactlyOneCfg (.encode .next cont)
        buffer₁ buffer₂ test input output work₁ saved seen
        (List.replicate count ()) wire)) =
      some (sequentialExactlyOneCfg (.pushEnd .next cont)
        buffer₁ buffer₂ false input
        (List.replicate count .argMark ++ output) work₁
        (List.replicate count () ++ saved) seen [] wire) := by
  induction count generalizing test output saved with
  | zero => rfl
  | succ count ih =>
      rw [show 3 * (count + 1) + 1 = (3 * count + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
          (some (sequentialExactlyOneCfg (.encode .next cont)
            buffer₁ buffer₂ true input (.argMark :: output) work₁
            (() :: saved) seen (List.replicate count ()) wire)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (.argMark :: output) (() :: saved)

private theorem encodeNext_restore_eval (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ restored seen wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
      (some (sequentialExactlyOneCfg (.restore .next cont)
        buffer₁ buffer₂ test input output work₁ (List.replicate count ())
        seen restored wire)) =
      some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none test input output work₁ [] seen
        (List.replicate count () ++ restored) wire) := by
  induction count generalizing buffer₂ test restored with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
          (some (sequentialExactlyOneCfg (.restore .next cont)
            buffer₁ (some ()) test input output work₁
            (List.replicate count ()) seen (() :: restored) wire)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some ()) test (() :: restored)

/-- Encode the `next` register in unary while restoring it exactly. -/
def encodeNext_run (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ seen wire : List Unit) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.encode .next cont)
        buffer₁ none test input output work₁ [] seen
        (List.replicate count ()) wire)
      (some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none false input
        ((encNat count).reverse ++ output) work₁ [] seen
        (List.replicate count ()) wire))
      (5 * count + 3) := by
  let afterConsume := sequentialExactlyOneCfg (.pushEnd .next cont)
    buffer₁ none false input
    (List.replicate count .argMark ++ output) work₁
    (List.replicate count ()) seen [] wire
  let afterEnd := sequentialExactlyOneCfg (.restore .next cont)
    buffer₁ none false input
    (.endMark :: (List.replicate count .argMark ++ output)) work₁
    (List.replicate count ()) seen [] wire
  have hconsume : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.encode .next cont)
        buffer₁ none test input output work₁ [] seen
        (List.replicate count ()) wire)
      (some afterConsume) (3 * count + 1) := by
    exact ⟨⟨3 * count + 1, by
      simpa [afterConsume] using encodeNext_consume_eval count cont
        buffer₁ none test input output work₁ [] seen wire⟩, le_rfl⟩
  have hend : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterConsume (some afterEnd) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterEnd
      (some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none false input
        (.endMark :: (List.replicate count .argMark ++ output)) work₁ []
        seen (List.replicate count ()) wire))
      (2 * count + 1) := by
    exact ⟨⟨2 * count + 1, by
      simpa [afterEnd] using encodeNext_restore_eval count cont buffer₁ none
        false input (.endMark :: (List.replicate count .argMark ++ output))
        work₁ [] seen wire⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (3 * count + 1) 1 _ afterConsume _ hconsume hend
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (3 * count + 1)) (2 * count + 1) _ afterEnd _ h₁ hrestore
  have hsteps : (2 * count + 1) + (1 + (3 * count + 1)) =
      5 * count + 3 := by omega
  rw [← hsteps]
  simpa [encNat, List.reverse_append, List.append_assoc] using full

private theorem encodeWire_consume_eval (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ saved seen next : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
      (some (sequentialExactlyOneCfg (.encode .wire cont)
        buffer₁ buffer₂ test input output work₁ saved seen next
        (List.replicate count ()))) =
      some (sequentialExactlyOneCfg (.pushEnd .wire cont)
        buffer₁ buffer₂ false input
        (List.replicate count .argMark ++ output) work₁
        (List.replicate count () ++ saved) seen next []) := by
  induction count generalizing test output saved with
  | zero => rfl
  | succ count ih =>
      rw [show 3 * (count + 1) + 1 = (3 * count + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
          (some (sequentialExactlyOneCfg (.encode .wire cont)
            buffer₁ buffer₂ true input (.argMark :: output) work₁
            (() :: saved) seen next (List.replicate count ()))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (.argMark :: output) (() :: saved)

private theorem encodeWire_restore_eval (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ restored seen next : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
      (some (sequentialExactlyOneCfg (.restore .wire cont)
        buffer₁ buffer₂ test input output work₁ (List.replicate count ())
        seen next restored)) =
      some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none test input output work₁ [] seen next
        (List.replicate count () ++ restored)) := by
  induction count generalizing buffer₂ test restored with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
          (some (sequentialExactlyOneCfg (.restore .wire cont)
            buffer₁ (some ()) test input output work₁
            (List.replicate count ()) seen next (() :: restored))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some ()) test (() :: restored)

/-- Encode the `wire` register in unary while restoring it exactly. -/
def encodeWire_run (count : Nat)
    (cont : SequentialExactlyOneCont) (buffer₁ : Option Unit)
    (test : Bool) (input : List Unit) (output : List CircuitSym)
    (work₁ seen next : List Unit) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.encode .wire cont)
        buffer₁ none test input output work₁ [] seen next
        (List.replicate count ()))
      (some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none false input
        ((encNat count).reverse ++ output) work₁ [] seen next
        (List.replicate count ())))
      (5 * count + 3) := by
  let afterConsume := sequentialExactlyOneCfg (.pushEnd .wire cont)
    buffer₁ none false input
    (List.replicate count .argMark ++ output) work₁
    (List.replicate count ()) seen next []
  let afterEnd := sequentialExactlyOneCfg (.restore .wire cont)
    buffer₁ none false input
    (.endMark :: (List.replicate count .argMark ++ output)) work₁
    (List.replicate count ()) seen next []
  have hconsume : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.encode .wire cont)
        buffer₁ none test input output work₁ [] seen next
        (List.replicate count ()))
      (some afterConsume) (3 * count + 1) := by
    exact ⟨⟨3 * count + 1, by
      simpa [afterConsume] using encodeWire_consume_eval count cont
        buffer₁ none test input output work₁ [] seen next⟩, le_rfl⟩
  have hend : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterConsume (some afterEnd) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterEnd
      (some (sequentialExactlyOneCfg (.resume cont)
        buffer₁ none false input
        (.endMark :: (List.replicate count .argMark ++ output)) work₁ []
        seen next (List.replicate count ())))
      (2 * count + 1) := by
    exact ⟨⟨2 * count + 1, by
      simpa [afterEnd] using encodeWire_restore_eval count cont buffer₁ none
        false input (.endMark :: (List.replicate count .argMark ++ output))
        work₁ [] seen next⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (3 * count + 1) 1 _ afterConsume _ hconsume hend
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (3 * count + 1)) (2 * count + 1) _ afterEnd _ h₁ hrestore
  have hsteps : (2 * count + 1) + (1 + (3 * count + 1)) =
      5 * count + 3 := by omega
  rw [← hsteps]
  simpa [encNat, List.reverse_append, List.append_assoc] using full

/-! ## One three-gate scan block -/

private def sequentialExactlyOneFirstChunk (wire : Nat) : List CircuitGate :=
  [.and 0 wire, .or 1 2, .or 0 wire]

private def sequentialExactlyOneLaterChunk (phase wire : Nat) :
    List CircuitGate :=
  [.and (3 * phase + 1) wire,
    .or (3 * phase) (3 * phase + 2),
    .or (3 * phase + 1) wire]

private def sequentialExactlyOneSeen (phase : Nat) : Nat :=
  if phase = 0 then 0 else 3 * phase + 1

private def sequentialExactlyOneDuplicate (phase : Nat) : Nat :=
  if phase = 0 then 1 else 3 * phase

private def sequentialExactlyOneChunk (phase wire : Nat) : List CircuitGate :=
  if phase = 0 then sequentialExactlyOneFirstChunk wire
  else sequentialExactlyOneLaterChunk phase wire

private def sequentialExactlyOneChunksFrom : Nat → Nat → List CircuitGate
  | _, 0 => []
  | phase, remaining + 1 =>
      sequentialExactlyOneChunk phase remaining ++
        sequentialExactlyOneChunksFrom (phase + 1) remaining

private theorem arithmeticScanFrom_range (phase remaining : Nat)
    (scan : ExactlyOneArithmeticScan)
    (hgates : scan.gates.length = 3 * phase + 2)
    (hseen : scan.seen = sequentialExactlyOneSeen phase)
    (hduplicate : scan.duplicate = sequentialExactlyOneDuplicate phase) :
    let result := (List.range remaining).reverse.foldl
      (exactlyOneArithmeticStep 0) scan
    result.gates = scan.gates ++
        sequentialExactlyOneChunksFrom phase remaining ∧
      result.gates.length = 3 * (phase + remaining) + 2 ∧
      result.seen = sequentialExactlyOneSeen (phase + remaining) ∧
      result.duplicate =
        sequentialExactlyOneDuplicate (phase + remaining) := by
  induction remaining generalizing phase scan with
  | zero =>
      simp [sequentialExactlyOneChunksFrom, hgates, hseen, hduplicate]
  | succ remaining ih =>
      have hrange : (List.range (remaining + 1)).reverse =
          remaining :: (List.range remaining).reverse := by
        simp [List.range_succ, List.reverse_append]
      rw [hrange]
      simp only [List.foldl]
      let nextScan := exactlyOneArithmeticStep 0 scan remaining
      have hnextGates : nextScan.gates = scan.gates ++
          sequentialExactlyOneChunk phase remaining := by
        unfold nextScan exactlyOneArithmeticStep sequentialExactlyOneChunk
        rw [hgates, hseen, hduplicate]
        by_cases hphase : phase = 0
        · subst phase
          rfl
        · simp only [hphase, ↓reduceIte, sequentialExactlyOneLaterChunk,
            sequentialExactlyOneSeen, sequentialExactlyOneDuplicate]
          simp
      have hnextLength : nextScan.gates.length =
          3 * (phase + 1) + 2 := by
        rw [hnextGates, List.length_append]
        unfold sequentialExactlyOneChunk
        by_cases hphase : phase = 0
        · subst phase
          have hg : scan.gates.length = 2 := by omega
          simp [sequentialExactlyOneFirstChunk, hg]
        · simp [hphase, sequentialExactlyOneLaterChunk, hgates]
          omega
      have hnextSeen : nextScan.seen =
          sequentialExactlyOneSeen (phase + 1) := by
        unfold nextScan exactlyOneArithmeticStep sequentialExactlyOneSeen
        rw [hgates]
        rw [if_neg (by omega : phase + 1 ≠ 0)]
        simp [Nat.mul_add]
      have hnextDuplicate : nextScan.duplicate =
          sequentialExactlyOneDuplicate (phase + 1) := by
        unfold nextScan exactlyOneArithmeticStep
          sequentialExactlyOneDuplicate
        rw [hgates]
        rw [if_neg (by omega : phase + 1 ≠ 0)]
        simp [Nat.mul_add]
      rcases ih (phase + 1) nextScan hnextLength hnextSeen hnextDuplicate with
        ⟨hresultGates, hresultLength, hresultSeen, hresultDuplicate⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hresultGates, hnextGates]
        simp [sequentialExactlyOneChunksFrom, List.append_assoc]
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hresultLength
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hresultSeen
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          hresultDuplicate

private theorem arithmeticScan_range (count : Nat) :
    let scan := exactlyOneArithmeticScan 0 (List.range count)
    scan.gates = [.const false, .const false] ++
        sequentialExactlyOneChunksFrom 0 count ∧
      scan.gates.length = 3 * count + 2 ∧
      scan.seen = sequentialExactlyOneSeen count ∧
      scan.duplicate = sequentialExactlyOneDuplicate count := by
  simpa [exactlyOneArithmeticScan, sequentialExactlyOneSeen,
    sequentialExactlyOneDuplicate] using
    arithmeticScanFrom_range 0 count
      ({ gates := [.const false, .const false], seen := 0, duplicate := 1 } :
        ExactlyOneArithmeticScan) rfl rfl rfl

private def sequentialExactlyOneGateList (count : Nat) : List CircuitGate :=
  [.const false, .const false] ++ sequentialExactlyOneChunksFrom 0 count ++
    [.not (sequentialExactlyOneDuplicate count),
      .and (sequentialExactlyOneSeen count) (3 * count + 2)]

private theorem sequentialExactlyOneGateList_eq_trace (count : Nat) :
    sequentialExactlyOneGateList count =
      (exactlyOneGateTrace 0 (List.range count)).gates := by
  rw [exactlyOneGateTrace_gates_eq_arithmeticScan]
  rcases arithmeticScan_range count with
    ⟨hgates, hlength, hseen, hduplicate⟩
  simp only [sequentialExactlyOneGateList]
  simp only [Nat.zero_add]
  rw [hduplicate, hseen, hlength, hgates]

private def firstGatePhase (wire : Nat) (buffer₁ : Option Unit)
    (work₁ : List Unit) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .pushFirstAnd buffer₁ none true [] output
        work₁ [] [] (List.replicate 2 ()) (List.replicate wire ()))
      (some (sequentialExactlyOneCfg .clearSeen buffer₁ none false []
        (((sequentialExactlyOneFirstChunk wire).flatMap
          encodeCircuitGate).reverse ++ output)
        work₁ [] [] (List.replicate 2 ()) (List.replicate wire ())))
      (10 * wire + 41) := by
  let c₀ := sequentialExactlyOneCfg (.encode .seen .firstASeen)
    buffer₁ none true [] (.andMark :: output) work₁ [] []
    (List.replicate 2 ()) (List.replicate wire ())
  have hpushA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .pushFirstAnd buffer₁ none true [] output
        work₁ [] [] (List.replicate 2 ()) (List.replicate wire ()))
      (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.resume .firstASeen)
    buffer₁ none false [] ((encNat 0).reverse ++ .andMark :: output)
    work₁ [] [] (List.replicate 2 ()) (List.replicate wire ())
  have hseenA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) 3 := by
    simpa [c₀, c₁] using
      encodeSeen_run 0 .firstASeen buffer₁ true [] (.andMark :: output)
        work₁ (List.replicate 2 ()) (List.replicate wire ())
  let c₂ := sequentialExactlyOneCfg (.encode .wire .firstAWire)
    buffer₁ none false [] ((encNat 0).reverse ++ .andMark :: output)
    work₁ [] [] (List.replicate 2 ()) (List.replicate wire ())
  have hjumpWireA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let outA := (encodeCircuitGate (.and 0 wire)).reverse ++ output
  let c₃ := sequentialExactlyOneCfg (.resume .firstAWire)
    buffer₁ none false [] outA work₁ [] []
    (List.replicate 2 ()) (List.replicate wire ())
  have hwireA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) (5 * wire + 3) := by
    simpa [c₂, c₃, outA, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run wire .firstAWire buffer₁ false []
        ((encNat 0).reverse ++ .andMark :: output) work₁ []
        (List.replicate 2 ())
  let c₄ := sequentialExactlyOneCfg .incFirstDuplicate
    buffer₁ none false [] (.orMark :: outA) work₁ [] []
    (List.replicate 2 ()) (List.replicate wire ())
  have hpushB : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₅ := sequentialExactlyOneCfg (.encode .seen .firstBDuplicate)
    buffer₁ none false [] (.orMark :: outA) work₁ [] [()]
    (List.replicate 2 ()) (List.replicate wire ())
  have hincDuplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₆ := sequentialExactlyOneCfg (.resume .firstBDuplicate)
    buffer₁ none false [] ((encNat 1).reverse ++ .orMark :: outA)
    work₁ [] [()] (List.replicate 2 ()) (List.replicate wire ())
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) 8 := by
    simpa [c₅, c₆] using
      encodeSeen_run 1 .firstBDuplicate buffer₁ false [] (.orMark :: outA)
        work₁ (List.replicate 2 ()) (List.replicate wire ())
  let c₇ := sequentialExactlyOneCfg (.encode .next .firstBNext)
    buffer₁ none true [] ((encNat 1).reverse ++ .orMark :: outA)
    work₁ [] [] (List.replicate 2 ()) (List.replicate wire ())
  have hrestoreDuplicate : EvalsToInTime
      (step sequentialExactlyOneRevProgram) c₆ (some c₇) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let outB := (encodeCircuitGate (.or 1 2)).reverse ++ outA
  let c₈ := sequentialExactlyOneCfg (.resume .firstBNext)
    buffer₁ none false [] outB work₁ [] []
    (List.replicate 2 ()) (List.replicate wire ())
  have hnextB : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) 13 := by
    simpa [c₇, c₈, outB, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run 2 .firstBNext buffer₁ true []
        ((encNat 1).reverse ++ .orMark :: outA) work₁ []
        (List.replicate wire ())
  let c₉ := sequentialExactlyOneCfg (.encode .seen .firstCSeen)
    buffer₁ none false [] (.orMark :: outB) work₁ [] []
    (List.replicate 2 ()) (List.replicate wire ())
  have hpushC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some c₉) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁₀ := sequentialExactlyOneCfg (.resume .firstCSeen)
    buffer₁ none false [] ((encNat 0).reverse ++ .orMark :: outB)
    work₁ [] [] (List.replicate 2 ()) (List.replicate wire ())
  have hseenC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₉ (some c₁₀) 3 := by
    simpa [c₉, c₁₀] using
      encodeSeen_run 0 .firstCSeen buffer₁ false [] (.orMark :: outB)
        work₁ (List.replicate 2 ()) (List.replicate wire ())
  let c₁₁ := sequentialExactlyOneCfg (.encode .wire .firstCWire)
    buffer₁ none false [] ((encNat 0).reverse ++ .orMark :: outB)
    work₁ [] [] (List.replicate 2 ()) (List.replicate wire ())
  have hjumpWireC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₀ (some c₁₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let outC := (encodeCircuitGate (.or 0 wire)).reverse ++ outB
  let c₁₂ := sequentialExactlyOneCfg (.resume .firstCWire)
    buffer₁ none false [] outC work₁ [] []
    (List.replicate 2 ()) (List.replicate wire ())
  have hwireC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₁ (some c₁₂) (5 * wire + 3) := by
    simpa [c₁₁, c₁₂, outC, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run wire .firstCWire buffer₁ false []
        ((encNat 0).reverse ++ .orMark :: outB) work₁ []
        (List.replicate 2 ())
  let finalCfg := sequentialExactlyOneCfg .clearSeen
    buffer₁ none false [] outC work₁ [] []
    (List.replicate 2 ()) (List.replicate wire ())
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₂ (some finalCfg) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 3 _ c₀ _ hpushA hseenA
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    4 1 _ c₁ _ h₁ hjumpWireA
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    5 (5 * wire + 3) _ c₂ _ h₂ hwireA
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * wire + 3) + 5) 1 _ c₃ _ h₃ hpushB
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * wire + 3) + 5)) 1 _ c₄ _ h₄ hincDuplicate
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (1 + ((5 * wire + 3) + 5))) 8 _ c₅ _ h₅ hduplicate
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (8 + (1 + (1 + ((5 * wire + 3) + 5)))) 1 _ c₆ _ h₆
      hrestoreDuplicate
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (8 + (1 + (1 + ((5 * wire + 3) + 5))))) 13 _ c₇ _ h₇ hnextB
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (13 + (1 + (8 + (1 + (1 + ((5 * wire + 3) + 5)))))) 1
    _ c₈ _ h₈ hpushC
  let h₁₀ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (13 + (1 + (8 + (1 + (1 + ((5 * wire + 3) + 5))))))) 3
    _ c₉ _ h₉ hseenC
  let h₁₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (3 + (1 + (13 + (1 + (8 + (1 + (1 +
      ((5 * wire + 3) + 5)))))))) 1 _ c₁₀ _ h₁₀ hjumpWireC
  let h₁₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (3 + (1 + (13 + (1 + (8 + (1 + (1 +
      ((5 * wire + 3) + 5))))))))) (5 * wire + 3)
    _ c₁₁ _ h₁₁ hwireC
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * wire + 3) + (1 + (3 + (1 + (13 + (1 + (8 + (1 + (1 +
      ((5 * wire + 3) + 5)))))))))) 1 _ c₁₂ _ h₁₂ hjumpClear
  have hsteps : 1 + ((5 * wire + 3) + (1 + (3 + (1 +
      (13 + (1 + (8 + (1 + (1 + ((5 * wire + 3) + 5)))))))))) =
      10 * wire + 41 := by omega
  rw [← hsteps]
  simpa [finalCfg, outC, outB, outA, sequentialExactlyOneFirstChunk,
    List.reverse_append, List.append_assoc] using full

private def laterGatePhase (phase wire : Nat) (buffer₁ : Option Unit)
    (work₁ : List Unit) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .pushLaterAnd buffer₁ none true [] output
        work₁ [] (List.replicate (3 * phase + 1) ())
        (List.replicate (3 * phase + 2) ()) (List.replicate wire ()))
      (some (sequentialExactlyOneCfg .clearSeen buffer₁ none false []
        (((sequentialExactlyOneLaterChunk phase wire).flatMap
          encodeCircuitGate).reverse ++ output)
        work₁ [] (List.replicate (3 * phase + 1) ())
        (List.replicate (3 * phase + 2) ()) (List.replicate wire ())))
      (60 * phase + 10 * wire + 46) := by
  let seen := 3 * phase + 1
  let next := 3 * phase + 2
  have hseenPos : 0 < seen := by simp [seen]
  let c₀ := sequentialExactlyOneCfg (.encode .seen .laterASeen)
    buffer₁ none true [] (.andMark :: output) work₁ []
    (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hpushA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .pushLaterAnd buffer₁ none true [] output
        work₁ [] (List.replicate seen ()) (List.replicate next ())
        (List.replicate wire ()))
      (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.resume .laterASeen)
    buffer₁ none false [] ((encNat seen).reverse ++ .andMark :: output)
    work₁ [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hseenA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) (5 * seen + 3) := by
    simpa [c₀, c₁] using
      encodeSeen_run seen .laterASeen buffer₁ true [] (.andMark :: output)
        work₁ (List.replicate next ()) (List.replicate wire ())
  let c₂ := sequentialExactlyOneCfg (.encode .wire .laterAWire)
    buffer₁ none false [] ((encNat seen).reverse ++ .andMark :: output)
    work₁ [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hjumpWireA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let outA := (encodeCircuitGate (.and seen wire)).reverse ++ output
  let c₃ := sequentialExactlyOneCfg (.resume .laterAWire)
    buffer₁ none false [] outA work₁ [] (List.replicate seen ())
    (List.replicate next ()) (List.replicate wire ())
  have hwireA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) (5 * wire + 3) := by
    simpa [c₂, c₃, outA, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run wire .laterAWire buffer₁ false []
        ((encNat seen).reverse ++ .andMark :: output) work₁
        (List.replicate seen ()) (List.replicate next ())
  let c₄ := sequentialExactlyOneCfg .decLaterDuplicate
    buffer₁ none false [] (.orMark :: outA) work₁ []
    (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hpushB : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₅ := sequentialExactlyOneCfg (.encode .seen .laterBDuplicate)
    buffer₁ none true [] (.orMark :: outA) work₁ []
    (List.replicate (seen - 1) ()) (List.replicate next ())
    (List.replicate wire ())
  have hdecDuplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    have hs : seen = (seen - 1) + 1 := by omega
    change step sequentialExactlyOneRevProgram c₄ = some c₅
    unfold c₄ c₅
    rw [hs, List.replicate_succ]
    rfl
  let c₆ := sequentialExactlyOneCfg (.resume .laterBDuplicate)
    buffer₁ none false [] ((encNat (seen - 1)).reverse ++ .orMark :: outA)
    work₁ [] (List.replicate (seen - 1) ()) (List.replicate next ())
    (List.replicate wire ())
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) (5 * (seen - 1) + 3) := by
    simpa [c₅, c₆] using
      encodeSeen_run (seen - 1) .laterBDuplicate buffer₁ true []
        (.orMark :: outA) work₁ (List.replicate next ())
        (List.replicate wire ())
  let c₇ := sequentialExactlyOneCfg (.encode .next .laterBNext)
    buffer₁ none false [] ((encNat (seen - 1)).reverse ++ .orMark :: outA)
    work₁ [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hrestoreDuplicate : EvalsToInTime
      (step sequentialExactlyOneRevProgram) c₆ (some c₇) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    have hs : seen = (seen - 1) + 1 := by omega
    change step sequentialExactlyOneRevProgram c₆ = some c₇
    unfold c₆ c₇
    rw [hs, List.replicate_succ]
    rfl
  let outB := (encodeCircuitGate (.or (seen - 1) next)).reverse ++ outA
  let c₈ := sequentialExactlyOneCfg (.resume .laterBNext)
    buffer₁ none false [] outB work₁ [] (List.replicate seen ())
    (List.replicate next ()) (List.replicate wire ())
  have hnextB : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) (5 * next + 3) := by
    simpa [c₇, c₈, outB, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run next .laterBNext buffer₁ false []
        ((encNat (seen - 1)).reverse ++ .orMark :: outA) work₁
        (List.replicate seen ()) (List.replicate wire ())
  let c₉ := sequentialExactlyOneCfg (.encode .seen .laterCSeen)
    buffer₁ none false [] (.orMark :: outB) work₁ []
    (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hpushC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some c₉) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁₀ := sequentialExactlyOneCfg (.resume .laterCSeen)
    buffer₁ none false [] ((encNat seen).reverse ++ .orMark :: outB)
    work₁ [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hseenC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₉ (some c₁₀) (5 * seen + 3) := by
    simpa [c₉, c₁₀] using
      encodeSeen_run seen .laterCSeen buffer₁ false [] (.orMark :: outB)
        work₁ (List.replicate next ()) (List.replicate wire ())
  let c₁₁ := sequentialExactlyOneCfg (.encode .wire .laterCWire)
    buffer₁ none false [] ((encNat seen).reverse ++ .orMark :: outB)
    work₁ [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hjumpWireC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₀ (some c₁₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let outC := (encodeCircuitGate (.or seen wire)).reverse ++ outB
  let c₁₂ := sequentialExactlyOneCfg (.resume .laterCWire)
    buffer₁ none false [] outC work₁ [] (List.replicate seen ())
    (List.replicate next ()) (List.replicate wire ())
  have hwireC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₁ (some c₁₂) (5 * wire + 3) := by
    simpa [c₁₁, c₁₂, outC, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run wire .laterCWire buffer₁ false []
        ((encNat seen).reverse ++ .orMark :: outB) work₁
        (List.replicate seen ()) (List.replicate next ())
  let finalCfg := sequentialExactlyOneCfg .clearSeen
    buffer₁ none false [] outC work₁ [] (List.replicate seen ())
    (List.replicate next ()) (List.replicate wire ())
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₂ (some finalCfg) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 (5 * seen + 3) _ c₀ _ hpushA hseenA
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * seen + 3) + 1) 1 _ c₁ _ h₁ hjumpWireA
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * seen + 3) + 1)) (5 * wire + 3) _ c₂ _ h₂ hwireA
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1))) 1
    _ c₃ _ h₃ hpushB
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1)))) 1
    _ c₄ _ h₄ hdecDuplicate
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1)))))
    (5 * (seen - 1) + 3) _ c₅ _ h₅ hduplicate
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * (seen - 1) + 3) +
      (1 + (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1))))))
    1 _ c₆ _ h₆ hrestoreDuplicate
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * (seen - 1) + 3) +
      (1 + (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1)))))))
    (5 * next + 3) _ c₇ _ h₇ hnextB
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * next + 3) + (1 + ((5 * (seen - 1) + 3) +
      (1 + (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1))))))))
    1 _ c₈ _ h₈ hpushC
  let h₁₀ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * next + 3) + (1 + ((5 * (seen - 1) + 3) +
      (1 + (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1)))))))))
    (5 * seen + 3) _ c₉ _ h₉ hseenC
  let h₁₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * seen + 3) + (1 + ((5 * next + 3) +
      (1 + ((5 * (seen - 1) + 3) + (1 +
        (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1))))))))))
    1 _ c₁₀ _ h₁₀ hjumpWireC
  let h₁₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * seen + 3) + (1 + ((5 * next + 3) +
      (1 + ((5 * (seen - 1) + 3) + (1 +
        (1 + ((5 * wire + 3) + (1 + ((5 * seen + 3) + 1)))))))))))
    (5 * wire + 3) _ c₁₁ _ h₁₁ hwireC
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁₂ _ h₁₂ hjumpClear
  convert full using 1
  · simp [finalCfg, outC, outB, outA, seen, next,
      sequentialExactlyOneLaterChunk, List.reverse_append,
      List.append_assoc]
  · simp [seen, next]
    omega

/-! ## Register update between scan blocks -/

private theorem clearSeen_eval (count : Nat) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (output : List CircuitSym) (work₁ work₂ next wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
      (some (sequentialExactlyOneCfg .clearSeen buffer₁ buffer₂ test [] output
        work₁ work₂ (List.replicate count ()) next wire)) =
      some (sequentialExactlyOneCfg .copyNext buffer₁ buffer₂ false [] output
        work₁ work₂ [] next wire) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
          (some (sequentialExactlyOneCfg .clearSeen buffer₁ buffer₂ true []
            output work₁ work₂ (List.replicate count ()) next wire)) = _
      simpa [List.replicate_succ] using ih true

private theorem copyNext_consume_eval (count : Nat)
    (buffer₁ buffer₂ : Option Unit) (test : Bool)
    (output : List CircuitSym) (work₁ saved seen wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
      (some (sequentialExactlyOneCfg .copyNext buffer₁ buffer₂ test [] output
        work₁ saved seen (List.replicate count ()) wire)) =
      some (sequentialExactlyOneCfg .restoreNext buffer₁ buffer₂ false [] output
        work₁ (List.replicate count () ++ saved)
        (List.replicate count () ++ seen) [] wire) := by
  induction count generalizing test saved seen with
  | zero => rfl
  | succ count ih =>
      rw [show 3 * (count + 1) + 1 = (3 * count + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
          (some (sequentialExactlyOneCfg .copyNext buffer₁ buffer₂ true []
            output work₁ (() :: saved) (() :: seen)
            (List.replicate count ()) wire)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (() :: saved) (() :: seen)

private theorem restoreNext_eval (count : Nat)
    (buffer₁ buffer₂ : Option Unit) (test : Bool)
    (output : List CircuitSym) (work₁ seen restored wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
      (some (sequentialExactlyOneCfg .restoreNext buffer₁ buffer₂ test [] output
        work₁ (List.replicate count ()) seen restored wire)) =
      some (sequentialExactlyOneCfg .incSeen₁ buffer₁ none test [] output
        work₁ [] seen (List.replicate count () ++ restored) wire) := by
  induction count generalizing buffer₂ test restored with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
          (some (sequentialExactlyOneCfg .restoreNext buffer₁ (some ()) test []
            output work₁ (List.replicate count ()) seen (() :: restored)
            wire)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some ()) test (() :: restored)

/-- Replace `seen` by `next + 2` and advance `next` by three, preserving
the current source wire. -/
def updateScanRegisters (seen next wire : Nat)
    (buffer₁ : Option Unit) (work₁ : List Unit)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .clearSeen buffer₁ none false [] output work₁ []
        (List.replicate seen ()) (List.replicate next ())
        (List.replicate wire ()))
      (some (sequentialExactlyOneCfg .nextLater buffer₁ none false [] output
        work₁ [] (List.replicate (next + 2) ())
        (List.replicate (next + 3) ()) (List.replicate wire ())))
      (seen + 5 * next + 8) := by
  let afterClear := sequentialExactlyOneCfg .copyNext buffer₁ none false []
    output work₁ [] [] (List.replicate next ()) (List.replicate wire ())
  let afterCopy := sequentialExactlyOneCfg .restoreNext buffer₁ none false []
    output work₁ (List.replicate next ()) (List.replicate next ()) []
    (List.replicate wire ())
  let afterRestore := sequentialExactlyOneCfg .incSeen₁ buffer₁ none false []
    output work₁ [] (List.replicate next ()) (List.replicate next ())
    (List.replicate wire ())
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .clearSeen buffer₁ none false [] output work₁ []
        (List.replicate seen ()) (List.replicate next ())
        (List.replicate wire ()))
      (some afterClear) (seen + 1) := by
    exact ⟨⟨seen + 1, by
      simpa [afterClear] using clearSeen_eval seen buffer₁ none false output
        work₁ [] (List.replicate next ()) (List.replicate wire ())⟩, le_rfl⟩
  have hcopy : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterClear (some afterCopy) (3 * next + 1) := by
    exact ⟨⟨3 * next + 1, by
      simpa [afterClear, afterCopy] using copyNext_consume_eval next
        buffer₁ none false output work₁ [] [] (List.replicate wire ())⟩,
      le_rfl⟩
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterCopy (some afterRestore) (2 * next + 1) := by
    exact ⟨⟨2 * next + 1, by
      simpa [afterCopy, afterRestore] using restoreNext_eval next buffer₁ none
        false output work₁ (List.replicate next ()) []
        (List.replicate wire ())⟩, le_rfl⟩
  let finalCfg := sequentialExactlyOneCfg .nextLater buffer₁ none false []
    output work₁ [] (List.replicate (next + 2) ())
    (List.replicate (next + 3) ()) (List.replicate wire ())
  have hincrements : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterRestore (some finalCfg) 5 := by
    refine ⟨⟨5, ?_⟩, le_rfl⟩
    change some (sequentialExactlyOneCfg .nextLater buffer₁ none false []
      output work₁ [] (() :: () :: List.replicate next ())
      (() :: () :: () :: List.replicate next ())
      (List.replicate wire ())) = some finalCfg
    unfold finalCfg
    simp [List.replicate_succ]
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (seen + 1) (3 * next + 1) _ afterClear _ hclear hcopy
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((3 * next + 1) + (seen + 1)) (2 * next + 1)
    _ afterCopy _ h₁ hrestore
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((2 * next + 1) + ((3 * next + 1) + (seen + 1))) 5
    _ afterRestore _ h₂ hincrements
  have hsteps : 5 + ((2 * next + 1) +
      ((3 * next + 1) + (seen + 1))) = seen + 5 * next + 8 := by omega
  rw [← hsteps]
  simpa [finalCfg] using full

/-! ## Unary input scan and the complete block loop -/

private theorem unitList_eq_replicate (input : List Unit) :
    input = List.replicate input.length () := by
  induction input with
  | nil => rfl
  | cons head rest ih =>
      cases head
      change () :: rest = List.replicate (rest.length + 1) ()
      rw [List.replicate_succ]
      exact congrArg (List.cons ()) ih

private theorem sequentialExactlyOne_scan_eval (input : List Unit)
    (buffer₁ : Option Unit) (work₁ wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[
        2 * input.length + 1]
      (some (sequentialExactlyOneCfg .scan buffer₁ none false input []
        work₁ [] [] [] wire)) =
      some (sequentialExactlyOneCfg .initNext₁ none none false [] []
        (input.reverse ++ work₁) [] [] []
        (List.replicate input.length () ++ wire)) := by
  induction input generalizing buffer₁ work₁ wire with
  | nil => rfl
  | cons head rest ih =>
      cases head
      rw [show 2 * (Unit.unit :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[
            2 * rest.length + 1]
          (some (sequentialExactlyOneCfg .scan (some ()) none false rest []
            (() :: work₁) [] [] [] (() :: wire))) = _
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.replicate_succ, replicate_append_cons, List.cons_append,
        List.nil_append] using ih (some ()) (() :: work₁) (() :: wire)

private def sequentialExactlyOnePrelude (input : List Unit) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (initialCfg sequentialExactlyOneRevProgram input)
      (some (sequentialExactlyOneCfg .nextFirst none none false []
        [.constFalseMark, .constFalseMark]
        (List.replicate input.length ()) [] [] (List.replicate 2 ())
        (List.replicate input.length ())))
      (2 * input.length + 5) := by
  let afterScan := sequentialExactlyOneCfg .initNext₁ none none false [] []
    input.reverse [] [] [] (List.replicate input.length ())
  have hscan : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (initialCfg sequentialExactlyOneRevProgram input)
      (some afterScan) (2 * input.length + 1) := by
    rw [show initialCfg sequentialExactlyOneRevProgram input =
        sequentialExactlyOneCfg .scan none none false input [] [] [] [] [] []
      by rfl]
    exact ⟨⟨2 * input.length + 1, by
      simpa [afterScan] using
        sequentialExactlyOne_scan_eval input none [] []⟩, le_rfl⟩
  let finalCfg := sequentialExactlyOneCfg .nextFirst none none false []
    [.constFalseMark, .constFalseMark] (List.replicate input.length ()) [] []
    (List.replicate 2 ()) (List.replicate input.length ())
  have hfixed : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterScan (some finalCfg) 4 := by
    refine ⟨⟨4, ?_⟩, le_rfl⟩
    have hreverse : input.reverse = List.replicate input.length () := by
      calc
        input.reverse = (List.replicate input.length ()).reverse :=
          congrArg List.reverse (unitList_eq_replicate input)
        _ = List.replicate input.length () := by simp
    unfold afterScan
    rw [hreverse]
    change some (sequentialExactlyOneCfg .nextFirst none none false []
      [.constFalseMark, .constFalseMark] (List.replicate input.length ()) [] []
      [(), ()] (List.replicate input.length ())) = some finalCfg
    unfold finalCfg
    rfl
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (2 * input.length + 1) 4 _ afterScan _ hscan hfixed
  have hsteps : 4 + (2 * input.length + 1) = 2 * input.length + 5 := by omega
  rw [← hsteps]
  simpa [finalCfg] using full

private def sequentialExactlyOneLaterSteps : Nat → Nat → Nat
  | _, 0 => 0
  | phase, remaining + 1 =>
      (78 * phase + 10 * remaining + 67) +
        sequentialExactlyOneLaterSteps (phase + 1) remaining

private def sequentialExactlyOneLaterPhases (phase remaining : Nat)
    (hphase : 0 < phase) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .nextLater (some ()) none false [] output
        (List.replicate remaining ()) []
        (List.replicate (3 * phase + 1) ())
        (List.replicate (3 * phase + 2) ())
        (List.replicate remaining ()))
      (some (sequentialExactlyOneCfg .nextLater (some ()) none false []
        (((sequentialExactlyOneChunksFrom phase remaining).flatMap
          encodeCircuitGate).reverse ++ output) [] []
        (List.replicate (3 * (phase + remaining) + 1) ())
        (List.replicate (3 * (phase + remaining) + 2) ()) []))
      (sequentialExactlyOneLaterSteps phase remaining) := by
  induction remaining generalizing phase output with
  | zero =>
      exact ⟨⟨0, by
        simp [sequentialExactlyOneChunksFrom]⟩,
        le_rfl⟩
  | succ remaining ih =>
      let afterPop := sequentialExactlyOneCfg .decLaterWire (some ()) none
        false [] output (List.replicate remaining ()) []
        (List.replicate (3 * phase + 1) ())
        (List.replicate (3 * phase + 2) ())
        (List.replicate (remaining + 1) ())
      have hpop : EvalsToInTime (step sequentialExactlyOneRevProgram)
          (sequentialExactlyOneCfg .nextLater (some ()) none false [] output
            (List.replicate (remaining + 1) ()) []
            (List.replicate (3 * phase + 1) ())
            (List.replicate (3 * phase + 2) ())
            (List.replicate (remaining + 1) ()))
          (some afterPop) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step sequentialExactlyOneRevProgram
          (sequentialExactlyOneCfg .nextLater (some ()) none false [] output
            (List.replicate (remaining + 1) ()) []
            (List.replicate (3 * phase + 1) ())
            (List.replicate (3 * phase + 2) ())
            (List.replicate (remaining + 1) ())) = some afterPop
        unfold afterPop
        rw [List.replicate_succ]
        rfl
      let beforeGates := sequentialExactlyOneCfg .pushLaterAnd (some ()) none
        true [] output (List.replicate remaining ()) []
        (List.replicate (3 * phase + 1) ())
        (List.replicate (3 * phase + 2) ())
        (List.replicate remaining ())
      have hdec : EvalsToInTime (step sequentialExactlyOneRevProgram)
          afterPop (some beforeGates) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step sequentialExactlyOneRevProgram afterPop = some beforeGates
        unfold afterPop beforeGates
        rw [List.replicate_succ]
        rfl
      let chunkOutput :=
        ((sequentialExactlyOneLaterChunk phase remaining).flatMap
          encodeCircuitGate).reverse ++ output
      let beforeUpdate := sequentialExactlyOneCfg .clearSeen (some ()) none
        false [] chunkOutput (List.replicate remaining ()) []
        (List.replicate (3 * phase + 1) ())
        (List.replicate (3 * phase + 2) ())
        (List.replicate remaining ())
      have hgates : EvalsToInTime (step sequentialExactlyOneRevProgram)
          beforeGates (some beforeUpdate)
            (60 * phase + 10 * remaining + 46) := by
        simpa [beforeGates, beforeUpdate, chunkOutput] using
          laterGatePhase phase remaining (some ())
            (List.replicate remaining ()) output
      let afterUpdate := sequentialExactlyOneCfg .nextLater (some ()) none
        false [] chunkOutput (List.replicate remaining ()) []
        (List.replicate (3 * (phase + 1) + 1) ())
        (List.replicate (3 * (phase + 1) + 2) ())
        (List.replicate remaining ())
      have hupdate : EvalsToInTime (step sequentialExactlyOneRevProgram)
          beforeUpdate (some afterUpdate) (18 * phase + 19) := by
        convert
          updateScanRegisters (3 * phase + 1) (3 * phase + 2) remaining
            (some ()) (List.replicate remaining ()) chunkOutput using 1 <;>
          simp [afterUpdate, chunkOutput, Nat.mul_add,
            Nat.add_assoc] <;> omega
      let remainingOutput :=
        ((sequentialExactlyOneChunksFrom (phase + 1) remaining).flatMap
          encodeCircuitGate).reverse ++ chunkOutput
      have hremaining := ih (phase + 1) (by omega) chunkOutput
      let throughPop := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        1 1 _ afterPop _ hpop hdec
      let throughGates := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram) 2
        (60 * phase + 10 * remaining + 46) _ beforeGates _
        throughPop hgates
      let throughUpdate := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram)
        ((60 * phase + 10 * remaining + 46) + 2)
        (18 * phase + 19) _ beforeUpdate _ throughGates hupdate
      let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        ((18 * phase + 19) +
          ((60 * phase + 10 * remaining + 46) + 2))
        (sequentialExactlyOneLaterSteps (phase + 1) remaining)
        _ afterUpdate _ throughUpdate hremaining
      have hsteps :
          sequentialExactlyOneLaterSteps (phase + 1) remaining +
              ((18 * phase + 19) +
                ((60 * phase + 10 * remaining + 46) + 2)) =
            sequentialExactlyOneLaterSteps phase (remaining + 1) := by
        change _ = (78 * phase + 10 * remaining + 67) +
          sequentialExactlyOneLaterSteps (phase + 1) remaining
        omega
      rw [← hsteps]
      simpa [remainingOutput, chunkOutput, afterUpdate,
        sequentialExactlyOneChunksFrom, sequentialExactlyOneChunk,
        show phase ≠ 0 from by omega, List.flatMap_append,
        List.reverse_append, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using full

/-! ## Final two gates and scratch cleanup -/

private theorem clearFirst_eval (count : Nat) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (output : List CircuitSym) (next wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
      (some (sequentialExactlyOneCfg .clear₁ buffer₁ buffer₂ test [] output
        [] [] (List.replicate count ()) next wire)) =
      some (sequentialExactlyOneCfg .clear₂ buffer₁ buffer₂ false [] output
        [] [] [] next wire) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
          (some (sequentialExactlyOneCfg .clear₁ buffer₁ buffer₂ true []
            output [] [] (List.replicate count ()) next wire)) = _
      simpa [List.replicate_succ] using ih true

private theorem clearNext_eval (count : Nat) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (output : List CircuitSym) (seen wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
      (some (sequentialExactlyOneCfg .clear₂ buffer₁ buffer₂ test [] output
        [] [] seen (List.replicate count ()) wire)) =
      some (sequentialExactlyOneCfg .clear₃ buffer₁ buffer₂ false [] output
        [] [] seen [] wire) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
          (some (sequentialExactlyOneCfg .clear₂ buffer₁ buffer₂ true []
            output [] [] seen (List.replicate count ()) wire)) = _
      simpa [List.replicate_succ] using ih true

private theorem clearWire_eval (count : Nat) (buffer₁ buffer₂ : Option Unit)
    (test : Bool) (output : List CircuitSym) (seen : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
      (some (sequentialExactlyOneCfg .clear₃ buffer₁ buffer₂ test [] output
        [] [] seen [] (List.replicate count ()))) =
      some (sequentialExactlyOneCfg .halt buffer₁ buffer₂ false [] output
        [] [] seen [] []) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
          (some (sequentialExactlyOneCfg .clear₃ buffer₁ buffer₂ true []
            output [] [] seen [] (List.replicate count ()))) = _
      simpa [List.replicate_succ] using ih true

/-- Clear all three unary registers and halt with the existing output. -/
def clearAllRegisters (seen next wire : Nat)
    (buffer₁ : Option Unit) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .clear₁ buffer₁ none false [] output [] []
        (List.replicate seen ()) (List.replicate next ())
        (List.replicate wire ()))
      (some (haltCfg sequentialExactlyOneRevProgram output))
      (seen + next + wire + 4) := by
  let afterSeen := sequentialExactlyOneCfg .clear₂ buffer₁ none false []
    output [] [] [] (List.replicate next ()) (List.replicate wire ())
  let afterNext := sequentialExactlyOneCfg .clear₃ buffer₁ none false []
    output [] [] [] [] (List.replicate wire ())
  let beforeHalt := sequentialExactlyOneCfg .halt buffer₁ none false []
    output [] [] [] [] []
  have hseen : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .clear₁ buffer₁ none false [] output [] []
        (List.replicate seen ()) (List.replicate next ())
        (List.replicate wire ()))
      (some afterSeen) (seen + 1) := by
    exact ⟨⟨seen + 1, by
      simpa [afterSeen] using clearFirst_eval seen buffer₁ none false output
        (List.replicate next ()) (List.replicate wire ())⟩, le_rfl⟩
  have hnext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterSeen (some afterNext) (next + 1) := by
    exact ⟨⟨next + 1, by
      simpa [afterSeen, afterNext] using clearNext_eval next buffer₁ none
        false output [] (List.replicate wire ())⟩, le_rfl⟩
  have hwire : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterNext (some beforeHalt) (wire + 1) := by
    exact ⟨⟨wire + 1, by
      simpa [afterNext, beforeHalt] using clearWire_eval wire buffer₁ none
        false output []⟩, le_rfl⟩
  have hhalt : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeHalt (some (haltCfg sequentialExactlyOneRevProgram output)) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (seen + 1) (next + 1) _ afterSeen _ hseen hnext
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((next + 1) + (seen + 1)) (wire + 1) _ afterNext _ h₁ hwire
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((wire + 1) + ((next + 1) + (seen + 1))) 1
    _ beforeHalt _ h₂ hhalt
  have hsteps : 1 + ((wire + 1) + ((next + 1) + (seen + 1))) =
      seen + next + wire + 4 := by omega
  rw [← hsteps]
  exact full

private def sequentialExactlyOneFinalZero (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalZero none none false [] output [] [] []
        (List.replicate 2 ()) [])
      (some (haltCfg sequentialExactlyOneRevProgram
        (([.not 1, .and 0 2].flatMap encodeCircuitGate).reverse ++ output)))
      37 := by
  let c₀ := sequentialExactlyOneCfg .incFinalZeroDuplicate none none false []
    (.notMark :: output) [] [] [] (List.replicate 2 ()) []
  have hnot : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalZero none none false [] output [] [] []
        (List.replicate 2 ()) []) (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.encode .seen .finalZeroDuplicate)
    none none false [] (.notMark :: output) [] [] [()]
    (List.replicate 2 ()) []
  have hinc : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₂ := sequentialExactlyOneCfg (.resume .finalZeroDuplicate)
    none none false [] ((encNat 1).reverse ++ .notMark :: output)
    [] [] [()] (List.replicate 2 ()) []
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) 8 := by
    simpa [c₁, c₂] using encodeSeen_run 1 .finalZeroDuplicate none false []
      (.notMark :: output) [] (List.replicate 2 ()) []
  let c₃ := sequentialExactlyOneCfg .restoreFinalZeroDuplicate none none
    false [] ((encNat 1).reverse ++ .notMark :: output)
    [] [] [()] (List.replicate 2 ()) []
  have hjump : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₄ := sequentialExactlyOneCfg .pushFinalAnd none none true []
    ((encNat 1).reverse ++ .notMark :: output)
    [] [] [] (List.replicate 2 ()) []
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₅ := sequentialExactlyOneCfg (.encode .seen .finalSeen) none none true []
    (.andMark :: (encNat 1).reverse ++ .notMark :: output)
    [] [] [] (List.replicate 2 ()) []
  have hand : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₆ := sequentialExactlyOneCfg (.resume .finalSeen) none none false []
    ((encNat 0).reverse ++ .andMark ::
      (encNat 1).reverse ++ .notMark :: output)
    [] [] [] (List.replicate 2 ()) []
  have hseen : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) 3 := by
    simpa [c₅, c₆] using encodeSeen_run 0 .finalSeen none true []
      (.andMark :: (encNat 1).reverse ++ .notMark :: output)
      [] (List.replicate 2 ()) []
  let c₇ := sequentialExactlyOneCfg (.encode .next .finalNext) none none false []
    ((encNat 0).reverse ++ .andMark ::
      (encNat 1).reverse ++ .notMark :: output)
    [] [] [] (List.replicate 2 ()) []
  have hjumpNext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₆ (some c₇) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let finalOutput :=
    (([.not 1, .and 0 2].flatMap encodeCircuitGate).reverse ++ output)
  let c₈ := sequentialExactlyOneCfg (.resume .finalNext) none none false []
    finalOutput [] [] [] (List.replicate 2 ()) []
  have hnext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) 13 := by
    simpa [c₇, c₈, finalOutput, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run 2 .finalNext none false []
        ((encNat 0).reverse ++ .andMark ::
          (encNat 1).reverse ++ .notMark :: output) [] [] []
  let beforeClear := sequentialExactlyOneCfg .clear₁ none none false []
    finalOutput [] [] [] (List.replicate 2 ()) []
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear (some (haltCfg sequentialExactlyOneRevProgram finalOutput)) 6 := by
    simpa [beforeClear] using clearAllRegisters 0 2 0 none finalOutput
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 1 _ c₀ _ hnot hinc
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    2 8 _ c₁ _ h₁ hduplicate
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    10 1 _ c₂ _ h₂ hjump
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    11 1 _ c₃ _ h₃ hrestore
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    12 1 _ c₄ _ h₄ hand
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    13 3 _ c₅ _ h₅ hseen
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    16 1 _ c₆ _ h₆ hjumpNext
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    17 13 _ c₇ _ h₇ hnext
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    30 1 _ c₈ _ h₈ hjumpClear
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    31 6 _ beforeClear _ h₉ hclear
  simpa [finalOutput] using full

private def sequentialExactlyOneFinalSome (count : Nat) (_hcount : 0 < count)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalSome none none false [] output [] []
        (List.replicate (3 * count + 1) ())
        (List.replicate (3 * count + 2) ()) [])
      (some (haltCfg sequentialExactlyOneRevProgram
        (([.not (3 * count), .and (3 * count + 1) (3 * count + 2)].flatMap
          encodeCircuitGate).reverse ++ output)))
      (51 * count + 38) := by
  let seen := 3 * count + 1
  let next := 3 * count + 2
  let duplicate := 3 * count
  have hseen : seen = duplicate + 1 := by simp [seen, duplicate]
  let c₀ := sequentialExactlyOneCfg .decFinalSomeDuplicate none none false []
    (.notMark :: output) [] [] (List.replicate seen ())
    (List.replicate next ()) []
  have hnot : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalSome none none false [] output [] []
        (List.replicate seen ()) (List.replicate next ()) [])
      (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.encode .seen .finalSomeDuplicate)
    none none true [] (.notMark :: output) [] []
    (List.replicate duplicate ()) (List.replicate next ()) []
  have hdec : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₀ = some c₁
    unfold c₀ c₁
    rw [hseen, List.replicate_succ]
    rfl
  let c₂ := sequentialExactlyOneCfg (.resume .finalSomeDuplicate)
    none none false [] ((encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate duplicate ()) (List.replicate next ()) []
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) (15 * count + 3) := by
    convert encodeSeen_run duplicate .finalSomeDuplicate none true []
      (.notMark :: output) [] (List.replicate next ()) [] using 1 <;>
      simp [duplicate] <;> omega
  let c₃ := sequentialExactlyOneCfg .restoreFinalSomeDuplicate none none
    false [] ((encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate duplicate ()) (List.replicate next ()) []
  have hjump : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₄ := sequentialExactlyOneCfg .pushFinalAnd none none false []
    ((encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ()) []
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₃ = some c₄
    unfold c₃ c₄
    rw [hseen, List.replicate_succ]
    rfl
  let c₅ := sequentialExactlyOneCfg (.encode .seen .finalSeen) none none false []
    (.andMark :: (encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ()) []
  have hand : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₆ := sequentialExactlyOneCfg (.resume .finalSeen) none none false []
    ((encNat seen).reverse ++ .andMark ::
      (encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ()) []
  have hencodeSeen : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) (15 * count + 8) := by
    convert encodeSeen_run seen .finalSeen none false []
      (.andMark :: (encNat duplicate).reverse ++ .notMark :: output)
      [] (List.replicate next ()) [] using 1 <;>
      simp [c₆, seen] <;> omega
  let c₇ := sequentialExactlyOneCfg (.encode .next .finalNext) none none false []
    ((encNat seen).reverse ++ .andMark ::
      (encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ()) []
  have hjumpNext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₆ (some c₇) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let finalOutput :=
    (([.not duplicate, .and seen next].flatMap encodeCircuitGate).reverse ++
      output)
  let c₈ := sequentialExactlyOneCfg (.resume .finalNext) none none false []
    finalOutput [] [] (List.replicate seen ()) (List.replicate next ()) []
  have hencodeNext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) (15 * count + 13) := by
    convert encodeNext_run next .finalNext none false []
      ((encNat seen).reverse ++ .andMark ::
        (encNat duplicate).reverse ++ .notMark :: output)
      [] (List.replicate seen ()) [] using 1 <;>
      simp [c₈, finalOutput, next, encodeCircuitGate,
        List.reverse_append, List.append_assoc] <;> omega
  let beforeClear := sequentialExactlyOneCfg .clear₁ none none false []
    finalOutput [] [] (List.replicate seen ()) (List.replicate next ()) []
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear (some (haltCfg sequentialExactlyOneRevProgram finalOutput))
        (6 * count + 7) := by
    convert clearAllRegisters seen next 0 none finalOutput using 1 <;>
      simp [beforeClear, seen, next] <;> omega
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 1 _ c₀ _ hnot hdec
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    2 (15 * count + 3) _ c₁ _ h₁ hduplicate
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((15 * count + 3) + 2) 1 _ c₂ _ h₂ hjump
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((15 * count + 3) + 2)) 1 _ c₃ _ h₃ hrestore
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (1 + ((15 * count + 3) + 2))) 1 _ c₄ _ h₄ hand
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (1 + (1 + ((15 * count + 3) + 2)))) (15 * count + 8)
    _ c₅ _ h₅ hencodeSeen
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((15 * count + 8) + (1 + (1 + (1 + ((15 * count + 3) + 2)))))
    1 _ c₆ _ h₆ hjumpNext
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((15 * count + 8) +
      (1 + (1 + (1 + ((15 * count + 3) + 2))))))
    (15 * count + 13) _ c₇ _ h₇ hencodeNext
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((15 * count + 13) + (1 + ((15 * count + 8) +
      (1 + (1 + (1 + ((15 * count + 3) + 2)))))))
    1 _ c₈ _ h₈ hjumpClear
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((15 * count + 13) + (1 + ((15 * count + 8) +
      (1 + (1 + (1 + ((15 * count + 3) + 2))))))))
    (6 * count + 7) _ beforeClear _ h₉ hclear
  have hsteps : (6 * count + 7) +
      (1 + ((15 * count + 13) + (1 + ((15 * count + 8) +
        (1 + (1 + (1 + ((15 * count + 3) + 2)))))))) =
      51 * count + 38 := by omega
  rw [← hsteps]
  simpa [finalOutput, seen, next, duplicate] using full

/-! ## Complete reversed serializer -/

private def sequentialExactlyOnePositivePhases (remaining : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .nextFirst none none false [] output
        (List.replicate (remaining + 1) ()) [] [] (List.replicate 2 ())
        (List.replicate (remaining + 1) ()))
      (some (sequentialExactlyOneCfg .nextLater (some ()) none false []
        (((sequentialExactlyOneChunksFrom 0 (remaining + 1)).flatMap
          encodeCircuitGate).reverse ++ output) [] []
        (List.replicate (3 * (remaining + 1) + 1) ())
        (List.replicate (3 * (remaining + 1) + 2) ()) []))
      (sequentialExactlyOneLaterSteps 1 remaining + 10 * remaining + 61) := by
  let afterPop := sequentialExactlyOneCfg .decFirstWire (some ()) none false []
    output (List.replicate remaining ()) [] [] (List.replicate 2 ())
    (List.replicate (remaining + 1) ())
  have hpop : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .nextFirst none none false [] output
        (List.replicate (remaining + 1) ()) [] [] (List.replicate 2 ())
        (List.replicate (remaining + 1) ()))
      (some afterPop) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram
      (sequentialExactlyOneCfg .nextFirst none none false [] output
        (List.replicate (remaining + 1) ()) [] [] (List.replicate 2 ())
        (List.replicate (remaining + 1) ())) = some afterPop
    unfold afterPop
    rw [List.replicate_succ]
    rfl
  let beforeFirst := sequentialExactlyOneCfg .pushFirstAnd (some ()) none true []
    output (List.replicate remaining ()) [] [] (List.replicate 2 ())
    (List.replicate remaining ())
  have hdec : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterPop (some beforeFirst) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram afterPop = some beforeFirst
    unfold afterPop beforeFirst
    rw [List.replicate_succ]
    rfl
  let firstOutput :=
    ((sequentialExactlyOneFirstChunk remaining).flatMap
      encodeCircuitGate).reverse ++ output
  let beforeUpdate := sequentialExactlyOneCfg .clearSeen (some ()) none false []
    firstOutput (List.replicate remaining ()) [] [] (List.replicate 2 ())
    (List.replicate remaining ())
  have hfirst : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeFirst (some beforeUpdate) (10 * remaining + 41) := by
    simpa [beforeFirst, beforeUpdate, firstOutput] using
      firstGatePhase remaining (some ()) (List.replicate remaining ()) output
  let afterUpdate := sequentialExactlyOneCfg .nextLater (some ()) none false []
    firstOutput (List.replicate remaining ()) [] (List.replicate 4 ())
    (List.replicate 5 ()) (List.replicate remaining ())
  have hupdate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeUpdate (some afterUpdate) 18 := by
    simpa [beforeUpdate, afterUpdate, firstOutput] using
      updateScanRegisters 0 2 remaining (some ())
        (List.replicate remaining ()) firstOutput
  have hlater := sequentialExactlyOneLaterPhases 1 remaining (by omega)
    firstOutput
  let throughPop := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 1 _ afterPop _ hpop hdec
  let throughFirst := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    2 (10 * remaining + 41) _ beforeFirst _ throughPop hfirst
  let throughUpdate := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((10 * remaining + 41) + 2) 18 _ beforeUpdate _ throughFirst hupdate
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (18 + ((10 * remaining + 41) + 2))
    (sequentialExactlyOneLaterSteps 1 remaining)
    _ afterUpdate _ throughUpdate hlater
  have hsteps : sequentialExactlyOneLaterSteps 1 remaining +
      (18 + ((10 * remaining + 41) + 2)) =
      sequentialExactlyOneLaterSteps 1 remaining + 10 * remaining + 61 := by
    omega
  rw [← hsteps]
  simpa [afterUpdate, firstOutput, sequentialExactlyOneChunksFrom,
    sequentialExactlyOneChunk, List.flatMap_append, List.reverse_append,
    List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using full

/-- Exact step count of the prepend-oriented exactly-one serializer. -/
def sequentialExactlyOneRevSteps (input : List Unit) : Nat :=
  match input.length with
  | 0 => 43
  | remaining + 1 =>
      (2 * (remaining + 1) + 5) +
        (sequentialExactlyOneLaterSteps 1 remaining + 10 * remaining + 61) +
        1 + (51 * (remaining + 1) + 38)

/-- Exact independent-semantics run producing the reversed semantic stream. -/
def sequentialExactlyOneRev_run (input : List Unit) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (initialCfg sequentialExactlyOneRevProgram input)
      (some (haltCfg sequentialExactlyOneRevProgram
        (sequentialExactlyOneGateStream input.length).reverse))
      (sequentialExactlyOneRevSteps input) := by
  let baseOutput : List CircuitSym := [.constFalseMark, .constFalseMark]
  cases hlength : input.length with
  | zero =>
      have hprelude := sequentialExactlyOnePrelude input
      have hdispatch : EvalsToInTime (step sequentialExactlyOneRevProgram)
          (sequentialExactlyOneCfg .nextFirst none none false [] baseOutput
            [] [] [] (List.replicate 2 ()) [])
          (some (sequentialExactlyOneCfg .finalZero none none false []
            baseOutput [] [] [] (List.replicate 2 ()) [])) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hfinal := sequentialExactlyOneFinalZero baseOutput
      let throughDispatch := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram) 5 1 _
        (sequentialExactlyOneCfg .nextFirst none none false [] baseOutput
          [] [] [] (List.replicate 2 ()) []) _
        (by simpa [hlength, baseOutput] using hprelude) hdispatch
      let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        6 37 _
        (sequentialExactlyOneCfg .finalZero none none false []
          baseOutput [] [] [] (List.replicate 2 ()) []) _
        throughDispatch hfinal
      have hgateList := sequentialExactlyOneGateList_eq_trace 0
      simp only [sequentialExactlyOneGateStream]
      rw [← hgateList]
      simpa [sequentialExactlyOneRevSteps, hlength,
        sequentialExactlyOneGateList, sequentialExactlyOneChunksFrom,
        sequentialExactlyOneSeen, sequentialExactlyOneDuplicate,
        baseOutput, encodeCircuitGate, List.flatMap_append, List.reverse_append,
        List.append_assoc] using full
  | succ remaining =>
      let count := remaining + 1
      have hprelude := sequentialExactlyOnePrelude input
      have hphases := sequentialExactlyOnePositivePhases remaining baseOutput
      let phaseOutput :=
        (((sequentialExactlyOneChunksFrom 0 count).flatMap
          encodeCircuitGate).reverse ++ baseOutput)
      have hdispatch : EvalsToInTime (step sequentialExactlyOneRevProgram)
          (sequentialExactlyOneCfg .nextLater (some ()) none false []
            phaseOutput [] [] (List.replicate (3 * count + 1) ())
            (List.replicate (3 * count + 2) ()) [])
          (some (sequentialExactlyOneCfg .finalSome none none false []
            phaseOutput [] [] (List.replicate (3 * count + 1) ())
            (List.replicate (3 * count + 2) ()) [])) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hfinal := sequentialExactlyOneFinalSome count (by omega) phaseOutput
      let throughPhases := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram) (2 * count + 5)
        (sequentialExactlyOneLaterSteps 1 remaining + 10 * remaining + 61)
        _ (sequentialExactlyOneCfg .nextFirst none none false [] baseOutput
          (List.replicate count ()) [] [] (List.replicate 2 ())
          (List.replicate count ())) _
        (by simpa [hlength, count, baseOutput] using hprelude)
        (by simpa [count, phaseOutput] using hphases)
      let throughDispatch := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram)
        ((sequentialExactlyOneLaterSteps 1 remaining + 10 * remaining + 61) +
          (2 * count + 5)) 1 _
        (sequentialExactlyOneCfg .nextLater (some ()) none false []
          phaseOutput [] [] (List.replicate (3 * count + 1) ())
          (List.replicate (3 * count + 2) ()) []) _
        throughPhases hdispatch
      let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        (1 + ((sequentialExactlyOneLaterSteps 1 remaining +
          10 * remaining + 61) + (2 * count + 5)))
        (51 * count + 38) _
        (sequentialExactlyOneCfg .finalSome none none false []
          phaseOutput [] [] (List.replicate (3 * count + 1) ())
          (List.replicate (3 * count + 2) ()) []) _
        throughDispatch hfinal
      have hgateList := sequentialExactlyOneGateList_eq_trace count
      simp only [sequentialExactlyOneGateStream]
      rw [← hgateList]
      simpa [sequentialExactlyOneRevSteps, hlength,
        sequentialExactlyOneGateList, count, phaseOutput, baseOutput,
        sequentialExactlyOneSeen, sequentialExactlyOneDuplicate,
        encodeCircuitGate,
        List.flatMap_append, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using full

/-- Exact reversed-stream builder contract. -/
theorem sequentialExactlyOneRev_builderOutputs :
    BuilderOutputs sequentialExactlyOneRevProgram
      (fun input => (sequentialExactlyOneGateStream input.length).reverse)
      sequentialExactlyOneRevSteps := by
  intro input
  exact ⟨sequentialExactlyOneRev_run input⟩

/-- Exact output contract after compiling the bounded builder to a TM2. -/
theorem sequentialExactlyOneRev_outputs :
    Outputs sequentialExactlyOneRevProgram
      (fun input => (sequentialExactlyOneGateStream input.length).reverse)
      sequentialExactlyOneRevSteps :=
  Outputs.of_builder_run sequentialExactlyOneRev_builderOutputs

private theorem sequentialExactlyOneLaterSteps_le (phase remaining : Nat) :
    sequentialExactlyOneLaterSteps phase remaining ≤
      88 * remaining * (phase + remaining) + 67 * remaining := by
  induction remaining generalizing phase with
  | zero => simp [sequentialExactlyOneLaterSteps]
  | succ remaining ih =>
      rw [sequentialExactlyOneLaterSteps]
      have hrest := ih (phase + 1)
      nlinarith

/-- Quadratic runtime envelope for the concrete reversed serializer. -/
noncomputable def sequentialExactlyOneRev_polyBound :
    PolyBound sequentialExactlyOneRevSteps where
  polynomial := 100 * Polynomial.X ^ 2 + 200 * Polynomial.X + 100
  bound input := by
    cases hlength : input.length with
    | zero =>
        simp [sequentialExactlyOneRevSteps, hlength,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X]
    | succ remaining =>
        have hlater := sequentialExactlyOneLaterSteps_le 1 remaining
        simp only [sequentialExactlyOneRevSteps, hlength,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_ofNat]
        nlinarith

/-- Concrete polynomial-time TM2 producing the reversed exactly-one gate
stream. -/
noncomputable def sequentialExactlyOneRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit =>
        (sequentialExactlyOneGateStream input.length).reverse) :=
  ComputableInPolyTime sequentialExactlyOneRevProgram _
    sequentialExactlyOneRevSteps sequentialExactlyOneRev_outputs
    sequentialExactlyOneRev_polyBound

/-- Concrete polynomial-time TM2 producing the forward semantic exactly-one
gate stream. -/
noncomputable def sequentialExactlyOneGateStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Unit =>
        sequentialExactlyOneGateStream input.length) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      sequentialExactlyOneRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := CircuitSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
