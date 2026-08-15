import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Not
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq

/-!
# Contextual non-halting NOT/XNOR cell block

One stack-cell validity block is a NOT gate followed immediately by a five-gate
Boolean equality.  This module is the first real primitive composition: the
shared program does not halt between those two gates.  Instead it reuses the
blank-source register to derive the NOT output wire, restores the equality
start, and enters the existing Boolean-equality kernel.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Exact six-gate stream: negate `blank`, then compare `left` with the fresh
NOT output `right`; the Boolean equality starts at `right + 1`. -/
def affineCellGateStream (right left blank : Nat) : List CircuitSym :=
  affineNotGateStream blank ++
    affineBoolEqGateStream (right + 1) left right

/-- The composed byte stream is exactly one NOT followed by the semantic XNOR
trace. -/
theorem affineCellGateStream_eq_trace (right left blank : Nat) :
    affineCellGateStream right left blank =
      ([CircuitGate.not blank] ++
        (CircuitBuilder.boolEqGateTrace (right + 1) left right).gates).flatMap
          encodeCircuitGate := by
  simp [affineCellGateStream, affineNotGateStream_eq_trace,
    affineBoolEqGateStream_eq_trace]

/-- Contextual entry.  `right` is one less than the equality start and is the
fresh wire produced by the leading NOT. -/
def affineCellBodyCfg (right left blank : Nat)
    (output : List CircuitSym) : BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg (.cell .notPush) none none false [] output [] []
    (List.replicate right ()) (List.replicate left ())
    (List.replicate blank ())

/-- Exact running time through cell cleanup, stopping at the final halt label
so a family controller can continue with the next framed cell. -/
def affineCellRevCoreSteps (right left blank : Nat) : Nat :=
  6 * blank + 5 * right + 9 +
    affineBoolEqRevCoreSteps (right + 1) left right

/-- Exact running time of the standalone non-halting NOT/XNOR composition. -/
def affineCellRevSteps (right left blank : Nat) : Nat :=
  6 * blank + 5 * right + 9 +
    affineBoolEqRevSteps (right + 1) left right

private theorem replicate_append_cons (count : Nat) (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons ()) ih

private theorem cellClearWire_eval (count : Nat) (test : Bool)
    (output : List CircuitSym) (seen next : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
      (some (sequentialExactlyOneCfg (.cell .clearWire) none none test []
        output [] [] seen next (List.replicate count ()))) =
      some (sequentialExactlyOneCfg (.cell .copyStart) none none false []
        output [] [] seen next []) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
          (some (sequentialExactlyOneCfg (.cell .clearWire) none none true []
            output [] [] seen next (List.replicate count ()))) = _
      simpa [List.replicate_succ] using ih true

private theorem cellCopyStart_eval (count : Nat) (test : Bool)
    (output : List CircuitSym) (saved next restored : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
      (some (sequentialExactlyOneCfg (.cell .copyStart) none none test []
        output saved [] (List.replicate count ()) next restored)) =
      some (sequentialExactlyOneCfg (.cell .restoreStart) none none false []
        output (List.replicate count () ++ saved) [] [] next
        (List.replicate count () ++ restored)) := by
  induction count generalizing test saved restored with
  | zero => rfl
  | succ count ih =>
      rw [show 3 * (count + 1) + 1 = (3 * count + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
          (some (sequentialExactlyOneCfg (.cell .copyStart) none none true []
            output (() :: saved) [] (List.replicate count ()) next
            (() :: restored))) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (() :: saved) (() :: restored)

private theorem cellRestoreStart_eval (count : Nat) (buffer₁ : Option Unit)
    (test : Bool) (output : List CircuitSym) (restored next wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
      (some (sequentialExactlyOneCfg (.cell .restoreStart) buffer₁ none test []
        output (List.replicate count ()) [] restored next wire)) =
      some (sequentialExactlyOneCfg (.cell .incStart) none none test []
        output [] [] (List.replicate count () ++ restored) next wire) := by
  induction count generalizing buffer₁ restored with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
          (some (sequentialExactlyOneCfg (.cell .restoreStart) (some ()) none
            test [] output (List.replicate count ()) [] (() :: restored)
            next wire)) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some ()) (() :: restored)

/-- Execute one complete six-gate cell block without halting between its NOT
and XNOR halves, clean every scratch stack, and stop at the redirectable halt
label. -/
def affineCellRev_runToHaltLabel (right left blank : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineCellBodyCfg right left blank output)
      (some (sequentialExactlyOneCfg .halt none none false []
        ((affineCellGateStream right left blank).reverse ++ output)
        [] [] [] [] []))
      (affineCellRevCoreSteps right left blank) := by
  let afterPush := sequentialExactlyOneCfg
    (.encode .wire .affineCellNotWire) none none false []
    (.notMark :: output) [] [] (List.replicate right ())
    (List.replicate left ()) (List.replicate blank ())
  have hpush : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineCellBodyCfg right left blank output) (some afterPush) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let notOutput := (affineNotGateStream blank).reverse ++ output
  let afterEncode := sequentialExactlyOneCfg
    (.resume .affineCellNotWire) none none false [] notOutput [] []
    (List.replicate right ()) (List.replicate left ())
    (List.replicate blank ())
  have hencode : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterPush (some afterEncode) (5 * blank + 3) := by
    simpa [afterPush, afterEncode, notOutput, affineNotGateStream,
      encodeCircuitGate, List.reverse_append, List.append_assoc] using
      encodeWire_run blank .affineCellNotWire none false []
        (.notMark :: output) [] (List.replicate right ())
        (List.replicate left ())
  let beforeClear := sequentialExactlyOneCfg (.cell .clearWire)
    none none false [] notOutput [] [] (List.replicate right ())
    (List.replicate left ()) (List.replicate blank ())
  have hjump : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterEncode (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let beforeCopy := sequentialExactlyOneCfg (.cell .copyStart)
    none none false [] notOutput [] [] (List.replicate right ())
    (List.replicate left ()) []
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear (some beforeCopy) (blank + 1) := by
    exact ⟨⟨blank + 1, by
      simpa [beforeClear, beforeCopy] using cellClearWire_eval blank false
        notOutput (List.replicate right ()) (List.replicate left ())⟩,
      le_rfl⟩
  let beforeRestore := sequentialExactlyOneCfg (.cell .restoreStart)
    none none false [] notOutput (List.replicate right ()) [] []
    (List.replicate left ()) (List.replicate right ())
  have hcopy : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeCopy (some beforeRestore) (3 * right + 1) := by
    exact ⟨⟨3 * right + 1, by
      simpa [beforeCopy, beforeRestore] using
        cellCopyStart_eval right false notOutput []
          (List.replicate left ()) []⟩, le_rfl⟩
  let beforeInc := sequentialExactlyOneCfg (.cell .incStart)
    none none false [] notOutput [] [] (List.replicate right ())
    (List.replicate left ()) (List.replicate right ())
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeRestore (some beforeInc) (2 * right + 1) := by
    exact ⟨⟨2 * right + 1, by
      simpa [beforeRestore, beforeInc] using
        cellRestoreStart_eval right none false notOutput []
          (List.replicate left ()) (List.replicate right ())⟩, le_rfl⟩
  have hinc : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeInc
      (some (affineBoolEqBodyCfg (right + 1) left right notOutput)) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change some (sequentialExactlyOneCfg (.boolEq .notLeft)
      none none false [] notOutput [] []
      (() :: List.replicate right ())
      (List.replicate left ()) (List.replicate right ())) =
      some (affineBoolEqBodyCfg (right + 1) left right notOutput)
    simp [affineBoolEqBodyCfg, List.replicate_succ]
  have heq := affineBoolEqRev_runToHaltLabel
    (right + 1) left right notOutput
  let t₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 (5 * blank + 3) _ afterPush _ hpush hencode
  let t₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ afterEncode _ t₁ hjump
  let t₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (blank + 1) _ beforeClear _ t₂ hclear
  let t₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (3 * right + 1) _ beforeCopy _ t₃ hcopy
  let t₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (2 * right + 1) _ beforeRestore _ t₄ hrestore
  let t₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ beforeInc _ t₅ hinc
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (affineBoolEqRevCoreSteps (right + 1) left right)
    _ (affineBoolEqBodyCfg (right + 1) left right notOutput) _ t₆ heq
  convert full using 1
  · simp [affineCellGateStream, notOutput, List.reverse_append,
      List.append_assoc]
  · simp [affineCellRevCoreSteps]
    omega

/-- Standalone wrapper: execute the redirectable cell core and then take the
ordinary successful-halt instruction. -/
def affineCellRev_runFrom (right left blank : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineCellBodyCfg right left blank output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((affineCellGateStream right left blank).reverse ++ output)))
      (affineCellRevSteps right left blank) := by
  let beforeHalt := sequentialExactlyOneCfg .halt none none false []
    ((affineCellGateStream right left blank).reverse ++ output)
    [] [] [] [] []
  have hcore := affineCellRev_runToHaltLabel right left blank output
  have hhalt : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeHalt
      (some (haltCfg sequentialExactlyOneRevProgram
        ((affineCellGateStream right left blank).reverse ++ output))) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (affineCellRevCoreSteps right left blank) 1 _ beforeHalt _ hcore hhalt
  convert full using 1
  simp [affineCellRevCoreSteps, affineCellRevSteps,
    affineBoolEqRevCoreSteps, affineBoolEqRevSteps]
  omega

/-- Uniform quadratic envelope for one composed cell invocation. -/
theorem affineCellRev_steps_le (right left blank : Nat) :
    affineCellRevSteps right left blank ≤
      200 * (right + left + blank + 1) ^ 2 := by
  simp [affineCellRevSteps, affineBoolEqRevSteps]
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
