import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun

/-!
# Contextual Boolean-equality serialization

This module gives the fixed five-gate Boolean-equality trace a concrete
counter-program execution.  The entry configuration is contextual: the first
fresh gate index, both source wires, and the already-produced output suffix are
all arbitrary.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Exact forward encoding of the contextual five-gate Boolean equality. -/
def affineBoolEqGateStream (start left right : Nat) : List CircuitSym :=
  (CircuitBuilder.boolEqGateTrace start left right).gates.flatMap
    encodeCircuitGate

/-- Contextual entry configuration for the reversed Boolean-equality builder. -/
def affineBoolEqBodyCfg (start left right : Nat)
    (output : List CircuitSym) : BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg (.boolEq .notLeft) none none false [] output [] []
    (List.replicate start ()) (List.replicate left ())
    (List.replicate right ())

private theorem boolEq_clearLeft_eval (count : Nat) (test : Bool)
    (output : List CircuitSym) (seen wire : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
      (some (sequentialExactlyOneCfg (.boolEq .clearLeft) none none test []
        output [] [] seen (List.replicate count ()) wire)) =
      some (sequentialExactlyOneCfg (.boolEq .clearRight) none none false []
        output [] [] seen [] wire) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
          (some (sequentialExactlyOneCfg (.boolEq .clearLeft) none none true []
            output [] [] seen (List.replicate count ()) wire)) = _
      simpa [List.replicate_succ] using ih true

private theorem boolEq_clearRight_eval (count : Nat) (test : Bool)
    (output : List CircuitSym) (seen : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
      (some (sequentialExactlyOneCfg (.boolEq .clearRight) none none test []
        output [] [] seen [] (List.replicate count ()))) =
      some (sequentialExactlyOneCfg (.boolEq .copyStart) none none false []
        output [] [] seen [] []) := by
  induction count generalizing test with
  | zero => rfl
  | succ count ih =>
      rw [show count + 1 + 1 = (count + 1) + 1 by omega,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[count + 1]
          (some (sequentialExactlyOneCfg (.boolEq .clearRight) none none true []
            output [] [] seen [] (List.replicate count ()))) = _
      simpa [List.replicate_succ] using ih true

private theorem replicate_append_cons {α : Type} (value : α)
    (count : Nat) (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private theorem boolEq_copyStart_eval (count : Nat) (test : Bool)
    (output : List CircuitSym) (saved copied : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
      (some (sequentialExactlyOneCfg (.boolEq .copyStart) none none test []
        output saved [] (List.replicate count ()) copied [])) =
      some (sequentialExactlyOneCfg (.boolEq .restoreStart) none none false []
        output (List.replicate count () ++ saved) [] []
        (List.replicate count () ++ copied) []) := by
  induction count generalizing test saved copied with
  | zero => rfl
  | succ count ih =>
      rw [show 3 * (count + 1) + 1 = (3 * count + 1) + 1 + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[3 * count + 1]
          (some (sequentialExactlyOneCfg (.boolEq .copyStart) none none true []
            output (() :: saved) [] (List.replicate count ())
            (() :: copied) [])) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih true (() :: saved) (() :: copied)

private theorem boolEq_restoreStart_eval (count : Nat)
    (buffer₁ : Option Unit) (output : List CircuitSym)
    (restored next : List Unit) :
    (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
      (some (sequentialExactlyOneCfg (.boolEq .restoreStart) buffer₁ none false []
        output (List.replicate count ()) [] restored next [])) =
      some (sequentialExactlyOneCfg (.boolEq .incNext) none none false []
        output [] [] (List.replicate count () ++ restored) next []) := by
  induction count generalizing buffer₁ restored with
  | zero => rfl
  | succ count ih =>
      rw [show 2 * (count + 1) + 1 = (2 * count + 1) + 1 + 1 by omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step sequentialExactlyOneRevProgram))^[2 * count + 1]
          (some (sequentialExactlyOneCfg (.boolEq .restoreStart) (some ()) none
            false [] output (List.replicate count ()) [] (() :: restored)
            next [])) = _
      simpa only [List.replicate_succ, replicate_append_cons,
        List.cons_append] using ih (some ()) (() :: restored)

private def affineBoolEq_prepare (start left right : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.boolEq .clearLeft) none none false []
        output [] [] (List.replicate start ()) (List.replicate left ())
        (List.replicate right ()))
      (some (sequentialExactlyOneCfg (.boolEq .andStart) none none false []
        output [] [] (List.replicate start ())
        (List.replicate (start + 1) ()) []))
      (left + right + 5 * start + 5) := by
  let afterLeft := sequentialExactlyOneCfg (.boolEq .clearRight) none none
    false [] output [] [] (List.replicate start ()) []
    (List.replicate right ())
  have hleft : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.boolEq .clearLeft) none none false []
        output [] [] (List.replicate start ()) (List.replicate left ())
        (List.replicate right ()))
      (some afterLeft) (left + 1) := by
    exact ⟨⟨left + 1, by
      simpa [afterLeft] using boolEq_clearLeft_eval left false output
        (List.replicate start ()) (List.replicate right ())⟩, le_rfl⟩
  let afterRight := sequentialExactlyOneCfg (.boolEq .copyStart) none none
    false [] output [] [] (List.replicate start ()) [] []
  have hright : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterLeft (some afterRight) (right + 1) := by
    exact ⟨⟨right + 1, by
      simpa [afterLeft, afterRight] using boolEq_clearRight_eval right false
        output (List.replicate start ())⟩, le_rfl⟩
  let afterCopy := sequentialExactlyOneCfg (.boolEq .restoreStart) none none
    false [] output (List.replicate start ()) [] []
    (List.replicate start ()) []
  have hcopy : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterRight (some afterCopy) (3 * start + 1) := by
    exact ⟨⟨3 * start + 1, by
      simpa [afterRight, afterCopy] using boolEq_copyStart_eval start false
        output [] []⟩, le_rfl⟩
  let beforeInc := sequentialExactlyOneCfg (.boolEq .incNext) none none
    false [] output [] [] (List.replicate start ())
    (List.replicate start ()) []
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterCopy (some beforeInc) (2 * start + 1) := by
    exact ⟨⟨2 * start + 1, by
      simpa [afterCopy, beforeInc] using boolEq_restoreStart_eval start none
        output [] (List.replicate start ())⟩, le_rfl⟩
  let finalCfg := sequentialExactlyOneCfg (.boolEq .andStart) none none
    false [] output [] [] (List.replicate start ())
    (List.replicate (start + 1) ()) []
  have hinc : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeInc (some finalCfg) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram beforeInc = some finalCfg
    unfold beforeInc finalCfg
    rw [List.replicate_succ]
    rfl
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (left + 1) (right + 1) _ afterLeft _ hleft hright
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((right + 1) + (left + 1)) (3 * start + 1) _ afterRight _ h₁ hcopy
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((3 * start + 1) + ((right + 1) + (left + 1))) (2 * start + 1)
    _ afterCopy _ h₂ hrestore
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((2 * start + 1) + ((3 * start + 1) + ((right + 1) + (left + 1))))
    1 _ beforeInc _ h₃ hinc
  convert full using 1 <;> omega

private def affineBoolEq_operandGates (start left right : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineBoolEqBodyCfg start left right output)
      (some (sequentialExactlyOneCfg (.boolEq .clearLeft) none none false []
        (([.not left, .not right, .and left right].flatMap
          encodeCircuitGate).reverse ++ output)
        [] [] (List.replicate start ()) (List.replicate left ())
        (List.replicate right ())))
      (10 * left + 10 * right + 19) := by
  let c₀ := sequentialExactlyOneCfg (.encode .next .boolEqNotLeft)
    none none false [] (.notMark :: output) [] []
    (List.replicate start ()) (List.replicate left ())
    (List.replicate right ())
  have h₀ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineBoolEqBodyCfg start left right output) (some c₀) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let out₁ := (encodeCircuitGate (.not left)).reverse ++ output
  let c₁ := sequentialExactlyOneCfg (.resume .boolEqNotLeft)
    none none false [] out₁ [] [] (List.replicate start ())
    (List.replicate left ()) (List.replicate right ())
  have h₁ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) (5 * left + 3) := by
    simpa [c₀, c₁, out₁, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run left .boolEqNotLeft none false [] (.notMark :: output)
        [] (List.replicate start ()) (List.replicate right ())
  let c₂ := sequentialExactlyOneCfg (.boolEq .notRight)
    none none false [] out₁ [] [] (List.replicate start ())
    (List.replicate left ()) (List.replicate right ())
  have h₂ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₃ := sequentialExactlyOneCfg (.encode .wire .boolEqNotRight)
    none none false [] (.notMark :: out₁) [] []
    (List.replicate start ()) (List.replicate left ())
    (List.replicate right ())
  have h₃ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let out₂ := (encodeCircuitGate (.not right)).reverse ++ out₁
  let c₄ := sequentialExactlyOneCfg (.resume .boolEqNotRight)
    none none false [] out₂ [] [] (List.replicate start ())
    (List.replicate left ()) (List.replicate right ())
  have h₄ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) (5 * right + 3) := by
    simpa [c₃, c₄, out₂, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run right .boolEqNotRight none false [] (.notMark :: out₁)
        [] (List.replicate start ()) (List.replicate left ())
  let c₅ := sequentialExactlyOneCfg (.boolEq .andLeft)
    none none false [] out₂ [] [] (List.replicate start ())
    (List.replicate left ()) (List.replicate right ())
  have h₅ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₆ := sequentialExactlyOneCfg (.encode .next .boolEqAndLeft)
    none none false [] (.andMark :: out₂) [] []
    (List.replicate start ()) (List.replicate left ())
    (List.replicate right ())
  have h₆ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₇ := sequentialExactlyOneCfg (.resume .boolEqAndLeft)
    none none false []
    ((encNat left).reverse ++ .andMark :: out₂) [] []
    (List.replicate start ()) (List.replicate left ())
    (List.replicate right ())
  have h₇ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₆ (some c₇) (5 * left + 3) := by
    simpa [c₆, c₇] using
      encodeNext_run left .boolEqAndLeft none false [] (.andMark :: out₂)
        [] (List.replicate start ()) (List.replicate right ())
  let c₈ := sequentialExactlyOneCfg (.encode .wire .boolEqAndRight)
    none none false []
    ((encNat left).reverse ++ .andMark :: out₂) [] []
    (List.replicate start ()) (List.replicate left ())
    (List.replicate right ())
  have h₈ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let out₃ := (encodeCircuitGate (.and left right)).reverse ++ out₂
  let c₉ := sequentialExactlyOneCfg (.resume .boolEqAndRight)
    none none false [] out₃ [] [] (List.replicate start ())
    (List.replicate left ()) (List.replicate right ())
  have h₉ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some c₉) (5 * right + 3) := by
    simpa [c₈, c₉, out₃, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run right .boolEqAndRight none false []
        ((encNat left).reverse ++ .andMark :: out₂) []
        (List.replicate start ()) (List.replicate left ())
  let finalCfg := sequentialExactlyOneCfg (.boolEq .clearLeft)
    none none false [] out₃ [] [] (List.replicate start ())
    (List.replicate left ()) (List.replicate right ())
  have h₁₀ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₉ (some finalCfg) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let t₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 (5 * left + 3) _ c₀ _ h₀ h₁
  let t₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁ _ t₁ h₂
  let t₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₂ _ t₂ h₃
  let t₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * right + 3) _ c₃ _ t₃ h₄
  let t₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₄ _ t₄ h₅
  let t₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₅ _ t₅ h₆
  let t₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * left + 3) _ c₆ _ t₆ h₇
  let t₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₇ _ t₇ h₈
  let t₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * right + 3) _ c₈ _ t₈ h₉
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₉ _ t₉ h₁₀
  convert full using 1
  · simp [finalCfg, out₃, out₂, out₁, List.reverse_append,
      List.append_assoc]
  · omega

private def affineBoolEq_resultGates (start : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.boolEq .andStart) none none false []
        output [] [] (List.replicate start ())
        (List.replicate (start + 1) ()) [])
      (some (haltCfg sequentialExactlyOneRevProgram
        (([.and start (start + 1), .or (start + 2) (start + 3)].flatMap
          encodeCircuitGate).reverse ++ output)))
      (22 * start + 61) := by
  let c₀ := sequentialExactlyOneCfg (.encode .seen .boolEqAndStart)
    none none false [] (.andMark :: output) [] []
    (List.replicate start ()) (List.replicate (start + 1) ()) []
  have h₀ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg (.boolEq .andStart) none none false []
        output [] [] (List.replicate start ())
        (List.replicate (start + 1) ()) [])
      (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.resume .boolEqAndStart)
    none none false [] ((encNat start).reverse ++ .andMark :: output) [] []
    (List.replicate start ()) (List.replicate (start + 1) ()) []
  have h₁ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) (5 * start + 3) := by
    simpa [c₀, c₁] using
      encodeSeen_run start .boolEqAndStart none false [] (.andMark :: output)
        [] (List.replicate (start + 1) ()) []
  let c₂ := sequentialExactlyOneCfg (.encode .next .boolEqAndNext)
    none none false [] ((encNat start).reverse ++ .andMark :: output) [] []
    (List.replicate start ()) (List.replicate (start + 1) ()) []
  have h₂ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let out₁ := (encodeCircuitGate (.and start (start + 1))).reverse ++ output
  let c₃ := sequentialExactlyOneCfg (.resume .boolEqAndNext)
    none none false [] out₁ [] [] (List.replicate start ())
    (List.replicate (start + 1) ()) []
  have h₃ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) (5 * (start + 1) + 3) := by
    simpa [c₂, c₃, out₁, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run (start + 1) .boolEqAndNext none false []
        ((encNat start).reverse ++ .andMark :: output) []
        (List.replicate start ()) []
  let c₄ := sequentialExactlyOneCfg (.boolEq .incSeen₁)
    none none false [] out₁ [] [] (List.replicate start ())
    (List.replicate (start + 1) ()) []
  have h₄ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₅ := sequentialExactlyOneCfg (.boolEq .incSeen₂)
    none none false [] out₁ [] [] (List.replicate (start + 1) ())
    (List.replicate (start + 1) ()) []
  have h₅ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₄ = some c₅
    unfold c₄ c₅
    rw [List.replicate_succ]
    rfl
  let c₆ := sequentialExactlyOneCfg (.boolEq .incNext₁)
    none none false [] out₁ [] [] (List.replicate (start + 2) ())
    (List.replicate (start + 1) ()) []
  have h₆ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₅ = some c₆
    unfold c₅ c₆
    rw [show start + 2 = (start + 1) + 1 by omega, List.replicate_succ]
    rfl
  let c₇ := sequentialExactlyOneCfg (.boolEq .incNext₂)
    none none false [] out₁ [] [] (List.replicate (start + 2) ())
    (List.replicate (start + 2) ()) []
  have h₇ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₆ (some c₇) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₆ = some c₇
    unfold c₆ c₇
    rw [show start + 2 = (start + 1) + 1 by omega, List.replicate_succ]
    rfl
  let c₈ := sequentialExactlyOneCfg (.boolEq .orStart)
    none none false [] out₁ [] [] (List.replicate (start + 2) ())
    (List.replicate (start + 3) ()) []
  have h₈ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₇ = some c₈
    unfold c₇ c₈
    rw [show start + 3 = (start + 2) + 1 by omega, List.replicate_succ]
    rfl
  let c₉ := sequentialExactlyOneCfg (.encode .seen .boolEqOrStart)
    none none false [] (.orMark :: out₁) [] []
    (List.replicate (start + 2) ()) (List.replicate (start + 3) ()) []
  have h₉ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some c₉) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁₀ := sequentialExactlyOneCfg (.resume .boolEqOrStart)
    none none false [] ((encNat (start + 2)).reverse ++ .orMark :: out₁)
    [] [] (List.replicate (start + 2) ())
    (List.replicate (start + 3) ()) []
  have h₁₀ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₉ (some c₁₀) (5 * (start + 2) + 3) := by
    simpa [c₉, c₁₀] using
      encodeSeen_run (start + 2) .boolEqOrStart none false []
        (.orMark :: out₁) [] (List.replicate (start + 3) ()) []
  let c₁₁ := sequentialExactlyOneCfg (.encode .next .boolEqOrNext)
    none none false [] ((encNat (start + 2)).reverse ++ .orMark :: out₁)
    [] [] (List.replicate (start + 2) ())
    (List.replicate (start + 3) ()) []
  have h₁₁ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₀ (some c₁₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let out₂ :=
    (encodeCircuitGate (.or (start + 2) (start + 3))).reverse ++ out₁
  let c₁₂ := sequentialExactlyOneCfg (.resume .boolEqOrNext)
    none none false [] out₂ [] [] (List.replicate (start + 2) ())
    (List.replicate (start + 3) ()) []
  have h₁₂ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₁ (some c₁₂) (5 * (start + 3) + 3) := by
    simpa [c₁₁, c₁₂, out₂, encodeCircuitGate,
      List.reverse_append, List.append_assoc] using
      encodeNext_run (start + 3) .boolEqOrNext none false []
        ((encNat (start + 2)).reverse ++ .orMark :: out₁) []
        (List.replicate (start + 2) ()) []
  let beforeClear := sequentialExactlyOneCfg .clear₁ none none false []
    out₂ [] [] (List.replicate (start + 2) ())
    (List.replicate (start + 3) ()) []
  have h₁₃ : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₂ (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear (some (haltCfg sequentialExactlyOneRevProgram out₂))
      (2 * start + 9) := by
    convert clearAllRegisters (start + 2) (start + 3) 0 none out₂ using 1
    · rfl
    · omega
  let t₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 (5 * start + 3) _ c₀ _ h₀ h₁
  let t₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁ _ t₁ h₂
  let t₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * (start + 1) + 3) _ c₂ _ t₂ h₃
  let t₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₃ _ t₃ h₄
  let t₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₄ _ t₄ h₅
  let t₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₅ _ t₅ h₆
  let t₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₆ _ t₆ h₇
  let t₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₇ _ t₇ h₈
  let t₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₈ _ t₈ h₉
  let t₁₀ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * (start + 2) + 3) _ c₉ _ t₉ h₁₀
  let t₁₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁₀ _ t₁₀ h₁₁
  let t₁₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * (start + 3) + 3) _ c₁₁ _ t₁₁ h₁₂
  let t₁₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁₂ _ t₁₂ h₁₃
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (2 * start + 9) _ beforeClear _ t₁₃ hclear
  convert full using 1
  · simp [out₂, out₁, List.reverse_append, List.append_assoc]
  · omega

/-! ## Public contextual contract -/

/-- Exact running time of the reversed contextual Boolean-equality builder. -/
def affineBoolEqRevSteps (start left right : Nat) : Nat :=
  27 * start + 11 * left + 11 * right + 85

/-- The public byte stream is definitionally the semantic five-gate trace. -/
theorem affineBoolEqGateStream_eq_trace (start left right : Nat) :
    affineBoolEqGateStream start left right =
      (CircuitBuilder.boolEqGateTrace start left right).gates.flatMap
        encodeCircuitGate := by
  rfl

/-- From arbitrary affine wire indices and an arbitrary existing suffix, the
counter program emits exactly the reversed Boolean-equality encoding and
clears all scratch state before halting. -/
def affineBoolEqRev_runFrom (start left right : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineBoolEqBodyCfg start left right output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((affineBoolEqGateStream start left right).reverse ++ output)))
      (affineBoolEqRevSteps start left right) := by
  let operandStream :=
    [.not left, .not right, .and left right].flatMap encodeCircuitGate
  let operandOutput := operandStream.reverse ++ output
  let afterOperands := sequentialExactlyOneCfg (.boolEq .clearLeft)
    none none false [] operandOutput [] [] (List.replicate start ())
    (List.replicate left ()) (List.replicate right ())
  have hoperands : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineBoolEqBodyCfg start left right output)
      (some afterOperands) (10 * left + 10 * right + 19) := by
    simpa [afterOperands, operandOutput, operandStream] using
      affineBoolEq_operandGates start left right output
  let afterPrepare := sequentialExactlyOneCfg (.boolEq .andStart)
    none none false [] operandOutput [] [] (List.replicate start ())
    (List.replicate (start + 1) ()) []
  have hprepare : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterOperands (some afterPrepare) (left + right + 5 * start + 5) := by
    simpa [afterOperands, afterPrepare] using
      affineBoolEq_prepare start left right operandOutput
  have hresults : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterPrepare
      (some (haltCfg sequentialExactlyOneRevProgram
        (([.and start (start + 1), .or (start + 2) (start + 3)].flatMap
          encodeCircuitGate).reverse ++ operandOutput)))
      (22 * start + 61) := by
    simpa [afterPrepare] using affineBoolEq_resultGates start operandOutput
  let throughPrepare := EvalsToInTime.trans
    (step sequentialExactlyOneRevProgram)
    (10 * left + 10 * right + 19) (left + right + 5 * start + 5)
    _ afterOperands _ hoperands hprepare
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((left + right + 5 * start + 5) + (10 * left + 10 * right + 19))
    (22 * start + 61) _ afterPrepare _ throughPrepare hresults
  convert full using 1
  · simp [affineBoolEqGateStream, CircuitBuilder.boolEqGateTrace,
      operandOutput, operandStream, List.reverse_append, List.append_assoc]
  · simp [affineBoolEqRevSteps]
    omega

/-- A uniform quadratic envelope for contextual Boolean equality. -/
theorem affineBoolEqRev_steps_le (start left right : Nat) :
    affineBoolEqRevSteps start left right ≤
      100 * (start + left + right + 1) ^ 2 := by
  simp [affineBoolEqRevSteps]
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
