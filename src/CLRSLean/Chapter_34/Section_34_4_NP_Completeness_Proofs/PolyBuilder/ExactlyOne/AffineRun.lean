import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineTrace

/-!
# Contextual affine sequential exactly-one serialization

This module will connect the affine arithmetic trace to the concrete
counter-based builder program.  The pure trace is imported separately so its
interface can be checked before the longer execution proof is added.
-/

namespace CLRS.Chapter34.Turing.PolyBuilder

open StateTransition

/-- Contextual body entry with affine gate/source bases and an arbitrary
pre-existing output suffix. -/
def affineSequentialExactlyOneBodyCfg
    (start rowBase count : Nat) (output : List CircuitSym) :
    BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg .nextFirst none none false []
    ([.constFalseMark, .constFalseMark] ++ output)
    (List.replicate count ()) []
    (List.replicate start ())
    (List.replicate (start + 2) ())
    (List.replicate (rowBase + count) ())

/-! ## Affine scan blocks -/

private def affineFirstGatePhase (start wire : Nat)
    (buffer₁ : Option Unit) (work₁ : List Unit)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .pushFirstAnd buffer₁ none true [] output
        work₁ [] (List.replicate start ())
        (List.replicate (start + 2) ()) (List.replicate wire ()))
      (some (sequentialExactlyOneCfg .clearSeen buffer₁ none false []
        (((AffineExactlyOne.firstChunk start wire).flatMap
          encodeCircuitGate).reverse ++ output)
        work₁ [] (List.replicate start ())
        (List.replicate (start + 2) ()) (List.replicate wire ())))
      (20 * start + 10 * wire + 41) := by
  let c₀ := sequentialExactlyOneCfg (.encode .seen .firstASeen)
    buffer₁ none true [] (.andMark :: output) work₁ []
    (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate wire ())
  have hpushA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .pushFirstAnd buffer₁ none true [] output
        work₁ [] (List.replicate start ())
        (List.replicate (start + 2) ()) (List.replicate wire ()))
      (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.resume .firstASeen)
    buffer₁ none false [] ((encNat start).reverse ++ .andMark :: output)
    work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hseenA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) (5 * start + 3) := by
    simpa [c₀, c₁] using
      encodeSeen_run start .firstASeen buffer₁ true [] (.andMark :: output)
        work₁ (List.replicate (start + 2) ()) (List.replicate wire ())
  let c₂ := sequentialExactlyOneCfg (.encode .wire .firstAWire)
    buffer₁ none false [] ((encNat start).reverse ++ .andMark :: output)
    work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hjumpWireA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let outA := (encodeCircuitGate (.and start wire)).reverse ++ output
  let c₃ := sequentialExactlyOneCfg (.resume .firstAWire)
    buffer₁ none false [] outA work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hwireA : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) (5 * wire + 3) := by
    simpa [c₂, c₃, outA, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run wire .firstAWire buffer₁ false []
        ((encNat start).reverse ++ .andMark :: output) work₁
        (List.replicate start ()) (List.replicate (start + 2) ())
  let c₄ := sequentialExactlyOneCfg .incFirstDuplicate
    buffer₁ none false [] (.orMark :: outA) work₁ []
    (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate wire ())
  have hpushB : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₅ := sequentialExactlyOneCfg (.encode .seen .firstBDuplicate)
    buffer₁ none false [] (.orMark :: outA) work₁ []
    (List.replicate (start + 1) ()) (List.replicate (start + 2) ())
    (List.replicate wire ())
  have hincDuplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₄ = some c₅
    unfold c₄ c₅
    rw [List.replicate_succ]
    rfl
  let c₆ := sequentialExactlyOneCfg (.resume .firstBDuplicate)
    buffer₁ none false []
    ((encNat (start + 1)).reverse ++ .orMark :: outA) work₁ []
    (List.replicate (start + 1) ()) (List.replicate (start + 2) ())
    (List.replicate wire ())
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) (5 * (start + 1) + 3) := by
    simpa [c₅, c₆] using
      encodeSeen_run (start + 1) .firstBDuplicate buffer₁ false []
        (.orMark :: outA) work₁ (List.replicate (start + 2) ())
        (List.replicate wire ())
  let c₇ := sequentialExactlyOneCfg (.encode .next .firstBNext)
    buffer₁ none true []
    ((encNat (start + 1)).reverse ++ .orMark :: outA) work₁ []
    (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate wire ())
  have hrestoreDuplicate : EvalsToInTime
      (step sequentialExactlyOneRevProgram) c₆ (some c₇) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₆ = some c₇
    unfold c₆ c₇
    rw [List.replicate_succ]
    rfl
  let outB :=
    (encodeCircuitGate (.or (start + 1) (start + 2))).reverse ++ outA
  let c₈ := sequentialExactlyOneCfg (.resume .firstBNext)
    buffer₁ none false [] outB work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hnextB : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) (5 * (start + 2) + 3) := by
    simpa [c₇, c₈, outB, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run (start + 2) .firstBNext buffer₁ true []
        ((encNat (start + 1)).reverse ++ .orMark :: outA) work₁
        (List.replicate start ()) (List.replicate wire ())
  let c₉ := sequentialExactlyOneCfg (.encode .seen .firstCSeen)
    buffer₁ none false [] (.orMark :: outB) work₁ []
    (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate wire ())
  have hpushC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some c₉) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁₀ := sequentialExactlyOneCfg (.resume .firstCSeen)
    buffer₁ none false [] ((encNat start).reverse ++ .orMark :: outB)
    work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hseenC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₉ (some c₁₀) (5 * start + 3) := by
    simpa [c₉, c₁₀] using
      encodeSeen_run start .firstCSeen buffer₁ false [] (.orMark :: outB)
        work₁ (List.replicate (start + 2) ()) (List.replicate wire ())
  let c₁₁ := sequentialExactlyOneCfg (.encode .wire .firstCWire)
    buffer₁ none false [] ((encNat start).reverse ++ .orMark :: outB)
    work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hjumpWireC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₀ (some c₁₁) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let outC := (encodeCircuitGate (.or start wire)).reverse ++ outB
  let c₁₂ := sequentialExactlyOneCfg (.resume .firstCWire)
    buffer₁ none false [] outC work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hwireC : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₁ (some c₁₂) (5 * wire + 3) := by
    simpa [c₁₁, c₁₂, outC, encodeCircuitGate,
      List.reverse_append, List.append_assoc] using
      encodeWire_run wire .firstCWire buffer₁ false []
        ((encNat start).reverse ++ .orMark :: outB) work₁
        (List.replicate start ()) (List.replicate (start + 2) ())
  let finalCfg := sequentialExactlyOneCfg .clearSeen
    buffer₁ none false [] outC work₁ [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate wire ())
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁₂ (some finalCfg) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 (5 * start + 3) _ c₀ _ hpushA hseenA
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * start + 3) + 1) 1 _ c₁ _ h₁ hjumpWireA
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * start + 3) + 1)) (5 * wire + 3) _ c₂ _ h₂ hwireA
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    ((5 * wire + 3) + (1 + ((5 * start + 3) + 1))) 1 _ c₃ _ h₃ hpushB
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + ((5 * wire + 3) + (1 + ((5 * start + 3) + 1)))) 1
    _ c₄ _ h₄ hincDuplicate
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (1 + (1 + ((5 * wire + 3) + (1 + ((5 * start + 3) + 1)))))
    (5 * (start + 1) + 3) _ c₅ _ h₅ hduplicate
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₆ _ h₆ hrestoreDuplicate
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * (start + 2) + 3) _ c₇ _ h₇ hnextB
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₈ _ h₈ hpushC
  let h₁₀ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * start + 3) _ c₉ _ h₉ hseenC
  let h₁₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁₀ _ h₁₀ hjumpWireC
  let h₁₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * wire + 3) _ c₁₁ _ h₁₁ hwireC
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁₂ _ h₁₂ hjumpClear
  convert full using 1
  · simp [finalCfg, outC, outB, outA, AffineExactlyOne.firstChunk,
      List.reverse_append, List.append_assoc]
  · omega

private def affineLaterGatePhase (start phase wire : Nat)
    (buffer₁ : Option Unit) (work₁ : List Unit)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .pushLaterAnd buffer₁ none true [] output
        work₁ [] (List.replicate (start + 3 * phase + 1) ())
        (List.replicate (start + 3 * phase + 2) ())
        (List.replicate wire ()))
      (some (sequentialExactlyOneCfg .clearSeen buffer₁ none false []
        (((AffineExactlyOne.laterChunk start phase wire).flatMap
          encodeCircuitGate).reverse ++ output)
        work₁ [] (List.replicate (start + 3 * phase + 1) ())
        (List.replicate (start + 3 * phase + 2) ())
        (List.replicate wire ())))
      (20 * start + 60 * phase + 10 * wire + 46) := by
  let seen := start + 3 * phase + 1
  let next := start + 3 * phase + 2
  let duplicate := start + 3 * phase
  have hseen : seen = duplicate + 1 := by omega
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
    (List.replicate duplicate ()) (List.replicate next ())
    (List.replicate wire ())
  have hdecDuplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₄ = some c₅
    unfold c₄ c₅
    rw [hseen, List.replicate_succ]
    rfl
  let c₆ := sequentialExactlyOneCfg (.resume .laterBDuplicate)
    buffer₁ none false []
    ((encNat duplicate).reverse ++ .orMark :: outA) work₁ []
    (List.replicate duplicate ()) (List.replicate next ())
    (List.replicate wire ())
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) (5 * duplicate + 3) := by
    simpa [c₅, c₆] using
      encodeSeen_run duplicate .laterBDuplicate buffer₁ true []
        (.orMark :: outA) work₁ (List.replicate next ())
        (List.replicate wire ())
  let c₇ := sequentialExactlyOneCfg (.encode .next .laterBNext)
    buffer₁ none false []
    ((encNat duplicate).reverse ++ .orMark :: outA) work₁ []
    (List.replicate seen ()) (List.replicate next ())
    (List.replicate wire ())
  have hrestoreDuplicate : EvalsToInTime
      (step sequentialExactlyOneRevProgram) c₆ (some c₇) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₆ = some c₇
    unfold c₆ c₇
    rw [hseen, List.replicate_succ]
    rfl
  let outB := (encodeCircuitGate (.or duplicate next)).reverse ++ outA
  let c₈ := sequentialExactlyOneCfg (.resume .laterBNext)
    buffer₁ none false [] outB work₁ [] (List.replicate seen ())
    (List.replicate next ()) (List.replicate wire ())
  have hnextB : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) (5 * next + 3) := by
    simpa [c₇, c₈, outB, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run next .laterBNext buffer₁ false []
        ((encNat duplicate).reverse ++ .orMark :: outA) work₁
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
    simpa [c₁₁, c₁₂, outC, encodeCircuitGate,
      List.reverse_append, List.append_assoc] using
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
    _ 1 _ c₁ _ h₁ hjumpWireA
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * wire + 3) _ c₂ _ h₂ hwireA
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₃ _ h₃ hpushB
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₄ _ h₄ hdecDuplicate
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * duplicate + 3) _ c₅ _ h₅ hduplicate
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₆ _ h₆ hrestoreDuplicate
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * next + 3) _ c₇ _ h₇ hnextB
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₈ _ h₈ hpushC
  let h₁₀ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * seen + 3) _ c₉ _ h₉ hseenC
  let h₁₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁₀ _ h₁₀ hjumpWireC
  let h₁₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * wire + 3) _ c₁₁ _ h₁₁ hwireC
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁₂ _ h₁₂ hjumpClear
  convert full using 1
  · simp [finalCfg, outC, outB, outA, seen, next, duplicate,
      AffineExactlyOne.laterChunk, List.reverse_append, List.append_assoc]
  · simp [seen, next, duplicate]
    omega

/-! ## Affine block loop -/

private def affineSequentialExactlyOneLaterSteps
    (start rowBase : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | phase, remaining + 1 =>
      (26 * start + 78 * phase + 10 * rowBase + 10 * remaining + 67) +
        affineSequentialExactlyOneLaterSteps start rowBase
          (phase + 1) remaining

private def affineSequentialExactlyOneLaterPhases
    (start rowBase phase remaining : Nat) (output : List CircuitSym)
    (hphase : 0 < phase) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .nextLater (some ()) none false [] output
        (List.replicate remaining ()) []
        (List.replicate (start + 3 * phase + 1) ())
        (List.replicate (start + 3 * phase + 2) ())
        (List.replicate (rowBase + remaining) ()))
      (some (sequentialExactlyOneCfg .nextLater (some ()) none false []
        (((AffineExactlyOne.chunksFrom start rowBase phase remaining).flatMap
          encodeCircuitGate).reverse ++ output) [] []
        (List.replicate (start + 3 * (phase + remaining) + 1) ())
        (List.replicate (start + 3 * (phase + remaining) + 2) ())
        (List.replicate rowBase ())))
      (affineSequentialExactlyOneLaterSteps start rowBase phase remaining) := by
  induction remaining generalizing phase output with
  | zero =>
      exact ⟨⟨0, by
        simp [AffineExactlyOne.chunksFrom]⟩, le_rfl⟩
  | succ remaining ih =>
      let afterPop := sequentialExactlyOneCfg .decLaterWire (some ()) none
        false [] output (List.replicate remaining ()) []
        (List.replicate (start + 3 * phase + 1) ())
        (List.replicate (start + 3 * phase + 2) ())
        (List.replicate (rowBase + remaining + 1) ())
      have hpop : EvalsToInTime (step sequentialExactlyOneRevProgram)
          (sequentialExactlyOneCfg .nextLater (some ()) none false [] output
            (List.replicate (remaining + 1) ()) []
            (List.replicate (start + 3 * phase + 1) ())
            (List.replicate (start + 3 * phase + 2) ())
            (List.replicate (rowBase + remaining + 1) ()))
          (some afterPop) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step sequentialExactlyOneRevProgram
          (sequentialExactlyOneCfg .nextLater (some ()) none false [] output
            (List.replicate (remaining + 1) ()) []
            (List.replicate (start + 3 * phase + 1) ())
            (List.replicate (start + 3 * phase + 2) ())
            (List.replicate (rowBase + remaining + 1) ())) = some afterPop
        unfold afterPop
        rw [List.replicate_succ]
        rfl
      let beforeGates := sequentialExactlyOneCfg .pushLaterAnd (some ()) none
        true [] output (List.replicate remaining ()) []
        (List.replicate (start + 3 * phase + 1) ())
        (List.replicate (start + 3 * phase + 2) ())
        (List.replicate (rowBase + remaining) ())
      have hdec : EvalsToInTime (step sequentialExactlyOneRevProgram)
          afterPop (some beforeGates) 1 := by
        refine ⟨⟨1, ?_⟩, le_rfl⟩
        change step sequentialExactlyOneRevProgram afterPop = some beforeGates
        unfold afterPop beforeGates
        rw [List.replicate_succ]
        rfl
      let chunkOutput :=
        ((AffineExactlyOne.laterChunk start phase
          (rowBase + remaining)).flatMap encodeCircuitGate).reverse ++ output
      let beforeUpdate := sequentialExactlyOneCfg .clearSeen (some ()) none
        false [] chunkOutput (List.replicate remaining ()) []
        (List.replicate (start + 3 * phase + 1) ())
        (List.replicate (start + 3 * phase + 2) ())
        (List.replicate (rowBase + remaining) ())
      have hgates : EvalsToInTime (step sequentialExactlyOneRevProgram)
          beforeGates (some beforeUpdate)
            (20 * start + 60 * phase + 10 * (rowBase + remaining) + 46) := by
        simpa [beforeGates, beforeUpdate, chunkOutput] using
          affineLaterGatePhase start phase (rowBase + remaining) (some ())
            (List.replicate remaining ()) output
      let afterUpdate := sequentialExactlyOneCfg .nextLater (some ()) none
        false [] chunkOutput (List.replicate remaining ()) []
        (List.replicate (start + 3 * (phase + 1) + 1) ())
        (List.replicate (start + 3 * (phase + 1) + 2) ())
        (List.replicate (rowBase + remaining) ())
      have hupdate : EvalsToInTime (step sequentialExactlyOneRevProgram)
          beforeUpdate (some afterUpdate)
            ((start + 3 * phase + 1) +
              5 * (start + 3 * phase + 2) + 8) := by
        convert updateScanRegisters (start + 3 * phase + 1)
          (start + 3 * phase + 2) (rowBase + remaining) (some ())
          (List.replicate remaining ()) chunkOutput using 1 <;>
          simp [afterUpdate, Nat.mul_add, Nat.add_assoc] <;> omega
      have hremaining := ih (phase + 1) chunkOutput (by omega)
      let throughPop := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        1 1 _ afterPop _ hpop hdec
      let throughGates := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram) 2
        (20 * start + 60 * phase + 10 * (rowBase + remaining) + 46)
        _ beforeGates _ throughPop hgates
      let throughUpdate := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram) _
        ((start + 3 * phase + 1) +
          5 * (start + 3 * phase + 2) + 8)
        _ beforeUpdate _ throughGates hupdate
      let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        _ (affineSequentialExactlyOneLaterSteps start rowBase
          (phase + 1) remaining)
        _ afterUpdate _ throughUpdate hremaining
      have hsteps :
          affineSequentialExactlyOneLaterSteps start rowBase
                (phase + 1) remaining +
              ((start + 3 * phase + 1) +
                5 * (start + 3 * phase + 2) + 8 +
                (20 * start + 60 * phase +
                  10 * (rowBase + remaining) + 46 + 2)) =
            affineSequentialExactlyOneLaterSteps start rowBase phase
              (remaining + 1) := by
        change
          affineSequentialExactlyOneLaterSteps start rowBase
                (phase + 1) remaining +
              ((start + 3 * phase + 1) +
                5 * (start + 3 * phase + 2) + 8 +
                (20 * start + 60 * phase +
                  10 * (rowBase + remaining) + 46 + 2)) =
            (26 * start + 78 * phase + 10 * rowBase +
                10 * remaining + 67) +
              affineSequentialExactlyOneLaterSteps start rowBase
                (phase + 1) remaining
        omega
      rw [← hsteps]
      simpa [afterUpdate, chunkOutput, AffineExactlyOne.chunksFrom,
        AffineExactlyOne.chunk, Nat.ne_of_gt hphase,
        List.flatMap_append, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using full

private def affineSequentialExactlyOnePositivePhases
    (start rowBase remaining : Nat) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .nextFirst none none false [] output
        (List.replicate (remaining + 1) ()) []
        (List.replicate start ()) (List.replicate (start + 2) ())
        (List.replicate (rowBase + remaining + 1) ()))
      (some (sequentialExactlyOneCfg .nextLater (some ()) none false []
        (((AffineExactlyOne.chunksFrom start rowBase 0
          (remaining + 1)).flatMap encodeCircuitGate).reverse ++ output)
        [] [] (List.replicate (start + 3 * (remaining + 1) + 1) ())
        (List.replicate (start + 3 * (remaining + 1) + 2) ())
        (List.replicate rowBase ())))
      (affineSequentialExactlyOneLaterSteps start rowBase 1 remaining +
        26 * start + 10 * rowBase + 10 * remaining + 61) := by
  let afterPop := sequentialExactlyOneCfg .decFirstWire (some ()) none false []
    output (List.replicate remaining ()) [] (List.replicate start ())
    (List.replicate (start + 2) ())
    (List.replicate (rowBase + remaining + 1) ())
  have hpop : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .nextFirst none none false [] output
        (List.replicate (remaining + 1) ()) [] (List.replicate start ())
        (List.replicate (start + 2) ())
        (List.replicate (rowBase + remaining + 1) ()))
      (some afterPop) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram
      (sequentialExactlyOneCfg .nextFirst none none false [] output
        (List.replicate (remaining + 1) ()) [] (List.replicate start ())
        (List.replicate (start + 2) ())
        (List.replicate (rowBase + remaining + 1) ())) = some afterPop
    unfold afterPop
    rw [List.replicate_succ]
    rfl
  let beforeFirst := sequentialExactlyOneCfg .pushFirstAnd (some ()) none true []
    output (List.replicate remaining ()) [] (List.replicate start ())
    (List.replicate (start + 2) ())
    (List.replicate (rowBase + remaining) ())
  have hdec : EvalsToInTime (step sequentialExactlyOneRevProgram)
      afterPop (some beforeFirst) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram afterPop = some beforeFirst
    unfold afterPop beforeFirst
    rw [List.replicate_succ]
    rfl
  let firstOutput :=
    ((AffineExactlyOne.firstChunk start (rowBase + remaining)).flatMap
      encodeCircuitGate).reverse ++ output
  let beforeUpdate := sequentialExactlyOneCfg .clearSeen (some ()) none false []
    firstOutput (List.replicate remaining ()) [] (List.replicate start ())
    (List.replicate (start + 2) ())
    (List.replicate (rowBase + remaining) ())
  have hfirst : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeFirst (some beforeUpdate)
        (20 * start + 10 * (rowBase + remaining) + 41) := by
    simpa [beforeFirst, beforeUpdate, firstOutput] using
      affineFirstGatePhase start (rowBase + remaining) (some ())
        (List.replicate remaining ()) output
  let afterUpdate := sequentialExactlyOneCfg .nextLater (some ()) none false []
    firstOutput (List.replicate remaining ()) []
    (List.replicate (start + 4) ()) (List.replicate (start + 5) ())
    (List.replicate (rowBase + remaining) ())
  have hupdate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeUpdate (some afterUpdate) (6 * start + 18) := by
    convert updateScanRegisters start (start + 2) (rowBase + remaining)
      (some ()) (List.replicate remaining ()) firstOutput using 1 <;>
      simp [beforeUpdate, afterUpdate] <;> omega
  have hlater := affineSequentialExactlyOneLaterPhases
    start rowBase 1 remaining firstOutput (by omega)
  let throughPop := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 1 _ afterPop _ hpop hdec
  let throughFirst := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    2 (20 * start + 10 * (rowBase + remaining) + 41)
    _ beforeFirst _ throughPop hfirst
  let throughUpdate := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (6 * start + 18) _ beforeUpdate _ throughFirst hupdate
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (affineSequentialExactlyOneLaterSteps start rowBase 1 remaining)
    _ afterUpdate _ throughUpdate hlater
  convert full using 1
  · simp [afterUpdate, firstOutput, AffineExactlyOne.chunksFrom,
      AffineExactlyOne.chunk, List.flatMap_append, List.reverse_append,
      List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  · omega

/-! ## Affine final gates -/

private def affineSequentialExactlyOneFinalZeroToHaltLabel
    (start rowBase : Nat) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalZero none none false [] output [] []
        (List.replicate start ()) (List.replicate (start + 2) ())
        (List.replicate rowBase ()))
      (some (sequentialExactlyOneCfg .halt none none false []
        (([.not (start + 1), .and start (start + 2)].flatMap
          encodeCircuitGate).reverse ++ output) [] [] [] [] []))
      (17 * start + rowBase + 36) := by
  let c₀ := sequentialExactlyOneCfg .incFinalZeroDuplicate none none false []
    (.notMark :: output) [] [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate rowBase ())
  have hnot : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalZero none none false [] output [] []
        (List.replicate start ()) (List.replicate (start + 2) ())
        (List.replicate rowBase ())) (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.encode .seen .finalZeroDuplicate)
    none none false [] (.notMark :: output) [] []
    (List.replicate (start + 1) ()) (List.replicate (start + 2) ())
    (List.replicate rowBase ())
  have hinc : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₀ = some c₁
    unfold c₀ c₁
    rw [show start + 1 = Nat.succ start by omega, List.replicate_succ]
    rfl
  let c₂ := sequentialExactlyOneCfg (.resume .finalZeroDuplicate)
    none none false [] ((encNat (start + 1)).reverse ++ .notMark :: output)
    [] [] (List.replicate (start + 1) ())
    (List.replicate (start + 2) ()) (List.replicate rowBase ())
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) (5 * (start + 1) + 3) := by
    simpa [c₁, c₂] using
      encodeSeen_run (start + 1) .finalZeroDuplicate none false []
        (.notMark :: output) [] (List.replicate (start + 2) ())
        (List.replicate rowBase ())
  let c₃ := sequentialExactlyOneCfg .restoreFinalZeroDuplicate none none
    false [] ((encNat (start + 1)).reverse ++ .notMark :: output)
    [] [] (List.replicate (start + 1) ())
    (List.replicate (start + 2) ()) (List.replicate rowBase ())
  have hjump : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₄ := sequentialExactlyOneCfg .pushFinalAnd none none true []
    ((encNat (start + 1)).reverse ++ .notMark :: output)
    [] [] (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate rowBase ())
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₃ = some c₄
    unfold c₃ c₄
    rw [show start + 1 = Nat.succ start by omega, List.replicate_succ]
    rfl
  let c₅ := sequentialExactlyOneCfg (.encode .seen .finalSeen) none none true []
    (.andMark :: (encNat (start + 1)).reverse ++ .notMark :: output)
    [] [] (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate rowBase ())
  have hand : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₆ := sequentialExactlyOneCfg (.resume .finalSeen) none none false []
    ((encNat start).reverse ++ .andMark ::
      (encNat (start + 1)).reverse ++ .notMark :: output)
    [] [] (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate rowBase ())
  have hseen : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) (5 * start + 3) := by
    simpa [c₅, c₆] using encodeSeen_run start .finalSeen none true []
      (.andMark :: (encNat (start + 1)).reverse ++ .notMark :: output)
      [] (List.replicate (start + 2) ()) (List.replicate rowBase ())
  let c₇ := sequentialExactlyOneCfg (.encode .next .finalNext) none none false []
    ((encNat start).reverse ++ .andMark ::
      (encNat (start + 1)).reverse ++ .notMark :: output)
    [] [] (List.replicate start ()) (List.replicate (start + 2) ())
    (List.replicate rowBase ())
  have hjumpNext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₆ (some c₇) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let finalOutput :=
    (([.not (start + 1), .and start (start + 2)].flatMap
      encodeCircuitGate).reverse ++ output)
  let c₈ := sequentialExactlyOneCfg (.resume .finalNext) none none false []
    finalOutput [] [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate rowBase ())
  have hnext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) (5 * (start + 2) + 3) := by
    simpa [c₇, c₈, finalOutput, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run (start + 2) .finalNext none false []
        ((encNat start).reverse ++ .andMark ::
          (encNat (start + 1)).reverse ++ .notMark :: output)
        [] (List.replicate start ()) (List.replicate rowBase ())
  let beforeClear := sequentialExactlyOneCfg .clear₁ none none false []
    finalOutput [] [] (List.replicate start ())
    (List.replicate (start + 2) ()) (List.replicate rowBase ())
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear (some (sequentialExactlyOneCfg .halt none none false []
        finalOutput [] [] [] [] [])) (2 * start + rowBase + 5) := by
    convert clearAllRegistersToHaltLabel start (start + 2) rowBase none
      finalOutput using 1 <;> simp [beforeClear] <;> omega
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 1 _ c₀ _ hnot hinc
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * (start + 1) + 3) _ c₁ _ h₁ hduplicate
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₂ _ h₂ hjump
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₃ _ h₃ hrestore
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₄ _ h₄ hand
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * start + 3) _ c₅ _ h₅ hseen
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₆ _ h₆ hjumpNext
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * (start + 2) + 3) _ c₇ _ h₇ hnext
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₈ _ h₈ hjumpClear
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (2 * start + rowBase + 5) _ beforeClear _ h₉ hclear
  convert full using 1 <;> simp [finalOutput] <;> omega

private def affineSequentialExactlyOneFinalSomeToHaltLabel
    (start rowBase count : Nat) (_hcount : 0 < count)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalSome none none false [] output [] []
        (List.replicate (start + 3 * count + 1) ())
        (List.replicate (start + 3 * count + 2) ())
        (List.replicate rowBase ()))
      (some (sequentialExactlyOneCfg .halt none none false []
        (([.not (start + 3 * count),
            .and (start + 3 * count + 1) (start + 3 * count + 2)].flatMap
          encodeCircuitGate).reverse ++ output) [] [] [] [] []))
      (17 * start + 51 * count + rowBase + 37) := by
  let seen := start + 3 * count + 1
  let next := start + 3 * count + 2
  let duplicate := start + 3 * count
  have hseen : seen = duplicate + 1 := by simp [seen, duplicate]
  let c₀ := sequentialExactlyOneCfg .decFinalSomeDuplicate none none false []
    (.notMark :: output) [] [] (List.replicate seen ())
    (List.replicate next ()) (List.replicate rowBase ())
  have hnot : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (sequentialExactlyOneCfg .finalSome none none false [] output [] []
        (List.replicate seen ()) (List.replicate next ())
        (List.replicate rowBase ())) (some c₀) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₁ := sequentialExactlyOneCfg (.encode .seen .finalSomeDuplicate)
    none none true [] (.notMark :: output) [] []
    (List.replicate duplicate ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hdec : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₀ = some c₁
    unfold c₀ c₁
    rw [hseen, List.replicate_succ]
    rfl
  let c₂ := sequentialExactlyOneCfg (.resume .finalSomeDuplicate)
    none none false [] ((encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate duplicate ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hduplicate : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some c₂) (5 * duplicate + 3) := by
    simpa [c₁, c₂] using
      encodeSeen_run duplicate .finalSomeDuplicate none true []
        (.notMark :: output) [] (List.replicate next ())
        (List.replicate rowBase ())
  let c₃ := sequentialExactlyOneCfg .restoreFinalSomeDuplicate none none
    false [] ((encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate duplicate ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hjump : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₂ (some c₃) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₄ := sequentialExactlyOneCfg .pushFinalAnd none none false []
    ((encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hrestore : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₃ (some c₄) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change step sequentialExactlyOneRevProgram c₃ = some c₄
    unfold c₃ c₄
    rw [hseen, List.replicate_succ]
    rfl
  let c₅ := sequentialExactlyOneCfg (.encode .seen .finalSeen) none none false []
    (.andMark :: (encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hand : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₄ (some c₅) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let c₆ := sequentialExactlyOneCfg (.resume .finalSeen) none none false []
    ((encNat seen).reverse ++ .andMark ::
      (encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hencodeSeen : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₅ (some c₆) (5 * seen + 3) := by
    simpa [c₅, c₆] using encodeSeen_run seen .finalSeen none false []
      (.andMark :: (encNat duplicate).reverse ++ .notMark :: output)
      [] (List.replicate next ()) (List.replicate rowBase ())
  let c₇ := sequentialExactlyOneCfg (.encode .next .finalNext) none none false []
    ((encNat seen).reverse ++ .andMark ::
      (encNat duplicate).reverse ++ .notMark :: output)
    [] [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hjumpNext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₆ (some c₇) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let finalOutput :=
    (([.not duplicate, .and seen next].flatMap encodeCircuitGate).reverse ++
      output)
  let c₈ := sequentialExactlyOneCfg (.resume .finalNext) none none false []
    finalOutput [] [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hencodeNext : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₇ (some c₈) (5 * next + 3) := by
    simpa [c₇, c₈, finalOutput, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeNext_run next .finalNext none false []
        ((encNat seen).reverse ++ .andMark ::
          (encNat duplicate).reverse ++ .notMark :: output)
        [] (List.replicate seen ()) (List.replicate rowBase ())
  let beforeClear := sequentialExactlyOneCfg .clear₁ none none false []
    finalOutput [] [] (List.replicate seen ()) (List.replicate next ())
    (List.replicate rowBase ())
  have hjumpClear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₈ (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear (some (sequentialExactlyOneCfg .halt none none false []
        finalOutput [] [] [] [] [])) (seen + next + rowBase + 3) := by
    simpa [beforeClear] using
      clearAllRegistersToHaltLabel seen next rowBase none finalOutput
  let h₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 1 _ c₀ _ hnot hdec
  let h₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * duplicate + 3) _ c₁ _ h₁ hduplicate
  let h₃ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₂ _ h₂ hjump
  let h₄ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₃ _ h₃ hrestore
  let h₅ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₄ _ h₄ hand
  let h₆ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * seen + 3) _ c₅ _ h₅ hencodeSeen
  let h₇ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₆ _ h₆ hjumpNext
  let h₈ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (5 * next + 3) _ c₇ _ h₇ hencodeNext
  let h₉ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₈ _ h₈ hjumpClear
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (seen + next + rowBase + 3) _ beforeClear _ h₉ hclear
  convert full using 1 <;>
    simp [finalOutput, seen, next, duplicate] <;> omega

/-! ## Complete contextual serializer -/

/-- Clean public endpoint before the standalone serializer executes its final
halt instruction.  Family controllers redirect this label to the next framed
group. -/
def affineSequentialExactlyOneHaltLabelCfg (output : List CircuitSym) :
    BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg .halt none none false [] output [] [] [] [] []

/-- Exact core cost through the clean redirectable halt label. -/
def affineSequentialExactlyOneRevCoreSteps
    (start rowBase count : Nat) : Nat :=
  match count with
  | 0 => 1 + (17 * start + rowBase + 36)
  | remaining + 1 =>
      (affineSequentialExactlyOneLaterSteps start rowBase 1 remaining +
          26 * start + 10 * rowBase + 10 * remaining + 61) +
        1 + (17 * start + 51 * (remaining + 1) + rowBase + 37)

/-- Starting at an arbitrary gate/source base, the concrete builder prepends
the reversed canonical affine exactly-one stream to any existing suffix and
stops at the clean redirectable halt label. -/
def affineSequentialExactlyOneRev_runToHaltLabel
    (start rowBase count : Nat) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineSequentialExactlyOneBodyCfg start rowBase count output)
      (some (affineSequentialExactlyOneHaltLabelCfg
        ((affineSequentialExactlyOneGateStream start rowBase count).reverse ++
          output)))
      (affineSequentialExactlyOneRevCoreSteps start rowBase count) := by
  let baseOutput : List CircuitSym :=
    [.constFalseMark, .constFalseMark] ++ output
  cases count with
  | zero =>
      have hdispatch : EvalsToInTime (step sequentialExactlyOneRevProgram)
          (affineSequentialExactlyOneBodyCfg start rowBase 0 output)
          (some (sequentialExactlyOneCfg .finalZero none none false []
            baseOutput [] [] (List.replicate start ())
            (List.replicate (start + 2) ())
            (List.replicate rowBase ()))) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hfinal :=
        affineSequentialExactlyOneFinalZeroToHaltLabel start rowBase baseOutput
      let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        1 (17 * start + rowBase + 36) _
        (sequentialExactlyOneCfg .finalZero none none false []
          baseOutput [] [] (List.replicate start ())
          (List.replicate (start + 2) ()) (List.replicate rowBase ())) _
        hdispatch hfinal
      have hgateList :=
        affineSequentialExactlyOneGateList_eq_trace start rowBase 0
      simp only [affineSequentialExactlyOneGateStream]
      rw [← hgateList]
      simpa [affineSequentialExactlyOneRevCoreSteps,
        affineSequentialExactlyOneHaltLabelCfg,
        AffineExactlyOne.gateList, AffineExactlyOne.chunksFrom,
        AffineExactlyOne.duplicate, AffineExactlyOne.seen, baseOutput,
        encodeCircuitGate, List.flatMap_append, List.reverse_append,
        List.append_assoc, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using full
  | succ remaining =>
      let count := remaining + 1
      have hphases := affineSequentialExactlyOnePositivePhases
        start rowBase remaining baseOutput
      let phaseOutput :=
        (((AffineExactlyOne.chunksFrom start rowBase 0 count).flatMap
          encodeCircuitGate).reverse ++ baseOutput)
      have hdispatch : EvalsToInTime (step sequentialExactlyOneRevProgram)
          (sequentialExactlyOneCfg .nextLater (some ()) none false []
            phaseOutput [] [] (List.replicate (start + 3 * count + 1) ())
            (List.replicate (start + 3 * count + 2) ())
            (List.replicate rowBase ()))
          (some (sequentialExactlyOneCfg .finalSome none none false []
            phaseOutput [] [] (List.replicate (start + 3 * count + 1) ())
            (List.replicate (start + 3 * count + 2) ())
            (List.replicate rowBase ()))) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hfinal := affineSequentialExactlyOneFinalSomeToHaltLabel
        start rowBase count (by omega) phaseOutput
      let throughDispatch := EvalsToInTime.trans
        (step sequentialExactlyOneRevProgram)
        (affineSequentialExactlyOneLaterSteps start rowBase 1 remaining +
          26 * start + 10 * rowBase + 10 * remaining + 61)
        1 _
        (sequentialExactlyOneCfg .nextLater (some ()) none false []
          phaseOutput [] [] (List.replicate (start + 3 * count + 1) ())
          (List.replicate (start + 3 * count + 2) ())
          (List.replicate rowBase ())) _
        (by simpa [affineSequentialExactlyOneBodyCfg, count, phaseOutput,
          baseOutput] using hphases) hdispatch
      let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
        _ (17 * start + 51 * count + rowBase + 37) _
        (sequentialExactlyOneCfg .finalSome none none false []
          phaseOutput [] [] (List.replicate (start + 3 * count + 1) ())
          (List.replicate (start + 3 * count + 2) ())
          (List.replicate rowBase ())) _ throughDispatch hfinal
      have hgateList :=
        affineSequentialExactlyOneGateList_eq_trace start rowBase count
      simp only [affineSequentialExactlyOneGateStream]
      rw [← hgateList]
      simpa [affineSequentialExactlyOneBodyCfg,
        affineSequentialExactlyOneRevCoreSteps,
        affineSequentialExactlyOneHaltLabelCfg, count, phaseOutput, baseOutput,
        AffineExactlyOne.gateList, AffineExactlyOne.duplicate,
        AffineExactlyOne.seen, encodeCircuitGate, List.flatMap_append,
        List.reverse_append, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using full

/-- Exact step count for the standalone contextual serializer, including its
final successful-halt normalization instruction. -/
def affineSequentialExactlyOneRevSteps
    (start rowBase count : Nat) : Nat :=
  affineSequentialExactlyOneRevCoreSteps start rowBase count + 1

/-- Standalone affine exactly-one serialization retains the original public
successful-halt interface as a one-step wrapper around the redirectable core. -/
def affineSequentialExactlyOneRev_runFrom
    (start rowBase count : Nat) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineSequentialExactlyOneBodyCfg start rowBase count output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((affineSequentialExactlyOneGateStream start rowBase count).reverse ++
          output)))
      (affineSequentialExactlyOneRevSteps start rowBase count) := by
  let finalOutput :=
    (affineSequentialExactlyOneGateStream start rowBase count).reverse ++ output
  have hcore := affineSequentialExactlyOneRev_runToHaltLabel
    start rowBase count output
  have hhalt : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineSequentialExactlyOneHaltLabelCfg finalOutput)
      (some (haltCfg sequentialExactlyOneRevProgram finalOutput)) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    (affineSequentialExactlyOneRevCoreSteps start rowBase count) 1 _
    (affineSequentialExactlyOneHaltLabelCfg finalOutput) _ hcore hhalt
  simpa [affineSequentialExactlyOneRevSteps, finalOutput, Nat.add_comm] using full

private theorem affineSequentialExactlyOneLaterSteps_le
    (start rowBase phase remaining : Nat) :
    affineSequentialExactlyOneLaterSteps start rowBase phase remaining ≤
      100 * remaining * (start + rowBase + phase + remaining + 1) := by
  induction remaining generalizing phase with
  | zero => simp [affineSequentialExactlyOneLaterSteps]
  | succ remaining ih =>
      rw [affineSequentialExactlyOneLaterSteps]
      have hrest := ih (phase + 1)
      nlinarith

/-- A uniform quadratic envelope for every affine contextual invocation. -/
theorem affineSequentialExactlyOneRev_steps_le
    (start rowBase count : Nat) :
    affineSequentialExactlyOneRevSteps start rowBase count ≤
      200 * (start + rowBase + count + 1) ^ 2 := by
  cases count with
  | zero =>
      simp [affineSequentialExactlyOneRevSteps,
        affineSequentialExactlyOneRevCoreSteps]
      nlinarith
  | succ remaining =>
      have hlater := affineSequentialExactlyOneLaterSteps_le
        start rowBase 1 remaining
      simp only [affineSequentialExactlyOneRevSteps,
        affineSequentialExactlyOneRevCoreSteps]
      nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
