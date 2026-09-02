import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.Edges

/-!
# Batch edge lookup: canonical instance header
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup

open PolyBuilder

/-- Move the canonical vertex-count field to work two. -/
def vertexField_run (aggregate : Bool) (vertexCount : Nat)
    (tail : List CliqueSym) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym)) (left right : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.vertexField aggregate) buffer₁ buffer₂ test
        ((prependCliqueTicks vertexCount (.fieldSep :: tail)).map some)
        output work₁ work₂ (List.replicate left ())
        (List.replicate right ()) [])
      (some (cfg (.targetField aggregate) buffer₁ (some (some .fieldSep))
        test (tail.map some) output work₁
        (((prependCliqueTicks vertexCount [.fieldSep]).map some).reverse ++
          work₂)
        (List.replicate left ()) (List.replicate right ()) []))
      (vertexCount + 1) := by
  induction vertexCount generalizing buffer₂ work₂ with
  | zero =>
      exact ⟨⟨1, by simp [flip, prependCliqueTicks, step, program, cfg,
        stepOp]⟩, le_rfl⟩
  | succ vertexCount ih =>
      let after := cfg (.vertexField aggregate) buffer₁
        (some (some .tick)) test
        ((prependCliqueTicks vertexCount (.fieldSep :: tail)).map some)
        output work₁ (some CliqueSym.tick :: work₂)
        (List.replicate left ()) (List.replicate right ()) []
      have first : EvalsToInTime (step program)
          (cfg (.vertexField aggregate) buffer₁ buffer₂ test
            ((prependCliqueTicks (vertexCount + 1)
              (.fieldSep :: tail)).map some) output work₁ work₂
            (List.replicate left ()) (List.replicate right ()) [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, prependCliqueTicks, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some (some CliqueSym.tick))
        (work₂ := some CliqueSym.tick :: work₂)
      let full := EvalsToInTime.trans (step program)
        1 (vertexCount + 1) _ after _ first rest
      simpa [prependCliqueTicks, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Move the canonical target-size field to work two. -/
def targetField_run (aggregate : Bool) (targetSize : Nat)
    (tail : List CliqueSym) (output : List Bool)
    (work₁ work₂ : List (Option CliqueSym)) (left right : Nat)
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.targetField aggregate) buffer₁ buffer₂ test
        ((prependCliqueTicks targetSize (.fieldSep :: tail)).map some)
        output work₁ work₂ (List.replicate left ())
        (List.replicate right ()) [])
      (some (cfg (.edges aggregate) buffer₁ (some (some .fieldSep)) test
        (tail.map some) output work₁
        (((prependCliqueTicks targetSize [.fieldSep]).map some).reverse ++
          work₂)
        (List.replicate left ()) (List.replicate right ()) []))
      (targetSize + 1) := by
  induction targetSize generalizing buffer₂ work₂ with
  | zero =>
      exact ⟨⟨1, by simp [flip, prependCliqueTicks, step, program, cfg,
        stepOp]⟩, le_rfl⟩
  | succ targetSize ih =>
      let after := cfg (.targetField aggregate) buffer₁
        (some (some .tick)) test
        ((prependCliqueTicks targetSize (.fieldSep :: tail)).map some)
        output work₁ (some CliqueSym.tick :: work₂)
        (List.replicate left ()) (List.replicate right ()) []
      have first : EvalsToInTime (step program)
          (cfg (.targetField aggregate) buffer₁ buffer₂ test
            ((prependCliqueTicks (targetSize + 1)
              (.fieldSep :: tail)).map some) output work₁ work₂
            (List.replicate left ()) (List.replicate right ()) [])
          (some after) 1 :=
        ⟨⟨1, by simp [flip, after, prependCliqueTicks, step, program, cfg,
          stepOp]⟩, le_rfl⟩
      have rest := ih (buffer₂ := some (some CliqueSym.tick))
        (work₂ := some CliqueSym.tick :: work₂)
      let full := EvalsToInTime.trans (step program)
        1 (targetSize + 1) _ after _ first rest
      simpa [prependCliqueTicks, List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact cost of moving the canonical graph header to work two. -/
def headerSteps (I : CliqueInstance) : Nat :=
  I.vertexCount + I.targetSize + 3

/-- Parse and preserve the complete canonical instance header. -/
def header_run (aggregate : Bool) (query : Nat × Nat) (I : CliqueInstance)
    (output : List Bool) (work₁ work₂ : List (Option CliqueSym))
    (buffer₁ buffer₂ : Option (Option CliqueSym)) (test : Bool) :
    EvalsToInTime (step program)
      (cfg (.instanceMark aggregate) buffer₁ buffer₂ test
        ((encodeCliqueInstance I).map some) output work₁ work₂
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some (cfg (.edges aggregate) buffer₁ (some (some .fieldSep)) test
        ((I.edges.flatMap encodeCliqueEdge).map some) output work₁
        (((encodeCliqueInstance { I with edges := [] }).map some).reverse ++
          work₂)
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (headerSteps I) := by
  let edgeInput := I.edges.flatMap encodeCliqueEdge
  let targetInput := prependCliqueTicks I.targetSize (.fieldSep :: edgeInput)
  let afterMark := cfg (.vertexField aggregate) buffer₁
    (some (some .instanceMark)) test
    ((prependCliqueTicks I.vertexCount (.fieldSep :: targetInput)).map some)
    output work₁ (some CliqueSym.instanceMark :: work₂)
    (List.replicate query.1 ()) (List.replicate query.2 ()) []
  have first : EvalsToInTime (step program)
      (cfg (.instanceMark aggregate) buffer₁ buffer₂ test
        ((encodeCliqueInstance I).map some) output work₁ work₂
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some afterMark) 1 :=
    ⟨⟨1, by simp [flip, afterMark, targetInput, edgeInput,
      encodeCliqueInstance, step, program, cfg, stepOp]⟩, le_rfl⟩
  have vertexRun := vertexField_run aggregate I.vertexCount targetInput output
    work₁ (some CliqueSym.instanceMark :: work₂) query.1 query.2 buffer₁
    (some (some .instanceMark)) test
  let vertexStored :=
    ((prependCliqueTicks I.vertexCount [.fieldSep]).map some).reverse ++
      some CliqueSym.instanceMark :: work₂
  have vertexRun' : EvalsToInTime (step program) afterMark
      (some (cfg (.targetField aggregate) buffer₁ (some (some .fieldSep))
        test (targetInput.map some) output work₁ vertexStored
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (I.vertexCount + 1) := by
    simpa [afterMark, vertexStored] using vertexRun
  have targetRun := targetField_run aggregate I.targetSize edgeInput output
    work₁ vertexStored query.1 query.2 buffer₁ (some (some .fieldSep)) test
  let headerStored :=
    ((encodeCliqueInstance { I with edges := [] }).map some).reverse ++ work₂
  have hsplit :
      prependCliqueTicks I.vertexCount
          (.fieldSep :: prependCliqueTicks I.targetSize [.fieldSep]) =
        prependCliqueTicks I.vertexCount [.fieldSep] ++
          prependCliqueTicks I.targetSize [.fieldSep] := by
    symm
    exact prependCliqueTicks_append _ _ _
  have hstored :
      ((prependCliqueTicks I.targetSize [.fieldSep]).map some).reverse ++
          vertexStored = headerStored := by
    unfold vertexStored headerStored
    simp only [encodeCliqueInstance, List.flatMap_nil,
      List.map_cons, List.reverse_cons]
    rw [hsplit]
    simp [List.map_append, List.reverse_append, List.append_assoc]
  rw [hstored] at targetRun
  have targetRun' : EvalsToInTime (step program)
      (cfg (.targetField aggregate) buffer₁ (some (some .fieldSep)) test
        (targetInput.map some) output work₁ vertexStored
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some (cfg (.edges aggregate) buffer₁ (some (some .fieldSep)) test
        (edgeInput.map some) output work₁ headerStored
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (I.targetSize + 1) := by
    simpa [targetInput] using targetRun
  let throughVertex := EvalsToInTime.trans (step program)
    1 (I.vertexCount + 1) _ afterMark _ first vertexRun'
  have throughVertex' : EvalsToInTime (step program)
      (cfg (.instanceMark aggregate) buffer₁ buffer₂ test
        ((encodeCliqueInstance I).map some) output work₁ work₂
        (List.replicate query.1 ()) (List.replicate query.2 ()) [])
      (some (cfg (.targetField aggregate) buffer₁ (some (some .fieldSep))
        test (targetInput.map some) output work₁ vertexStored
        (List.replicate query.1 ()) (List.replicate query.2 ()) []))
      (1 + (I.vertexCount + 1)) := by
    simpa [Nat.add_comm] using throughVertex
  let full := EvalsToInTime.trans (step program)
    (1 + (I.vertexCount + 1)) (I.targetSize + 1)
    _ _ _ throughVertex' targetRun'
  simpa [headerSteps, edgeInput, headerStored, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup
