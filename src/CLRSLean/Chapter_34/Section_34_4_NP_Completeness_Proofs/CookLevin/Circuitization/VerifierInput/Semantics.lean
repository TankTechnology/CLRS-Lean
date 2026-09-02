import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Core

/-! # Exact verifier-input semantics via `filterMap`, without certificate enumeration. -/
namespace CLRS.Chapter34.Turing.CookLevin
noncomputable section
private theorem map_pairEncoding {α β : Type} (f : Option α → β)
    (c x : List α) :
    List.map f (pairEncoding c x) =
      List.map (f ∘ some) c ++ [f none] ++ List.map (f ∘ some) x := by
  simp [pairEncoding]

private theorem map_inv_filterMap_eq_of_ne_none {α Γ : Type}
    (e : α ≃ Option Γ) (ys : List α)
    (h : ∀ y ∈ ys, e y ≠ none) :
    List.map (fun g => e.invFun (some g)) (ys.filterMap e) = ys := by
  induction ys with
  | nil => simp
  | cons y ys ih =>
      have hy := h y (by simp)
      cases he : e y with
      | none => exact (hy he).elim
      | some g =>
          have htail : ∀ z ∈ ys, e z ≠ none := by
            intro z hz
            exact h z (by simp [hz])
          simp only [List.filterMap_cons, he, List.map_cons, List.cons.injEq]
          constructor
          · exact e.injective (by simp [he])
          · exact ih htail

private theorem verifierInputArmMatches_iff {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (bits : StackBits W.machine.tm H W.machine.tm.k₀)
    (ys : List (W.machine.tm.Γ W.machine.tm.k₀))
    (hrep : bits.Represents ys) (length : Nat) :
    VerifierInputArmMatches W H x bits length ↔
      ∃ c : List Γ, c.length = length ∧
        ys = List.map W.machine.inputAlphabet.invFun (pairEncoding c x) := by
  constructor
  · rintro ⟨hfit, hheight, hprefix, hseparator, hfixed⟩
    have hlen : ys.length = length + 1 + x.length := by
      exact (hrep.height_eq_true_iff _).mp hheight |>.symm
    let prefixList := ys.take length
    let c := prefixList.filterMap W.machine.inputAlphabet
    have hprefixNone : ∀ y ∈ prefixList,
        W.machine.inputAlphabet y ≠ none := by
      intro y hy hnone
      rcases List.mem_iff_getElem.mp hy with ⟨i, hi, hyget⟩
      have hilength : i < length := by
        have := hi
        simp only [prefixList, List.length_take] at this
        omega
      have hiys : i < ys.length := by omega
      have hiy : ys.get ⟨i, by omega⟩ = y := by
        simpa [prefixList] using hyget
      have hcell := hprefix ⟨i, hilength⟩
      have htrue := (hrep.active_cell_eq_true_iff ⟨i, by omega⟩
        hiys (verifierInputSymbol W none)).2
      have hsymbol : ys.get ⟨i, hiys⟩ =
          (verifierInputSymbol W none).val := by
        rw [hiy]
        exact W.machine.inputAlphabet.injective
          (by simp [hnone])
      have hcontr := htrue hsymbol
      have hcell' : bits.cell ⟨i, by omega⟩
          (verifierInputCode W none) = false := hcell
      change bits.cell ⟨i, by omega⟩ (verifierInputCode W none) = true at hcontr
      rw [hcell'] at hcontr
      exact Bool.noConfusion hcontr
    have hprefixMap :
        List.map (fun g => W.machine.inputAlphabet.invFun (some g)) c =
          prefixList := by
      exact map_inv_filterMap_eq_of_ne_none W.machine.inputAlphabet prefixList
        hprefixNone
    have hcLength : c.length = length := by
      have := congrArg List.length hprefixMap
      have hle : length ≤ ys.length := by omega
      simpa [c, prefixList, hle] using this
    have hsepGet : ys.get ⟨length, by omega⟩ =
        W.machine.inputAlphabet.invFun none := by
      have hactive : length < ys.length := by omega
      exact (hrep.active_cell_eq_true_iff ⟨length, by omega⟩
        hactive (verifierInputSymbol W none)).mp hseparator
    have htail : ys.drop length =
        W.machine.inputAlphabet.invFun none ::
          List.map (fun g => W.machine.inputAlphabet.invFun (some g)) x := by
      apply List.ext_getElem
      · simp only [List.length_drop, List.length_cons, List.length_map]
        omega
      · intro i hi₁ hi₂
        cases i with
        | zero => simpa using hsepGet
        | succ i =>
            have hi : i < x.length := by
              simp only [List.length_drop] at hi₁
              omega
            have hcellH : length + 1 + i < H := by omega
            have hactive : length + 1 + i < ys.length := by omega
            have hget := (hrep.active_cell_eq_true_iff
              ⟨length + 1 + i, hcellH⟩ hactive
              (verifierInputSymbol W (some x[i]))).mp (hfixed ⟨i, hi⟩)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hget
    refine ⟨c, hcLength, ?_⟩
    calc
      ys = prefixList ++ ys.drop length := by
        change ys = ys.take length ++ ys.drop length
        exact (List.take_append_drop length ys).symm
      _ = List.map (fun g => W.machine.inputAlphabet.invFun (some g)) c ++
          W.machine.inputAlphabet.invFun none ::
            List.map (fun g => W.machine.inputAlphabet.invFun (some g)) x := by
        rw [hprefixMap, htail]
      _ = List.map W.machine.inputAlphabet.invFun (pairEncoding c x) := by
        rw [map_pairEncoding]
        change List.map (fun g => W.machine.inputAlphabet.invFun (some g)) c ++
            W.machine.inputAlphabet.invFun none ::
              List.map (fun g => W.machine.inputAlphabet.invFun (some g)) x =
          (List.map (fun g => W.machine.inputAlphabet.invFun (some g)) c ++
            [W.machine.inputAlphabet.invFun none]) ++
              List.map (fun g => W.machine.inputAlphabet.invFun (some g)) x
        exact (List.append_assoc _ [_] _).symm
  · rintro ⟨c, hcLength, rfl⟩
    rcases hrep.eq_encode with ⟨_, hheightBound, _⟩
    have hfit : length + 1 + x.length ≤ H := by
      simp only [List.length_map, pairEncoding_length, hcLength] at hheightBound
      omega
    refine ⟨hfit, ?_, ?_, ?_, ?_⟩
    · apply (hrep.height_eq_true_iff _).2
      simp only [List.length_map, pairEncoding_length, hcLength]
      omega
    · intro i
      have hactive : i.val <
          (List.map W.machine.inputAlphabet.invFun (pairEncoding c x)).length := by
        simp [pairEncoding, hcLength]; omega
      have hiff := hrep.active_cell_eq_true_iff ⟨i.val, by omega⟩ hactive
        (verifierInputSymbol W none)
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      have heq := hiff.mp htrue
      have := congrArg W.machine.inputAlphabet heq
      simp [pairEncoding, hcLength] at this
    · apply (hrep.active_cell_eq_true_iff ⟨length, by omega⟩
        (by simp [pairEncoding, hcLength])
        (verifierInputSymbol W none)).2
      simp [pairEncoding, hcLength]
    · intro i
      apply (hrep.active_cell_eq_true_iff ⟨length + 1 + i.val, by omega⟩
        (by simp [pairEncoding, hcLength]; omega)
        (verifierInputSymbol W (some (x.get i)))).2
      simp [pairEncoding, hcLength, Nat.add_comm, Nat.add_left_comm]

/-- Exact semantic characterization of the verifier-input shape circuit. -/
theorem verifierInputShapeCircuit_eval_iff {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ)
    (inputs : Nat → Bool) (ys : List (W.machine.tm.Γ W.machine.tm.k₀))
    (hrep : (evalStackBits base inputs inputStack).Represents ys) :
    let result := verifierInputShapeCircuit W H base pool inputStack
      hinputStack x
    result.builder.evalWire inputs result.wire = true ↔ IsVerifierInput W x ys := by
  change (verifierInputShapeCircuit W H base pool inputStack hinputStack x).builder.evalWire
    inputs (verifierInputShapeCircuit W H base pool inputStack hinputStack x).wire =
      true ↔ IsVerifierInput W x ys
  have hstruct :
      (verifierInputShapeCircuit W H base pool inputStack hinputStack x).builder.evalWire
          inputs (verifierInputShapeCircuit W H base pool inputStack hinputStack x).wire =
            true ↔
        ∃ length, length ≤ W.certificateBound.eval x.length ∧
          VerifierInputArmMatches W H x
            (evalStackBits base inputs inputStack) length :=
    verifierInputShapeCircuit_eval_iff_exists_length W H base pool inputStack
      hinputStack x inputs
  rw [hstruct]
  constructor
  · rintro ⟨length, hlength, hmatches⟩
    rcases (verifierInputArmMatches_iff W H x _ ys hrep length).mp hmatches with
      ⟨c, hcLength, hys⟩
    exact ⟨c, by omega, hys⟩
  · rintro ⟨c, hcBound, hys⟩
    refine ⟨c.length, hcBound, ?_⟩
    exact (verifierInputArmMatches_iff W H x _ ys hrep c.length).2
      ⟨c, rfl, hys⟩

/-- Soundness wrapper for downstream assembly. -/
theorem verifierInputShapeCircuit_sound {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ)
    (inputs : Nat → Bool) (ys : List (W.machine.tm.Γ W.machine.tm.k₀))
    (hrep : (evalStackBits base inputs inputStack).Represents ys)
    (htrue : (verifierInputShapeCircuit W H base pool inputStack
      hinputStack x).builder.evalWire inputs
        (verifierInputShapeCircuit W H base pool inputStack hinputStack x).wire = true) :
    IsVerifierInput W x ys :=
  (verifierInputShapeCircuit_eval_iff W H base pool inputStack hinputStack x
    inputs ys hrep).mp htrue

/-- Completeness wrapper for downstream assembly. -/
theorem verifierInputShapeCircuit_complete {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ)
    (inputs : Nat → Bool) (ys : List (W.machine.tm.Γ W.machine.tm.k₀))
    (hrep : (evalStackBits base inputs inputStack).Represents ys)
    (hinput : IsVerifierInput W x ys) :
    let result := verifierInputShapeCircuit W H base pool inputStack
      hinputStack x
    result.builder.evalWire inputs result.wire = true :=
  (verifierInputShapeCircuit_eval_iff W H base pool inputStack hinputStack x
    inputs ys hrep).mpr hinput

/-- Evaluation of the shape output is stable in every later builder. -/
theorem verifierInputShapeCircuit_eval_extends {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack : inputStack.ValidIn base) (x : List Γ)
    (inputs : Nat → Bool) {next : CircuitBuilder}
    (hext : (verifierInputShapeCircuit W H base pool inputStack
      hinputStack x).builder.Extends next) :
    next.evalWire inputs
        (verifierInputShapeCircuit W H base pool inputStack hinputStack x).wire =
      (verifierInputShapeCircuit W H base pool inputStack hinputStack x).builder.evalWire
        inputs
        (verifierInputShapeCircuit W H base pool inputStack hinputStack x).wire :=
  hext.evalWire_eq inputs
    (verifierInputShapeCircuit_wireValid W H base pool inputStack hinputStack x)

/-- The output value is independent of the proof supplied for input-stack
wire validity. -/
theorem verifierInputShapeCircuit_eval_proof_irrel {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (base : CircuitBuilder)
    (pool : base.BoolWirePool)
    (inputStack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hinputStack₁ hinputStack₂ : inputStack.ValidIn base) (x : List Γ)
    (inputs : Nat → Bool) :
    (verifierInputShapeCircuit W H base pool inputStack hinputStack₁ x).builder.evalWire
        inputs
        (verifierInputShapeCircuit W H base pool inputStack hinputStack₁ x).wire =
      (verifierInputShapeCircuit W H base pool inputStack hinputStack₂ x).builder.evalWire
        inputs
        (verifierInputShapeCircuit W H base pool inputStack hinputStack₂ x).wire := by
  rw [verifierInputShapeCircuit_proof_irrel W H base pool inputStack
    hinputStack₁ hinputStack₂ x]

end
end CLRS.Chapter34.Turing.CookLevin
