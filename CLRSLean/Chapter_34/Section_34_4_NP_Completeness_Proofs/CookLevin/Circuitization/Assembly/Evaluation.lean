import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Structure

/-!
# Evaluation projections for the assembled verifier circuit

These lemmas isolate the bookkeeping of the final conjunction from the
semantic proofs for individual constraint families.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

private theorem verifierConjunction_eval {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool) :
    (verifierConjunction W x).1.evalWire inputs
        (verifierConjunction W x).2 =
      (verifierConstraintWires W x).all (fun wire =>
        (verifierAcceptingBoundary W x).builder.evalWire inputs wire) := by
  rw [show verifierConjunction W x =
      (verifierAcceptingBoundary W x).builder.conjunction
        (verifierConstraintWires W x) (verifierConstraintWires_valid W x) by
    rfl]
  exact CircuitBuilder.conjunction_eval _ _ _ _

private theorem verifierValidity_to_accepting {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierValidity W x).builder.Extends
      (verifierAcceptingBoundary W x).builder :=
  (verifierTransitions W x).extension.trans
    ((verifierInitialBoundary W x).extension.trans
      ((verifierInputBoundary W x).extension.trans
        (verifierAcceptingBoundary W x).extension))

private theorem verifierTransitions_to_accepting {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (x : List Γ) :
    (verifierTransitions W x).builder.Extends
      (verifierAcceptingBoundary W x).builder :=
  (verifierInitialBoundary W x).extension.trans
    ((verifierInputBoundary W x).extension.trans
      (verifierAcceptingBoundary W x).extension)

private theorem verifierInitial_to_accepting {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierInitialBoundary W x).builder.Extends
      (verifierAcceptingBoundary W x).builder :=
  (verifierInputBoundary W x).extension.trans
    (verifierAcceptingBoundary W x).extension

private theorem verifierInput_to_accepting {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierInputBoundary W x).builder.Extends
      (verifierAcceptingBoundary W x).builder :=
  (verifierAcceptingBoundary W x).extension

/-- A true final conjunction forces every row-validity output to be true. -/
theorem verifierConjunction_validity_true {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool)
    (hfinal : (verifierConjunction W x).1.evalWire inputs
      (verifierConjunction W x).2 = true) :
    ∀ row, (verifierValidity W x).builder.evalWire inputs
      ((verifierValidity W x).outputs row) = true := by
  intro row
  rw [verifierConjunction_eval] at hfinal
  have hmember : (verifierValidity W x).outputs row ∈
      verifierConstraintWires W x := by
    unfold verifierConstraintWires
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨row, rfl⟩
  have hatAccepting := (List.all_eq_true.mp hfinal)
    ((verifierValidity W x).outputs row) hmember
  rw [(verifierValidity_to_accepting W x).evalWire_eq inputs
    ((verifierValidity W x).outputsValid row)] at hatAccepting
  exact hatAccepting

/-- A true final conjunction forces every adjacent transition output true. -/
theorem verifierConjunction_transitions_true {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool)
    (hfinal : (verifierConjunction W x).1.evalWire inputs
      (verifierConjunction W x).2 = true) :
    ∀ step, (verifierTransitions W x).builder.evalWire inputs
      ((verifierTransitions W x).outputs step) = true := by
  intro step
  rw [verifierConjunction_eval] at hfinal
  have hmember : (verifierTransitions W x).outputs step ∈
      verifierConstraintWires W x := by
    unfold verifierConstraintWires
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨step, rfl⟩
  have hatAccepting := (List.all_eq_true.mp hfinal)
    ((verifierTransitions W x).outputs step) hmember
  rw [(verifierTransitions_to_accepting W x).evalWire_eq inputs
    ((verifierTransitions W x).outputsValid step)] at hatAccepting
  exact hatAccepting

/-- A true final conjunction forces the symbolic initial boundary true. -/
theorem verifierConjunction_initial_true {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool)
    (hfinal : (verifierConjunction W x).1.evalWire inputs
      (verifierConjunction W x).2 = true) :
    (verifierInitialBoundary W x).builder.evalWire inputs
      (verifierInitialBoundary W x).wire = true := by
  rw [verifierConjunction_eval] at hfinal
  have hmember : (verifierInitialBoundary W x).wire ∈
      verifierConstraintWires W x := by
    simp [verifierConstraintWires]
  have result := (List.all_eq_true.mp hfinal) _ hmember
  rw [(verifierInitial_to_accepting W x).evalWire_eq inputs
    (verifierInitialBoundary W x).valid] at result
  exact result

/-- A true final conjunction forces the verifier-input shape boundary true. -/
theorem verifierConjunction_input_true {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool)
    (hfinal : (verifierConjunction W x).1.evalWire inputs
      (verifierConjunction W x).2 = true) :
    (verifierInputBoundary W x).builder.evalWire inputs
      (verifierInputBoundary W x).wire = true := by
  rw [verifierConjunction_eval] at hfinal
  have hmember : (verifierInputBoundary W x).wire ∈
      verifierConstraintWires W x := by
    simp [verifierConstraintWires]
  have result := (List.all_eq_true.mp hfinal) _ hmember
  rw [(verifierInput_to_accepting W x).evalWire_eq inputs
    (verifierInputBoundary W x).valid] at result
  exact result

/-- A true final conjunction forces the exact accepting boundary true. -/
theorem verifierConjunction_accepting_true {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool)
    (hfinal : (verifierConjunction W x).1.evalWire inputs
      (verifierConjunction W x).2 = true) :
    (verifierAcceptingBoundary W x).builder.evalWire inputs
      (verifierAcceptingBoundary W x).wire = true := by
  rw [verifierConjunction_eval] at hfinal
  exact (List.all_eq_true.mp hfinal) _ (by
    simp [verifierConstraintWires])

/-- If all five classes of original-stage outputs are true, the final
conjunction is true. -/
theorem verifierConjunction_true_of_components
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) (inputs : Nat → Bool)
    (hvalidity : ∀ row, (verifierValidity W x).builder.evalWire inputs
      ((verifierValidity W x).outputs row) = true)
    (htransitions : ∀ step,
      (verifierTransitions W x).builder.evalWire inputs
        ((verifierTransitions W x).outputs step) = true)
    (hinitial : (verifierInitialBoundary W x).builder.evalWire inputs
      (verifierInitialBoundary W x).wire = true)
    (hinput : (verifierInputBoundary W x).builder.evalWire inputs
      (verifierInputBoundary W x).wire = true)
    (haccepting : (verifierAcceptingBoundary W x).builder.evalWire inputs
      (verifierAcceptingBoundary W x).wire = true) :
    (verifierConjunction W x).1.evalWire inputs
      (verifierConjunction W x).2 = true := by
  rw [verifierConjunction_eval, List.all_eq_true]
  intro wire hwire
  simp only [verifierConstraintWires, List.mem_append, List.mem_ofFn,
    List.mem_cons, List.not_mem_nil, or_false] at hwire
  rcases hwire with (⟨row, rfl⟩ | ⟨step, rfl⟩) | hwire
  · rw [(verifierValidity_to_accepting W x).evalWire_eq inputs
      ((verifierValidity W x).outputsValid row)]
    exact hvalidity row
  · rw [(verifierTransitions_to_accepting W x).evalWire_eq inputs
      ((verifierTransitions W x).outputsValid step)]
    exact htransitions step
  · rcases hwire with rfl | rfl | rfl
    · rw [(verifierInitial_to_accepting W x).evalWire_eq inputs
        (verifierInitialBoundary W x).valid]
      exact hinitial
    · rw [(verifierInput_to_accepting W x).evalWire_eq inputs
        (verifierInputBoundary W x).valid]
      exact hinput
    · exact haccepting

end

end CLRS.Chapter34.Turing.CookLevin
