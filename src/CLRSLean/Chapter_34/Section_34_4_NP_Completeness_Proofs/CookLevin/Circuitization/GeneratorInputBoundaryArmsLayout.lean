import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundarySeparatorSource

/-!
# Structural layout of verifier-input arms

The published tableau height contains the complete certificate/input envelope.
Consequently every candidate length enumerated by the input-boundary builder
fits, and the optional conjunction family has no absent entry.  This removes
the only data-dependent control branch from the arm source compiler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Every candidate certificate length enumerated by the verifier-input
boundary fits in the published tableau height. -/
theorem verifierInputArm_fits
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) :
    arm.val + 1 + input.length ≤ (verifierHeight W).eval input.length := by
  rw [verifierHeight_eval, verifierInputBound_eval]
  have harm : arm.val ≤ W.certificateBound.eval input.length := by
    omega
  omega

/-- On the actual verifier dimensions, one arm has its unconditional exact
conjunction cost. -/
@[simp] theorem verifierInputArmGateCost_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) :
    verifierInputArmGateCost ((verifierHeight W).eval input.length)
        input.length arm.val =
      arm.val + input.length + 3 := by
  unfold verifierInputArmGateCost
  rw [if_pos (verifierInputArm_fits W input arm)]

/-- The recursive frame compiler emits exactly one optional entry per
candidate length, independently of which entries fit. -/
@[simp] theorem VerifierInput.compileInputArmFrames_length
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (input : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (count : Nat) :
    (VerifierInput.compileInputArmFrames W H input start pool stack hstack
      separatorNots hseparatorNots hseparatorEval count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [VerifierInput.compileInputArmFrames, ih]

/-- One canonical optional arm entry, stated without the recursive frame-list
compiler.  Its start is the builder length after precisely the preceding
arms. -/
def VerifierInput.compileInputArmEntry
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (input : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (length : Nat) : Option AffineConjunctionFrame :=
  if hfit : length + 1 + input.length ≤ H then
    let previous := VerifierInput.buildInputArms W H input start pool stack
      hstack separatorNots hseparatorNots hseparatorEval length
    some
      { start := previous.builder.gates.length
        wires := VerifierInput.inputArmWires W H input stack separatorNots
          length hfit }
  else none

/-- The recursive compiler is extensionally the ordinal-indexed canonical
entry family. -/
theorem VerifierInput.compileInputArmFrames_eq_ofFn
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (input : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (count : Nat) :
    VerifierInput.compileInputArmFrames W H input start pool stack hstack
        separatorNots hseparatorNots hseparatorEval count =
      List.ofFn fun index : Fin count =>
        VerifierInput.compileInputArmEntry W H input start pool stack hstack
          separatorNots hseparatorNots hseparatorEval index.val := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [VerifierInput.compileInputArmFrames, List.ofFn_succ', ih]
      simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last]
      rfl

/-- If every ordinal below `count` fits, the recursive compiler contains no
absent optional conjunction entry. -/
theorem VerifierInput.compileInputArmFrames_all_some
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (input : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (count : Nat)
    (hfit : ∀ length, length < count → length + 1 + input.length ≤ H) :
    ∀ entry ∈
      VerifierInput.compileInputArmFrames W H input start pool stack hstack
        separatorNots hseparatorNots hseparatorEval count,
      ∃ frame, entry = some frame := by
  induction count with
  | zero => simp [VerifierInput.compileInputArmFrames]
  | succ count ih =>
      intro entry hentry
      simp only [VerifierInput.compileInputArmFrames, List.mem_append,
        List.mem_singleton] at hentry
      rcases hentry with hprevious | rfl
      · exact ih (fun length hlength => hfit length (by omega)) entry hprevious
      · simp [hfit count (by omega)]

/-- The assembled verifier-input script contains no zero-gate arm marker. -/
theorem verifierInputBoundaryScript_armFrames_all_some
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    ∀ entry ∈ (verifierInputBoundaryScript W input).armFrames,
      ∃ frame, entry = some frame := by
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  apply VerifierInput.compileInputArmFrames_all_some
  intro length hlength
  have hle : length ≤ W.certificateBound.eval input.length := by omega
  rw [verifierHeight_eval, verifierInputBound_eval]
  omega

/-- The arm family has the advertised exact polynomial number of entries. -/
@[simp] theorem verifierInputBoundaryScript_armFrames_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundaryScript W input).armFrames.length =
      W.certificateBound.eval input.length + 1 := by
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  exact VerifierInput.compileInputArmFrames_length _ _ _ _ _ _ _ _ _ _ _

/-- The final disjunction consumes exactly one output wire per candidate
certificate length. -/
@[simp] theorem verifierInputBoundaryScript_finalOrWires_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundaryScript W input).finalOrWires.length =
      W.certificateBound.eval input.length + 1 := by
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  simp

end CLRS.Chapter34.Turing.CookLevin
