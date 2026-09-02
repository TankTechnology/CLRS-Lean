import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationDescriptorFalseExecute
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowOrderReverse

/-!
# Reversing the unified four-way dispatch descriptor stream

The physical router emits one marked `false / true / coordinates / selectors`
group per transition seed.  Reversing marked-row order preserves every unary
payload while exposing `selectors / coordinates / true / false` for the last
seed first.  This is the direction needed by the prepend-oriented final label
assembler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem fourWayReverse_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> simp

/-- Typed marked-row view of the actual seed-major four-way descriptor
stream. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows :=
    (verifierTransitionRowSeeds W input).flatMap fun seed =>
      [ encodeUnaryFrame
          (transitionDispatchMuxFalseArmDescriptorValues W.machine.tm seed),
        encodeUnaryFrame
          (transitionDispatchTrueArmSpanDescriptorValues W.machine.tm seed),
        encodeUnaryFrame
          (transitionDispatchMuxCoordinateDescriptorValues W.machine.tm seed),
        encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ]
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rw [List.mem_flatMap] at hrow
    rcases hrow with ⟨seed, hseed, hrow⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with hrow | hrow | hrow | hrow
    · subst row
      exact fourWayReverse_encodeUnaryFrame_frameEnd_free _ symbol hsymbol
    · subst row
      exact fourWayReverse_encodeUnaryFrame_frameEnd_free _ symbol hsymbol
    · subst row
      exact fourWayReverse_encodeUnaryFrame_frameEnd_free _ symbol hsymbol
    · subst row
      exact fourWayReverse_encodeUnaryFrame_frameEnd_free _ symbol hsymbol

@[simp] theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily
      W input).rows =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        [ encodeUnaryFrame
            (transitionDispatchMuxFalseArmDescriptorValues W.machine.tm seed),
          encodeUnaryFrame
            (transitionDispatchTrueArmSpanDescriptorValues W.machine.tm seed),
          encodeUnaryFrame
            (transitionDispatchMuxCoordinateDescriptorValues W.machine.tm seed),
          encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ] := by
  rfl

/-- Its marked encoding is byte-for-byte the output of the existing concrete
four-way descriptor router. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily
          W input) =
      verifierTransitionDispatchMuxInvocationDescriptorFourWayRows W input := by
  rw [verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_eq]
  unfold encodeUnaryFrameMarkedRowFamily
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily_rows]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  simp [List.append_assoc]

private theorem fourWayDescriptorPayloadRows_reverse
    (tm : _root_.Turing.FinTM2) (seeds : List TransitionRowSeed) :
    (seeds.flatMap fun seed =>
        [ encodeUnaryFrame
            (transitionDispatchMuxFalseArmDescriptorValues tm seed),
          encodeUnaryFrame
            (transitionDispatchTrueArmSpanDescriptorValues tm seed),
          encodeUnaryFrame
            (transitionDispatchMuxCoordinateDescriptorValues tm seed),
          encodeUnaryFrame (transitionDispatchSelectors tm seed) ]).reverse =
      seeds.reverse.flatMap fun seed =>
        [ encodeUnaryFrame (transitionDispatchSelectors tm seed),
          encodeUnaryFrame
            (transitionDispatchMuxCoordinateDescriptorValues tm seed),
          encodeUnaryFrame
            (transitionDispatchTrueArmSpanDescriptorValues tm seed),
          encodeUnaryFrame
            (transitionDispatchMuxFalseArmDescriptorValues tm seed) ] := by
  induction seeds with
  | nil => rfl
  | cons seed seeds ih =>
      simp [ih]

/-- Concrete reversed-row stream generated from the original verifier word. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayReversedRows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameMarkedRowOrderReverse
    (verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily
      W input)

/-- Exact physical order after reversal: seed order and the four rows inside
each seed are both reversed, while every row payload remains forward. -/
theorem
    verifierTransitionDispatchMuxInvocationDescriptorFourWayReversedRows_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionDispatchMuxInvocationDescriptorFourWayReversedRows
        W input =
      (verifierTransitionRowSeeds W input).reverse.flatMap fun seed =>
        encodeUnaryFrame (transitionDispatchSelectors W.machine.tm seed) ++
          [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxCoordinateDescriptorValues
              W.machine.tm seed) ++ [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchTrueArmSpanDescriptorValues
              W.machine.tm seed) ++ [.frameEnd] ++
          encodeUnaryFrame
            (transitionDispatchMuxFalseArmDescriptorValues
              W.machine.tm seed) ++ [.frameEnd] := by
  unfold
    verifierTransitionDispatchMuxInvocationDescriptorFourWayReversedRows
    encodeUnaryFrameMarkedRowOrderReverse
  rw [
    verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily_rows]
  rw [fourWayDescriptorPayloadRows_reverse]
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro seed hseed
  simp [List.append_assoc]

/-- From the original verifier input, four-way routing followed by marked-row
reversal remains one fixed polynomial-time TM2. -/
noncomputable def
    verifierTransitionDispatchMuxInvocationDescriptorFourWayReversedRows_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayReversedRows
        W) := by
  let routed :=
    verifierTransitionDispatchMuxInvocationDescriptorFourWayRows_computableInPolyTime
      W
  let typed : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily
        W) :=
    { tm := routed.tm
      inputAlphabet := routed.inputAlphabet
      outputAlphabet := routed.outputAlphabet
      time := routed.time
      outputsFun := fun input => by
        have run := routed.outputsFun input
        simpa only [id_eq,
          verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily_encoding_eq]
          using run }
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch typed
      unaryFrameMarkedRowOrderReverse_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => encodeUnaryFrameMarkedRowOrderReverse
      (verifierTransitionDispatchMuxInvocationDescriptorFourWayMarkedFamily
        W input))
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
