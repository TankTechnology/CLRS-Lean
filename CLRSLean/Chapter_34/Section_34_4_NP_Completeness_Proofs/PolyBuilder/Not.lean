import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun

/-!
# Contextual single-NOT serialization

This is the one-gate primitive needed immediately before every stack-cell
Boolean equality.  It shares the established counter-preserving unary encoder
and clears all scratch state on exit.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Exact encoding of one NOT gate at an arbitrary source wire. -/
def affineNotGateStream (source : Nat) : List CircuitSym :=
  encodeCircuitGate (.not source)

/-- The public stream is definitionally the corresponding semantic gate. -/
theorem affineNotGateStream_eq_trace (source : Nat) :
    affineNotGateStream source =
      ([CircuitGate.not source]).flatMap encodeCircuitGate := by
  simp [affineNotGateStream]

/-- Contextual entry configuration for a single reversed NOT gate. -/
def affineNotBodyCfg (source : Nat) (output : List CircuitSym) :
    BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg (.singleNot .push) none none false [] output [] []
    [] [] (List.replicate source ())

/-- Exact running time of the contextual single-NOT serializer. -/
def affineNotRevSteps (source : Nat) : Nat :=
  6 * source + 9

/-- The shared counter program emits exactly one reversed NOT encoding and
clears its source counter before halting. -/
def affineNotRev_runFrom (source : Nat) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineNotBodyCfg source output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((affineNotGateStream source).reverse ++ output)))
      (affineNotRevSteps source) := by
  let c₀ := sequentialExactlyOneCfg (.encode .wire .affineNotWire)
    none none false [] (.notMark :: output) [] [] [] []
    (List.replicate source ())
  have hpush : EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineNotBodyCfg source output) (some c₀) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  let gateOutput := (encodeCircuitGate (.not source)).reverse ++ output
  let c₁ := sequentialExactlyOneCfg (.resume .affineNotWire)
    none none false [] gateOutput [] [] [] [] (List.replicate source ())
  have hsource : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₀ (some c₁) (5 * source + 3) := by
    simpa [c₀, c₁, gateOutput, encodeCircuitGate, List.reverse_append,
      List.append_assoc] using
      encodeWire_run source .affineNotWire none false []
        (.notMark :: output) [] [] []
  let beforeClear := sequentialExactlyOneCfg .clear₁ none none false []
    gateOutput [] [] [] [] (List.replicate source ())
  have hjump : EvalsToInTime (step sequentialExactlyOneRevProgram)
      c₁ (some beforeClear) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  have hclear : EvalsToInTime (step sequentialExactlyOneRevProgram)
      beforeClear
      (some (haltCfg sequentialExactlyOneRevProgram gateOutput))
      (source + 4) := by
    simpa [beforeClear] using
      clearAllRegisters 0 0 source none gateOutput
  let t₁ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    1 (5 * source + 3) _ c₀ _ hpush hsource
  let t₂ := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ 1 _ c₁ _ t₁ hjump
  let full := EvalsToInTime.trans (step sequentialExactlyOneRevProgram)
    _ (source + 4) _ beforeClear _ t₂ hclear
  convert full using 1
  · simp [affineNotGateStream, gateOutput]
  · simp [affineNotRevSteps]
    omega

/-- Uniform quadratic envelope for a single NOT invocation. -/
theorem affineNotRev_steps_le (source : Nat) :
    affineNotRevSteps source ≤ 10 * (source + 1) ^ 2 := by
  simp [affineNotRevSteps]
  nlinarith

end CLRS.Chapter34.Turing.PolyBuilder
