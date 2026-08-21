import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveLinearRouteBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# Typed raw-input row families for linear statement results

The affine-span source already emits one complete `frameEnd`-delimited route
per transition seed.  This module packages the same stream as a typed marked
row family, so it can be consumed by the reusable row-family combinators.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem linearResult_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values, symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction values with
  | nil => simp [encodeUnaryFrame] at hsymbol
  | cons value values ih =>
      simp only [encodeUnaryFrame, List.flatMap_cons] at hsymbol
      rw [List.mem_append] at hsymbol
      rcases hsymbol with hhead | htail
      · unfold encodeUnaryFrameBlock at hhead
        rw [List.mem_append] at hhead
        rcases hhead with htick | hseparator
        · have : symbol = UnaryFrameSym.tick :=
            List.eq_of_mem_replicate htick
          subst symbol
          decide
        · have : symbol = UnaryFrameSym.separator := by
            simpa using hseparator
          subst symbol
          decide
      · exact ih htail

/-- Semantic complete-route rows of one fixed normalized linear result. -/
noncomputable def verifierTransitionLinearResultRouteFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult W.machine.tm)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  { rows := (verifierTransitionRowSeeds W input).map fun seed =>
      encodeUnaryFrame
        (result.completeRouteValues W.machine.tm seed labelOffset)
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact linearResult_encodeUnaryFrame_frameEnd_free _ symbol hsymbol }

/-- Under the automatically proved route invariant, the concrete affine-span
machine output is exactly the typed semantic row family encoding. -/
theorem verifierTransitionLinearResultRouteFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult W.machine.tm)
    (hbounds : ∀ seed ∈ verifierTransitionRowSeeds W input,
      result.RouteBounds W.machine.tm seed labelOffset) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionLinearResultRouteFamily W labelOffset result
          input) =
      verifierTransitionLinearResultAffineSpanFrames W labelOffset result
        input := by
  rw [result.verifierLinearResultAffineSpanFrames_eq W input labelOffset
    hbounds]
  unfold encodeUnaryFrameMarkedRowFamily
    verifierTransitionLinearResultRouteFamily
  simp [List.flatMap_map]

/-- Any fixed linear result whose recursive provenance supplies the route
bounds has a concrete polynomial-time TM2 producing its semantic rows from
the original verifier input. -/
noncomputable def
    verifierTransitionLinearResultRouteFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult W.machine.tm)
    (hbounds : ∀ input seed,
      seed ∈ verifierTransitionRowSeeds W input →
        result.RouteBounds W.machine.tm seed labelOffset) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionLinearResultRouteFamily W labelOffset result) := by
  let source :=
    verifierTransitionLinearResultAffineSpanFrames_computableInPolyTime
      W labelOffset result
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierTransitionLinearResultRouteFamily_encoding_eq W input
            labelOffset result (fun seed hseed =>
              hbounds input seed hseed)] using source.outputsFun input }

end CLRS.Chapter34.Turing.CookLevin
