import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeedRowSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInputCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameQuoteCore
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-!
# Constant quoted rows indexed by transition seeds

Some statement-controller fragments are fixed tags rather than affine
numeric payloads.  This small reusable source replaces each marked transition
seed with one delimiter-safe quotation of a fixed word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Streaming action that recognizes only the outer seed marker. -/
def transitionConstantQuotedSeedExpandBody
    (payload : List UnaryFrameSym) : LoopBody UnaryFrameSym UnaryFrameSym where
  emit symbol := if symbol = .frameEnd then
    quoteUnaryFrameStream payload ++ [.frameEnd]
  else []
  cost _ := 2 * payload.length + 1
  emit_length_le_cost symbol := by
    by_cases h : symbol = UnaryFrameSym.frameEnd
    · subst symbol
      simp [quoteUnaryFrameStream, List.length_flatMap]
      omega
    · simp [h]

/-- One copy of the fixed quoted word per canonical transition seed. -/
noncomputable def verifierTransitionConstantQuotedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (payload : List UnaryFrameSym) (input : List Γ) :
    UnaryFrameMarkedRowFamily where
  rows := (verifierTransitionRowSeeds W input).map fun _ =>
    quoteUnaryFrameStream payload
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rw [List.mem_map] at hrow
    rcases hrow with ⟨seed, hseed, rfl⟩
    exact quoteUnaryFrameStream_frameEnd_free payload symbol hsymbol

@[simp] theorem verifierTransitionConstantQuotedFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (payload : List UnaryFrameSym) (input : List Γ) :
    (verifierTransitionConstantQuotedFamily W payload input).rows =
      (verifierTransitionRowSeeds W input).map fun _ =>
        quoteUnaryFrameStream payload := rfl

private theorem constantQuotedExpand_encodeUnaryFrame
    (payload : List UnaryFrameSym) (values : List Nat) :
    (encodeUnaryFrame values).flatMap
        (transitionConstantQuotedSeedExpandBody payload).emit = [] := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      change
        (encodeUnaryFrameBlock value ++ encodeUnaryFrame values).flatMap
            (transitionConstantQuotedSeedExpandBody payload).emit = []
      rw [List.flatMap_append, ih]
      simp [encodeUnaryFrameBlock, transitionConstantQuotedSeedExpandBody]

private theorem constantQuotedExpand_markedSeedRows
    (payload : List UnaryFrameSym) (seeds : List TransitionRowSeed) :
    (seeds.flatMap fun seed =>
        encodeUnaryFrame [seed.height, seed.start, seed.rowBase] ++
          [.frameEnd]).flatMap
        (transitionConstantQuotedSeedExpandBody payload).emit =
      seeds.flatMap fun _ =>
        quoteUnaryFrameStream payload ++ [.frameEnd] := by
  induction seeds with
  | nil => rfl
  | cons seed seeds ih =>
      simp only [List.flatMap_cons]
      have hhead :
          (encodeUnaryFrame [seed.height, seed.start, seed.rowBase] ++
              [UnaryFrameSym.frameEnd]).flatMap
                (transitionConstantQuotedSeedExpandBody payload).emit =
            quoteUnaryFrameStream payload ++ [UnaryFrameSym.frameEnd] := by
        rw [List.flatMap_append,
          constantQuotedExpand_encodeUnaryFrame]
        simp [transitionConstantQuotedSeedExpandBody]
      rw [List.flatMap_append]
      rw [hhead, ih]

/-- Exact flat encoding produced by the fixed streaming expander. -/
theorem verifierTransitionConstantQuoted_expand
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (payload : List UnaryFrameSym) (input : List Γ) :
    (verifierTransitionRowMarkedSeedFrames W input).flatMap
        (transitionConstantQuotedSeedExpandBody payload).emit =
      encodeUnaryFrameMarkedRowFamily
        (verifierTransitionConstantQuotedFamily W payload input) := by
  rw [verifierTransitionRowMarkedSeedFrames_eq_seeds]
  rw [constantQuotedExpand_markedSeedRows]
  unfold encodeUnaryFrameMarkedRowFamily
  rw [verifierTransitionConstantQuotedFamily_rows, List.flatMap_map]

/-- Concrete fixed polynomial-time source for constant quoted seed rows. -/
noncomputable def
    verifierTransitionConstantQuotedFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (payload : List UnaryFrameSym) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionConstantQuotedFamily W payload) := by
  let seedCompiler :=
    verifierTransitionRowMarkedSeedFrames_computableInPolyTime W
  let expander := boundedLoop_computableInPolyTime
    (transitionConstantQuotedSeedExpandBody payload)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch seedCompiler
      expander
  let result := Classical.choice composed
  exact
    { tm := result.tm
      inputAlphabet := result.inputAlphabet
      outputAlphabet := result.outputAlphabet
      time := result.time
      outputsFun := fun input => by
        have run := result.outputsFun input
        simp only [Function.comp_apply, id_eq] at run
        rw [verifierTransitionConstantQuoted_expand W payload input] at run
        exact run }

/-- Typed reusable seed-row source. -/
noncomputable def verifierTransitionConstantQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (payload : List UnaryFrameSym) : VerifierTransitionSeedRowSource W where
  row := fun _ => quoteUnaryFrameStream payload
  family := verifierTransitionConstantQuotedFamily W payload
  rows_eq := verifierTransitionConstantQuotedFamily_rows W payload
  computableInPolyTime :=
    verifierTransitionConstantQuotedFamily_computableInPolyTime W payload

end CLRS.Chapter34.Turing.CookLevin
