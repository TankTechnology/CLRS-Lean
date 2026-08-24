import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer.Simulation
import Mathlib.Tactic

/-!
# Raw graph syntax normalizer: complete run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer

open PolyBuilder
open GeneralCliqueVerifier

/-- Exact branch-sensitive cost of one complete normalization. -/
def steps (input : List CliqueSym) : Nat :=
  if accepts (scanSymbols initialInstanceParseMode input) then
    4 * input.length + 3
  else
    3 * input.length + 7

/-- The fixed controller halts on every raw graph string with the pure
syntax-normalized stream. -/
def run (input : List CliqueSym) :
    EvalsToInTime (step program)
      (initialCfg program input)
      (some (haltCfg program (normalizedStream input)))
      (steps input) := by
  rcases scan_run initialInstanceParseMode input [] [] none none false with
    ⟨finalBuffer, scanned⟩
  have scanned' : EvalsToInTime (step program)
      (initialCfg program input)
      (some (cfg (.scan (scanSymbols initialInstanceParseMode input))
        finalBuffer none false [] [] input.reverse []))
      (2 * input.length) := by
    simpa [initialCfg, cfg, program] using scanned
  by_cases haccepts :
      accepts (scanSymbols initialInstanceParseMode input) = true
  · have finish : EvalsToInTime (step program)
        (cfg (.scan (scanSymbols initialInstanceParseMode input))
          finalBuffer none false [] [] input.reverse [])
        (some (cfg .restore none none false [] [] input.reverse [])) 1 :=
      ⟨⟨1, by simp [flip, step, program, cfg, stepOp, haccepts]⟩, le_rfl⟩
    have restored := restore_run input.reverse [] none none false
    have restored' : EvalsToInTime (step program)
        (cfg .restore none none false [] [] input.reverse [])
        (some (haltCfg program input))
        (2 * input.length + 2) := by
      simpa using restored
    let first := EvalsToInTime.trans (step program)
      (2 * input.length) 1 _ _ _ scanned' finish
    let full := EvalsToInTime.trans (step program)
      _ (2 * input.length + 2) _ _ _ first restored'
    convert full using 1
    all_goals simp [steps, normalizedStream, haccepts, Nat.add_comm,
      Nat.add_left_comm]
    omega
  · have hacceptsFalse :
        accepts (scanSymbols initialInstanceParseMode input) = false :=
      Bool.eq_false_of_not_eq_true haccepts
    have finish : EvalsToInTime (step program)
        (cfg (.scan (scanSymbols initialInstanceParseMode input))
          finalBuffer none false [] [] input.reverse [])
        (some (cfg .clear none none false [] [] input.reverse [])) 1 :=
      ⟨⟨1, by simp [flip, step, program, cfg, stepOp, hacceptsFalse]⟩,
        le_rfl⟩
    have cleared := clear_run input.reverse [] none none false
    let first := EvalsToInTime.trans (step program)
      (2 * input.length) 1 _ _ _ scanned' finish
    let second := EvalsToInTime.trans (step program)
      _ (input.length + 1) _ _ _ first (by simpa using cleared)
    have fallbackRun := fallback_run [] none none false
    let full := EvalsToInTime.trans (step program)
      _ 5 _ _ _ second fallbackRun
    convert full using 1
    all_goals simp [steps, normalizedStream, hacceptsFalse, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]
    omega

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer
