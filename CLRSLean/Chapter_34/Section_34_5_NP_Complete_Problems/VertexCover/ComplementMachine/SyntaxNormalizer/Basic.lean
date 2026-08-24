import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.ParseSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# Raw graph syntax normalizer: controller

The controller buffers one graph string while running the existing finite
parser.  Valid syntax is restored unchanged.  Invalid syntax is replaced by a
canonical encoding whose target exceeds its empty vertex universe, preserving
rejection information for the later well-formedness guard.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer

open PolyBuilder
open GeneralCliqueVerifier

/-- Canonical syntax with deliberately false graph well-formedness. -/
def malformedGraphSentinel : CliqueInstance where
  vertexCount := 0
  targetSize := 1
  edges := []

/-- The sentinel is rejected by the shared target-bound invariant. -/
theorem malformedGraphSentinel_not_wellFormed :
    ¬malformedGraphSentinel.WellFormed := by
  simp [malformedGraphSentinel, CliqueInstance.WellFormed]

/-- Complete-grammar verdict for a final instance-parser mode. -/
def accepts (mode : ParseMode) : Bool :=
  mode.valid && decide (mode.grammar = .instanceEdges)

/-- Pure stream computed by the controller. -/
def normalizedStream (input : List CliqueSym) : List CliqueSym :=
  if accepts (scanSymbols initialInstanceParseMode input) then input
  else encodeCliqueInstance malformedGraphSentinel

/-- Finite control for parsing, buffering, restoring, or emitting the fixed
four-symbol sentinel encoding. -/
inductive Label
  | scan (mode : ParseMode)
  | save (mode : ParseMode) (symbol : CliqueSym)
  | restore
  | emit (symbol : CliqueSym)
  | clear
  | fallbackFinalSep
  | fallbackTargetTick
  | fallbackFieldSep
  | fallbackInstanceMark
  | halt
deriving DecidableEq, Fintype

/-- Fixed syntax-normalizer controller. -/
def program : Program CliqueSym CliqueSym where
  Label := Label
  main := .scan initialInstanceParseMode
  op
    | .scan mode => .popInput
        (if accepts mode then .restore else .clear)
        (fun symbol => .save (stepSymbol mode symbol) symbol)
    | .save mode symbol => .pushWork₁ symbol (.scan mode)
    | .restore => .popWork₁ .halt .emit
    | .emit symbol => .pushOutput symbol .restore
    | .clear => .popWork₁ .fallbackFinalSep (fun _ => .clear)
    | .fallbackFinalSep => .pushOutput .fieldSep .fallbackTargetTick
    | .fallbackTargetTick => .pushOutput .tick .fallbackFieldSep
    | .fallbackFieldSep => .pushOutput .fieldSep .fallbackInstanceMark
    | .fallbackInstanceMark => .pushOutput .instanceMark .halt
    | .halt => .halt

/-- Proof-facing controller configuration. -/
def cfg (label : Label) (buffer₁ buffer₂ : Option CliqueSym)
    (test : Bool) (input output work₁ work₂ : List CliqueSym) :
    BuilderCfg program where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer
