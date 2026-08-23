import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.ParseSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import Mathlib.Tactic.DeriveFintype

/-!
# General CLIQUE verifier: raw-input canonicalizer

The final verifier must be total on arbitrary certificate and instance
strings, whereas the arithmetic submachines consume canonical encodings.  The
fixed controller below buffers one raw string, validates it with the existing
finite parser, and either restores it unchanged or emits a fixed empty object.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

open PolyBuilder

/-- Which standalone CLIQUE grammar is being canonicalized. -/
abbrev Kind := ParseSide

/-- Initial parser mode for the selected standalone grammar. -/
def initialMode : Kind → ParseMode
  | .certificate => initialParseMode
  | .instance => initialInstanceParseMode

/-- Complete-grammar verdict for a final parser mode. -/
def accepts : Kind → ParseMode → Bool
  | .certificate, mode =>
      mode.valid && decide (mode.grammar = .certificateVertices)
  | .instance, mode =>
      mode.valid && decide (mode.grammar = .instanceEdges)

/-- Fixed fallback string for a malformed standalone object. -/
def fallback : Kind → List CliqueSym
  | .certificate => encodeCliqueCertificate []
  | .instance => encodeCliqueInstance
      { vertexCount := 0, targetSize := 0, edges := [] }

/-- Pure total canonicalization performed by the concrete controller. -/
def canonicalStream (kind : Kind) (input : List CliqueSym) : List CliqueSym :=
  if accepts kind (scanSymbols (initialMode kind) input) then input
  else fallback kind

/-- Finite control for buffering, restoring, and emitting either fallback. -/
inductive Label
  | scan (mode : ParseMode)
  | save (mode : ParseMode) (symbol : CliqueSym)
  | restore | emit (symbol : CliqueSym) | clear
  | fallbackCertificate
  | fallbackInstanceSep₁ | fallbackInstanceSep₂ | fallbackInstanceMark
  | halt
deriving DecidableEq, Fintype

/-- One fixed controller per grammar kind. -/
def program (kind : Kind) : Program CliqueSym CliqueSym where
  Label := Label
  main := .scan (initialMode kind)
  op
    | .scan mode => .popInput
        (if accepts kind mode then .restore else .clear)
        (fun symbol => .save (stepSymbol mode symbol) symbol)
    | .save mode symbol => .pushWork₁ symbol (.scan mode)
    | .restore => .popWork₁ .halt .emit
    | .emit symbol => .pushOutput symbol .restore
    | .clear => .popWork₁
        (match kind with
          | .certificate => .fallbackCertificate
          | .instance => .fallbackInstanceSep₁)
        (fun _ => .clear)
    | .fallbackCertificate => .pushOutput .certificateMark .halt
    | .fallbackInstanceSep₁ => .pushOutput .fieldSep .fallbackInstanceSep₂
    | .fallbackInstanceSep₂ => .pushOutput .fieldSep .fallbackInstanceMark
    | .fallbackInstanceMark => .pushOutput .instanceMark .halt
    | .halt => .halt

/-- Proof-facing configuration for the canonicalizer. -/
def cfg (kind : Kind) (label : Label)
    (buffer₁ buffer₂ : Option CliqueSym) (test : Bool)
    (input output work₁ work₂ : List CliqueSym) :
    BuilderCfg (program kind) where
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

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer
