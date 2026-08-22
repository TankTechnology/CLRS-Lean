import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Normalize

/-!
# Concrete three-CNF width checking

A fixed finite-state pass checks the at-most-three-literals convention on a
canonical CNF stream.  Composing it with raw-input normalization gives an
exact Boolean flag for every source word, including malformed encodings.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Saturated width of the current canonical clause. -/
inductive ThreeCNFWidth
  | zero | one | two | three | overflow
deriving DecidableEq, Fintype, Repr

/-- Finite control remembers the current width and whether every completed
prefix has respected the width bound. -/
structure ThreeCNFCheckMode where
  valid : Bool
  width : ThreeCNFWidth
deriving DecidableEq, Fintype, Repr

private def advanceThreeCNFWidth : ThreeCNFWidth → ThreeCNFWidth
  | .zero => .one
  | .one => .two
  | .two => .three
  | .three | .overflow => .overflow

private def threeCNFWidthAcceptsLiteral : ThreeCNFWidth → Bool
  | .zero | .one | .two => true
  | .three | .overflow => false

/-- One finite-control transition over the canonical CNF alphabet. -/
def threeCNFCheckStep (mode : ThreeCNFCheckMode) : CNFSym → ThreeCNFCheckMode
  | .clauseMark => { mode with width := .zero }
  | .posMark | .negMark =>
      { valid := mode.valid && threeCNFWidthAcceptsLiteral mode.width
        width := advanceThreeCNFWidth mode.width }
  | .varMark | .endMark => mode

/-- Finite-state flat-map specification emitting only the terminal flag. -/
def threeCNFCheckSpec :
    StatefulFlatMapSpec ThreeCNFCheckMode CNFSym Bool where
  initial := { valid := true, width := .zero }
  action mode symbol := ([], threeCNFCheckStep mode symbol)
  finish mode := [mode.valid]

@[simp] theorem threeCNFCheckSpec_action (mode : ThreeCNFCheckMode)
    (symbol : CNFSym) :
    threeCNFCheckSpec.action mode symbol =
      ([], threeCNFCheckStep mode symbol) := rfl

@[simp] theorem threeCNFCheckSpec_finish (mode : ThreeCNFCheckMode) :
    threeCNFCheckSpec.finish mode = [mode.valid] := rfl

/-- Pure final control state of the width scan. -/
def runThreeCNFCheck : ThreeCNFCheckMode → List CNFSym → ThreeCNFCheckMode
  | mode, [] => mode
  | mode, symbol :: rest =>
      runThreeCNFCheck (threeCNFCheckStep mode symbol) rest

/-- Width-check flag on an already canonical CNF stream. -/
def threeCNFFlag (input : List CNFSym) : List Bool :=
  rewriteStatefulFlatMap threeCNFCheckSpec input

/-- Width-check flag generated directly from an arbitrary raw CNF word. -/
def canonicalThreeCNFFlag (input : List CNFSym) : List Bool :=
  threeCNFFlag (normalizeCNFInput input)

private theorem rewriteThreeCNFCheckFrom_eq (mode : ThreeCNFCheckMode)
    (input : List CNFSym) :
    rewriteStatefulFlatMapFrom threeCNFCheckSpec mode input =
      [(runThreeCNFCheck mode input).valid] := by
  induction input generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      simp [rewriteStatefulFlatMapFrom, ih, runThreeCNFCheck]

private theorem runThreeCNFCheck_append (mode : ThreeCNFCheckMode)
    (left right : List CNFSym) :
    runThreeCNFCheck mode (left ++ right) =
      runThreeCNFCheck (runThreeCNFCheck mode left) right := by
  induction left generalizing mode with
  | nil => rfl
  | cons symbol rest ih =>
      simpa [runThreeCNFCheck] using
        ih (threeCNFCheckStep mode symbol)

private theorem runThreeCNFCheck_replicate_endMark
    (mode : ThreeCNFCheckMode) (count : Nat) (suffix : List CNFSym) :
    runThreeCNFCheck mode
        (List.replicate count CNFSym.endMark ++ suffix) =
      runThreeCNFCheck mode suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simpa [List.replicate_succ, runThreeCNFCheck,
        threeCNFCheckStep] using ih

@[simp] private theorem runThreeCNFCheck_encLit (mode : ThreeCNFCheckMode)
    (literal : Literal) (suffix : List CNFSym) :
    runThreeCNFCheck mode (encLit literal ++ suffix) =
      runThreeCNFCheck
        { valid := mode.valid && threeCNFWidthAcceptsLiteral mode.width
          width := advanceThreeCNFWidth mode.width }
        suffix := by
  cases literal <;>
    simp [encLit, litSym, runThreeCNFCheck,
      threeCNFCheckStep, runThreeCNFCheck_replicate_endMark]

@[simp] private theorem runThreeCNFCheck_encLit_only
    (mode : ThreeCNFCheckMode) (literal : Literal) :
    runThreeCNFCheck mode (encLit literal) =
      { valid := mode.valid && threeCNFWidthAcceptsLiteral mode.width
        width := advanceThreeCNFWidth mode.width } := by
  simpa [runThreeCNFCheck] using runThreeCNFCheck_encLit mode literal []

private theorem runThreeCNFCheck_invalid (width : ThreeCNFWidth)
    (input : List CNFSym) :
    (runThreeCNFCheck { valid := false, width } input).valid = false := by
  induction input generalizing width with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol <;> cases width <;>
        simp [runThreeCNFCheck, threeCNFCheckStep,
          threeCNFWidthAcceptsLiteral, ih]

private theorem runThreeCNFCheck_encClause_valid
    (mode : ThreeCNFCheckMode) (clause : Clause) :
    (runThreeCNFCheck mode (encClause clause)).valid =
      (mode.valid && decide (clause.length ≤ 3)) := by
  cases clause with
  | nil => simp [encClause, runThreeCNFCheck, threeCNFCheckStep]
  | cons first rest =>
      cases rest with
      | nil =>
          simp [encClause, runThreeCNFCheck,
            threeCNFCheckStep, threeCNFWidthAcceptsLiteral,
            advanceThreeCNFWidth]
      | cons second rest =>
          cases rest with
          | nil =>
              simp [encClause, runThreeCNFCheck,
                threeCNFCheckStep, runThreeCNFCheck_append,
                threeCNFWidthAcceptsLiteral, advanceThreeCNFWidth]
          | cons third rest =>
              cases rest with
              | nil =>
                  simp [encClause, runThreeCNFCheck,
                    threeCNFCheckStep, runThreeCNFCheck_append,
                    threeCNFWidthAcceptsLiteral, advanceThreeCNFWidth]
              | cons fourth rest =>
                  simp [encClause, runThreeCNFCheck,
                    threeCNFCheckStep, runThreeCNFCheck_append,
                    threeCNFWidthAcceptsLiteral, advanceThreeCNFWidth,
                    runThreeCNFCheck_invalid]

private theorem runThreeCNFCheck_encCNF_valid
    (mode : ThreeCNFCheckMode) (formula : CNF) :
    (runThreeCNFCheck mode (encCNF formula)).valid =
      (mode.valid && decide (IsThreeCNF formula)) := by
  induction formula generalizing mode with
  | nil => simp [encCNF, runThreeCNFCheck, IsThreeCNF]
  | cons clause formula ih =>
      rw [show encCNF (clause :: formula) =
          encClause clause ++ encCNF formula by rfl,
        runThreeCNFCheck_append, ih,
        runThreeCNFCheck_encClause_valid]
      have hcons : IsThreeCNF (clause :: formula) ↔
          clause.length ≤ 3 ∧ IsThreeCNF formula := by
        simp [IsThreeCNF]
      by_cases hclause : clause.length ≤ 3 <;>
        by_cases hformula : IsThreeCNF formula <;>
          simp [hcons, hclause, hformula]

/-- Exact flag semantics on a canonical formula encoding. -/
theorem threeCNFFlag_encCNF (formula : CNF) :
    threeCNFFlag (encCNF formula) = [decide (IsThreeCNF formula)] := by
  rw [threeCNFFlag, rewriteStatefulFlatMap,
    rewriteThreeCNFCheckFrom_eq, runThreeCNFCheck_encCNF_valid]
  simp [threeCNFCheckSpec]

/-- Exact all-input semantics after the concrete normalization pass. -/
theorem canonicalThreeCNFFlag_eq (input : List CNFSym) :
    canonicalThreeCNFFlag input = [decide (IsThreeCNF (decodeCNF input))] := by
  rw [canonicalThreeCNFFlag, normalizeCNFInput_eq_encCNF_decodeCNF,
    threeCNFFlag_encCNF]

/-- The canonical width flag is computed by a fixed polynomial-time TM2. -/
noncomputable def canonicalThreeCNFFlag_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id canonicalThreeCNFFlag := by
  let checker : _root_.Turing.TM2ComputableInPolyTime id id threeCNFFlag :=
    statefulFlatMap_computableInPolyTime threeCNFCheckSpec
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      normalizeCNFInput_computableInPolyTime checker
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => threeCNFFlag (normalizeCNFInput input))
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS
