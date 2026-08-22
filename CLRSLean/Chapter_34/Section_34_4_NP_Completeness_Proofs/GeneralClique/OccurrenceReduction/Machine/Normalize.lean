import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# A concrete CNF normalization pass for the general-CLIQUE reduction

The project source language deliberately gives malformed `CNFSym` strings a
total junk-decoding semantics.  Before occurrence enumeration, one fixed
finite-state transducer turns that raw input into the canonical serialization
of its decoded CNF.  At most two symbols of look-ahead are delayed; the final
action flushes such pending malformed prefixes.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Finite parser modes.  The Boolean records negative polarity. -/
inductive CNFNormalizeMode
  | outside
  | clause
  | pendingPolarity (negative : Bool)
  | pendingVariable (negative : Bool)
  | variableIndex
deriving DecidableEq, Fintype, Repr

/-- Canonical encoding of the junk literal used by `decodeLit`. -/
def junkLiteralEncoding : List CNFSym :=
  [.posMark, .varMark, .endMark]

private def normalizedPolarity (negative : Bool) : CNFSym :=
  if negative then .negMark else .posMark

/-- Process one symbol known to occur at a clause-literal boundary. -/
def normalizeClauseAction (symbol : CNFSym) :
    List CNFSym × CNFNormalizeMode :=
  match symbol with
  | .clauseMark => ([.clauseMark], .clause)
  | .posMark => ([], .pendingPolarity false)
  | .negMark => ([], .pendingPolarity true)
  | .varMark | .endMark => (junkLiteralEncoding, .clause)

/-- Fixed finite-state action implementing the permissive decoder exactly. -/
def cnfNormalizeAction : CNFNormalizeMode → CNFSym →
    List CNFSym × CNFNormalizeMode
  | .outside, .clauseMark => ([.clauseMark], .clause)
  | .outside, _ => ([], .outside)
  | .clause, symbol => normalizeClauseAction symbol
  | .pendingPolarity negative, .varMark =>
      ([], .pendingVariable negative)
  | .pendingPolarity _, symbol =>
      let next := normalizeClauseAction symbol
      (junkLiteralEncoding ++ next.1, next.2)
  | .pendingVariable negative, .endMark =>
      ([normalizedPolarity negative, .varMark, .endMark], .variableIndex)
  | .pendingVariable _, symbol =>
      let next := normalizeClauseAction symbol
      (junkLiteralEncoding ++ junkLiteralEncoding ++ next.1, next.2)
  | .variableIndex, .endMark => ([.endMark], .variableIndex)
  | .variableIndex, symbol => normalizeClauseAction symbol

/-- Flush delayed malformed prefixes at end of input. -/
def cnfNormalizeFinish : CNFNormalizeMode → List CNFSym
  | .pendingPolarity _ => junkLiteralEncoding
  | .pendingVariable _ => junkLiteralEncoding ++ junkLiteralEncoding
  | _ => []

/-- Finite-state normalization specification. -/
def cnfNormalizeSpec :
    StatefulFlatMapSpec CNFNormalizeMode CNFSym CNFSym where
  initial := .outside
  action := cnfNormalizeAction
  finish := cnfNormalizeFinish

@[simp] theorem cnfNormalizeSpec_action (mode : CNFNormalizeMode)
    (symbol : CNFSym) :
    cnfNormalizeSpec.action mode symbol = cnfNormalizeAction mode symbol := rfl

@[simp] theorem cnfNormalizeSpec_finish (mode : CNFNormalizeMode) :
    cnfNormalizeSpec.finish mode = cnfNormalizeFinish mode := rfl

/-- Observable output of the normalization controller. -/
def normalizeCNFInput (input : List CNFSym) : List CNFSym :=
  rewriteStatefulFlatMap cnfNormalizeSpec input

/-! ## A structural specification for the five parser modes -/

mutual
  /-- Canonical continuation while positioned at a literal boundary. -/
  def normalizeClauseStream : List CNFSym → List CNFSym
    | [] => []
    | .clauseMark :: rest => .clauseMark :: normalizeClauseStream rest
    | .posMark :: .varMark :: .endMark :: rest =>
        .posMark :: .varMark :: .endMark :: normalizeVariableIndexStream rest
    | .negMark :: .varMark :: .endMark :: rest =>
        .negMark :: .varMark :: .endMark :: normalizeVariableIndexStream rest
    | _ :: rest => junkLiteralEncoding ++ normalizeClauseStream rest
  termination_by input => (input.length, 0)
  decreasing_by all_goals simp_wf; omega

  /-- Copy the remaining unary index and resume at a literal boundary. -/
  def normalizeVariableIndexStream : List CNFSym → List CNFSym
    | .endMark :: rest => .endMark :: normalizeVariableIndexStream rest
    | input => normalizeClauseStream input
  termination_by input => (input.length, 1)
  decreasing_by all_goals simp_wf; omega
end

/-- Structural normalization before the first clause marker. -/
def normalizeTopStream : List CNFSym → List CNFSym
  | [] => []
  | .clauseMark :: rest => .clauseMark :: normalizeClauseStream rest
  | _ :: rest => normalizeTopStream rest

/-- Structural target denoted by each finite parser mode. -/
def normalizeModeStream : CNFNormalizeMode → List CNFSym → List CNFSym
  | .outside, input => normalizeTopStream input
  | .clause, input => normalizeClauseStream input
  | .pendingPolarity negative, input =>
      normalizeClauseStream (normalizedPolarity negative :: input)
  | .pendingVariable negative, input =>
      normalizeClauseStream
        (normalizedPolarity negative :: .varMark :: input)
  | .variableIndex, input => normalizeVariableIndexStream input

private theorem rewriteCNFNormalizeFrom_eq_modeStream
    (mode : CNFNormalizeMode) (input : List CNFSym) :
    rewriteStatefulFlatMapFrom cnfNormalizeSpec mode input =
      normalizeModeStream mode input := by
  induction input generalizing mode with
  | nil =>
      cases mode with
      | outside | clause | variableIndex =>
          simp [rewriteStatefulFlatMapFrom, cnfNormalizeFinish,
            normalizeModeStream, normalizeTopStream, normalizeClauseStream,
            normalizeVariableIndexStream]
      | pendingPolarity negative | pendingVariable negative =>
          cases negative <;>
            simp [rewriteStatefulFlatMapFrom, cnfNormalizeFinish,
              normalizeModeStream, normalizeClauseStream,
              junkLiteralEncoding, normalizedPolarity]
  | cons symbol rest ih =>
      cases mode with
      | outside | clause | variableIndex =>
          cases symbol <;>
            simp [rewriteStatefulFlatMapFrom, cnfNormalizeAction,
              normalizeClauseAction, normalizeModeStream,
              normalizeTopStream, normalizeClauseStream,
              normalizeVariableIndexStream, junkLiteralEncoding,
              normalizedPolarity, ih]
      | pendingPolarity negative | pendingVariable negative =>
          cases negative <;> cases symbol <;>
            simp [rewriteStatefulFlatMapFrom, cnfNormalizeAction,
              normalizeClauseAction, normalizeModeStream,
              normalizeClauseStream,
              junkLiteralEncoding, normalizedPolarity, ih]

theorem normalizeCNFInput_eq_normalizeTopStream (input : List CNFSym) :
    normalizeCNFInput input = normalizeTopStream input := by
  exact rewriteCNFNormalizeFrom_eq_modeStream .outside input

/-! ## Connection to the project's total CNF decoder -/

private theorem decodeCNFVarIdx_add (start : Nat) (input : List CNFSym) :
    decodeCNFVarIdx start input =
      let decoded := decodeCNFVarIdx 0 input
      (start + decoded.1, decoded.2) := by
  induction input generalizing start with
  | nil => simp [decodeCNFVarIdx]
  | cons symbol rest ih =>
      cases symbol with
      | endMark =>
          simp only [decodeCNFVarIdx]
          rw [ih (start + 1), ih 1]
          rcases hdecoded : decodeCNFVarIdx 0 rest with ⟨count, suffix⟩
          simp [Nat.add_assoc]
      | clauseMark | posMark | negMark | varMark =>
          simp [decodeCNFVarIdx]

private theorem normalizeVariableIndexStream_eq (input : List CNFSym) :
    normalizeVariableIndexStream input =
      let decoded := decodeCNFVarIdx 0 input
      List.replicate decoded.1 CNFSym.endMark ++
        normalizeClauseStream decoded.2 := by
  induction input with
  | nil => simp [normalizeVariableIndexStream, decodeCNFVarIdx]
  | cons symbol rest ih =>
      cases symbol with
      | endMark =>
          simp only [normalizeVariableIndexStream, decodeCNFVarIdx]
          rw [decodeCNFVarIdx_add 1 rest, ih]
          rcases hdecoded : decodeCNFVarIdx 0 rest with ⟨count, suffix⟩
          simp [List.replicate_succ, Nat.add_comm]
      | clauseMark | posMark | negMark | varMark =>
          simp [normalizeVariableIndexStream, decodeCNFVarIdx]

/-- Canonical encoding of the decoded current clause followed by all later
decoded clauses. -/
def encodeDecodedClauseStream (input : List CNFSym) : List CNFSym :=
  (decodeLits input).1.flatMap encLit ++
    encCNF (decodeCNF (decodeLits input).2)

private theorem normalizeClauseStream_eq_encodeDecodedClauseStream
    (input : List CNFSym) :
    normalizeClauseStream input = encodeDecodedClauseStream input := by
  let P : List CNFSym → Prop := fun symbols =>
    normalizeClauseStream symbols = encodeDecodedClauseStream symbols
  have hwf : ∀ n : Nat, ∀ symbols : List CNFSym,
      symbols.length = n → P symbols := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro symbols hlength
        cases symbols with
        | nil =>
            simp [P, normalizeClauseStream, encodeDecodedClauseStream,
              decodeLits, decodeCNF, encCNF]
        | cons symbol rest =>
            have hrest : P rest :=
              ih rest.length (by simp at hlength; omega) rest rfl
            cases symbol with
            | clauseMark =>
                simp [P, normalizeClauseStream, encodeDecodedClauseStream,
                  decodeLits, decodeCNF, encCNF, encClause, hrest]
            | varMark | endMark =>
                simp [P, normalizeClauseStream, encodeDecodedClauseStream,
                  decodeLits, decodeLit, junkLiteralEncoding, encLit,
                  litSym, litIndex, hrest]
            | posMark =>
                cases rest with
                | nil =>
                    simp [P, normalizeClauseStream, encodeDecodedClauseStream,
                      decodeLits, decodeLit, junkLiteralEncoding, encLit,
                      litSym, litIndex, decodeCNF, encCNF]
                | cons second tail =>
                    cases second with
                    | clauseMark | posMark | negMark | endMark =>
                        simpa [P, normalizeClauseStream,
                          encodeDecodedClauseStream, decodeLits, decodeLit,
                          junkLiteralEncoding, encLit, litSym, litIndex] using
                          hrest
                    | varMark =>
                        cases tail with
                        | nil =>
                            simpa [P, normalizeClauseStream,
                              encodeDecodedClauseStream, decodeLits,
                              decodeLit, junkLiteralEncoding, encLit,
                              litSym, litIndex] using hrest
                        | cons third more =>
                            cases third with
                            | clauseMark | posMark | negMark | varMark =>
                                simpa [P, normalizeClauseStream,
                                  encodeDecodedClauseStream, decodeLits,
                                  decodeLit, junkLiteralEncoding, encLit,
                                  litSym, litIndex] using hrest
                            | endMark =>
                                rcases hdecoded : decodeCNFVarIdx 0 more with
                                  ⟨index, suffix⟩
                                have hsuffixLength : suffix.length ≤ more.length := by
                                  have hle := decodeCNFVarIdx_suffix_le 0 more
                                  simpa [hdecoded] using hle
                                have hsuffix : P suffix :=
                                  ih suffix.length (by
                                    simp at hlength
                                    omega) suffix rfl
                                have hindex :=
                                  normalizeVariableIndexStream_eq more
                                rw [hdecoded] at hindex
                                simp [P, normalizeClauseStream,
                                  encodeDecodedClauseStream, decodeLits,
                                  decodeLit, hdecoded, hindex, hsuffix,
                                  encLit, litSym, litIndex,
                                  List.replicate_succ]
            | negMark =>
                cases rest with
                | nil =>
                    simp [P, normalizeClauseStream, encodeDecodedClauseStream,
                      decodeLits, decodeLit, junkLiteralEncoding, encLit,
                      litSym, litIndex, decodeCNF, encCNF]
                | cons second tail =>
                    cases second with
                    | clauseMark | posMark | negMark | endMark =>
                        simpa [P, normalizeClauseStream,
                          encodeDecodedClauseStream, decodeLits, decodeLit,
                          junkLiteralEncoding, encLit, litSym, litIndex] using
                          hrest
                    | varMark =>
                        cases tail with
                        | nil =>
                            simpa [P, normalizeClauseStream,
                              encodeDecodedClauseStream, decodeLits,
                              decodeLit, junkLiteralEncoding, encLit,
                              litSym, litIndex] using hrest
                        | cons third more =>
                            cases third with
                            | clauseMark | posMark | negMark | varMark =>
                                simpa [P, normalizeClauseStream,
                                  encodeDecodedClauseStream, decodeLits,
                                  decodeLit, junkLiteralEncoding, encLit,
                                  litSym, litIndex] using hrest
                            | endMark =>
                                rcases hdecoded : decodeCNFVarIdx 0 more with
                                  ⟨index, suffix⟩
                                have hsuffixLength : suffix.length ≤ more.length := by
                                  have hle := decodeCNFVarIdx_suffix_le 0 more
                                  simpa [hdecoded] using hle
                                have hsuffix : P suffix :=
                                  ih suffix.length (by
                                    simp at hlength
                                    omega) suffix rfl
                                have hindex :=
                                  normalizeVariableIndexStream_eq more
                                rw [hdecoded] at hindex
                                simp [P, normalizeClauseStream,
                                  encodeDecodedClauseStream, decodeLits,
                                  decodeLit, hdecoded, hindex, hsuffix,
                                  encLit, litSym, litIndex,
                                  List.replicate_succ]
  exact hwf input.length input rfl

private theorem normalizeTopStream_eq_encCNF_decodeCNF
    (input : List CNFSym) :
    normalizeTopStream input = encCNF (decodeCNF input) := by
  induction input with
  | nil => simp [normalizeTopStream, decodeCNF, encCNF]
  | cons symbol rest ih =>
      cases symbol with
      | clauseMark =>
          simp [normalizeTopStream, decodeCNF, encCNF, encClause,
            normalizeClauseStream_eq_encodeDecodedClauseStream,
            encodeDecodedClauseStream]
      | posMark | negMark | varMark | endMark =>
          simpa [normalizeTopStream, decodeCNF] using ih

/-- Exact all-input semantics of the concrete normalization TM2. -/
theorem normalizeCNFInput_eq_encCNF_decodeCNF (input : List CNFSym) :
    normalizeCNFInput input = encCNF (decodeCNF input) := by
  rw [normalizeCNFInput_eq_normalizeTopStream,
    normalizeTopStream_eq_encCNF_decodeCNF]

/-- The normalization stream is computed by one fixed polynomial-time TM2. -/
noncomputable def normalizeCNFInput_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id normalizeCNFInput :=
  statefulFlatMap_computableInPolyTime cnfNormalizeSpec

end TMClique
end Turing
end Chapter34
end CLRS
