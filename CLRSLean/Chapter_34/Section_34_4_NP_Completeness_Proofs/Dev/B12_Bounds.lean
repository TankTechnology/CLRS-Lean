import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B11_CopyOut
import Mathlib.Computability.TuringMachine.Computable

/-!
# Dev B12: polynomial-time bounds

The mathematical resource bounds used by the full SAT-to-3-CNF machine run: `to3CNF'_bounds`, `parseSteps_le`, the decoder bounds, `encCNF_to3CNF'_le`, and `satTo3CNFTime`.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- polynomial time: arithmetic and encoding-size bounds
-- ============================================================

/-- Both the value variable and the next auxiliary index of a formula are
bounded by `c` plus the encoding length. -/
lemma to3CNF'_bounds (f : Formula) (c : Nat) :
    (to3CNF' f c).2.1 ≤ c + (enc f).length ∧
    (to3CNF' f c).2.2 ≤ c + (enc f).length := by
  induction f generalizing c with
  | var i =>
      constructor <;> simp [to3CNF', enc, varEnc] <;> omega
  | const b =>
      by_cases hb : b
      · constructor <;> simp [to3CNF', hb, forceTrue, forceFalse, enc] <;> omega
      · constructor <;> simp [to3CNF', hb, forceTrue, forceFalse, enc] <;> omega
  | not f' ih =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ih c).2]
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ih c).2]
  | and f' g' ihf ihg =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ihf c).2, (ihg (to3CNF' f' c).2.2).2]
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ihf c).2, (ihg (to3CNF' f' c).2.2).2]
  | or f' g' ihf ihg =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ihf c).2, (ihg (to3CNF' f' c).2.2).2]
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ihf c).2, (ihg (to3CNF' f' c).2.2).2]
  | iff f' g' ihf ihg =>
      constructor
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ihf c).2, (ihg (to3CNF' f' c).2.2).2]
      · simp [to3CNF', enc, List.length_cons]
        nlinarith [(ihf c).2, (ihg (to3CNF' f' c).2.2).2]

/-- The number of clauses in the Tseitin encoding is at most four per node of
the formula.  Each node contributes at most four clauses (`iff` contributes
four, `and`/`or` three, `not` two, `const` one) and at least one symbol to the
encoding. -/
lemma to3CNF'_clauses_num_le (f : Formula) (c : Nat) :
    (to3CNF' f c).1.length ≤ 4 * (enc f).length := by
  induction f generalizing c with
  | var i => simp [to3CNF', enc, varEnc]
  | const b => by_cases hb : b <;> simp [to3CNF', hb, forceTrue, forceFalse, enc]
  | not f' ih =>
      simp [to3CNF', enc, notClauses, List.length_cons]
      nlinarith [ih c]
  | and f' g' ihf ihg =>
      simp [to3CNF', enc, andClauses, List.length_cons]
      nlinarith [ihf c, ihg (to3CNF' f' c).2.2]
  | or f' g' ihf ihg =>
      simp [to3CNF', enc, orClauses, List.length_cons]
      nlinarith [ihf c, ihg (to3CNF' f' c).2.2]
  | iff f' g' ihf ihg =>
      simp [to3CNF', enc, iffClauses, List.length_cons]
      nlinarith [ihf c, ihg (to3CNF' f' c).2.2]

/-- The parse step count is bounded by a quadratic in the encoding length. -/
lemma parseSteps_le (f : Formula) (c : Nat) :
    parseSteps f c ≤ 40 * (enc f).length * (c + (enc f).length + 1) := by
  induction f generalizing c with
  | var i =>
      simp [parseSteps, enc, varEnc]
      nlinarith
  | const b =>
      by_cases hb : b <;> simp [parseSteps, enc, hb] <;> omega
  | not f' ih =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hb := to3CNF'_bounds f' c
      rcases ht1 : to3CNF' f' c with ⟨cl, y1, c1⟩
      simp [ht1] at hb
      rcases hb with ⟨hy, hc1⟩
      have hsteps : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ih c
      simp [parseSteps, enc, ht1]
      nlinarith
  | and f' g' ihf ihg =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by
        cases g' <;> simp [enc, varEnc]
      have hb1 := to3CNF'_bounds f' c
      rcases ht2 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      simp [ht2] at hb1
      rcases hb1 with ⟨hy1, hc1⟩
      have hb2 := to3CNF'_bounds g' c1
      rcases ht3 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      simp [ht3] at hb2
      rcases hb2 with ⟨hy2, hc2⟩
      have hf : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ihf c
      have hg : parseSteps g' c1 ≤ 40 * (enc g').length * (c1 + (enc g').length + 1) := ihg c1
      simp [parseSteps, enc, ht2, ht3]
      nlinarith
  | or f' g' ihf ihg =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by
        cases g' <;> simp [enc, varEnc]
      have hb1 := to3CNF'_bounds f' c
      rcases ht4 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      simp [ht4] at hb1
      rcases hb1 with ⟨hy1, hc1⟩
      have hb2 := to3CNF'_bounds g' c1
      rcases ht5 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      simp [ht5] at hb2
      rcases hb2 with ⟨hy2, hc2⟩
      have hf : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ihf c
      have hg : parseSteps g' c1 ≤ 40 * (enc g').length * (c1 + (enc g').length + 1) := ihg c1
      simp [parseSteps, enc, ht4, ht5]
      nlinarith
  | iff f' g' ihf ihg =>
      have hn : (enc f').length ≥ 1 := by
        cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by
        cases g' <;> simp [enc, varEnc]
      have hb1 := to3CNF'_bounds f' c
      rcases ht6 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      simp [ht6] at hb1
      rcases hb1 with ⟨hy1, hc1⟩
      have hb2 := to3CNF'_bounds g' c1
      rcases ht7 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      simp [ht7] at hb2
      rcases hb2 with ⟨hy2, hc2⟩
      have hf : parseSteps f' c ≤ 40 * (enc f').length * (c + (enc f').length + 1) := ihf c
      have hg : parseSteps g' c1 ≤ 40 * (enc g').length * (c1 + (enc g').length + 1) := ihg c1
      simp [parseSteps, enc, ht6, ht7]
      nlinarith

/-- `decodeAux` decodes a formula whose encoding is bounded by twice the number
of consumed symbols plus one.  The constant is forced to `1`: composing the
`2·consumed + 1` bounds of two subformulas under a binary node gives
`2·(consumed₁ + consumed₂ + 1) + 1`, exactly the bound for the combined
consumption. -/
lemma decodeAux_enc_consumed_le (n : Nat) (l : List FormulaSym) :
    (enc (decodeAux n l).1).length ≤ 2 * (l.length - (decodeAux n l).2.length) + 1 := by
  revert n
  refine WellFounded.induction (measure List.length).wf l
    (C := fun l' => ∀ (n : Nat),
      (enc (decodeAux n l').1).length ≤ 2 * (l'.length - (decodeAux n l').2.length) + 1) ?_
  intro l ih n
  cases l with
  | nil => cases n <;> simp [decodeAux, enc]
  | cons s rest =>
      have hlt_rest : rest.length < (s :: rest).length := by
        simp [List.length_cons]
      cases n with
      | zero => simp [decodeAux, enc]
      | succ n' =>
          cases s with
          | lit _ => simp [decodeAux, enc]
          | varMark =>
              by_cases h : rest.head? = some FormulaSym.endMark
              · rcases hrun : endMarkRun rest with ⟨k, suf⟩
                have hspec := endMarkRun_spec rest
                rw [hrun] at hspec
                have hrep : rest = List.replicate k FormulaSym.endMark ++ suf := hspec.1
                have hk : 1 ≤ k := by
                  by_contra hk0
                  have hk0' : k = 0 := by omega
                  have : rest = suf := by
                    rw [hk0'] at hrep
                    simpa using hrep
                  rw [this] at h
                  exact hspec.2 h
                have hdec := decodeVar_endMarkRun rest k suf hk hrun
                have hlen : rest.length = k + suf.length := by
                  rw [hrep]
                  simp [List.length_replicate, List.length_append]
                have hk1 : k ≤ rest.length := by omega
                simp [decodeAux, hdec, enc, varEnc]
                omega
              · cases rest with
                | nil => simp [decodeAux, decodeVar, enc]
                | cons s0 t =>
                    have hsne : s0 ≠ FormulaSym.endMark := by
                      intro hse
                      simp [hse] at h
                    simp [decodeAux, decodeVar, enc, hsne]
          | endMark => simp [decodeAux, enc]
          | notMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              simp [decodeAux, enc, List.length_cons]
              omega
          | andMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                  2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 1 :=
                ih (decodeAux n' rest).2
                  (Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) hlt_rest) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                decodeAux_suffix_le n' (decodeAux n' rest).2
              simp [decodeAux, enc, List.length_cons]
              omega
          | orMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                  2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 1 :=
                ih (decodeAux n' rest).2
                  (Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) hlt_rest) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                decodeAux_suffix_le n' (decodeAux n' rest).2
              simp [decodeAux, enc, List.length_cons]
              omega
          | iffMark =>
              have h1 : (enc (decodeAux n' rest).1).length ≤
                  2 * (rest.length - (decodeAux n' rest).2.length) + 1 :=
                ih rest hlt_rest n'
              have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                  2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 1 :=
                ih (decodeAux n' rest).2
                  (Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) hlt_rest) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                decodeAux_suffix_le n' (decodeAux n' rest).2
              simp [decodeAux, enc, List.length_cons]
              omega

/-- The encoding of the decoded formula is at most double the input plus three. -/
lemma enc_decode_le (x : List FormulaSym) :
    (enc (decode x)).length ≤ 2 * x.length + 3 := by
  have h := decodeAux_enc_consumed_le x.length x
  have hle : x.length - (decodeAux x.length x).2.length ≤ x.length := by omega
  simpa [decode] using (by omega : (enc (decodeAux x.length x).1).length ≤ 2 * x.length + 3)

/-- The number of original variables of a decoded formula is at most the input
length. -/
lemma numVars_decode_le (x : List FormulaSym) : numVars (decode x) ≤ x.length := by
  let P : List FormulaSym → Prop := fun l => ∀ n, numVars (decodeAux n l).1 ≤ l.length
  have hP : P x := by
    dsimp [P]
    refine WellFounded.induction (measure (fun l : List FormulaSym => l.length)).wf x
        (C := fun l => ∀ n, numVars (decodeAux n l).1 ≤ l.length) ?_
    intro l ih
    intro n
    cases l with
    | nil => cases n <;> simp [decodeAux, numVars]
    | cons s rest =>
        cases n with
        | zero => simp [decodeAux, numVars]
        | succ n' =>
            cases s with
            | lit _ => simp [decodeAux, numVars]
            | varMark =>
                by_cases h : rest.head? = some FormulaSym.endMark
                · rcases hrun : endMarkRun rest with ⟨k, suf⟩
                  have hspec := endMarkRun_spec rest
                  rw [hrun] at hspec
                  have hrep : rest = List.replicate k FormulaSym.endMark ++ suf := hspec.1
                  have hk : 1 ≤ k := by
                    by_contra hk0
                    have hk0' : k = 0 := by omega
                    have : rest = suf := by
                      rw [hk0'] at hrep
                      simpa using hrep
                    rw [this] at h
                    exact hspec.2 h
                  have hdec := decodeVar_endMarkRun rest k suf hk hrun
                  have hlen : rest.length = k + suf.length := by
                    rw [hrep]
                    simp [List.length_replicate, List.length_append]
                  simp [decodeAux, hdec, numVars]
                  omega
                · cases rest with
                  | nil => simp [decodeAux, decodeVar, numVars]
                  | cons s0 t =>
                      have hsne : s0 ≠ FormulaSym.endMark := by
                        intro hse
                        simp [hse] at h
                      simp [decodeAux, decodeVar, numVars, hsne]
            | endMark => simp [decodeAux, numVars]
            | notMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.notMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                simp [decodeAux, numVars]
                omega
            | andMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.andMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                    (decodeAux n' rest).2.length := by
                  refine ih (decodeAux n' rest).2 ?_ n'
                  change (decodeAux n' rest).2.length < (FormulaSym.andMark :: rest).length
                  simpa [List.length_cons] using
                    Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) (Nat.lt_succ_self rest.length)
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                simp [decodeAux, numVars]
                omega
            | orMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.orMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                    (decodeAux n' rest).2.length := by
                  refine ih (decodeAux n' rest).2 ?_ n'
                  change (decodeAux n' rest).2.length < (FormulaSym.orMark :: rest).length
                  simpa [List.length_cons] using
                    Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) (Nat.lt_succ_self rest.length)
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                simp [decodeAux, numVars]
                omega
            | iffMark =>
                have h1 : numVars (decodeAux n' rest).1 ≤ rest.length :=
                  ih rest (by
                    change rest.length < (FormulaSym.iffMark :: rest).length
                    simpa [List.length_cons] using Nat.lt_succ_self rest.length) n'
                have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                    (decodeAux n' rest).2.length := by
                  refine ih (decodeAux n' rest).2 ?_ n'
                  change (decodeAux n' rest).2.length < (FormulaSym.iffMark :: rest).length
                  simpa [List.length_cons] using
                    Nat.lt_of_le_of_lt (decodeAux_suffix_le n' rest) (Nat.lt_succ_self rest.length)
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                simp [decodeAux, numVars]
                omega
  simpa [decode, P] using hP x.length
/-- The encoded Tseitin clauses are bounded by a quadratic in the encoding
length. -/
lemma encCNF_to3CNF'_le (f : Formula) (c : Nat) :
    (encCNF (to3CNF' f c).1).length ≤
      12 * (enc f).length * (c + (enc f).length + 1) + 6 * (enc f).length := by
  induction f generalizing c with
  | var i => simp [to3CNF', enc, varEnc, encCNF]
  | const b => by_cases hb : b <;> simp [to3CNF', hb, enc, encCNF, forceTrue, forceFalse, encClause, encLit, litSym, litIndex] <;> omega
  | not f' ih =>
      rcases h : to3CNF' f' c with ⟨cl, y1, c1⟩
      have hc : (encCNF cl).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h] using ih c
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h] using (to3CNF'_bounds f' c).1
      have hc1 : c1 ≤ c + (enc f').length := by simpa [h] using (to3CNF'_bounds f' c).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h] at hg
        exact hg
      have hcl : cl.length ≤ 4 * (enc f').length := by simpa [h] using to3CNF'_clauses_num_le f' c
      have hnotc : (encCNF (notClauses c1 y1)).length ≤ 12 * (c + (enc f').length + 1) + 30 := by
        simp [encCNF, notClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl ++ notClauses c1 y1)).length =
          (encCNF cl).length + (encCNF (notClauses c1 y1)).length := by
        simp [encCNF, List.length_append, List.flatMap_append]
      simp [to3CNF', enc, h]
      nlinarith [hsplit]
  | and f' g' ihf ihg =>
      rcases h1 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases h2 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h1] using ihf c
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa [h2] using ihg c1
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by cases g' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).1
      have hc1' : c1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).2
      have hy2 : y2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).1
      have hc2' : c2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h1] at hg
        exact hg
      have hcl1 : cl1.length ≤ 4 * (enc f').length := by simpa [h1] using to3CNF'_clauses_num_le f' c
      have hcl2 : cl2.length ≤ 4 * (enc g').length := by simpa [h2] using to3CNF'_clauses_num_le g' c1
      have hclc : (encCNF (andClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 30 := by
        simp [encCNF, andClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl1 ++ (cl2 ++ andClauses c2 y1 y2))).length =
          (encCNF cl1).length + (encCNF cl2).length + (encCNF (andClauses c2 y1 y2)).length := by
        simp [encCNF, List.length_append, List.flatMap_append, Nat.add_assoc]
      simp [to3CNF', enc, h1, h2]
      nlinarith [hsplit]
  | or f' g' ihf ihg =>
      rcases h1 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases h2 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h1] using ihf c
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa [h2] using ihg c1
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by cases g' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).1
      have hc1' : c1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).2
      have hy2 : y2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).1
      have hc2' : c2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h1] at hg
        exact hg
      have hcl1 : cl1.length ≤ 4 * (enc f').length := by simpa [h1] using to3CNF'_clauses_num_le f' c
      have hcl2 : cl2.length ≤ 4 * (enc g').length := by simpa [h2] using to3CNF'_clauses_num_le g' c1
      have hclc : (encCNF (orClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 30 := by
        simp [encCNF, orClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl1 ++ (cl2 ++ orClauses c2 y1 y2))).length =
          (encCNF cl1).length + (encCNF cl2).length + (encCNF (orClauses c2 y1 y2)).length := by
        simp [encCNF, List.length_append, List.flatMap_append, Nat.add_assoc]
      simp [to3CNF', enc, h1, h2]
      nlinarith [hsplit]
  | iff f' g' ihf ihg =>
      rcases h1 : to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases h2 : to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa [h1] using ihf c
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa [h2] using ihg c1
      have hn : (enc f').length ≥ 1 := by cases f' <;> simp [enc, varEnc]
      have hn2 : (enc g').length ≥ 1 := by cases g' <;> simp [enc, varEnc]
      have hy1 : y1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).1
      have hc1' : c1 ≤ c + (enc f').length := by simpa [h1] using (to3CNF'_bounds f' c).2
      have hy2 : y2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).1
      have hc2' : c2 ≤ c1 + (enc g').length := by simpa [h2] using (to3CNF'_bounds g' c1).2
      have hnext : c ≤ c1 := by
        have hg := to3CNF'_next_ge f' c
        rw [h1] at hg
        exact hg
      have hcl1 : cl1.length ≤ 4 * (enc f').length := by simpa [h1] using to3CNF'_clauses_num_le f' c
      have hcl2 : cl2.length ≤ 4 * (enc g').length := by simpa [h2] using to3CNF'_clauses_num_le g' c1
      have hclc : (encCNF (iffClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 40 := by
        simp [encCNF, iffClauses, encClause, encLit, litSym, litIndex]
        nlinarith
      have hsplit : (encCNF (cl1 ++ (cl2 ++ iffClauses c2 y1 y2))).length =
          (encCNF cl1).length + (encCNF cl2).length + (encCNF (iffClauses c2 y1 y2)).length := by
        simp [encCNF, List.length_append, List.flatMap_append, Nat.add_assoc]
      simp [to3CNF', enc, h1, h2]
      nlinarith [hsplit]
/-- The input alphabet of the machine is `FormulaSym`. -/
def satInputAlphabet : (mach).Γ (mach).k₀ ≃ FormulaSym := Equiv.refl _

/-- The output alphabet of the machine is `CNFSym`. -/
def satOutputAlphabet : (mach).Γ (mach).k₁ ≃ CNFSym := Equiv.refl _

/-- The polynomial time bound. -/
noncomputable def satTo3CNFTime : Polynomial ℕ :=
  800 * Polynomial.X ^ 2 + 3000 * Polynomial.X + 2000

/-- Evaluation of the explicit time polynomial as natural-number arithmetic. -/
lemma satTo3CNFTime_eval (n : Nat) :
    satTo3CNFTime.eval n = 800 * n * n + 3000 * n + 2000 := by
  simp [satTo3CNFTime, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_natCast]
  ring

end TM3CNF

end Turing

end Chapter34

end CLRS
