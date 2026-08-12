import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.Dev.B11_CopyOut
import Mathlib.Computability.TuringMachine.Computable

/-!
# Dev B12: polynomial-time bounds

The polynomial-time bounds: `to3CNF'_bounds`, `parseSteps_le`, the decode bounds, `encCNF_to3CNF'_le`, `satTo3CNFTime`, and the `count`/`reorder` phase lemmas.
-/

namespace CLRS

namespace Chapter34

open CLRS.Chapter34
open Computability StateTransition
open Turing

namespace Turing

namespace TM3CNF

-- ============================================================
-- polynomial time: bounds and the full run (`outputsFun`)
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
of consumed symbols plus three. -/
lemma decodeAux_enc_consumed_le (n : Nat) (l : List FormulaSym) :
    (enc (decodeAux n l).1).length ≤ 2 * (l.length - (decodeAux n l).2.length) + 3 := by
  -- Strong induction on the input length so the hypothesis applies to the
  -- suffixes consumed by the binary connectives.
  let P : List FormulaSym → Prop := fun l => ∀ n,
      (enc (decodeAux n l).1).length ≤ 2 * (l.length - (decodeAux n l).2.length) + 3
  have hP : P l := by
    refine WellFounded.induction (measure (fun l : List FormulaSym => l.length)).wf l ?_
    intro l ih
    dsimp [P] at ih ⊢
    intro n
    cases l with
    | nil => cases n <;> simp [decodeAux, enc]
    | cons s rest =>
        cases n with
        | zero => simp [decodeAux, enc]
        | succ n' =>
            cases s with
            | lit b => simp [decodeAux, enc]
            | varMark =>
                by_cases h : rest.head? = some FormulaSym.endMark
                · rcases hend : endMarkRun rest with ⟨k, suf⟩
                  have hrep : rest = List.replicate k FormulaSym.endMark ++ suf := by
                    have hs := endMarkRun_spec rest
                    rw [hend] at hs
                    exact hs.1
                  have hsuf_ne : suf.head? ≠ some FormulaSym.endMark := by
                    have hs := endMarkRun_spec rest
                    rw [hend] at hs
                    exact hs.2
                  have hk : 1 ≤ k := by
                    by_contra hk0
                    have hk0' : k = 0 := by omega
                    rw [hk0'] at hrep
                    have : rest = suf := by simpa using hrep
                    rw [← this] at hsuf_ne
                    exact hsuf_ne h
                  have hdec := decodeVar_endMarkRun rest k suf hk hend
                  have hlen : rest.length = k + suf.length := by
                    rw [hrep]
                    simp [List.length_append, List.length_replicate]
                  simp [decodeAux, hdec, enc, varEnc]
                  omega
                · have hdec : decodeVar rest = (Formula.const false, rest) := by
                    cases rest with
                    | nil => simp [decodeVar]
                    | cons s rest' => cases s <;> simp [decodeVar] at h ⊢
                  simp [decodeAux, hdec, enc]
                  omega
            | endMark => simp [decodeAux, enc]
            | notMark =>
                have h1 : (enc (decodeAux n' rest).1).length ≤
                    2 * (rest.length - (decodeAux n' rest).2.length) + 3 := ih rest (by omega) n'
                simp [decodeAux, enc, List.length_cons]
                omega
            | andMark =>
                have h1 : (enc (decodeAux n' rest).1).length ≤
                    2 * (rest.length - (decodeAux n' rest).2.length) + 3 := ih rest (by omega) n'
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                    2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 3 := by
                  exact ih (decodeAux n' rest).2 (by omega) n'
                have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                  decodeAux_suffix_le n' (decodeAux n' rest).2
                simp [decodeAux, enc, List.length_cons]
                omega
            | orMark =>
                have h1 : (enc (decodeAux n' rest).1).length ≤
                    2 * (rest.length - (decodeAux n' rest).2.length) + 3 := ih rest (by omega) n'
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                    2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 3 := by
                  exact ih (decodeAux n' rest).2 (by omega) n'
                have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                  decodeAux_suffix_le n' (decodeAux n' rest).2
                simp [decodeAux, enc, List.length_cons]
                omega
            | iffMark =>
                have h1 : (enc (decodeAux n' rest).1).length ≤
                    2 * (rest.length - (decodeAux n' rest).2.length) + 3 := ih rest (by omega) n'
                have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
                have h2 : (enc (decodeAux n' (decodeAux n' rest).2).1).length ≤
                    2 * ((decodeAux n' rest).2.length - (decodeAux n' (decodeAux n' rest).2).2.length) + 3 := by
                  exact ih (decodeAux n' rest).2 (by omega) n'
                have hsuf2 : (decodeAux n' (decodeAux n' rest).2).2.length ≤ (decodeAux n' rest).2.length :=
                  decodeAux_suffix_le n' (decodeAux n' rest).2
                simp [decodeAux, enc, List.length_cons]
                omega
  simpa using hP n

/-- The encoding of the decoded formula is at most double the input plus three. -/
lemma enc_decode_le (x : List FormulaSym) :
    (enc (decode x)).length ≤ 2 * x.length + 3 := by
  have h := decodeAux_enc_consumed_le x.length x
  have hle : x.length - (decodeAux x.length x).2.length ≤ x.length := by omega
  simpa [decode] using (by omega : (enc (decodeAux x.length x).1).length ≤ 2 * x.length + 3)

/-- The number of original variables of a decoded formula is at most the input
length. -/
lemma numVars_decode_le (x : List FormulaSym) : numVars (decode x) ≤ x.length := by
  refine (show ∀ n, numVars (decodeAux n x).1 ≤ x.length from ?_) x.length
  refine WellFounded.induction (measure (fun l : List FormulaSym => l.length)).wf x ?_
  intro l ih
  intro n
  cases l with
  | nil => simp [decodeAux]
  | cons s rest =>
      cases n with
      | zero => simp [decodeAux]
      | succ n' =>
          cases s with
          | lit _ => simp [decodeAux]
          | varMark =>
              by_cases h : rest.head? = some FormulaSym.endMark
              · rcases endMarkRun rest with ⟨k, suf⟩
                have hk : 1 ≤ k := by
                  have hs := endMarkRun_spec rest
                  rw [h] at hs
                  have hrep : rest = List.replicate k FormulaSym.endMark ++ suf := hs.1
                  by_contra hk0
                  have hk0' : k = 0 := by omega
                  rw [hk0'] at hrep
                  have : rest = suf := by simpa using hrep
                  rw [this] at hs
                  exact hs.2 h
                have hdec := decodeVar_endMarkRun rest k suf hk (by rfl)
                have hk1 : k ≤ rest.length := by
                  have hs := endMarkRun_spec rest
                  rw [h] at hs
                  omega
                simp [decodeAux, hdec]
                omega
              · simp [decodeAux, decodeVar]
                omega
          | endMark => simp [decodeAux]
          | notMark =>
              have h1 : numVars (decodeAux n' rest).1 ≤ rest.length := by
                simpa using ih rest (by simp [List.length_cons]) n'
              simp [decodeAux]
              omega
          | andMark =>
              have h1 : numVars (decodeAux n' rest).1 ≤ rest.length := by
                simpa using ih rest (by simp [List.length_cons]) n'
              have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                  (decodeAux n' rest).2.length := by
                simpa using ih (decodeAux n' rest).2 (by
                  have hsuf := decodeAux_suffix_le n' rest
                  simp [List.length_cons]
                  omega) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              simp [decodeAux]
              omega
          | orMark =>
              have h1 : numVars (decodeAux n' rest).1 ≤ rest.length := by
                simpa using ih rest (by simp [List.length_cons]) n'
              have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                  (decodeAux n' rest).2.length := by
                simpa using ih (decodeAux n' rest).2 (by
                  have hsuf := decodeAux_suffix_le n' rest
                  simp [List.length_cons]
                  omega) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              simp [decodeAux]
              omega
          | iffMark =>
              have h1 : numVars (decodeAux n' rest).1 ≤ rest.length := by
                simpa using ih rest (by simp [List.length_cons]) n'
              have h2 : numVars (decodeAux n' (decodeAux n' rest).2).1 ≤
                  (decodeAux n' rest).2.length := by
                simpa using ih (decodeAux n' rest).2 (by
                  have hsuf := decodeAux_suffix_le n' rest
                  simp [List.length_cons]
                  omega) n'
              have hsuf : (decodeAux n' rest).2.length ≤ rest.length := decodeAux_suffix_le n' rest
              simp [decodeAux]
              omega

/-- The encoded Tseitin clauses are bounded by a quadratic in the encoding
length. -/
lemma encCNF_to3CNF'_le (f : Formula) (c : Nat) :
    (encCNF (to3CNF' f c).1).length ≤
      12 * (enc f).length * (c + (enc f).length + 1) + 6 * (enc f).length := by
  induction f with
  | var i => simp [to3CNF', enc, varEnc, encCNF]
  | const b => by_cases hb : b <;> simp [to3CNF', hb, enc, encCNF, forceTrue, forceFalse, encClause, encLit, litSym, litIndex]
  | not f' ih =>
      rcases to3CNF' f' c with ⟨cl, y1, c1⟩
      have hc : (encCNF cl).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa using ih
      have hb := to3CNF'_bounds f' c
      rcases hb with ⟨hy1, hc1⟩
      have hcl : cl.length ≤ (enc f').length + 1 := by
        have hcnum := to3CNF'_clauses_num_le f' c
        simpa using hcnum
      simp [to3CNF', enc, notClauses, encCNF, List.length_cons]
      nlinarith
  | and f' g' ihf ihg =>
      rcases to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa using ihf
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa using ihg
      have hb1 := to3CNF'_bounds f' c
      rcases hb1 with ⟨hy1, hc1'⟩
      have hb2 := to3CNF'_bounds g' c1
      rcases hb2 with ⟨hy2, hc2'⟩
      have hcl1 : cl1.length ≤ (enc f').length + 1 := by
        have hcnum := to3CNF'_clauses_num_le f' c
        simpa using hcnum
      have hcl2 : cl2.length ≤ (enc g').length + 1 := by
        have hcnum := to3CNF'_clauses_num_le g' c1
        simpa using hcnum
      have hclc : (encCNF (andClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 30 := by
        have hlen : (encCNF (andClauses c2 y1 y2)).length = 3 * (c2 + y1 + y2 + 3) + 6 := by
          simp [encCNF, andClauses, encClause, encLit, litSym, litIndex]
        rw [hlen]
        nlinarith
      simp [to3CNF', enc, encCNF]
      nlinarith
  | or f' g' ihf ihg =>
      rcases to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa using ihf
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa using ihg
      have hb1 := to3CNF'_bounds f' c
      rcases hb1 with ⟨hy1, hc1'⟩
      have hb2 := to3CNF'_bounds g' c1
      rcases hb2 with ⟨hy2, hc2'⟩
      have hcl1 : cl1.length ≤ (enc f').length + 1 := by
        have hcnum := to3CNF'_clauses_num_le f' c
        simpa using hcnum
      have hcl2 : cl2.length ≤ (enc g').length + 1 := by
        have hcnum := to3CNF'_clauses_num_le g' c1
        simpa using hcnum
      have hclc : (encCNF (orClauses c2 y1 y2)).length ≤ 12 * (c1 + (enc f').length + (enc g').length + 1) + 30 := by
        have hlen : (encCNF (orClauses c2 y1 y2)).length = 3 * (c2 + y1 + y2 + 3) + 6 := by
          simp [encCNF, orClauses, encClause, encLit, litSym, litIndex]
        rw [hlen]
        nlinarith
      simp [to3CNF', enc, encCNF]
      nlinarith
  | iff f' g' ihf ihg =>
      rcases to3CNF' f' c with ⟨cl1, y1, c1⟩
      rcases to3CNF' g' c1 with ⟨cl2, y2, c2⟩
      have hc1 : (encCNF cl1).length ≤ 12 * (enc f').length * (c + (enc f').length + 1) + 6 * (enc f').length := by simpa using ihf
      have hc2 : (encCNF cl2).length ≤ 12 * (enc g').length * (c1 + (enc g').length + 1) + 6 * (enc g').length := by simpa using ihg
      have hb1 := to3CNF'_bounds f' c
      rcases hb1 with ⟨hy1, hc1'⟩
      have hb2 := to3CNF'_bounds g' c1
      rcases hb2 with ⟨hy2, hc2'⟩
      have hcl1 : cl1.length ≤ (enc f').length + 1 := by
        have hcnum := to3CNF'_clauses_num_le f' c
        simpa using hcnum
      have hcl2 : cl2.length ≤ (enc g').length + 1 := by
        have hcnum := to3CNF'_clauses_num_le g' c1
        simpa using hcnum
      have hclc : (encCNF (iffClauses c2 y1 y2)).length ≤ 16 * (c1 + (enc f').length + (enc g').length + 1) + 40 := by
        have hlen : (encCNF (iffClauses c2 y1 y2)).length = 4 * (c2 + y1 + y2 + 3) + 8 := by
          simp [encCNF, iffClauses, encClause, encLit, litSym, litIndex]
        rw [hlen]
        nlinarith
      simp [to3CNF', enc, encCNF]
      nlinarith

/-- The input alphabet of the machine is `FormulaSym`. -/
def satInputAlphabet : (mach).Γ (mach).k₀ ≃ FormulaSym := Equiv.refl _

/-- The output alphabet of the machine is `CNFSym`. -/
def satOutputAlphabet : (mach).Γ (mach).k₁ ≃ CNFSym := Equiv.refl _

/-- The polynomial time bound. -/
def satTo3CNFTime : Polynomial ℕ :=
  800 * Polynomial.X ^ 2 + 3000 * Polynomial.X + 2000

/-- `count` from any pre-state: the count step pops from `in` and overwrites the
state, so `count_phase_aux` (stated from `St.rd default`) applies from the
machine's initial state `St.init` as well. -/
lemma count_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[inp.length + 1]
        (some (⟨some Label.count, v, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.reorder, St.done, stk [] (inp.reverse ++ T) (c + inp.length) V F S O U⟩ : (mach).Cfg) := by
  induction inp generalizing T c v with
  | nil =>
      simp [stk, Sstep, prog, flip]
  | cons s rest ih =>
      have hone := count_step s rest T c V F S O U
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.count, St.rd s, stk (s :: rest) T c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] ((s :: rest).reverse ++ T) (c + (s :: rest).length) V F S O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (v := St.rd s) (T := s :: T) (c := c + 1)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.count, St.rd s, stk rest (s :: T) (c + 1) V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.reorder, St.done, stk [] (rest.reverse ++ (s :: T)) ((c + 1) + rest.length) V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.reorder, St.done, stk [] ((s :: rest).reverse ++ T) (c + (s :: rest).length) V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, List.length_cons, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- `reorder` from any pre-state: the reorder step pops from `temp` and
overwrites the state, so `reorder_phase_aux` (stated from `St.rd default`)
applies from the state `St.done` left by the count phase. -/
lemma reorder_phase (v : St) (inp T : List FormulaSym) (c : Nat) (V : List Bool) (F : List Frame)
    (S : List Unit) (O U : List CNFSym) :
    (flip bind Sstep)^[T.length + 1]
        (some (⟨some Label.reorder, v, stk inp T c V F S O U⟩ : (mach).Cfg))
      = some (⟨some Label.rd, St.done, stk (T.reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
  induction T generalizing inp v with
  | nil =>
      simp [stk, Sstep, prog, flip]
  | cons s rest ih =>
      have hone : Sstep (⟨some Label.reorder, St.rd s, stk inp (s :: rest) c V F S O U⟩ : (mach).Cfg)
          = some (⟨some Label.reorder, St.rd s, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg) := by
        apply congrArg some
        apply Turing.TM2Comp.Cfg_ext
        · rfl
        · rfl
        · funext k
          cases k <;> simp [stk, Function.update, prog, Sstep]
      rw [show (s :: rest).length + 1 = (rest.length + 1) + 1 by simp [List.length_cons]]
      rw [Function.iterate_succ_apply]
      change (flip bind Sstep)^[rest.length + 1]
          (Sstep (⟨some Label.reorder, St.rd s, stk inp (s :: rest) c V F S O U⟩ : (mach).Cfg))
        = some (⟨some Label.rd, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg)
      rw [hone]
      have hih := ih (inp := s :: inp) (v := St.rd s)
      calc
        (flip bind Sstep)^[rest.length + 1]
            (some (⟨some Label.reorder, St.rd s, stk (s :: inp) rest c V F S O U⟩ : (mach).Cfg))
          = some (⟨some Label.rd, St.done, stk (rest.reverse ++ (s :: inp)) [] c V F S O U⟩ : (mach).Cfg) := hih
        _ = some (⟨some Label.rd, St.done, stk ((s :: rest).reverse ++ inp) [] c V F S O U⟩ : (mach).Cfg) := by
            apply congrArg some
            apply Turing.TM2Comp.Cfg_ext
            · rfl
            · rfl
            · funext k
              cases k <;> simp [stk, List.reverse_cons, List.cons_append, List.append_assoc, Nat.add_comm, Nat.add_assoc] <;> try omega

/-- The full machine run: count, reorder, the recursive descent, the root unit
clause, copying `o` to `out`, and clearing the junk.  The final `out` tape is
`encCNF (to3CNF_len (decode inp) inp.length)`. -/
noncomputable def satTo3CNFOutputsFun (inp : List FormulaSym) :
    TM2OutputsInTime mach inp (some (encCNF (to3CNF_len (decode inp) inp.length))) (satTo3CNFTime.eval inp.length) := by
  let n := inp.length
  let f0 := decode inp
  let rest := (decodeAux n inp).2
  let cls := (to3CNF' f0 n).1
  let y := (to3CNF' f0 n).2.1
  let next := (to3CNF' f0 n).2.2
  let outList := encCNF (to3CNF_len f0 n)
  let initC : (mach).Cfg := ⟨some Label.count, St.init, stk inp [] 0 [] [] [] [] []⟩
  let C1 : (mach).Cfg := ⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩
  let C2 : (mach).Cfg := ⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩
  have hdec : decodeAux n inp = (f0, rest) := by
    change decodeAux inp.length inp = (f0, rest)
    rfl
  have hV : ([] : List Bool).head? ≠ some true := by simp
  have hparse0 : ∀ v₀ : St, ∃ v₁ : St,
      (flip bind Sstep)^[parseSteps f0 n]
        (some (⟨some Label.rd, v₀, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reduce, v₁, stk rest [] next
            (false :: List.replicate (y + 1) true) [] []
            ((encCNF cls).reverse) []⟩ : (mach).Cfg) := by
    intro v₀
    simpa using parse_phase f0 n inp rest n [] [] [] [] [] hV le_rfl hdec v₀
  rcases hparse0 St.done with ⟨v₁, hparse⟩
  let C3 : (mach).Cfg := ⟨some Label.reduce, v₁, stk rest [] next
      (false :: List.replicate (y + 1) true) [] [] ((encCNF cls).reverse) []⟩
  let C4 : (mach).Cfg := ⟨some Label.emitTrue, St.emitTrue, stk rest [] next
      (false :: List.replicate (y + 1) true) [] [] ((encCNF cls).reverse) []⟩
  let C5 : (mach).Cfg := ⟨some Label.copyOut, St.done, stk rest [] next [] [] []
      ((encCNF [[Literal.pos y]]).reverse ++ (encCNF cls).reverse) []⟩
  let C6 : (mach).Cfg := ⟨some Label.clearIn, St.init, stk rest [] next [] [] [] [] (C5.stk K.o).reverse⟩
  let C7 : (mach).Cfg := ⟨some Label.clearCnt, St.done, stk [] [] next [] [] [] [] (C5.stk K.o).reverse⟩
  let C8 : (mach).Cfg := ⟨some Label.done, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩
  let C9 : (mach).Cfg := ⟨none, St.init, stk [] [] 0 [] [] [] [] (C5.stk K.o).reverse⟩
  have hcount : EvalsToInTime Sstep initC (some C1) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some initC) = some C1
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.count, St.init, stk inp [] 0 [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩ : (mach).Cfg)
    rw [count_phase St.init inp [] 0 [] [] [] [] []]
    simp [n, List.append_nil, Nat.zero_add]
  have hreorder : EvalsToInTime Sstep C1 (some C2) (n + 1) := by
    refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[n + 1] (some C1) = some C2
    change (flip bind Sstep)^[n + 1]
        (some (⟨some Label.reorder, St.done, stk [] inp.reverse n [] [] [] [] []⟩ : (mach).Cfg))
        = some (⟨some Label.rd, St.done, stk inp [] n [] [] [] [] []⟩ : (mach).Cfg)
    rw [show n + 1 = inp.reverse.length + 1 by simp [n, List.length_reverse]]
    rw [reorder_phase St.done [] inp.reverse n [] [] [] [] []]
    simp [n, List.reverse_reverse]
  have hparseE : EvalsToInTime Sstep C2 (some C3) (parseSteps f0 n) := by
    refine ⟨⟨parseSteps f0 n, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[parseSteps f0 n] (some C2) = some C3
    exact hparse
  have hreduce : EvalsToInTime Sstep C3 (some C4) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C3) = some C4
    exact reduce_top_step v₁ rest [] next (false :: List.replicate (y + 1) true) [] [] ((encCNF cls).reverse) []
  have hemTrue : EvalsToInTime Sstep C4 (some C5) ((y + 1) + 2) := by
    refine ⟨⟨(y + 1) + 2, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[(y + 1) + 2] (some C4) = some C5
    exact emitTrue_phase y St.emitTrue rest [] next [] [] [] ((encCNF cls).reverse) []
  have hcopyOut : EvalsToInTime Sstep C5 (some C6) ((C5.stk K.o).length + 1) := by
    refine ⟨⟨(C5.stk K.o).length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[(C5.stk K.o).length + 1] (some C5) = some C6
    simpa using copyOut_phase St.done rest [] next [] [] [] (C5.stk K.o) []
  have hclearIn : EvalsToInTime Sstep C6 (some C7) (rest.length + 1) := by
    refine ⟨⟨rest.length + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[rest.length + 1] (some C6) = some C7
    simpa using clearIn_phase St.init rest [] next [] [] [] [] (C5.stk K.o).reverse
  have hclearCnt : EvalsToInTime Sstep C7 (some C8) (next + 1) := by
    refine ⟨⟨next + 1, ?_⟩, le_rfl⟩
    change (flip bind Sstep)^[next + 1] (some C7) = some C8
    simpa using clearCnt_phase St.done [] [] next [] [] [] [] (C5.stk K.o).reverse
  have hdone : EvalsToInTime Sstep C8 (some C9) 1 := by
    refine ⟨⟨1, ?_⟩, le_rfl⟩
    change (flip bind Sstep) (some C8) = some C9
    exact done_step [] [] 0 [] [] [] (C5.stk K.o).reverse
  have h12 : EvalsToInTime Sstep initC (some C2) ((n + 1) + (n + 1)) :=
    EvalsToInTime.trans Sstep (n + 1) (n + 1) initC C1 (some C2) hcount hreorder
  have h123 : EvalsToInTime Sstep initC (some C3) (parseSteps f0 n + ((n + 1) + (n + 1))) :=
    EvalsToInTime.trans Sstep ((n + 1) + (n + 1)) (parseSteps f0 n) initC C2 (some C3) h12 hparseE
  have h1234 : EvalsToInTime Sstep initC (some C4) (1 + (parseSteps f0 n + ((n + 1) + (n + 1)))) :=
    EvalsToInTime.trans Sstep (parseSteps f0 n + ((n + 1) + (n + 1))) 1 initC C3 (some C4) h123 hreduce
  have h12345 : EvalsToInTime Sstep initC (some C5) (((y + 1) + 2) + (1 + (parseSteps f0 n + ((n + 1) + (n + 1))))) :=

end TM3CNF

end Turing

end Chapter34

end CLRS
