import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SatTo3CNFSat

/-!
# 3-CNF-SAT and its occurrence-graph clique intermediate

The reduction of CLRS Lemma 34.10: a 3-CNF formula is satisfiable iff the graph
with one vertex per literal occurrence — two vertices adjacent when they are in
different clauses and their literals are not complementary — has a clique of
size equal to the number of clauses.

Main results:

- `complement`: the literal that contradicts `l`.
- `not_evalLit_complement`: complementary literals cannot both hold.
- The occurrence graph `occurrenceAdj` and the clique notion `HasCliqueOn`.
- `cnfSatisfiable_iff_hasClique`: the reduction correctness (a CNF is
  satisfiable iff its occurrence graph has a clique of size `f.length`).
- `cnfSatisfiable_iff_hasClique_3CNF`: the same for the project's
  at-most-3-literal CNF convention.
- The graph/list encoding `GraphSym`/`relabel`/`undoRelabel` and the specialized
  language `ThreeCNFOccurrenceCLIQUE`: the reduction maps a 3-CNF encoding to
  its occurrence-graph encoding by inserting a `vertexMark` before each
  literal.  The legacy name `CLIQUE` is a compatibility alias for this
  intermediate language, not yet a general graph-plus-`k` CLIQUE encoding.

**Current status**: the semantic core and specialized graph/list encoding are
in place.  The reduction machine and its `outputsFun`, assembling the
reduction to `ThreeCNFOccurrenceCLIQUE`, live in `CNFToCliqueMachine`.  A
general graph-plus-`k` CLIQUE language is not claimed here.
-/

namespace CLRS

namespace Chapter34

/-- The clause at index `i` of a CNF (empty when out of bounds). -/
def clauseAt (f : CNF) (i : Nat) : Clause := f.getD i []

/-- The literal that contradicts `l` (`pos x` ↔ `neg x`). -/
def complement (l : Literal) : Literal :=
  match l with
  | Literal.pos i => Literal.neg i
  | Literal.neg i => Literal.pos i

/-- A literal occurrence: a clause index together with the literal. -/
abbrev Occurrence := Nat × Literal

/-- Two occurrences are adjacent when they are in different clauses and their
literals are not complementary (CLRS Lemma 34.10). -/
def occurrenceAdj (u v : Occurrence) : Prop :=
  u.1 ≠ v.1 ∧ u.2 ≠ complement v.2

/-- The occurrence graph of `f` has a `k`-clique when there are `k` valid
literal occurrences, pairwise adjacent (one per clause at most, no two
complementary). -/
def HasCliqueOn (f : CNF) (k : Nat) : Prop :=
  ∃ S : Finset Occurrence,
    S.card = k ∧
    (∀ v ∈ S, v.2 ∈ clauseAt f v.1) ∧
    (∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u ≠ v → occurrenceAdj u v)

/-- Complementary literals cannot both hold under the same assignment. -/
lemma not_evalLit_complement (σ : Nat → Bool) (l : Literal) :
    ¬ (evalLit σ l ∧ evalLit σ (complement l)) := by
  cases l <;> simp [evalLit, complement]

/-- `clauseAt f i` is the actual clause when `i` is in bounds. -/
lemma clauseAt_eq_getElem (f : CNF) {i : Nat} (hi : i < f.length) :
    clauseAt f i = f[i] := by
  simp [clauseAt, hi]

/-- `clauseAt f i` is empty out of bounds. -/
lemma clauseAt_eq_nil_of_ge (f : CNF) {i : Nat} (h : f.length ≤ i) :
    clauseAt f i = [] := by
  simp [clauseAt, h]

/-- A valid occurrence is in bounds. -/
lemma occurrence_clauseIndex_lt {f : CNF} {v : Occurrence}
    (hv : v.2 ∈ clauseAt f v.1) : v.1 < f.length := by
  by_contra hge
  rw [clauseAt_eq_nil_of_ge f (Nat.le_of_not_gt hge)] at hv
  simp at hv

/-- The first literal of a clause that `σ` makes true (junk `pos 0` when none). -/
def firstTrueLit (σ : Nat → Bool) : Clause → Literal
  | [] => Literal.pos 0
  | l :: rest => if evalLitBool σ l then l else firstTrueLit σ rest

/-- If `σ` satisfies a clause, the literal `firstTrueLit σ c` is in `c`. -/
lemma firstTrueLit_mem {σ : Nat → Bool} {c : Clause} (hc : evalClause σ c) :
    firstTrueLit σ c ∈ c := by
  induction c with
  | nil => simp [evalClause] at hc
  | cons l rest ih =>
      by_cases h : evalLit σ l
      · have hb : evalLitBool σ l = true := (evalLitBool_eq_true σ l).2 h
        simp [firstTrueLit, hb]
      · have hb : evalLitBool σ l = false := (evalLitBool_eq_false σ l).2 h
        have hrest : evalClause σ rest := by
          simp [evalClause] at hc ⊢
          rcases hc with heval | ⟨l', hl', he⟩
          · exact False.elim (h heval)
          · exact ⟨l', hl', he⟩
        simp [firstTrueLit, hb, ih hrest]

/-- If `σ` satisfies a clause, `firstTrueLit σ c` is true under `σ`. -/
lemma firstTrueLit_eval {σ : Nat → Bool} {c : Clause} (hc : evalClause σ c) :
    evalLit σ (firstTrueLit σ c) := by
  induction c with
  | nil => simp [evalClause] at hc
  | cons l rest ih =>
      by_cases h : evalLit σ l
      · have hb : evalLitBool σ l = true := (evalLitBool_eq_true σ l).2 h
        simpa [firstTrueLit, hb] using h
      · have hb : evalLitBool σ l = false := (evalLitBool_eq_false σ l).2 h
        have hrest : evalClause σ rest := by
          simp [evalClause] at hc ⊢
          rcases hc with heval | ⟨l', hl', he⟩
          · exact False.elim (h heval)
          · exact ⟨l', hl', he⟩
        simpa [firstTrueLit, hb] using ih hrest

/-- The occurrence chosen for clause `i`: the first literal of that clause that
`σ` makes true. -/
def chosenOcc (σ : Nat → Bool) (f : CNF) (i : Nat) : Occurrence :=
  (i, firstTrueLit σ (clauseAt f i))

/-- The chosen occurrences for all clauses, one per clause index. -/
def chosenOccs (σ : Nat → Bool) (f : CNF) : List Occurrence :=
  List.finRange f.length |>.map (fun i => chosenOcc σ f i.val)

/-- The chosen occurrences are all distinct (they have distinct clause indices). -/
lemma chosenOccs_nodup (σ : Nat → Bool) (f : CNF) : (chosenOccs σ f).Nodup := by
  rw [chosenOccs]
  refine List.Nodup.map ?_ (List.nodup_finRange f.length)
  intro a b h
  apply Fin.ext
  exact congrArg Prod.fst h

/-- The chosen occurrences have one entry per clause. -/
lemma chosenOccs_length (σ : Nat → Bool) (f : CNF) :
    (chosenOccs σ f).length = f.length := by
  rw [chosenOccs, List.length_map, List.length_finRange]

/-- The occurrence chosen for clause `i` is valid and its literal is true. -/
lemma chosenOcc_valid (σ : Nat → Bool) {f : CNF} (hσ : evalCNF σ f) {i : Nat}
    (hi : i < f.length) :
    (chosenOcc σ f i).2 ∈ clauseAt f i ∧ evalLit σ (chosenOcc σ f i).2 := by
  have hc := hσ (clauseAt f i) (by rw [clauseAt_eq_getElem f hi]; exact List.getElem_mem hi)
  constructor
  · exact firstTrueLit_mem hc
  · exact firstTrueLit_eval hc

/-- The occurrence chosen for clause `i` is not complementary to the occurrence
chosen for a different clause `j`. -/
lemma chosenOccs_adjacent (σ : Nat → Bool) {f : CNF} (hσ : evalCNF σ f)
    {i j : Nat} (hi : i < f.length) (hj : j < f.length) (hij : i ≠ j) :
    occurrenceAdj (chosenOcc σ f i) (chosenOcc σ f j) := by
  refine ⟨hij, ?_⟩
  intro heq
  have htrue_i : evalLit σ (chosenOcc σ f i).2 := (chosenOcc_valid σ hσ hi).2
  have htrue_j : evalLit σ (chosenOcc σ f j).2 := (chosenOcc_valid σ hσ hj).2
  rw [heq] at htrue_i
  exact not_evalLit_complement σ (chosenOcc σ f j).2 ⟨htrue_j, htrue_i⟩

/-- **⇒**: a satisfying assignment gives a clique of size `f.length`, one chosen
occurrence per clause. -/
lemma cnfSatisfiable_implies_hasClique {f : CNF} (hσ : CnfSatisfiable f) :
    HasCliqueOn f f.length := by
  rcases hσ with ⟨σ, hσ⟩
  refine ⟨(chosenOccs σ f).toFinset, ?card, ?valid, ?adj⟩
  · rw [List.toFinset_card_of_nodup, chosenOccs_length]
    exact chosenOccs_nodup σ f
  · intro v hv
    rw [List.mem_toFinset] at hv
    rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
    exact (chosenOcc_valid σ hσ i.isLt).1
  · intro u hu v hv huv
    rw [List.mem_toFinset] at hu hv
    rcases List.mem_map.mp hu with ⟨i, hi, rfl⟩
    rcases List.mem_map.mp hv with ⟨j, hj, rfl⟩
    have hij : i.val ≠ j.val := by
      intro hij
      apply huv
      simp [hij]
    exact chosenOccs_adjacent σ hσ i.isLt j.isLt hij

/-- A clique covers every clause index. -/
lemma clique_covers_clauses {f : CNF} {S : Finset Occurrence}
    (hvalid : ∀ v ∈ S, v.2 ∈ clauseAt f v.1)
    (hadj : ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u ≠ v → occurrenceAdj u v)
    (hcard : S.card = f.length) :
    ∀ i : Nat, i < f.length → ∃ v ∈ S, v.1 = i := by
  intro i hi
  have hsubset : S.image Prod.fst ⊆ Finset.range f.length := by
    intro j hj
    rcases Finset.mem_image.mp hj with ⟨v, hv, rfl⟩
    exact Finset.mem_range.mpr (occurrence_clauseIndex_lt (hvalid v hv))
  have hinj : Set.InjOn Prod.fst (↑S : Set Occurrence) := by
    intro u hu v hv heq
    by_contra hne
    exact (hadj hu hv hne).1 heq
  have hcard' : (S.image Prod.fst).card = f.length := by
    rw [← hcard]
    exact Finset.card_image_of_injOn hinj
  have heq : S.image Prod.fst = Finset.range f.length := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hcard', Finset.card_range]
  have hi' : i ∈ Finset.range f.length := Finset.mem_range.mpr hi
  rw [← heq] at hi'
  rcases Finset.mem_image.mp hi' with ⟨v, hv, hvi⟩
  exact ⟨v, hv, hvi⟩

/-- The assignment induced by a clique: a variable is true when its positive
occurrence is in the clique. -/
def assignmentFromClique (S : Finset Occurrence) : Nat → Bool :=
  fun x => if ∃ v ∈ S, v.2 = Literal.pos x then true else false

/-- A clause that the clique covers holds under `assignmentFromClique`. -/
lemma evalClause_of_clique {f : CNF} {S : Finset Occurrence}
    (hvalid : ∀ v ∈ S, v.2 ∈ clauseAt f v.1)
    (hadj : ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → u ≠ v → occurrenceAdj u v)
    (hcard : S.card = f.length) (i : Nat) (hi : i < f.length) :
    evalClause (assignmentFromClique S) (clauseAt f i) := by
  rcases clique_covers_clauses hvalid hadj hcard i hi with ⟨v, hv, hvi⟩
  refine ⟨v.2, ?_, ?_⟩
  · simpa [hvi] using hvalid v hv
  · cases hvlit : v.2 with
    | pos x =>
        have hx : assignmentFromClique S x = true := by
          rw [assignmentFromClique, if_pos ⟨v, hv, by simp [hvlit]⟩]
        simp [evalLit, hx]
    | neg x =>
        have hx : assignmentFromClique S x = false := by
          rw [assignmentFromClique]
          apply if_neg
          intro hx'
          rcases hx' with ⟨w, hw, hwpos⟩
          have hne : w ≠ v := by
            intro hwv
            subst w
            simp [hvlit] at hwpos
          have hadj' : occurrenceAdj w v := hadj hw hv hne
          have hcompl : complement v.2 = w.2 := by
            rw [hvlit, hwpos]
            rfl
          exact hadj'.2 hcompl.symm
        simp [evalLit, hx]

/-- **⇐**: a clique of size `f.length` gives a satisfying assignment, one chosen
literal per clause. -/
lemma hasClique_implies_cnfSatisfiable {f : CNF} (h : HasCliqueOn f f.length) :
    CnfSatisfiable f := by
  rcases h with ⟨S, hcard, hvalid, hadj⟩
  refine ⟨assignmentFromClique S, ?_⟩
  intro c hc
  rcases List.mem_iff_getElem.mp hc with ⟨i, hi, rfl⟩
  have hcl : clauseAt f i = f[i] := clauseAt_eq_getElem f hi
  rw [← hcl]
  exact evalClause_of_clique hvalid hadj hcard i hi

/--
**Occurrence-graph semantic equivalence underlying CLRS Lemma 34.10.**  A CNF
`f` is satisfiable iff its occurrence graph has a clique of size `f.length`.
-/
theorem cnfSatisfiable_iff_hasClique (f : CNF) :
    CnfSatisfiable f ↔ HasCliqueOn f f.length :=
  ⟨cnfSatisfiable_implies_hasClique, hasClique_implies_cnfSatisfiable⟩

/-- The at-most-3-literal version used by this project's 3-CNF-SAT convention. -/
theorem cnfSatisfiable_iff_hasClique_3CNF (f : CNF)
    (_h3 : IsThreeCNF f) :
    CnfSatisfiable f ↔ HasCliqueOn f f.length := by
  exact cnfSatisfiable_iff_hasClique f

-- ============================================================
-- Graph/list encoding and the CLIQUE language
--
-- The occurrence graph's vertices are the literal occurrences of the CNF, so
-- the graph encoding is the CNF encoding with a `vertexMark` inserted before
-- each literal.  Clause indices come from the `clauseMark` grouping and the
-- clique size is the number of clauses, both recovered by `decodeCNF`.
-- ============================================================

/-- The alphabet of the occurrence-graph encoding: one `vertexMark` per
occurrence plus the CNF-derived clause/literal markers. -/
inductive GraphSym : Type
  | vertexMark
  | posMark | negMark
  | varMark | endMark
  | clauseMark
deriving DecidableEq, Repr, Fintype, Inhabited

/-- Map a CNF encoding to the occurrence-graph encoding: insert a `vertexMark`
before each literal's polarity mark and translate the remaining symbols.  This
is the CLRS Lemma 34.10 reduction on encodings. -/
def relabel : List CNFSym → List GraphSym
  | [] => []
  | CNFSym.clauseMark :: rest => GraphSym.clauseMark :: relabel rest
  | CNFSym.posMark :: rest => GraphSym.vertexMark :: GraphSym.posMark :: relabel rest
  | CNFSym.negMark :: rest => GraphSym.vertexMark :: GraphSym.negMark :: relabel rest
  | CNFSym.varMark :: rest => GraphSym.varMark :: relabel rest
  | CNFSym.endMark :: rest => GraphSym.endMark :: relabel rest

/-- Drop the `vertexMark`s of a graph encoding, recovering the underlying CNF
encoding. -/
def undoRelabel : List GraphSym → List CNFSym
  | [] => []
  | GraphSym.vertexMark :: rest => undoRelabel rest
  | GraphSym.clauseMark :: rest => CNFSym.clauseMark :: undoRelabel rest
  | GraphSym.posMark :: rest => CNFSym.posMark :: undoRelabel rest
  | GraphSym.negMark :: rest => CNFSym.negMark :: undoRelabel rest
  | GraphSym.varMark :: rest => CNFSym.varMark :: undoRelabel rest
  | GraphSym.endMark :: rest => CNFSym.endMark :: undoRelabel rest

/-- `undoRelabel` inverts `relabel`: the inserted `vertexMark`s are exactly the
ones it removes. -/
lemma undoRelabel_relabel (x : List CNFSym) : undoRelabel (relabel x) = x := by
  induction x with
  | nil => simp [relabel, undoRelabel]
  | cons s rest ih =>
      cases s <;> simp [relabel, undoRelabel, ih]

/-- The unrestricted occurrence-graph language induced by decoded CNF syntax.
This is a semantic helper, not the general textbook graph-plus-`k` language. -/
def OccurrenceCLIQUE : Language GraphSym :=
  { syms | HasCliqueOn (decodeCNF (undoRelabel syms)) (decodeCNF (undoRelabel syms)).length }

/-- The well-shaped intermediate target of the current 3-CNF occurrence-graph
reduction.  Requiring `IsThreeCNF` makes malformed source encodings map to
target no-instances while preserving the concrete `relabel` transducer. -/
def ThreeCNFOccurrenceCLIQUE : Language GraphSym :=
  { syms |
      IsThreeCNF (decodeCNF (undoRelabel syms)) ∧
        HasCliqueOn (decodeCNF (undoRelabel syms))
          (decodeCNF (undoRelabel syms)).length }

/-- Compatibility name for the currently represented, specialized occurrence-
graph target.  A genuine general graph-plus-`k` CLIQUE encoding remains a
separate Chapter 34 gap. -/
abbrev CLIQUE : Language GraphSym := ThreeCNFOccurrenceCLIQUE

end Chapter34

end CLRS
