import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching

/-!
# S1. Matching API extensions

Extensions to the §26.3 `Matching` structure that the §25.1 development
needs: matched-endpoint sets, matched/unmatched predicates, maximality, the
empty matching, and their cardinality and participation lemmas.

These declarations live in the original `CLRS.Chapter26.Matching` namespace
so that dot notation keeps working.

Main results:

- `matchedLeft_card` / `matchedRight_card`: the matched endpoint sets have
  the same cardinality as the matching
- `IsMaximum`: a matching that no other matching exceeds in size
- `mem_L_of_isMatchedLeft` / `mem_R_of_isMatchedRight`: matched vertices lie
  in the corresponding partition
-/
namespace CLRS

open Finset Classical

/- API extensions to the §26.3 matching structures live in their original
namespace so that dot notation keeps working. -/
namespace Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}

namespace Matching

/-- The left endpoints of the edges of a matching. -/
def matchedLeft {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) : Finset V :=
  M.edges.image Prod.fst

/-- The right endpoints of the edges of a matching. -/
def matchedRight {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) : Finset V :=
  M.edges.image Prod.snd

/-- A left vertex is *matched* when it is the left endpoint of a matching
edge. -/
def IsMatchedLeft {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (l : V) : Prop :=
  ∃ r, (l, r) ∈ M.edges

/-- A right vertex is *matched* when it is the right endpoint of a matching
edge. -/
def IsMatchedRight {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (r : V) : Prop :=
  ∃ l, (l, r) ∈ M.edges

/-- A left vertex is *unmatched* when no matching edge leaves it. -/
def IsUnmatchedLeft {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (l : V) : Prop :=
  ∀ r, (l, r) ∉ M.edges

/-- A right vertex is *unmatched* when no matching edge enters it. -/
def IsUnmatchedRight {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) (r : V) : Prop :=
  ∀ l, (l, r) ∉ M.edges

/-- A matching is *maximum* when no matching has more edges. -/
def IsMaximum {V : Type*} [Fintype V] [DecidableEq V] {G : BipartiteGraph V}
    (M : Matching V G) : Prop :=
  ∀ M' : Matching V G, M'.size ≤ M.size

/-- The empty matching. -/
def empty (G : BipartiteGraph V) : Matching V G where
  edges := ∅
  h_subset := Finset.empty_subset _
  h_unique_left := by simp
  h_unique_right := by simp

/-- The empty matching has size zero. -/
@[simp]
lemma empty_size (G : BipartiteGraph V) : (empty G).size = 0 := rfl

/-- Left endpoints of distinct matching edges are distinct, so the matched
left set has the same cardinality as the matching. -/
lemma matchedLeft_card (M : Matching V G) : M.matchedLeft.card = M.size := by
  unfold matchedLeft Matching.size
  rw [Finset.card_image_of_injOn]
  intro e₁ he₁ e₂ he₂ h
  exact Prod.ext h (M.h_unique_left e₁.1 e₁.2 e₂.2 he₁ (by simpa [h] using he₂))

/-- Right endpoints of distinct matching edges are distinct, so the matched
right set has the same cardinality as the matching. -/
lemma matchedRight_card (M : Matching V G) : M.matchedRight.card = M.size := by
  unfold matchedRight Matching.size
  rw [Finset.card_image_of_injOn]
  intro e₁ he₁ e₂ he₂ h
  exact Prod.ext (M.h_unique_right e₁.1 e₂.1 e₁.2 he₁ (by simpa [h] using he₂)) h

/-- Membership in `matchedLeft` is exactly being matched on the left. -/
lemma mem_matchedLeft_iff (M : Matching V G) (l : V) :
    l ∈ M.matchedLeft ↔ M.IsMatchedLeft l := by
  simp [matchedLeft, IsMatchedLeft]

/-- Membership in `matchedRight` is exactly being matched on the right. -/
lemma mem_matchedRight_iff (M : Matching V G) (r : V) :
    r ∈ M.matchedRight ↔ M.IsMatchedRight r := by
  simp [matchedRight, IsMatchedRight]

/-- Unmatched on the left is the negation of matched on the left. -/
lemma isUnmatchedLeft_iff_not_matched (M : Matching V G) (l : V) :
    M.IsUnmatchedLeft l ↔ ¬ M.IsMatchedLeft l := by
  simp [IsUnmatchedLeft, IsMatchedLeft]

/-- Unmatched on the right is the negation of matched on the right. -/
lemma isUnmatchedRight_iff_not_matched (M : Matching V G) (r : V) :
    M.IsUnmatchedRight r ↔ ¬ M.IsMatchedRight r := by
  simp [IsUnmatchedRight, IsMatchedRight]

/-- Matched left vertices lie in `G.L`. -/
lemma mem_L_of_isMatchedLeft (M : Matching V G) {l : V} (h : M.IsMatchedLeft l) :
    l ∈ G.L := by
  rcases h with ⟨r, hr⟩
  exact M.left_mem_L hr

/-- Matched right vertices lie in `G.R`. -/
lemma mem_R_of_isMatchedRight (M : Matching V G) {r : V} (h : M.IsMatchedRight r) :
    r ∈ G.R := by
  rcases h with ⟨l, hl⟩
  exact M.right_mem_R hl

/-- Left vertices are never right vertices. -/
lemma not_mem_R_of_mem_L {G : BipartiteGraph V} {v : V} (hv : v ∈ G.L) : v ∉ G.R :=
  G.not_mem_R_of_mem_L hv

/-- Right vertices are never left vertices. -/
lemma not_mem_L_of_mem_R {G : BipartiteGraph V} {v : V} (hv : v ∈ G.R) : v ∉ G.L :=
  G.not_mem_L_of_mem_R hv

end Matching

end Chapter26

end CLRS
