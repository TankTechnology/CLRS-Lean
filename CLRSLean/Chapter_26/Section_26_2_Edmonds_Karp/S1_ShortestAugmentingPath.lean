import Mathlib
import CLRSLean.Chapter_26.Section_26_2_Edmonds_Karp

/-!
# 26.2 S1. Shortest augmenting paths

This module constructs an explicit shortest residual source-to-sink path
whenever the sink is residual-reachable.  The construction walks backwards
from the sink through exact predecessors (`IsShortestDist.exists_predecessor`),
collecting vertices into a list whose distance from the source strictly
decreases, then reverses it into a simple `Flow.ResidualPath` whose edge count
realizes the residual distance.

Main results:

- `back`: the backwards walk from a vertex at distance `d`
- `back_head`, `back_last`, `back_length`, `back_chain_rev`, `back_nodup`,
  and `back_getElem_shortest`: its structural properties
- `shortestFlow.ResidualPath`: the assembled shortest residual source-to-sink path
- `exists_shortest_augmenting_path`: residual reachability yields a shortest
  augmenting path (the mathematical core shared by the Edmonds-Karp loop and
  the `O(VE²)` analysis)
-/

set_option autoImplicit true

namespace CLRS
namespace Chapter26

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

/-- The vertices of a shortest residual path from `s` to `v`, listed from `v`
back to `s`: `v`, its exact predecessor, and so on down to the source. -/
noncomputable def back {φ : Flow V G} : (d : ℕ) → (v : V) → IsShortestDist φ G.s v d → List V
  | 0, v, _ => [v]
  | d + 1, v, hd =>
      let u := Classical.choose (IsShortestDist.exists_predecessor hd)
      let hdu := (Classical.choose_spec (IsShortestDist.exists_predecessor hd)).2
      v :: back d u hdu

/-- The backward walk starts at the requested vertex. -/
lemma back_head {φ : Flow V G} (d : ℕ) (v : V) (hd : IsShortestDist φ G.s v d) :
    (back d v hd).head? = some v := by
  induction d generalizing v with
  | zero => simp [back]
  | succ d ih =>
      have hspec := Classical.choose_spec (IsShortestDist.exists_predecessor hd)
      simp [back]

/-- The backward walk ends at the source. -/
lemma back_last {φ : Flow V G} (d : ℕ) (v : V) (hd : IsShortestDist φ G.s v d) :
    (back d v hd).getLast? = some G.s := by
  induction d generalizing v with
  | zero =>
      have hv : v = G.s := by
        rcases hd with ⟨hpath, _⟩
        cases hpath with
        | refl => rfl
      simp [back, hv]
  | succ d ih =>
      have hspec := Classical.choose_spec (IsShortestDist.exists_predecessor hd)
      simp [back, List.getLast?_cons, ih (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2]

/-- The backward walk from distance `d` has exactly `d + 1` vertices. -/
lemma back_length {φ : Flow V G} (d : ℕ) (v : V) (hd : IsShortestDist φ G.s v d) :
    (back d v hd).length = d + 1 := by
  induction d generalizing v with
  | zero => simp [back]
  | succ d ih =>
      have hspec := Classical.choose_spec (IsShortestDist.exists_predecessor hd)
      simp [back, ih (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2]

/-- The vertex at position `i` of the backward walk has residual distance
`d - i` from the source. -/
lemma back_getElem_shortest {φ : Flow V G} (d : ℕ) (v : V) (hd : IsShortestDist φ G.s v d) :
    ∀ i (hi : i < (back d v hd).length),
      IsShortestDist φ G.s (back d v hd)[i] (d - i) := by
  induction d generalizing v with
  | zero =>
      intro i hi
      have hlen : (back 0 v hd).length = 1 := by simp [back]
      have hi0 : i = 0 := by omega
      subst i
      simpa [back] using hd
  | succ d ih =>
      have hspec := Classical.choose_spec (IsShortestDist.exists_predecessor hd)
      intro i hi
      cases i with
      | zero => simpa [back] using hd
      | succ j =>
          have hj : j < (back d (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2).length := by
            simpa [back] using hi
          have hget : (back (d + 1) v hd)[j + 1] =
              (back d (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2)[j] := by
            rfl
          rw [hget]
          have hshort := ih (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2 j hj
          convert hshort using 1
          omega

/-- Consecutive pairs of the backward walk are residual edges (in the reverse
direction: `a` precedes `b` when the residual edge is `b → a`). -/
lemma back_chain_rev {φ : Flow V G} (d : ℕ) (v : V) (hd : IsShortestDist φ G.s v d) :
    (back d v hd).IsChain (fun a b => φ.residualEdge b a) := by
  induction d generalizing v with
  | zero => simp [back]
  | succ d ih =>
      have hspec := Classical.choose_spec (IsShortestDist.exists_predecessor hd)
      apply List.IsChain.cons
      · exact ih (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2
      · intro y hy
        have hu := back_head d (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2
        have hyu : y = Classical.choose (IsShortestDist.exists_predecessor hd) := by
          simpa [hu, eq_comm] using hy
        simpa [hyu] using hspec.1

/-- The backward walk is a simple list: its distances strictly decrease, so
no vertex repeats. -/
lemma back_nodup {φ : Flow V G} (d : ℕ) (v : V) (hd : IsShortestDist φ G.s v d) :
    (back d v hd).Nodup := by
  induction d generalizing v with
  | zero => simp [back]
  | succ d ih =>
      have hspec := Classical.choose_spec (IsShortestDist.exists_predecessor hd)
      constructor
      · intro hmem hmem_mem
        have hmem' : ∃ i, ∃ (h : i < (back d (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2).length),
            (back d (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2)[i] = hmem :=
          List.mem_iff_getElem.mp hmem_mem
        rcases hmem' with ⟨j, hj, hget⟩
        have hshort := back_getElem_shortest d (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2 j hj
        have hd' : IsShortestDist φ G.s hmem (d - j) := by
          simpa [hget] using hshort
        intro hv
        have hd'' : IsShortestDist φ G.s v (d - j) := by
          simpa [hv] using hd'
        have heq : d + 1 = d - j := hd.unique hd''
        omega
      · exact ih (Classical.choose (IsShortestDist.exists_predecessor hd)) hspec.2

/-- Appending a vertex related to the last element of a chain preserves the
chain. -/
lemma IsChain_append_last {α : Type*} {R : α → α → Prop} {xs : List α} {x : α}
    (hchain : xs.IsChain R) (hlast : ∀ y, y ∈ xs.getLast? → R y x) :
    (xs ++ [x]).IsChain R := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      apply List.IsChain.cons
      · exact ih hchain.tail (by
          intro y hy
          have h' : y ∈ (a :: xs).getLast? := by
            rw [List.getLast?_cons]
            simp
            have hys : xs.getLast? = some y := by simpa using hy
            rw [hys]
            rfl
          simpa using hlast y h')
      · intro y hy
        cases xs with
        | nil =>
            have hyx : y = x := by
              have hxy : x = y := by simpa using hy
              exact hxy.symm
            simpa [hyx] using hlast a (by simp)
        | cons b xs =>
            have hyb : y = b := by
              have hby : b = y := by simpa using hy
              exact hby.symm
            simpa [hyb] using hchain.rel_head

/-- Decomposing a chain that ends in a singleton: the prefix is a chain and
its last element relates to the appended one. -/
lemma IsChain_append_elim {α : Type*} {R : α → α → Prop} {xs : List α} {a : α}
    (h : (xs ++ [a]).IsChain R) (hxs : xs ≠ []) :
    xs.IsChain R ∧ ∀ y, y ∈ xs.getLast? → R y a := by
  induction xs with
  | nil => simp at hxs
  | cons b xs ih =>
      cases xs
      case nil =>
          constructor
          · simp
          · intro y hy
            have hyb : y = b := by
              have hby : b = y := by simpa using hy
              exact hby.symm
            simpa [hyb] using h.rel_head
      case cons c xs =>
          rcases ih h.tail (by simp) with ⟨hxs_chain, hlast_xs⟩
          constructor
          · apply List.IsChain.cons
            · exact hxs_chain
            · intro y hy
              have hyc : y = c := by
                have hcy : c = y := by simpa using hy
                exact hcy.symm
              simpa [hyc] using h.rel_head
          · intro y hy
            have hget : (b :: c :: xs).getLast? = (c :: xs).getLast? := by
              simp [List.getLast?_cons_cons]
            have hy' : y ∈ (c :: xs).getLast? := by
              simpa [hget] using hy
            simpa using hlast_xs y hy'

/-- Reversing a chain swaps the relation. -/
lemma IsChain_reverse_swap {α : Type*} {R : α → α → Prop} {l : List α}
    (h : l.IsChain (fun a b => R b a)) : l.reverse.IsChain R := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
      by_cases hxs : xs = []
      · simp [hxs]
      · rcases IsChain_append_elim (R := fun a b => R b a) h hxs with ⟨hxs_chain, hlast_xs⟩
        simp [List.reverse_append]
        apply List.IsChain.cons
        · exact ih hxs_chain
        · intro y hy
          simpa [List.head?_reverse] using hlast_xs y (by simpa [List.head?_reverse] using hy)

/-- A residual chain from `u` to `v` of length `k` gives a length-indexed
residual path. -/
lemma chain_segment {φ : Flow V G} (xs : List V)
    (hchain : xs.IsChain φ.residualEdge) (i k : ℕ)
    (hik : i + k < xs.length) :
    ResidualPathLength φ xs[i] xs[i + k] k := by
  induction k with
  | zero => simpa using ResidualPathLength.refl (φ := φ) xs[i]
  | succ k ih =>
      have hik' : i + k < xs.length := by omega
      have hedge : φ.residualEdge xs[i + k] xs[i + k + 1] :=
        hchain.getElem (i + k) (by omega)
      have htail := ResidualPathLength.tail (φ := φ)
        xs[i] xs[i + k] xs[i + k + 1] k (ih hik') hedge
      simpa [Nat.add_assoc] using htail

/-- The shortest residual source-to-sink path realizing residual distance
`d`. -/
noncomputable def shortestFlow.ResidualPath {φ : Flow V G} (d : ℕ)
    (hd : IsShortestDist φ G.s G.t d) : Flow.ResidualPath φ G.s G.t :=
  { vertices := (back d G.t hd).reverse
  , chain := by
      exact IsChain_reverse_swap (back_chain_rev d G.t hd)
  , head_eq := by
      simpa [List.head?_reverse] using back_last d G.t hd
  , last_eq := by
      simpa [List.getLast?_reverse] using back_head d G.t hd
  , nodup := by
      exact List.nodup_reverse.mpr (back_nodup d G.t hd)
  }

/-- The edge count of the shortest path realizes the residual distance. -/
lemma shortestFlow.ResidualPath_edges_length {φ : Flow V G} (d : ℕ)
    (hd : IsShortestDist φ G.s G.t d) :
    (shortestFlow.ResidualPath d hd).edges.length = d := by
  rw [Flow.ResidualPath.edges_length]
  simp [shortestFlow.ResidualPath, back_length d G.t hd]

/-- **Shortest augmenting path existence.**  If the sink is residual-reachable
from the source, there is an explicit simple augmenting path whose edge count
realizes the residual distance (the mathematical core of the Edmonds-Karp
loop and its analysis). -/
theorem exists_shortest_augmenting_path (φ : Flow V G) (h : φ.hasAugmentingPath) :
    Nonempty (ShortestAugmentingPath φ) := by
  rcases (Flow.hasAugmentingPath_iff_nonempty_augmentingPath.mp h) with ⟨p⟩
  have hne : p.vertices ≠ [] := by
    intro hnil
    simpa [hnil] using p.head_eq
  have hlen : 0 < p.vertices.length := List.length_pos_iff.mpr hne
  have hseg := chain_segment p.vertices p.chain 0 (p.vertices.length - 1) (by omega)
  have hfirst : p.vertices[0] = G.s := by
    have hhead : p.vertices.head hne = G.s := by
      simpa [List.head?_eq_some_head hne] using p.head_eq
    exact (List.head_eq_getElem hne).symm.trans hhead
  have hlast : p.vertices[p.vertices.length - 1]'(Nat.sub_lt hlen (by omega)) = G.t := by
    rw [← List.getLast_eq_getElem hne]
    exact List.getLast_of_getLast?_eq_some p.last_eq
  have hpath : ResidualPathLength φ G.s G.t (p.vertices.length - 1) := by
    simpa [hfirst, hlast] using hseg
  let d := Nat.find ⟨p.vertices.length - 1, hpath⟩
  have hd : IsShortestDist φ G.s G.t d :=
    ⟨Nat.find_spec ⟨p.vertices.length - 1, hpath⟩,
     fun n hn => Nat.find_min' ⟨p.vertices.length - 1, hpath⟩ hn⟩
  have hshort : IsShortestDist φ G.s G.t (shortestFlow.ResidualPath d hd).edges.length := by
    rw [shortestFlow.ResidualPath_edges_length d hd]
    exact hd
  exact ⟨{ path := shortestFlow.ResidualPath d hd, h_shortest := hshort }⟩

end Chapter26
end CLRS
