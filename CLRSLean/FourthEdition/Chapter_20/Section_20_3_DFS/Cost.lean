import CLRSLean.FourthEdition.Chapter_20.Section_20_3_DFS

/-!
# Section 20.3 - Depth-first search cost accounting

This companion module closes the textbook {lit}`O(V + E)` work bound for the
costed depth-first search defined in the base Section 20.3 module.  The proof
uses an exact potential balance: every newly processed vertex contributes one
unit of vertex work, and its outgoing adjacency list contributes exactly its
out-degree.

Main results:

- Theorem {lit}`dfsWithCost_cost_eq`: whole-graph DFS performs exactly
  {lit}`V + E`
  charged control steps.
- Theorem {lit}`dfsWithCost_cost_le`: the textbook {lit}`O(V + E)` upper bound.
-/

namespace CLRS
namespace Chapter22
namespace Graph

variable {V : Type} [DecidableEq V]
variable (G : Graph V)

/-- One costed adjacency-fold step, retaining the accumulated work counter. -/
private noncomputable def dfsCostFoldStep (fuel : Nat) (parent : V)
    (sc : DFSState V × Nat) (v : V) : DFSState V × Nat :=
  if sc.1.color v = Color.white then
    let result := dfsVisitWithCost G fuel v (sc.1.setParent v parent)
    (result.1, sc.2 + result.2)
  else
    sc

/-- The corresponding state-only adjacency-fold step. -/
private noncomputable def dfsPlainFoldStep (fuel : Nat) (parent : V)
    (s : DFSState V) (v : V) : DFSState V :=
  if s.color v = Color.white then dfsVisit G fuel v (s.setParent v parent) else s

/-- Parent-pointer updates do not change the number of white graph vertices. -/
@[simp] private theorem whiteCount_setParent (s : DFSState V) (v parent : V) :
    whiteCount G (s.setParent v parent) = whiteCount G s := by
  rfl

/-- Parent-pointer updates do not change the scanned black-vertex weight. -/
@[simp] private theorem blackWeight_setParent (s : DFSState V) (v parent : V) :
    blackWeight G (s.setParent v parent) = blackWeight G s := by
  rfl

/-- Discovery-time updates do not change the scanned black-vertex weight. -/
@[simp] private theorem blackWeight_setDiscovery (s : DFSState V) (v : V) :
    blackWeight G (s.setDiscovery v) = blackWeight G s := by
  rfl

/-- Finish-time updates do not change the number of white graph vertices. -/
@[simp] private theorem whiteCount_setFinish (s : DFSState V) (v : V) :
    whiteCount G (s.setFinish v) = whiteCount G s := by
  rfl

/-- Recoloring a white vertex gray does not change the already scanned weight. -/
private theorem blackWeight_setColor_gray_of_white {s : DFSState V} {u : V}
    (hwhite : s.color u = Color.white) :
    blackWeight G (s.setColor u Color.gray) = blackWeight G s := by
  unfold blackWeight
  have hfilter :
      G.vertices.filter (fun x => (s.setColor u Color.gray).color x = Color.black) =
        G.vertices.filter (fun x => s.color x = Color.black) := by
    ext x
    by_cases hxu : x = u
    · subst x
      simp [hwhite]
    · simp [hxu]
  rw [hfilter]

/-- Recoloring a nonwhite vertex black does not change the number of white
graph vertices. -/
private theorem whiteCount_setColor_black_of_not_white {s : DFSState V} {u : V}
    (hnotwhite : s.color u ≠ Color.white) :
    whiteCount G (s.setColor u Color.black) = whiteCount G s := by
  unfold whiteCount
  have hfilter :
      G.vertices.filter (fun x => (s.setColor u Color.black).color x = Color.white) =
        G.vertices.filter (fun x => s.color x = Color.white) := by
    ext x
    by_cases hxu : x = u
    · subst x
      simp [hnotwhite]
    · simp [hxu]
  rw [hfilter]

/-- Erasing a single costed fold step recovers the state-only DFS step. -/
private theorem dfsCostFoldStep_state (fuel : Nat) (parent : V)
    (sc : DFSState V × Nat) (v : V) :
    (dfsCostFoldStep G fuel parent sc v).1 =
      dfsPlainFoldStep G fuel parent sc.1 v := by
  by_cases hwhite : sc.1.color v = Color.white
  · simp [dfsCostFoldStep, dfsPlainFoldStep, hwhite, dfsVisitWithCost_result]
  · simp [dfsCostFoldStep, dfsPlainFoldStep, hwhite]

/-- Erasing an entire costed adjacency fold recovers the plain adjacency fold. -/
private theorem dfsCostFold_state (fuel : Nat) (parent : V)
    (vertices : List V) (sc : DFSState V × Nat) :
    (vertices.foldl (dfsCostFoldStep G fuel parent) sc).1 =
      vertices.foldl (dfsPlainFoldStep G fuel parent) sc.1 := by
  induction vertices generalizing sc with
  | nil => rfl
  | cons v rest ih =>
      simp only [List.foldl]
      rw [ih, dfsCostFoldStep_state]

/-- A completed costed DFS visit satisfies the exact white/black work balance. -/
theorem dfsVisitWithCost_balance {fuel : Nat} {u : V} {s : DFSState V}
    (hu : u ∈ G.vertices) :
    let result := dfsVisitWithCost G fuel u s
    result.2 + whiteCount G result.1 + blackWeight G s =
      whiteCount G s + blackWeight G result.1 := by
  induction fuel generalizing u s with
  | zero => simp [dfsVisitWithCost]
  | succ n visitIH =>
      by_cases hwhite : s.color u = Color.white
      · let s1 := s.setColor u Color.gray |>.setDiscovery u
        let folded := (G.adj u).toList.foldl (dfsCostFoldStep G n u) (s1, 0)
        let s2 := folded.1
        let cost2 := folded.2
        have hfold : ∀ (vertices : List V) (sc : DFSState V × Nat),
            (∀ v ∈ vertices, v ∈ G.vertices) →
            let result := vertices.foldl (dfsCostFoldStep G n u) sc
            result.2 + whiteCount G result.1 + blackWeight G sc.1 =
              sc.2 + whiteCount G sc.1 + blackWeight G result.1 := by
          intro vertices
          induction vertices with
          | nil =>
              intro sc _
              simp
          | cons v rest restIH =>
              intro sc hvertices
              have hv : v ∈ G.vertices := hvertices v (by simp)
              have hrest : ∀ w ∈ rest, w ∈ G.vertices := by
                intro w hw
                exact hvertices w (by simp [hw])
              simp only [List.foldl]
              by_cases hvwhite : sc.1.color v = Color.white
              · let visitResult := dfsVisitWithCost G n v (sc.1.setParent v u)
                have hstep : dfsCostFoldStep G n u sc v =
                    (visitResult.1, sc.2 + visitResult.2) := by
                  simp [dfsCostFoldStep, hvwhite, visitResult]
                rw [hstep]
                have hvisit := visitIH (u := v) (s := sc.1.setParent v u) hv
                have htail := restIH (visitResult.1, sc.2 + visitResult.2) hrest
                have hvisit' :
                    visitResult.2 + whiteCount G visitResult.1 + blackWeight G sc.1 =
                      whiteCount G sc.1 + blackWeight G visitResult.1 := by
                  simpa [visitResult] using hvisit
                simp only at htail
                omega
              · have hstep : dfsCostFoldStep G n u sc v = sc := by
                  simp [dfsCostFoldStep, hvwhite]
                rw [hstep]
                exact restIH sc hrest
        have hadj : ∀ v ∈ (G.adj u).toList, v ∈ G.vertices := by
          intro v hv
          exact G.adj_mem_right (by simpa [Adj] using (Finset.mem_toList.mp hv))
        have hfoldMain :
            cost2 + whiteCount G s2 + blackWeight G s1 =
              whiteCount G s1 + blackWeight G s2 := by
          simpa [folded, s2, cost2] using hfold (G.adj u).toList (s1, 0) hadj
        have hplainGray :
            ((G.adj u).toList.foldl (dfsPlainFoldStep G n u) s1).color u =
              Color.gray := by
          change
            ((G.adj u).toList.foldl
              (fun s' v =>
                if s'.color v = Color.white then
                  dfsVisit G n v (s'.setParent v u)
                else s') s1).color u = Color.gray
          simpa [s1] using
            (dfsVisit_u_stays_gray (G := G) (fuel := n + 1) (u := u) (s := s)
              (by omega) hwhite)
        have hcostState : s2 =
            (G.adj u).toList.foldl (dfsPlainFoldStep G n u) s1 := by
          simpa [folded, s2] using
            (dfsCostFold_state G n u (G.adj u).toList (s1, 0))
        have hgray : s2.color u = Color.gray := by
          rw [hcostState]
          exact hplainGray
        have hwhiteStart : whiteCount G s1 + 1 = whiteCount G s := by
          simpa [s1] using whiteCount_setColor_gray G hu hwhite
        have hblackStart : blackWeight G s1 = blackWeight G s := by
          simpa [s1] using blackWeight_setColor_gray_of_white G hwhite
        have hwhiteFinish :
            whiteCount G (s2.setColor u Color.black |>.setFinish u) =
              whiteCount G s2 := by
          simpa using whiteCount_setColor_black_of_not_white G (by
            rw [hgray]
            decide)
        have hblackFinish :
            blackWeight G (s2.setColor u Color.black |>.setFinish u) =
              blackWeight G s2 + (G.adj u).card := by
          exact blackWeight_setColor_black G hu hgray
        have hresult : dfsVisitWithCost G (n + 1) u s =
            (s2.setColor u Color.black |>.setFinish u,
              1 + (G.adj u).card + cost2) := by
          have hstep :
              (fun (sc : DFSState V × Nat) (v : V) =>
                if sc.1.color v = Color.white then
                  let result := dfsVisitWithCost G n v (sc.1.setParent v u)
                  (result.1, sc.2 + result.2)
                else sc) = dfsCostFoldStep G n u := by
            funext sc v
            rfl
          simp only [dfsVisitWithCost, hwhite, if_pos]
          rw [hstep]
        rw [hresult]
        change
          (1 + (G.adj u).card + cost2) +
                whiteCount G (s2.setColor u Color.black |>.setFinish u) +
              blackWeight G s =
            whiteCount G s +
              blackWeight G (s2.setColor u Color.black |>.setFinish u)
        omega
      · simp [dfsVisitWithCost, hwhite]

/-- A costed DFS traversal over graph vertices satisfies the same exact work
balance as one visit. -/
theorem dfsFromListWithCost_balance {fuel : Nat} {vertices : List V}
    {s : DFSState V} (hvertices : ∀ v ∈ vertices, v ∈ G.vertices) :
    let result := dfsFromListWithCost G fuel vertices s
    result.2 + whiteCount G result.1 + blackWeight G s =
      whiteCount G s + blackWeight G result.1 := by
  induction vertices generalizing s with
  | nil => simp [dfsFromListWithCost]
  | cons u rest restIH =>
      have hu : u ∈ G.vertices := hvertices u (by simp)
      have hrest : ∀ v ∈ rest, v ∈ G.vertices := by
        intro v hv
        exact hvertices v (by simp [hv])
      by_cases hwhite : s.color u = Color.white
      · let visitResult := dfsVisitWithCost G fuel u s
        let restResult := dfsFromListWithCost G fuel rest visitResult.1
        have hvisit := dfsVisitWithCost_balance G (fuel := fuel) (u := u) (s := s) hu
        have htail := restIH (s := visitResult.1) hrest
        have hresult : dfsFromListWithCost G fuel (u :: rest) s =
            (restResult.1, visitResult.2 + restResult.2) := by
          simp [dfsFromListWithCost, hwhite, visitResult, restResult]
        rw [hresult]
        change
          visitResult.2 + restResult.2 + whiteCount G restResult.1 +
              blackWeight G s =
            whiteCount G s + blackWeight G restResult.1
        have hvisit' :
            visitResult.2 + whiteCount G visitResult.1 + blackWeight G s =
              whiteCount G s + blackWeight G visitResult.1 := by
          simpa [visitResult] using hvisit
        have htail' :
            restResult.2 + whiteCount G restResult.1 + blackWeight G visitResult.1 =
              whiteCount G visitResult.1 + blackWeight G restResult.1 := by
          simpa [restResult] using htail
        omega
      · simpa [dfsFromListWithCost, hwhite] using restIH (s := s) hrest

/-- The initial DFS state has one white vertex for every graph vertex. -/
private theorem whiteCount_dfsInit : whiteCount G (dfsInit : DFSState V) = G.vertices.card := by
  simp [whiteCount, dfsInit]

/-- The initial DFS state has scanned no outgoing adjacency list. -/
private theorem blackWeight_dfsInit : blackWeight G (dfsInit : DFSState V) = 0 := by
  simp [blackWeight, dfsInit]

/-- A whole-graph DFS result has no remaining white graph vertex. -/
private theorem whiteCount_dfsWithCost : whiteCount G (dfsWithCost (G := G)).1 = 0 := by
  rw [dfsWithCost_result]
  simp only [whiteCount, Finset.card_eq_zero]
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hv, hwhite⟩
    rw [G.dfs_all_black hv] at hwhite
    cases hwhite
  · simp

/-- A whole-graph DFS result has scanned every outgoing adjacency list. -/
private theorem blackWeight_dfsWithCost :
    blackWeight G (dfsWithCost (G := G)).1 = edgeCount G := by
  rw [dfsWithCost_result]
  simp only [blackWeight, edgeCount]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  constructor
  · exact And.left
  · intro hv
    exact ⟨hv, G.dfs_all_black hv⟩

/-- **Exact DFS work.**  The costed whole-graph traversal charges one unit per
vertex and one unit per directed edge. -/
theorem dfsWithCost_cost_eq :
    (dfsWithCost (G := G)).2 = G.vertices.card + edgeCount G := by
  have hvertices : ∀ v ∈ G.vertices.toList, v ∈ G.vertices := by
    intro v hv
    exact Finset.mem_toList.mp hv
  have hbalance := dfsFromListWithCost_balance G
    (fuel := G.vertices.card + 1) (vertices := G.vertices.toList)
    (s := dfsInit) hvertices
  change (dfsWithCost (G := G)).2 + whiteCount G (dfsWithCost (G := G)).1 +
      blackWeight G dfsInit =
    whiteCount G dfsInit + blackWeight G (dfsWithCost (G := G)).1 at hbalance
  rw [whiteCount_dfsWithCost, blackWeight_dfsInit, whiteCount_dfsInit,
    blackWeight_dfsWithCost] at hbalance
  omega

/-- **DFS running time.**  The instrumented depth-first search costs at most
{lit}`V + E` control steps, and hence runs in {lit}`O(V + E)` in the selected
model. -/
theorem dfsWithCost_cost_le :
    (dfsWithCost (G := G)).2 ≤ G.vertices.card + edgeCount G := by
  exact (dfsWithCost_cost_eq G).le

end Graph
end Chapter22
end CLRS
