import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S3_ExecutablePrim

/-!
# Counters on the reference frontier execution

These counters measure edge visits, attempted and successful decreases, and
minimum-key comparisons in the actual reference loop. This implementation
rebuilds its frontier each round. Its finite-set sorting, functional-map access,
and component-oracle evaluation are not constant-time operations certified by
these counters. In particular, these results do not imply binary-heap runtime.
-/
namespace CLRS.MST.ExecutablePrim.CountedFrontier
variable {n : Nat} {E : Type} [LinearOrder E]

structure Built (n : Nat) (E : Type) where
  queue : Queue n E
  edgeVisits : Nat
  decreaseTests : Nat
  decreases : Nat

def build (G : FiniteGraph (Fin n) E) (w : E → Nat) (S : Finset (Fin n)) :
    List E → Built n E
  | [] => ⟨Queue.initial (G.vertices \ S), 0, 0, 0⟩
  | e :: es =>
    let old := build G w S es
    if crossesBool G.toGraph S e then
      let v := outsideVertex G.toGraph S e
      if (w e : Key) < old.queue.key v then
        ⟨{ old.queue with key := Function.update old.queue.key v (w e)
                          parent := Function.update old.queue.parent v (some e) },
          old.edgeVisits + 1, old.decreaseTests + 1, old.decreases + 1⟩
      else ⟨old.queue, old.edgeVisits + 1, old.decreaseTests + 1, old.decreases⟩
    else ⟨old.queue, old.edgeVisits + 1, old.decreaseTests, old.decreases⟩

theorem build_refines (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) (es : List E) :
    (build G w S es).queue = buildQueue G w S es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [build, buildQueue, relaxEdge]
    split
    · simp only [Queue.decreaseKey, ih]
      split <;> rfl
    · exact ih

theorem build_counts (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) (es : List E) :
    (build G w S es).edgeVisits = es.length ∧
    (build G w S es).decreases ≤ (build G w S es).decreaseTests ∧
    (build G w S es).decreaseTests ≤ es.length := by
  induction es with
  | nil => simp [build]
  | cons e es ih =>
    simp only [build, List.length_cons]
    split
    · split <;> dsimp <;> omega
    · dsimp; omega

/-- Tail-first linear extraction with one count at each actual key comparison. -/
def minimum (key : Fin n → Key) : List (Fin n) → Option (Fin n) × Nat
  | [] => (none, 0)
  | v :: vs =>
    let old := minimum key vs
    match old.1 with
    | none => (some v, old.2)
    | some u => (if key v ≤ key u then some v else some u, old.2 + 1)

theorem minimum_refines (key : Fin n → Key) (vs : List (Fin n)) :
    (minimum key vs).1 = extractMinList key vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [minimum, extractMinList, ih]
    cases extractMinList key vs <;> rfl

theorem minimum_comparisons (key : Fin n → Key) (vs : List (Fin n)) :
    (minimum key vs).2 = vs.length - 1 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [minimum]
    split
    · rename_i h
      have hv : vs = [] := (extractMinList_eq_none_iff key vs).1
        ((minimum_refines key vs).symm.trans h)
      subst vs
      rfl
    · rename_i u h
      have hv : vs ≠ [] := by
        intro he; subst vs; simp [minimum] at h
      have hp := List.length_pos_iff.mpr hv
      simp only [List.length_cons]
      omega

structure Round where
  edgeVisits : Nat
  decreaseTests : Nat
  decreases : Nat
  minComparisons : Nat
  extracted : Bool
  deriving Repr, DecidableEq

def choose (G : FiniteGraph (Fin n) E) (w : E → Nat) (S : Finset (Fin n)) :
    Option (Fin n × E) × Round :=
  let b := build G w S (G.edges.sort (· ≤ ·))
  let m := minimum b.queue.key (b.queue.members.sort (· ≤ ·))
  let result := m.1.bind (fun u => (b.queue.parent u).map (fun e => (u, e)))
  (result, ⟨b.edgeVisits, b.decreaseTests, b.decreases, m.2, result.isSome⟩)

theorem choose_refines (G : FiniteGraph (Fin n) E) (w : E → Nat) (S : Finset (Fin n)) :
    (choose G w S).1 = (frontierQueue G w S).choose := by
  simp only [choose, build_refines, minimum_refines, frontierQueue, Queue.choose, Queue.extractMin]
  cases extractMinList (buildQueue G w S (G.edges.sort (· ≤ ·))).key
      ((buildQueue G w S (G.edges.sort (· ≤ ·))).members.sort (· ≤ ·)) with
  | none => rfl
  | some u =>
    simp only [Option.bind_some]
    cases hp : (buildQueue G w S (G.edges.sort (· ≤ ·))).parent u <;> simp [hp]

theorem choose_counts (G : FiniteGraph (Fin n) E) (w : E → Nat) (S : Finset (Fin n)) :
    (choose G w S).2.edgeVisits = G.edges.card ∧
    (choose G w S).2.decreases ≤ (choose G w S).2.decreaseTests ∧
    (choose G w S).2.decreaseTests ≤ G.edges.card ∧
    (choose G w S).2.minComparisons = (G.vertices \ S).card - 1 := by
  have hb := build_counts G w S (G.edges.sort (· ≤ ·))
  simp only [Finset.length_sort] at hb
  refine ⟨hb.1, hb.2.1, hb.2.2, ?_⟩
  simp only [choose, minimum_comparisons, build_refines, Finset.length_sort]
  rw [(buildQueue_invariant G w S (G.edges.sort (· ≤ ·))
    (fun e he => (G.edges.mem_sort (· ≤ ·)).1 he)).members_eq]

structure Execution (E : Type) where
  edges : List E
  rounds : List Round
  deriving Repr

def execute (G : FiniteGraph (Fin n) E) (C : ComponentOracle G.toGraph)
    (w : E → Nat) (root : Fin n) : Nat → Finset E → Execution E
  | 0, _ => ⟨[], []⟩
  | fuel + 1, A =>
    let step := choose G w (C.component A root)
    match step.1 with
    | none => ⟨[], [step.2]⟩
    | some (_, e) =>
      let rest := execute G C w root fuel (insert e A)
      ⟨e :: rest.edges, step.2 :: rest.rounds⟩

theorem execute_refines (G : FiniteGraph (Fin n) E) (C : ComponentOracle G.toGraph)
    (w : E → Nat) (root : Fin n)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (fuel : Nat) (A : Finset E) :
    (execute G C w root fuel A).edges = frontierRun G C w root hall fuel A := by
  induction fuel generalizing A with
  | zero => rfl
  | succ fuel ih =>
    simp only [execute, frontierRun, run, frontierProvider, choose_refines]
    split <;> rename_i h <;> simp_all [frontierRun, frontierProvider]

/-- The recorded rounds are generated by the execution, including its last failed extraction. -/
theorem execute_rounds_le (G : FiniteGraph (Fin n) E) (C : ComponentOracle G.toGraph)
    (w : E → Nat) (root : Fin n) (fuel : Nat) (A : Finset E) :
    (execute G C w root fuel A).rounds.length ≤ fuel := by
  induction fuel generalizing A with
  | zero => simp [execute]
  | succ fuel ih =>
    simp only [execute]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (ih _)

/-- Every recorded round scans the entire edge list; it is not an adjacency-once heap trace. -/
theorem execute_edgeVisits (G : FiniteGraph (Fin n) E) (C : ComponentOracle G.toGraph)
    (w : E → Nat) (root : Fin n) (fuel : Nat) (A : Finset E) :
    ((execute G C w root fuel A).rounds.map Round.edgeVisits).sum =
      (execute G C w root fuel A).rounds.length * G.edges.card := by
  induction fuel generalizing A with
  | zero => simp [execute]
  | succ fuel ih =>
    simp only [execute]
    split <;> simp [choose_counts, ih, Nat.add_mul, Nat.add_comm]

theorem execute_edgeVisits_le (G : FiniteGraph (Fin n) E) (C : ComponentOracle G.toGraph)
    (w : E → Nat) (root : Fin n) (fuel : Nat) (A : Finset E) :
    ((execute G C w root fuel A).rounds.map Round.edgeVisits).sum ≤ fuel * G.edges.card := by
  rw [execute_edgeVisits]
  exact Nat.mul_le_mul_right _ (execute_rounds_le G C w root fuel A)

end CLRS.MST.ExecutablePrim.CountedFrontier
