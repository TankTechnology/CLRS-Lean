import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim

/-!
# Chapter 23 - Executable indexed-queue Prim

This module supplies the implementation-facing state omitted by the abstract
`PrimTrace`: a finite priority queue, vertex keys, parent edges,
`decreaseKey`, and `extractMin`.  The queue implementation is a small
executable reference model.  Its operation trace is also the semantic target
for an array-backed binary heap refinement.
-/

namespace CLRS
namespace MST
namespace ExecutablePrim

open Finset

variable {n : Nat} {E : Type} [LinearOrder E]

/-- `top` is the CLRS infinity key; finite values are edge weights. -/
abbrev Key := WithTop Nat

/-- Indexed minimum-priority-queue state used by Prim. -/
structure Queue (n : Nat) (E : Type) where
  members : Finset (Fin n)
  key : Fin n → Key
  parent : Fin n → Option E

/-- Empty-key initialization over a prescribed queue universe. -/
def Queue.initial (members : Finset (Fin n)) : Queue n E where
  members := members
  key := fun _ => ⊤
  parent := fun _ => none

/-- CLRS `DECREASE-KEY`, together with the parent edge attaining the new key.
An update whose key is not strictly smaller is ignored. -/
def Queue.decreaseKey (q : Queue n E) (v : Fin n) (k : Nat) (e : E) :
    Queue n E :=
  if (k : Key) < q.key v then
    { q with
      key := Function.update q.key v k
      parent := Function.update q.parent v (some e) }
  else q

@[simp]
theorem Queue.initial_members (members : Finset (Fin n)) :
    (Queue.initial (E := E) members).members = members :=
  rfl

@[simp]
theorem Queue.initial_key (members : Finset (Fin n)) (v : Fin n) :
    (Queue.initial (E := E) members).key v = ⊤ :=
  rfl

@[simp]
theorem Queue.initial_parent (members : Finset (Fin n)) (v : Fin n) :
    (Queue.initial (E := E) members).parent v = none :=
  rfl

@[simp]
theorem Queue.decreaseKey_members (q : Queue n E) (v : Fin n)
    (k : Nat) (e : E) :
    (q.decreaseKey v k e).members = q.members := by
  unfold Queue.decreaseKey
  split <;> rfl

/-- Decreasing one key never raises any queue key. -/
theorem Queue.decreaseKey_key_le (q : Queue n E) (v x : Fin n)
    (k : Nat) (e : E) :
    (q.decreaseKey v k e).key x ≤ q.key x := by
  unfold Queue.decreaseKey
  split <;> rename_i h
  · by_cases hx : x = v
    · subst x
      simp [Function.update, h.le]
    · simp [Function.update, hx]
  · exact le_rfl

/-- After `decreaseKey v k`, the target key is at most `k`. -/
theorem Queue.decreaseKey_target_le (q : Queue n E) (v : Fin n)
    (k : Nat) (e : E) :
    (q.decreaseKey v k e).key v ≤ (k : Key) := by
  unfold Queue.decreaseKey
  split <;> rename_i h
  · simp
  · exact le_of_not_gt h

/-- A changed parent entry records exactly the supplied edge and finite key. -/
theorem Queue.decreaseKey_parent_some {q : Queue n E} {v x : Fin n}
    {k : Nat} {e f : E}
    (hparent : (q.decreaseKey v k e).parent x = some f) :
    (x = v ∧ f = e ∧ (q.decreaseKey v k e).key x = k) ∨
      (q.parent x = some f ∧ (q.decreaseKey v k e).key x = q.key x) := by
  by_cases hk : (k : Key) < q.key v
  · by_cases hx : x = v
    · subst x
      have hfe : f = e := by
        have : e = f := by
          simpa [Queue.decreaseKey, hk, Function.update] using hparent
        exact this.symm
      subst f
      left
      simp [Queue.decreaseKey, hk, Function.update]
    · right
      have hold : q.parent x = some f := by
        simpa [Queue.decreaseKey, hk, Function.update, hx] using hparent
      exact ⟨hold, by simp [Queue.decreaseKey, hk, Function.update, hx]⟩
  · right
    have hold : q.parent x = some f := by
      simpa [Queue.decreaseKey, hk] using hparent
    exact ⟨hold, by simp [Queue.decreaseKey, hk]⟩

/-! ## Executable extract-min -/

/-- Linear reference implementation of minimum selection.  A binary heap will
refine the same operation contract below. -/
def extractMinList (key : Fin n → Key) : List (Fin n) → Option (Fin n)
  | [] => none
  | v :: vs =>
      match extractMinList key vs with
      | none => some v
      | some u => if key v ≤ key u then some v else some u

theorem extractMinList_mem {key : Fin n → Key} {vs : List (Fin n)} {u : Fin n}
    (h : extractMinList key vs = some u) : u ∈ vs := by
  induction vs with
  | nil => simp [extractMinList] at h
  | cons v vs ih =>
      simp only [extractMinList] at h
      split at h
      · simp_all
      · split at h <;> simp_all

theorem extractMinList_eq_none_iff (key : Fin n → Key) (vs : List (Fin n)) :
    extractMinList key vs = none ↔ vs = [] := by
  cases vs with
  | nil => simp [extractMinList]
  | cons v vs =>
      cases hrest : extractMinList key vs with
      | none => simp [extractMinList, hrest]
      | some u =>
          by_cases hle : key v ≤ key u <;>
            simp [extractMinList, hrest, hle]

theorem extractMinList_key_le {key : Fin n → Key} {vs : List (Fin n)}
    {u : Fin n} (h : extractMinList key vs = some u) :
    ∀ v ∈ vs, key u ≤ key v := by
  induction vs generalizing u with
  | nil => simp [extractMinList] at h
  | cons x xs ih =>
      intro v hv
      simp only [extractMinList] at h
      split at h
      · rename_i hnone
        simp only [Option.some.injEq] at h
        subst u
        have hempty : xs = [] :=
          (extractMinList_eq_none_iff key xs).1 hnone
        simp_all
      · rename_i y hy
        split at h <;> rename_i hxy
        · simp only [Option.some.injEq] at h
          subst u
          rcases List.mem_cons.mp hv with rfl | hv
          · exact le_rfl
          · exact hxy.trans (ih hy v hv)
        · simp only [Option.some.injEq] at h
          subst u
          rcases List.mem_cons.mp hv with rfl | hv
          · exact le_of_not_ge hxy
          · exact ih hy v hv

/-- Remove and return a minimum-key queue member. -/
def Queue.extractMin (q : Queue n E) : Option (Fin n × Queue n E) :=
  match h : extractMinList q.key (q.members.sort (· ≤ ·)) with
  | none => none
  | some u => some (u, { q with members := q.members.erase u })

theorem Queue.extractMin_mem {q : Queue n E} {u : Fin n} {q' : Queue n E}
    (h : q.extractMin = some (u, q')) : u ∈ q.members := by
  unfold Queue.extractMin at h
  split at h <;> rename_i hmin
  · contradiction
  · cases h
    exact (q.members.mem_sort (· ≤ ·)).mp (extractMinList_mem hmin)

theorem Queue.extractMin_key_le {q : Queue n E} {u : Fin n} {q' : Queue n E}
    (h : q.extractMin = some (u, q')) {v : Fin n} (hv : v ∈ q.members) :
    q.key u ≤ q.key v := by
  unfold Queue.extractMin at h
  split at h <;> rename_i hmin
  · contradiction
  · cases h
    exact extractMinList_key_le hmin v ((q.members.mem_sort (· ≤ ·)).mpr hv)

theorem Queue.extractMin_members {q : Queue n E} {u : Fin n} {q' : Queue n E}
    (h : q.extractMin = some (u, q')) :
    q'.members = q.members.erase u := by
  unfold Queue.extractMin at h
  split at h
  · contradiction
  · cases h
    rfl

/-! ## Building the indexed queue by edge relaxation -/

/-- The endpoint outside a cut.  It is used only when the edge is known to
cross the cut, in which case exactly one endpoint is outside. -/
def outsideVertex (G : Graph (Fin n) E) (S : Finset (Fin n)) (e : E) : Fin n :=
  if G.src e ∈ S then G.dst e else G.src e

theorem outsideVertex_not_mem {G : Graph (Fin n) E} {S : Finset (Fin n)}
    {e : E} (hcross : G.Crosses S e) : outsideVertex G S e ∉ S := by
  unfold outsideVertex
  split <;> rename_i hsrc
  · rcases hcross with h | h
    · exact h.2
    · exact (h.2 hsrc).elim
  · exact hsrc

theorem outsideVertex_eq_endpoint {G : Graph (Fin n) E}
    {S : Finset (Fin n)} {e : E} :
    outsideVertex G S e = G.src e ∨ outsideVertex G S e = G.dst e := by
  unfold outsideVertex
  split <;> simp

theorem outsideVertex_mem_vertices {G : FiniteGraph (Fin n) E}
    {S : Finset (Fin n)} {e : E} (he : e ∈ G.edges) :
    outsideVertex G.toGraph S e ∈ G.vertices := by
  rcases outsideVertex_eq_endpoint (G := G.toGraph) (S := S) (e := e) with h | h
  · rw [h]
    exact G.src_mem e he
  · rw [h]
    exact G.dst_mem e he

/-- Relax one crossing edge into the indexed queue. -/
def crossesBool (G : Graph (Fin n) E) (S : Finset (Fin n)) (e : E) : Bool :=
  if G.src e ∈ S then decide (G.dst e ∉ S) else decide (G.dst e ∈ S)

theorem crossesBool_eq_true_iff (G : Graph (Fin n) E)
    (S : Finset (Fin n)) (e : E) :
    crossesBool G S e = true ↔ G.Crosses S e := by
  by_cases hs : G.src e ∈ S <;> by_cases hd : G.dst e ∈ S <;>
    simp [crossesBool, Graph.Crosses, hs, hd]

def relaxEdge (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) (q : Queue n E) (e : E) : Queue n E :=
  if crossesBool G.toGraph S e then
    q.decreaseKey (outsideVertex G.toGraph S e) (w e) e
  else q

/-- Build the frontier queue by repeated CLRS `decreaseKey`. -/
def buildQueue (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) : List E → Queue n E
  | [] => Queue.initial (G.vertices \ S)
  | e :: es => relaxEdge G w S (buildQueue G w S es) e

/-- Inductive specification of a queue built from a finite edge prefix. -/
structure BuildInvariant (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) (edges : List E) (q : Queue n E) : Prop where
  members_eq : q.members = G.vertices \ S
  parent_sound : ∀ v e, q.parent v = some e →
    e ∈ edges ∧ e ∈ G.edges ∧ G.toGraph.Crosses S e ∧
      outsideVertex G.toGraph S e = v ∧ q.key v = w e
  covers : ∀ e, e ∈ edges → G.toGraph.Crosses S e →
    q.key (outsideVertex G.toGraph S e) ≤ (w e : Key)

theorem buildQueue_invariant (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) (edges : List E)
    (hall : ∀ e, e ∈ edges → e ∈ G.edges) :
    BuildInvariant G w S edges (buildQueue G w S edges) := by
  induction edges with
  | nil =>
      refine ⟨rfl, ?_, ?_⟩
      · intro v e h
        simp [buildQueue, Queue.initial] at h
      · intro e he
        simp at he
  | cons e edges ih =>
      have ihall : ∀ f, f ∈ edges → f ∈ G.edges := by
        intro f hf
        exact hall f (by simp [hf])
      have old := ih ihall
      by_cases hcross : G.toGraph.Crosses S e
      · let v := outsideVertex G.toGraph S e
        have hcrossBool : crossesBool G.toGraph S e = true :=
          (crossesBool_eq_true_iff G.toGraph S e).2 hcross
        have hstep :
            buildQueue G w S (e :: edges) =
              (buildQueue G w S edges).decreaseKey v (w e) e := by
          simp [buildQueue, relaxEdge, hcrossBool, v]
        rw [hstep]
        refine ⟨?_, ?_, ?_⟩
        · rw [Queue.decreaseKey_members, old.members_eq]
        · intro x f hparent
          rcases Queue.decreaseKey_parent_some hparent with hnew | hold
          · rcases hnew with ⟨hx, hfe, hkey⟩
            subst x
            subst f
            exact ⟨List.mem_cons_self, hall e List.mem_cons_self,
              hcross, rfl, hkey⟩
          · rcases hold with ⟨hparentOld, hkeyEq⟩
            rcases old.parent_sound x f hparentOld with
              ⟨hf, hfG, hfcross, hout, hkey⟩
            exact ⟨by simp [hf], hfG, hfcross, hout, hkeyEq.trans hkey⟩
        · intro f hf hfcross
          rw [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact Queue.decreaseKey_target_le _ _ _ _
          · exact (Queue.decreaseKey_key_le _ _ _ _ _).trans
              (old.covers f hf hfcross)
      · have hcrossBool : crossesBool G.toGraph S e = false := by
          cases h : crossesBool G.toGraph S e
          · rfl
          · exact (hcross ((crossesBool_eq_true_iff G.toGraph S e).1 h)).elim
        have hstep : buildQueue G w S (e :: edges) =
            buildQueue G w S edges := by
          simp [buildQueue, relaxEdge, hcrossBool]
        rw [hstep]
        refine ⟨old.members_eq, ?_, ?_⟩
        · intro v f hparent
          rcases old.parent_sound v f hparent with
            ⟨hf, hfG, hfcross, hout, hkey⟩
          exact ⟨by simp [hf], hfG, hfcross, hout, hkey⟩
        · intro f hf hfcross
          rw [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact (hcross hfcross).elim
          · exact old.covers f hf hfcross

/-- The concrete queue for the current Prim cut. -/
def frontierQueue (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) : Queue n E :=
  buildQueue G w S (G.edges.sort (· ≤ ·))

theorem frontierQueue_invariant (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) :
    BuildInvariant G w S (G.edges.sort (· ≤ ·)) (frontierQueue G w S) := by
  apply buildQueue_invariant
  intro e he
  exact (G.edges.mem_sort (· ≤ ·)).mp he

/-! ## Queue evidence implies a CLRS light edge -/

/-- The queue facts needed at one Prim extraction.  `covers` is the familiar
key invariant: every crossing edge has an outside queue endpoint whose current
key is no greater than that edge's weight. -/
structure ChoiceCertificate (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (A : Finset E) (q : Queue n E) (u : Fin n) (e : E) : Prop where
  extracted : ∃ q', q.extractMin = some (u, q')
  parent_eq : q.parent u = some e
  edge_mem : e ∈ G.edges
  crosses : G.toGraph.Crosses (C.component A root) e
  key_eq : q.key u = w e
  covers : ∀ f, G.toGraph.Crosses (C.component A root) f →
    ∃ v, v ∈ q.members ∧ q.key v ≤ (w f : Key)

/-- Extract-min plus the key invariant proves that the parent edge is globally
light across the current Prim cut. -/
theorem ChoiceCertificate.light {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} {w : E → Nat} {root : Fin n}
    {A : Finset E} {q : Queue n E} {u : Fin n} {e : E}
    (cert : ChoiceCertificate G C w root A q u e) :
    ∀ f, G.toGraph.Crosses (C.component A root) f → w e ≤ w f := by
  intro f hcross
  rcases cert.extracted with ⟨q', hextract⟩
  rcases cert.covers f hcross with ⟨v, hv, hkey⟩
  have hmin : q.key u ≤ q.key v := q.extractMin_key_le hextract hv
  rw [cert.key_eq] at hmin
  exact_mod_cast hmin.trans hkey

/-! ## Executable queue-driven Prim loop -/

/-- Extract a minimum-key vertex and return its recorded parent edge. -/
def Queue.choose (q : Queue n E) : Option (Fin n × E) := do
  let (u, _) ← q.extractMin
  let e ← q.parent u
  pure (u, e)

theorem Queue.choose_eq_some {q : Queue n E} {u : Fin n} {e : E}
    (h : q.choose = some (u, e)) :
    ∃ q', q.extractMin = some (u, q') ∧ q.parent u = some e := by
  cases hExtract : q.extractMin with
  | none => simp [Queue.choose, hExtract] at h
  | some pair =>
      rcases pair with ⟨v, q'⟩
      cases hParent : q.parent v with
      | none => simp [Queue.choose, hExtract, hParent] at h
      | some f =>
          simp [Queue.choose, hExtract, hParent] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨q', rfl, hParent⟩

/-- A queue provider recomputes or incrementally maintains the indexed heap
for each selected edge set.  The proof field is erased at runtime. -/
structure QueueProvider (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n) where
  queue : Finset E → Queue n E
  choose : Finset E → Option (Fin n × E) := fun A => (queue A).choose
  correct : ∀ A u e, choose A = some (u, e) →
    ChoiceCertificate G C w root A (queue A) u e

/-- Concrete provider obtained by scanning graph edges and applying
`decreaseKey` to their outside endpoints.  The closure hypothesis rules out
edge values outside the finite graph, matching the existing Chapter 23
`PrimTrace` quantification over all edge labels. -/
def frontierProvider (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges) :
    QueueProvider G C w root where
  queue A := frontierQueue G w (C.component A root)
  choose A := (frontierQueue G w (C.component A root)).choose
  correct := by
    intro A u e hchoose
    let S := C.component A root
    let q := frontierQueue G w S
    have hchoose' : q.choose = some (u, e) := by
      simpa [q, S] using hchoose
    rcases Queue.choose_eq_some hchoose' with ⟨q', hextract, hparent⟩
    have inv := frontierQueue_invariant G w S
    rcases inv.parent_sound u e hparent with
      ⟨heList, heG, heCross, hout, hkey⟩
    refine
      { extracted := ⟨q', hextract⟩
        parent_eq := hparent
        edge_mem := heG
        crosses := heCross
        key_eq := hkey
        covers := ?_ }
    intro f hfCross
    have hfG : f ∈ G.edges := hall A f (by simpa [S] using hfCross)
    let v := outsideVertex G.toGraph S f
    refine ⟨v, ?_, ?_⟩
    · rw [inv.members_eq]
      exact Finset.mem_sdiff.mpr
        ⟨outsideVertex_mem_vertices hfG, outsideVertex_not_mem hfCross⟩
    · exact inv.covers f ((G.edges.mem_sort (· ≤ ·)).mpr hfG)
        (by simpa [S] using hfCross)

/-- Fuelled executable Prim edge choices.  Fuel bounds the number of
successful vertex extractions. -/
def run {G : FiniteGraph (Fin n) E} {C : ComponentOracle G.toGraph}
    {w : E → Nat} {root : Fin n}
    (provider : QueueProvider G C w root) : Nat → Finset E → List E
  | 0, _ => []
  | fuel + 1, A =>
      match provider.choose A with
      | none => []
      | some (_, e) => e :: run provider fuel (insert e A)

/-- The executable key/parent/extract-min loop refines the abstract CLRS
`PrimTrace` consumed by the Chapter 23 MST theorem. -/
theorem run_refines_PrimTrace {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} {w : E → Nat} {root : Fin n}
    (provider : QueueProvider G C w root) (fuel : Nat) (A : Finset E) :
    G.PrimTrace C w root (run provider fuel A) A := by
  induction fuel generalizing A with
  | zero => trivial
  | succ fuel ih =>
      simp only [run]
      split
      · trivial
      · rename_i u e hchoose
        have cert := provider.correct A u e hchoose
        exact ⟨cert.edge_mem, cert.crosses, cert.light, ih (insert e A)⟩

/-- Fully instantiated executable Prim choices from the concrete frontier
queue. -/
def frontierRun (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (fuel : Nat) (A : Finset E) : List E :=
  run (frontierProvider G C w root hall) fuel A

theorem frontierRun_refines_PrimTrace (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (fuel : Nat) (A : Finset E) :
    G.PrimTrace C w root (frontierRun G C w root hall fuel A) A :=
  run_refines_PrimTrace (frontierProvider G C w root hall) fuel A

/-! ## Binary-heap operation-count model -/

/-- One extraction and a finite batch of decreases in a binary heap. -/
structure HeapRound where
  decreases : Nat

/-- Binary-heap work charged to a sequence of Prim rounds. -/
def binaryHeapWork (vertices : Nat) (rounds : List HeapRound) : Nat :=
  (rounds.map fun r =>
    (r.decreases + 1) * (Nat.log2 vertices + 1)).sum

theorem binaryHeapWork_eq (vertices : Nat) (rounds : List HeapRound) :
    binaryHeapWork vertices rounds =
      ((rounds.map HeapRound.decreases).sum + rounds.length) *
        (Nat.log2 vertices + 1) := by
  induction rounds with
  | nil => simp [binaryHeapWork]
  | cons r rounds ih =>
      rw [show binaryHeapWork vertices (r :: rounds) =
          (r.decreases + 1) * (Nat.log2 vertices + 1) +
            binaryHeapWork vertices rounds by rfl]
      rw [ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      ring

/-- Direct binary-heap bound before using graph connectedness to absorb the
vertex term into the edge term. -/
theorem binaryHeapWork_le_edges_vertices_log {vertices edges : Nat}
    {rounds : List HeapRound}
    (hdecreases : (rounds.map HeapRound.decreases).sum ≤ 2 * edges)
    (hextracts : rounds.length ≤ vertices) :
    binaryHeapWork vertices rounds ≤
      (2 * edges + vertices) * (Nat.log2 vertices + 1) := by
  rw [binaryHeapWork_eq]
  exact Nat.mul_le_mul_right _ (Nat.add_le_add hdecreases hextracts)

/-- With at most one decrease per scanned adjacency and at most one extraction
per vertex, a binary-heap Prim trace has the textbook `O(E log V)` bound. -/
theorem binaryHeapWork_le_edge_log {vertices edges : Nat}
    {rounds : List HeapRound}
    (hdecreases : (rounds.map HeapRound.decreases).sum ≤ 2 * edges)
    (hextracts : rounds.length ≤ vertices)
    (hconnected : vertices ≤ 2 * edges) :
    binaryHeapWork vertices rounds ≤
      4 * edges * (Nat.log2 vertices + 1) := by
  exact (binaryHeapWork_le_edges_vertices_log hdecreases hextracts).trans <| by
    nlinarith [Nat.zero_le (Nat.log2 vertices + 1)]

/-- Alternative queue costs: an unsorted array gives quadratic extraction,
whereas Fibonacci-heap decrease-key yields the usual `E + V log V` profile. -/
def unsortedArrayWork (vertices edges : Nat) : Nat :=
  vertices * vertices + edges

def fibonacciHeapWork (vertices edges : Nat) : Nat :=
  edges + vertices * (Nat.log2 vertices + 1)

end ExecutablePrim
end MST
end CLRS
