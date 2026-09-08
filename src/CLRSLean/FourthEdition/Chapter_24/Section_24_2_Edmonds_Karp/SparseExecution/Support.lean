import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S3_WorkAnalysis
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS.CostedSupportBFS

/-!
# The fixed sparse residual support

Positive-capacity arcs and their reverses contain every residual edge of every
feasible flow. The executable input supplies those positive arcs as a list;
its representation proof establishes completeness and absence of duplicates.
Support preparation executes two bucket insertions per input arc. It does not
search an implicit dense capacity matrix to discover the sparse input.
-/
noncomputable section
namespace CLRS.Chapter26.SparseEK
open Finset Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

def positiveArcs (G : FlowNetwork V) : Finset (V × V) :=
  Finset.univ.filter (fun e => 0 < G.c e.1 e.2)

def support (G : FlowNetwork V) : Finset (V × V) :=
  positiveArcs G ∪ (positiveArcs G).image Prod.swap

@[simp] theorem mem_support (u v : V) :
    (u,v) ∈ support G ↔ 0 < G.c u v ∨ 0 < G.c v u := by
  simp [support, positiveArcs]

theorem support_card_le (G : FlowNetwork V) :
    (support G).card ≤ 2 * (positiveArcs G).card := by
  have hi := Finset.card_image_le (s := positiveArcs G) (f := Prod.swap)
  have hu := Finset.card_union_le (positiveArcs G) ((positiveArcs G).image Prod.swap)
  unfold support
  omega

theorem residual_mem_support (φ : Flow V G) {u v : V} (h : φ.residualEdge u v) :
    (u,v) ∈ support G := by
  rw [mem_support]
  by_contra hn
  push Not at hn
  have hc := φ.hcapacity v u
  have hs := φ.hskew_symm u v
  change 0 < G.c u v - φ.f u v at h
  linarith

/-- A sparse-capacity input representation, not a premise about execution counts. -/
structure CapacityInput (G : FlowNetwork V) where
  arcs : List (V × V)
  nodup : arcs.Nodup
  mem_iff : ∀ u v, (u,v) ∈ arcs ↔ 0 < G.c u v

theorem CapacityInput.length_eq (input : CapacityInput G) :
    input.arcs.length = (positiveArcs G).card := by
  have heq : input.arcs.toFinset = positiveArcs G := by
    ext ⟨u,v⟩
    simp [positiveArcs, input.mem_iff]
  rw [← heq, List.toFinset_card_of_nodup input.nodup]

def prepare : List (V × V) → SupportBuild V
  | [] => ⟨SupportAdjacency.empty, 0⟩
  | e :: es =>
    let old := prepare es
    ⟨(old.adjacency.insertArc e).insertArc e.swap, old.work + 2⟩

omit [Fintype V] in
theorem prepare_work (es : List (V × V)) : (prepare es).work = 2 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [prepare, ih, Nat.mul_add, Nat.add_comm]

omit [Fintype V] in
theorem prepare_mem (es : List (V × V)) (u v : V) :
    v ∈ (prepare es).adjacency.bucket u ↔ (u,v) ∈ es ∨ (v,u) ∈ es := by
  induction es with
  | nil => simp [prepare]
  | cons e es ih =>
    rcases e with ⟨a,b⟩
    simp [prepare, SupportAdjacency.mem_insertArc_bucket, ih]
    tauto

theorem CapacityInput.prepare_mem (input : CapacityInput G) (u v : V) :
    v ∈ (prepare input.arcs).adjacency.bucket u ↔ (u,v) ∈ support G := by
  simp [SparseEK.prepare_mem, input.mem_iff]

omit [Fintype V] in
private theorem adjacency_ext {A B : SupportAdjacency V} (h : A.bucket = B.bucket) : A = B := by
  cases A
  cases B
  cases h
  rfl

theorem CapacityInput.prepare_storage (input : CapacityInput G) :
    (prepare input.arcs).adjacency.storage = (support G).card := by
  have heq : (prepare input.arcs).adjacency = (buildSupportAdjacency (support G)).adjacency := by
    apply adjacency_ext
    funext u
    ext v
    rw [input.prepare_mem, mem_buildSupportAdjacency]
  rw [heq, buildSupportAdjacency_storage]

theorem CapacityInput.covers (input : CapacityInput G) (φ : Flow V G) :
    SupportsResidual (prepare input.arcs).adjacency φ := by
  intro u v h
  exact (input.prepare_mem u v).2 (residual_mem_support φ h)

/-- Isolated vertices are never dequeued: a reached non-source vertex is a support target. -/
theorem residualBFS_visited_subset (φ : Flow V G) :
    (residualBFS φ).visited ⊆ insert G.s ((support G).image Prod.snd) := by
  intro v hv
  have hr := (residualBFS_visited_iff_reachable φ v).1 hv
  induction hr with
  | refl => simp
  | @tail v w hprev hedge ih =>
    exact mem_insert_of_mem (mem_image.mpr ⟨(v,w), residual_mem_support φ hedge, rfl⟩)

/-- Actual support BFS work has no ambient-vertex term, even with isolated vertices. -/
theorem bfs_work_le (input : CapacityInput G) (φ : Flow V G) :
    (costedResidualBFS (prepare input.arcs).adjacency φ).work ≤
      1 + 5 * (support G).card := by
  let A := (prepare input.arcs).adjacency
  have cover := input.covers φ
  have hinitQueue : BFSQueueInv φ (bfsStateInit G.s).visited (bfsStateInit G.s).queue := by
    intro v hv
    simpa [BFSQueueInv, bfsStateInit] using hv
  have hinitNodup : (bfsStateInit G.s).queue.Nodup := by simp [bfsStateInit]
  have hw := costedBFSAux_work_eq A φ cover (Fintype.card V) (bfsStateInit G.s)
    hinitQueue hinitNodup
  rw [supportBFSWork_init] at hw
  have hstate := costedResidualBFS_state A φ cover
  have hqueue : (costedResidualBFS A φ).state.queue = [] := by
    rw [hstate]; exact residualBFS_queue_empty φ
  have hw' : (costedResidualBFS A φ).work =
      (residualBFS φ).visited.card + 4 * ∑ u ∈ (residualBFS φ).visited, (A.bucket u).card := by
    change (costedResidualBFS A φ).work + 0 =
      supportBFSWork A (costedResidualBFS A φ).state.visited
        (costedResidualBFS A φ).state.queue at hw
    rw [Nat.add_zero, hstate] at hw
    simpa [supportBFSWork, residualBFS_queue_empty] using hw
  have hc := Finset.card_le_card (residualBFS_visited_subset φ)
  have hci := Finset.card_insert_le G.s ((support G).image Prod.snd)
  have him := Finset.card_image_le (s := support G) (f := Prod.snd)
  have hsum := sum_bucket_card_le_storage A (residualBFS φ).visited
  have hstorage : A.storage = (support G).card := input.prepare_storage
  rw [hw']
  omega

end CLRS.Chapter26.SparseEK
