import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.SparseExecution.Update

/-!
# Edmonds–Karp from the counted BFS-selected paths

Support buckets and the finite vertex count are prepared once. A polynomial
number of rounds suffices for arbitrary nonnegative real capacities. A round
that finds no path retains its flow; later rounds may repeat the failed BFS,
and their work remains included. The same returned flow, path choices, and
local updates are used in the correctness and work proofs.
-/
noncomputable section
namespace CLRS.Chapter26.SparseEK
open Finset Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

structure ExecutionResult (G : FlowNetwork V) where
  flow : Flow V G
  work : Nat
  augmentations : Nat

def step (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (prev : ExecutionResult G) : ExecutionResult G :=
  let found := search input A hA prev.flow
  match found.path with
  | none => ⟨prev.flow,prev.work+found.work,prev.augmentations⟩
  | some p =>
    let next := augmentWithCost prev.flow p.path
    ⟨next.flow,prev.work+found.work+next.work,prev.augmentations+1⟩

def iterate (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (N : Nat) : ExecutionResult G :=
  Nat.rec ⟨zeroFlow G,0,0⟩ (fun _ previous => step input A hA previous) N

@[simp] theorem iterate_zero (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) :
    iterate input A hA 0 = ⟨zeroFlow G,0,0⟩ := rfl

@[simp] theorem iterate_succ (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (N : Nat) :
    iterate input A hA (N+1) = step input A hA (iterate input A hA N) := rfl

def timeline (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) : Timeline G where
  flow i := (iterate input A hA i).flow
  path i := (search input A hA (iterate input A hA i).flow).path
  next i := by
    cases hp : (search input A hA (iterate input A hA i).flow).path with
    | none => simp [iterate_succ,step,hp]
    | some p => simpa [iterate_succ,step,hp] using
        augmentWithCost_refines (iterate input A hA i).flow p.path

theorem iterate_no_path_step (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (i : Nat)
    (h : ¬ (iterate input A hA i).flow.hasAugmentingPath) :
    (iterate input A hA (i+1)).flow = (iterate input A hA i).flow := by
  have hn := (search_none_iff input A hA _).2 h
  simp [iterate_succ,step,hn]

theorem iterate_stable (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) {i j : Nat} (hij : i ≤ j)
    (h : ¬ (iterate input A hA i).flow.hasAugmentingPath) :
    (iterate input A hA j).flow = (iterate input A hA i).flow := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [iterate_no_path_step input A hA k (by simpa [ih] using h),ih]

/-- The bound comes from the actual selector's timeline, not the old classical chooser. -/
theorem iterate_terminal (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (N : Nat)
    (hN : (support G).card * Fintype.card V < N) :
    ¬ (iterate input A hA N).flow.hasAugmentingPath := by
  intro hlast
  have hall : ∀ i < N, (timeline input A hA).Augments i := by
    intro i hi
    cases hp : (search input A hA (iterate input A hA i).flow).path with
    | none =>
      have hn := (search_none_iff input A hA _).1 hp
      have hs := iterate_stable input A hA (Nat.le_of_lt hi) hn
      exact (hn (hs ▸ hlast)).elim
    | some p => exact ⟨p,hp⟩
  have hc := (timeline input A hA).all_steps_bound N hall
  omega

theorem iterate_augmentations (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (N : Nat) :
    (iterate input A hA N).augmentations =
      ((Finset.range N).filter (timeline input A hA).Augments).card := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one]
    cases hp : (search input A hA (iterate input A hA N).flow).path with
    | none =>
      have hn : ¬ (timeline input A hA).Augments N := by
        simp [Timeline.Augments,timeline,hp]
      simp [iterate_succ,step,hp,Finset.filter_insert,hn,ih]
    | some p =>
      have hn : (timeline input A hA).Augments N := ⟨p,hp⟩
      simp [iterate_succ,step,hp,Finset.filter_insert,hn,ih]

theorem iterate_work_le (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (N : Nat) :
    (iterate input A hA N).work ≤ N*(5+17*(support G).card) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := search_work_le input A hA (iterate input A hA N).flow
    simp only [iterate_succ,step]
    split
    · dsimp only
      nlinarith
    · rename_i p hp
      have hu := augmentWithCost_work_le (iterate input A hA N).flow p
      dsimp only
      nlinarith

/-- Count the input vertex enumeration once; no per-round dense initialization occurs. -/
def countVertices : List V → Nat
  | [] => 0
  | _ :: vs => countVertices vs+1

omit [Fintype V] [DecidableEq V] in
theorem countVertices_eq (vs : List V) : countVertices vs = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [countVertices,ih]

def execute (input : CapacityInput G) : ExecutionResult G :=
  let prepared := prepare input.arcs
  let vertices := countVertices (Finset.univ.toList : List V)
  let result := iterate input prepared.adjacency rfl (prepared.work*vertices+1)
  { result with work := prepared.work+vertices+result.work }

/-- The actual returned flow is maximal, without an integrality premise. -/
theorem execute_maximal (input : CapacityInput G) : (execute input).flow.isMaximal := by
  apply Flow.maximal_of_noAugmentingPath
  apply iterate_terminal input _ rfl
  have hc := support_card_le G
  simp only [prepare_work,countVertices_eq,Finset.length_toList,Finset.card_univ]
  rw [input.length_eq]
  nlinarith [Nat.mul_le_mul_right (Fintype.card V) hc]

/-- Actual augmentations are bounded by positive arcs times vertices. -/
theorem execute_augmentations_le (input : CapacityInput G) :
    (execute input).augmentations ≤ 2*(positiveArcs G).card*Fintype.card V := by
  change (iterate input _ rfl _).augmentations ≤ _
  rw [iterate_augmentations]
  exact (timeline input _ rfl).augmentation_count_sparse _

/-- General bound before absorbing lower-order preparation and failed-search costs. -/
theorem execute_work_polynomial (input : CapacityInput G) :
    (execute input).work ≤ 2*(positiveArcs G).card+Fintype.card V+
      (2*(positiveArcs G).card*Fintype.card V+1)*(5+34*(positiveArcs G).card) := by
  have hi := iterate_work_le input (prepare input.arcs).adjacency rfl
    ((prepare input.arcs).work*countVertices (Finset.univ.toList : List V)+1)
  have hs := support_card_le G
  simp only [execute,prepare_work,countVertices_eq,Finset.length_toList,Finset.card_univ,input.length_eq] at *
  nlinarith [Nat.mul_le_mul_left (2*(positiveArcs G).card*Fintype.card V+1)
    (show 5+17*(support G).card ≤ 5+34*(positiveArcs G).card by omega)]

/-- On nonempty sparse inputs the complete counted execution is O(V E²). -/
theorem execute_work_bound (input : CapacityInput G) (hE : 0 < (positiveArcs G).card) :
    (execute input).work ≤ 130*Fintype.card V*((positiveArcs G).card)^2 := by
  have hc := execute_work_polynomial input
  have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.s⟩
  have hE1 : 1 ≤ (positiveArcs G).card := hE
  have hsq : (positiveArcs G).card ≤ ((positiveArcs G).card)^2 := by nlinarith
  have hVE : (positiveArcs G).card ≤ Fintype.card V*(positiveArcs G).card := by nlinarith
  have hVE2 : ((positiveArcs G).card)^2 ≤ Fintype.card V*((positiveArcs G).card)^2 := by nlinarith
  have hV2 : Fintype.card V ≤ Fintype.card V*((positiveArcs G).card)^2 := by nlinarith
  nlinarith

/-- Empty capacity input still pays for vertex enumeration and one failed search. -/
theorem execute_work_empty (input : CapacityInput G) (hE : (positiveArcs G).card = 0) :
    (execute input).work ≤ Fintype.card V+2 := by
  have hs : (support G).card = 0 := by have := support_card_le G; omega
  have hn : ¬ (zeroFlow G).hasAugmentingPath := by
    intro h
    obtain ⟨p⟩ := exists_shortest_augmenting_path (zeroFlow G) h
    have hp := shortest_length_support (zeroFlow G) p
    have hpos := p.path.edges_nonempty
    have : 0 < p.path.edges.length := List.length_pos_iff.mpr hpos
    omega
  have hp := (search_none_iff input (prepare input.arcs).adjacency rfl _).2 hn
  have hw := search_work_of_none input (prepare input.arcs).adjacency rfl _ hp
  have hb := bfs_work_le input (zeroFlow G)
  simp only [hs,Nat.mul_zero,Nat.add_zero] at hb
  simp only [execute,prepare_work,countVertices_eq,Finset.length_toList,Finset.card_univ,
    input.length_eq,hE,Nat.mul_zero,Nat.zero_mul,Nat.zero_add,iterate_succ,iterate_zero,step,hp]
  omega

/-- Uniform bound including the empty sparse input and its initialization. -/
theorem execute_work_uniform (input : CapacityInput G) :
    (execute input).work ≤ Fintype.card V+2+
      130*Fintype.card V*((positiveArcs G).card)^2 := by
  by_cases hE : (positiveArcs G).card = 0
  · simpa [hE] using execute_work_empty input hE
  · have := execute_work_bound input (Nat.pos_of_ne_zero hE)
    omega

end CLRS.Chapter26.SparseEK
