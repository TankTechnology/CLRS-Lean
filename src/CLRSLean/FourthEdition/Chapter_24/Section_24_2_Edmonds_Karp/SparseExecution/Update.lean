import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.SparseExecution.Search

/-!
# Local counted flow updates

The recovered path is converted to consecutive arcs once. A counted scan finds
its bottleneck, then two dictionary-cell updates are executed per arc. The
resulting dictionary refines the legacy mathematical augmentation. Dictionary
reads/writes and exact-real arithmetic are unit-cost abstract primitives, as in
the existing support-BFS model; persistent-container evaluator time is excluded.
-/
noncomputable section
namespace CLRS.Chapter26.SparseEK
open Finset Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

def edgesWithCost : List V → List (V × V) × Nat
  | [] => ([],0)
  | [_] => ([],0)
  | a :: b :: vs =>
    let old := edgesWithCost (b :: vs)
    ((a,b) :: old.1, old.2+1)

omit [Fintype V] [DecidableEq V] in
theorem edgesWithCost_spec (vs : List V) :
    (edgesWithCost vs).1 = vs.consecutivePairs ∧
      (edgesWithCost vs).2 = vs.length-1 := by
  induction vs with
  | nil => exact ⟨rfl,rfl⟩
  | cons a vs ih =>
    cases vs with
    | nil => exact ⟨rfl,rfl⟩
    | cons b vs => simp [edgesWithCost, List.consecutivePairs, ih]

def scanCaps (φ : Flow V G) : List (V × V) → WithTop ℝ × Nat
  | [] => (⊤,0)
  | e :: es =>
    let old := scanCaps φ es
    (min (φ.residualCapacity e.1 e.2 : WithTop ℝ) old.1, old.2+4)

@[simp] theorem scanCaps_work (φ : Flow V G) (es : List (V × V)) :
    (scanCaps φ es).2 = 4*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [scanCaps, ih, Nat.mul_add, Nat.add_comm]

theorem scanCaps_le (φ : Flow V G) (es : List (V × V)) (e : V × V) (he : e ∈ es) :
    (scanCaps φ es).1 ≤ (φ.residualCapacity e.1 e.2 : WithTop ℝ) := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih he)

theorem le_scanCaps (φ : Flow V G) (es : List (V × V)) (x : WithTop ℝ)
    (h : ∀ e ∈ es, x ≤ (φ.residualCapacity e.1 e.2 : WithTop ℝ)) :
    x ≤ (scanCaps φ es).1 := by
  induction es with
  | nil => exact le_top
  | cons e es ih =>
    exact le_min (h e (by simp)) (ih (fun f hf => h f (by simp [hf])))

theorem scanCaps_eq_bottleneck (φ : Flow V G) (p : Flow.AugmentingPath φ) :
    (scanCaps φ p.edges).1 = (p.bottleneck : WithTop ℝ) := by
  apply le_antisymm
  · have hm : p.bottleneck ∈ p.edges.toFinset.image
        (fun e => φ.residualCapacity e.1 e.2) := by
      unfold Flow.AugmentingPath.bottleneck
      exact Finset.min'_mem _ _
    obtain ⟨e,he,heq⟩ := Finset.mem_image.mp hm
    rw [← heq]
    exact scanCaps_le φ p.edges e (List.mem_toFinset.mp he)
  · apply le_scanCaps
    intro e he
    exact_mod_cast p.bottleneck_le_residualCapacity he

structure MapRun (V : Type*) where
  cells : (V × V) → ℝ
  work : Nat

def bump (old : MapRun V) (e : V × V) (delta : ℝ) : MapRun V :=
  ⟨Function.update old.cells e (old.cells e + delta),old.work+2⟩

def pushPair (f : (V × V) → ℝ) (delta : ℝ) (e : V × V) : MapRun V :=
  bump (bump ⟨f,0⟩ e delta) e.swap (-delta)

omit [Fintype V] in
theorem bump_apply (old : MapRun V) (e x : V × V) (delta : ℝ) :
    (bump old e delta).cells x = old.cells x + if x=e then delta else 0 := by
  by_cases h : x=e <;> simp [bump, Function.update, h]

omit [Fintype V] in
theorem pushPair_apply (f : (V × V) → ℝ) (delta : ℝ) (a b u v : V) :
    (pushPair f delta (a,b)).cells (u,v) = f (u,v) + Flow.edgeDelta delta a b u v := by
  simp only [pushPair, bump_apply, Prod.swap_prod_mk, Prod.mk.injEq, Flow.edgeDelta]
  split_ifs <;> ring

def updateAll (f : (V × V) → ℝ) (delta : ℝ) : List (V × V) → MapRun V
  | [] => ⟨f,0⟩
  | e :: es =>
    let first := pushPair f delta e
    let rest := updateAll first.cells delta es
    ⟨rest.cells,first.work+rest.work⟩

omit [Fintype V] in
@[simp] theorem updateAll_work (f : (V × V) → ℝ) (delta : ℝ) (es : List (V × V)) :
    (updateAll f delta es).work = 4*es.length := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih => simp [updateAll, pushPair, bump, ih, Nat.mul_add, Nat.add_comm]

omit [Fintype V] in
theorem updateAll_path (f : (V × V) → ℝ) (delta : ℝ) (vs : List V) (u v : V) :
    (updateAll f delta vs.consecutivePairs).cells (u,v) = f (u,v) + Flow.pathDelta delta vs u v := by
  induction vs generalizing f with
  | nil => simp [List.consecutivePairs, updateAll, Flow.pathDelta]
  | cons a vs ih =>
    cases vs with
    | nil => simp [List.consecutivePairs, updateAll, Flow.pathDelta]
    | cons b vs =>
      have he : (a :: b :: vs).consecutivePairs = (a,b) :: (b :: vs).consecutivePairs := rfl
      rw [he]
      simp only [updateAll, ih, pushPair_apply, Flow.pathDelta]
      ring

structure FlowRun (G : FlowNetwork V) where
  flow : Flow V G
  work : Nat

private theorem flow_ext {φ ψ : Flow V G} (h : φ.f = ψ.f) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- All executable value fields come from the counted scans and local dictionary writes. -/
def augmentWithCost (φ : Flow V G) (p : Flow.AugmentingPath φ) : FlowRun G :=
  let edges := edgesWithCost p.vertices
  let bottle := scanCaps φ edges.1
  let delta := bottle.1.untopD 0
  let updated := updateAll (fun e => φ.f e.1 e.2) delta edges.1
  have he : edges.1 = p.edges := (edgesWithCost_spec p.vertices).1
  have hd : delta = p.bottleneck := by
    dsimp [delta,bottle]
    rw [he,scanCaps_eq_bottleneck]
    rfl
  have hf : ∀ u v, updated.cells (u,v) = (φ.augment p).f u v := by
    intro u v
    dsimp [updated]
    rw [he,hd]
    exact updateAll_path _ _ p.vertices u v
  let result : Flow V G :=
    { f := fun u v => updated.cells (u,v)
      hcapacity := by intro u v; rw [hf]; exact (φ.augment p).hcapacity u v
      hskew_symm := by intro u v; rw [hf,hf]; exact (φ.augment p).hskew_symm u v
      hconservation := by intro u hu ht; simp only [hf]; exact (φ.augment p).hconservation u hu ht }
  ⟨result, edges.2+bottle.2+updated.work+1⟩

theorem augmentWithCost_refines (φ : Flow V G) (p : Flow.AugmentingPath φ) :
    (augmentWithCost φ p).flow = φ.augment p := by
  apply flow_ext
  funext u v
  simp only [augmentWithCost]
  rw [(edgesWithCost_spec p.vertices).1]
  change (updateAll (fun e => φ.f e.1 e.2) ((scanCaps φ p.edges).1.untopD 0) p.edges).cells (u,v) = _
  rw [scanCaps_eq_bottleneck]
  exact updateAll_path _ _ p.vertices u v

theorem augmentWithCost_work (φ : Flow V G) (p : Flow.AugmentingPath φ) :
    (augmentWithCost φ p).work = 9*p.edges.length+1 := by
  simp only [augmentWithCost, (edgesWithCost_spec p.vertices).1,
    (edgesWithCost_spec p.vertices).2, scanCaps_work,updateAll_work,Flow.ResidualPath.edges_length]
  have hlen : p.vertices.consecutivePairs.length = p.vertices.length-1 := p.edges_length
  omega

theorem augmentWithCost_work_le (φ : Flow V G) (p : ShortestAugmentingPath φ) :
    (augmentWithCost φ p.path).work ≤ 9*(support G).card+1 := by
  rw [augmentWithCost_work]
  have h := shortest_length_support φ p
  omega

end CLRS.Chapter26.SparseEK
