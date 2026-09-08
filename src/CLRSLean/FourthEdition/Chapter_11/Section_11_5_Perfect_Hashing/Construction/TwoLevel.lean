import CLRSLean.FourthEdition.Chapter_11.Section_11_5_Perfect_Hashing.Construction.Secondary
import CLRSLean.FourthEdition.Chapter_08.Section_08_4_Bucket_Sort

/-!
# Measured assembly of all secondary tables

The constructor actually distributes original {lit}`Fin n` payloads into primary
buckets, caches bucket sizes, and executes and retains every secondary builder.
The measured indexed-operation work has conditional expectation at most nine
times {lit}`constructionCost` and unconditional expectation below {lit}`45 * n`.

Secondary tables hash and store local bucket indices. Original payload buckets
remain in the result; converting an original query key to its local index is a
separate representation boundary. This does not claim constant-time hashing on
an arbitrary original key universe or machine runtime for persistent arrays.
-/

namespace CLRS.Chapter11.PerfectConstruction
open CLRS.Probability

/-- Uniform dependent-product sampling has the expected one-coordinate marginal. -/
theorem expect_pi_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ω : ι → Type) [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    [∀ i, Nonempty (Ω i)] (j : ι) (X : Ω j → ℝ) :
    fintypeExpect (fun w : (i : ι) → Ω i => X (w j)) = fintypeExpect X := by
  classical
  calc
    fintypeExpect (fun w : (i : ι) → Ω i => X (w j)) =
        fintypeExpect (fun p : Ω j × ((i : {i : ι // i ≠ j}) → Ω i.val) => X p.1) :=
      fintypeExpect_equiv (Equiv.piSplitAt j Ω) (fun p => X p.1)
    _ = _ := fintypeExpect_fst Fintype.card_ne_zero X

structure Assembly {m : Nat} (sizes : Fin m → Nat) where
  buckets : Array (Σ j : Fin m, Build (sizes j))
  work : Nat

/-- Execute every bucket constructor, storing its returned table in the output
array. Each push of a completed bucket record contributes one more operation. -/
def assemble {m t : Nat} (sizes : Fin m → Nat)
    (A : (j : Fin m) → Fin t → Hash (sizes j)) :
    List (Fin m) → Array (Σ j : Fin m, Build (sizes j)) → Assembly sizes
  | [], out => ⟨out, 0⟩
  | j :: js, out =>
      let built := buildTrace (A j)
      let rest := assemble sizes A js (out.push ⟨j, built⟩)
      ⟨rest.buckets, built.work + 1 + rest.work⟩

theorem assemble_result {m t : Nat} (sizes : Fin m → Nat)
    (A : (j : Fin m) → Fin t → Hash (sizes j))
    (js : List (Fin m)) (out : Array (Σ j : Fin m, Build (sizes j))) :
    (assemble sizes A js out).buckets.toList =
      out.toList ++ js.map (fun j => ⟨j, buildTrace (A j)⟩) := by
  induction js generalizing out with
  | nil => simp [assemble]
  | cons j js ih => simp [assemble, ih, List.append_assoc]

theorem assemble_work {m t : Nat} (sizes : Fin m → Nat)
    (A : (j : Fin m) → Fin t → Hash (sizes j))
    (js : List (Fin m)) (out : Array (Σ j : Fin m, Build (sizes j))) :
    (assemble sizes A js out).work = js.length + (js.map (fun j => (buildTrace (A j)).work)).sum := by
  induction js generalizing out with
  | nil => simp [assemble]
  | cons j js ih => simp [assemble, ih]; omega

theorem assemble_success {m t : Nat} (sizes : Fin m → Nat)
    (A : (j : Fin m) → Fin t → Hash (sizes j)) :
    ∀ entry ∈ (assemble sizes A (List.finRange m) #[]).buckets.toList,
      entry.2.selected.success = true := by
  rw [assemble_result]
  simp only [List.nil_append, List.mem_map]
  rintro entry ⟨j, hj, rfl⟩
  simpa only [buildTrace_eq] using build_success _

/-- Expected work of the actual assembly over independent finite per-bucket
trace spaces; no assumption on empty/singleton bucket sizes is needed. -/
theorem expected_assemble_work_le {m : Nat} (sizes : Fin m → Nat) (t : Nat) :
    fintypeExpect (fun A : (j : Fin m) → Fin t → Hash (sizes j) =>
      ((assemble sizes A (List.finRange m) #[]).work : ℝ)) ≤
      (m : ℝ) + 12 * ∑ j : Fin m, (sizes j : ℝ) ^ 2 := by
  classical
  haveI (j : Fin m) : Nonempty (Fin t → Hash (sizes j)) := ⟨fun _ => fallback (sizes j)⟩
  have hex : (fun A : (j : Fin m) → Fin t → Hash (sizes j) =>
      ((assemble sizes A (List.finRange m) #[]).work : ℝ)) =
      (fun A => (m : ℝ) + ∑ j : Fin m, ((buildTrace (A j)).work : ℝ)) := by
    funext A
    rw [assemble_work]
    simp [← List.ofFn_id, List.map_ofFn, List.sum_ofFn]
  rw [hex, fintypeExpect_add, fintypeExpect_const Fintype.card_ne_zero,
    fintypeExpect_sum]
  have hmarginal (j : Fin m) :
      fintypeExpect (fun A : (j : Fin m) → Fin t → Hash (sizes j) =>
        ((buildTrace (A j)).work : ℝ)) ≤ 12 * (sizes j : ℝ) ^ 2 := by
    rw [expect_pi_apply (fun j : Fin m => Fin t → Hash (sizes j)) j
      (fun B : Fin t → Hash (sizes j) => ((buildTrace B).work : ℝ))]
    exact expected_buildTrace_work_le_all (sizes j) t
  calc
    (m : ℝ) + ∑ j : Fin m,
        fintypeExpect (fun A : (j : Fin m) → Fin t → Hash (sizes j) =>
          ((buildTrace (A j)).work : ℝ)) ≤
        (m : ℝ) + ∑ j : Fin m, 12 * (sizes j : ℝ) ^ 2 := by
      gcongr with j
      exact hmarginal j
    _ = _ := by rw [Finset.mul_sum]


/-- Count a bucket's length by traversing its elements once. -/
def measureLength : List α → Nat × Nat
  | [] => (0, 0)
  | _ :: xs => let rest := measureLength xs; (rest.1 + 1, rest.2 + 1)

@[simp] theorem measureLength_result (xs : List α) : (measureLength xs).1 = xs.length := by
  induction xs <;> simp_all [measureLength]

@[simp] theorem measureLength_work (xs : List α) : (measureLength xs).2 = xs.length := by
  induction xs <;> simp_all [measureLength]

/-- Cache bucket cardinalities once, counting both visits and cache writes. -/
def measureBuckets : List (List α) → Array Nat → Array Nat × Nat
  | [], out => (out, 0)
  | b :: bs, out =>
      let measured := measureLength b
      let rest := measureBuckets bs (out.push measured.1)
      (rest.1, measured.2 + 1 + rest.2)

theorem measureBuckets_result (bs : List (List α)) (out : Array Nat) :
    (measureBuckets bs out).1.toList = out.toList ++ bs.map List.length := by
  induction bs generalizing out with
  | nil => simp [measureBuckets]
  | cons b bs ih => simp [measureBuckets, ih, List.append_assoc]

theorem measureBuckets_work (bs : List (List α)) (out : Array Nat) :
    (measureBuckets bs out).2 = bs.length + bs.flatten.length := by
  induction bs generalizing out with
  | nil => simp [measureBuckets]
  | cons b bs ih => simp [measureBuckets, ih]; omega

structure Primary (n : Nat) where
  buckets : Array (List (Fin n))
  sizes : Array Nat
  work : Nat

/-- One primary distribution and one bucket-cardinality traversal. Subsequent
secondary attempts read cached sizes instead of recomputing the partition. -/
def preparePrimary {n : Nat} (a : Fin n → Fin n) : Primary n :=
  let initial := Chapter08.CountingExecution.initializeBuckets (α := Fin n) n
  let distributed := Chapter08.CountingExecution.distribute
    (fun i => (a i).val) (List.finRange n) initial.1
  let measured := measureBuckets distributed.buckets.toList #[]
  ⟨distributed.buckets, measured.1,
    initial.2 + 2 * distributed.inputs + 3 * distributed.updates + measured.2⟩

@[simp] theorem preparePrimary_bucket_size {n : Nat} (a : Fin n → Fin n) :
    (preparePrimary a).buckets.size = n := by
  simp [preparePrimary]

theorem preparePrimary_buckets {n : Nat} (a : Fin n → Fin n) :
    (preparePrimary a).buckets.toList =
      (List.range n).map (Chapter08.bucket (fun i => (a i).val) (List.finRange n)) := by
  simp [preparePrimary, Chapter08.CountingExecution.distribute_toList]

theorem preparePrimary_sizes {n : Nat} (a : Fin n → Fin n) :
    (preparePrimary a).sizes.toList =
      (preparePrimary a).buckets.toList.map List.length := by
  simp [preparePrimary, measureBuckets_result]

@[simp] theorem preparePrimary_sizes_size {n : Nat} (a : Fin n → Fin n) :
    (preparePrimary a).sizes.size = n := by
  rw [← Array.length_toList, preparePrimary_sizes]
  simp

theorem preparePrimary_total_length {n : Nat} (a : Fin n → Fin n) :
    (preparePrimary a).buckets.toList.flatten.length = n := by
  rw [preparePrimary_buckets]
  cases n with
  | zero => simp
  | succ n =>
      change (Chapter08.countingSortBy n (fun i => (a i).val) (List.finRange (n + 1))).length = n + 1
      have hp := Chapter08.countingSortBy_perm n (fun i => (a i).val) (List.finRange (n + 1))
        (by intro i hi; change (a i).val ≤ n; have h := (a i).isLt; omega)
      simpa using hp.length_eq

theorem preparePrimary_work {n : Nat} (a : Fin n → Fin n) :
    (preparePrimary a).work = 8 * n := by
  have hu : (Chapter08.CountingExecution.distribute
      (fun i : Fin n => (a i).val) (List.finRange n) (Array.replicate n [])).updates = n := by
    simpa using Chapter08.CountingExecution.distribute_updates_eq
      (fun i : Fin n => (a i).val) (List.finRange n) (Array.replicate n [])
      (by intro i hi; simp)
  have hl := preparePrimary_total_length a
  unfold preparePrimary at hl ⊢
  simp only [Chapter08.CountingExecution.initializeBuckets_visits,
    Chapter08.CountingExecution.distribute_inputs, hu, List.length_finRange,
    measureBuckets_work, Array.length_toList, Chapter08.CountingExecution.distribute_size,
    Chapter08.CountingExecution.initializeBuckets_array, Array.size_replicate] at hl ⊢
  rw [hl]
  omega

/-- A stored cached cardinality, not a repeated list-length computation. -/
def bucketCard {n : Nat} (a : Fin n → Fin n) (j : Fin n) : Nat :=
  (preparePrimary a).sizes[j.val]'(by simp)

theorem bucketCard_eq {n : Nat} (a : Fin n → Fin n) (j : Fin n) :
    bucketCard a j = (Chapter08.bucket (fun i => (a i).val) (List.finRange n) j.val).length := by
  unfold bucketCard
  simp only [← Array.getElem_toList, preparePrimary_sizes, preparePrimary_buckets,
    List.getElem_map, List.getElem_range]

theorem bucketCard_cast {n : Nat} (a : Fin n → Fin n) (j : Fin n) :
    (bucketCard a j : ℝ) = bucketSize a j := by
  rw [bucketCard_eq, Chapter08.bucket_length_eq_card]
  exact (Chapter08.bucketOccupancy_eq_card a j).symm

theorem bucketCard_sq_sum {n : Nat} (a : Fin n → Fin n) :
    (∑ j : Fin n, (bucketCard a j : ℝ) ^ 2) = totalSecondarySpace a := by
  unfold totalSecondarySpace
  exact Finset.sum_congr rfl (fun j _ => by rw [bucketCard_cast])

structure TwoLevel {n : Nat} (a : Fin n → Fin n) where
  primary : Primary n
  secondary : Assembly (bucketCard a)
  work : Nat

/-- Construct every actual secondary array from finite supplied trial traces,
retaining the primary payload buckets and all completed secondary arrays. -/
def buildTwoLevel {n t : Nat} (a : Fin n → Fin n)
    (A : (j : Fin n) → Fin t → Hash (bucketCard a j)) : TwoLevel a :=
  let primary := preparePrimary a
  let secondary := assemble (fun j => primary.sizes[j.val]'(by simp [primary])) A (List.finRange n) #[]
  ⟨primary, secondary, primary.work + secondary.work⟩

/-- All secondary tables returned by the complete constructor succeeded. -/
theorem buildTwoLevel_success {n t : Nat} (a : Fin n → Fin n)
    (A : (j : Fin n) → Fin t → Hash (bucketCard a j)) :
    ∀ entry ∈ (buildTwoLevel a A).secondary.buckets.toList,
      entry.2.selected.success = true :=
  assemble_success (bucketCard a) A

/-- Conditional expected measured work is bounded by the pre-existing analytic
budget up to an explicit operation-count constant. -/
theorem expected_buildTwoLevel_work_le_budget {n : Nat} (a : Fin n → Fin n) (t : Nat) :
    fintypeExpect (fun A : (j : Fin n) → Fin t → Hash (bucketCard a j) =>
      ((buildTwoLevel a A).work : ℝ)) ≤ 9 * constructionCost a := by
  classical
  haveI (j : Fin n) : Nonempty (Fin t → Hash (bucketCard a j)) :=
    ⟨fun _ => fallback (bucketCard a j)⟩
  have he := expected_assemble_work_le (bucketCard a) t
  rw [bucketCard_sq_sum] at he
  have hex : (fun A : (j : Fin n) → Fin t → Hash (bucketCard a j) =>
      ((buildTwoLevel a A).work : ℝ)) =
      (fun A => (8 * n : ℝ) + ((assemble (bucketCard a) A (List.finRange n) #[]).work : ℝ)) := by
    funext A
    change (((preparePrimary a).work + (assemble (bucketCard a) A (List.finRange n) #[]).work : Nat) : ℝ) = _
    rw [preparePrimary_work]
    push_cast
    rfl
  rw [hex, fintypeExpect_add, fintypeExpect_const Fintype.card_ne_zero]
  have hs : 0 ≤ totalSecondarySpace a := by
    unfold totalSecondarySpace
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  unfold constructionCost
  nlinarith

/-- Average actual finite-with-fallback construction work is linear under the
primary SUHA assignment and the conditional independent secondary trace spaces. -/
theorem expected_buildTwoLevel_work_lt {n : Nat} (hn : 0 < n) (t : Nat) :
    fintypeExpect (fun a : Fin n → Fin n =>
      fintypeExpect (fun A : (j : Fin n) → Fin t → Hash (bucketCard a j) =>
        ((buildTwoLevel a A).work : ℝ))) < 45 * (n : ℝ) := by
  classical
  calc
    fintypeExpect (fun a : Fin n → Fin n =>
        fintypeExpect (fun A : (j : Fin n) → Fin t → Hash (bucketCard a j) =>
          ((buildTwoLevel a A).work : ℝ))) ≤
        fintypeExpect (fun a : Fin n → Fin n => 9 * constructionCost a) := by
      apply fintypeExpect_mono
      intro a
      exact expected_buildTwoLevel_work_le_budget a t
    _ = 9 * fintypeExpect (fun a : Fin n → Fin n => constructionCost a) :=
      fintypeExpect_const_mul 9 _
    _ < 9 * (5 * (n : ℝ)) :=
      mul_lt_mul_of_pos_left (perfectHash_expected_construction_time_le_const_n hn) (by norm_num)
    _ = _ := by ring


/-- Each returned secondary array stores every local key index at the slot
selected by the hash returned by that same execution. -/
theorem buildTwoLevel_stores {n t : Nat} (a : Fin n → Fin n)
    (A : (j : Fin n) → Fin t → Hash (bucketCard a j)) :
    ∀ entry ∈ (buildTwoLevel a A).secondary.buckets.toList,
      ∀ i : Fin (bucketCard a entry.1),
        entry.2.selected.slots[(entry.2.selected.hash i).val]?.join = some i := by
  change ∀ entry ∈ (assemble (bucketCard a) A (List.finRange n) #[]).buckets.toList, _
  rw [assemble_result]
  simp only [List.nil_append, List.mem_map]
  rintro entry ⟨j, hj, rfl⟩ i
  simp only [buildTrace_eq]
  change (build (List.ofFn (A j))).selected.slots[
    ((build (List.ofFn (A j))).selected.hash i).val]?.join = some i
  rw [build_selected_eq]
  simp only [attempt_hash]
  rw [Array.getElem?_eq_getElem (by simp), Option.join_some]
  exact attempt_stores _ (build_hash_injective (List.ofFn (A j))) i


theorem preparePrimary_bucket_length {n : Nat} (a : Fin n → Fin n) (j : Fin n) :
    ((preparePrimary a).buckets[j.val]'(by simp)).length = bucketCard a j := by
  rw [bucketCard_eq]
  simp only [← Array.getElem_toList, preparePrimary_buckets,
    List.getElem_map, List.getElem_range]

/-- Resolve a supplied local index through its selected secondary slot to the
original payload. Supplying the local index is an explicit interface requirement. -/
def recoverPayload {n : Nat} {a : Fin n → Fin n} (built : TwoLevel a)
    (entry : Σ j : Fin n, Build (bucketCard a j)) (i : Fin (bucketCard a entry.1)) :
    Option (Fin n) := do
  let localIndex ← entry.2.selected.slots[(entry.2.selected.hash i).val]?.join
  let payloads ← built.primary.buckets[entry.1.val]?
  payloads[localIndex.val]?

theorem buildTwoLevel_recovers {n t : Nat} (a : Fin n → Fin n)
    (A : (j : Fin n) → Fin t → Hash (bucketCard a j))
    (entry : Σ j : Fin n, Build (bucketCard a j))
    (he : entry ∈ (buildTwoLevel a A).secondary.buckets.toList)
    (i : Fin (bucketCard a entry.1)) :
    recoverPayload (buildTwoLevel a A) entry i =
      some (((preparePrimary a).buckets[entry.1.val]'(by simp))[i.val]'(by
        rw [preparePrimary_bucket_length]; exact i.isLt)) := by
  unfold recoverPayload
  rw [buildTwoLevel_stores a A entry he i]
  change ((preparePrimary a).buckets[entry.1.val]?.bind fun xs => xs[i.val]?) = _
  rw [Array.getElem?_eq_getElem (by simp), Option.bind_some,
    List.getElem?_eq_getElem (by rw [preparePrimary_bucket_length]; exact i.isLt)]


theorem preparePrimary_covers {n : Nat} (a : Fin n → Fin n) (x : Fin n) :
    ∃ i : Fin (bucketCard a (a x)),
      ((preparePrimary a).buckets[(a x).val]'(by simp))[i.val]'(by
        rw [preparePrimary_bucket_length]; exact i.isLt) = x := by
  have hm : x ∈ (preparePrimary a).buckets[(a x).val]'(by simp) := by
    simp only [← Array.getElem_toList, preparePrimary_buckets,
      List.getElem_map, List.getElem_range]
    simp [CLRS.Chapter08.bucket]
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem hm
  exact ⟨⟨i, by rwa [preparePrimary_bucket_length] at hi⟩, hx⟩


/-- Every original stored payload can be recovered through its actual returned
secondary table, given its local index. This does not construct an inverse map
from arbitrary original query keys to local indices. -/
theorem buildTwoLevel_recovers_original {n t : Nat} (a : Fin n → Fin n)
    (A : (j : Fin n) → Fin t → Hash (bucketCard a j)) (x : Fin n) :
    ∃ i : Fin (bucketCard a (a x)),
      recoverPayload (buildTwoLevel a A) ⟨a x, buildTrace (A (a x))⟩ i = some x := by
  obtain ⟨i, hi⟩ := preparePrimary_covers a x
  refine ⟨i, ?_⟩
  rw [buildTwoLevel_recovers, hi]
  change (⟨a x, buildTrace (A (a x))⟩ : Σ j : Fin n, Build (bucketCard a j)) ∈
    (assemble (bucketCard a) A (List.finRange n) #[]).buckets.toList
  rw [assemble_result]
  simp only [List.nil_append, List.mem_map]
  exact ⟨a x, List.mem_finRange _, rfl⟩
end CLRS.Chapter11.PerfectConstruction
