import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

/-!
# CLRS Section 16.3 - Huffman codes

This section gives a self-contained Lean proof of the optimality of Huffman
codes.  It is isolated from the legacy {lit}`CfProofs.Greedy.Huffman.*` modules and
is arranged as a readable pipeline:

1. Trees, frequencies, forests, and the Huffman merge algorithm.
2. Local tree-editing lemmas for swaps, merges, and split leaves.
3. Preservation lemmas for {lit}`huffman` over a forest.
4. The exchange/split-leaf theorem.
5. The bundled-forest V2 optimality theorem and frequency-table interface.
-/

open List

namespace CLRS
namespace HuffmanV2

/-! ## Trees, forests, and the Huffman algorithm -/

inductive HuffTree : Type
  | htLeaf (symbol freq : ℕ) | htInner (left right : HuffTree)
  deriving Repr, DecidableEq
open HuffTree

def rootFreq : HuffTree → ℕ
  | htLeaf _ f => f | htInner l r => rootFreq l + rootFreq r
def alphabet : HuffTree → Finset ℕ
  | htLeaf s _ => {s} | htInner l r => alphabet l ∪ alphabet r
def consistent : HuffTree → Prop
  | htLeaf _ _ => True
  | htInner l r => consistent l ∧ consistent r ∧ Disjoint (alphabet l) (alphabet r)
def height : HuffTree → ℕ
  | htLeaf _ _ => 0 | htInner l r => max (height l) (height r) + 1
def depthOf (s : ℕ) : HuffTree → Option ℕ
  | htLeaf sym _ => if sym = s then some 0 else none
  | htInner l r =>
    match depthOf s l with
    | some d => some (d + 1)
    | none => match depthOf s r with | some d => some (d + 1) | none => none
def freqOf (s : ℕ) : HuffTree → ℕ
  | htLeaf sym f => if sym = s then f else 0
  | htInner l r => freqOf s l + freqOf s r
def cost : HuffTree → ℕ
  | htLeaf _ _ => 0 | htInner l r => cost l + cost r + rootFreq l + rootFreq r
def nodeCount : HuffTree → ℕ
  | htLeaf _ _ => 1
  | htInner l r => 1 + nodeCount l + nodeCount r

lemma height_eq_zero_iff (t : HuffTree) : height t = 0 ↔ ∃ s f, t = htLeaf s f := by
  constructor
  · intro h; cases t with
    | htLeaf s f => exact ⟨s, f, rfl⟩
    | htInner l r => simp [height] at h
  · rintro ⟨s, f, rfl⟩; rfl

lemma height_pos_of_distinct_mem (t : HuffTree) {a b : ℕ}
    (ha : a ∈ alphabet t) (hb : b ∈ alphabet t) (hne : a ≠ b) : height t ≥ 1 := by
  by_contra! h_lt
  have h_zero : height t = 0 := by omega
  rcases (height_eq_zero_iff t).mp h_zero with ⟨s, f, rfl⟩
  simp [alphabet] at ha hb
  exact hne (ha.trans hb.symm)

def sameFreqs (t u : HuffTree) : Prop := ∀ s, freqOf s t = freqOf s u
def optimum (t : HuffTree) : Prop :=
  consistent t ∧ (∀ s ∈ alphabet t, freqOf s t > 0) ∧ ∀ u, consistent u → sameFreqs t u → cost t ≤ cost u
def unite (t₁ t₂ : HuffTree) : HuffTree := htInner t₁ t₂
def insortTree (t : HuffTree) : List HuffTree → List HuffTree
  | [] => [t]
  | u :: us => if rootFreq t ≤ rootFreq u then t :: u :: us else u :: insortTree t us
def huffman : List HuffTree → HuffTree
  | [] => htLeaf 0 0 | [t] => t
  | t₁ :: t₂ :: rest => huffman (insortTree (unite t₁ t₂) rest)
termination_by forest => forest.length
decreasing_by
  simp_wf
  have hlen : (insortTree (unite t₁ t₂) rest).length = rest.length + 1 := by
    induction rest with
    | nil => simp [insortTree]
    | cons u us ih => simp [insortTree]; split <;> simp [ih, add_comm, add_left_comm]
  omega
def forest_consistent : List HuffTree → Prop
  | [] => True | [t] => consistent t
  | t :: ts => consistent t ∧ forest_consistent ts ∧ (∀ u ∈ ts, Disjoint (alphabet t) (alphabet u))
def forest_sorted : List HuffTree → Prop
  | [] => True | [_] => True
  | t₁ :: t₂ :: ts => rootFreq t₁ ≤ rootFreq t₂ ∧ forest_sorted (t₂ :: ts)
def replaceFreq (sym newFreq : ℕ) : HuffTree → HuffTree
  | htLeaf s f => if s = sym then htLeaf s newFreq else htLeaf s f
  | htInner l r => htInner (replaceFreq sym newFreq l) (replaceFreq sym newFreq r)
def swapFreqs (a c : ℕ) (t : HuffTree) : HuffTree :=
  replaceFreq c (freqOf a t) (replaceFreq a (freqOf c t) t)
def splitLeaf (t : HuffTree) (z a b fa fb : ℕ) : HuffTree :=
  match t with
  | htLeaf sym f => if sym = z then htInner (htLeaf a fa) (htLeaf b fb) else htLeaf sym f
  | htInner l r => htInner (splitLeaf l z a b fa fb) (splitLeaf r z a b fa fb)
def swapLeaves (a b : ℕ) : HuffTree → HuffTree
  | htLeaf s f => if s = a then htLeaf b f else if s = b then htLeaf a f else htLeaf s f
  | htInner l r => htInner (swapLeaves a b l) (swapLeaves a b r)
def mergePair (a b z fz : ℕ) : HuffTree → HuffTree
  | htInner (htLeaf x fx) (htLeaf y fy) =>
    if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then htLeaf z fz
    else htInner (htLeaf x fx) (htLeaf y fy)
  | htInner l r => htInner (mergePair a b z fz l) (mergePair a b z fz r)
  | t => t

lemma nodeCount_exchangeLeaf_eq (a x : ℕ) (t : HuffTree) :
    nodeCount (swapFreqs a x (swapLeaves a x t)) = nodeCount t := by
  have h_swap : ∀ a b t, nodeCount (swapLeaves a b t) = nodeCount t := by
    intro a b t
    induction t with
    | htLeaf s f => unfold swapLeaves; simp [nodeCount]; split_ifs <;> simp [nodeCount]
    | htInner l r ihl ihr => unfold swapLeaves; simp [nodeCount, ihl, ihr]
  have h_replace : ∀ sym f t, nodeCount (replaceFreq sym f t) = nodeCount t := by
    intro sym f t
    induction t with
    | htLeaf s f' => unfold replaceFreq; simp [nodeCount]; split_ifs <;> simp [nodeCount]
    | htInner l r ihl ihr => unfold replaceFreq; simp [nodeCount, ihl, ihr]
  dsimp [swapFreqs]
  rw [h_replace, h_replace, h_swap]

/-! ## Alphabet, frequency, and depth lemmas -/

theorem freqOf_eq_zero_of_not_mem (s : ℕ) (t : HuffTree) (h : s ∉ alphabet t) : freqOf s t = 0 := by
  induction t with
  | htLeaf sym f =>
    have hs : sym ≠ s := by intro heq; subst heq; exact h (by simp [alphabet])
    simp [freqOf, hs]
  | htInner l r ihl ihr =>
    have hl : s ∉ alphabet l := by intro hm; apply h; simp [alphabet, hm]
    have hr : s ∉ alphabet r := by intro hm; apply h; simp [alphabet, hm]
    simp [freqOf, ihl hl, ihr hr]

theorem mem_alphabet_of_freq_pos (s : ℕ) (t : HuffTree) (h : freqOf s t > 0) :
    s ∈ alphabet t := by
  contrapose! h
  simpa [freqOf_eq_zero_of_not_mem s t h]

theorem depthOf_none_of_not_mem (s : ℕ) (t : HuffTree) (h : s ∉ alphabet t) : depthOf s t = none := by
  induction t with
  | htLeaf sym f =>
    have hs : sym ≠ s := by intro heq; subst heq; exact h (by simp [alphabet])
    simp [depthOf, hs]
  | htInner l r ihl ihr =>
    have hl : s ∉ alphabet l := by intro hm; apply h; simp [alphabet, hm]
    have hr : s ∉ alphabet r := by intro hm; apply h; simp [alphabet, hm]
    simp [depthOf, ihl hl, ihr hr]

theorem depthOf_some_of_mem (s : ℕ) (t : HuffTree) (h : s ∈ alphabet t) : ∃ d, depthOf s t = some d := by
  induction t with
  | htLeaf sym f => simp [alphabet] at h; subst h; exact ⟨0, by simp [depthOf]⟩
  | htInner l r ihl ihr =>
    have h_union : s ∈ alphabet l ∪ alphabet r := by simpa [alphabet] using h
    rcases Finset.mem_union.1 h_union with (hl | hr)
    · rcases ihl hl with ⟨d, hd⟩; refine ⟨d + 1, ?_⟩; rw [depthOf]; simp [hd]
    · by_cases hl' : s ∈ alphabet l
      · rcases ihl hl' with ⟨d, hd⟩; refine ⟨d + 1, ?_⟩; rw [depthOf]; simp [hd]
      · have h_none_l : depthOf s l = none := depthOf_none_of_not_mem s l hl'
        rcases ihr hr with ⟨d, hd⟩
        refine ⟨d + 1, ?_⟩; rw [depthOf]; simp [h_none_l, hd]

theorem alphabet_replaceFreq (sym newFreq : ℕ) (t : HuffTree) :
    alphabet (replaceFreq sym newFreq t) = alphabet t := by
  induction t with
  | htLeaf s f => unfold replaceFreq; split <;> simp [alphabet]
  | htInner l r ihl ihr => simp [replaceFreq, alphabet, ihl, ihr]

theorem consistent_replaceFreq (sym newFreq : ℕ) (t : HuffTree) (h_cons : consistent t) :
    consistent (replaceFreq sym newFreq t) := by
  induction t with
  | htLeaf s f => unfold replaceFreq; split <;> simp [consistent]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rw [replaceFreq, consistent]
    refine ⟨ihl hcl, ihr hcr, ?_⟩
    rw [alphabet_replaceFreq sym newFreq l, alphabet_replaceFreq sym newFreq r]
    exact hd

theorem freqOf_replaceFreq_of_ne (sym newFreq other : ℕ) (t : HuffTree) (h_ne : other ≠ sym) :
    freqOf other (replaceFreq sym newFreq t) = freqOf other t := by
  induction t with
  | htLeaf s f =>
    by_cases h_eq : s = sym
    · subst h_eq; simp [replaceFreq, freqOf, Ne.symm h_ne]
    · simp [replaceFreq, freqOf, h_eq]
  | htInner l r ihl ihr => simp [replaceFreq, freqOf, ihl, ihr]

private lemma rootFreq_replaceFreq_id_of_not_mem (sym newFreq : ℕ) (t : HuffTree) (h : sym ∉ alphabet t) :
    rootFreq (replaceFreq sym newFreq t) = rootFreq t := by
  induction t with
  | htLeaf s f =>
    have hs : s ≠ sym := by intro heq; subst heq; exact h (by simp [alphabet])
    simp [replaceFreq, rootFreq, hs]
  | htInner l r ihl ihr =>
    have hl : sym ∉ alphabet l := by intro hm; apply h; simp [alphabet, hm]
    have hr : sym ∉ alphabet r := by intro hm; apply h; simp [alphabet, hm]
    simp [replaceFreq, rootFreq, ihl hl, ihr hr]

private lemma cost_replaceFreq_id_of_not_mem (sym newFreq : ℕ) (t : HuffTree) (h : sym ∉ alphabet t) :
    cost (replaceFreq sym newFreq t) = cost t := by
  induction t with
  | htLeaf s f =>
    have hs : s ≠ sym := by intro heq; subst heq; exact h (by simp [alphabet])
    simp [replaceFreq, cost, hs]
  | htInner l r ihl ihr =>
    have hl : sym ∉ alphabet l := by intro hm; apply h; simp [alphabet, hm]
    have hr : sym ∉ alphabet r := by intro hm; apply h; simp [alphabet, hm]
    have h_root_l : rootFreq (replaceFreq sym newFreq l) = rootFreq l :=
      rootFreq_replaceFreq_id_of_not_mem sym newFreq l hl
    have h_root_r : rootFreq (replaceFreq sym newFreq r) = rootFreq r :=
      rootFreq_replaceFreq_id_of_not_mem sym newFreq r hr
    simp [replaceFreq, cost, ihl hl, ihr hr, h_root_l, h_root_r]

theorem rootFreq_replaceFreq_eq_int (sym newFreq : ℕ) (t : HuffTree) (h_cons : consistent t)
    (h_sym_in : sym ∈ alphabet t) :
    (rootFreq (replaceFreq sym newFreq t) : ℤ) = (rootFreq t : ℤ) + ((newFreq : ℤ) - (freqOf sym t : ℤ)) := by
  induction t with
  | htLeaf s f => simp [alphabet] at h_sym_in; subst h_sym_in; simp [replaceFreq, rootFreq, freqOf]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    have h_union : sym ∈ alphabet l ∪ alphabet r := by simpa [alphabet] using h_sym_in
    rcases Finset.mem_union.1 h_union with (hl_in | hr_in)
    · have hr_not : sym ∉ alphabet r := Finset.disjoint_left.mp hd hl_in
      have h_freq_r : freqOf sym r = 0 := freqOf_eq_zero_of_not_mem sym r hr_not
      have h_root_r : rootFreq (replaceFreq sym newFreq r) = rootFreq r :=
        rootFreq_replaceFreq_id_of_not_mem sym newFreq r hr_not
      have h_ih := ihl hcl hl_in
      simp [replaceFreq, rootFreq, freqOf, h_freq_r, h_root_r, h_ih]; ring
    · have hl_not : sym ∉ alphabet l := Finset.disjoint_right.mp hd hr_in
      have h_freq_l : freqOf sym l = 0 := freqOf_eq_zero_of_not_mem sym l hl_not
      have h_root_l : rootFreq (replaceFreq sym newFreq l) = rootFreq l :=
        rootFreq_replaceFreq_id_of_not_mem sym newFreq l hl_not
      have h_ih := ihr hcr hr_in
      simp [replaceFreq, rootFreq, freqOf, h_freq_l, h_root_l, h_ih]; ring

theorem cost_replaceFreq_eq (sym newFreq : ℕ) (t : HuffTree) (h_cons : consistent t) :
    (cost (replaceFreq sym newFreq t) : ℤ) = (cost t : ℤ) +
    ((newFreq : ℤ) - (freqOf sym t : ℤ)) * ((depthOf sym t).getD 0 : ℤ) := by
  induction t with
  | htLeaf s f =>
    by_cases h_eq : s = sym
    · subst h_eq; simp [replaceFreq, cost, freqOf, depthOf]
    · simp [replaceFreq, cost, freqOf, depthOf, h_eq]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    by_cases h_sym_l : sym ∈ alphabet l
    · have h_sym_not_r : sym ∉ alphabet r := Finset.disjoint_left.mp hd h_sym_l
      have h_freq_r : freqOf sym r = 0 := freqOf_eq_zero_of_not_mem sym r h_sym_not_r
      have h_depth_r : depthOf sym r = none := depthOf_none_of_not_mem sym r h_sym_not_r
      rcases depthOf_some_of_mem sym l h_sym_l with ⟨dl, h_depth_l⟩
      have h_root_l := rootFreq_replaceFreq_eq_int sym newFreq l hcl h_sym_l
      have h_cost_r_id : cost (replaceFreq sym newFreq r) = cost r :=
        cost_replaceFreq_id_of_not_mem sym newFreq r h_sym_not_r
      have h_root_r_id : rootFreq (replaceFreq sym newFreq r) = rootFreq r :=
        rootFreq_replaceFreq_id_of_not_mem sym newFreq r h_sym_not_r
      have h_ih := ihl hcl
      simp [replaceFreq, cost, rootFreq, freqOf, depthOf,
        h_freq_r, h_depth_r, h_depth_l, h_cost_r_id, h_root_r_id, h_ih, h_root_l]; ring
    · by_cases h_sym_r : sym ∈ alphabet r
      · have h_sym_not_l : sym ∉ alphabet l := h_sym_l
        have h_freq_l : freqOf sym l = 0 := freqOf_eq_zero_of_not_mem sym l h_sym_not_l
        have h_depth_l : depthOf sym l = none := depthOf_none_of_not_mem sym l h_sym_not_l
        rcases depthOf_some_of_mem sym r h_sym_r with ⟨dr, h_depth_r⟩
        have h_root_r := rootFreq_replaceFreq_eq_int sym newFreq r hcr h_sym_r
        have h_cost_l_id : cost (replaceFreq sym newFreq l) = cost l :=
          cost_replaceFreq_id_of_not_mem sym newFreq l h_sym_not_l
        have h_root_l_id : rootFreq (replaceFreq sym newFreq l) = rootFreq l :=
          rootFreq_replaceFreq_id_of_not_mem sym newFreq l h_sym_not_l
        have h_ih := ihr hcr
        simp [replaceFreq, cost, rootFreq, freqOf, depthOf,
          h_freq_l, h_depth_l, h_depth_r, h_cost_l_id, h_root_l_id, h_ih, h_root_r]; ring
      · have h_freq_l : freqOf sym l = 0 := freqOf_eq_zero_of_not_mem sym l h_sym_l
        have h_freq_r : freqOf sym r = 0 := freqOf_eq_zero_of_not_mem sym r h_sym_r
        have h_depth_l : depthOf sym l = none := depthOf_none_of_not_mem sym l h_sym_l
        have h_depth_r : depthOf sym r = none := depthOf_none_of_not_mem sym r h_sym_r
        have h_cost_l : cost (replaceFreq sym newFreq l) = cost l :=
          cost_replaceFreq_id_of_not_mem sym newFreq l h_sym_l
        have h_cost_r : cost (replaceFreq sym newFreq r) = cost r :=
          cost_replaceFreq_id_of_not_mem sym newFreq r h_sym_r
        have h_root_l : rootFreq (replaceFreq sym newFreq l) = rootFreq l :=
          rootFreq_replaceFreq_id_of_not_mem sym newFreq l h_sym_l
        have h_root_r : rootFreq (replaceFreq sym newFreq r) = rootFreq r :=
          rootFreq_replaceFreq_id_of_not_mem sym newFreq r h_sym_r
        simp [replaceFreq, cost, rootFreq, freqOf, depthOf,
          h_freq_l, h_freq_r, h_depth_l, h_depth_r, h_cost_l, h_cost_r, h_root_l, h_root_r]

/-! ## splitLeaf infrastructure -/

lemma splitLeaf_eq_of_z_not_mem (t : HuffTree) (z a b fa fb : ℕ) (h : z ∉ alphabet t) :
    splitLeaf t z a b fa fb = t := by
  induction t with
  | htLeaf sym f =>
    have hs : sym ≠ z := by intro heq; subst heq; exact h (by simp [alphabet])
    simp [splitLeaf, hs]
  | htInner l r ihl ihr =>
    have hl : z ∉ alphabet l := by intro hm; apply h; simp [alphabet, hm]
    have hr : z ∉ alphabet r := by intro hm; apply h; simp [alphabet, hm]
    simp [splitLeaf, ihl hl, ihr hr]

theorem rootFreq_splitLeaf_eq (t : HuffTree) (z a b fa fb : ℕ) (h_cons : consistent t)
    (h_z_in : z ∈ alphabet t) (h_sum : freqOf z t = fa + fb) :
    rootFreq (splitLeaf t z a b fa fb) = rootFreq t := by
  induction t with
  | htLeaf sym f =>
    simp [alphabet] at h_z_in; subst h_z_in
    have hf : f = fa + fb := by simp [freqOf] at h_sum; omega
    simp [splitLeaf, rootFreq, hf]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    have h_union : z ∈ alphabet l ∪ alphabet r := by simpa [alphabet] using h_z_in
    rcases Finset.mem_union.1 h_union with (hl_in | hr_in)
    · have hr_not : z ∉ alphabet r := Finset.disjoint_left.mp hd hl_in
      have h_freq_r : freqOf z r = 0 := freqOf_eq_zero_of_not_mem z r hr_not
      have h_sum_l : freqOf z l = fa + fb := by
        simp [freqOf] at h_sum; rw [h_freq_r] at h_sum; omega
      have h_split_r : splitLeaf r z a b fa fb = r :=
        splitLeaf_eq_of_z_not_mem r z a b fa fb hr_not
      have h_ih := ihl hcl hl_in h_sum_l
      simp [splitLeaf, rootFreq, h_split_r, h_ih]
    · have hl_not : z ∉ alphabet l := Finset.disjoint_right.mp hd hr_in
      have h_freq_l : freqOf z l = 0 := freqOf_eq_zero_of_not_mem z l hl_not
      have h_sum_r : freqOf z r = fa + fb := by
        simp [freqOf] at h_sum; rw [h_freq_l] at h_sum; omega
      have h_split_l : splitLeaf l z a b fa fb = l :=
        splitLeaf_eq_of_z_not_mem l z a b fa fb hl_not
      have h_ih := ihr hcr hr_in h_sum_r
      simp [splitLeaf, rootFreq, h_split_l, h_ih]

theorem cost_splitLeaf_eq (t : HuffTree) (z a b fa fb : ℕ) (h_cons : consistent t)
    (h_z_in : z ∈ alphabet t) (h_sum : freqOf z t = fa + fb) :
    cost (splitLeaf t z a b fa fb) = cost t + fa + fb := by
  have rootFreq_splitLeaf_eq' : ∀ (t' : HuffTree), consistent t' → z ∈ alphabet t' →
      freqOf z t' = fa + fb → rootFreq (splitLeaf t' z a b fa fb) = rootFreq t' := by
    intro t' hc hzin hs
    induction t' with
    | htLeaf sym f =>
      simp [alphabet] at hzin; subst hzin
      have hf : f = fa + fb := by simp [freqOf] at hs; omega
      simp [splitLeaf, rootFreq, hf]
    | htInner l r ihl ihr =>
      rcases hc with ⟨hcl, hcr, hd⟩
      have h_union : z ∈ alphabet l ∪ alphabet r := by simpa [alphabet] using hzin
      rcases Finset.mem_union.1 h_union with (hl_in | hr_in)
      · have hr_not : z ∉ alphabet r := Finset.disjoint_left.mp hd hl_in
        have h_freq_r : freqOf z r = 0 := freqOf_eq_zero_of_not_mem z r hr_not
        have h_sum_l : freqOf z l = fa + fb := by
          simp [freqOf] at hs; rw [h_freq_r] at hs; omega
        have h_split_r : splitLeaf r z a b fa fb = r :=
          splitLeaf_eq_of_z_not_mem r z a b fa fb hr_not
        have h_ih := ihl hcl hl_in h_sum_l
        simp [splitLeaf, rootFreq, h_split_r, h_ih]
      · have hl_not : z ∉ alphabet l := Finset.disjoint_right.mp hd hr_in
        have h_freq_l : freqOf z l = 0 := freqOf_eq_zero_of_not_mem z l hl_not
        have h_sum_r : freqOf z r = fa + fb := by
          simp [freqOf] at hs; rw [h_freq_l] at hs; omega
        have h_split_l : splitLeaf l z a b fa fb = l :=
          splitLeaf_eq_of_z_not_mem l z a b fa fb hl_not
        have h_ih := ihr hcr hr_in h_sum_r
        simp [splitLeaf, rootFreq, h_split_l, h_ih]
  induction t with
  | htLeaf sym f =>
    simp [alphabet] at h_z_in; subst h_z_in
    have hf : f = fa + fb := by simp [freqOf] at h_sum; omega
    simp [splitLeaf, cost, rootFreq, hf]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    have h_union : z ∈ alphabet l ∪ alphabet r := by simpa [alphabet] using h_z_in
    rcases Finset.mem_union.1 h_union with (hl_in | hr_in)
    · have hr_not : z ∉ alphabet r := Finset.disjoint_left.mp hd hl_in
      have h_freq_r : freqOf z r = 0 := freqOf_eq_zero_of_not_mem z r hr_not
      have h_sum_l : freqOf z l = fa + fb := by
        simp [freqOf] at h_sum; rw [h_freq_r] at h_sum; omega
      have h_split_r : splitLeaf r z a b fa fb = r :=
        splitLeaf_eq_of_z_not_mem r z a b fa fb hr_not
      have h_ih := ihl hcl hl_in h_sum_l
      have h_root_l : rootFreq (splitLeaf l z a b fa fb) = rootFreq l :=
        rootFreq_splitLeaf_eq l z a b fa fb hcl hl_in h_sum_l
      simp [splitLeaf, cost, h_split_r, h_ih, h_root_l]; omega
    · have hl_not : z ∉ alphabet l := Finset.disjoint_right.mp hd hr_in
      have h_freq_l : freqOf z l = 0 := freqOf_eq_zero_of_not_mem z l hl_not
      have h_sum_r : freqOf z r = fa + fb := by
        simp [freqOf] at h_sum; rw [h_freq_l] at h_sum; omega
      have h_split_l : splitLeaf l z a b fa fb = l :=
        splitLeaf_eq_of_z_not_mem l z a b fa fb hl_not
      have h_ih := ihr hcr hr_in h_sum_r
      have h_root_r : rootFreq (splitLeaf r z a b fa fb) = rootFreq r :=
        rootFreq_splitLeaf_eq r z a b fa fb hcr hr_in h_sum_r
      simp [splitLeaf, cost, h_split_l, h_ih, h_root_r]; omega


/-! ## Basic swap invariants -/

lemma cost_swapLeaves_eq (a b : ℕ) (t : HuffTree) : cost (swapLeaves a b t) = cost t := by
  have h_root : ∀ t, rootFreq (swapLeaves a b t) = rootFreq t := by
    intro t
    induction t with
    | htLeaf s f =>
      by_cases hsa : s = a
      · rw [hsa]; simp [swapLeaves, rootFreq]
      · by_cases hsb : s = b
        · rw [hsb]; by_cases hba : b = a
          · rw [hba]; simp [swapLeaves, rootFreq]
          · simp [swapLeaves, rootFreq, hba]
        · simp [swapLeaves, rootFreq, hsa, hsb]
    | htInner l r ihl ihr => simp [swapLeaves, rootFreq, ihl, ihr]
  induction t with
  | htLeaf s f =>
    by_cases hsa : s = a
    · rw [hsa]; simp [swapLeaves, cost]
    · by_cases hsb : s = b
      · rw [hsb]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, cost]
        · simp [swapLeaves, cost, hba]
      · simp [swapLeaves, cost, hsa, hsb]
  | htInner l r ihl ihr =>
    simp [swapLeaves, cost, ihl, ihr, h_root l, h_root r]


/-! ## Frequency and depth behavior under swaps -/

lemma freqOf_swapLeaves_of_not_is (a b s : ℕ) (t : HuffTree) (h_ne_a : s ≠ a) (h_ne_b : s ≠ b) :
    freqOf s (swapLeaves a b t) = freqOf s t := by
  induction t with
  | htLeaf sym f =>
    by_cases h_eq_a : sym = a
    · rw [h_eq_a]; simp [swapLeaves, freqOf, h_ne_a.symm, h_ne_b.symm]
    · by_cases h_eq_b : sym = b
      · rw [h_eq_b]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, freqOf, h_ne_a.symm, h_ne_b.symm]
        · simp [swapLeaves, freqOf, h_ne_a.symm, h_ne_b.symm, hba]
      · simp [swapLeaves, freqOf, h_eq_a, h_eq_b]
  | htInner l r ihl ihr => simp [swapLeaves, freqOf, ihl, ihr]

lemma freqOf_swapLeaves_at_a (a b : ℕ) (t : HuffTree) (h_ne : a ≠ b) :
    freqOf a (swapLeaves a b t) = freqOf b t := by
  induction t with
  | htLeaf sym f =>
    by_cases h_eq_a : sym = a
    · rw [h_eq_a]; simp [swapLeaves, freqOf, h_ne, h_ne.symm]
    · by_cases h_eq_b : sym = b
      · rw [h_eq_b]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, freqOf, h_ne.symm]
        · simp [swapLeaves, freqOf, h_ne.symm, hba]
      · simp [swapLeaves, freqOf, h_eq_a, h_eq_b]
  | htInner l r ihl ihr => simp [swapLeaves, freqOf, ihl, ihr]

lemma freqOf_swapLeaves_at_b (a b : ℕ) (t : HuffTree) (h_ne : a ≠ b) :
    freqOf b (swapLeaves a b t) = freqOf a t := by
  induction t with
  | htLeaf sym f =>
    by_cases h_eq_a : sym = a
    · rw [h_eq_a]; simp [swapLeaves, freqOf, h_ne, h_ne.symm]
    · by_cases h_eq_b : sym = b
      · rw [h_eq_b]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, freqOf, h_ne]
        · simp [swapLeaves, freqOf, hba, h_ne, h_ne.symm]
      · simp [swapLeaves, freqOf, h_eq_a, h_eq_b]
  | htInner l r ihl ihr => simp [swapLeaves, freqOf, ihl, ihr]

lemma depthOf_swapLeaves_of_not_is (a b s : ℕ) (t : HuffTree) (h_ne_a : s ≠ a) (h_ne_b : s ≠ b) :
    depthOf s (swapLeaves a b t) = depthOf s t := by
  induction t with
  | htLeaf sym f =>
    by_cases h_eq_a : sym = a
    · rw [h_eq_a]; simp [swapLeaves, depthOf, h_ne_a.symm, h_ne_b.symm]
    · by_cases h_eq_b : sym = b
      · rw [h_eq_b]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, depthOf, h_ne_a.symm, h_ne_b.symm]
        · simp [swapLeaves, depthOf, h_ne_a.symm, h_ne_b.symm, hba]
      · simp [swapLeaves, depthOf, h_eq_a, h_eq_b]
  | htInner l r ihl ihr => simp [swapLeaves, depthOf, ihl, ihr]

lemma depthOf_swapLeaves_at_a (a b : ℕ) (t : HuffTree) (h_ne : a ≠ b) :
    depthOf a (swapLeaves a b t) = depthOf b t := by
  induction t with
  | htLeaf sym f =>
    by_cases h_eq_a : sym = a
    · rw [h_eq_a]; simp [swapLeaves, depthOf, h_ne, h_ne.symm]
    · by_cases h_eq_b : sym = b
      · rw [h_eq_b]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, depthOf, h_ne.symm]
        · simp [swapLeaves, depthOf, h_ne.symm, hba]
      · simp [swapLeaves, depthOf, h_eq_a, h_eq_b]
  | htInner l r ihl ihr => simp [swapLeaves, depthOf, ihl, ihr]

lemma depthOf_swapLeaves_at_b (a b : ℕ) (t : HuffTree) (h_ne : a ≠ b) :
    depthOf b (swapLeaves a b t) = depthOf a t := by
  induction t with
  | htLeaf sym f =>
    by_cases h_eq_a : sym = a
    · rw [h_eq_a]; simp [swapLeaves, depthOf, h_ne, h_ne.symm]
    · by_cases h_eq_b : sym = b
      · rw [h_eq_b]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, depthOf, h_ne]
        · simp [swapLeaves, depthOf, hba, h_ne, h_ne.symm]
      · simp [swapLeaves, depthOf, h_eq_a, h_eq_b]
  | htInner l r ihl ihr => simp [swapLeaves, depthOf, ihl, ihr]

lemma depthOf_replaceFreq_eq (sym newFreq s : ℕ) (t : HuffTree) :
    depthOf s (replaceFreq sym newFreq t) = depthOf s t := by
  induction t with
  | htLeaf sym' f =>
    by_cases h : sym' = sym
    · subst h; simp [replaceFreq, depthOf]
    · simp [replaceFreq, depthOf, h]
  | htInner l r ihl ihr => simp [replaceFreq, depthOf, ihl, ihr]

lemma depthOf_swapFreqs_eq (a c s : ℕ) (t : HuffTree) :
    depthOf s (swapFreqs a c t) = depthOf s t := by
  rw [swapFreqs, depthOf_replaceFreq_eq, depthOf_replaceFreq_eq]

lemma depthOf_getD_exchange_of_ne (a x s : ℕ) (t : HuffTree)
    (hs_ne_a : s ≠ a) (hs_ne_x : s ≠ x) :
    (depthOf s (swapFreqs a x (swapLeaves a x t))).getD 0 = (depthOf s t).getD 0 := by
  rw [depthOf_swapFreqs_eq, depthOf_swapLeaves_of_not_is a x s t hs_ne_a hs_ne_x]


/-! ## Consistency and cost behavior under exchanges -/

def swapSym (a b s : ℕ) : ℕ := if s = a then b else if s = b then a else s

lemma swapSym_involutive (a b : ℕ) : Function.Involutive (swapSym a b) := by
  intro s
  dsimp [swapSym]
  by_cases hsa : s = a
  · subst s; simp
  · by_cases hsb : s = b
    · subst s
      by_cases hba : b = a
      · subst b; simp
      · have h1 : swapSym a b b = a := by dsimp [swapSym]; simp [hba]
        have h2 : swapSym a b a = b := by dsimp [swapSym]; simp
        calc
          swapSym a b (swapSym a b b) = swapSym a b a := by rw [h1]
          _ = b := h2
    · simp [hsa, hsb]

lemma alphabet_swapLeaves_eq_image (a b : ℕ) (t : HuffTree) :
    alphabet (swapLeaves a b t) = (alphabet t).image (swapSym a b) := by
  induction t with
  | htLeaf s f =>
    by_cases hsa : s = a
    · subst s; simp [swapLeaves, alphabet, swapSym]
    · by_cases hsb : s = b
      · subst s; simp [swapLeaves, alphabet, swapSym, hsa]
      · simp [swapLeaves, alphabet, swapSym, hsa, hsb]
  | htInner l r ihl ihr =>
    simp [swapLeaves, alphabet, ihl, ihr, Finset.image_union]

lemma consistent_swapLeaves (a b : ℕ) (t : HuffTree) (h_cons : consistent t) :
    consistent (swapLeaves a b t) := by
  induction t with
  | htLeaf s f =>
    by_cases hsa : s = a
    · rw [hsa]; simp [swapLeaves, consistent]
    · by_cases hsb : s = b
      · rw [hsb]; by_cases hba : b = a
        · rw [hba]; simp [swapLeaves, consistent]
        · simp [swapLeaves, consistent, hba]
      · simp [swapLeaves, consistent, hsa, hsb]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rw [swapLeaves, consistent]
    have h_l := ihl hcl; have h_r := ihr hcr
    have hd' : Disjoint (alphabet (swapLeaves a b l)) (alphabet (swapLeaves a b r)) :=
      by
        rw [alphabet_swapLeaves_eq_image a b l, alphabet_swapLeaves_eq_image a b r]
        exact (Finset.disjoint_image (swapSym_involutive a b).injective).mpr hd
    exact ⟨h_l, h_r, hd'⟩

lemma freqOf_replaceFreq_eq_of_mem (sym f : ℕ) (t : HuffTree) (h_sym : sym ∈ alphabet t) (h_cons : consistent t) :
    freqOf sym (replaceFreq sym f t) = f := by
  induction t with
  | htLeaf s g =>
    simp [alphabet] at h_sym; subst h_sym; simp [replaceFreq, freqOf]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    simp [replaceFreq, freqOf]
    simp [alphabet] at h_sym
    rcases h_sym with (hl | hr)
    · have hr_not : sym ∉ alphabet r := Finset.disjoint_left.mp hd hl
      have h_r : freqOf sym (replaceFreq sym f r) = 0 :=
        freqOf_eq_zero_of_not_mem sym (replaceFreq sym f r)
          (by rw [alphabet_replaceFreq sym f r]; exact hr_not)
      rw [ihl hl hcl, h_r, add_zero]
    · have hl_not : sym ∉ alphabet l := Finset.disjoint_right.mp hd hr
      have h_l : freqOf sym (replaceFreq sym f l) = 0 :=
        freqOf_eq_zero_of_not_mem sym (replaceFreq sym f l)
          (by rw [alphabet_replaceFreq sym f l]; exact hl_not)
      rw [ihr hr hcr, h_l, zero_add]

lemma freqOf_exchangeLeaf (t : HuffTree) (a x s : ℕ) (h_ne : a ≠ x)
    (ha_in : a ∈ alphabet t) (hx_in : x ∈ alphabet t) (h_cons : consistent t) :
    freqOf s (swapFreqs a x (swapLeaves a x t)) = freqOf s t := by
  have h_ne' : x ≠ a := Ne.symm h_ne
  let t' := swapLeaves a x t
  have h_cons_t' : consistent t' := consistent_swapLeaves a x t h_cons
  have ha_t' : freqOf a t' = freqOf x t := freqOf_swapLeaves_at_a a x t h_ne
  have hx_t' : freqOf x t' = freqOf a t := freqOf_swapLeaves_at_b a x t h_ne
  have ha_mem_t' : a ∈ alphabet t' := by
    rw [alphabet_swapLeaves_eq_image a x t, Finset.mem_image]
    exact ⟨x, hx_in, by dsimp [swapSym]; simp [h_ne']⟩
  have hx_mem_t' : x ∈ alphabet t' := by
    rw [alphabet_swapLeaves_eq_image a x t, Finset.mem_image]
    exact ⟨a, ha_in, by dsimp [swapSym]; simp⟩
  by_cases hs_a : s = a
  · rw [hs_a]
    dsimp [swapFreqs]
    rw [hx_t', ha_t']
    rw [freqOf_replaceFreq_of_ne x (freqOf x t) a (replaceFreq a (freqOf a t) t') h_ne]
    rw [freqOf_replaceFreq_eq_of_mem a (freqOf a t) t' ha_mem_t' h_cons_t']
  · by_cases hs_x : s = x
    · rw [hs_x]
      dsimp [swapFreqs]
      rw [hx_t', ha_t']
      have h_cons_t1 : consistent (replaceFreq a (freqOf a t) t') :=
        consistent_replaceFreq a (freqOf a t) t' h_cons_t'
      have hx_mem_t1 : x ∈ alphabet (replaceFreq a (freqOf a t) t') := by
        rw [alphabet_replaceFreq a (freqOf a t) t']; exact hx_mem_t'
      rw [freqOf_replaceFreq_eq_of_mem x (freqOf x t) (replaceFreq a (freqOf a t) t') hx_mem_t1 h_cons_t1]
    ·
      have hs_t' : freqOf s t' = freqOf s t :=
        freqOf_swapLeaves_of_not_is a x s t hs_a hs_x
      have hs_ne_a : s ≠ a := hs_a
      have hs_ne_x : s ≠ x := hs_x
      dsimp [swapFreqs]
      rw [hx_t', ha_t']
      rw [freqOf_replaceFreq_of_ne x (freqOf x t) s (replaceFreq a (freqOf a t) t') hs_ne_x]
      rw [freqOf_replaceFreq_of_ne a (freqOf a t) s t' hs_ne_a, hs_t']

lemma cost_exchangeLeaf_le (t : HuffTree) (a x : ℕ) (h_cons : consistent t)
    (ha_in : a ∈ alphabet t) (hx_in : x ∈ alphabet t) (h_ne : a ≠ x)
    (h_freq : freqOf a t ≤ freqOf x t)
    (h_depth : (depthOf a t).getD 0 ≤ (depthOf x t).getD 0) :
    (cost (swapFreqs a x (swapLeaves a x t)) : ℤ) ≤ (cost t : ℤ) := by
  have h_ne' : x ≠ a := Ne.symm h_ne
  let t1 := swapLeaves a x t
  have h_cost_t1 : cost t1 = cost t := cost_swapLeaves_eq a x t
  have h_cons_t1 : consistent t1 := consistent_swapLeaves a x t h_cons
  have h_fa_t1 : freqOf a t1 = freqOf x t := freqOf_swapLeaves_at_a a x t h_ne
  have h_fx_t1 : freqOf x t1 = freqOf a t := freqOf_swapLeaves_at_b a x t h_ne
  have h_da_val : (depthOf a t1).getD 0 = (depthOf x t).getD 0 := by
    have h := depthOf_swapLeaves_at_a a x t h_ne; simp [t1, h]
  have h_dx_val : (depthOf x t1).getD 0 = (depthOf a t).getD 0 := by
    have h := depthOf_swapLeaves_at_b a x t h_ne; simp [t1, h]
  let t2 := replaceFreq a (freqOf x t1) t1
  have h_cons_t2 : consistent t2 := consistent_replaceFreq a (freqOf x t1) t1 h_cons_t1
  have h_fx_t2 : freqOf x t2 = freqOf x t1 := by
    simp [t2, freqOf_replaceFreq_of_ne a (freqOf x t1) x t1 h_ne']
  have h_dx_t2_val : (depthOf x t2).getD 0 = (depthOf x t1).getD 0 := by
    simp [t2, depthOf_replaceFreq_eq a (freqOf x t1) x t1]
  calc
    (cost (swapFreqs a x (swapLeaves a x t)) : ℤ)
        = (cost (swapFreqs a x t1) : ℤ) := by simp [t1]
    _ = (cost (replaceFreq x (freqOf a t1) t2) : ℤ) := by simp [t2, swapFreqs]
    _ = (cost t2 : ℤ) + (((freqOf a t1 : ℤ) - (freqOf x t2 : ℤ)) * ((depthOf x t2).getD 0 : ℤ)) :=
      cost_replaceFreq_eq x (freqOf a t1) t2 h_cons_t2
    _ = (cost t2 : ℤ) + (((freqOf x t : ℤ) - (freqOf a t : ℤ)) * ((depthOf a t).getD 0 : ℤ)) := by
      simp [h_fa_t1, h_fx_t2, h_fx_t1, h_dx_t2_val, h_dx_val]
    _ = ((cost t : ℤ) + (((freqOf a t : ℤ) - (freqOf x t : ℤ)) * ((depthOf x t).getD 0 : ℤ))) +
        (((freqOf x t : ℤ) - (freqOf a t : ℤ)) * ((depthOf a t).getD 0 : ℤ)) := by
      have h_t2_eq_raw := cost_replaceFreq_eq a (freqOf x t1) t1 h_cons_t1
      have h_t2_eq : (cost t2 : ℤ) = (cost t1 : ℤ) + (((freqOf x t1 : ℤ) - (freqOf a t1 : ℤ)) * ((depthOf a t1).getD 0 : ℤ)) := by
        simpa [t2] using h_t2_eq_raw
      rw [h_t2_eq]
      simp [h_cost_t1, h_fx_t1, h_fa_t1, h_da_val]
    _ = (cost t : ℤ) + (((freqOf a t : ℤ) - (freqOf x t : ℤ)) * (((depthOf x t).getD 0 : ℤ) - ((depthOf a t).getD 0 : ℤ))) := by ring
    _ ≤ (cost t : ℤ) := by
      have h_fa_le_fx_int : (freqOf a t : ℤ) ≤ (freqOf x t : ℤ) := by exact_mod_cast h_freq
      have h_da_le_dx_int : ((depthOf a t).getD 0 : ℤ) ≤ ((depthOf x t).getD 0 : ℤ) := by exact_mod_cast h_depth
      nlinarith


/-! ## Merging sibling leaves -/

inductive areSiblings (a b : ℕ) : HuffTree → Prop
  | here (fa fb : ℕ) : areSiblings a b (htInner (htLeaf a fa) (htLeaf b fb))
  | here' (fa fb : ℕ) : areSiblings a b (htInner (htLeaf b fb) (htLeaf a fa))
  | inLeft (l r : HuffTree) : areSiblings a b l → areSiblings a b (htInner l r)
  | inRight (l r : HuffTree) : areSiblings a b r → areSiblings a b (htInner l r)

lemma mergePair_eq_self_of_not_mem (a b z fz : ℕ) (t : HuffTree)
    (ha : a ∉ alphabet t) (hb : b ∉ alphabet t) : mergePair a b z fz t = t := by
  induction t with
  | htLeaf s f => simp [mergePair]
  | htInner l r ihl ihr =>
    have ha_l : a ∉ alphabet l := by intro hm; apply ha; simp [alphabet, hm]
    have hb_l : b ∉ alphabet l := by intro hm; apply hb; simp [alphabet, hm]
    have ha_r : a ∉ alphabet r := by intro hm; apply ha; simp [alphabet, hm]
    have hb_r : b ∉ alphabet r := by intro hm; apply hb; simp [alphabet, hm]
    have hl := ihl ha_l hb_l
    have hr := ihr ha_r hb_r
    cases l with
    | htLeaf sl fl =>
      cases r with
      | htLeaf sr fr =>
        have h_not_pair : ¬ ((sl = a ∧ sr = b) ∨ (sl = b ∧ sr = a)) := by
          intro h; rcases h with (⟨hsl, hsr⟩ | ⟨hsl, hsr⟩)
          · subst hsl hsr; exact ha (by simp [alphabet])
          · subst hsl hsr; exact ha (by simp [alphabet])
        simp [mergePair, h_not_pair, hl, hr]
      | htInner _ _ => simp [mergePair, hl, hr]
    | htInner _ _ => simp [mergePair, hl, hr]

lemma nodeCount_mergePair_le (a b z fz : ℕ) (t : HuffTree) :
    nodeCount (mergePair a b z fz t) ≤ nodeCount t := by
  induction t with
  | htLeaf s f => simp [mergePair, nodeCount]
  | htInner l r ihl ihr =>
    cases l with
    | htLeaf x fx =>
      cases r with
      | htLeaf y fy =>
        simp [mergePair, nodeCount]
        by_cases hc : (x = a ∧ y = b) ∨ (x = b ∧ y = a)
        · simp [hc, nodeCount]
        · simp [hc, nodeCount]
      | htInner rl rr =>
        have hm : mergePair a b z fz (htInner (htLeaf x fx) (htInner rl rr)) =
          htInner (htLeaf x fx) (mergePair a b z fz (htInner rl rr)) := by simp [mergePair]
        rw [hm]; simp [nodeCount] at ihr ⊢
        omega
    | htInner ll lr =>
      cases r with
      | htLeaf y fy =>
        have hm : mergePair a b z fz (htInner (htInner ll lr) (htLeaf y fy)) =
          htInner (mergePair a b z fz (htInner ll lr)) (htLeaf y fy) := by simp [mergePair]
        rw [hm]; simp [nodeCount] at ihl ⊢
        omega
      | htInner rl rr =>
        have hm : mergePair a b z fz (htInner (htInner ll lr) (htInner rl rr)) =
          htInner (mergePair a b z fz (htInner ll lr)) (mergePair a b z fz (htInner rl rr)) := by simp [mergePair]
        rw [hm]; simp [nodeCount] at ihl ihr ⊢
        omega

lemma areSiblings_mem_alphabet {a b : ℕ} {t : HuffTree} (h_sib : areSiblings a b t) :
    a ∈ alphabet t ∧ b ∈ alphabet t := by
  induction h_sib with
  | here fa fb => simp [alphabet]
  | here' fa fb => simp [alphabet]
  | inLeft l r h ih =>
    rcases ih with ⟨ha, hb⟩
    exact ⟨Finset.mem_union_left _ ha, Finset.mem_union_left _ hb⟩
  | inRight l r h ih =>
    rcases ih with ⟨ha, hb⟩
    exact ⟨Finset.mem_union_right _ ha, Finset.mem_union_right _ hb⟩

lemma nodeCount_mergePair_lt_of_areSiblings (t : HuffTree) (a b z fz : ℕ)
    (h_sib : areSiblings a b t) (h_ne : a ≠ b) :
    nodeCount (mergePair a b z fz t) < nodeCount t := by
  induction h_sib with
  | here fa fb =>
    simp [mergePair, nodeCount]
  | here' fa fb =>
    simp [mergePair, nodeCount]
  | inLeft l r h_sib_l ih =>
    cases l with
    | htLeaf s f => exfalso; cases h_sib_l
    | htInner ll lr =>
      have h_l : nodeCount (mergePair a b z fz (htInner ll lr)) < nodeCount (htInner ll lr) := ih
      have h_r : nodeCount (mergePair a b z fz r) ≤ nodeCount r := nodeCount_mergePair_le a b z fz r
      simp [nodeCount] at h_l h_r ⊢
      have hm : mergePair a b z fz (htInner (htInner ll lr) r) =
        htInner (mergePair a b z fz (htInner ll lr)) (mergePair a b z fz r) := by simp [mergePair]
      rw [hm]; simp [nodeCount]
      omega
  | inRight l r h_sib_r ih =>
    cases r with
    | htLeaf s f => exfalso; cases h_sib_r
    | htInner rl rr =>
      have h_l : nodeCount (mergePair a b z fz l) ≤ nodeCount l := nodeCount_mergePair_le a b z fz l
      have h_r : nodeCount (mergePair a b z fz (htInner rl rr)) < nodeCount (htInner rl rr) := ih
      simp [nodeCount] at h_l h_r ⊢
      have hm : mergePair a b z fz (htInner l (htInner rl rr)) =
        htInner (mergePair a b z fz l) (mergePair a b z fz (htInner rl rr)) := by simp [mergePair]
      rw [hm]; simp [nodeCount]
      omega

lemma rootFreq_mergePair_of_areSiblings (t : HuffTree) (a b z fz : ℕ)
    (h_sib : areSiblings a b t) (h_cons : consistent t) (h_ne : a ≠ b) (h_fz : fz = freqOf a t + freqOf b t) :
    rootFreq (mergePair a b z fz t) = rootFreq t := by
  induction h_sib with
  | here fa fb =>
    simp [mergePair, rootFreq, freqOf, h_ne, h_ne.symm, h_fz]
  | here' fa fb =>
    simp [mergePair, rootFreq, freqOf, h_ne, h_ne.symm, h_fz]; omega
  | inLeft l r h_sib_l ih =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_l with ⟨ha_l, hb_l⟩
    have ha_r : a ∉ alphabet r := Finset.disjoint_left.mp hd ha_l
    have hb_r : b ∉ alphabet r := Finset.disjoint_left.mp hd hb_l
    have h_fz_l : fz = freqOf a l + freqOf b l := by
      rw [freqOf, freqOf, freqOf_eq_zero_of_not_mem a r ha_r, freqOf_eq_zero_of_not_mem b r hb_r] at h_fz
      simpa [add_comm, add_left_comm, add_assoc] using h_fz
    have h_merge_r : mergePair a b z fz r = r := mergePair_eq_self_of_not_mem a b z fz r ha_r hb_r
    have h_root_l : rootFreq (mergePair a b z fz l) = rootFreq l := ih hcl h_fz_l
    cases l with
    | htLeaf s f => exfalso; cases h_sib_l
    | htInner ll lr =>
      simp [mergePair, rootFreq, h_merge_r, h_root_l]
  | inRight l r h_sib_r ih =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_r with ⟨ha_r, hb_r⟩
    have ha_l : a ∉ alphabet l := Finset.disjoint_right.mp hd ha_r
    have hb_l : b ∉ alphabet l := Finset.disjoint_right.mp hd hb_r
    have h_fz_r : fz = freqOf a r + freqOf b r := by
      rw [freqOf, freqOf, freqOf_eq_zero_of_not_mem a l ha_l, freqOf_eq_zero_of_not_mem b l hb_l] at h_fz
      simpa [add_comm, add_left_comm, add_assoc] using h_fz
    have h_merge_l : mergePair a b z fz l = l := mergePair_eq_self_of_not_mem a b z fz l ha_l hb_l
    have h_root_r : rootFreq (mergePair a b z fz r) = rootFreq r := ih hcr h_fz_r
    cases r with
    | htLeaf s f => exfalso; cases h_sib_r
    | htInner rl rr =>
      simp [mergePair, rootFreq, h_merge_l, h_root_r]

lemma cost_mergePair_of_areSiblings (t : HuffTree) (a b z fa fb : ℕ)
    (h_sib : areSiblings a b t) (h_cons : consistent t) (h_ne : a ≠ b)
    (h_fa : freqOf a t = fa) (h_fb : freqOf b t = fb) (h_fz : fz = fa + fb) :
    (cost (mergePair a b z fz t) : ℤ) = (cost t : ℤ) - (fa : ℤ) - (fb : ℤ) := by
  revert h_cons h_fa h_fb h_fz
  induction h_sib with
  | here fa' fb' =>
    intro h_cons h_fa h_fb h_fz
    have h_fa_val : freqOf a (htInner (htLeaf a fa') (htLeaf b fb')) = fa' := by
      simp [freqOf, h_ne, h_ne.symm]
    have h_fb_val : freqOf b (htInner (htLeaf a fa') (htLeaf b fb')) = fb' := by
      simp [freqOf, h_ne, h_ne.symm]
    rw [h_fa_val] at h_fa; rw [h_fb_val] at h_fb; subst h_fa; subst h_fb
    have h_cost_merged : cost (mergePair a b z fz (htInner (htLeaf a fa') (htLeaf b fb'))) = 0 := by
      simp [mergePair, cost]
    have h_cost_t : cost (htInner (htLeaf a fa') (htLeaf b fb')) = fa' + fb' := by
      simp [cost, rootFreq]
    rw [h_cost_merged, h_cost_t]; push_cast; omega
  | here' fa' fb' =>
    intro h_cons h_fa h_fb h_fz
    have h_fa_val : freqOf a (htInner (htLeaf b fb') (htLeaf a fa')) = fa' := by
      simp [freqOf, h_ne, h_ne.symm]
    have h_fb_val : freqOf b (htInner (htLeaf b fb') (htLeaf a fa')) = fb' := by
      simp [freqOf, h_ne, h_ne.symm]
    rw [h_fa_val] at h_fa; rw [h_fb_val] at h_fb; subst h_fa; subst h_fb
    have h_cost_merged : cost (mergePair a b z fz (htInner (htLeaf b fb') (htLeaf a fa'))) = 0 := by
      simp [mergePair, cost]
    have h_cost_t : cost (htInner (htLeaf b fb') (htLeaf a fa')) = fa' + fb' := by
      simp [cost, rootFreq]; omega
    rw [h_cost_merged, h_cost_t]; push_cast; omega
  | inLeft l r h_sib_l ih =>
    intro h_cons h_fa h_fb h_fz
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_l with ⟨ha_l, hb_l⟩
    have ha_r : a ∉ alphabet r := Finset.disjoint_left.mp hd ha_l
    have hb_r : b ∉ alphabet r := Finset.disjoint_left.mp hd hb_l
    have h_freq_l_a : freqOf a l = fa := by
      rw [← h_fa, freqOf, freqOf_eq_zero_of_not_mem a r ha_r]; simp
    have h_freq_l_b : freqOf b l = fb := by
      rw [← h_fb, freqOf, freqOf_eq_zero_of_not_mem b r hb_r]; simp
    have h_root_l : rootFreq (mergePair a b z fz l) = rootFreq l :=
      rootFreq_mergePair_of_areSiblings l a b z fz h_sib_l hcl h_ne (by rw [h_freq_l_a, h_freq_l_b]; exact h_fz)
    have h_cost_l : (cost (mergePair a b z fz l) : ℤ) = (cost l : ℤ) - (fa : ℤ) - (fb : ℤ) :=
      ih hcl h_freq_l_a h_freq_l_b h_fz
    have h_cost_r : cost (mergePair a b z fz r) = cost r := by
      simp [mergePair_eq_self_of_not_mem a b z fz r ha_r hb_r]
    have h_root_r : rootFreq (mergePair a b z fz r) = rootFreq r := by
      simp [mergePair_eq_self_of_not_mem a b z fz r ha_r hb_r]
    cases l with
    | htLeaf s f => exfalso; cases h_sib_l
    | htInner ll lr =>
      simp [mergePair, cost, h_cost_l, h_cost_r, h_root_l, h_root_r]; ring
  | inRight l r h_sib_r ih =>
    intro h_cons h_fa h_fb h_fz
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_r with ⟨ha_r, hb_r⟩
    have ha_l : a ∉ alphabet l := Finset.disjoint_right.mp hd ha_r
    have hb_l : b ∉ alphabet l := Finset.disjoint_right.mp hd hb_r
    have h_freq_r_a : freqOf a r = fa := by
      rw [← h_fa, freqOf, freqOf_eq_zero_of_not_mem a l ha_l]; simp
    have h_freq_r_b : freqOf b r = fb := by
      rw [← h_fb, freqOf, freqOf_eq_zero_of_not_mem b l hb_l]; simp
    have h_root_r : rootFreq (mergePair a b z fz r) = rootFreq r :=
      rootFreq_mergePair_of_areSiblings r a b z fz h_sib_r hcr h_ne (by rw [h_freq_r_a, h_freq_r_b]; exact h_fz)
    have h_cost_r : (cost (mergePair a b z fz r) : ℤ) = (cost r : ℤ) - (fa : ℤ) - (fb : ℤ) :=
      ih hcr h_freq_r_a h_freq_r_b h_fz
    have h_cost_l : cost (mergePair a b z fz l) = cost l := by
      simp [mergePair_eq_self_of_not_mem a b z fz l ha_l hb_l]
    have h_root_l : rootFreq (mergePair a b z fz l) = rootFreq l := by
      simp [mergePair_eq_self_of_not_mem a b z fz l ha_l hb_l]
    cases r with
    | htLeaf s f => exfalso; cases h_sib_r
    | htInner rl rr =>
      simp [mergePair, cost, h_cost_l, h_cost_r, h_root_l, h_root_r]; ring

lemma alphabet_mergePair_subset (a b z fz : ℕ) (t : HuffTree) :
    alphabet (mergePair a b z fz t) ⊆ alphabet t ∪ {z} := by
  induction t with
  | htLeaf s f => simp [mergePair]
  | htInner l r ihl ihr =>
    intro x hx
    cases l with
    | htLeaf sl fl =>
      cases r with
      | htLeaf sr fr =>
        by_cases hpair : (sl = a ∧ sr = b) ∨ (sl = b ∧ sr = a)
        ·
          have h_merge_val : mergePair a b z fz (htInner (htLeaf sl fl) (htLeaf sr fr)) = htLeaf z fz := by
            simp [mergePair, hpair]
          have hx' : x ∈ alphabet (htLeaf z fz) := by rwa [h_merge_val] at hx
          rcases Finset.mem_singleton.mp hx' with rfl
          simp
        ·
          have h_merge_val : mergePair a b z fz (htInner (htLeaf sl fl) (htLeaf sr fr)) =
                             htInner (htLeaf sl fl) (htLeaf sr fr) := by
            simp [mergePair, hpair]
          have hx' : x ∈ alphabet (htInner (htLeaf sl fl) (htLeaf sr fr)) := by rwa [h_merge_val] at hx
          exact Finset.mem_union_left _ hx'
      | htInner rl rr =>
        simp only [mergePair, alphabet] at hx ⊢
        rcases Finset.mem_union.mp hx with (hx_l | hx_r)
        · apply Finset.mem_union_left; apply Finset.mem_union_left; exact hx_l
        · have h := ihr hx_r
          rcases Finset.mem_union.mp h with (h' | h')
          · apply Finset.mem_union_left; apply Finset.mem_union_right; exact h'
          · apply Finset.mem_union_right; exact h'
    | htInner ll lr =>
      cases r with
      | htLeaf sr fr =>
        simp only [mergePair, alphabet] at hx ⊢
        rcases Finset.mem_union.mp hx with (hx_l | hx_r)
        · have h := ihl hx_l
          rcases Finset.mem_union.mp h with (h' | h')
          · apply Finset.mem_union_left; apply Finset.mem_union_left; exact h'
          · apply Finset.mem_union_right; exact h'
        · apply Finset.mem_union_left; apply Finset.mem_union_right; exact hx_r
      | htInner rl rr =>
        simp only [mergePair, alphabet] at hx ⊢
        rcases Finset.mem_union.mp hx with (hx_l | hx_r)
        · have h := ihl hx_l
          rcases Finset.mem_union.mp h with (h' | h')
          · apply Finset.mem_union_left; apply Finset.mem_union_left; exact h'
          · apply Finset.mem_union_right; exact h'
        · have h := ihr hx_r
          rcases Finset.mem_union.mp h with (h' | h')
          · apply Finset.mem_union_left; apply Finset.mem_union_right; exact h'
          · apply Finset.mem_union_right; exact h'

lemma freqOf_mergePair_of_areSiblings (t : HuffTree) (a b z : ℕ)
    (h_sib : areSiblings a b t) (h_cons : consistent t) (hz_fresh : z ∉ alphabet t) (s : ℕ) :
    freqOf s (mergePair a b z (freqOf a t + freqOf b t) t) =
    if s = z then freqOf a t + freqOf b t
    else if s = a ∨ s = b then 0
    else freqOf s t := by
  cases h_sib with
  | here fa fb =>
    rcases h_cons with ⟨_, _, hd⟩
    have h_ne : a ≠ b := by
      intro h_eq
      subst h_eq
      simpa [alphabet, Finset.disjoint_iff_inter_eq_empty] using hd
    have hz_ne_a : z ≠ a := by intro heq; subst heq; apply hz_fresh; simp [alphabet]
    have hz_ne_b : z ≠ b := by intro heq; subst heq; apply hz_fresh; simp [alphabet]
    have h_freq_sum : freqOf a (htInner (htLeaf a fa) (htLeaf b fb)) +
                     freqOf b (htInner (htLeaf a fa) (htLeaf b fb)) = fa + fb := by
      simp [freqOf, h_ne, h_ne.symm]
    have h_merge_val : mergePair a b z (freqOf a (htInner (htLeaf a fa) (htLeaf b fb)) +
                                        freqOf b (htInner (htLeaf a fa) (htLeaf b fb)))
                                        (htInner (htLeaf a fa) (htLeaf b fb)) =
                       htLeaf z (fa + fb) := by
      rw [h_freq_sum]; simp [mergePair]
    rw [h_merge_val, freqOf, h_freq_sum]
    by_cases hsz : s = z
    · subst s; simp
    · rw [if_neg (Ne.symm hsz), if_neg hsz]
      by_cases hsa : s = a
      · subst s; simp
      · by_cases hsb : s = b
        · subst s; simp
        · have h_freq_s : freqOf s (htInner (htLeaf a fa) (htLeaf b fb)) = 0 := by
            simp [freqOf, hsa, hsb, Ne.symm hsa, Ne.symm hsb]
          simp [hsa, hsb, h_freq_s]
  | here' fb_a fa_a =>
    rcases h_cons with ⟨_, _, hd⟩
    have h_ne : a ≠ b := by
      intro h_eq
      subst h_eq
      simpa [alphabet, Finset.disjoint_iff_inter_eq_empty] using hd
    have hz_ne_a : z ≠ a := by intro heq; subst heq; apply hz_fresh; simp [alphabet]
    have hz_ne_b : z ≠ b := by intro heq; subst heq; apply hz_fresh; simp [alphabet]
    have h_freq_sum : freqOf a (htInner (htLeaf b fa_a) (htLeaf a fb_a)) +
                     freqOf b (htInner (htLeaf b fa_a) (htLeaf a fb_a)) = fa_a + fb_a := by
      simp [freqOf, h_ne, h_ne.symm]; omega
    have h_merge_val : mergePair a b z (freqOf a (htInner (htLeaf b fa_a) (htLeaf a fb_a)) +
                                        freqOf b (htInner (htLeaf b fa_a) (htLeaf a fb_a)))
                                        (htInner (htLeaf b fa_a) (htLeaf a fb_a)) =
                       htLeaf z (fa_a + fb_a) := by
      rw [h_freq_sum]; simp [mergePair]
    rw [h_merge_val, freqOf, h_freq_sum]
    by_cases hsz : s = z
    · subst s; simp
    · rw [if_neg (Ne.symm hsz), if_neg hsz]
      by_cases hsa : s = a
      · subst s; simp
      · by_cases hsb : s = b
        · subst s; simp
        · have h_freq_s : freqOf s (htInner (htLeaf b fa_a) (htLeaf a fb_a)) = 0 := by
            simp [freqOf, hsa, hsb, Ne.symm hsa, Ne.symm hsb]
          simp [hsa, hsb, h_freq_s]
  | inLeft l r h_sib_l =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_l with ⟨ha_l, hb_l⟩
    have ha_r : a ∉ alphabet r := Finset.disjoint_left.mp hd ha_l
    have hb_r : b ∉ alphabet r := Finset.disjoint_left.mp hd hb_l
    have hz_l : z ∉ alphabet l := by intro hz; apply hz_fresh; simp [alphabet, hz]
    have hz_r : z ∉ alphabet r := by intro hz; apply hz_fresh; simp [alphabet, hz]
    have h_freq_ar : freqOf a r = 0 := freqOf_eq_zero_of_not_mem _ _ ha_r
    have h_freq_br : freqOf b r = 0 := freqOf_eq_zero_of_not_mem _ _ hb_r
    have h_freq_zr : freqOf z r = 0 := freqOf_eq_zero_of_not_mem _ _ hz_r
    cases l with
    | htLeaf _ _ => exfalso; cases h_sib_l
    | htInner ll lr =>
      have h_fz_l : freqOf a (htInner (htInner ll lr) r) + freqOf b (htInner (htInner ll lr) r) =
                   freqOf a (htInner ll lr) + freqOf b (htInner ll lr) := by
        simp [freqOf, h_freq_ar, h_freq_br]
      rw [h_fz_l]
      have h_merge_r' : mergePair a b z (freqOf a (htInner ll lr) + freqOf b (htInner ll lr)) r = r :=
        mergePair_eq_self_of_not_mem a b z (freqOf a (htInner ll lr) + freqOf b (htInner ll lr)) r ha_r hb_r
      have h_freq_l := freqOf_mergePair_of_areSiblings (htInner ll lr) a b z h_sib_l hcl hz_l s
      have h_mp : mergePair a b z (freqOf a (htInner ll lr) + freqOf b (htInner ll lr))
                                 (htInner (htInner ll lr) r) =
                 htInner (mergePair a b z (freqOf a (htInner ll lr) + freqOf b (htInner ll lr)) (htInner ll lr))
                        (mergePair a b z (freqOf a (htInner ll lr) + freqOf b (htInner ll lr)) r) := by
        simp [mergePair]
      rw [h_mp, h_merge_r']
      conv => lhs; rw [freqOf]
      rw [h_freq_l]
      by_cases hsz : s = z
      · subst s; simp [h_freq_zr]
      · by_cases hsa : s = a
        · subst s; simp [h_freq_ar]
        · by_cases hsb : s = b
          · subst s; simp [h_freq_br]
          · simp [hsz, hsa, hsb, freqOf]
  | inRight l r h_sib_r =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_r with ⟨ha_r, hb_r⟩
    have ha_l : a ∉ alphabet l := Finset.disjoint_right.mp hd ha_r
    have hb_l : b ∉ alphabet l := Finset.disjoint_right.mp hd hb_r
    have hz_l : z ∉ alphabet l := by intro hz; apply hz_fresh; simp [alphabet, hz]
    have hz_r : z ∉ alphabet r := by intro hz; apply hz_fresh; simp [alphabet, hz]
    have h_freq_al : freqOf a l = 0 := freqOf_eq_zero_of_not_mem _ _ ha_l
    have h_freq_bl : freqOf b l = 0 := freqOf_eq_zero_of_not_mem _ _ hb_l
    have h_freq_zl : freqOf z l = 0 := freqOf_eq_zero_of_not_mem _ _ hz_l
    cases r with
    | htLeaf _ _ => exfalso; cases h_sib_r
    | htInner rl rr =>
      have h_fz_r : freqOf a (htInner l (htInner rl rr)) + freqOf b (htInner l (htInner rl rr)) =
                   freqOf a (htInner rl rr) + freqOf b (htInner rl rr) := by
        simp [freqOf, h_freq_al, h_freq_bl]
      rw [h_fz_r]
      have h_merge_l' : mergePair a b z (freqOf a (htInner rl rr) + freqOf b (htInner rl rr)) l = l :=
        mergePair_eq_self_of_not_mem a b z (freqOf a (htInner rl rr) + freqOf b (htInner rl rr)) l ha_l hb_l
      have h_freq_r := freqOf_mergePair_of_areSiblings (htInner rl rr) a b z h_sib_r hcr hz_r s
      have h_mp : mergePair a b z (freqOf a (htInner rl rr) + freqOf b (htInner rl rr))
                                 (htInner l (htInner rl rr)) =
                 htInner (mergePair a b z (freqOf a (htInner rl rr) + freqOf b (htInner rl rr)) l)
                        (mergePair a b z (freqOf a (htInner rl rr) + freqOf b (htInner rl rr)) (htInner rl rr)) := by
        simp [mergePair]
      rw [h_mp, h_merge_l']
      conv => lhs; rw [freqOf]
      rw [h_freq_r]
      by_cases hsz : s = z
      · subst s; simp [h_freq_zl]
      · by_cases hsa : s = a
        · subst s; simp [h_freq_al]
        · by_cases hsb : s = b
          · subst s; simp [h_freq_bl]
          · simp [hsz, hsa, hsb, freqOf]


/-! ## Commuting split leaves through Huffman merging -/

/-! The commutation proof only needs {lit}`rootFreq (splitLeaf t) = rootFreq t` for each forest tree. -/

lemma insortTree_length (t : HuffTree) (ts : List HuffTree) : (insortTree t ts).length = ts.length + 1 := by
  induction ts with
  | nil => simp [insortTree]
  | cons u us ih => simp [insortTree]; split <;> simp [ih]

lemma insortTree_ne_nil (t : HuffTree) (ts : List HuffTree) : insortTree t ts ≠ [] := by rw [← List.length_pos_iff_ne_nil, insortTree_length]; omega

@[simp] lemma splitLeaf_unite (l r : HuffTree) (z a b fa fb : ℕ) :
    splitLeaf (unite l r) z a b fa fb = unite (splitLeaf l z a b fa fb) (splitLeaf r z a b fa fb) := by
  simp [unite, splitLeaf]

@[simp] lemma rootFreq_unite (t1 t2 : HuffTree) : rootFreq (unite t1 t2) = rootFreq t1 + rootFreq t2 := by simp [unite, rootFreq]

/-! ### {name}`insortTree` commutation with {lean}`map splitLeaf` -/

lemma map_splitLeaf_insortTree (U : HuffTree) (ts : List HuffTree) (s1 s2 f1 f2 : ℕ)
    (hU_rf : rootFreq (splitLeaf U s1 s1 s2 f1 f2) = rootFreq U)
    (hts_rf : ∀ t ∈ ts, rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t) :
    (insortTree U ts).map (λ t => splitLeaf t s1 s1 s2 f1 f2)
    = insortTree (splitLeaf U s1 s1 s2 f1 f2) (ts.map (λ t => splitLeaf t s1 s1 s2 f1 f2)) := by
  induction ts generalizing U with
  | nil => simp [insortTree]
  | cons t us ih =>
    have h_us_rf : ∀ u ∈ us, rootFreq (splitLeaf u s1 s1 s2 f1 f2) = rootFreq u :=
      fun u hu => hts_rf u (by simp [hu])
    have ht_rf := hts_rf t (by simp)
    simp [insortTree, List.map_cons]
    by_cases h_rf : rootFreq U ≤ rootFreq t
    · have h_rf' : rootFreq (splitLeaf U s1 s1 s2 f1 f2) ≤ rootFreq (splitLeaf t s1 s1 s2 f1 f2) := by
        rw [hU_rf, ht_rf]; exact h_rf
      simp [h_rf, h_rf']
    · have h_rf' : ¬ rootFreq (splitLeaf U s1 s1 s2 f1 f2) ≤ rootFreq (splitLeaf t s1 s1 s2 f1 f2) := by
        rw [hU_rf, ht_rf]; exact h_rf
      simp [h_rf, h_rf', ih U hU_rf h_us_rf]

/-! ### {name}`insortTree` membership -/

lemma mem_insortTree (t : HuffTree) (ts : List HuffTree) (u : HuffTree) :
    u ∈ insortTree t ts ↔ u = t ∨ u ∈ ts := by
  induction ts generalizing t with
  | nil => simp [insortTree]
  | cons v vs ih =>
    simp [insortTree]
    by_cases h : rootFreq t ≤ rootFreq v
    · simp [h, ih, or_assoc]
    · simp [h, ih, or_assoc, or_comm, or_left_comm]

lemma forall_mem_insortTree {P : HuffTree → Prop} {U : HuffTree} {ts : List HuffTree}
    (hU : P U) (hts : ∀ t ∈ ts, P t) : ∀ t ∈ insortTree U ts, P t := by
  intro t ht
  rcases (mem_insortTree U ts t).mp ht with (rfl | ht')
  · exact hU
  · exact hts t ht'

/-! ### General commutation theorem -/

theorem splitLeaf_huffman_commute_general (ts : List HuffTree) (s1 s2 f1 f2 : ℕ)
    (h_nonempty : ts ≠ [])
    (h_rf_forest : ∀ t ∈ ts, rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t) :
    splitLeaf (huffman ts) s1 s1 s2 f1 f2
    = huffman (ts.map (λ t => splitLeaf t s1 s1 s2 f1 f2)) := by
  induction ts using huffman.induct with
  | case1 =>
    exfalso; exact h_nonempty rfl
  | case2 t => simp [huffman]
  | case3 t1 t2 rest IH =>
    have h1_rf := h_rf_forest t1 (by simp)
    have h2_rf := h_rf_forest t2 (by simp)
    have h_rest_rf : ∀ t ∈ rest, rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t :=
      fun t ht => h_rf_forest t (by simp [ht])
    let U := unite t1 t2
    have hU_rf : rootFreq (splitLeaf U s1 s1 s2 f1 f2) = rootFreq U :=
      by simp [U, h1_rf, h2_rf]
    have h_rec_rf : ∀ t ∈ insortTree U rest,
        rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t :=
      forall_mem_insortTree (P := λ t => rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t)
        hU_rf h_rest_rf
    simp [huffman, List.map_cons, splitLeaf_unite, U]
    have h_nonempty_rec : insortTree U rest ≠ [] := insortTree_ne_nil U rest
    rw [IH h_nonempty_rec h_rec_rf]
    have hU_rf' : rootFreq (splitLeaf U s1 s1 s2 f1 f2) = rootFreq U :=
      h_rec_rf U ((mem_insortTree U rest U).mpr (Or.inl rfl))
    have h_rest_rf' : ∀ t ∈ rest, rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t :=
      fun t ht => h_rec_rf t ((mem_insortTree U rest t).mpr (Or.inr ht))
    rw [map_splitLeaf_insortTree U rest s1 s2 f1 f2 hU_rf' h_rest_rf']
    rfl

/-! ### Special case for {lit}`optimum_huffman` -/

/--
Given a forest {lit}`rest` where {lit}`s1` appears only as
{lit}`htLeaf s1 (f1+f2)` (the combined leaf),
we have the commutation:

{lit}`splitLeaf (huffman (insortTree (htLeaf s1 (f1+f2)) rest)) s1 s1 s2 f1 f2`
{lit}`= huffman (insortTree (htInner (htLeaf s1 f1) (htLeaf s2 f2)) rest)`

Requires: {lit}`s1 ∉ alphabet t` for all {lit}`t ∈ rest`, so that
{name}`splitLeaf` does nothing on {lit}`rest`.
-/
theorem splitLeaf_huffman_commute (s1 s2 f1 f2 : ℕ) (rest : List HuffTree)
    (h_s1_notin_rest : ∀ t ∈ rest, s1 ∉ alphabet t) :
    splitLeaf (huffman (insortTree (htLeaf s1 (f1+f2)) rest)) s1 s1 s2 f1 f2
    = huffman (insortTree (htInner (htLeaf s1 f1) (htLeaf s2 f2)) rest) := by
  let LF := htLeaf s1 (f1+f2)
  let IF := htInner (htLeaf s1 f1) (htLeaf s2 f2)
  have h_LF_rf : rootFreq (splitLeaf LF s1 s1 s2 f1 f2) = rootFreq LF := by
    simp [LF, splitLeaf, rootFreq]
  have h_rest_rf : ∀ t ∈ rest, rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t := by
    intro t ht
    have h_id : splitLeaf t s1 s1 s2 f1 f2 = t :=
      splitLeaf_eq_of_z_not_mem t s1 s1 s2 f1 f2 (h_s1_notin_rest t ht)
    rw [h_id]
  have h_rf_forest : ∀ t ∈ insortTree LF rest,
      rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t :=
    forall_mem_insortTree (P := λ t => rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t)
      h_LF_rf h_rest_rf
  calc
    splitLeaf (huffman (insortTree LF rest)) s1 s1 s2 f1 f2
        = huffman ((insortTree LF rest).map (λ t => splitLeaf t s1 s1 s2 f1 f2)) :=
      splitLeaf_huffman_commute_general (insortTree LF rest) s1 s2 f1 f2
        (insortTree_ne_nil LF rest)
        h_rf_forest
    _ = huffman (insortTree (splitLeaf LF s1 s1 s2 f1 f2) (rest.map (λ t => splitLeaf t s1 s1 s2 f1 f2))) := by
      have hLF_rf' : rootFreq (splitLeaf LF s1 s1 s2 f1 f2) = rootFreq LF :=
        h_rf_forest LF ((mem_insortTree LF rest LF).mpr (Or.inl rfl))
      have h_rest_rf' : ∀ t ∈ rest, rootFreq (splitLeaf t s1 s1 s2 f1 f2) = rootFreq t :=
        fun t ht => h_rf_forest t ((mem_insortTree LF rest t).mpr (Or.inr ht))
      rw [map_splitLeaf_insortTree LF rest s1 s2 f1 f2 hLF_rf' h_rest_rf']
    _ = huffman (insortTree IF (rest.map (λ t => splitLeaf t s1 s1 s2 f1 f2))) := by
      simp [LF, IF, splitLeaf]
    _ = huffman (insortTree IF rest) := by
      have h_map_id : rest.map (λ t => splitLeaf t s1 s1 s2 f1 f2) = rest := by
        let go : ∀ ts : List HuffTree,
            (∀ t ∈ ts, s1 ∉ alphabet t) →
            ts.map (λ t => splitLeaf t s1 s1 s2 f1 f2) = ts := by
          intro ts h
          induction ts with
          | nil => rfl
          | cons t ts ih =>
            have h_t : s1 ∉ alphabet t := h t (by simp)
            have h_ts : ∀ t' ∈ ts, s1 ∉ alphabet t' := fun t' ht' => h t' (by simp [ht'])
            simp [splitLeaf_eq_of_z_not_mem t s1 s1 s2 f1 f2 h_t, ih h_ts]
        exact go rest h_s1_notin_rest
      rw [h_map_id]


/-! ## Preservation of forest frequencies and alphabets -/

/-! {name}`huffman` preserves the aggregate frequencies and alphabet of a nonempty forest. -/

def forest_freq (ts : List HuffTree) (s : ℕ) : ℕ := (ts.map (freqOf s)).sum

def forest_alphabet : List HuffTree → Finset ℕ
  | [] => ∅
  | t :: ts => alphabet t ∪ forest_alphabet ts

lemma mem_forest_alphabet (ts : List HuffTree) (s : ℕ) :
    s ∈ forest_alphabet ts ↔ ∃ t ∈ ts, s ∈ alphabet t := by
  induction ts with
  | nil => simp [forest_alphabet]
  | cons t ts ih =>
    simp [forest_alphabet, ih]

lemma forest_freq_cons (t : HuffTree) (ts : List HuffTree) (s : ℕ) :
    forest_freq (t :: ts) s = freqOf s t + forest_freq ts s := by simp [forest_freq]

lemma forest_freq_insortTree (t : HuffTree) (ts : List HuffTree) (s : ℕ) :
    forest_freq (insortTree t ts) s = forest_freq (t :: ts) s := by
  induction ts generalizing t with
  | nil => simp [insortTree, forest_freq]
  | cons u us ih =>
    by_cases h : rootFreq t ≤ rootFreq u
    · simp [insortTree, h, forest_freq]
    · simp [insortTree, h, forest_freq]
      have h_ih := ih t
      simp [forest_freq] at h_ih ⊢
      omega

lemma forest_alphabet_insortTree (t : HuffTree) (ts : List HuffTree) :
    forest_alphabet (insortTree t ts) = forest_alphabet (t :: ts) := by
  induction ts generalizing t with
  | nil => simp [insortTree, forest_alphabet]
  | cons u us ih =>
    by_cases h : rootFreq t ≤ rootFreq u
    · simp [insortTree, h, forest_alphabet]
    · simp [insortTree, h, ih, forest_alphabet]; ac_rfl

lemma freqOf_huffman_eq_forest_freq (ts : List HuffTree) (s : ℕ) (h_nonempty : ts ≠ []) :
    freqOf s (huffman ts) = forest_freq ts s := by
  induction ts using huffman.induct with
  | case1 => exact False.elim (h_nonempty rfl)
  | case2 t => simp [huffman, forest_freq]
  | case3 t1 t2 rest IH =>
    simp [huffman, forest_freq_insortTree, IH (insortTree_ne_nil (unite t1 t2) rest)]
    simp [forest_freq, unite, freqOf]
    omega

lemma alphabet_huffman_eq_forest_alphabet (ts : List HuffTree) (h_nonempty : ts ≠ []) :
    alphabet (huffman ts) = forest_alphabet ts := by
  induction ts using huffman.induct with
  | case1 => exact False.elim (h_nonempty rfl)
  | case2 t => simp [huffman, forest_alphabet]
  | case3 t1 t2 rest IH =>
    simp [huffman, forest_alphabet_insortTree, IH (insortTree_ne_nil (unite t1 t2) rest)]
    simp [forest_alphabet, unite, alphabet]

lemma forest_consistent_cons_iff (t : HuffTree) (ts : List HuffTree) :
    forest_consistent (t :: ts) ↔
      consistent t ∧ forest_consistent ts ∧ ∀ u ∈ ts, Disjoint (alphabet t) (alphabet u) := by
  cases ts with
  | nil => simp [forest_consistent]
  | cons u us => simp [forest_consistent]

lemma forest_consistent_tail (t : HuffTree) (ts : List HuffTree)
    (h_cons : forest_consistent (t :: ts)) : forest_consistent ts := by
  rw [forest_consistent_cons_iff] at h_cons
  exact h_cons.2.1

lemma forest_consistent_insortTree_fresh (z fz : ℕ) (ts : List HuffTree)
    (h_fresh : ∀ t ∈ ts, z ∉ alphabet t)
    (h_cons : forest_consistent ts) :
  forest_consistent (insortTree (htLeaf z fz) ts) := by
  induction ts with
  | nil => simp [insortTree, forest_consistent, consistent]
  | cons u us ih =>
    have h_fresh_u : z ∉ alphabet u := h_fresh u (by simp)
    have h_fresh_us : ∀ t ∈ us, z ∉ alphabet t := fun t ht => h_fresh t (by simp [ht])
    have h_cons_us : forest_consistent us := forest_consistent_tail u us h_cons
    rw [forest_consistent_cons_iff] at h_cons
    have hcu : consistent u := h_cons.1
    have hdisj_u : ∀ w ∈ us, Disjoint (alphabet u) (alphabet w) := h_cons.2.2
    simp [insortTree]
    split_ifs with h
    · rw [forest_consistent_cons_iff]
      refine ⟨by simp [consistent], ?_, ?_⟩
      · rw [forest_consistent_cons_iff]
        refine ⟨hcu, h_cons_us, hdisj_u⟩
      · intro w hw
        simp [alphabet] at hw ⊢
        cases hw with
        | inl h_eq => rw [h_eq]; exact h_fresh_u
        | inr h_mem => exact h_fresh_us w h_mem
    · rw [forest_consistent_cons_iff]
      refine ⟨hcu, ih h_fresh_us h_cons_us, ?_⟩
      intro w hw
      rw [mem_insortTree] at hw
      cases hw with
      | inl h_eq => rw [h_eq]; simp [alphabet]; exact h_fresh_u
      | inr h_mem => exact hdisj_u w h_mem

lemma forest_freq_eq_zero_of_not_mem (ts : List HuffTree) (s : ℕ)
    (h : s ∉ forest_alphabet ts) : forest_freq ts s = 0 := by
  simp [forest_freq]
  apply List.sum_eq_zero
  intro x hx
  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
  exact freqOf_eq_zero_of_not_mem s t
    (fun h_mem => h ((mem_forest_alphabet ts s).mpr ⟨t, ht, h_mem⟩))

lemma forest_freq_eq_rootFreq_of_mem_leaf (ts : List HuffTree) (s : ℕ) (t : HuffTree)
    (h_leaves : ∀ u ∈ ts, height u = 0)
    (h_cons : forest_consistent ts)
    (ht : t ∈ ts)
    (hs : s ∈ alphabet t) :
    forest_freq ts s = rootFreq t := by
  induction ts generalizing t with
  | nil => simp at ht
  | cons u us ih =>
    by_cases h_eq : t = u
    ·
      subst h_eq
      simp [forest_freq]
      have h_zero : forest_freq us s = 0 := by
        apply forest_freq_eq_zero_of_not_mem
        rw [mem_forest_alphabet]
        rintro ⟨v, hv, h_mem⟩
        rw [forest_consistent_cons_iff] at h_cons
        exact (Finset.disjoint_left.mp (h_cons.2.2 v hv) hs) h_mem
      have h_freq_t : freqOf s t = rootFreq t := by
        rcases height_eq_zero_iff t |>.mp (h_leaves t (by simp)) with ⟨sym, f, rfl⟩
        simp [alphabet] at hs
        subst hs
        simp [freqOf, rootFreq]
      simp [h_freq_t, forest_freq] at h_zero ⊢
      omega
    ·
      have h_mem' : t ∈ us := by
        simpa [h_eq] using ht
      simp [forest_freq]
      have h_zero : freqOf s u = 0 :=
        freqOf_eq_zero_of_not_mem s u (by
          rw [forest_consistent_cons_iff] at h_cons
          intro h_su
          exact (Finset.disjoint_left.mp (h_cons.2.2 t h_mem') h_su) hs)
      have h_rec : forest_freq us s = rootFreq t :=
        ih t (fun v hv => h_leaves v (by simp [hv]))
          (forest_consistent_tail u us h_cons) h_mem' hs
      simp [forest_freq] at h_rec ⊢
      simp [h_zero, h_rec]


lemma forest_sorted_tail (t : HuffTree) (ts : List HuffTree)
    (h_sorted : forest_sorted (t :: ts)) : forest_sorted ts := by
  cases ts with
  | nil => simp [forest_sorted]
  | cons u us => simpa [forest_sorted] using h_sorted.2

lemma forest_sorted_insortTree_of_sorted (t : HuffTree) (ts : List HuffTree)
    (h_sorted : forest_sorted ts) : forest_sorted (insortTree t ts) := by
  induction ts generalizing t with
  | nil => simp [insortTree, forest_sorted]
  | cons u us ih =>
    have h_sorted_us : forest_sorted us := forest_sorted_tail u us h_sorted
    simp [insortTree]
    by_cases h : rootFreq t ≤ rootFreq u
    · simp [h, forest_sorted, h_sorted]
    · simp [h]
      have h_ne : insortTree t us ≠ [] := insortTree_ne_nil t us
      have h1 : rootFreq u ≤ rootFreq ((insortTree t us).head h_ne) := by
        cases us with
        | nil =>
          simp [insortTree]
          omega
        | cons v vs =>
          simp [insortTree]
          by_cases h2 : rootFreq t ≤ rootFreq v
          · simp [h2]; omega
          · simp [h2]; simp [forest_sorted] at h_sorted; omega
      have ih' := ih t h_sorted_us
      cases h_r : insortTree t us with
      | nil =>
        exact False.elim (h_ne h_r)
      | cons x xs =>
        simp [h_r] at h1 ih'
        simpa [forest_sorted] using And.intro h1 ih'

lemma forest_consistent_insortTree (t : HuffTree) (ts : List HuffTree)
    (h_cons : forest_consistent (t :: ts)) :
  forest_consistent (insortTree t ts) := by
  induction ts generalizing t with
  | nil => simpa [insortTree]
  | cons u us ih =>
    have h_parts := (forest_consistent_cons_iff t (u :: us)).mp h_cons
    have h_cons_u_us : forest_consistent (u :: us) := h_parts.2.1
    have h_u_parts := (forest_consistent_cons_iff u us).mp h_cons_u_us
    have h_cons_t_us : forest_consistent (t :: us) := by
      rw [forest_consistent_cons_iff]
      exact ⟨h_parts.1, h_u_parts.2.1, fun w hw => h_parts.2.2 w (by simp [hw])⟩
    have ih' := ih t h_cons_t_us
    simp [insortTree]
    by_cases h : rootFreq t ≤ rootFreq u
    · simp [h]; exact h_cons
    · simp [h]
      rw [forest_consistent_cons_iff]
      refine ⟨h_u_parts.1, ih', ?_⟩
      intro w hw
      rw [mem_insortTree] at hw
      rcases hw with rfl | hw
      · exact Disjoint.symm (h_parts.2.2 u (by simp))
      · exact h_u_parts.2.2 w hw

lemma rootFreq_le_of_mem_sorted (t : HuffTree) (ts : List HuffTree)
    (h_sorted : forest_sorted (t :: ts)) :
    ∀ u ∈ ts, rootFreq t ≤ rootFreq u := by
  induction ts generalizing t with
  | nil => simp
  | cons v vs ih =>
    intro u hu
    simp [forest_sorted] at h_sorted
    by_cases huv : u = v
    · rw [huv]; exact h_sorted.1
    · have hu' : u ∈ vs := by simpa [huv] using hu
      have h_sorted_t_vs : forest_sorted (t :: vs) := by
        cases vs with
        | nil => simp [forest_sorted]
        | cons w ws =>
          simp [forest_sorted]
          constructor
          · have hvw : rootFreq v ≤ rootFreq w := by
              apply ih v h_sorted.2 w (by simp)
            omega
          · exact h_sorted.2.2
      exact ih t h_sorted_t_vs u hu'

/-! ## Core exchange and split-leaf optimality theorem -/

def deepestSiblingPair (t : HuffTree) : ℕ × ℕ :=
  match t with
  | htLeaf s _ => (s, s)
  | htInner l r =>
    match l, r with
    | htLeaf x _, htLeaf y _ => (x, y)
    | htLeaf _ _, _ => deepestSiblingPair r
    | _, htLeaf _ _ => deepestSiblingPair l
    | _, _ => if height l ≥ height r then deepestSiblingPair l else deepestSiblingPair r

lemma deepestSiblingPair_mem1 (t : HuffTree) : (deepestSiblingPair t).1 ∈ alphabet t := by
  induction t with
  | htLeaf s f => simp [deepestSiblingPair, alphabet]
  | htInner l r ihl ihr =>
    cases l with
    | htLeaf x fx => cases r with
      | htLeaf y fy => simp [deepestSiblingPair, alphabet]
      | htInner rl rr =>
        have h_dsp : deepestSiblingPair (htInner (htLeaf x fx) (htInner rl rr)) = deepestSiblingPair (htInner rl rr) := by simp [deepestSiblingPair]
        have h_alph : alphabet (htInner (htLeaf x fx) (htInner rl rr)) = {x} ∪ alphabet (htInner rl rr) := by simp [alphabet]
        rw [h_dsp, h_alph]; exact Finset.mem_union_right {x} ihr
    | htInner ll lr => cases r with
      | htLeaf y fy =>
        have h_dsp : deepestSiblingPair (htInner (htInner ll lr) (htLeaf y fy)) = deepestSiblingPair (htInner ll lr) := by simp [deepestSiblingPair]
        have h_alph : alphabet (htInner (htInner ll lr) (htLeaf y fy)) = alphabet (htInner ll lr) ∪ {y} := by simp [alphabet]
        rw [h_dsp, h_alph]; exact Finset.mem_union_left {y} ihl
      | htInner rl rr =>
        have h_dsp : deepestSiblingPair (htInner (htInner ll lr) (htInner rl rr)) = (if height (htInner ll lr) ≥ height (htInner rl rr) then deepestSiblingPair (htInner ll lr) else deepestSiblingPair (htInner rl rr)) := by simp [deepestSiblingPair]
        have h_alph : alphabet (htInner (htInner ll lr) (htInner rl rr)) = alphabet (htInner ll lr) ∪ alphabet (htInner rl rr) := by simp [alphabet]
        rw [h_dsp, h_alph]
        by_cases h_ge : height (htInner ll lr) ≥ height (htInner rl rr)
        · rw [if_pos h_ge]; exact Finset.mem_union_left (alphabet (htInner rl rr)) ihl
        · rw [if_neg h_ge]; exact Finset.mem_union_right (alphabet (htInner ll lr)) ihr

lemma deepestSiblingPair_mem2 (t : HuffTree) : (deepestSiblingPair t).2 ∈ alphabet t := by
  induction t with
  | htLeaf s f => simp [deepestSiblingPair, alphabet]
  | htInner l r ihl ihr =>
    cases l with
    | htLeaf x fx => cases r with
      | htLeaf y fy => simp [deepestSiblingPair, alphabet]
      | htInner rl rr =>
        have h_dsp : deepestSiblingPair (htInner (htLeaf x fx) (htInner rl rr)) = deepestSiblingPair (htInner rl rr) := by simp [deepestSiblingPair]
        have h_alph : alphabet (htInner (htLeaf x fx) (htInner rl rr)) = {x} ∪ alphabet (htInner rl rr) := by simp [alphabet]
        rw [h_dsp, h_alph]; exact Finset.mem_union_right {x} ihr
    | htInner ll lr => cases r with
      | htLeaf y fy =>
        have h_dsp : deepestSiblingPair (htInner (htInner ll lr) (htLeaf y fy)) = deepestSiblingPair (htInner ll lr) := by simp [deepestSiblingPair]
        have h_alph : alphabet (htInner (htInner ll lr) (htLeaf y fy)) = alphabet (htInner ll lr) ∪ {y} := by simp [alphabet]
        rw [h_dsp, h_alph]; exact Finset.mem_union_left {y} ihl
      | htInner rl rr =>
        have h_dsp : deepestSiblingPair (htInner (htInner ll lr) (htInner rl rr)) = (if height (htInner ll lr) ≥ height (htInner rl rr) then deepestSiblingPair (htInner ll lr) else deepestSiblingPair (htInner rl rr)) := by simp [deepestSiblingPair]
        have h_alph : alphabet (htInner (htInner ll lr) (htInner rl rr)) = alphabet (htInner ll lr) ∪ alphabet (htInner rl rr) := by simp [alphabet]
        rw [h_dsp, h_alph]
        by_cases h_ge : height (htInner ll lr) ≥ height (htInner rl rr)
        · rw [if_pos h_ge]; exact Finset.mem_union_left (alphabet (htInner rl rr)) ihl
        · rw [if_neg h_ge]; exact Finset.mem_union_right (alphabet (htInner ll lr)) ihr

lemma depthOf_getD_inner_of_mem_left {s : ℕ} {l r : HuffTree} (h : s ∈ alphabet l) :
    (depthOf s (htInner l r)).getD 0 = (depthOf s l).getD 0 + 1 := by
  have ⟨d, hd⟩ := depthOf_some_of_mem s l h
  simp [depthOf, hd]

lemma depthOf_getD_inner_of_mem_right {s : ℕ} {l r : HuffTree} (h : s ∈ alphabet r) (h_not : s ∉ alphabet l) :
    (depthOf s (htInner l r)).getD 0 = (depthOf s r).getD 0 + 1 := by
  have ⟨d, hd⟩ := depthOf_some_of_mem s r h
  simp [depthOf, depthOf_none_of_not_mem s l h_not, hd]

lemma deepestSiblingPair_depth (t : HuffTree) (h_cons : consistent t) :
    (depthOf (deepestSiblingPair t).1 t).getD 0 = height t ∧ (depthOf (deepestSiblingPair t).2 t).getD 0 = height t := by
  induction t with
  | htLeaf s f => simp [deepestSiblingPair, depthOf, height]
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    cases l with
    | htLeaf x fx =>
      cases r with
      | htLeaf y fy =>
        simp [deepestSiblingPair, height]
        have hx : (depthOf x (htInner (htLeaf x fx) (htLeaf y fy))).getD 0 = 1 := by
          simp [depthOf, Option.getD]
        have hy : (depthOf y (htInner (htLeaf x fx) (htLeaf y fy))).getD 0 = 1 := by
          by_cases h_eq : x = y
          · subst h_eq; simp [depthOf, Option.getD]
          · simp [depthOf, h_eq, Option.getD]
        exact And.intro hx hy
      | htInner rl rr =>
        have h_dsp : deepestSiblingPair (htInner (htLeaf x fx) (htInner rl rr)) = deepestSiblingPair (htInner rl rr) := by
          simp [deepestSiblingPair]
        have h_height : height (htInner (htLeaf x fx) (htInner rl rr)) = height (htInner rl rr) + 1 := by
          simp [height]
        rw [h_dsp, h_height]
        rcases ihr hcr with ⟨h1, h2⟩
        have h_mem1 : (deepestSiblingPair (htInner rl rr)).1 ∈ alphabet (htInner rl rr) :=
          deepestSiblingPair_mem1 (htInner rl rr)
        have h_not_mem_l1 : (deepestSiblingPair (htInner rl rr)).1 ∉ alphabet (htLeaf x fx) :=
          Finset.disjoint_right.mp hd h_mem1
        have h_mem2 : (deepestSiblingPair (htInner rl rr)).2 ∈ alphabet (htInner rl rr) :=
          deepestSiblingPair_mem2 (htInner rl rr)
        have h_not_mem_l2 : (deepestSiblingPair (htInner rl rr)).2 ∉ alphabet (htLeaf x fx) :=
          Finset.disjoint_right.mp hd h_mem2
        constructor
        · rw [depthOf_getD_inner_of_mem_right h_mem1 h_not_mem_l1, h1]
        · rw [depthOf_getD_inner_of_mem_right h_mem2 h_not_mem_l2, h2]
    | htInner ll lr =>
      cases r with
      | htLeaf y fy =>
        have h_dsp : deepestSiblingPair (htInner (htInner ll lr) (htLeaf y fy)) = deepestSiblingPair (htInner ll lr) := by
          simp [deepestSiblingPair]
        have h_height : height (htInner (htInner ll lr) (htLeaf y fy)) = height (htInner ll lr) + 1 := by
          simp [height]
        rw [h_dsp, h_height]
        rcases ihl hcl with ⟨h1, h2⟩
        have h_mem1 : (deepestSiblingPair (htInner ll lr)).1 ∈ alphabet (htInner ll lr) :=
          deepestSiblingPair_mem1 (htInner ll lr)
        have h_mem2 : (deepestSiblingPair (htInner ll lr)).2 ∈ alphabet (htInner ll lr) :=
          deepestSiblingPair_mem2 (htInner ll lr)
        constructor
        · rw [depthOf_getD_inner_of_mem_left h_mem1, h1]
        · rw [depthOf_getD_inner_of_mem_left h_mem2, h2]
      | htInner rl rr =>
        have h_height : height (htInner (htInner ll lr) (htInner rl rr)) = max (height (htInner ll lr)) (height (htInner rl rr)) + 1 := by
          simp [height]
        rw [h_height]
        by_cases h_ge : height (htInner ll lr) ≥ height (htInner rl rr)
        · have h_dsp : deepestSiblingPair (htInner (htInner ll lr) (htInner rl rr)) = deepestSiblingPair (htInner ll lr) := by
            simp [deepestSiblingPair, h_ge]
          have h_max : max (height (htInner ll lr)) (height (htInner rl rr)) = height (htInner ll lr) := by
            simp [h_ge]
          rw [h_dsp, h_max]
          rcases ihl hcl with ⟨h1, h2⟩
          have h_mem1 : (deepestSiblingPair (htInner ll lr)).1 ∈ alphabet (htInner ll lr) :=
            deepestSiblingPair_mem1 (htInner ll lr)
          have h_mem2 : (deepestSiblingPair (htInner ll lr)).2 ∈ alphabet (htInner ll lr) :=
            deepestSiblingPair_mem2 (htInner ll lr)
          constructor
          · rw [depthOf_getD_inner_of_mem_left h_mem1, h1]
          · rw [depthOf_getD_inner_of_mem_left h_mem2, h2]
        · have h_dsp : deepestSiblingPair (htInner (htInner ll lr) (htInner rl rr)) = deepestSiblingPair (htInner rl rr) := by
            simp [deepestSiblingPair, h_ge]
          have h_max : max (height (htInner ll lr)) (height (htInner rl rr)) = height (htInner rl rr) :=
            Nat.max_eq_right (by omega)
          rw [h_dsp, h_max]
          rcases ihr hcr with ⟨h1, h2⟩
          have h_mem1 : (deepestSiblingPair (htInner rl rr)).1 ∈ alphabet (htInner rl rr) :=
            deepestSiblingPair_mem1 (htInner rl rr)
          have h_not_mem_l1 : (deepestSiblingPair (htInner rl rr)).1 ∉ alphabet (htInner ll lr) :=
            Finset.disjoint_right.mp hd h_mem1
          have h_mem2 : (deepestSiblingPair (htInner rl rr)).2 ∈ alphabet (htInner rl rr) :=
            deepestSiblingPair_mem2 (htInner rl rr)
          have h_not_mem_l2 : (deepestSiblingPair (htInner rl rr)).2 ∉ alphabet (htInner ll lr) :=
            Finset.disjoint_right.mp hd h_mem2
          constructor
          · rw [depthOf_getD_inner_of_mem_right h_mem1 h_not_mem_l1, h1]
          · rw [depthOf_getD_inner_of_mem_right h_mem2 h_not_mem_l2, h2]

lemma deepestSiblingPair_areSiblings (t : HuffTree) (h_cons : consistent t)
    (h_height : height t ≥ 1) :
    areSiblings (deepestSiblingPair t).1 (deepestSiblingPair t).2 t := by
  induction t with
  | htLeaf s f => simp [height] at h_height
  | htInner l r ihl ihr =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    cases l with
    | htLeaf x fx =>
      cases r with
      | htLeaf y fy => exact areSiblings.here (a := x) (b := y) fx fy
      | htInner rl rr =>
        have hh_r : height (htInner rl rr) ≥ 1 := by simp [height]
        have hh := ihr hcr hh_r
        exact areSiblings.inRight (htLeaf x fx) (htInner rl rr) hh
    | htInner ll lr =>
      cases r with
      | htLeaf y fy =>
        have hh_l : height (htInner ll lr) ≥ 1 := by simp [height]
        have hh := ihl hcl hh_l
        exact areSiblings.inLeft (htInner ll lr) (htLeaf y fy) hh
      | htInner rl rr =>
        have hh_l : height (htInner ll lr) ≥ 1 := by simp [height]
        have hh_r : height (htInner rl rr) ≥ 1 := by simp [height]
        by_cases h_ge : height (htInner ll lr) ≥ height (htInner rl rr)
        · have hh := ihl hcl hh_l
          simpa [deepestSiblingPair, h_ge] using
            areSiblings.inLeft (htInner ll lr) (htInner rl rr) hh
        · have hh := ihr hcr hh_r
          simpa [deepestSiblingPair, h_ge] using
            areSiblings.inRight (htInner ll lr) (htInner rl rr) hh

lemma areSiblings_exchangeLeft (t : HuffTree) (a x y : ℕ) (h_sib : areSiblings x y t)
    (h_ne_ax : a ≠ x) (h_ne_ay : a ≠ y) (h_ne_xy : x ≠ y) : areSiblings a y (swapLeaves a x t) := by
  induction h_sib with
  | here fa fb =>
    simp [swapLeaves, h_ne_ax.symm, h_ne_ay.symm, h_ne_xy.symm]
    refine areSiblings.here (a := a) (b := y) ?_ ?_ <;> simp
  | here' fa fb =>
    simp [swapLeaves, h_ne_ax.symm, h_ne_ay.symm, h_ne_xy, h_ne_xy.symm]
    refine areSiblings.here' (a := a) (b := y) ?_ ?_ <;> simp
  | inLeft l r h ih =>
    simp [swapLeaves]
    exact areSiblings.inLeft _ _ ih
  | inRight l r h ih =>
    simp [swapLeaves]
    exact areSiblings.inRight _ _ ih

lemma areSiblings_replaceFreq (t : HuffTree) (a b sym freq : ℕ) (h_sib : areSiblings a b t) :
    areSiblings a b (replaceFreq sym freq t) := by
  induction h_sib with
  | here fa fb =>
    simp [replaceFreq]; split <;> split <;> apply areSiblings.here
  | here' fa fb =>
    simp [replaceFreq]; split <;> split <;> apply areSiblings.here'
  | inLeft l r h ih =>
    simp [replaceFreq]; exact areSiblings.inLeft _ _ ih
  | inRight l r h ih =>
    simp [replaceFreq]; exact areSiblings.inRight _ _ ih

lemma areSiblings_swapFreqs_preserved (t : HuffTree) (a b x y : ℕ) (h_sib : areSiblings a b t) :
    areSiblings a b (swapFreqs x y t) := by
  dsimp [swapFreqs]
  apply areSiblings_replaceFreq _ _ _ _ _ (areSiblings_replaceFreq _ _ _ _ _ h_sib)

lemma areSiblings_ne (t : HuffTree) (a b : ℕ) (h_cons : consistent t) (h_sib : areSiblings a b t) : a ≠ b := by
  induction h_sib with
  | here fa fb =>
    rcases h_cons with ⟨_, _, hd⟩
    intro heq; subst heq
    simp [alphabet, Finset.disjoint_iff_inter_eq_empty] at hd
  | here' fa fb =>
    rcases h_cons with ⟨_, _, hd⟩
    intro heq; subst heq
    simp [alphabet, Finset.disjoint_iff_inter_eq_empty] at hd
  | inLeft l r h_sib_l ih =>
    rcases h_cons with ⟨hcl, _, _⟩
    exact ih hcl
  | inRight l r h_sib_r ih =>
    rcases h_cons with ⟨_, hcr, _⟩
    exact ih hcr

lemma depthOf_getD_le_height (t : HuffTree) (s : ℕ) : (depthOf s t).getD 0 ≤ height t := by
  induction t with
  | htLeaf sym f => simp [depthOf, height]; split <;> simp
  | htInner l r ihl ihr =>
    simp [depthOf, height]
    cases h_l : depthOf s l with
    | none =>
      simp [h_l]
      cases h_r : depthOf s r with
      | none => simp
      | some d =>
        simp [h_r]
        have hd : d ≤ height r := by simpa [h_r] using ihr
        omega
    | some d =>
        simp [h_l]
        have hd : d ≤ height l := by simpa [h_l] using ihl
        omega

lemma optimum_leaf (s f : ℕ) (h_f_pos : f > 0) : optimum (htLeaf s f) := by
  refine ⟨by simp [consistent], ?_, ?_⟩
  · simp [alphabet, freqOf, h_f_pos]
  · intro u _ h_sameFreqs
    exact Nat.zero_le (cost u)

private lemma swapLeaves_comm (a b : ℕ) (t : HuffTree) : swapLeaves a b t = swapLeaves b a t := by
  induction t with
  | htLeaf s f =>
    dsimp [swapLeaves]
    by_cases h1 : s = a
    · rw [h1]
      by_cases h2 : a = b
      · rw [h2]
      · simp [h2]
    · by_cases h2 : s = b
      · rw [h2]; simp [h1, Ne.symm h1]
      · simp [h1, h2]
  | htInner l r ihl ihr =>
    simp [swapLeaves, ihl, ihr]

private lemma areSiblings_swap_siblings {a b : ℕ} {t : HuffTree} (h_sib : areSiblings a b t) (h_ne : a ≠ b) :
    areSiblings b a (swapLeaves a b t) := by
  induction h_sib with
  | here fa fb =>
    simp [swapLeaves, h_ne, h_ne.symm]
    exact areSiblings.here fa fb
  | here' fa fb =>
    simp [swapLeaves, h_ne, h_ne.symm]
    exact areSiblings.here' fa fb
  | inLeft l r h ih => simp [swapLeaves]; exact areSiblings.inLeft _ _ ih
  | inRight l r h ih => simp [swapLeaves]; exact areSiblings.inRight _ _ ih

lemma areSiblings_exchangeRight (t : HuffTree) (a b x : ℕ) (h_sib : areSiblings a x t)
    (h_ne_ba : b ≠ a) (h_ne_bx : b ≠ x) (h_ne_ax : a ≠ x) : areSiblings a b (swapLeaves b x t) := by
  induction h_sib with
  | here fa fx =>
    simp [swapLeaves, h_ne_bx.symm, h_ne_ba.symm, h_ne_ax]
    refine areSiblings.here (a := a) (b := b) ?_ ?_ <;> simp
  | here' fa fx =>
    simp [swapLeaves, h_ne_bx.symm, h_ne_ba.symm, h_ne_ax, h_ne_ax.symm]
    refine areSiblings.here' (a := a) (b := b) ?_ ?_ <;> simp
  | inLeft l r h ih =>
    simp [swapLeaves]
    exact areSiblings.inLeft _ _ ih
  | inRight l r h ih =>
    simp [swapLeaves]
    exact areSiblings.inRight _ _ ih

private lemma freqOf_mergePair_same_sibling (t : HuffTree) (b z s : ℕ)
    (h_sib : areSiblings z b t) (h_cons : consistent t) (hz_ne_b : z ≠ b) :
    freqOf s (mergePair z b z (freqOf z t + freqOf b t) t) =
    if s = z then freqOf z t + freqOf b t else if s = b then 0 else freqOf s t := by
  induction h_sib with
  | here fa fb =>
    have h_freq_sum : freqOf z (htInner (htLeaf z fa) (htLeaf b fb)) +
                     freqOf b (htInner (htLeaf z fa) (htLeaf b fb)) = fa + fb := by
      simp [freqOf, hz_ne_b, hz_ne_b.symm]
    have h_merge_val : mergePair z b z (freqOf z (htInner (htLeaf z fa) (htLeaf b fb)) +
                                        freqOf b (htInner (htLeaf z fa) (htLeaf b fb)))
                                        (htInner (htLeaf z fa) (htLeaf b fb)) =
                       htLeaf z (fa + fb) := by
      rw [h_freq_sum]; simp [mergePair]
    rw [h_merge_val, freqOf, h_freq_sum]
    by_cases hsz : s = z
    · subst s; simp [hz_ne_b]
    · rw [if_neg (Ne.symm hsz), if_neg hsz]
      by_cases hsb : s = b
      · subst s; simp [hz_ne_b]
      · have h_freq_s : freqOf s (htInner (htLeaf z fa) (htLeaf b fb)) = 0 := by
          simp [freqOf, hsz, hsb, Ne.symm hsz, Ne.symm hsb]
        simp [hsz, hsb, h_freq_s]
  | here' fa fb =>
    have h_freq_sum : freqOf z (htInner (htLeaf b fb) (htLeaf z fa)) +
                     freqOf b (htInner (htLeaf b fb) (htLeaf z fa)) = fa + fb := by
      simp [freqOf, hz_ne_b, hz_ne_b.symm]
    have h_merge_val : mergePair z b z (freqOf z (htInner (htLeaf b fb) (htLeaf z fa)) +
                                        freqOf b (htInner (htLeaf b fb) (htLeaf z fa)))
                                        (htInner (htLeaf b fb) (htLeaf z fa)) =
                       htLeaf z (fa + fb) := by
      rw [h_freq_sum]; simp [mergePair]
    rw [h_merge_val, freqOf, h_freq_sum]
    by_cases hsz : s = z
    · subst s; simp [hz_ne_b]
    · rw [if_neg (Ne.symm hsz), if_neg hsz]
      by_cases hsb : s = b
      · subst s; simp [hz_ne_b]
      · have h_freq_s : freqOf s (htInner (htLeaf b fb) (htLeaf z fa)) = 0 := by
          simp [freqOf, hsz, hsb, Ne.symm hsz, Ne.symm hsb]
        simp [hsz, hsb, h_freq_s]
  | inLeft l r h_sib_l ih =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_l with ⟨hz_l, hb_l⟩
    have hz_r : z ∉ alphabet r := Finset.disjoint_left.mp hd hz_l
    have hb_r : b ∉ alphabet r := Finset.disjoint_left.mp hd hb_l
    have h_freq_zr : freqOf z r = 0 := freqOf_eq_zero_of_not_mem _ _ hz_r
    have h_freq_br : freqOf b r = 0 := freqOf_eq_zero_of_not_mem _ _ hb_r
    cases l with
    | htLeaf _ _ => exfalso; cases h_sib_l
    | htInner ll lr =>
      have h_freq_sum : freqOf z (htInner (htInner ll lr) r) + freqOf b (htInner (htInner ll lr) r) =
                       freqOf z (htInner ll lr) + freqOf b (htInner ll lr) := by
        simp [freqOf, h_freq_zr, h_freq_br]
      rw [h_freq_sum]
      have h_merge_r : mergePair z b z (freqOf z (htInner ll lr) + freqOf b (htInner ll lr)) r = r :=
        mergePair_eq_self_of_not_mem z b z (freqOf z (htInner ll lr) + freqOf b (htInner ll lr)) r hz_r hb_r
      have h_freq_l := ih hcl
      have h_mp : mergePair z b z (freqOf z (htInner ll lr) + freqOf b (htInner ll lr))
                                 (htInner (htInner ll lr) r) =
                 htInner (mergePair z b z (freqOf z (htInner ll lr) + freqOf b (htInner ll lr)) (htInner ll lr))
                        (mergePair z b z (freqOf z (htInner ll lr) + freqOf b (htInner ll lr)) r) := by
        simp [mergePair]
      rw [h_mp, h_merge_r]
      conv => lhs; rw [freqOf]
      rw [h_freq_l]
      by_cases hsz : s = z
      · subst s; simp [h_freq_zr]
      · by_cases hsb : s = b
        · subst s; simp [h_freq_br]
        · simp [hsz, hsb, freqOf]
  | inRight l r h_sib_r ih =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_r with ⟨hz_r, hb_r⟩
    have hz_l : z ∉ alphabet l := Finset.disjoint_right.mp hd hz_r
    have hb_l : b ∉ alphabet l := Finset.disjoint_right.mp hd hb_r
    have h_freq_zl : freqOf z l = 0 := freqOf_eq_zero_of_not_mem _ _ hz_l
    have h_freq_bl : freqOf b l = 0 := freqOf_eq_zero_of_not_mem _ _ hb_l
    cases r with
    | htLeaf _ _ => exfalso; cases h_sib_r
    | htInner rl rr =>
      have h_freq_sum : freqOf z (htInner l (htInner rl rr)) + freqOf b (htInner l (htInner rl rr)) =
                       freqOf z (htInner rl rr) + freqOf b (htInner rl rr) := by
        simp [freqOf, h_freq_zl, h_freq_bl]
      rw [h_freq_sum]
      have h_merge_l : mergePair z b z (freqOf z (htInner rl rr) + freqOf b (htInner rl rr)) l = l :=
        mergePair_eq_self_of_not_mem z b z (freqOf z (htInner rl rr) + freqOf b (htInner rl rr)) l hz_l hb_l
      have h_freq_r := ih hcr
      have h_mp : mergePair z b z (freqOf z (htInner rl rr) + freqOf b (htInner rl rr))
                                 (htInner l (htInner rl rr)) =
                 htInner (mergePair z b z (freqOf z (htInner rl rr) + freqOf b (htInner rl rr)) l)
                        (mergePair z b z (freqOf z (htInner rl rr) + freqOf b (htInner rl rr)) (htInner rl rr)) := by
        simp [mergePair]
      rw [h_mp, h_merge_l]
      conv => lhs; rw [freqOf]
      rw [h_freq_r]
      by_cases hsz : s = z
      · subst s; simp [h_freq_zl]
      · by_cases hsb : s = b
        · subst s; simp [h_freq_bl]
        · simp [hsz, hsb, freqOf]

private lemma consistent_mergePair_same_sibling (t : HuffTree) (b z fz : ℕ)
    (h_sib : areSiblings z b t) (h_cons : consistent t) (hz_ne_b : z ≠ b) :
    consistent (mergePair z b z fz t) := by
  induction h_sib with
  | here fa fb => simp [mergePair, consistent]
  | here' fa fb => simp [mergePair, consistent]
  | inLeft l r h_sib_l ih =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_l with ⟨hz_l, hb_l⟩
    have hz_not_r : z ∉ alphabet r := Finset.disjoint_left.mp hd hz_l
    have hb_not_r : b ∉ alphabet r := Finset.disjoint_left.mp hd hb_l
    have h_merge_r : mergePair z b z fz r = r :=
      mergePair_eq_self_of_not_mem z b z fz r hz_not_r hb_not_r
    have h_l : consistent (mergePair z b z fz l) := ih hcl
    have h_disjoint_merge : Disjoint (alphabet (mergePair z b z fz l)) (alphabet r) := by
      have h_sub : alphabet (mergePair z b z fz l) ⊆ alphabet l ∪ {z} :=
        alphabet_mergePair_subset z b z fz l
      have h_disj_sup : Disjoint (alphabet l ∪ {z}) (alphabet r) := by
        rw [Finset.disjoint_union_left]
        exact ⟨hd, by rw [Finset.disjoint_singleton_left]; exact hz_not_r⟩
      exact Finset.disjoint_of_subset_left h_sub h_disj_sup
    cases l with
    | htLeaf s f => exfalso; cases h_sib_l
    | htInner ll lr =>
      simp [mergePair, h_merge_r, consistent]
      exact ⟨h_l, hcr, h_disjoint_merge⟩
  | inRight l r h_sib_r ih =>
    rcases h_cons with ⟨hcl, hcr, hd⟩
    rcases areSiblings_mem_alphabet h_sib_r with ⟨hz_r, hb_r⟩
    have hz_not_l : z ∉ alphabet l := Finset.disjoint_right.mp hd hz_r
    have hb_not_l : b ∉ alphabet l := Finset.disjoint_right.mp hd hb_r
    have h_merge_l : mergePair z b z fz l = l :=
      mergePair_eq_self_of_not_mem z b z fz l hz_not_l hb_not_l
    have h_r : consistent (mergePair z b z fz r) := ih hcr
    have h_disjoint_merge : Disjoint (alphabet l) (alphabet (mergePair z b z fz r)) := by
      have h_sub : alphabet (mergePair z b z fz r) ⊆ alphabet r ∪ {z} :=
        alphabet_mergePair_subset z b z fz r
      have h_disj_sup : Disjoint (alphabet l) (alphabet r ∪ {z}) := by
        rw [Finset.disjoint_union_right]
        exact ⟨hd, by rw [Finset.disjoint_singleton_right]; exact hz_not_l⟩
      exact Finset.disjoint_of_subset_right h_sub h_disj_sup
    cases r with
    | htLeaf s f => exfalso; cases h_sib_r
    | htInner rl rr =>
      simp [mergePair, h_merge_l, consistent]
      exact ⟨hcl, h_r, h_disjoint_merge⟩

private lemma mem_alphabet_splitLeaf_of_ne (t : HuffTree) (z b fa fb x : ℕ) (hx_ne_z : x ≠ z) (hx_ne_b : x ≠ b) :
    x ∈ alphabet (splitLeaf t z z b fa fb) → x ∈ alphabet t := by
  induction t with
  | htLeaf sym f =>
    by_cases hz : sym = z
    · subst hz; simp [splitLeaf, alphabet, hx_ne_z, hx_ne_b]
    · simp [splitLeaf, alphabet, hz]
  | htInner l r ihl ihr =>
    simp [splitLeaf, alphabet, Finset.mem_union]
    intro h
    rcases h with (h | h)
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)

private lemma freqOf_splitLeaf_of_ne (t : HuffTree) (z b fa fb x : ℕ) (hx_ne_z : x ≠ z) (hx_ne_b : x ≠ b) :
    freqOf x (splitLeaf t z z b fa fb) = freqOf x t := by
  induction t with
  | htLeaf sym f =>
    by_cases hz : sym = z
    · subst hz; simp [splitLeaf, freqOf, hx_ne_z, hx_ne_b, Ne.symm hx_ne_z, Ne.symm hx_ne_b]
    · simp [splitLeaf, freqOf, hz]
  | htInner l r ihl ihr =>
    simp [splitLeaf, freqOf, ihl, ihr]

private lemma freqOf_splitLeaf_left (t : HuffTree) (z b fa fb : ℕ) (h_cons : consistent t)
    (hz_in : z ∈ alphabet t) (hb_not : b ∉ alphabet t) (hz_ne_b : z ≠ b) :
    freqOf z (splitLeaf t z z b fa fb) = fa := by
  revert h_cons hz_in hb_not hz_ne_b
  induction t with
  | htLeaf sym f =>
    intro h_cons hz_in hb_not hz_ne_b
    have hz_sym : z = sym := by simpa [alphabet] using hz_in
    subst hz_sym
    simp [splitLeaf, freqOf, hz_ne_b, hz_ne_b.symm, add_zero]
  | htInner l r ihl ihr =>
    intro h_cons hz_in hb_not hz_ne_b
    rcases h_cons with ⟨hcl, hcr, hd⟩
    simp [splitLeaf, freqOf]
    have hz_union : z ∈ alphabet l ∨ z ∈ alphabet r := by simpa [alphabet] using hz_in
    rcases hz_union with (hz_l | hz_r)
    · have hz_not_r : z ∉ alphabet r := Finset.disjoint_left.mp hd hz_l
      rw [splitLeaf_eq_of_z_not_mem r z z b fa fb hz_not_r]
      have hz_freq_r : freqOf z r = 0 := freqOf_eq_zero_of_not_mem z r hz_not_r
      rw [hz_freq_r, add_zero]
      apply ihl hcl hz_l (by intro h; apply hb_not; simp [alphabet, h]) hz_ne_b
    · have hz_not_l : z ∉ alphabet l := Finset.disjoint_right.mp hd hz_r
      rw [splitLeaf_eq_of_z_not_mem l z z b fa fb hz_not_l]
      have hz_freq_l : freqOf z l = 0 := freqOf_eq_zero_of_not_mem z l hz_not_l
      rw [hz_freq_l, zero_add]
      apply ihr hcr hz_r (by intro h; apply hb_not; simp [alphabet, h]) hz_ne_b

private lemma freqOf_splitLeaf_right (t : HuffTree) (z b fa fb : ℕ) (h_cons : consistent t)
    (hz_in : z ∈ alphabet t) (hb_not : b ∉ alphabet t) (hz_ne_b : z ≠ b) :
    freqOf b (splitLeaf t z z b fa fb) = fb := by
  revert h_cons hz_in hb_not hz_ne_b
  induction t with
  | htLeaf sym f =>
    intro h_cons hz_in hb_not hz_ne_b
    have hz_sym : z = sym := by simpa [alphabet] using hz_in
    subst hz_sym
    simp [splitLeaf, freqOf, hz_ne_b, hz_ne_b.symm, add_zero]
  | htInner l r ihl ihr =>
    intro h_cons hz_in hb_not hz_ne_b
    rcases h_cons with ⟨hcl, hcr, hd⟩
    simp [splitLeaf, freqOf]
    have hz_union : z ∈ alphabet l ∨ z ∈ alphabet r := by simpa [alphabet] using hz_in
    rcases hz_union with (hz_l | hz_r)
    · have hz_not_r : z ∉ alphabet r := Finset.disjoint_left.mp hd hz_l
      rw [splitLeaf_eq_of_z_not_mem r z z b fa fb hz_not_r]
      have hb_freq_r : freqOf b r = 0 := freqOf_eq_zero_of_not_mem b r (by intro h; apply hb_not; simp [alphabet, h])
      rw [hb_freq_r, add_zero]
      apply ihl hcl hz_l (by intro h; apply hb_not; simp [alphabet, h]) hz_ne_b
    · have hz_not_l : z ∉ alphabet l := Finset.disjoint_right.mp hd hz_r
      rw [splitLeaf_eq_of_z_not_mem l z z b fa fb hz_not_l]
      have hb_freq_l : freqOf b l = 0 := freqOf_eq_zero_of_not_mem b l (by intro h; apply hb_not; simp [alphabet, h])
      rw [hb_freq_l, zero_add]
      apply ihr hcr hz_r (by intro h; apply hb_not; simp [alphabet, h]) hz_ne_b

private lemma consistent_splitLeaf_v2 (t : HuffTree) (z b fa fb : ℕ) (h_cons : consistent t)
    (hz_in : z ∈ alphabet t) (hb_not : b ∉ alphabet t) (hz_ne_b : z ≠ b) :
    consistent (splitLeaf t z z b fa fb) := by
  revert h_cons hz_in hb_not hz_ne_b
  induction t with
  | htLeaf sym f =>
    intro h_cons hz_in hb_not hz_ne_b
    by_cases hz : sym = z
    · subst hz; simp [splitLeaf, consistent, alphabet, hz_ne_b]
    · simp [splitLeaf, consistent, hz]
  | htInner l r ihl ihr =>
    intro h_cons hz_in hb_not hz_ne_b
    rcases h_cons with ⟨hcl, hcr, hd⟩
    have h_empty := Finset.disjoint_iff_inter_eq_empty.mp hd
    have hb_not_l : b ∉ alphabet l := by intro h; apply hb_not; simp [alphabet, h]
    have hb_not_r : b ∉ alphabet r := by intro h; apply hb_not; simp [alphabet, h]
    have hz_union : z ∈ alphabet l ∨ z ∈ alphabet r := by
      simpa [alphabet] using hz_in
    rcases hz_union with (hz_l | hz_r)
    · have hz_not_r : z ∉ alphabet r := Finset.disjoint_left.mp hd hz_l
      have h_split_r : splitLeaf r z z b fa fb = r :=
        splitLeaf_eq_of_z_not_mem r z z b fa fb hz_not_r
      rw [splitLeaf, consistent, h_split_r]
      have h_l := ihl hcl hz_l hb_not_l hz_ne_b
      have h_disjoint : Disjoint (alphabet (splitLeaf l z z b fa fb)) (alphabet r) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        by_contra h_ne
        have h_nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
        rcases h_nonempty with ⟨s, hs⟩
        rcases Finset.mem_inter.mp hs with ⟨hs_lsplit, hs_r⟩
        by_cases hsb : s = b
        · subst s; apply hb_not; simp [alphabet, hs_r]
        · by_cases hsz : s = z
          · subst s; exact hz_not_r hs_r
          · have hs_l : s ∈ alphabet l :=
              mem_alphabet_splitLeaf_of_ne l z b fa fb s hsz hsb hs_lsplit
            have hi := Finset.mem_inter.mpr ⟨hs_l, hs_r⟩
            rw [h_empty] at hi; simp at hi
      exact And.intro h_l (And.intro hcr h_disjoint)
    · have hz_not_l : z ∉ alphabet l := Finset.disjoint_right.mp hd hz_r
      have h_split_l : splitLeaf l z z b fa fb = l :=
        splitLeaf_eq_of_z_not_mem l z z b fa fb hz_not_l
      rw [splitLeaf, consistent, h_split_l]
      have h_r := ihr hcr hz_r hb_not_r hz_ne_b
      have h_disjoint : Disjoint (alphabet l) (alphabet (splitLeaf r z z b fa fb)) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        by_contra h_ne
        have h_nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
        rcases h_nonempty with ⟨s, hs⟩
        rcases Finset.mem_inter.mp hs with ⟨hs_l, hs_rsplit⟩
        by_cases hsb : s = b
        · subst s; apply hb_not; simp [alphabet, hs_l]
        · by_cases hsz : s = z
          · subst s; exact hz_not_l hs_l
          · have hs_r : s ∈ alphabet r :=
              mem_alphabet_splitLeaf_of_ne r z b fa fb s hsz hsb hs_rsplit
            have hi := Finset.mem_inter.mpr ⟨hs_l, hs_r⟩
            rw [h_empty] at hi; simp at hi
      exact And.intro hcl (And.intro h_r h_disjoint)

lemma splitLeaf_pos_of_pos (t : HuffTree) (z b fa fb : ℕ)
    (h_cons : consistent t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b)
    (h_fa_pos : fa > 0) (h_fb_pos : fb > 0)
    (h_pos : ∀ s ∈ alphabet t, freqOf s t > 0) :
    ∀ s ∈ alphabet (splitLeaf t z z b fa fb),
      freqOf s (splitLeaf t z z b fa fb) > 0 := by
  intro s hs
  by_cases hsz : s = z
  · subst s
    rw [freqOf_splitLeaf_left t z b fa fb h_cons h_z_in hb_not_mem hz_ne_b]
    exact h_fa_pos
  · by_cases hsb : s = b
    · subst s
      rw [freqOf_splitLeaf_right t z b fa fb h_cons h_z_in hb_not_mem hz_ne_b]
      exact h_fb_pos
    · rw [freqOf_splitLeaf_of_ne t z b fa fb s hsz hsb]
      exact h_pos s (mem_alphabet_splitLeaf_of_ne t z b fa fb s hsz hsb hs)

structure SplitFreqCandidate (t base tree : HuffTree) (z b fa fb : ℕ) where
  cons : consistent tree
  freq_rel : ∀ s, freqOf s tree = freqOf s (splitLeaf t z z b fa fb)
  cost_le : (cost tree : ℤ) ≤ (cost base : ℤ)

namespace SplitFreqCandidate

theorem ofBase {t base : HuffTree} {z b fa fb : ℕ}
    (h_cons : consistent base)
    (h_freq_rel : ∀ s, freqOf s base = freqOf s (splitLeaf t z z b fa fb)) :
    SplitFreqCandidate t base base z b fa fb :=
  { cons := h_cons
    freq_rel := h_freq_rel
    cost_le := le_refl _ }

theorem ofExchange {t base w : HuffTree} {z b fa fb a x : ℕ}
    (h_ne : a ≠ x) (ha_in : a ∈ alphabet w) (hx_in : x ∈ alphabet w)
    (h_cons_w : consistent w)
    (h_freq_rel_w : ∀ s, freqOf s w = freqOf s (splitLeaf t z z b fa fb))
    (h_cost_le : (cost (swapFreqs a x (swapLeaves a x w)) : ℤ) ≤ (cost base : ℤ)) :
    SplitFreqCandidate t base (swapFreqs a x (swapLeaves a x w)) z b fa fb :=
  { cons := by
      dsimp [swapFreqs]
      apply consistent_replaceFreq x _ (replaceFreq a _ (swapLeaves a x w))
      apply consistent_replaceFreq a _ (swapLeaves a x w)
      exact consistent_swapLeaves a x w h_cons_w
    freq_rel := by
      intro s
      rw [freqOf_exchangeLeaf w a x s h_ne ha_in hx_in h_cons_w]
      exact h_freq_rel_w s
    cost_le := h_cost_le }

theorem freq_left {t base tree : HuffTree} {z b fa fb : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_cons_t : consistent t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b) :
    freqOf z tree = fa := by
  rw [C.freq_rel z]
  exact freqOf_splitLeaf_left t z b fa fb h_cons_t h_z_in hb_not_mem hz_ne_b

theorem freq_right {t base tree : HuffTree} {z b fa fb : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_cons_t : consistent t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b) :
    freqOf b tree = fb := by
  rw [C.freq_rel b]
  exact freqOf_splitLeaf_right t z b fa fb h_cons_t h_z_in hb_not_mem hz_ne_b

theorem freq_left_le_of_min {t base tree : HuffTree} {z b fa fb s : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_cons_t : consistent t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b)
    (h_fa_min : ∀ s ∈ alphabet t, fa ≤ freqOf s t)
    (h_s_in_t : s ∈ alphabet t) (h_s_ne_z : s ≠ z) (h_s_ne_b : s ≠ b) :
    freqOf z tree ≤ freqOf s tree := by
  rw [C.freq_left h_cons_t h_z_in hb_not_mem hz_ne_b]
  rw [C.freq_rel s, freqOf_splitLeaf_of_ne t z b fa fb s h_s_ne_z h_s_ne_b]
  exact h_fa_min s h_s_in_t

theorem freq_right_le_of_min {t base tree : HuffTree} {z b fa fb s : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_cons_t : consistent t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b)
    (h_fb_min : ∀ s ∈ alphabet t, s ≠ z → fb ≤ freqOf s t)
    (h_s_in_t : s ∈ alphabet t) (h_s_ne_z : s ≠ z) (h_s_ne_b : s ≠ b) :
    freqOf b tree ≤ freqOf s tree := by
  rw [C.freq_right h_cons_t h_z_in hb_not_mem hz_ne_b]
  rw [C.freq_rel s, freqOf_splitLeaf_of_ne t z b fa fb s h_s_ne_z h_s_ne_b]
  exact h_fb_min s h_s_in_t h_s_ne_z

theorem freq_eq_zero_of_not_mem {t base tree : HuffTree} {z b fa fb s : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_s_not_mem : s ∉ alphabet t) (h_s_ne_z : s ≠ z) (h_s_ne_b : s ≠ b) :
    freqOf s tree = 0 := by
  rw [C.freq_rel s, freqOf_splitLeaf_of_ne t z b fa fb s h_s_ne_z h_s_ne_b]
  exact freqOf_eq_zero_of_not_mem s t h_s_not_mem

theorem freq_left_le_right {t base tree : HuffTree} {z b fa fb : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_cons_t : consistent t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b)
    (h_fa_le_fb : fa ≤ fb) :
    freqOf z tree ≤ freqOf b tree := by
  rw [C.freq_left h_cons_t h_z_in hb_not_mem hz_ne_b,
    C.freq_right h_cons_t h_z_in hb_not_mem hz_ne_b]
  exact h_fa_le_fb

theorem sameFreqs_prune_zero {t base tree : HuffTree} {z b fa fb keep drop : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_sib : areSiblings keep drop tree) (h_ne : keep ≠ drop)
    (h_drop_zero : freqOf drop tree = 0) :
    sameFreqs (splitLeaf t z z b fa fb)
      (mergePair keep drop keep (freqOf keep tree + freqOf drop tree) tree) := by
  intro s
  rw [freqOf_mergePair_same_sibling tree drop keep s h_sib C.cons h_ne,
    h_drop_zero, add_zero]
  by_cases h_keep : s = keep
  · subst s
    simpa using (C.freq_rel keep).symm
  · by_cases h_drop : s = drop
    · subst s
      simpa [h_ne.symm, h_drop_zero] using (C.freq_rel drop).symm
    · simp [h_keep, h_drop, (C.freq_rel s).symm]

end SplitFreqCandidate

structure SplitMergeCandidate (t base : HuffTree) (z b fa fb : ℕ) where
  tree : HuffTree
  freq : SplitFreqCandidate t base tree z b fa fb
  sibling : areSiblings z b tree

theorem merge_split_siblings_cost_bound (t v v' : HuffTree) (z b fa fb : ℕ)
    (h_opt_t : ∀ u, consistent u → sameFreqs t u → cost t ≤ cost u)
    (hb_fb_t : freqOf b t = 0) (hz_ne_b : z ≠ b)
    (h_sum : freqOf z t = fa + fb)
    (h_sib_zb : areSiblings z b v') (h_cons_v' : consistent v')
    (h_fz_v' : freqOf z v' = fa) (h_fb_v' : freqOf b v' = fb)
    (h_freq_rel : ∀ s, freqOf s v' = freqOf s (splitLeaf t z z b fa fb))
    (h_cost_v'_le : (cost v' : ℤ) ≤ (cost v : ℤ)) :
    cost t + fa + fb ≤ cost v := by
  let v'' := mergePair z b z (fa + fb) v'
  have h_cost_v'' : (cost v'' : ℤ) = (cost v' : ℤ) - (fa : ℤ) - (fb : ℤ) :=
    cost_mergePair_of_areSiblings v' z b z fa fb h_sib_zb h_cons_v'
      hz_ne_b h_fz_v' h_fb_v' rfl
  have h_cons_v'' : consistent v'' :=
    consistent_mergePair_same_sibling v' b z (fa + fb) h_sib_zb h_cons_v' hz_ne_b
  have h_sameFreqs_v'' : sameFreqs t v'' := by
    intro s
    dsimp [v'']
    have h_freq_sum : freqOf z v' + freqOf b v' = fa + fb := by
      rw [h_fz_v', h_fb_v']
    have h_lemma := freqOf_mergePair_same_sibling v' b z s h_sib_zb h_cons_v' hz_ne_b
    have h_merge_eq : freqOf s (mergePair z b z (fa + fb) v') =
        freqOf s (mergePair z b z (freqOf z v' + freqOf b v') v') := by
      rw [← h_freq_sum]
    rw [h_merge_eq, h_lemma]
    split_ifs with hsz hsb
    · rw [hsz, h_fz_v', h_fb_v', h_sum]
    · rw [hsb, hb_fb_t]
    · rw [h_freq_rel s, freqOf_splitLeaf_of_ne t z b fa fb s hsz hsb]
  have h_t_le : (cost t : ℤ) ≤ (cost v'' : ℤ) := by
    exact_mod_cast h_opt_t v'' h_cons_v'' h_sameFreqs_v''
  exact_mod_cast (show (cost t : ℤ) + (fa : ℤ) + (fb : ℤ) ≤ (cost v : ℤ) from by
    linarith)

namespace SplitMergeCandidate

def ofBase {t base : HuffTree} {z b fa fb : ℕ}
    (h_sib : areSiblings z b base) (h_cons : consistent base)
    (h_freq_rel : ∀ s, freqOf s base = freqOf s (splitLeaf t z z b fa fb)) :
    SplitMergeCandidate t base z b fa fb where
  tree := base
  freq := SplitFreqCandidate.ofBase h_cons h_freq_rel
  sibling := h_sib

def ofExchange {t base w : HuffTree} {z b fa fb a x : ℕ}
    (h_ne : a ≠ x) (ha_in : a ∈ alphabet w) (hx_in : x ∈ alphabet w)
    (h_cons_w : consistent w)
    (h_freq_rel_w : ∀ s, freqOf s w = freqOf s (splitLeaf t z z b fa fb))
    (h_sib : areSiblings z b (swapFreqs a x (swapLeaves a x w)))
    (h_cost_le : (cost (swapFreqs a x (swapLeaves a x w)) : ℤ) ≤ (cost base : ℤ)) :
    SplitMergeCandidate t base z b fa fb where
  tree := swapFreqs a x (swapLeaves a x w)
  freq := SplitFreqCandidate.ofExchange h_ne ha_in hx_in h_cons_w h_freq_rel_w h_cost_le
  sibling := h_sib

def ofFreqCandidate {t base tree : HuffTree} {z b fa fb : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_sib : areSiblings z b tree) :
    SplitMergeCandidate t base z b fa fb where
  tree := tree
  freq := C
  sibling := h_sib

theorem cost_bound {t base : HuffTree} {z b fa fb : ℕ}
    (C : SplitMergeCandidate t base z b fa fb)
    (h_opt_t : ∀ u, consistent u → sameFreqs t u → cost t ≤ cost u)
    (h_cons_t : consistent t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b)
    (hb_fb_t : freqOf b t = 0) (h_sum : freqOf z t = fa + fb) :
    cost t + fa + fb ≤ cost base :=
  merge_split_siblings_cost_bound t base C.tree z b fa fb h_opt_t hb_fb_t hz_ne_b
    h_sum C.sibling C.freq.cons
    (C.freq.freq_left h_cons_t h_z_in hb_not_mem hz_ne_b)
    (C.freq.freq_right h_cons_t h_z_in hb_not_mem hz_ne_b)
    C.freq.freq_rel C.freq.cost_le

end SplitMergeCandidate

namespace SplitFreqCandidate

def exchangeToMerge {t base tree : HuffTree} {z b fa fb a x : ℕ}
    (C : SplitFreqCandidate t base tree z b fa fb)
    (h_ne : a ≠ x) (ha_in : a ∈ alphabet tree) (hx_in : x ∈ alphabet tree)
    (h_sib : areSiblings z b (swapFreqs a x (swapLeaves a x tree)))
    (h_cost_step : (cost (swapFreqs a x (swapLeaves a x tree)) : ℤ) ≤ (cost tree : ℤ)) :
    SplitMergeCandidate t base z b fa fb :=
  SplitMergeCandidate.ofFreqCandidate
    (SplitFreqCandidate.ofExchange (t := t) (base := base) (w := tree)
      (z := z) (b := b) (fa := fa) (fb := fb) (a := a) (x := x)
      h_ne ha_in hx_in C.cons C.freq_rel (le_trans h_cost_step C.cost_le))
    h_sib

end SplitFreqCandidate

theorem optimum_splitLeaf (t : HuffTree) (z b fa fb : ℕ)
    (h_opt : optimum t) (h_z_in : z ∈ alphabet t)
    (hb_not_mem : b ∉ alphabet t) (hz_ne_b : z ≠ b)
    (h_fa_pos : fa > 0) (h_fb_pos : fb > 0) (h_fa_le_fb : fa ≤ fb)
    (h_fa_min : ∀ s ∈ alphabet t, fa ≤ freqOf s t)
    (h_fb_min : ∀ s ∈ alphabet t, s ≠ z → fb ≤ freqOf s t)
    (h_sum : freqOf z t = fa + fb) :
    optimum (splitLeaf t z z b fa fb) := by
  rcases h_opt with ⟨h_cons_t, h_pos_t, h_opt_t⟩
  have hb_fb_t : freqOf b t = 0 := freqOf_eq_zero_of_not_mem b t hb_not_mem
  refine ⟨consistent_splitLeaf_v2 t z b fa fb h_cons_t h_z_in hb_not_mem hz_ne_b,
    splitLeaf_pos_of_pos t z b fa fb h_cons_t h_z_in hb_not_mem hz_ne_b
      h_fa_pos h_fb_pos h_pos_t, ?_⟩
  intro u h_cons_u h_sameFreqs
  rw [cost_splitLeaf_eq t z z b fa fb h_cons_t h_z_in h_sum]
  let P (n : ℕ) : Prop := ∀ (v : HuffTree), nodeCount v = n → consistent v →
    sameFreqs (splitLeaf t z z b fa fb) v → cost t + fa + fb ≤ cost v
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n IH v hn h_cons_v h_sameFreqs_v
    have Cbase : SplitFreqCandidate t v v z b fa fb :=
      SplitFreqCandidate.ofBase h_cons_v (fun s => (h_sameFreqs_v s).symm)
    have h_freq_z_le_b_v : freqOf z v ≤ freqOf b v :=
      Cbase.freq_left_le_right h_cons_t h_z_in hb_not_mem hz_ne_b h_fa_le_fb
    have hz_in_v : z ∈ alphabet v :=
      mem_alphabet_of_freq_pos z v
        (by simpa [Cbase.freq_left h_cons_t h_z_in hb_not_mem hz_ne_b] using h_fa_pos)
    have hb_in_v : b ∈ alphabet v :=
      mem_alphabet_of_freq_pos b v
        (by simpa [Cbase.freq_right h_cons_t h_z_in hb_not_mem hz_ne_b] using h_fb_pos)
    have h_height : height v ≥ 1 :=
      height_pos_of_distinct_mem v hz_in_v hb_in_v hz_ne_b
    have h_dsp_sib : areSiblings (deepestSiblingPair v).1 (deepestSiblingPair v).2 v :=
      deepestSiblingPair_areSiblings v h_cons_v h_height
    set x := (deepestSiblingPair v).1 with hx_def
    set y := (deepestSiblingPair v).2 with hy_def
    have h_dsp_sib_xy : areSiblings x y v := by simpa [hx_def, hy_def] using h_dsp_sib
    have hx_in : x ∈ alphabet v := by simpa [hx_def] using deepestSiblingPair_mem1 v
    have hy_in : y ∈ alphabet v := by simpa [hy_def] using deepestSiblingPair_mem2 v
    rcases deepestSiblingPair_depth v h_cons_v with ⟨h_depth_x_raw, h_depth_y_raw⟩
    have h_depth_x : (depthOf x v).getD 0 = height v := by simpa [hx_def] using h_depth_x_raw
    have h_depth_y : (depthOf y v).getD 0 = height v := by simpa [hy_def] using h_depth_y_raw
    have h_depth_le_x (s : ℕ) : (depthOf s v).getD 0 ≤ (depthOf x v).getD 0 := by
      rw [h_depth_x]; exact depthOf_getD_le_height v s
    have h_depth_le_y (s : ℕ) : (depthOf s v).getD 0 ≤ (depthOf y v).getD 0 := by
      rw [h_depth_y]; exact depthOf_getD_le_height v s
    have h_depth_z_le_dx : (depthOf z v).getD 0 ≤ (depthOf x v).getD 0 := h_depth_le_x z
    have h_depth_b_le_dy : (depthOf b v).getD 0 ≤ (depthOf y v).getD 0 := h_depth_le_y b
    have h_depth_b_le_dx : (depthOf b v).getD 0 ≤ (depthOf x v).getD 0 := h_depth_le_x b
    have h_merge_conclude (C : SplitMergeCandidate t v z b fa fb) :
        cost t + fa + fb ≤ cost v :=
      C.cost_bound h_opt_t h_cons_t h_z_in hb_not_mem hz_ne_b hb_fb_t h_sum
    have h_exchange_leaf_conclude {tree : HuffTree} {a x' : ℕ}
        (C : SplitFreqCandidate t v tree z b fa fb)
        (h_ne : a ≠ x') (ha_in : a ∈ alphabet tree) (hx_in' : x' ∈ alphabet tree)
        (h_freq : freqOf a tree ≤ freqOf x' tree)
        (h_depth : (depthOf a tree).getD 0 ≤ (depthOf x' tree).getD 0)
        (h_sib_swap : areSiblings z b (swapLeaves a x' tree)) :
        cost t + fa + fb ≤ cost v := by
      exact h_merge_conclude
        (C.exchangeToMerge h_ne ha_in hx_in'
          (areSiblings_swapFreqs_preserved (swapLeaves a x' tree) z b a x' h_sib_swap)
          (cost_exchangeLeaf_le tree a x' C.cons ha_in hx_in' h_ne h_freq h_depth))
    have h_exchange_sibling_order_conclude {tree : HuffTree}
        (C : SplitFreqCandidate t v tree z b fa fb)
        (h_sib_bz : areSiblings b z tree)
        (h_depth : (depthOf z tree).getD 0 ≤ (depthOf b tree).getD 0) :
        cost t + fa + fb ≤ cost v := by
      exact h_exchange_leaf_conclude C hz_ne_b (areSiblings_mem_alphabet h_sib_bz).2
        (areSiblings_mem_alphabet h_sib_bz).1
        (C.freq_left_le_right h_cons_t h_z_in hb_not_mem hz_ne_b h_fa_le_fb)
        h_depth
        (by
          simpa [swapLeaves_comm b z tree] using
            areSiblings_swap_siblings h_sib_bz (Ne.symm hz_ne_b))
    have h_exchange_leaf_candidate {a x' : ℕ}
        (h_ne : a ≠ x') (ha_in : a ∈ alphabet v) (hx_in' : x' ∈ alphabet v)
        (h_freq : freqOf a v ≤ freqOf x' v)
        (h_depth : (depthOf a v).getD 0 ≤ (depthOf x' v).getD 0) :
        SplitFreqCandidate t v (swapFreqs a x' (swapLeaves a x' v)) z b fa fb :=
      SplitFreqCandidate.ofExchange (t := t) (base := v) (w := v)
        (z := z) (b := b) (fa := fa) (fb := fb) (a := a) (x := x')
        h_ne ha_in hx_in' h_cons_v (fun s => (h_sameFreqs_v s).symm)
        (cost_exchangeLeaf_le v a x' h_cons_v ha_in hx_in' h_ne h_freq h_depth)
    have h_prune_zero_candidate_conclude {w : HuffTree} {keep drop : ℕ}
        (C : SplitFreqCandidate t v w z b fa fb)
        (h_nodes_w : nodeCount w = nodeCount v)
        (h_sib : areSiblings keep drop w) (h_ne : keep ≠ drop)
        (h_drop_zero : freqOf drop w = 0) :
        cost t + fa + fb ≤ cost v := by
      let v_pruned := mergePair keep drop keep (freqOf keep w + freqOf drop w) w
      have h_sameFreqs_pruned : sameFreqs (splitLeaf t z z b fa fb) v_pruned := by
        simpa [v_pruned] using C.sameFreqs_prune_zero h_sib h_ne h_drop_zero
      have h_cost_pruned_le_v : cost v_pruned ≤ cost v := by
        have h_cost_int : (cost v_pruned : ℤ) = (cost w : ℤ) - (freqOf keep w : ℤ) := by
          have h := cost_mergePair_of_areSiblings w keep drop keep (freqOf keep w) 0
            (fz := freqOf keep w + freqOf drop w)
            h_sib C.cons h_ne rfl h_drop_zero (by rw [h_drop_zero, add_zero])
          simpa [v_pruned, h_drop_zero, add_zero] using h
        have h_goal : (cost v_pruned : ℤ) ≤ (cost v : ℤ) := by
          have h_fk_nonneg : (0 : ℤ) ≤ freqOf keep w := by exact_mod_cast Nat.zero_le (freqOf keep w)
          have h_cost_w_le_v := C.cost_le
          linarith
        exact_mod_cast h_goal
      have h_nodeCount_pruned_lt : nodeCount v_pruned < n := by
        simpa [v_pruned, h_nodes_w, hn] using
          nodeCount_mergePair_lt_of_areSiblings w keep drop keep
            (freqOf keep w + freqOf drop w) h_sib h_ne
      have h_cons_pruned : consistent v_pruned := by
        simpa [v_pruned] using
          consistent_mergePair_same_sibling w drop keep
            (freqOf keep w + freqOf drop w) h_sib C.cons h_ne
      exact le_trans
        (IH (nodeCount v_pruned) h_nodeCount_pruned_lt v_pruned rfl h_cons_pruned h_sameFreqs_pruned)
        h_cost_pruned_le_v
    have h_resolve_z_pair_conclude {tree : HuffTree} {y' : ℕ}
        (C : SplitFreqCandidate t v tree z b fa fb) (h_nodes_tree : nodeCount tree = nodeCount v)
        (h_sib_zy : areSiblings z y' tree)
        (h_depth : (depthOf b tree).getD 0 ≤ (depthOf y' tree).getD 0) :
        cost t + fa + fb ≤ cost v := by
      by_cases hy'_eq_b : y' = b
      · rw [hy'_eq_b] at h_sib_zy
        exact h_merge_conclude (SplitMergeCandidate.ofFreqCandidate C h_sib_zy)
      · have hz_ne_y' : z ≠ y' := areSiblings_ne tree z y' C.cons h_sib_zy
        by_cases hy'_in_t : y' ∈ alphabet t
        · have hb_in_tree : b ∈ alphabet tree :=
            mem_alphabet_of_freq_pos b tree
              (by simpa [C.freq_right h_cons_t h_z_in hb_not_mem hz_ne_b] using h_fb_pos)
          have h_freq_b_y' : freqOf b tree ≤ freqOf y' tree :=
            C.freq_right_le_of_min h_cons_t h_z_in hb_not_mem hz_ne_b
              h_fb_min hy'_in_t (Ne.symm hz_ne_y') hy'_eq_b
          exact h_exchange_leaf_conclude C (Ne.symm hy'_eq_b) hb_in_tree
            (areSiblings_mem_alphabet h_sib_zy).2
            h_freq_b_y' h_depth
            (areSiblings_exchangeRight tree z b y' h_sib_zy (Ne.symm hz_ne_b)
              (Ne.symm hy'_eq_b) hz_ne_y')
        · exact h_prune_zero_candidate_conclude C h_nodes_tree h_sib_zy hz_ne_y'
            (C.freq_eq_zero_of_not_mem hy'_in_t (Ne.symm hz_ne_y') hy'_eq_b)
    have h_exchange_z_then_resolve {x' y' : ℕ}
        (h_ne : z ≠ x') (hx'_in : x' ∈ alphabet v) (h_sib_x'y' : areSiblings x' y' v)
        (hz_ne_y' : z ≠ y') (hx'_ne_y' : x' ≠ y')
        (h_freq : freqOf z v ≤ freqOf x' v)
        (h_depth_exchange : (depthOf z v).getD 0 ≤ (depthOf x' v).getD 0)
        (h_depth_resolve : (depthOf b (swapFreqs z x' (swapLeaves z x' v))).getD 0 ≤
          (depthOf y' (swapFreqs z x' (swapLeaves z x' v))).getD 0) :
        cost t + fa + fb ≤ cost v := by
      let v1 := swapFreqs z x' (swapLeaves z x' v)
      exact h_resolve_z_pair_conclude
        (by simpa [v1] using h_exchange_leaf_candidate h_ne hz_in_v hx'_in h_freq h_depth_exchange)
        (by simpa [v1] using nodeCount_exchangeLeaf_eq z x' v)
        (by
          simpa [v1] using areSiblings_swapFreqs_preserved (swapLeaves z x' v) z y' z x'
            (areSiblings_exchangeLeft v z x' y' h_sib_x'y' h_ne hz_ne_y' hx'_ne_y'))
        (by simpa [v1] using h_depth_resolve)
    by_cases hxz : x = z
    ·
      rw [hxz] at h_dsp_sib_xy hx_in h_depth_x h_depth_z_le_dx h_depth_b_le_dx
      exact h_resolve_z_pair_conclude Cbase rfl h_dsp_sib_xy h_depth_b_le_dy
    · by_cases hxb : x = b
      ·
        rw [hxb] at h_dsp_sib_xy hx_in h_depth_x h_depth_z_le_dx h_depth_b_le_dx
        have hb_ne_y : b ≠ y := areSiblings_ne v b y h_cons_v h_dsp_sib_xy
        by_cases hyz : y = z
        ·
          rw [hyz] at h_dsp_sib_xy
          exact h_exchange_sibling_order_conclude Cbase h_dsp_sib_xy h_depth_z_le_dx
        ·
          exact h_exchange_z_then_resolve hz_ne_b hb_in_v h_dsp_sib_xy (Ne.symm hyz) hb_ne_y
            h_freq_z_le_b_v h_depth_z_le_dx
            (by
              simpa [depthOf_swapFreqs_eq, depthOf_swapLeaves_at_b z b v hz_ne_b,
                depthOf_swapLeaves_of_not_is z b y v hyz (Ne.symm hb_ne_y)]
                using h_depth_le_y z)
      ·
        have hx_ne_z : x ≠ z := hxz
        have hx_ne_b : x ≠ b := hxb
        have hz_ne_x : z ≠ x := Ne.symm hxz
        have hb_ne_x : b ≠ x := Ne.symm hxb
        have hx_ne_y : x ≠ y := areSiblings_ne v x y h_cons_v h_dsp_sib_xy
        have h_prune_absent_x_sibling_conclude {keep : ℕ}
            (h_sib : areSiblings x keep v) (h_ne : x ≠ keep)
            (h_keep_in : keep ∈ alphabet v) (hx_not_t : x ∉ alphabet t)
            (h_keep_depth : (depthOf keep v).getD 0 = height v) :
            cost t + fa + fb ≤ cost v := by
          let v_pre := swapFreqs x keep (swapLeaves x keep v)
          have h_zero_x : freqOf x v = 0 :=
            Cbase.freq_eq_zero_of_not_mem hx_not_t hx_ne_z hx_ne_b
          exact h_prune_zero_candidate_conclude
            (by
              simpa [v_pre] using h_exchange_leaf_candidate h_ne hx_in h_keep_in
                (by rw [h_zero_x]; omega) (by rw [h_depth_x, h_keep_depth]))
            (by simpa [v_pre] using nodeCount_exchangeLeaf_eq x keep v)
            (by
              simpa [v_pre] using areSiblings_swapFreqs_preserved (swapLeaves x keep v)
                keep x x keep (areSiblings_swap_siblings h_sib h_ne))
            (Ne.symm h_ne)
            (by
              simpa [v_pre, h_zero_x] using
                freqOf_exchangeLeaf v x keep x h_ne hx_in h_keep_in h_cons_v)
        by_cases hyz : y = z
        ·
          rw [hyz] at h_dsp_sib_xy
          by_cases hx_in_t' : x ∈ alphabet t
          ·
            have h_freq_b_x : freqOf b v ≤ freqOf x v :=
              Cbase.freq_right_le_of_min h_cons_t h_z_in hb_not_mem hz_ne_b
                h_fb_min hx_in_t' hx_ne_z hx_ne_b
            let v1 := swapFreqs b x (swapLeaves b x v)
            have h_sib_v1 : areSiblings b z v1 :=
              areSiblings_swapFreqs_preserved (swapLeaves b x v) b z b x
                (areSiblings_exchangeLeft v b x z h_dsp_sib_xy hb_ne_x (Ne.symm hz_ne_b) hx_ne_z)
            have C1 : SplitFreqCandidate t v v1 z b fa fb :=
              h_exchange_leaf_candidate hb_ne_x hb_in_v hx_in
                h_freq_b_x h_depth_b_le_dx
            exact h_exchange_sibling_order_conclude C1 h_sib_v1
              (by
                simpa [v1, depthOf_swapFreqs_eq, depthOf_swapLeaves_at_a b x v hb_ne_x,
                  depthOf_swapLeaves_of_not_is b x z v hz_ne_b (Ne.symm hx_ne_z)]
                  using h_depth_z_le_dx)
          ·
            exact h_prune_absent_x_sibling_conclude h_dsp_sib_xy hx_ne_z
              hz_in_v hx_in_t' (by rw [← hyz]; exact h_depth_y)
        ·
          by_cases hx_in_t : x ∈ alphabet t
          ·
            have h_freq_z_x : freqOf z v ≤ freqOf x v :=
              Cbase.freq_left_le_of_min h_cons_t h_z_in hb_not_mem hz_ne_b
                h_fa_min hx_in_t hx_ne_z hx_ne_b
            exact h_exchange_z_then_resolve hz_ne_x hx_in h_dsp_sib_xy (Ne.symm hyz) hx_ne_y
              h_freq_z_x h_depth_z_le_dx
              (by
                simpa [depthOf_getD_exchange_of_ne z x b v (Ne.symm hz_ne_b) hb_ne_x,
                  depthOf_getD_exchange_of_ne z x y v hyz (Ne.symm hx_ne_y)]
                  using h_depth_b_le_dy)
          ·
            exact h_prune_absent_x_sibling_conclude h_dsp_sib_xy hx_ne_y
              hy_in hx_in_t h_depth_y

  have h_node : P (nodeCount u) := Nat.strong_induction_on (nodeCount u) hP
  exact h_node u rfl h_cons_u h_sameFreqs

/-!
### Split-leaf optimality interface

The long exchange proof above is intentionally hidden behind the following
small certificate.  The rest of the Huffman proof only needs to know that a
merged symbol {lit}`z` can be split into two positive minimum-frequency symbols
{lit}`z` and {lit}`b`, with the old frequency of {lit}`z` equal to their sum.
-/

structure SplitLeafOptimalitySpec (t : HuffTree) (z b fa fb : ℕ) where
  z_mem : z ∈ alphabet t
  b_fresh : b ∉ alphabet t
  sym_ne : z ≠ b
  fa_pos : fa > 0
  fb_pos : fb > 0
  fa_le_fb : fa ≤ fb
  fa_min : ∀ s ∈ alphabet t, fa ≤ freqOf s t
  fb_min : ∀ s ∈ alphabet t, s ≠ z → fb ≤ freqOf s t
  freq_z : freqOf z t = fa + fb

theorem split_leaf_preserves_optimum {t : HuffTree} {z b fa fb : ℕ}
    (S : SplitLeafOptimalitySpec t z b fa fb) (h_opt : optimum t) :
    optimum (splitLeaf t z z b fa fb) :=
  optimum_splitLeaf t z b fa fb h_opt S.z_mem S.b_fresh S.sym_ne
    S.fa_pos S.fb_pos S.fa_le_fb S.fa_min S.fb_min S.freq_z

/-! ## Bundled forest invariant and greedy-step certificate -/

structure Forest where
  trees : List HuffTree
  sorted : forest_sorted trees
  consistent : forest_consistent trees
  allLeaves : ∀ t ∈ trees, height t = 0
  allPos : ∀ t ∈ trees, rootFreq t > 0
  nonempty : trees ≠ []

namespace Forest

def length (F : Forest) : ℕ := F.trees.length

/-- Greedy step on a raw list that already satisfies the forest invariant. -/
def mergeCheapestList (ts : List HuffTree)
    (h_sorted : forest_sorted ts)
    (h_cons : forest_consistent ts)
    (h_leaves : ∀ t ∈ ts, height t = 0)
    (h_pos : ∀ t ∈ ts, rootFreq t > 0)
    (h : ts.length ≥ 2) : Forest :=
  match h_eq : ts with
  | [] => by simp at h
  | [t] => by simp at h
  | t1 :: t2 :: rest =>
      have h1 : height t1 = 0 := h_leaves t1 (by simp)
      have h2 : height t2 = 0 := h_leaves t2 (by simp)
      match h1_eq : t1, h2_eq : t2 with
      | htLeaf sa fa, htLeaf sb fb =>
          let tNew := htLeaf sa (fa + fb)
          {
            trees := insortTree tNew rest,
            sorted := forest_sorted_insortTree_of_sorted tNew rest
              (forest_sorted_tail (htLeaf sb fb) rest
                (forest_sorted_tail (htLeaf sa fa) (htLeaf sb fb :: rest) h_sorted)),
            consistent := by
              have h_fresh : ∀ t ∈ rest, sa ∉ alphabet t := by
                intro t ht
                rw [forest_consistent_cons_iff] at h_cons
                have hdisj : Disjoint (alphabet (htLeaf sa fa)) (alphabet t) :=
                  h_cons.2.2 t (by simp [ht])
                simp [alphabet] at hdisj
                exact hdisj
              exact forest_consistent_insortTree_fresh sa (fa + fb) rest h_fresh
                (forest_consistent_tail (htLeaf sb fb) rest
                  (forest_consistent_tail (htLeaf sa fa) (htLeaf sb fb :: rest) h_cons)),
            allLeaves := forall_mem_insortTree (P := λ t => height t = 0)
              (by simp [tNew, height]) (fun t ht => h_leaves t (by simp [ht])),
            allPos := by
              have h_pos_new : rootFreq tNew > 0 := by
                have h_fa := h_pos (htLeaf sa fa) (by simp)
                have h_fb := h_pos (htLeaf sb fb) (by simp)
                simp [rootFreq, tNew] at h_fa h_fb ⊢
                omega
              exact forall_mem_insortTree (P := λ t => rootFreq t > 0)
                h_pos_new (fun t ht => h_pos t (by simp [ht])),
            nonempty := insortTree_ne_nil tNew rest
          }
      | htInner l r, _ => by simp [height] at h1
      | _, htInner l r => by simp [height] at h2

/-- The bundled greedy reduction step. -/
def mergeCheapest (F : Forest) (h : F.length ≥ 2) : Forest :=
  mergeCheapestList F.trees F.sorted F.consistent F.allLeaves F.allPos (by simpa [length] using h)

/-! ### Specification of {name}`mergeCheapest` -/

lemma mergeCheapestList_spec (ts : List HuffTree)
    (h_sorted : forest_sorted ts)
    (h_cons : forest_consistent ts)
    (h_leaves : ∀ t ∈ ts, height t = 0)
    (h_pos : ∀ t ∈ ts, rootFreq t > 0)
    (h : ts.length ≥ 2) :
    ∃ sa fa sb fb rest,
      ts = htLeaf sa fa :: htLeaf sb fb :: rest ∧
      (mergeCheapestList ts h_sorted h_cons h_leaves h_pos h).trees =
        insortTree (htLeaf sa (fa + fb)) rest := by
  cases ts with
  | nil => simp at h
  | cons t1 ts1 =>
      cases ts1 with
      | nil => simp at h
      | cons t2 rest =>
          rcases height_eq_zero_iff t1 |>.mp (h_leaves t1 (by simp)) with ⟨sa, fa, h1'⟩
          rcases height_eq_zero_iff t2 |>.mp (h_leaves t2 (by simp)) with ⟨sb, fb, h2'⟩
          subst h1' h2'
          use sa, fa, sb, fb, rest
          constructor
          · rfl
          · simp [mergeCheapestList]

lemma mergeCheapest_spec (F : Forest) (h : F.length ≥ 2) :
    ∃ sa fa sb fb ts,
      F.trees = htLeaf sa fa :: htLeaf sb fb :: ts ∧
      (F.mergeCheapest h).trees = insortTree (htLeaf sa (fa + fb)) ts ∧
      sa ≠ sb ∧
      (∀ t ∈ ts, sa ∉ alphabet t) := by
  rcases mergeCheapestList_spec F.trees F.sorted F.consistent F.allLeaves F.allPos
    (by simpa [length] using h) with ⟨sa, fa, sb, fb, ts, h_eq, h_eq'⟩
  have h_cons_parts :=
    (forest_consistent_cons_iff (htLeaf sa fa) (htLeaf sb fb :: ts)).mp
      (by simpa [h_eq] using F.consistent)
  have h_ne : sa ≠ sb := by
    simpa [alphabet] using h_cons_parts.2.2 (htLeaf sb fb) (by simp)
  have h_fresh : ∀ t ∈ ts, sa ∉ alphabet t := by
    intro t ht
    simpa [alphabet] using h_cons_parts.2.2 t (by simp [ht])
  exact ⟨sa, fa, sb, fb, ts, h_eq, h_eq', h_ne, h_fresh⟩

lemma mergeCheapest_length_lt (F : Forest) (h : F.length ≥ 2) :
    (F.mergeCheapest h).length < F.length := by
  rcases mergeCheapest_spec F h with ⟨sa, fa, sb, fb, ts, h_eq, h_eq', _, _⟩
  simp [length, h_eq', h_eq, insortTree_length]

/--
Named certificate for the facts produced by one bundled greedy step.
It packages the exact hypotheses needed by {name}`optimum_splitLeaf` plus the final
commutation equality back to the original forest.
-/
structure MergeCheapestSplitReady (F : Forest) (h : F.length ≥ 2) where
  sa : ℕ
  fa : ℕ
  sb : ℕ
  fb : ℕ
  fa_pos : fa > 0
  fb_pos : fb > 0
  sym_ne : sa ≠ sb
  sa_mem : sa ∈ alphabet (huffman (F.mergeCheapest h).trees)
  sb_not_mem : sb ∉ alphabet (huffman (F.mergeCheapest h).trees)
  freq_sa : freqOf sa (huffman (F.mergeCheapest h).trees) = fa + fb
  fa_le_fb : fa ≤ fb
  min_fa : ∀ s ∈ alphabet (huffman (F.mergeCheapest h).trees),
    fa ≤ freqOf s (huffman (F.mergeCheapest h).trees)
  min_fb : ∀ s ∈ alphabet (huffman (F.mergeCheapest h).trees),
    s ≠ sa → fb ≤ freqOf s (huffman (F.mergeCheapest h).trees)
  split_commute :
    splitLeaf (huffman (F.mergeCheapest h).trees) sa sa sb fa fb = huffman F.trees

/--
The bundled greedy step exposes exactly the side conditions needed to split
the merged leaf after the recursive Huffman call.  This is the main V2
interface: callers do not inspect the forest plumbing directly.
-/
lemma mergeCheapest_split_ready (F : Forest) (h : F.length ≥ 2) :
    Nonempty (MergeCheapestSplitReady F h) := by
  rcases mergeCheapest_spec F h with
    ⟨sa, fa, sb, fb, rest, h_eq_trees, h_eq_reduced, h_ne, h_fresh⟩
  let F' := F.mergeCheapest h
  have h_F'_trees : F'.trees = insortTree (htLeaf sa (fa + fb)) rest := h_eq_reduced
  have h_orig_cons : forest_consistent (htLeaf sa fa :: htLeaf sb fb :: rest) := by
    simpa [h_eq_trees] using F.consistent
  have h_sb_rest_cons : forest_consistent (htLeaf sb fb :: rest) :=
    forest_consistent_tail (htLeaf sa fa) (htLeaf sb fb :: rest) h_orig_cons
  have h_rest_cons : forest_consistent rest :=
    forest_consistent_tail (htLeaf sb fb) rest h_sb_rest_cons
  have h_orig_sorted : forest_sorted (htLeaf sa fa :: htLeaf sb fb :: rest) := by
    simpa [h_eq_trees] using F.sorted
  have h_fa_pos : fa > 0 := by
    simpa [rootFreq] using F.allPos (htLeaf sa fa) (by rw [h_eq_trees]; simp)
  have h_fb_pos : fb > 0 := by
    simpa [rootFreq] using F.allPos (htLeaf sb fb) (by rw [h_eq_trees]; simp)
  have h_a_in_reduced : sa ∈ alphabet (huffman F'.trees) := by
    rw [alphabet_huffman_eq_forest_alphabet F'.trees F'.nonempty, mem_forest_alphabet]
    exact ⟨htLeaf sa (fa + fb), by rw [h_F'_trees, mem_insortTree]; simp, by simp [alphabet]⟩
  have h_b_notin_reduced : sb ∉ alphabet (huffman F'.trees) := by
    rw [alphabet_huffman_eq_forest_alphabet F'.trees F'.nonempty, mem_forest_alphabet]
    rintro ⟨t, ht, h_mem⟩
    rw [h_F'_trees, mem_insortTree] at ht
    rcases ht with (rfl | ht)
    · simp [alphabet] at h_mem
      exact h_ne h_mem.symm
    · rw [forest_consistent_cons_iff] at h_sb_rest_cons
      exact (Finset.disjoint_left.mp (h_sb_rest_cons.2.2 t ht) (by simp [alphabet])) h_mem
  have h_freq_a : freqOf sa (huffman F'.trees) = fa + fb := by
    rw [freqOf_huffman_eq_forest_freq F'.trees sa F'.nonempty, h_F'_trees,
      forest_freq_insortTree, forest_freq_cons]
    have h_zero : forest_freq rest sa = 0 :=
      forest_freq_eq_zero_of_not_mem rest sa (by
        rw [mem_forest_alphabet]
        rintro ⟨t, ht, h_mem⟩
        exact h_fresh t ht h_mem)
    simp [freqOf, h_zero]
  have h_fa_le_fb : fa ≤ fb := by
    simpa [rootFreq] using h_orig_sorted.1
  have h_min : ∀ s ∈ alphabet (huffman F'.trees),
      fa ≤ freqOf s (huffman F'.trees) ∧
      (s ≠ sa → fb ≤ freqOf s (huffman F'.trees)) := by
    intro s hs
    rw [alphabet_huffman_eq_forest_alphabet F'.trees F'.nonempty, mem_forest_alphabet] at hs
    rcases hs with ⟨t, ht, h_mem⟩
    rw [h_F'_trees, mem_insortTree] at ht
    rcases ht with (rfl | ht)
    · have hs_eq : s = sa := by simpa [alphabet] using h_mem
      rw [hs_eq, h_freq_a]
      constructor
      · omega
      · intro _
        omega
    · have h_s_ne_a : s ≠ sa := fun h_eq => h_fresh t ht (by simpa [h_eq] using h_mem)
      have h_freq_leaf : freqOf s (htLeaf sa (fa + fb)) = 0 := by
        simp [freqOf, h_s_ne_a.symm]
      have h_freq_s : freqOf s (huffman F'.trees) = rootFreq t := by
        rw [freqOf_huffman_eq_forest_freq F'.trees s F'.nonempty, h_F'_trees,
          forest_freq_insortTree, forest_freq_cons, h_freq_leaf, zero_add]
        exact forest_freq_eq_rootFreq_of_mem_leaf rest s t
          (fun u hu => F.allLeaves u (by rw [h_eq_trees]; simp [hu]))
          h_rest_cons ht h_mem
      rw [h_freq_s]
      constructor
      · have h_le := rootFreq_le_of_mem_sorted (htLeaf sa fa) (htLeaf sb fb :: rest)
          h_orig_sorted t (by simp [ht])
        simpa [rootFreq] using h_le
      · intro _
        have h_le := rootFreq_le_of_mem_sorted (htLeaf sb fb) rest
          (forest_sorted_tail (htLeaf sa fa) (htLeaf sb fb :: rest) h_orig_sorted) t ht
        simpa [rootFreq] using h_le
  have h_split_commute : splitLeaf (huffman F'.trees) sa sa sb fa fb = huffman F.trees := by
    rw [h_eq_trees, h_F'_trees, splitLeaf_huffman_commute sa sb fa fb rest h_fresh]
    simp [huffman, unite]
  exact ⟨{
    sa := sa
    fa := fa
    sb := sb
    fb := fb
    fa_pos := h_fa_pos
    fb_pos := h_fb_pos
    sym_ne := h_ne
    sa_mem := h_a_in_reduced
    sb_not_mem := h_b_notin_reduced
    freq_sa := h_freq_a
    fa_le_fb := h_fa_le_fb
    min_fa := fun s hs => (h_min s hs).1
    min_fb := fun s hs h_s_ne_a => (h_min s hs).2 h_s_ne_a
    split_commute := h_split_commute
  }⟩

namespace MergeCheapestSplitReady

theorem splitLeafSpec {F : Forest} {h : F.length ≥ 2} (R : MergeCheapestSplitReady F h) :
    SplitLeafOptimalitySpec (huffman (F.mergeCheapest h).trees) R.sa R.sb R.fa R.fb :=
  { z_mem := R.sa_mem
    b_fresh := R.sb_not_mem
    sym_ne := R.sym_ne
    fa_pos := R.fa_pos
    fb_pos := R.fb_pos
    fa_le_fb := R.fa_le_fb
    fa_min := R.min_fa
    fb_min := R.min_fb
    freq_z := R.freq_sa }

lemma optimum {F : Forest} {h : F.length ≥ 2} (R : MergeCheapestSplitReady F h)
    (h_opt_reduced : optimum (huffman (F.mergeCheapest h).trees)) :
    optimum (huffman F.trees) := by
  rw [← R.split_commute]
  exact split_leaf_preserves_optimum R.splitLeafSpec h_opt_reduced

end MergeCheapestSplitReady

theorem mergeCheapest_preserves_optimum (F : Forest) (h : F.length ≥ 2)
    (h_opt_reduced : optimum (huffman (F.mergeCheapest h).trees)) :
    optimum (huffman F.trees) := by
  rcases mergeCheapest_split_ready F h with ⟨R⟩
  exact R.optimum h_opt_reduced

end Forest

namespace OptimalV2

private theorem optimum_singleton_forest (F : Forest) (h_len : F.length = 1) :
    optimum (huffman F.trees) := by
  cases h_eq : F.trees with
  | nil => exact False.elim (F.nonempty (by rw [h_eq]))
  | cons t ts =>
      cases ts with
      | nil =>
          have h_leaf : height t = 0 := F.allLeaves t (by simp [h_eq])
          rcases height_eq_zero_iff t |>.mp h_leaf with ⟨s, f, ht⟩
          have h_f_pos : f > 0 := by
            simpa [rootFreq] using F.allPos (htLeaf s f) (by rw [h_eq, ht]; simp)
          rw [ht]
          simp [huffman]
          exact optimum_leaf s f h_f_pos
      | cons u us =>
          simp [Forest.length, h_eq] at h_len

/-- Huffman's algorithm produces an optimum tree for every valid bundled forest. -/
theorem optimum_huffman_v2 (F : Forest) : optimum (huffman F.trees) := by
  generalize hlen : F.length = n
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
      by_cases h_len2 : F.length ≥ 2
      · apply Forest.mergeCheapest_preserves_optimum F h_len2
        exact ih (F.mergeCheapest h_len2).length
          (by rw [← hlen]; exact Forest.mergeCheapest_length_lt F h_len2)
          (F.mergeCheapest h_len2) rfl
      · exact optimum_singleton_forest F (by
          have h_pos : F.length > 0 := by simpa [Forest.length, List.length_pos_iff_ne_nil] using F.nonempty
          omega)

end OptimalV2

/-! ## Frequency-table interface -/

/-- The frequency assigned to a symbol by a raw frequency table. -/
def tableFreq (xs : List (ℕ × ℕ)) (s : ℕ) : ℕ :=
  (xs.map (fun p => if p.1 = s then p.2 else 0)).sum

/-- Turn a frequency table into singleton Huffman leaves. -/
def leavesOfFreqs (xs : List (ℕ × ℕ)) : List HuffTree :=
  xs.map (fun p => htLeaf p.1 p.2)

/-- Insertion-sort a forest by {name}`rootFreq`, using the same order expected by {name}`huffman`. -/
def sortForest : List HuffTree → List HuffTree
  | [] => []
  | t :: ts => insortTree t (sortForest ts)

/-- Run Huffman's algorithm on an arbitrary frequency table. -/
def huffmanOfFreqs (xs : List (ℕ × ℕ)) : HuffTree :=
  huffman (sortForest (leavesOfFreqs xs))

lemma sortForest_sorted (ts : List HuffTree) : forest_sorted (sortForest ts) := by
  induction ts with
  | nil => simp [sortForest, forest_sorted]
  | cons t ts ih => simpa [sortForest] using forest_sorted_insortTree_of_sorted t (sortForest ts) ih

lemma sortForest_ne_nil {ts : List HuffTree} (h_nonempty : ts ≠ []) : sortForest ts ≠ [] := by
  cases ts with
  | nil => contradiction
  | cons t ts => simpa [sortForest] using insortTree_ne_nil t (sortForest ts)

lemma mem_sortForest (t : HuffTree) (ts : List HuffTree) :
    t ∈ sortForest ts ↔ t ∈ ts := by
  induction ts with
  | nil => simp [sortForest]
  | cons u us ih => simp [sortForest, mem_insortTree, ih]

lemma forest_consistent_sortForest (ts : List HuffTree)
    (h_cons : forest_consistent ts) :
    forest_consistent (sortForest ts) := by
  induction ts with
  | nil => simpa [sortForest] using h_cons
  | cons t ts ih =>
    rw [forest_consistent_cons_iff] at h_cons
    simpa [sortForest] using forest_consistent_insortTree t (sortForest ts) (by
      rw [forest_consistent_cons_iff]
      exact ⟨h_cons.1, ih h_cons.2.1,
        fun u hu => h_cons.2.2 u ((mem_sortForest u ts).mp hu)⟩)

lemma forest_freq_sortForest (ts : List HuffTree) (s : ℕ) :
    forest_freq (sortForest ts) s = forest_freq ts s := by
  induction ts with
  | nil => simp [sortForest, forest_freq]
  | cons t ts ih => rw [sortForest, forest_freq_insortTree]; simpa [forest_freq] using ih

lemma forest_freq_leavesOfFreqs (xs : List (ℕ × ℕ)) (s : ℕ) :
    forest_freq (leavesOfFreqs xs) s = tableFreq xs s := by
  induction xs with
  | nil => simp [leavesOfFreqs, tableFreq, forest_freq]
  | cons p ps ih =>
      simp [leavesOfFreqs, tableFreq, forest_freq, freqOf]
      simpa [leavesOfFreqs, tableFreq, forest_freq] using ih

lemma forest_consistent_leavesOfFreqs (xs : List (ℕ × ℕ))
    (h_nodup : (xs.map Prod.fst).Nodup) :
    forest_consistent (leavesOfFreqs xs) := by
  induction xs with
  | nil => simp [leavesOfFreqs, forest_consistent]
  | cons p ps ih =>
    rcases List.nodup_cons.mp
      (show (p.1 :: ps.map Prod.fst).Nodup by simpa using h_nodup) with
      ⟨h_not_mem, h_tail_nodup⟩
    change forest_consistent (htLeaf p.1 p.2 :: leavesOfFreqs ps)
    rw [forest_consistent_cons_iff]
    refine ⟨by simp [consistent], ih h_tail_nodup, ?_⟩
    intro u hu
    dsimp [leavesOfFreqs] at hu
    rcases List.mem_map.mp hu with ⟨q, hq, rfl⟩
    simpa [alphabet] using
      (fun h_eq => h_not_mem (List.mem_map.mpr ⟨q, hq, h_eq.symm⟩) : p.1 ≠ q.1)

theorem freqOf_huffmanOfFreqs_eq_tableFreq (xs : List (ℕ × ℕ)) (s : ℕ)
    (h_nonempty : xs ≠ []) :
    freqOf s (huffmanOfFreqs xs) = tableFreq xs s := by
  unfold huffmanOfFreqs
  rw [freqOf_huffman_eq_forest_freq, forest_freq_sortForest, forest_freq_leavesOfFreqs]
  exact sortForest_ne_nil (by simpa [leavesOfFreqs] using h_nonempty)

/--
Huffman's algorithm is optimal for every nonempty positive frequency table with
no duplicate symbols.  The table may be in any order; it is sorted before
calling the bundled V2 {name}`huffman` optimality theorem.
-/
theorem optimum_huffman_freqs (xs : List (ℕ × ℕ))
    (h_nodup : (xs.map Prod.fst).Nodup)
    (h_pos : ∀ p ∈ xs, p.2 > 0)
    (h_nonempty : xs ≠ []) :
    optimum (huffmanOfFreqs xs) := by
  unfold huffmanOfFreqs
  exact OptimalV2.optimum_huffman_v2
    { trees := sortForest (leavesOfFreqs xs)
      sorted := sortForest_sorted (leavesOfFreqs xs)
      consistent := forest_consistent_sortForest (leavesOfFreqs xs)
        (forest_consistent_leavesOfFreqs xs h_nodup)
      allLeaves := fun t ht => by
        rcases (by simpa [leavesOfFreqs] using
          (mem_sortForest t (leavesOfFreqs xs)).mp ht) with ⟨a, b, _, rfl⟩
        simp [height]
      allPos := fun t ht => by
        rcases (by simpa [leavesOfFreqs] using
          (mem_sortForest t (leavesOfFreqs xs)).mp ht) with ⟨a, b, hp, rfl⟩
        simpa [rootFreq] using h_pos (a, b) hp
      nonempty := sortForest_ne_nil (by simpa [leavesOfFreqs] using h_nonempty) }

end HuffmanV2
end CLRS
