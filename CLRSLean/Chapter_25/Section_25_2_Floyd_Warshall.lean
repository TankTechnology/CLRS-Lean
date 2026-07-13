import Mathlib
import CLRSLean.Chapter_25.Section_25_1_All_Pairs_Model

/-!
# 25.2. The Floyd-Warshall algorithm
-/

namespace CLRS
namespace Chapter24
open Finset

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-! ## Floyd-Warshall algorithm definition -/

def fwStep (D : V → V → WithTop ℝ) (k : V) (i j : V) : WithTop ℝ :=
  min (D i j) (D i k + D k j)

noncomputable def D (G : WeightedGraph V) : List V → V → V → WithTop ℝ
  | [], i, j => G.weightMatrix i j
  | k :: ks, i, j => min (G.D ks i j) (G.D ks i k + G.D ks k j)

@[simp] theorem D_nil (G : WeightedGraph V) (i j : V) : G.D [] i j = G.weightMatrix i j := rfl

theorem D_cons (k : V) (ks : List V) (i j : V) : G.D (k :: ks) i j =
    min (G.D ks i j) (G.D ks i k + G.D ks k j) := rfl

noncomputable def floydWarshall (G : WeightedGraph V) : V → V → WithTop ℝ :=
  G.D (Finset.univ.toList : List V)

@[simp] theorem floydWarshall_eq_D (G : WeightedGraph V) :
    G.floydWarshall = G.D (Finset.univ.toList : List V) := rfl

/-! ## Auxiliary lemmas -/

lemma mem_of_getLast?_eq_some {l : List α} {a : α} (h : l.getLast? = some a) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp
    rcases xs with (_ | ⟨y, ys⟩)
    · simp at h; subst a; simp
    · have h' : (y :: ys).getLast? = some a := by simpa using h
      have hmem : a ∈ (y :: ys) := ih h'
      exact Or.inr hmem

lemma walkWeight_append_adjacent (w : V → V → ℝ) (q1 q2 : List V) (k : V)
    (hq1_ne : q1 ≠ []) (hq2_ne : q2 ≠ []) (hlast : q1.getLast hq1_ne = k)
    (hhead : q2.head? = some k) :
    walkWeight w (q1 ++ q2.tail) = walkWeight w q1 + walkWeight w q2 := by
  have hq1_snoc : q1 = q1.dropLast ++ [k] := by
    have := List.dropLast_append_getLast hq1_ne
    rw [hlast] at this
    exact this.symm
  have hq2_cons : q2 = k :: q2.tail := by
    rcases q2 with (_ | ⟨a, as⟩)
    · simp at hq2_ne
    · have ha_k : a = k := by simpa using hhead
      subst ha_k; rfl
  rw [hq1_snoc, hq2_cons]
  simp
  rw [walkWeight_split w (q1.dropLast) k q2.tail]

lemma getLast?_cons_ne_nil (a : V) (l : List V) (h : l ≠ []) : (a :: l).getLast? = l.getLast? := by
  cases l
  · exact (h rfl).elim
  · rename_i b bs; rfl

lemma concat_walks {p1 p2 : List V} (hp1 : G.IsWalkFrom i k p1) (hp2 : G.IsWalkFrom k j p2) :
    G.IsWalkFrom i j (p1 ++ p2.tail) := by
  have hp1_ne : p1 ≠ [] := hp1.ne_nil
  have hp2_ne : p2 ≠ [] := hp2.ne_nil
  have hp2_eq : p2 = k :: p2.tail := by
    rcases p2 with (_ | ⟨x, xs⟩)
    · exact absurd rfl hp2_ne
    · have hx_k : x = k := by simpa using hp2.head
      subst x; rfl
  have hchain_info := (List.isChain_cons.1 (by
    rw [← hp2_eq]; exact hp2.chain))
  have hchain_tail : List.IsChain G.Adj p2.tail := hchain_info.2
  have h_edge_to_tail : ∀ y ∈ p2.tail.head?, G.Adj k y := hchain_info.1
  have hchain_combined : List.IsChain G.Adj (p1 ++ p2.tail) := by
    have h_conn : ∀ a b, a ∈ p1.getLast? → b ∈ p2.tail.head? → G.Adj a b := by
      intro a b ha hb
      have ha_eq_k : a = k := by
        have ha' : p1.getLast? = some a := ha
        have hk' : p1.getLast? = some k := hp1.last
        rw [ha'] at hk'
        exact Option.some_inj.mp hk'
      subst a
      exact h_edge_to_tail b hb
    apply hp1.chain.append hchain_tail
    intro x hx y hy
    apply h_conn x y hx hy
  have hhead_combined : (p1 ++ p2.tail).head? = some i := by
    rcases p1 with (_ | ⟨x, xs⟩)
    · exact absurd rfl hp1_ne
    · simpa using hp1.head
  have hlast_combined : (p1 ++ p2.tail).getLast? = some j := by
    by_cases htail : p2.tail = []
    · rw [htail]
      have hlast_p2 : p2.getLast? = some j := hp2.last
      have h_single : p2 = [k] := by
        rcases p2 with (_ | ⟨x, xs⟩)
        · exact absurd rfl hp2_ne
        · have hx_k : x = k := by simpa using hp2.head
          subst x; simp at htail; subst htail; rfl
      have : k = j := by
        rw [h_single] at hlast_p2
        simpa using hlast_p2
      subst this
      simpa using hp1.last
    · rw [List.getLast?_append_of_ne_nil p1 htail]
      have htail' : p2.tail ≠ [] := htail
      have hlast_p2 : (k :: p2.tail).getLast? = some j := by
        rw [← hp2_eq]
        exact hp2.last
      have : p2.tail.getLast? = some j := by
        rw [← getLast?_cons_ne_nil k p2.tail htail', hlast_p2]
      exact this
  exact ⟨hchain_combined, hhead_combined, hlast_combined⟩

lemma concat_walks_weight (w : V → V → ℝ) {p1 p2 : List V} (hp1 : G.IsWalkFrom i k p1)
    (hp2 : G.IsWalkFrom k j p2) : walkWeight w (p1 ++ p2.tail) = walkWeight w p1 + walkWeight w p2 := by
  have hp1_ne : p1 ≠ [] := hp1.ne_nil
  have hp2_ne : p2 ≠ [] := hp2.ne_nil
  have hp1_getLast : p1.getLast hp1_ne = k := by
    have h1 : p1.getLast? = some (p1.getLast hp1_ne) :=
      List.getLast?_eq_getLast_of_ne_nil hp1_ne
    have h2 : p1.getLast? = some k := hp1.last
    rw [h1] at h2
    exact Option.some_inj.mp h2
  have hp2_head : p2.head? = some k := hp2.head
  exact walkWeight_append_adjacent w p1 p2 k hp1_ne hp2_ne hp1_getLast hp2_head

/-! ## Correctness: lower bound for simple walks -/

theorem D_le_simple (hNC : G.NoNegCycle) (ks : List V) (i j : V) (q : List V)
    (hq : G.IsWalkFrom i j q) (hq_simple : q.Nodup)
    (h_verts : ∀ x ∈ q, x = i ∨ x = j ∨ x ∈ ks) :
    G.D ks i j ≤ (walkWeight G.w q : WithTop ℝ) := by
  induction ks generalizing i j q with
  | nil =>
    rw [D_nil]
    unfold weightMatrix
    have hall_ij : ∀ x ∈ q, x = i ∨ x = j := by
      intro x hx
      rcases h_verts x hx with (h | h | h)
      · exact Or.inl h
      · exact Or.inr h
      · simp at h
    by_cases hij : i = j
    · subst j
      have hq_single : q = [i] := by
        have hall_i : ∀ x ∈ q, x = i := by
          intro x hx; rcases hall_ij x hx with (h | h); exact h; exact h
        rcases q with (_ | ⟨x, xs⟩)
        · exact absurd rfl hq.ne_nil
        · have hx_i : x = i := hall_i x (by simp)
          subst x
          have hxs_nil : xs = [] := by
            by_contra! hne
            rcases xs with (_ | ⟨y, ys⟩)
            · exact hne rfl
            · have hy_i : y = i := hall_i y (by simp)
              have hi_notin_xs : i ∉ (y :: ys) := by
                have := hq_simple
                -- Nodup (i :: y :: ys) implies i ∉ (y :: ys)
                -- Use the lemma List.nodup_cons
                simpa using (List.nodup_cons.mp hq_simple).1
              subst hy_i; exact hi_notin_xs (by simp)
          simp
      simp [hq_single]
    · have h_edge : G.Adj i j := by
        have h_first_two : ∃ r, q = i :: j :: r := by
          have hhead : q.head? = some i := hq.head
          rcases q with (_ | ⟨a, r⟩)
          · exact absurd rfl hq.ne_nil
          · have ha_i : a = i := by simpa using hhead
            subst a
            rcases r with (_ | ⟨b, r'⟩)
            · -- r = []: q = [i], but then hq.last implies j = i, contradicting i ≠ j
              have : j = i := by
                have hlast_i : (i :: []).getLast? = some j := hq.last
                simpa using hlast_i
              exact absurd this Ne.symm hij
            · -- r = b :: r': need to show b = j
              have hb_j : b = j := by
                have hb_vert : b = i ∨ b = j ∨ b ∈ [] := h_verts b (by simp)
                rcases hb_vert with (h | h | h)
                · have : (i :: i :: b :: r').Nodup := hq_simple
                  simp at this
                · exact h
                · exact (h : False).elim
              subst b; exact ⟨r', rfl⟩
        rcases h_first_two with ⟨r, hq_eq⟩
        have hchain : List.IsChain G.Adj q := hq.chain
        rw [hq_eq] at hchain
        exact hchain.rel_head
      have hq_ij : q = [i, j] := by
        have hhead : q.head? = some i := hq.head
        have hlast : q.getLast? = some j := hq.last
        have hlen2 : q.length = 2 := by
          have h_ge_2 : q.length ≥ 2 := by
            by_contra! h
            have hlen1 : q.length = 1 := by omega
            rcases q with (_ | ⟨a, r⟩)
            · exact absurd rfl hq.ne_nil
            · rcases r with (_ | ⟨b, r'⟩)
              · have ha_i : a = i := by simpa using hhead
                have ha_j : a = j := by simpa using hlast
                exact hij (ha_i.trans ha_j.symm)
              · simp at hlen1
          by_contra! h
          have h_ge_3 : q.length ≥ 3 := by omega
          have hcard_eq_len : Finset.card (q.toFinset) = q.length :=
            List.toFinset_card_of_nodup hq_simple
          have hset_subset : q.toFinset ⊆ ({i, j} : Finset V) := by
            intro x hx
            have hx' : x ∈ q := by
              rw [List.mem_toFinset] at hx; exact hx
            rcases hall_ij x hx' with (h | h)
            · simp [h]
            · simp [h]
          have hcard_le_2 : Finset.card (q.toFinset) ≤ 2 := by
            calc
              Finset.card (q.toFinset) ≤ Finset.card ({i, j} : Finset V) :=
                Finset.card_le_card hset_subset
              _ = 2 := by simp
          rw [hcard_eq_len] at hcard_le_2
          omega
        obtain ⟨x, y, hq_eq⟩ := List.length_eq_two.mp hlen2
        have hx_i : x = i := by
          have : q.head? = some x := by
            rw [hq_eq]; simp
          simpa [this, hhead]
        have hy_j : y = j := by
          have : q.getLast? = some y := by
            rw [hq_eq]; simp
          simpa [this, hlast]
        rw [hx_i, hy_j] at hq_eq
        exact hq_eq
      simp [hij, hq_ij, h_edge]
  | cons k ks' ih =>
    have h_rec := D_le_simple hNC ks'
    rw [D_cons]
    by_cases hk : k ∈ q
    · rcases List.mem_iff_append.mp hk with ⟨l1, l2, hq_eq, hk_notin_l1⟩
      have hk_notin_l2 : k ∉ l2 := by
        intro hk_l2
        have hcount_q : Multiset.count k (q : Multiset V) = 1 :=
          List.count_eq_one_of_mem hq_simple hk
        have hcount_ge_2 : Multiset.count k (q : Multiset V) ≥ 2 := by
          have hq_ms_eq : (q : Multiset V) = (l1 ++ k :: l2 : Multiset V) := by
            simpa [hq_eq]
          rw [hq_ms_eq]
          simp [hk_notin_l1, hk_l2]
        linarith
      let q1 := l1 ++ [k]
      let q2 := k :: l2
      have hq1_walk : G.IsWalkFrom i k q1 := by
        refine ⟨?_, ?_, ?_⟩
        · have hchain : List.IsChain G.Adj (l1 ++ k :: l2) := by
            rw [← hq_eq]; exact hq.chain
          have h_prefix : (l1 ++ [k]) <+: (l1 ++ k :: l2) := ⟨l2, by simp⟩
          exact hchain.prefix h_prefix
        · simp [q1]
        · simp [q1]
      have hq1_simple : q1.Nodup :=
        hq_simple.sublist (by rw [hq_eq]; simp)
      have hq1_verts : ∀ x ∈ q1, x = i ∨ x = k ∨ x ∈ ks' := by
        intro x hx
        have hx_in_q : x ∈ q := by
          rw [hq_eq]
          rcases hx with (hx_l1 | hx_k)
          · exact Or.inl hx_l1
          · simp
        rcases h_verts x hx_in_q with (hxi | hxj | hxks)
        · exact Or.inl hxi
        · by_cases hjk : j = k
          · subst j; exact Or.inr (Or.inl rfl)
          · have hj_notin_l1 : j ∉ l1 := by
              intro hj
              have : Multiset.count j (q : Multiset V) ≥ 2 := by
                rw [hq_eq]
                have hj_in_suffix : j ∈ k :: l2 := by
                  have hlast : q.getLast? = some j := hq.last
                  rw [hq_eq] at hlast
                  have hlast_suff : (k :: l2).getLast? = some j := by
                    simpa [getLast?_append_cons] using hlast
                  exact mem_of_getLast?_eq_some hlast_suff
                simp [hj, hj_in_suffix]
              have : Multiset.count j (q : Multiset V) = 1 :=
                List.count_eq_one_of_mem hq_simple (mem_of_getLast?_eq_some hq.last)
              omega
            rcases hx with (hx_l1 | hx_k)
            · exact (hj_notin_l1 hx_l1).elim
            · simp at hx_k; subst x; exact hjk rfl
        · rcases hxks with (rfl | hxks)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr hxks)
      have hq2_walk : G.IsWalkFrom k j q2 := by
        refine ⟨?_, ?_, ?_⟩
        · have hchain : List.IsChain G.Adj (l1 ++ k :: l2) := by
            rw [← hq_eq]; exact hq.chain
          have h_suffix : (k :: l2) <:+ (l1 ++ k :: l2) := ⟨l1, by simp⟩
          exact hchain.suffix h_suffix
        · simp [q2]
        · have hlast : q.getLast? = some j := hq.last
          rw [hq_eq] at hlast
          simpa [getLast?_append_cons] using hlast
      have hq2_simple : q2.Nodup :=
        hq_simple.sublist (by rw [hq_eq]; simp)
      have hq2_verts : ∀ x ∈ q2, x = k ∨ x = j ∨ x ∈ ks' := by
        intro x hx
        have hx_in_q : x ∈ q := by
          rw [hq_eq]
          rcases hx with (hx_k | hx_l2)
          · simp
          · simp [hx_l2]
        rcases h_verts x hx_in_q with (hxi | hxj | hxks)
        · by_cases hik : i = k
          · subst i; exact Or.inl rfl
          · have hi_notin_l2 : i ∉ l2 := by
              intro hi
              have : Multiset.count i (q : Multiset V) ≥ 2 := by
                rw [hq_eq]
                have hi_in_prefix : i ∈ l1 := by
                  have hhead : q.head? = some i := hq.head
                  rw [hq_eq] at hhead
                  by_cases hl1_nil : l1 = []
                  · subst l1; simp at hhead; exact hik.symm (by simpa using hhead)
                  · have hhead_l1 : l1.head? = some i := by simpa using hhead
                    rcases l1 with (_ | ⟨a, as⟩)
                    · simp at hl1_nil
                    · simp; simpa using hhead_l1
                simp [hi_in_prefix, hi]
              have : Multiset.count i (q : Multiset V) = 1 :=
                List.count_eq_one_of_mem hq_simple (mem_of_getLast?_eq_some hq.head)
              omega
            rcases hx with (hx_k | hx_l2)
            · exact Or.inl hx_k
            · exact (hi_notin_l2 hx_l2).elim
        · exact Or.inr (Or.inl hxj)
        · rcases hxks with (rfl | hxks)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr hxks)
      have h1 : G.D ks' i k ≤ (walkWeight G.w q1 : WithTop ℝ) :=
        h_rec i k q1 hq1_walk hq1_simple hq1_verts
      have h2 : G.D ks' k j ≤ (walkWeight G.w q2 : WithTop ℝ) :=
        h_rec k j q2 hq2_walk hq2_simple hq2_verts
      have hsplit : (walkWeight G.w q1 : WithTop ℝ) + (walkWeight G.w q2 : WithTop ℝ) =
          (walkWeight G.w q : WithTop ℝ) := by
        rw [hq_eq]
        have hcalc : walkWeight G.w (l1 ++ [k] ++ l2) =
            walkWeight G.w (l1 ++ [k]) + walkWeight G.w (k :: l2) := by
          rw [walkWeight_split G.w l1 k l2]
        simp [q1, q2, hcalc]
      calc
        min (G.D ks' i j) (G.D ks' i k + G.D ks' k j) ≤ G.D ks' i k + G.D ks' k j := min_le_right _ _
        _ ≤ (walkWeight G.w q1 : WithTop ℝ) + (walkWeight G.w q2 : WithTop ℝ) := add_le_add h1 h2
        _ = (walkWeight G.w q : WithTop ℝ) := hsplit
    · have h_verts_ks' : ∀ x ∈ q, x = i ∨ x = j ∨ x ∈ ks' := by
        intro x hx
        rcases h_verts x hx with (h | h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · rcases h with (rfl | h)
          · exact (hk hx).elim
          · exact Or.inr (Or.inr h)
      have h_ij : G.D ks' i j ≤ (walkWeight G.w q : WithTop ℝ) :=
        h_rec i j q hq hq_simple h_verts_ks'
      exact le_trans (min_le_left _ _) h_ij

/-! ## Correctness: attainability -/

theorem D_attainable (ks : List V) (i j : V) (h : G.D ks i j ≠ ⊤) :
    ∃ p, G.IsWalkFrom i j p ∧ (walkWeight G.w p : WithTop ℝ) = G.D ks i j := by
  induction ks generalizing i j with
  | nil =>
    rw [D_nil] at h
    unfold weightMatrix at h
    by_cases hij : i = j
    · subst j
      refine ⟨[i], ?_, ?_⟩
      · refine ⟨List.isChain_singleton _, ?_, ?_⟩
        · simp
        · simp
      · simp
    · have hedge : G.Adj i j := by
        unfold weightMatrix at h
        split_ifs at h with h_edge h_eq
        · exact False.elim (hij h_eq)
        · exact h_edge
        · simp at h
      refine ⟨[i, j], ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · apply List.isChain_append.2
          refine ⟨List.isChain_singleton _, List.isChain_singleton _, ?_⟩
          intro a ha b hb
          simp at ha hb; subst a; subst b; exact hedge
        · simp
        · simp
      · simp [weightMatrix, hij, hedge]
  | cons k ks' ih =>
    rw [D_cons] at h
    have hmin : min (G.D ks' i j) (G.D ks' i k + G.D ks' k j) ≠ ⊤ := h
    by_cases hij' : G.D ks' i j = ⊤
    · have hsum : G.D ks' i k + G.D ks' k j ≠ ⊤ := by
        intro hsum_top
        apply hmin
        simp [hij', hsum_top]
      have h_add : G.D ks' i k ≠ ⊤ ∧ G.D ks' k j ≠ ⊤ := by
          simpa using hsum
      rcases h_add with ⟨hik, hkj⟩
      rcases ih i k hik with ⟨p1, hp1, hp1_eq⟩
      rcases ih k j hkj with ⟨p2, hp2, hp2_eq⟩
      have hp_combined : G.IsWalkFrom i j (p1 ++ p2.tail) :=
        concat_walks hp1 hp2
      have hp_weight : (walkWeight G.w (p1 ++ p2.tail) : WithTop ℝ) = G.D (k :: ks') i j := by
        rw [D_cons]
        have hcalc : walkWeight G.w (p1 ++ p2.tail) = walkWeight G.w p1 + walkWeight G.w p2 :=
          concat_walks_weight G.w hp1 hp2
        calc
          (walkWeight G.w (p1 ++ p2.tail) : WithTop ℝ) =
              (walkWeight G.w p1 + walkWeight G.w p2 : WithTop ℝ) := by rw [hcalc]
          _ = G.D ks' i k + G.D ks' k j := by simp [hp1_eq, hp2_eq]
          _ = min (G.D ks' i j) (G.D ks' i k + G.D ks' k j) := by simp [hij']
      refine ⟨p1 ++ p2.tail, hp_combined, hp_weight⟩
    · rcases ih i j hij' with ⟨p, hp, hp_eq⟩
      refine ⟨p, hp, ?_⟩
      rw [D_cons]
      simp [hij', hp_eq]

/-! ## Main correctness theorem -/

theorem floydWarshall_correct (hNC : G.NoNegCycle) (i j : V) :
    G.IsShortestDist i j (G.floydWarshall i j) := by
  constructor
  · intro p hp
    rcases G.exists_simple_le hNC i j p.length p (le_refl _) hp with ⟨q, hq, hq_simple, hqle⟩
    have h_verts : ∀ x ∈ q, x = i ∨ x = j ∨ x ∈ (Finset.univ.toList : List V) := by
      intro x hx
      have hx_mem : x ∈ (Finset.univ : Finset V) := Finset.mem_univ x
      have hx_list : x ∈ (Finset.univ : Finset V).toList := by
        rw [Finset.mem_toList]; exact hx_mem
      exact Or.inr (Or.inr hx_list)
    have hDle := G.D_le_simple hNC (Finset.univ.toList : List V) i j q hq hq_simple h_verts
    rw [floydWarshall_eq_D]
    have h_cast : (walkWeight G.w q : WithTop ℝ) ≤ (walkWeight G.w p : WithTop ℝ) := by
      exact_mod_cast hqle
    exact le_trans hDle h_cast
  · by_cases h : G.floydWarshall i j = ⊤
    · left; exact h
    · right
      have hD : G.D (Finset.univ.toList : List V) i j ≠ ⊤ := by
        rw [← floydWarshall_eq_D]; exact h
      rcases G.D_attainable (Finset.univ.toList : List V) i j hD with ⟨p, hp, hp_eq⟩
      refine ⟨p, hp, ?_⟩
      rw [floydWarshall_eq_D, hp_eq]

end WeightedGraph
end Chapter24
end CLRS
