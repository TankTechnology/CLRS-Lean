import CLRSLean.FourthEdition.Chapter_11.Section_11_4_Open_Addressing.UniformProbe.Definitions
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# CLRS Section 11.4 - Counting uniform probe prefixes

We restrict a slot permutation to its first {lit}`i` positions.  The symmetric
group acts transitively on these prefix embeddings, so every embedding has the
same number of permutation extensions.  Counting all embeddings determines
that extension count and then the number whose range lies in the occupied set.
-/

namespace CLRS
namespace Chapter11

/-- Inclusion of the first {lit}`i` probe positions into a table of size
{lit}`m`. -/
def probePrefixEmbedding {m i : Nat} (hi : i ≤ m) : Fin i ↪ Fin m :=
  Fin.castLEEmb hi

/-- Restriction of a full probe permutation to its first {lit}`i` positions. -/
def probePermutationPrefix {m i : Nat} (hi : i ≤ m)
    (σ : Equiv.Perm (Fin m)) : Fin i ↪ Fin m :=
  (probePrefixEmbedding hi).trans σ.toEmbedding

/-- Left multiplication of permutations becomes the natural action on their
prefix embeddings. -/
theorem probePermutationPrefix_mul {m i : Nat} (hi : i ≤ m)
    (τ σ : Equiv.Perm (Fin m)) :
    probePermutationPrefix hi (τ * σ) = τ • probePermutationPrefix hi σ := by
  ext j
  simp [probePermutationPrefix, probePrefixEmbedding,
    Function.Embedding.smul_apply, Equiv.Perm.smul_def, Equiv.Perm.mul_apply]

/-- Every injective ordered prefix extends to a full slot permutation. -/
theorem probePermutationPrefix_surjective {m i : Nat} (hi : i ≤ m) :
    Function.Surjective (probePermutationPrefix hi) := by
  intro e
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding
    (probePrefixEmbedding hi) e
  refine ⟨τ, ?_⟩
  ext j
  have hj := DFunLike.congr_fun hτ j
  exact congrArg Fin.val hj

/-- Fibers of prefix restriction have equal cardinality. -/
theorem probePermutationPrefix_fiber_card_eq {m i : Nat} (hi : i ≤ m)
    (e₁ e₂ : Fin i ↪ Fin m) :
    ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      (fun σ => probePermutationPrefix hi σ = e₁)).card =
    ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      (fun σ => probePermutationPrefix hi σ = e₂)).card := by
  classical
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding e₁ e₂
  have hτinv : τ⁻¹ • e₂ = e₁ := by
    rw [← hτ]
    simp
  refine Finset.card_bij' (fun σ _ => τ * σ) (fun σ _ => τ⁻¹ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [probePermutationPrefix_mul, hσ, hτ]
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rw [probePermutationPrefix_mul, hσ, hτinv]
  · intro σ hσ
    simp
  · intro σ hσ
    simp

/-- A prescribed injective prefix has exactly {lit}`(m-i)!` extensions to a
permutation of all table slots. -/
theorem probePermutationPrefix_fiber_card {m i : Nat} (hi : i ≤ m)
    (e : Fin i ↪ Fin m) :
    ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      (fun σ => probePermutationPrefix hi σ = e)).card = (m - i).factorial := by
  classical
  let base : Fin i ↪ Fin m := probePrefixEmbedding hi
  let fiberCard := ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
    (fun σ => probePermutationPrefix hi σ = base)).card
  have htotal : m.factorial = m.descFactorial i * fiberCard := by
    have hpartition := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Equiv.Perm (Fin m))))
      (t := (Finset.univ : Finset (Fin i ↪ Fin m)))
      (f := probePermutationPrefix hi) (by simp)
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hpartition
    calc
      m.factorial = ∑ b : Fin i ↪ Fin m,
          ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
            (fun σ => probePermutationPrefix hi σ = b)).card := hpartition
      _ = ∑ _b : Fin i ↪ Fin m, fiberCard := by
        apply Finset.sum_congr rfl
        intro b hb
        exact probePermutationPrefix_fiber_card_eq hi b base
      _ = m.descFactorial i * fiberCard := by
        simp [Fintype.card_embedding_eq]
  have hfactorial : (m - i).factorial * m.descFactorial i = m.factorial :=
    Nat.factorial_mul_descFactorial hi
  have hprefixPos : 0 < m.descFactorial i := Nat.descFactorial_pos.mpr hi
  have hbase : fiberCard = (m - i).factorial := by
    apply Nat.eq_of_mul_eq_mul_left hprefixPos
    calc
      m.descFactorial i * fiberCard = m.factorial := htotal.symm
      _ = m.descFactorial i * (m - i).factorial := by
        rw [← hfactorial, Nat.mul_comm]
  calc
    ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
      (fun σ => probePermutationPrefix hi σ = e)).card = fiberCard :=
        probePermutationPrefix_fiber_card_eq hi e base
    _ = (m - i).factorial := hbase

/-- Restrict the codomain of an embedding to a finite occupied set. -/
def embeddingIntoOccupied {m i : Nat} (occupied : Finset (Fin m))
    (e : Fin i ↪ Fin m) (he : ∀ j, e j ∈ occupied) : Fin i ↪ occupied where
  toFun j := ⟨e j, he j⟩
  inj' _a _b hab := e.injective (Subtype.ext_iff.mp hab)

@[simp] theorem embeddingIntoOccupied_val {m i : Nat} (occupied : Finset (Fin m))
    (e : Fin i ↪ Fin m) (he : ∀ j, e j ∈ occupied) (j : Fin i) :
    ((embeddingIntoOccupied occupied e he j : occupied) : Fin m) = e j := rfl

/-- Number of injective ordered prefixes whose values all lie in a fixed
occupied set. -/
theorem occupiedPrefixEmbedding_card {m i : Nat} (occupied : Finset (Fin m)) :
    ((Finset.univ : Finset (Fin i ↪ Fin m)).filter
      (fun e => ∀ j, e j ∈ occupied)).card = occupied.card.descFactorial i := by
  classical
  calc
    ((Finset.univ : Finset (Fin i ↪ Fin m)).filter
      (fun e => ∀ j, e j ∈ occupied)).card =
        (Finset.univ : Finset (Fin i ↪ occupied)).card := by
      refine Finset.card_bij
        (fun e he => by
          have he' : ∀ j, e j ∈ occupied := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
          exact embeddingIntoOccupied occupied e he') ?_ ?_ ?_
      · intro e he
        simp
      · intro e₁ h₁ e₂ h₂ heq
        ext j
        have hj := congrArg Subtype.val (DFunLike.congr_fun heq j)
        have hfin : e₁ j = e₂ j := by
          simpa [embeddingIntoOccupied] using hj
        exact congrArg Fin.val hfin
      · intro e he
        let lifted : Fin i ↪ Fin m :=
          { toFun := fun j => e j
            inj' := fun a b hab => e.injective (Subtype.ext hab) }
        refine ⟨lifted, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro j
          exact (e j).property
        · ext j
          rfl
    _ = occupied.card.descFactorial i := by
      simp [Fintype.card_embedding_eq]

/-- The occupied-prefix event can be read from the restricted embedding. -/
theorem firstProbesOccupied_iff_prefix {m i : Nat} (occupied : Finset (Fin m))
    (hi : i ≤ m) (σ : Equiv.Perm (Fin m)) :
    firstProbesOccupied occupied i σ ↔
      ∀ j : Fin i, probePermutationPrefix hi σ j ∈ occupied := by
  constructor
  · intro h j
    exact h (probePrefixEmbedding hi j) j.isLt
  · intro h j hj
    let k : Fin i := ⟨j.val, hj⟩
    simpa [probePermutationPrefix, probePrefixEmbedding, k] using h k

/-- Full probe permutations whose first {lit}`i` positions are occupied. -/
noncomputable def occupiedPrefixPermutations {m : Nat}
    (occupied : Finset (Fin m)) (i : Nat) : Finset (Equiv.Perm (Fin m)) := by
  classical
  exact Finset.univ.filter (firstProbesOccupied occupied i)

/-- Exact number of full probe permutations whose first {lit}`i` positions
are occupied. -/
theorem firstProbesOccupied_card {m i : Nat} (occupied : Finset (Fin m))
    (hi : i ≤ m) :
    (occupiedPrefixPermutations occupied i).card =
      occupied.card.descFactorial i * (m - i).factorial := by
  classical
  let good := (Finset.univ : Finset (Fin i ↪ Fin m)).filter
    (fun e => ∀ j, e j ∈ occupied)
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Equiv.Perm (Fin m))) good
    (probePermutationPrefix hi)
  have hfilter :
      ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
        (fun σ => probePermutationPrefix hi σ ∈ good)) =
      occupiedPrefixPermutations occupied i := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, good,
      occupiedPrefixPermutations]
    exact (firstProbesOccupied_iff_prefix occupied hi σ).symm
  rw [hfilter] at hfiber
  calc
    (occupiedPrefixPermutations occupied i).card =
        ∑ e ∈ good,
          ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter
            (fun σ => probePermutationPrefix hi σ = e)).card := hfiber.symm
    _ = ∑ _e ∈ good, (m - i).factorial := by
      apply Finset.sum_congr rfl
      intro e he
      exact probePermutationPrefix_fiber_card hi e
    _ = good.card * (m - i).factorial := by simp
    _ = occupied.card.descFactorial i * (m - i).factorial := by
      rw [show good.card = occupied.card.descFactorial i by
        exact occupiedPrefixEmbedding_card occupied]

end Chapter11
end CLRS
