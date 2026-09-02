import CLRSLean.FourthEdition.Chapter_30.Section_30_2_DFT_And_FFT.S2_DFT

/-! # Chapter 30.2: Fourier inversion and convolution

This module proves the algebraic inverse of the generic DFT and then connects
pointwise multiplication in Fourier space to cyclic convolution.
-/

namespace CLRS
namespace Chapter30

open Polynomial

/-- The inverse DFT uses the inverse root and normalizes by the transform
length. -/
def idft [Field K] {n : Nat} (omega : K) (a : CoeffVector K n) :
    CoeffVector K n :=
  fun k => (n : K)⁻¹ * dft omega⁻¹ a k

/-- A positive natural has nonzero image in a characteristic-zero field. -/
theorem natCast_ne_zero_of_pos [Field K] [CharZero K]
    {n : Nat} (hn : 0 < n) :
    (n : K) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt hn

/-- Applying the inverse transform after the forward transform recovers the
input vector. -/
theorem idft_dft [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n)
    (a : CoeffVector K n) :
    idft omega (dft omega a) = a := by
  funext k
  change (n : K)⁻¹ *
      (∑ i : Fin n, (∑ j : Fin n,
        a j * omega ^ (j.1 * i.1)) * omega⁻¹ ^ (i.1 * k.1)) = a k
  calc
    (n : K)⁻¹ *
        (∑ i : Fin n, (∑ j : Fin n,
          a j * omega ^ (j.1 * i.1)) * omega⁻¹ ^ (i.1 * k.1)) =
        (n : K)⁻¹ *
          (∑ i : Fin n, ∑ j : Fin n,
            (a j * omega ^ (j.1 * i.1)) *
              omega⁻¹ ^ (i.1 * k.1)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ = (n : K)⁻¹ *
          (∑ j : Fin n, ∑ i : Fin n,
            (a j * omega ^ (j.1 * i.1)) *
              omega⁻¹ ^ (i.1 * k.1)) := by
          rw [Finset.sum_comm]
    _ = (n : K)⁻¹ *
          (∑ j : Fin n, a j *
            (∑ i : Fin n,
              omega ^ (i.1 * j.1) * omega⁻¹ ^ (i.1 * k.1))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Nat.mul_comm j.1 i.1]
          ring
    _ = (n : K)⁻¹ *
          (∑ j : Fin n, a j * (if j = k then (n : K) else 0)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [root_sum_difference_orthogonality hn homega j k]
    _ = a k := by
          simp only [mul_ite, mul_zero]
          rw [Finset.sum_ite_eq' Finset.univ k,
            if_pos (Finset.mem_univ k)]
          calc
            (n : K)⁻¹ * (a k * (n : K)) =
                a k * ((n : K)⁻¹ * (n : K)) := by ring
            _ = a k := by
              rw [inv_mul_cancel₀ (natCast_ne_zero_of_pos hn), mul_one]

/-- Applying the forward transform after the inverse transform also recovers
the input vector. -/
theorem dft_idft [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n)
    (a : CoeffVector K n) :
    dft omega (idft omega a) = a := by
  have hinv := idft_dft hn (primitiveRoot_inv homega) a
  have hinv' :
      (n : K)⁻¹ • dft omega (dft omega⁻¹ a) = a := by
    calc
      (n : K)⁻¹ • dft omega (dft omega⁻¹ a) =
          idft omega⁻¹ (dft omega⁻¹ a) := by
        funext k
        simp only [idft, inv_inv, Pi.smul_apply, smul_eq_mul]
      _ = a := hinv
  have hidft : idft omega a = (n : K)⁻¹ • dft omega⁻¹ a := by
    funext k
    rfl
  calc
    dft omega (idft omega a) =
        dft omega ((n : K)⁻¹ • dft omega⁻¹ a) := by rw [hidft]
    _ = (n : K)⁻¹ • dft omega (dft omega⁻¹ a) :=
      dft_smul omega (n : K)⁻¹ (dft omega⁻¹ a)
    _ = a := hinv'

/-- A primitive-root DFT of positive length is injective. -/
theorem dft_injective [Field K] [CharZero K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n) :
    Function.Injective
      (dft omega : CoeffVector K n → CoeffVector K n) := by
  intro a b h
  calc
    a = idft omega (dft omega a) := (idft_dft hn homega a).symm
    _ = idft omega (dft omega b) := congrArg (idft omega) h
    _ = b := idft_dft hn homega b

/-- Total subtraction modulo a positive vector length. -/
def cyclicSub {n : Nat} (hn : 0 < n) (k j : Fin n) : Fin n :=
  ⟨(k.1 + n - j.1) % n, Nat.mod_lt _ hn⟩

/-- Cyclic convolution of two fixed-capacity vectors. -/
def cyclicConvolution [Semiring K] {n : Nat} (hn : 0 < n)
    (a b : CoeffVector K n) : CoeffVector K n :=
  fun k => ∑ j : Fin n, a j * b (cyclicSub hn k j)

/-- The concrete modular subtraction agrees with subtraction in `ZMod n`. -/
private theorem finEquiv_cyclicSub {n : Nat} [NeZero n] (hn : 0 < n)
    (k j : Fin n) :
    ZMod.finEquiv n (cyclicSub hn k j) =
      ZMod.finEquiv n k - ZMod.finEquiv n j := by
  rw [show cyclicSub hn k j =
      (ZMod.finEquiv n).symm
        (ZMod.finEquiv n k - ZMod.finEquiv n j) by
    cases n with
    | zero => omega
    | succ n =>
      apply Fin.ext
      simp only [cyclicSub, ZMod.finEquiv]
      congr 1
      omega]
  exact Equiv.apply_symm_apply _ _

/-- For fixed `j`, subtracting `j` modulo `n` permutes every index. -/
private def cyclicSubEquiv {n : Nat} [NeZero n] (j : Fin n) :
    Fin n ≃ Fin n :=
  (ZMod.finEquiv n).toEquiv.trans
    ((Equiv.subRight (ZMod.finEquiv n j)).trans
      (ZMod.finEquiv n).toEquiv.symm)

/-- The cyclic-subtraction equivalence computes the concrete modular index. -/
private theorem cyclicSubEquiv_apply {n : Nat} [NeZero n]
    (hn : 0 < n) (k j : Fin n) :
    cyclicSubEquiv j k = cyclicSub hn k j := by
  apply (ZMod.finEquiv n).injective
  rw [finEquiv_cyclicSub hn k j]
  simp [cyclicSubEquiv]

/-- A cyclicly subtracted index reconstructs the original index modulo `n`. -/
private theorem cyclicSub_add_modEq {n : Nat} [NeZero n]
    (hn : 0 < n) (k j : Fin n) :
    k.1 ≡ j.1 + (cyclicSub hn k j).1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add]
  rw [← finEquiv_eq_natCast k, ← finEquiv_eq_natCast j,
    ← finEquiv_eq_natCast (cyclicSub hn k j),
    finEquiv_cyclicSub hn k j]
  abel

/-- A primitive root turns modular index reconstruction into multiplication
of powers. -/
private theorem pow_index_eq_mul_pow_cyclicSub [Field K]
    {n : Nat} [NeZero n] (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega n) (k j r : Fin n) :
    omega ^ (k.1 * r.1) =
      omega ^ (j.1 * r.1) *
        omega ^ ((cyclicSub hn k j).1 * r.1) := by
  have hmod :
      k.1 * r.1 ≡
        j.1 * r.1 + (cyclicSub hn k j).1 * r.1 [MOD n] := by
    simpa only [Nat.add_mul] using
      (cyclicSub_add_modEq hn k j).mul_right r.1
  rw [← pow_add]
  exact pow_eq_pow_of_modEq hmod homega.pow_eq_one

/-- Reindexing by cyclic subtraction separates one Fourier kernel factor. -/
private theorem sum_cyclicSub_mul_pow [Field K] {n : Nat} (hn : 0 < n)
    {omega : K} (homega : IsPrimitiveRoot omega n)
    (b : CoeffVector K n) (j r : Fin n) :
    (∑ k : Fin n,
      b (cyclicSub hn k j) * omega ^ (k.1 * r.1)) =
      omega ^ (j.1 * r.1) *
        (∑ l : Fin n, b l * omega ^ (l.1 * r.1)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let e : Fin n ≃ Fin n := cyclicSubEquiv j
  calc
    (∑ k : Fin n,
        b (cyclicSub hn k j) * omega ^ (k.1 * r.1)) =
        ∑ k : Fin n, b (e k) * omega ^ (k.1 * r.1) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [cyclicSubEquiv_apply hn k j]
    _ = ∑ l : Fin n,
          b l * omega ^ ((e.symm l).1 * r.1) := by
      simpa only [Equiv.symm_apply_apply] using
        (e.sum_comp
          (fun l : Fin n =>
            b l * omega ^ ((e.symm l).1 * r.1)))
    _ = ∑ l : Fin n,
          b l * (omega ^ (j.1 * r.1) * omega ^ (l.1 * r.1)) := by
      apply Finset.sum_congr rfl
      intro l _
      have he : cyclicSub hn (e.symm l) j = l := by
        rw [← cyclicSubEquiv_apply hn (e.symm l) j]
        exact e.apply_symm_apply l
      rw [pow_index_eq_mul_pow_cyclicSub hn homega (e.symm l) j r, he]
    _ = omega ^ (j.1 * r.1) *
          (∑ l : Fin n, b l * omega ^ (l.1 * r.1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- The DFT sends cyclic convolution to pointwise multiplication. -/
theorem dft_cyclicConvolution [Field K] [CharZero K]
    {n : Nat} (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega n)
    (a b : CoeffVector K n) :
    dft omega (cyclicConvolution hn a b) =
      pointwiseMul (dft omega a) (dft omega b) := by
  funext r
  change (∑ k : Fin n,
      (∑ j : Fin n, a j * b (cyclicSub hn k j)) *
        omega ^ (k.1 * r.1)) =
    (∑ j : Fin n, a j * omega ^ (j.1 * r.1)) *
      (∑ l : Fin n, b l * omega ^ (l.1 * r.1))
  calc
    (∑ k : Fin n,
        (∑ j : Fin n, a j * b (cyclicSub hn k j)) *
          omega ^ (k.1 * r.1)) =
        ∑ k : Fin n, ∑ j : Fin n,
          (a j * b (cyclicSub hn k j)) *
            omega ^ (k.1 * r.1) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
    _ = ∑ j : Fin n, ∑ k : Fin n,
          (a j * b (cyclicSub hn k j)) *
            omega ^ (k.1 * r.1) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, a j *
          (∑ k : Fin n,
            b (cyclicSub hn k j) * omega ^ (k.1 * r.1)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j : Fin n, a j *
          (omega ^ (j.1 * r.1) *
            (∑ l : Fin n, b l * omega ^ (l.1 * r.1))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [sum_cyclicSub_mul_pow hn homega b j r]
    _ = (∑ j : Fin n, a j * omega ^ (j.1 * r.1)) *
          (∑ l : Fin n, b l * omega ^ (l.1 * r.1)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Inverse-transforming pointwise products recovers cyclic convolution. -/
theorem idft_pointwiseMul [Field K] [CharZero K]
    {n : Nat} (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega n)
    (a b : CoeffVector K n) :
    idft omega (pointwiseMul (dft omega a) (dft omega b)) =
      cyclicConvolution hn a b := by
  rw [← dft_cyclicConvolution hn homega, idft_dft hn homega]

/-- When a polynomial product fits in the vector capacity, cyclic convolution
has no wrapped contribution and equals its coefficient vector. -/
theorem cyclicConvolution_eq_coeffVector_mul [Field K]
    {n : Nat} (hn : 0 < n) (p q : K[X])
    (hfit : (p * q).degree < n) :
    cyclicConvolution hn (coeffVector n p) (coeffVector n q) =
      coeffVector n (p * q) := by
  by_cases hp : p = 0
  · subst p
    funext k
    simp [cyclicConvolution, coeffVector]
  by_cases hq : q = 0
  · subst q
    funext k
    simp [cyclicConvolution, coeffVector]
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  have hnatfit : p.natDegree + q.natDegree < n := by
    rw [← Polynomial.natDegree_mul hp hq]
    exact (Polynomial.natDegree_lt_iff_degree_lt hpq).mpr hfit
  funext k
  change (∑ j : Fin n,
      p.coeff j.1 * q.coeff (cyclicSub hn k j).1) =
    (p * q).coeff k.1
  rw [show (∑ j : Fin n,
      p.coeff j.1 * q.coeff (cyclicSub hn k j).1) =
      ∑ j ∈ Finset.range n,
        p.coeff j * q.coeff
          (cyclicSub hn k ⟨j % n, Nat.mod_lt _ hn⟩).1 by
    simpa [Nat.mod_eq_of_lt] using
      (Fin.sum_univ_eq_sum_range
        (fun j : Nat =>
          p.coeff j * q.coeff
            (cyclicSub hn k ⟨j % n, Nat.mod_lt _ hn⟩).1) n)]
  rw [Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => p.coeff i * q.coeff j) k.1]
  calc
    (∑ j ∈ Finset.range n,
        p.coeff j *
          q.coeff (cyclicSub hn k
            ⟨j % n, Nat.mod_lt _ hn⟩).1) =
        ∑ j ∈ Finset.range (k.1 + 1),
          p.coeff j *
            q.coeff (cyclicSub hn k
              ⟨j % n, Nat.mod_lt _ hn⟩).1 := by
      symm
      apply Finset.sum_subset
      · intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega
      · intro j hjn hjk
        simp only [Finset.mem_range] at hjn hjk
        have hkj : k.1 < j := by omega
        have hjcast :
            (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j, hjn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hjn
        have hcyc :
            (cyclicSub hn k
              ⟨j % n, Nat.mod_lt _ hn⟩).1 = k.1 + n - j := by
          rw [hjcast]
          simp only [cyclicSub]
          rw [Nat.mod_eq_of_lt (by omega)]
        by_contra hterm
        have hpcoeff : p.coeff j ≠ 0 := by
          intro hz
          exact hterm (by simp [hz])
        have hqcoeff :
            q.coeff (cyclicSub hn k
              ⟨j % n, Nat.mod_lt _ hn⟩).1 ≠ 0 := by
          intro hz
          exact hterm (by simp [hz])
        have hjdeg : j ≤ p.natDegree :=
          Polynomial.le_natDegree_of_ne_zero hpcoeff
        have hcycdeg :
            (cyclicSub hn k
              ⟨j % n, Nat.mod_lt _ hn⟩).1 ≤ q.natDegree :=
          Polynomial.le_natDegree_of_ne_zero hqcoeff
        omega
    _ = ∑ j ∈ Finset.range (k.1 + 1),
          p.coeff j * q.coeff (k.1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      have hjn : j < n := by omega
      have hjk : j ≤ k.1 := by omega
      have hjcast :
          (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨j, hjn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hjn
      congr 2
      rw [hjcast]
      simp only [cyclicSub]
      rw [show k.1 + n - j = n + (k.1 - j) by omega]
      have hlt : k.1 - j < n :=
        lt_of_le_of_lt (Nat.sub_le _ _) k.2
      simp [Nat.add_mod, Nat.mod_eq_of_lt hlt]

end Chapter30
end CLRS
