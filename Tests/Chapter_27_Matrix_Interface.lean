import CLRSLean.Chapter_27

namespace CLRS.Chapter27

#check Costed
#check Costed.pure
#check Costed.charge
#check Costed.map
#check Costed.seq
#check Costed.par
#check Costed.par4
#check Costed.par8

example : (Costed.pure 11).work = 0 ∧ (Costed.pure 11).span = 0 := by
  native_decide

example : (Costed.charge 5 3 11).value = 11 ∧
    (Costed.charge 5 3 11).work = 5 ∧ (Costed.charge 5 3 11).span = 3 := by
  native_decide

example :
    let result := Costed.map (fun x : ℕ => x + 1) (Costed.charge 5 3 11)
    result.value = 12 ∧ result.work = 5 ∧ result.span = 3 := by
  native_decide

example : (Costed.map (fun x : ℕ => x + 1) (Costed.charge 5 3 11)).value = 12 := by
  simp

example :
    let result := Costed.seq (Costed.charge 2 3 4)
      (fun x => Costed.charge 5 7 (x + 1))
    result.value = 5 ∧ result.work = 7 ∧ result.span = 10 := by
  native_decide

example :
    let result := Costed.par (Costed.charge 2 3 4) (Costed.charge 5 7 6)
    result.value = (4, 6) ∧ result.work = 8 ∧ result.span = 8 := by
  native_decide

example :
    let result := Costed.par4 (Costed.pure 1) (Costed.pure 2)
      (Costed.pure 3) (Costed.pure 4)
    result.value = ((1, 2), (3, 4)) ∧ result.work = 3 ∧ result.span = 2 := by
  native_decide

example :
    let result := Costed.par8 (Costed.pure 1) (Costed.pure 2)
      (Costed.pure 3) (Costed.pure 4) (Costed.pure 5) (Costed.pure 6)
      (Costed.pure 7) (Costed.pure 8)
    result.value = (((1, 2), (3, 4)), ((5, 6), (7, 8))) ∧
      result.work = 7 ∧ result.span = 3 := by
  native_decide

#check pAdd
#check pAdd_value
#check pAdd_correct
#print axioms pAdd_correct

#check pMatMul
#check pMatMul_value
#check pMatMul_correct
#print axioms pMatMul_correct

example :
    let result := pAdd ℤ 0 7 (-2)
    result.value = 5 ∧ result.work = 1 ∧ result.span = 1 := by
  norm_num [pAdd, Costed.charge]

example :
    let A : Chapter04.SqMat ℤ 1 := !![1, 2; 3, 4]
    let B : Chapter04.SqMat ℤ 1 := !![5, 6; 7, 8]
    let result := pAdd ℤ 1 A B
    result.value = !![6, 8; 10, 12] ∧
      result.work = 7 ∧ result.span = 3 := by
  dsimp only
  constructor
  · funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pAdd, Costed.par4, Costed.par, Costed.map, Costed.charge]
  · norm_num [pAdd, Costed.par4, Costed.par, Costed.map, Costed.charge]

example (A B : Chapter04.SqMat ℤ 1) :
    (pAdd ℤ 1 A B).value = A + B := by
  exact pAdd_correct ℤ 1 A B

example :
    let result := pMatMul ℤ 0 7 (-2)
    result.value = -14 ∧ result.work = 1 ∧ result.span = 1 := by
  norm_num [pMatMul, Costed.charge]

example :
    let A : Chapter04.SqMat ℤ 1 := !![1, 2; 3, 4]
    let B : Chapter04.SqMat ℤ 1 := !![5, 6; 7, 8]
    let result := pMatMul ℤ 1 A B
    result.value = !![19, 22; 43, 50] ∧
      result.work = 22 ∧ result.span = 7 := by
  dsimp only
  constructor
  · funext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pMatMul, pAdd, Costed.seq, Costed.par8, Costed.par4,
        Costed.par, Costed.map, Costed.charge]
  · norm_num [pMatMul, pAdd, Costed.seq, Costed.par8, Costed.par4,
      Costed.par, Costed.map, Costed.charge]

example (A B : Chapter04.SqMat ℤ 1) :
    (pMatMul ℤ 1 A B).value = A * B := by
  exact pMatMul_correct ℤ 1 A B

end CLRS.Chapter27
