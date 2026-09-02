import CLRSLean.Research.ThreeDIC.AffineWindowLoad

/-!
# Research interface: balanced affine window load

This file freezes the exact translated-window count API for affine colorings
with a coprime horizontal or vertical coefficient.
-/

open CLRS.Research.ThreeDIC

#check affineWindowColorCount
#check affineGridColor_window_count_eq_of_coprime_alpha
#check affineGridColor_window_count_eq_of_coprime_beta
#check affineGridColor_window_count_eq_of_coprime_coefficient

example
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcop : Nat.Coprime K alpha) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K :=
  affineGridColor_window_count_eq_of_coprime_alpha
    M K alpha beta gamma p q c hK hKM hc hcop

example
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcop : Nat.Coprime K beta) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K :=
  affineGridColor_window_count_eq_of_coprime_beta
    M K alpha beta gamma p q c hK hKM hc hcop

example
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hunit : Nat.Coprime K alpha ∨ Nat.Coprime K beta) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K :=
  affineGridColor_window_count_eq_of_coprime_coefficient
    M K alpha beta gamma p q c hK hKM hc hunit

example : affineWindowColorCount 4 2 1 0 3 5 7 0 = 8 := by decide

example : affineWindowColorCount 4 2 0 1 3 5 7 1 = 8 := by decide
