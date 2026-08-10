import Mathlib.Tactic

example (K : ℕ) (A B C : ℝ) : A - B * (∑ k ∈ Finset.range (K + 1), (C - C)) + (↑K + 1) * B ≤
    A - B * (∑ k ∈ Finset.range (K + 1), (C - C)) + ↑(K + 1) * B := by
  norm_cast
  ring_nf

example (K : ℕ) (A B C : ℝ) : A - B * (∑ k ∈ Finset.range (K + 1), (C - C)) + (↑K + 1) * B ≤
    A - B * (∑ k ∈ Finset.range (K + 1), (C - C)) + ↑(K + 1) * B := by
  ring_nf
  norm_num
