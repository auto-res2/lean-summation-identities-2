import Mathlib.Tactic

/-- The Gauss sum: twice the sum of `i` over `i < n + 1` equals `n * (n + 1)`. -/
theorem gauss_sum_mul_two (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring
