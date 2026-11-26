module

public import LocallyRamsey.Upper.LocalBound
public import LocallyRamsey.Lower.MainBound

public section

namespace LocallyRamsey

/-- The lower bound in Theorem 1, with base-two logarithms. -/
theorem lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (Real.logb 2 (n : ℝ)) ^ (7 / 2 : ℝ) / (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 24
        < (threshold n (target n) : ℝ) :=
  main_lower_bound

/-- The upper bound in Theorem 1, with each fixed coefficient greater than
`9/2`. -/
theorem upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (threshold n (target n) : ℝ) ≤
        (2 : ℝ) ^ ((9 / 2 + ε) * (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2) :=
  BinaryTree.main_upper_bound

end LocallyRamsey
