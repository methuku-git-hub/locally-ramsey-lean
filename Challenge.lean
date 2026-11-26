module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# Upper and lower bounds for locally Ramsey graphs

These are the two inequalities in Theorem 1 of the revised Nov 23 manuscript
of Balogh, Bucić, Luo and Methuku. The lower bound has exponent $7/2$ with
a power of the iterated base-two logarithm in the denominator. The upper bound is asymptotic
with leading coefficient $9/2$ in the base-two logarithm of the threshold.
-/

namespace LocallyRamsey

/-- Every set of exactly `m` vertices contains both an `r`-clique and
an independent set of order `r`. Above the graph order the condition is vacuous. -/
def IsLocallyRamsey {V : Type*} (G : SimpleGraph V) (m r : ℕ) : Prop :=
  ∀ A : Finset V, A.card = m →
    (∃ K : Finset V, K ⊆ A ∧ G.IsNClique r K) ∧
    (∃ I : Finset V, I ⊆ A ∧ Gᶜ.IsNClique r I)

/-- The least local threshold achievable on `n` vertices.
The set being minimized over contains `n + 1`, by vacuity. -/
noncomputable def threshold (n r : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ G : SimpleGraph (Fin n), IsLocallyRamsey G m r}

/-- The integer target order in the manuscript, namely the ceiling of the
base-two logarithm of the graph order. -/
noncomputable def target (n : ℕ) : ℕ :=
  ⌈Real.logb 2 (n : ℝ)⌉₊

/-- The lower bound in Theorem 1, with base-two logarithms. -/
theorem lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (Real.logb 2 (n : ℝ)) ^ (7 / 2 : ℝ) / (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 24
        < (threshold n (target n) : ℝ) := by
  sorry

/-- The upper bound in Theorem 1. Every coefficient strictly greater
than `9/2` works for all sufficiently large graph orders. -/
theorem upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (threshold n (target n) : ℝ) ≤
        (2 : ℝ) ^ ((9 / 2 + ε) * (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2) := by
  sorry

end LocallyRamsey
