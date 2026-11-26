module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-! # Definitions shared with the advertised locally Ramsey bounds -/

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

end LocallyRamsey
