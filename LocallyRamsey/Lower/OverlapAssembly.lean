module

public import LocallyRamsey.Overlap
public import LocallyRamsey.Lower.Variance

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- In a group of (q) positions, count each vertex as many times as it
survives. Vertices surviving too rarely can be charged to a single set,
regardless of the subset (C) in which the retained mass is evaluated. -/
theorem mean_retained_positions_ge {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (q : ℕ) (hq : 0 < q) (w : Ω → V → ℝ) (hw : ∀ z x, 0 ≤ w z x)
    (C : Finset V) (bad : Ω → Finset V) (kept : Ω → Fin q → Finset V)
    {p : ℝ} (hp : 0 ≤ p)
    (hsurvive : ∀ z, ∀ x ∈ C, x ∉ bad z →
      p * (q : ℝ) ≤ ((Finset.univ.filter (fun i => x ∈ kept z i)).card : ℝ)) :
    p * (μ.mean (fun z => mass (w z) C) - μ.mean (fun z => mass (w z) (bad z))) ≤
      μ.mean (fun z => (∑ i, mass (w z) (C ∩ kept z i)) / q) := by
  classical
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpoint (z : Ω) : p * (mass (w z) C - mass (w z) (bad z)) ≤
      (∑ i, mass (w z) (C ∩ kept z i)) / q := by
    have heq : (∑ i, mass (w z) (C ∩ kept z i)) =
        ∑ x ∈ C, ((Finset.univ.filter (fun i => x ∈ kept z i)).card : ℝ) * w z x := by
      have hrow (i : Fin q) : mass (w z) (C ∩ kept z i) =
          ∑ x ∈ C, if x ∈ kept z i then w z x else 0 := by
        rw [mass, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
      simp only [hrow]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hsum : (p * q) * mass (w z) (C \ bad z) ≤
        ∑ x ∈ C, ((Finset.univ.filter (fun i => x ∈ kept z i)).card : ℝ) * w z x := by
      rw [mass, Finset.mul_sum]
      refine (Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right
        (hsurvive z x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2) (hw z x))).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun x _ _ => mul_nonneg (Nat.cast_nonneg _) (hw z x))
    have hsplit : mass (w z) (C \ bad z) + mass (w z) (C ∩ bad z) = mass (w z) C := by
      simp only [mass]
      rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun x hx hx' =>
         (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hx').2))]
      congr 1
      ext x
      by_cases h : x ∈ bad z <;> simp [h]
    rw [le_div_iff₀ hq', heq]
    have hmono : mass (w z) (C ∩ bad z) ≤ mass (w z) (bad z) :=
      mass_mono (hw z) Finset.inter_subset_right
    have hdiff : mass (w z) C - mass (w z) (bad z) ≤ mass (w z) (C \ bad z) := by
      linarith only [hsplit, hmono]
    exact (show p * (mass (w z) C - mass (w z) (bad z)) * q ≤
      (p * q) * mass (w z) (C \ bad z) by
        rw [mul_right_comm]
        exact mul_le_mul_of_nonneg_left hdiff (by positivity)).trans hsum
  have hh := μ.mean_mono hpoint
  rwa [μ.mean_mul_const, μ.mean_sub] at hh

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The mean over positions in Proposition 21. Marked mass and nonadjacent
pair mass are bounded at each position, and the normalizing constants
are bounded only on average. -/
theorem mean_overlap_positions_le {I Ω : Type*} [Fintype I] [Fintype Ω]
    (π : FiniteLaw I) (μ : I → FiniteLaw Ω) (w : I → Ω → V → ℝ)
    (B C : Finset V) (hCB : C ⊆ B) (hw : ∀ i z x, 0 ≤ w i z x)
    (hB : ∀ i z, mass (w i z) B ≤ 1)
    {γ δ v D A : ℝ} (ell : I → ℝ) (hell : ∀ i, 0 < ell i)
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hδγ : δ ≤ γ) (hv : 0 ≤ v)
    (hD : 0 < D) (hA : 0 ≤ A)
    (hbase : π.mean ell ≤ A * γ)
    (hmarked : ∀ i, (μ i).mean (fun z => mass (w i z) (marked G (w i z) B γ)) ≤ δ ^ 2)
    (hnonadj : ∀ i, (μ i).mean (fun z => ∑ x ∈ C, w i z x *
      mass (w i z) (nonNeighbors G C x)) ≤
      (δ + 4 * v / (D * ell i)) * (μ i).mean (fun z => mass (w i z) C)) :
    π.mean (fun i => ell i * (μ i).mean (fun z => mass (w i z) C)) ≤
      4 * v / D + 3 * A * γ ^ 2 := by
  have hi (i : I) := mean_position_mass_le G (μ i) (w i) B C hCB (hw i) (hB i)
    hγ hδ hv hD (hell i) (hmarked i) (hnonadj i)
  have hm : (γ + 2 * δ) * π.mean ell ≤ 3 * A * γ ^ 2 := by
    calc
      _ ≤ (γ + 2 * δ) * (A * γ) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ (3 * γ) * (A * γ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  refine (π.mean_mono hi).trans ?_
  rw [π.mean_add, π.mean_const, π.mean_mul_const]
  linarith only [hm]

end LocallyRamsey
