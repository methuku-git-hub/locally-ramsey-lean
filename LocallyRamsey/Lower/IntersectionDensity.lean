module

public import LocallyRamsey.Lower.AffinityStabilization
public import LocallyRamsey.Lower.RepeatedPositions
public import LocallyRamsey.Overlap

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- Average product of the vertex weights over a region. -/
@[expose] noncomputable def intersectionDensity (L : Ω → V → ℝ)
    (B : Finset V) {q : ℕ} (ω : Fin q → Ω) : ℝ :=
  (∑ x ∈ B, ∏ i, L (ω i) x) / B.card

omit [DecidableEq V] [Fintype Ω] in
theorem intersectionDensity_nonneg (L : Ω → V → ℝ) (hL : ∀ s x, 0 ≤ L s x)
    (B : Finset V) {q : ℕ} (ω : Fin q → Ω) :
    0 ≤ intersectionDensity L B ω :=
  div_nonneg (Finset.sum_nonneg fun x _ => Finset.prod_nonneg fun i _ => hL (ω i) x)
    (Nat.cast_nonneg _)

omit [DecidableEq V] in
theorem mean_intersectionDensity (μ : FiniteLaw Ω) (L : Ω → V → ℝ)
    (B : Finset V) (hB : B.Nonempty) (hL : ∀ x ∈ B, μ.mean (fun ω => L ω x) = 1) (q : ℕ) :
    (FiniteLaw.product (fun _ : Fin q => μ)).mean (intersectionDensity L B) = 1 := by
  let ν := FiniteLaw.product (fun _ : Fin q => μ)
  have hB0 : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
  change ν.mean (fun ω => (∑ x ∈ B, ∏ i, L (ω i) x) / B.card) = 1
  simp only [div_eq_inv_mul]
  rw [ν.mean_mul_const, ν.mean_sum]
  have hp (x : V) (hx : x ∈ B) : ν.mean (fun ω => ∏ i, L (ω i) x) = 1 := by
    rw [FiniteLaw.mean_product (fun _ => μ) (fun _ ω => L ω x)]
    simp [hL x hx]
  simp only [Finset.sum_congr rfl hp, Finset.sum_const, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hB0]

/-- The mixture obtained by choosing one vertex of (B) and drawing
independent samples conditional on that vertex has the intersection
density relative to the biased product law. -/
theorem intersectionDensity_prob (μ : FiniteLaw Ω) (L : Ω → V → ℝ)
    (hL0 : ∀ s x, 0 ≤ L s x) (W B : Finset V) (hB : B.Nonempty) (hBW : B ⊆ W)
    (hL1 : ∀ x ∈ W, μ.mean (fun s => L s x) = 1)
    (q : ℕ) (ω : Fin q → Ω) :
    let R (x : V) := if hx : x ∈ W then
      FiniteLaw.product (fun _ : Fin q => μ.withDensity (fun s => L s x) (fun s => hL0 s x) (hL1 x hx))
      else FiniteLaw.product (fun _ : Fin q => μ)
    (vertexMixture R B hB).prob ω =
      (FiniteLaw.product (fun _ : Fin q => μ)).prob ω * intersectionDensity L B ω := by
  classical
  intro R
  change (∑ x ∈ B, (R x).prob ω) / B.card = _
  rw [intersectionDensity, ← mul_div_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun x hx => ?_)
  simp only [R, dite_eq_left (hBW hx), FiniteLaw.product, FiniteLaw.withDensity, Finset.prod_mul_distrib]

/-- Conditioning on one sample amounts to taking the mean of the other
factors over the vertices of that sample in the fixed region. -/
theorem intersectionDensity_cons_of_constant (L : Ω → V → ℝ)
    (B F : Finset V) (hFB : F ⊆ B) (s : Ω) {c : ℝ}
    (hrow : ∀ x ∈ B, L s x = if x ∈ F then c else 0) {q : ℕ} (ω : Fin q → Ω) :
    intersectionDensity L B (Fin.cons (α := fun _ => Ω) s ω) =
      (F.card * c / B.card) * intersectionDensity L F ω := by
  classical
  rw [intersectionDensity, intersectionDensity]
  have heq (x : V) (hx : x ∈ B) : (∏ i : Fin (q + 1), L ((Fin.cons (α := fun _ => Ω) s ω) i) x) =
      if x ∈ F then c * ∏ i, L (ω i) x else 0 := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hrow x hx, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl heq, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hFB, ← Finset.mul_sum]
  by_cases hF : F.Nonempty
  · have hc : (F.card : ℝ) ≠ 0 := by exact_mod_cast hF.card_ne_zero
    by_cases hB : (B.card : ℝ) = 0
    · simp [hB]
    · field_simp
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [he]

end LocallyRamsey
