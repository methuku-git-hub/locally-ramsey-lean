module

public import LocallyRamsey.DensityComparison
public import LocallyRamsey.IndependentBlocks

public section

open scoped BigOperators

namespace LocallyRamsey

variable {Ω : Type*} [Fintype Ω]

/-- The affinity of two finite laws. -/
@[expose] noncomputable def affinity (P Q : FiniteLaw Ω) : ℝ :=
  ∑ z, Real.sqrt (P.prob z) * Real.sqrt (Q.prob z)

theorem affinity_symm (P Q : FiniteLaw Ω) : affinity P Q = affinity Q P := by
  simp only [affinity, mul_comm]

/-- The marginal on the first coordinate of a finite pair. -/
@[expose] def FiniteLaw.firstMarginal {B : Type*} [Fintype B] (P : FiniteLaw (Ω × B)) :
    FiniteLaw Ω where
  prob x := ∑ y, P.prob (x, y)
  nonneg x := Finset.sum_nonneg fun y _ => P.nonneg (x, y)
  total := by rw [← Fintype.sum_prod_type]; exact P.total

/-- Forgetting a coordinate cannot decrease affinity. -/
theorem affinity_le_affinity_firstMarginal {B : Type*} [Fintype B]
    (P Q : FiniteLaw (Ω × B)) : affinity P Q ≤ affinity P.firstMarginal Q.firstMarginal := by
  unfold affinity
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum (fun x _ => Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun y => P.nonneg (x, y)) (fun y => Q.nonneg (x, y)))

theorem affinity_eq_mean_ratio (P Q : FiniteLaw Ω) :
    affinity P Q = P.mean (fun z => Real.sqrt (Q.prob z / P.prob z)) := by
  classical
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : P.prob z = 0
  · simp [h]
  · change Real.sqrt (P.prob z) * Real.sqrt (Q.prob z) =
      P.prob z * Real.sqrt (Q.prob z / P.prob z)
    rw [Real.sqrt_div (Q.nonneg z)]
    have hpos := lt_of_le_of_ne (P.nonneg z) (fun h' => h h'.symm)
    have hs := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
    rw [Real.sq_sqrt (P.nonneg z), mul_comm]

theorem affinity_eq_one_sub_rootDistance (μ : FiniteLaw Ω) (a b : Ω → ℝ)
    (ha : ∀ z, 0 ≤ a z) (hb : ∀ z, 0 ≤ b z) (hsa : μ.mean a = 1) (hsb : μ.mean b = 1) :
    affinity (μ.withDensity a ha hsa) (μ.withDensity b hb hsb) =
      1 - rootDistance μ a b / 2 := by
  have haff : affinity (μ.withDensity a ha hsa) (μ.withDensity b hb hsb) =
      μ.mean (fun z => Real.sqrt (a z) * Real.sqrt (b z)) := by
    apply Finset.sum_congr rfl
    intro z _
    change Real.sqrt (μ.prob z * a z) * Real.sqrt (μ.prob z * b z) =
      μ.prob z * (Real.sqrt (a z) * Real.sqrt (b z))
    rw [Real.sqrt_mul (μ.nonneg z), Real.sqrt_mul (μ.nonneg z),
      mul_mul_mul_comm, Real.mul_self_sqrt (μ.nonneg z)]
  have hid : rootDistance μ a b =
      μ.mean a + μ.mean b + (-2) * μ.mean (fun z => Real.sqrt (a z) * Real.sqrt (b z)) := by
    have hFun : (fun z => (Real.sqrt (a z) - Real.sqrt (b z)) ^ 2) =
        fun z => (a z + b z) + (-2) * (Real.sqrt (a z) * Real.sqrt (b z)) := by
      funext z
      nlinarith only [Real.sq_sqrt (ha z), Real.sq_sqrt (hb z)]
    unfold rootDistance
    rw [hFun, μ.mean_add, μ.mean_add, μ.mean_mul_const]
  linarith only [haff, hid, hsa, hsb]

/-- Repeating an affinity test on independent groups. Absolute continuity
ensures that dividing by the reference likelihood is valid wherever the
observed law has positive mass. -/
theorem event_product_likelihood_le (R P Q : FiniteLaw Ω)
    (hSupport : ∀ z, 0 < R.prob z → 0 < P.prob z) (k : ℕ) {a : ℝ}
    (hmean : R.mean (fun z => Real.sqrt (Q.prob z / P.prob z)) ≤ a) :
    (FiniteLaw.product (fun _ : Fin k => R)).event (fun z =>
      (∏ i, P.prob (z i)) ≤ ∏ i, Q.prob (z i)) ≤ a ^ k := by
  classical
  let ν := FiniteLaw.product (fun _ : Fin k => R)
  let X := fun z => Real.sqrt (Q.prob z / P.prob z)
  let bad (z : Fin k → Ω) := ∏ i, P.prob (z i) ≤ ∏ i, Q.prob (z i)
  have hnonneg : 0 ≤ R.mean X := R.mean_nonneg fun _ => Real.sqrt_nonneg _
  have hpoint (z : Fin k → Ω) :
      ν.prob z * (if bad z then 1 else 0) ≤ ν.prob z * ∏ i, X (z i) := by
    by_cases hz : ν.prob z = 0
    · simp [hz]
    · refine mul_le_mul_of_nonneg_left ?_ (ν.nonneg z)
      by_cases hb : bad z
      · have hR (i : Fin k) : 0 < R.prob (z i) := by
          refine lt_of_le_of_ne (R.nonneg _) ?_
          intro heq
          exact hz (Finset.prod_eq_zero (Finset.mem_univ i) heq.symm)
        have hP : (0 : ℝ) < ∏ i, P.prob (z i) := Finset.prod_pos (fun i _ => hSupport _ (hR i))
        have hone : 1 ≤ (∏ i, Q.prob (z i)) / ∏ i, P.prob (z i) :=
          (one_le_div hP).mpr hb
        have hprod : (∏ i, X (z i)) = Real.sqrt ((∏ i, Q.prob (z i)) / ∏ i, P.prob (z i)) := by
          rw [← Finset.prod_div_distrib]
          exact (Real.sqrt_prod _ (fun i _ => div_nonneg (Q.nonneg _) (P.nonneg _))).symm
        simp only [hb, ite_true, hprod]
        simpa using Real.sqrt_le_sqrt hone
      · simp only [hb, ite_false]
        exact Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _
  have hE : ν.event bad ≤ ν.mean (fun z => ∏ i, X (z i)) := by
    rw [← ν.mean_indicator]
    exact Finset.sum_le_sum (fun z _ => hpoint z)
  refine hE.trans ?_
  rw [FiniteLaw.mean_product (fun _ : Fin k => R) (fun _ => X)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ hnonneg hmean k

end LocallyRamsey
