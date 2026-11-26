module

public import LocallyRamsey.Sampling
public import LocallyRamsey.DensityComparison
public import LocallyRamsey.Lower.Variance

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- The weight of a vertex in a biased sample is its conditional likelihood
relative to the common sample law. The equality holds also at zero density. -/
theorem biasedLaw_prob_mul_weight (W : Finset V) (hW : W.Nonempty)
    (μ : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    {p : ℝ} (hp : 0 < p) (hprob : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p)
    {x : V} (hx : x ∈ W) (ω : Ω) :
    (biasedLaw W hW μ contains p hp hprob).prob ω * sampleWeight W contains ω x =
      μ.prob ω * (if contains ω x then 1 else 0) / p := by
  simp only [biasedLaw, sampleWeight]
  by_cases h : contains ω x
  · simp only [h, ite_true, mul_one]
    field_simp [(sampleDensity_pos hx h).ne', hp.ne']
  · simp [h]

/-- Under the law at a fixed vertex, a retention rule that only keeps sampled
vertices has its original marginal divided by the inclusion probability. -/
theorem at_vertex_retention (W : Finset V) (hW : W.Nonempty)
    (μ : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    {p : ℝ} (hp : 0 < p) (hprob : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p)
    {x : V} (hx : x ∈ W) (keep : Ω → Prop) [DecidablePred keep] (hkeep : ∀ ω, keep ω → contains ω x) :
    (biasedLaw W hW μ contains p hp hprob).mean
        (fun ω => sampleWeight W contains ω x * (if keep ω then 1 else 0)) =
      μ.event keep / p := by
  classical
  rw [← μ.mean_indicator keep, FiniteLaw.mean, FiniteLaw.mean, Finset.sum_div]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [← mul_assoc, biasedLaw_prob_mul_weight W hW μ contains hp hprob hx]
  by_cases h : keep ω
  · simp [h, hkeep ω h]
  · simp [h]

/-- Independent repetitions of a sample rule, viewed from a vertex. The
density of their joint law is the product of the individual densities. -/
theorem mean_weighted_product (μ : FiniteLaw Ω) (L : Ω → ℝ)
    (hL : ∀ ω, 0 ≤ L ω) (hmean : μ.mean L = 1) {q : ℕ}
    (f : (Fin q → Ω) → ℝ) :
    (FiniteLaw.product (fun _ : Fin q => μ)).mean
        (fun ω => (∏ i, L (ω i)) * f ω) =
      (FiniteLaw.product (fun _ : Fin q => μ.withDensity L hL hmean)).mean f := by
  simp only [FiniteLaw.mean, FiniteLaw.product, FiniteLaw.withDensity,
    Finset.prod_mul_distrib, mul_assoc]

/-- Expected weight of the vertices retained too few times in a fixed
group. The exceptions are measured under a uniform choice of its vertex. -/
theorem mean_weight_too_few_retained_le (μ : FiniteLaw Ω) {q : ℕ}
    (B E : Finset V) (hE : E ⊆ B) (L : Ω → V → ℝ)
    (hL : ∀ s x, 0 ≤ L s x) (hmean : ∀ x ∈ B, μ.mean (fun s => L s x) = 1)
    (F : Ω → Finset V) {γ : ℝ} (hγ : 0 ≤ γ)
    (hsurvive : ∀ x ∈ B, x ∉ E →
      γ / 2 ≤ μ.mean (fun s => L s x * (if x ∈ F s then 1 else 0))) :
    (FiniteLaw.product (fun _ : Fin q => μ)).mean (fun ω =>
      (∑ x ∈ B, (∏ i, L (ω i) x) *
        (if ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * q / 4
         then 1 else 0)) / B.card) ≤
      ((E.card : ℝ) / B.card) + Real.exp (-(γ * q) / 16) := by
  classical
  let τ := FiniteLaw.product (fun _ : Fin q => μ)
  let bad (x : V) (ω : Fin q → Ω) :=
    ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * q / 4
  have hper (x : V) (hx : x ∈ B) : τ.mean (fun ω =>
      (∏ i, L (ω i) x) * (if bad x ω then 1 else 0)) ≤
      if x ∈ E then 1 else Real.exp (-(γ * q) / 16) := by
    let P := μ.withDensity (fun s => L s x) (fun s => hL s x) (hmean x hx)
    let ν := FiniteLaw.product (fun _ : Fin q => P)
    let X : Fin q → Ω → ℝ := fun _ s => if x ∈ F s then 1 else 0
    rw [mean_weighted_product μ _ (fun s => hL s x) (hmean x hx)]
    change ν.mean (fun ω => if bad x ω then 1 else 0) ≤ _
    rw [ν.mean_indicator]
    by_cases he : x ∈ E
    · rw [ite_eq_left he]
      rw [← ν.mean_indicator]
      have hle := ν.mean_mono (X := fun ω => if bad x ω then 1 else 0)
        (Y := fun _ => 1) (fun ω => by split <;> norm_num)
      exact hle.trans_eq (ν.mean_const 1)
    · rw [ite_eq_right he]
      have hm0 : γ * q / 2 ≤ ∑ i, P.mean (X i) := by
        simp only [X, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        change γ * q / 2 ≤ q * P.mean (fun s => if x ∈ F s then 1 else 0)
        have hv : γ / 2 ≤ P.mean (fun s => if x ∈ F s then 1 else 0) := by
          simpa only [P, FiniteLaw.withDensity, FiniteLaw.mean, mul_assoc] using hsurvive x hx he
        linarith only [mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg q)]
      have hb (ω : Fin q → Ω) : bad x ω →
          ∑ i, X i (ω i) ≤ (∑ i, P.mean (X i)) / 2 := by
        intro h
        have hcard : (∑ i, X i (ω i)) =
            ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) := by
          simp [X]
        rw [hcard]
        change ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * q / 4 at h
        linarith only [h, hm0]
      refine (ν.event_mono hb).trans ((FiniteLaw.prob_sum_le_half_mean (fun _ => P) X
        (fun i s => by dsimp [X]; split <;> norm_num)).trans ?_)
      exact Real.exp_le_exp.mpr (by linarith only [hm0])
  have hsum : (∑ x ∈ B, τ.mean (fun ω => (∏ i, L (ω i) x) *
      (if bad x ω then 1 else 0))) ≤ (E.card : ℝ) + B.card * Real.exp (-(γ * q) / 16) := by
    refine (Finset.sum_le_sum (fun x hx => hper x hx)).trans ?_
    have hpt (x : V) : (if x ∈ E then 1 else Real.exp (-(γ * q) / 16)) ≤
        (if x ∈ E then 1 else (0 : ℝ)) + Real.exp (-(γ * q) / 16) := by
      by_cases h : x ∈ E <;> simp [h, (Real.exp_pos _).le]
    refine (Finset.sum_le_sum (fun x _ => hpt x)).trans_eq ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hE]
    simp
  change τ.mean (fun ω => (∑ x ∈ B, (∏ i, L (ω i) x) *
    (if bad x ω then 1 else 0)) / B.card) ≤ _
  simp_rw [div_eq_inv_mul]
  rw [τ.mean_mul_const, τ.mean_sum]
  by_cases hB : B.card = 0
  · simp [hB, (Real.exp_pos _).le]
  · have hBr : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB
    refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq ?_
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hBr, one_mul]
    simp only [div_eq_inv_mul]

end LocallyRamsey
