module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

public section

namespace LocallyRamsey

open scoped BigOperators

/-- A probability distribution on a finite type, with real-valued masses. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  prob : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ prob ω
  total : ∑ ω, prob ω = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

@[expose] def mean (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.prob ω * X ω

theorem mean_mono (μ : FiniteLaw Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    μ.mean X ≤ μ.mean Y := by
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω)

theorem mean_nonneg (μ : FiniteLaw Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ μ.mean X := Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (h ω)

theorem mean_add (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.mean (fun ω => X ω + Y ω) = μ.mean X + μ.mean Y := by
  simp [mean, mul_add, Finset.sum_add_distrib]

theorem mean_mul_const (μ : FiniteLaw Ω) (a : ℝ) (X : Ω → ℝ) :
    μ.mean (fun ω => a * X ω) = a * μ.mean X := by
  simp [mean, Finset.mul_sum, mul_left_comm]

theorem mean_sum {κ : Type*} (μ : FiniteLaw Ω) (A : Finset κ) (X : κ → Ω → ℝ) :
    μ.mean (fun ω => ∑ x ∈ A, X x ω) = ∑ x ∈ A, μ.mean (X x) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Probability of any event in a finite law. -/
noncomputable def event (μ : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω ∈ Finset.univ.filter P, μ.prob ω

theorem event_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    μ.event P ≤ μ.event Q := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun ω _ _ => μ.nonneg ω)
  intro ω hω
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ ω, h ω (Finset.mem_filter.mp hω).2⟩

theorem mean_indicator (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    μ.mean (fun ω => if P ω then 1 else 0) = μ.event P := by
  classical
  simp only [mean, event, Finset.sum_filter, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem mean_const (μ : FiniteLaw Ω) (a : ℝ) : μ.mean (fun _ => a) = a := by
  rw [mean, ← Finset.sum_mul, μ.total, one_mul]

theorem sq_mean_le_mean_sq (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.mean X ^ 2 ≤ μ.mean (fun ω => X ω ^ 2) := by
  let m := μ.mean X
  have h := μ.mean_nonneg (X := fun ω => (X ω - m) ^ 2) (fun ω => sq_nonneg _)
  have hid : (fun ω => (X ω - m) ^ 2) =
      fun ω => (X ω ^ 2 + (-2 * m) * X ω) + m ^ 2 := by
    funext ω
    ring
  rw [hid, μ.mean_add, μ.mean_add, μ.mean_mul_const, μ.mean_const] at h
  change m ^ 2 ≤ _
  nlinarith only [h]

/-- Markov's inequality for the mass of a threshold event. -/
theorem prob_ge_le (μ : FiniteLaw Ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω)
    {a : ℝ} (ha : 0 < a) :
    (∑ ω ∈ Finset.univ.filter (fun ω => a ≤ X ω), μ.prob ω) ≤ μ.mean X / a := by
  classical
  rw [le_div_iff₀ ha, Finset.sum_mul]
  calc
    _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω => a ≤ X ω), μ.prob ω * X ω :=
      Finset.sum_le_sum fun ω hω =>
        mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hω).2 (μ.nonneg ω)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun ω _ _ => mul_nonneg (μ.nonneg ω) (hX ω)

/-- Taking an exponential moment of a variable valued in `[0,1]`. -/
theorem mean_exp_le (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    μ.mean (fun ω => Real.exp (t * X ω)) ≤
      Real.exp ((Real.exp t - 1) * μ.mean X) := by
  have hchord (ω : Ω) : Real.exp (t * X ω) ≤
      1 + (Real.exp t - 1) * X ω := by
    have hx : 0 ≤ X ω ∧ X ω ≤ 1 := hX ω
    have hweights : 1 - X ω + X ω = 1 := sub_add_cancel _ _
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
      (sub_nonneg.mpr hx.2) hx.1 hweights
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    rw [mul_comm t]
    linarith
  calc
    _ ≤ μ.mean (fun ω => 1 + (Real.exp t - 1) * X ω) := μ.mean_mono hchord
    _ = ((Real.exp t - 1) * μ.mean X) + 1 := by
      rw [μ.mean_add, μ.mean_const, μ.mean_mul_const, add_comm]
    _ ≤ _ := Real.add_one_le_exp _

theorem event_ge_le (μ : FiniteLaw Ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω)
    {a : ℝ} (ha : 0 < a) : μ.event (fun ω => a ≤ X ω) ≤ μ.mean X / a := by
  classical
  exact μ.prob_ge_le hX ha

/-- The union bound, with no independence restriction on the events. -/
theorem event_exists_le_sum {κ : Type*} [Fintype κ]
    (μ : FiniteLaw Ω) (P : κ → Ω → Prop) :
    μ.event (fun ω => ∃ k, P k ω) ≤ ∑ k, μ.event (P k) := by
  classical
  simp_rw [← μ.mean_indicator]
  rw [← μ.mean_sum]
  apply μ.mean_mono
  intro ω
  by_cases hex : ∃ k, P k ω
  · obtain ⟨k, hk⟩ := hex
    rw [ite_eq_left ⟨k, hk⟩]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if P j ω then (1 : ℝ) else 0)
      (fun j _ => by split <;> positivity) (Finset.mem_univ k)
    simpa [hk] using h
  · rw [ite_eq_right hex]
    exact Finset.sum_nonneg fun k _ => by split <;> positivity

/-- The joint experiment of drawing a first observation and then choosing a
law for the remaining observation using the first. -/
@[expose] def staged {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') :
    FiniteLaw (Ω × Ω') where
  prob s := μ.prob s.1 * (ν s.1).prob s.2
  nonneg s := mul_nonneg (μ.nonneg s.1) ((ν s.1).nonneg s.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, fun ω => (ν ω).total, mul_one, μ.total]

theorem staged_mean {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω)
    (ν : Ω → FiniteLaw Ω') (X : Ω × Ω' → ℝ) :
    (μ.staged ν).mean X = μ.mean (fun ω => (ν ω).mean (fun ω' => X (ω, ω'))) := by
  simp only [mean, staged, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- Conditioning on an exposed value of positive probability gives exactly
the indicated remaining law. In particular, drawing the remaining groups
from a product law independent of this observation preserves that law. -/
theorem staged_conditional_mass {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') (ω : Ω) (hω : 0 < μ.prob ω)
    (ω' : Ω') :
    (μ.staged ν).prob (ω, ω') / (μ.staged ν).event (fun s => s.1 = ω) =
      (ν ω).prob ω' := by
  classical
  have hfirst : (μ.staged ν).event (fun s => s.1 = ω) = μ.prob ω := by
    rw [← mean_indicator, staged_mean]
    have hmean (a : Ω) :
        (ν a).mean (fun _ => if a = ω then (1 : ℝ) else 0) = if a = ω then 1 else 0 :=
      (ν a).mean_const _
    simp_rw [hmean]
    simp [mean, mul_ite, Finset.sum_ite_eq']
  rw [hfirst]
  change (μ.prob ω * (ν ω).prob ω') / μ.prob ω = _
  field_simp

theorem event_nonneg (μ : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ μ.event P := by
  classical
  exact Finset.sum_nonneg fun ω _ => μ.nonneg ω

theorem event_not (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.event (fun ω => ¬ P ω) = 1 - μ.event P := by
  classical
  rw [← mean_indicator, ← mean_indicator, eq_sub_iff_add_eq, ← mean_add]
  have hone : (fun ω => (if ¬ P ω then (1 : ℝ) else 0) + (if P ω then 1 else 0)) =
      fun _ => 1 := by
    funext ω
    by_cases h : P ω <;> simp [h]
  rw [hone, mean_const]

/-- Express the probability in a two-stage experiment as the first-stage
average of the conditional probabilities. -/
theorem staged_event {Ω' : Type*} [Fintype Ω']
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') (P : Ω × Ω' → Prop) :
    (μ.staged ν).event P = μ.mean (fun ω => (ν ω).event (fun ω' => P (ω, ω'))) := by
  classical
  rw [← mean_indicator, staged_mean]
  simp_rw [mean_indicator]

theorem event_lt_one_exists_not (μ : FiniteLaw Ω) {P : Ω → Prop}
    (h : μ.event P < 1) : ∃ ω, ¬ P ω := by
  classical
  by_contra! he
  unfold event at h
  simp [he, μ.total] at h

/-- Control the inner averages simultaneously by bounding each outer
expectation, then applying Markov and the union bound. The inner draw
represents a random partition, and the outer draw the original data. -/
theorem bad_inner_mean_le {Ω' κ : Type*} [Fintype Ω'] [Fintype κ]
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω') (X : κ → Ω × Ω' → ℝ)
    {bound limit : ℝ} (hlimit : 0 < limit) (hX : ∀ k s, 0 ≤ X k s)
    (hmean : ∀ k, (μ.staged ν).mean (X k) ≤ bound) :
    μ.event (fun ω => ∃ k, limit < (ν ω).mean (fun ω' => X k (ω, ω'))) ≤
      (Fintype.card κ : ℝ) * (bound / limit) := by
  classical
  let Y := fun k ω => (ν ω).mean (fun ω' => X k (ω, ω'))
  calc
    _ ≤ ∑ k, μ.event (fun ω => limit < Y k ω) :=
      μ.event_exists_le_sum _
    _ ≤ ∑ _k : κ, bound / limit := by
      apply Finset.sum_le_sum
      intro k _
      have hnonneg (ω : Ω) : 0 ≤ Y k ω := (ν ω).mean_nonneg fun ω' => hX k (ω, ω')
      calc
        _ ≤ μ.event (fun ω => limit ≤ Y k ω) := μ.event_mono fun _ h => h.le
        _ ≤ μ.mean (Y k) / limit := μ.event_ge_le hnonneg hlimit
        _ ≤ _ := by
          rw [← μ.staged_mean ν (X k)]
          exact div_le_div_of_nonneg_right (hmean k) hlimit.le
    _ = _ := by simp

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]

/-- Independent draws at finitely many positions. -/
@[expose] def product (μ : ∀ i, FiniteLaw (S i)) : FiniteLaw ((i : ι) → S i) where
  prob ω := ∏ i, (μ i).prob (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => (μ i).nonneg (ω i)
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [(μ _).total]

theorem mean_product (μ : ∀ i, FiniteLaw (S i)) (X : ∀ i, S i → ℝ) :
    (product μ).mean (fun ω => ∏ i, X i (ω i)) = ∏ i, (μ i).mean (X i) := by
  classical
  simp only [mean, product, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => (μ i).prob ω * X i ω)).symm

/-- Exponential moment bound for independent group contributions. -/
theorem mean_exp_sum_le (μ : ∀ i, FiniteLaw (S i)) (X : ∀ i, S i → ℝ)
    (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    (product μ).mean (fun ω => Real.exp (t * ∑ i, X i (ω i))) ≤
      Real.exp ((Real.exp t - 1) * ∑ i, (μ i).mean (X i)) := by
  have heq : (fun ω : (i : ι) → S i => Real.exp (t * ∑ i, X i (ω i))) =
      fun ω => ∏ i, Real.exp (t * X i (ω i)) := by
    funext ω
    rw [Finset.mul_sum, Real.exp_sum]
  rw [heq, mean_product μ (fun i ω => Real.exp (t * X i ω)), Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod₀
    (fun i _ => (μ i).mean_nonneg (fun _ => (Real.exp_pos _).le))
    (fun i _ => (μ i).mean_exp_le _ (hX i) t)

/-- Exponential upper tail from the product moment and Markov's inequality. -/
theorem prob_sum_ge_le (μ : ∀ i, FiniteLaw (S i)) (X : ∀ i, S i → ℝ)
    (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (a : ℝ) :
    (product μ).event (fun ω => a ≤ ∑ i, X i (ω i)) ≤
      Real.exp ((Real.exp t - 1) * (∑ i, (μ i).mean (X i)) - t * a) := by
  classical
  let Y : ((i : ι) → S i) → ℝ := fun ω => Real.exp (t * ∑ i, X i (ω i))
  have hevent (ω : (i : ι) → S i) : Real.exp (t * a) ≤ Y ω ↔ a ≤ ∑ i, X i (ω i) := by
    dsimp [Y]
    rw [Real.exp_le_exp, mul_le_mul_iff_right₀ ht]
  have h := (product μ).prob_ge_le (X := Y) (fun _ => (Real.exp_pos _).le)
    (Real.exp_pos (t * a))
  simp only [hevent] at h
  unfold event
  refine h.trans ?_
  rw [Real.exp_sub]
  exact div_le_div_of_nonneg_right (mean_exp_sum_le μ X hX t) (Real.exp_pos _).le

/-- Lower tail estimate used when a fixed vertex has independent chances
of surviving the selections at several positions. -/
theorem prob_sum_le_half_mean (μ : ∀ i, FiniteLaw (S i)) (X : ∀ i, S i → ℝ)
    (hX : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1) :
    (product μ).event (fun ω => ∑ i, X i (ω i) ≤ (∑ i, (μ i).mean (X i)) / 2) ≤
      Real.exp (-(∑ i, (μ i).mean (X i)) / 8) := by
  let m := ∑ i, (μ i).mean (X i)
  let Y : ((i : ι) → S i) → ℝ := fun ω => Real.exp (-(Real.log 2) * ∑ i, X i (ω i))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm : 0 ≤ m := Finset.sum_nonneg fun i _ =>
    (μ i).mean_nonneg fun ω => (show 0 ≤ X i ω ∧ X i ω ≤ 1 from hX i ω).1
  have hmarkov := (product μ).event_ge_le (X := Y) (fun _ => (Real.exp_pos _).le)
    (Real.exp_pos (-(Real.log 2) * (m / 2)))
  have hmoment := mean_exp_sum_le μ X hX (-(Real.log 2))
  have heq : Real.exp (-(Real.log 2)) = (1 : ℝ) / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
  rw [heq, show (1 : ℝ) / 2 - 1 = -1 / 2 by norm_num] at hmoment
  calc
    _ ≤ (product μ).event (fun ω => Real.exp (-(Real.log 2) * (m / 2)) ≤ Y ω) :=
      (product μ).event_mono fun ω hω =>
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hω (neg_nonpos.mpr hlog.le))
    _ ≤ _ := hmarkov
    _ ≤ Real.exp ((-1 / 2) * m) / Real.exp (-(Real.log 2) * (m / 2)) :=
      div_le_div_of_nonneg_right hmoment (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_sub]
      apply Real.exp_le_exp.mpr
      have hlog' : Real.log 2 < 3 / 4 := by linarith [Real.log_two_lt_d9]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hlog'.le) hm]

end Product

end FiniteLaw
end LocallyRamsey
