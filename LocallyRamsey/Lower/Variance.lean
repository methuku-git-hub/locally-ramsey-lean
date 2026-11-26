module

public import LocallyRamsey.Lower.Stabilization
public import LocallyRamsey.IndependentBlocks
public import Mathlib.Algebra.BigOperators.Fin

public section

open scoped BigOperators

namespace LocallyRamsey.FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- Variance written as the mean square minus the square of the mean. -/
def variance (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  μ.mean (fun z => f z ^ 2) - μ.mean f ^ 2

theorem variance_le_sq_distance (μ : FiniteLaw Ω) (f : Ω → ℝ) (a : ℝ) :
    μ.variance f ≤ μ.mean (fun z => (f z - a) ^ 2) := by
  have heq : (fun z => (f z - a) ^ 2) = fun z => (f z ^ 2 + (-2 * a) * f z) + a ^ 2 := by
    funext z
    ring
  rw [heq, μ.mean_add, μ.mean_add, μ.mean_mul_const, μ.mean_const, variance]
  nlinarith only [sq_nonneg (μ.mean f - a)]

theorem mean_sub (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.mean (fun z => f z - g z) = μ.mean f - μ.mean g := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib]

theorem variance_staged {B : Type*} [Fintype B]
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw B) (f : Ω × B → ℝ) :
    (μ.staged ν).variance f = μ.mean (fun x => (ν x).variance (fun y => f (x, y))) +
      μ.variance (fun x => (ν x).mean (fun y => f (x, y))) := by
  simp only [variance, staged_mean, mean_sub]
  ring

theorem mean_split_first (μ : FiniteLaw Ω) {n : ℕ} (f : (Fin (n + 1) → Ω) → ℝ) :
    (product (fun _ : Fin (n + 1) => μ)).mean f =
      μ.mean (fun x => (product (fun _ : Fin n => μ)).mean (fun y => f (Fin.cons x y))) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => Ω)
  rw [← staged_mean (X := fun (z : Ω × (Fin n → Ω)) => f (Fin.cons z.1 z.2))]
  simp only [mean]
  apply Fintype.sum_equiv e.symm
  intro x
  congr 1
  · change (∏ i : Fin (n + 1), μ.prob (x i)) =
      μ.prob (x 0) * ∏ i : Fin n, μ.prob (x i.succ)
    exact Fin.prod_univ_succ _
  · exact congrArg f (e.apply_symm_apply x).symm

/-- Tensorization of variance, using an arbitrary approximation that omits
each coordinate. The approximation need not be the conditional mean. -/
theorem variance_product_le (μ : FiniteLaw Ω) (n : ℕ) (f : (Fin n → Ω) → ℝ)
    (g : Fin n → (Fin n → Ω) → ℝ)
    (hskip : ∀ i x y, (∀ j, j ≠ i → x j = y j) → g i x = g i y) :
    let ν := product (fun _ : Fin n => μ)
    ν.variance f ≤ ∑ i, ν.mean (fun z => (f z - g i z) ^ 2) := by
  classical
  induction n with
  | zero =>
    intro ν
    have hf : f = fun _ => f Fin.elim0 := by
      funext z
      congr 1
      exact funext fun j => Fin.elim0 j
    rw [hf, variance]
    simp [mean_const]
  | succ n ih =>
    intro ν
    let τ := product (fun _ : Fin n => μ)
    let f' (x : Ω) (z : Fin n → Ω) := f (Fin.cons x z)
    let g' (x : Ω) (j : Fin n) (z : Fin n → Ω) := g j.succ (Fin.cons x z)
    have htail (x : Ω) : τ.variance (f' x) ≤
        ∑ j, τ.mean (fun z => (f' x z - g' x j z) ^ 2) := by
      refine ih (f' x) (g' x) ?_
      intro i z t heq
      apply hskip
      intro j hj
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        exact heq j (fun hj' => hj (congrArg Fin.succ hj'))
    have hvar : ν.variance f = μ.mean (fun x => τ.variance (f' x)) +
        μ.variance (fun x => τ.mean (f' x)) := by
      have h := variance_staged μ (fun _ => τ) (fun s => f' s.1 s.2)
      have h' : (μ.staged (fun _ => τ)).variance (fun s => f' s.1 s.2) = ν.variance f := by
        change (μ.staged (fun _ => τ)).mean (fun s => f' s.1 s.2 ^ 2) -
          (μ.staged (fun _ => τ)).mean (fun s => f' s.1 s.2) ^ 2 = _
        rw [staged_mean, staged_mean]
        change μ.mean (fun x => τ.mean (fun z => f (Fin.cons x z) ^ 2)) -
          μ.mean (fun x => τ.mean (fun z => f (Fin.cons x z))) ^ 2 = _
        rw [← mean_split_first μ (fun w => f w ^ 2), ← mean_split_first μ f]
        rfl
      rw [← h']
      exact h
    have hrest : μ.mean (fun x => τ.variance (f' x)) ≤
        ∑ j : Fin n, ν.mean (fun z => (f z - g j.succ z) ^ 2) := by
      refine (μ.mean_mono htail).trans_eq ?_
      rw [μ.mean_sum]
      exact Finset.sum_congr rfl (fun j _ => (mean_split_first μ (fun z => (f z - g j.succ z) ^ 2)).symm)
    have hfirst : μ.variance (fun x => τ.mean (f' x)) ≤
        ν.mean (fun z => (f z - g 0 z) ^ 2) := by
      classical
      have hΩ : Nonempty Ω := by
        by_contra! h
        let _ : IsEmpty Ω := h
        simpa using μ.total
      let x₀ := Classical.choice hΩ
      let G₀ := fun z : Fin n → Ω => g 0 (Fin.cons x₀ z)
      have h₀ (x : Ω) (z : Fin n → Ω) : g 0 (Fin.cons x z) = G₀ z := by
        apply hskip
        intro j hj
        cases j using Fin.cases with
        | zero => contradiction
        | succ j => rfl
      refine (variance_le_sq_distance μ (fun x => τ.mean (f' x)) (τ.mean G₀)).trans ?_
      change _ ≤ (product (fun _ : Fin (n + 1) => μ)).mean _
      rw [mean_split_first]
      apply μ.mean_mono
      intro x
      rw [← τ.mean_sub]
      refine (τ.sq_mean_le_mean_sq _).trans_eq ?_
      simp only [f', h₀]
      rfl
    rw [hvar, Fin.sum_univ_succ]
    exact (add_le_add hrest hfirst).trans_eq (add_comm _ _)

/-- A mean-one density is concentrated between one half and two when the
variance of its square root is small. -/
theorem event_density_outside_le (μ : FiniteLaw Ω) (Y : Ω → ℝ)
    (hY : ∀ z, 0 ≤ Y z) (hm : μ.mean Y = 1) :
    μ.event (fun z => Y z < 1 / 2 ∨ 2 < Y z) ≤
      32 * μ.variance (fun z => Real.sqrt (Y z)) := by
  let f := fun z => Real.sqrt (Y z)
  have hf : (fun z => f z ^ 2) = Y := funext fun z => Real.sq_sqrt (hY z)
  have h0 : 0 ≤ μ.mean f := μ.mean_nonneg fun _ => Real.sqrt_nonneg _
  have hs := μ.sq_mean_le_mean_sq f
  rw [hf, hm] at hs
  have h1 : μ.mean f ≤ 1 := by
    by_contra! h
    nlinarith only [hs, mul_pos (sub_pos.mpr h) (by linarith : 0 < μ.mean f + 1)]
  have hdev : μ.mean (fun z => (f z - 1) ^ 2) ≤ 2 * μ.variance f := by
    have heq : (fun z => (f z - 1) ^ 2) = fun z => (f z ^ 2 + (-2 : ℝ) * f z) + 1 := by
      funext z
      ring
    rw [heq, μ.mean_add, μ.mean_add, μ.mean_mul_const, μ.mean_const, variance, hf, hm]
    nlinarith only [mul_nonneg (sub_nonneg.mpr h1) h0]
  have htail (z : Ω) (h : Y z < 1 / 2 ∨ 2 < Y z) : 1 / 16 ≤ (f z - 1) ^ 2 := by
    have hz := congrFun hf z
    have hf₀ : 0 ≤ f z := Real.sqrt_nonneg _
    rcases h with h | h
    · have hf' := Real.sqrt_le_sqrt (show Y z ≤ (3 / 4 : ℝ) ^ 2 by linarith)
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 4)] at hf'
      nlinarith only [mul_nonneg (show 0 ≤ 3 / 4 - f z from sub_nonneg.mpr hf')
        (show 0 ≤ 5 / 4 - f z by linarith)]
    · have hf' := Real.sqrt_le_sqrt (show (5 / 4 : ℝ) ^ 2 ≤ Y z by linarith)
      rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5 / 4)] at hf'
      nlinarith only [mul_nonneg (show 0 ≤ f z - 5 / 4 from sub_nonneg.mpr hf')
        (show 0 ≤ f z - 3 / 4 by linarith)]
  exact (μ.event_mono htail).trans ((μ.event_ge_le (fun z => sq_nonneg (f z - 1))
    (by norm_num : (0 : ℝ) < 1 / 16)).trans (by linarith only [hdev]))

/-- A whole group has controlled intersection density if each omitted
coordinate changes the square root by little in mean square. This also
accounts for the chance that an individual sample has too small a density. -/
theorem event_bad_intersection_group_le (μ : FiniteLaw Ω) (q : ℕ)
    (Y : (Fin q → Ω) → ℝ) (Yomit : Fin q → (Fin q → Ω) → ℝ)
    (hskip : ∀ i x y, (∀ j, j ≠ i → x j = y j) → Yomit i x = Yomit i y)
    (hY : ∀ z, 0 ≤ Y z) (hm : (product (fun _ : Fin q => μ)).mean Y = 1)
    (badSample : Ω → Prop) {δ ε : ℝ} (hbad : μ.event badSample ≤ δ)
    (herr : ∀ i, (product (fun _ : Fin q => μ)).mean (fun z =>
      (Real.sqrt (Y z) - Real.sqrt (Yomit i z)) ^ 2) ≤ ε) :
    (product (fun _ : Fin q => μ)).event (fun z => Y z < 1 / 2 ∨ 2 < Y z ∨
      ∃ i, badSample (z i)) ≤ (q : ℝ) * (32 * ε + δ) := by
  classical
  let ν := product (fun _ : Fin q => μ)
  let badY := fun z => Y z < 1 / 2 ∨ 2 < Y z
  let badZ := fun z : Fin q → Ω => ∃ i, badSample (z i)
  have hvar : ν.variance (fun z => Real.sqrt (Y z)) ≤ (q : ℝ) * ε := by
    have h := variance_product_le μ q (fun z => Real.sqrt (Y z)) (fun i z => Real.sqrt (Yomit i z))
      (fun i x y hxy => congrArg Real.sqrt (hskip i x y hxy))
    refine h.trans ((Finset.sum_le_sum fun i _ => herr i).trans_eq ?_)
    simp
  have hYprob : ν.event badY ≤ 32 * ((q : ℝ) * ε) :=
    (event_density_outside_le ν Y hY hm).trans (mul_le_mul_of_nonneg_left hvar (by norm_num))
  have hZprob : ν.event badZ ≤ (q : ℝ) * δ := by
    refine (ν.event_exists_le_sum (fun i z => badSample (z i))).trans ?_
    have hZ (i : Fin q) : ν.event (fun z => badSample (z i)) ≤ δ :=
      (event_coordinate (fun _ : Fin q => μ) i badSample).trans_le hbad
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hZ i)
  refine (ν.event_mono (fun z hz => ?_)).trans ((ν.event_union_le badY badZ).trans ?_)
  · exact hz.elim (fun h => Or.inl (Or.inl h)) (fun h => h.elim (fun h' => Or.inl (Or.inr h')) Or.inr)
  · nlinarith only [hYprob, hZprob]

end LocallyRamsey.FiniteLaw
