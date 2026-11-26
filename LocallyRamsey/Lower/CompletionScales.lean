module

public import LocallyRamsey.Lower.LocationScales
public import LocallyRamsey.Lower.FiniteCompletion

public section

open Filter

namespace LocallyRamsey

/-- Scalar requirements for the final probability comparison, after
fixing the parameters used to locate the clique. -/
structure CompletionScales (n r w : ℕ) (p : LocationScales n r w) where
  records : ℕ
  mass : ℝ
  probabilityError : ℝ
  hMass : mass = (r : ℝ) /
    (100 * largeCliqueOrder r * p.draws * ((p.regionSize : ℝ) / w))
  mass_pos : 0 < mass
  hγ : 9 * overlapQuota r ≤ mass
  hη : 8 * (r : ℝ)⁻¹ ^ 3 ≤ mass
  hRecords :
    ⌈(overlapBlockCount r : ℝ) * overlapDegree r * Real.log (1 + 1 / ((r : ℝ)⁻¹ ^ 3))⌉₊ ≤ records
  hSize : 2 * (overlapGroupSize r - 1) * (overlapGroupSize r - 1) ≤
    overlapGroupSize r * overlapBlockCount r - 1
  hExposed : 2 * (p.recorded : ℝ) ≤ (overlapBlockCount r : ℝ) * overlapQuota r
  hGap : 4 / (overlapDegree r * overlapQuota r) + 288 * overlapQuota r / mass < 1 / 9
  hError : let h := overlapBlockCount r
    let q := overlapGroupSize r
    let γ := overlapQuota r
    (Real.exp (-(h * γ) / 2) +
      Real.exp ((p.draws : ℝ) * γ - Real.log 2 * (2 * p.draws * γ))) +
      Real.exp (-(h * γ) / 16) +
      ((q * h : ℕ) : ℝ) * (Real.exp (1 / 8 - Real.log 2 * ((h : ℝ) * γ - 1)) / ((h : ℝ)⁻¹) ^ 2) +
      Real.exp (-((q * h : ℕ) : ℝ) * γ / 2) ≤ probabilityError
  hError0 : 0 ≤ probabilityError
  hBoth : let N := p.draws
    let b := largeCliqueOrder r
    let s := p.recorded
    let K := 4 * b * ((p.regionSize : ℝ) / w)
    ((Fintype.card (RecordDescription N b s) : ℝ) * probabilityError) +
      ((Fintype.card (RecordDescription N b s) : ℝ) * ((N * b : ℕ) + 1 : ℕ) ^ records) *
        Real.exp ((N : ℝ) * (K * mass) - Real.log 2 * (((r / 2 : ℕ) : ℝ) - s - records)) < 4 / 5

set_option maxHeartbeats 1200000 in
/-- The two exceptional probabilities are small even after summing over
every description, and the two overlap inequalities have disjoint
ranges. -/
theorem eventually_completion_scales :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℕ, (n : ℝ) ^ (1 / 6 : ℝ) ≤ w →
      ∀ p : LocationScales n (target n) w, Nonempty (CompletionScales n (target n) w p) := by
  have rn : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have un := Real.tendsto_log_atTop.comp rn
  filter_upwards [eventually_gt_atTop (0 : ℕ), rn.eventually_ge_atTop 200000,
    un.eventually_ge_atTop 10000, eventually_log_pow_le_target 100, sampling_ratio_bounds,
    overlap_sampling_parameter_bounds, overlap_group_size_products,
    eventually_overlap_gap (A := 96) (by norm_num)] with n hn hr hu hrU har hO hQ hGap
  intro w hw p
  let r := target n
  let R : ℝ := r
  let u := Real.log R
  let a := samplingRatio r
  let γ := overlapQuota r
  let D := overlapDegree r
  let q := overlapGroupSize r
  let h := overlapBlockCount r
  let η := R⁻¹ ^ 3
  let b := largeCliqueOrder r
  let N := p.draws
  let s := p.recorded
  let P := (p.regionSize : ℝ) / w
  let g := R / (100 * (b : ℝ) * N * P)
  let H := ⌈(h : ℝ) * D * Real.log (1 + 1 / η)⌉₊
  let err := 5 * Real.exp (-(10 * u ^ 2))
  change (200000 : ℝ) ≤ R at hr
  change (10000 : ℝ) ≤ u at hu
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 < a := zero_lt_one.trans_le har.1
  have hw0 : (0 : ℝ) < w := (by positivity : 0 < (n : ℝ) ^ (1 / 6 : ℝ)).trans_le hw
  have hRlog : Real.exp u = R := Real.exp_log hR0
  have hProd (j k : ℕ) (hj : j + k ≤ 100) : u ^ j ≤ R / u ^ k := by
    rw [le_div_iff₀ (by positivity), ← pow_add]
    exact (pow_le_pow_right₀ hu1 hj).trans hrU
  have hUP (k : ℕ) (hk : 1 ≤ k) : u ≤ u ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ hu1 hk
  have hb0 : (0 : ℝ) < b := by
    by_contra! hh
    have hz : b = 0 := by exact_mod_cast (le_antisymm hh (Nat.cast_nonneg b))
    have ha : 1 ≤ (lowerTestSize r : ℝ) / (R * b) := har.1
    rw [hz, Nat.cast_zero, mul_zero, div_zero] at ha
    norm_num at ha
  have hbU : (b : ℝ) ≤ R ^ 2 / u :=
    (Nat.floor_le (by positivity : 0 ≤ R ^ 2 / (24000 * u))).trans
      (div_le_div_of_nonneg_left (by positivity) hu0 (by linarith))
  have hbR : (b : ℝ) ≤ R ^ 2 := hbU.trans (div_le_self (by positivity) hu1)
  have hP : 0 < P := div_pos ((by positivity : 0 < (w : ℝ) / R ^ 2).trans_le p.region_fraction_lower) hw0
  have hN : (0 : ℝ) < N := by exact_mod_cast p.draws_pos
  have hs : (s : ℝ) ≤ u := p.record_size
  obtain ⟨hD, hγ, hq, hh, _, _, hqγ, hhγ, hDγ, hqh⟩ := hO
  change 2 ≤ q at hq
  change 0 < h at hh
  change u ^ 10 ≤ (h : ℝ) * γ at hhγ
  change (q : ℝ) / h ≤ 2 / u ^ 6 at hqh
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨_, hhUp, hqSq, hqhR, _⟩ := hQ
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hhR : (h : ℝ) ≤ R := by
    have hh := mul_le_mul_of_nonneg_right hq1 hh0.le
    linarith only [hh, hqhR]
  have hNγlow : 4 * R / u ^ 8 ≤ (N : ℝ) * γ := by
    have hn := mul_le_mul_of_nonneg_right p.draws_lower hγ.le
    have he : 4 * R * a * γ = 4 * R / u ^ 8 := by
      change 4 * R * a * (1 / (a * u ^ 8)) = _
      field_simp
    exact he ▸ hn
  have hMass := overlap_mass_scale_le hR0 ha0 hu0 hb0 hN hP hbU p.draws_upper p.region_fraction_upper
  have hg : 0 < g := (hGap g hMass).1
  have hGap' : 4 / (D * γ) + 288 * γ / g < 1 / 9 := by
    have h := (hGap g hMass).2
    norm_num at h
    exact h
  have hγg : 9 * γ ≤ g := by
    refine le_trans ?_ hMass
    change 9 * (1 / (a * u ^ 8)) ≤ 1 / (1000 * a * u ^ 5)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hx := mul_le_mul_of_nonneg_right
      ((by change 10000 ≤ u at hu; linarith : (9000 : ℝ) ≤ u).trans (hUP 3 (by decide)))
      (show 0 ≤ a * u ^ 5 by positivity)
    nlinarith only [hx]
  have hηg : 8 * η ≤ g := by
    have hγR : R⁻¹ ≤ γ := by
      rw [inv_eq_one_div, div_le_iff₀ hR0]
      have hh := (div_le_iff₀ hγ).mp hDγ
      linarith only [hh, hD]
    have hηR : η ≤ R⁻¹ := by
      exact (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hR1) (show 1 ≤ 3 by decide)).trans_eq
        (by rw [pow_one])
    linarith only [hηR, hγR, hγg, hγ]
  have hBlock : 2 * (q - 1) * (q - 1) ≤ q * h - 1 := by
    have hFrac : 4 * (q : ℝ) ≤ h := by
      have h2 : (8 : ℝ) ≤ u ^ 6 := (by linarith : (8 : ℝ) ≤ u).trans (hUP 6 (by decide))
      rw [div_le_div_iff₀ hh0 (by positivity : 0 < u ^ 6)] at hqh
      nlinarith only [hqh, mul_le_mul_of_nonneg_right h2 hq0.le]
    have h4q : 4 * q ≤ h := by exact_mod_cast hFrac
    have hx : 4 * (q * q) ≤ q * h := by
      calc
        _ = q * (4 * q) := by ring
        _ ≤ _ := Nat.mul_le_mul_left q h4q
    have hp : 0 < q * q := Nat.mul_pos (by omega) (by omega)
    have hsq := Nat.mul_le_mul (Nat.sub_le q 1) (Nat.sub_le q 1)
    calc
      _ = 2 * ((q - 1) * (q - 1)) := by ring
      _ ≤ 2 * (q * q) := Nat.mul_le_mul_left 2 hsq
      _ ≤ _ := by omega
  have hExposed : 2 * (s : ℝ) ≤ (h : ℝ) * γ := by
    have hU := mul_le_mul_of_nonneg_right
      ((by linarith : (2 : ℝ) ≤ u).trans (hUP 9 (by decide))) hu0.le
    nlinarith only [hs, hhγ, hU]
  have hHlog : Real.log (1 + 1 / η) ≤ 4 * u := by
    have he : 1 / η = R ^ 3 := by dsimp [η]; field_simp
    rw [he, ← show Real.log (R ^ 4) = 4 * u by rw [Real.log_pow]; rfl]
    apply Real.log_le_log (by positivity)
    have h := mul_le_mul_of_nonneg_right (show 2 ≤ R by linarith) (show 0 ≤ R ^ 3 by positivity)
    have h1 : (1 : ℝ) ≤ R ^ 3 := one_le_pow₀ hR1
    nlinarith only [h, h1]
  have hH : (H : ℝ) ≤ 8 * R / u ^ 8 + 1 := by
    have hD0 : 0 < D := zero_lt_one.trans hD
    have hlog0 : 0 ≤ Real.log (1 + 1 / η) := Real.log_nonneg
      (le_add_of_nonneg_right (by dsimp [η]; positivity))
    have h1 := mul_le_mul hhUp (le_refl D) hD0.le (by positivity : 0 ≤ 2 * a * u ^ 18)
    have h2 := mul_le_mul h1 hHlog hlog0 (by positivity : 0 ≤ 2 * a * u ^ 18 * D)
    have hEq : 2 * a * u ^ 18 * D * (4 * u) = a ^ 2 * (8 * u ^ 37) := by
      change 2 * a * u ^ 18 * (a * u ^ 18) * (4 * u) = _
      ring
    rw [hEq] at h2
    have h3 := mul_le_mul_of_nonneg_right har.2 (show 0 ≤ 8 * u ^ 37 by positivity)
    rw [show R / u ^ 45 * (8 * u ^ 37) = 8 * R / u ^ 8 by field_simp] at h3
    have hCeil := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg hh0.le hD0.le) hlog0)
    linarith only [h2, h3, hCeil]
  have hHsm : (H : ℝ) + s ≤ R / (100 * u) := by
    have h1 : 8 * R / u ^ 8 ≤ R / (200 * u) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h := mul_le_mul_of_nonneg_right
        ((by linarith : (1600 : ℝ) ≤ u).trans (hUP 7 (by decide))) (show 0 ≤ R * u by positivity)
      nlinarith only [h]
    have h2 : u + 1 ≤ R / (200 * u) := by
      rw [show R / (200 * u) = (R / u) / 200 by ring]
      have h : u ^ 2 ≤ R / u := by simpa only [pow_one] using (hProd 2 1 (by decide))
      have h' := mul_le_mul_of_nonneg_right (show 1000 ≤ u by linarith) hu0.le
      nlinarith only [h, h', hu]
    have he : R / (100 * u) = 2 * (R / (200 * u)) := by ring
    rw [he]
    linarith only [hH, hs, h1, h2]
  let A : ℝ := (N * b : ℕ) + 1
  have hA1 : 1 ≤ A := by
    exact le_add_of_nonneg_left (Nat.cast_nonneg (N * b))
  have hA0 : 0 < A := zero_lt_one.trans_le hA1
  have hAR : A ≤ R ^ 5 := by
    have hx := mul_le_mul p.drawR hbR hb0.le (by positivity : 0 ≤ R ^ 2)
    have hh := mul_le_mul_of_nonneg_right (show 2 ≤ R by linarith) (show 0 ≤ R ^ 4 by positivity)
    have h1 := one_le_pow₀ hR1 (n := 4)
    dsimp [A]
    push_cast
    nlinarith only [hx, hh, h1]
  have hALog : Real.log A ≤ 5 * u := by
    have h := Real.log_le_log hA0 hAR
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hdCard : (Fintype.card (RecordDescription N b s) : ℝ) = A ^ s := by
    norm_num [RecordDescription, A, Fintype.card_fun, Fintype.card_option, Fintype.card_prod,
      add_comm]
  have hAexp (j : ℕ) : A ^ j ≤ Real.exp (5 * u * (j : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hA0]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hALog (Nat.cast_nonneg _))
  have hCardErr : (Fintype.card (RecordDescription N b s) : ℝ) * err ≤ 1 / 10 := by
    rw [hdCard]
    have he := (hAexp s).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 5 * u)))
    refine (mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ err)).trans ?_
    change Real.exp (5 * u * u) * (5 * Real.exp (-(10 * u ^ 2))) ≤ _
    rw [mul_left_comm, ← Real.exp_add, show 5 * u * u + -(10 * u ^ 2) = -(5 * u ^ 2) by ring]
    have hh : Real.exp (-(5 * u ^ 2)) ≤ 1 / 50 := by
      rw [Real.exp_neg, inv_eq_one_div]
      refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
      have h := Real.add_one_le_exp (5 * u ^ 2)
      nlinarith only [h, hu, sq_nonneg (u - 10000)]
    linarith only [hh]
  have hRecErr : let K := 4 * (b : ℝ) * P
      ((Fintype.card (RecordDescription N b s) : ℝ) * A ^ H) *
        Real.exp ((N : ℝ) * (K * g) - Real.log 2 * (((r / 2 : ℕ) : ℝ) - s - H)) ≤ 1 / 10 := by
    intro K
    rw [hdCard, ← pow_add]
    have hCard := hAexp (s + H)
    have hT : 5 * u * (↑(s + H) : ℝ) ≤ R / 20 := by
      push_cast
      have h := mul_le_mul_of_nonneg_left hHsm (show 0 ≤ 5 * u by positivity)
      rw [show 5 * u * (R / (100 * u)) = R / 20 by field_simp <;> ring] at h
      simpa only [add_comm (s : ℝ)] using h
    have hK : (N : ℝ) * (K * g) = R / 25 := by
      dsimp [K, g]
      field_simp
      <;> ring
    have hrH : R / 3 ≤ (↑(r / 2 : ℕ) : ℝ) - s - H := by
      have ha : (r : ℝ) ≤ 2 * (↑(r / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (show r ≤ 2 * (r / 2) + 1 by omega)
      have hb : (H : ℝ) + s ≤ R / 100 :=
        hHsm.trans (div_le_div_of_nonneg_left hR0.le (by norm_num) (by linarith))
      linarith only [ha, hb, hr]
    have hlog := mul_le_mul
      (show (1 : ℝ) / 2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
      hrH (by positivity : 0 ≤ R / 3) (by linarith [Real.log_two_gt_d9] : 0 ≤ Real.log 2)
    refine (mul_le_mul_of_nonneg_right (hCard.trans (Real.exp_le_exp.mpr hT)) (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add, hK]
    refine (Real.exp_le_exp.mpr (show R / 20 + (R / 25 - Real.log 2 * _) ≤ -(R / 20) by
      linarith only [hlog, hR0])).trans ?_
    rw [Real.exp_neg, inv_eq_one_div]
    refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    have hh := Real.add_one_le_exp (R / 20)
    linarith only [hh, hr]
  have hError :
      (Real.exp (-(h * γ) / 2) +
        Real.exp ((N : ℝ) * γ - Real.log 2 * (2 * N * γ))) +
        Real.exp (-(h * γ) / 16) +
        ((q * h : ℕ) : ℝ) * (Real.exp (1 / 8 - Real.log 2 * ((h : ℝ) * γ - 1)) / ((h : ℝ)⁻¹) ^ 2) +
        Real.exp (-((q * h : ℕ) : ℝ) * γ / 2) ≤ err := by
    have hBasic : 1000 * u ^ 2 ≤ u ^ 10 := by
      have h1 := mul_le_mul_of_nonneg_right
        ((by linarith : (1000 : ℝ) ≤ u).trans (hUP 8 (by decide))) (show 0 ≤ u ^ 2 by positivity)
      nlinarith only [h1]
    have hNγ' : 1000 * u ^ 2 ≤ (N : ℝ) * γ := by
      have hU := hProd 3 8 (by decide)
      have hy := mul_le_mul_of_nonneg_right (show (1000 : ℝ) ≤ u by linarith) (show 0 ≤ u ^ 2 by positivity)
      rw [show 4 * R / u ^ 8 = 4 * (R / u ^ 8) by ring] at hNγlow
      nlinarith only [hNγlow, hU, hy, sq_nonneg u]
    have hlog2 : (5 : ℝ) / 8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hE₁ : Real.exp (-(h * γ) / 2) ≤ Real.exp (-(10 * u ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith only [hhγ, hBasic, sq_nonneg u])
    have hE₂ : Real.exp ((N : ℝ) * γ - Real.log 2 * (2 * N * γ)) ≤ Real.exp (-(10 * u ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hlog2 (show 0 ≤ 2 * (N : ℝ) * γ by positivity)
      nlinarith only [h, hNγ', sq_nonneg u]
    have hE₃ : Real.exp (-(h * γ) / 16) ≤ Real.exp (-(10 * u ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith only [hhγ, hBasic, sq_nonneg u])
    have hE₄ : ((q * h : ℕ) : ℝ) * (Real.exp (1 / 8 - Real.log 2 * ((h : ℝ) * γ - 1)) /
        ((h : ℝ)⁻¹) ^ 2) ≤ Real.exp (-(10 * u ^ 2)) := by
      have ht : 1 / 8 - Real.log 2 * ((h : ℝ) * γ - 1) ≤ -(20 * u ^ 2) := by
        have ht0 : 0 ≤ (h : ℝ) * γ - 1 := by
          nlinarith only [hhγ, hBasic, hu, sq_nonneg (u - 10000)]
        have h := mul_le_mul_of_nonneg_right hlog2 ht0
        nlinarith only [h, hhγ, hBasic, hu, sq_nonneg (u - 10000)]
      rw [show ((h : ℝ)⁻¹) ^ 2 = ((h : ℝ) ^ 2)⁻¹ by rw [inv_pow], div_inv_eq_mul]
      have hp := mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.exp_le_exp.mpr ht) (pow_le_pow_left₀ hh0.le hhR 2)
          (by positivity : 0 ≤ (h : ℝ) ^ 2) (Real.exp_pos _).le) (show 0 ≤ ((q * h : ℕ) : ℝ) by positivity)
      refine hp.trans ?_
      have hk : ((q * h : ℕ) : ℝ) * (Real.exp (-(20 * u ^ 2)) * R ^ 2) ≤
          R ^ 3 * Real.exp (-(20 * u ^ 2)) := by
        push_cast
        exact (mul_le_mul_of_nonneg_right hqhR (by positivity)).trans_eq (by ring)
      refine hk.trans ?_
      rw [← hRlog, ← Real.exp_nat_mul, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by push_cast; nlinarith only [hu, sq_nonneg (u - 10000)])
    have hE₅ : Real.exp (-((q * h : ℕ) : ℝ) * γ / 2) ≤ Real.exp (-(10 * u ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have hhh := mul_le_mul_of_nonneg_right hq1 (show 0 ≤ (h : ℝ) * γ by positivity)
      push_cast
      nlinarith only [hhh, hhγ, hBasic, sq_nonneg u]
    dsimp [err]
    linarith only [hE₁, hE₂, hE₃, hE₄, hE₅]
  refine ⟨⟨H, g, err, rfl, hg, hγg, hηg, le_rfl, hBlock, hExposed, hGap', hError,
    by positivity, ?_⟩⟩
  have h := (add_le_add hCardErr hRecErr).trans_lt (show (1 / 10 : ℝ) + 1 / 10 < 4 / 5 by norm_num)
  simpa only [A, Nat.cast_add, Nat.cast_one] using h

end LocallyRamsey
