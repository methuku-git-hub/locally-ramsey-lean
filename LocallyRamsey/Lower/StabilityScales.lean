module

public import LocallyRamsey.Lower.OverlapScales

public section

namespace LocallyRamsey

/-- The separating tests stop before exhausting a fixed positive power
of the available vertex set. -/
structure StabilityScales (r n : ℝ) (q : ℕ) (p : ℝ) where
  repetitions : ℕ
  steps : ℕ
  stops :
    ((p⁻¹) ^ q) ^ repetitions * (1 / 2 : ℝ) ^ steps <
      1 - (steps : ℝ) * (1 - (1 / (100000 * (q : ℝ))) / 2) ^ repetitions
  size_factor :
    n ^ (-1 / 12 : ℝ) ≤ ((1 / (100000 * (q : ℝ))) / 2 * r⁻¹ ^ 100) ^ steps

noncomputable def stability_scales_of_bounds {r N p : ℝ} {q : ℕ}
    (hr : 200000 ≤ r) (hN : 0 < N) (hq : 0 < q) (hqR : (q : ℝ) ≤ r)
    (hp : 1 / r ^ 3 ≤ p) (hlog : r / 4 ≤ Real.log N)
    (hu : 10000 ≤ Real.log r) (hq2 : (q : ℝ) ^ 2 ≤ 4 * r / (Real.log r) ^ 21) :
    StabilityScales r N q p := by
  let u := Real.log r
  let ε := 1 / (100000 * (q : ℝ))
  let k := ⌈200 * u / ε⌉₊
  let s := ⌈10 * (q : ℝ) * k * u⌉₊
  have hr0 : 0 < r := by linarith
  have hu0 : 0 < u := by change 10000 ≤ u at hu; linarith
  have hu1 : 1 ≤ u := by change 10000 ≤ u at hu; linarith
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : 0 < 100000 * (q : ℝ))).2
    linarith only [hq1]
  have hp0 : 0 < p := (by positivity : 0 < 1 / r ^ 3).trans_le hp
  have hklo : 200 * u / ε ≤ (k : ℝ) := Nat.le_ceil _
  have hk0 : (0 : ℝ) < k := (by positivity : 0 < 200 * u / ε).trans_le hklo
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by exact_mod_cast hk0)
  have hsk : 10 * (q : ℝ) * (k : ℝ) * u ≤ (s : ℝ) := Nat.le_ceil _
  have hqU : 1 ≤ (q : ℝ) * u := one_le_mul_of_one_le_of_one_le hq1 hu1
  have hKhi : (k : ℝ) ≤ 21000000 * (q : ℝ) * u := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 200 * u / ε by positivity)
    change (k : ℝ) < 200 * u / ε + 1 at h
    rw [show 200 * u / ε = 20000000 * q * u by dsimp [ε]; field_simp; ring] at h
    nlinarith only [h, hqU]
  have hSbound : (s : ℝ) ≤ 220000000 * (q : ℝ) ^ 2 * u ^ 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 10 * (q : ℝ) * (k : ℝ) * u by positivity)
    change (s : ℝ) < 10 * q * k * u + 1 at h
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hKhi (by positivity : 0 ≤ 10 * (q : ℝ))) hu0.le
    have h1 : 1 ≤ (q : ℝ) ^ 2 * u ^ 2 := by
      rw [← mul_pow]
      exact one_le_pow₀ hqU
    nlinarith only [h, hc, h1]
  have hSsmall : (s : ℝ) ≤ r / (10000 * u) := by
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2
      (show 0 ≤ (220000000 : ℝ) by norm_num)) (show 0 ≤ u ^ 2 by positivity)
    change 220000000 * (q : ℝ) ^ 2 * u ^ 2 ≤ 220000000 * (4 * r / u ^ 21) * u ^ 2 at hb
    rw [show 220000000 * (4 * r / u ^ 21) * u ^ 2 = 880000000 * r / u ^ 19 by field_simp; norm_num] at hb
    refine hSbound.trans (hb.trans ?_)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hu18 : (8800000000000 : ℝ) ≤ u ^ 18 := by
      have h4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000) (show (10000 : ℝ) ≤ u from hu) 4
      have h18 := pow_le_pow_right₀ hu1 (show 4 ≤ 18 by decide)
      norm_num at h4
      linarith only [h4, h18]
    have hh := mul_le_mul_of_nonneg_right hu18 (show 0 ≤ r * u by positivity)
    nlinarith only [hh]
  have hSr : (s : ℝ) ≤ r := hSsmall.trans (div_le_self hr0.le (by linarith only [hu1]))
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hSizePow : ((p⁻¹) ^ q) ^ k * (1 / 2 : ℝ) ^ s ≤ Real.exp (-(2 * (q : ℝ) * k * u)) := by
    have hpinv : p⁻¹ ≤ r ^ 3 := by
      rw [← one_div, div_le_iff₀ hp0]
      have hh := (div_le_iff₀ (show 0 < r ^ 3 by positivity)).1 hp
      simpa only [mul_comm] using hh
    have h1 : ((p⁻¹) ^ q) ^ k ≤ ((r ^ 3) ^ q) ^ k := pow_le_pow_left₀ (by positivity)
      (pow_le_pow_left₀ (by positivity) hpinv q) k
    have h2 : (1 / 2 : ℝ) ^ s = Real.exp (-(s : ℝ) * Real.log 2) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div, inv_pow]
    have h3 : ((r ^ 3) ^ q) ^ k = Real.exp (3 * (q : ℝ) * k * u) := by
      rw [show r ^ 3 = Real.exp (3 * u) from by
        change r ^ 3 = Real.exp ((3 : ℕ) * Real.log r)
        rw [Real.exp_nat_mul, Real.exp_log hr0]]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      ring
    refine (mul_le_mul_of_nonneg_right h1 (show 0 ≤ (1 / 2 : ℝ) ^ s by positivity)).trans ?_
    rw [h2, h3, ← Real.exp_add, Real.exp_le_exp]
    nlinarith only [hsk, mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg s)]
  have hv1 : Real.exp (-(2 * (q : ℝ) * k * u)) < 1 / 2 := by
    rw [Real.exp_neg, ← one_div, div_lt_div_iff_of_pos_left (by norm_num) (Real.exp_pos _) (by norm_num)]
    have hs : (1 : ℝ) ≤ (q : ℝ) * k * u :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq1 hk1) hu1
    linarith only [hs, Real.add_one_le_exp (2 * (q : ℝ) * k * u)]
  have hFail : (s : ℝ) * (1 - ε / 2) ^ k < 1 / 2 := by
    have h1 : (1 - ε / 2) ^ k ≤ Real.exp (-100 * u) := by
      have hbase : 1 - ε / 2 ≤ Real.exp (-(ε / 2)) := by linarith only [Real.add_one_le_exp (-(ε / 2))]
      refine (pow_le_pow_left₀ (by linarith only [hε1]) hbase k).trans ?_
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have hk := (div_le_iff₀ hε).1 hklo
      nlinarith only [hk]
    have he : Real.exp (-100 * u) = 1 / r ^ 100 := by
      rw [show -100 * u = -((100 : ℕ) * Real.log r) by dsimp [u]; norm_num,
        Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr0, one_div]
    have hR2 : r ^ 2 ≤ r ^ 100 := pow_le_pow_right₀ (by linarith : 1 ≤ r) (by decide)
    calc
      _ ≤ r * Real.exp (-100 * u) :=
        mul_le_mul hSr h1 (pow_nonneg (by linarith only [hε1]) _) hr0.le
      _ ≤ r * (1 / r ^ 2) := by
        rw [he]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left zero_le_one (by positivity) hR2) hr0.le
      _ < _ := by
        rw [show r * (1 / r ^ 2) = 1 / r by field_simp, div_lt_div_iff₀ hr0 (by norm_num : (0 : ℝ) < 2)]
        linarith
  refine ⟨k, s, (by linarith only [hSizePow, hv1, hFail]), ?_⟩
  have hbase : r⁻¹ ^ 102 ≤ ε / 2 * r⁻¹ ^ 100 := by
    have he : r⁻¹ ^ 102 = (1 / r ^ 2) * r⁻¹ ^ 100 := by
      rw [show (102 : ℕ) = 2 + 100 by decide, pow_add, inv_pow, ← one_div]
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp [ε]
    rw [div_div, div_le_div_iff_of_pos_left (by norm_num) (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_right hr (show 0 ≤ r by positivity)
    nlinarith only [h, hqR]
  have hPow := pow_le_pow_left₀ (show 0 ≤ r⁻¹ ^ 102 by positivity) hbase s
  refine (?_ : N ^ (-1 / 12 : ℝ) ≤ (r⁻¹ ^ 102) ^ s).trans hPow
  have he : (r⁻¹ ^ 102) ^ s = Real.exp (-(102 * u * (s : ℝ))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_inv]
    change _ = Real.exp (-(102 * Real.log r * (s : ℝ)))
    congr 1
    ring
  rw [he, Real.rpow_def_of_pos hN, Real.exp_le_exp]
  have hs := (le_div_iff₀ (show 0 < 10000 * u by positivity)).1 hSsmall
  have h0 : 102 * u * (s : ℝ) ≤ r / 48 := by
    have h := mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 1 / 98)
    nlinarith only [h, hr]
  linarith only [h0, hlog]

end LocallyRamsey
