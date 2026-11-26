module

public import LocallyRamsey.Lower.OverlapScales

public section

namespace LocallyRamsey

/-- Numerical conditions for the prescribed-set and capped-retention
lemmas at the scales of the manuscript. -/
structure RetentionScales (r a u p α : ℝ) (K b B : ℕ) where
  H : ℕ
  stages : ℕ
  cutoff : ℕ
  cutoff_eq : cutoff = ⌊(B : ℝ) * r⁻¹ ^ 4⌋₊
  hH : ⌈(a * u ^ 18) * Real.log (1 + 1 / (r⁻¹ ^ 3))⌉₊ ≤ H
  cost : (stages : ℝ) * (2 * ((1 / (a * u ^ 8)) * p) / (1 / (500 * a * b))) ≤ 1
  reduction : B / 2 ^ stages ≤ cutoff
  error : (H : ℝ) + α / 10 +
    K * ((K * b + 1 : ℕ) : ℝ) ^ H * Real.exp (-(Real.log 2 * (α / 10))) +
      4 * K * b * (1 / (500 * a * b)) ≤
        α * (1 - (K : ℝ) ^ 2 * (b * (2 * b / (cutoff + 1))))

noncomputable def retention_scales_of_bounds {r a p : ℝ} {K b B : ℕ}
    (hr : 200000 ≤ r) (hu : 10000 ≤ Real.log r)
    (ha : 1 ≤ a) (ha2 : a ^ 2 ≤ r / (Real.log r) ^ 45)
    (hPow : (Real.log r) ^ 12 ≤ Real.sqrt r)
    (hKlo : r / (2 * (Real.log r) ^ 10) ≤ (K : ℝ))
    (hKhi : (K : ℝ) ≤ r / (Real.log r) ^ 10)
    (hb : 0 < b) (hBu : (b : ℝ) ≤ r ^ 2 / (24000 * Real.log r))
    (hp : 0 < p) (hpHi : p ≤ 16 * (Real.log r) ^ 6 / r ^ 2)
    (hB : r ^ 13 ≤ (B : ℝ)) :
    RetentionScales r a (Real.log r) p ((K : ℝ) / (40 * a)) K b B := by
  let u := Real.log r
  let α := (K : ℝ) / (40 * a)
  let D := a * u ^ 18
  let γ := 1 / (a * u ^ 8)
  let η := r⁻¹ ^ 3
  let rate := 1 / (500 * a * (b : ℝ))
  let H := ⌈D * Real.log (1 + 1 / η)⌉₊
  let stages := ⌈10 * u⌉₊
  let cutoff := ⌊(B : ℝ) * r⁻¹ ^ 4⌋₊
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hu0 : 0 < u := by change 10000 ≤ u at hu; linarith
  have hu1 : 1 ≤ u := by change 10000 ≤ u at hu; linarith
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hK0 : (0 : ℝ) < K := (by positivity : 0 < r / (2 * u ^ 10)).trans_le hKlo
  have hK : (K : ℝ) ≤ r := hKhi.trans (div_le_self hr0.le (one_le_pow₀ hu1))
  have hB' : (b : ℝ) ≤ r ^ 2 := hBu.trans (div_le_self (by positivity) (by linarith only [hu1]))
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hαr : r / (80 * a * u ^ 10) ≤ α := by
    have h := div_le_div_of_nonneg_right hKlo (by positivity : 0 ≤ 40 * a)
    refine (show r / (80 * a * u ^ 10) = (r / (2 * u ^ 10)) / (40 * a) by field_simp; norm_num).le.trans h
  have hαlo : u ^ 2 / 80 ≤ α := by
    have haS : a ≤ Real.sqrt r := by
      have h := ha2.trans (div_le_self hr0.le (one_le_pow₀ hu1))
      nlinarith only [h, Real.sq_sqrt hr0.le, Real.sqrt_nonneg r, ha0]
    refine (show u ^ 2 / 80 ≤ r / (80 * a * u ^ 10) from ?_).trans hαr
    rw [le_div_iff₀ (by positivity : 0 < 80 * a * u ^ 10)]
    have h := mul_le_mul haS hPow (by positivity : 0 ≤ u ^ 12) (Real.sqrt_nonneg r)
    rw [← pow_two (Real.sqrt r), Real.sq_sqrt hr0.le] at h
    nlinarith only [h]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hHhi : (H : ℝ) ≤ 5 * a * u ^ 19 := by
    have hlog : Real.log (1 + 1 / η) ≤ 4 * u := by
      have he : 1 + 1 / η = 1 + r ^ 3 := by dsimp [η]; rw [one_div, inv_pow, inv_inv]
      rw [he]
      have hle : 1 + r ^ 3 ≤ r ^ 4 := by
        have h := mul_le_mul_of_nonneg_right (show 2 ≤ r by linarith) (show 0 ≤ r ^ 3 by positivity)
        nlinarith only [h, one_le_pow₀ hr1 (n := 3)]
      have h := Real.log_le_log (by positivity : 0 < 1 + r ^ 3) hle
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hη : 0 < η := by dsimp [η]; positivity
    have hlog0 : 0 ≤ Real.log (1 + 1 / η) := Real.log_nonneg (by linarith [
      (show 0 ≤ 1 / η by positivity)])
    have hh := Nat.ceil_lt_add_one (mul_nonneg (show 0 ≤ D by dsimp [D]; positivity) hlog0)
    have hM := mul_le_mul_of_nonneg_left hlog (show 0 ≤ D by dsimp [D]; positivity)
    have hu19 := one_le_pow₀ hu1 (n := 19)
    have haU := one_le_mul_of_one_le_of_one_le ha hu19
    change (H : ℝ) < D * Real.log (1 + 1 / η) + 1 at hh
    dsimp only [D] at hM
    nlinarith only [hh, hM, haU]
  have hHu : (H : ℝ) * (4 * u) ≤ α / 100 := by
    have hp := mul_le_mul_of_nonneg_right hHhi (show 0 ≤ 4 * u by positivity)
    have h20 : (H : ℝ) * (4 * u) ≤ 20 * a * u ^ 20 := hp.trans_eq (by ring)
    refine h20.trans ?_
    refine (?_ : 20 * a * u ^ 20 ≤ (r / (80 * a * u ^ 10)) / 100).trans
      (div_le_div_of_nonneg_right hαr (by norm_num))
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100),
      le_div_iff₀ (by positivity : 0 < 80 * a * u ^ 10)]
    have h := mul_le_mul_of_nonneg_right ha2 (show 0 ≤ 160000 * u ^ 30 by positivity)
    change a ^ 2 * (160000 * u ^ 30) ≤ r / u ^ 45 * (160000 * u ^ 30) at h
    rw [show r / u ^ 45 * (160000 * u ^ 30) = 160000 * r / u ^ 15 by field_simp] at h
    have h15 : (160000 : ℝ) ≤ u ^ 15 := by
      have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000) (show 10000 ≤ u from hu) 2
      have h15 := pow_le_pow_right₀ hu1 (show 2 ≤ 15 by decide)
      norm_num at h2
      linarith only [h2, h15]
    have hfinal : 160000 * r / u ^ 15 ≤ r := by
      rw [div_le_iff₀ (by positivity : 0 < u ^ 15)]
      exact mul_le_mul_of_nonneg_right h15 hr0.le |>.trans_eq (by ring)
    nlinarith only [h, hfinal]
  have hHsmall : (H : ℝ) ≤ α / 100 := by
    have h := mul_le_mul_of_nonneg_left (show 1 ≤ 4 * u by linarith only [hu1]) (Nat.cast_nonneg H)
    nlinarith only [h, hHu]
  have hTail : (K : ℝ) * ((K * b + 1 : ℕ) : ℝ) ^ H *
      Real.exp (-(Real.log 2 * (α / 10))) ≤ α / 10 := by
    have hlog : Real.log ((K * b + 1 : ℕ) : ℝ) ≤ 4 * u := by
      have hKb := mul_le_mul hK hB' (by positivity : 0 ≤ (b : ℝ)) hr0.le
      have h : ((K * b + 1 : ℕ) : ℝ) ≤ r ^ 4 := by
        push_cast
        have hr3 := mul_le_mul_of_nonneg_right (show 2 ≤ r by linarith) (show 0 ≤ r ^ 3 by positivity)
        nlinarith only [hKb, hr3, one_le_pow₀ hr1 (n := 3)]
      have h' := Real.log_le_log (by positivity : 0 < ((K * b + 1 : ℕ) : ℝ)) h
      simpa only [Real.log_pow, Nat.cast_ofNat] using h'
    have hP : ((K * b + 1 : ℕ) : ℝ) ^ H * Real.exp (-(Real.log 2 * (α / 10))) ≤
        Real.exp (-α / 25) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, Real.exp_le_exp]
      have hl := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg H)
      have h2 := mul_le_mul_of_nonneg_right hlog2 (show 0 ≤ α / 10 by positivity)
      nlinarith only [hl, h2, hHu]
    have huu : 50 * u ≤ α := by
      have hh := mul_le_mul_of_nonneg_right (show 4000 ≤ u by
        change 10000 ≤ u at hu; linarith only [hu]) hu0.le
      nlinarith only [hh, hαlo]
    have he : Real.exp (-(2 * u)) = 1 / r ^ 2 := by
      change Real.exp (-((2 : ℕ) * Real.log r)) = _
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hr0, one_div]
    have hsmall := Real.exp_le_exp.mpr (show -α / 25 ≤ -(2 * u) by linarith only [huu])
    rw [he] at hsmall
    rw [mul_assoc]
    refine (mul_le_mul_of_nonneg_left (hP.trans hsmall) hK0.le).trans ?_
    refine (mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 1 / r ^ 2)).trans ?_
    rw [show r * (1 / r ^ 2) = 1 / r by field_simp]
    have hr' : 1 / r ≤ (1 : ℝ) := by rw [div_le_iff₀ hr0]; linarith
    linarith only [hr', huu, hu1]
  have hcut : r ^ 9 ≤ (cutoff : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((B : ℝ) * r⁻¹ ^ 4)
    change (B : ℝ) * r⁻¹ ^ 4 < (cutoff : ℝ) + 1 at h
    have h' := mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ r⁻¹ ^ 4)
    rw [show r ^ 13 * r⁻¹ ^ 4 = r ^ 9 by rw [inv_pow]; field_simp] at h'
    exact h'.trans h.le
  have hLoss : (K : ℝ) ^ 2 * (b * (2 * b / ((cutoff : ℝ) + 1))) ≤ 1 / 4 := by
    have hb2 := pow_le_pow_left₀ hb0.le hB' 2
    have hK2 := pow_le_pow_left₀ (Nat.cast_nonneg K) hK 2
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    have h := mul_le_mul hK2 hb2 (by positivity : 0 ≤ (b : ℝ) ^ 2) (by positivity : 0 ≤ r ^ 2)
    have hr6 : 8 * r ^ 6 ≤ r ^ 9 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show 2 ≤ r by linarith) 3
      have h := mul_le_mul_of_nonneg_right hh (show 0 ≤ r ^ 6 by positivity)
      norm_num at h
      nlinarith only [h]
    nlinarith only [h, hr6, hcut]
  have hrRate : (4 : ℝ) * K * b * rate = (8 / 25 : ℝ) * α := by
    dsimp [rate, α]
    field_simp
    ring
  have hErr : (H : ℝ) + α / 10 +
      K * ((K * b + 1 : ℕ) : ℝ) ^ H * Real.exp (-(Real.log 2 * (α / 10))) +
      4 * K * b * rate ≤ α * (1 - (K : ℝ) ^ 2 * (b * (2 * b / (cutoff + 1)))) := by
    rw [hrRate]
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hLoss 1) hα0.le
    linarith only [hHsmall, hTail, h, hα0.le]
  have hReduction : B / 2 ^ stages ≤ cutoff := by
    apply Nat.le_floor
    have h := Nat.cast_div_le (α := ℝ) (m := B) (n := 2 ^ stages)
    have hLo : r ^ 4 ≤ (2 : ℝ) ^ stages := by
      have hT : 10 * u ≤ (stages : ℝ) := Nat.le_ceil _
      have he : r ^ 4 = Real.exp (4 * u) := by
        change r ^ 4 = Real.exp ((4 : ℕ) * Real.log r)
        rw [Real.exp_nat_mul, Real.exp_log hr0]
      have hs : (2 : ℝ) ^ stages = Real.exp ((stages : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [he, hs, Real.exp_le_exp]
      nlinarith only [hT, hu0, mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg stages)]
    have he : (B : ℝ) / r ^ 4 = (B : ℝ) * r⁻¹ ^ 4 := by rw [inv_pow, div_eq_mul_inv]
    rw [← he]
    push_cast at h
    exact h.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hLo)
  have hCost : (stages : ℝ) * (2 * (γ * p) / rate) ≤ 1 := by
    have hst := Nat.ceil_lt_add_one (show 0 ≤ 10 * u by positivity)
    have hst' : (stages : ℝ) ≤ 11 * u := by linarith only [hst, hu1]
    have hPb : p * b ≤ u ^ 5 / 1500 := by
      refine (mul_le_mul hpHi hBu hb0.le (by positivity)).trans_eq ?_
      change (16 * u ^ 6 / r ^ 2) * (r ^ 2 / (24000 * u)) = _
      field_simp
      ring
    have he : 2 * (γ * p) / rate = 1000 * (p * b) / u ^ 8 := by
      dsimp [γ, rate]
      field_simp
      ring
    have h : 2 * (γ * p) / rate ≤ 1 / u ^ 3 := by
      rw [he]
      refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hPb (by norm_num))
        (by positivity)).trans ?_
      rw [div_le_div_iff₀ (by positivity : 0 < u ^ 8) (by positivity : 0 < u ^ 3)]
      nlinarith only [show 0 ≤ u ^ 8 by positivity]
    refine (mul_le_mul hst' h (by positivity) (by positivity)).trans ?_
    rw [← mul_div_assoc, div_le_one (by positivity : 0 < u ^ 3)]
    have ht : 11 ≤ u ^ 2 := by change 10000 ≤ u at hu; nlinarith only [hu]
    nlinarith only [mul_le_mul_of_nonneg_left ht hu0.le]
  exact ⟨H, stages, cutoff, rfl, le_rfl, hCost, hReduction, hErr⟩

end LocallyRamsey
