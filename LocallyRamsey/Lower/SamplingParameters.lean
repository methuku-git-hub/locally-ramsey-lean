module

public import LocallyRamsey.Lower.ThresholdParameters

public section

open Filter

namespace LocallyRamsey

/-- The ratio (M/(rb)) in the lower-bound sampling argument. -/
@[expose] noncomputable def samplingRatio (r : ℕ) : ℝ :=
  (lowerTestSize r : ℝ) / ((r : ℝ) * largeCliqueOrder r)

theorem sampling_ratio_bounds :
    ∀ᶠ n : ℕ in atTop,
      let r := target n
      1 ≤ samplingRatio r ∧ samplingRatio r ^ 2 ≤ (r : ℝ) / Real.log (r : ℝ) ^ 45 := by
  have hcast : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have hLog := (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop
    ((48000 : ℝ) ^ 2)
  have hLogPow := (isLittleO_log_rpow_rpow_atTop 23 (by norm_num : (0 : ℝ) < 1 / 2)).eventuallyLE
  filter_upwards [lower_parameter_bounds, hLog, hcast.eventually hLogPow] with n hn huBig hLogPow
  obtain ⟨_, hr, hrM, _, huR, _⟩ := hn
  let r := target n
  let u := Real.log (r : ℝ)
  let b := largeCliqueOrder r
  let M := lowerTestSize r
  have hr' : (100 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hu0 : 0 < u := by change (48000 : ℝ) ^ 2 ≤ u at huBig; linarith
  have huL : u ^ 23 ≤ Real.sqrt (r : ℝ) := by
    change ‖u ^ (23 : ℝ)‖ ≤ ‖(r : ℝ) ^ (1 / 2 : ℝ)‖ at hLogPow
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hr0.le _),
      show (23 : ℝ) = ((23 : ℕ) : ℝ) by rfl, Real.rpow_natCast] at hLogPow
    rwa [Real.sqrt_eq_rpow]
  have hbhi : (b : ℝ) ≤ (r : ℝ) ^ 2 / (24000 * u) :=
    Nat.floor_le (show 0 ≤ (r : ℝ) ^ 2 / (24000 * u) by positivity)
  have hblo : (r : ℝ) ^ 2 / (48000 * u) ≤ b := by
    have hbig : (2 : ℝ) ≤ (r : ℝ) ^ 2 / (24000 * u) := by
      apply (le_div_iff₀ (by positivity)).mpr
      change 8000 * u ≤ r at huR
      nlinarith only [huR, mul_le_mul_of_nonneg_right hr' hr0.le]
    have hbround := Nat.lt_floor_add_one ((r : ℝ) ^ 2 / (24000 * u))
    change (r : ℝ) ^ 2 / (24000 * u) < (b : ℝ) + 1 at hbround
    have heq : (r : ℝ) ^ 2 / (24000 * u) = 2 * ((r : ℝ) ^ 2 / (48000 * u)) := by field_simp; ring
    linarith only [hbig, hbround, heq]
  have hb0 : 0 < (b : ℝ) := (by positivity : 0 < (r : ℝ) ^ 2 / (48000 * u)).trans_le hblo
  have hMhi : (M : ℝ) ≤ lowerScale r := Nat.floor_le (by dsimp [lowerScale]; positivity)
  have hMlo : lowerScale r / 2 ≤ M := by
    have hround := Nat.lt_floor_add_one (lowerScale r)
    have hMr : (r : ℝ) ≤ M := by exact_mod_cast hrM
    change (lowerScale r : ℝ) < (M : ℝ) + 1 at hround
    linarith only [hround, hMr, hr']
  have hpow : (r : ℝ) ^ (7 / 2 : ℝ) = (r : ℝ) ^ 3 * Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hr0]
    norm_num
  have hUpper : samplingRatio r ≤ 48000 * Real.sqrt r / u ^ 23 := by
    change (M : ℝ) / ((r : ℝ) * b) ≤ _
    have h₁ := div_le_div_of_nonneg_right hMhi (by positivity : 0 ≤ (r : ℝ) * b)
    have h₂ := div_le_div_of_nonneg_left (by dsimp [lowerScale]; positivity : 0 ≤ lowerScale r)
      (by positivity : 0 < (r : ℝ) * ((r : ℝ) ^ 2 / (48000 * u)))
      (mul_le_mul_of_nonneg_left hblo hr0.le)
    refine h₁.trans (h₂.trans_eq ?_)
    change (r : ℝ) ^ (7 / 2 : ℝ) / u ^ 24 / ((r : ℝ) * ((r : ℝ) ^ 2 / (48000 * u))) = _
    rw [hpow]
    field_simp
  have hLower : 1 ≤ samplingRatio r := by
    have h₁ := div_le_div_of_nonneg_right hMlo (by positivity : 0 ≤ (r : ℝ) * b)
    have h₂ := div_le_div_of_nonneg_left (by dsimp [lowerScale]; positivity : 0 ≤ lowerScale r / 2)
      (by positivity : 0 < (r : ℝ) * b) (mul_le_mul_of_nonneg_left hbhi hr0.le)
    change 1 ≤ (M : ℝ) / ((r : ℝ) * b)
    refine (show 1 ≤ lowerScale r / 2 / ((r : ℝ) * ((r : ℝ) ^ 2 / (24000 * u))) from ?_).trans
      (h₂.trans h₁)
    have heq : lowerScale r / 2 / ((r : ℝ) * ((r : ℝ) ^ 2 / (24000 * u))) =
        12000 * Real.sqrt r / u ^ 23 := by
      change (r : ℝ) ^ (7 / 2 : ℝ) / u ^ 24 / 2 / ((r : ℝ) * ((r : ℝ) ^ 2 / (24000 * u))) = _
      rw [hpow]
      field_simp
      norm_num
    rw [heq, le_div_iff₀ (by positivity), one_mul]
    linarith only [huL, Real.sqrt_nonneg (r : ℝ)]
  refine ⟨hLower, ?_⟩
  have hpos : 0 ≤ samplingRatio r := zero_le_one.trans hLower
  calc
    _ ≤ (48000 * Real.sqrt r / u ^ 23) ^ 2 := pow_le_pow_left₀ hpos hUpper 2
    _ = (48000 : ℝ) ^ 2 * r / u ^ 46 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hr0.le, ← pow_mul]
    _ ≤ _ := by
      change (48000 : ℝ) ^ 2 * r / u ^ 46 ≤ (r : ℝ) / u ^ 45
      change (48000 : ℝ) ^ 2 ≤ u at huBig
      refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right huBig hr0.le)
        (by positivity : 0 ≤ u ^ 46)).trans_eq ?_
      rw [pow_succ u 45]
      field_simp

/-- The degree parameter for a retained set at a position. -/
@[expose] noncomputable def overlapDegree (r : ℕ) : ℝ :=
  samplingRatio r * Real.log (r : ℝ) ^ 18

/-- The common conditional probability of keeping a vertex. -/
@[expose] noncomputable def overlapQuota (r : ℕ) : ℝ :=
  1 / (samplingRatio r * Real.log (r : ℝ) ^ 8)

/-- Number of samples in a group. -/
@[expose] noncomputable def overlapGroupSize (r : ℕ) : ℕ :=
  ⌈samplingRatio r * Real.log (r : ℝ) ^ 12⌉₊

/-- Number of blocks in an anchored partition. -/
@[expose] noncomputable def overlapBlockCount (r : ℕ) : ℕ := ⌈overlapDegree r⌉₊

theorem overlap_sampling_parameter_bounds :
    ∀ᶠ n : ℕ in atTop, let r := target n
      let u := Real.log (r : ℝ)
      let D := overlapDegree r
      let γ := overlapQuota r
      let q := overlapGroupSize r
      let h := overlapBlockCount r
      1 < D ∧ 0 < γ ∧ 2 ≤ q ∧ 0 < h ∧
      (h : ℝ) - 1 ≤ D ∧ (h : ℝ)⁻¹ ≤ γ ∧
      u ^ 4 ≤ (q : ℝ) * γ ∧ u ^ 10 ≤ (h : ℝ) * γ ∧
      D / γ ≤ (r : ℝ) ∧ (q : ℝ) / h ≤ 2 / u ^ 6 := by
  have ht : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  filter_upwards [sampling_ratio_bounds, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 2] with n hn hu
  let r := target n
  let u := Real.log (r : ℝ)
  let a := samplingRatio r
  let D := overlapDegree r
  let γ := overlapQuota r
  let q := overlapGroupSize r
  let h := overlapBlockCount r
  change 1 ≤ a ∧ a ^ 2 ≤ (r : ℝ) / u ^ 45 at hn
  change 2 ≤ u at hu
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have ha0 : 0 < a := zero_lt_one.trans_le hn.1
  have hu18 : (2 : ℝ) ≤ u ^ 18 := by
    exact hu.trans (by simpa using pow_le_pow_right₀ hu1 (show (1 : ℕ) ≤ 18 by decide))
  have hu12 : (2 : ℝ) ≤ u ^ 12 := by
    exact hu.trans (by simpa using pow_le_pow_right₀ hu1 (show (1 : ℕ) ≤ 12 by decide))
  have hD : 1 < D := by
    change 1 < a * u ^ 18
    have h := mul_le_mul_of_nonneg_right hn.1 (by positivity : 0 ≤ u ^ 18)
    linarith only [h, hu18]
  have hγ : 0 < γ := by change 0 < 1 / (a * u ^ 8); positivity
  have hqfrac : a * u ^ 12 ≤ q := Nat.le_ceil _
  have hqceil : (q : ℝ) < a * u ^ 12 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq2 : 2 ≤ q := by
    have hp := mul_le_mul_of_nonneg_right hn.1 (show (0 : ℝ) ≤ u ^ 12 by positivity)
    have hqr : (2 : ℝ) ≤ q := by linarith only [hqfrac, hp, hu12]
    exact_mod_cast hqr
  have hhceil : D ≤ h := Nat.le_ceil _
  have hh : 0 < h := by
    have hh' : (0 : ℝ) < h := (zero_lt_one.trans hD).trans_le hhceil
    exact_mod_cast hh'
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hhround : (h : ℝ) < D + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqγ : u ^ 4 ≤ (q : ℝ) * γ := by
    refine (show u ^ 4 = (a * u ^ 12) * γ from ?_).trans_le
      (mul_le_mul_of_nonneg_right hqfrac hγ.le)
    change u ^ 4 = (a * u ^ 12) * (1 / (a * u ^ 8))
    field_simp
  have hDγ : u ^ 10 = D * γ := by
    change u ^ 10 = (a * u ^ 18) * (1 / (a * u ^ 8))
    field_simp
  have hhγ : u ^ 10 ≤ (h : ℝ) * γ := hDγ.trans_le (mul_le_mul_of_nonneg_right hhceil hγ.le)
  have hinv : (h : ℝ)⁻¹ ≤ γ := by
    rw [← one_div, div_le_iff₀ hhr, mul_comm]
    exact (one_le_pow₀ hu1).trans hhγ
  have hDquot : D / γ ≤ r := by
    change (a * u ^ 18) / (1 / (a * u ^ 8)) ≤ _
    rw [div_eq_mul_inv, one_div, inv_inv]
    have he : (a * u ^ 18) * (a * u ^ 8) = a ^ 2 * u ^ 26 := by ring
    rw [he]
    have hp := mul_le_mul_of_nonneg_right hn.2 (show 0 ≤ u ^ 26 by positivity)
    have hfrac : (r : ℝ) / u ^ 45 * u ^ 26 = (r : ℝ) / u ^ 19 := by field_simp
    rw [hfrac] at hp
    exact hp.trans (div_le_self (by positivity) (one_le_pow₀ hu1))
  have hqRatio : (q : ℝ) / h ≤ 2 / u ^ 6 := by
    have hqbound : (q : ℝ) ≤ 2 * (a * u ^ 12) := by
      have hp := mul_le_mul_of_nonneg_right hn.1 (show (0 : ℝ) ≤ u ^ 12 by positivity)
      linarith only [hqceil, hp, hu12]
    refine (div_le_div_of_nonneg_right hqbound hhr.le).trans ?_
    have hDb : 0 < D := zero_lt_one.trans hD
    refine (div_le_div_of_nonneg_left (by positivity) hDb hhceil).trans_eq ?_
    change 2 * (a * u ^ 12) / (a * u ^ 18) = 2 / u ^ 6
    field_simp
  exact ⟨hD, hγ, hq2, hh, by linarith, hinv, hqγ, hhγ, hDquot, hqRatio⟩


/-- The number of groups, drawn positions, and recorded samples are all
polynomial in the target, with the savings required by the union bounds. -/
theorem overlap_group_size_products :
    ∀ᶠ n : ℕ in atTop, let r := target n
      let u := Real.log (r : ℝ)
      let a := samplingRatio r
      let q := overlapGroupSize r
      let h := overlapBlockCount r
      (q : ℝ) ≤ 2 * a * u ^ 12 ∧ (h : ℝ) ≤ 2 * a * u ^ 18 ∧
      (q : ℝ) ^ 2 ≤ 4 * (r : ℝ) / u ^ 21 ∧
      (q : ℝ) * h ≤ r ∧ (q : ℝ) * u ≤ (r : ℝ) / 10000 := by
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  filter_upwards [sampling_ratio_bounds, hrT.eventually_ge_atTop 200000,
    (Real.tendsto_log_atTop.comp hrT).eventually_ge_atTop 10000] with n hn hr hu
  let r := target n
  let u := Real.log (r : ℝ)
  let a := samplingRatio r
  let q := overlapGroupSize r
  let h := overlapBlockCount r
  have ha : 0 < a := zero_lt_one.trans_le hn.1
  have hu0 : 0 < u := by change 10000 ≤ u at hu; linarith
  have hu1 : 1 ≤ u := by change 10000 ≤ u at hu; linarith
  have hr0 : (0 : ℝ) < r := by change (200000 : ℝ) ≤ r at hr; linarith
  have hceil (k : ℕ) : (⌈a * u ^ k⌉₊ : ℝ) ≤ 2 * a * u ^ k := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ a * u ^ k by positivity)
    have h1 : 1 ≤ a * u ^ k := one_le_mul_of_one_le_of_one_le hn.1 (one_le_pow₀ hu1)
    linarith only [h, h1]
  have hq : (q : ℝ) ≤ 2 * a * u ^ 12 := hceil 12
  have hh : (h : ℝ) ≤ 2 * a * u ^ 18 := hceil 18
  have hqa : (q : ℝ) ^ 2 ≤ 4 * (r : ℝ) / u ^ 21 := by
    have hq2 := pow_le_pow_left₀ (Nat.cast_nonneg q) hq 2
    have h2 := mul_le_mul_of_nonneg_right hn.2 (show 0 ≤ 4 * u ^ 24 by positivity)
    rw [show (r : ℝ) / u ^ 45 * (4 * u ^ 24) = 4 * r / u ^ 21 by field_simp] at h2
    nlinarith only [hq2, h2]
  have hqh : (q : ℝ) * h ≤ r := by
    have hq' := mul_le_mul hq hh (Nat.cast_nonneg h) (show 0 ≤ 2 * a * u ^ 12 by positivity)
    have he : 2 * a * u ^ 12 * (2 * a * u ^ 18) = a ^ 2 * (4 * u ^ 30) := by ring
    rw [he] at hq'
    have hu15 : (4 : ℝ) ≤ u ^ 15 := by
      have h := pow_le_pow_right₀ hu1 (show 1 ≤ 15 by decide)
      simp only [pow_one] at h
      change 10000 ≤ u at hu
      linarith only [h, hu]
    have h2 := mul_le_mul_of_nonneg_right hn.2 (show 0 ≤ 4 * u ^ 30 by positivity)
    rw [show (r : ℝ) / u ^ 45 * (4 * u ^ 30) = 4 * r / u ^ 15 by field_simp] at h2
    refine hq'.trans (h2.trans ?_)
    apply (div_le_iff₀ (show 0 < u ^ 15 by positivity)).mpr
    exact mul_le_mul_of_nonneg_right hu15 hr0.le |>.trans_eq (by ring)
  have hqu : (q : ℝ) * u ≤ (r : ℝ) / 10000 := by
    have h := mul_le_mul_of_nonneg_right hqa (show 0 ≤ u ^ 2 by positivity)
    rw [← mul_pow, show 4 * (r : ℝ) / u ^ 21 * u ^ 2 = 4 * r / u ^ 19 by field_simp] at h
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (by positivity : (0 : ℝ) ≤ (r : ℝ) / 10000)
    refine h.trans ?_
    apply (div_le_iff₀ (show 0 < u ^ 19 by positivity)).mpr
    have hu19 : (400000000 : ℝ) ≤ u ^ 19 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10000) (show 10000 ≤ u from hu) 3
      norm_num at h
      exact (by linarith only [h] : (400000000 : ℝ) ≤ u ^ 3).trans
        (pow_le_pow_right₀ hu1 (show 3 ≤ 19 by decide))
    have h2 := mul_le_mul_of_nonneg_right hu19 (show 0 ≤ (r : ℝ) ^ 2 / 100000000 by positivity)
    change (200000 : ℝ) ≤ r at hr
    nlinarith only [h2, mul_le_mul_of_nonneg_right hr hr0.le]
  exact ⟨hq, hh, hqa, hqh, hqu⟩

end LocallyRamsey
