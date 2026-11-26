module

public import LocallyRamsey.Lower.PreparedSampling
public import LocallyRamsey.Lower.BiasedGroupDraws

public section

open Filter

namespace LocallyRamsey

/-- The rounded parameters for locating the clique and the bounds used
for the exposed descriptions. -/
structure LocationScales (n r w : ℕ) where
  listLength : ℕ
  recorded : ℕ
  degreeCap : ℕ
  regionSize : ℕ
  draws : ℕ
  occupancy : ℕ
  lost : ℕ
  collisionCap : ℕ
  list_pos : 0 < listLength
  records_pos : 0 < recorded
  draws_pos : 0 < draws
  occupancy_pos : 0 < occupancy
  draw_cover : 2 * lowerTestSize r ≤ draws * largeCliqueOrder r
  record_size : (recorded : ℝ) ≤ Real.log (r : ℝ)
  region_upper : regionSize ≤ w
  region_fraction_lower : (w : ℝ) / (r : ℝ) ^ 2 ≤ regionSize
  region_fraction_upper : (regionSize : ℝ) / w ≤ 2 * Real.log (r : ℝ) ^ 6 / (r : ℝ) ^ 2
  region_large : (n : ℝ) ^ (1 / 7 : ℝ) ≤ regionSize
  startLarge : (n : ℝ) ^ (1 / 7 : ℝ) ≤ (w : ℝ) * ((r : ℝ)⁻¹ ^ 10) ^ overlapGroupSize r / 2
  signature_budget :
    let d := ⌊2 * (100 * Real.log (r : ℝ) / r) * (listLength : ℝ)⌋₊
    let cutoff := ⌈(n : ℝ) ^ (1 / 40 : ℝ)⌉₊
    (((listLength + 1) ^ d * cutoff * 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 7 : ℝ)
  density_quota : 8 * (100 * Real.log (r : ℝ) / r) ≤ overlapQuota r
  lost_lt : lost < r
  small_collision : (recorded : ℝ) ^ 2 / (r - (lost : ℝ)) ≤ 1 / 2
  small_common : (listLength : ℝ) * ((degreeCap : ℝ) / (r - (lost : ℝ))) ^ recorded <
    ((regionSize : ℝ) / w) * listLength / 4
  half_clique : (r : ℝ) / 2 + 1 + recorded * ((collisionCap : ℝ) + 1) +
    2 * draws * overlapQuota r ≤ r
  draws_lower : 4 * r * samplingRatio r ≤ draws
  draws_upper : (draws : ℝ) ≤ 5 * r * samplingRatio r
  drawR : (draws : ℝ) ≤ (r : ℝ) ^ 2
  err :
    let R : ℝ := r
    let u := Real.log R
    let b := largeCliqueOrder r
    let q := overlapGroupSize r
    let h := overlapBlockCount r
    let γ := overlapQuota r
    let d := ⌊2 * (100 * u / R) * (listLength : ℝ)⌋₊
    2 * (1 / 100 + 4 * Real.exp ((listLength : ℝ) * (100 * u / R) - Real.log 2 * d)) +
      (draws : ℝ) ^ 2 * (b * (2 * b / (n : ℝ) ^ (1 / 7 : ℝ))) +
      (listLength : ℝ) * (Real.exp (-(h * γ) / 2) +
        Real.exp (2 * draws * γ - Real.log 2 * degreeCap)) +
      ((q * h : ℕ) : ℝ) * Real.exp ((draws : ℝ) * ((q : ℝ) / ((q * h : ℕ) : ℝ)) - Real.log 2 * occupancy) +
      (draws : ℝ) ^ r * Real.exp ((Real.exp 1 - 1) * ((q : ℝ) / ((q * h : ℕ) : ℝ)) *
        ((R * q) / occupancy) * R - ((lost * (collisionCap + 1) : ℕ) : ℝ) / (2 * occupancy)) +
      Real.exp (-(((regionSize : ℝ) / w) * listLength) / 8) * ((draws : ℝ) * (2 * b)) ^ recorded ≤
        1 / 5

theorem eventually_log_pow_le_target (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, Real.log (target n : ℝ) ^ k ≤ (target n : ℝ) := by
  have hr : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  filter_upwards [hr.eventually_gt_atTop 1,
    hr.eventually (isLittleO_log_rpow_rpow_atTop k (by norm_num : (0 : ℝ) < 1)).eventuallyLE] with n h hn
  simpa only [Real.rpow_natCast, Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg (target n)),
    Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg h.le) k)] using hn

/-- Bound the error terms in the clique location experiment at the
rounded scales. -/
theorem location_errors_small {R u Wn b p m N q h γ d dSig c rLoss cap s : ℝ} {r records : ℕ}
    (hR : R = r) (hs : s = records)
    (hR0 : 0 < R) (hu : 10000 ≤ u) (hLog : u = Real.log R)
    (hRbig : u ^ 100 ≤ R) (hWn : R ^ 20 ≤ Wn)
    (hparams : 0 ≤ b ∧ b ≤ R ^ 2 ∧ 0 ≤ N ∧ N ≤ R ^ 2 ∧ 0 ≤ m ∧ m ≤ R ^ 2 ∧
      0 < q ∧ 0 < h ∧ q * h ≤ R ∧ 0 < d ∧ 0 ≤ s ∧ s ≤ u)
    (hRec : s ≤ u / 5000)
    (hSig : dSig ≥ 2 * m * (100 * u / R) - 1)
    (hm : R ^ 2 / (2 * u ^ 4) ≤ m)
    (hγh : u ^ 10 ≤ h * γ)
    (hγN : N * γ ≤ 5 * R / u ^ 8)
    (hcap : R / (2 * u ^ 4) ≤ c)
    (hd : 2 * N / h ≤ d)
    (hdlo : 4 * R / u ^ 18 ≤ d)
    (hdhi : d ≤ 12 * R / u ^ 18)
    (hq : q / h ≤ 2 / u ^ 6)
    (hLoss : R ^ 2 / u ^ 5 ≤ rLoss * (cap + 1))
    (hp : u ^ 6 / R ^ 2 ≤ p)
    (hS : 0 ≤ p) :
    2 * (1 / 100 + 4 * Real.exp (m * (100 * u / R) - Real.log 2 * dSig)) +
      N ^ 2 * (b * (2 * b / Wn)) +
      m * (Real.exp (-(h * γ) / 2) + Real.exp (2 * N * γ - Real.log 2 * c)) +
      (q * h) * Real.exp (N * (q / (q * h)) - Real.log 2 * d) +
      N ^ r * Real.exp ((Real.exp 1 - 1) * (q / (q * h)) *
        ((R * q) / d) * R - (rLoss * (cap + 1)) / (2 * d)) +
      Real.exp (-(p * m) / 8) * (N * (2 * b)) ^ records ≤ 1 / 5 := by
  obtain ⟨hb0, hb, hN0, hN, hm0, hmU, hq0, hh0, hqh, hd0, hs0, hsU⟩ := hparams
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have huP (j : ℕ) (hj : j ≤ 100) : u ^ j ≤ R :=
    (pow_le_pow_right₀ hu1 hj).trans hRbig
  have hR1 : 10000 ≤ R := hu.trans (by simpa only [pow_one] using huP 1 (by decide))
  have hExp (k : ℕ) : Real.exp (-((k : ℝ) * u)) = (R ^ k)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul, hLog, Real.exp_log hR0]
  have hExp4 : Real.exp (-(4 * u)) = (R ^ 4)⁻¹ := hExp 4
  have hLog2 : (5 : ℝ) / 8 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hExp1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hRlog : Real.exp u = R := hLog ▸ Real.exp_log hR0
  have hProd (j k : ℕ) (hj : j + k ≤ 100) : u ^ j ≤ R / u ^ k := by
    rw [le_div_iff₀ (by positivity), ← pow_add]
    exact huP _ hj
  have hSigLarge : 50 * u ^ 3 ≤ m * (100 * u / R) := by
    have hp := mul_le_mul_of_nonneg_right hm (show 0 ≤ 100 * u / R by positivity)
    have he : (R ^ 2 / (2 * u ^ 4)) * (100 * u / R) = 50 * (R / u ^ 3) := by field_simp; ring
    rw [he] at hp
    exact (mul_le_mul_of_nonneg_left (hProd 3 3 (by decide)) (by norm_num : (0 : ℝ) ≤ 50)).trans hp
  have hSigPos : 0 ≤ dSig := by
    have h3 : u ≤ u ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hu1 (show 1 ≤ 3 by decide)
    linarith only [h3, hu, hSig, hSigLarge]
  have hExpSig : m * (100 * u / R) - Real.log 2 * dSig ≤ -(4 * u) := by
    have hmul := mul_le_mul_of_nonneg_right hLog2 hSigPos
    have h3 : u ≤ u ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hu1 (show 1 ≤ 3 by decide)
    linarith only [hSig, hSigLarge, hmul, h3, hu]
  have hExpDegree1 : -(h * γ) / 2 ≤ -(4 * u) := by
    have h0 : 8 * u ≤ u ^ 10 := by
      have hh : (8 : ℝ) ≤ u ^ 9 := (by linarith : 8 ≤ u).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hu1 (show 1 ≤ 9 by decide))
      nlinarith only [mul_le_mul_of_nonneg_right hh hu0.le]
    linarith only [hγh, h0]
  have hExpDegree2 : 2 * N * γ - Real.log 2 * c ≤ -(4 * u) := by
    have hT : 10 * R / u ^ 8 ≤ R / (16 * u ^ 4) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hp : 160 ≤ u ^ 4 := (by linarith : 160 ≤ u).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hu1 (show 1 ≤ 4 by decide))
      calc
        _ = (160 : ℝ) * (R * u ^ 4) := by ring
        _ ≤ u ^ 4 * (R * u ^ 4) := mul_le_mul_of_nonneg_right hp (by positivity)
        _ = _ := by ring
    have hc0 : 0 ≤ c := (by positivity : 0 ≤ R / (2 * u ^ 4)).trans hcap
    have hlead := mul_le_mul_of_nonneg_right hLog2 hc0
    have hlow := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 5 / 8)
    rw [show (5 / 8 : ℝ) * (R / (2 * u ^ 4)) = 5 * (R / (16 * u ^ 4)) by ring] at hlow
    have huPow := hProd 5 4 (by decide)
    have hU : 16 * u ≤ u ^ 5 := by
      have hh : (16 : ℝ) ≤ u ^ 4 := (by linarith : 16 ≤ u).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hu1 (show 1 ≤ 4 by decide))
      nlinarith only [mul_le_mul_of_nonneg_right hh hu0.le]
    rw [show R / (16 * u ^ 4) = (R / u ^ 4) / 16 by ring] at hT hlow
    rw [show 5 * R / u ^ 8 = 5 * (R / u ^ 8) by ring] at hγN
    rw [show 10 * R / u ^ 8 = 10 * (R / u ^ 8) by ring] at hT
    nlinarith only [hlead, hlow, hT, hγN, huPow, hU]
  have hqdiv : q / (q * h) = 1 / h := by field_simp
  have hExpOccupancy : N * (q / (q * h)) - Real.log 2 * d ≤ -(4 * u) := by
    rw [hqdiv]
    have hLogMul := mul_le_mul_of_nonneg_right hLog2 hd0.le
    have hPow := hProd 2 18 (by decide)
    have hU : 8 * u ≤ u ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right (show 8 ≤ u by linarith) hu0.le]
    rw [show N * (1 / h) = N / h by ring]
    rw [show 2 * N / h = 2 * (N / h) by ring] at hd
    rw [show 4 * R / u ^ 18 = 4 * (R / u ^ 18) by ring] at hdlo
    linarith only [hLogMul, hd, hdlo, hPow, hU]
  have hPairBound : (Real.exp 1 - 1) * (q / (q * h)) * (R * q / d) * R -
      rLoss * (cap + 1) / (2 * d) ≤ -(R * (2 * u + 4)) := by
    have hpositive : 0 ≤ Real.exp 1 - 1 :=
      sub_nonneg.mpr (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num))
    rw [hqdiv]
    have hEq : (Real.exp 1 - 1) * (1 / h) * (R * q / d) * R =
        (Real.exp 1 - 1) * (q / h) * (R ^ 2 / d) := by field_simp <;> ring
    rw [hEq]
    have hGt : (Real.exp 1 - 1) * (q / h) * (R ^ 2 / d) ≤ 4 * R ^ 2 / u ^ 6 / d := by
      have ha := mul_le_mul (show Real.exp 1 - 1 ≤ 2 by linarith) hq
        (by positivity : 0 ≤ q / h) (by norm_num : (0 : ℝ) ≤ 2)
      exact (mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ R ^ 2 / d)).trans_eq (by ring)
    have hLt := div_le_div_of_nonneg_right hLoss (by positivity : 0 ≤ 2 * d)
    have he : 4 * R ^ 2 / u ^ 6 / d ≤ (R ^ 2 / u ^ 5) / (4 * d) := by
      apply (div_le_div_iff₀ hd0 (by positivity : 0 < 4 * d)).mpr
      have hu16 : (16 : ℝ) ≤ u := by linarith
      have hU := div_le_div_of_nonneg_left (sq_nonneg R) (by positivity : 0 < 16 * u ^ 5)
        (show 16 * u ^ 5 ≤ u ^ 6 by
          nlinarith only [mul_le_mul_of_nonneg_right hu16 (show 0 ≤ u ^ 5 by positivity)])
      exact (show 4 * R ^ 2 / u ^ 6 * (4 * d) = (R ^ 2 / u ^ 6) * (16 * d) by ring).le.trans
        ((mul_le_mul_of_nonneg_right hU (show 0 ≤ 16 * d by positivity)).trans_eq (by ring))
    have hA : R * (2 * u + 4) ≤ (R ^ 2 / u ^ 5) / (4 * d) := by
      refine le_trans ?_ (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 4 * d)
        (mul_le_mul_of_nonneg_left hdhi (by norm_num : (0 : ℝ) ≤ 4)))
      have hx : (96 * u + 192 : ℝ) ≤ u ^ 13 := by
        have h13 : u ^ 2 ≤ u ^ 13 := pow_le_pow_right₀ hu1 (by decide)
        nlinarith only [h13, mul_le_mul_of_nonneg_right (show 1000 ≤ u by linarith) hu0.le, hu]
      rw [show R ^ 2 / u ^ 5 / (4 * (12 * R / u ^ 18)) = R * (u ^ 13 / 48) by field_simp <;> ring]
      exact mul_le_mul_of_nonneg_left (by linarith only [hx]) hR0.le
    linarith only [hGt, hLt, he, hA,
      show R ^ 2 / u ^ 5 / (2 * d) = 2 * (R ^ 2 / u ^ 5 / (4 * d)) by ring]
  have hPair : N ^ r * Real.exp ((Real.exp 1 - 1) * (q / (q * h)) *
      ((R * q) / d) * R - (rLoss * (cap + 1)) / (2 * d)) ≤ (R ^ 4)⁻¹ := by
    have hPow : N ^ r ≤ Real.exp (2 * R * u) := by
      refine (pow_le_pow_left₀ hN0 hN r).trans_eq ?_
      rw [← hRlog, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hRlog, ← hR]
      congr 1
      ring
    refine (mul_le_mul hPow (Real.exp_le_exp.mpr hPairBound) (Real.exp_pos _).le (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add, ← hExp 4]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith only [hR1, huP 1 (by decide)]
  have hCommon : Real.exp (-(p * m) / 8) * (N * (2 * b)) ^ records ≤ (R ^ 4)⁻¹ := by
    have hpm : u ^ 2 / 2 ≤ p * m := by
      have hprod := mul_le_mul hp hm (by positivity : 0 ≤ R ^ 2 / (2 * u ^ 4)) hS
      rwa [show u ^ 6 / R ^ 2 * (R ^ 2 / (2 * u ^ 4)) = u ^ 2 / 2 by field_simp <;> ring] at hprod
    have hbN : N * (2 * b) ≤ R ^ 5 := by
      have hm := mul_le_mul hN (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2))
        (mul_nonneg (by norm_num) hb0) (by positivity : 0 ≤ R ^ 2)
      exact hm.trans (by
        have h := mul_le_mul_of_nonneg_right (show 2 ≤ R by linarith) (show 0 ≤ R ^ 4 by positivity)
        nlinarith only [h])
    have hPow : (N * (2 * b)) ^ records ≤ Real.exp (5 * u * s) := by
      refine (pow_le_pow_left₀ (by positivity) hbN records).trans_eq ?_
      rw [← hRlog, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← hs]
      congr 1
      ring
    refine (mul_le_mul_of_nonneg_left hPow (Real.exp_pos _).le).trans ?_
    rw [← Real.exp_add, ← hExp 4]
    apply Real.exp_le_exp.mpr
    have hS' := mul_le_mul_of_nonneg_left hRec (show 0 ≤ 5 * u by positivity)
    have hU := mul_le_mul_of_nonneg_right (show (10000 : ℝ) ≤ u from hu) hu0.le
    nlinarith only [hpm, hS', hU, hu]
  have hSmall4 : (R ^ 4)⁻¹ ≤ 1 / 1000 := by
    rw [inv_eq_one_div]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact (by linarith : (1000 : ℝ) ≤ R).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ R) (show 1 ≤ 4 by decide))
  have hErrPair : N ^ 2 * (b * (2 * b / Wn)) ≤ 1 / 1000 := by
    have hWpos : 0 < Wn := (by positivity : 0 < R ^ 20).trans_le hWn
    have hp : N ^ 2 * (b * (2 * b / Wn)) ≤ 2 * R ^ 8 / Wn := by
      have hm := mul_le_mul (pow_le_pow_left₀ hN0 hN 2)
        (mul_le_mul hb (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)) hWpos.le)
          (by positivity : 0 ≤ 2 * b / Wn) (by positivity : 0 ≤ R ^ 2))
          (by positivity : 0 ≤ b * (2 * b / Wn)) (by positivity : 0 ≤ (R ^ 2) ^ 2)
      exact hm.trans_eq (by ring)
    refine hp.trans ?_
    rw [div_le_iff₀ hWpos]
    have hR12 : (2000 : ℝ) ≤ R ^ 12 := (by linarith : (2000 : ℝ) ≤ R).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ R) (show 1 ≤ 12 by decide))
    have h := mul_le_mul_of_nonneg_right hR12 (show 0 ≤ R ^ 8 by positivity)
    nlinarith only [hWn, h, show R ^ 12 * R ^ 8 = R ^ 20 by rw [← pow_add]]
  have hErrDegree : m * (Real.exp (-(h * γ) / 2) + Real.exp (2 * N * γ - Real.log 2 * c)) ≤ 1 / 1000 := by
    have hmE := mul_le_mul hmU (add_le_add (Real.exp_le_exp.mpr hExpDegree1)
      (Real.exp_le_exp.mpr hExpDegree2)) (by positivity) (by positivity : 0 ≤ R ^ 2)
    rw [hExp4] at hmE
    refine hmE.trans ?_
    rw [show R ^ 2 * ((R ^ 4)⁻¹ + (R ^ 4)⁻¹) = 2 / R ^ 2 by field_simp <;> ring]
    rw [div_le_iff₀ (by positivity : 0 < R ^ 2)]
    nlinarith only [hR1, sq_nonneg (R - 10000)]
  have hErrOccupancy : (q * h) * Real.exp (N * (q / (q * h)) - Real.log 2 * d) ≤ 1 / 1000 := by
    refine (mul_le_mul hqh (Real.exp_le_exp.mpr hExpOccupancy) (Real.exp_pos _).le hR0.le).trans ?_
    rw [hExp4, show R * (R ^ 4)⁻¹ = 1 / R ^ 3 by field_simp]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact (by linarith : (1000 : ℝ) ≤ R).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ R) (show 1 ≤ 3 by decide))
  have hSigErr := (Real.exp_le_exp.mpr hExpSig).trans_eq hExp4
  linarith only [hSigErr, hSmall4, hErrPair, hErrDegree, hErrOccupancy, hPair, hCommon]

set_option maxHeartbeats 1200000 in
/-- The location scales are available for every sufficiently large graph
and every region of the size supplied by the stabilized rule. -/
theorem eventually_location_scales :
    ∀ᶠ n : ℕ in atTop, ∀ w : ℕ, (n : ℝ) ^ (1 / 6 : ℝ) ≤ w →
      Nonempty (LocationScales n (target n) w) := by
  have rn : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have un := Real.tendsto_log_atTop.comp rn
  have nn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ), rn.eventually_ge_atTop 200000,
    un.eventually_ge_atTop 10000, (Real.tendsto_log_atTop.comp un).eventually_ge_atTop 10000,
    eventually_log_pow_le_target 100, sampling_ratio_bounds, overlap_sampling_parameter_bounds,
    overlap_group_size_products, eventually_target_pow_le_graph_rpow 20 (by norm_num : (0 : ℝ) < 1 / 7),
    eventually_target_pow_le_graph_rpow 2 (by norm_num : (0 : ℝ) < 1 / 42),
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 7 - (1 / 40 + 1 / 1000))).comp nn).eventually_ge_atTop 8,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 84)).comp nn).eventually_ge_atTop 2]
    with n hn hr hu hlu hRBig ha hO hQ hn20 hn2 hnS hnB
  intro w hW
  let r := target n
  let R : ℝ := r
  let u := Real.log R
  let a := samplingRatio r
  let M := lowerTestSize r
  let b := largeCliqueOrder r
  let q := overlapGroupSize r
  let h := overlapBlockCount r
  let γ := overlapQuota r
  have hR0 : 0 < R := by change 200000 ≤ R at hr; linarith
  have hR1 : 1 ≤ R := by change 200000 ≤ R at hr; linarith
  have hu0 : 0 < u := by change 10000 ≤ u at hu; linarith
  change (10000 : ℝ) ≤ u at hu
  have hu1 : 1 ≤ u := by linarith
  have ha0 : 0 < a := zero_lt_one.trans_le ha.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_of_lt hn
  have hw0 : 0 < (w : ℝ) := (by positivity : 0 < (n : ℝ) ^ (1 / 6 : ℝ)).trans_le hW
  have huP (j : ℕ) (hj : j ≤ 100) : u ^ j ≤ R :=
    (pow_le_pow_right₀ hu1 hj).trans hRBig
  have hprod (j k : ℕ) (hj : j + k ≤ 100) : u ^ j ≤ R / u ^ k := by
    rw [le_div_iff₀ (by positivity), ← pow_add]
    exact huP _ hj
  have hlarge (j : ℕ) (hj : 1 ≤ j) : u ≤ u ^ j := by
    simpa only [pow_one] using (pow_le_pow_right₀ hu1 hj)
  have hf (x : ℝ) (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    linarith only [Nat.lt_floor_add_one x, hx]
  have hceil (x : ℝ) (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    linarith only [Nat.ceil_lt_add_one (zero_le_one.trans hx), hx]
  have hA2 : a ^ 2 ≤ R := ha.2.trans (div_le_self hR0.le (one_le_pow₀ hu1))
  have hAs : a ≤ Real.sqrt R := le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt hR0.le]; exact hA2)
  have hW7 : (n : ℝ) ^ (1 / 7 : ℝ) ≤ w :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)).trans hW
  have hw20 : R ^ 20 ≤ (w : ℝ) := hn20.trans hW7
  have hw2 : R ^ 2 ≤ (w : ℝ) := (pow_le_pow_right₀ hR1 (show 2 ≤ 20 by decide)).trans hw20
  have hbU : (b : ℝ) ≤ R ^ 2 := by
    have hf : (b : ℝ) ≤ R ^ 2 / (24000 * u) := Nat.floor_le (by positivity)
    exact hf.trans (div_le_self (by positivity) (by linarith))
  have hb0 : 0 < b := by
    by_contra! h
    have hz : b = 0 := Nat.eq_zero_of_le_zero h
    have ha' : 1 ≤ (M : ℝ) / (R * b) := ha.1
    rw [hz, Nat.cast_zero, mul_zero, div_zero] at ha'
    norm_num at ha'
  have hrlog : R / 4 ≤ Real.log (n : ℝ) := by
    have h1 := target_log_relation hn
    have h2 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9]) (show 0 ≤ R - 1 by linarith)
    change (R - 1) * Real.log 2 ≤ Real.log (n : ℝ) at h1
    change (200000 : ℝ) ≤ R at hr
    linarith only [h1, h2, hr]
  obtain ⟨hD, hγ0, hq2, hh0, _, _, hqγ, hhγ, hDγ, hqh⟩ := hO
  change 2 ≤ q at hq2
  change 0 < h at hh0
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hhP : (0 : ℝ) < h := by exact_mod_cast hh0
  have hγ0' : 0 < γ := hγ0
  obtain ⟨_, hhUpper, hqSquare, hqhR, hqu⟩ := hQ
  have hhLower : a * u ^ 18 ≤ (h : ℝ) := Nat.le_ceil _
  let m := ⌊R ^ 2 / u ^ 4⌋₊
  let s := ⌈u / 10000⌉₊
  let c := ⌊R / u ^ 4⌋₊
  let B := ⌈u ^ 6 * (w : ℝ) / R ^ 2⌉₊
  let N := ⌈4 * R * a⌉₊
  let d := ⌈2 * (N : ℝ) / h⌉₊
  let lost := ⌈R / u ^ 2⌉₊
  let cap := ⌊R / u ^ 3⌋₊
  have hc0 : 2 ≤ R / u ^ 4 :=
    (by linarith : (2 : ℝ) ≤ u).trans (by simpa only [pow_one] using (hprod 1 4 (by decide)))
  have hm0 : 2 ≤ R ^ 2 / u ^ 4 := hc0.trans
    (div_le_div_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_right hR1 hR0.le] : R ≤ R ^ 2)
      (by positivity))
  have hmL : R ^ 2 / (2 * u ^ 4) ≤ (m : ℝ) := by
    rw [show R ^ 2 / (2 * u ^ 4) = R ^ 2 / u ^ 4 / 2 by ring]
    exact hf _ hm0
  have hmU : (m : ℝ) ≤ R ^ 2 / u ^ 4 := Nat.floor_le (by positivity)
  have hmP : (0 : ℝ) < m := (by positivity : 0 < R ^ 2 / (2 * u ^ 4)).trans_le hmL
  have hcL : R / (2 * u ^ 4) ≤ (c : ℝ) := by
    rw [show R / (2 * u ^ 4) = R / u ^ 4 / 2 by ring]
    exact hf _ hc0
  have hcU : (c : ℝ) ≤ R / u ^ 4 := Nat.floor_le (by positivity)
  have hsL : u / 10000 ≤ (s : ℝ) := Nat.le_ceil _
  have hsU : (s : ℝ) ≤ u / 5000 := by
    have h1 : 1 ≤ u / 10000 := by change 10000 ≤ u at hu; linarith
    have h2 := hceil _ h1
    linarith only [h2]
  have hNL : 4 * R * a ≤ (N : ℝ) := Nat.le_ceil _
  have hNU : (N : ℝ) ≤ 5 * R * a := by
    have h1 := mul_le_mul_of_nonneg_left ha.1 hR0.le
    have h2 := Nat.ceil_lt_add_one (show 0 ≤ 4 * R * a by positivity)
    linarith only [h1, h2, hr]
  have hNP : (0 : ℝ) < N := (by positivity : 0 < 4 * R * a).trans_le hNL
  have hNR : (N : ℝ) ≤ R ^ 2 := by
    have he : 5 * a ≤ R := by
      have hs : 5 ≤ Real.sqrt R := by
        apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
        rw [Real.sq_sqrt hR0.le]
        linarith
      have hx := mul_le_mul hs hAs ha0.le (by positivity : 0 ≤ Real.sqrt R)
      rwa [← pow_two, Real.sq_sqrt hR0.le] at hx
    exact hNU.trans (by nlinarith only [mul_le_mul_of_nonneg_left he hR0.le])
  have hNγ : (N : ℝ) * γ ≤ 5 * R / u ^ 8 :=
    (mul_le_mul_of_nonneg_right hNU hγ0'.le).trans_eq (by
      change 5 * R * a * (1 / (a * u ^ 8)) = _
      field_simp)
  have hdL : 2 * (N : ℝ) / h ≤ (d : ℝ) := Nat.le_ceil _
  have hd0 : 4 * R / u ^ 18 ≤ 2 * (N : ℝ) / h := by
    have hb : h ≤ 2 * a * u ^ 18 := hhUpper
    refine le_trans ?_ (div_le_div_of_nonneg_left (by positivity)
      hhP hb)
    rw [le_div_iff₀ (by positivity : 0 < 2 * a * u ^ 18)]
    rw [show 4 * R / u ^ 18 * (2 * a * u ^ 18) = 2 * (4 * R * a) by field_simp <;> ring]
    linarith only [hNL]
  have hdU : (d : ℝ) ≤ 12 * R / u ^ 18 := by
    have hb : 2 * (N : ℝ) / h ≤ 10 * R / u ^ 18 := by
      refine le_trans ?_ (by rfl : (10 * R / u ^ 18 : ℝ) ≤ _)
      rw [div_le_div_iff₀ hhP (by positivity)]
      have hx := mul_le_mul_of_nonneg_left hhLower (show 0 ≤ 10 * R by positivity)
      have hy := mul_le_mul_of_nonneg_right hNU (show 0 ≤ u ^ 18 by positivity)
      nlinarith only [hx, hy]
    have hs := Nat.ceil_lt_add_one (show 0 ≤ 2 * (N : ℝ) / h by positivity)
    have hlarge := hprod 1 18 (by decide)
    rw [show 10 * R / u ^ 18 = 10 * (R / u ^ 18) by ring] at hb
    rw [show 12 * R / u ^ 18 = 12 * (R / u ^ 18) by ring]
    linarith only [hb, hs, hlarge, hu1]
  have hdP : (0 : ℝ) < d := (by positivity : 0 < 2 * (N : ℝ) / h).trans_le hdL
  have hLost : (lost : ℝ) ≤ R / 2 := by
    have h0 : u ≤ R / u ^ 2 := by simpa only [pow_one] using (hprod 1 2 (by decide))
    have hl := hceil (R / u ^ 2) (hu1.trans h0)
    refine hl.trans ?_
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show 2 * (R / u ^ 2) * 2 = 4 * R / u ^ 2 by ring,
      div_le_iff₀ (by positivity : 0 < u ^ 2)]
    have he : (4 : ℝ) ≤ u ^ 2 := (by change 10000 ≤ u at hu; linarith : 4 ≤ u).trans (hlarge 2 (by decide))
    nlinarith only [mul_le_mul_of_nonneg_right he hR0.le]
  have hLost' : lost < r := by
    have hh : (lost : ℝ) < (r : ℝ) := hLost.trans_lt (by linarith : R / 2 < R)
    exact_mod_cast hh
  have hcap : (cap : ℝ) + 1 ≤ 2 * (R / u ^ 3) := by
    have hh := Nat.floor_le (show 0 ≤ R / u ^ 3 by positivity)
    have h := hprod 1 3 (by decide)
    linarith only [hh, h, hu1]
  have hLossProd : R ^ 2 / u ^ 5 ≤ (lost : ℝ) * ((cap : ℝ) + 1) := by
    apply le_trans _ (mul_le_mul (Nat.le_ceil (R / u ^ 2)) (Nat.lt_floor_add_one (R / u ^ 3)).le
      (by positivity : 0 ≤ R / u ^ 3) (Nat.cast_nonneg lost))
    ring_nf
    exact le_rfl
  have hBbase : 1 ≤ u ^ 6 * (w : ℝ) / R ^ 2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [one_mul, one_mul] using hw2.trans
      (le_mul_of_one_le_left (Nat.cast_nonneg w) (one_le_pow₀ hu1 : 1 ≤ u ^ 6))
  have hBL : u ^ 6 / R ^ 2 ≤ (B : ℝ) / w := by
    rw [le_div_iff₀ hw0, show u ^ 6 / R ^ 2 * w = u ^ 6 * (w : ℝ) / R ^ 2 by ring]
    exact Nat.le_ceil _
  have hBU : (B : ℝ) / w ≤ 2 * u ^ 6 / R ^ 2 := by
    rw [div_le_iff₀ hw0, show 2 * u ^ 6 / R ^ 2 * w = 2 * (u ^ 6 * (w : ℝ) / R ^ 2) by ring]
    exact hceil _ hBbase
  have hBsub : B ≤ w := by
    have h1 : 2 * u ^ 6 / R ^ 2 ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have h := huP 6 (by decide)
      nlinarith only [h, mul_le_mul_of_nonneg_right (show 2 ≤ R by linarith) hR0.le]
    exact_mod_cast (div_le_one hw0).mp (hBU.trans h1)
  have hBfrac : (w : ℝ) / R ^ 2 ≤ B := by
    refine le_trans ?_ (Nat.le_ceil _)
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (Nat.cast_nonneg w)
      (one_le_pow₀ hu1)) (by positivity)
  have hB7 : (n : ℝ) ^ (1 / 7 : ℝ) ≤ B := by
    have hn52 := div_le_div_of_nonneg_left (by positivity : 0 ≤ (n : ℝ) ^ (1 / 6 : ℝ))
      (by positivity : 0 < R ^ 2) hn2
    rw [← Real.rpow_sub hn0, show (1 / 6 - 1 / 42 : ℝ) = 1 / 7 by norm_num] at hn52
    exact hn52.trans ((div_le_div_of_nonneg_right hW (by positivity)).trans hBfrac)
  have hStart : (n : ℝ) ^ (1 / 7 : ℝ) ≤ w * (R⁻¹ ^ 10) ^ q / 2 := by
    have hA : ((n : ℝ) ^ (-(1 / 84) : ℝ)) ≤ (R⁻¹ ^ 10) ^ q := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : 0 < R⁻¹ ^ 10),
        Real.rpow_def_of_pos hn0, Real.exp_le_exp, Real.log_pow, Real.log_inv]
      change Real.log (n : ℝ) * (-(1 / 84)) ≤ (10 : ℝ) * (-u) * q
      change (q : ℝ) * u ≤ R / 10000 at hqu
      nlinarith only [hrlog, hqu, hR0]
    have hp := mul_le_mul hW hA (Real.rpow_nonneg hn0.le _) (Nat.cast_nonneg w)
    rw [← Real.rpow_add hn0, show (1 / 6 + -(1 / 84) : ℝ) = 1 / 7 + 1 / 84 by norm_num,
      Real.rpow_add hn0] at hp
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      ((mul_le_mul_of_nonneg_left hnB (Real.rpow_nonneg hn0.le _)).trans hp)
  have hSigBudget :
      let dSig := ⌊2 * (100 * u / R) * (m : ℝ)⌋₊
      let cutoff := ⌈(n : ℝ) ^ (1 / 40 : ℝ)⌉₊
      (((m + 1) ^ dSig * cutoff * 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 7 : ℝ) := by
    intro dSig cutoff
    have h100 : (100 : ℝ) ≤ (r : ℝ) := by change 100 ≤ R; linarith
    have hs : (((m + 1) ^ dSig : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 1000 : ℝ) :=
      initial_signature_count_le hn (by exact_mod_cast h100) hu hrlog hmU
    have hC : (cutoff : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 40 : ℝ) :=
      hceil _ (Real.one_le_rpow hn1 (by norm_num))
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul hs hC (Nat.cast_nonneg _) (by positivity))
      (by norm_num : (0 : ℝ) ≤ 4)).trans ?_
    rw [show (n : ℝ) ^ (1 / 7 : ℝ) = (n : ℝ) ^ (1 / 40 + 1 / 1000 : ℝ) *
          (n : ℝ) ^ (1 / 7 - (1 / 40 + 1 / 1000) : ℝ) by rw [← Real.rpow_add hn0, add_sub_cancel]]
    rw [Real.rpow_add hn0]
    change (8 : ℝ) ≤ (n : ℝ) ^ (1 / 7 - (1 / 40 + 1 / 1000) : ℝ) at hnS
    have hh := mul_le_mul_of_nonneg_left hnS
      (show 0 ≤ (n : ℝ) ^ (1 / 40 : ℝ) * (n : ℝ) ^ (1 / 1000 : ℝ) by positivity)
    nlinarith only [hh]
  have hDensity : 8 * (100 * u / R) ≤ γ := by
    change 8 * (100 * u / R) ≤ 1 / (a * u ^ 8)
    rw [show 8 * (100 * u / R) = 800 * u / R by ring, div_le_div_iff₀ hR0 (by positivity), one_mul]
    have huS : 800 * u ^ 9 ≤ Real.sqrt R := by
      apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt hR0.le]
      have hbig : (640000 : ℝ) ≤ u ^ 2 := by
        change 10000 ≤ u at hu
        nlinarith only [hu, sq_nonneg (u - 10000)]
      exact (show (800 * u ^ 9) ^ 2 ≤ u ^ 20 by
        nlinarith only [mul_le_mul_of_nonneg_right hbig (show 0 ≤ u ^ 18 by positivity)]).trans
        (huP 20 (by decide))
    have hx := mul_le_mul huS hAs ha0.le (Real.sqrt_nonneg R)
    rw [← pow_two, Real.sq_sqrt hR0.le] at hx
    nlinarith only [hx]
  have hC' : (s : ℝ) ^ 2 / (R - (lost : ℝ)) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < R - (lost : ℝ))).mpr
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg s) (hsU.trans (by linarith : u / 5000 ≤ u)) 2
    have he : 4 * u ^ 2 ≤ R := by
      have hh := mul_le_mul_of_nonneg_right (show 4 ≤ u by linarith) (show 0 ≤ u ^ 2 by positivity)
      exact (show 4 * u ^ 2 ≤ u ^ 3 by nlinarith only [hh]).trans (huP _ (by decide))
    linarith only [hh, he, hLost]
  have hSmall : (m : ℝ) * ((c : ℝ) / (R - (lost : ℝ))) ^ s < ((B : ℝ) / w) * m / 4 := by
    have hRat : (c : ℝ) / (R - (lost : ℝ)) ≤ u⁻¹ ^ 3 := by
      refine (div_le_div_of_nonneg_right hcU (by linarith : 0 ≤ R - (lost : ℝ))).trans ?_
      refine (div_le_div_of_nonneg_left (by positivity : 0 ≤ R / u ^ 4)
        (by positivity : 0 < R / 2) (by linarith : R / 2 ≤ R - (lost : ℝ))).trans ?_
      rw [show R / u ^ 4 / (R / 2) = 2 / u ^ 4 by field_simp <;> ring,
        inv_pow, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_right (show 2 ≤ u by linarith) (show 0 ≤ u ^ 3 by positivity)]
    have hpow := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg c)
      (show 0 ≤ R - (lost : ℝ) by linarith)) hRat s
    have hExp : (u⁻¹ ^ 3) ^ s ≤ R⁻¹ ^ 3 := by
      rw [show (u⁻¹ ^ 3) ^ s = Real.exp (Real.log (u⁻¹ ^ 3) * s) by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : 0 < u⁻¹ ^ 3)],
        show R⁻¹ ^ 3 = Real.exp (Real.log R⁻¹ * (3 : ℝ)) by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : 0 < R⁻¹)]
          norm_num,
        Real.exp_le_exp, Real.log_pow, Real.log_inv, Real.log_inv]
      have hMul := mul_le_mul hsL (show (10000 : ℝ) ≤ Real.log u from hlu)
        (by norm_num : (0 : ℝ) ≤ 10000) (Nat.cast_nonneg s)
      change (3 : ℝ) * (-Real.log u) * (s : ℝ) ≤ -u * 3
      nlinarith only [hMul]
    have h4 : R⁻¹ ^ 3 < (B : ℝ) / w / 4 := by
      refine lt_of_lt_of_le ?_ (div_le_div_of_nonneg_right hBL (by norm_num))
      rw [inv_pow, inv_eq_one_div, div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      have h1 : (4 : ℝ) < R := by linarith
      have hp := mul_lt_mul_of_pos_right (h1.trans_le (le_mul_of_one_le_right hR0.le (one_le_pow₀ hu1 : 1 ≤ u ^ 6)))
        (show 0 < R ^ 2 by positivity)
      nlinarith only [hp]
    have hlt := mul_lt_mul_of_pos_left (hpow.trans_lt (hExp.trans_lt h4)) hmP
    nlinarith only [hlt]
  have hBudget : R / 2 + 1 + (s : ℝ) * ((cap : ℝ) + 1) + 2 * (N : ℝ) * γ ≤ R := by
    have hsCap := mul_le_mul (hsU.trans (by linarith : u / 5000 ≤ u)) hcap
      (by positivity : 0 ≤ (cap : ℝ) + 1) hu0.le
    rw [show u * (2 * (R / u ^ 3)) = 2 * R / u ^ 2 by field_simp <;> ring] at hsCap
    have h1 : 2 * R / u ^ 2 ≤ R / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 8)]
      have h := mul_le_mul_of_nonneg_right
        ((by linarith : (16 : ℝ) ≤ u).trans (hlarge 2 (by decide))) hR0.le
      nlinarith only [h]
    have h2 : 5 * R / u ^ 8 ≤ R / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 16)]
      have h := mul_le_mul_of_nonneg_right
        ((by linarith : (80 : ℝ) ≤ u).trans (hlarge 8 (by decide))) hR0.le
      nlinarith only [h]
    nlinarith only [hsCap, hNγ, h1, h2, hr]
  refine ⟨⟨m, s, c, B, N, d, lost, cap, by exact_mod_cast hmP,
    by exact_mod_cast ((by positivity : 0 < u / 10000).trans_le hsL),
    by exact_mod_cast hNP, by exact_mod_cast hdP, ?_, hsU.trans (by linarith), hBsub, hBfrac,
    hBU, hB7, hStart, hSigBudget, hDensity, hLost', hC', hSmall, hBudget, hNL, hNU, hNR, ?_⟩⟩
  · have haM : R * a * (b : ℝ) = M := by
      change R * ((M : ℝ) / (R * b)) * b = M
      field_simp
    have hx := mul_le_mul_of_nonneg_right hNL (Nat.cast_nonneg b)
    have hxx : (2 : ℝ) * M ≤ (N : ℝ) * b := by nlinarith only [hx, haM, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    change 2 * M ≤ N * b
    exact_mod_cast hxx
  · dsimp only
    push_cast
    let dSig := ⌊2 * (100 * u / R) * (m : ℝ)⌋₊
    have hdSig : (dSig : ℝ) ≥ 2 * (m : ℝ) * (100 * u / R) - 1 := by
      have hx := Nat.lt_floor_add_one (2 * (100 * u / R) * (m : ℝ))
      linarith only [hx]
    exact location_errors_small rfl rfl hR0 hu rfl hRBig hn20
      ⟨Nat.cast_nonneg b, hbU, Nat.cast_nonneg N, hNR, Nat.cast_nonneg m,
        hmU.trans (div_le_self (by positivity) (one_le_pow₀ hu1)), hq0, hhP, hqhR, hdP,
        Nat.cast_nonneg s, hsU.trans (by linarith)⟩ hsU hdSig hmL hhγ hNγ hcL hdL
      (hd0.trans hdL) hdU hqh hLossProd hBL (by positivity)

end LocallyRamsey
