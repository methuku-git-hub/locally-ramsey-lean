module

public import LocallyRamsey.Lower.OverlapScales

public section

namespace LocallyRamsey

/-- The four error probabilities in the initial sampling experiment
are small once the basic rounded parameter bounds have been verified. -/
theorem initial_sampling_error_lt_one {r u v b K l m s cap limit : ℝ}
    (hu : 10000 ≤ u) (hr : 100 ≤ r) (hlogr : Real.log r = u)
    (hv : r ^ 10 ≤ v) (hb : 0 < b) (hK : 0 < K) (hl : 0 < l) (hm : 0 < m)
    (hs : 0 ≤ s) (hsc : s ≤ u / 5000)
    (hM : r ^ 2 / (2 * u ^ 4) ≤ m) (hMu : m ≤ r ^ 2)
    (hB : K * b ≤ r ^ 3) (hL : l ≤ r) (hLKb : 1 ≤ l * (K * b))
    (hcap : u ^ 6 / 2 ≤ cap / K)
    (hRatio : u ^ 10 ≤ r / K) (hsK : s * K ≤ r / 4)
    (hDegree : 8 * l * (100 * u / r) ≤ 1)
    (hLimit : u ^ 6 / r ^ 2 ≤ limit / v) :
    let p := 8 * (K * b) / v
    let payoff := r / (4 * l * K)
    (l * (K * b)) ^ s *
        Real.exp (l * payoff - Real.log 2 * ((r - s * K) / K)) +
      (l ^ 2 * ((K * b) * p) +
       m * Real.exp (l * ((100 * u / r * v) * p / (b * K)) - Real.log 2 * (cap / K)) +
       Real.exp (-(limit / v * m) / 8) * (l * (v * p)) ^ s) < 1 := by
  let p := 8 * (K * b) / v
  let payoff := r / (4 * l * K)
  change (l * (K * b)) ^ s *
        Real.exp (l * payoff - Real.log 2 * ((r - s * K) / K)) +
      (l ^ 2 * ((K * b) * p) +
       m * Real.exp (l * ((100 * u / r * v) * p / (b * K)) - Real.log 2 * (cap / K)) +
       Real.exp (-(limit / v * m) / 8) * (l * (v * p)) ^ s) < 1
  have hr0 : 0 < r := by linarith
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hv0 : 0 < v := (by positivity : 0 < r ^ 10).trans_le hv
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2nonneg : 0 ≤ Real.log 2 := by linarith
  have hPow (k : ℕ) (hk : 2 ≤ k) : u ^ 2 ≤ u ^ k := pow_le_pow_right₀ hu1 hk
  have hPowU (k : ℕ) (hk : 1 ≤ k) : u ≤ u ^ k := by
    simpa only [pow_one] using pow_le_pow_right₀ hu1 hk
  have hexp : Real.exp 4 ≥ 4 := by linarith [Real.add_one_le_exp 4]
  have hfour : Real.exp (-4) ≤ (1 : ℝ) / 4 := by
    rw [Real.exp_neg, ← one_div, div_le_div_iff_of_pos_left (by norm_num) (Real.exp_pos _) (by norm_num)]
    exact hexp
  have hBase4 : l * (K * b) ≤ r ^ 4 :=
    (mul_le_mul hL hB (by positivity) hr0.le).trans_eq (by ring)
  have hBase8 : l * (v * p) ≤ r ^ 8 := by
    have he : l * (v * p) = 8 * (l * (K * b)) := by dsimp [p]; field_simp
    rw [he]
    have hr4 : (8 : ℝ) ≤ r ^ 4 := by
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 100 by norm_num) hr 4
      norm_num at h
      linarith
    calc
      _ ≤ 8 * r ^ 4 := mul_le_mul_of_nonneg_left hBase4 (by norm_num)
      _ ≤ r ^ 4 * r ^ 4 := mul_le_mul_of_nonneg_right hr4 (by positivity)
      _ = _ := by ring
  have hsPow (base : ℝ) (hbase : 0 < base) (k : ℕ) (h : base ≤ r ^ k) :
      base ^ s ≤ Real.exp (s * k * u) := by
    rw [Real.rpow_def_of_pos hbase]
    apply Real.exp_le_exp.mpr
    have hlog := Real.log_le_log hbase h
    rw [Real.log_pow, hlogr] at hlog
    nlinarith only [mul_le_mul_of_nonneg_right hlog hs]
  have hFirst : (l * (K * b)) ^ s *
        Real.exp (l * payoff - Real.log 2 * ((r - s * K) / K)) ≤ 1 / 4 := by
    calc
      _ ≤ Real.exp (s * (4 : ℕ) * u) *
          Real.exp (l * payoff - Real.log 2 * ((r - s * K) / K)) :=
        mul_le_mul_of_nonneg_right (hsPow _ (by positivity) 4 hBase4) (Real.exp_pos _).le
      _ ≤ Real.exp (-4) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hpay : l * payoff = (r / K) / 4 := by dsimp [payoff]; field_simp
        have hsk : 3 * (r / K) / 4 ≤ (r - s * K) / K := by
          rw [show 3 * (r / K) / 4 = (3 * r / 4) / K by ring]
          exact div_le_div_of_nonneg_right (by linarith only [hsK]) hK.le
        have hn : 0 ≤ (r - s * K) / K := (by positivity : 0 ≤ 3 * (r / K) / 4).trans hsk
        have he : 3 * (r / K) / 8 ≤ Real.log 2 * ((r - s * K) / K) := by
          have h1 := mul_le_mul_of_nonneg_right hlog2 hn
          linarith only [h1, hsk]
        have hs' := mul_le_mul_of_nonneg_right hsc hu0.le
        norm_num
        rw [hpay]
        nlinarith only [he, hRatio, hs', hPow 10 (by decide), hu]
      _ ≤ _ := hfour
  have hSecond : l ^ 2 * ((K * b) * p) < 1 / 4 := by
    dsimp [p]
    rw [← mul_div_assoc, ← mul_div_assoc, div_lt_iff₀ hv0]
    have hp : l ^ 2 * ((K * b) * (8 * (K * b))) ≤ 8 * r ^ 8 := by
      have hlB := pow_le_pow_left₀ (show 0 ≤ l * (K * b) by positivity) hBase4 2
      ring_nf at hlB ⊢
      nlinarith only [hlB]
    refine hp.trans_lt ?_
    have hr2 : (32 : ℝ) < r ^ 2 := by
      have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 100 by norm_num) hr 2
      norm_num at h
      linarith
    have h := mul_lt_mul_of_pos_right hr2 (show 0 < r ^ 8 by positivity)
    rw [show r ^ 2 * r ^ 8 = r ^ 10 by ring] at h
    linarith only [h, hv]
  have hThird : m * Real.exp (l * ((100 * u / r * v) * p / (b * K)) -
      Real.log 2 * (cap / K)) ≤ 1 / 4 := by
    have he : l * ((100 * u / r * v) * p / (b * K)) = 8 * l * (100 * u / r) := by
      dsimp [p]
      field_simp
    have hd : (0 : ℝ) ≤ cap / K := (by positivity : 0 ≤ u ^ 6 / 2).trans hcap
    calc
      _ ≤ r ^ 2 * Real.exp (l * ((100 * u / r * v) * p / (b * K)) -
        Real.log 2 * (cap / K)) := mul_le_mul_of_nonneg_right hMu (Real.exp_pos _).le
      _ ≤ Real.exp (-4) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos hr0, hlogr, ← Real.exp_add, he]
        have h1 := mul_le_mul_of_nonneg_right hlog2 hd
        have h2 : Real.log 2 * (cap / K) ≥ u ^ 6 / 4 := by linarith only [h1, hcap]
        apply Real.exp_le_exp.mpr
        norm_num
        nlinarith only [hDegree, h2, hPow 6 (by decide), hu]
      _ ≤ _ := hfour
  have hFourth : Real.exp (-(limit / v * m) / 8) * (l * (v * p)) ^ s ≤ 1 / 4 := by
    calc
      _ ≤ Real.exp (-(limit / v * m) / 8) * Real.exp (s * (8 : ℕ) * u) :=
        mul_le_mul_of_nonneg_left (hsPow _ (by dsimp [p]; positivity) 8 hBase8) (Real.exp_pos _).le
      _ ≤ Real.exp (-4) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h : u ^ 2 / 2 ≤ limit / v * m := by
          calc
            _ = (u ^ 6 / r ^ 2) * (r ^ 2 / (2 * u ^ 4)) := by field_simp
            _ ≤ _ := mul_le_mul hLimit hM (by positivity) ((by positivity : 0 ≤ u ^ 6 / r ^ 2).trans hLimit)
        have k := mul_le_mul_of_nonneg_right hsc hu0.le
        norm_num
        nlinarith only [h, k, hu]
      _ ≤ _ := hfour
  linarith only [hFirst, hSecond, hThird, hFourth]


/-- The rounded lengths and probability thresholds in the first
sampling experiment. -/
structure InitialSamplingScales (r b M v : ℕ) where
  K : ℕ
  draws : ℕ
  listLength : ℕ
  records : ℕ
  degreeCap : ℕ
  regionLimit : ℕ
  K_pos : 0 < K
  list_pos : 0 < listLength
  list_upper : (listLength : ℝ) ≤ (r : ℝ) ^ 2 / (Real.log (r : ℝ)) ^ 4
  list_lower : (r : ℝ) ^ 2 / (2 * (Real.log (r : ℝ)) ^ 4) ≤ (listLength : ℝ)
  records_eq : records = ⌈Real.log (r : ℝ) / 10000⌉₊
  cap_eq : degreeCap = ⌊(r : ℝ) / (Real.log (r : ℝ)) ^ 4⌋₊
  region_eq : regionLimit = ⌈(Real.log (r : ℝ)) ^ 6 * (v : ℝ) / (r : ℝ) ^ 2⌉₊
  draws_le_target : draws ≤ r
  covers : M ≤ draws * (K * b)
  small_collision : (records : ℝ) ^ 2 * ((K : ℝ) / r) ≤ 1 / 2
  small_common : let u := Real.log (r : ℝ)
    (listLength : ℝ) * ((degreeCap : ℝ) / r) ^ records <
      ((regionLimit : ℝ) / v) * listLength / 4
  region_budget : let u := Real.log (r : ℝ)
    (regionLimit : ℝ) ≤ (16 * u ^ 6 / (r : ℝ) ^ 2) * v / 8
  payoff : ℝ
  payoff_pos : 0 < payoff
  payoff_lower : let a := (M : ℝ) / ((r : ℝ) * b)
    (1 / (10 * a)) ≤ payoff
  K_upper : (K : ℝ) ≤ (r : ℝ) / (Real.log (r : ℝ)) ^ 10
  K_lower : (r : ℝ) / (2 * (Real.log (r : ℝ)) ^ 10) ≤ (K : ℝ)
  error : let u := Real.log (r : ℝ)
    let p := 8 * ((K * b : ℕ) : ℝ) / v
    ((draws * (K * b) : ℕ) : ℝ) ^ records *
      Real.exp ((draws : ℝ) * payoff - Real.log 2 * (((r : ℝ) - records * K) / K)) +
    ((draws : ℝ) ^ 2 * ((K * b : ℕ) * p) +
     listLength * Real.exp ((draws : ℝ) * ((100 * u / r * v) * p / (b * K)) -
       Real.log 2 * (degreeCap / K)) +
     Real.exp (-(((regionLimit : ℝ) / v) * listLength) / 8) *
       ((draws : ℝ) * (v * p)) ^ records) < 1

private theorem floor_at_least_half {x : ℝ} (h : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  linarith only [Nat.lt_floor_add_one x, h]

/-- Construct the rounded parameters and verify their probability
bounds. A record length proportional to the logarithm is sufficient
with a small absolute coefficient. -/
noncomputable def initial_scales_of_bounds {r b M v : ℕ}
    (hr : 100 ≤ r) (hb : 0 < b) (hB : (b : ℝ) ≤ (r : ℝ) ^ 2)
    (hv : (r : ℝ) ^ 10 ≤ v)
    (hu : 10000 ≤ Real.log (r : ℝ)) (hlogu : 10000 ≤ Real.log (Real.log (r : ℝ)))
    (hpow : (Real.log (r : ℝ)) ^ 12 ≤ Real.sqrt r)
    (ha : 1 ≤ (M : ℝ) / ((r : ℝ) * b))
    (haUpper : (M : ℝ) / ((r : ℝ) * b) ≤ Real.sqrt r) :
    InitialSamplingScales r b M v := by
  let R : ℝ := r
  let u := Real.log R
  let a := (M : ℝ) / (R * b)
  have hr' : 100 ≤ R := by dsimp [R]; exact_mod_cast hr
  have hR0 : 0 < R := by linarith
  have hU0 : 0 < u := by dsimp [u]; linarith
  have hU1 : 1 ≤ u := by dsimp [u]; linarith
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hv0 : 0 < (v : ℝ) := (by positivity : 0 < R ^ 10).trans_le hv
  have ha' : 0 < a := zero_lt_one.trans_le ha
  have hsq : u ^ 12 * u ^ 12 ≤ R := by
    have h := mul_le_mul hpow hpow (show 0 ≤ u ^ 12 by positivity) (Real.sqrt_nonneg _)
    change u ^ 12 * u ^ 12 ≤ Real.sqrt R * Real.sqrt R at h
    rwa [← pow_two (Real.sqrt R), Real.sq_sqrt hR0.le] at h
  have hu_le {j : ℕ} (hj : j ≤ 12) : u ^ j ≤ u ^ 12 := pow_le_pow_right₀ hU1 hj
  have hbase : 2 ≤ R / u ^ 10 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h1 := mul_le_mul (hu_le (show 10 ≤ 12 by decide)) (show 2 ≤ u ^ 12 by
      have h := hu_le (show 1 ≤ 12 by decide)
      simp only [pow_one] at h
      dsimp [u] at *
      linarith only [hu, h]) (show (0 : ℝ) ≤ 2 by norm_num) (show 0 ≤ u ^ 12 by positivity)
    nlinarith only [h1, hsq]
  have hbase4 : 2 ≤ R / u ^ 4 := by
    have h : u ^ 4 ≤ u ^ 10 := pow_le_pow_right₀ hU1 (by decide)
    exact hbase.trans (div_le_div_of_nonneg_left hR0.le (by positivity) h)
  let K := ⌊R / u ^ 10⌋₊
  let cap := ⌊R / u ^ 4⌋₊
  let m := ⌊R ^ 2 / u ^ 4⌋₊
  let s := ⌈u / 10000⌉₊
  let limit := ⌈u ^ 6 * v / R ^ 2⌉₊
  let l := ⌈2 * (M : ℝ) / (K * b)⌉₊
  have hKlo : R / (2 * u ^ 10) ≤ (K : ℝ) := by
    rw [show R / (2 * u ^ 10) = (R / u ^ 10) / 2 by ring]
    exact floor_at_least_half hbase
  have hKhi : (K : ℝ) ≤ R / u ^ 10 := Nat.floor_le (by positivity)
  have hK0 : (0 : ℝ) < K := (by positivity : 0 < R / (2 * u ^ 10)).trans_le hKlo
  have hKn : 0 < K := by exact_mod_cast hK0
  have hcaplo : R / (2 * u ^ 4) ≤ (cap : ℝ) := by
    rw [show R / (2 * u ^ 4) = (R / u ^ 4) / 2 by ring]
    exact floor_at_least_half hbase4
  have hcaphi : (cap : ℝ) ≤ R / u ^ 4 := Nat.floor_le (by positivity)
  have hmlo : R ^ 2 / (2 * u ^ 4) ≤ (m : ℝ) := by
    rw [show R ^ 2 / (2 * u ^ 4) = (R ^ 2 / u ^ 4) / 2 by ring]
    apply floor_at_least_half
    exact hbase4.trans (div_le_div_of_nonneg_right (by nlinarith only [hr']) (by positivity))
  have hmhi : (m : ℝ) ≤ R ^ 2 := (Nat.floor_le (by positivity)).trans
    (div_le_self (by positivity) (one_le_pow₀ hU1))
  have hm0 : (0 : ℝ) < m := (by positivity : 0 < R ^ 2 / (2 * u ^ 4)).trans_le hmlo
  have hslo : u / 10000 ≤ (s : ℝ) := Nat.le_ceil _
  have hshi : (s : ℝ) ≤ u / 5000 := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ u / 10000 by positivity)
    change u / 10000 ≤ (s : ℝ) at hslo
    change (s : ℝ) < u / 10000 + 1 at ht
    dsimp [u] at *
    linarith only [ht, hu]
  have hM : (M : ℝ) = a * (R * b) := by
    dsimp [a]
    symm
    exact div_mul_cancel₀ _ (show R * (b : ℝ) ≠ 0 by positivity)
  have hM0 : (0 : ℝ) < M := by rw [hM]; positivity
  have hln1 : 1 ≤ l := by
    have hl := Nat.le_ceil (2 * (M : ℝ) / (K * b))
    have h0 : (0 : ℝ) < l := (by positivity : 0 < 2 * (M : ℝ) / (K * b)).trans_le hl
    exact_mod_cast h0
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hlhi : (l : ℝ) ≤ 5 * a * u ^ 10 := by
    have hround := Nat.ceil_lt_add_one (show 0 ≤ 2 * (M : ℝ) / (K * b) by positivity)
    change (l : ℝ) < 2 * (M : ℝ) / (K * b) + 1 at hround
    have h := div_le_div_of_nonneg_left (show 0 ≤ 2 * (M : ℝ) by positivity)
      (show 0 < (R / (2 * u ^ 10)) * b by positivity)
      (mul_le_mul_of_nonneg_right hKlo hb'.le)
    have he : 2 * (M : ℝ) / ((R / (2 * u ^ 10)) * b) = 4 * a * u ^ 10 := by rw [hM]; field_simp; ring
    rw [he] at h
    have ha10 := mul_le_mul ha (one_le_pow₀ hU1 (n := 10)) (by norm_num : 0 ≤ (1 : ℝ)) ha'.le
    norm_num at ha10
    linarith only [hround, h, ha10]
  have hlR : (l : ℝ) ≤ R := by
    have h5 : 5 * u ^ 10 ≤ u ^ 12 := by
      rw [show u ^ 12 = u ^ 10 * u ^ 2 by ring]
      have hu2 : 5 ≤ u ^ 2 := by dsimp [u] at *; nlinarith only [hu]
      nlinarith only [mul_le_mul_of_nonneg_left hu2 (show 0 ≤ u ^ 10 by positivity)]
    refine hlhi.trans ?_
    have hh := mul_le_mul haUpper h5 (show 0 ≤ 5 * u ^ 10 by positivity) (Real.sqrt_nonneg R)
    have hp := mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg R)
    change u ^ 12 ≤ Real.sqrt R at hpow
    rw [← pow_two, Real.sq_sqrt hR0.le] at hp
    nlinarith only [hh, hp]
  have hKratio : u ^ 10 ≤ R / K := by
    rw [le_div_iff₀ hK0]
    have h := (le_div_iff₀ (show 0 < u ^ 10 by positivity)).1 hKhi
    rwa [mul_comm] at h
  have hcapratio : u ^ 6 / 2 ≤ (cap : ℝ) / K := by
    refine (show u ^ 6 / 2 = (R / (2 * u ^ 4)) / (R / u ^ 10) by field_simp).le.trans ?_
    exact (div_le_div_of_nonneg_left (by positivity) hK0 hKhi).trans
      (div_le_div_of_nonneg_right hcaplo hK0.le)
  have hsp : (s : ℝ) ≤ u := hshi.trans (by linarith only [hU0])
  have hsK : (s : ℝ) * K ≤ R / 4 := by
    have he : u * (R / u ^ 10) ≤ R / 4 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (show 0 < u ^ 10 by positivity) (by norm_num : (0 : ℝ) < 4)]
      have hu9 : (4 : ℝ) ≤ u ^ 9 := by
        have hh := pow_le_pow_right₀ hU1 (show 1 ≤ 9 by decide)
        simp only [pow_one] at hh
        dsimp [u] at *
        linarith only [hu, hh]
      have hh := mul_le_mul_of_nonneg_left hu9 (show 0 ≤ R * u by positivity)
      rw [show R * u * u ^ 9 = R * u ^ 10 by ring] at hh
      nlinarith only [hh]
    exact (mul_le_mul hsp hKhi hK0.le hU0.le).trans he
  have hCollision : (s : ℝ) ^ 2 * ((K : ℝ) / R) ≤ 1 / 2 := by
    have hp : (s : ℝ) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hsp 2
    have hk : (K : ℝ) / R ≤ 1 / u ^ 10 :=
      (div_le_div_of_nonneg_right hKhi hR0.le).trans_eq (by field_simp)
    have hu8 : (2 : ℝ) ≤ u ^ 8 := by
      have hh := pow_le_pow_right₀ hU1 (show 1 ≤ 8 by decide)
      simp only [pow_one] at hh
      dsimp [u] at *
      linarith only [hu, hh]
    refine (mul_le_mul hp hk (by positivity) (by positivity)).trans ?_
    rw [show u ^ 2 * (1 / u ^ 10) = 1 / u ^ 8 by field_simp]
    exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hu8
  have hLimit0 : u ^ 6 / R ^ 2 ≤ (limit : ℝ) / v := by
    apply (le_div_iff₀ hv0).mpr
    exact (show u ^ 6 / R ^ 2 * v = u ^ 6 * v / R ^ 2 by ring).le.trans (Nat.le_ceil _)
  have hLimit2 : (limit : ℝ) ≤ 2 * (u ^ 6 * v / R ^ 2) := by
    have hm := Nat.ceil_lt_add_one (show 0 ≤ u ^ 6 * v / R ^ 2 by positivity)
    have h2 : 1 ≤ u ^ 6 * v / R ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      have hvr : R ^ 2 ≤ v := (pow_le_pow_right₀ (by linarith : 1 ≤ R) (show 2 ≤ 10 by decide)).trans hv
      exact hvr.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hU1) hv0.le)
    linarith only [hm, h2]
  have hSmall : (m : ℝ) * ((cap : ℝ) / R) ^ s < ((limit : ℝ) / v) * m / 4 := by
    have hlog : Real.log ((cap : ℝ) / R) ≤ -4 * Real.log u := by
      have hle : (cap : ℝ) / R ≤ 1 / u ^ 4 :=
        (div_le_div_of_nonneg_right hcaphi hR0.le).trans_eq (by field_simp)
      have hpos : 0 < (cap : ℝ) / R :=
        div_pos ((by positivity : 0 < R / (2 * u ^ 4)).trans_le hcaplo) hR0
      have hh := Real.log_le_log hpos hle
      rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by positivity), Real.log_one, Real.log_pow, zero_sub] at hh
      linarith only [hh]
    have hEq : ((cap : ℝ) / R) ^ s ≤ Real.exp (-4 * u) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos
        (div_pos ((by positivity : 0 < R / (2 * u ^ 4)).trans_le hcaplo) hR0)]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg s)
      have h := mul_le_mul hlogu hslo (show 0 ≤ u / 10000 by positivity) (by positivity : 0 ≤ Real.log u)
      nlinarith only [hh, h]
    have hExp : Real.exp (-4 * u) = 1 / R ^ 4 := by
      rw [show -4 * u = -(4 * u) by ring, Real.exp_neg, ← one_div, show 4 * u = (4 : ℕ) * u by norm_num,
        Real.exp_nat_mul, Real.exp_log hR0]
    have hcomp : 1 / R ^ 4 < (u ^ 6 / R ^ 2) / 4 := by
      rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
      have hR2 : 4 < R ^ 2 := by nlinarith only [hr', sq_nonneg (R - 100)]
      have hu6 := one_le_pow₀ hU1 (n := 6)
      have hh := mul_lt_mul_of_pos_left hR2 (show 0 < R ^ 2 by positivity)
      nlinarith only [hh, mul_le_mul_of_nonneg_right hu6 (show 0 ≤ R ^ 4 by positivity)]
    have hout := (hEq.trans_eq hExp).trans_lt
      (hcomp.trans_le (div_le_div_of_nonneg_right hLimit0 (by norm_num)))
    nlinarith only [mul_lt_mul_of_pos_right hout hm0]
  have hKle : (K : ℝ) ≤ R := hKhi.trans (div_le_self hR0.le (one_le_pow₀ hU1))
  have hDegree : 8 * (l : ℝ) * (100 * u / R) ≤ 1 := by
    have hAu : a * u ^ 12 ≤ R := by
      have hh := mul_le_mul haUpper hpow (show 0 ≤ u ^ 12 by positivity) (Real.sqrt_nonneg R)
      rwa [← pow_two, Real.sq_sqrt hR0.le] at hh
    have hU : 4000 * (a * u ^ 11) ≤ R := by
      have hh := mul_le_mul_of_nonneg_right (by dsimp [u]; linarith only [hu] : 4000 ≤ u)
        (show 0 ≤ a * u ^ 11 by positivity)
      nlinarith only [hh, hAu]
    have hh := mul_le_mul_of_nonneg_right hlhi (show 0 ≤ 8 * (100 * u / R) by positivity)
    have he : (5 * a * u ^ 10) * (8 * (100 * u / R)) = 4000 * (a * u ^ 11) / R := by ring
    rw [he] at hh
    nlinarith only [hh, (div_le_one hR0).mpr hU]
  let payoff := R / (4 * l * K)
  have hPay : 1 / (10 * a) ≤ payoff := by
    have hh := mul_le_mul hlhi hKhi hK0.le (by positivity : 0 ≤ 5 * a * u ^ 10)
    have he : (5 * a * u ^ 10) * (R / u ^ 10) = 5 * a * R := by field_simp
    rw [he] at hh
    -- The sharper product bound comes from the ceiling for the number of draws.
    have hround := Nat.ceil_lt_add_one (show 0 ≤ 2 * (M : ℝ) / (K * b) by positivity)
    change (l : ℝ) < 2 * (M : ℝ) / (K * b) + 1 at hround
    have hp := mul_lt_mul_of_pos_right hround hK0
    have hp' : (2 * (M : ℝ) / (K * b) + 1) * K = 2 * R * a + K := by
      rw [hM]
      field_simp
    rw [hp'] at hp
    have hKsmall : (K : ℝ) ≤ R * a / 2 := by
      have hU : (2 : ℝ) ≤ u ^ 10 := by
        have h := pow_le_pow_right₀ hU1 (show 1 ≤ 10 by decide)
        simp only [pow_one] at h
        dsimp [u] at *
        linarith only [hu, h]
      have hhK := hKhi.trans (div_le_div_of_nonneg_left hR0.le (by norm_num) hU)
      have haR := mul_le_mul_of_nonneg_left ha hR0.le
      linarith only [hhK, haR]
    dsimp [payoff]
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    nlinarith only [hp, hKsmall]
  have hCovers : M ≤ l * (K * b) := by
    have h := (div_le_iff₀ (show 0 < (K : ℝ) * b by positivity)).1
      (Nat.le_ceil (2 * (M : ℝ) / (K * b)))
    have hh : (M : ℝ) ≤ (l : ℝ) * (K * b) := by linarith only [h, hM0]
    exact_mod_cast hh
  have hKB : (K : ℝ) * b ≤ R ^ 3 :=
    (mul_le_mul hKle hB hb'.le hR0.le).trans_eq (by ring)
  have hFirst : 1 ≤ (l : ℝ) * ((K : ℝ) * b) := by
    have hl : (1 : ℝ) ≤ l := by exact_mod_cast hln1
    have hk : (1 : ℝ) ≤ K := by exact_mod_cast hKn
    have hbb : (1 : ℝ) ≤ b := by exact_mod_cast hb
    exact one_le_mul_of_one_le_of_one_le hl (one_le_mul_of_one_le_of_one_le hk hbb)
  refine ⟨K, l, m, s, cap, limit, hKn, (by exact_mod_cast hm0), Nat.floor_le (by positivity),
    hmlo, rfl, rfl, rfl, (by dsimp [R] at hlR; exact_mod_cast hlR), hCovers, hCollision, hSmall, ?_, payoff,
    (by dsimp [payoff]; positivity), hPay, hKhi, hKlo, ?_⟩
  · refine hLimit2.trans_eq ?_
    ring
  · have he := initial_sampling_error_lt_one hu hr' rfl hv hb' hK0 hl0 hm0 (Nat.cast_nonneg s) hshi hmlo
      hmhi hKB hlR hFirst hcapratio hKratio hsK hDegree hLimit0
    simpa only [Nat.cast_mul, Real.rpow_natCast] using he

end LocallyRamsey
