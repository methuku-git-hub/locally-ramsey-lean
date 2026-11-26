module

public import LocallyRamsey.Lower.InitialScales
public import LocallyRamsey.Lower.InitialRule
public import LocallyRamsey.Lower.EqualMarginals

public section

open Filter

namespace LocallyRamsey

/-- The number of neighbourhood signatures in the initial experiment
is small compared with every vertex set on which the clique supply is
used. The unrefined bound ((m+1)^d) suffices. -/
theorem initial_signature_count_le {n r m : ℕ} (hn : 0 < n)
    (hr : 100 ≤ r) (hu : 10000 ≤ Real.log (r : ℝ))
    (hrn : (r : ℝ) / 4 ≤ Real.log (n : ℝ))
    (hm : (m : ℝ) ≤ (r : ℝ) ^ 2 / (Real.log (r : ℝ)) ^ 4) :
    let density := 100 * Real.log (r : ℝ) / r
    let d := ⌊2 * density * (m : ℝ)⌋₊
    (((m + 1) ^ d : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 1000 : ℝ) := by
  intro density d
  let R : ℝ := r
  let u := Real.log R
  have hr' : (100 : ℝ) ≤ R := by dsimp [R]; exact_mod_cast hr
  have hr0 : 0 < R := by linarith
  have hu0 : 0 < u := by dsimp [u]; linarith only [hu]
  have hu1 : 1 ≤ u := by dsimp [u]; linarith only [hu]
  have hm2 : (m : ℝ) ≤ R ^ 2 := hm.trans (div_le_self (by positivity) (one_le_pow₀ hu1))
  have hlog : Real.log ((m : ℝ) + 1) ≤ 3 * u := by
    have hlo : (m : ℝ) + 1 ≤ R ^ 3 := by
      have hR := mul_le_mul_of_nonneg_right (show 2 ≤ R by linarith) (show 0 ≤ R ^ 2 by positivity)
      nlinarith only [hR, hm2, hr']
    have h := Real.log_le_log (show 0 < (m : ℝ) + 1 by positivity) hlo
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hd : (d : ℝ) ≤ 200 * R / u ^ 3 := by
    have h := Nat.floor_le (show 0 ≤ 2 * density * (m : ℝ) by dsimp [density]; positivity)
    calc
      _ ≤ 2 * density * (m : ℝ) := h
      _ ≤ 2 * density * (R ^ 2 / u ^ 4) :=
        mul_le_mul_of_nonneg_left hm (by dsimp [density]; positivity)
      _ = _ := by change 2 * (100 * u / R) * (R ^ 2 / u ^ 4) = _; field_simp; ring
  have hexp : (d : ℝ) * Real.log ((m : ℝ) + 1) ≤ (1 / 1000 : ℝ) * Real.log (n : ℝ) := by
    have hm0 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith only [show (0 : ℝ) ≤ (m : ℝ) by positivity]
    have h := mul_le_mul hd hlog (Real.log_nonneg hm0) (by positivity : 0 ≤ 200 * R / u ^ 3)
    have hflat : 200 * R / u ^ 3 * (3 * u) = 600 * R / u ^ 2 := by field_simp; ring
    rw [hflat] at h
    have h2 : 600 * R / u ^ 2 ≤ R / 4000 := by
      have hu2 : (2400000 : ℝ) ≤ u ^ 2 := by
        change 10000 ≤ u at hu
        nlinarith only [hu, sq_nonneg (u - 10000)]
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4000)]
      nlinarith only [mul_le_mul_of_nonneg_left hu2 hr0.le]
    exact h.trans (h2.trans (by linarith only [hrn]))
  push_cast
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (show 0 < (m : ℝ) + 1 by positivity),
    Real.rpow_def_of_pos (by exact_mod_cast hn)]
  exact Real.exp_le_exp.mpr (by linarith only [hexp])

/-- When the graph order is large, polynomial factors in the target
and the number of signatures are absorbed by the available vertex
set sizes. -/
theorem eventually_initial_signature_budgets :
    ∀ᶠ n : ℕ in atTop, ∀ (v b K m : ℕ),
      (n : ℝ) / (target n : ℝ) ^ 50 ≤ v →
      (b : ℝ) ≤ (target n : ℝ) ^ 2 → (K : ℝ) ≤ (target n : ℝ) →
      (m : ℝ) ≤ (target n : ℝ) ^ 2 / (Real.log (target n : ℝ)) ^ 4 →
      let large := ⌈(n : ℝ) ^ (1 / 60 : ℝ)⌉₊
      let cutoff := ⌈(n : ℝ) ^ (1 / 40 : ℝ)⌉₊
      let density := 100 * Real.log (target n : ℝ) / target n
      let d := ⌊2 * density * (m : ℝ)⌋₊
      8 * ((m + 1) ^ d * large + K * b) ≤ 3 * v ∧ (m + 1) ^ d * large < cutoff := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have h1 := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40 - (1 / 60 + 1 / 1000))).comp
    hcast).eventually_ge_atTop 3
  have h2 := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4 - 1 / 40)).comp
    hcast).eventually_ge_atTop 16
  filter_upwards [eventually_gt_atTop (0 : ℕ), target_tendsto_atTop.eventually_ge_atTop 100,
    (Real.tendsto_log_atTop.comp hrT).eventually_ge_atTop 10000,
    eventually_target_pow_le_graph_rpow 50 (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_target_pow_le_graph_rpow 3 (by norm_num : (0 : ℝ) < 1 / 40), h1, h2]
    with n hn hr hu h50 h3 hsmall hbig
  intro v b K m hv hb hK hm
  let r := target n
  let R : ℝ := r
  let u := Real.log R
  let N : ℝ := n
  let large := ⌈N ^ (1 / 60 : ℝ)⌉₊
  let cutoff := ⌈N ^ (1 / 40 : ℝ)⌉₊
  let density := 100 * u / R
  let d := ⌊2 * density * (m : ℝ)⌋₊
  have hr' : (100 : ℝ) ≤ R := by dsimp [R, r]; exact_mod_cast hr
  have hRpos : 0 < R := by linarith
  have hNpos : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_of_lt hn
  have hLog : R / 4 ≤ Real.log N := by
    have hs := target_log_relation hn
    have hh := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9]) (show 0 ≤ R - 1 by linarith)
    change (R - 1) * Real.log 2 ≤ Real.log N at hs
    linarith only [hs, hh, hr']
  have hcount : (((m + 1) ^ d : ℕ) : ℝ) ≤ N ^ (1 / 1000 : ℝ) :=
    initial_signature_count_le hn hr hu hLog hm
  have hlarge : (large : ℝ) ≤ 2 * N ^ (1 / 60 : ℝ) := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ N ^ (1 / 60 : ℝ) by positivity)
    have hp : 1 ≤ N ^ (1 / 60 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
    linarith only [h, hp]
  have hmul : (((m + 1) ^ d * large : ℕ) : ℝ) < N ^ (1 / 40 : ℝ) := by
    have h := mul_le_mul hcount hlarge (Nat.cast_nonneg large) (by positivity : 0 ≤ N ^ (1 / 1000 : ℝ))
    rw [Nat.cast_mul]
    refine h.trans_lt ?_
    change (3 : ℝ) ≤ N ^ (1 / 40 - (1 / 60 + 1 / 1000) : ℝ) at hsmall
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ N ^ (1 / 60 + 1 / 1000 : ℝ) by positivity)
    rw [← Real.rpow_add hNpos] at hh
    have hs : (1 / 40 - (1 / 60 + 1 / 1000) + (1 / 60 + 1 / 1000) : ℝ) = 1 / 40 := by ring
    rw [hs] at hh
    have he : N ^ (1 / 1000 : ℝ) * (2 * N ^ (1 / 60 : ℝ)) =
        2 * N ^ (1 / 60 + 1 / 1000 : ℝ) := by rw [Real.rpow_add hNpos]; ring
    rw [he]
    linarith only [hh, show 0 < N ^ (1 / 60 + 1 / 1000 : ℝ) by positivity]
  have hvlarge : N ^ (3 / 4 : ℝ) ≤ (v : ℝ) := by
    refine (show N ^ (3 / 4 : ℝ) = N / N ^ (1 / 4 : ℝ) from ?_).le.trans ?_
    · calc
        _ = N ^ (1 - 1 / 4 : ℝ) := by norm_num
        _ = _ := by rw [Real.rpow_sub hNpos, Real.rpow_one]
    · exact (div_le_div_of_nonneg_left hNpos.le (by positivity) h50).trans hv
  change 8 * ((m + 1) ^ d * large + K * b) ≤ 3 * v ∧ (m + 1) ^ d * large < cutoff
  constructor
  · have hprod : (K : ℝ) * b ≤ R ^ 3 :=
      (mul_le_mul hK hb (by positivity) hRpos.le).trans_eq (by ring)
    change (16 : ℝ) ≤ N ^ (3 / 4 - 1 / 40 : ℝ) at hbig
    have hh := mul_le_mul_of_nonneg_right hbig (show 0 ≤ N ^ (1 / 40 : ℝ) by positivity)
    rw [← Real.rpow_add hNpos, sub_add_cancel] at hh
    have hNum : (8 : ℝ) * ((((m + 1) ^ d * large : ℕ) : ℝ) + (K : ℝ) * b) ≤ 3 * v :=
      by linarith only [hmul, hprod.trans h3, hh, hvlarge, show 0 ≤ (v : ℝ) by positivity]
    exact_mod_cast hNum
  · exact_mod_cast hmul.trans_le (Nat.le_ceil (N ^ (1 / 40 : ℝ)))


open Classical in
/-- The original locally Ramsey condition gives a single sparse random
sample rule valid against every prescribed union of the selected family
of disjoint cliques. -/
theorem initial_sampling_rule :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      let r := target n
      let a := samplingRatio r
      let b := largeCliqueOrder r
      let u := Real.log (r : ℝ)
      let cutoff := ⌈(n : ℝ) ^ (1 / 40 : ℝ)⌉₊
      IsLocallyRamsey G (lowerTestSize r) r →
      ∃ (V' : Finset (Fin n)) (family : Finset (Fin n) → Prop)
        (μ : FiniteLaw (Finset (Fin n))) (K : ℕ),
        (0 < K ∧ (r : ℝ) / (2 * u ^ 10) ≤ (K : ℝ) ∧ (K : ℝ) ≤ (r : ℝ) / u ^ 10) ∧
        (n : ℝ) ^ (1 / 2 : ℝ) ≤ V'.card ∧
        (∀ A : Finset (Fin n), A ⊆ V' → cutoff ≤ A.card →
          ∃ C : Finset (Fin n), C ⊆ A ∧ C.card = b ∧ family C) ∧
        (∀ C, family C → G.IsClique (C : Set (Fin n))) ∧
        (∀ S, 0 < μ.prob S → S ⊆ V') ∧
        (∀ x ∈ V', μ.event (fun S => x ∈ S) ≤ 16 * u ^ 6 / (r : ℝ) ^ 2) ∧
        ∀ C : Fin K → Finset (Fin n), (∀ j, C j ⊆ V' ∧ (C j).card = b ∧ family (C j)) →
          (Pairwise fun i j => Disjoint (C i) (C j)) →
          (1 / (20 * a)) * K ≤ μ.mean (fun S =>
            (independenceOrder G (S ∩ Finset.univ.biUnion C) : ℝ)) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have huT := Real.tendsto_log_atTop.comp hrT
  have hlogPow := (isLittleO_log_rpow_rpow_atTop 12 (by norm_num : (0 : ℝ) < 1 / 2)).eventuallyLE
  have hN1 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hcast
  filter_upwards [lower_parameter_bounds, lower_clique_supply, lower_degree_supply,
    sampling_ratio_bounds, eventually_initial_signature_budgets,
    huT.eventually_ge_atTop 10000, (Real.tendsto_log_atTop.comp huT).eventually_ge_atTop 10000,
    hrT.eventually hlogPow, eventually_target_pow_le_graph_rpow 50 (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_target_pow_le_graph_rpow 60 (by norm_num : (0 : ℝ) < 1),
    hN1.eventually_ge_atTop 4]
    with n hp hclique hdegree hratio hbudget hu hlogu hpow hn50 hn60 hn1
  intro G r a b u cutoff hG
  obtain ⟨hn, hr, _, _, _, _⟩ := hp
  let N : ℝ := n
  let R : ℝ := r
  let large := ⌈N ^ (1 / 60 : ℝ)⌉₊
  have hnP : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hnOne : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_of_lt hn
  have hrP : 0 < R := by dsimp [R, r]; exact_mod_cast (show 0 < target n by omega)
  have huP : 0 < u := by change 10000 ≤ u at hu; linarith
  have hu1 : 1 ≤ u := by change 10000 ≤ u at hu; linarith
  have haP : 0 < a := zero_lt_one.trans_le hratio.1
  have hb : 0 < b := by
    by_contra! h
    have h0 : b = 0 := by omega
    have h' : (1 : ℝ) ≤ (lowerTestSize r : ℝ) / (R * (b : ℝ)) := hratio.1
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (by simpa only [h0, Nat.cast_zero, mul_zero, div_zero] using h')
  have hBu : (b : ℝ) ≤ R ^ 2 := by
    have h : (b : ℝ) ≤ R ^ 2 / (24000 * u) := Nat.floor_le (by positivity)
    refine h.trans (div_le_self (by positivity) ?_)
    linarith only [hu1]
  have hAu : a ≤ Real.sqrt R := by
    have ha2 : a ^ 2 ≤ R / u ^ 45 := hratio.2
    have h := ha2.trans (div_le_self hrP.le (one_le_pow₀ hu1))
    have he := Real.sq_sqrt hrP.le
    nlinarith only [h, he, Real.sqrt_nonneg R, haP]
  have huR : u ^ 12 ≤ Real.sqrt R := by
    change ‖u ^ (12 : ℝ)‖ ≤ ‖R ^ (1 / 2 : ℝ)‖ at hpow
    rw [Real.norm_of_nonneg (Real.rpow_nonneg huP.le _), Real.norm_of_nonneg (Real.rpow_nonneg hrP.le _),
      show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hpow
    rwa [Real.sqrt_eq_rpow]
  have hAll : N ^ (1 / 8 : ℝ) ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact (Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)).trans_eq (Real.rpow_one N)
  obtain ⟨U, _, hUsize, hDeg⟩ :=
    hdegree G hG (Finset.univ : Finset (Fin n)) hAll
  have hUs : N / R ^ 50 ≤ (U.card : ℝ) := by simpa using hUsize
  have hUpos : (0 : ℝ) < U.card := (by positivity : (0 : ℝ) < N / R ^ 50).trans_le hUs
  have hUne : U.Nonempty := Finset.card_pos.mp (by exact_mod_cast hUpos)
  have hU10 : R ^ 10 ≤ (U.card : ℝ) := by
    refine (le_div_iff₀ (by positivity : 0 < R ^ 50)).mpr ?_ |>.trans hUs
    rw [← pow_add]
    exact hn60.trans_eq (Real.rpow_one _)
  let c := initial_scales_of_bounds (M := lowerTestSize r) hr hb hBu hU10 hu hlogu huR
    hratio.1 hAu
  have hKu : (c.K : ℝ) ≤ R := c.K_upper.trans (div_le_self hrP.le (one_le_pow₀ hu1))
  obtain ⟨hPack, hCut⟩ := hbudget U.card b c.K c.listLength hUs hBu hKu c.list_upper
  have hSupply (A : Finset (Fin n)) (_ : A ⊆ U) (ha : large ≤ A.card) :
      ∃ C : Finset (Fin n), C ⊆ A ∧ C.card = b ∧ G.IsClique (C : Set (Fin n)) := by
    have h := (Nat.le_ceil (N ^ (1 / 60 : ℝ))).trans (show (large : ℝ) ≤ A.card by exact_mod_cast ha)
    obtain ⟨C, hc⟩ := (hclique G hG A h).1
    obtain ⟨hCA, hCard, hCl⟩ := mem_cliquesIn.mp hc
    exact ⟨C, hCA, hCard, hCl⟩
  have hRamsey (A : Finset (Fin n)) (_ : A ⊆ U) (hA : lowerTestSize r ≤ A.card) :
      ∃ Q : Finset (Fin n), Q ⊆ A ∧ Q.card = r ∧ Gᶜ.IsClique (Q : Set (Fin n)) := by
    obtain ⟨T, hTA, hCard⟩ := Finset.exists_subset_card_eq hA
    obtain ⟨Q, hQT, hQ⟩ := (hG T hCard).2
    exact ⟨Q, hQT.trans hTA, hQ.card_eq, hQ.isClique⟩
  have hDeg' (y : Fin n) (hy : y ∈ U) :
      ((U.filter (Gᶜ.Adj y)).card : ℝ) ≤ (100 * u / R) * U.card := by
    simpa only [neighborsIn] using hDeg y hy
  obtain ⟨V', family, μ, _, hSize, hSupp, hFam, hSupport, hMarg, hPay⟩ :=
    exists_initial_sample_in_dense_region G U hUne c.list_pos c.K_pos hb
      (show 0 < r by dsimp [r]; omega)
      (show 0 < 100 * u / R by positivity) c.payoff_pos (show 0 < 16 * u ^ 6 / R ^ 2 by positivity)
      hDeg' hSupply hRamsey c.covers c.small_collision c.small_common hPack hCut c.region_budget c.error
  have hVlarge : N ^ (1 / 2 : ℝ) ≤ (V'.card : ℝ) := by
    have hN3 : N ^ (3 / 4 : ℝ) ≤ (U.card : ℝ) := by
      calc
        _ = N / N ^ (1 / 4 : ℝ) := by
          rw [show (3 / 4 : ℝ) = 1 - 1 / 4 by norm_num, Real.rpow_sub hnP, Real.rpow_one]
        _ ≤ _ := (div_le_div_of_nonneg_left hnP.le (by positivity) hn50).trans hUs
    have hh := mul_le_mul_of_nonneg_right hn1 (by positivity : 0 ≤ N ^ (1 / 2 : ℝ))
    change 4 * N ^ (1 / 2 : ℝ) ≤ N ^ (1 / 4 : ℝ) * N ^ (1 / 2 : ℝ) at hh
    rw [← Real.rpow_add hnP, show (1 / 4 + 1 / 2 : ℝ) = 3 / 4 by norm_num] at hh
    linarith only [hh, hN3, hSize]
  refine ⟨V', family, μ, c.K, ⟨c.K_pos, c.K_lower, c.K_upper⟩, hVlarge, hSupp, hFam, hSupport,
    hMarg, fun C hC hDis => ?_⟩
  refine (?_ : _ ≤ (c.K : ℝ) * c.payoff / 2).trans (hPay C hC hDis)
  have h := mul_le_mul_of_nonneg_left c.payoff_lower (Nat.cast_nonneg c.K)
  change (c.K : ℝ) * (1 / (10 * a)) ≤ (c.K : ℝ) * c.payoff at h
  rw [show (1 : ℝ) / (20 * a) = (1 / (10 * a)) / 2 by ring]
  linarith only [h]



open Classical in
/-- Thin a class of comparable marginals to obtain a common inclusion
probability while retaining the clique-family guarantee. -/
theorem balanced_initial_rule :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      let r := target n
      let a := samplingRatio r
      let b := largeCliqueOrder r
      let u := Real.log (r : ℝ)
      let cutoff := ⌈(n : ℝ) ^ (1 / 40 : ℝ)⌉₊
      IsLocallyRamsey G (lowerTestSize r) r →
      ∃ (V₀ : Finset (Fin n)) (family : Finset (Fin n) → Prop)
        (μ : FiniteLaw (Finset (Fin n))) (K : ℕ) (p : ℝ),
        (0 < K ∧ (r : ℝ) / (2 * u ^ 10) ≤ (K : ℝ) ∧ (K : ℝ) ≤ (r : ℝ) / u ^ 10) ∧
        (n : ℝ) ^ (1 / 3 : ℝ) ≤ V₀.card ∧
        (∀ A : Finset (Fin n), A ⊆ V₀ → cutoff ≤ A.card →
          ∃ C : Finset (Fin n), C ⊆ A ∧ C.card = b ∧ family C) ∧
        (∀ C, family C → G.IsClique (C : Set (Fin n))) ∧
        (∀ S, 0 < μ.prob S → S ⊆ V₀) ∧
        ((1 : ℝ) / (r : ℝ) ^ 3 ≤ p ∧ p ≤ 16 * u ^ 6 / (r : ℝ) ^ 2) ∧
        (∀ x ∈ V₀, μ.event (fun S => x ∈ S) = p) ∧
        ∀ C : Fin K → Finset (Fin n), (∀ j, C j ⊆ V₀ ∧ (C j).card = b ∧ family (C j)) →
          (Pairwise fun i j => Disjoint (C i) (C j)) →
          (1 / (40 * a)) * K ≤ μ.mean (fun S =>
            (independenceOrder G (S ∩ Finset.univ.biUnion C) : ℝ)) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have huT := Real.tendsto_log_atTop.comp hrT
  have hlogPow := (isLittleO_log_rpow_rpow_atTop 12 (by norm_num : (0 : ℝ) < 1 / 2)).eventuallyLE
  have hN1 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp hcast
  have hN2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2 - 1 / 40)).comp hcast
  filter_upwards [initial_sampling_rule, lower_parameter_bounds, sampling_ratio_bounds,
    huT.eventually_ge_atTop 10000, hrT.eventually hlogPow,
    eventually_target_pow_le_graph_rpow 3 (by norm_num : (0 : ℝ) < 1 / 40),
    eventually_target_pow_le_graph_rpow 1 (by norm_num : (0 : ℝ) < 1 / 12),
    hN1.eventually_ge_atTop 4, hN2.eventually_ge_atTop 6] with n hInitial hp hratio hu hpow hN3 hN4 hn1 hn2
  intro G r a b u cutoff hG
  obtain ⟨hn, hr, _, _, hru, _⟩ := hp
  let N : ℝ := n
  let R : ℝ := r
  have hNpos : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hN1' : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_of_lt hn
  have hRpos : 0 < R := by dsimp [R, r]; exact_mod_cast (show 0 < target n by omega)
  have hUpos : 0 < u := by change 10000 ≤ u at hu; linarith
  have hU1 : 1 ≤ u := by change 10000 ≤ u at hu; linarith
  have haP : 0 < a := zero_lt_one.trans_le hratio.1
  have hb : 0 < b := by
    by_contra! h
    have h0 : b = 0 := by omega
    have h' : (1 : ℝ) ≤ (lowerTestSize r : ℝ) / (R * (b : ℝ)) := hratio.1
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (by simpa only [h0, Nat.cast_zero, mul_zero, div_zero] using h')
  have hbP : (0 : ℝ) < b := by exact_mod_cast hb
  have hBu : (b : ℝ) ≤ R ^ 2 := by
    have h : (b : ℝ) ≤ R ^ 2 / (24000 * u) := Nat.floor_le (by positivity)
    refine h.trans (div_le_self (by positivity) ?_)
    linarith only [hU1]
  have hAu : a ≤ Real.sqrt R := by
    have ha2 : a ^ 2 ≤ R / u ^ 45 := hratio.2
    have h := ha2.trans (div_le_self hRpos.le (one_le_pow₀ hU1))
    have he := Real.sq_sqrt hRpos.le
    nlinarith only [h, he, Real.sqrt_nonneg R, haP]
  have huR : u ^ 12 ≤ Real.sqrt R := by
    change ‖u ^ (12 : ℝ)‖ ≤ ‖R ^ (1 / 2 : ℝ)‖ at hpow
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hUpos.le _), Real.norm_of_nonneg (Real.rpow_nonneg hRpos.le _),
      show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hpow
    rwa [Real.sqrt_eq_rpow]
  obtain ⟨V', family, μ, K, ⟨hK, hKlo, hKhi⟩, hSize, hSupply, hFam, _, hUpper, hSample⟩ := hInitial G hG
  let α := 1 / (20 * a)
  let pmin := α / (2 * (b : ℝ))
  let pmax := 16 * u ^ 6 / R ^ 2
  let A := V'.filter (fun x => pmin ≤ μ.event (fun S => x ∈ S))
  let bad := V'.filter (fun x => μ.event (fun S => x ∈ S) < pmin)
  have hα : 0 < α := by dsimp [α]; positivity
  have hpmin : 0 < pmin := by dsimp [pmin]; positivity
  have hA : A ⊆ V' := Finset.filter_subset _ _
  have hbad : bad.card < cutoff + K * b :=
    card_low_marginals_lt G μ id V' hb hK hα family hSupply hSample
  have hGoodSize : N ^ (1 / 2 : ℝ) / 2 ≤ (A.card : ℝ) := by
    have hcut : (cutoff : ℝ) ≤ 2 * N ^ (1 / 40 : ℝ) := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ N ^ (1 / 40 : ℝ) by positivity)
      linarith only [h, Real.one_le_rpow hN1' (by norm_num : (0 : ℝ) ≤ 1 / 40)]
    have hKB : (K : ℝ) * b ≤ N ^ (1 / 40 : ℝ) := by
      have hk : (K : ℝ) ≤ R := hKhi.trans (div_le_self hRpos.le (one_le_pow₀ hU1))
      exact (mul_le_mul hk hBu hbP.le hRpos.le).trans_eq (by ring) |>.trans hN3
    have hkbad : (bad.card : ℝ) ≤ 3 * N ^ (1 / 40 : ℝ) := by
      have h : (bad.card : ℝ) ≤ cutoff + (K : ℝ) * b := by exact_mod_cast hbad.le
      linarith only [h, hcut, hKB]
    have hSplit : (A.card : ℝ) + bad.card = V'.card := by
      have he : bad = V'.filter (fun x => ¬ (pmin ≤ μ.event (fun S => x ∈ S))) := by
        ext x
        simp [bad]
      rw [he]
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := V') (fun x => pmin ≤ μ.event (fun S => x ∈ S))
    change (6 : ℝ) ≤ N ^ (1 / 2 - 1 / 40 : ℝ) at hn2
    have hh := mul_le_mul_of_nonneg_right hn2 (by positivity : 0 ≤ N ^ (1 / 40 : ℝ))
    rw [← Real.rpow_add hNpos, sub_add_cancel] at hh
    linarith only [hSize, hSplit, hkbad, hh]
  have hPow : pmax ≤ R ^ 2 * pmin := by
    have hR2 : (640 : ℝ) * u ^ 6 ≤ Real.sqrt R := by
      refine (show 640 * u ^ 6 ≤ u ^ 12 from ?_).trans huR
      rw [show u ^ 12 = u ^ 6 * u ^ 6 by ring]
      have h6 : 640 ≤ u ^ 6 := by
        have h := pow_le_pow_right₀ hU1 (show 1 ≤ 6 by decide)
        simp only [pow_one] at h
        change 10000 ≤ u at hu
        linarith only [h, hu]
      nlinarith only [mul_le_mul_of_nonneg_left h6 (show 0 ≤ u ^ 6 by positivity)]
    have heu : 640 * u ^ 6 * a ≤ R := by
      have h := mul_le_mul hR2 hAu haP.le (Real.sqrt_nonneg R)
      rwa [← pow_two (Real.sqrt R), Real.sq_sqrt hRpos.le] at h
    have hA' : 640 * u ^ 6 * a * b ≤ R ^ 3 :=
      (mul_le_mul heu hBu hbP.le (by positivity)).trans_eq (by ring)
    have hR1 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ (by
      have h : (100 : ℝ) ≤ R := by dsimp [R, r]; exact_mod_cast hr
      linarith) (by decide)
    dsimp [pmax, pmin, α]
    field_simp
    nlinarith only [hA', hR1]
  let m := ⌈4 * u⌉₊
  let size := ⌈N ^ (1 / 3 : ℝ)⌉₊
  have hm : (m + 1 : ℕ) ≤ r := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 4 * u by positivity)
    change (m : ℝ) < 4 * u + 1 at h
    change 8000 * u ≤ R at hru
    have hh : (m : ℝ) + 1 ≤ R := by linarith only [h, hru, hU1]
    dsimp [R] at hh
    exact_mod_cast hh
  have hRpow : R ^ 2 ≤ (2 : ℝ) ^ m := by
    have he : (R : ℝ) ^ 2 = Real.exp (2 * u) := by
      change R ^ 2 = Real.exp ((2 : ℕ) * Real.log R)
      rw [Real.exp_nat_mul, Real.exp_log hRpos]
    have hm' : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [he, hm', Real.exp_le_exp]
    have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hM : 4 * u ≤ (m : ℝ) := Nat.le_ceil _
    nlinarith only [hM, mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg m)]
  have hrange : pmax ≤ (2 : ℝ) ^ m * pmin :=
    hPow.trans (mul_le_mul_of_nonneg_right hRpow hpmin.le)
  have hsz : (m + 1) * size ≤ A.card := by
    have hsize : (size : ℝ) ≤ 2 * N ^ (1 / 3 : ℝ) := by
      have ht := Nat.ceil_lt_add_one (show 0 ≤ N ^ (1 / 3 : ℝ) by positivity)
      linarith only [ht, Real.one_le_rpow hN1' (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    have hmr : (m : ℝ) + 1 ≤ N ^ (1 / 12 : ℝ) := by
      refine (show (m : ℝ) + 1 ≤ R from ?_).trans ?_
      · dsimp [R]; exact_mod_cast hm
      · simpa only [pow_one] using hN4
    have h := mul_le_mul hmr hsize (Nat.cast_nonneg size) (by positivity : 0 ≤ N ^ (1 / 12 : ℝ))
    have he : N ^ (1 / 12 : ℝ) * (2 * N ^ (1 / 3 : ℝ)) = 2 * N ^ (5 / 12 : ℝ) := by
      rw [show (5 / 12 : ℝ) = 1 / 12 + 1 / 3 by ring, Real.rpow_add hNpos]
      ring
    rw [he] at h
    change 4 ≤ N ^ (1 / 12 : ℝ) at hn1
    have h' := mul_le_mul_of_nonneg_right hn1 (by positivity : 0 ≤ N ^ (5 / 12 : ℝ))
    rw [← Real.rpow_add hNpos, show (1 / 12 + 5 / 12 : ℝ) = 1 / 2 by ring] at h'
    have h'' : ((m : ℝ) + 1) * size ≤ A.card := by linarith only [h, h', hGoodSize]
    exact_mod_cast h''
  have hsizePos : 0 < size := by
    have ht := (show 0 < N ^ (1 / 3 : ℝ) by positivity).trans_le (Nat.le_ceil _)
    exact_mod_cast (show (0 : ℝ) < size from ht)
  obtain ⟨V₀, ν, T, p, hV, hVsize, hPmin, hPmax, hSubset, hMarg, hPay⟩ :=
    exists_balanced_sample_on_large_class G μ id A hpmin hrange (fun x hx =>
      ⟨(Finset.mem_filter.mp hx).2, hUpper x (hA hx)⟩) hsz hsizePos
  have hV' : V₀ ⊆ V' := hV.trans hA
  have hInv : 1 / R ^ 3 ≤ pmin := by
    have hR : 40 ≤ Real.sqrt R := by
      have h12 := pow_le_pow_right₀ hU1 (show 1 ≤ 12 by decide)
      simp only [pow_one] at h12
      change 10000 ≤ u at hu
      linarith only [huR, h12, hu]
    have h := mul_le_mul hR hAu haP.le (Real.sqrt_nonneg R)
    rw [← pow_two (Real.sqrt R), Real.sq_sqrt hRpos.le] at h
    have h2 := mul_le_mul h hBu hbP.le hRpos.le
    dsimp [pmin, α]
    field_simp
    nlinarith only [h2]
  have hV₀ : N ^ (1 / 3 : ℝ) ≤ V₀.card := (Nat.le_ceil _).trans (by exact_mod_cast hVsize)
  refine ⟨V₀, family, ν.map T, K, p, ⟨hK, hKlo, hKhi⟩, hV₀,
    (fun A hA' hsize => hSupply A (hA'.trans hV') hsize), hFam, ?_,
    ⟨hInv.trans hPmin, hPmax⟩, ?_, ?_⟩
  · intro S hS
    by_contra h
    have hn (x : Finset (Fin n) × (Fin n → Bool)) : T x ≠ S :=
      fun he => h (he ▸ (hSubset x).trans Finset.inter_subset_right)
    simp [FiniteLaw.map, hn] at hS
  · intro x hx
    rw [ν.event_map]
    exact hMarg x hx
  · intro C hC hDis
    have hc : Finset.univ.biUnion C ⊆ V₀ := by
      intro x hx
      obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
      exact (hC j).1 hxj
    rw [ν.mean_map]
    refine (?_ : _ ≤ (1 / 2 : ℝ) * μ.mean (fun s => (independenceOrder G
      (s ∩ Finset.univ.biUnion C) : ℝ))).trans (hPay _ hc)
    have h := hSample C (fun j => ⟨(hC j).1.trans hV', (hC j).2⟩) hDis
    change (1 / (20 * a)) * K ≤ _ at h
    rw [show (1 : ℝ) / (40 * a) * K = (1 / 2 : ℝ) * ((1 / (20 * a)) * K) by ring]
    exact mul_le_mul_of_nonneg_left h (by norm_num)

end LocallyRamsey
