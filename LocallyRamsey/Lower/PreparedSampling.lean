module

public import LocallyRamsey.Lower.InitialConstruction
public import LocallyRamsey.Lower.GoodIntersections
public import LocallyRamsey.Lower.StabilityScales

public section

open Filter
open scoped BigOperators Classical

namespace LocallyRamsey

/-- After restricting to a large set, all large subregions have comparable
intersection densities under the biased law. A full group is good with
probability at least 0.99. -/
theorem prepared_intersections :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      let r := target n
      let q := overlapGroupSize r
      let ε := 1 / (100000 * (q : ℝ))
      let τ := (r : ℝ)⁻¹ ^ 10
      IsLocallyRamsey G (lowerTestSize r) r →
      ∀ (V₀ : Finset (Fin n)) (μ : FiniteLaw (Finset (Fin n))) (p : ℝ),
        (n : ℝ) ^ (1 / 3 : ℝ) ≤ V₀.card →
        1 / (r : ℝ) ^ 3 ≤ p →
        (∀ x ∈ V₀, μ.event (fun S => x ∈ S) = p) →
        ∃ (W : Finset (Fin n)) (hW : W.Nonempty) (hp : 0 < p)
          (hu : ∀ x ∈ W, μ.event (fun S => x ∈ S) = p),
          let contains (S : Finset (Fin n)) x := x ∈ S
          let π := biasedLaw W hW μ contains p hp hu
          let L := sampleWeight W contains
          W ⊆ V₀ ∧ (n : ℝ) ^ (1 / 6 : ℝ) ≤ W.card ∧
          (∀ x ∈ W, ((W.filter (G.Adj x)).card : ℝ) ≤
            (100 * Real.log (r : ℝ) / r) * W.card) ∧
          (∀ (j : ℕ), j ≤ q → ∀ U T : Finset (Fin n), U ⊆ W → T ⊆ W →
            (r : ℝ)⁻¹ ^ 40 * (W.card : ℝ) ≤ U.card →
            (r : ℝ)⁻¹ ^ 40 * (W.card : ℝ) ≤ T.card →
            rootDistance (FiniteLaw.product (fun _ : Fin j => π))
              (intersectionDensity L U) (intersectionDensity L T) ≤ 2 * ε) ∧
          (FiniteLaw.product (fun _ : Fin q => π)).event (fun S =>
            intersectionDensity L W S < 1 / 2 ∨ 2 < intersectionDensity L W S ∨
            ∃ i, sampleDensity W contains (S i) < τ) ≤ 1 / 100 := by
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ), target_tendsto_atTop.eventually_ge_atTop 200000,
    (Real.tendsto_log_atTop.comp hrT).eventually_ge_atTop 10000, sampling_ratio_bounds,
    overlap_sampling_parameter_bounds, lower_degree_supply,
    eventually_target_pow_le_graph_rpow 50 (by norm_num : (0 : ℝ) < 1 / 12)]
    with n hn hr hu hratio hPar hSupply hn50
  intro G r q ε τ hG V₀ μ p hVsize hpMin hMarg
  let N : ℝ := n
  let R : ℝ := r
  let u := Real.log R
  let a := samplingRatio r
  have hn0 : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hn1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_of_lt hn
  have hr' : (200000 : ℝ) ≤ R := by dsimp [R, r]; exact_mod_cast hr
  have hr0 : 0 < R := by linarith
  have hr1 : 1 ≤ R := by linarith
  have hu0 : 0 < u := by change 10000 ≤ u at hu; linarith
  have hu1 : 1 ≤ u := by change 10000 ≤ u at hu; linarith
  have haP : 0 < a := zero_lt_one.trans_le hratio.1
  have hV₀ : V₀.Nonempty := Finset.card_pos.mp (by
    have h : (0 : ℝ) < V₀.card := (by positivity : 0 < N ^ (1 / 3 : ℝ)).trans_le hVsize
    exact_mod_cast h)
  have hp : 0 < p := (by positivity : 0 < 1 / R ^ 3).trans_le hpMin
  have hlog : R / 4 ≤ Real.log N := by
    have h1 := target_log_relation hn
    have h2 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9]) (show 0 ≤ R - 1 by linarith)
    change (R - 1) * Real.log 2 ≤ Real.log N at h1
    linarith only [h1, h2, hr']
  obtain ⟨_, _, hq2, _, _, _, _, _, _, _⟩ := hPar
  have hqP : 0 < q := by change 2 ≤ q at hq2; omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqP
  have hqSquare : (q : ℝ) ^ 2 ≤ 4 * R / u ^ 21 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ a * u ^ 12 by positivity)
    change (q : ℝ) < a * u ^ 12 + 1 at h
    have haU : 1 ≤ a * u ^ 12 := one_le_mul_of_one_le_of_one_le hratio.1 (one_le_pow₀ hu1)
    have hqHi : (q : ℝ) ≤ 2 * a * u ^ 12 := by linarith only [h, haU]
    have h2 := pow_le_pow_left₀ hq0.le hqHi 2
    have ha2 : a ^ 2 ≤ R / u ^ 45 := hratio.2
    have k := mul_le_mul_of_nonneg_right ha2 (show 0 ≤ 4 * u ^ 24 by positivity)
    rw [show R / u ^ 45 * (4 * u ^ 24) = 4 * R / u ^ 21 by field_simp] at k
    nlinarith only [h2, k]
  have hqR : (q : ℝ) ≤ R := by
    have huu : (4 : ℝ) ≤ u ^ 21 := by
      have h := pow_le_pow_right₀ hu1 (show 1 ≤ 21 by decide)
      simp only [pow_one] at h
      change 10000 ≤ u at hu
      linarith only [hu, h]
    have h : 4 * R / u ^ 21 ≤ R := by
      rw [div_le_iff₀ (by positivity : 0 < u ^ 21)]
      nlinarith only [mul_le_mul_of_nonneg_right huu hr0.le]
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqP
    nlinarith only [hqSquare.trans h, hq1, sq_nonneg ((q : ℝ) - 1)]
  let sc := stability_scales_of_bounds hr' hn0 hqP hqR hpMin hlog hu hqSquare
  let α := R⁻¹ ^ 100
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1)
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqP
    apply (div_le_one (by positivity : 0 < 100000 * (q : ℝ))).mpr
    linarith only [hq1]
  let contains (S : Finset (Fin n)) (x : Fin n) := x ∈ S
  let Rlaw (x : Fin n) := if hx : x ∈ V₀ then lawContaining μ (fun S => contains S x) hp (hMarg x hx) else μ
  obtain ⟨Z, hZV, hZ, hStable⟩ :=
    exists_stable_vertex_domain V₀ hV₀ μ contains hp hMarg hε0 hε1 hα0 hα1 q
      sc.repetitions sc.steps sc.stops
  have hZlarge : N ^ (1 / 4 : ℝ) ≤ Z.card := by
    have h := mul_le_mul sc.size_factor hVsize (by positivity : 0 ≤ N ^ (1 / 3 : ℝ))
      (by positivity : 0 ≤ (ε / 2 * α) ^ sc.steps)
    have he : N ^ (-1 / 12 : ℝ) * N ^ (1 / 3 : ℝ) = N ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hn0]
      norm_num
    rw [he] at h
    exact h.trans hZ
  have hG' : IsLocallyRamsey Gᶜ (lowerTestSize r) r := by
    intro A hA
    obtain ⟨hi, hc⟩ := hG A hA
    exact ⟨hc, by simpa using hi⟩
  have hZsmall : N ^ (1 / 8 : ℝ) ≤ Z.card :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)).trans hZlarge
  obtain ⟨W, hWZ, hWsize, hDeg⟩ := hSupply Gᶜ hG' Z hZsmall
  have hWlarge : N ^ (1 / 6 : ℝ) ≤ W.card := by
    calc
      _ = N ^ (1 / 4 : ℝ) / N ^ (1 / 12 : ℝ) := by
        rw [← Real.rpow_sub hn0]
        norm_num
      _ ≤ (Z.card : ℝ) / R ^ 50 := div_le_div_of_nonneg_left (by positivity)
        (by positivity) hn50 |>.trans (div_le_div_of_nonneg_right hZlarge (by positivity))
      _ ≤ _ := hWsize
  have hW : W.Nonempty := Finset.card_pos.mp (by
    have h : (0 : ℝ) < W.card := (by positivity : 0 < N ^ (1 / 6 : ℝ)).trans_le hWlarge
    exact_mod_cast h)
  have hWV : W ⊆ V₀ := hWZ.trans hZV
  have hm (x : Fin n) (hx : x ∈ W) : μ.event (fun S => contains S x) = p :=
    hMarg x (hWV hx)
  let π := biasedLaw W hW μ contains p hp hm
  let L := sampleWeight W contains
  have hZcomp : α * (Z.card : ℝ) ≤ R⁻¹ ^ 40 * (W.card : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hWsize (show 0 ≤ R⁻¹ ^ 40 by positivity)
    have hEq : R⁻¹ ^ 40 * ((Z.card : ℝ) / R ^ 50) = R⁻¹ ^ 90 * Z.card := by
      rw [inv_pow, inv_pow]
      field_simp
    rw [hEq] at h
    have hpow := pow_le_pow_of_le_one (by positivity : 0 ≤ R⁻¹) (inv_le_one_of_one_le₀ hr1)
      (show 90 ≤ 100 by decide)
    exact (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)).trans h
  have hCompare (j : ℕ) (hjq : j ≤ q) (U T : Finset (Fin n)) (hUW : U ⊆ W) (hTW : T ⊆ W)
      (hU : R⁻¹ ^ 40 * (W.card : ℝ) ≤ U.card) (hT : R⁻¹ ^ 40 * (W.card : ℝ) ≤ T.card) :
      rootDistance (FiniteLaw.product (fun _ : Fin j => π))
        (intersectionDensity L U) (intersectionDensity L T) ≤ 2 * ε := by
    have hW0 : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
    have hposSize : 0 < R⁻¹ ^ 40 * (W.card : ℝ) := by positivity
    have hUne := Finset.card_pos.mp (show 0 < U.card by exact_mod_cast hposSize.trans_le hU)
    have hTne := Finset.card_pos.mp (show 0 < T.card by exact_mod_cast hposSize.trans_le hT)
    have hAff := hStable U T (hUW.trans hWZ) (hTW.trans hWZ) (hZcomp.trans hU)
      (hZcomp.trans hT) hUne hTne
    exact rootDistance_intersections_of_affinity V₀ W U T hWV hUW hTW hW hUne hTne
      μ contains hp hMarg j (hAff.trans (affinity_vertex_product_mono Rlaw U T hUne hTne hjq))
  refine ⟨W, hW, hp, hm, hWV, hWlarge, ?_, hCompare, ?_⟩
  · intro x hx
    simpa only [neighborsIn, compl_compl] using hDeg x hx
  · have hqEq : q - 1 + 1 = q := Nat.sub_add_cancel hqP
    let k := q - 1
    have hClose (S : Finset (Fin n)) (hτ : τ ≤ sampleDensity W contains S) :
        rootDistance (FiniteLaw.product (fun _ : Fin k => π))
          (intersectionDensity L (W.filter (contains S))) (intersectionDensity L W) ≤ 2 * ε := by
      have hW0 : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
      have hρ : sampleDensity W contains S = ((W.filter (contains S)).card : ℝ) / W.card := by
        rw [sampleDensity, ← Finset.sum_filter]
        simp
      have hj : R⁻¹ ^ 40 ≤ τ := pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ hr1) (show (10 : ℕ) ≤ 40 by decide)
      refine hCompare k (Nat.sub_le _ _) _ W (Finset.filter_subset _ _) (Finset.Subset.refl _) ?_ ?_
      · rw [hρ] at hτ
        exact (mul_le_mul_of_nonneg_right hj hW0.le).trans ((le_div_iff₀ hW0).mp hτ)
      · exact mul_le_of_le_one_left hW0.le (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1))
    have hτ0 : 0 < τ := by change 0 < R⁻¹ ^ 10; positivity
    have h := event_bad_biased_group_le W hW μ contains hp hτ0 hε0.le hm k hClose
    dsimp only [k] at h
    rw [hqEq] at h
    refine h.trans ?_
    have hδ : τ / p ≤ 1 / R ^ 7 := by
      refine (div_le_div_of_nonneg_left hτ0.le (by positivity : 0 < 1 / R ^ 3) hpMin).trans_eq ?_
      change R⁻¹ ^ 10 / (1 / R ^ 3) = _
      rw [inv_pow]
      field_simp
    have hQδ : (q : ℝ) * (τ / p) ≤ 1 / R ^ 6 :=
      (mul_le_mul hqR hδ (by positivity) hr0.le).trans_eq (by field_simp)
    have hQE : (q : ℝ) * ε = 1 / 100000 := by dsimp [ε]; field_simp
    have hR6 : (200000 : ℝ) ≤ R ^ 6 := by
      have hR1 := pow_le_pow_right₀ hr1 (show (1 : ℕ) ≤ 6 by decide)
      rw [pow_one] at hR1
      exact hr'.trans hR1
    have h6 : 1 / R ^ 6 ≤ (1 : ℝ) / 200000 :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num) hR6
    nlinarith only [hQE, hQδ.trans h6]

end LocallyRamsey
