module

public import LocallyRamsey.Lower.SamplingParameters
public import LocallyRamsey.Overlap

public section

open Filter

namespace LocallyRamsey

/-- Every fixed power of the target order is eventually smaller than
every fixed positive power of the graph order. -/
theorem eventually_target_pow_le_graph_rpow (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, (target n : ℝ) ^ k ≤ (n : ℝ) ^ t := by
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have hSmall := Real.isLittleO_log_id_atTop.bound (show 0 < t / (4 * (k + 1)) by positivity)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hrT.eventually_ge_atTop 2, hrT.eventually hSmall]
    with n hn hr hsmall
  let r := target n
  have hrpos : (0 : ℝ) < r := by change (2 : ℝ) ≤ r at hr; linarith
  have hu : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by change (2 : ℝ) ≤ r at hr; linarith)
  have huSmall : Real.log (r : ℝ) ≤ t / (4 * (k + 1)) * r := by
    change ‖Real.log (r : ℝ)‖ ≤ t / (4 * (k + 1)) * ‖id (r : ℝ)‖ at hsmall
    simpa only [id_eq, Real.norm_of_nonneg hu, Real.norm_of_nonneg hrpos.le] using hsmall
  have hk : (k : ℝ) * Real.log r ≤ t * r / 4 := by
    have h := mul_le_mul_of_nonneg_left huSmall (show 0 ≤ (k : ℝ) + 1 by positivity)
    have hh : ((k : ℝ) + 1) * (t / (4 * (k + 1)) * r) = t * r / 4 := by
      have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    rw [hh] at h
    linarith only [h, hu]
  have hnLog : (r : ℝ) / 4 ≤ Real.log (n : ℝ) := by
    have h1 := target_log_relation hn
    have h2 := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9]) (show 0 ≤ (r : ℝ) - 1 by
        change (2 : ℝ) ≤ r at hr
        linarith)
    change (2 : ℝ) ≤ r at hr
    linarith only [h1, h2, hr]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos hrpos, Real.rpow_def_of_pos (by exact_mod_cast hn)]
  apply Real.exp_le_exp.mpr
  rw [mul_comm (Real.log (r : ℝ)), mul_comm (Real.log (n : ℝ))]
  exact hk.trans (by linarith only [mul_le_mul_of_nonneg_left hnLog ht.le])

/-- A bound on the enlargement ratio and the number of draws provides
the lower scale needed for the final overlap comparison. -/
theorem overlap_mass_scale_le {r a u b N p₀ : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hu : 0 < u) (hb : 0 < b) (hN : 0 < N) (hp : 0 < p₀)
    (hB : b ≤ r ^ 2 / u) (hDraw : N ≤ 5 * r * a) (hRegion : p₀ ≤ 2 * u ^ 6 / r ^ 2) :
    1 / (1000 * a * u ^ 5) ≤ r / (100 * b * N * p₀) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc
    _ ≤ 100 * (r ^ 2 / u) * (5 * r * a) * (2 * u ^ 6 / r ^ 2) := by gcongr
    _ = _ := by field_simp; ring

/-- The final numerical comparison follows when the lower mass scale is
at least a fixed constant times the inverse of (a u^5). -/
theorem eventually_overlap_gap {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop, let r := target n
      let u := Real.log (r : ℝ)
      let γ := overlapQuota r
      let D := overlapDegree r
      ∀ g : ℝ, 1 / (1000 * samplingRatio r * u ^ 5) ≤ g →
        0 < g ∧ 4 / (D * γ) + 3 * A * γ / g < 1 / 9 := by
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  filter_upwards [sampling_ratio_bounds,
    (Real.tendsto_log_atTop.comp hrT).eventually_ge_atTop (2 + 9 * (4 + 3000 * A))] with n hratio hu
  let r := target n
  let u := Real.log (r : ℝ)
  let a := samplingRatio r
  let γ := overlapQuota r
  let D := overlapDegree r
  change 2 + 9 * (4 + 3000 * A) ≤ u at hu
  have ha : 0 < a := zero_lt_one.trans_le hratio.1
  have hu₁ : 1 ≤ u := by linarith only [hu, hA]
  have hu0 : 0 < u := zero_lt_one.trans_le hu₁
  change ∀ g : ℝ, 1 / (1000 * a * u ^ 5) ≤ g →
    0 < g ∧ 4 / (D * γ) + 3 * A * γ / g < 1 / 9
  intro g hg
  let g₀ := 1 / (1000 * a * u ^ 5)
  have hg₀ : 0 < g₀ := by dsimp [g₀]; positivity
  have hgpos : 0 < g := hg₀.trans_le hg
  have hγ : 0 < γ := by dsimp [γ, overlapQuota, a, u]; positivity
  have hγD : D * γ = u ^ 10 := by
    change (a * u ^ 18) * (1 / (a * u ^ 8)) = _
    field_simp
  have hγg : 3 * A * γ / g₀ = 3000 * A / u ^ 3 := by
    change 3 * A * (1 / (a * u ^ 8)) / (1 / (1000 * a * u ^ 5)) = _
    field_simp
    ring
  refine ⟨hgpos, ?_⟩
  rw [hγD]
  calc
    _ ≤ 4 / u ^ 10 + 3 * A * γ / g₀ :=
      add_le_add_right (div_le_div_of_nonneg_left (by positivity) hg₀ hg) _
    _ ≤ (4 + 3000 * A) / u := by
      rw [hγg, add_div]
      apply add_le_add
      · exact div_le_div_of_nonneg_left (by norm_num) hu0
          (by simpa only [pow_one] using pow_le_pow_right₀ hu₁ (show (1 : ℕ) ≤ 10 by decide))
      · exact div_le_div_of_nonneg_left (by positivity) hu0
          (by simpa only [pow_one] using pow_le_pow_right₀ hu₁ (show (1 : ℕ) ≤ 3 by decide))
    _ < _ := (div_lt_iff₀ hu0).mpr (by linarith only [hu])

end LocallyRamsey
