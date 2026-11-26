module

public import LocallyRamsey.Lower.SupplyParameters
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

public section

open Filter

namespace LocallyRamsey

/-- The real threshold at the right side of equation (3). -/
@[expose] noncomputable def lowerScale (r : ℕ) : ℝ :=
  (r : ℝ) ^ (7 / 2 : ℝ) / (Real.log (r : ℝ)) ^ 24

/-- The integer test-set order used in the lower bound. -/
@[expose] noncomputable def lowerTestSize (r : ℕ) : ℕ := ⌊lowerScale r⌋₊

theorem target_tendsto_atTop : Tendsto target atTop atTop := by
  refine tendsto_atTop.mpr (fun a => ?_)
  have hLog : Tendsto (fun n : ℕ => Real.logb 2 (n : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hLog.eventually_ge_atTop (a : ℝ)] with n hn
  have h : (a : ℝ) ≤ (target n : ℝ) := hn.trans (Nat.le_ceil (Real.logb 2 (n : ℝ)))
  exact_mod_cast h

theorem target_log_relation {n : ℕ} (hn : 0 < n) :
    ((target n : ℝ) - 1) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hn')
  change (target n : ℝ) < Real.logb 2 (n : ℝ) + 1 at h
  rw [Real.logb] at h
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (le_div_iff₀ h₂).mp (by linarith)

private theorem testSize_bounds_of_log {r : ℕ}
    (hu₁ : 1 ≤ Real.log (r : ℝ))
    (hlogpow : (Real.log (r : ℝ)) ^ 24 ≤ (r : ℝ) ^ (5 / 2 : ℝ)) :
    r ≤ lowerTestSize r ∧ lowerTestSize r ≤ r ^ 6 := by
  have hu : 0 < Real.log (r : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hr : 1 ≤ (r : ℝ) := by
    by_contra! h
    exact (not_le_of_gt hu) (Real.log_nonpos hr0 h.le)
  constructor
  · apply Nat.le_floor
    dsimp [lowerScale]
    apply (le_div_iff₀ (by positivity : 0 < Real.log (r : ℝ) ^ 24)).mpr
    refine (mul_le_mul_of_nonneg_left hlogpow hr0).trans_eq ?_
    conv_lhs => lhs; rw [← Real.rpow_one (r : ℝ)]
    rw [← Real.rpow_add (by positivity : 0 < (r : ℝ)), show (1 : ℝ) + 5 / 2 = 7 / 2 by norm_num]
  · have hpow : (r : ℝ) ^ (7 / 2 : ℝ) ≤ (r : ℝ) ^ 6 := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
    apply Nat.floor_le_of_le
    push_cast
    exact (div_le_self (by positivity)
      (one_le_pow₀ hu₁)).trans hpow

/-- For large graph orders, the integer test size and the clique extraction
satisfy all the hypotheses of the supply lemma. -/
theorem lower_parameter_bounds :
    ∀ᶠ n : ℕ in atTop,
      let r := target n
      0 < n ∧ 100 ≤ r ∧ r ≤ lowerTestSize r ∧ lowerTestSize r ≤ r ^ 6 ∧
      8000 * Real.log (r : ℝ) ≤ r ∧ (r : ℝ) ^ 6 ≤ (n : ℝ) ^ (1 / 8 : ℝ) := by
  have hcast : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have hLog := (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  have hPow := (isLittleO_log_rpow_rpow_atTop 24 (by norm_num : (0 : ℝ) < 5 / 2)).eventuallyLE
  have hlin := (Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 8000))
  filter_upwards [eventually_gt_atTop (0 : ℕ), target_tendsto_atTop.eventually_ge_atTop 100,
    hLog, hcast.eventually hPow, hcast.eventually hlin] with n hn hr hu₁ hPowN hlinN
  let r := target n
  have hu : 0 < Real.log (r : ℝ) := by exact lt_of_lt_of_le (by norm_num) hu₁
  have hR : 100 ≤ (r : ℝ) := by exact_mod_cast hr
  have hlogpow : (Real.log (r : ℝ)) ^ 24 ≤ (r : ℝ) ^ (5 / 2 : ℝ) := by
    change ‖Real.log (r : ℝ) ^ (24 : ℝ)‖ ≤ ‖(r : ℝ) ^ (5 / 2 : ℝ)‖ at hPowN
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hu.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (r : ℝ)) _),
      show (24 : ℝ) = ((24 : ℕ) : ℝ) by rfl, Real.rpow_natCast] at hPowN
    exact hPowN
  have hul : 8000 * Real.log (r : ℝ) ≤ r := by
    change ‖Real.log (r : ℝ)‖ ≤ (1 / 8000 : ℝ) * ‖(r : ℝ)‖ at hlinN
    rw [Real.norm_of_nonneg hu.le, Real.norm_of_nonneg (by positivity)] at hlinN
    linarith
  refine ⟨hn, hr, (testSize_bounds_of_log hu₁ hlogpow).1, (testSize_bounds_of_log hu₁ hlogpow).2,
    hul, ?_⟩
  have hs := target_log_relation hn
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ (r : ℝ) - 1 by linarith)
  have hlogs : (6 : ℝ) * Real.log (r : ℝ) ≤ Real.log (n : ℝ) * (1 / 8 : ℝ) :=
    by nlinarith only [hh, hs, hul, hR]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : 0 < (r : ℝ)),
    Real.rpow_def_of_pos (by exact_mod_cast hn : 0 < (n : ℝ))]
  exact Real.exp_le_exp.mpr (by linarith only [hlogs])

/-- For the graph and test-set order in equation (3), every sufficiently
large vertex set contains a clique and an independent set of the order
needed to start the lower-bound construction. -/
theorem lower_clique_supply :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      IsLocallyRamsey G (lowerTestSize (target n)) (target n) →
      ∀ A : Finset (Fin n), (n : ℝ) ^ (1 / 60 : ℝ) ≤ A.card →
        (∃ K, K ∈ cliquesIn G A (largeCliqueOrder (target n))) ∧
        (∃ I, I ∈ cliquesIn Gᶜ A (largeCliqueOrder (target n))) := by
  filter_upwards [lower_parameter_bounds] with n hn
  obtain ⟨hn, hr, hrM, hM, hu, _⟩ := hn
  intro G hG A hA
  have hGc : IsLocallyRamsey Gᶜ (lowerTestSize (target n)) (target n) := by
    intro X hx
    obtain ⟨hk, hi⟩ := hG X hx
    exact ⟨hi, by simpa using hk⟩
  obtain ⟨K, hK, _⟩ := exists_large_clique hG hr hrM hM hn (target_log_relation hn) hu hA
  obtain ⟨I, hI, _⟩ := exists_large_clique hGc hr hrM hM hn (target_log_relation hn) hu hA
  exact ⟨⟨K, hK⟩, ⟨I, hI⟩⟩

/-- The low-degree assertion of the supply lemma at the sizes required
in the lower-bound construction. Apply this to the complement to bound
ordinary degrees. -/
theorem lower_degree_supply :
    ∀ᶠ n : ℕ in atTop, ∀ (G : SimpleGraph (Fin n)) [DecidableRel Gᶜ.Adj],
      IsLocallyRamsey G (lowerTestSize (target n)) (target n) →
      ∀ A : Finset (Fin n), (n : ℝ) ^ (1 / 8 : ℝ) ≤ A.card →
        ∃ X : Finset (Fin n), X ⊆ A ∧ (A.card : ℝ) / (target n : ℝ) ^ 50 ≤ X.card ∧
          ∀ x ∈ X, ((neighborsIn Gᶜ X x).card : ℝ) ≤
            (100 * Real.log (target n : ℝ) / target n) * X.card := by
  filter_upwards [lower_parameter_bounds] with n hn
  obtain ⟨_, hr, hrM, hM, hu, hpower⟩ := hn
  intro G inst hG A hA
  have hp : target n ^ 6 ≤ A.card := by exact_mod_cast hpower.trans hA
  have htwo : 2 * target n ≤ target n ^ 6 := by
    calc
      _ ≤ target n ^ 2 := by
        nlinarith only [Nat.mul_le_mul_right (target n) (show 2 ≤ target n by omega)]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  exact exists_large_low_degree_at_parameters G A hG hr hrM (hM.trans hp) (htwo.trans hp) hM hu

end LocallyRamsey
