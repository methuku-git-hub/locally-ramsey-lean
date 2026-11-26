module

public import LocallyRamsey.FiniteProbability
public import Mathlib.Analysis.Real.Sqrt

public section

namespace LocallyRamsey

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- Squared distance between square roots of the densities of two finite
laws. This quantity equals twice one minus their affinity. -/
@[expose] noncomputable def rootDistance (μ : FiniteLaw Ω) (a b : Ω → ℝ) : ℝ :=
  μ.mean (fun ω => (Real.sqrt (a ω) - Real.sqrt (b ω)) ^ 2)

/-- The probability law with the specified nonnegative density. -/
@[expose] def FiniteLaw.withDensity (μ : FiniteLaw Ω) (a : Ω → ℝ)
    (ha : ∀ ω, 0 ≤ a ω) (hsum : μ.mean a = 1) : FiniteLaw Ω where
  prob ω := μ.prob ω * a ω
  nonneg ω := mul_nonneg (μ.nonneg ω) (ha ω)
  total := hsum

/-- The first comparison in Lemma 13. The event that the density of one
law exceeds four times that of the other has small probability under
the first law. -/
theorem event_density_gt_four_le (μ : FiniteLaw Ω) (a b : Ω → ℝ)
    (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω) (hsum : μ.mean a = 1) :
    (μ.withDensity a ha hsum).event (fun ω => 4 * b ω < a ω) ≤
      4 * rootDistance μ a b := by
  classical
  let P := fun ω => 4 * b ω < a ω
  have hpoint (ω : Ω) :
      a ω * (if P ω then (1 : ℝ) else 0) ≤
        4 * (Real.sqrt (a ω) - Real.sqrt (b ω)) ^ 2 := by
    by_cases h : P ω
    · have h' : 4 * b ω < a ω := h
      have hs₁ := Real.sqrt_nonneg (a ω)
      have hs₂ := Real.sqrt_nonneg (b ω)
      have ha_sq := Real.sq_sqrt (ha ω)
      have hb_sq := Real.sq_sqrt (hb ω)
      have hsep : 2 * Real.sqrt (b ω) ≤ Real.sqrt (a ω) := by
        by_contra! hh
        have hp := mul_pos (sub_pos.mpr hh)
          (show 0 < 2 * Real.sqrt (b ω) + Real.sqrt (a ω) by linarith)
        nlinarith only [hp, h', ha_sq, hb_sq]
      have hsq := mul_nonneg (show 0 ≤ Real.sqrt (a ω) - 2 * Real.sqrt (b ω) by linarith)
        (show 0 ≤ 3 * Real.sqrt (a ω) - 2 * Real.sqrt (b ω) by linarith)
      simp only [ite_eq_left h, mul_one]
      nlinarith only [hsq, ha_sq]
    · rw [ite_eq_right h, mul_zero]
      positivity
  have hle := μ.mean_mono hpoint
  rw [μ.mean_mul_const] at hle
  change (μ.withDensity a ha hsum).event P ≤ 4 * rootDistance μ a b
  rw [← FiniteLaw.mean_indicator _ P]
  simpa only [FiniteLaw.mean, FiniteLaw.withDensity, mul_assoc, rootDistance] using hle

/-- The second comparison in Lemma 13. The additive error controls the
probability of any event under the first law using its probability under
the second law. -/
theorem event_le_two_add_distance (μ : FiniteLaw Ω) (a b : Ω → ℝ)
    (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω) (hsa : μ.mean a = 1)
    (hsb : μ.mean b = 1) (P : Ω → Prop) :
    (μ.withDensity a ha hsa).event P ≤
      2 * (μ.withDensity b hb hsb).event P + 2 * rootDistance μ a b := by
  classical
  let indicator := fun ω => if P ω then (1 : ℝ) else 0
  have hpoint (ω : Ω) : a ω * indicator ω ≤
      2 * (b ω * indicator ω) + 2 * (Real.sqrt (a ω) - Real.sqrt (b ω)) ^ 2 := by
    by_cases h : P ω
    · simp [indicator, h]
      nlinarith only [Real.sq_sqrt (ha ω), Real.sq_sqrt (hb ω),
        sq_nonneg (Real.sqrt (a ω) - 2 * Real.sqrt (b ω))]
    · simp [indicator, h]
      positivity
  have h := μ.mean_mono hpoint
  rw [μ.mean_add, μ.mean_mul_const, μ.mean_mul_const] at h
  rw [← FiniteLaw.mean_indicator _ P, ← FiniteLaw.mean_indicator _ P]
  simpa only [FiniteLaw.mean, FiniteLaw.withDensity, rootDistance, mul_assoc, indicator] using h

end LocallyRamsey
