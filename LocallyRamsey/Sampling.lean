module

public import LocallyRamsey.FiniteProbability

public section

namespace LocallyRamsey

open scoped BigOperators

variable {V Ω : Type*}

/-- The density of a sample in the fixed vertex set. -/
@[expose] noncomputable def sampleDensity (W : Finset V) (contains : Ω → V → Prop)
    [∀ ω, DecidablePred (contains ω)] (ω : Ω) : ℝ :=
  (∑ x ∈ W, if contains ω x then (1 : ℝ) else 0) / W.card

/-- The factor attached to a vertex in a sample intersection. -/
@[expose] noncomputable def sampleWeight (W : Finset V) (contains : Ω → V → Prop)
    [∀ ω, DecidablePred (contains ω)] (ω : Ω) (x : V) : ℝ :=
  (if contains ω x then 1 else 0) / sampleDensity W contains ω

theorem sampleDensity_nonneg (W : Finset V) (contains : Ω → V → Prop)
    [∀ ω, DecidablePred (contains ω)] (ω : Ω) : 0 ≤ sampleDensity W contains ω := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun x _ => by split <;> positivity

theorem sampleDensity_pos {W : Finset V} {contains : Ω → V → Prop}
    [∀ ω, DecidablePred (contains ω)] {ω : Ω} {x : V}
    (hx : x ∈ W) (h : contains ω x) : 0 < sampleDensity W contains ω := by
  have hsum : 1 ≤ ∑ z ∈ W, if contains ω z then (1 : ℝ) else 0 := by
    have hsingle := Finset.single_le_sum (f := fun z => if contains ω z then (1 : ℝ) else 0)
      (fun z _ => by split <;> positivity) hx
    simpa [h] using hsingle
  exact div_pos (by linarith) (by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩)

variable [Fintype Ω]

theorem mean_sampleDensity (W : Finset V) (hW : W.Nonempty) (μ : FiniteLaw Ω)
    (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    (p : ℝ) (hp : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p) :
    μ.mean (sampleDensity W contains) = p := by
  classical
  have hcard : (W.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hW).ne'
  calc
    _ = (W.card : ℝ)⁻¹ * ∑ x ∈ W, μ.event (fun ω => contains ω x) := by
      have hd : sampleDensity W contains =
          fun ω => (W.card : ℝ)⁻¹ * ∑ x ∈ W, if contains ω x then (1 : ℝ) else 0 := by
        funext ω
        simp only [sampleDensity, div_eq_inv_mul]
      rw [hd, μ.mean_mul_const, μ.mean_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      exact μ.mean_indicator _
    _ = p := by
      rw [Finset.sum_congr rfl hp]
      simp [hcard]

/-- Size-biasing the original law by the sample density in `W`. -/
@[expose] noncomputable def biasedLaw (W : Finset V) (hW : W.Nonempty) (μ : FiniteLaw Ω)
    (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    (p : ℝ) (hp : 0 < p) (huniform : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p) :
    FiniteLaw Ω where
  prob ω := μ.prob ω * sampleDensity W contains ω / p
  nonneg ω := div_nonneg (mul_nonneg (μ.nonneg ω) (sampleDensity_nonneg W contains ω)) hp.le
  total := by
    rw [← Finset.sum_div]
    change μ.mean (sampleDensity W contains) / p = 1
    rw [mean_sampleDensity W hW μ contains p huniform, div_self hp.ne']

/-- The fundamental identity in Section 4.4. Under the biased law,
the normalized factor at each fixed vertex in `W` has expectation one. -/
theorem biasedLaw_mean_weight (W : Finset V) (hW : W.Nonempty) (μ : FiniteLaw Ω)
    (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    (p : ℝ) (hp : 0 < p) (huniform : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p)
    {x : V} (hx : x ∈ W) :
    (biasedLaw W hW μ contains p hp huniform).mean (fun ω => sampleWeight W contains ω x) = 1 := by
  classical
  have hid (ω : Ω) : (biasedLaw W hW μ contains p hp huniform).prob ω *
      sampleWeight W contains ω x = p⁻¹ * (μ.prob ω * if contains ω x then 1 else 0) := by
    change μ.prob ω * sampleDensity W contains ω / p *
      ((if contains ω x then 1 else 0) / sampleDensity W contains ω) = _
    by_cases h : contains ω x
    · simp only [ite_eq_left h, mul_one]
      field_simp [(sampleDensity_pos hx h).ne', hp.ne']
    · simp [h]
  calc
    _ = p⁻¹ * μ.mean (fun ω => if contains ω x then 1 else 0) := by
      simp only [FiniteLaw.mean, hid, Finset.mul_sum]
    _ = 1 := by rw [μ.mean_indicator, huniform x hx, inv_mul_cancel₀ hp.ne']

end LocallyRamsey
