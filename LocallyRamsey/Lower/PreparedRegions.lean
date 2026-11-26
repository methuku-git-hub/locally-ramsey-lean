module

public import LocallyRamsey.Lower.PreparedRetention
public import LocallyRamsey.Lower.RetentionEvents
public import LocallyRamsey.Lower.PreparedSampling

public section

open Filter
open scoped BigOperators Classical

namespace LocallyRamsey

/-- Once a sufficiently large region has been fixed, the capped
retention rule supplies all pointwise and mean estimates for the
conditional group tests. -/
theorem prepared_region_tests :
    ∀ᶠ n : ℕ in atTop,
      let r := target n
      let R : ℝ := r
      let D := overlapDegree r
      let γ := overlapQuota r
      let q := overlapGroupSize r
      let ε := 1 / (100000 * (q : ℝ))
      let ρ := R⁻¹ ^ 10
      ∀ (G : SimpleGraph (Fin n)) (W B : Finset (Fin n)) (hW : W.Nonempty) (hBW : B ⊆ W)
        (μ : FiniteLaw (Finset (Fin n))) (p : ℝ) (hp : 0 < p)
        (hu : ∀ x ∈ W, μ.event (fun S => x ∈ S) = p)
        (ν : Finset (Fin n) → FiniteLaw (Finset (Fin n))),
        let contains (S : Finset (Fin n)) x := x ∈ S
        let π := biasedLaw W hW μ contains p hp hu
        let L := sampleWeight W contains
        let l (s : Finset (Fin n) × Finset (Fin n)) := L s.1
        let c (s : Finset (Fin n) × Finset (Fin n)) := (sampleDensity W contains s.1)⁻¹
        let good (w : Fin q → Finset (Fin n) × Finset (Fin n)) :=
          goodPositionGroup W contains ρ (Prod.fst ∘ w)
        let kept (w : Fin q → Finset (Fin n) × Finset (Fin n)) :=
          good w ∧ intersectionDensity l B w ≤ 8
        (n : ℝ) ^ (1 / 7 : ℝ) ≤ B.card → (W.card : ℝ) / R ^ 2 ≤ B.card →
        (∀ j ≤ q, ∀ U T : Finset (Fin n), U ⊆ W → T ⊆ W →
          R⁻¹ ^ 40 * (W.card : ℝ) ≤ U.card → R⁻¹ ^ 40 * (W.card : ℝ) ≤ T.card →
          rootDistance (FiniteLaw.product (fun _ : Fin j => π))
            (intersectionDensity L U) (intersectionDensity L T) ≤ 2 * ε) →
        (∀ S F, 0 < (ν S).prob F → F ⊆ B ∧ F ⊆ S ∧
          ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) ≤ (F.card + R⁻¹ ^ 3 * (S ∩ B).card) / D) →
        (∀ x ∈ B, (μ.staged ν).event (fun z => x ∈ z.2) ≤ γ * p) →
        (B.filter (fun x => (μ.staged ν).event (fun z => x ∈ z.2) < γ * p)).card ≤
          ⌊(B.card : ℝ) * R⁻¹ ^ 4⌋₊ →
        ∃ F : Finset (Fin n) × Finset (Fin n) → Finset (Fin n),
          (∀ s, F s ⊆ B ∧ F s ⊆ s.1) ∧
          (∀ s, (F s).card * c s / B.card ∈ Set.Icc (0 : ℝ) 2) ∧
          (π.staged ν).mean (fun s => (F s).card * c s / B.card) ≤ γ ∧
          (∀ s x, x ∈ F s → mass (fun _ => c s / B.card) (neighborsIn G (F s) x) ≤
            ((F s).card * c s / B.card + γ) / D) ∧
          (∀ w i, good w → c (w i) / B.card ≤ γ / D) ∧
          ((FiniteLaw.product (fun _ : Fin q => π.staged ν)).event
            (fun ω => good ω ∧ 8 < intersectionDensity l B ω) ≤ γ / 4) ∧
          (∀ ω, poorlyRetainedMass B l F c γ kept ω ∈ Set.Icc (0 : ℝ) 8) ∧
          (FiniteLaw.product (fun _ : Fin q => π.staged ν)).mean
            (poorlyRetainedMass B l F c γ kept) ≤ γ / 32 := by
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  filter_upwards [hrT.eventually_ge_atTop 200000, (Real.tendsto_log_atTop.comp hrT).eventually_ge_atTop 10000,
    overlap_sampling_parameter_bounds, eventually_target_pow_le_graph_rpow 11
    (by norm_num : (0 : ℝ) < 1 / 7)] with n hr hu hPar h11
  intro r R D γ q ε ρ G W B hW hBW μ p hp hu' ν contains π L l c good kept hB hBWsize hClose hν hMarg hException
  let u := Real.log R
  let δ := R⁻¹ ^ 40 * (W.card : ℝ)
  have hR0 : 0 < R := by change (200000 : ℝ) ≤ R at hr; linarith
  have hR1 : 1 ≤ R := by linarith
  have hri : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
  have hu1 : 1 ≤ u := by change 10000 ≤ u at hu; linarith
  obtain ⟨hD, hγ, hq, _, _, _, hqγ, _, hDγ, _⟩ := hPar
  change 2 ≤ q at hq
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hδ : 0 < δ := by dsimp [δ]; exact mul_pos (by positivity) (by exact_mod_cast hW.card_pos)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hBW0 : 0 < (B.card : ℝ) := (by positivity : 0 < (W.card : ℝ) / R ^ 2).trans_le hBWsize
  have hγR : R⁻¹ ≤ γ := by
    have hk := (div_le_iff₀ hγ).mp hDγ
    rw [inv_eq_one_div, div_le_iff₀ hR0]
    nlinarith only [hD, hk]
  have hεγ : 100000 * ε ≤ γ := by
    have hf : (q : ℝ)⁻¹ ≤ γ := by
      rw [inv_eq_one_div, div_le_iff₀ (by positivity : 0 < (q : ℝ))]
      exact (one_le_pow₀ hu1).trans (by simpa only [mul_comm] using hqγ)
    change 100000 * (1 / (100000 * (q : ℝ))) ≤ γ
    rw [show 100000 * (1 / (100000 * (q : ℝ))) = (q : ℝ)⁻¹ by field_simp]
    exact hf
  have hδW : δ ≤ ρ * W.card := by
    dsimp [δ, ρ]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by positivity) hri (by decide)) (Nat.cast_nonneg _)
  have hδB : δ / B.card ≤ R⁻¹ ^ 38 := by
    rw [div_le_iff₀ hBW0]
    calc
      δ = R⁻¹ ^ 38 * ((W.card : ℝ) / R ^ 2) := by dsimp [δ]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hBWsize (by positivity)
  have hδB' : δ ≤ B.card := (div_le_one hBW0).mp
    (hδB.trans (pow_le_one₀ (by positivity) hri))
  have hsmall : δ / (ρ * B.card) ≤ R⁻¹ ^ 28 := by
    rw [mul_comm ρ, ← div_div, div_le_iff₀ hρ]
    refine hδB.trans_eq ?_
    dsimp [ρ]
    rw [← pow_add]
  have hθ : 2 * R⁻¹ ^ 3 ≤ γ := by
    refine le_trans ?_ hγR
    have h1 : 2 ≤ R ^ 2 := by nlinarith only [hr, sq_nonneg (R - 200000)]
    rw [inv_pow, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) hR0]
    nlinarith only [mul_le_mul_of_nonneg_right h1 hR0.le]
  let initial := R⁻¹ ^ 4 + δ / B.card + Real.exp (-(γ * q) / 16)
  have hRinv : R⁻¹ ≤ 1 / 10000 := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hfirst : R⁻¹ ^ 4 ≤ γ / 10000 := by
    calc
      _ ≤ R⁻¹ * R⁻¹ := by simpa [pow_two] using
        (pow_le_pow_of_le_one (by positivity : 0 ≤ R⁻¹) hri (show 2 ≤ 4 by decide))
      _ ≤ _ := by simpa [div_eq_mul_inv, mul_comm] using
        mul_le_mul hRinv hγR (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 10000)
  have hsecond : δ / B.card ≤ γ / 10000 := hδB.trans <|
    (pow_le_pow_of_le_one (by positivity) hri (show 4 ≤ 38 by decide)).trans hfirst
  have hthird : Real.exp (-(γ * q) / 16) ≤ γ / 10000 := by
    have hx : 32 * u ≤ u ^ 4 := by
      have : (32 : ℝ) ≤ u ^ 3 := (by change (10000 : ℝ) ≤ u at hu; linarith : 32 ≤ u).trans
        (by simpa using pow_le_pow_right₀ hu1 (show 1 ≤ 3 by decide))
      nlinarith only [mul_le_mul_of_nonneg_right this (show 0 ≤ u by linarith)]
    have hExp : Real.exp (-(γ * q) / 16) ≤ Real.exp (-2 * u) :=
      Real.exp_le_exp.mpr (by nlinarith only [hqγ, hx])
    rw [show -2 * u = -((2 : ℕ) * u) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, show Real.exp u = R from Real.exp_log hR0,
      ← inv_pow] at hExp
    have hprod := mul_le_mul hRinv hγR (by positivity : 0 ≤ R⁻¹)
      (by norm_num : (0 : ℝ) ≤ 1 / 10000)
    exact hExp.trans (by simpa only [pow_two, div_eq_mul_inv, one_div, one_mul, mul_comm] using hprod)
  have hTiny : 8 * R⁻¹ ^ 28 / γ ≤ γ / 10000 := by
    rw [div_le_iff₀ hγ]
    have hη : 8 * R⁻¹ ≤ 1 / 1000 := by linarith only [hRinv]
    have hinv2 : 8 * R⁻¹ ^ 2 ≤ 1 / 10000 := by
      nlinarith only [mul_le_mul hη hRinv (by positivity : 0 ≤ R⁻¹) (by norm_num : (0 : ℝ) ≤ 1 / 1000)]
    have he : R⁻¹ ^ 28 ≤ R⁻¹ ^ 4 :=
      pow_le_pow_of_le_one (by positivity) hri (show 4 ≤ 28 by decide)
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ R⁻¹) hγR 2
    nlinarith only [he, mul_le_mul hinv2 hsq (by positivity : 0 ≤ R⁻¹ ^ 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 10000)]
  have hBudget : initial + (8 * R⁻¹ ^ 28 / γ + 64 * ε) ≤ γ / 32 := by
    dsimp [initial]
    linarith only [hfirst, hsecond, hthird, hTiny, hεγ, hε, hγ]
  have hExc : ((B.filter (fun x => (μ.staged ν).event (fun z => x ∈ z.2) < γ * p)).card : ℝ) ≤
      R⁻¹ ^ 4 * B.card := by
    have hh : ((B.filter (fun x => (μ.staged ν).event (fun z => x ∈ z.2) < γ * p)).card : ℝ) ≤
        (⌊(B.card : ℝ) * R⁻¹ ^ 4⌋₊ : ℝ) := by exact_mod_cast hException
    have hFloor := Nat.floor_le (show 0 ≤ (B.card : ℝ) * R⁻¹ ^ 4 by positivity)
    exact hh.trans (by simpa only [mul_comm] using hFloor)
  obtain ⟨F, hF, hz, hm, hdeg, hi⟩ := prepared_position_retention G W B hW hBW μ hp hγ.le
    hδ hδB' (zero_lt_one.trans hD) (by positivity : 0 ≤ R⁻¹ ^ 3) hθ
    (show 36 * ε ≤ γ / 2 by linarith only [hεγ, hε, hγ]) hu' ν hν hMarg
    (bound := R⁻¹ ^ 4) hExc
    (fun A hA ha => hClose 1 (by omega) A W (hA.trans hBW) (by rfl) ha
      (hδB'.trans (by exact_mod_cast Finset.card_le_card hBW))) q
  have hAtom (ω : Fin q → Finset (Fin n) × Finset (Fin n)) (i : Fin q)
      (hg : good ω) : c (ω i) / B.card ≤ γ / D := by
    have hs : ρ ≤ sampleDensity W contains (ω i).1 := hg.2.2 i
    have hci : c (ω i) ≤ R ^ 10 := by
      calc
        _ ≤ ρ⁻¹ := inv_anti₀ hρ hs
        _ = _ := by simp [ρ, inv_pow]
    have hb : R ^ 11 ≤ (B.card : ℝ) := h11.trans hB
    have hd : R⁻¹ ≤ γ / D := by
      rw [inv_eq_one_div, div_le_div_iff₀ hR0 (zero_lt_one.trans hD), one_mul]
      simpa only [mul_comm] using (div_le_iff₀ hγ).mp hDγ
    apply le_trans _ hd
    rw [inv_eq_one_div, div_le_div_iff₀ hBW0 hR0, one_mul]
    exact (mul_le_mul_of_nonneg_right hci hR0.le).trans (by simpa only [pow_succ] using hb)
  refine ⟨F, hF, hz, hm, hdeg, hAtom, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  dsimp only [good, kept]
  rw [hk] at hClose ⊢
  exact prepared_group_retention W B hW hBW π ν F hF hρ hγ hε hδ hδB' hδW hsmall
    (by linarith only [hεγ, hε, hγ]) hBudget
    (fun x hx => biasedLaw_mean_weight W hW μ contains p hp hu' hx) hClose hm (by
      have hcq : (k : ℝ) + 1 = q := by exact_mod_cast hk.symm
      rw [← hk, hcq]
      exact hi)

end LocallyRamsey
