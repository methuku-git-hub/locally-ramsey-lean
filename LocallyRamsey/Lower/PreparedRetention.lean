module

public import LocallyRamsey.Lower.InitialConstruction
public import LocallyRamsey.Lower.PositionRetention
public import LocallyRamsey.Lower.RetentionScales

public section

open Filter
open scoped BigOperators Classical

namespace LocallyRamsey

/-- On every region of the required size, the balanced sampling rule has
a retention rule with the degree bound and the desired common marginal,
apart from the allowed exceptional vertices. -/
theorem prepared_capped_retention :
    ∀ᶠ n : ℕ in atTop,
      let r := target n
      let R : ℝ := r
      let a := samplingRatio r
      let b := largeCliqueOrder r
      let u := Real.log R
      let limit := ⌈(n : ℝ) ^ (1 / 40 : ℝ)⌉₊
      let γ := overlapQuota r
      let D := overlapDegree r
      ∀ (G : SimpleGraph (Fin n)) (V₀ : Finset (Fin n)) (family : Finset (Fin n) → Prop)
        (μ : FiniteLaw (Finset (Fin n))) (K : ℕ) (p : ℝ),
        R / (2 * u ^ 10) ≤ (K : ℝ) → (K : ℝ) ≤ R / u ^ 10 →
        0 < p → p ≤ 16 * u ^ 6 / R ^ 2 →
        (∀ A : Finset (Fin n), A ⊆ V₀ → limit ≤ A.card →
          ∃ C : Finset (Fin n), C ⊆ A ∧ C.card = b ∧ family C) →
        (∀ C, family C → G.IsClique (C : Set (Fin n))) →
        (∀ C : Fin K → Finset (Fin n), (∀ j, C j ⊆ V₀ ∧ (C j).card = b ∧ family (C j)) →
          (Pairwise fun i j => Disjoint (C i) (C j)) →
          (1 / (40 * a)) * K ≤ μ.mean (fun S =>
            (independenceOrder G (S ∩ Finset.univ.biUnion C) : ℝ))) →
        ∀ B : Finset (Fin n), B ⊆ V₀ → (n : ℝ) ^ (1 / 7 : ℝ) ≤ B.card →
        ∃ ν : Finset (Fin n) → FiniteLaw (Finset (Fin n)),
          (∀ S F, 0 < (ν S).prob F → F ⊆ B ∧ F ⊆ S ∧
            ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) ≤
              (F.card + R⁻¹ ^ 3 * (S ∩ B).card) / D) ∧
          (∀ x ∈ B, (μ.staged ν).event (fun z => x ∈ z.2) ≤ γ * p) ∧
          (B.filter (fun x => (μ.staged ν).event (fun z => x ∈ z.2) < γ * p)).card ≤
            ⌊(B.card : ℝ) * R⁻¹ ^ 4⌋₊ := by
  have hN : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hrT : Tendsto (fun n : ℕ => (target n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp target_tendsto_atTop
  have hLog := (isLittleO_log_rpow_rpow_atTop 12 (by norm_num : (0 : ℝ) < 1 / 2)).eventuallyLE
  have h12 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 7 - 1 / 20 - 1 / 40)).comp hN
  filter_upwards [eventually_gt_atTop (0 : ℕ), target_tendsto_atTop.eventually_ge_atTop 200000,
    (Real.tendsto_log_atTop.comp hrT).eventually_ge_atTop 10000, sampling_ratio_bounds,
    overlap_sampling_parameter_bounds, hrT.eventually hLog,
    eventually_target_pow_le_graph_rpow 13 (by norm_num : (0 : ℝ) < 1 / 7),
    eventually_target_pow_le_graph_rpow 4 (by norm_num : (0 : ℝ) < 1 / 20),
    h12.eventually_ge_atTop 4] with n hn hr hu hratio hOverlap hPow h13 h4 hN12
  intro r R a b u limit γ D G V₀ family μ K p hKlo hKhi hp hpHi hSupply hClique hSample B hBV hB
  let N : ℝ := n
  have hn0 : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hn1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.one_le_of_lt hn
  have hr' : (200000 : ℝ) ≤ R := by dsimp [R, r]; exact_mod_cast hr
  have hr0 : 0 < R := by linarith
  have hu0 : 0 < u := by change 10000 ≤ u at hu; linarith
  have ha0 : 0 < a := zero_lt_one.trans_le hratio.1
  have hb : 0 < b := by
    by_contra! hb
    have hz : b = 0 := by omega
    have h' : (1 : ℝ) ≤ (lowerTestSize r : ℝ) / (R * (b : ℝ)) := hratio.1
    exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (by simpa only [hz, Nat.cast_zero, mul_zero, div_zero] using h')
  have hBu : (b : ℝ) ≤ R ^ 2 / (24000 * u) := Nat.floor_le (by positivity)
  have hK : 0 < K := by
    exact_mod_cast (show (0 : ℝ) < K from (by positivity : 0 < R / (2 * u ^ 10)).trans_le hKlo)
  have hPow' : u ^ 12 ≤ Real.sqrt R := by
    change ‖u ^ (12 : ℝ)‖ ≤ ‖R ^ (1 / 2 : ℝ)‖ at hPow
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _), Real.norm_of_nonneg (Real.rpow_nonneg hr0.le _),
      show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hPow
    rwa [Real.sqrt_eq_rpow]
  let sc := retention_scales_of_bounds hr' hu hratio.1 hratio.2 hPow' hKlo hKhi hb hBu hp hpHi (h13.trans hB)
  have hSc : 2 * (limit : ℝ) ≤ (B.card : ℝ) * R⁻¹ ^ 4 := by
    have hT : N ^ (1 / 7 - 1 / 20 : ℝ) ≤ (B.card : ℝ) * R⁻¹ ^ 4 := by
      rw [Real.rpow_sub hn0, inv_pow, ← div_eq_mul_inv]
      exact (div_le_div_of_nonneg_left (by positivity : 0 ≤ N ^ (1 / 7 : ℝ))
        (by positivity : 0 < R ^ 4) h4).trans (div_le_div_of_nonneg_right hB (by positivity))
    have hL : (limit : ℝ) ≤ 2 * N ^ (1 / 40 : ℝ) := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ N ^ (1 / 40 : ℝ) by positivity)
      linarith only [h, Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1 / 40)]
    change (4 : ℝ) ≤ N ^ (1 / 7 - 1 / 20 - 1 / 40 : ℝ) at hN12
    have hh := mul_le_mul_of_nonneg_right hN12 (show 0 ≤ N ^ (1 / 40 : ℝ) by positivity)
    rw [← Real.rpow_add hn0, sub_add_cancel] at hh
    linarith only [hT, hL, hh]
  have hPack (A : Finset (Fin n)) (hAB : A ⊆ B) (hA : sc.cutoff < A.card) :
      ∃ pack : Finset (Finset (Fin n)),
        (∀ C ∈ pack, C ⊆ A ∧ C.card = b ∧ family C) ∧
        (pack : Set (Finset (Fin n))).Pairwise Disjoint ∧
        (A.card : ℝ) / 2 ≤ (pack.card : ℝ) * b := by
    have hA' : 2 * limit ≤ A.card := by
      have hT : (B.card : ℝ) * R⁻¹ ^ 4 < (sc.cutoff : ℝ) + 1 := by
        rw [sc.cutoff_eq]
        exact Nat.lt_floor_add_one _
      have hC : (sc.cutoff : ℝ) + 1 ≤ A.card := by exact_mod_cast Nat.succ_le_of_lt hA
      have h : 2 * (limit : ℝ) ≤ A.card := (hSc.trans hT.le).trans hC
      exact_mod_cast h
    obtain ⟨pack, hF, hDis, hLeft⟩ :=
      exists_packing (U := A) (d := limit) hb family (fun X hX => hSupply X (hX.trans (hAB.trans hBV)))
    let covered := pack.biUnion id
    have hCover : covered ⊆ A := by
      intro x hx
      obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx
      exact (hF P hP).1 hxP
    have hCard : (covered.card : ℝ) = (pack.card : ℝ) * b := by
      have he : covered.card = pack.card * b := by
        change (pack.biUnion (fun P => P)).card = _
        rw [Finset.card_biUnion hDis]
        trans ∑ _P ∈ pack, b
        · exact Finset.sum_congr rfl (fun P hP => (hF P hP).2.1)
        · simp
      exact_mod_cast he
    have hSub : ((A \ covered).card : ℝ) + covered.card = A.card := by
      rw [Finset.card_sdiff_of_subset hCover]
      exact_mod_cast Nat.sub_add_cancel (Finset.card_le_card hCover)
    have hLeft' : ((A \ covered).card : ℝ) < limit := by exact_mod_cast hLeft
    have hA'' : 2 * (limit : ℝ) ≤ A.card := by exact_mod_cast hA'
    exact ⟨pack, hF, hDis, by linarith only [hCard, hSub, hLeft', hA'']⟩
  have hD : 1 < D := hOverlap.1
  have hγ : 0 < γ := hOverlap.2.1
  obtain ⟨ν, hSup, hProb, hExc⟩ := exists_retention_rule_from_sampler G μ id B hb hK
    family hClique hPack (by positivity : 0 ≤ (K : ℝ) / (40 * a)) (mul_nonneg hγ.le hp.le)
    (by positivity : 0 < 1 / (500 * a * (b : ℝ))) hD
    (by positivity : 0 < R⁻¹ ^ 3) (by positivity : 0 ≤ (K : ℝ) / (40 * a) / 10)
    sc.hH (fun C hC hDis => by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, id_eq] using
        hSample C (fun j => ⟨(hC j).1.trans hBV, (hC j).2⟩) hDis) sc.error sc.reduction sc.cost
  exact ⟨ν, hSup, hProb, hExc.trans_eq sc.cutoff_eq⟩

end LocallyRamsey
