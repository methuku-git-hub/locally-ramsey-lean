module

public import LocallyRamsey.Lower.PreparedRegions
public import LocallyRamsey.Lower.CompletionScales

public section

open Filter
open scoped BigOperators Classical

namespace LocallyRamsey

set_option maxHeartbeats 1600000 in
/-- Equation (3) of the manuscript, with its integer target and natural
logarithm. The contradiction applies to an arbitrary graph at the
rounded test-set size. -/
theorem eventually_no_graph_at_lower_test_size :
    ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n), ¬ IsLocallyRamsey G (lowerTestSize (target n)) (target n) := by
  classical
  filter_upwards [balanced_initial_rule, prepared_intersections, prepared_capped_retention,
    prepared_region_tests, eventually_location_scales, eventually_completion_scales,
    overlap_sampling_parameter_bounds, lower_clique_supply, lower_parameter_bounds]
    with n hInitial hPrepared hCapped hRegions hScales hFinish hPar hSupply hLower
  intro G hG
  let r := target n
  let R : ℝ := r
  let D := overlapDegree r
  let γ := overlapQuota r
  let ρ := R⁻¹ ^ 10
  let q := overlapGroupSize r
  let h := overlapBlockCount r
  let b := largeCliqueOrder r
  let M := lowerTestSize r
  let u := Real.log R
  let δ := 100 * u / R
  let cutoff := ⌈(n : ℝ) ^ (1 / 40 : ℝ)⌉₊
  let V := Fin n
  let Ω := Finset V
  let I := Fin (q * h)
  let J := PositionGroup I q
  obtain ⟨V₀, family, μ, K, p, hK, hV₀, hFam, hClique, _, hp, hu, hSample⟩ := hInitial G hG
  obtain ⟨W, hW, hp0, hUnif, hWV, hW6, hDegree, hClose, hGood⟩ :=
    hPrepared G hG V₀ μ p hV₀ hp.1 hu
  obtain ⟨sc⟩ := hScales W.card hW6
  obtain ⟨fin⟩ := hFinish W.card hW6 sc
  obtain ⟨hD, hγ0, hq2, hh, hhD, hhγ, _, _, _, _⟩ := hPar
  change 2 ≤ q at hq2
  change 0 < h at hh
  have hq : 0 < q := by omega
  have hqm : q ≤ Fintype.card I := by simp only [I, Fintype.card_fin]; exact Nat.le_mul_of_pos_right _ hh
  haveI : Nonempty J := (Finset.powersetCard_nonempty.mpr (by simpa only [Finset.card_univ] using hqm)).to_subtype
  let σ := FiniteLaw.uniform J
  let m := sc.listLength
  let N := sc.draws
  let s := sc.recorded
  let region := sc.regionSize
  let dSig := ⌊2 * δ * (m : ℝ)⌋₊
  let contains (S : Ω) (x : V) := x ∈ S
  let π := biasedLaw W hW μ contains p hp0 hUnif
  let L := sampleWeight W contains
  let c (S : Ω) := (sampleDensity W contains S)⁻¹
  let good (w : Fin q → Ω) := goodPositionGroup W contains ρ w
  letI : Nonempty ↥W := hW.to_subtype
  let ξ := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
  let valid (B : Finset V) := B ⊆ W ∧ B.card = region
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_of_lt hLower.1
  have hr100 : 100 ≤ r := hLower.2.1
  have hrpos : 0 < r := by omega
  have hR0 : 0 < R := by
    change (0 : ℝ) < (r : ℝ)
    exact_mod_cast hrpos
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hR1 : 1 < R := by
    change (1 : ℝ) < (r : ℝ)
    exact_mod_cast (show 1 < r by omega)
  have hu0 : 0 < u := Real.log_pos hR1
  have hb : 0 < b := by
    have h := sc.draw_cover
    by_contra! hb
    have hz : b = 0 := Nat.eq_zero_of_le_zero hb
    have hMR : r ≤ M := hLower.2.2.1
    have hM : 0 < M := hrpos.trans_le hMR
    change 2 * M ≤ N * b at h
    rw [hz, mul_zero] at h
    omega
  have hLarge : 0 < (n : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hWht (x : V) (hx : x ∈ W) : π.mean (fun S => L S x) = 1 :=
    biasedLaw_mean_weight W hW μ contains p hp0 hUnif hx
  have hL (S : Ω) (x : V) : 0 ≤ L S x := by
    change 0 ≤ (if contains S x then 1 else 0) / sampleDensity W contains S
    apply div_nonneg _ (sampleDensity_nonneg _ _ _)
    split <;> norm_num
  have hGood' : (FiniteLaw.product (fun _ : Fin q => π)).event (fun w => ¬ good w) ≤ 1 / 100 := by
    refine (FiniteLaw.event_mono _ (Q := fun w =>
      intersectionDensity L W w < 1 / 2 ∨ 2 < intersectionDensity L W w ∨
      ∃ i, sampleDensity W contains (w i) < ρ) ?_).trans hGood
    intro w hw
    change ¬ (1 / 2 ≤ intersectionDensity L W w ∧ intersectionDensity L W w ≤ 2 ∧
      ∀ i, ρ ≤ sampleDensity W contains (w i)) at hw
    push Not at hw
    by_cases h1 : intersectionDensity L W w < 1 / 2
    · exact Or.inl h1
    · by_cases h2 : 2 < intersectionDensity L W w
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (hw (le_of_not_gt h1) (le_of_not_gt h2)))
  have hOpp (B : Finset V) (_ : B ⊆ W) (hB : cutoff ≤ B.card) :
      ∃ C : Finset V, C ⊆ B ∧ C.card = b ∧ Gᶜ.IsClique (C : Set V) := by
    have h' : (n : ℝ) ^ (1 / 40 : ℝ) ≤ (B.card : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hB)
    obtain ⟨C, hC⟩ := (hSupply G hG B
      ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)).trans h')).2
    exact ⟨C, mem_cliquesIn.mp hC⟩
  obtain ⟨law, draw, cap, hDraw, hMarg, hMargBound, hTotal, hEmpty, hDegrees, hLocal⟩ :=
    exists_biased_group_draws G W hW π (q := q) (h := h) (m := m) (d := dSig) (k := cutoff)
      (N := N) (degreeCap := sc.degreeCap) (density := δ) (γ := γ) (τ := ρ)
      (δ := 1 / 100) (minSize := (n : ℝ) ^ (1 / 7 : ℝ))
      hq hh hb hρ (show 0 ≤ δ by dsimp [δ]; positivity) hγ0.le
      sc.density_quota hLarge hOpp hDegree sc.startLarge sc.signature_budget hWht hGood'
  have hRamsey (B : Finset V) (_ : B ⊆ W) (hB : M ≤ B.card) :
      ∃ C : Finset V, C ⊆ B ∧ C.card = r ∧ G.IsClique (C : Set V) := by
    obtain ⟨A, hAB, hA⟩ := Finset.exists_subset_card_eq hB
    obtain ⟨⟨C, hCA, hC⟩, _⟩ := hG A hA
    exact ⟨C, hCA.trans hAB, hC.card_eq, hC.isClique⟩
  have hDraw' (w : I → Ω) (l : Fin m → ↥W) (j : J) (S : Ω) :
      draw w l j S ⊆ W ∧ Gᶜ.IsClique (draw w l j S : Set V) ∧
      (draw w l j S = ∅ ∨ (draw w l j S).card = b) :=
    ⟨(hDraw w l j S).1, (hDraw w l j S).2.1, (hDraw w l j S).2.2.imp id And.right⟩
  have hloc := probability_locate_clique (cap := sc.collisionCap) G W hW (Finset.univ : Finset I)
    (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by simp [I, Nat.mul_pos hq hh])))
    (by simpa only [Finset.card_univ] using hqm) sc.draws_pos sc.occupancy_pos
    (FiniteLaw.product (fun _ : I => π)) law draw hDraw' sc.draw_cover hRamsey
    (by positivity : 0 ≤ 2 * (b : ℝ) / (n : ℝ) ^ (1 / 7 : ℝ))
    (by positivity : 0 ≤ 2 * (b : ℝ)) cap
    (fun w j x => (hMargBound w j x).1) hMarg (fun w j x => (hMargBound w j x).2.1)
    hTotal sc.small_collision sc.lost_lt sc.small_common sc.region_upper hEmpty hDegrees
  let blocks (i : I) : Fin h → Finset ↥((Finset.univ : Finset I).erase i) :=
    Classical.choose (exists_anchored_blocks (Finset.univ : Finset I) i (Finset.mem_univ i) hh hq
      (by simp [I]))
  have hblocks (i : I) := Classical.choose_spec
    (exists_anchored_blocks (Finset.univ : Finset I) i (Finset.mem_univ i) hh hq
      (by simp [I]))
  let ruleSpec (B : Finset V) (ν : Ω → FiniteLaw Ω) (F : Ω × Ω → Finset V) :=
      (∀ s, F s ⊆ B ∧ F s ⊆ s.1) ∧
      (∀ s, ((F s).card * c s.1 / B.card : ℝ) ∈ Set.Icc 0 2) ∧
      (π.staged ν).mean (fun s => (F s).card * c s.1 / B.card) ≤ γ ∧
      (∀ s x, x ∈ F s → mass (fun _ => c s.1 / B.card) (neighborsIn G (F s) x) ≤
        ((F s).card * c s.1 / B.card + γ) / D) ∧
      (∀ w : Fin q → Ω × Ω, ∀ i, good (Prod.fst ∘ w) → c (w i).1 / B.card ≤ γ / D) ∧
      ((FiniteLaw.product (fun _ : Fin q => π.staged ν)).event
        (fun w => good (Prod.fst ∘ w) ∧ 8 < intersectionDensity (fun s => L s.1) B w) ≤ γ / 4) ∧
      (∀ w, poorlyRetainedMass B (fun s => L s.1) F (fun s => c s.1) γ
        (fun w => good (Prod.fst ∘ w) ∧ intersectionDensity (fun s => L s.1) B w ≤ 8) w ∈ Set.Icc 0 8) ∧
      (FiniteLaw.product (fun _ : Fin q => π.staged ν)).mean
        (poorlyRetainedMass B (fun s => L s.1) F (fun s => c s.1) γ
          (fun w => good (Prod.fst ∘ w) ∧ intersectionDensity (fun s => L s.1) B w ≤ 8)) ≤ γ / 32
  let regionRule (B : Finset V) := ∃ ν F, ruleSpec B ν F
  have hRule (B : Finset V) (hB : valid B) : regionRule B := by
    have hsize : (n : ℝ) ^ (1 / 7 : ℝ) ≤ B.card := hB.2 ▸ sc.region_large
    have hsize' : (W.card : ℝ) / R ^ 2 ≤ B.card := hB.2 ▸ sc.region_fraction_lower
    obtain ⟨ν, hν, hMarg, hExc⟩ := hCapped G V₀ family μ K p hK.2.1 hK.2.2 hp0 hp.2
      hFam hClique hSample B (hB.1.trans hWV) hsize
    obtain ⟨F, hF⟩ := hRegions G W B hW hB.1 μ p hp0 hUnif ν hsize hsize' hClose hν hMarg hExc
    exact ⟨ν, F, hF⟩
  let retentionLaw (B : Finset V) : Ω → FiniteLaw Ω :=
    if hB : valid B then Classical.choose (hRule B hB) else fun _ => FiniteLaw.single ∅
  let F (B : Finset V) : Ω × Ω → Finset V :=
    if hB : valid B then Classical.choose (Classical.choose_spec (hRule B hB)) else fun _ => ∅
  have hSpec (B : Finset V) (hB : valid B) := Classical.choose_spec (Classical.choose_spec (hRule B hB))
  have hChosen (B : Finset V) (hB : valid B) : ruleSpec B (retentionLaw B) (F B) := by
    simpa only [retentionLaw, F, dite_eq_left hB] using hSpec B hB
  let e : LowerExperiment V I Ω (Fin m → ↥W) Ω Ω q h N b s r region :=
    ⟨G, W, π, ξ, law, fun w l jt => draw w l jt.1 jt.2, hW.choose, ∅,
      retentionLaw, γ, L, c, good, F, blocks⟩
  let K' := 4 * (b : ℝ) * ((region : ℝ) / W.card)
  have region_pos : 0 < (region : ℝ) := hLarge.trans_le sc.region_large
  have hhD' : 1 < (h : ℝ) * D := by
    have hH : (1 : ℝ) ≤ h := by exact_mod_cast (Nat.succ_le_of_lt hh)
    exact hD.trans_le (le_mul_of_one_le_left (zero_lt_one.trans hD).le hH)
  refine e.impossible ∅ hq2 hh (by simp [I]) (fun i => ?_)
    (fun i j => (hblocks i).1 j) (fun i => (hblocks i).2)
    (cost := s * (sc.collisionCap + 1)) (r' := r / 2) (H := fin.records)
    (g := fin.mass) (η := R⁻¹ ^ 3) (D := D) (K := K') (err := fin.probabilityError)
    (by positivity) (zero_lt_one.trans hD) hhD' hγ0 fin.mass_pos (by positivity)
    fin.hγ fin.hη fin.hRecords hhγ fin.hExposed fin.hGap fin.hError0 fin.hBoth ?_ ?_
    hL (fun S => inv_nonneg.mpr (sampleDensity_nonneg _ _ _)) ?_ ?_
    (fun w l j => (hDraw' w l j.1 j.2).2.1)
    (fun w l j => (hDraw' w l j.1 j.2).2.2) ?_
    (fun w w' l j h => (hLocal w w' l j h).1)
    (fun w w' l j t h => congrFun (hLocal w w' l j h).2 t) ?_ ?_
  · rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    exact fin.hSize
  · have hrHalf : (↑(r / 2 : ℕ) : ℝ) ≤ R / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      change (↑(r / 2 : ℕ) : ℝ) * 2 ≤ (r : ℝ)
      exact_mod_cast (show r / 2 * 2 ≤ r by omega)
    have hCost := sc.half_clique
    push_cast
    change (↑(r / 2 : ℕ) : ℝ) + (s : ℝ) * (sc.collisionCap + 1) + 2 * (N : ℝ) * γ ≤ R
    linarith only [hrHalf, hCost]
  · refine le_trans ?_ ((FiniteLaw.event_mono _ (fun w hw => ?_)).trans' hloc)
    · have hErr := sc.err
      dsimp only at hErr
      have hI : Fintype.card I = q * h := Fintype.card_fin _
      simp only [Finset.card_univ, hI]
      dsimp only [m, N, δ, dSig, γ, q, h, R, r, u] at *
      linarith only [hErr]
    · exact hw.2.imp (fun f h => h.imp (fun v h => h.imp (fun Q h => ⟨h.2.1, h.2.2⟩)))
  · intro B hB s'
    have h : valid B := hB
    exact ((hChosen B h).1 s').1
  · intro B hB s'
    have h : valid B := hB
    exact ((hChosen B h).2.1 s').2
  · intro w l j hn
    rcases (hDraw w l j.1 j.2).2.2 with he | hg
    · exact False.elim (by simpa [e, he] using hn)
    · exact hg.1
  · intro w l j B x hB hgood
    have hcard : B.card = region := hB.2
    have hg := (hMargBound w j x).2.2 hgood
    have h := (hMarg w l j x).trans hg
    change (law w l j).event (fun S => x ∈ draw w l j S) ≤
      4 * (b : ℝ) * (∏ i : Fin q, L (w (groupPosition j i)) x) / W.card at h
    rw [groupPosition_prod j (fun i => L (w i) x)] at h
    refine h.trans_eq ?_
    change 4 * (b : ℝ) * (∏ i ∈ j.val, L (w i) x) / W.card =
      K' * ((∏ i ∈ j.val, L (w i) x) / B.card)
    rw [hcard]
    dsimp [K']
    field_simp
  · intro B exposed d hB
    have hB' : valid B := hB
    let t := e.tests B exposed
    let α := π.staged (retentionLaw B)
    obtain ⟨hF0, hz, hMean, hdeg, hAtom, hRej, hLoss, hLossMean⟩ := hChosen B hB'
    have hCard : Fintype.card {j // j ∉ namedDraws d} ≤ N := by
      simpa only [Fintype.card_fin] using
        (Fintype.card_le_of_injective (fun i : {j // j ∉ namedDraws d} => i.val) Subtype.val_injective)
    have hL1 (x : V) (hx : x ∈ B) : α.mean (fun s => L s.1 x) = 1 := by
      rw [show α = π.staged (retentionLaw B) from rfl, FiniteLaw.staged_mean]
      have he (S : Ω) : (retentionLaw B S).mean (fun _ => L S x) = L S x :=
        (retentionLaw B S).mean_const _
      simp_rw [he]
      exact hWht x (hB'.1 hx)
    have hFact (z : Ω × Ω) (x : V) (hx : x ∈ F B z) : L z.1 x = c z.1 := by
      simp [L, c, sampleWeight, contains, (hF0 z).2 hx, one_div]
    have hDeg' (z : Ω × Ω) (x : V) (hx : x ∈ F B z) :
        ((neighborsIn G (F B z) x).card : ℝ) * (c z.1 / B.card) ≤
          ((F B z).card * c z.1 / B.card + γ) / D := by
      simpa only [mass, Finset.sum_const, nsmul_eq_mul] using hdeg z x hx
    have hAtom' (i : I) (w : I → Ω × Ω) (J' : Finset I) (hi : i ∈ J')
        (hg : RetainedGroups.isGood t.good w J') : c (w i).1 / B.card ≤ γ / D := by
      obtain ⟨hc, hg⟩ := hg
      let ep := Finset.equivFinOfCardEq hc
      let j := ep ⟨i, hi⟩
      have hj : (ep.symm j).val = i := congrArg Subtype.val (ep.symm_apply_apply ⟨i, hi⟩)
      simpa only [hj] using hAtom (fun j => w (ep.symm j).val) j hg
    have hE := t.event_bad_le α hCard hh (by simp [I]) hγ0 (zero_lt_one.trans hD) hhD
      (fun i => (hblocks i).2) (fun s => (hF0 s).1) hFact (fun s x => hL s.1 x) hL1
      (fun s => inv_nonneg.mpr (sampleDensity_nonneg _ _ _)) hz hMean hDeg' hAtom' hRej hLoss hLossMean
    have hI : Fintype.card I = q * h := Fintype.card_fin _
    refine le_trans ?_ (hE.trans (by rw [hI]; exact fin.hError))
    change ((FiniteLaw.product (fun _ : {j // j ∉ namedDraws d} => σ)).staged (fun _ =>
      FiniteLaw.product (fun _ : I => α))).event (fun w => t.badEvent N w.2 w.1) ≤ _
    rw [FiniteLaw.staged_event, FiniteLaw.staged_event]
    simp_rw [← FiniteLaw.mean_indicator]
    rw [FiniteLaw.mean_mean_comm]

/-- The rounded test size in equation (3) lies below the optimal
threshold for all sufficiently large graph orders. -/
theorem main_lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (Real.logb 2 (n : ℝ)) ^ (7 / 2 : ℝ) / (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 24
        < (threshold n (target n) : ℝ) := by
  apply lower_bound_of_integer_target
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp eventually_no_graph_at_lower_test_size
  refine ⟨n₀, fun n hn => ?_⟩
  have h : 0 ≤ lowerScale (target n) := by unfold lowerScale; positivity
  exact (lt_threshold_iff h).mpr (hn₀ n hn)

end LocallyRamsey
