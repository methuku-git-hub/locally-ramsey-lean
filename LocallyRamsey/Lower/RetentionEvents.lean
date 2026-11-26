module

public import LocallyRamsey.Lower.AnchorProbability
public import LocallyRamsey.Lower.DescriptionExperiment

public section

open scoped BigOperators Classical

namespace LocallyRamsey.RetainedGroups

variable {V I Ω T : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype Ω]
variable {q h N : ℕ}

/-- The group predicate on ordered samples, written as a predicate of
the underlying set of positions. -/
@[expose] def isGood (good : (Fin q → Ω) → Prop) (ω : I → Ω) (J : Finset I) : Prop :=
  ∃ hc : J.card = q, good (fun j => ω ((Finset.equivFinOfCardEq hc).symm j).val)

theorem isGood_local (good : (Fin q → Ω) → Prop) (ω ω' : I → Ω) (J : Finset I)
    (he : ∀ i ∈ J, ω i = ω' i) : isGood good ω J ↔ isGood good ω' J := by
  unfold isGood
  apply exists_congr
  intro hJ
  have hh : (fun j => ω ((Finset.equivFinOfCardEq hJ).symm j).val) =
      (fun j => ω' ((Finset.equivFinOfCardEq hJ).symm j).val) :=
    funext (fun j => he _ ((Finset.equivFinOfCardEq hJ).symm j).property)
  rw [hh]

theorem isGood_group (good : (Fin q → Ω) → Prop) (ω : I → Ω) (J : PositionGroup I q) :
    isGood good ω J.val ↔ good (ω ∘ groupPosition J) := by
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(Finset.mem_powersetCard.mp J.property).2, h⟩⟩

/-- The two numerical thresholds that control the removal of groups and
of positions, together with the conditions for the upper estimate. -/
structure Tests (V I Ω : Type*) (q h : ℕ) [Fintype I] [DecidableEq I] where
  graph : SimpleGraph V
  region : Finset V
  exposed : Finset I
  factor : Ω → V → ℝ
  retained : Ω → Finset V
  singleFactor : Ω → ℝ
  good : (Fin q → Ω) → Prop
  γ : ℝ
  blocks : (i : I) → Fin h → Finset ↥((Finset.univ : Finset I).erase i)

namespace Tests

variable (t : Tests V I Ω q h)

@[expose] noncomputable def experiment (ω : I → Ω) : RetainedGroups V I Ω :=
  ⟨t.region, t.exposed, ω, t.factor, t.retained, t.singleFactor, isGood t.good ω, t.γ⟩

@[expose] def reject (ω : I → Ω) (J : PositionGroup I q) : Prop :=
  Disjoint t.exposed J.val ∧ (t.experiment ω).good J.val ∧
    8 < mass ((t.experiment ω).rawWeight J.val) t.region

@[expose] noncomputable def loss (ω : I → Ω) (J : PositionGroup I q) : ℝ :=
  mass ((t.experiment ω).weight J.val) ((t.experiment ω).bad J)

@[expose] noncomputable def markedMass [DecidableRel t.graph.Adj] (ω : I → Ω) (i : I) : ℝ :=
  (FiniteLaw.uniform (Equiv.Perm ↥((Finset.univ : Finset I).erase i))).mean (fun p =>
    let w := (t.experiment ω).meanAt i (t.blocks i) p
    mass w (marked t.graph w t.region t.γ))

@[expose] noncomputable def unrevealedMass (ω : I → Ω) : ℝ :=
  ∑ i ∈ Finset.univ \ t.exposed, (t.experiment ω).positionMass i

@[expose] def badEvent [Fintype T] [DecidableRel t.graph.Adj] [Nonempty (PositionGroup I q)]
    (N : ℕ) (ω : I → Ω) (draws : T → PositionGroup I q) : Prop :=
  (2 * (N : ℝ) * t.γ < ∑ j, if t.reject ω (draws j) then (1 : ℝ) else 0) ∨
    t.γ < (FiniteLaw.uniform (PositionGroup I q)).mean (t.loss ω) ∨
    (∃ i, ((h : ℝ)⁻¹) ^ 2 < t.markedMass ω i) ∨
    (4 * (Fintype.card I : ℝ) * t.γ < t.unrevealedMass ω)

theorem rawWeight_local (ω ω' : I → Ω) (J : Finset I)
    (he : ∀ i ∈ J, ω i = ω' i) :
    (t.experiment ω).rawWeight J = (t.experiment ω').rawWeight J := by
  funext x
  unfold experiment rawWeight
  congr 1
  exact Finset.prod_congr rfl (fun i hi => congrArg (fun s => t.factor s x) (he i hi))

theorem kept_local (ω ω' : I → Ω) (J : Finset I) (he : ∀ i ∈ J, ω i = ω' i) :
    (t.experiment ω).kept J ↔ (t.experiment ω').kept J := by
  unfold kept
  rw [t.rawWeight_local ω ω' J he]
  exact and_congr Iff.rfl (and_congr (isGood_local t.good ω ω' J he) Iff.rfl)

theorem badEvent_local [Fintype T] [DecidableRel t.graph.Adj] [Nonempty (PositionGroup I q)]
    (N : ℕ) (ω ω' : I → Ω) (draws : T → PositionGroup I q)
    (he : ∀ i, i ∉ t.exposed → ω i = ω' i) : t.badEvent N ω draws ↔ t.badEvent N ω' draws := by
  classical
  have hlocal (J : Finset I) (hJ : Disjoint t.exposed J) (i : I) (hi : i ∈ J) : ω i = ω' i :=
    he i (fun h => Finset.disjoint_left.mp hJ h hi)
  have hr (J : PositionGroup I q) : t.reject ω J ↔ t.reject ω' J := by
    unfold reject
    apply and_congr_right
    intro hJ
    rw [t.rawWeight_local ω ω' _ (hlocal _ hJ)]
    exact and_congr (isGood_local t.good ω ω' _ (hlocal _ hJ)) Iff.rfl
  have hl (J : PositionGroup I q) : t.loss ω J = t.loss ω' J := by
    simp only [loss, kept_mass_bad_eq]
    by_cases hJ : Disjoint t.exposed J.val
    · have hProj : ω ∘ groupPosition J = ω' ∘ groupPosition J :=
        funext (fun i => hlocal _ hJ _ (groupPosition_mem J i))
      have hw := t.rawWeight_local ω ω' _ (hlocal _ hJ)
      have hg := isGood_local t.good ω ω' _ (hlocal _ hJ)
      rw [show (t.experiment ω).revealed = t.exposed from rfl, if_pos hJ]
      rw [show (t.experiment ω').revealed = t.exposed from rfl, if_pos hJ]
      have hp : (fun _ : Fin q → Ω => (t.experiment ω).good J.val ∧
          mass ((t.experiment ω).rawWeight J.val) (t.experiment ω).region ≤ 8) =
          (fun _ : Fin q → Ω => (t.experiment ω').good J.val ∧
            mass ((t.experiment ω').rawWeight J.val) (t.experiment ω').region ≤ 8) := by
        funext w
        apply propext
        rw [hw]
        exact and_congr hg Iff.rfl
      rw [hp]
      exact congrArg _ hProj
    · simp [experiment, hJ]
  have hm (i : I) : t.markedMass ω i = t.markedMass ω' i := by
    have hn (J : Finset I) (hi : i ∈ J) :
        (t.experiment ω).normalized i J = (t.experiment ω').normalized i J := by
      by_cases hJ : Disjoint t.exposed J
      · have hiEq := hlocal J hJ i hi
        have hk := t.kept_local ω ω' J (hlocal J hJ)
        have hw := t.rawWeight_local ω ω' J (hlocal J hJ)
        have hg : (t.experiment ω).kept J = (t.experiment ω').kept J := propext hk
        have hz : (t.experiment ω).positionMass i = (t.experiment ω').positionMass i := by
          simp only [positionMass, experiment, hiEq]
        have hW : (t.experiment ω).weight J = (t.experiment ω').weight J := by
          funext x
          unfold weight
          rw [hg, hw]
        unfold normalized
        rw [hz, hg, hW]
        simp only [experiment, hiEq]
        rfl
      · have h0 : ¬ (t.experiment ω).kept J := fun hk => hJ hk.1
        have h0' : ¬ (t.experiment ω').kept J := fun hk => hJ hk.1
        funext x
        simp [normalized, normalizedOverlap, h0, h0']
    have hc (p : Equiv.Perm ↥((Finset.univ : Finset I).erase i)) :
        (t.experiment ω).meanAt i (t.blocks i) p = (t.experiment ω').meanAt i (t.blocks i) p := by
      funext x
      unfold meanAt
      congr 1
      exact Finset.sum_congr rfl (fun j _ => congrFun (hn _ (by simp [restoreAnchor])) x)
    simp only [markedMass, hc]
  have hm' : t.unrevealedMass ω = t.unrevealedMass ω' := by
    unfold unrevealedMass
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [positionMass, positionMass]
    simp only [experiment, he i (Finset.mem_sdiff.mp hi).2]
  have heLoss : t.loss ω = t.loss ω' := funext hl
  simp only [badEvent, heLoss, hm, hm']
  have hs : (∑ j, if t.reject ω (draws j) then (1 : ℝ) else 0) =
      ∑ j, if t.reject ω' (draws j) then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hr]
  rw [hs]

/-- After fixing one description, the four bad events have small
probability. Each event is measured over the independent fresh
samples, auxiliary choices, and fresh groups. -/
theorem event_bad_le [Fintype T] [DecidableEq T] [DecidableRel t.graph.Adj]
    [Nonempty (PositionGroup I q)] (μ : FiniteLaw Ω)
    (hN : Fintype.card T ≤ N) (hh : 0 < h) (hI : Fintype.card I = q * h)
    {D : ℝ} (hγ : 0 < t.γ) (hD : 0 < D) (hsize : (h : ℝ) - 1 ≤ D)
    (hdisj : ∀ i, Pairwise fun j k => Disjoint (t.blocks i j) (t.blocks i k))
    (hF : ∀ s, t.retained s ⊆ t.region)
    (hrow : ∀ s x, x ∈ t.retained s → t.factor s x = t.singleFactor s)
    (hL : ∀ s x, 0 ≤ t.factor s x) (hL1 : ∀ x ∈ t.region, μ.mean (fun s => t.factor s x) = 1)
    (hc : ∀ s, 0 ≤ t.singleFactor s)
    (hz : ∀ s, ((t.retained s).card * t.singleFactor s / t.region.card : ℝ) ∈ Set.Icc 0 2)
    (hmean : μ.mean (fun s => (t.retained s).card * t.singleFactor s / t.region.card) ≤ t.γ)
    (hdeg : ∀ s x, x ∈ t.retained s →
      ((neighborsIn t.graph (t.retained s) x).card : ℝ) * (t.singleFactor s / t.region.card) ≤
        ((t.retained s).card * t.singleFactor s / t.region.card + t.γ) / D)
    (hatom : ∀ (i : I) z J, i ∈ J → isGood t.good z J →
      t.singleFactor (z i) / t.region.card ≤ t.γ / D)
    (hReject : (FiniteLaw.product (fun _ : Fin q => μ)).event (fun w =>
      t.good w ∧ 8 < intersectionDensity t.factor t.region w) ≤ t.γ / 4)
    (hLoss : ∀ w, (poorlyRetainedMass t.region t.factor t.retained t.singleFactor t.γ
      (fun w => t.good w ∧ intersectionDensity t.factor t.region w ≤ 8) w) ∈ Set.Icc 0 8)
    (hLossMean : (FiniteLaw.product (fun _ : Fin q => μ)).mean
      (poorlyRetainedMass t.region t.factor t.retained t.singleFactor t.γ
        (fun w => t.good w ∧ intersectionDensity t.factor t.region w ≤ 8)) ≤ t.γ / 32) :
    let α := FiniteLaw.product (fun _ : I => μ)
    let σ := FiniteLaw.uniform (PositionGroup I q)
    let law := α.staged (fun _ => FiniteLaw.product (fun _ : T => σ))
    law.event (fun z => t.badEvent N z.1 z.2) ≤
      (Real.exp (-(h * t.γ) / 2) +
        Real.exp ((N : ℝ) * t.γ - Real.log 2 * (2 * N * t.γ))) +
      Real.exp (-(h * t.γ) / 16) +
      Fintype.card I * (Real.exp (1 / 8 - Real.log 2 * ((h : ℝ) * t.γ - 1)) / ((h : ℝ)⁻¹) ^ 2) +
      Real.exp (-(Fintype.card I : ℝ) * t.γ / 2) := by
  classical
  intro α σ law
  let R (ω : I → Ω) (w : T → PositionGroup I q) :=
    2 * (N : ℝ) * t.γ < ∑ j, if t.reject ω (w j) then (1 : ℝ) else 0
  let Ls (ω : I → Ω) := t.γ < σ.mean (t.loss ω)
  let M (ω : I → Ω) := ∃ i, ((h : ℝ)⁻¹) ^ 2 < t.markedMass ω i
  let Z (ω : I → Ω) := 4 * (Fintype.card I : ℝ) * t.γ < t.unrevealedMass ω
  have hAvg (X : PositionGroup I q → ℝ) : σ.mean X =
      (∑ j : PositionGroup I q, X j) / Fintype.card (PositionGroup I q) := by
    change ∑ j : PositionGroup I q, (Fintype.card (PositionGroup I q) : ℝ)⁻¹ * X j = _
    rw [← Finset.mul_sum, inv_mul_eq_div]
  have hraw (ω : I → Ω) (J : PositionGroup I q) :
      mass ((t.experiment ω).rawWeight J.val) t.region =
        intersectionDensity t.factor t.region (ω ∘ groupPosition J) := by
    unfold intersectionDensity mass
    simp only [rawWeight, experiment]
    rw [← Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl (fun x _ =>
      (groupPosition_prod J (fun i => t.factor (ω i) x)).symm)
  have hLossBound : α.event Ls ≤ Real.exp (-(h * t.γ) / 16) := by
    let f := poorlyRetainedMass t.region t.factor t.retained t.singleFactor t.γ
        (fun w => t.good w ∧ intersectionDensity t.factor t.region w ≤ 8)
    have h := event_average_retention_loss_gt_le μ hh hI (fun J => Disjoint t.exposed J)
      f hLoss hγ.le hLossMean
    refine le_trans ?_ h
    apply FiniteLaw.event_mono
    intro ω hω
    have he (J : PositionGroup I q) : t.loss ω J =
        if hJ : Disjoint t.exposed J.val ∧ J.val.card = q then
          f (fun i => ω ((Finset.equivFinOfCardEq hJ.2).symm i).val) else 0 := by
      rw [loss, kept_mass_bad_eq]
      by_cases hd : Disjoint t.exposed J.val
      · have hJ : Disjoint t.exposed J.val ∧ J.val.card = q :=
          ⟨hd, (Finset.mem_powersetCard.mp J.property).2⟩
        rw [dite_eq_left hJ]
        rw [show (t.experiment ω).revealed = t.exposed from rfl, if_pos hd]
        change poorlyRetainedMass t.region t.factor t.retained t.singleFactor t.γ
          (fun _ => isGood t.good ω J.val ∧ mass ((t.experiment ω).rawWeight J.val) t.region ≤ 8)
          (ω ∘ groupPosition J) = f (ω ∘ groupPosition J)
        rw [hraw, isGood_group]
        unfold f poorlyRetainedMass
        rfl
      · have hJ : ¬ (Disjoint t.exposed J.val ∧ J.val.card = q) := fun h => hd h.1
        rw [dite_eq_right hJ]
        simp [experiment, hd]
    change t.γ < σ.mean (t.loss ω) at hω
    rw [hAvg, Fintype.card_coe] at hω
    let X (J : Finset I) := if hJ : Disjoint t.exposed J ∧ J.card = q then
      f (fun i => ω ((Finset.equivFinOfCardEq hJ.2).symm i).val) else 0
    have he' (j : PositionGroup I q) := he j
    change _ < (∑ j : PositionGroup I q, _) / _ at hω
    rw [Finset.sum_congr rfl (fun j _ => show _ = X j.val from he' j),
      Finset.sum_coe_sort _ X] at hω
    exact hω
  have hRejBound : law.event (fun z => R z.1 z.2) ≤
      Real.exp (-(h * t.γ) / 2) + Real.exp ((N : ℝ) * t.γ - Real.log 2 * (2 * N * t.γ)) := by
    refine (event_many_fresh_draws_from_rare_groups α σ t.reject hN hγ.le).trans ?_
    apply add_le_add_left
    let test (w : Fin q → Ω) := t.good w ∧ 8 < intersectionDensity t.factor t.region w
    let f (w : Fin q → Ω) := if test w then (1 : ℝ) else 0
    have hf (w : Fin q → Ω) : f w ∈ Set.Icc (0 : ℝ) 1 := by unfold f; split <;> norm_num
    have hfMean : (FiniteLaw.product (fun _ : Fin q => μ)).mean f ≤ t.γ / 4 := by
      unfold f
      rwa [FiniteLaw.mean_indicator]
    have h := event_eligible_group_average_gt_le μ hh hI (fun J => Disjoint t.exposed J) f hf hγ.le hfMean
    refine le_trans ?_ h
    apply FiniteLaw.event_mono
    intro ω hω
    have he (J : PositionGroup I q) :
        (if t.reject ω J then (1 : ℝ) else 0) =
        if hJ : Disjoint t.exposed J.val ∧ J.val.card = q then
          f (fun i => ω ((Finset.equivFinOfCardEq hJ.2).symm i).val) else 0 := by
      by_cases hd : Disjoint t.exposed J.val
      · have hJ : Disjoint t.exposed J.val ∧ J.val.card = q :=
          ⟨hd, (Finset.mem_powersetCard.mp J.property).2⟩
        rw [dite_eq_left hJ]
        have hr : t.reject ω J ↔ t.good (ω ∘ groupPosition J) ∧
            8 < intersectionDensity t.factor t.region (ω ∘ groupPosition J) := by
          unfold reject
          rw [hraw]
          simp only [hd, true_and]
          exact and_congr (isGood_group t.good ω J) Iff.rfl
        change (if t.reject ω J then (1 : ℝ) else 0) = f (ω ∘ groupPosition J)
        by_cases h : test (ω ∘ groupPosition J)
        · have hr' := hr.mpr h
          simp [f, h, hr']
        · have hr' : ¬ t.reject ω J := fun h' => h (hr.mp h')
          simp [f, h, hr']
      · have hJ : ¬ (Disjoint t.exposed J.val ∧ J.val.card = q) := fun h => hd h.1
        simp [reject, hd, hJ]
    rw [← FiniteLaw.mean_indicator, hAvg, Fintype.card_coe] at hω
    let X (J : Finset I) := if hJ : Disjoint t.exposed J ∧ J.card = q then
      f (fun i => ω ((Finset.equivFinOfCardEq hJ.2).symm i).val) else 0
    have he' (j : PositionGroup I q) := he j
    change _ < (∑ j : PositionGroup I q, _) / _ at hω
    rw [Finset.sum_congr rfl (fun j _ => show _ = X j.val from he' j),
      Finset.sum_coe_sort _ X] at hω
    exact hω
  have hMarks : α.event M ≤
      Fintype.card I * (Real.exp (1 / 8 - Real.log 2 * ((h : ℝ) * t.γ - 1)) / ((h : ℝ)⁻¹) ^ 2) := by
    refine (α.event_exists_le_sum (fun i ω => ((h : ℝ)⁻¹) ^ 2 < t.markedMass ω i)).trans ?_
    rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun i _ => event_anchor_marked_gt_le t.graph μ t.region t.exposed i
      t.factor t.retained t.singleFactor (isGood t.good) (isGood_local t.good) hF hrow hL hL1
      hc hγ hD hdeg (hatom i) hh hsize (t.blocks i) (hdisj i))
  have hZ : α.event Z ≤ Real.exp (-(Fintype.card I : ℝ) * t.γ / 2) := by
    let X (_ : I) (s : Ω) := ((t.retained s).card * t.singleFactor s / t.region.card : ℝ) / 2
    have hX (i : I) (s : Ω) : X i s ∈ Set.Icc (0 : ℝ) 1 := by
      obtain ⟨h0, h1⟩ := hz s
      exact ⟨by dsimp [X]; linarith, by dsimp [X]; linarith⟩
    have hZ' := FiniteLaw.prob_sum_ge_le (fun _ : I => μ) X hX
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (2 * (Fintype.card I : ℝ) * t.γ)
    refine (α.event_mono (Q := fun ω => 2 * (Fintype.card I : ℝ) * t.γ ≤ ∑ i, X i (ω i))
      (fun ω hω => ?_)).trans (hZ'.trans ?_)
    · have hs : t.unrevealedMass ω ≤ ∑ i : I, (t.experiment ω).positionMass i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => (hz (ω i)).1)
      change 2 * (Fintype.card I : ℝ) * t.γ ≤ ∑ i, (t.experiment ω).positionMass i / 2
      rw [← Finset.sum_div]
      change _ < t.unrevealedMass ω at hω
      linarith only [hω, hs]
    · rw [Real.exp_le_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hx (i : I) : μ.mean (X i) ≤ t.γ / 2 := by
        have he : X i = fun s => (2 : ℝ)⁻¹ * ((t.retained s).card * t.singleFactor s / t.region.card) :=
          funext (fun s => by dsimp [X]; ring)
        rw [he, FiniteLaw.mean_mul_const, div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hmean (by norm_num)
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hx i)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
      have hlog := mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ≤ Real.log 2 by
        linarith [Real.log_two_gt_d9]) (show 0 ≤ 2 * (Fintype.card I : ℝ) * t.γ by positivity)
      nlinarith only [hs, hlog]
  have hp (P : (I → Ω) → Prop) : law.event (fun w => P w.1) = α.event P := by
    rw [FiniteLaw.staged_event, ← FiniteLaw.mean_indicator]
    congr 1
    funext w
    simp only [← FiniteLaw.mean_indicator, FiniteLaw.mean_const]
  refine (law.event_mono (Q := fun z => ((R z.1 z.2 ∨ Ls z.1) ∨ M z.1) ∨ Z z.1)
    (fun w hw => by dsimp [badEvent, R, Ls, M, Z] at *; tauto)).trans ?_
  refine (law.event_union_le (fun z => (R z.1 z.2 ∨ Ls z.1) ∨ M z.1) (fun z => Z z.1)).trans ?_
  refine add_le_add ?_ (by rw [hp]; exact hZ)
  refine (law.event_union_le (fun z => R z.1 z.2 ∨ Ls z.1) (fun z => M z.1)).trans ?_
  refine add_le_add ?_ (by rw [hp]; exact hMarks)
  exact (law.event_union_le (fun z => R z.1 z.2) (fun z => Ls z.1)).trans
    (add_le_add hRejBound (by rw [hp]; exact hLossBound))

end Tests
end LocallyRamsey.RetainedGroups
