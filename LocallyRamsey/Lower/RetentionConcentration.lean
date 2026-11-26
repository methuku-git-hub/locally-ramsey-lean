module

public import LocallyRamsey.Lower.GroupCollisions
public import LocallyRamsey.Lower.GroupConcentration
public import LocallyRamsey.Lower.RetentionLoss

public section

open scoped BigOperators

namespace LocallyRamsey

variable {I Ω : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

/-- The concentration estimate for group averages also applies to
eligible groups of independent samples after conditioning, by giving
zero weight to groups that meet revealed positions. -/
theorem event_eligible_group_average_gt_le (μ : FiniteLaw Ω) {q h : ℕ}
    (hh : 0 < h) (hsize : Fintype.card I = q * h)
    (eligible : Finset I → Prop) [DecidablePred eligible]
    (X : (Fin q → Ω) → ℝ) (hX : ∀ ω, X ω ∈ Set.Icc (0 : ℝ) 1)
    {z : ℝ} (hz : 0 ≤ z)
    (hMean : (FiniteLaw.product (fun _ : Fin q => μ)).mean X ≤ z / 4) :
    let groups := (Finset.univ : Finset I).powersetCard q
    let Y (J : Finset I) (ω : I → Ω) :=
      if h : eligible J ∧ J.card = q then
        X (fun i => ω ((Finset.equivFinOfCardEq h.2).symm i).val) else 0
    (FiniteLaw.product (fun _ : I => μ)).event
      (fun ω => z < (∑ J ∈ groups, Y J ω) / groups.card) ≤ Real.exp (-(h * z) / 2) := by
  classical
  intro groups Y
  refine event_average_groups_gt_le μ hh hsize Y ?_ ?_ hz ?_
  · intro J u v huv
    dsimp [Y]
    split
    · rename_i hJ
      congr 1
      funext i
      exact huv _ ((Finset.equivFinOfCardEq hJ.2).symm i).property
    · rfl
  · intro J ω _
    dsimp [Y]
    split
    · exact hX _
    · norm_num
  · intro J _
    by_cases hJ : eligible J ∧ J.card = q
    · simp only [Y, dite_eq_left hJ]
      let f (i : Fin q) := ((Finset.equivFinOfCardEq hJ.2).symm i).val
      have hf : Function.Injective f :=
        Subtype.val_injective.comp (Finset.equivFinOfCardEq hJ.2).symm.injective
      change (FiniteLaw.product (fun _ : I => μ)).mean (fun ω => X (ω ∘ f)) ≤ _
      rwa [FiniteLaw.mean_injective_projection μ f hf X]
    · simp only [Y, dite_eq_right hJ, FiniteLaw.mean_const]
      positivity

open Classical in
/-- The bound on the number of discarded draws uses the conditional
fraction of bad groups. Arbitrarily bad outcomes of the samples are
paid for at their original probability. -/
theorem event_many_draws_from_rare_groups {J : Type*} [Fintype J] (μ : FiniteLaw Ω)
    (ν : FiniteLaw J) (bad : Ω → J → Prop) [∀ x, DecidablePred (bad x)] (N : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (μ.staged (fun _ => FiniteLaw.product (fun _ : Fin N => ν))).event
      (fun z => 2 * N * γ < ∑ j, if bad z.1 (z.2 j) then (1 : ℝ) else 0) ≤
      μ.event (fun x => γ < ν.event (bad x)) +
        Real.exp ((N : ℝ) * γ - Real.log 2 * (2 * N * γ)) := by
  classical
  rw [μ.staged_event, ← μ.mean_indicator,
    ← μ.mean_const (Real.exp ((N : ℝ) * γ - Real.log 2 * (2 * N * γ))), ← μ.mean_add]
  apply μ.mean_mono
  intro x
  let τ := FiniteLaw.product (fun _ : Fin N => ν)
  let X (_ : Fin N) (j : J) := if bad x j then (1 : ℝ) else 0
  by_cases hx : γ < ν.event (bad x)
  · rw [ite_eq_left hx]
    have he := τ.event_nonneg (fun w => ¬(2 * (N : ℝ) * γ < ∑ j, X j (w j)))
    rw [τ.event_not] at he
    exact (sub_nonneg.mp he).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [ite_eq_right hx, zero_add]
    refine (τ.event_mono (fun w hw => (lt_of_lt_of_le hw le_rfl).le)).trans ?_
    refine (FiniteLaw.prob_sum_ge_le (fun _ : Fin N => ν) X (fun j s => by
      dsimp [X]; split <;> norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (2 * N * γ)).trans ?_
    rw [Real.exp_le_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
    have hmean : ∑ j : Fin N, ν.mean (X j) ≤ (N : ℝ) * γ := by
      simp only [X, ν.mean_indicator, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left (le_of_not_gt hx) (Nat.cast_nonneg _)
    exact hmean

/-- A prescribed number of fresh draws may be bounded by the original
number of draws, even when fewer remain after exposing a description. -/
theorem event_many_fresh_draws_from_rare_groups {J K : Type*} [Fintype J] [Fintype K] [DecidableEq K]
    (μ : FiniteLaw Ω) (ν : FiniteLaw J) (bad : Ω → J → Prop) [∀ x, DecidablePred (bad x)]
    {N : ℕ} (hN : Fintype.card K ≤ N) {γ : ℝ} (hγ : 0 ≤ γ) :
    (μ.staged (fun _ => FiniteLaw.product (fun _ : K => ν))).event
      (fun z => 2 * N * γ < ∑ j, if bad z.1 (z.2 j) then (1 : ℝ) else 0) ≤
      μ.event (fun x => γ < ν.event (bad x)) +
        Real.exp ((N : ℝ) * γ - Real.log 2 * (2 * N * γ)) := by
  classical
  rw [μ.staged_event]
  let Y (x : Ω) := (FiniteLaw.product (fun _ : Fin N => ν)).event
    (fun w => 2 * N * γ < ∑ j, if bad x (w j) then (1 : ℝ) else 0)
  refine (μ.mean_mono (Y := Y) (fun x => ?_)).trans ?_
  · let e := ((Fintype.equivFin K).trans (Fin.castLEEmb hN).toEquivRange).trans
      (Equiv.refl _)
    let f (j : K) := Fin.castLE hN (Fintype.equivFin K j)
    have hf : Function.Injective f := (Fin.castLE_injective hN).comp (Fintype.equivFin K).injective
    rw [← FiniteLaw.event_injective_projection ν f hf
      (fun w => 2 * N * γ < ∑ j, if bad x (w j) then (1 : ℝ) else 0)]
    apply FiniteLaw.event_mono
    intro w hw
    refine hw.trans_le ?_
    rw [show (∑ j : K, if bad x ((w ∘ f) j) then (1 : ℝ) else 0) =
        ∑ i ∈ Finset.univ.map (⟨f, hf⟩ : K ↪ Fin N), if bad x (w i) then (1 : ℝ) else 0 by
      rw [Finset.sum_map]
      rfl]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by split <;> norm_num)
  · have h := event_many_draws_from_rare_groups μ ν bad N hγ
    rw [FiniteLaw.staged_event] at h
    exact h

/-- A bound on expected loss of weight within a group and a deterministic
cap of eight give the manuscript's concentration bound for the average
loss over all groups. -/
theorem event_average_retention_loss_gt_le (μ : FiniteLaw Ω) {q h : ℕ}
    (hh : 0 < h) (hsize : Fintype.card I = q * h)
    (eligible : Finset I → Prop) [DecidablePred eligible]
    (loss : (Fin q → Ω) → ℝ) (hLoss : ∀ ω, loss ω ∈ Set.Icc (0 : ℝ) 8)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hMean : (FiniteLaw.product (fun _ : Fin q => μ)).mean loss ≤ γ / 32) :
    let groups := (Finset.univ : Finset I).powersetCard q
    let Y (J : Finset I) (ω : I → Ω) :=
      if h : eligible J ∧ J.card = q then
        loss (fun i => ω ((Finset.equivFinOfCardEq h.2).symm i).val) else 0
    (FiniteLaw.product (fun _ : I => μ)).event
      (fun ω => γ < (∑ J ∈ groups, Y J ω) / groups.card) ≤ Real.exp (-(h * γ) / 16) := by
  classical
  intro groups Y
  let Z (w : Fin q → Ω) := loss w / 8
  have hZ (w : Fin q → Ω) : Z w ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (hLoss w).1 (by norm_num), (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr (hLoss w).2⟩
  have hZm : (FiniteLaw.product (fun _ : Fin q => μ)).mean Z ≤ (γ / 8) / 4 := by
    have he : (FiniteLaw.product (fun _ : Fin q => μ)).mean Z =
        ((FiniteLaw.product (fun _ : Fin q => μ)).mean loss) / 8 := by
      simp only [Z, div_eq_inv_mul, FiniteLaw.mean_mul_const]
    rw [he]
    linarith only [hMean, hγ]
  have h := event_eligible_group_average_gt_le μ hh hsize eligible Z (I := I) hZ
    (div_nonneg hγ (by norm_num)) hZm
  refine ((FiniteLaw.product (fun _ : I => μ)).event_mono (Q := _) ?_).trans (h.trans_eq ?_)
  · intro ω ωh
    have hY (J : Finset I) :
        (if h : eligible J ∧ J.card = q then Z
            (fun i => ω ((Finset.equivFinOfCardEq h.2).symm i).val) else 0) = Y J ω / 8 := by
      dsimp [Y, Z]
      split <;> simp_all
    simp_rw [hY]
    rw [← Finset.sum_div, div_right_comm]
    exact div_lt_div_of_pos_right ωh (by norm_num)
  · congr 1
    ring


/-- In a good group the comparison density is at most two. If the
density on the new region exceeds eight, the original product law
assigns only a small probability to this event. -/
theorem event_reject_group_le (μ : FiniteLaw Ω) (a b : Ω → ℝ)
    (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω) (hmean : μ.mean a = 1)
    (good : Ω → Prop) [DecidablePred good] (hg : ∀ ω, good ω → b ω ≤ 2)
    {ε : ℝ} (hClose : rootDistance μ a b ≤ 2 * ε) :
    μ.event (fun ω => good ω ∧ 8 < a ω) ≤ ε := by
  classical
  let E (ω : Ω) := good ω ∧ 8 < a ω
  have hE (ω : Ω) (hw : E ω) : 4 * b ω < a ω := by
    have hb := hg ω hw.1
    have ha := hw.2
    linarith only [hb, ha]
  have h := mean_density_restriction_le μ a b ha hb hmean E hE
  have hMass : 8 * μ.event E ≤ μ.mean (fun ω => if E ω then a ω else 0) := by
    rw [← μ.mean_indicator, ← μ.mean_mul_const]
    apply μ.mean_mono
    intro ω
    by_cases hw : E ω
    · simpa [hw] using hw.2.le
    · simp [hw]
  linarith only [h, hMass, hClose]

/-- Conditional on any fixed description, combining the group-average
bound with independent draws of the groups controls the number rejected. -/
theorem event_many_rejected_groups_le (μ : FiniteLaw Ω) {q h : ℕ}
    (hh : 0 < h) (hsize : Fintype.card I = q * h)
    (eligible : Finset I → Prop) [DecidablePred eligible]
    (test : (Fin q → Ω) → Prop) [DecidablePred test]
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hMean : (FiniteLaw.product (fun _ : Fin q => μ)).event test ≤ γ / 4)
    (N : ℕ)
    [Nonempty ↥((Finset.univ : Finset I).powersetCard q)] :
    let groups := (Finset.univ : Finset I).powersetCard q
    let Q (ω : I → Ω) (J : ↥groups) := eligible J.val ∧
      test (fun i => ω ((Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm i).val)
    let ξ := FiniteLaw.product (fun _ : I => μ)
    let σ := FiniteLaw.uniform ↥groups
    (ξ.staged (fun _ => FiniteLaw.product (fun _ : Fin N => σ))).event
      (fun w => 2 * N * γ < ∑ i, if Q w.1 (w.2 i) then (1 : ℝ) else 0) ≤
      Real.exp (-(h * γ) / 2) + Real.exp ((N : ℝ) * γ - Real.log 2 * (2 * N * γ)) := by
  classical
  intro groups Q ξ σ
  refine (event_many_draws_from_rare_groups ξ σ Q N hγ).trans ?_
  apply add_le_add_left
  let X (ω : Fin q → Ω) := if test ω then (1 : ℝ) else 0
  have hX (ω : Fin q → Ω) : X ω ∈ Set.Icc (0 : ℝ) 1 := by dsimp [X]; split <;> norm_num
  have hX' : (FiniteLaw.product (fun _ : Fin q => μ)).mean X ≤ γ / 4 := by
    rwa [FiniteLaw.mean_indicator]
  let Y (J : Finset I) (ω : I → Ω) :=
    if h : eligible J ∧ J.card = q then
      X (fun i => ω ((Finset.equivFinOfCardEq h.2).symm i).val) else 0
  have hEq (ω : I → Ω) : σ.event (Q ω) = (∑ J ∈ groups, Y J ω) / groups.card := by
    rw [← σ.mean_indicator]
    change ∑ J : ↥groups, (Fintype.card ↥groups : ℝ)⁻¹ *
      (if Q ω J then (1 : ℝ) else 0) = _
    rw [← Finset.mul_sum, inv_mul_eq_div, Fintype.card_coe]
    congr 1
    rw [← Finset.sum_coe_sort groups (fun J => Y J ω)]
    apply Finset.sum_congr rfl
    intro J _
    have hj := (Finset.mem_powersetCard.mp J.property).2
    by_cases hJ : eligible J.val
    · simp [Y, X, Q, hJ, hj]
    · simp [Y, Q, hJ]
  simp_rw [hEq]
  exact event_eligible_group_average_gt_le μ hh hsize eligible X hX hγ hX'

end LocallyRamsey
