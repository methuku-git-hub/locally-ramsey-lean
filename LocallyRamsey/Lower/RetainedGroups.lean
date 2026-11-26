module

public import LocallyRamsey.Lower.PreparedGroupRetention
public import LocallyRamsey.Lower.RecordedOverlap

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V I Ω T : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable {q : ℕ}

abbrev PositionGroup (I : Type*) [Fintype I] [DecidableEq I] (q : ℕ) :=
  ↥((Finset.univ : Finset I).powersetCard q)

/-- The coordinates of a group, in a fixed order. -/
@[expose] noncomputable def groupPosition (J : PositionGroup I q) (i : Fin q) : I :=
  ((Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm i).val

theorem groupPosition_mem (J : PositionGroup I q) (i : Fin q) : groupPosition J i ∈ J.val :=
  ((Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm i).property

/-- The product weight in the group does not depend on its ordering. -/
theorem groupPosition_prod (J : PositionGroup I q) (L : I → ℝ) :
    (∏ i : Fin q, L (groupPosition J i)) = ∏ i ∈ J.val, L i := by
  let e := (Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm
  simpa only [groupPosition] using
    (Fintype.prod_equiv e (fun i => L (e i).val) (fun i => L i.val) (fun _ => rfl)).trans
      (Finset.prod_coe_sort J.val L)

variable [Fintype Ω]

/-- All input to the retained-group calculations after fixing the
region and the exposed positions of a description. -/
structure RetainedGroups (V I Ω : Type*) where
  region : Finset V
  revealed : Finset I
  outcome : I → Ω
  factor : Ω → V → ℝ
  retained : Ω → Finset V
  singleFactor : Ω → ℝ
  good : Finset I → Prop
  quota : ℝ

namespace RetainedGroups

variable (u : RetainedGroups V I Ω)

@[expose] noncomputable def positionMass (i : I) : ℝ :=
  ((u.retained (u.outcome i)).card : ℝ) * u.singleFactor (u.outcome i) / u.region.card

@[expose] noncomputable def rawWeight (J : Finset I) (x : V) : ℝ :=
  (∏ i ∈ J, u.factor (u.outcome i) x) / u.region.card

@[expose] def kept (J : Finset I) : Prop :=
  Disjoint u.revealed J ∧ u.good J ∧ mass (u.rawWeight J) u.region ≤ 8

@[expose] noncomputable def weight (J : Finset I) (x : V) : ℝ :=
  if u.kept J then u.rawWeight J x else 0

@[expose] noncomputable def survivors (J : PositionGroup I q) (i : Fin q) : Finset V := by
  classical
  let p := groupPosition J i
  exact if mass (u.rawWeight J.val) (u.retained (u.outcome p)) ≤ 16 * u.positionMass p
    then u.retained (u.outcome p) else ∅

@[expose] noncomputable def bad (J : PositionGroup I q) : Finset V := by
  classical
  exact u.region.filter (fun x =>
    ((Finset.univ.filter (fun i => x ∈ u.survivors J i)).card : ℝ) < u.quota / 8 * q)

theorem weight_nonneg (hL : ∀ s x, 0 ≤ u.factor s x) (J : Finset I) (x : V) :
    0 ≤ u.weight J x := by
  unfold weight rawWeight
  split
  · exact div_nonneg (Finset.prod_nonneg fun i _ => hL _ _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem mass_weight_le (J : Finset I) : mass (u.weight J) u.region ≤ 8 := by
  by_cases h : u.kept J
  · have he : u.weight J = u.rawWeight J := funext (fun x => by simp [weight, h])
    rw [he]
    exact h.2.2
  · simp [weight, h, mass]

theorem kept_mass_bad_eq (J : PositionGroup I q) :
    mass (u.weight J.val) (u.bad J) =
      if Disjoint u.revealed J.val then
        poorlyRetainedMass u.region u.factor u.retained u.singleFactor u.quota
          (fun _ => u.good J.val ∧ mass (u.rawWeight J.val) u.region ≤ 8)
          (u.outcome ∘ groupPosition J)
      else 0 := by
  classical
  let w := u.rawWeight J.val
  have he (x : V) :
      (∏ i, u.factor ((u.outcome ∘ groupPosition J) i) x) / u.region.card = w x := by
    rw [show (∏ i, u.factor ((u.outcome ∘ groupPosition J) i) x) =
      ∏ i ∈ J.val, u.factor (u.outcome i) x from groupPosition_prod J (fun i => u.factor (u.outcome i) x)]
    rfl
  have hcard (x : V) :
      (Finset.univ.filter (fun i => x ∈ u.survivors J i)) =
      ((Finset.univ.filter (fun i : Fin q =>
          mass w (u.retained ((u.outcome ∘ groupPosition J) i)) ≤
          16 * (↑(u.retained ((u.outcome ∘ groupPosition J) i)).card *
            u.singleFactor ((u.outcome ∘ groupPosition J) i) / ↑u.region.card))).filter
        (fun i => x ∈ u.retained ((u.outcome ∘ groupPosition J) i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    change (x ∈ (if mass w _ ≤ _ then _ else ∅)) ↔ _
    dsimp only [positionMass]
    by_cases hi : mass w (u.retained (u.outcome (groupPosition J i))) ≤
        16 * (↑(u.retained (u.outcome (groupPosition J i))).card *
          u.singleFactor (u.outcome (groupPosition J i)) / ↑u.region.card)
    · simp [hi]
    · simp [hi]
  by_cases hJ : Disjoint u.revealed J.val
  · by_cases hgood : u.good J.val ∧ mass (u.rawWeight J.val) u.region ≤ 8
    · have hk : u.kept J.val := ⟨hJ, hgood⟩
      have hw' : u.weight J.val = w := funext (fun x => by simp [w, weight, hk])
      simp only [hJ, ite_true, poorlyRetainedMass, he, hgood, hw', bad, hcard,
        true_and, show u.quota / 8 * (q : ℝ) = u.quota * q / 8 by ring]
    · have hk : ¬ u.kept J.val := fun h => hgood h.2
      simp only [hJ, ite_true, poorlyRetainedMass, he, w, hgood, ite_false]
      simp [weight, hk, mass]
  · have hk : ¬ u.kept J.val := fun h => hJ h.1
    simp [weight, hk, mass, hJ]

/-- Install the weights from the retained groups into the conditional
lower-overlap argument. -/
@[expose] noncomputable def overlapData (g : T → PositionGroup I q) (draw : T → Finset V) :
    CliqueOverlapData V (PositionGroup I q) T q where
  region := u.region
  groupWeight J := u.weight J.val
  badVertices := u.bad
  retained := u.survivors
  keptDraw ω := if u.kept (g ω).val then draw ω else ∅

theorem kept_draw_hit_le [Fintype T] [Nonempty (PositionGroup I q)]
    (ν : PositionGroup I q → FiniteLaw T) (draw : PositionGroup I q × T → Finset V)
    {K : ℝ} (hK : 0 ≤ K) (C : Finset V)
    (hMarg : ∀ J x, u.kept J.val →
      (ν J).event (fun ω => x ∈ draw (J, ω)) ≤ K * u.rawWeight J.val x) :
    ((FiniteLaw.uniform (PositionGroup I q)).staged ν).event
      (fun ω => ¬ Disjoint C ((u.overlapData Prod.fst draw).keptDraw ω)) ≤
      K * (FiniteLaw.uniform (PositionGroup I q)).mean (fun J => mass (u.weight J.val) C) := by
  let σ := FiniteLaw.uniform (PositionGroup I q)
  rw [FiniteLaw.staged_event, ← σ.mean_mul_const]
  apply σ.mean_mono
  intro J
  by_cases h : u.kept J.val
  · have he : u.weight J.val = u.rawWeight J.val := funext (fun x => by simp [weight, h])
    simp only [overlapData, h, ite_true, he]
    rw [mass, Finset.mul_sum]
    refine ((ν J).event_mono (Q := fun ω => ∃ x : ↥C, x.val ∈ draw (J, ω)) ?_).trans ?_
    · intro ω hw
      obtain ⟨x, hxc, hxω⟩ := Finset.not_disjoint_iff.mp hw
      exact ⟨⟨x, hxc⟩, hxω⟩
    · refine ((ν J).event_exists_le_sum (fun x : ↥C => fun ω => x.val ∈ draw (J, ω))).trans ?_
      rw [← Finset.sum_coe_sort C]
      exact Finset.sum_le_sum (fun x _ => hMarg J x h)
  · simp [overlapData, weight, h, mass, ← FiniteLaw.mean_indicator, FiniteLaw.mean_const]

end RetainedGroups
end LocallyRamsey
