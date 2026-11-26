module

public import LocallyRamsey.Lower.RetentionConcentration

public section

open scoped BigOperators

namespace LocallyRamsey.FiniteLaw

variable {I J Ω : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype Ω]

/-- Drawing a group and then drawing in it at every coordinate has the
same law as first drawing all the groups and then making the independent
within-group draws. -/
theorem mean_product_of_staged (μ : I → FiniteLaw J) (ν : I → J → FiniteLaw Ω)
    (X : (I → (J × Ω)) → ℝ) :
    (product (fun i => (μ i).staged (ν i))).mean X =
      (product μ).mean (fun g =>
        (product (fun i => ν i (g i))).mean (fun ω => X (fun i => (g i, ω i)))) := by
  classical
  let e : (I → (J × Ω)) ≃ (I → J) × (I → Ω) :=
    { toFun := fun u => (fun i => (u i).1, fun i => (u i).2)
      invFun := fun x i => (x.1 i, x.2 i)
      left_inv := fun u => funext (fun i => by simp)
      right_inv := fun x => by cases x; rfl }
  simp only [mean, Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun x : (I → J) × (I → Ω) =>
    (product μ).prob x.1 * ((product (fun i => ν i (x.1 i))).prob x.2 * X (fun i => (x.1 i, x.2 i))))]
  apply Fintype.sum_equiv e
  intro u
  change (∏ i, (μ i).prob (u i).1 * (ν i (u i).1).prob (u i).2) * X u =
    (∏ i, (μ i).prob (u i).1) * ((∏ i, (ν i (u i).1).prob (u i).2) * X (fun i => ((u i).1, (u i).2)))
  rw [Finset.prod_mul_distrib]
  simp only [Prod.eta, mul_assoc]

theorem event_product_of_staged (μ : I → FiniteLaw J) (ν : I → J → FiniteLaw Ω)
    (P : (I → (J × Ω)) → Prop) :
    (product (fun i => (μ i).staged (ν i))).event P =
      (product μ).mean (fun g =>
        (product (fun i => ν i (g i))).event (fun ω => P (fun i => (g i, ω i)))) := by
  classical
  rw [← mean_indicator, mean_product_of_staged]
  simp_rw [mean_indicator]

open Classical in
/-- The fraction of failed draws can be bounded just from its expected
value. The law of a coordinate may depend on common sampled data. -/
theorem event_many_failures_in_staged_draws {A : Type*} [Fintype A]
    (η : FiniteLaw A) (μ : A → I → FiniteLaw Ω)
    (fails : A → I → Ω → Prop) [∀ a i, DecidablePred (fails a i)]
    {p : ℝ} (h : ∀ i, (η.staged (fun a => μ a i)).event (fun a => fails a.1 i a.2) ≤ p)
    {T : ℝ} (hT : 0 < T) :
    let law := η.staged (fun a => product (μ a))
    law.event (fun x => T ≤ ∑ i, if fails x.1 i (x.2 i) then (1 : ℝ) else 0) ≤
      (Fintype.card I : ℝ) * p / T := by
  classical
  intro law
  let count (x : A × (I → Ω)) := ∑ i, if fails x.1 i (x.2 i) then (1 : ℝ) else 0
  refine (law.event_ge_le (X := count) (fun x => Finset.sum_nonneg (fun i _ => by
    split <;> norm_num)) hT).trans ?_
  apply div_le_div_of_nonneg_right _ hT.le
  change law.mean (fun x => ∑ i, if fails x.1 i (x.2 i) then (1 : ℝ) else 0) ≤ _
  rw [law.mean_sum]
  have he (i : I) : law.mean (fun x => if fails x.1 i (x.2 i) then (1 : ℝ) else 0) =
      (η.staged (fun a => μ a i)).event (fun a => fails a.1 i a.2) := by
    rw [← mean_indicator, staged_mean, staged_mean]
    congr 1
    funext a
    exact mean_coordinate (μ a) i (fun w => if fails a i w then 1 else 0)
  simp_rw [he]
  exact (Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp)


/-- Fill the positions exposed by a description and the positions left
unexposed. -/
@[expose] def fillPositions (A : Finset I)
    (e : {i // i ∈ A} → Ω) (fresh : {i // i ∉ A} → Ω) (i : I) : Ω :=
  if hi : i ∈ A then e ⟨i, hi⟩ else fresh ⟨i, hi⟩

/-- Groups can be chosen first, and the data they reveal can be exposed
before drawing the other samples. The samples outside the exposed
groups retain their original independent laws. -/
theorem event_split_exposed_positions {T : Type*} [Fintype T] (σ : FiniteLaw J)
    (μ : I → FiniteLaw Ω) (active : J → Finset I)
    (ν : (g : J) → ({i // i ∈ active g} → Ω) → FiniteLaw T)
    (P : J → (I → Ω) → T → Prop) :
    (σ.staged (fun g => (product μ).staged
      (fun ω => ν g (fun i => ω i.val)))).event (fun z => P z.1 z.2.1 z.2.2) =
    σ.mean (fun g => (product (fun i : {i // i ∈ active g} => μ i.val)).mean (fun e =>
      (ν g e).mean (fun t => (product (fun i : {i // i ∉ active g} => μ i.val)).event
        (fun fresh => P g (fillPositions (active g) e fresh) t)))) := by
  classical
  rw [σ.staged_event]
  congr 1
  funext g
  rw [staged_event]
  let reveal (e : {i // i ∈ active g} → Ω) (fresh : {i // i ∉ active g} → Ω) :=
    (ν g e).event (fun t => P g (fillPositions (active g) e fresh) t)
  have he (ω : I → Ω) : fillPositions (active g) (fun i => ω i.val) (fun i => ω i.val) = ω := by
    funext i
    by_cases hi : i ∈ active g <;> simp [fillPositions, hi]
  have hmean := mean_split_revealed μ (active g) (fun y => reveal y.1 y.2)
  simp only [reveal, he, staged_mean] at hmean
  rw [hmean]
  congr 1
  funext e
  simp_rw [← (ν g e).mean_indicator, ← (product (fun i : {i // i ∉ active g} => μ i.val)).mean_indicator]
  exact mean_mean_comm _ _ _

/-- A uniform bound after fixing the data of a description holds before
any of the data was exposed. -/
theorem event_exposed_positions_le {T : Type*} [Fintype T] (σ : FiniteLaw J)
    (μ : I → FiniteLaw Ω) (active : J → Finset I)
    (ν : (g : J) → ({i // i ∈ active g} → Ω) → FiniteLaw T)
    (P : J → (I → Ω) → T → Prop) {c : ℝ}
    (h : ∀ g e t, (product (fun i : {i // i ∉ active g} => μ i.val)).event
        (fun fresh => P g (fillPositions (active g) e fresh) t) ≤ c) :
    (σ.staged (fun g => (product μ).staged
      (fun ω => ν g (fun i => ω i.val)))).event (fun z => P z.1 z.2.1 z.2.2) ≤ c := by
  rw [event_split_exposed_positions]
  refine (σ.mean_mono (Y := fun _ => c) (fun g => ?_)).trans_eq (σ.mean_const c)
  let law := product (fun i : {i // i ∈ active g} => μ i.val)
  refine (law.mean_mono (Y := fun _ => c) (fun e => ?_)).trans_eq (law.mean_const c)
  exact ((ν g e).mean_mono (h g e)).trans_eq ((ν g e).mean_const c)


/-- The vertex list and the group choices are independent given the
original samples. They can be integrated in either order even though the
law of each within-group draw depends on both. -/
theorem event_list_after_groups {A T : Type*} [Fintype A] [Fintype T]
    (η : FiniteLaw A) (ξ : FiniteLaw T) (σ : FiniteLaw J)
    (μ : A → T → J → FiniteLaw Ω) (P : A → T → (I → J × Ω) → Prop) :
    (η.staged (fun x => ξ.staged (fun L =>
      product (fun _ : I => σ.staged (μ x L))))).event (fun z => P z.1 z.2.1 z.2.2) =
      η.mean (fun x => (product (fun _ : I => σ)).mean (fun g =>
        (ξ.staged (fun L => product (fun i => μ x L (g i)))).event
          (fun z => P x z.1 (fun i => (g i, z.2 i))))) := by
  classical
  rw [η.staged_event]
  congr 1
  funext x
  rw [ξ.staged_event]
  simp_rw [event_product_of_staged (fun _ : I => σ), ξ.staged_event]
  exact mean_mean_comm _ _ _

end LocallyRamsey.FiniteLaw
