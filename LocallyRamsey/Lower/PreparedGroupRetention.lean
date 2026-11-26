module

public import LocallyRamsey.Lower.PreparedPositions
public import LocallyRamsey.Lower.CountedRetention
public import LocallyRamsey.Lower.GoodIntersections

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Extra choices at each position affect which vertices are retained,
but leave a comparison between the sample densities unchanged. -/
theorem rootDistance_product_staged (π : FiniteLaw (Finset V))
    (ν : Finset V → FiniteLaw (Finset V)) (L : Finset V → V → ℝ)
    (A B : Finset V) (q : ℕ) :
    rootDistance (FiniteLaw.product (fun _ : Fin q => π.staged ν))
      (intersectionDensity (fun s : Finset V × Finset V => L s.1) A)
      (intersectionDensity (fun s : Finset V × Finset V => L s.1) B) =
    rootDistance (FiniteLaw.product (fun _ : Fin q => π))
      (intersectionDensity L A) (intersectionDensity L B) := by
  rw [rootDistance, rootDistance, FiniteLaw.mean_product_of_staged]
  congr 1
  funext ω
  exact (FiniteLaw.product (fun i : Fin q => ν (ω i))).mean_const
    ((√(intersectionDensity L A ω) - √(intersectionDensity L B ω)) ^ 2)

/-- A group passes the density tests exactly when its intersection
has comparable weight to the original region and its samples all have
the required minimum density. -/
@[expose] def goodPositionGroup {Ω : Type*} [Fintype Ω]
    (W : Finset V) (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)]
    {q : ℕ} (ρ : ℝ) (ω : Fin q → Ω) : Prop :=
  1 / 2 ≤ intersectionDensity (sampleWeight W contains) W ω ∧
  intersectionDensity (sampleWeight W contains) W ω ≤ 2 ∧
  ∀ i, ρ ≤ sampleDensity W contains (ω i)

@[expose] def keptPositionGroup {Ω : Type*} [Fintype Ω]
    (W B : Finset V) (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)]
    {q : ℕ} (ρ : ℝ) (ω : Fin q → Ω) : Prop :=
  goodPositionGroup W contains ρ ω ∧ intersectionDensity (sampleWeight W contains) B ω ≤ 8

/-- The weight in a kept group of vertices appearing in too few
counted positions. Positions are counted only at bounded total weight. -/
@[expose] noncomputable def poorlyRetainedMass {Ω : Type*} [Fintype Ω]
    (B : Finset V) (L : Ω → V → ℝ) (F : Ω → Finset V) (c : Ω → ℝ)
    {q : ℕ} (γ : ℝ) (kept : (Fin q → Ω) → Prop) (ω : Fin q → Ω) : ℝ := by
  classical
  let w (x : V) := (∏ i, L (ω i) x) / B.card
  let counted := Finset.univ.filter (fun i => mass w (F (ω i)) ≤ 16 * ((F (ω i)).card * c (ω i) / B.card))
  exact if kept ω then mass w (B.filter fun x =>
    ((counted.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * q / 8) else 0

set_option maxHeartbeats 1000000 in
/-- The probability of rejecting a good group and the mean weight lost
in a kept group satisfy the two estimates needed after fixing a
description. The size lower bounds identify exactly which sets may
use the stabilized density comparison. -/
theorem prepared_group_retention (W B : Finset V) (hW : W.Nonempty) (hBW : B ⊆ W)
    (π : FiniteLaw (Finset V)) (ν : Finset V → FiniteLaw (Finset V))
    (F : Finset V × Finset V → Finset V) (hF : ∀ s, F s ⊆ B ∧ F s ⊆ s.1)
    {k : ℕ} {ρ γ ε δ small initial : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hB : δ ≤ B.card) (hδW : δ ≤ ρ * W.card)
    (hsmall : δ / (ρ * B.card) ≤ small)
    (hεγ : ε ≤ γ / 4)
    (hBudget : initial + (8 * small / γ + 64 * ε) ≤ γ / 32)
    (hWeight : ∀ x ∈ W, π.mean (fun S => sampleWeight W (fun S x => x ∈ S) S x) = 1)
    (hClose : let L := sampleWeight W (fun (S : Finset V) x => x ∈ S)
      ∀ j ≤ k + 1, ∀ U T : Finset V, U ⊆ W → T ⊆ W → δ ≤ U.card → δ ≤ T.card →
      rootDistance (FiniteLaw.product (fun _ : Fin j => π))
        (intersectionDensity L U) (intersectionDensity L T) ≤ 2 * ε)
    (hMean : let c (s : Finset V × Finset V) := (sampleDensity W (fun S x => x ∈ S) s.1)⁻¹
      (π.staged ν).mean (fun s => (F s).card * c s / B.card) ≤ γ)
    (hInit : let L (s : Finset V × Finset V) := sampleWeight W (fun S x => x ∈ S) s.1
      (FiniteLaw.product (fun _ : Fin (k + 1) => π.staged ν)).mean (fun ω =>
        (∑ x ∈ B, (∏ i, L (ω i) x) *
          (if ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * (k + 1) / 4
            then 1 else 0)) / B.card) ≤ initial) :
    let contains (S : Finset V) x := x ∈ S
    let L (s : Finset V × Finset V) := sampleWeight W contains s.1
    let c (s : Finset V × Finset V) := (sampleDensity W contains s.1)⁻¹
    let good (ω : Fin (k + 1) → Finset V × Finset V) := goodPositionGroup W contains ρ (Prod.fst ∘ ω)
    let kept (ω : Fin (k + 1) → Finset V × Finset V) := keptPositionGroup W B contains ρ (Prod.fst ∘ ω)
    let loss := poorlyRetainedMass B L F c γ kept
    ((FiniteLaw.product (fun _ : Fin (k + 1) => π.staged ν)).event
      (fun ω => good ω ∧ 8 < intersectionDensity L B ω) ≤ γ / 4) ∧
    (∀ ω, loss ω ∈ Set.Icc (0 : ℝ) 8) ∧
    (FiniteLaw.product (fun _ : Fin (k + 1) => π.staged ν)).mean loss ≤ γ / 32 := by
  classical
  intro contains L c good kept loss
  let μ := π.staged ν
  let T (s : Finset V × Finset V) := W.filter (fun x => x ∈ s.1)
  let enabled (s : Finset V × Finset V) := ρ ≤ sampleDensity W contains s.1
  have hB0 : (0 : ℝ) < B.card := hδ.trans_le hB
  have hBne : B.Nonempty := Finset.card_pos.mp (by exact_mod_cast hB0)
  have hδW' : δ ≤ (W.card : ℝ) := hB.trans (by exact_mod_cast Finset.card_le_card hBW)
  have hc (s : Finset V × Finset V) : 0 ≤ c s :=
    inv_nonneg.mpr (sampleDensity_nonneg _ _ _)
  have hrow (s : Finset V × Finset V) (x : V) (hx : x ∈ W) :
      L s x = if x ∈ T s then c s else 0 := by
    by_cases h : x ∈ s.1 <;> simp [L, T, c, contains, sampleWeight, hx, h, one_div]
  have hL0 (s : Finset V × Finset V) (x : V) : 0 ≤ L s x := by
    by_cases h : x ∈ s.1 <;> simp [L, c, sampleWeight, contains, h, one_div, hc s]
  have hL1 (x : V) (hx : x ∈ W) : μ.mean (fun s => L s x) = 1 := by
    rw [show μ = π.staged ν from rfl, FiniteLaw.staged_mean]
    have he (S : Finset V) : (ν S).mean (fun _ => L (S, ∅) x) = L (S, ∅) x :=
      (ν S).mean_const _
    change (π.mean fun S => (ν S).mean (fun _ => L (S, ∅) x)) = 1
    simp_rw [he]
    exact hWeight x hx
  have hT (s : Finset V × Finset V) : T s ⊆ W := Finset.filter_subset _ _
  have hFT (s : Finset V × Finset V) : F s ⊆ T s := fun x hx =>
    Finset.mem_filter.mpr ⟨hBW ((hF s).1 hx), (hF s).2 hx⟩
  have hDist (j : ℕ) (hj : j ≤ k + 1) (U T' : Finset V) (hU : U ⊆ W) (hT' : T' ⊆ W)
      (hUc : δ ≤ U.card) (hTc : δ ≤ T'.card) :
      rootDistance (FiniteLaw.product (fun _ : Fin j => μ))
        (intersectionDensity L U) (intersectionDensity L T') ≤ 2 * ε := by
    rw [rootDistance_product_staged]
    exact hClose j hj U T' hU hT' hUc hTc
  have hClose' (s : Finset V × Finset V) (hs : enabled s) :
      (F s).card * c s / B.card ≤ small ∨
      rootDistance (FiniteLaw.product (fun _ : Fin k => μ))
        (intersectionDensity L (F s)) (intersectionDensity L (T s)) ≤ 2 * ε := by
    by_cases hlarge : δ ≤ ((F s).card : ℝ)
    · right
      refine hDist k (Nat.le_succ _) _ _ ((hF s).1.trans hBW) (hT s) hlarge ?_
      have he : sampleDensity W contains s.1 * W.card = (T s).card := by
        unfold sampleDensity
        rw [div_mul_cancel₀ _ (by exact_mod_cast hW.card_ne_zero)]
        simp only [contains, T, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [← he]
      exact hδW.trans (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))
    · left
      have hcs : c s ≤ ρ⁻¹ := inv_anti₀ hρ hs
      refine le_trans ?_ hsmall
      rw [← div_div, div_eq_mul_inv δ ρ]
      apply div_le_div_of_nonneg_right _ hB0.le
      exact mul_le_mul (le_of_not_ge hlarge) hcs (hc s) hδ.le
  have hSymm (e : Equiv.Perm (Fin (k + 1))) (ω : Fin (k + 1) → Finset V × Finset V) :
      kept (ω ∘ e) ↔ kept ω := by
    have he (A : Finset V) : intersectionDensity L A (ω ∘ e) = intersectionDensity L A ω := by
      unfold intersectionDensity
      congr 1
      exact Finset.sum_congr rfl (fun x _ =>
        Fintype.prod_equiv e (fun i => L (ω (e i)) x) (fun i => L (ω i) x) (fun _ => rfl))
    have hr : (∀ i, ρ ≤ sampleDensity W contains ((ω ∘ e) i).1) ↔
        ∀ i, ρ ≤ sampleDensity W contains (ω i).1 :=
      (e.surjective.forall (p := fun i => ρ ≤ sampleDensity W contains (ω i).1)).symm
    change (1 / 2 ≤ intersectionDensity L W (ω ∘ e) ∧
      intersectionDensity L W (ω ∘ e) ≤ 2 ∧ (∀ i, ρ ≤ sampleDensity W contains ((ω ∘ e) i).1)) ∧
      intersectionDensity L B (ω ∘ e) ≤ 8 ↔ _
    rw [he W, he B, hr]
    rfl
  have hEnable (s : Finset V × Finset V) (ω : Fin k → Finset V × Finset V)
      (hg : kept (Fin.cons s ω)) : enabled s := hg.1.2.2 0
  have hGood (s : Finset V × Finset V) (ω : Fin k → Finset V × Finset V)
      (hg : kept (Fin.cons s ω)) : intersectionDensity L (T s) ω ≤ 2 := by
    have he : Prod.fst ∘ Fin.cons s ω = Fin.cons s.1 (Prod.fst ∘ ω) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have htest' := hg.1.2.1
    change intersectionDensity (sampleWeight W contains) W (Prod.fst ∘ Fin.cons s ω) ≤ 2 at htest'
    rw [he, intersectionDensity_cons_sample] at htest'
    exact htest'
  have hsmall0 : 0 ≤ small := (by positivity : 0 ≤ δ / (ρ * B.card)).trans hsmall
  refine ⟨?_, ?_, ?_⟩
  · exact (event_reject_group_le (FiniteLaw.product (fun _ : Fin (k + 1) => μ))
      (intersectionDensity L B) (intersectionDensity L W)
      (intersectionDensity_nonneg L hL0 _) (intersectionDensity_nonneg L hL0 _)
      (mean_intersectionDensity μ L B hBne (fun x hx => hL1 x (hBW hx)) _)
      good (fun ω h => h.2.1) (hDist _ le_rfl B W hBW (by rfl) hB hδW')).trans hεγ
  · intro ω
    by_cases h : kept ω
    · simp only [loss, poorlyRetainedMass, h, ite_true]
      have hw (x : V) : 0 ≤ (∏ i, L (ω i) x) / B.card :=
        div_nonneg (Finset.prod_nonneg fun i _ => hL0 (ω i) x) hB0.le
      refine ⟨Finset.sum_nonneg (fun x _ => hw x), ?_⟩
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => hw x)).trans ?_
      rw [← Finset.sum_div]
      exact h.2
    · simp [loss, poorlyRetainedMass, h, Set.mem_Icc]
  · have h := mean_counted_group_loss μ W B hBW L hL0 hL1 F T c
      (fun s => (hF s).1) hFT hrow hT hc kept hSymm enabled hEnable hGood
      hsmall0 hε hγ hMean hClose' hInit
    have he : ((k : ℝ) + 1) * (small + 8 * ε * γ) / (γ * ((k : ℝ) + 1) / 8) =
        8 * small / γ + 64 * ε := by
      have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      <;> ring
    rw [he] at h
    apply le_trans _ hBudget
    convert h using 1
    apply congrArg (FiniteLaw.mean _)
    funext ω
    by_cases hg : kept ω <;> simp [loss, poorlyRetainedMass, hg]

end LocallyRamsey
