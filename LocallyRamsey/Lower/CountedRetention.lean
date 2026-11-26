module

public import LocallyRamsey.Lower.RetentionConcentration
public import LocallyRamsey.Lower.IntersectionDensity

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- After fixing the sample and retained set at a position, the other
samples multiply its weight by the intersection density in the retained
set. This bounds the expected loss from the position's weight test. -/
theorem mean_rejected_first_position (μ : FiniteLaw Ω) (W B : Finset V)
    (hBW : B ⊆ W) (L : Ω → V → ℝ) (hL0 : ∀ s x, 0 ≤ L s x)
    (hL1 : ∀ x ∈ W, μ.mean (fun s => L s x) = 1)
    (F T : Ω → Finset V) (c : Ω → ℝ)
    (hFB : ∀ s, F s ⊆ B) (hFT : ∀ s, F s ⊆ T s)
    (hrow : ∀ s x, x ∈ W → L s x = if x ∈ T s then c s else 0)
    (hT : ∀ s, T s ⊆ W) (hc : ∀ s, 0 ≤ c s)
    {q : ℕ} (good : (Fin (q + 1) → Ω) → Prop) [DecidablePred good]
    (enabled : Ω → Prop) [DecidablePred enabled]
    (hEnable : ∀ s ω, good (Fin.cons (α := fun _ => Ω) s ω) → enabled s)
    (hGood : ∀ s ω, good (Fin.cons (α := fun _ => Ω) s ω) → intersectionDensity L (T s) ω ≤ 2)
    {τ ε γ : ℝ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hmean : μ.mean (fun s => (F s).card * c s / B.card) ≤ γ)
    (hClose : ∀ s, enabled s → (F s).card * c s / B.card ≤ τ ∨
      rootDistance (FiniteLaw.product (fun _ : Fin q => μ))
        (intersectionDensity L (F s)) (intersectionDensity L (T s)) ≤ 2 * ε) :
    let z (s : Ω) := (F s).card * c s / B.card
    let weight (ω : Fin (q + 1) → Ω) := fun x => (∏ i, L (ω i) x) / B.card
    (FiniteLaw.product (fun _ : Fin (q + 1) => μ)).mean (fun ω =>
      if good ω ∧ 16 * z (ω 0) < mass (weight ω) (F (ω 0))
      then mass (weight ω) (F (ω 0)) else 0) ≤ τ + 8 * ε * γ := by
  classical
  intro z weight
  rw [FiniteLaw.mean_split_first]
  let ν := FiniteLaw.product (fun _ : Fin q => μ)
  have hMass (s : Ω) (ω : Fin q → Ω) :
      mass (weight (Fin.cons (α := fun _ => Ω) s ω)) (F s) = z s * intersectionDensity L (F s) ω := by
    have he (x : V) (hx : x ∈ F s) :
        (∏ i : Fin (q + 1), L ((Fin.cons (α := fun _ => Ω) s ω) i) x) = c s * ∏ i, L (ω i) x := by
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hrow s x (hBW (hFB s hx)), hFT s hx, ite_true]
    simp only [mass, weight, ← Finset.sum_div, Finset.sum_congr rfl he, ← Finset.mul_sum,
      intersectionDensity, z]
    by_cases hF : F s = ∅
    · simp [hF]
    · have hn : ((F s).card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hF)
      by_cases hB : (B.card : ℝ) = 0
      · simp [hB]
      · field_simp
  have hBound (s : Ω) : ν.mean (fun ω =>
      if good (Fin.cons (α := fun _ => Ω) s ω) ∧ 16 * z s < z s * intersectionDensity L (F s) ω
      then z s * intersectionDensity L (F s) ω else 0) ≤ τ + 8 * ε * z s := by
    have hz : 0 ≤ z s := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hc s)) (Nat.cast_nonneg _)
    by_cases hs : enabled s
    · by_cases hf : (F s).Nonempty
      · exact mean_discarded_position_le ν (intersectionDensity L (F s)) (intersectionDensity L (T s))
          (intersectionDensity_nonneg L hL0 _) (intersectionDensity_nonneg L hL0 _)
          (mean_intersectionDensity μ L (F s) hf (fun x hx => hL1 x (hBW (hFB s hx))) q)
          (fun ω => good (Fin.cons (α := fun _ => Ω) s ω)) (hGood s) hz hτ hε (hClose s hs)
      · have he := Finset.not_nonempty_iff_eq_empty.mp hf
        have hz' : z s = 0 := by simp [z, he]
        simp [hz', ν.mean_const, hτ]
    · have hno (ω : Fin q → Ω) : ¬ good (Fin.cons (α := fun _ => Ω) s ω) := fun hg => hs (hEnable s ω hg)
      simpa [hno, ν.mean_const] using add_nonneg hτ (mul_nonneg (by positivity) hz)
  simp only [Fin.cons_zero, hMass]
  refine (μ.mean_mono hBound).trans ?_
  rw [μ.mean_add, μ.mean_const, μ.mean_mul_const]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hmean (by positivity : (0 : ℝ) ≤ 8 * ε)) τ


/-- In a kept group the poorly retained mass is bounded by the mass
already poorly retained before the tests, plus the expected losses
at the individual positions divided by the number of losses required
to make a previously frequent vertex infrequent. -/
theorem mean_counted_group_loss (μ : FiniteLaw Ω) (W B : Finset V)
    (hBW : B ⊆ W) (L : Ω → V → ℝ) (hL0 : ∀ s x, 0 ≤ L s x)
    (hL1 : ∀ x ∈ W, μ.mean (fun s => L s x) = 1)
    (F T : Ω → Finset V) (c : Ω → ℝ)
    (hFB : ∀ s, F s ⊆ B) (hFT : ∀ s, F s ⊆ T s)
    (hrow : ∀ s x, x ∈ W → L s x = if x ∈ T s then c s else 0)
    (hT : ∀ s, T s ⊆ W) (hc : ∀ s, 0 ≤ c s)
    {q : ℕ} (good : (Fin (q + 1) → Ω) → Prop) [DecidablePred good]
    (hSymm : ∀ (π : Equiv.Perm (Fin (q + 1))) (ω : Fin (q + 1) → Ω), good (ω ∘ π) ↔ good ω)
    (enabled : Ω → Prop) [DecidablePred enabled]
    (hEnable : ∀ s ω, good (Fin.cons (α := fun _ => Ω) s ω) → enabled s)
    (hGood : ∀ s ω, good (Fin.cons (α := fun _ => Ω) s ω) → intersectionDensity L (T s) ω ≤ 2)
    {τ ε γ initial : ℝ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hmean : μ.mean (fun s => (F s).card * c s / B.card) ≤ γ)
    (hClose : ∀ s, enabled s → (F s).card * c s / B.card ≤ τ ∨
      rootDistance (FiniteLaw.product (fun _ : Fin q => μ))
        (intersectionDensity L (F s)) (intersectionDensity L (T s)) ≤ 2 * ε)
    (hInit : (FiniteLaw.product (fun _ : Fin (q + 1) => μ)).mean (fun ω =>
      (∑ x ∈ B, (∏ i, L (ω i) x) *
        (if ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * (q + 1) / 4
          then 1 else 0)) / B.card) ≤ initial) :
    let z (s : Ω) := (F s).card * c s / B.card
    let weight (ω : Fin (q + 1) → Ω) := fun x => (∏ i, L (ω i) x) / B.card
    let counted (ω : Fin (q + 1) → Ω) :=
      Finset.univ.filter (fun i => mass (weight ω) (F (ω i)) ≤ 16 * z (ω i))
    (FiniteLaw.product (fun _ : Fin (q + 1) => μ)).mean (fun ω =>
      if good ω then mass (weight ω) (B.filter fun x =>
        (((counted ω).filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * (q + 1) / 8) else 0) ≤
      initial + (q + 1) * (τ + 8 * ε * γ) / (γ * (q + 1) / 8) := by
  classical
  intro z weight counted
  let ν := FiniteLaw.product (fun _ : Fin (q + 1) => μ)
  let loss (i : Fin (q + 1)) (ω : Fin (q + 1) → Ω) :=
    if good ω ∧ 16 * z (ω i) < mass (weight ω) (F (ω i)) then mass (weight ω) (F (ω i)) else 0
  have hw (ω : Fin (q + 1) → Ω) (x : V) : 0 ≤ weight ω x :=
    div_nonneg (Finset.prod_nonneg fun i _ => hL0 (ω i) x) (Nat.cast_nonneg _)
  have h0 : ν.mean (loss 0) ≤ τ + 8 * ε * γ :=
    mean_rejected_first_position μ W B hBW L hL0 hL1 F T c hFB hFT hrow hT hc
      good enabled hEnable hGood hτ hε hmean hClose
  have hswap (i : Fin (q + 1)) : ν.mean (loss i) = ν.mean (loss 0) := by
    let π := Equiv.swap (0 : Fin (q + 1)) i
    have hp : π 0 = i := Equiv.swap_apply_left _ _
    have he (ω : Fin (q + 1) → Ω) : weight (ω ∘ π) = weight ω := by
      funext x
      dsimp [weight, Function.comp_apply]
      congr 1
      exact Fintype.prod_equiv π (fun j => L (ω (π j)) x)
        (fun j => L (ω j) x) (fun _ => rfl)
    have htest (ω : Fin (q + 1) → Ω) : loss i ω = loss 0 (ω ∘ π) := by
      simp only [loss, hSymm, Function.comp_apply, hp, he]
    rw [show loss i = fun ω => loss 0 (ω ∘ π) from funext htest]
    exact FiniteLaw.mean_injective_projection μ π π.injective (loss 0)
  have hCount (ω : Fin (q + 1) → Ω) (i : Fin (q + 1)) :
      i ∉ counted ω ↔ 16 * z (ω i) < mass (weight ω) (F (ω i)) := by
    simp [counted, not_le]
  have hLoss (i : Fin (q + 1)) : ν.mean (fun ω =>
      if good ω ∧ i ∉ counted ω then mass (weight ω) (B ∩ F (ω i)) else 0) ≤ τ + 8 * ε * γ := by
    simp only [hCount, fun (ω : Fin (q + 1) → Ω) => Finset.inter_eq_right.mpr (hFB (ω i))]
    exact (hswap i).trans_le h0
  have hI : ν.mean (fun ω => mass (weight ω) (B.filter (fun x =>
      ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < 2 * (γ * (q + 1) / 8)))) ≤ initial := by
    have hEq (ω : Fin (q + 1) → Ω) :
        mass (weight ω) (B.filter (fun x => ((Finset.univ.filter (fun i =>
          x ∈ F (ω i))).card : ℝ) < 2 * (γ * (q + 1) / 8))) =
        (∑ x ∈ B, (∏ i, L (ω i) x) *
          (if ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * (q + 1) / 4
            then 1 else 0)) / B.card := by
      rw [show 2 * (γ * (q + 1) / 8) = γ * (q + 1) / 4 by ring]
      unfold mass
      rw [Finset.sum_filter, Finset.sum_div]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      dsimp [weight]
      split <;> simp_all
    simp_rw [hEq]
    exact hInit
  simpa only [Nat.cast_succ] using mean_weight_after_position_tests_le ν B weight hw
    (fun ω i => F (ω i)) good counted (show 0 < γ * (q + 1) / 8 by positivity) hI hLoss


end LocallyRamsey
