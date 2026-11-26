module

public import LocallyRamsey.Lower.GroupDrawRule

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option maxHeartbeats 1200000 in
/-- The actual draw laws for the biased group experiment. The law adds
vertices after drawing a group, with a marginal bound proportional to
its intersection weight. -/
theorem exists_biased_group_draws (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hW : W.Nonempty) (π : FiniteLaw (Finset V))
    {q h m d k b N degreeCap : ℕ} (hq : 0 < q) (hh : 0 < h) (hb : 0 < b)
    {τ γ density δ minSize : ℝ} (hτ : 0 < τ) (hdensity : 0 ≤ density)
    (hγ : 0 ≤ γ) (hdensityγ : 8 * density ≤ γ) (hminSize : 0 < minSize)
    (hSupply : ∀ C : Finset V, C ⊆ W → k ≤ C.card →
      ∃ P : Finset V, P ⊆ C ∧ P.card = b ∧ Gᶜ.IsClique (P : Set V))
    (hDegree : ∀ x ∈ W, ((W.filter (G.Adj x)).card : ℝ) ≤ density * W.card)
    (hSize : minSize ≤ (W.card : ℝ) * τ ^ q / 2)
    (hSig : (((m + 1) ^ d * k * 4 : ℕ) : ℝ) ≤ minSize)
    (hWeight : ∀ x ∈ W, π.mean (fun S => sampleWeight W (fun S x => x ∈ S) S x) = 1)
    (hGood : let L := sampleWeight W (fun (S : Finset V) x => x ∈ S)
      (FiniteLaw.product (fun _ : Fin q => π)).event (fun z =>
        ¬((1 : ℝ) / 2 ≤ intersectionDensity L W z ∧ intersectionDensity L W z ≤ 2 ∧
          ∀ i, τ ≤ sampleDensity W (fun S x => x ∈ S) (z i))) ≤ δ) :
    letI : Nonempty ↥W := hW.to_subtype
    let I := Fin (q * h)
    let groups := (Finset.univ : Finset I).powersetCard q
    letI : Nonempty ↥groups := (Finset.powersetCard_nonempty.mpr (by
      simp only [Finset.card_univ, Fintype.card_fin, I]
      exact Nat.le_mul_of_pos_right q hh)).to_subtype
    let η := FiniteLaw.product (fun _ : I => π)
    let ξ := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
    let σ := FiniteLaw.uniform ↥groups
    let L := sampleWeight W (fun (S : Finset V) x => x ∈ S)
    let byPosition (z : I → Finset V) (J : ↥groups) (i : Fin q) :=
      z ((Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm i).val
    let Y (z : Fin q → Finset V) := intersectionDensity L W z
    let good (z : I → Finset V) (J : ↥groups) :=
      (1 : ℝ) / 2 ≤ Y (byPosition z J) ∧ Y (byPosition z J) ≤ 2 ∧
      ∀ i, τ ≤ sampleDensity W (fun S x => x ∈ S) (byPosition z J i)
    let C (z : I → Finset V) (J : ↥groups) := W.filter (fun x => ∀ i, x ∈ byPosition z J i)
    ∃ (ν : (I → Finset V) → (Fin m → ↥W) → ↥groups → FiniteLaw (Finset V))
      (draw : (I → Finset V) → (Fin m → ↥W) → ↥groups → Finset V → Finset V)
      (marginal : (I → Finset V) → ↥groups → V → ℝ),
      (∀ z list J S, draw z list J S ⊆ W ∧ Gᶜ.IsClique (draw z list J S : Set V) ∧
        (draw z list J S = ∅ ∨ good z J ∧ (draw z list J S).card = b)) ∧
      (∀ z list J x, (ν z list J).event (fun S => x ∈ draw z list J S) ≤ marginal z J x) ∧
      (∀ z J x, 0 ≤ marginal z J x ∧ marginal z J x ≤ 2 * b / minSize ∧
        (good z J → marginal z J x ≤
          4 * b * (∏ i, L (byPosition z J i) x) / W.card)) ∧
      (∀ z J, ∑ x, marginal z J x ≤ 2 * b) ∧
      (η.staged (fun a => ξ.staged (fun list => σ.staged (ν a list)))).event
        (fun z => draw z.1 z.2.1 z.2.2.1 z.2.2.2 = ∅) ≤
        δ + 4 * Real.exp ((m : ℝ) * density - Real.log 2 * d) ∧
      (η.staged (fun a => ξ.staged (fun list => FiniteLaw.product
        (fun _ : Fin N => σ.staged (ν a list))))).event
        (fun z => ∃ j : Fin m, degreeCap < ((Finset.univ : Finset (Fin N)).filter
          (fun i => ∃ x ∈ draw z.1 z.2.1 (z.2.2 i).1 (z.2.2 i).2, G.Adj (z.2.1 j).val x)).card) ≤
        (m : ℝ) * (Real.exp (-(h * γ) / 2) + Real.exp (2 * (N : ℝ) * γ - Real.log 2 * degreeCap)) ∧
      (∀ z z' list (J : ↥groups), (∀ i ∈ J.val, z i = z' i) →
        ν z list J = ν z' list J ∧ draw z list J = draw z' list J) := by
  let _ : Nonempty ↥W := hW.to_subtype
  intro I groups η ξ σ L byPosition Y good C
  let marginal (z : I → Finset V) (J : ↥groups) (x : V) :=
    if good z J ∧ x ∈ C z J then 2 * (b : ℝ) / (C z J).card else 0
  let _ : Nonempty ↥groups := (Finset.powersetCard_nonempty.mpr (by
    simp only [Finset.card_univ, Fintype.card_fin, I]
    exact Nat.le_mul_of_pos_right q hh)).to_subtype
  have hC (z : I → Finset V) (J : ↥groups) : C z J ⊆ W := Finset.filter_subset _ _
  have hCS (z : I → Finset V) (J : ↥groups) (hg : good z J) : minSize ≤ ((C z J).card : ℝ) :=
    hSize.trans (good_intersection_support W hW (fun S x => x ∈ S) (byPosition z J) hτ hg.2.2 hg.1).1
  have hNe (z : I → Finset V) (J : ↥groups) (hg : good z J) : (C z J).Nonempty :=
    Finset.card_pos.mp (by exact_mod_cast hminSize.trans_le (hCS z J hg))
  have hNum (z : I → Finset V) (J : ↥groups) (hg : good z J) :
      (m + 1) ^ d * k * 4 ≤ (C z J).card := by exact_mod_cast hSig.trans (hCS z J hg)
  have hG' (J : ↥groups) : η.event (fun z => ¬good z J) ≤ δ := by
    let f (i : Fin q) := ((Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm i).val
    have hf : Function.Injective f := Subtype.val_injective.comp
      (Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm.injective
    change (FiniteLaw.product (fun _ : I => π)).event (fun z =>
      ¬((1 : ℝ) / 2 ≤ Y (z ∘ f) ∧ Y (z ∘ f) ≤ 2 ∧
        ∀ i, τ ≤ sampleDensity W (fun S x => x ∈ S) ((z ∘ f) i))) ≤ δ
    rw [FiniteLaw.event_injective_projection π f hf (fun z => ¬((1 : ℝ) / 2 ≤ Y z ∧ Y z ≤ 2 ∧
      ∀ i, τ ≤ sampleDensity W (fun S x => x ∈ S) (z i)))]
    exact hGood
  obtain ⟨ν, draw, hD, hMarg, hAdj, hTotal, hEmpty, hLocal⟩ := exists_group_draw_rule G W hW η σ
    hb C good hC hNe hNum hSupply hdensity hDegree hG'
  refine ⟨ν, draw, marginal, ?_, ?_, ?_, ?_, hEmpty, ?_, ?_⟩
  · intro z list J S
    obtain ⟨hs, hi, hb⟩ := hD z list J S
    exact ⟨hs.trans (hC z J), hi, hb⟩
  · intro z list J x
    have hm := hMarg z list J x
    by_cases hx : good z J ∧ x ∈ C z J <;> simpa only [marginal, hx, if_true, if_false] using hm
  · intro z J x
    have hb0 : 0 ≤ 2 * (b : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    have hn0 : 0 ≤ 2 * (b : ℝ) / minSize := div_nonneg hb0 hminSize.le
    by_cases hx : good z J ∧ x ∈ C z J
    · rw [show marginal z J x = 2 * (b : ℝ) / (C z J).card by simp [marginal, hx]]
      refine ⟨div_nonneg hb0 (Nat.cast_nonneg _),
        div_le_div_of_nonneg_left hb0 hminSize (hCS z J hx.1), fun hg => ?_⟩
      have hP := (good_intersection_support W hW (fun S x => x ∈ S)
        (byPosition z J) hτ hg.2.2 hg.1).2 x hx.2
      have h := mul_le_mul_of_nonneg_left hP hb0
      convert h using 1 <;> dsimp only [L, C] <;> ring
    · rw [show marginal z J x = 0 by simp [marginal, hx]]
      exact ⟨le_rfl, hn0, fun _ => by
        apply div_nonneg _ (Nat.cast_nonneg _)
        refine mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => ?_)
        dsimp [L, sampleWeight]
        apply div_nonneg _ (sampleDensity_nonneg _ _ _)
        split <;> norm_num⟩
  · intro z J
    refine le_trans ?_ (hTotal z J)
    apply le_of_eq
    refine Finset.sum_congr rfl (fun x _ => ?_)
    by_cases hx : good z J ∧ x ∈ C z J <;> simp only [marginal, hx, if_true, if_false]
  · let score (z : I → Finset V) (J : ↥groups) (y : ↥W) :=
      if good z J then ((C z J).filter (G.Adj y.val)).card / ((C z J).card : ℝ) else 0
    have hAvg (y : ↥W) : η.event (fun z => γ < σ.mean (fun J => score z J y)) ≤
        Real.exp (-(h * γ) / 2) := by
      let T := W.filter (G.Adj y.val)
      let good' (z : Fin q → Finset V) := (1 : ℝ) / 2 ≤ Y z ∧ Y z ≤ 2 ∧
        ∀ i, τ ≤ sampleDensity W (fun S x => x ∈ S) (z i)
      let inters (z : Fin q → Finset V) := W.filter (fun x => ∀ i, x ∈ z i)
      let X (z : Fin q → Finset V) :=
        if good' z then ((T ∩ inters z).card : ℝ) / (inters z).card else 0
      have hX (z : Fin q → Finset V) : X z ∈ Set.Icc (0 : ℝ) 1 := by
        by_cases hz : good' z
        · rw [show X z = ((T ∩ inters z).card : ℝ) / (inters z).card by simp [X, hz]]
          have hin := (good_intersection_support W hW (fun S x => x ∈ S) z hτ hz.2.2 hz.1).1
          have hpos : (0 : ℝ) < (inters z).card := (by positivity :
            0 < (W.card : ℝ) * τ ^ q / 2).trans_le hin
          exact ⟨by positivity, (div_le_one hpos).mpr
            (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)⟩
        · simp [X, hz, Set.mem_Icc]
      have hXmean : (FiniteLaw.product (fun _ : Fin q => π)).mean X ≤ γ / 4 := by
        refine (mean_good_intersection_fraction W T hW (Finset.filter_subset _ _) π
          (fun S x => x ∈ S) hWeight good' hτ (fun z hz => ⟨hz.1, hz.2.2⟩)).trans ?_
        have hW0 : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
        have h : (T.card : ℝ) / W.card ≤ density := (div_le_iff₀ hW0).mpr (hDegree y.val y.property)
        rw [mul_div_assoc]
        linarith only [h, hdensityγ]
      let Y' (J : Finset I) (ω : I → Finset V) :=
        if hs : True ∧ J.card = q then
          X (fun i => ω ((Finset.equivFinOfCardEq hs.2).symm i).val) else 0
      have hEq (z : I → Finset V) : σ.mean (fun J => score z J y) =
          (∑ J ∈ groups, Y' J z) / groups.card := by
        change (∑ J : ↥groups, (Fintype.card ↥groups : ℝ)⁻¹ * score z J y) = _
        rw [← Finset.mul_sum, inv_mul_eq_div, Fintype.card_coe]
        congr 1
        rw [← Finset.sum_coe_sort groups (fun J => Y' J z)]
        refine Finset.sum_congr rfl (fun J _ => ?_)
        have hj := (Finset.mem_powersetCard.mp J.property).2
        have hc : (C z J).filter (G.Adj y.val) = T ∩ C z J := by
          ext x
          constructor
          · intro hx
            obtain ⟨hxC, hxA⟩ := Finset.mem_filter.mp hx
            exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hC _ _ hxC, hxA⟩, hxC⟩
          · intro hx
            exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hx).2,
              (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2⟩
        simp only [Y', true_and, hj, dite_true, score, hc]
        rfl
      simp_rw [hEq]
      exact event_eligible_group_average_gt_le π hh (by simp [I]) (fun _ : Finset I => True) X hX hγ hXmean
    have hAdj' (z : I → Finset V) (list : Fin m → ↥W) (J : ↥groups) (i : Fin m) :
        (ν z list J).event (fun S => ∃ x ∈ draw z list J S, G.Adj (list i).val x) ≤
          2 * score z J (list i) := by
      have ha := hAdj z list J i
      by_cases hg : good z J <;> simpa only [score, hg, ite_true, ite_false] using ha
    have hs := event_many_list_degree_hits (N := N) (degreeCap := degreeCap)
      η ξ σ (fun L i => L i) ν (fun z L J S y => ∃ x ∈ draw z L J S, G.Adj y.val x)
      score hγ hAvg hAdj'
    refine le_trans ?_ hs
    apply FiniteLaw.event_mono
    intro z hz
    obtain ⟨j, hj⟩ := hz
    refine ⟨j, ?_⟩
    convert hj using 2
    ext i
    simp

  · intro z z' list J he
    have hProj : byPosition z J = byPosition z' J := by
      funext i
      exact he _ ((Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm i).property
    apply hLocal
    · simp only [C, hProj]
    · simp only [good, hProj]

end LocallyRamsey
