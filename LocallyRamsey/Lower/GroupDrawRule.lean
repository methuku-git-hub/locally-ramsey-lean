module

public import LocallyRamsey.Lower.LocationProbability
public import LocallyRamsey.Lower.GoodIntersections

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V A J : Type*} [Fintype V] [DecidableEq V] [Fintype A] [Fintype J]

/-- Choose the law of each within-group draw after seeing the samples and
the list. The vertex cap and the count of neighbours on the list follow
from the packing. Bad groups report the empty set. -/
theorem exists_group_draw_rule (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hW : W.Nonempty) (η : FiniteLaw A) (σ : FiniteLaw J)
    {m d k b : ℕ} (hb : 0 < b) (C : A → J → Finset V) (good : A → J → Prop)
    (hC : ∀ a j, C a j ⊆ W)
    (hCne : ∀ a j, good a j → (C a j).Nonempty)
    (hNum : ∀ a j, good a j → (m + 1) ^ d * k * 4 ≤ (C a j).card)
    (hSupply : ∀ X : Finset V, X ⊆ W → k ≤ X.card →
      ∃ P : Finset V, P ⊆ X ∧ P.card = b ∧ Gᶜ.IsClique (P : Set V))
    {density error : ℝ} (hd : 0 ≤ density)
    (hDegree : ∀ x ∈ W, ((W.filter (G.Adj x)).card : ℝ) ≤ density * W.card)
    (hGood : ∀ j, η.event (fun a => ¬ good a j) ≤ error) :
    letI : Nonempty ↥W := hW.to_subtype
    let ξ := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
    let cap (a : A) (j : J) (x : V) :=
      if good a j ∧ x ∈ C a j then 2 * (b : ℝ) / (C a j).card else 0
    let degree (a : A) (j : J) (y : V) :=
      if good a j then ((C a j).filter (G.Adj y)).card / ((C a j).card : ℝ) else 0
    ∃ (ν : A → (Fin m → ↥W) → J → FiniteLaw (Finset V))
      (draw : A → (Fin m → ↥W) → J → Finset V → Finset V),
      (∀ a L j S, draw a L j S ⊆ C a j ∧ Gᶜ.IsClique (draw a L j S : Set V) ∧
        (draw a L j S = ∅ ∨ good a j ∧ (draw a L j S).card = b)) ∧
      (∀ a L j x, (ν a L j).event (fun S => x ∈ draw a L j S) ≤ cap a j x) ∧
      (∀ a L j i, (ν a L j).event (fun S => ∃ x ∈ draw a L j S, G.Adj (L i).val x) ≤
        2 * degree a j (L i).val) ∧
      (∀ a j, (∑ x : V, cap a j x) ≤ 2 * b) ∧
      (η.staged (fun a => ξ.staged (fun L => σ.staged (ν a L)))).event
        (fun z => draw z.1 z.2.1 z.2.2.1 z.2.2.2 = ∅) ≤
        error + 4 * Real.exp ((m : ℝ) * density - Real.log 2 * d) ∧
      (∀ a a' j j' L, C a j = C a' j' → (good a j ↔ good a' j') →
        ν a L j = ν a' L j' ∧ draw a L j = draw a' L j') := by
  let _ : Nonempty ↥W := hW.to_subtype
  intro ξ cap degree
  let adj (y : ↥W) (x : V) := G.Adj y.val x
  let _ : DecidableRel adj := fun _ _ => inferInstanceAs (Decidable (G.Adj _ _))
  let family (S : Finset V) := Gᶜ.IsClique (S : Set V)
  have pick (B : Finset V) (L : Fin m → ↥W)
      (hBW : B ⊆ W) (hB : B.Nonempty) (hn : (m + 1) ^ d * k * 4 ≤ B.card) :=
    exists_supported_list_draw adj L B hB hb family
      (fun X hX => hSupply X (hX.trans hBW)) hn
  have hDraw (a : A) (L : Fin m → ↥W) (j : J) (h : good a j) :=
    pick (C a j) L (hC a j) (hCne a j h) (hNum a j h)
  let ν (a : A) (L : Fin m → ↥W) (j : J) : FiniteLaw (Finset V) :=
    if h : good a j then Classical.choose (hDraw a L j h) else FiniteLaw.single ∅
  let draw (a : A) (L : Fin m → ↥W) (j : J) : Finset V → Finset V :=
    if h : good a j then Classical.choose (Classical.choose_spec (hDraw a L j h)) else fun _ => ∅
  have hs (a : A) (L : Fin m → ↥W) (j : J) (h : good a j) :=
    Classical.choose_spec (Classical.choose_spec (hDraw a L j h))
  refine ⟨ν, draw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a L j S
    by_cases h : good a j
    · rcases (hs a L j h).1 S with hS | hS
      · have hEmp : draw a L j S = ∅ := by simpa only [draw, dite_eq_left h] using hS
        simp [hEmp]
      · simpa only [draw, dite_eq_left h] using ⟨hS.1, hS.2.2, Or.inr ⟨h, hS.2.1⟩⟩
    · simp [draw, h]
  · intro a L j x
    by_cases h : good a j
    · simpa only [ν, draw, cap, dite_eq_left h, h, true_and] using (hs a L j h).2.1 x
    · simp [ν, draw, cap, h, FiniteLaw.single_event]
  · intro a L j i
    by_cases h : good a j
    · have he : (C a j).filter (adj (L i)) = (C a j).filter (G.Adj (L i).val) := by
        ext x
        simp [adj]
      have htest := (hs a L j h).2.2.1 i
      rw [he] at htest
      rw [show ν a L j = Classical.choose (hDraw a L j h) by simp only [ν, dite_eq_left h],
        show draw a L j = Classical.choose (Classical.choose_spec (hDraw a L j h)) by
          simp only [draw, dite_eq_left h]]
      rw [show degree a j (L i).val = ((C a j).filter (G.Adj (L i).val)).card /
          ((C a j).card : ℝ) by simp only [degree, ite_eq_left h]]
      rw [← he] at htest ⊢
      convert htest using 1
      <;> ring
    · simp [ν, draw, degree, h, FiniteLaw.single_event]
  · intro a j
    by_cases h : good a j
    · have hc : ((C a j).card : ℝ) ≠ 0 := by exact_mod_cast (hCne a j h).card_ne_zero
      have he : (Finset.univ : Finset V).filter (fun x => x ∈ C a j) = C a j := by ext; simp
      simp only [cap, h, true_and, ← Finset.sum_filter, he, Finset.sum_const, nsmul_eq_mul]
      field_simp
      rfl
    · simp [cap, h]
  · let loss := 4 * Real.exp ((m : ℝ) * density - Real.log 2 * d)
    let P (a : A) (L : Fin m → ↥W) (j : J) := (ν a L j).event (fun S => draw a L j S = ∅)
    have hs' (a : A) (j : J) : ξ.mean (fun L => P a L j) ≤
        (if ¬good a j then 1 else 0) + loss := by
      by_cases h : good a j
      · simp only [h, not_true_eq_false, ite_false, zero_add]
        let removed (L : Fin m → ↥W) := (C a j).filter (fun x => d < (listSignature adj L x).card)
        let E (L : Fin m → ↥W) := ((C a j).card : ℝ) / 4 < (removed L).card
        have hprob : ξ.event E ≤ loss :=
          event_many_long_signatures_le W (C a j) hW G.Adj m d hd (fun x hx => by
            have hEq : (W.filter (fun y => G.Adj y x)) = W.filter (G.Adj x) := by
              ext y
              simp only [Finset.mem_filter]
              exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
            rw [hEq]
            exact hDegree x (hC a j hx))
        refine (ξ.mean_mono (Y := fun L => if E L then (1 : ℝ) else 0) ?_).trans
          ((ξ.mean_indicator E).trans_le hprob)
        intro L
        by_cases hE : E L
        · rw [ite_eq_left hE]
          have hp := (ν a L j).event_nonneg (fun S => ¬draw a L j S = ∅)
          rw [FiniteLaw.event_not] at hp
          exact sub_nonneg.mp hp
        · rw [ite_eq_right hE]
          have hCeq : ((C a j).filter (fun x => (listSignature adj L x).card ≤ d)).card +
              (removed L).card = (C a j).card := by
            let f (x : V) := (listSignature adj L x).card ≤ d
            simpa [f, removed] using (Finset.card_filter_add_card_filter_not (s := C a j) f)
          have hEq : (((C a j).filter (fun x =>
              (listSignature adj L x).card ≤ d)).card : ℝ) + (removed L).card = (C a j).card := by
            exact_mod_cast hCeq
          have hsize : ((C a j).card : ℝ) * 3 / 4 ≤
              (((C a j).filter (fun x => (listSignature adj L x).card ≤ d)).card : ℝ) := by
            have ht : ((removed L).card : ℝ) ≤ (C a j).card / 4 := le_of_not_gt hE
            linarith only [ht, hEq]
          exact (show P a L j = 0 by
            simpa only [P, ν, draw, dite_eq_left h] using (hs a L j h).2.2.2 hsize).le
      · simp only [h, not_false_eq_true, ite_true]
        have he : ∀ L, P a L j = 1 := by
          intro L
          simp [P, ν, draw, h, FiniteLaw.single_event]
        simp_rw [he, ξ.mean_const]
        exact le_add_of_nonneg_right (by dsimp [loss]; positivity)
    simp only [FiniteLaw.staged_event]
    change η.mean (fun a => ξ.mean (fun L => σ.mean (fun j => P a L j))) ≤ _
    simp_rw [ξ.mean_mean_comm σ]
    have hBound (a : A) : σ.mean (fun j => ξ.mean (fun L => P a L j)) ≤
        σ.mean (fun j => (if ¬good a j then 1 else 0)) + loss := by
      exact (σ.mean_mono (hs' a)).trans_eq (by rw [σ.mean_add, σ.mean_const])
    refine (η.mean_mono hBound).trans ?_
    rw [η.mean_add, η.mean_const, η.mean_mean_comm σ]
    simp_rw [η.mean_indicator]
    exact add_le_add_left ((σ.mean_mono hGood).trans_eq (σ.mean_const _)) loss
  · intro a a' j j' L he hg
    by_cases h : good a j
    · have h' := hg.mp h
      simp only [ν, draw, dite_eq_left h, dite_eq_left h']
      have aux (B B' : Finset V) (hBW : B ⊆ W) (hB'W : B' ⊆ W)
          (hB : B.Nonempty) (hB' : B'.Nonempty)
          (hn : (m + 1) ^ d * k * 4 ≤ B.card) (hn' : (m + 1) ^ d * k * 4 ≤ B'.card)
          (he : B = B') :
          Classical.choose (pick B L hBW hB hn) = Classical.choose (pick B' L hB'W hB' hn') ∧
          Classical.choose (Classical.choose_spec (pick B L hBW hB hn)) =
            Classical.choose (Classical.choose_spec (pick B' L hB'W hB' hn')) := by
        subst B'
        exact ⟨rfl, rfl⟩
      exact aux _ _ (hC a j) (hC a' j') (hCne a j h) (hCne a' j' h')
        (hNum a j h) (hNum a' j' h') he
    · have h' : ¬ good a' j' := fun h' => h (hg.mpr h')
      simp only [ν, draw, dite_eq_right h, dite_eq_right h', and_self]


/-- The proportion of neighbours in a good intersection has mean at
most twice their proportion in the original region. -/
theorem mean_good_intersection_fraction {Ω : Type*} [Fintype Ω]
    (W D : Finset V) (hW : W.Nonempty) (hDW : D ⊆ W)
    (π : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)]
    (hWeight : ∀ x ∈ W, π.mean (fun s => sampleWeight W contains s x) = 1)
    {q : ℕ} (good : (Fin q → Ω) → Prop) [DecidablePred good]
    {τ : ℝ} (hτ : 0 < τ)
    (hGood : ∀ z, good z → (1 : ℝ) / 2 ≤ intersectionDensity (sampleWeight W contains) W z ∧
      ∀ i, τ ≤ sampleDensity W contains (z i)) :
    let C (z : Fin q → Ω) := W.filter (fun x => ∀ i, contains (z i) x)
    (FiniteLaw.product (fun _ : Fin q => π)).mean
      (fun z => if good z then ((D ∩ C z).card : ℝ) / (C z).card else 0) ≤
      2 * (D.card : ℝ) / W.card := by
  intro C
  let ν := FiniteLaw.product (fun _ : Fin q => π)
  let L := sampleWeight W contains
  have hW0 : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hL0 (s : Ω) (x : V) : 0 ≤ L s x := by
    change 0 ≤ (if contains s x then 1 else 0) / sampleDensity W contains s
    apply div_nonneg _ (sampleDensity_nonneg W contains s)
    split <;> norm_num
  have hPoint (z : Fin q → Ω) :
      (if good z then ((D ∩ C z).card : ℝ) / (C z).card else 0) ≤
      2 * (∑ x ∈ D, ∏ i, L (z i) x) / W.card := by
    by_cases hg : good z
    · rw [ite_eq_left hg, Finset.mul_sum, Finset.sum_div]
      have hs := (good_intersection_support W hW contains z hτ (hGood z hg).2 (hGood z hg).1).2
      have he : ((D ∩ C z).card : ℝ) / (C z).card =
          ∑ _x ∈ D ∩ C z, (1 : ℝ) / (C z).card := by simp [Finset.sum_const, div_eq_mul_inv, mul_comm]
      rw [he]
      exact (Finset.sum_le_sum (fun x hx => hs x (Finset.mem_inter.mp hx).2)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
          (fun x _ _ => div_nonneg (mul_nonneg (by norm_num) (Finset.prod_nonneg (fun i _ => hL0 (z i) x))) hW0.le))
    · simp only [hg, ite_false]
      exact div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun x _ =>
        Finset.prod_nonneg (fun i _ => hL0 (z i) x)))) hW0.le
  refine (ν.mean_mono hPoint).trans_eq ?_
  have hFactor (x : V) (hx : x ∈ D) : ν.mean (fun z => ∏ i, L (z i) x) = 1 := by
    change (FiniteLaw.product (fun _ : Fin q => π)).mean (fun z => ∏ i, L (z i) x) = 1
    rw [FiniteLaw.mean_product (fun _ : Fin q => π) (fun _ s => L s x)]
    simp [L, hWeight x (hDW hx)]
  simp_rw [div_eq_inv_mul, ν.mean_mul_const, ν.mean_sum]
  rw [Finset.sum_congr rfl hFactor]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

end LocallyRamsey
