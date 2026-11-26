module

public import LocallyRamsey.Lower.SamplingExperiment
public import LocallyRamsey.Lower.CliqueLocation
public import LocallyRamsey.Lower.ListPacking

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V Ω J A : Type*} [DecidableEq V] [Fintype V] [Fintype Ω] [Fintype J] [Fintype A]

/-- The random-list bound applies after fixing all the originally drawn
samples and group choices, because only the within-group draws use the
list. Their vertex marginal bounds are uniform over that list. -/
theorem event_bad_location_list (W : Finset V) (hW : W.Nonempty)
    (G : SimpleGraph V) (η : FiniteLaw A) (σ : FiniteLaw J)
    {m s N : ℕ} (ν : A → (Fin m → ↥W) → J → FiniteLaw Ω)
    (draw : A → (Fin m → ↥W) → J → Ω → Finset V)
    (marginal : A → J → V → ℝ)
    (hm : ∀ a j x, 0 ≤ marginal a j x)
    (hDraw : ∀ a L j x, (ν a L j).event (fun ω => x ∈ draw a L j ω) ≤ marginal a j x)
    {t p : ℝ} (ht : 0 ≤ t) (hTotal : ∀ a j, (∑ x, marginal a j x) ≤ t) :
    letI : Nonempty ↥W := hW.to_subtype
    let ξ := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
    let law := η.staged (fun a => ξ.staged (fun L =>
      FiniteLaw.product (fun _ : Fin N => σ.staged (ν a L))))
    law.event (fun z =>
      ∃ (f : Fin s → Fin N) (v : Fin s → V), Function.Injective f ∧
        (p ≤ (FiniteLaw.uniform ↥W).event (fun y => ∀ k, G.Adj y.val (v k)) ∧
         listCommonCount (fun (y : ↥W) x => G.Adj y.val x) z.2.1 v < p * m / 2) ∧
        ∀ k, v k ∈ draw z.1 z.2.1 (z.2.2 (f k)).1 (z.2.2 (f k)).2) ≤
      Real.exp (-(p * m) / 8) * ((N : ℝ) * t) ^ s := by
  let _ : Nonempty ↥W := hW.to_subtype
  intro ξ law
  let rel (y : ↥W) (x : V) := G.Adj y.val x
  let bad (a : A) (L : Fin m → ↥W) (ω : Fin N → J × Ω) :=
    ∃ (f : Fin s → Fin N) (v : Fin s → V), Function.Injective f ∧
      (p ≤ (FiniteLaw.uniform ↥W).event (fun y => ∀ k, rel y (v k)) ∧
       listCommonCount rel L v < p * m / 2) ∧
      ∀ k, v k ∈ draw a L (ω (f k)).1 (ω (f k)).2
  change law.event (fun z => bad z.1 z.2.1 z.2.2) ≤ _
  rw [FiniteLaw.event_list_after_groups η ξ σ ν bad]
  refine (η.mean_mono (Y := fun _ => _) (fun a => ?_)).trans_eq (η.mean_const _)
  let σN := FiniteLaw.product (fun _ : Fin N => σ)
  refine (σN.mean_mono (Y := fun _ => _) (fun g => ?_)).trans_eq (σN.mean_const _)
  have h := FiniteLaw.staged_event_exists_injective_inclusions_le ξ
    (fun L (i : Fin N) => ν a L (g i)) (fun L i ω x => x ∈ draw a L (g i) ω)
    (fun i x => marginal a (g i) x) (fun L i x => hDraw a L (g i) x)
    (fun i x => hm a (g i) x) s
    (fun v L => p ≤ (FiniteLaw.uniform ↥W).event (fun y => ∀ k, rel y (v k)) ∧
      listCommonCount rel L v < p * m / 2)
    (Real.exp_pos (-(p * m) / 8)).le (initial_list_tuple_tail (FiniteLaw.uniform ↥W) rel p)
  refine h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hm _ _ _) ?_ s)
    (Real.exp_pos _).le)
  calc
    _ ≤ ∑ _i : Fin N, t := Finset.sum_le_sum (fun i _ => hTotal a (g i))
    _ = _ := by simp

/-- The random groups chosen for the draws have their independent
uniform law even after the within-group vertices are added. -/
theorem event_group_property_under_draws
    (η : FiniteLaw A) (σ : FiniteLaw J) (ν : A → J → FiniteLaw Ω)
    (N : ℕ) (E : (Fin N → J) → Prop) :
    (η.staged (fun a => FiniteLaw.product (fun _ : Fin N => σ.staged (ν a)))).event
      (fun z => E (fun i => (z.2 i).1)) = (FiniteLaw.product (fun _ : Fin N => σ)).event E := by
  rw [η.staged_event, ← η.mean_const ((FiniteLaw.product (fun _ : Fin N => σ)).event E)]
  congr 1
  funext a
  rw [FiniteLaw.event_product_of_staged (fun _ : Fin N => σ)]
  simp_rw [← FiniteLaw.mean_indicator, FiniteLaw.mean_const]


/-- The finite probability bound for locating a clique. The errors are
the missing draws, vertex collisions, excessive list degrees, shared
positions, and failure of the common-neighbour test. -/
theorem probability_locate_clique {I : Type*} [DecidableEq I]
    (G : SimpleGraph V) (W : Finset V) (hW : W.Nonempty)
    (positions : Finset I) (hPos : positions.Nonempty) {q : ℕ} (hq : q ≤ positions.card)
    [Nonempty ↥(positions.powersetCard q)]
    {m s N r d b lost cap limit M degreeCap : ℕ} (hN : 0 < N) (hd : 0 < d)
    (η : FiniteLaw A)
    (ν : A → (Fin m → ↥W) → ↥(positions.powersetCard q) → FiniteLaw Ω)
    (draw : A → (Fin m → ↥W) → ↥(positions.powersetCard q) → Ω → Finset V)
    (hDraw : ∀ a L g ω, draw a L g ω ⊆ W ∧ Gᶜ.IsClique (draw a L g ω : Set V) ∧
      (draw a L g ω = ∅ ∨ (draw a L g ω).card = b))
    (hLarge : 2 * M ≤ N * b)
    (hRamsey : ∀ S : Finset V, S ⊆ W → M ≤ S.card →
      ∃ Q : Finset V, Q ⊆ S ∧ Q.card = r ∧ G.IsClique (Q : Set V))
    {p t missing badDegrees : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ t)
    (marginal : A → ↥(positions.powersetCard q) → V → ℝ)
    (hmarginal : ∀ a g x, 0 ≤ marginal a g x)
    (hMarginal : ∀ a L g x, (ν a L g).event (fun ω => x ∈ draw a L g ω) ≤ marginal a g x)
    (hMargMax : ∀ a g x, marginal a g x ≤ p)
    (hMargTotal : ∀ a g, ∑ x, marginal a g x ≤ t)
    (hCollision : (s : ℝ) ^ 2 / (r - (lost : ℝ)) ≤ 1 / 2) (hlost : lost < r)
    (hSmall : (m : ℝ) * ((degreeCap : ℝ) / (r - (lost : ℝ))) ^ s <
      ((limit : ℝ) / W.card) * m / 4)
    (hLimit : limit ≤ W.card)
    (hEmpty : letI : Nonempty ↥W := hW.to_subtype
      let ξ := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
      let σ := FiniteLaw.uniform ↥(positions.powersetCard q)
      (η.staged (fun a => ξ.staged (fun L => σ.staged (ν a L)))).event
        (fun z => draw z.1 z.2.1 z.2.2.1 z.2.2.2 = ∅) ≤ missing)
    (hDegrees : letI : Nonempty ↥W := hW.to_subtype
      let ξ := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
      let σ := FiniteLaw.uniform ↥(positions.powersetCard q)
      (η.staged (fun a => ξ.staged (fun L => FiniteLaw.product
        (fun _ : Fin N => σ.staged (ν a L))))).event
        (fun z => ∃ j : Fin m, degreeCap < ((Finset.univ : Finset (Fin N)).filter
          (fun i => ∃ x ∈ draw z.1 z.2.1 (z.2.2 i).1 (z.2.2 i).2, G.Adj (z.2.1 j).val x)).card) ≤ badDegrees) :
    letI : Nonempty ↥W := hW.to_subtype
    let ξ := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
    let σ := FiniteLaw.uniform ↥(positions.powersetCard q)
    let full := η.staged (fun a => ξ.staged (fun L =>
      FiniteLaw.product (fun _ : Fin N => σ.staged (ν a L))))
    let errGroup := positions.card * Real.exp ((N : ℝ) * ((q : ℝ) / positions.card) - Real.log 2 * d) +
      (N : ℝ) ^ r * Real.exp ((Real.exp 1 - 1) * ((q : ℝ) / positions.card) * ((r : ℝ) * q / d) * r -
        ((lost * (cap + 1) : ℕ) : ℝ) / (2 * d))
    1 - (2 * missing + (N : ℝ) ^ 2 * (b * p) + badDegrees + errGroup +
      Real.exp (-(((limit : ℝ) / W.card) * m) / 8) * ((N : ℝ) * t) ^ s) ≤
    full.event (fun z =>
      let P (i : Fin N) := draw z.1 z.2.1 (z.2.2 i).1 (z.2.2 i).2
      let group (i : Fin N) := (z.2.2 i).1.val
      (Pairwise fun i j => Disjoint (P i) (P j)) ∧
      ∃ (f : Fin s → Fin N) (v : Fin s → V) (Q : Finset V),
        Function.Injective f ∧ (∀ j, v j ∈ P (f j)) ∧
        let B := commonRegion G W (Finset.univ.image v) limit
        B ⊆ W ∧ B.card = limit ∧ Q ⊆ B ∧ G.IsClique (Q : Set V) ∧
        r ≤ Q.card + s * (cap + 1) ∧
        ∀ x ∈ Q, ∃ i, x ∈ P i ∧ ∀ j, Disjoint (group (f j)) (group i)) := by
  let _ : Nonempty ↥W := hW.to_subtype
  intro ξ σ full errGroup
  let getP (z : A × ((Fin m → ↥W) × (Fin N → ↥(positions.powersetCard q) × Ω))) (i : Fin N) :=
    draw z.1 z.2.1 (z.2.2 i).1 (z.2.2 i).2
  let getG (z : A × ((Fin m → ↥W) × (Fin N → ↥(positions.powersetCard q) × Ω))) (i : Fin N) :=
    (z.2.2 i).1.val
  let badEmpty z := (N : ℝ) / 2 ≤ ∑ i : Fin N, if getP z i = ∅ then (1 : ℝ) else 0
  let badDisj z := ∃ i j, i ≠ j ∧ ¬ Disjoint (getP z i) (getP z j)
  let badDeg (z : A × ((Fin m → ↥W) × (Fin N → ↥(positions.powersetCard q) × Ω))) :=
    ∃ j : Fin m, degreeCap < ((Finset.univ : Finset (Fin N)).filter
      (fun i => ∃ x ∈ getP z i, G.Adj (z.2.1 j).val x)).card
  let badGroup z := ∃ f : Fin r → Fin N, Function.Injective f ∧
    (lost * (cap + 1) : ℕ) ≤ groupCollisionCount (getG z) f
  let pList := (limit : ℝ) / W.card
  let badList (z : A × ((Fin m → ↥W) × (Fin N → ↥(positions.powersetCard q) × Ω))) :=
    ∃ (f : Fin s → Fin N) (v : Fin s → V), Function.Injective f ∧
      (pList ≤ (FiniteLaw.uniform ↥W).event (fun y => ∀ k, G.Adj y.val (v k)) ∧
        listCommonCount (fun (y : ↥W) x => G.Adj y.val x) z.2.1 v < pList * m / 2) ∧
      ∀ k, v k ∈ getP z (f k)
  let bad z := badEmpty z ∨ badDisj z ∨ badDeg z ∨ badGroup z ∨ badList z
  have hEmpty' : full.event badEmpty ≤ 2 * missing := by
    have h := FiniteLaw.event_many_failures_in_staged_draws (η.staged (fun _ => ξ))
      (fun a (_ : Fin N) => σ.staged (ν a.1 a.2)) (fun a _ w => draw a.1 a.2 w.1 w.2 = ∅)
      (p := missing) (fun _ => by
        rw [FiniteLaw.staged_event, FiniteLaw.staged_mean]
        simpa only [FiniteLaw.staged_event] using hEmpty)
      (show 0 < (N : ℝ) / 2 by exact div_pos (by exact_mod_cast hN) (by norm_num))
    have he : full.event badEmpty =
        ((η.staged (fun _ => ξ)).staged (fun a => FiniteLaw.product
          (fun _ : Fin N => σ.staged (ν a.1 a.2)))).event
          (fun z => (N : ℝ) / 2 ≤ ∑ i : Fin N,
            if draw z.1.1 z.1.2 (z.2 i).1 (z.2 i).2 = ∅ then (1 : ℝ) else 0) := by
      simp only [full, FiniteLaw.staged_event, FiniteLaw.staged_mean, badEmpty, getP]
    rw [he]
    refine h.trans_eq ?_
    simp only [Fintype.card_fin]
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [div_div_eq_mul_div, div_eq_iff hNz]
    ring
  have hDisj' : full.event badDisj ≤ (N : ℝ) ^ 2 * (b * p) := by
    simp only [full, FiniteLaw.staged_event]
    refine (η.mean_mono (Y := fun _ => _) (fun a => ?_)).trans_eq (η.mean_const _)
    refine (ξ.mean_mono (Y := fun _ => _) (fun L => ?_)).trans_eq (ξ.mean_const _)
    exact event_intersecting_draws_le (σ.staged (ν a L)) (fun x => draw a L x.1 x.2) N b hp
      (fun w => ((hDraw a L w.1 w.2).2.2).elim (fun h => by simp [h]) Eq.le)
      (fun x => by
        rw [FiniteLaw.staged_event]
        exact (σ.mean_mono (fun g => (hMarginal a L g x).trans (hMargMax a g x))).trans_eq (σ.mean_const _))
  have hGroup' : full.event badGroup ≤ errGroup := by
    have h := event_many_shared_positions positions hPos hq N r d hd (((lost * (cap + 1) : ℕ) : ℝ) / 2)
    have he : full.event badGroup =
        (FiniteLaw.product (fun _ : Fin N => σ)).event (fun ω =>
          ∃ f : Fin r → Fin N, Function.Injective f ∧
            (lost * (cap + 1) : ℕ) ≤ groupCollisionCount Subtype.val (ω ∘ f)) := by
      rw [FiniteLaw.staged_event]
      have hG (a : A) :
          (ξ.staged (fun L => FiniteLaw.product (fun _ : Fin N => σ.staged (ν a L)))).event
            (fun z => badGroup (a, z)) = _ :=
        event_group_property_under_draws ξ σ (ν a) N (fun ω =>
          ∃ f : Fin r → Fin N, Function.Injective f ∧
            (lost * (cap + 1) : ℕ) ≤ groupCollisionCount Subtype.val (ω ∘ f))
      simp_rw [hG, η.mean_const]
    rw [he]
    dsimp at h
    rw [show 2 * (((lost * (cap + 1) : ℕ) : ℝ) / 2) =
      (((lost * (cap + 1) : ℕ) : ℝ)) by ring] at h
    simpa only [errGroup, div_div] using h
  have hList' := event_bad_location_list W hW G η σ (m := m) (s := s) (N := N) ν draw
    marginal hmarginal hMarginal ht hMargTotal (p := pList)
  change full.event badList ≤ _ at hList'
  have hbad : full.event bad ≤ 2 * missing + (N : ℝ) ^ 2 * (b * p) + badDegrees + errGroup +
      Real.exp (-(pList * m) / 8) * ((N : ℝ) * t) ^ s := by
    have hd : full.event badDeg ≤ badDegrees := hDegrees
    have h0 := (full.event_union_le badGroup badList).trans (add_le_add hGroup' hList')
    have h1 := (full.event_union_le badDeg (fun z => badGroup z ∨ badList z)).trans (add_le_add hd h0)
    have h2 := (full.event_union_le badDisj (fun z => badDeg z ∨ badGroup z ∨ badList z)).trans (add_le_add hDisj' h1)
    have h3 := (full.event_union_le badEmpty (fun z => badDisj z ∨ badDeg z ∨ badGroup z ∨ badList z)).trans
      (add_le_add hEmpty' h2)
    change full.event bad ≤ _ at h3
    linarith only [h3]
  refine (show _ ≤ full.event (fun z => ¬bad z) from by rw [full.event_not]; linarith only [hbad]).trans
    (full.event_mono ?_)
  intro z hz
  have hD : Pairwise fun i j => Disjoint (getP z i) (getP z j) := fun i j hij =>
    by_contra (fun h => hz (Or.inr (Or.inl ⟨i, j, hij, h⟩)))
  have hCoverage : M ≤ (Finset.univ.biUnion (getP z)).card := by
    have hE : (∑ i : Fin N, if getP z i = ∅ then (1 : ℝ) else 0) < (N : ℝ) / 2 :=
      lt_of_not_ge (fun h => hz (Or.inl h))
    rw [Finset.card_biUnion (fun i _ j _ h => hD h)]
    have hEq (i : Fin N) : (getP z i).card = if getP z i = ∅ then 0 else b := by
      by_cases h : getP z i = ∅
      · simp [h]
      · simp only [h, ite_false]
        exact (hDraw z.1 z.2.1 (z.2.2 i).1 (z.2.2 i).2).2.2.resolve_left h
    have hSum (i : Fin N) : ((getP z i).card : ℝ) +
        (if getP z i = ∅ then (1 : ℝ) else 0) * b = b := by
      rw [hEq]
      split <;> simp
    have hTotal := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin N))) rfl (fun i _ => hSum i)
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hTotal
    have hL : 2 * (M : ℝ) ≤ (N : ℝ) * b := by exact_mod_cast hLarge
    have hb : 0 ≤ (b : ℝ) := by positivity
    have hfin : (M : ℝ) ≤ ∑ i : Fin N, ((getP z i).card : ℝ) := by
      nlinarith only [hL, hTotal, mul_le_mul_of_nonneg_right hE.le hb]
    exact_mod_cast hfin
  refine ⟨hD, locate_clique_from_good_draws W hW z.2.1 (getP z) (getG z)
    (fun i => (hDraw z.1 z.2.1 (z.2.2 i).1 (z.2.2 i).2).1)
    (fun i => (hDraw z.1 z.2.1 (z.2.2 i).1 (z.2.2 i).2).2.1) hD hCoverage hRamsey
    (fun f hf => (lt_of_not_ge (fun h => hz (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, h⟩)))))).le)
    hlost (fun j => le_of_not_gt (fun h => hz (Or.inr (Or.inr (Or.inl ⟨j, h⟩)))))
    hCollision hSmall ?_ hLimit⟩
  intro f v hf hv hd
  exact le_of_not_gt (fun h => hz (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, v, hf, ⟨hd, h⟩, hv⟩)))))



/-- The proportion of groups meeting a neighbourhood controls the number
of draws meeting that neighbourhood. The list entry is independent of
the base samples, although the within-group draws may use the full list. -/
theorem event_many_list_degree_hits {Y T : Type*} [Fintype T]
    (η : FiniteLaw A) (ξ : FiniteLaw T) (σ : FiniteLaw J)
    {m N degreeCap : ℕ}
    (read : T → Fin m → Y)
    (ν : A → T → J → FiniteLaw Ω)
    (test : A → T → J → Ω → Y → Prop)
    (score : A → J → Y → ℝ)
    {γ e : ℝ} (hγ : 0 ≤ γ)
    (hAvg : ∀ y, η.event (fun a => γ < σ.mean (fun g => score a g y)) ≤ e)
    (hTest : ∀ a L j i, (ν a L j).event (fun ω => test a L j ω (read L i)) ≤
      2 * score a j (read L i)) :
    let full := η.staged (fun a => ξ.staged (fun L =>
      FiniteLaw.product (fun _ : Fin N => σ.staged (ν a L))))
    full.event (fun z => ∃ i : Fin m, degreeCap <
      ((Finset.univ : Finset (Fin N)).filter (fun j => test z.1 z.2.1
        (z.2.2 j).1 (z.2.2 j).2 (read z.2.1 i))).card) ≤
      (m : ℝ) * (e + Real.exp (2 * (N : ℝ) * γ - Real.log 2 * degreeCap)) := by
  intro full
  let bad (i : Fin m) (z : A × (T × (Fin N → J × Ω))) := degreeCap <
    ((Finset.univ : Finset (Fin N)).filter (fun j => test z.1 z.2.1
      (z.2.2 j).1 (z.2.2 j).2 (read z.2.1 i))).card
  let tail := Real.exp (2 * (N : ℝ) * γ - Real.log 2 * degreeCap)
  have hOne (i : Fin m) : full.event (bad i) ≤ e + tail := by
    simp only [full, FiniteLaw.staged_event]
    rw [η.mean_mean_comm ξ]
    refine (ξ.mean_mono (Y := fun _ => _) (fun L => ?_)).trans_eq (ξ.mean_const _)
    let tooLarge (a : A) := γ < σ.mean (fun g => score a g (read L i))
    have hBound (a : A) :
        (FiniteLaw.product (fun _ : Fin N => σ.staged (ν a L))).event
          (fun w => bad i (a, L, w)) ≤ (if tooLarge a then 1 else 0) + tail := by
      let μ := σ.staged (ν a L)
      let τ := FiniteLaw.product (fun _ : Fin N => μ)
      let X (_ : Fin N) (w : J × Ω) :=
        if test a L w.1 w.2 (read L i) then (1 : ℝ) else 0
      by_cases h : tooLarge a
      · rw [ite_eq_left h]
        have hb := τ.event_nonneg (fun w => ¬bad i (a, L, w))
        rw [τ.event_not] at hb
        exact (sub_nonneg.mp hb).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
      · rw [ite_eq_right h, zero_add]
        have hmean (j : Fin N) : μ.mean (X j) ≤ 2 * γ := by
          rw [show μ.mean (X j) = μ.event (fun w => test a L w.1 w.2 (read L i)) from μ.mean_indicator _,
            show μ = σ.staged (ν a L) by rfl, FiniteLaw.staged_event]
          calc
            _ ≤ σ.mean (fun g => 2 * score a g (read L i)) := σ.mean_mono (fun g => hTest a L g i)
            _ = 2 * σ.mean (fun g => score a g (read L i)) := σ.mean_mul_const _ _
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_not_gt h) (by norm_num)
        refine (τ.event_mono (Q := fun w => (degreeCap : ℝ) ≤ ∑ j, X j (w j)) ?_).trans ?_
        · intro w hw
          have he : (∑ j, X j (w j)) =
              (((Finset.univ : Finset (Fin N)).filter (fun j => test a L (w j).1 (w j).2 (read L i))).card : ℝ) := by
            simp [X]
          rw [he]
          exact_mod_cast Nat.le_of_lt hw
        · refine (FiniteLaw.prob_sum_ge_le (fun _ : Fin N => μ) X (fun j w => by
              dsimp [X]; split <;> norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)) degreeCap).trans ?_
          have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun j _ => hmean j)
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
          dsimp [tail]
          rw [Real.exp_le_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          linarith only [hsum]
    refine (η.mean_mono hBound).trans ?_
    rw [η.mean_add, η.mean_const, η.mean_indicator]
    exact add_le_add_left (hAvg (read L i)) tail
  refine (full.event_exists_le_sum bad).trans ?_
  exact (Finset.sum_le_sum (fun i _ => hOne i)).trans_eq (by simp [tail, mul_add])


end LocallyRamsey
