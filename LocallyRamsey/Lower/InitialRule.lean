module

public import LocallyRamsey.Lower.InitialSampling
public import LocallyRamsey.Lower.Minimax
public import Mathlib.Logic.Equiv.Fin.Basic

public section

open scoped BigOperators Classical

namespace LocallyRamsey

namespace FiniteLaw

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The law obtained by reporting a function of the outcome. -/
@[expose] noncomputable def map (μ : FiniteLaw I) (f : I → J) : FiniteLaw J where
  prob y := ∑ i, if f i = y then μ.prob i else 0
  nonneg y := Finset.sum_nonneg (fun i _ => by split <;> first | exact μ.nonneg i | rfl)
  total := by
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, μ.total]

theorem mean_map (μ : FiniteLaw I) (f : I → J) (X : J → ℝ) :
    (μ.map f).mean X = μ.mean (X ∘ f) := by
  simp only [mean, map, Finset.sum_mul, ite_mul, zero_mul, Function.comp_apply]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem event_map (μ : FiniteLaw I) (f : I → J) (E : J → Prop) :
    (μ.map f).event E = μ.event (E ∘ f) := by
  rw [← (μ.map f).mean_indicator, μ.mean_map, ← μ.mean_indicator]
  rfl

theorem mean_mean_comm (μ : FiniteLaw I) (ν : FiniteLaw J) (X : I → J → ℝ) :
    μ.mean (fun i => ν.mean (X i)) = ν.mean (fun j => μ.mean (fun i => X i j)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm]

end FiniteLaw

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Turn a response to every capped law of clique unions into a single
sampling rule. A packing removes the unions with small mean payoff, and
a cardinality bound removes vertices with excessive marginal probability. -/
theorem exists_initial_sample_on_large_set
    (G : SimpleGraph V) (W : Finset V) (hW : W.Nonempty) {B limit : ℕ} (hB : 0 < B)
    (test : Finset V → Prop) [DecidablePred test] (d : ℝ) (hd : 0 < d) {p : ℝ} (hp : 0 < p)
    (hbudget : (limit : ℝ) ≤ p * W.card / 4)
    (hAllowed : ∃ ν : FiniteLaw {P : Finset V // P ⊆ W ∧ P.card = B ∧ test P},
      ∀ x : V, ν.event (fun P => x ∈ P.val) ≤ 4 * (B : ℝ) / W.card)
    (hResponse : ∀ ν : FiniteLaw {P : Finset V // P ⊆ W ∧ P.card = B ∧ test P},
      (∀ x : V, ν.event (fun P => x ∈ P.val) ≤ 4 * (B : ℝ) / W.card) →
      ∃ S : Finset V, S ⊆ W ∧ S.card ≤ limit ∧
        2 * d ≤ ν.mean (fun P => (independenceOrder G (S ∩ P.val) : ℝ))) :
    ∃ (W' : Finset V) (μ : FiniteLaw {S : Finset V // S ⊆ W ∧ S.card ≤ limit}),
      let sample := fun S => S.val ∩ W'
      W' ⊆ W ∧ (W.card : ℝ) / 2 ≤ W'.card ∧
      (∀ x ∈ W', μ.event (fun S => x ∈ sample S) ≤ p) ∧
      ∀ P : Finset V, P ⊆ W' → P.card = B → test P →
        d ≤ μ.mean (fun S => (independenceOrder G (sample S ∩ P) : ℝ)) := by
  let T := {P : Finset V // P ⊆ W ∧ P.card = B ∧ test P}
  let A := {S : Finset V // S ⊆ W ∧ S.card ≤ limit}
  let gain (S : A) (P : T) := (independenceOrder G (S.val ∩ P.val) : ℝ)
  obtain ⟨μ, hmu⟩ := exists_common_response (fun (x : V) (P : T) => x ∈ P.val)
    (fun _ => 4 * (B : ℝ) / W.card) gain d hAllowed (by
      intro ν hν
      obtain ⟨S, hSW, hlim, hS⟩ := hResponse ν hν
      exact ⟨⟨S, hSW, hlim⟩, (by linarith only [hd] : d < 2 * d).trans_le hS⟩)
  let payoff (P : Finset V) := μ.mean (fun S => (independenceOrder G (S.val ∩ P) : ℝ))
  obtain ⟨W₁, hW₁, hLarge, hpay⟩ := remove_bad_tests W hW hB test payoff d (by
    intro I _ ν value hValue hcap
    let f (i : I) : T := ⟨value i, hValue i⟩
    have hcap' (x : V) : (ν.map f).event (fun P => x ∈ P.val) ≤ 4 * (B : ℝ) / W.card := by
      rw [ν.event_map]
      exact hcap x
    have h := (hmu (ν.map f) hcap').le
    rwa [μ.mean_mean_comm, ν.mean_map] at h)
  let bad := W.filter (fun x => p < μ.event (fun S => x ∈ S.val))
  have hb : (bad.card : ℝ) * p ≤ ∑ x ∈ bad, μ.event (fun S => x ∈ S.val) := by
    calc
      _ = ∑ _x ∈ bad, p := by simp
      _ ≤ _ := Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2.le)
  have hsum : (∑ x ∈ bad, μ.event (fun S => x ∈ S.val)) ≤ (limit : ℝ) := by
    simp_rw [← μ.mean_indicator]
    rw [← μ.mean_sum, ← μ.mean_const (limit : ℝ)]
    apply μ.mean_mono
    intro S
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsub : (bad.filter (fun x => x ∈ S.val)) ⊆ S.val :=
      fun x hx => (Finset.mem_filter.mp hx).2
    exact_mod_cast (Finset.card_le_card hsub).trans S.property.2
  have hbad : (bad.card : ℝ) ≤ (W.card : ℝ) / 4 := by
    apply (mul_le_mul_iff_of_pos_right hp).mp
    exact (hb.trans hsum).trans (by linarith only [hbudget])
  let W' := W₁ \ bad
  refine ⟨W', μ, Finset.sdiff_subset.trans hW₁, ?_, ?_, ?_⟩
  · have hcard : (W'.card : ℝ) + (W₁ ∩ bad).card = W₁.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter W₁ bad
    have hc : ((W₁ ∩ bad).card : ℝ) ≤ bad.card := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right (s := W₁ ∩ bad)
    linarith only [hcard, hc, hbad, hLarge]
  · intro x hx
    have hn := (Finset.mem_sdiff.mp hx).2
    have hxW := hW₁ (Finset.sdiff_subset hx)
    have h : μ.event (fun S : A => x ∈ S.val) ≤ p :=
      le_of_not_gt (fun ht => hn (Finset.mem_filter.mpr ⟨hxW, ht⟩))
    exact (μ.event_mono (fun _ h => (Finset.mem_inter.mp h).1)).trans h
  · intro P hP hcard htest
    have heq (S : A) : S.val ∩ W' ∩ P = S.val ∩ P := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hP]
    simp_rw [heq]
    exact hpay P (hP.trans Finset.sdiff_subset) hcard htest


/-- Group a packing into unions of (K) sets. The incomplete final group
costs fewer than (K) sets, so uniform choice among the complete groups
has the required vertex marginals. -/
theorem exists_capped_law_of_packed_unions (W : Finset V) (hW : W.Nonempty) {K b : ℕ}
    (hK : 0 < K) (family : Finset V → Prop)
    (packing : Finset (Finset V))
    (hPack : ∀ P ∈ packing, P ⊆ W ∧ P.card = b ∧ family P)
    (hDisj : (packing : Set (Finset V)).Pairwise Disjoint)
    (hEnough : W.card + 4 * (K * b) ≤ 4 * (packing.card * b))
    (test : Finset V → Prop) [DecidablePred test]
    (hTest : ∀ C : Fin K → Finset V, (∀ j, (C j).card = b ∧ family (C j)) →
      (Pairwise fun i j => Disjoint (C i) (C j)) → test (Finset.univ.biUnion C)) :
    ∃ ν : FiniteLaw {P : Finset V // P ⊆ W ∧ P.card = K * b ∧ test P},
      ∀ x : V, ν.event (fun P => x ∈ P.val) ≤ 4 * ((K * b : ℕ) : ℝ) / W.card := by
  let q := packing.card / K
  have hm : q * K ≤ packing.card := by
    simpa [q, mul_comm] using Nat.div_mul_le_self packing.card K
  have hmod : packing.card % K < K := Nat.mod_lt _ hK
  have hquot : q * K + packing.card % K = packing.card := Nat.div_add_mod' _ _
  have hcoverage : W.card ≤ 4 * (q * (K * b)) := by
    have hmod' := Nat.mul_le_mul_right b hmod.le
    rw [← hquot, Nat.add_mul, Nat.mul_assoc q K b] at hEnough
    omega
  have hq : 0 < q := Nat.pos_of_ne_zero (fun hzero => by
    rw [hzero, zero_mul, mul_zero] at hcoverage
    exact (Nat.not_le_of_lt hW.card_pos) hcoverage)
  let _ : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let e (i : Fin q) (j : Fin K) : ↥packing :=
    (Finset.equivFinOfCardEq rfl).symm (Fin.castLE hm (finProdFinEquiv (i, j)))
  have he {i i' : Fin q} {j j' : Fin K} (h : e i j = e i' j') : i = i' ∧ j = j' := by
    have h' := finProdFinEquiv.injective (Fin.castLE_injective hm
      ((Finset.equivFinOfCardEq rfl).symm.injective h))
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  let C (i : Fin q) (j : Fin K) := (e i j).val
  let P (i : Fin q) := Finset.univ.biUnion (C i)
  have hCW i j : C i j ⊆ W := (hPack _ (e i j).property).1
  have hCC i j : (C i j).card = b := (hPack _ (e i j).property).2.1
  have hPW i : P i ⊆ W := by
    intro x hx
    obtain ⟨j, _, h⟩ := Finset.mem_biUnion.mp hx
    exact hCW i j h
  have hCDis i : Pairwise fun j j' => Disjoint (C i j) (C i j') :=
    fun j j' h => hDisj (e i j).property (e i j').property
      (fun heq => h (he (Subtype.ext heq)).2)
  have hPCard i : (P i).card = K * b := by
    rw [Finset.card_biUnion (fun j _ j' _ h => hCDis i h)]
    simp [hCC]
  let f (i : Fin q) : {P : Finset V // P ⊆ W ∧ P.card = K * b ∧ test P} :=
    ⟨P i, hPW i, hPCard i, hTest (C i) (fun j => ⟨hCC i j, (hPack _ (e i j).property).2.2⟩)
      (hCDis i)⟩
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  refine ⟨(FiniteLaw.uniform (Fin q)).map f, fun x => ?_⟩
  rw [FiniteLaw.event_map, FiniteLaw.uniform_event, Fintype.card_fin]
  have hcard : (Finset.univ.filter (fun i => x ∈ P i)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi i' hi'
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hi).2
    obtain ⟨j', _, hj'⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hi').2
    by_contra hne
    exact (Finset.disjoint_left.mp
      (hDisj (e i j).property (e i' j').property (fun heq => hne (he (Subtype.ext heq)).1))) hj hj'
  calc
    _ ≤ 1 / (q : ℝ) := div_le_div_of_nonneg_right (by exact_mod_cast hcard) hqpos.le
    _ ≤ _ := by
      rw [div_le_div_iff₀ hqpos hWpos, one_mul]
      have hcast : (W.card : ℝ) ≤ 4 * ((q : ℝ) * ((K * b : ℕ) : ℝ)) := by
        exact_mod_cast hcoverage
      linarith only [hcast]


/-- Given enough cliques agreeing on each list, construct a single
sampling rule before the tested cliques are specified. The probability
estimates are separated from the numerical choices of the parameters. -/
theorem exists_initial_sample_from_lists (G : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    {m s l K b r M cap limit : ℕ} (hK : 0 < K) (hb : 0 < b) (hr : 0 < r)
    (W : (Fin m → ↥U) → Finset V) (hW : ∀ L, W L ⊆ U) (hWne : ∀ L, (W L).Nonempty)
    (family : (Fin m → ↥U) → Finset V → Prop)
    (hClique : ∀ L C, family L C → G.IsClique (C : Set V))
    (hSame : ∀ L C j x y, family L C → x ∈ C → y ∈ C →
      (Gᶜ.Adj (L j).val x ↔ Gᶜ.Adj (L j).val y))
    (hPack : ∀ L, ∃ packing : Finset (Finset V),
      (∀ P ∈ packing, P ⊆ W L ∧ P.card = b ∧ family L P) ∧
      (packing : Set (Finset V)).Pairwise Disjoint ∧
      (W L).card + 4 * (K * b) ≤ 4 * (packing.card * b))
    (hRamsey : ∀ A : Finset V, A ⊆ U → M ≤ A.card →
      ∃ Q : Finset V, Q ⊆ A ∧ Q.card = r ∧ Gᶜ.IsClique (Q : Set V))
    (hLarge : M ≤ l * (K * b))
    (hCollision : (s : ℝ) ^ 2 * ((K : ℝ) / r) ≤ 1 / 2)
    (hSmall : (m : ℝ) * ((cap : ℝ) / r) ^ s < ((limit : ℝ) / U.card) * m / 4)
    {p δ a pSample : ℝ} (hp : 0 ≤ p) (ha : 0 < a) (hpSample : 0 < pSample)
    (hDegree : ∀ y ∈ U, ((U.filter (Gᶜ.Adj y)).card : ℝ) ≤ δ)
    (hPCap : ∀ L, 4 * ((K * b : ℕ) : ℝ) / (W L).card ≤ p)
    (hSBudget : ∀ L, (limit : ℝ) ≤ pSample * (W L).card / 4)
    (herr :
      ((l * (K * b) : ℕ) : ℝ) ^ s *
          Real.exp ((l : ℝ) * a - Real.log 2 * (((r : ℝ) - s * K) / K)) +
        ((l : ℝ) ^ 2 * ((K * b : ℕ) * p) +
        m * Real.exp ((l : ℝ) * (δ * p / (b * K)) - Real.log 2 * (cap / K)) +
        Real.exp (-(((limit : ℝ) / U.card) * m) / 8) * ((l : ℝ) * (U.card * p)) ^ s) < 1) :
    ∃ (L : Fin m → ↥U) (W' : Finset V)
        (μ : FiniteLaw {S : Finset V // S ⊆ W L ∧ S.card ≤ limit}),
      let sample := fun S => S.val ∩ W'
      W' ⊆ W L ∧ ((W L).card : ℝ) / 2 ≤ W'.card ∧
      (∀ x ∈ W', μ.event (fun S => x ∈ sample S) ≤ pSample) ∧
      ∀ C : Fin K → Finset V,
        (∀ j, C j ⊆ W' ∧ (C j).card = b ∧ family L (C j)) →
        (Pairwise fun i j => Disjoint (C i) (C j)) →
        (K : ℝ) * a / 2 ≤ μ.mean (fun S =>
          (independenceOrder G (sample S ∩ Finset.univ.biUnion C) : ℝ)) := by
  let Ω := Fin K → Finset V
  let ok (L : Fin m → ↥U) (C : Ω) :=
    (∀ j, (C j).card = b ∧ family L (C j)) ∧ Pairwise fun i j => Disjoint (C i) (C j)
  let union (C : Ω) := Finset.univ.biUnion C
  let test (L : Fin m → ↥U) (P : Finset V) := ∃ C : Ω, P = union C ∧ ok L C
  let _ (L : Fin m → ↥U) : DecidablePred (test L) := fun _ => Classical.propDecidable _
  let T (L : Fin m → ↥U) := {P : Finset V // P ⊆ W L ∧ P.card = K * b ∧ test L P}
  have hAllowed (L : Fin m → ↥U) : ∃ η : FiniteLaw (T L),
      ∀ x : V, η.event (fun P => x ∈ P.val) ≤ 4 * ((K * b : ℕ) : ℝ) / (W L).card := by
    obtain ⟨packing, hF, hD, hb⟩ := hPack L
    exact exists_capped_law_of_packed_unions (W L) (hWne L) hK (family L) packing hF hD hb
      (test L) (fun C hCard hPair => ⟨C, rfl, hCard, hPair⟩)
  let representation (L : Fin m → ↥U) (P : T L) : Ω :=
    Classical.choose P.property.2.2
  have hrep (L : Fin m → ↥U) (P : T L) :
      P.val = union (representation L P) ∧ ok L (representation L P) :=
    Classical.choose_spec P.property.2.2
  have hExist (L : Fin m → ↥U) : ∃ C : Ω, union C ⊆ W L ∧ ok L C := by
    obtain ⟨η, _⟩ := hAllowed L
    cases isEmpty_or_nonempty (T L) with
    | inl h =>
      let _ : IsEmpty (T L) := h
      have hn := η.total
      simp at hn
    | inr h =>
      obtain ⟨P⟩ := h
      exact ⟨representation L P, (hrep L P).1 ▸ P.property.1, (hrep L P).2⟩
  let draw (L : Fin m → ↥U) (C : Ω) : Ω :=
    if union C ⊆ W L ∧ ok L C then C else Classical.choose (hExist L)
  have hDraw (L : Fin m → ↥U) (C : Ω) :
      union (draw L C) ⊆ W L ∧ ok L (draw L C) := by
    by_cases h : union C ⊆ W L ∧ ok L C
    · simp [draw, h]
    · simpa [draw, h] using Classical.choose_spec (hExist L)
  have hDrawW (L : Fin m → ↥U) (C : Ω) (j : Fin K) : draw L C j ⊆ W L :=
    fun x hx => (hDraw L C).1 (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hx⟩)
  have hDrawRep (L : Fin m → ↥U) (P : T L) : union (draw L (representation L P)) = P.val := by
    have h : union (representation L P) ⊆ W L ∧ ok L (representation L P) :=
      ⟨(hrep L P).1 ▸ P.property.1, (hrep L P).2⟩
    simpa [draw, h] using (hrep L P).1.symm
  obtain ⟨L, hL⟩ := exists_fixed_list_for_random_unions G U hU hK hb hr W hW draw hDrawW
    (fun L C j => hClique L _ ((hDraw L C).2.1 j).2)
    (fun L C j => ((hDraw L C).2.1 j).1) (fun L C => (hDraw L C).2.2)
    (fun L C k j x y hx hy => hSame L _ j x y ((hDraw L C).2.1 k).2 hx hy)
    hRamsey hLarge hCollision hSmall hp ha.le hDegree herr
  have hd : 0 < (K : ℝ) * a / 2 := by positivity
  obtain ⟨W', μ, hW', hSize, hMarginal, hTest⟩ := exists_initial_sample_on_large_set G
    (W L) (hWne L) (Nat.mul_pos hK hb) (test L) ((K : ℝ) * a / 2) hd hpSample
    (hSBudget L) (hAllowed L) (by
      intro ν hν
      have hm (x : V) : (ν.map (representation L)).event (fun C => x ∈ union (draw L C)) ≤ p := by
        rw [ν.event_map, Function.comp_def]
        simp_rw [hDrawRep]
        exact (hν x).trans (hPCap L)
      obtain ⟨S, hS, hb, hPay⟩ := hL (ν.map (representation L)) hm
      refine ⟨S, hS, hb, ?_⟩
      rw [FiniteLaw.mean_map] at hPay
      change (K : ℝ) * a ≤ ν.mean (fun P => (independenceOrder G
        (S ∩ union (draw L (representation L P))) : ℝ)) at hPay
      simp_rw [hDrawRep] at hPay
      linarith only [hPay])
  refine ⟨L, W', μ, hW', hSize, hMarginal, ?_⟩
  intro C hC hpair
  have hU' : union C ⊆ W' := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    exact (hC j).1 hj
  have hCard : (union C).card = K * b := by
    rw [Finset.card_biUnion (fun i _ j _ h => hpair h)]
    simp only [fun j => (hC j).2.1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact hTest (union C) hU' hCard ⟨C, rfl, fun j => (hC j).2, hpair⟩


/-- The initial sample is obtained entirely from the local Ramsey property
and the dense starting region. The hypotheses on the parameters are the
size bounds and probability estimates for the random-list experiment. -/
theorem exists_initial_sample_in_dense_region (G : SimpleGraph V)
    (U : Finset V) (hU : U.Nonempty)
    {m s l K b r M cap limit large cutoff : ℕ} (hm : 0 < m)
    (hK : 0 < K) (hb : 0 < b) (hr : 0 < r)
    {density payoff upper : ℝ} (hDensity : 0 < density) (hPayoff : 0 < payoff)
    (hUpper : 0 < upper)
    (hDeg : ∀ y ∈ U, ((U.filter (Gᶜ.Adj y)).card : ℝ) ≤ density * U.card)
    (hsupply : ∀ A : Finset V, A ⊆ U → large ≤ A.card →
      ∃ C : Finset V, C ⊆ A ∧ C.card = b ∧ G.IsClique (C : Set V))
    (hRamsey : ∀ A : Finset V, A ⊆ U → M ≤ A.card →
      ∃ Q : Finset V, Q ⊆ A ∧ Q.card = r ∧ Gᶜ.IsClique (Q : Set V))
    (hLarge : M ≤ l * (K * b))
    (hCollision : (s : ℝ) ^ 2 * ((K : ℝ) / r) ≤ 1 / 2)
    (hSmall : (m : ℝ) * ((cap : ℝ) / r) ^ s < ((limit : ℝ) / U.card) * m / 4)
    (hPacking : 8 * ((m + 1) ^ ⌊2 * density * m⌋₊ * large + K * b) ≤ 3 * U.card)
    (hCutoff : (m + 1) ^ ⌊2 * density * m⌋₊ * large < cutoff)
    (hBudget : (limit : ℝ) ≤ upper * U.card / 8)
    (herr : let p := 8 * ((K * b : ℕ) : ℝ) / U.card
      ((l * (K * b) : ℕ) : ℝ) ^ s *
          Real.exp ((l : ℝ) * payoff - Real.log 2 * (((r : ℝ) - s * K) / K)) +
        ((l : ℝ) ^ 2 * ((K * b : ℕ) * p) +
        m * Real.exp ((l : ℝ) * ((density * U.card) * p / (b * K)) - Real.log 2 * (cap / K)) +
        Real.exp (-(((limit : ℝ) / U.card) * m) / 8) * ((l : ℝ) * (U.card * p)) ^ s) < 1) :
    ∃ (V' : Finset V) (family : Finset V → Prop) (μ : FiniteLaw (Finset V)),
      V' ⊆ U ∧ (U.card : ℝ) / 4 ≤ V'.card ∧
      (∀ A : Finset V, A ⊆ V' → cutoff ≤ A.card →
        ∃ C : Finset V, C ⊆ A ∧ C.card = b ∧ family C) ∧
      (∀ C, family C → G.IsClique (C : Set V)) ∧
      (∀ S, 0 < μ.prob S → S ⊆ V') ∧
      (∀ x ∈ V', μ.event (fun S => x ∈ S) ≤ upper) ∧
      ∀ C : Fin K → Finset V, (∀ j, C j ⊆ V' ∧ (C j).card = b ∧ family (C j)) →
        (Pairwise fun i j => Disjoint (C i) (C j)) →
        (K : ℝ) * payoff / 2 ≤ μ.mean (fun S =>
          (independenceOrder G (S ∩ Finset.univ.biUnion C) : ℝ)) := by
  let H (y : ↥U) (x : V) := Gᶜ.Adj y.val x
  let d := ⌊2 * density * (m : ℝ)⌋₊
  let W (L : Fin m → ↥U) := U.filter (fun x =>
    ((listSignature H L x).card : ℝ) ≤ 2 * density * m)
  let family (L : Fin m → ↥U) (C : Finset V) := G.IsClique (C : Set V) ∧
    ∀ x y, x ∈ C → y ∈ C → listSignature H L x = listSignature H L y
  have hWU (L : Fin m → ↥U) : W L ⊆ U := Finset.filter_subset _ _
  have hHalf (L : Fin m → ↥U) : (U.card : ℝ) / 2 ≤ (W L).card :=
    card_small_signatures_ge_half hm H L U hDensity (fun i => hDeg (L i).val (L i).property)
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hWpos (L : Fin m → ↥U) : (0 : ℝ) < (W L).card :=
    (by positivity : (0 : ℝ) < U.card / 2).trans_le (hHalf L)
  have hWne (L : Fin m → ↥U) : (W L).Nonempty := Finset.card_pos.mp (by exact_mod_cast hWpos L)
  have hshort (L : Fin m → ↥U) (x : V) (hx : x ∈ W L) :
      (listSignature H L x).card ≤ d := Nat.le_floor (Finset.mem_filter.mp hx).2
  have hPack (L : Fin m → ↥U) : ∃ packing : Finset (Finset V),
      (∀ C ∈ packing, C ⊆ W L ∧ C.card = b ∧ family L C) ∧
      (packing : Set (Finset V)).Pairwise Disjoint ∧
      (W L).card + 4 * (K * b) ≤ 4 * (packing.card * b) := by
    have hSize : 4 * ((m + 1) ^ d * large + K * b) ≤ 3 * (W L).card := by
      have h1 : (8 : ℝ) * (((m + 1) ^ d * large + K * b : ℕ) : ℝ) ≤ 3 * U.card := by
        exact_mod_cast hPacking
      have h2 : (4 : ℝ) * (((m + 1) ^ d * large + K * b : ℕ) : ℝ) ≤ 3 * (W L).card :=
        by linarith only [h1, hHalf L]
      exact_mod_cast h2
    obtain ⟨packing, hp, hD, hEnough⟩ := pack_list_classes_for_unions H L (W L) d large K b hb
      (fun C => G.IsClique (C : Set V)) (hshort L)
      (fun A hA => hsupply A (hA.trans (hWU L))) hSize
    exact ⟨packing, hp, hD, hEnough⟩
  let p := 8 * ((K * b : ℕ) : ℝ) / U.card
  have hMarg (L : Fin m → ↥U) : 4 * ((K * b : ℕ) : ℝ) / (W L).card ≤ p := by
    dsimp [p]
    rw [div_le_div_iff₀ (hWpos L) hUpos]
    have hp := mul_le_mul_of_nonneg_left (hHalf L)
      (show (0 : ℝ) ≤ 8 * ((K * b : ℕ) : ℝ) by positivity)
    nlinarith only [hp]
  have hLocalB (L : Fin m → ↥U) : (limit : ℝ) ≤ upper * (W L).card / 4 :=
    hBudget.trans (by linarith only [mul_le_mul_of_nonneg_left (hHalf L) hUpper.le])
  obtain ⟨L, V', ν, hV'W, hV'size, hν, htests⟩ :=
    exists_initial_sample_from_lists G U hU hK hb hr W hWU hWne family
      (fun _ _ h => h.1)
      (fun L C i x y h hx hy => by
        have he := h.2 x y hx hy
        have hm : i ∈ listSignature H L x ↔ i ∈ listSignature H L y := by rw [he]
        simpa [listSignature, H] using hm)
      hPack hRamsey hLarge hCollision hSmall (show 0 ≤ p by dsimp [p]; positivity)
      hPayoff hUpper hDeg hMarg hLocalB herr
  let sample := fun S : {S : Finset V // S ⊆ W L ∧ S.card ≤ limit} => S.val ∩ V'
  refine ⟨V', family L, ν.map sample, hV'W.trans (hWU L),
    (by linarith only [hV'size, hHalf L]), ?_, fun _ h => h.1, ?_, ?_, ?_⟩
  · intro A hA hcard
    exact exists_in_one_list_class H L A d large b hb (fun C => G.IsClique (C : Set V))
      (fun x hx => hshort L x (hV'W (hA hx)))
      (fun C hC => hsupply C (hC.trans (hA.trans (hV'W.trans (hWU L)))))
      (hCutoff.trans_le hcard)
  · intro S hS
    by_contra hno
    have hn (x : {S : Finset V // S ⊆ W L ∧ S.card ≤ limit}) : sample x ≠ S :=
      fun h => hno (h ▸ Finset.inter_subset_right)
    simp [FiniteLaw.map, hn] at hS
  · intro x hx
    rw [ν.event_map]
    exact hν x hx
  · intro C hC hDis
    rw [ν.mean_map]
    exact htests C hC hDis

end LocallyRamsey
