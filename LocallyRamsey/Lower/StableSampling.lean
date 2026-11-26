module

public import LocallyRamsey.Lower.IntersectionDensity
public import LocallyRamsey.Lower.GroupCollisions

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- The distribution of a sample conditional on containing a given
vertex. -/
@[expose] noncomputable def lawContaining (μ : FiniteLaw Ω) (contains : Ω → Prop)
    [DecidablePred contains] {p : ℝ} (hp : 0 < p) (h : μ.event contains = p) : FiniteLaw Ω := by
  let X (ω : Ω) := (if contains ω then 1 else 0) / p
  have hmean : μ.mean X = 1 := by
    simp only [X, div_eq_inv_mul, μ.mean_mul_const, μ.mean_indicator, h, inv_mul_cancel₀ hp.ne']
  exact μ.withDensity X (fun ω => by dsimp [X]; split <;> positivity) hmean

/-- The stabilization lemma applied to the product laws at individual
vertices. The density bound is exactly the reciprocal inclusion
probability raised to the number of samples. -/
theorem exists_stable_vertex_domain (V₀ : Finset V) (hV₀ : V₀.Nonempty)
    (μ : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    [∀ x, DecidablePred (fun ω => contains ω x)]
    {p ε α : ℝ} (hp : 0 < p) (hu : ∀ x ∈ V₀, μ.event (fun ω => contains ω x) = p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (q k steps : ℕ)
    (hstop : ((p⁻¹) ^ q) ^ k * (1 / 2 : ℝ) ^ steps < 1 - (steps : ℝ) * (1 - ε / 2) ^ k) :
    let R (x : V) := if hx : x ∈ V₀ then lawContaining μ (fun ω => contains ω x) hp (hu x hx) else μ
    let productAt (x : V) := FiniteLaw.product (fun _ : Fin q => R x)
    ∃ Z : Finset V, Z ⊆ V₀ ∧ (ε / 2 * α) ^ steps * (V₀.card : ℝ) ≤ Z.card ∧
      ∀ U T : Finset V, U ⊆ Z → T ⊆ Z → α * Z.card ≤ U.card → α * Z.card ≤ T.card →
        ∀ (hU : U.Nonempty) (hT : T.Nonempty),
          1 - ε ≤ affinity (vertexMixture productAt U hU) (vertexMixture productAt T hT) := by
  classical
  intro R productAt
  let π := FiniteLaw.product (fun _ : Fin q => μ)
  have hAt (x : V) (hx : x ∈ V₀) (ω : Ω) : (R x).prob ω ≤ p⁻¹ * μ.prob ω := by
    simp only [R, dite_eq_left hx, lawContaining, FiniteLaw.withDensity]
    split
    · rw [one_div, mul_comm]
    · rw [zero_div, mul_zero]
      exact mul_nonneg (by positivity) (μ.nonneg ω)
  have hProd (x : V) (hx : x ∈ V₀) (z : Fin q → Ω) :
      (productAt x).prob z ≤ (p⁻¹) ^ q * π.prob z := by
    have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin q)))
      (fun i _ => (R x).nonneg (z i)) (fun i _ => hAt x hx (z i))
    simpa only [productAt, π, FiniteLaw.product, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] using h
  exact exists_affinity_stable_set V₀ hV₀ π productAt hε hε1 hα hα1 (by positivity) hProd k steps hstop

/-- Forgetting information cannot decrease affinity. This form applies
to any finite map, including restriction to selected coordinates. -/
theorem affinity_le_affinity_map {J : Type*} [Fintype J] (μ ν : FiniteLaw Ω) (f : Ω → J) :
    affinity μ ν ≤ affinity (μ.map f) (ν.map f) := by
  classical
  let fiber (y : J) := (Finset.univ : Finset Ω).filter (fun x => f x = y)
  have hEq (σ : FiniteLaw Ω) (y : J) :
      (σ.map f).prob y = ∑ x ∈ fiber y, σ.prob x := by
    simp only [FiniteLaw.map, fiber, Finset.sum_filter]
  unfold affinity
  have hSum : (∑ y : J, ∑ x ∈ fiber y, Real.sqrt (μ.prob x) * Real.sqrt (ν.prob x)) =
      ∑ x, Real.sqrt (μ.prob x) * Real.sqrt (ν.prob x) := by
    simp only [fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [← hSum]
  simp only [hEq]
  exact Finset.sum_le_sum (fun y _ =>
    Real.sum_sqrt_mul_sqrt_le (fiber y) μ.nonneg ν.nonneg)

/-- Mixing by a uniform vertex commutes with forgetting information. -/
theorem map_vertexMixture {J : Type*} [Fintype J] (R : V → FiniteLaw Ω)
    (U : Finset V) (hU : U.Nonempty) (f : Ω → J) :
    (vertexMixture R U hU).map f = vertexMixture (fun x => (R x).map f) U hU := by
  classical
  suffices hp : ∀ y, ((vertexMixture R U hU).map f).prob y =
      (vertexMixture (fun x => (R x).map f) U hU).prob y by
    have extLaw (a b : FiniteLaw J) (hp : a.prob = b.prob) : a = b := by
      cases a
      cases b
      congr
    exact extLaw _ _ (funext hp)
  intro y
  simp only [FiniteLaw.map, vertexMixture, div_eq_inv_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split <;> simp_all

/-- The stabilized comparison persists when fewer independent samples
are drawn at the chosen vertex. -/
theorem affinity_vertex_product_mono (R : V → FiniteLaw Ω)
    (U T : Finset V) (hU : U.Nonempty) (hT : T.Nonempty)
    {j q : ℕ} (hj : j ≤ q) :
    affinity (vertexMixture (fun x => FiniteLaw.product (fun _ : Fin q => R x)) U hU)
      (vertexMixture (fun x => FiniteLaw.product (fun _ : Fin q => R x)) T hT) ≤
    affinity (vertexMixture (fun x => FiniteLaw.product (fun _ : Fin j => R x)) U hU)
      (vertexMixture (fun x => FiniteLaw.product (fun _ : Fin j => R x)) T hT) := by
  let f (z : Fin q → Ω) := z ∘ Fin.castLE hj
  have hm (x : V) : (FiniteLaw.product (fun _ : Fin q => R x)).map f =
      FiniteLaw.product (fun _ : Fin j => R x) :=
    FiniteLaw.map_product_injective (R x) (Fin.castLE hj) (Fin.castLE_injective hj)
  have h := affinity_le_affinity_map
    (vertexMixture (fun x => FiniteLaw.product (fun _ : Fin q => R x)) U hU)
    (vertexMixture (fun x => FiniteLaw.product (fun _ : Fin q => R x)) T hT) f
  simpa only [map_vertexMixture, hm] using h


/-- The biased product law has as its density the normalized weight of
the intersection. Thus the stabilized affinity comparison bounds the
squared difference of the square roots of the two densities. -/
theorem rootDistance_intersections_of_affinity
    (V₀ W U T : Finset V) (hWV₀ : W ⊆ V₀) (hUW : U ⊆ W) (hTW : T ⊆ W)
    (hW : W.Nonempty) (hU : U.Nonempty) (hT : T.Nonempty)
    (μ : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    [∀ x, DecidablePred (fun ω => contains ω x)]
    {p ε : ℝ} (hp : 0 < p) (hu : ∀ x ∈ V₀, μ.event (fun ω => contains ω x) = p)
    (q : ℕ)
    (hAff : let R (x : V) := if hx : x ∈ V₀ then lawContaining μ (fun ω => contains ω x) hp (hu x hx) else μ
      let productAt (x : V) := FiniteLaw.product (fun _ : Fin q => R x)
      1 - ε ≤ affinity (vertexMixture productAt U hU) (vertexMixture productAt T hT)) :
    let π := biasedLaw W hW μ contains p hp (fun x hx => hu x (hWV₀ hx))
    let L := sampleWeight W contains
    rootDistance (FiniteLaw.product (fun _ : Fin q => π))
      (intersectionDensity L U) (intersectionDensity L T) ≤ 2 * ε := by
  classical
  intro π L
  let R (x : V) := if hx : x ∈ V₀ then lawContaining μ (fun ω => contains ω x) hp (hu x hx) else μ
  let productAt (x : V) := FiniteLaw.product (fun _ : Fin q => R x)
  let ν := FiniteLaw.product (fun _ : Fin q => π)
  have hL0 (s : Ω) (x : V) : 0 ≤ L s x := by
    change 0 ≤ (if contains s x then 1 else 0) / sampleDensity W contains s
    apply div_nonneg _ (sampleDensity_nonneg W contains s)
    split <;> norm_num
  have hL1 (x : V) (hx : x ∈ W) : π.mean (fun s => L s x) = 1 :=
    biasedLaw_mean_weight W hW μ contains p hp (fun x hx => hu x (hWV₀ hx)) hx
  have hfactor (x : V) (hx : x ∈ W) (s : Ω) :
      (R x).prob s = π.prob s * L s x := by
    rw [biasedLaw_prob_mul_weight W hW μ contains hp (fun x hx => hu x (hWV₀ hx)) hx s]
    simp only [R, dite_eq_left (hWV₀ hx), lawContaining, FiniteLaw.withDensity, mul_div_assoc]
  have hm (B : Finset V) (hB : B.Nonempty) (hBW : B ⊆ W) :
      vertexMixture productAt B hB =
        ν.withDensity (intersectionDensity L B) (intersectionDensity_nonneg L hL0 B)
          (mean_intersectionDensity π L B hB (fun x hx => hL1 x (hBW hx)) q) := by
    have he (z : Fin q → Ω) : (vertexMixture productAt B hB).prob z =
        ν.prob z * intersectionDensity L B z := by
      change (∑ x ∈ B, (productAt x).prob z) / B.card = _
      rw [intersectionDensity, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun x hx => ?_)
      simp only [productAt, ν, FiniteLaw.product, hfactor x (hBW hx), Finset.prod_mul_distrib]
    have extLaw (a b : FiniteLaw (Fin q → Ω)) (hp : a.prob = b.prob) : a = b := by
      cases a
      cases b
      congr
    exact extLaw _ _ (funext he)
  change 1 - ε ≤ affinity (vertexMixture productAt U hU) (vertexMixture productAt T hT) at hAff
  rw [hm U hU hUW, hm T hT hTW, affinity_eq_one_sub_rootDistance] at hAff
  change rootDistance ν (intersectionDensity L U) (intersectionDensity L T) ≤ 2 * ε
  linarith only [hAff]

/-- A sample of small density has small probability under the biased
law. The estimate holds even for outcomes of density zero. -/
theorem biasedLaw_event_small_density_le (W : Finset V) (hW : W.Nonempty)
    (μ : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    {p τ : ℝ} (hp : 0 < p) (hτ : 0 ≤ τ)
    (hu : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p) :
    (biasedLaw W hW μ contains p hp hu).event (fun ω => sampleDensity W contains ω < τ) ≤ τ / p := by
  classical
  let π := biasedLaw W hW μ contains p hp hu
  rw [← π.mean_indicator]
  have hpoint (ω : Ω) : π.prob ω * (if sampleDensity W contains ω < τ then (1 : ℝ) else 0) ≤
      μ.prob ω * (τ / p) := by
    by_cases h : sampleDensity W contains ω < τ
    · simp only [h, ite_true, mul_one, π, biasedLaw]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h.le hp.le) (μ.nonneg ω)
    · simp only [h, ite_false, mul_zero]
      exact mul_nonneg (μ.nonneg ω) (div_nonneg hτ hp.le)
  calc
    _ ≤ μ.mean (fun _ => τ / p) := Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = _ := μ.mean_const _


/-- Large deviations of a density from the reference law are bounded
using the squared difference of square roots. -/
theorem event_density_gt_two_le (μ : FiniteLaw Ω) (Y : Ω → ℝ)
    (hY : ∀ s, 0 ≤ Y s) :
    μ.event (fun s => 2 < Y s) ≤ 8 * rootDistance μ Y (fun _ => 1) := by
  classical
  let X := fun s => (Real.sqrt (Y s) - 1) ^ 2
  have hp (s : Ω) (hs : 2 < Y s) : (1 : ℝ) / 8 ≤ X s := by
    have h := Real.sqrt_le_sqrt hs.le
    have h' : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have h1 : (2 / 5 : ℝ) ≤ Real.sqrt (Y s) - 1 := by linarith only [h, h']
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2 / 5) h1 2
    norm_num at h2
    exact (by norm_num : (1 : ℝ) / 8 ≤ (4 : ℝ) / 25).trans h2
  refine ((μ.event_mono hp).trans
    (μ.event_ge_le (X := X) (fun _ => sq_nonneg _) (by norm_num : (0 : ℝ) < 1 / 8))).trans_eq ?_
  have hEq : μ.mean X = rootDistance μ Y (fun _ => 1) := by
    simp only [rootDistance, X, Real.sqrt_one]
  rw [hEq]
  ring

/-- The one-sample comparison is the same comparison formulated with
only a single product coordinate. -/
theorem rootDistance_single_intersection (μ : FiniteLaw Ω) (L : Ω → V → ℝ)
    (A B : Finset V) :
    rootDistance (FiniteLaw.product (fun _ : Fin 1 => μ))
      (intersectionDensity L A) (intersectionDensity L B) =
    rootDistance μ (fun s => (∑ x ∈ A, L s x) / A.card) (fun s => (∑ x ∈ B, L s x) / B.card) := by
  unfold rootDistance
  have he (S : Fin 1 → Ω) (C : Finset V) : intersectionDensity L C S =
      (∑ x ∈ C, L (S 0) x) / C.card := by
    simp only [intersectionDensity, Fin.prod_univ_one]
  simp_rw [he]
  exact FiniteLaw.mean_coordinate (fun _ : Fin 1 => μ) 0
    (fun s => (Real.sqrt ((∑ x ∈ A, L s x) / A.card) -
      Real.sqrt ((∑ x ∈ B, L s x) / B.card)) ^ 2)



/-- Averaging the normalized sample weights over their original region
gives one at every outcome with positive biased probability. -/
theorem biasedLaw_avg_weight_eq_one
    (W : Finset V) (hW : W.Nonempty) (μ : FiniteLaw Ω)
    (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)]
    {p : ℝ} (hp : 0 < p) (hu : ∀ x ∈ W, μ.event (fun s => contains s x) = p)
    (s : Ω) (hs : 0 < (biasedLaw W hW μ contains p hp hu).prob s) :
    (∑ x ∈ W, sampleWeight W contains s x) / W.card = 1 := by
  have hρ : 0 < sampleDensity W contains s := by
    by_contra! h
    have hz := le_antisymm h (sampleDensity_nonneg W contains s)
    simp [biasedLaw, hz] at hs
  have hw : (W.card : ℝ) ≠ 0 := by exact_mod_cast hW.card_ne_zero
  have hsum : (∑ x ∈ W, if contains s x then (1 : ℝ) else 0) =
      sampleDensity W contains s * W.card := by
    unfold sampleDensity
    field_simp
  simp only [sampleWeight, ← Finset.sum_div]
  rw [hsum]
  field_simp

/-- The one-position density test has small probability when viewed
from any sufficiently large collection of vertices. -/
theorem mean_weight_of_large_density_le (π : FiniteLaw Ω) (L : Ω → V → ℝ)
    (W A B : Finset V) (hA : A.Nonempty)
    (hL : ∀ s x, 0 ≤ L s x)
    (hmean : ∀ x ∈ A, π.mean (fun s => L s x) = 1)
    (hW : ∀ s, 0 < π.prob s → (∑ x ∈ W, L s x) / W.card = 1)
    {ε : ℝ}
    (hAB : rootDistance π (fun s => (∑ x ∈ A, L s x) / A.card)
      (fun s => (∑ x ∈ W, L s x) / W.card) ≤ 2 * ε)
    (hB : rootDistance π (fun s => (∑ x ∈ B, L s x) / B.card)
      (fun s => (∑ x ∈ W, L s x) / W.card) ≤ 2 * ε) :
    (∑ x ∈ A, π.mean (fun s => L s x *
      (if 2 < (∑ y ∈ B, L s y) / B.card then (1 : ℝ) else 0))) / A.card ≤ 36 * ε := by
  classical
  let Y (C : Finset V) (s : Ω) := (∑ x ∈ C, L s x) / C.card
  let bad (s : Ω) := 2 < Y B s
  have hY0 (C : Finset V) (s : Ω) : 0 ≤ Y C s :=
    div_nonneg (Finset.sum_nonneg fun x _ => hL s x) (Nat.cast_nonneg C.card)
  have heq (C : Finset V) : rootDistance π (Y C) (Y W) = rootDistance π (Y C) (fun _ => 1) := by
    simp only [rootDistance, FiniteLaw.mean]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hs : 0 < π.prob s
    · change π.prob s * (Real.sqrt (Y C s) - Real.sqrt (Y W s)) ^ 2 =
        π.prob s * (Real.sqrt (Y C s) - Real.sqrt 1) ^ 2
      have h : Y W s = 1 := hW s hs
      rw [h]
    · simp only [le_antisymm (le_of_not_gt hs) (π.nonneg s), zero_mul]
  have hYa : π.mean (Y A) = 1 := by
    have ha0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_ne_zero
    simp only [Y, div_eq_inv_mul, π.mean_mul_const, π.mean_sum,
      Finset.sum_congr rfl (fun x hx => hmean x hx), Finset.sum_const, nsmul_eq_mul, mul_one,
      inv_mul_cancel₀ ha0]
  have hX : π.event bad ≤ 16 * ε := by
    refine (event_density_gt_two_le π (Y B) (hY0 B)).trans ?_
    have h : rootDistance π (Y B) (Y W) ≤ 2 * ε := hB
    rw [heq] at h
    linarith only [h]
  have hP := event_le_two_add_distance π (Y A) (fun _ => 1) (hY0 A) (fun _ => zero_le_one)
    hYa (π.mean_const 1) bad
  have hd : rootDistance π (Y A) (fun _ => 1) ≤ 2 * ε := by
    rw [← heq]
    exact hAB
  have hbase : (π.withDensity (fun _ => 1) (fun _ => zero_le_one) (π.mean_const 1)).event bad =
      π.event bad := by
    rw [← FiniteLaw.mean_indicator, ← π.mean_indicator]
    simp only [FiniteLaw.mean, FiniteLaw.withDensity, mul_one]
  rw [hbase] at hP
  have ht : (π.withDensity (Y A) (hY0 A) hYa).event bad =
      (∑ x ∈ A, π.mean (fun s => L s x * (if bad s then 1 else 0))) / A.card := by
    rw [← FiniteLaw.mean_indicator]
    simp only [FiniteLaw.mean, FiniteLaw.withDensity, Y, div_eq_inv_mul, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun s _ => ?_))
    ring
  rw [ht] at hP
  linarith only [hP, hX, hd]


end LocallyRamsey
