module

public import LocallyRamsey.Lower.Affinity
public import LocallyRamsey.Lower.Stabilization

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- Draw a uniform vertex from (U), then an outcome from its law. -/
@[expose] noncomputable def vertexMixture (R : V → FiniteLaw Ω) (U : Finset V) (hU : U.Nonempty) :
    FiniteLaw Ω where
  prob z := (∑ x ∈ U, (R x).prob z) / U.card
  nonneg z := div_nonneg (Finset.sum_nonneg fun x _ => (R x).nonneg z) (by positivity)
  total := by
    rw [← Finset.sum_div, Finset.sum_comm]
    simp only [(R _).total, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast Finset.card_ne_zero.mpr hU)

omit [DecidableEq V] in
theorem vertexMixture_mean (R : V → FiniteLaw Ω) (U : Finset V) (hU : U.Nonempty)
    (f : Ω → ℝ) :
    (vertexMixture R U hU).mean f = (∑ x ∈ U, (R x).mean f) / U.card := by
  simp only [FiniteLaw.mean, vertexMixture, div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]

omit [DecidableEq V] in
theorem vertexMixture_pos (R : V → FiniteLaw Ω) (U : Finset V) (hU : U.Nonempty)
    {x : V} (hx : x ∈ U) {z : Ω} (hz : 0 < (R x).prob z) :
    0 < (vertexMixture R U hU).prob z := by
  have hcard : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  exact div_pos (hz.trans_le (Finset.single_le_sum (fun y _ => (R y).nonneg z) hx)) hcard

/-- If the two mixture laws have small affinity, then the likelihood test
in favour of the first law succeeds at most candidates in a specified
large subset of the first vertex set, after independent repetition. -/
theorem affinity_separates_mixtures (R : V → FiniteLaw Ω)
    (U T : Finset V) (hU : U.Nonempty) (hT : T.Nonempty)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : affinity (vertexMixture R U hU) (vertexMixture R T hT) < 1 - ε)
    (k : ℕ) :
    ∃ U' : Finset V, U' ⊆ U ∧ (ε / 2) * U.card ≤ U'.card ∧
      ∀ x ∈ U', (FiniteLaw.product (fun _ : Fin k => R x)).event (fun z =>
        (∏ i, (vertexMixture R U hU).prob (z i)) ≤
          ∏ i, (vertexMixture R T hT).prob (z i)) ≤ (1 - ε / 2) ^ k := by
  classical
  let P := vertexMixture R U hU
  let Q := vertexMixture R T hT
  let f := fun z => Real.sqrt (Q.prob z / P.prob z)
  let a := fun x => (R x).mean f
  let U' := U.filter (fun x => a x ≤ 1 - ε / 2)
  have ha (x : V) : 0 ≤ a x := (R x).mean_nonneg (fun _ => Real.sqrt_nonneg _)
  have hUc : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  change affinity P Q < 1 - ε at hsep
  rw [affinity_eq_mean_ratio, vertexMixture_mean] at hsep
  have hsmall : (∑ x ∈ U, a x) < (1 - ε) * U.card := (div_lt_iff₀ hUc).mp hsep
  have hlo : (1 - ε / 2) * ((U.card : ℝ) - U'.card) ≤ ∑ x ∈ U, a x := by
    have hsub : U' ⊆ U := Finset.filter_subset _ _
    have hcard : ((U \ U').card : ℝ) = (U.card : ℝ) - U'.card := by
      rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [← hcard, mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    have hOutside : (∑ _x ∈ U \ U', (1 - ε / 2)) ≤ ∑ x ∈ U \ U', a x := by
      refine Finset.sum_le_sum fun x hx => ?_
      obtain ⟨hxU, hxnot⟩ := Finset.mem_sdiff.mp hx
      exact le_of_not_ge fun h => hxnot (Finset.mem_filter.mpr ⟨hxU, h⟩)
    exact hOutside.trans
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun x _ _ => ha x))
  have hcount : (ε / 2) * U.card ≤ U'.card := by
    have := mul_nonneg hε.le (show 0 ≤ (U'.card : ℝ) by positivity)
    nlinarith only [hlo, hsmall, this]
  refine ⟨U', Finset.filter_subset _ _, hcount, ?_⟩
  intro x hx
  obtain ⟨hxU, hxgood⟩ := Finset.mem_filter.mp hx
  exact event_product_likelihood_le (R x) P Q (fun _ hz => vertexMixture_pos R U hU hxU hz) k hxgood

/-- Restrict the vertex set until any two sufficiently large subsets have
mixture laws of affinity at least (1-ε). The inputs give the number of
repetitions and the stopping inequality of the separating tests. -/
theorem exists_affinity_stable_set (A : Finset V) (hA : A.Nonempty)
    (μ : FiniteLaw Ω) (R : V → FiniteLaw Ω)
    {ε α L : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1) (hα : 0 < α) (hα' : α ≤ 1) (hL : 0 ≤ L)
    (hdom : ∀ x ∈ A, ∀ z, (R x).prob z ≤ L * μ.prob z)
    (k steps : ℕ)
    (hstop : L ^ k * (1 / 2 : ℝ) ^ steps < 1 - (steps : ℝ) * (1 - ε / 2) ^ k) :
    ∃ B : Finset V, B ⊆ A ∧ (ε / 2 * α) ^ steps * (A.card : ℝ) ≤ B.card ∧
      ∀ U T : Finset V, U ⊆ B → T ⊆ B → α * B.card ≤ U.card → α * B.card ≤ T.card →
        ∀ (hU : U.Nonempty) (hT : T.Nonempty),
          1 - ε ≤ affinity (vertexMixture R U hU) (vertexMixture R T hT) := by
  classical
  let stable (B : Finset V) := ∀ U T : Finset V, U ⊆ B → T ⊆ B →
    α * (B.card : ℝ) ≤ U.card → α * (B.card : ℝ) ≤ T.card →
    ∀ (hU : U.Nonempty) (hT : T.Nonempty),
      1 - ε ≤ affinity (vertexMixture R U hU) (vertexMixture R T hT)
  refine exists_stable_set_of_separating_tests A hA (FiniteLaw.product (fun _ : Fin k => μ))
    (fun x => FiniteLaw.product (fun _ : Fin k => R x)) (c := ε / 2 * α)
    (δ := (1 - ε / 2) ^ k) (L := L ^ k) (by positivity)
    (by nlinarith only [hε', hα', mul_le_mul_of_nonneg_right hε' hα.le])
    (pow_nonneg (by linarith) _) (pow_nonneg hL _) ?_ stable ?_ steps hstop
  · intro x hx z
    change (∏ i, (R x).prob (z i)) ≤
      L ^ k * ∏ i, μ.prob (z i)
    have hprod := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin k)))
      (fun i _ => (R x).nonneg (z i)) (fun i _ => hdom x hx (z i))
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod
  · intro B _ _ hbad
    dsimp [stable] at hbad
    push Not at hbad
    obtain ⟨U, T, hUB, hTB, hUcard, hTcard, hU, hT, hsep⟩ := hbad
    obtain ⟨U', hU'U, hu, huTest⟩ := affinity_separates_mixtures R U T hU hT hε hsep k
    obtain ⟨T', hT'T, ht, htTest⟩ := affinity_separates_mixtures R T U hT hU hε
      (by rw [affinity_symm]; exact hsep) k
    let p := fun z : Fin k → Ω => ∏ i, (vertexMixture R U hU).prob (z i)
    let q := fun z : Fin k → Ω => ∏ i, (vertexMixture R T hT).prob (z i)
    refine ⟨U', T', fun z => q z < p z, fun z => p z < q z, hU'U.trans hUB, hT'T.trans hTB,
      ?_, ?_, fun z h => lt_asymm h.1 h.2, ?_, ?_⟩
    · rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left hUcard (by positivity)).trans hu
    · rw [mul_assoc]
      exact (mul_le_mul_of_nonneg_left hTcard (by positivity)).trans ht
    · intro x hx
      simpa only [not_lt, p, q] using huTest x hx
    · intro x hx
      simpa only [not_lt, p, q] using htTest x hx

end LocallyRamsey
