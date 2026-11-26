module

public import LocallyRamsey.Lower.UpperOverlapEstimate
public import LocallyRamsey.Lower.SampleOverlap

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- A uniformly permuted image of a fixed block outside the anchor, with
the anchor restored, is uniform over the groups containing that anchor. -/
theorem mean_uniform_through_anchor (U : Finset I) {i : I} (hi : i ∈ U)
    {q : ℕ} (hq : 0 < q) (block : Finset ↥(U.erase i)) (hblock : block.card = q - 1)
    (f : Finset I → ℝ) :
    let through := (U.powersetCard q).filter (fun J => i ∈ J)
    (FiniteLaw.uniform (Equiv.Perm ↥(U.erase i))).mean
      (fun p => f (restoreAnchor U i (block.map p.toEmbedding))) =
        (∑ J ∈ through, f J) / through.card := by
  classical
  intro through
  have h := mean_uniform_perm_block block (fun F => f (restoreAnchor U i F))
  rw [hblock] at h
  have hEq : through = ((Finset.univ : Finset ↥(U.erase i)).powersetCard (q - 1)).image
      (restoreAnchor U i) := by
    simpa [through] using
      restored_companions_image U hi hq (∅ : Finset ↥(U.erase i))
  rw [hEq, Finset.sum_image (fun _ _ _ _ h => restoreAnchor_injective U i h),
    Finset.card_image_of_injective _ (restoreAnchor_injective U i)]
  exact h

/-- The average over anchored partitions is the same retained overlap as
the average over positions inside the uniformly chosen group. -/
theorem retained_overlap_group_position (U : Finset I) {q h : ℕ}
    (hq : 0 < q) (hh : 0 < h) (hqU : q ≤ U.card)
    (blocks : (i : ↥U) → Fin h → Finset ↥(U.erase i.val))
    (hblock : ∀ i j, (blocks i j).card = q - 1) (f : I → Finset I → ℝ) :
    let groups := U.powersetCard q
    (∑ J ∈ groups, (∑ i ∈ J, f i J) / q) / groups.card =
      (∑ i : ↥U, (FiniteLaw.uniform (Equiv.Perm ↥(U.erase i.val))).mean
        (fun p => (h : ℝ)⁻¹ * ∑ j, f i.val (restoreAnchor U i.val ((blocks i j).map p.toEmbedding))))
      / U.card := by
  classical
  intro groups
  let through (i : I) := groups.filter (fun J => i ∈ J)
  have h (i : ↥U) :
      (FiniteLaw.uniform (Equiv.Perm ↥(U.erase i.val))).mean
        (fun p => (h : ℝ)⁻¹ * ∑ j, f i.val (restoreAnchor U i.val ((blocks i j).map p.toEmbedding))) =
      (∑ J ∈ through i.val, f i.val J) / (through i.val).card := by
    rw [FiniteLaw.mean_mul_const, FiniteLaw.mean_sum]
    simp_rw [fun j => mean_uniform_through_anchor U i.property hq (blocks i j) (hblock i j) (f i.val)]
    have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
    change (h : ℝ)⁻¹ * ∑ _j : Fin h, ((∑ J ∈ through i.val, f i.val J) / (through i.val).card) = _
    simp [← mul_assoc, hh']
  simp_rw [h]
  rw [Finset.sum_coe_sort U (fun i : I => (∑ J ∈ through i, f i J) / (through i).card)]
  exact mean_group_position_eq_mean_position_group U q hq hqU f

/-- The upper overlap estimate for the same group-position average used
in the lower bound. Summing the per-anchor bounds only needs a bound on
the mean normalizing factor. -/
theorem mean_overlap_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset I) {q h : ℕ} (hq : 2 ≤ q) (hh : 0 < h)
    (hU : U.card = q * h) (hsize : ∀ i : ↥U, 2 * (q - 1) * (q - 1) ≤ (U.erase i.val).card)
    (blocks : (i : ↥U) → Fin h → Finset ↥(U.erase i.val))
    (hblock : ∀ i j, (blocks i j).card = q - 1)
    (hdisj : ∀ i, Pairwise (fun j l => Disjoint (blocks i j) (blocks i l)))
    (B C : Finset V) (hCB : C ⊆ B)
    (raw : Finset I → V → ℝ) (w : I → Finset I → V → ℝ)
    (hraw : ∀ J x, 0 ≤ raw J x) (hw : ∀ i J x, 0 ≤ w i J x)
    (ell : I → ℝ) (hell : ∀ i ∈ U, 0 < ell i)
    {γ D v A : ℝ} (hγ : 0 ≤ γ) (hD : 0 < D) (hv : 0 ≤ v) (hA : 0 ≤ A)
    (hhγ : (h : ℝ)⁻¹ ≤ γ)
    (hMean : (∑ i ∈ U, ell i) / U.card ≤ A * γ)
    (hpt : ∀ i ∈ U, ∀ J x, w i J x ≤ raw J x / ell i)
    (htotal : ∀ i ∈ U, ∀ J, J.card = q → mass (w i J) B ≤ 1)
    (hNon : ∀ x ∈ C,
      (∑ J ∈ U.powersetCard q, mass (raw J) (nonNeighbors G C x)) / (U.powersetCard q).card ≤
        2 * v / ((h : ℝ) * D))
    (hmarked : ∀ i : ↥U,
      let π := FiniteLaw.uniform (Equiv.Perm ↥(U.erase i.val))
      let avg (p : Equiv.Perm ↥(U.erase i.val)) (x : V) :=
        (h : ℝ)⁻¹ * ∑ j, w i.val (restoreAnchor U i.val ((blocks i j).map p.toEmbedding)) x
      π.mean (fun p => mass (avg p) (marked G (avg p) B γ)) ≤ ((h : ℝ)⁻¹) ^ 2) :
    let groups := U.powersetCard q
    (∑ J ∈ groups, (∑ i ∈ J, ell i * mass (w i J) C) / q) / groups.card ≤
      4 * v / D + 3 * A * γ ^ 2 := by
  classical
  intro groups
  have hqU : q ≤ U.card := by rw [hU]; exact Nat.le_mul_of_pos_right _ hh
  have hpos (i : ↥U) :=
    upper_overlap_at_anchor G U i.property hq hh hU (hsize i) (blocks i) (hdisj i)
      (hblock i) B C hCB raw (w i.val) hraw (hw i.val) (hell i.val i.property)
      hγ hv hD (hpt i.val i.property) (htotal i.val i.property) hNon (hmarked i)
  have hEq := retained_overlap_group_position U (by omega : 0 < q) hh hqU blocks hblock
    (fun i J => ell i * mass (w i J) C)
  rw [hEq]
  have hterm (i : ↥U) :
      (FiniteLaw.uniform (Equiv.Perm ↥(U.erase i.val))).mean (fun p =>
        (h : ℝ)⁻¹ * ∑ j, ell i.val * mass (w i.val (restoreAnchor U i.val ((blocks i j).map p.toEmbedding))) C) ≤
      4 * v / D + (γ + 2 * (h : ℝ)⁻¹) * ell i.val := by
    let avg (p : Equiv.Perm ↥(U.erase i.val)) (x : V) :=
      (h : ℝ)⁻¹ * ∑ j, w i.val (restoreAnchor U i.val ((blocks i j).map p.toEmbedding)) x
    let π := FiniteLaw.uniform (Equiv.Perm ↥(U.erase i.val))
    have he (p : Equiv.Perm ↥(U.erase i.val)) :
        (h : ℝ)⁻¹ * (∑ j, ell i.val * mass (w i.val (restoreAnchor U i.val ((blocks i j).map p.toEmbedding))) C) =
          ell i.val * mass (avg p) C := by
      simp only [mass, avg, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      ring
    simp_rw [he, FiniteLaw.mean_mul_const]
    exact hpos i
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => hterm i)) (Nat.cast_nonneg _)).trans ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_coe_sort U ell, add_div, mul_div_assoc]
  have hU0 : (U.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((show 0 < q by omega).trans_le hqU))
  have hcancel : (U.card : ℝ) * (4 * (v / D / U.card)) = 4 * (v / D) := by field_simp
  rw [hcancel]
  have hmul : (γ + 2 * (h : ℝ)⁻¹) * ((∑ i ∈ U, ell i) / U.card) ≤ 3 * A * γ ^ 2 := by
    refine (mul_le_mul_of_nonneg_left hMean (by positivity)).trans ?_
    have hp := mul_le_mul_of_nonneg_right (show γ + 2 * (h : ℝ)⁻¹ ≤ 3 * γ by linarith)
      (mul_nonneg hA hγ)
    nlinarith only [hp]
  linarith only [hmul]


open Classical in
/-- Cancelling the normalizing factor recovers precisely the retained
weight counted in the lower-overlap estimate. -/
theorem normalized_counted_mass (B C F : Finset V) (kept : Prop) (raw : V → ℝ)
    (z ell : ℝ) (hell : ell ≠ 0) :
    let restricted := fun x => if x ∈ F then raw x else 0
    ell * mass (normalizedOverlap B z ell kept restricted) C =
      (if kept ∧ mass raw (B ∩ F) ≤ 16 * z then mass raw (C ∩ F) else 0) := by
  classical
  intro restricted
  have hrestrict (A : Finset V) : mass restricted A = mass raw (A ∩ F) := by
    simp only [mass, restricted, ← Finset.sum_filter, Finset.filter_mem_eq_inter]
  by_cases h : kept ∧ mass raw (B ∩ F) ≤ 16 * z
  · have hw : normalizedOverlap B z ell kept restricted = fun x => restricted x / ell := by
      funext x
      unfold normalizedOverlap
      rw [hrestrict B, if_pos h]
    rw [hw, if_pos h, ← hrestrict C]
    simp only [mass, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    field_simp
  · have hw : normalizedOverlap B z ell kept restricted = fun _ => 0 := by
      funext x
      unfold normalizedOverlap
      rw [hrestrict B, if_neg h]
    rw [hw, if_neg h]
    simp [mass]

open Classical in
/-- The same normalization and counting condition are used in both
overlap arguments. Once the required clique and the marked-weight bound
are available, the resulting inequalities give a contradiction. -/
theorem counted_overlap_impossible (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset I) {q h : ℕ} (hq : 2 ≤ q) (hh : 0 < h)
    (hU : U.card = q * h) (hsize : ∀ i : ↥U, 2 * (q - 1) * (q - 1) ≤ (U.erase i.val).card)
    (blocks : (i : ↥U) → Fin h → Finset ↥(U.erase i.val))
    (hblock : ∀ i j, (blocks i j).card = q - 1)
    (hdisj : ∀ i, Pairwise (fun j l => Disjoint (blocks i j) (blocks i l)))
    (B C : Finset V) (hCB : C ⊆ B) (kept : Finset I → Prop)
    (raw : Finset I → V → ℝ) (F : I → Finset V)
    (hraw : ∀ J x, 0 ≤ raw J x)
    (z : I → ℝ) (hz : ∀ i, 0 ≤ z i)
    {γ D v g A : ℝ} (hγ : 0 < γ) (hD : 0 < D) (hg : 0 < g) (hgv : g ≤ v) (hA : 0 ≤ A)
    (hhγ : (h : ℝ)⁻¹ ≤ γ)
    (hMean : (∑ i ∈ U, 16 * (z i + γ)) / U.card ≤ A * γ)
    (hNon : ∀ x ∈ C,
      (∑ J ∈ U.powersetCard q, mass (raw J) (nonNeighbors G C x)) / (U.powersetCard q).card ≤
        2 * v / ((h : ℝ) * D))
    (hmarked : ∀ i : ↥U,
      let π := FiniteLaw.uniform (Equiv.Perm ↥(U.erase i.val))
      let avg (p : Equiv.Perm ↥(U.erase i.val)) (x : V) :=
        (h : ℝ)⁻¹ * ∑ j, let J := restoreAnchor U i.val ((blocks i j).map p.toEmbedding)
        normalizedOverlap B (z i.val) (16 * (z i.val + γ)) (kept J)
          (fun y => if y ∈ F i.val then raw J y else 0) x
      π.mean (fun p => mass (avg p) (marked G (avg p) B γ)) ≤ ((h : ℝ)⁻¹) ^ 2)
    (hsmall : 4 / (D * γ) + (3 * A) * γ / g < 1 / 9)
    (hLower : let groups := U.powersetCard q
      γ * v / 9 ≤ (∑ J ∈ groups, (∑ i ∈ J,
        if kept J ∧ mass (raw J) (B ∩ F i) ≤ 16 * z i then mass (raw J) (C ∩ F i) else 0) / q) /
        groups.card) : False := by
  let ell (i : I) := 16 * (z i + γ)
  let restricted (i : I) (J : Finset I) (x : V) := if x ∈ F i then raw J x else 0
  let w (i : I) (J : Finset I) := normalizedOverlap B (z i) (ell i) (kept J) (restricted i J)
  have hell (i : I) : 0 < ell i := by
    dsimp [ell]
    linarith only [hz i, hγ]
  have hle (i : I) (J : Finset I) (x : V) : w i J x ≤ raw J x / ell i := by
    dsimp [w, normalizedOverlap]
    split
    · apply div_le_div_of_nonneg_right _ (hell i).le
      dsimp [restricted]
      split <;> simp only [le_refl, hraw]
    · exact div_nonneg (hraw J x) (hell i).le
  have hW (i : I) (J : Finset I) (x : V) : 0 ≤ w i J x := by
    dsimp [w, normalizedOverlap]
    split
    · apply div_nonneg _ (hell i).le
      dsimp [restricted]
      split <;> simp only [le_refl, hraw]
    · rfl
  have hTotal (i : I) (J : Finset I) : mass (w i J) B ≤ 1 := by
    have he := normalized_counted_mass B B (F i) (kept J) (raw J) (z i) (ell i) (hell i).ne'
    change ell i * mass (w i J) B = _ at he
    rw [← mul_le_mul_iff_of_pos_left (hell i), mul_one, he]
    split
    · dsimp [ell]
      linarith only [‹kept J ∧ mass (raw J) (B ∩ F i) ≤ 16 * z i›.2, hγ]
    · exact (hell i).le
  have hUpper := mean_overlap_upper G U hq hh hU hsize blocks hblock hdisj
    B C hCB raw w hraw hW ell (fun i _ => hell i) hγ.le hD (hg.trans_le hgv).le hA hhγ
    hMean (fun i _ J x => hle i J x) (fun i _ J _ => hTotal i J)
    (fun x hx => hNon x hx) (fun i => hmarked i)
  have he (i : I) (J : Finset I) : ell i * mass (w i J) C =
      if kept J ∧ mass (raw J) (B ∩ F i) ≤ 16 * z i then mass (raw J) (C ∩ F i) else 0 :=
    normalized_counted_mass B C (F i) (kept J) (raw J) (z i) (ell i) (hell i).ne'
  simp_rw [he] at hUpper
  exact overlap_bounds_incompatible hg hgv hγ hD (by positivity) hsmall hLower hUpper

end LocallyRamsey
