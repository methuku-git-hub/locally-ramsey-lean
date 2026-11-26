module

public import LocallyRamsey.DensityComparison
public import LocallyRamsey.Lower.OverlapAssembly

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- The mass where a new density is larger than four times the comparison
density, measured with the new density itself. -/
theorem mean_density_restriction_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (a b : Ω → ℝ) (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω)
    (hmean : μ.mean a = 1) (P : Ω → Prop) [DecidablePred P]
    (hP : ∀ ω, P ω → 4 * b ω < a ω) :
    μ.mean (fun ω => if P ω then a ω else 0) ≤ 4 * rootDistance μ a b := by
  have heq : μ.mean (fun ω => if P ω then a ω else 0) =
      (μ.withDensity a ha hmean).event P := by
    rw [← (μ.withDensity a ha hmean).mean_indicator]
    simp only [FiniteLaw.mean, FiniteLaw.withDensity]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : P ω <;> simp [h]
  rw [heq]
  exact ((μ.withDensity a ha hmean).event_mono hP).trans
    (event_density_gt_four_le μ a b ha hb hmean)

/-- Mass lost by discarding one position whose retained mass is too large.
When the retained set is sufficiently large its density has the comparison
bound, and for a small retained set the original mass is already small. -/
theorem mean_discarded_position_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (a b : Ω → ℝ) (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω)
    (hmean : μ.mean a = 1) (good : Ω → Prop) [DecidablePred good]
    (hgood : ∀ ω, good ω → b ω ≤ 2) {z τ ε : ℝ}
    (hz : 0 ≤ z) (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hsmall_or_close : z ≤ τ ∨ rootDistance μ a b ≤ 2 * ε) :
    μ.mean (fun ω => if good ω ∧ 16 * z < z * a ω then z * a ω else 0) ≤
      τ + 8 * ε * z := by
  rcases hsmall_or_close with hsmall | hclose
  · calc
      _ ≤ μ.mean (fun ω => z * a ω) := μ.mean_mono fun ω => by
        split
        · exact le_rfl
        · exact mul_nonneg hz (ha ω)
      _ = z := by rw [μ.mean_mul_const, hmean, mul_one]
      _ ≤ _ := by linarith only [hsmall, mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (8 : ℝ)) hε) hz]
  · by_cases hz' : z = 0
    · simp only [hz', mul_zero, zero_mul, lt_self_iff_false, and_false, ite_false, FiniteLaw.mean_const,
        add_zero]
      exact hτ
    have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz')
    let P := fun ω => good ω ∧ 16 * z < z * a ω
    have hrel (ω : Ω) (h : P ω) : 4 * b ω < a ω := by
      have hd : 16 < a ω := (mul_lt_mul_iff_right₀ hzpos).mp (by simpa [mul_comm] using h.2)
      linarith only [hgood ω h.1, hd]
    have heq : (fun ω => if P ω then z * a ω else 0) =
        (fun ω => z * (if P ω then a ω else 0)) := by
      ext ω
      split <;> simp_all
    change μ.mean (fun ω => if P ω then z * a ω else 0) ≤ _
    rw [heq, μ.mean_mul_const]
    have hh := mul_le_mul_of_nonneg_left (mean_density_restriction_le μ a b ha hb hmean P hrel) hz
    have hd := mul_le_mul_of_nonneg_left hclose (show 0 ≤ 4 * z by positivity)
    nlinarith only [hh, hd, hτ]

/-- Discarding positions can make a previously frequent vertex infrequent
only when it loses at least the difference in the two required counts. -/
theorem mass_after_discarding_positions_le {q : ℕ}
    (B : Finset V) (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (F : Fin q → Finset V) (counted : Finset (Fin q)) {t : ℝ} (ht : 0 < t) :
    let initialBad := B.filter (fun x =>
      ((Finset.univ.filter (fun i => x ∈ F i)).card : ℝ) < 2 * t)
    let finalBad := B.filter (fun x =>
      ((counted.filter (fun i => x ∈ F i)).card : ℝ) < t)
    mass w finalBad ≤ mass w initialBad +
      (∑ i ∈ Finset.univ \ counted, mass w (B ∩ F i)) / t := by
  classical
  intro initialBad finalBad
  let loss (x : V) := ((Finset.univ \ counted).filter (fun i => x ∈ F i)).card
  have hs (x : V) : (Finset.univ.filter (fun i => x ∈ F i)).card =
      (counted.filter (fun i => x ∈ F i)).card + loss x := by
    have h : (counted.filter (fun i => x ∈ F i)) ∪ ((Finset.univ \ counted).filter (fun i => x ∈ F i)) =
        Finset.univ.filter (fun i => x ∈ F i) := by
      ext i
      by_cases hi : i ∈ counted <;> simp [hi]
    rw [← h, Finset.card_union_of_disjoint]
    exact Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hj).1).2
      (Finset.mem_filter.mp hi).1)
  have hmass :
      (∑ i ∈ Finset.univ \ counted, mass w (B ∩ F i)) = ∑ x ∈ B, (loss x : ℝ) * w x := by
    have hr (i : Fin q) : mass w (B ∩ F i) = ∑ x ∈ B, if x ∈ F i then w x else 0 := by
      rw [mass, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
    simp only [hr]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun x _ => by
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, loss])
  have hB : finalBad ⊆ B := Finset.filter_subset _ _
  have hineq : t * mass w (finalBad \ initialBad) ≤ ∑ x ∈ B, (loss x : ℝ) * w x := by
    rw [mass, Finset.mul_sum]
    refine (Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right ?_ (hw x))).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset.trans hB) (fun x _ _ => mul_nonneg (Nat.cast_nonneg _) (hw x)))
    obtain ⟨hf, hn⟩ := Finset.mem_sdiff.mp hx
    have hcut : (((counted.filter (fun i => x ∈ F i)).card) : ℝ) < t := (Finset.mem_filter.mp hf).2
    have htotal : 2 * t ≤ ((Finset.univ.filter (fun i => x ∈ F i)).card : ℝ) :=
      le_of_not_gt fun h => hn (Finset.mem_filter.mpr ⟨hB hf, h⟩)
    rw [hs, Nat.cast_add] at htotal
    linarith only [hcut, htotal]
  have hsplit : mass w finalBad ≤ mass w initialBad + mass w (finalBad \ initialBad) := by
    have hsub : finalBad ⊆ initialBad ∪ (finalBad \ initialBad) := by
      intro x hx
      by_cases hx' : x ∈ initialBad <;> simp [hx, hx']
    refine (mass_mono hw hsub).trans_eq ?_
    unfold mass
    rw [Finset.sum_union (Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx))]
  rw [hmass]
  have hdiv : mass w (finalBad \ initialBad) ≤ (∑ x ∈ B, (loss x : ℝ) * w x) / t :=
    (le_div_iff₀ ht).mpr (by rw [mul_comm]; exact hineq)
  linarith only [hsplit, hdiv]

/-- The total mass retained too rarely in a kept group is bounded by the
loss before testing positions and the sum of the masses at rejected
positions. Discarded groups contribute zero. -/
theorem mean_weight_after_position_tests_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) {q : ℕ} (B : Finset V) (w : Ω → V → ℝ)
    (hw : ∀ ω x, 0 ≤ w ω x) (F : Ω → Fin q → Finset V)
    (kept : Ω → Prop) [DecidablePred kept] (counted : Ω → Finset (Fin q))
    {t a b : ℝ} (ht : 0 < t)
    (hinitial : μ.mean (fun ω => mass (w ω) (B.filter fun x =>
      ((Finset.univ.filter (fun i => x ∈ F ω i)).card : ℝ) < 2 * t)) ≤ a)
    (hloss : ∀ i, μ.mean (fun ω => if kept ω ∧ i ∉ counted ω then mass (w ω) (B ∩ F ω i)
      else 0) ≤ b) :
    μ.mean (fun ω => if kept ω then mass (w ω) (B.filter fun x =>
      (((counted ω).filter (fun i => x ∈ F ω i)).card : ℝ) < t) else 0) ≤
      a + (q : ℝ) * b / t := by
  classical
  let loss (i : Fin q) (ω : Ω) :=
    if kept ω ∧ i ∉ counted ω then mass (w ω) (B ∩ F ω i) else 0
  let init (ω : Ω) := mass (w ω) (B.filter fun x =>
    ((Finset.univ.filter (fun i => x ∈ F ω i)).card : ℝ) < 2 * t)
  let final (ω : Ω) := if kept ω then mass (w ω) (B.filter fun x =>
    (((counted ω).filter (fun i => x ∈ F ω i)).card : ℝ) < t) else 0
  have hpoint (ω : Ω) : final ω ≤ init ω + (∑ i, loss i ω) / t := by
    by_cases hk : kept ω
    · have hsum : ∑ i, loss i ω =
          ∑ i ∈ Finset.univ \ counted ω, mass (w ω) (B ∩ F ω i) := by
        have hfilter : ((Finset.univ : Finset (Fin q)).filter (fun i => i ∉ counted ω)) =
            Finset.univ \ counted ω := by ext i; simp
        simp only [loss, hk, true_and, ← Finset.sum_filter, hfilter]
      simp only [final, ite_eq_left hk, hsum]
      exact mass_after_discarding_positions_le B (w ω) (hw ω) (F ω) (counted ω) ht
    · have hi : 0 ≤ init ω := Finset.sum_nonneg (fun x _ => hw ω x)
      simpa [final, hk, loss] using hi
  have hsum : μ.mean (fun ω => (∑ i, loss i ω) / t) ≤ q * b / t := by
    have heq : μ.mean (fun ω => (∑ i, loss i ω) / t) =
        (∑ i, μ.mean (loss i)) / t := by
      simp only [div_eq_inv_mul, μ.mean_mul_const, μ.mean_sum]
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ ht.le
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q))) (fun i _ => hloss i)
  have h := μ.mean_mono hpoint
  rw [μ.mean_add] at h
  exact h.trans (add_le_add hinitial hsum)

end LocallyRamsey
