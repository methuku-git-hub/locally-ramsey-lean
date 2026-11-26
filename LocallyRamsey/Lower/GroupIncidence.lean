module

public import LocallyRamsey.Lower.CompanionGroups

public section

open scoped BigOperators

namespace LocallyRamsey

variable {I : Type*} [DecidableEq I]

/-- Counting incidences in either order gives the same average at a
position of a group. The group size must be positive and at most the
number of positions. -/
theorem mean_group_position_eq_mean_position_group
    (U : Finset I) (q : ℕ) (hq : 0 < q) (hqU : q ≤ U.card) (f : I → Finset I → ℝ) :
    let groups := U.powersetCard q
    let through (i : I) := groups.filter (fun J => i ∈ J)
    (∑ J ∈ groups, (∑ i ∈ J, f i J) / q) / groups.card =
      (∑ i ∈ U, (∑ J ∈ through i, f i J) / (through i).card) / U.card := by
  classical
  intro groups through
  let k := (U.card - 1).choose (q - 1)
  have hc (i : I) (hi : i ∈ U) : (through i).card = k := by
    have hsub : ({i} : Finset I) ⊆ U := Finset.singleton_subset_iff.mpr hi
    have hs : ({i} : Finset I).card ≤ q := by simpa using (Nat.succ_le_of_lt hq)
    simpa only [through, groups, k, Finset.singleton_subset_iff, Finset.card_singleton] using
      Finset.card_filter_powersetCard_subset {i} U q hsub hs
  have hcount : groups.card * q = U.card * k := by
    have h := Nat.choose_mul (n := U.card) (k := q) (s := 1) (Nat.succ_le_of_lt hq)
    change (U.powersetCard q).card * q = _
    rw [Finset.card_powersetCard]
    simpa only [Nat.choose_one_right, k] using h
  have hcountR : (groups.card : ℝ) * q = (U.card : ℝ) * k := by exact_mod_cast hcount
  have hsum :
      (∑ J ∈ groups, ∑ i ∈ J, f i J) = ∑ i ∈ U, ∑ J ∈ through i, f i J := by
    have hrow (J : Finset I) (hJ : J ∈ groups) :
        ∑ i ∈ J, f i J = ∑ i ∈ U, if i ∈ J then f i J else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hJ).1]
    refine (Finset.sum_congr rfl hrow).trans ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_filter]
  have hrhs :
      (∑ i ∈ U, (∑ J ∈ through i, f i J) / (through i).card) / U.card =
        ((∑ i ∈ U, ∑ J ∈ through i, f i J) / k) / U.card := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [hc i hi])]
    congr 1
    exact (Finset.sum_div _ _ _).symm
  rw [hrhs, ← Finset.sum_div, hsum, div_div, div_div, mul_comm (q : ℝ), mul_comm (k : ℝ), hcountR]

/-- The fraction of all groups containing a specified position is the
group size divided by the number of positions. -/
theorem fraction_groups_through (U : Finset I) {i : I} (hi : i ∈ U)
    (q : ℕ) (hq : 0 < q) (hqU : q ≤ U.card) :
    let groups := U.powersetCard q
    let through := groups.filter (fun J => i ∈ J)
    (through.card : ℝ) / groups.card = (q : ℝ) / U.card := by
  classical
  intro groups through
  have hc : through.card = (U.card - 1).choose (q - 1) := by
    have hsub : ({i} : Finset I) ⊆ U := Finset.singleton_subset_iff.mpr hi
    have hs : ({i} : Finset I).card ≤ q := by simpa using (Nat.succ_le_of_lt hq)
    simpa only [through, groups, Finset.singleton_subset_iff, Finset.card_singleton] using
      Finset.card_filter_powersetCard_subset {i} U q hsub hs
  have hcount : groups.card * q = U.card * through.card := by
    have h := Nat.choose_mul (n := U.card) (k := q) (s := 1) (Nat.succ_le_of_lt hq)
    rw [hc]
    change (U.powersetCard q).card * q = _
    simpa only [Nat.choose_one_right, Finset.card_powersetCard] using h
  have hU0 : (U.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨i, hi⟩).ne'
  have hgroups0 : (groups.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hqU)).ne'
  apply (div_eq_div_iff hgroups0 hU0).mpr
  have hcountR : (groups.card : ℝ) * q = (U.card : ℝ) * through.card := by exact_mod_cast hcount
  linarith only [hcountR]

end LocallyRamsey
