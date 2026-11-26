module

public import LocallyRamsey.IndependentBlocks
public import Mathlib.Analysis.Convex.Jensen

public section

open scoped BigOperators

namespace LocallyRamsey.FiniteLaw

variable {I J P : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype P] {S : I → Type*} [∀ i, Fintype (S i)]

/-- If every block in every partition has expected score at most (z/4),
then the partition-averaged score has the same exponential tail as the
mean of disjoint blocks. The law on partitions is independent of the data. -/
theorem event_group_average_gt_le
    (μ : ∀ i, FiniteLaw (S i)) (π : FiniteLaw P) (label : P → I → J)
    (X : (p : P) → (j : J) → Block (label p) j S → ℝ)
    (hX : ∀ p j s, X p j s ∈ Set.Icc (0 : ℝ) 1)
    {z : ℝ} (hz : 0 ≤ z)
    (hmean : ∀ p j, (product (fun i : {i // label p i = j} => μ i.val)).mean (X p j) ≤ z / 4) :
    (product μ).event (fun ω =>
      (Fintype.card J : ℝ) * z < π.mean (fun p => ∑ j, X p j (fun i => ω i.val))) ≤
      Real.exp (-((Fintype.card J : ℝ) * z) / 2) := by
  classical
  let ν := product μ
  let h : ℝ := Fintype.card J
  let total (ω : (i : I) → S i) (p : P) := ∑ j, X p j (fun i => ω i.val)
  let avg (ω : (i : I) → S i) := π.mean (total ω)
  have hjensen (ω : (i : I) → S i) :
      Real.exp (avg ω) ≤ π.mean (fun p => Real.exp (total ω p)) := by
    simpa only [avg, mean, smul_eq_mul] using
      (convexOn_exp.map_sum_le (t := Finset.univ) (w := π.prob) (p := total ω)
        (fun p _ => π.nonneg p) π.total (fun _ _ => Set.mem_univ _))
  have hmoment (p : P) : ν.mean (fun ω => Real.exp (total ω p)) ≤
      Real.exp ((Real.exp 1 - 1) * (h * z / 4)) := by
    let μp (j : J) : FiniteLaw (Block (label p) j S) :=
      product (fun i : {i // label p i = j} => μ i.val)
    change (product μ).mean (fun ω => Real.exp (∑ j, X p j (fun i => ω i.val))) ≤ _
    rw [mean_on_blocks μ (label p) (fun s => Real.exp (∑ j, X p j (s j)))]
    have hp := mean_exp_sum_le μp (X p) (hX p) 1
    simp only [one_mul] at hp
    refine hp.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ (by
      linarith [Real.add_one_le_exp (1 : ℝ)])))
    calc
      _ ≤ ∑ _j : J, z / 4 := Finset.sum_le_sum (fun j _ => hmean p j)
      _ = _ := by simp [h]; ring
  have hcomm : ν.mean (fun ω => π.mean (fun p => Real.exp (total ω p))) =
      π.mean (fun p => ν.mean (fun ω => Real.exp (total ω p))) := by
    simp only [mean, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  have hB : ν.mean (fun ω => Real.exp (avg ω)) ≤ Real.exp ((Real.exp 1 - 1) * (h * z / 4)) := by
    refine (ν.mean_mono hjensen).trans ?_
    rw [hcomm]
    exact (π.mean_mono hmoment).trans_eq (π.mean_const _)
  have he : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_d9]
  have ht : 0 ≤ h * z / 4 := by dsimp [h]; positivity
  calc
    _ ≤ ν.event (fun ω => Real.exp (h * z) ≤ Real.exp (avg ω)) :=
      ν.event_mono (fun _ hω => (Real.exp_le_exp.mpr hω.le))
    _ ≤ _ := ν.event_ge_le (fun _ => (Real.exp_pos _).le) (Real.exp_pos (h * z))
    _ ≤ Real.exp ((Real.exp 1 - 1) * (h * z / 4)) / Real.exp (h * z) :=
      div_le_div_of_nonneg_right hB (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← Real.exp_sub]
      refine Real.exp_le_exp.mpr ?_
      exact (sub_le_sub_right (mul_le_mul_of_nonneg_right he ht) (h * z)).trans_eq (by ring)

end LocallyRamsey.FiniteLaw
