module

public import LocallyRamsey.Upper.Recurrence
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

namespace LocallyRamsey.BinaryTree

/-- The logarithmic potential for the iteration. Dropping the logarithm
of the target by at least `d` pays for one step of cost `A + x`. -/
noncomputable def iterationPotential (A d x : ℝ) : ℝ :=
  (A + d / 2) * x / d + x ^ 2 / (2 * d)

theorem iterationPotential_nonneg {A d x : ℝ} (hA : 0 ≤ A) (hd : 0 < d) (hx : 0 ≤ x) :
    0 ≤ iterationPotential A d x := by
  unfold iterationPotential
  positivity

theorem iterationPotential_step {A d x y : ℝ} (hA : 0 ≤ A) (hd : 0 < d)
    (hy : 0 ≤ y) (hdrop : y ≤ x - d) :
    A + x + iterationPotential A d y ≤ iterationPotential A d x := by
  have hmon : iterationPotential A d y ≤ iterationPotential A d (x - d) := by
    unfold iterationPotential
    gcongr
  have hstep : A + x + iterationPotential A d (x - d) = iterationPotential A d x := by
    unfold iterationPotential
    field_simp
    ring
  rw [← hstep]
  exact add_le_add_right hmon _

/-- A bound for the iteration through a fixed finite range of target orders. -/
theorem mergingBound_small {T : ℕ} {a q : ℕ → ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hbase : (q 2 : ℝ) ≤ Real.exp B)
    (s : ℕ) (hstep : ∀ k, 2 < k → k ≤ s → (2 * T * q k : ℕ) ≤ Real.exp B) :
    (mergingBound T a q s : ℝ) ≤ Real.exp ((s + 1 : ℕ) * B) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    rw [mergingBound]
    split
    · rename_i h
      have h₁ := hstep s h.1 le_rfl
      have h₂ := ih (a s) h.2 (fun k hk hks => hstep k hk (hks.trans h.2.le))
      push_cast at h₂ ⊢
      calc
        _ ≤ Real.exp B * Real.exp (((a s : ℝ) + 1) * B) :=
          mul_le_mul (by exact_mod_cast h₁) h₂ (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ ≤ _ := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hlt : (a s : ℝ) + 1 ≤ s := by exact_mod_cast h.2
          nlinarith [mul_le_mul_of_nonneg_right hlt hB]
    · exact hbase.trans (Real.exp_le_exp.mpr (by
        have hs : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
        push_cast
        nlinarith [mul_nonneg hs hB]))

/-- The real exponential bound for the iterated merging recurrence.
Above a fixed order, the logarithm of the target drops by at least `d`
and a step at order `s` costs at most `exp (A + log s)`. -/
theorem mergingBound_exp {T : ℕ} {a q : ℕ → ℕ} {A d : ℝ} {S r : ℕ}
    (hA : 0 ≤ A) (hd : 0 < d) (hS : 2 ≤ S)
    (ha : ∀ s, 2 < s → s ≤ r → 2 ≤ a s ∧ a s < s)
    (hbase : (q 2 : ℝ) ≤ Real.exp A)
    (hcost : ∀ s, 2 < s → s ≤ r → (2 * T * q s : ℕ) ≤ Real.exp (A + Real.log s))
    (hdrop : ∀ s, S < s → s ≤ r → Real.log (a s : ℝ) ≤ Real.log s - d)
    (s : ℕ) (hs : 2 ≤ s) (hr : s ≤ r) :
    (mergingBound T a q s : ℝ) ≤
      Real.exp ((S + 1 : ℕ) * (A + Real.log S) + iterationPotential A d (Real.log s)) := by
  have hlogS : 0 ≤ Real.log (S : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ S))
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hstop : s ≤ S
    · have hB : 0 ≤ A + Real.log (S : ℝ) := add_nonneg hA hlogS
      have hbase' : (q 2 : ℝ) ≤ Real.exp (A + Real.log S) :=
        hbase.trans (Real.exp_le_exp.mpr (by linarith))
      have hcost' (k : ℕ) (hk : 2 < k) (hks : k ≤ s) :
          (2 * T * q k : ℕ) ≤ Real.exp (A + Real.log S) := by
        have hlog := Real.log_le_log (show 0 < (k : ℝ) by exact_mod_cast (by omega : 0 < k))
          (show (k : ℝ) ≤ S by exact_mod_cast hks.trans hstop)
        exact (hcost k hk (hks.trans hr)).trans (Real.exp_le_exp.mpr (add_le_add_right hlog A))
      refine (mergingBound_small hB hbase' s hcost').trans (Real.exp_le_exp.mpr ?_)
      have hpot : 0 ≤ iterationPotential A d (Real.log (s : ℝ)) :=
        iterationPotential_nonneg hA hd (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ s)))
      have hss : ((s + 1 : ℕ) : ℝ) ≤ (S + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hstop
      exact (mul_le_mul_of_nonneg_right hss hB).trans (le_add_of_nonneg_right hpot)
    · have hbig : 2 < s := by omega
      obtain ⟨ha₂, has⟩ := ha s hbig hr
      have hsa := ih (a s) has ha₂ (has.le.trans hr)
      rw [mergingBound, dite_eq_left ⟨hbig, has⟩]
      push_cast
      calc
        _ ≤ Real.exp (A + Real.log (s : ℝ)) *
            Real.exp (((S : ℝ) + 1) * (A + Real.log S) +
              iterationPotential A d (Real.log (a s : ℝ))) := by
          have hc := hcost s hbig hr
          push_cast at hc hsa
          apply mul_le_mul hc hsa (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ ≤ _ := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hpot := iterationPotential_step hA hd
            (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ a s))) (hdrop s (by omega) hr)
          linarith

/-- The leading coefficient of the logarithmic bound is 9/2 at target
`r = T`. All other terms are at most linear in `log T`. -/
theorem iterationPotential_local {d L c : ℝ} (hd : d ≠ 0) :
    iterationPotential (4 * L + c) d L =
      (9 / 2) / d * L ^ 2 + (c / d + 1 / 2) * L := by
  unfold iterationPotential
  field_simp
  ring

/-- The leading coefficient is 12 at target `r = 100 T^2`.
Here `b` absorbs the factor 100 in the logarithm of the target. -/
theorem iterationPotential_global {d L c b : ℝ} (hd : d ≠ 0) :
    iterationPotential (5 * L + c) d (2 * L + b) =
      12 / d * L ^ 2 + ((7 * b + 2 * c) / d + 1) * L +
        ((c * b + b ^ 2 / 2) / d + b / 2) := by
  unfold iterationPotential
  field_simp
  ring

end LocallyRamsey.BinaryTree
