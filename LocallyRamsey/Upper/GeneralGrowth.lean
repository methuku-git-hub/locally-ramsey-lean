module

public import LocallyRamsey.Upper.LocalBound

public section

namespace LocallyRamsey.BinaryTree

/-- A uniform growth bound at general target `r`, before the final
reversals. Its leading terms are the ones used in equation (2). -/
theorem threshold_general_exp {T r : ℕ} (hT : 0 < T) (hr : 2 ≤ r) (hrT : r ≤ 2 ^ T)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    let S := max 2 ⌈2 / ε⌉₊
    let d := -Real.log ((1 + 2 * ε) / 2)
    let A := 3 * Real.log (T : ℝ) + Real.log (r : ℝ) + Real.log (8000 / ε)
    (threshold (2 ^ T) r : ℝ) ≤
      Real.exp ((S + 1 : ℕ) * (A + Real.log S) + iterationPotential A d (Real.log r) + Real.log 2) := by
  intro S d A
  let a := mergeOrder ε
  let p := reversalRate T r ε
  let q := fun s => mergeCount T p (a s)
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hTr : 0 < (T : ℝ) := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have hrr : 0 < (r : ℝ) := by linarith
  have hL : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hT1
  have hV : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr1
  have hK : 1 ≤ 8000 / ε := by rw [le_div_iff₀ hε]; linarith
  have hc : 0 ≤ Real.log (8000 / ε) := Real.log_nonneg hK
  have hd : 0 < d := neg_pos.mpr (Real.log_neg (by positivity) (by linarith))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : 2 ≤ S := le_max_left _ _
  have hAexp : Real.exp A = (8000 / ε) * (T : ℝ) ^ 3 * r := by
    dsimp [A]
    rw [Real.exp_add, Real.exp_add, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log hTr, Real.exp_log hrr, Real.exp_log (by linarith : 0 < 8000 / ε)]
    ring
  have hTpow : (T : ℝ) ^ 2 ≤ (T : ℝ) ^ 3 := pow_le_pow_right₀ hT1 (by norm_num)
  have hcost (s : ℕ) (hs : 2 < s) (hsr : s ≤ r) :
      (2 * T * q s : ℕ) ≤ Real.exp (A + Real.log s) := by
    have hq := mergeCount_le hT hr hs.le hε hε'
    change (q s : ℝ) ≤ _ at hq
    rw [Real.exp_add, hAexp, Real.exp_log (by exact_mod_cast (by omega : 0 < s))]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * T by positivity)
    convert hh using 1
    ring
  have hbase : (q 2 : ℝ) ≤ Real.exp A := by
    have hq := mergeCount_le hT hr le_rfl hε hε'
    change (q 2 : ℝ) ≤ _ at hq
    rw [hAexp]
    refine hq.trans ?_
    rw [show 4000 / ε * (2 : ℕ) * (T : ℝ) ^ 2 * r = (8000 / ε) * (T : ℝ) ^ 2 * r by ring]
    gcongr
  have hiter := mergingBound_exp (T := T) (a := a) (q := q) (r := r)
    hA hd hS (fun s hs _ => mergeOrder_bounds hε hε' hs) hbase hcost
    (fun s hs _ => mergeOrder_log_drop hε hε' hs) r hr le_rfl
  let X := ((S + 1 : ℕ) : ℝ) * (A + Real.log S) + iterationPotential A d (Real.log r)
  have hX : 0 ≤ X := by
    have hlogS : 0 ≤ Real.log (S : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ S))
    have hI := iterationPotential_nonneg hA hd hV
    dsimp [X]
    positivity
  have hle := threshold_binary_bound hT hr hrT hε hε'
  change threshold (2 ^ T) r ≤ mergingBound T a q r + 1 at hle
  have hle' : (threshold (2 ^ T) r : ℝ) ≤ (mergingBound T a q r : ℝ) + 1 := by exact_mod_cast hle
  calc
    _ ≤ Real.exp X + 1 := by linarith [hiter]
    _ ≤ Real.exp X * 2 := by linarith [Real.one_le_exp_iff.mpr hX]
    _ = _ := by
      change Real.exp X * 2 = Real.exp (X + Real.log 2)
      rw [Real.exp_add X (Real.log 2), Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end LocallyRamsey.BinaryTree
