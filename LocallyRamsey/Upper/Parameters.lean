module

public import LocallyRamsey.Upper.UnionBound
public import LocallyRamsey.Upper.Growth
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.Complex.ExponentialBounds

public section

namespace LocallyRamsey.BinaryTree

/-- The target order in one descendant set. -/
@[expose] noncomputable def mergeOrder (ε : ℝ) (s : ℕ) : ℕ :=
  if s ≤ 2 then 1 else ⌈((1 + ε) / 2) * (s : ℝ)⌉₊

/-- The common probability of a reversal in the construction with target
`r` and depth `T`. -/
@[expose] noncomputable def reversalRate (T r : ℕ) (ε : ℝ) : ℝ :=
  ε / (100 * (T : ℝ) * (r : ℝ))

/-- The number of branches needed for the pairwise merging estimate. -/
@[expose] noncomputable def mergeCount (T : ℕ) (p : ℝ) (a : ℕ) : ℕ :=
  ⌈16 * ((a : ℝ) + 1) * Real.log ((2 : ℝ) ^ T) / p⌉₊

theorem mergeOrder_bounds {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4)
    {s : ℕ} (hs : 2 < s) : 2 ≤ mergeOrder ε s ∧ mergeOrder ε s < s := by
  rw [mergeOrder, ite_eq_right (not_le.mpr hs)]
  let z := (1 + ε) / 2 * (s : ℝ)
  change 2 ≤ ⌈z⌉₊ ∧ ⌈z⌉₊ < s
  have hs' : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hz : 1 < z := by
    dsimp [z]
    nlinarith [mul_nonneg hε.le (show (0 : ℝ) ≤ s by positivity)]
  constructor
  · have hceil := Nat.le_ceil z
    by_contra! h
    have hn : (⌈z⌉₊ : ℝ) ≤ 1 := by exact_mod_cast (by omega : ⌈z⌉₊ ≤ 1)
    linarith
  · have hle : z ≤ (s : ℝ) - 1 := by
      dsimp [z]
      nlinarith [mul_nonneg (show 0 ≤ (1 / 4 : ℝ) - ε by linarith) (show (0 : ℝ) ≤ s by positivity)]
    have hnat : z ≤ ((s - 1 : ℕ) : ℝ) := by simpa [Nat.cast_sub (by omega : 1 ≤ s)] using hle
    have hceil := Nat.ceil_le.mpr hnat
    omega

theorem mergeOrder_room {ε : ℝ} {s : ℕ} (hs : 2 < s) :
    (1 + ε) * (s : ℝ) ≤ (mergeOrder ε s : ℝ) + mergeOrder ε s := by
  rw [mergeOrder, ite_eq_right (not_le.mpr hs)]
  linarith [Nat.le_ceil (((1 + ε) / 2) * (s : ℝ))]

/-- The loss estimate after a successful coin is comfortably below one half. -/
theorem merge_budget {T r s : ℕ} (hT : 0 < T) (hs : 2 ≤ s) (hsr : s ≤ r)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    let a := mergeOrder ε s
    let p := reversalRate T r ε
    (a : ℝ) * a * ((T : ℝ) * p) / ((a + a - s + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
  intro a p
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hr : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hpos : 0 < p := by dsimp [p, reversalRate]; positivity
  have hpT : (T : ℝ) * p = ε / (100 * r) := by
    dsimp [p, reversalRate]
    field_simp
  by_cases h₂ : s = 2
  · subst s
    have ha : a = 1 := by simp [a, mergeOrder]
    simp only [ha, Nat.reduceAdd, Nat.reduceSub, Nat.cast_one, one_mul, div_one]
    rw [hpT, div_le_iff₀ (by positivity : 0 < 100 * (r : ℝ))]
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hsr
    linarith
  · have hs₃ : 2 < s := by omega
    have ha' : a < s := (mergeOrder_bounds hε hε' hs₃).2
    have hroomr := mergeOrder_room (ε := ε) hs₃
    change (1 + ε) * (s : ℝ) ≤ (a : ℝ) + a at hroomr
    have hroom : s ≤ a + a := by
      exact_mod_cast (show (s : ℝ) ≤ (a : ℝ) + a by
        nlinarith [mul_nonneg hε.le (Nat.cast_nonneg s)])
    have hd : 0 < ((a + a - s + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hd, hpT]
    have hden : ε * (s : ℝ) ≤ ((a + a - s + 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hroom]
      linarith
    have hsq : (a : ℝ) * a ≤ (s : ℝ) * r := by
      exact mul_le_mul (by exact_mod_cast ha'.le)
        (by exact_mod_cast ha'.le.trans hsr) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hbound : (a : ℝ) * a * (ε / (100 * r)) ≤ ε * (s : ℝ) / 100 := by
      calc
        _ ≤ (s : ℝ) * r * (ε / (100 * r)) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = _ := by field_simp
    nlinarith

/-- The exponential union bound for one target at one depth. -/
theorem fixedLevel_bound {T a q : ℕ} (hT : 0 < T)
    {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1 / 2)
    (hq : 16 * ((a : ℝ) + 1) * Real.log ((2 : ℝ) ^ T) ≤ p * q) :
    ((2 ^ T : ℕ) : ℝ) ^ ((a + 1) * q) * (1 - p / 2) ^ q.choose 2 ≤
      1 / ((2 : ℝ) ^ T) ^ 4 := by
  let N := (2 : ℝ) ^ T
  let D := ((a : ℝ) + 1) * Real.log N
  have hN : (2 : ℝ) ≤ N := by simpa [N] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ T by omega)
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : (1 : ℝ) / 2 < Real.log N := hlog2.trans_le (Real.log_le_log (by norm_num) hN)
  have hD : 0 < D := by dsimp [D]; positivity
  have hDlog : Real.log N ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg (Nat.cast_nonneg a) (show 0 ≤ Real.log N by linarith)]
  have hq' : 16 * D ≤ p * q := by linarith only [hq]
  have hq4 : 4 ≤ q := by
    by_contra! hq4
    have hqs : (q : ℝ) < 4 := by exact_mod_cast hq4
    nlinarith [mul_le_mul_of_nonneg_right hp' (Nat.cast_nonneg q)]
  have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq4
  have hchoose : (q.choose 2 : ℝ) = (q : ℝ) * ((q : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ q
  have hstep : 1 - p / 2 ≤ Real.exp (-p / 2) := by linarith [Real.add_one_le_exp (-p / 2)]
  have hminor : 0 ≤ 1 - p / 2 := by linarith
  have heqN : N ^ ((a + 1) * q) = Real.exp (D * q) := by
    rw [← Real.exp_log (by linarith : 0 < N), ← Real.exp_nat_mul]
    congr 1
    dsimp [D]
    push_cast
    ring
  have hsmall : D * q + (q.choose 2 : ℝ) * (-p / 2) ≤ -4 * Real.log N := by
    rw [hchoose]
    have h₁ := mul_le_mul_of_nonneg_right hq' (show 0 ≤ (q : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left (show (q : ℝ) / 2 ≤ (q : ℝ) - 1 by linarith)
      (show 0 ≤ p * (q : ℝ) by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hqR hD.le
    nlinarith only [h₁, h₂, h₃, hDlog]
  push_cast
  change N ^ ((a + 1) * q) * (1 - p / 2) ^ q.choose 2 ≤ 1 / N ^ 4
  rw [heqN]
  calc
    _ ≤ Real.exp (D * q) * Real.exp (-p / 2) ^ q.choose 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hminor hstep _) (Real.exp_pos _).le
    _ = Real.exp (D * q + (q.choose 2 : ℝ) * (-p / 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (-4 * Real.log N) := Real.exp_le_exp.mpr hsmall
    _ = 1 / N ^ 4 := by
      rw [show -4 * Real.log N = -(4 * Real.log N) by ring, Real.exp_neg]
      rw [show 4 * Real.log N = ((4 : ℕ) : ℝ) * Real.log N by norm_num,
        Real.exp_nat_mul, Real.exp_log (show 0 < N by linarith), one_div]

/-- The manuscript's random construction admits a simultaneous merging
outcome with its explicit reversal probabilities and branch counts. -/
theorem exists_merges_with_parameters {T r : ℕ} (hT : 0 < T) (hr : 2 ≤ r) (hrT : r ≤ 2 ^ T)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    let p := reversalRate T r ε
    let a := mergeOrder ε
    let q := fun s => mergeCount T p (a s)
    ∃ G : SimpleGraph (Leaf T), ∀ s, 2 ≤ s → s ≤ r →
      ∀ j, 0 < j → j ≤ T → MergesAt G j (a s) s (q s) ∧ MergesAt Gᶜ j (a s) s (q s) := by
  intro p a q
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp : 0 < p := by dsimp [p, reversalRate]; positivity
  have hp' : p ≤ 1 / 2 := by
    dsimp [p, reversalRate]
    rw [div_le_iff₀ (by positivity : 0 < 100 * (T : ℝ) * r)]
    nlinarith [mul_le_mul hT' hr' (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ (T : ℝ))]
  let N := (2 : ℝ) ^ T
  have hN : 2 ≤ N := by simpa [N] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ T by omega)
  refine exists_simultaneous_merges hp.le hp' (B := 1 / N ^ 4) (by positivity)
    ?_ (fun s hs hsr => merge_budget hT hs hsr hε hε') ?_ ?_
  · intro s hs hsr
    by_cases h₂ : s = 2
    · subst s
      norm_num [a, mergeOrder]
    · have hs' : 2 < s := by omega
      obtain ⟨ha₂, _⟩ := mergeOrder_bounds hε hε' hs'
      have hroom := mergeOrder_room (ε := ε) hs'
      refine ⟨by dsimp [a]; omega, ?_⟩
      change (1 + ε) * (s : ℝ) ≤ (a s : ℝ) + a s at hroom
      exact_mod_cast (show (s : ℝ) ≤ (a s : ℝ) + a s by
        nlinarith [mul_nonneg hε.le (Nat.cast_nonneg s)])
  · intro s hs hsr
    apply fixedLevel_bound hT hp hp'
    have hceil := Nat.le_ceil (16 * ((a s : ℝ) + 1) * Real.log N / p)
    have hh := (div_le_iff₀ hp).mp hceil
    simpa [q, mergeCount, N, mul_comm p] using hh
  · have hTN : (T : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast (Nat.lt_two_pow_self (n := T)).le
    have hrN : (r : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast hrT
    push_cast
    rw [mul_one_div, div_lt_one (by positivity : 0 < N ^ 4)]
    have he := mul_le_mul hTN (show (r : ℝ) + 1 ≤ N + 1 by linarith)
      (by positivity : 0 ≤ (r : ℝ) + 1) (by positivity : 0 ≤ N)
    have hN₂ : (4 : ℝ) ≤ N ^ 2 := by nlinarith
    have hN₄ : 4 * N ^ 2 ≤ N ^ 4 := by nlinarith [mul_le_mul_of_nonneg_right hN₂ (sq_nonneg N)]
    nlinarith

/-- An explicit finite local threshold supplied by the construction.
The ensuing logarithmic growth estimate uses `mergingBound_exp`. -/
theorem threshold_binary_bound {T r : ℕ} (hT : 0 < T) (hr : 2 ≤ r) (hrT : r ≤ 2 ^ T)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    threshold (2 ^ T) r ≤ mergingBound T (mergeOrder ε)
      (fun s => mergeCount T (reversalRate T r ε) (mergeOrder ε s)) r + 1 := by
  let a := mergeOrder ε
  let p := reversalRate T r ε
  let q := fun s => mergeCount T p (a s)
  have hp : 0 < p := by dsimp [p, reversalRate]; positivity
  have hlog : 0 < Real.log ((2 : ℝ) ^ T) :=
    Real.log_pos (one_lt_pow₀ (by norm_num) hT.ne')
  have hq (s : ℕ) : 0 < q s := by
    have hz : 0 < 16 * ((a s : ℝ) + 1) * Real.log ((2 : ℝ) ^ T) / p := by positivity
    have hh := hz.trans_le (Nat.le_ceil _)
    dsimp [q, mergeCount]
    exact_mod_cast hh
  have ha₂ : a 2 = 1 := by simp [a, mergeOrder]
  obtain ⟨G, hG⟩ := exists_merges_with_parameters hT hr hrT hε hε'
  apply threshold_le_iff.mpr
  refine ⟨G, isLocallyRamsey_of_merges (a := a) (q := q) hT hr
    (fun s hs _ => mergeOrder_bounds hε hε' hs) (fun s _ _ => hq s) ?_ ?_ ?_ ?_⟩
  · rw [← ha₂]
    exact (hG 2 le_rfl hr T hT le_rfl).1
  · rw [← ha₂]
    exact (hG 2 le_rfl hr T hT le_rfl).2
  · exact fun s hs hsr j hj hjT => (hG s hs.le hsr j hj hjT).1
  · exact fun s hs hsr j hj hjT => (hG s hs.le hsr j hj hjT).2

end LocallyRamsey.BinaryTree
