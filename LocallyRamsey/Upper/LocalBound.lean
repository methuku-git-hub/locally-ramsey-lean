module

public import LocallyRamsey.Upper.Parameters

public section

namespace LocallyRamsey.BinaryTree

theorem mergeCount_le {T r s : ℕ} (hT : 0 < T) (hr : 2 ≤ r) (hs : 2 ≤ s)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    (mergeCount T (reversalRate T r ε) (mergeOrder ε s) : ℝ) ≤
      (4000 / ε) * (s : ℝ) * (T : ℝ) ^ 2 * r := by
  let a := mergeOrder ε s
  let p := reversalRate T r ε
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hs' : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hTr : 0 < (T : ℝ) := by linarith
  have hrr : 0 < (r : ℝ) := by linarith
  have hp : 0 < p := by dsimp [p, reversalRate]; exact div_pos hε (by positivity)
  have ha : a ≤ s := by
    by_cases h : s = 2
    · subst s
      norm_num [a, mergeOrder]
    · exact (mergeOrder_bounds hε hε' (by omega : 2 < s)).2.le
  have har : (a : ℝ) + 1 ≤ 2 * s := by
    have hh : (a : ℝ) ≤ s := by exact_mod_cast ha
    linarith
  have hlog : 0 ≤ Real.log ((2 : ℝ) ^ T) := Real.log_nonneg (one_le_pow₀ (by norm_num))
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hlogT : Real.log ((2 : ℝ) ^ T) ≤ T := by
    rw [Real.log_pow]
    nlinarith only [mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg T)]
  have hz : 0 ≤ 16 * ((a : ℝ) + 1) * Real.log ((2 : ℝ) ^ T) / p := by positivity
  have hceil := Nat.ceil_lt_add_one hz
  unfold mergeCount
  refine hceil.le.trans ?_
  have hscale : 16 * (2 * (s : ℝ)) * T / p =
      (3200 / ε) * s * (T : ℝ) ^ 2 * r := by
    dsimp [p, reversalRate]
    field_simp
    ring
  have hpad : 1 ≤ (800 / ε) * (s : ℝ) * (T : ℝ) ^ 2 * r := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hε]
    have hunit : (1 : ℝ) ≤ (s : ℝ) * T ^ 2 * r := by
      have hT2 : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
      have h1 : (1 : ℝ) ≤ (s : ℝ) * T ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith) hT2
      exact one_le_mul_of_one_le_of_one_le h1 (by linarith)
    nlinarith
  have harg : 16 * ((a : ℝ) + 1) * Real.log ((2 : ℝ) ^ T) / p ≤
      16 * (2 * (s : ℝ)) * T / p := by
    gcongr
  rw [hscale] at harg
  calc
    _ ≤ (3200 / ε) * (s : ℝ) * T ^ 2 * r + (800 / ε) * (s : ℝ) * T ^ 2 * r :=
      add_le_add harg hpad
    _ = _ := by ring

theorem mergeOrder_log_drop {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4)
    {s : ℕ} (hs : max 2 ⌈2 / ε⌉₊ < s) :
    Real.log (mergeOrder ε s : ℝ) ≤ Real.log s - (-Real.log ((1 + 2 * ε) / 2)) := by
  have h₂ : 2 < s := (le_max_left 2 _).trans_lt hs
  have hscale : 2 / ε ≤ (s : ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right 2 _).trans hs.le)
  have hscale' : 1 ≤ ε * (s : ℝ) / 2 := by
    have h := (div_le_iff₀ hε).mp hscale
    linarith
  let ratio := (1 + 2 * ε) / 2
  have hratio : 0 < ratio := by dsimp [ratio]; positivity
  have hratios : (mergeOrder ε s : ℝ) ≤ ratio * (s : ℝ) := by
    rw [mergeOrder, ite_eq_right (not_le.mpr h₂)]
    have h := Nat.ceil_lt_add_one (show 0 ≤ (1 + ε) / 2 * (s : ℝ) by positivity)
    dsimp [ratio]
    linarith
  have hpa : 0 < (mergeOrder ε s : ℝ) := by
    exact_mod_cast (show 0 < mergeOrder ε s from by
      have h := (mergeOrder_bounds hε hε' h₂).1
      omega)
  have h := Real.log_le_log hpa hratios
  rw [Real.log_mul hratio.ne' (by exact_mod_cast (by omega : s ≠ 0))] at h
  linarith

/-- The finite upper estimate on powers of two for target `T`. -/
theorem threshold_power_two_exp {T : ℕ} (hT : 2 ≤ T)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) :
    let S := max 2 ⌈2 / ε⌉₊
    let c := Real.log (8000 / ε)
    let d := -Real.log ((1 + 2 * ε) / 2)
    let L := Real.log (T : ℝ)
    (threshold (2 ^ T) T : ℝ) ≤
      Real.exp ((S + 1 : ℕ) * (4 * L + c + Real.log S) +
        ((9 / 2) / d) * L ^ 2 + (c / d + 1 / 2) * L + Real.log 2) := by
  intro S c d L
  let a := mergeOrder ε
  let p := reversalRate T T ε
  let q := fun s => mergeCount T p (a s)
  let A := 4 * L + c
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hTr : 0 < (T : ℝ) := by linarith
  have hL : 0 ≤ L := Real.log_nonneg hT1
  have hK : 1 ≤ 8000 / ε := by rw [le_div_iff₀ hε]; linarith
  have hc : 0 ≤ c := Real.log_nonneg hK
  have hd : 0 < d := by
    dsimp [d]
    exact neg_pos.mpr (Real.log_neg (by positivity) (by linarith))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hS : 2 ≤ S := le_max_left _ _
  have hAexp : Real.exp A = (8000 / ε) * (T : ℝ) ^ 4 := by
    dsimp [A, L, c]
    rw [Real.exp_add, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log hTr, Real.exp_log (by linarith : 0 < 8000 / ε), mul_comm]
  have hTpow : (T : ℝ) ^ 3 ≤ (T : ℝ) ^ 4 := pow_le_pow_right₀ hT1 (by norm_num)
  have hcost (s : ℕ) (hs : 2 < s) (hsT : s ≤ T) :
      (2 * T * q s : ℕ) ≤ Real.exp (A + Real.log s) := by
    have hq := mergeCount_le (by omega : 0 < T) hT hs.le hε hε'
    change (q s : ℝ) ≤ _ at hq
    rw [Real.exp_add, hAexp, Real.exp_log (by exact_mod_cast (by omega : 0 < s))]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 * T by positivity)
    convert hh using 1
    ring
  have hbase : (q 2 : ℝ) ≤ Real.exp A := by
    have hq := mergeCount_le (by omega : 0 < T) hT le_rfl hε hε'
    change (q 2 : ℝ) ≤ _ at hq
    rw [hAexp]
    refine hq.trans ?_
    rw [show 4000 / ε * (2 : ℕ) * (T : ℝ) ^ 2 * T = (8000 / ε) * (T : ℝ) ^ 3 by ring]
    exact mul_le_mul_of_nonneg_left hTpow (by positivity)
  have hiter := mergingBound_exp (T := T) (a := a) (q := q) (r := T)
    hA hd hS (fun s hs _ => mergeOrder_bounds hε hε' hs) hbase hcost
    (fun s hs _ => mergeOrder_log_drop hε hε' hs) T hT le_rfl
  rw [show Real.log (T : ℝ) = L from rfl, show A = 4 * L + c from rfl,
    iterationPotential_local hd.ne'] at hiter
  let X := ((S + 1 : ℕ) : ℝ) * (4 * L + c + Real.log S) +
    (9 / 2) / d * L ^ 2 + (c / d + 1 / 2) * L
  have hX : 0 ≤ X := by
    have hlogS : 0 ≤ Real.log (S : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ S))
    dsimp [X]
    positivity
  have hle := threshold_binary_bound (by omega : 0 < T) hT T.lt_two_pow_self.le hε hε'
  rw [show (mergingBound T (mergeOrder ε) (fun s => mergeCount T (reversalRate T T ε)
    (mergeOrder ε s)) T) = mergingBound T a q T from rfl] at hle
  have hle' : (threshold (2 ^ T) T : ℝ) ≤ (mergingBound T a q T : ℝ) + 1 := by exact_mod_cast hle
  calc
    _ ≤ Real.exp X + 1 := by
      have hh : (mergingBound T a q T : ℝ) ≤ Real.exp X := by
        simpa only [X, add_assoc] using hiter
      linarith
    _ ≤ Real.exp X * 2 := by linarith [Real.one_le_exp_iff.mpr hX]
    _ = _ := by
      change Real.exp X * 2 = Real.exp (X + Real.log 2)
      rw [Real.exp_add X (Real.log 2), Real.exp_log (by norm_num : (0 : ℝ) < 2)]

/-- The upper half of Theorem 1, with the exact coefficient and
the ceiling convention in the manuscript. -/
theorem main_upper_bound :
    ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (threshold n (target n) : ℝ) ≤
        (2 : ℝ) ^ ((9 / 2 + δ) * (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2) := by
  intro δ hδ
  let ℓ := Real.log 2
  have hℓ : 0 < ℓ := Real.log_pos (by norm_num)
  let β := (9 / 2 + δ) / ℓ
  have hβ : 0 < β := by dsimp [β]; positivity
  let ε := min (1 / 8 : ℝ) (δ / (4 * β))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε' : ε < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  let d := -Real.log ((1 + 2 * ε) / 2)
  have hd : 0 < d := neg_pos.mpr (Real.log_neg (by positivity) (by linarith))
  have hdℓ : ℓ - 2 * ε ≤ d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * ε by positivity)
    dsimp [d, ℓ]
    rw [Real.log_div (by positivity : 1 + 2 * ε ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  let α := (9 / 2 : ℝ) / d
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαβ : α < β := by
    have hgap : ε * (4 * β) ≤ δ := (le_div_iff₀ (by positivity : 0 < 4 * β)).mp
      (min_le_right _ _)
    have hβℓ : β * ℓ = 9 / 2 + δ := div_mul_cancel₀ _ hℓ.ne'
    apply (div_lt_iff₀ hd).mpr
    nlinarith only [hgap, hβℓ, mul_le_mul_of_nonneg_left hdℓ hβ.le, hδ]
  let S := max 2 ⌈2 / ε⌉₊
  let c := Real.log (8000 / ε)
  have hc : 0 ≤ c := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hlogS : 0 ≤ Real.log (S : ℝ) := Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ S from (by norm_num : 1 ≤ 2).trans (le_max_left _ _)))
  let B := 4 * ((S + 1 : ℕ) : ℝ) + c / d + 1 / 2
  let C := ((S + 1 : ℕ) : ℝ) * (c + Real.log S) + ℓ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let B' := 2 * α * ℓ + B
  let C' := α * ℓ ^ 2 + B * ℓ + C
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  let H := max 1 ((B' + C') / (β - α))
  have hH : 1 ≤ H := le_max_left _ _
  refine ⟨max 4 ⌈(2 : ℝ) ^ Real.exp H⌉₊, ?_⟩
  intro n hn
  let t := Real.logb 2 (n : ℝ)
  let T := target n
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast (le_max_left 4 _).trans hn
  have hnr : 0 < (n : ℝ) := by linarith
  have htr : 2 ≤ t := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hnr).mpr
    norm_num [Real.rpow_natCast]
    exact (le_max_left 4 _).trans hn
  have htT : t ≤ (T : ℝ) := Nat.le_ceil t
  have hT : 2 ≤ T := by exact_mod_cast htr.trans htT
  have hnt : n ≤ 2 ^ T := by rw [show T = Nat.clog 2 n from target_eq_clog n]; exact Nat.le_pow_clog (by decide) n
  have hTt : (T : ℝ) ≤ 2 * t := by
    have hround := Nat.ceil_lt_add_one (show 0 ≤ t by linarith)
    change (T : ℝ) < t + 1 at hround
    linarith
  let x := Real.log t
  let y := Real.log (T : ℝ)
  have hxy : y ≤ x + ℓ := by
    have h := Real.log_le_log (show 0 < (T : ℝ) by linarith) hTt
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0), add_comm] at h
    exact h
  have hy0 : 0 ≤ y := Real.log_nonneg (by linarith)
  have hxt : H ≤ x := by
    have hp : (2 : ℝ) ^ Real.exp H ≤ (n : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right 4 _).trans hn)
    have h := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hnr).mpr hp
    simpa [x] using Real.log_le_log (Real.exp_pos H) h
  have hx1 : 1 ≤ x := hH.trans hxt
  have hthreshold : (threshold n T : ℝ) ≤ threshold (2 ^ T) T := by
    exact_mod_cast threshold_mono_vertices hnt
  have hpow := threshold_power_two_exp hT hε hε'
  have hpow' : (threshold (2 ^ T) T : ℝ) ≤ Real.exp (α * y ^ 2 + B * y + C) := by
    refine hpow.trans_eq ?_
    dsimp [S, c, d, ℓ, α, y, B, C]
    congr 1
    ring
  have hmove : α * y ^ 2 + B * y + C ≤ α * x ^ 2 + B' * x + C' := by
    have hmono : α * y ^ 2 + B * y + C ≤ α * (x + ℓ) ^ 2 + B * (x + ℓ) + C := by gcongr
    dsimp [B', C']
    linarith only [hmono]
  have habsorb : B' * x + C' ≤ (β - α) * x ^ 2 := by
    have hbound : (B' + C') / (β - α) ≤ x := (le_max_right _ _).trans hxt
    have hh := (div_le_iff₀ (sub_pos.mpr hαβ)).mp hbound
    have hp := mul_le_mul_of_nonneg_right hh (zero_le_one.trans hx1)
    nlinarith only [hp, mul_le_mul_of_nonneg_left hx1 hC']
  have hconvert :
      Real.exp (β * x ^ 2) = (2 : ℝ) ^ ((9 / 2 + δ) * (Real.logb 2 t) ^ 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.logb]
    congr 1
    dsimp [β, x, ℓ]
    field_simp
  exact hthreshold.trans (hpow'.trans ((Real.exp_le_exp.mpr (by linarith)).trans_eq hconvert))

end LocallyRamsey.BinaryTree
