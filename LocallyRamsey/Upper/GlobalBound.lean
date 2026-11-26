module

public import LocallyRamsey.Upper.GeneralGrowth
public import LocallyRamsey.Upper.GlobalReversal

public section

namespace LocallyRamsey.BinaryTree

private theorem target_le_tree_size {T : ℕ} (hT : 16 ≤ T) :
    100 * T ^ 2 ≤ 2 ^ T := by
  induction T, hT using Nat.le_induction with
  | base => decide
  | succ T hT ih =>
    rw [pow_succ]
    calc
      100 * (T + 1) ^ 2 ≤ (100 * T ^ 2) * 2 := by
        nlinarith [Nat.mul_le_mul_left T (show 3 ≤ T by omega)]
      _ ≤ 2 ^ T * 2 := Nat.mul_le_mul_right 2 ih

private theorem clique_on_image {V W : Type*} {G : SimpleGraph W} (f : V ↪ W)
    {A : Finset V} (h : (G.comap f).IsClique (A : Set V)) :
    G.IsClique ((A.map f : Finset W) : Set W) := by
  intro x hx y hy hxy
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
  exact h hu hv (fun huv => hxy (congrArg f huv))

/-- Theorem 4, including the prescribed global clique and independence bound. -/
theorem global_upper_bound :
    ∀ C : ℝ, 12 < C → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ G : SimpleGraph (Fin n), ∃ m : ℕ,
        IsLocallyRamsey G m (target n) ∧
        (m : ℝ) ≤ (2 : ℝ) ^ (C * (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 2) ∧
        ∀ A : Finset (Fin n), G.IsClique (A : Set (Fin n)) ∨ Gᶜ.IsClique (A : Set (Fin n)) →
          (A.card : ℝ) ≤ 33 * (Real.logb 2 (n : ℝ)) ^ 2 := by
  intro C hC
  let ℓ := Real.log 2
  have hℓ : 0 < ℓ := Real.log_pos (by norm_num)
  let β := C / ℓ
  have hβ : 0 < β := by dsimp [β]; positivity
  let ε := min (1 / 8 : ℝ) ((C - 12) / (4 * β))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (sub_pos.mpr hC) (by positivity))
  have hε' : ε < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  let d := -Real.log ((1 + 2 * ε) / 2)
  have hd : 0 < d := neg_pos.mpr (Real.log_neg (by positivity) (by linarith))
  have hdℓ : ℓ - 2 * ε ≤ d := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * ε by positivity)
    dsimp [d, ℓ]
    rw [Real.log_div (by positivity : 1 + 2 * ε ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  let α := (12 : ℝ) / d
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hαβ : α < β := by
    have hgap : ε * (4 * β) ≤ C - 12 := (le_div_iff₀ (by positivity : 0 < 4 * β)).mp
      (min_le_right _ _)
    have hβℓ : β * ℓ = C := div_mul_cancel₀ _ hℓ.ne'
    apply (div_lt_iff₀ hd).mpr
    nlinarith only [hgap, hβℓ, mul_le_mul_of_nonneg_left hdℓ hβ.le, hC]
  let S := max 2 ⌈2 / ε⌉₊
  let b := Real.log (100 : ℝ)
  let c := b + Real.log (8000 / ε)
  have hb : 0 ≤ b := Real.log_nonneg (by norm_num)
  have hc : 0 ≤ c := add_nonneg hb (Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith))
  have hlogS : 0 ≤ Real.log (S : ℝ) := Real.log_nonneg (by exact_mod_cast
    (show 1 ≤ S from (by norm_num : 1 ≤ 2).trans (le_max_left _ _)))
  let B := 5 * ((S + 1 : ℕ) : ℝ) + ((7 * b + 2 * c) / d + 1)
  let D := ((S + 1 : ℕ) : ℝ) * (c + Real.log S) + ((c * b + b ^ 2 / 2) / d + b / 2) + ℓ
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let B' := 2 * α * ℓ + B
  let D' := α * ℓ ^ 2 + B * ℓ + D
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  let H := max 1 ((B' + D') / (β - α))
  have hH : 1 ≤ H := le_max_left _ _
  refine ⟨max (2 ^ 100) ⌈(2 : ℝ) ^ Real.exp H⌉₊, ?_⟩
  intro n hn
  let t := Real.logb 2 (n : ℝ)
  let T := target n
  have hn100 : 2 ^ 100 ≤ n := (le_max_left _ _).trans hn
  have hn' : (2 : ℝ) ^ (100 : ℕ) ≤ n := by exact_mod_cast hn100
  have hnr : 0 < (n : ℝ) := (by positivity : (0 : ℝ) < 2 ^ (100 : ℕ)).trans_le hn'
  have htr : 100 ≤ t := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hnr).mpr
    rw [show (100 : ℝ) = ((100 : ℕ) : ℝ) by rfl, Real.rpow_natCast]
    exact hn'
  have htT : t ≤ (T : ℝ) := Nat.le_ceil t
  have hT : 100 ≤ T := by exact_mod_cast htr.trans htT
  have hTr : (0 : ℝ) < T := by linarith
  have hnt : n ≤ 2 ^ T := by
    rw [show T = Nat.clog 2 n from target_eq_clog n]
    exact Nat.le_pow_clog (by decide) n
  have hround : (T : ℝ) < t + 1 := Nat.ceil_lt_add_one (show 0 ≤ t by linarith)
  have hTt : (T : ℝ) ≤ 2 * t := by linarith
  let x := Real.log t
  let y := Real.log (T : ℝ)
  have hxy : y ≤ x + ℓ := by
    have h := Real.log_le_log hTr hTt
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0), add_comm] at h
    exact h
  have hy0 : 0 ≤ y := Real.log_nonneg (by linarith)
  have hxt : H ≤ x := by
    have hp : (2 : ℝ) ^ Real.exp H ≤ (n : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (le_max_right (2 ^ 100) _).trans hn)
    have h := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hnr).mpr hp
    simpa [x] using Real.log_le_log (Real.exp_pos H) h
  have hx1 : 1 ≤ x := hH.trans hxt
  let r := 100 * T ^ 2
  have hr : 2 ≤ r := by dsimp [r]; nlinarith
  have hrT : r ≤ 2 ^ T := target_le_tree_size (by omega)
  have hlogr : Real.log (r : ℝ) = 2 * y + b := by
    dsimp [r, y, b]
    push_cast
    rw [Real.log_mul (by norm_num : (100 : ℝ) ≠ 0) (pow_ne_zero _ hTr.ne'), Real.log_pow]
    ring
  have hparam : 3 * Real.log (T : ℝ) + Real.log (r : ℝ) + Real.log (8000 / ε) = 5 * y + c := by
    rw [hlogr]
    change 3 * y + (2 * y + b) + Real.log (8000 / ε) = _
    dsimp [c]
    ring
  have hpow := threshold_general_exp (by omega : 0 < T) hr hrT hε hε'
  dsimp only at hpow
  rw [hparam, hlogr, iterationPotential_global hd.ne'] at hpow
  have hpow' : (threshold (2 ^ T) r : ℝ) ≤ Real.exp (α * y ^ 2 + B * y + D) := by
    refine hpow.trans_eq ?_
    congr 1
    change ((S + 1 : ℕ) : ℝ) * (5 * y + c + Real.log S) + _ + ℓ = _
    dsimp [α, B, D]
    ring
  have hmove : α * y ^ 2 + B * y + D ≤ α * x ^ 2 + B' * x + D' := by
    have hmono : α * y ^ 2 + B * y + D ≤ α * (x + ℓ) ^ 2 + B * (x + ℓ) + D := by gcongr
    dsimp [B', D']
    linarith only [hmono]
  have habsorb : B' * x + D' ≤ (β - α) * x ^ 2 := by
    have hbound : (B' + D') / (β - α) ≤ x := (le_max_right _ _).trans hxt
    have hh := (div_le_iff₀ (sub_pos.mpr hαβ)).mp hbound
    have hp := mul_le_mul_of_nonneg_right hh (zero_le_one.trans hx1)
    nlinarith only [hp, mul_le_mul_of_nonneg_left hx1 hD']
  have hconvert : Real.exp (β * x ^ 2) = (2 : ℝ) ^ (C * (Real.logb 2 t) ^ 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.logb]
    congr 1
    dsimp [β, x, ℓ]
    field_simp
  have hm := hpow'.trans ((Real.exp_le_exp.mpr (show _ ≤ β * x ^ 2 by linarith)).trans_eq hconvert)
  obtain ⟨G, hG⟩ := exists_graph_at_threshold (2 ^ T) r
  obtain ⟨J, hJ, hglobal⟩ := exists_reversal_preserving_local (by omega : 0 < T) G hG
  let f : Fin n ↪ Leaf T := ⟨Fin.castLE hnt, Fin.castLE_injective hnt⟩
  refine ⟨J.comap f, threshold (2 ^ T) r, hJ.comap f, hm, ?_⟩
  intro A hA
  have hA' : J.IsClique ((A.map f : Finset (Leaf T)) : Set (Leaf T)) ∨
      Jᶜ.IsClique ((A.map f : Finset (Leaf T)) : Set (Leaf T)) := by
    rcases hA with hA | hA
    · exact Or.inl (clique_on_image f hA)
    · rw [comap_complement] at hA
      exact Or.inr (clique_on_image f hA)
  have hcard := hglobal _ hA'
  rw [Finset.card_map] at hcard
  have hcard' : (A.card : ℝ) ≤ 32 * (T : ℝ) ^ 2 := by exact_mod_cast hcard.le
  have hTsmall : (T : ℝ) ≤ (101 / 100 : ℝ) * t := by linarith only [hround, htr]
  have hsq := pow_le_pow_left₀ hTr.le hTsmall 2
  exact hcard'.trans (by nlinarith only [hsq, sq_nonneg t])

end LocallyRamsey.BinaryTree
