module

public import LocallyRamsey.Lower.SmallDegrees

public section

namespace LocallyRamsey

variable {V : Type*} [LinearOrder V]

/-- Clique order used by the lower-bound extraction. -/
@[expose] noncomputable def largeCliqueOrder (r : ℕ) : ℕ :=
  ⌊(r : ℝ) ^ 2 / (24000 * Real.log (r : ℝ))⌋₊

theorem exists_large_clique
    {G : SimpleGraph V} {A : Finset V} {n M r : ℕ}
    (hG : IsLocallyRamsey G M r) (hr : 100 ≤ r) (hrM : r ≤ M) (hM : M ≤ r ^ 6)
    (hn : 0 < n) (hln : ((r : ℝ) - 1) * Real.log 2 ≤ Real.log (n : ℝ))
    (hu : 8000 * Real.log (r : ℝ) ≤ r)
    (hA : (n : ℝ) ^ (1 / 60 : ℝ) ≤ A.card) :
    ∃ K ∈ cliquesIn G A (largeCliqueOrder r), K.card = largeCliqueOrder r := by
  let u := Real.log (r : ℝ)
  let g := r / 2
  let l := ⌊(r : ℝ) / (4000 * u)⌋₊
  have hr100 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  have hrr : 1 < (r : ℝ) := by linarith
  have hu0 : 0 < u := Real.log_pos hrr
  have hg : g ≤ r := Nat.div_le_self _ _
  have hg' : 7 * r < 16 * (r - g) := by dsimp [g]; omega
  have hmax : ((max M (2 * r) : ℕ) : ℝ) ≤ (r : ℝ) ^ 6 := by
    have htwo : 2 * r ≤ r ^ 6 := by
      have ht : 2 * r ≤ r ^ 2 := by nlinarith only [Nat.mul_le_mul_right r (show 2 ≤ r by omega)]
      exact ht.trans (Nat.pow_le_pow_right (by omega) (by decide))
    exact_mod_cast max_le hM htwo
  have hsize : ((max M (2 * r) : ℕ) : ℝ) * ((r : ℝ) ^ 16) ^ l ≤ A.card := by
    have hl := Nat.floor_le (show 0 ≤ (r : ℝ) / (4000 * u) by positivity)
    change (l : ℝ) ≤ (r : ℝ) / (4000 * u) at hl
    have hl' := (le_div_iff₀ (by positivity : 0 < 4000 * u)).mp hl
    have hlog : Real.log (n : ℝ) / 60 ≥ (6 + (l : ℝ) * 16) * u := by
      have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hprod := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ (r : ℝ) - 1 by linarith)
      change 8000 * u ≤ r at hu
      nlinarith only [hl', hu, hprod, hln, hr100]
    calc
      _ ≤ (r : ℝ) ^ (6 : ℕ) * ((r : ℝ) ^ (16 : ℕ)) ^ l :=
        mul_le_mul_of_nonneg_right hmax (by positivity)
      _ = Real.exp ((6 + (l : ℝ) * 16) * u) := by
        rw [add_mul, Real.exp_add, mul_assoc, Real.exp_nat_mul]
        have he6 : Real.exp (6 * u) = (r : ℝ) ^ (6 : ℕ) := by
          rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by rfl, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < (r : ℝ))]
        have he16 : Real.exp (16 * u) = (r : ℝ) ^ (16 : ℕ) := by
          rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by rfl, Real.exp_nat_mul, Real.exp_log (by positivity : 0 < (r : ℝ))]
        rw [he6, he16]
      _ ≤ Real.exp (Real.log (n : ℝ) / 60) := Real.exp_le_exp.mpr hlog
      _ = (n : ℝ) ^ (1 / 60 : ℝ) := by
        rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
        congr 1
        ring
      _ ≤ _ := hA
  obtain ⟨Q, hQ⟩ := exists_clique_from_repeated_extraction hG (by omega) hrM hM hg hg' hsize
  obtain ⟨hQA, hQcard, hQc⟩ := mem_cliquesIn.mp hQ
  have hgle : (r : ℝ) / 3 ≤ g := by
    have h := (show r ≤ 3 * g by dsimp [g]; omega)
    have h' : (r : ℝ) ≤ 3 * (g : ℝ) := by exact_mod_cast h
    linarith
  have hll : (r : ℝ) / (8000 * u) ≤ l := by
    have hlf := Nat.lt_floor_add_one ((r : ℝ) / (4000 * u))
    change (r : ℝ) / (4000 * u) < (l : ℝ) + 1 at hlf
    have htwo : (2 : ℝ) ≤ (r : ℝ) / (4000 * u) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have heq : (r : ℝ) / (4000 * u) = 2 * ((r : ℝ) / (8000 * u)) := by field_simp; ring
    linarith only [hlf, htwo, heq]
  have horder : largeCliqueOrder r ≤ g * l := by
    apply Nat.floor_le_of_le
    push_cast
    convert mul_le_mul hgle hll (by positivity : 0 ≤ (r : ℝ) / (8000 * u)) (by positivity) using 1
    dsimp [u]
    ring
  obtain ⟨K, hKQ, hKcard⟩ := Finset.exists_subset_card_eq (hQcard ▸ horder)
  exact ⟨K, mem_cliquesIn.mpr ⟨hKQ.trans hQA, hKcard,
    fun x hx y hy hxy => hQc (hKQ hx) (hKQ hy) hxy⟩, hKcard⟩

/-- The second assertion of the supply lemma, at the manuscript's
degree and set-size parameters. -/
theorem exists_large_low_degree_at_parameters
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj] (A : Finset V) {M r : ℕ}
    (hG : IsLocallyRamsey G M r) (hr : 100 ≤ r) (hrM : r ≤ M)
    (hMA : M ≤ A.card) (hA : 2 * r ≤ A.card) (hM : M ≤ r ^ 6)
    (hu : 8000 * Real.log (r : ℝ) ≤ r) :
    ∃ X : Finset V, X ⊆ A ∧ (A.card : ℝ) / (r : ℝ) ^ 50 ≤ X.card ∧
      ∀ x ∈ X, ((neighborsIn Gᶜ X x).card : ℝ) ≤ (100 * Real.log (r : ℝ) / r) * X.card := by
  let u := Real.log (r : ℝ)
  let δ := 1 / (r : ℝ) ^ 50
  let η := δ / 4
  let D := (r : ℝ) / (80 * u)
  let L := 100 * u / r
  let g := (3 * r) / 4
  have hr100 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  have hrr : 1 < (r : ℝ) := by linarith
  have hr0 : 0 < (r : ℝ) := by linarith
  have hu0 : 0 < u := Real.log_pos hrr
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ' : δ ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ hrr.le)
  have hη : 0 < η := by dsimp [η]; positivity
  have hD : 1 < D := by
    apply (lt_div_iff₀ (by positivity : 0 < 80 * u)).mpr
    change 8000 * u ≤ r at hu
    linarith
  have hL : δ + η ≤ L * D * δ := by
    have heq : L * D = 5 / 4 := by dsimp [L, D]; field_simp; ring
    rw [heq]
    dsimp [η]
    linarith
  have hg : g ≤ r := by dsimp [g]; omega
  have hbudget : ⌈D * Real.log (1 + 1 / η)⌉₊ ≤ g := by
    apply Nat.ceil_le.mpr
    have heη : 1 / η = 4 * (r : ℝ) ^ 50 := by dsimp [η, δ]; field_simp
    have hp : 1 + 1 / η ≤ (r : ℝ) ^ 51 := by
      rw [heη, pow_succ]
      have hp50 : 1 ≤ (r : ℝ) ^ 50 := one_le_pow₀ hrr.le
      nlinarith only [hp50, mul_le_mul_of_nonneg_left hr100 (by positivity : 0 ≤ (r : ℝ) ^ 50)]
    have hlog := Real.log_le_log (by positivity : 0 < 1 + 1 / η) hp
    rw [Real.log_pow] at hlog
    change Real.log (1 + 1 / η) ≤ (51 : ℝ) * u at hlog
    have heq : D * (51 * u) = (51 / 80 : ℝ) * r := by dsimp [D]; field_simp
    have hgl : 3 * r ≤ 4 * g + 3 := by dsimp [g]; omega
    have hgl' : 3 * (r : ℝ) ≤ 4 * (g : ℝ) + 3 := by exact_mod_cast hgl
    exact (mul_le_mul_of_nonneg_left hlog (by linarith)).trans
      (by rw [heq]; linarith only [hgl', hr100])
  have hcount : ((g + 1 : ℕ) : ℝ) * δ ^ (r - g) < (1 / (r : ℝ) ^ 7) ^ r := by
    have hgs : g + 1 ≤ r := by dsimp [g]; omega
    have hgs' : ((g + 1 : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by
      have hl : ((g + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hgs
      exact hl.trans (by simpa only [pow_one] using pow_le_pow_right₀ hrr.le (by omega : 1 ≤ r))
    have hex : 8 * r + r < 50 * (r - g) := by dsimp [g]; omega
    have hden : (r : ℝ) ^ (7 * r) * (r : ℝ) ^ r < (r : ℝ) ^ (50 * (r - g)) := by
      rw [← pow_add]
      exact pow_lt_pow_right₀ hrr (by omega)
    dsimp [δ]
    simp only [one_div, inv_pow, ← pow_mul]
    rw [← one_div ((r : ℝ) ^ (7 * r)), lt_div_iff₀ (by positivity)]
    rw [mul_comm _ ((r : ℝ) ^ (7 * r)), ← mul_assoc]
    have hm := mul_le_mul_of_nonneg_left hgs' (by positivity : 0 ≤ (r : ℝ) ^ (7 * r))
    calc
      _ ≤ ((r : ℝ) ^ (7 * r) * (r : ℝ) ^ r) * ((r : ℝ) ^ (50 * (r - g)))⁻¹ :=
        mul_le_mul_of_nonneg_right hm (by positivity)
      _ < 1 := by
        rw [← div_eq_mul_inv, div_lt_one (by positivity)]
        exact hden
  obtain ⟨X, hXA, hsize, hdegree⟩ := exists_large_low_degree_complement G A hG
    (by omega) hrM hMA hA hM hδ hδ' hη hD hL hg hbudget hcount
  refine ⟨X, hXA, ?_, hdegree⟩
  simpa [δ, div_eq_mul_inv, mul_comm] using hsize

end LocallyRamsey
