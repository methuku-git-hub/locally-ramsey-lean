module

public import LocallyRamsey.Upper.FinalReversal
public import LocallyRamsey.Upper.GreedyIndependent
public import Mathlib.Data.Nat.Choose.Bounds

public section

open scoped BigOperators

namespace LocallyRamsey.BinaryTree

private theorem dyadic_pow_exp (T r : ℕ) :
    ((2 : ℝ) ^ T) ^ r = Real.exp ((T : ℝ) * r * Real.log 2) := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  rw [Real.log_exp]
  congr 1
  ring

/-- The final reversals can be chosen so that the smaller local target
survives and no homogeneous set has size `32 T²`. For preservation we
use the degree sum on each old witness set, followed by the greedy
independent-set bound. -/
theorem exists_reversal_preserving_local {T : ℕ} (hT : 0 < T)
    (G : SimpleGraph (Leaf T)) {m : ℕ} (hG : IsLocallyRamsey G m (100 * T ^ 2)) :
    ∃ H : SimpleGraph (Leaf T), IsLocallyRamsey H m T ∧
      ∀ A : Finset (Leaf T), H.IsClique (A : Set (Leaf T)) ∨ Hᶜ.IsClique (A : Set (Leaf T)) →
        A.card < 32 * T ^ 2 := by
  classical
  let r := 100 * T ^ 2
  let j := 32 * T ^ 2
  let p := (1 : ℝ) / (16 * (T : ℝ))
  let D := (r : ℝ) ^ 2 / (10 * (T : ℝ))
  have hT₁ : (1 : ℝ) ≤ T := by exact_mod_cast (by omega : 1 ≤ T)
  have hTr : 0 < (T : ℝ) := by linarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hp' : p ≤ 1 / 2 := by
    dsimp [p]
    rw [div_le_iff₀ (by positivity : 0 < 16 * (T : ℝ))]
    linarith
  let μ := FiniteLaw.product (fun _ : Sym2 (Leaf T) => FiniteLaw.bernoulli p hp.le
    (hp'.trans (by norm_num)))
  let badLarge (w : Sym2 (Leaf T) → Bool) :=
    ∃ A : Finset (Leaf T), A.card = j ∧
      ((toggleEdges G w).IsClique (A : Set (Leaf T)) ∨ (toggleEdges G w)ᶜ.IsClique (A : Set (Leaf T)))
  let tooMany (w : Sym2 (Leaf T) → Bool) :=
    ∃ A : Finset (Leaf T), A.card = r ∧ D ≤ (reversedPairs A w : ℝ)
  have hlog : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hr100 : (100 : ℝ) ≤ r := by
    push_cast [r]
    nlinarith
  have hj32 : (32 : ℝ) ≤ j := by
    push_cast [j]
    nlinarith
  have hpow (n : ℕ) : ((Fintype.card (Leaf T)).choose n : ℝ) ≤ ((2 : ℝ) ^ T) ^ n := by
    simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using
      (show ((Fintype.card (Leaf T)).choose n : ℝ) ≤ (((2 ^ T : ℕ) ^ n : ℕ) : ℝ) by
        simp only [Fintype.card_fin]
        exact_mod_cast Nat.choose_le_pow (2 ^ T) n)
  have hsmallLarge : μ.event badLarge ≤ 1 / 4 := by
    have hstart := prob_homogeneous_after_toggle_le G j hp.le hp'
    change μ.event badLarge ≤ _ at hstart
    have hpowflip : (1 - p) ^ j.choose 2 ≤ Real.exp (-(p * (j.choose 2 : ℝ))) := by
      rw [show -(p * (j.choose 2 : ℝ)) = (j.choose 2 : ℝ) * (-p) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) _
    have hjj : (j : ℝ) - 1 ≥ (31 / 32 : ℝ) * j := by linarith
    have hden : (31 / 32 : ℝ) * (T : ℝ) * j ≤ p * (j.choose 2 : ℝ) := by
      rw [Nat.cast_choose_two ℝ j]
      have hjr : (j : ℝ) = 32 * (T : ℝ) ^ 2 := by push_cast [j]; ring
      have h := mul_le_mul_of_nonneg_left hjj (show 0 ≤ p * (j : ℝ) / 2 by positivity)
      have hpj : p * (j : ℝ) / 2 = T := by
        rw [hjr]
        dsimp [p]
        field_simp
        <;> ring
      rw [hpj] at h
      rw [show p * ((j : ℝ) * ((j : ℝ) - 1) / 2) =
        (p * (j : ℝ) / 2) * ((j : ℝ) - 1) by ring, hpj]
      simpa [mul_assoc, mul_left_comm] using h
    have hbig : 32 ≤ (T : ℝ) * j := by nlinarith [mul_le_mul_of_nonneg_right hT₁ (show 0 ≤ (j : ℝ) by positivity)]
    have hexp : (T : ℝ) * j * Real.log 2 - p * (j.choose 2 : ℝ) ≤ -7 := by
      nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ (T : ℝ) * j by positivity), hden, hbig]
    have hconst : 2 * Real.exp (-7) ≤ 1 / 4 := by
      rw [Real.exp_neg]
      field_simp
      linarith [Real.add_one_le_exp (7 : ℝ)]
    calc
      _ ≤ _ := hstart
      _ ≤ 2 * ((2 : ℝ) ^ T) ^ j * Real.exp (-(p * (j.choose 2 : ℝ))) := by
        apply mul_le_mul _ hpowflip (pow_nonneg (by linarith) _) (by positivity)
        exact mul_le_mul_of_nonneg_left (hpow _) (by norm_num)
      _ = 2 * Real.exp ((T : ℝ) * j * Real.log 2 - p * (j.choose 2 : ℝ)) := by
        rw [dyadic_pow_exp, mul_assoc, ← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)).trans hconst
  have hsmallMany : μ.event tooMany ≤ 1 / 4 := by
    let sets := (Finset.univ : Finset (Leaf T)).powersetCard r
    let bad (A : ↥sets) (w : Sym2 (Leaf T) → Bool) := D ≤ (reversedPairs A.val w : ℝ)
    have hcase (A : ↥sets) : μ.event (bad A) ≤ Real.exp (-(3 / 80 : ℝ) * (r : ℝ) ^ 2 / T) := by
      have h := prob_reversedPairs_ge A.val hp.le (hp'.trans (by norm_num)) (by norm_num : (0 : ℝ) < 1) D
      rw [(Finset.mem_powersetCard.mp A.property).2] at h
      refine h.trans (Real.exp_le_exp.mpr ?_)
      have hchoose : (r.choose 2 : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by rw [Nat.cast_choose_two ℝ r]; nlinarith
      have hchoose0 : 0 ≤ (r.choose 2 : ℝ) := Nat.cast_nonneg _
      have hstep : (Real.exp 1 - 1) * (r.choose 2 : ℝ) * p ≤ (r : ℝ) ^ 2 / (16 * T) := by
        calc
          _ ≤ 2 * ((r : ℝ) ^ 2 / 2) * p := by gcongr; linarith [Real.exp_one_lt_three]
          _ = _ := by dsimp [p]; ring
      dsimp [D]
      linarith only [hstep, show (r : ℝ) ^ 2 / (16 * T) - (r : ℝ) ^ 2 / (10 * T) =
        -(3 / 80 : ℝ) * (r : ℝ) ^ 2 / T by ring]
    have hsum : μ.event tooMany ≤ ((2 : ℝ) ^ T) ^ r * Real.exp (-(3 / 80 : ℝ) * (r : ℝ) ^ 2 / T) := by
      calc
        _ ≤ μ.event (fun w => ∃ A, bad A w) := μ.event_mono (by
          rintro w ⟨A, hA, hw⟩
          exact ⟨⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA⟩⟩, hw⟩)
        _ ≤ ∑ A, μ.event (bad A) := μ.event_exists_le_sum _
        _ ≤ ∑ _A : ↥sets, Real.exp (-(3 / 80 : ℝ) * (r : ℝ) ^ 2 / T) :=
          Finset.sum_le_sum fun A _ => hcase A
        _ ≤ _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, sets, Finset.card_powersetCard,
            nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hpow _) (Real.exp_pos _).le
    have hconst : Real.exp (-3) ≤ 1 / 4 := by
      rw [Real.exp_neg]
      field_simp
      linarith [Real.add_one_le_exp (3 : ℝ)]
    refine hsum.trans ?_
    rw [dyadic_pow_exp, ← Real.exp_add]
    refine (Real.exp_le_exp.mpr ?_).trans hconst
    have hmul : (r : ℝ) ^ 2 / T = 100 * (T : ℝ) * r := by
      have hr := show (r : ℝ) = 100 * (T : ℝ) ^ 2 by push_cast [r]; ring
      rw [hr]
      field_simp
      <;> ring
    rw [mul_div_assoc, hmul]
    nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0 ≤ (T : ℝ) * r by positivity),
      mul_le_mul_of_nonneg_right hT₁ (show 0 ≤ (r : ℝ) by positivity), hr100]
  have hunion : μ.event (fun w => badLarge w ∨ tooMany w) < 1 := by
    have h := μ.event_exists_le_sum (fun (b : Bool) w => if b then badLarge w else tooMany w)
    have heq : (fun w => ∃ b : Bool, if b then badLarge w else tooMany w) =
        fun w => badLarge w ∨ tooMany w := by
      funext w
      simp [Bool.exists_bool, or_comm]
    rw [heq] at h
    have h' : μ.event (fun w => badLarge w ∨ tooMany w) ≤ μ.event badLarge + μ.event tooMany := by
      simpa [Fintype.sum_bool, add_comm] using h
    linarith
  obtain ⟨w, hw⟩ := μ.event_lt_one_exists_not hunion
  have hwLarge : ¬ badLarge w := fun h => hw (Or.inl h)
  have hwMany : ¬ tooMany w := fun h => hw (Or.inr h)
  refine ⟨toggleEdges G w, locallyRamsey_toggle_of_unaltered hG ?_, ?_⟩
  · intro A hA
    let F := toggleEdges (⊥ : SimpleGraph (Leaf T)) w
    have hcount : (reversedPairs A w : ℝ) < D := lt_of_not_ge fun h => hwMany ⟨A, hA, h⟩
    have hsum : (∑ x ∈ A, (closedNeighbors F A x).card) ≤ (45 * T) * (A.card - (45 * T) * T) := by
      rw [sum_closedNeighbors_after_reversals A w, hA]
      have hform : r - (45 * T) * T = 55 * T ^ 2 := by
        dsimp [r]
        rw [show 45 * T * T = 45 * T ^ 2 by ring, ← Nat.sub_mul]
      rw [hform]
      have hD : D = 1000 * (T : ℝ) ^ 3 := by
        dsimp [D, r]
        push_cast
        field_simp
        <;> ring
      rw [hD] at hcount
      exact_mod_cast (show ((r : ℝ) + 2 * reversedPairs A w) ≤
        (45 * T : ℝ) * (55 * (T : ℝ) ^ 2) by
          push_cast [r]
          nlinarith only [hcount, mul_le_mul_of_nonneg_right hT₁ (sq_nonneg (T : ℝ))])
    have hA' : (45 * T) * T ≤ A.card := by rw [hA]; change _ ≤ 100 * T ^ 2; nlinarith
    obtain ⟨I, hI, hcl⟩ := exists_independent_of_degree_sum F (by positivity : 0 < 45 * T) hA' hsum
    refine ⟨I, hI, hcl.card_eq, ?_⟩
    intro x hx y hy hxy
    have hneg := ((SimpleGraph.compl_adj F x y).mp (hcl.isClique hx hy hxy)).2
    cases hbit : w s(x, y) with
    | false => rfl
    | true =>
      apply (hneg ?_).elim
      change x ≠ y ∧ ((⊥ : SimpleGraph (Leaf T)).Adj x y ↔ w s(x, y) = false)
      simp [hxy, hbit]
  · intro A hA
    by_contra! hcard
    obtain ⟨K, hK, hc⟩ := Finset.exists_subset_card_eq hcard
    exact hwLarge ⟨K, hc, hA.imp (fun h => h.subset hK) (fun h => h.subset hK)⟩

end LocallyRamsey.BinaryTree
