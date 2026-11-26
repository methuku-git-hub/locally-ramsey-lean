module

public import LocallyRamsey.Lower.CompanionGroups
public import LocallyRamsey.Lower.InitialRule
public import LocallyRamsey.Lower.Variance
public import Mathlib.Algebra.BigOperators.Ring.Finset

public section

open scoped BigOperators

namespace LocallyRamsey

private theorem choose_ratio_le (n q k : ℕ) (hqn : q ≤ n) (hkn : k ≤ q)
    (hn : 0 < n) :
    (q.choose k : ℝ) ≤ (n.choose k : ℝ) * ((q : ℝ) / n) ^ k := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  induction k with
  | zero => simp
  | succ k ih =>
    have hkq : k ≤ q := by omega
    have hkn' : k ≤ n := hkq.trans hqn
    have hqn' : (q : ℝ) ≤ n := by exact_mod_cast hqn
    have h : ((q - k : ℕ) : ℝ) ≤ ((n - k : ℕ) : ℝ) * ((q : ℝ) / n) := by
      rw [Nat.cast_sub hkq, Nat.cast_sub hkn', ← mul_div_assoc, le_div_iff₀ hn']
      nlinarith only [mul_le_mul_of_nonneg_right hqn' (Nat.cast_nonneg k)]
    have hchoose (a : ℕ) : (a.choose (k + 1) : ℝ) * (k + 1) = a.choose k * (a - k : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq a k
    apply (mul_le_mul_iff_of_pos_right (show (0 : ℝ) < k + 1 by positivity)).mp
    rw [hchoose q]
    calc
      _ ≤ ((n.choose k : ℝ) * ((q : ℝ) / n) ^ k) * (q - k : ℕ) :=
        mul_le_mul_of_nonneg_right (ih hkq) (by positivity)
      _ ≤ ((n.choose k : ℝ) * ((q : ℝ) / n) ^ k) * ((n - k : ℕ) * ((q : ℝ) / n)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((n.choose k : ℝ) * (n - k : ℕ)) * ((q : ℝ) / n) ^ (k + 1) := by rw [pow_succ]; ring
      _ = _ := by rw [← hchoose n]; ring

variable {I : Type*} [DecidableEq I]

/-- A uniform fixed-size group contains a prescribed set with probability
at most the probability obtained from independent inclusion at the same
marginal rate. -/
theorem event_uniform_group_contains_le (U A : Finset I) (hU : U.Nonempty)
    (hAU : A ⊆ U) {q : ℕ} (hq : q ≤ U.card)
    [Nonempty ↥(U.powersetCard q)] :
    (FiniteLaw.uniform ↥(U.powersetCard q)).event (fun J => A ⊆ J.val) ≤
      ((q : ℝ) / U.card) ^ A.card := by
  classical
  rw [uniform_vertex_event (U.powersetCard q) (Finset.powersetCard_nonempty.mpr hq)]
  by_cases ha : A.card ≤ q
  · rw [Finset.card_filter_powersetCard_subset A U q hAU ha, Finset.card_powersetCard]
    have h1 := Nat.choose_mul (n := U.card) (k := q) (s := A.card) ha
    have h2 : ((U.card.choose q : ℕ) : ℝ) * q.choose A.card =
        (U.card.choose A.card : ℝ) * (U.card - A.card).choose (q - A.card) := by
      exact_mod_cast h1
    have h0 : (0 : ℝ) < U.card.choose q := by exact_mod_cast Nat.choose_pos hq
    have hA0 : (0 : ℝ) < U.card.choose A.card := by exact_mod_cast Nat.choose_pos (ha.trans hq)
    have he : ((U.card - A.card).choose (q - A.card) : ℝ) / U.card.choose q =
        (q.choose A.card : ℝ) / U.card.choose A.card := by
      exact (div_eq_div_iff h0.ne' hA0.ne').mpr (by linarith only [h2])
    rw [he, div_le_iff₀ hA0, mul_comm]
    exact choose_ratio_le U.card q A.card hq ha hU.card_pos
  · have he : ((U.powersetCard q).filter (fun J => A ⊆ J)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro J hj
      obtain ⟨hJ, hAJ⟩ := Finset.mem_filter.mp hj
      have hc := Finset.card_le_card hAJ
      rw [(Finset.mem_powersetCard.mp hJ).2] at hc
      exact ha hc
    rw [he, Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

/-- The exponential moment of a weighted uniform group is bounded by the
moment for independent inclusion with the same marginal probabilities. -/
theorem mean_exp_uniform_group_le (U : Finset I) (hU : U.Nonempty) {q : ℕ} (hq : q ≤ U.card)
    [Nonempty ↥(U.powersetCard q)] (X : I → ℝ)
    (hX : ∀ i ∈ U, X i ∈ Set.Icc (0 : ℝ) 1) :
    (FiniteLaw.uniform ↥(U.powersetCard q)).mean (fun J => Real.exp (∑ x ∈ J.val, X x)) ≤
      Real.exp ((Real.exp 1 - 1) * ((q : ℝ) / U.card) * ∑ x ∈ U, X x) := by
  classical
  let μ := FiniteLaw.uniform ↥(U.powersetCard q)
  let p := (q : ℝ) / U.card
  let a (x : I) := Real.exp (X x) - 1
  have ha (i : I) (hi : i ∈ U) : 0 ≤ a i := by
    simpa only [a, sub_nonneg, ← Real.exp_zero] using Real.exp_le_exp.mpr (hX i hi).1
  have he (J : ↥(U.powersetCard q)) :
      Real.exp (∑ x ∈ J.val, X x) =
        ∑ A ∈ U.powerset, (if A ⊆ J.val then ∏ x ∈ A, a x else 0) := by
    rw [Real.exp_sum, ← Finset.sum_filter]
    have hJ := (Finset.mem_powersetCard.mp J.property).1
    have hEq : U.powerset.filter (fun A => A ⊆ J.val) = J.val.powerset := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨And.right, fun h => ⟨h.trans hJ, h⟩⟩
    rw [hEq, ← Finset.prod_one_add]
    exact Finset.prod_congr rfl (fun x _ => by dsimp [a]; ring)
  simp_rw [he]
  rw [μ.mean_sum]
  have hterm (A : Finset I) (hA : A ∈ U.powerset) :
      μ.mean (fun J => if A ⊆ J.val then ∏ x ∈ A, a x else 0) ≤
        ∏ x ∈ A, (p * a x) := by
    have hAU := Finset.mem_powerset.mp hA
    have hfun : (fun J : ↥(U.powersetCard q) => if A ⊆ J.val then ∏ x ∈ A, a x else 0) =
        fun J => (∏ x ∈ A, a x) * (if A ⊆ J.val then 1 else 0) := by
      ext J
      split <;> simp_all
    rw [hfun, μ.mean_mul_const, μ.mean_indicator, Finset.prod_mul_distrib, Finset.prod_const, mul_comm]
    exact mul_le_mul_of_nonneg_right (event_uniform_group_contains_le U A hU hAU hq)
      (Finset.prod_nonneg fun x hx => ha x (hAU hx))
  calc
    _ ≤ ∑ A ∈ U.powerset, ∏ x ∈ A, (p * a x) := Finset.sum_le_sum hterm
    _ = ∏ x ∈ U, (1 + p * a x) := (Finset.prod_one_add _).symm
    _ ≤ ∏ x ∈ U, Real.exp (p * a x) :=
      Finset.prod_le_prod₀ (fun x hx => by
        have hh : 0 ≤ p * a x := mul_nonneg (by dsimp [p]; positivity) (ha x hx)
        linarith only [hh]) (fun x _ => by linarith [Real.add_one_le_exp (p * a x)])
    _ ≤ _ := by
      rw [← Real.exp_sum, ← Finset.mul_sum]
      apply Real.exp_le_exp.mpr
      have hp : 0 ≤ p := by dsimp [p]; positivity
      rw [mul_comm (Real.exp 1 - 1) p, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hp
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun x hx => by
        have hb := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1)
          (sub_nonneg.mpr (hX x hx).2) (hX x hx).1 (by ring : 1 - X x + X x = 1)
        norm_num [smul_eq_mul] at hb
        dsimp [a]
        linarith only [hb])


/-- Charge each appearance of a position by the number of previous draws
that used it, capped at the prescribed limit. -/
@[expose] def cappedCollisionScore (d : ℕ) {Ω : Type*} (draw : Ω → Finset I) :
    (n : ℕ) → (I → ℕ) → (Fin n → Ω) → ℝ
  | 0, _, _ => 0
  | n + 1, count, ω => (∑ x ∈ draw (ω 0), (min d (count x) : ℝ)) +
      cappedCollisionScore d draw n
        (fun x => count x + if x ∈ draw (ω 0) then 1 else 0) (fun i => ω i.succ)

/-- Exposing one entire group at a time gives an exponential tail for the
capped sum of shared positions. The same cap is used at every step. -/
theorem event_capped_collisions_ge_le (U : Finset I) (hU : U.Nonempty) {q : ℕ}
    (hq : q ≤ U.card) [Nonempty ↥(U.powersetCard q)] (r d : ℕ) (hd : 0 < d)
    (T : ℝ) :
    let μ := FiniteLaw.uniform ↥(U.powersetCard q)
    (FiniteLaw.product (fun _ : Fin r => μ)).event (fun ω =>
      T ≤ cappedCollisionScore d Subtype.val r (fun _ => 0) ω) ≤
      Real.exp ((Real.exp 1 - 1) * ((q : ℝ) / U.card) * ((r : ℝ) * q / d) * r - T / d) := by
  classical
  intro μ
  let p := (q : ℝ) / U.card
  let c := (Real.exp 1 - 1) * p * ((r : ℝ) * q / d)
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hmoment (n : ℕ) (count : I → ℕ)
      (hcount : (∑ x ∈ U, count x) + n * q ≤ r * q) :
      (FiniteLaw.product (fun _ : Fin n => μ)).mean (fun ω =>
        Real.exp (cappedCollisionScore d Subtype.val n count ω / d)) ≤ Real.exp (c * n) := by
    induction n generalizing count with
    | zero => simp [cappedCollisionScore, FiniteLaw.mean_const]
    | succ n ih =>
      rw [FiniteLaw.mean_split_first]
      let more (J : ↥(U.powersetCard q)) := fun x : I => count x + if x ∈ J.val then 1 else 0
      let X (x : I) := (min d (count x) : ℝ) / d
      have hrange (x : I) (_ : x ∈ U) : X x ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨by dsimp [X]; positivity, (div_le_one hd').mpr (by exact_mod_cast min_le_left d (count x))⟩
      have hn (J : ↥(U.powersetCard q)) : (∑ x ∈ U, more J x) + n * q ≤ r * q := by
        have hJ := (Finset.mem_powersetCard.mp J.property)
        have hsum : (∑ x ∈ U, if x ∈ J.val then 1 else 0) = q := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hJ.1]
          simp [hJ.2]
        simp only [more, Finset.sum_add_distrib, hsum]
        rw [Nat.succ_mul] at hcount
        omega
      have hx : ∑ x ∈ U, X x ≤ (r : ℝ) * q / d := by
        simp only [X, ← Finset.sum_div]
        apply div_le_div_of_nonneg_right _ hd'.le
        have hreal : (∑ x ∈ U, (count x : ℝ)) ≤ (r : ℝ) * q := by
          exact_mod_cast (show (∑ x ∈ U, count x) ≤ r * q by omega)
        exact (Finset.sum_le_sum fun x _ => by exact_mod_cast min_le_right d (count x)).trans hreal
      have hrow : μ.mean (fun J => Real.exp (∑ x ∈ J.val, X x)) ≤ Real.exp c := by
        refine (mean_exp_uniform_group_le U hU hq X hrange).trans (Real.exp_le_exp.mpr ?_)
        have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp 1]
        exact mul_le_mul_of_nonneg_left hx (mul_nonneg he hp)
      have hpoint (J : ↥(U.powersetCard q)) :
          (FiniteLaw.product (fun _ : Fin n => μ)).mean (fun ω =>
            Real.exp (cappedCollisionScore d Subtype.val (n + 1) count (Fin.cons J ω) / d)) ≤
          Real.exp (c * n) * Real.exp (∑ x ∈ J.val, X x) := by
        simp only [cappedCollisionScore, Fin.cons_zero, Fin.cons_succ, add_div, Real.exp_add, Finset.sum_div]
        rw [FiniteLaw.mean_mul_const, mul_comm]
        exact mul_le_mul_of_nonneg_right (ih (more J) (hn J)) (Real.exp_pos _).le
      refine (μ.mean_mono hpoint).trans ?_
      rw [μ.mean_mul_const, Nat.cast_succ, mul_add, mul_one, Real.exp_add]
      exact mul_le_mul_of_nonneg_left hrow (Real.exp_pos _).le
  let ν := FiniteLaw.product (fun _ : Fin r => μ)
  let F (ω : Fin r → ↥(U.powersetCard q)) :=
    Real.exp (cappedCollisionScore d Subtype.val r (fun _ => 0) ω / d)
  refine (ν.event_mono (Q := fun ω => Real.exp (T / d) ≤ F ω) (fun ω hω =>
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hω hd'.le))).trans ?_
  refine (ν.event_ge_le (fun ω => (Real.exp_pos _).le) (Real.exp_pos (T / d))).trans ?_
  refine (div_le_div_of_nonneg_right (hmoment r (fun _ => 0) (by simp))
    (Real.exp_pos (T / d)).le).trans_eq ?_
  rw [← Real.exp_sub]


/-- The number of times a position appears in the specified collection
of draws. -/
@[expose] def groupOccurrences {Ω : Type*} {n : ℕ} (draw : Ω → Finset I)
    (ω : Fin n → Ω) (x : I) : ℕ :=
  ∑ i, if x ∈ draw (ω i) then 1 else 0

/-- The total number of shared positions over ordered pairs of distinct
draws. -/
@[expose] def groupCollisionCount {Ω : Type*} {n : ℕ} (draw : Ω → Finset I)
    (ω : Fin n → Ω) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else ((draw (ω i) ∩ draw (ω j)).card : ℝ)

private theorem sum_indicator_mem (A B : Finset I) :
    (∑ x ∈ A, if x ∈ B then (1 : ℝ) else 0) = ((A ∩ B).card : ℝ) := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]
  simp

/-- If the total occurrences do not exceed the cap, the cap is never
active, and the accumulated charge counts each unordered pair once. -/
theorem twice_cappedCollisionScore_eq {Ω : Type*} (draw : Ω → Finset I) (d n : ℕ)
    (ω : Fin n → Ω) (count : I → ℕ)
    (hcap : ∀ x, count x + groupOccurrences draw ω x ≤ d) :
    2 * cappedCollisionScore d draw n count ω =
      groupCollisionCount draw ω + 2 * ∑ i, ∑ x ∈ draw (ω i), (count x : ℝ) := by
  induction n generalizing count with
  | zero => simp [cappedCollisionScore, groupCollisionCount]
  | succ n ih =>
    let tail (i : Fin n) := ω i.succ
    let more (x : I) := count x + if x ∈ draw (ω 0) then 1 else 0
    have hocc (x : I) : groupOccurrences draw ω x =
        (if x ∈ draw (ω 0) then 1 else 0) + groupOccurrences draw tail x := by
      simp only [groupOccurrences, Fin.sum_univ_succ, tail]
    have htail (x : I) : more x + groupOccurrences draw tail x ≤ d := by
      have hc := hcap x
      rwa [hocc, ← add_assoc] at hc
    have hd (x : I) : min (d : ℝ) (count x : ℝ) = (count x : ℝ) := by
      apply min_eq_right
      exact_mod_cast (Nat.le_add_right _ _).trans (hcap x)
    have hp : groupCollisionCount draw ω =
        groupCollisionCount draw tail + 2 * ∑ j : Fin n, ((draw (tail j) ∩ draw (ω 0)).card : ℝ) := by
      unfold groupCollisionCount
      rw [Fin.sum_univ_succ]
      simp only [Fin.sum_univ_succ, Fin.succ_ne_zero, fun i => Ne.symm (Fin.succ_ne_zero i),
        Fin.succ_inj, ite_false, ite_true, eq_self]
      rw [Finset.sum_add_distrib]
      simp_rw [Finset.inter_comm (draw (ω 0))]
      simp only [tail, zero_add]
      ring
    have hb : (∑ i : Fin n, ∑ x ∈ draw (tail i), (more x : ℝ)) =
        (∑ i : Fin n, ∑ x ∈ draw (tail i), (count x : ℝ)) +
          ∑ i : Fin n, ((draw (tail i) ∩ draw (ω 0)).card : ℝ) := by
      simp only [more, Nat.cast_add, Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact sum_indicator_mem _ _
    change 2 * ((∑ x ∈ draw (ω 0), (min d (count x) : ℝ)) +
      cappedCollisionScore d draw n more tail) = _
    simp only [hd]
    rw [mul_add, ih tail more htail, hp, hb, Fin.sum_univ_succ]
    change _ = _ + 2 * ((∑ x ∈ draw (ω 0), (count x : ℝ)) +
      (∑ i : Fin n, ∑ x ∈ draw (tail i), (count x : ℝ)))
    ring



namespace FiniteLaw

private theorem event_eq_outcome {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (x : Ω) :
    μ.event (fun y => y = x) = μ.prob x := by
  classical
  rw [← μ.mean_indicator]
  simp [mean, mul_ite, Finset.sum_ite_eq']

/-- The coordinates on any list of distinct indices have the same
product law as a newly drawn list. -/
theorem map_product_injective {Ω J K : Type*} [Fintype Ω] [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K] (μ : FiniteLaw Ω) (f : K → J) (hf : Function.Injective f) :
    (product (fun _ : J => μ)).map (fun ω => ω ∘ f) =
      product (fun _ : K => μ) := by
  classical
  let ν := product (fun _ : J => μ)
  let τ := product (fun _ : K => μ)
  let proj (ω : J → Ω) := ω ∘ f
  have heq (w : K → Ω) : (ν.map proj).prob w = τ.prob w := by
    rw [← event_eq_outcome (ν.map proj), ν.event_map]
    let P (j : J) (x : Ω) := ∀ k, f k = j → x = w k
    have hP : (fun ω => (proj ω = w)) = fun ω => ∀ k, P (f k) (ω (f k)) := by
      ext ω
      constructor
      · intro hw k l hl
        have h : k = l := (hf hl).symm
        subst l
        exact congrFun hw k
      · exact fun h => funext (fun k => h k k rfl)
    change ν.event (fun ω => proj ω = w) = _
    rw [hP, event_all_at_injective (fun _ : J => μ) f hf P]
    change (∏ k, μ.event (P (f k))) = ∏ k, μ.prob (w k)
    refine Finset.prod_congr rfl (fun k _ => ?_)
    have hp : P (f k) = fun y => y = w k := by
      ext y
      exact ⟨fun h => h k rfl, fun h l hl => hf hl ▸ h⟩
    rw [hp, event_eq_outcome]
  change ν.map proj = τ
  have extLaw (a b : FiniteLaw (K → Ω)) (hp : a.prob = b.prob) : a = b := by
    cases a
    cases b
    congr
  exact extLaw _ _ (funext heq)

theorem event_injective_projection {Ω J K : Type*} [Fintype Ω] [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K] (μ : FiniteLaw Ω) (f : K → J) (hf : Function.Injective f)
    (E : (K → Ω) → Prop) :
    (product (fun _ : J => μ)).event (fun ω => E (ω ∘ f)) =
      (product (fun _ : K => μ)).event E := by
  rw [← map_product_injective μ f hf, event_map]
  rfl

theorem mean_injective_projection {Ω J K : Type*} [Fintype Ω] [Fintype J] [Fintype K]
    [DecidableEq J] [DecidableEq K] (μ : FiniteLaw Ω) (f : K → J) (hf : Function.Injective f)
    (X : (K → Ω) → ℝ) :
    (product (fun _ : J => μ)).mean (fun ω => X (ω ∘ f)) =
      (product (fun _ : K => μ)).mean X := by
  rw [← map_product_injective μ f hf, mean_map]
  rfl

end FiniteLaw

/-- The shared-position estimate holds simultaneously for every choice of
distinct draws. The second term is the union bound over those choices;
the first accounts for positions that occur more often than the cap. -/
theorem event_many_shared_positions {I : Type*} [DecidableEq I]
    (U : Finset I) (hU : U.Nonempty) {q : ℕ} (hq : q ≤ U.card)
    [Nonempty ↥(U.powersetCard q)] (N r d : ℕ) (hd : 0 < d) (T : ℝ) :
    let μ := FiniteLaw.uniform ↥(U.powersetCard q)
    (FiniteLaw.product (fun _ : Fin N => μ)).event (fun ω =>
      ∃ f : Fin r → Fin N, Function.Injective f ∧
        2 * T ≤ groupCollisionCount Subtype.val (ω ∘ f)) ≤
      U.card * Real.exp ((N : ℝ) * ((q : ℝ) / U.card) - Real.log 2 * d) +
        (N : ℝ) ^ r * Real.exp ((Real.exp 1 - 1) * ((q : ℝ) / U.card) *
          ((r : ℝ) * q / d) * r - T / d) := by
  classical
  intro μ
  let ν := FiniteLaw.product (fun _ : Fin N => μ)
  let tooOften (x : ↥U) (ω : Fin N → ↥(U.powersetCard q)) :=
    d < groupOccurrences Subtype.val ω x.val
  let heavy (ω : Fin N → ↥(U.powersetCard q)) := ∃ x, tooOften x ω
  let tooMany (f : Fin r → Fin N) (ω : Fin N → ↥(U.powersetCard q)) :=
    Function.Injective f ∧ T ≤ cappedCollisionScore d Subtype.val r (fun _ => 0) (ω ∘ f)
  have hcap (x : ↥U) : ν.event (tooOften x) ≤
      Real.exp ((N : ℝ) * ((q : ℝ) / U.card) - Real.log 2 * d) := by
    let X (_ : Fin N) (J : ↥(U.powersetCard q)) := if x.val ∈ J.val then (1 : ℝ) else 0
    have hx (i : Fin N) : μ.mean (X i) ≤ ((q : ℝ) / U.card) := by
      simp only [X, μ.mean_indicator]
      have ha := event_uniform_group_contains_le U {x.val} hU
        (Finset.singleton_subset_iff.mpr x.property) hq
      simpa only [Finset.singleton_subset_iff, Finset.card_singleton, pow_one] using ha
    refine (ν.event_mono (Q := fun ω => (d : ℝ) ≤ ∑ i, X i (ω i)) ?_).trans ?_
    · intro ω hw
      have hn : d ≤ groupOccurrences Subtype.val ω x.val := (Nat.le_of_lt hw)
      simpa only [groupOccurrences, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
        (show (d : ℝ) ≤ (groupOccurrences Subtype.val ω x.val : ℝ) by exact_mod_cast hn)
    · refine (FiniteLaw.prob_sum_ge_le (fun _ : Fin N => μ) X (fun i J => by
          dsimp [X]; split <;> norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)) d).trans ?_
      rw [Real.exp_le_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
      exact (Finset.sum_le_sum (fun i _ => hx i)).trans_eq (by simp)
  have hHeavy : ν.event heavy ≤ U.card * Real.exp ((N : ℝ) * ((q : ℝ) / U.card) - Real.log 2 * d) := by
    refine (ν.event_exists_le_sum tooOften).trans ?_
    exact (Finset.sum_le_sum (fun x _ => hcap x)).trans_eq (by simp)
  have hMany (f : Fin r → Fin N) : ν.event (tooMany f) ≤
      Real.exp ((Real.exp 1 - 1) * ((q : ℝ) / U.card) * ((r : ℝ) * q / d) * r - T / d) := by
    by_cases hf : Function.Injective f
    · simp only [tooMany, hf, true_and, ν]
      rw [FiniteLaw.event_injective_projection μ f hf
        (fun ω => T ≤ cappedCollisionScore d Subtype.val r (fun _ => 0) ω)]
      exact event_capped_collisions_ge_le U hU hq r d hd T
    · rw [← ν.mean_indicator]
      simp only [tooMany, hf, false_and, ite_false, ν.mean_const]
      exact (Real.exp_pos _).le
  have hsub (ω : Fin N → ↥(U.powersetCard q))
      (hw : ∃ f : Fin r → Fin N, Function.Injective f ∧
        2 * T ≤ groupCollisionCount Subtype.val (ω ∘ f)) : heavy ω ∨ ∃ f, tooMany f ω := by
    by_cases hh : heavy ω
    · exact Or.inl hh
    · obtain ⟨f, hf, hTf⟩ := hw
      have htotal (x : I) : groupOccurrences Subtype.val ω x ≤ d := by
        by_cases hx : x ∈ U
        · exact le_of_not_gt (fun h => hh ⟨⟨x, hx⟩, h⟩)
        · have hn (i : Fin N) : x ∉ (ω i).val :=
            fun hi => hx ((Finset.mem_powersetCard.mp (ω i).property).1 hi)
          simp [groupOccurrences, hn]
      have hsmall (x : I) :
          (fun _ : I => (0 : ℕ)) x + groupOccurrences Subtype.val (ω ∘ f) x ≤ d := by
        simp only [zero_add, groupOccurrences, Function.comp_apply]
        refine (?_ : _ ≤ groupOccurrences Subtype.val ω x).trans (htotal x)
        unfold groupOccurrences
        calc
          _ = ∑ i ∈ (Finset.univ : Finset (Fin r)).image f, (if x ∈ (ω i).val then 1 else 0) :=
            (Finset.sum_image (fun i _ j _ hij => hf hij)).symm
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)
      have hEq := twice_cappedCollisionScore_eq Subtype.val d r (ω ∘ f) (fun _ => 0) hsmall
      simp at hEq
      exact Or.inr ⟨f, hf, by linarith only [hEq, hTf]⟩
  refine ((ν.event_mono hsub).trans (ν.event_union_le heavy (fun ω => ∃ f, tooMany f ω))).trans ?_
  refine add_le_add hHeavy ((ν.event_exists_le_sum tooMany).trans ?_)
  exact (Finset.sum_le_sum (fun f _ => hMany f)).trans_eq
    (by simp [Nat.cast_pow])


end LocallyRamsey
