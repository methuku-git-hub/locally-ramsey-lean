module

public import LocallyRamsey.Lower.ListExtraction

public section

open scoped BigOperators

namespace LocallyRamsey

/-- Number of positions in a list that are adjacent to every vertex of a
candidate tuple. The same vertex may occur at several positions. -/
@[expose] def listCommonCount {Y V : Type*} (adj : Y → V → Prop) [DecidableRel adj]
    {m s : ℕ} (L : Fin m → Y) (v : Fin s → V) : ℝ :=
  ∑ j, if ∀ k, adj (L j) (v k) then 1 else 0

/-- For a fixed tuple with enough common neighbours, its common
neighbour count on a uniform list has an exponential lower tail. -/
theorem initial_list_tuple_tail {Y V : Type*} [Fintype Y]
    (μ : FiniteLaw Y) (adj : Y → V → Prop) [DecidableRel adj]
    {m s : ℕ} (p : ℝ) (v : Fin s → V) :
    (FiniteLaw.product (fun _ : Fin m => μ)).event (fun L =>
      p ≤ μ.event (fun y => ∀ k, adj y (v k)) ∧ listCommonCount adj L v < p * m / 2) ≤
      Real.exp (-(p * m) / 8) := by
  classical
  let listLaw := FiniteLaw.product (fun _ : Fin m => μ)
  let c := μ.event (fun y => ∀ k, adj y (v k))
  by_cases hpc : p ≤ c
  · let X : Fin m → Y → ℝ := fun _ y => if ∀ k, adj y (v k) then 1 else 0
    have htotal : ∑ j, μ.mean (X j) = (m : ℝ) * c := by
      simp only [X, μ.mean_indicator, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, c]
    have hm := mul_le_mul_of_nonneg_right hpc (by positivity : 0 ≤ (m : ℝ))
    have hTail := FiniteLaw.prob_sum_le_half_mean (fun _ : Fin m => μ) X
      (fun j y => by dsimp [X]; split <;> norm_num)
    rw [htotal] at hTail
    refine (listLaw.event_mono ?_).trans (hTail.trans ?_)
    · intro L hL
      change (∑ j, X j (L j)) ≤ (m : ℝ) * c / 2
      have hL' : (∑ j, X j (L j)) < p * m / 2 := hL.2
      linarith only [hm, hL']
    · apply Real.exp_le_exp.mpr
      linarith only [hm]
  · rw [← listLaw.mean_indicator]
    simp only [hpc, c, false_and, ite_false, listLaw.mean_const]
    exact (Real.exp_pos _).le

section RandomList

variable {Y V J : Type*} [Fintype Y] [Fintype V] [Fintype J] [DecidableEq J]
variable {S : J → Type*} [∀ j, Fintype (S j)]

/-- The probability that some represented tuple has a large common
neighbourhood but too few common neighbours on the random list. The
vertices of the tuple must come from distinct draws. -/
theorem event_bad_commonNeighbor_list_le (μ : FiniteLaw Y)
    (adj : Y → V → Prop) [DecidableRel adj] {m s : ℕ}
    (ν : (Fin m → Y) → (j : J) → FiniteLaw (S j))
    (contains : (j : J) → S j → V → Prop) (a : J → V → ℝ)
    (ha : ∀ L j x, (ν L j).event (fun z => contains j z x) ≤ a j x)
    (ha0 : ∀ j x, 0 ≤ a j x) (p : ℝ) :
    let listLaw := FiniteLaw.product (fun _ : Fin m => μ)
    (listLaw.staged (fun L => FiniteLaw.product (ν L))).event (fun Lω =>
      ∃ (f : Fin s → J) (v : Fin s → V), Function.Injective f ∧
        (p ≤ μ.event (fun y => ∀ k, adj y (v k)) ∧ listCommonCount adj Lω.1 v < p * m / 2) ∧
        ∀ k, contains (f k) (Lω.2 (f k)) (v k)) ≤
      Real.exp (-(p * m) / 8) * (∑ j, ∑ x, a j x) ^ s := by
  classical
  intro listLaw
  refine FiniteLaw.staged_event_exists_injective_inclusions_le listLaw ν (fun _ => contains) a ha ha0 s
    (fun v L => p ≤ μ.event (fun y => ∀ k, adj y (v k)) ∧ listCommonCount adj L v < p * m / 2)
    (Real.exp_pos _).le ?_
  exact initial_list_tuple_tail μ adj p

end RandomList

/-- On a list for which the bad event did not occur, an appropriate
candidate set contains a tuple from distinct draws with a small common
neighbourhood. The bounds on assignment collisions and on the number of
candidate neighbours are expressed as probabilities under any chosen law
on the candidate set. -/
theorem exists_small_common_with_distinct_draws {Y V J Q : Type*} [Fintype Y] [Fintype Q]
    (μ : FiniteLaw Y) (μQ : FiniteLaw Q) (vertex : Q → V) (assign : Q → J)
    (adj : Y → V → Prop) [DecidableRel adj] {m s : ℕ}
    (L : Fin m → Y) (contains : J → V → Prop)
    (hall : ∀ x, contains (assign x) (vertex x))
    {p c d : ℝ} (hp : 0 ≤ p) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hcap : ∀ x, μQ.event (fun y => assign x = assign y) ≤ c)
    (hcollision : (s : ℝ) ^ 2 * c ≤ 1 / 2)
    (hdeg : ∀ j, μQ.event (fun x => adj (L j) (vertex x)) ≤ d)
    (hsmall : m * d ^ s < p * m / 4)
    (hgood : ∀ (f : Fin s → J) (v : Fin s → V), Function.Injective f →
      (∀ k, contains (f k) (v k)) → p ≤ μ.event (fun y => ∀ k, adj y (v k)) →
      p * m / 2 ≤ listCommonCount adj L v) :
    ∃ q : Fin s → Q, Function.Injective (assign ∘ q) ∧
      μ.event (fun y => ∀ k, adj y (vertex (q k))) < p := by
  classical
  let rel : Y → Q → Prop := fun y x => adj y (vertex x)
  let _ : DecidableRel rel := fun y x => inferInstanceAs (Decidable (adj y (vertex x)))
  let large := fun q : Fin s → Q => p ≤ μ.event (fun y => ∀ k, adj y (vertex (q k)))
  obtain ⟨q, hq, hlt⟩ := exists_small_common_of_list μQ assign rel L hc hcollision hcap
    hdeg hd hp hsmall large (fun q hq hg => by
      simpa only [listCommonCount, Function.comp_apply, rel] using
        hgood (assign ∘ q) (vertex ∘ q) hq (fun k => hall (q k)) hg)
  exact ⟨q, hq, lt_of_not_ge hlt⟩

end LocallyRamsey
