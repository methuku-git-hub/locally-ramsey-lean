module

public import LocallyRamsey.Lower.Recording

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Greedily selecting a vertex and removing its closed neighbourhood
gives an independent set of size at least `|X| / d` if every closed
neighbourhood in `X` has at most `d` vertices. -/
theorem exists_independent_of_degree {X : Finset V} {d : ℕ}
    (hdeg : ∀ x ∈ X, (closedNeighbors G X x).card ≤ d) :
    ∃ I : Finset V, I ⊆ X ∧ Gᶜ.IsClique (I : Set V) ∧ X.card ≤ d * I.card := by
  suffices h : ∀ n (X : Finset V), X.card = n →
      (∀ x ∈ X, (closedNeighbors G X x).card ≤ d) →
        ∃ I : Finset V, I ⊆ X ∧ Gᶜ.IsClique (I : Set V) ∧ X.card ≤ d * I.card from
    h X.card X rfl hdeg
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X hX hdeg
    by_cases h : X.Nonempty
    · obtain ⟨x, hx⟩ := h
      let A := nonNeighbors G X x
      have hA : A ⊆ X := Finset.filter_subset _ _
      have hxA : x ∉ A := by simp [A, nonNeighbors]
      have hlt : A.card < n := by
        rw [← hX]
        exact Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hA, fun he => hxA (he ▸ hx)⟩)
      have hdegA (y : V) (hy : y ∈ A) : (closedNeighbors G A y).card ≤ d :=
        (Finset.card_le_card (Finset.filter_subset_filter _ hA)).trans (hdeg y (hA hy))
      obtain ⟨I, hI, hcl, hsize⟩ := ih A.card hlt A rfl hdegA
      have hxI : x ∉ I := fun ha => hxA (hI ha)
      have hcover : A ∪ closedNeighbors G X x = X := by
        ext v
        simp only [Finset.mem_union, A, nonNeighbors, closedNeighbors, Finset.mem_filter]
        tauto
      have hcard := Finset.card_union_le A (closedNeighbors G X x)
      rw [hcover] at hcard
      refine ⟨insert x I, Finset.insert_subset hx (hI.trans hA), ?_, ?_⟩
      · rw [Finset.coe_insert]
        apply hcl.insert
        intro y hy hxy
        have hy' := (Finset.mem_filter.mp (hI hy)).2
        exact (SimpleGraph.compl_adj G x y).mpr ⟨hxy, fun h => hy' (Or.inr h)⟩
      · rw [Finset.card_insert_of_notMem hxI, Nat.mul_succ]
        have h := hdeg x hx
        omega
    · have hX0 := Finset.not_nonempty_iff_eq_empty.mp h
      subst X
      exact ⟨∅, by simp, by simp, by simp⟩

/-- A bound on the sum of closed neighbourhood sizes ensures that
enough vertices have individually bounded degrees for the greedy
procedure. -/
theorem exists_independent_of_degree_sum {X : Finset V} {d t : ℕ}
    (hd : 0 < d) (hX : d * t ≤ X.card)
    (hsum : (∑ x ∈ X, (closedNeighbors G X x).card) ≤ d * (X.card - d * t)) :
    ∃ I : Finset V, I ⊆ X ∧ Gᶜ.IsNClique t I := by
  let low := X.filter fun x => (closedNeighbors G X x).card ≤ d
  let high := X.filter fun x => ¬(closedNeighbors G X x).card ≤ d
  have hhigh : d * high.card ≤ ∑ x ∈ X, (closedNeighbors G X x).card := by
    calc
      _ = ∑ _x ∈ high, d := by simp [mul_comm]
      _ ≤ ∑ x ∈ high, (closedNeighbors G X x).card :=
        Finset.sum_le_sum fun x hx => (lt_of_not_ge (Finset.mem_filter.mp hx).2).le
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hsplit : low.card + high.card = X.card := by
    rw [show low = X.filter (fun x => (closedNeighbors G X x).card ≤ d) from rfl,
      show high = X.filter (fun x => ¬(closedNeighbors G X x).card ≤ d) from rfl]
    exact Finset.card_filter_add_card_filter_not (s := X) _
  have hlow : d * t ≤ low.card := by
    have h := (Nat.le_of_mul_le_mul_left (hhigh.trans hsum) hd)
    omega
  obtain ⟨I, hI, hcl, hcard⟩ := exists_independent_of_degree G (X := low) (d := d) (by
    intro x hx
    exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans
      (Finset.mem_filter.mp hx).2)
  have hIt : t ≤ I.card := Nat.le_of_mul_le_mul_left (hlow.trans hcard) hd
  obtain ⟨K, hK, hcardK⟩ := Finset.exists_subset_card_eq hIt
  exact ⟨K, hK.trans (hI.trans (Finset.filter_subset _ _)), ⟨hcl.subset hK, hcardK⟩⟩

end LocallyRamsey
