module

public import LocallyRamsey.Lower.CliqueSupply

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- All independent subsets of a specified finite set of vertices. -/
noncomputable def independentSubsets (G : SimpleGraph V) (A : Finset V) : Finset (Finset V) := by
  classical
  exact A.powerset.filter fun Q => Gᶜ.IsClique (Q : Set V)

theorem mem_independentSubsets {G : SimpleGraph V} {A Q : Finset V} :
    Q ∈ independentSubsets G A ↔ Q ⊆ A ∧ Gᶜ.IsClique (Q : Set V) := by
  classical
  simp [independentSubsets]

/-- Largest order of an independent set in (G[A]). -/
noncomputable def independenceOrder (G : SimpleGraph V) (A : Finset V) : ℕ :=
  (independentSubsets G A).sup Finset.card

theorem card_le_independenceOrder {G : SimpleGraph V} {A Q : Finset V} (hQ : Q ⊆ A)
    (hQc : Gᶜ.IsClique (Q : Set V)) : Q.card ≤ independenceOrder G A :=
  Finset.le_sup (f := Finset.card) (mem_independentSubsets.mpr ⟨hQ, hQc⟩)

theorem exists_independenceOrder (G : SimpleGraph V) (A : Finset V) :
    ∃ Q : Finset V, Q ⊆ A ∧ Gᶜ.IsNClique (independenceOrder G A) Q := by
  have h : (independentSubsets G A).Nonempty :=
    ⟨∅, mem_independentSubsets.mpr ⟨Finset.empty_subset _, by simp⟩⟩
  obtain ⟨Q, hQ, hEq⟩ := Finset.exists_mem_eq_sup _ h Finset.card
  obtain ⟨hQA, hQc⟩ := mem_independentSubsets.mp hQ
  exact ⟨Q, hQA, hQc, hEq.symm⟩

theorem independenceOrder_mono {G : SimpleGraph V} {A B : Finset V}
    (hAB : A ⊆ B) : independenceOrder G A ≤ independenceOrder G B := by
  obtain ⟨Q, hQA, hQc⟩ := exists_independenceOrder G A
  rw [← hQc.card_eq]
  exact card_le_independenceOrder (hQA.trans hAB) hQc.isClique

theorem independenceOrder_le_card (G : SimpleGraph V) (A : Finset V) :
    independenceOrder G A ≤ A.card := by
  obtain ⟨Q, hQA, hQc⟩ := exists_independenceOrder G A
  rw [← hQc.card_eq]
  exact Finset.card_le_card hQA

@[simp] theorem independenceOrder_empty (G : SimpleGraph V) : independenceOrder G ∅ = 0 :=
  Nat.eq_zero_of_le_zero (independenceOrder_le_card G ∅)

theorem card_inter_le_one_of_cliques {G : SimpleGraph V} {P Q : Finset V}
    (hP : G.IsClique (P : Set V)) (hQ : Gᶜ.IsClique (Q : Set V)) :
    (P ∩ Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyP, hyQ⟩ := Finset.mem_inter.mp hy
  exact ((SimpleGraph.compl_adj G x y).mp (hQ hxQ hyQ hxy)).2 (hP hxP hyP hxy)

/-- An independent set meets at most one vertex of each clique in a
cover. Several cliques may cover the same vertex. -/
theorem card_independent_le_clique_cover {G : SimpleGraph V} {J : Type*}
    (T : Finset J) (P : J → Finset V) (hP : ∀ j ∈ T, G.IsClique (P j : Set V))
    (Q : Finset V) (hQ : Gᶜ.IsClique (Q : Set V)) (hcovered : Q ⊆ T.biUnion P) :
    Q.card ≤ T.card := by
  classical
  have hsub : Q ⊆ T.biUnion (fun j => P j ∩ Q) := by
    intro x hx
    obtain ⟨j, hj, hxP⟩ := Finset.mem_biUnion.mp (hcovered hx)
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hxP, hx⟩⟩
  refine ((Finset.card_le_card hsub).trans Finset.card_biUnion_le).trans ?_
  calc
    _ ≤ ∑ _j ∈ T, 1 := Finset.sum_le_sum (fun j hj => card_inter_le_one_of_cliques (hP j hj) hQ)
    _ = _ := by simp

/-- The finite analogue of subadditivity of the largest independent-set
size over a cover. -/
theorem independenceOrder_le_sum_cover {G : SimpleGraph V} {J : Type*}
    (T : Finset J) (P : J → Finset V) {A : Finset V} (hcovered : A ⊆ T.biUnion P) :
    independenceOrder G A ≤ ∑ j ∈ T, independenceOrder G (P j) := by
  classical
  obtain ⟨Q, hQA, hQc⟩ := exists_independenceOrder G A
  have hsub : Q ⊆ T.biUnion (fun j => P j ∩ Q) := by
    intro x hx
    obtain ⟨j, hj, hxP⟩ := Finset.mem_biUnion.mp (hcovered (hQA hx))
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hxP, hx⟩⟩
  rw [← hQc.card_eq]
  refine ((Finset.card_le_card hsub).trans Finset.card_biUnion_le).trans ?_
  exact Finset.sum_le_sum (fun j _ => card_le_independenceOrder Finset.inter_subset_left
    (fun x hx y hy hxy => hQc.isClique (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2 hxy))

end LocallyRamsey
