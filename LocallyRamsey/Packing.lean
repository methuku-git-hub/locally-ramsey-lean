module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

public section

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- The disjoint packing used to select a family of cliques or independent
sets. Every large enough remaining set contains a nonempty member of the
family, so the process leaves fewer than `d` uncovered vertices. -/
theorem exists_packing {U : Finset V} {d b : ℕ} (hb : 0 < b)
    (family : Finset V → Prop)
    (hsupply : ∀ A : Finset V, A ⊆ U → d ≤ A.card →
      ∃ P : Finset V, P ⊆ A ∧ P.card = b ∧ family P) :
    ∃ packing : Finset (Finset V),
      (∀ P ∈ packing, P ⊆ U ∧ P.card = b ∧ family P) ∧
      (packing : Set (Finset V)).Pairwise Disjoint ∧
      (U \ packing.biUnion id).card < d := by
  suffices h : ∀ n (A : Finset V), A.card = n → A ⊆ U →
      ∃ packing : Finset (Finset V),
        (∀ P ∈ packing, P ⊆ A ∧ P.card = b ∧ family P) ∧
        (packing : Set (Finset V)).Pairwise Disjoint ∧
        (A \ packing.biUnion id).card < d from h U.card U rfl (Finset.Subset.refl U)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hcard hAU
    by_cases hlarge : d ≤ A.card
    · obtain ⟨P, hPA, hPcard, hPfamily⟩ := hsupply A hAU hlarge
      have hlt : (A \ P).card < n := by
        rw [Finset.card_sdiff_of_subset hPA, hPcard, hcard]
        have hp := Finset.card_le_card hPA
        omega
      obtain ⟨packing, hall, hpair, hrem⟩ :=
        ih (A \ P).card hlt (A \ P) rfl (Finset.sdiff_subset.trans hAU)
      refine ⟨insert P packing, ?_, ?_, ?_⟩
      · intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact ⟨hPA, hPcard, hPfamily⟩
        · exact ⟨(hall Q hQ).1.trans Finset.sdiff_subset, (hall Q hQ).2⟩
      · simp only [Finset.coe_insert, Set.pairwise_insert]
        refine ⟨hpair, fun Q hQ _ => ?_⟩
        have hDQ : Disjoint Q P :=
          Finset.disjoint_left.mpr fun _ hx hxP =>
            (Finset.mem_sdiff.mp ((hall Q hQ).1 hx)).2 hxP
        exact ⟨hDQ.symm, hDQ⟩
      · convert hrem using 2
        ext x
        simp [Finset.biUnion_insert, and_assoc]
    · exact ⟨∅, by simp, by simp, by simpa using Nat.lt_of_not_ge hlarge⟩

end LocallyRamsey
