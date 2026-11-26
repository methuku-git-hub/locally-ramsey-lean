module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Tactic

public section

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The missing edges between two fixed cliques, each oriented from the
first clique to the second. -/
@[expose] def missingCrossEdges (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter fun p => ¬ G.Adj p.1 p.2

/-- The deterministic part of Lemma 2. Delete the first endpoint of
every missing cross edge, costing at most one vertex per missing edge. -/
theorem merge_cliques {A B : Finset V} {s : ℕ}
    (hd : Disjoint A B) (hA : G.IsClique (A : Set V)) (hB : G.IsClique (B : Set V))
    (hs : s + (missingCrossEdges G A B).card ≤ A.card + B.card) :
    ∃ K : Finset V, K ⊆ A ∪ B ∧ G.IsNClique s K := by
  let bad := (missingCrossEdges G A B).image Prod.fst
  have hbad : bad ⊆ A := by
    intro x hx
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (Finset.mem_filter.mp huv).1).1
  have hbadcard : bad.card ≤ (missingCrossEdges G A B).card := Finset.card_image_le
  have hcomplete : ∀ u ∈ A \ bad, ∀ v ∈ B, G.Adj u v := by
    intro u hu v hv
    by_contra hmissing
    have huv : (u, v) ∈ missingCrossEdges G A B :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp hu).1, hv⟩, hmissing⟩
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨(u, v), huv, rfl⟩)
  let R := (A \ bad) ∪ B
  have hR : R ⊆ A ∪ B := Finset.union_subset_union Finset.sdiff_subset (Finset.Subset.refl _)
  have hRd : Disjoint (A \ bad) B := hd.mono_left Finset.sdiff_subset
  have hcard : s ≤ R.card := by
    rw [show R = (A \ bad) ∪ B from rfl, Finset.card_union_of_disjoint hRd,
      Finset.card_sdiff_of_subset hbad]
    omega
  have hclique : G.IsClique (R : Set V) := by
    intro u hu v hv hne
    rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
    · exact hA (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hv).1 hne
    · exact hcomplete u hu v hv
    · exact (hcomplete v hv u hu).symm
    · exact hB hu hv hne
  obtain ⟨K, hK, hKcard⟩ := Finset.exists_subset_card_eq hcard
  exact ⟨K, hK.trans hR, (SimpleGraph.isNClique_iff G).2 ⟨hclique.subset hK, hKcard⟩⟩

end LocallyRamsey
