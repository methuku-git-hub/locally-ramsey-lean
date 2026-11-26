module

public import LocallyRamsey.Upper.BinaryTree
public import LocallyRamsey.Threshold
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*}

/-- A set contains a clique of exactly the specified order. -/
def HasClique (G : SimpleGraph V) (s : ℕ) (X : Finset V) : Prop :=
  ∃ K : Finset V, K ⊆ X ∧ G.IsNClique s K

theorem HasClique.mono {G : SimpleGraph V} {s : ℕ} {X Y : Finset V}
    (h : HasClique G s X) (hXY : X ⊆ Y) : HasClique G s Y := by
  obtain ⟨K, hK, hclique⟩ := h
  exact ⟨K, hK.trans hXY, hclique⟩

namespace BinaryTree

variable {T : ℕ}

/-- The simultaneous merging property at a depth and a target order.
Each specified clique lies in its own branch. -/
def MergesAt (G : SimpleGraph (Leaf T)) (j a s q : ℕ) : Prop :=
  ∀ P : Finset ℕ, P ⊆ Finset.range (2 ^ j) → P.card = q →
    ∀ K : ℕ → Finset (Leaf T),
      (∀ v ∈ P, K v ⊆ branch Finset.univ j v ∧ G.IsNClique a (K v)) →
      ∃ v ∈ P, ∃ w ∈ P, v ≠ w ∧ HasClique G s (K v ∪ K w)

/-- Nodes whose branches in `X` contain an `a`-clique. -/
noncomputable def markedNodes (G : SimpleGraph (Leaf T)) (X : Finset (Leaf T))
    (a j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (2 ^ j)).filter (fun v => HasClique G a (branch X j v))

@[simp]
theorem mem_markedNodes {G : SimpleGraph (Leaf T)} {X : Finset (Leaf T)} {a j v : ℕ} :
    v ∈ markedNodes G X a j ↔ v < 2 ^ j ∧ HasClique G a (branch X j v) := by
  simp [markedNodes]

theorem card_markedNodes_lt {G : SimpleGraph (Leaf T)} {X : Finset (Leaf T)} {a j s q : ℕ}
    (hmerge : MergesAt G j a s q) (hX : ¬ HasClique G s X) :
    (markedNodes G X a j).card < q := by
  classical
  by_contra! hcard
  obtain ⟨P, hP, hq⟩ := Finset.exists_subset_card_eq hcard
  have hcl (v : ℕ) (hv : v ∈ P) : HasClique G a (branch X j v) :=
    (mem_markedNodes.mp (hP hv)).2
  choose clique hclique using hcl
  let K (v : ℕ) := if hv : v ∈ P then clique v hv else ∅
  have hK (v : ℕ) (hv : v ∈ P) : K v ⊆ branch X j v ∧ G.IsNClique a (K v) := by
    simpa [K, hv] using hclique v hv
  have hPnode : P ⊆ Finset.range (2 ^ j) :=
    fun _ hv => Finset.mem_range.mpr (mem_markedNodes.mp (hP hv)).1
  obtain ⟨v, hv, w, hw, _, hjoin⟩ := hmerge P hPnode hq K fun v hv =>
    ⟨(hK v hv).1.trans (by
      intro x hx
      exact mem_branch.mpr ⟨Finset.mem_univ x, (mem_branch.mp hx).2⟩), (hK v hv).2⟩
  exact hX (hjoin.mono (Finset.union_subset
    ((hK v hv).1.trans (Finset.filter_subset _ _))
    ((hK w hw).1.trans (Finset.filter_subset _ _))))

theorem card_branch_leaf_le_one (X : Finset (Leaf T)) (v : ℕ) :
    (branch X T v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  apply Fin.ext
  have h₁ := (mem_branch.mp hx).2
  have h₂ := (mem_branch.mp hy).2
  simpa only [prefix_leaf] using h₁.trans h₂.symm

/-- The base of the recurrence, using merging between singleton leaf
branches. -/
theorem card_lt_of_no_edge {G : SimpleGraph (Leaf T)} {X : Finset (Leaf T)} {q : ℕ}
    (hmerge : MergesAt G T 1 2 q) (hX : ¬ HasClique G 2 X) : X.card < q := by
  have hset : X.image Fin.val ⊆ markedNodes G X 1 T := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    refine mem_markedNodes.mpr ⟨x.isLt, ?_⟩
    exact ⟨{x}, by simpa using (mem_branch.mpr ⟨hx, prefix_leaf x⟩ :
      x ∈ branch X T x.val), SimpleGraph.isNClique_singleton.mpr rfl⟩
  have hcard := Finset.card_le_card hset
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  exact hcard.trans_lt (card_markedNodes_lt hmerge hX)

/-- The recurrence from Lemma 3, given the merging property at each
positive depth. A vertex is covered at the first unmarked node of its path. -/
theorem recurrence {G : SimpleGraph (Leaf T)} {X : Finset (Leaf T)} {a s q M : ℕ}
    (hT : 0 < T) (hq : 0 < q) (ha : 2 ≤ a)
    (hmerge : ∀ j, 0 < j → j ≤ T → MergesAt G j a s q)
    (hsmall : ∀ Y : Finset (Leaf T), ¬ HasClique G a Y → Y.card ≤ M)
    (hX : ¬ HasClique G s X) : X.card ≤ 2 * T * q * M := by
  classical
  by_cases hroot : HasClique G a X
  · let stopped (j : ℕ) := ((markedNodes G X a j).biUnion
        (fun v => {2 * v, 2 * v + 1})).filter
        (fun v => ¬ HasClique G a (branch X (j + 1) v))
    let slice (j : ℕ) := (stopped j).biUnion (branch X (j + 1))
    have hnodes (j : ℕ) (hj : j < T) : (markedNodes G X a j).card ≤ q := by
      by_cases hj0 : j = 0
      · subst j
        have hs : markedNodes G X a 0 ⊆ ({0} : Finset ℕ) := by
          intro v hv
          have h := (mem_markedNodes.mp hv).1
          simp at h
          simp [h]
        simpa using (Finset.card_le_card hs).trans (by simpa using Nat.succ_le_of_lt hq)
      · exact (card_markedNodes_lt (hmerge j (by omega) (by omega)) hX).le
    have hslicecard (j : ℕ) (hj : j < T) : (slice j).card ≤ 2 * q * M := by
      have hchild (v : ℕ) : ({2 * v, 2 * v + 1} : Finset ℕ).card ≤ 2 := by
        exact (Finset.card_insert_le _ _).trans (by simp)
      have hstopped : (stopped j).card ≤ q * 2 :=
        (Finset.card_filter_le _ _).trans <|
          (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hchild v)).trans
            (Nat.mul_le_mul_right 2 (hnodes j hj))
      have hpart (v : ℕ) (hv : v ∈ stopped j) : (branch X (j + 1) v).card ≤ M :=
        hsmall _ (Finset.mem_filter.mp hv).2
      exact (Finset.card_biUnion_le_card_mul _ _ _ hpart).trans
        (by simpa [mul_comm q 2] using Nat.mul_le_mul_right M hstopped)
    have hcovered : X ⊆ (Finset.range T).biUnion slice := by
      intro x hx
      have hex : ∃ j, ¬ HasClique G a (branch X j (ancestor j x)) := by
        refine ⟨T, ?_⟩
        rintro ⟨K, hK, hk⟩
        have hcard := (SimpleGraph.isNClique_iff G).mp hk |>.2
        have hle := (Finset.card_le_card hK).trans (card_branch_leaf_le_one X _)
        omega
      let j := Nat.find hex
      have hstop : ¬ HasClique G a (branch X j (ancestor j x)) := Nat.find_spec hex
      have hjT : j ≤ T := Nat.find_min' hex (by
        rintro ⟨K, hK, hk⟩
        have hcard := (SimpleGraph.isNClique_iff G).mp hk |>.2
        have hle := (Finset.card_le_card hK).trans (card_branch_leaf_le_one X _)
        omega)
      have hjpos : 0 < j := by
        by_contra! hj
        have hj0 : j = 0 := by omega
        exact hstop (by simpa [hj0] using hroot)
      let k := j - 1
      have hkj : k + 1 = j := by dsimp [k]; omega
      have hkT : k < T := by omega
      have hparent := prefix_parent hkT x
      rw [hkj] at hparent
      have hmarked : ancestor k x ∈ markedNodes G X a k := by
        refine mem_markedNodes.mpr ⟨prefix_lt (by omega) x, ?_⟩
        by_contra! hm
        exact (Nat.find_min hex (show k < Nat.find hex by omega)) hm
      have hc : ancestor j x = 2 * ancestor k x ∨ ancestor j x = 2 * ancestor k x + 1 := by omega
      have hst : ancestor j x ∈ stopped k := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨ancestor k x, hmarked, ?_⟩, ?_⟩
        · simpa [Finset.mem_insert] using hc
        · simpa [hkj] using hstop
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkT,
        Finset.mem_biUnion.mpr ⟨ancestor j x, hst, mem_branch.mpr ⟨hx, by rw [hkj]⟩⟩⟩
    have hsize := (Finset.card_le_card hcovered).trans
      (Finset.card_biUnion_le_card_mul _ _ _ (fun j hj => hslicecard j (Finset.mem_range.mp hj)))
    simpa [mul_assoc, mul_comm T 2, mul_left_comm T] using hsize
  · exact (hsmall X hroot).trans (Nat.le_mul_of_pos_left _ (by positivity))

/-- The iterated bound obtained by reducing the target order at each
merge, with the two-vertex bound as its base case. -/
def mergingBound (T : ℕ) (a q : ℕ → ℕ) (s : ℕ) : ℕ :=
  if h : 2 < s ∧ a s < s then 2 * T * q s * mergingBound T a q (a s)
  else q 2
termination_by s
decreasing_by exact h.2

theorem card_le_mergingBound {G : SimpleGraph (Leaf T)} {a q : ℕ → ℕ} {r : ℕ}
    (hT : 0 < T) (ha : ∀ s, 2 < s → s ≤ r → 2 ≤ a s ∧ a s < s)
    (hq : ∀ s, 2 < s → s ≤ r → 0 < q s)
    (hbase : MergesAt G T 1 2 (q 2))
    (hmerges : ∀ s, 2 < s → s ≤ r → ∀ j, 0 < j → j ≤ T → MergesAt G j (a s) s (q s))
    (s : ℕ) (hs : 2 ≤ s) (hr : s ≤ r) (X : Finset (Leaf T)) (hX : ¬ HasClique G s X) :
    X.card ≤ mergingBound T a q s := by
  induction s using Nat.strong_induction_on generalizing X with
  | h s ih =>
    by_cases hbig : 2 < s
    · obtain ⟨ha₂, has⟩ := ha s hbig hr
      rw [mergingBound, dite_eq_left ⟨hbig, has⟩]
      exact recurrence hT (hq s hbig hr) ha₂ (hmerges s hbig hr)
        (fun Y hY => ih (a s) has ha₂ (has.le.trans hr) Y hY) hX
    · have heq : s = 2 := by omega
      subst s
      rw [mergingBound]
      simp only [lt_self_iff_false, false_and, dite_false]
      exact (card_lt_of_no_edge hbase hX).le

/-- A graph and its complement with the merging properties satisfy the
local Ramsey condition at the resulting bound plus one. -/
theorem isLocallyRamsey_of_merges {G : SimpleGraph (Leaf T)} {a q : ℕ → ℕ} {r : ℕ}
    (hT : 0 < T) (hr : 2 ≤ r)
    (ha : ∀ s, 2 < s → s ≤ r → 2 ≤ a s ∧ a s < s)
    (hq : ∀ s, 2 < s → s ≤ r → 0 < q s)
    (hbase : MergesAt G T 1 2 (q 2)) (hbase' : MergesAt Gᶜ T 1 2 (q 2))
    (hmerges : ∀ s, 2 < s → s ≤ r → ∀ j, 0 < j → j ≤ T → MergesAt G j (a s) s (q s))
    (hmerges' : ∀ s, 2 < s → s ≤ r → ∀ j, 0 < j → j ≤ T → MergesAt Gᶜ j (a s) s (q s)) :
    IsLocallyRamsey G (mergingBound T a q r + 1) r := by
  intro X hcard
  have hG : HasClique G r X := by
    by_contra h
    have hle := card_le_mergingBound hT ha hq hbase hmerges r hr le_rfl X h
    omega
  have hGc : HasClique Gᶜ r X := by
    by_contra h
    have hle := card_le_mergingBound hT ha hq hbase' hmerges' r hr le_rfl X h
    omega
  exact ⟨hG, hGc⟩

end BinaryTree
end LocallyRamsey
