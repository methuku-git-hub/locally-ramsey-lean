module

public import LocallyRamsey.Lower.CommonNeighborList
public import LocallyRamsey.Lower.PackedTests
public import Mathlib.Data.Nat.Choose.Sum

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Y : Type*} [DecidableEq V]

/-- The positions of the neighbours of one vertex on a list. Repeated
occurrences have separate positions. -/
@[expose] def listSignature {m : ℕ} (adj : Y → V → Prop) [DecidableRel adj]
    (L : Fin m → Y) (x : V) : Finset (Fin m) :=
  Finset.univ.filter (fun i => adj (L i) x)

/-- If every list entry has at most a (lambda) fraction of the vertices
as neighbours, at least half the vertices have at most (2lambda m)
neighbours on the list. -/
theorem card_small_signatures_ge_half {m : ℕ} (hm : 0 < m)
    (adj : Y → V → Prop) [DecidableRel adj] (L : Fin m → Y)
    (U : Finset V) {density : ℝ} (hdensity : 0 < density)
    (hdeg : ∀ i, ((U.filter (adj (L i))).card : ℝ) ≤ density * U.card) :
    (U.card : ℝ) / 2 ≤ ((U.filter (fun x => ((listSignature adj L x).card : ℝ) ≤ 2 * density * m)).card : ℝ) := by
  classical
  let good := U.filter (fun x => ((listSignature adj L x).card : ℝ) ≤ 2 * density * m)
  let bad := U.filter (fun x => 2 * density * m < ((listSignature adj L x).card : ℝ))
  have hs (x : V) : ((listSignature adj L x).card : ℝ) =
      ∑ i : Fin m, if adj (L i) x then (1 : ℝ) else 0 := by simp [listSignature]
  have heq : (∑ x ∈ U, ((listSignature adj L x).card : ℝ)) =
      ∑ i : Fin m, ((U.filter (adj (L i))).card : ℝ) := by
    simp_rw [hs]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  have hsum : (∑ x ∈ U, ((listSignature adj L x).card : ℝ)) ≤ (m : ℝ) * (density * U.card) := by
    rw [heq]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdeg i)
  have hfloor : (bad.card : ℝ) * (2 * density * m) ≤ ∑ x ∈ U, ((listSignature adj L x).card : ℝ) := by
    change (bad.card : ℝ) * (2 * density * m) ≤ _
    have hs₁ : ∑ _x ∈ bad, 2 * density * m ≤ ∑ x ∈ bad, ((listSignature adj L x).card : ℝ) :=
      Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp hx).2.le)
    have hs₂ : ∑ x ∈ bad, ((listSignature adj L x).card : ℝ) ≤
        ∑ x ∈ U, ((listSignature adj L x).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    simpa using hs₁.trans hs₂
  have hsplit : good.card + bad.card = U.card := by
    have he : bad = U.filter (fun x => ¬(((listSignature adj L x).card : ℝ) ≤ 2 * density * m)) := by
      ext x
      simp [bad]
    rw [he]
    exact Finset.card_filter_add_card_filter_not _
  have hsplit' : (good.card : ℝ) + bad.card = U.card := by exact_mod_cast hsplit
  have hmul : 0 < density * (m : ℝ) := mul_pos hdensity (by exact_mod_cast hm)
  have hbad : 2 * (bad.card : ℝ) ≤ U.card := by
    by_contra! h
    have hcontra := mul_lt_mul_of_pos_right h hmul
    nlinarith only [hcontra, hsum, hfloor]
  change (U.card : ℝ) / 2 ≤ good.card
  linarith only [hbad, hsplit']

/-- Coarse but sufficient count of (d)-sparse signatures. -/
theorem card_small_signatures_le (m d : ℕ) :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.card ≤ d)).card ≤ (m + 1) ^ d := by
  classical
  let U : Finset (Fin m) := Finset.univ
  let S : Finset (Finset (Fin m)) := Finset.univ.filter (fun T => T.card ≤ d)
  have hsub : S ⊆ (Finset.range (d + 1)).biUnion (fun j => U.powersetCard j) := by
    intro P hP
    have hPc := (Finset.mem_filter.mp hP).2
    exact Finset.mem_biUnion.mpr ⟨P.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ P, rfl⟩⟩
  change S.card ≤ _
  refine ((Finset.card_le_card hsub).trans Finset.card_biUnion_le).trans ?_
  simp only [Finset.card_powersetCard, U, Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ ∑ j ∈ Finset.range (d + 1), m ^ j := Finset.sum_le_sum (fun j _ => Nat.choose_le_pow m j)
    _ ≤ ∑ j ∈ Finset.range (d + 1), m ^ j * 1 ^ (d - j) * d.choose j := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have h := Nat.choose_pos (show j ≤ d by have := Finset.mem_range.mp hj; omega)
      simpa using Nat.mul_le_mul_left (m ^ j) (Nat.succ_le_of_lt h)
    _ = _ := by rw [add_pow]; simp

/-- With the signatures fixed, packing sets within classes leaves fewer
than (v_0) vertices in each class. The total deficit is at most
(v_0) times the number of possible signatures. -/
theorem pack_within_list_classes {m : ℕ} (adj : Y → V → Prop) [DecidableRel adj]
    (L : Fin m → Y) (U : Finset V) (d v₀ b : ℕ) (hb : 0 < b) (family : Finset V → Prop)
    (hshort : ∀ x ∈ U, (listSignature adj L x).card ≤ d)
    (hsupply : ∀ A : Finset V, A ⊆ U → v₀ ≤ A.card →
      ∃ F : Finset V, F ⊆ A ∧ F.card = b ∧ family F) :
    ∃ packing : Finset (Finset V),
      (∀ F ∈ packing, F ⊆ U ∧ F.card = b ∧ family F ∧
        ∀ x y, x ∈ F → y ∈ F → listSignature adj L x = listSignature adj L y) ∧
      (packing : Set (Finset V)).Pairwise Disjoint ∧
      (U \ packing.biUnion id).card ≤ (m + 1) ^ d * v₀ := by
  classical
  let homogeneous := fun F : Finset V =>
    F.card = b ∧ family F ∧ ∀ x y, x ∈ F → y ∈ F → listSignature adj L x = listSignature adj L y
  obtain ⟨packing, hpack, hdisj, hmax⟩ := exists_maximal_disjoint_packing U homogeneous
    (fun F hF => Finset.card_pos.mp (hF.1 ▸ hb))
  refine ⟨packing, hpack, hdisj, ?_⟩
  let X := U \ packing.biUnion id
  let fiber (s : Finset (Fin m)) := X.filter (fun x => listSignature adj L x = s)
  let codes := (Finset.univ : Finset (Finset (Fin m))).filter (fun s => s.card ≤ d)
  have hsize (s : Finset (Fin m)) : (fiber s).card < v₀ := by
    by_contra! h
    obtain ⟨F, hF, hbF, hfam⟩ := hsupply (fiber s)
      ((Finset.filter_subset _ _).trans Finset.sdiff_subset) h
    exact hmax F (hF.trans (Finset.filter_subset _ _)) ⟨hbF, hfam, fun x y hx hy =>
      ((Finset.mem_filter.mp (hF hx)).2).trans (Finset.mem_filter.mp (hF hy)).2.symm⟩
  have hX : X ⊆ codes.biUnion fiber := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨listSignature adj L x,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hshort x (Finset.sdiff_subset hx)⟩,
      Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  refine ((Finset.card_le_card hX).trans Finset.card_biUnion_le).trans ?_
  calc
    _ ≤ ∑ _s ∈ codes, v₀ := Finset.sum_le_sum (fun s _ => (hsize s).le)
    _ = codes.card * v₀ := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_small_signatures_le m d)


/-- A set larger than the total deficit contains a member lying entirely
in one class. This applies to any subset of the original vertex set. -/
theorem exists_in_one_list_class {m : ℕ} (adj : Y → V → Prop) [DecidableRel adj]
    (L : Fin m → Y) (A : Finset V) (d v₀ b : ℕ) (hb : 0 < b)
    (family : Finset V → Prop) (hshort : ∀ x ∈ A, (listSignature adj L x).card ≤ d)
    (hsupply : ∀ B : Finset V, B ⊆ A → v₀ ≤ B.card →
      ∃ F : Finset V, F ⊆ B ∧ F.card = b ∧ family F)
    (hLarge : (m + 1) ^ d * v₀ < A.card) :
    ∃ F : Finset V, F ⊆ A ∧ F.card = b ∧ family F ∧
      ∀ x y, x ∈ F → y ∈ F → listSignature adj L x = listSignature adj L y := by
  obtain ⟨packing, hp, _, hDeficit⟩ :=
    pack_within_list_classes adj L A d v₀ b hb family hshort hsupply
  have hNonempty : packing.Nonempty := by
    by_contra h
    have hEmpty : packing = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hEmpty] at hDeficit
    exact (not_lt_of_ge hDeficit) hLarge
  obtain ⟨F, hF⟩ := hNonempty
  exact ⟨F, hp F hF⟩

/-- The deficit bound also suffices to choose a random union of whole
cliques from the packing in the initial sampling argument. -/
theorem pack_list_classes_for_unions {m : ℕ} (adj : Y → V → Prop) [DecidableRel adj]
    (L : Fin m → Y) (A : Finset V) (d v₀ K b : ℕ) (hb : 0 < b)
    (family : Finset V → Prop) (hshort : ∀ x ∈ A, (listSignature adj L x).card ≤ d)
    (hsupply : ∀ B : Finset V, B ⊆ A → v₀ ≤ B.card →
      ∃ F : Finset V, F ⊆ B ∧ F.card = b ∧ family F)
    (hSize : 4 * ((m + 1) ^ d * v₀ + K * b) ≤ 3 * A.card) :
    ∃ packing : Finset (Finset V),
      (∀ F ∈ packing, F ⊆ A ∧ F.card = b ∧ family F ∧
        ∀ x y, x ∈ F → y ∈ F → listSignature adj L x = listSignature adj L y) ∧
      (packing : Set (Finset V)).Pairwise Disjoint ∧
      A.card + 4 * (K * b) ≤ 4 * (packing.card * b) := by
  obtain ⟨packing, hp, hD, hDeficit⟩ :=
    pack_within_list_classes adj L A d v₀ b hb family hshort hsupply
  have hCover : packing.biUnion id ⊆ A := fun x hx => by
    obtain ⟨F, hF, hxF⟩ := Finset.mem_biUnion.mp hx
    exact (hp F hF).1 hxF
  have hCard : (packing.biUnion id).card = packing.card * b := by
    change (packing.biUnion (fun P => P)).card = _
    rw [Finset.card_biUnion hD]
    trans ∑ _F ∈ packing, b
    · exact Finset.sum_congr rfl (fun F hF => (hp F hF).2.1)
    · simp
  rw [Finset.card_sdiff_of_subset hCover, hCard] at hDeficit
  have hLe := Finset.card_le_card hCover
  rw [hCard] at hLe
  exact ⟨packing, hp, hD, by omega⟩

end LocallyRamsey
