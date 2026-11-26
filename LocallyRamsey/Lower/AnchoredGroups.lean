module

public import LocallyRamsey.Lower.CompanionGroups
public import Mathlib.Data.Finset.Preimage

public section

open scoped BigOperators

namespace LocallyRamsey

variable {I : Type*} [DecidableEq I]

/-- Restore the common position to a group of other positions. -/
@[expose] def restoreAnchor (U : Finset I) (i : I) (A : Finset ↥(U.erase i)) : Finset I :=
  insert i (A.map ⟨Subtype.val, Subtype.val_injective⟩)

theorem card_restoreAnchor (U : Finset I) (i : I) (A : Finset ↥(U.erase i)) :
    (restoreAnchor U i A).card = A.card + 1 := by
  have hn : i ∉ A.map (⟨Subtype.val, Subtype.val_injective⟩ : ↥(U.erase i) ↪ I) := by
    intro h
    obtain ⟨x, _, he⟩ := Finset.mem_map.mp h
    exact (Finset.mem_erase.mp x.property).1 he
  rw [restoreAnchor, Finset.card_insert_of_notMem hn, Finset.card_map]

theorem restoreAnchor_injective (U : Finset I) (i : I) : Function.Injective (restoreAnchor U i) := by
  intro A B h
  let e : ↥(U.erase i) ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have hnone (S : Finset ↥(U.erase i)) : i ∉ S.map e := by
    intro hi
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hi
    exact (Finset.mem_erase.mp x.property).1 hx
  have heq := congrArg (fun J : Finset I => J.erase i) h
  have heq' : A.map e = B.map e := by simpa [restoreAnchor, e, hnone A, hnone B] using heq
  exact (Finset.map_injective e) heq'

/-- The image of disjoint companion blocks after restoring the anchor. -/
theorem restored_companions_image (U : Finset I) {i : I} (hi : i ∈ U) {q : ℕ} (hq : 0 < q)
    (A : Finset ↥(U.erase i)) :
    let e : ↥(U.erase i) ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
    let F := A.map e
    let all := U.powersetCard q
    let good := ((Finset.univ : Finset ↥(U.erase i)).powersetCard (q - 1)).filter (fun T => Disjoint A T)
    (all.filter (fun J => i ∈ J ∧ Disjoint J F)) = good.image (restoreAnchor U i) := by
  classical
  intro e F all good
  have hF : F ⊆ U.erase i := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hy
    exact x.property
  have hFi : i ∉ F := fun h => (Finset.mem_erase.mp (hF h)).1 rfl
  ext T
  constructor
  · intro hT
    obtain ⟨hTq, hiT, hTF⟩ := Finset.mem_filter.mp hT
    obtain ⟨hTU, hTcard⟩ := Finset.mem_powersetCard.mp hTq
    let B := (T.erase i).preimage e e.injective.injOn
    have hBEq : B.map e = T.erase i := by
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_preimage.mp hy
      · intro hx
        have hxU := Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hx).1, hTU (Finset.mem_erase.mp hx).2⟩
        exact Finset.mem_map.mpr ⟨⟨x, hxU⟩, Finset.mem_preimage.mpr hx, rfl⟩
    have hBcard : B.card = q - 1 := by
      rw [← Finset.card_map e, hBEq, Finset.card_erase_of_mem hiT, hTcard]
    have hd : Disjoint A B := Finset.disjoint_left.mpr fun x hxA hxB =>
      Finset.disjoint_left.mp hTF (Finset.erase_subset _ _ (Finset.mem_preimage.mp hxB))
        (Finset.mem_map.mpr ⟨x, hxA, rfl⟩)
    refine Finset.mem_image.mpr ⟨B, Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hBcard⟩, hd⟩, ?_⟩
    change insert i (B.map e) = T
    rw [hBEq, Finset.insert_erase hiT]
  · intro hT
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hBq, hAB⟩ := Finset.mem_filter.mp hB
    have hBcard := (Finset.mem_powersetCard.mp hBq).2
    have hSub : B.map e ⊆ U := by
      intro x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
      exact Finset.erase_subset _ _ y.property
    have hdisj : Disjoint (B.map e) F := by
      apply Finset.disjoint_left.mpr
      intro x hx hxF
      obtain ⟨a, ha, hea⟩ := Finset.mem_map.mp hxF
      obtain ⟨b, hb, heb⟩ := Finset.mem_map.mp hx
      have hEq : a = b := e.injective (hea.trans heb.symm)
      exact Finset.disjoint_left.mp hAB ha (hEq.symm ▸ hb)
    have hcard : (restoreAnchor U i B).card = q := by
      rw [card_restoreAnchor, hBcard]
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.insert_subset_iff.mpr ⟨hi, hSub⟩, hcard⟩, Finset.mem_insert_self _ _,
      Finset.disjoint_insert_left.mpr ⟨hFi, hdisj⟩⟩

/-- Arithmetic mean over groups whose parts outside the anchor are
disjoint from a fixed group. Restoring the common position makes this
the same average as conditioning on the anchor and avoiding the other
positions of the fixed group. -/
theorem mean_restored_companions_le (U : Finset I) {i : I} (hi : i ∈ U)
    (q : ℕ) (hq : 2 ≤ q) (hqU : q ≤ U.card)
    (A : Finset ↥(U.erase i)) (hA : A.card = q - 1)
    (hsize : 2 * (q - 1) * (q - 1) ≤ (U.erase i).card)
    (f : Finset I → ℝ) (hf : ∀ T, 0 ≤ f T) :
    let all := U.powersetCard q
    let good := ((Finset.univ : Finset ↥(U.erase i)).powersetCard (q - 1)).filter (fun B => Disjoint A B)
    (∑ B ∈ good, f (restoreAnchor U i B)) / good.card ≤
      (2 * (U.card : ℝ) / q) * ((∑ J ∈ all, f J) / all.card) := by
  classical
  intro all good
  let e : ↥(U.erase i) ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  let F := A.map e
  have hF : F ⊆ U.erase i := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hy
    exact x.property
  have hFi : i ∉ F := fun h => (Finset.mem_erase.mp (hF h)).1 rfl
  let allowed := all.filter (fun J => i ∈ J ∧ Disjoint J F)
  have hEquals : allowed = good.image (restoreAnchor U i) :=
    restored_companions_image U hi (by omega) A
  have hn : 2 * F.card * (q - 1) ≤ (U.erase i).card := by simpa [F, hA] using hsize
  have hBound := mean_groups_through_avoiding_le U F hi hF hq hqU hn f hf
  change (∑ J ∈ allowed, f J) / allowed.card ≤ _ at hBound
  rw [hEquals, Finset.card_image_of_injective _ (restoreAnchor_injective U i),
    Finset.sum_image (fun _ _ _ _ hh => restoreAnchor_injective U i hh)] at hBound
  exact hBound

/-- A set of at least (hk) positions has (h) disjoint blocks of size
(k). Unused positions may be discarded. -/
theorem exists_disjoint_blocks_of_mul_le (U : Finset I) {h k : ℕ} (hle : h * k ≤ U.card) :
    ∃ block : Fin h → Finset I, (∀ j, block j ⊆ U) ∧
      (∀ j, (block j).card = k) ∧ Pairwise (fun j l => Disjoint (block j) (block l)) := by
  classical
  obtain ⟨A, hAU, hA⟩ := Finset.exists_subset_card_eq hle
  let f : Fin h × Fin k ≃ ↥A := Fintype.equivOfCardEq (by simp [hA])
  let idx (j : Fin h) : Fin k ↪ I :=
    ⟨fun x => (f (j, x)).val,
      fun _ _ h => congrArg Prod.snd (f.injective (Subtype.ext h))⟩
  let block (j : Fin h) := Finset.univ.map (idx j)
  refine ⟨block, fun j x hx => ?_, fun j => by simp [block], ?_⟩
  · obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hx
    exact hAU (f (j, t)).property
  · intro j l hneq
    apply Finset.disjoint_left.mpr
    intro x hxj hxl
    obtain ⟨a, _, hae⟩ := Finset.mem_map.mp hxj
    obtain ⟨b, _, hbe⟩ := Finset.mem_map.mp hxl
    exact hneq (congrArg Prod.fst (f.injective (Subtype.ext (hae.trans hbe.symm))))

/-- Leave out the anchor before forming (h) blocks of size (q-1). -/
theorem exists_anchored_blocks (U : Finset I) (i : I) (hi : i ∈ U)
    {h q : ℕ} (hh : 0 < h) (hq : 0 < q) (hU : U.card = q * h) :
    ∃ block : Fin h → Finset ↥(U.erase i), (∀ j, (block j).card = q - 1) ∧
      Pairwise (fun j l => Disjoint (block j) (block l)) := by
  have hP : h * (q - 1) ≤ (U.erase i).card := by
    rw [Finset.card_erase_of_mem hi, hU, Nat.mul_sub_left_distrib, Nat.mul_one, mul_comm h q]
    omega
  obtain ⟨blocks, _, hcard, hdisj⟩ :=
    exists_disjoint_blocks_of_mul_le (Finset.univ : Finset ↥(U.erase i))
      (show h * (q - 1) ≤ (Finset.univ : Finset ↥(U.erase i)).card by simpa using hP)
  exact ⟨blocks, hcard, hdisj⟩

end LocallyRamsey
