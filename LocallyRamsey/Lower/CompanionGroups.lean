module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic

public section

open scoped BigOperators

namespace LocallyRamsey

variable {J : Type*} [DecidableEq J]

/-- Among the (k)-subsets of (U), at most a fraction
(|F|k/|U|) meet the forbidden positions (F). -/
theorem card_groups_meeting_le (U F : Finset J) (hFU : F ⊆ U) {k : ℕ} (hk : 0 < k) :
    (((U.powersetCard k).filter (fun I => ¬Disjoint I F)).card) * U.card ≤
      F.card * k * (U.powersetCard k).card := by
  classical
  let through (x : J) := (U.powersetCard k).filter (fun I => x ∈ I)
  have hsub : (U.powersetCard k).filter (fun I => ¬Disjoint I F) ⊆ F.biUnion through := by
    intro I hI
    obtain ⟨hIU, hIF⟩ := Finset.mem_filter.mp hI
    obtain ⟨x, hxI, hxF⟩ := Finset.not_disjoint_iff.mp hIF
    exact Finset.mem_biUnion.mpr ⟨x, hxF, Finset.mem_filter.mpr ⟨hIU, hxI⟩⟩
  have hcount : ((U.powersetCard k).filter (fun I => ¬Disjoint I F)).card ≤
      F.card * (U.card - 1).choose (k - 1) := by
    refine ((Finset.card_le_card hsub).trans Finset.card_biUnion_le).trans_eq ?_
    calc
      _ = ∑ _x ∈ F, (U.card - 1).choose (k - 1) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hsingleton : ({x} : Finset J) ⊆ U := Finset.singleton_subset_iff.mpr (hFU hx)
        change ((U.powersetCard k).filter (fun I => x ∈ I)).card = _
        simpa only [Finset.singleton_subset_iff, Finset.card_singleton] using
          Finset.card_filter_powersetCard_subset {x} U k hsingleton (by simp; omega)
      _ = _ := by simp
  have h := Nat.choose_mul (n := U.card) (k := k) (s := 1) (by omega)
  rw [Nat.choose_one_right, Nat.choose_one_right] at h
  calc
    _ ≤ (F.card * (U.card - 1).choose (k - 1)) * U.card := Nat.mul_le_mul_right _ hcount
    _ = F.card * (U.card * (U.card - 1).choose (k - 1)) := by ring
    _ = _ := by rw [← h, Finset.card_powersetCard]; ring

/-- If the forbidden set is small enough, at least half the fixed-size
groups avoid it. -/
theorem card_groups_avoiding_ge (U F : Finset J) (hFU : F ⊆ U) {k : ℕ} (hk : 0 < k)
    (hs : 2 * F.card * k ≤ U.card) :
    (U.powersetCard k).card ≤ 2 * ((U.powersetCard k).filter (fun I => Disjoint I F)).card := by
  classical
  by_cases hU : U = ∅
  · simp [hU, Nat.choose_eq_zero_of_lt hk]
  have hpos : 0 < U.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
  let Z := U.powersetCard k
  let bad := Z.filter (fun I => ¬Disjoint I F)
  let good := Z.filter (fun I => Disjoint I F)
  have hpart : good.card + bad.card = Z.card := Finset.card_filter_add_card_filter_not _
  have hbad : 2 * bad.card ≤ Z.card := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc
      _ = 2 * (bad.card * U.card) := by ring
      _ ≤ 2 * (F.card * k * Z.card) := Nat.mul_le_mul_left _ (card_groups_meeting_le U F hFU hk)
      _ = (2 * F.card * k) * Z.card := by ring
      _ ≤ U.card * Z.card := Nat.mul_le_mul_right _ hs
      _ = _ := by ring
  change Z.card ≤ 2 * good.card
  omega

/-- Anchoring a group at one position and excluding the other positions
of a fixed group. For any nonnegative test, conditioning on the two
requirements costs at most twice the reciprocal of the anchor probability. -/
theorem mean_groups_through_avoiding_le (U F : Finset J) {i : J} (hi : i ∈ U)
    (hF : F ⊆ U.erase i) {q : ℕ} (hq : 2 ≤ q) (hqU : q ≤ U.card)
    (hs : 2 * F.card * (q - 1) ≤ (U.erase i).card)
    (f : Finset J → ℝ) (hf : ∀ I, 0 ≤ f I) :
    let all := U.powersetCard q
    let allowed := all.filter (fun I => i ∈ I ∧ Disjoint I F)
    (∑ I ∈ allowed, f I) / allowed.card ≤
      (2 * (U.card : ℝ) / q) * ((∑ I ∈ all, f I) / all.card) := by
  classical
  intro all allowed
  let reduced := ((U.erase i).powersetCard (q - 1)).filter (fun I => Disjoint I F)
  have hiF : i ∉ F := fun h => (Finset.mem_erase.mp (hF h)).1 rfl
  have hImage : allowed = reduced.image (insert i) := by
    ext I
    simp only [allowed, all, reduced, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_image]
    constructor
    · rintro ⟨⟨hIU, hIq⟩, hii, hIF⟩
      refine ⟨I.erase i, ⟨⟨?_, ?_⟩, hIF.mono_left (Finset.erase_subset _ _)⟩,
        Finset.insert_erase hii⟩
      · exact fun x hx => Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hIU (Finset.mem_erase.mp hx).2⟩
      · rw [Finset.card_erase_of_mem hii, hIq]
    · rintro ⟨I, ⟨⟨hI, hIc⟩, hd⟩, rfl⟩
      have hiI : i ∉ I := fun h => (Finset.mem_erase.mp (hI h)).1 rfl
      refine ⟨⟨Finset.insert_subset_iff.mpr ⟨hi, hI.trans (Finset.erase_subset _ _)⟩, ?_⟩,
        Finset.mem_insert_self _ _, ?_⟩
      · rw [Finset.card_insert_of_notMem hiI, hIc]
        omega
      · exact Finset.disjoint_insert_left.mpr ⟨hiF, hd⟩
  have hInj : Set.InjOn (insert i) (reduced : Set (Finset J)) := by
    intro A hA B hB hab
    have hno (C : Finset J) (hC : C ∈ reduced) : i ∉ C := fun hx =>
      (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp ((Finset.mem_filter.mp hC).1)).1 hx)).1 rfl
    have h := congrArg (fun I : Finset J => I.erase i) hab
    simpa [Finset.erase_insert, hno A hA, hno B hB] using h
  have hcard := card_groups_avoiding_ge (U.erase i) F hF (by omega : 0 < q - 1) hs
  have hcardEq : allowed.card = reduced.card := by rw [hImage, Finset.card_image_of_injOn hInj]
  rw [hcardEq]
  have hcoef : (all.card : ℝ) * q ≤ 2 * (U.card : ℝ) * reduced.card := by
    have hMul := Nat.choose_mul (n := U.card) (k := q) (s := 1) (by omega)
    rw [Nat.choose_one_right, Nat.choose_one_right, ← Finset.card_powersetCard, ← Finset.card_erase_of_mem hi,
      ← Finset.card_powersetCard] at hMul
    have hR : all.card * q ≤ 2 * U.card * reduced.card :=
      hMul.le.trans (Nat.mul_le_mul_left _ hcard) |>.trans_eq (by ring)
    exact_mod_cast hR
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hallpos : (0 : ℝ) < all.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.powersetCard_nonempty.mpr hqU)
  have hredpos : (0 : ℝ) < reduced.card := by
    have hn : 0 < (U.erase i).card.choose (q - 1) := Nat.choose_pos (by
      rw [Finset.card_erase_of_mem hi]; omega)
    rw [Finset.card_powersetCard] at hcard
    change (U.erase i).card.choose (q - 1) ≤ 2 * reduced.card at hcard
    exact_mod_cast (show 0 < reduced.card by omega)
  have hsum : ∑ I ∈ allowed, f I ≤ ∑ I ∈ all, f I :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun I _ _ => hf I)
  have hnonneg : 0 ≤ ∑ I ∈ all, f I := Finset.sum_nonneg fun I _ => hf I
  calc
    _ ≤ (∑ I ∈ all, f I) / reduced.card := div_le_div_of_nonneg_right hsum hredpos.le
    _ = ((all.card : ℝ) / reduced.card) * ((∑ I ∈ all, f I) / all.card) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_div_iff₀ hredpos hqpos).mpr hcoef)
      (div_nonneg hnonneg hallpos.le)

end LocallyRamsey
