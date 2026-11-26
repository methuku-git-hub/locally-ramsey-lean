module

public import LocallyRamsey.Threshold
public import LocallyRamsey.Lower.Recording
public import Mathlib.Data.Nat.Choose.Bounds

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- The unordered cliques of a given order in a finite vertex set. -/
noncomputable def cliquesIn (G : SimpleGraph V) (A : Finset V) (r : ℕ) : Finset (Finset V) := by
  classical
  exact (A.powersetCard r).filter fun K => G.IsClique (K : Set V)

theorem mem_cliquesIn {G : SimpleGraph V} {A K : Finset V} {r : ℕ} :
    K ∈ cliquesIn G A r ↔ K ⊆ A ∧ K.card = r ∧ G.IsClique (K : Set V) := by
  classical
  simp [cliquesIn, and_assoc]

/-- Double counting incidences between an (M)-set and an (r)-clique. -/
theorem choose_le_cliquesIn_mul_choose {G : SimpleGraph V} {A : Finset V} {M r : ℕ}
    (hG : IsLocallyRamsey G M r) (hrM : r ≤ M) (hMA : M ≤ A.card) :
    A.card.choose r ≤ (cliquesIn G A r).card * M.choose r := by
  classical
  let cover := fun K : Finset V => (A.powersetCard M).filter (K ⊆ ·)
  have hsub : A.powersetCard M ⊆ (cliquesIn G A r).biUnion cover := by
    intro X hX
    obtain ⟨hXA, hXcard⟩ := Finset.mem_powersetCard.mp hX
    obtain ⟨K, hKX, hK⟩ := (hG X hXcard).1
    exact Finset.mem_biUnion.mpr ⟨K,
      mem_cliquesIn.mpr ⟨hKX.trans hXA, hK.card_eq, hK.isClique⟩,
      Finset.mem_filter.mpr ⟨hX, hKX⟩⟩
  have h := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [Finset.card_powersetCard] at h
  have hbound : A.card.choose M ≤ (cliquesIn G A r).card * (A.card - r).choose (M - r) := by
    refine h.trans_eq ?_
    calc
      _ = ∑ _K ∈ cliquesIn G A r, (A.card - r).choose (M - r) := by
        refine Finset.sum_congr rfl (fun K hK => ?_)
        obtain ⟨hKA, hKcard, _⟩ := mem_cliquesIn.mp hK
        dsimp [cover]
        rw [Finset.card_filter_powersetCard_subset K A M hKA (hKcard ▸ hrM), hKcard]
      _ = _ := by simp [Finset.sum_const]
  have hpos : 0 < (A.card - r).choose (M - r) := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hpos
  rw [← Nat.choose_mul hrM, mul_assoc, mul_comm (M.choose r), ← mul_assoc]
  exact Nat.mul_le_mul_right _ hbound

/-- The lower bound used in the extraction of large cliques and sets of
small maximum degree, expressed as a count of unordered cliques. -/
theorem cliquesIn_lower {G : SimpleGraph V} {A : Finset V} {M r : ℕ}
    (hG : IsLocallyRamsey G M r) (hr : 2 ≤ r) (hrM : r ≤ M)
    (hMA : M ≤ A.card) (hlarge : 2 * r ≤ A.card) (hM : M ≤ r ^ 6) :
    ((A.card : ℝ) / (r : ℝ) ^ 7) ^ r ≤ (cliquesIn G A r).card := by
  have hr0 : (0 : ℝ) < r := by positivity
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hrM' : (M : ℝ) ≤ (r : ℝ) ^ 6 := by exact_mod_cast hM
  have hhalf : (A.card : ℝ) / 2 ≤ (A.card + 1 - r : ℕ) := by
    have hcast : (↑(A.card + 1 - r) : ℝ) = (A.card : ℝ) + 1 - r := by
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    rw [hcast]
    have hlarge' : 2 * (r : ℝ) ≤ A.card := by exact_mod_cast hlarge
    linarith
  have hchoose1 := Nat.pow_le_choose (α := ℝ) r A.card
  have hchoose2 := Nat.choose_le_pow_div (α := ℝ) r M
  have hcount : (A.card.choose r : ℝ) ≤
      (cliquesIn G A r).card * (M.choose r : ℝ) := by
    exact_mod_cast choose_le_cliquesIn_mul_choose hG hrM hMA
  have hf : (0 : ℝ) < (r.factorial : ℝ) := by positivity
  have hhalfPow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ A.card / 2) hhalf r
  have h := (div_le_div_of_nonneg_right hhalfPow hf.le).trans
    (hchoose1.trans (hcount.trans (mul_le_mul_of_nonneg_left hchoose2 (by positivity))))
  rw [← mul_div_assoc] at h
  have hp := (div_le_div_iff_of_pos_right hf).mp h
  have hbase : (A.card : ℝ) / (r : ℝ) ^ 7 ≤ A.card / (2 * (M : ℝ)) := by
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    rw [pow_succ]
    nlinarith only [mul_le_mul_of_nonneg_left hrM' (show (0 : ℝ) ≤ 2 by norm_num),
      mul_le_mul_of_nonneg_left hr2 (show (0 : ℝ) ≤ (r : ℝ) ^ 6 by positivity)]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (A.card : ℝ) / (r : ℝ) ^ 7) hbase r
  rw [← div_div, div_pow ((A.card : ℝ) / 2)] at hpow
  exact hpow.trans ((div_le_iff₀ (by positivity : 0 < (M : ℝ) ^ r)).mpr hp)

/-- Unordered common neighbours inside the current set. -/
noncomputable def commonNeighborsIn (G : SimpleGraph V) (A K : Finset V) : Finset V := by
  classical
  exact A.filter fun y => ∀ x ∈ K, G.Adj x y

omit [DecidableEq V] in
theorem mem_commonNeighborsIn {G : SimpleGraph V} {A K : Finset V} {y : V} :
    y ∈ commonNeighborsIn G A K ↔ y ∈ A ∧ ∀ x ∈ K, G.Adj x y := by
  classical
  simp [commonNeighborsIn]

/-- Each clique of order (r) can be described by its first (g) vertices
and an ((r-g))-set in their common neighbourhood. Here any selection of
the first (g) vertices suffices for the counting bound. -/
theorem cliquesIn_upper_common {G : SimpleGraph V} {A : Finset V} {r g : ℕ} {B : ℝ}
    (hgr : g ≤ r) (hB : 0 ≤ B)
    (hcommon : ∀ K ∈ cliquesIn G A g, ((commonNeighborsIn G A K).card : ℝ) ≤ B) :
    ((cliquesIn G A r).card : ℝ) ≤ (A.card : ℝ) ^ g * B ^ (r - g) := by
  classical
  let desc := fun K : Finset V => ((commonNeighborsIn G A K).powersetCard (r - g)).image (K ∪ ·)
  have hsub : cliquesIn G A r ⊆ (cliquesIn G A g).biUnion desc := by
    intro Q hQ
    obtain ⟨hQA, hQcard, hQc⟩ := mem_cliquesIn.mp hQ
    obtain ⟨K, hKQ, hKcard⟩ := Finset.exists_subset_card_eq (hQcard ▸ hgr)
    refine Finset.mem_biUnion.mpr ⟨K,
      mem_cliquesIn.mpr ⟨hKQ.trans hQA, hKcard, fun x hx y hy hxy => hQc (hKQ hx) (hKQ hy) hxy⟩,
      Finset.mem_image.mpr ⟨Q \ K, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩⟩
    · intro y hy
      obtain ⟨hyQ, hyK⟩ := Finset.mem_sdiff.mp hy
      exact mem_commonNeighborsIn.mpr ⟨hQA hyQ, fun x hx =>
        hQc (hKQ hx) hyQ (fun heq => hyK (heq ▸ hx))⟩
    · rw [Finset.card_sdiff_of_subset hKQ, hQcard, hKcard]
    · rw [Finset.union_comm, Finset.sdiff_union_of_subset hKQ]
  have hall (K : Finset V) (hK : K ∈ cliquesIn G A g) :
      ((desc K).card : ℝ) ≤ B ^ (r - g) := by
    have hcard := (Finset.card_image_le (f := (K ∪ ·))).trans (le_of_eq
      (Finset.card_powersetCard (r - g) (commonNeighborsIn G A K)))
    have hnat := hcard.trans (Nat.choose_le_pow _ _)
    exact (show ((desc K).card : ℝ) ≤ ((commonNeighborsIn G A K).card : ℝ) ^ (r - g)
      by exact_mod_cast hnat).trans (pow_le_pow_left₀ (by positivity) (hcommon K hK) _)
  have hnum : ((cliquesIn G A g).card : ℝ) ≤ (A.card : ℝ) ^ g := by
    have h := Finset.card_filter_le (s := A.powersetCard g) (fun K => G.IsClique (K : Set V))
    rw [Finset.card_powersetCard] at h
    exact_mod_cast h.trans (Nat.choose_le_pow _ _)
  have h := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ K ∈ cliquesIn G A g, ((desc K).card : ℝ) := by exact_mod_cast h
    _ ≤ ∑ _K ∈ cliquesIn G A g, B ^ (r - g) := Finset.sum_le_sum hall
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hnum (pow_nonneg hB _)

/-- The first (g) vertices of some (r)-clique may be chosen with a
large common neighbourhood, by comparing the two clique counts. -/
theorem exists_clique_with_commonNeighbors {G : SimpleGraph V} {A : Finset V} {M r g : ℕ}
    (hG : IsLocallyRamsey G M r) (hr : 2 ≤ r) (hrM : r ≤ M)
    (hMA : M ≤ A.card) (hlarge : 2 * r ≤ A.card) (hM : M ≤ r ^ 6)
    (hgr : g ≤ r) (hg : 7 * r < 16 * (r - g)) :
    ∃ K ∈ cliquesIn G A g, (A.card : ℝ) / (r : ℝ) ^ 16 ≤ (commonNeighborsIn G A K).card := by
  have hr2 : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hA : 0 < (A.card : ℝ) := by exact_mod_cast (show 0 < A.card by omega)
  by_contra! h
  have hlo := cliquesIn_lower hG hr hrM hMA hlarge hM
  have hhi := cliquesIn_upper_common hgr (by positivity) (fun K hK => (h K hK).le)
  have hden := pow_lt_pow_right₀ hr2 hg
  have hlt : (A.card : ℝ) ^ g * ((A.card : ℝ) / (r : ℝ) ^ 16) ^ (r - g) <
      ((A.card : ℝ) / (r : ℝ) ^ 7) ^ r := by
    rw [div_pow, div_pow, ← pow_mul, ← pow_mul, ← mul_div_assoc, ← pow_add,
      Nat.add_sub_of_le hgr]
    exact div_lt_div_of_pos_left (pow_pos hA _) (by positivity) hden
  exact (not_lt_of_ge (hlo.trans hhi)) hlt

/-- Iterate the common-neighbour extraction. At each step the (g) chosen
vertices extend the clique and the remaining set loses at most the specified
factor. -/
theorem exists_clique_from_repeated_extraction {G : SimpleGraph V} {A : Finset V} {M r g l : ℕ}
    (hG : IsLocallyRamsey G M r) (hr : 2 ≤ r) (hrM : r ≤ M) (hM : M ≤ r ^ 6)
    (hgr : g ≤ r) (hg : 7 * r < 16 * (r - g))
    (hsize : ((max M (2 * r) : ℕ) : ℝ) * ((r : ℝ) ^ 16) ^ l ≤ A.card) :
    ∃ K, K ∈ cliquesIn G A (g * l) := by
  classical
  have hbase : 1 ≤ (r : ℝ) ^ 16 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ r by omega))
  induction l generalizing A with
  | zero => exact ⟨∅, mem_cliquesIn.mpr ⟨by simp, by simp, by simp⟩⟩
  | succ l ih =>
    have hmax : (max M (2 * r) : ℕ) ≤ A.card := by
      have hp := mul_le_mul_of_nonneg_left (one_le_pow₀ hbase (n := l + 1))
        (show (0 : ℝ) ≤ (max M (2 * r) : ℕ) by positivity)
      rw [mul_one] at hp
      exact_mod_cast hp.trans hsize
    obtain ⟨K, hK, hN⟩ := exists_clique_with_commonNeighbors hG hr hrM
      ((le_max_left _ _).trans hmax) ((le_max_right _ _).trans hmax) hM hgr hg
    let N := commonNeighborsIn G A K
    have hNsize : ((max M (2 * r) : ℕ) : ℝ) * ((r : ℝ) ^ 16) ^ l ≤ N.card := by
      refine (le_div_iff₀ (by positivity : 0 < (r : ℝ) ^ 16)).mpr ?_ |>.trans hN
      rw [mul_assoc, ← pow_succ]
      exact hsize
    obtain ⟨J, hJ⟩ := ih hNsize
    obtain ⟨hJA, hJcard, hJcl⟩ := mem_cliquesIn.mp hJ
    obtain ⟨hKA, hKcard, hKcl⟩ := mem_cliquesIn.mp hK
    have hNJ (z : V) (hz : z ∈ J) : z ∈ A ∧ ∀ y ∈ K, G.Adj y z :=
      mem_commonNeighborsIn.mp (hJA hz)
    have hdisj : Disjoint K J := Finset.disjoint_left.mpr fun y hyK hyJ =>
      G.irrefl ((hNJ y hyJ).2 y hyK)
    refine ⟨K ∪ J, mem_cliquesIn.mpr ⟨Finset.union_subset hKA (fun z hz => (hNJ z hz).1),
      ?_, ?_⟩⟩
    · rw [Finset.card_union_of_disjoint hdisj, hKcard, hJcard, Nat.mul_succ, add_comm]
    · intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hxK | hxJ <;>
        rcases Finset.mem_union.mp hy with hyK | hyJ
      · exact hKcl hxK hyK hxy
      · exact (hNJ y hyJ).2 x hxK
      · exact ((hNJ x hxJ).2 y hyK).symm
      · exact hJcl hxJ hyJ hxy

/-- Counting cliques whose recorded vertices determine a small remainder. -/
theorem cliquesIn_upper_recorded {G : SimpleGraph V} {A : Finset V} {r g : ℕ} {B : ℝ}
    (Y : Finset V → Finset V) (hB : 0 ≤ B)
    (hrecord : ∀ Q ∈ cliquesIn G A r, ∃ R : Finset V, R ⊆ Q ∧ R.card ≤ g ∧
      Q \ R ⊆ Y R ∧ ((Y R).card : ℝ) ≤ B) :
    ((cliquesIn G A r).card : ℝ) ≤
      ∑ j ∈ Finset.range (g + 1), (A.card : ℝ) ^ j * B ^ (r - j) := by
  classical
  let desc (R : Finset V) :=
    if ((Y R).card : ℝ) ≤ B then ((Y R).powersetCard (r - R.card)).image (R ∪ ·) else ∅
  let bySize (j : ℕ) := (A.powersetCard j).biUnion desc
  have hsub : cliquesIn G A r ⊆ (Finset.range (g + 1)).biUnion bySize := by
    intro Q hQ
    obtain ⟨hQA, hQcard, _⟩ := mem_cliquesIn.mp hQ
    obtain ⟨R, hR, hRcard, hsub, hbound⟩ := hrecord Q hQ
    refine Finset.mem_biUnion.mpr ⟨R.card, Finset.mem_range.mpr (by omega), ?_⟩
    refine Finset.mem_biUnion.mpr ⟨R, Finset.mem_powersetCard.mpr ⟨hR.trans hQA, rfl⟩, ?_⟩
    simp only [desc, ite_eq_left hbound]
    refine Finset.mem_image.mpr ⟨Q \ R, Finset.mem_powersetCard.mpr ⟨hsub, ?_⟩, ?_⟩
    · rw [Finset.card_sdiff_of_subset hR, hQcard]
    · rw [Finset.union_comm, Finset.sdiff_union_of_subset hR]
  have hdesc (j : ℕ) (R : Finset V) (hR : R ∈ A.powersetCard j) :
      ((desc R).card : ℝ) ≤ B ^ (r - j) := by
    have hc := (Finset.mem_powersetCard.mp hR).2
    by_cases h : ((Y R).card : ℝ) ≤ B
    · have hnat := (Finset.card_image_le (f := (R ∪ ·))).trans (le_of_eq
          (Finset.card_powersetCard (r - R.card) (Y R)))
      have hpow := hnat.trans (Nat.choose_le_pow _ _)
      have hh : (((Finset.powersetCard (r - R.card) (Y R)).image (R ∪ ·)).card : ℝ) ≤
          ((Y R).card : ℝ) ^ (r - R.card) := by exact_mod_cast hpow
      simp only [desc, ite_eq_left h, ← hc]
      exact hh.trans (pow_le_pow_left₀ (by positivity) h _)
    · simp only [desc, ite_eq_right h, Finset.card_empty, Nat.cast_zero]
      exact pow_nonneg hB _
  have hsize (j : ℕ) : ((bySize j).card : ℝ) ≤ (A.card : ℝ) ^ j * B ^ (r - j) := by
    have hcard : ((A.powersetCard j).card : ℝ) ≤ (A.card : ℝ) ^ j := by
      rw [Finset.card_powersetCard]
      exact_mod_cast Nat.choose_le_pow A.card j
    calc
      _ ≤ ∑ R ∈ A.powersetCard j, ((desc R).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le : (bySize j).card ≤ _)
      _ ≤ ∑ _R ∈ A.powersetCard j, B ^ (r - j) := Finset.sum_le_sum (hdesc j)
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard (pow_nonneg hB _)
  have h := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  exact (show ((cliquesIn G A r).card : ℝ) ≤
    ∑ j ∈ Finset.range (g + 1), ((bySize j).card : ℝ) by exact_mod_cast h).trans
      (Finset.sum_le_sum fun j _ => hsize j)

end LocallyRamsey
