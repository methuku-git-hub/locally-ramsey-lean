module

public import LocallyRamsey.Lower.IndependentOrder
public import LocallyRamsey.Lower.DeferredDraws

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- Recover a small vertex set retaining an independent set in expectation.
The description names a few vertices by their draw and their position in
that draw, so the draws used to estimate the expected order stay fresh. -/
theorem exists_region_of_common_nonNeighbors (G : SimpleGraph V)
    (μ : FiniteLaw Ω) (P : Ω → Finset V) (W : Finset V) {b l s K r limit : ℕ} (hK : 0 < K)
    (enumerate : Ω → Fin b → V)
    (hEnum : ∀ ω x, x ∈ P ω → ∃ j, enumerate ω j = x)
    (hOrder : ∀ ω, independenceOrder G (P ω) ≤ K)
    (successful : (Fin l → Ω) → Prop) {a : ℝ} (ha : 0 ≤ a)
    (hcount : ((l * b : ℕ) : ℝ) ^ s *
        Real.exp ((l : ℝ) * a - Real.log 2 * (((r : ℝ) - s * K) / K)) <
      (FiniteLaw.product (fun _ : Fin l => μ)).event successful)
    (hwitness : ∀ ω, successful ω → ∃ (Q : Finset V) (f : Fin s → Fin l) (v : Fin s → V),
      Q ⊆ W ∧ Q ⊆ Finset.univ.biUnion (fun i => P (ω i)) ∧ Gᶜ.IsClique (Q : Set V) ∧
      r ≤ Q.card ∧ (∀ j, v j ∈ Q ∧ v j ∈ P (ω (f j))) ∧
      (commonNeighborsIn Gᶜ W (Finset.univ.image v)).card ≤ limit) :
    ∃ S : Finset V, S ⊆ W ∧ S.card ≤ limit ∧
      (K : ℝ) * a ≤ μ.mean (fun ω => (independenceOrder G (S ∩ P ω) : ℝ)) := by
  classical
  let D := Fin s → Fin l × Fin b
  let A (d : D) := Finset.univ.image (fun j => (d j).1)
  let vdesc (d : D) (e : {i // i ∈ A d} → Ω) (j : Fin s) : V :=
    enumerate (e ⟨(d j).1, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩) (d j).2
  let decode (d : D) (e : {i // i ∈ A d} → Ω) :=
    commonNeighborsIn Gᶜ W (Finset.univ.image (vdesc d e))
  let valid (S : Finset V) := S ⊆ W ∧ S.card ≤ limit
  let score (S : Finset V) (ω : Ω) := (independenceOrder G (S ∩ P ω) : ℝ) / K
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hscore (S : Finset V) (ω : Ω) : score S ω ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by positivity) hKr.le, (div_le_one hKr).mpr
      (by exact_mod_cast (independenceOrder_mono Finset.inter_subset_right).trans (hOrder ω))⟩
  have hcount' : (Fintype.card D : ℝ) *
      Real.exp ((l : ℝ) * a - Real.log 2 * (((r : ℝ) - s * K) / K)) <
        (FiniteLaw.product (fun _ : Fin l => μ)).event successful := by
    simpa only [D, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow] using hcount
  have hdecode (ω : Fin l → Ω) (hω : successful ω) :
      ∃ d : D, valid (decode d (fun i => ω i.val)) ∧
        ((r : ℝ) - s * K) / K ≤
          ∑ i : {i // i ∉ A d}, score (decode d (fun j => ω j.val)) (ω i.val) := by
    obtain ⟨Q, f, v, hQW, hQcover, hQcl, hQr, hV, hlimit⟩ := hwitness ω hω
    let d : D := fun j => (f j, Classical.choose (hEnum _ _ (hV j).2))
    let E := (A d).biUnion (fun i => P (ω i))
    let Q' := Q \ E
    let S := decode d (fun i => ω i.val)
    have hVeq (j : Fin s) : vdesc d (fun i => ω i.val) j = v j :=
      Classical.choose_spec (hEnum _ _ (hV j).2)
    have hSeq : S = commonNeighborsIn Gᶜ W (Finset.univ.image v) :=
      congrArg (commonNeighborsIn Gᶜ W) (congrArg (Finset.univ.image ·) (funext hVeq))
    have hQ'S : Q' ⊆ S := by
      rw [hSeq]
      intro x hx
      obtain ⟨hxQ, hxE⟩ := Finset.mem_sdiff.mp hx
      refine mem_commonNeighborsIn.mpr ⟨hQW hxQ, fun y hy => ?_⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact hQcl (hV j).1 hxQ (fun heq => hxE (Finset.mem_biUnion.mpr
        ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, heq ▸ (hV j).2⟩))
    have hQ'card : r ≤ Q'.card + s * K := by
      have hrem : (Q ∩ E).card ≤ s * K := by
        have hSub : Q ∩ E ⊆ (A d).biUnion (fun i => Q ∩ P (ω i)) := by
          intro x hx
          obtain ⟨hxQ, hxE⟩ := Finset.mem_inter.mp hx
          obtain ⟨i, hi, hxP⟩ := Finset.mem_biUnion.mp hxE
          exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hxQ, hxP⟩⟩
        refine ((Finset.card_le_card hSub).trans Finset.card_biUnion_le).trans ?_
        calc
          _ ≤ ∑ _i ∈ A d, K := by
            apply Finset.sum_le_sum
            intro i _
            refine (card_le_independenceOrder Finset.inter_subset_right (Q := Q ∩ P (ω i)) ?_).trans
              (hOrder (ω i))
            exact fun x hx y hy hxy => hQcl (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hy).1 hxy
          _ = (A d).card * K := by simp
          _ ≤ s * K := Nat.mul_le_mul_right K (Finset.card_image_le.trans_eq (by simp))
      have heq : Q'.card + (Q ∩ E).card = Q.card := by
        change (Q \ E).card + (Q ∩ E).card = Q.card
        exact Finset.card_sdiff_add_card_inter _ _
      omega
    have hCover : Q' ⊆ (Finset.univ : Finset {i // i ∉ A d}).biUnion
        (fun i => S ∩ P (ω i.val)) := by
      intro x hx
      obtain ⟨hxQ, hxE⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨i, _, hxP⟩ := Finset.mem_biUnion.mp (hQcover hxQ)
      have hi : i ∉ A d := fun ha => hxE (Finset.mem_biUnion.mpr ⟨i, ha, hxP⟩)
      exact Finset.mem_biUnion.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hQ'S hx, hxP⟩⟩
    have hQ'cl : Gᶜ.IsClique (Q' : Set V) :=
      fun x hx y hy hxy => hQcl (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hy).1 hxy
    have hSum : Q'.card ≤ ∑ i : {i // i ∉ A d}, independenceOrder G (S ∩ P (ω i.val)) :=
      (card_le_independenceOrder (Finset.Subset.refl Q') hQ'cl).trans
        (independenceOrder_le_sum_cover Finset.univ _ hCover)
    refine ⟨d, ⟨fun x hx => (mem_commonNeighborsIn.mp hx).1, ?_⟩, ?_⟩
    · change S.card ≤ limit
      rwa [hSeq]
    change _ ≤ ∑ i : {i // i ∉ A d}, (independenceOrder G (S ∩ P (ω i.val)) : ℝ) / K
    rw [← Finset.sum_div, div_le_div_iff_of_pos_right hKr]
    have hc1 : (r : ℝ) ≤ (Q'.card : ℝ) + (s : ℝ) * K := by exact_mod_cast hQ'card
    have hc2 : (Q'.card : ℝ) ≤ ∑ i : {i // i ∉ A d}, (independenceOrder G (S ∩ P (ω i.val)) : ℝ) := by
      exact_mod_cast hSum
    linarith only [hc1, hc2]

  obtain ⟨S, hS, hmean⟩ := FiniteLaw.exists_test_of_deferred_reconstruction μ l A decode valid score
    hscore successful ha hcount' hdecode
  refine ⟨S, hS.1, hS.2, ?_⟩
  have hEq : score S = fun ω => (K : ℝ)⁻¹ * independenceOrder G (S ∩ P ω) := by
    funext ω
    simp only [score, div_eq_inv_mul]
  rw [hEq, μ.mean_mul_const, inv_mul_eq_div] at hmean
  simpa only [mul_comm] using (le_div_iff₀ hKr).mp hmean

/-- The list may be fixed before choosing the law of the random union.
Otherwise choose a failing law for each list, then run the joint experiment
with these laws and apply the reconstruction estimate conditionally. -/
theorem exists_list_recovering_against_all_laws {L : Type*} [Fintype L]
    (G : SimpleGraph V) (μL : FiniteLaw L) (P : L → Ω → Finset V) (W : L → Finset V)
    {b l s K r limit : ℕ} (hK : 0 < K) {a : ℝ} (ha : 0 ≤ a)
    (enumerate : L → Ω → Fin b → V)
    (hEnum : ∀ L ω x, x ∈ P L ω → ∃ j, enumerate L ω j = x)
    (hOrder : ∀ L ω, independenceOrder G (P L ω) ≤ K)
    (allowed : L → FiniteLaw Ω → Prop)
    (hjoint : ∀ ν : L → FiniteLaw Ω, (∀ L, allowed L (ν L)) →
      ∃ successful : L → (Fin l → Ω) → Prop,
        ((l * b : ℕ) : ℝ) ^ s * Real.exp ((l : ℝ) * a - Real.log 2 * (((r : ℝ) - s * K) / K)) <
          (μL.staged (fun L => FiniteLaw.product (fun _ : Fin l => ν L))).event
            (fun x => successful x.1 x.2) ∧
        ∀ L ω, successful L ω → ∃ (Q : Finset V) (f : Fin s → Fin l) (v : Fin s → V),
          Q ⊆ W L ∧ Q ⊆ Finset.univ.biUnion (fun i => P L (ω i)) ∧ Gᶜ.IsClique (Q : Set V) ∧
          r ≤ Q.card ∧ (∀ j, v j ∈ Q ∧ v j ∈ P L (ω (f j))) ∧
          (commonNeighborsIn Gᶜ (W L) (Finset.univ.image v)).card ≤ limit) :
    ∃ L : L, ∀ ν : FiniteLaw Ω, allowed L ν →
      ∃ S : Finset V, S ⊆ W L ∧ S.card ≤ limit ∧
        (K : ℝ) * a ≤ ν.mean (fun ω => (independenceOrder G (S ∩ P L ω) : ℝ)) := by
  classical
  by_contra! hbad
  choose ν hν hFailure using hbad
  obtain ⟨successful, hcount, hwitness⟩ := hjoint ν hν
  let error := ((l * b : ℕ) : ℝ) ^ s * Real.exp ((l : ℝ) * a - Real.log 2 * (((r : ℝ) - s * K) / K))
  have hsmall (L : L) : (FiniteLaw.product (fun _ : Fin l => ν L)).event (successful L) ≤ error := by
    by_contra! hLarge
    obtain ⟨S, hSW, hScard, hMean⟩ := exists_region_of_common_nonNeighbors G (ν L) (P L) (W L)
      hK (enumerate L) (hEnum L) (hOrder L) (successful L) ha hLarge (hwitness L)
    exact (not_lt_of_ge hMean) (hFailure L S hSW hScard)
  rw [FiniteLaw.staged_event] at hcount
  exact (not_lt_of_ge ((μL.mean_mono hsmall).trans_eq (μL.mean_const error))) hcount

end LocallyRamsey
