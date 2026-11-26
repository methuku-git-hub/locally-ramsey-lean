module

public import LocallyRamsey.Lower.GroupIncidence
public import LocallyRamsey.Lower.ListExtraction
public import Mathlib.Logic.Equiv.Fintype

public section

open scoped BigOperators

namespace LocallyRamsey

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A permutation can send two disjoint blocks to two other disjoint
blocks of the corresponding orders. -/
theorem exists_perm_map_disjoint_blocks (A B C D : Finset I)
    (hAB : Disjoint A B) (hCD : Disjoint C D)
    (hAC : A.card = C.card) (hBD : B.card = D.card) :
    ∃ τ : Equiv.Perm I, A.map τ.toEmbedding = C ∧ B.map τ.toEmbedding = D := by
  classical
  let e₁ : ↥A ≃ ↥C := Fintype.equivOfCardEq (by simpa using hAC)
  let e₂ : ↥B ≃ ↥D := Fintype.equivOfCardEq (by simpa using hBD)
  let e : ↥(A ∪ B) ≃ ↥(C ∪ D) :=
    (Equiv.Finset.union A B hAB).symm.trans
      ((Equiv.sumCongr e₁ e₂).trans (Equiv.Finset.union C D hCD))
  let τ : Equiv.Perm I := e.extendSubtype
  have hl (x : ↥A) : τ x.val = (e₁ x).val := by
    rw [show τ x.val = (e ⟨x.val, Finset.mem_union_left _ x.property⟩).val from
      e.extendSubtype_apply_of_mem _ (Finset.mem_union_left _ x.property)]
    simp [e, Equiv.Finset.union_symm_left, x.property]
  have hr (x : ↥B) : τ x.val = (e₂ x).val := by
    rw [show τ x.val = (e ⟨x.val, Finset.mem_union_right _ x.property⟩).val from
      e.extendSubtype_apply_of_mem _ (Finset.mem_union_right _ x.property)]
    simp [e, Equiv.Finset.union_symm_right, x.property]
  refine ⟨τ, ?_, ?_⟩
  · ext z
    constructor
    · rintro hz
      obtain ⟨x, hxA, rfl⟩ := Finset.mem_map.mp hz
      simpa only [Equiv.toEmbedding_apply, hl ⟨x, hxA⟩] using (e₁ ⟨x, hxA⟩).property
    · intro hz
      let x := e₁.symm ⟨z, hz⟩
      exact Finset.mem_map.mpr ⟨x.val, x.property, (hl x).trans (congrArg Subtype.val
        (e₁.apply_symm_apply ⟨z, hz⟩))⟩
  · ext z
    constructor
    · rintro hz
      obtain ⟨x, hxB, rfl⟩ := Finset.mem_map.mp hz
      simpa only [Equiv.toEmbedding_apply, hr ⟨x, hxB⟩] using (e₂ ⟨x, hxB⟩).property
    · intro hz
      let x := e₂.symm ⟨z, hz⟩
      exact Finset.mem_map.mpr ⟨x.val, x.property, (hr x).trans (congrArg Subtype.val
        (e₂.apply_symm_apply ⟨z, hz⟩))⟩

/-- Images of two disjoint fixed blocks by a uniform permutation. All
ordered disjoint pairs of the corresponding sizes have equal probability. -/
theorem uniform_perm_block_pair_event_eq (A B C D C' D' : Finset I)
    (hCD : Disjoint C D) (hCD' : Disjoint C' D')
    (hC : C.card = C'.card) (hD : D.card = D'.card) :
    (FiniteLaw.uniform (Equiv.Perm I)).event
      (fun p => A.map p.toEmbedding = C ∧ B.map p.toEmbedding = D) =
      (FiniteLaw.uniform (Equiv.Perm I)).event
        (fun p => A.map p.toEmbedding = C' ∧ B.map p.toEmbedding = D') := by
  classical
  obtain ⟨τ, hτC, hτD⟩ := exists_perm_map_disjoint_blocks C D C' D' hCD hCD' hC hD
  let e : Equiv.Perm I ≃ Equiv.Perm I := {
    toFun := fun p => p.trans τ
    invFun := fun p => p.trans τ.symm
    left_inv := fun p => by ext x; simp
    right_inv := fun p => by ext x; simp }
  rw [← FiniteLaw.mean_indicator, ← FiniteLaw.mean_indicator]
  simp only [FiniteLaw.mean, FiniteLaw.uniform]
  apply Fintype.sum_equiv e
  intro p
  have hmap (Q S T : Finset I) (hST : S.map τ.toEmbedding = T) :
      Q.map p.toEmbedding = S ↔ Q.map (e p).toEmbedding = T := by
    change Q.map p.toEmbedding = S ↔ Q.map (p.trans τ).toEmbedding = T
    have hemb : (p.trans τ).toEmbedding = p.toEmbedding.trans τ.toEmbedding := rfl
    rw [← hST, hemb, ← Finset.map_map]
    exact (Finset.map_injective τ.toEmbedding).eq_iff.symm
  have hab := and_congr (hmap A C C' hτC) (hmap B D D' hτD)
  by_cases hp : A.map p.toEmbedding = C ∧ B.map p.toEmbedding = D
  · simp [hp, hab.mp hp]
  · have hp' := mt hab.mpr hp
    simp [hp, hp']

/-- Each single block image is uniform among sets of the same size. -/
theorem uniform_perm_block_event_eq (A C D : Finset I) (h : C.card = D.card) :
    (FiniteLaw.uniform (Equiv.Perm I)).event (fun p => A.map p.toEmbedding = C) =
      (FiniteLaw.uniform (Equiv.Perm I)).event (fun p => A.map p.toEmbedding = D) := by
  simpa using uniform_perm_block_pair_event_eq A ∅ C ∅ D ∅ (by simp) (by simp) h rfl

/-- A conditional arithmetic mean bound becomes a bound on an average
weighted by a function of the first observation. The fibres with any
fixed first observation have equal mass over the allowed second values. -/
theorem mean_weighted_uniform_companion_le {Ω A B : Type*} [Fintype Ω]
    [DecidableEq A] [DecidableEq B] (μ : FiniteLaw Ω) (first : Ω → A) (second : Ω → B)
    (M : Finset A) (N : A → Finset B)
    (hfirst : ∀ ω, first ω ∈ M) (hsecond : ∀ ω, second ω ∈ N (first ω))
    (hequal : ∀ a ∈ M, ∀ b ∈ N a, ∀ b' ∈ N a,
      μ.event (fun ω => first ω = a ∧ second ω = b) =
        μ.event (fun ω => first ω = a ∧ second ω = b'))
    (f : A → ℝ) (g : B → ℝ) {K : ℝ} (hf : ∀ a ∈ M, 0 ≤ f a)
    (hg : ∀ a ∈ M, (∑ b ∈ N a, g b) ≤ K * (N a).card) :
    μ.mean (fun ω => f (first ω) * g (second ω)) ≤ K * μ.mean (fun ω => f (first ω)) := by
  classical
  let P (a : A) (b : B) (ω : Ω) := first ω = a ∧ second ω = b
  have expand (u : A → B → ℝ) : μ.mean (fun ω => u (first ω) (second ω)) =
      ∑ a ∈ M, ∑ b ∈ N a, u a b * μ.event (P a b) := by
    have hsum (ω : Ω) : u (first ω) (second ω) =
        ∑ a ∈ M, ∑ b ∈ N a, u a b * (if P a b ω then 1 else 0) := by
      have htt (a : A) (b : B) :
          u a b * (if P a b ω then 1 else 0) =
          if first ω = a then (if second ω = b then u a b else 0) else 0 := by
        by_cases ha : first ω = a <;> by_cases hb : second ω = b <;> simp [P, ha, hb]
      simp only [htt]
      symm
      rw [Finset.sum_eq_single (first ω)]
      · simp only [if_true]
        rw [Finset.sum_eq_single (second ω)]
        · simp only [if_true]
        · intro j _ hj
          rw [if_neg (Ne.symm hj)]
        · exact fun h => (h (hsecond ω)).elim
      · intro a ha hne
        simp only [if_neg (Ne.symm hne), Finset.sum_const_zero]
      · exact fun h => (h (hfirst ω)).elim
    calc
      _ = μ.mean (fun ω => ∑ a ∈ M, ∑ b ∈ N a, u a b * (if P a b ω then 1 else 0)) :=
        congrArg μ.mean (funext hsum)
      _ = _ := by
        rw [μ.mean_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [μ.mean_sum]
        exact Finset.sum_congr rfl (fun b _ => by rw [μ.mean_mul_const, μ.mean_indicator])
  have hrow (a : A) (ha : a ∈ M) :
      (∑ b ∈ N a, (f a * g b) * μ.event (P a b)) ≤
        ∑ b ∈ N a, (K * f a) * μ.event (P a b) := by
    by_cases hn : (N a).Nonempty
    · obtain ⟨b₀, hb₀⟩ := hn
      let p := μ.event (P a b₀)
      have hp : 0 ≤ p := μ.event_nonneg _
      have hp' (b : B) (hb : b ∈ N a) : μ.event (P a b) = p := hequal a ha b hb b₀ hb₀
      have heLeft : (∑ b ∈ N a, (f a * g b) * μ.event (P a b)) =
          ∑ b ∈ N a, (f a * g b) * p :=
        Finset.sum_congr rfl (fun b hb => by rw [hp' b hb])
      have heRight : (∑ b ∈ N a, (K * f a) * μ.event (P a b)) =
          ∑ _b ∈ N a, (K * f a) * p :=
        Finset.sum_congr rfl (fun b hb => by rw [hp' b hb])
      rw [heLeft, heRight]
      have heL : (∑ b ∈ N a, f a * g b * p) = f a * (∑ b ∈ N a, g b) * p := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [heL]
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hg a ha) (hf a ha)) hp
      nlinarith only [hbound]
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  rw [← μ.mean_mul_const, expand (fun a b => f a * g b), expand (fun a _ => K * f a)]
  exact Finset.sum_le_sum hrow

/-- Companion-block bound after a uniform permutation. For fixed disjoint
blocks, the second image is uniform among the sets disjoint from the first.
The factor depending on the first image is arbitrary and nonnegative. -/
theorem mean_perm_disjoint_companion_le (A B : Finset I) (hAB : Disjoint A B)
    (f g : Finset I → ℝ) {K : ℝ}
    (hf : ∀ C, C.card = A.card → 0 ≤ f C)
    (hg : ∀ C, C.card = A.card →
      let allowed := ((Finset.univ : Finset I).powersetCard B.card).filter (fun D => Disjoint C D)
      (∑ D ∈ allowed, g D) ≤ K * allowed.card) :
    (FiniteLaw.uniform (Equiv.Perm I)).mean
        (fun p => f (A.map p.toEmbedding) * g (B.map p.toEmbedding)) ≤
      K * (FiniteLaw.uniform (Equiv.Perm I)).mean (fun p => f (A.map p.toEmbedding)) := by
  classical
  let M := (Finset.univ : Finset I).powersetCard A.card
  let N (C : Finset I) := ((Finset.univ : Finset I).powersetCard B.card).filter (fun D => Disjoint C D)
  refine mean_weighted_uniform_companion_le (FiniteLaw.uniform _) (fun p : Equiv.Perm I => A.map p.toEmbedding)
    (fun p => B.map p.toEmbedding) M N (fun p => ?_) (fun p => ?_) ?_ f g
    (fun C hC => hf C (Finset.mem_powersetCard.mp hC).2)
    (fun C hC => hg C (Finset.mem_powersetCard.mp hC).2)
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_map _⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_map _⟩,
      ?_⟩
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y, hyA, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨z, hzB, hz⟩ := Finset.mem_map.mp hy
    have heq := p.injective hz
    exact Finset.disjoint_left.mp hAB (heq ▸ hyA : z ∈ A) hzB
  · intro C _ D hD D' hD'
    obtain ⟨hsize, hdisj⟩ := Finset.mem_filter.mp hD
    obtain ⟨hsize', hdisj'⟩ := Finset.mem_filter.mp hD'
    exact uniform_perm_block_pair_event_eq A B C D C D' hdisj hdisj' rfl
      ((Finset.mem_powersetCard.mp hsize).2.trans (Finset.mem_powersetCard.mp hsize').2.symm)

/-- Averaging a function of a block image under uniform permutation gives
the arithmetic mean over all sets of the block's size. -/
theorem mean_uniform_perm_block (A : Finset I) (f : Finset I → ℝ) :
    (FiniteLaw.uniform (Equiv.Perm I)).mean (fun p => f (A.map p.toEmbedding)) =
      (∑ T ∈ (Finset.univ : Finset I).powersetCard A.card, f T) /
        ((Finset.univ : Finset I).powersetCard A.card).card := by
  classical
  let μ := FiniteLaw.uniform (Equiv.Perm I)
  let Y (p : Equiv.Perm I) := A.map p.toEmbedding
  let N := (Finset.univ : Finset I).powersetCard A.card
  let c := μ.event (fun p => Y p = A)
  have hmem (p : Equiv.Perm I) : Y p ∈ N :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_map _⟩
  have hc (T : Finset I) (ht : T ∈ N) : μ.event (fun p => Y p = T) = c :=
    uniform_perm_block_event_eq A T A (Finset.mem_powersetCard.mp ht).2
  have hexp (g : Finset I → ℝ) : μ.mean (fun p => g (Y p)) =
      (∑ T ∈ N, g T) * c := by
    have hsplit (p : Equiv.Perm I) :
        g (Y p) = ∑ T ∈ N, g T * (if Y p = T then 1 else 0) := by
      symm
      rw [Finset.sum_eq_single (Y p)]
      · simp
      · intro T hT hne
        simp [Ne.symm hne]
      · exact fun h => (h (hmem p)).elim
    rw [funext hsplit, μ.mean_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun T hT => ?_)
    rw [μ.mean_mul_const, μ.mean_indicator, hc T hT]
  have hN : (N.card : ℝ) * c = 1 := by
    simpa [μ.mean_const] using (hexp (fun _ => 1)).symm
  change μ.mean (fun p => f (Y p)) = (∑ T ∈ N, f T) / N.card
  rw [hexp]
  have hN0 : (N.card : ℝ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hN
    norm_num at hN
  apply (eq_div_iff hN0).mpr
  calc
    _ = (∑ T ∈ N, f T) * ((N.card : ℝ) * c) := by ring
    _ = _ := by rw [hN, mul_one]

end LocallyRamsey
