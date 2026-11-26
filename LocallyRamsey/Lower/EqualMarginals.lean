module

public import LocallyRamsey.Lower.IndependentOrder
public import LocallyRamsey.IndependentBlocks
public import LocallyRamsey.Packing
public import Mathlib.Combinatorics.Pigeonhole

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

private theorem event_true_coin {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    (FiniteLaw.bernoulli p hp₀ hp₁).event (fun b => b = true) = p := by
  let μ := FiniteLaw.bernoulli p hp₀ hp₁
  change μ.event _ = _
  rw [← μ.mean_indicator]
  simp [FiniteLaw.mean, μ, FiniteLaw.bernoulli_prob_true]

/-- On a set of comparable marginals, thin each sampled vertex to the
same inclusion probability. Every fixed union of cliques retains at least
the same fraction of its expected maximum independent-set order. -/
theorem exists_equal_marginal_sample (G : SimpleGraph V) (μ : FiniteLaw Ω) (A : Ω → Finset V)
    (W : Finset V) {p β : ℝ} (hp : 0 < p)
    (hmin : ∀ x ∈ W, p ≤ μ.event (fun ω => x ∈ A ω))
    (hfrac : ∀ x ∈ W, β * μ.event (fun ω => x ∈ A ω) ≤ p) :
    ∃ (ν : FiniteLaw (Ω × (V → Bool))) (S : Ω × (V → Bool) → Finset V),
      (∀ z, S z ⊆ A z.1 ∩ W) ∧
      (∀ x ∈ W, ν.event (fun z => x ∈ S z) = p) ∧
      ∀ P : Finset V, P ⊆ W →
        β * μ.mean (fun ω => (independenceOrder G (A ω ∩ P) : ℝ)) ≤
          ν.mean (fun z => (independenceOrder G (S z ∩ P) : ℝ)) := by
  classical
  let t (x : V) := if x ∈ W then p / μ.event (fun ω => x ∈ A ω) else 0
  have ht₀ (x : V) : 0 ≤ t x := by
    by_cases hx : x ∈ W
    · simp only [t, hx, ite_true]
      exact div_nonneg hp.le ((hmin x hx).trans' hp.le)
    · simp [t, hx]
  have ht₁ (x : V) : t x ≤ 1 := by
    by_cases hx : x ∈ W
    · simp only [t, hx, ite_true]
      exact (div_le_one (hp.trans_le (hmin x hx))).mpr (hmin x hx)
    · simp [t, hx]
  let coins (x : V) := FiniteLaw.bernoulli (t x) (ht₀ x) (ht₁ x)
  let τ := FiniteLaw.product coins
  let ν := μ.staged (fun _ => τ)
  let keep (z : Ω × (V → Bool)) := (A z.1 ∩ W).filter (fun x => z.2 x = true)
  have hcoin (x : V) : τ.event (fun f => f x = true) = t x :=
    (FiniteLaw.event_coordinate coins x (fun b => b = true)).trans (event_true_coin _ _)
  refine ⟨ν, keep, fun z => Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx
    change (μ.staged fun _ => τ).event (fun z => x ∈ keep z) = p
    rw [μ.staged_event]
    have hevent (ω : Ω) : τ.event (fun f => x ∈ keep (ω, f)) =
        t x * (if x ∈ A ω then 1 else 0) := by
      by_cases ha : x ∈ A ω
      · simpa [keep, hx, ha] using hcoin x
      · rw [← τ.mean_indicator]
        simp [keep, ha, FiniteLaw.mean_const]
    simp_rw [hevent]
    rw [μ.mean_mul_const, μ.mean_indicator]
    simp only [t, hx, ite_true]
    field_simp [(hp.trans_le (hmin x hx)).ne']
  · intro P hPW
    change _ ≤ (μ.staged fun _ => τ).mean _
    rw [μ.staged_mean, ← μ.mean_mul_const]
    apply μ.mean_mono
    intro ω
    obtain ⟨Q, hQ, hQc⟩ := exists_independenceOrder G (A ω ∩ P)
    let aux (f : V → Bool) := Q.filter (fun x => f x = true)
    have hsub (f : V → Bool) : aux f ⊆ keep (ω, f) ∩ P := by
      intro x hx
      obtain ⟨hax, hfx⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxA, hxP⟩ := Finset.mem_inter.mp (hQ hax)
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hxA, hPW hxP⟩, hfx⟩, hxP⟩
    have hQind (f : V → Bool) : Gᶜ.IsClique (aux f : Set V) :=
      fun x hx y hy hxy => hQc.isClique ((Finset.mem_filter.mp hx).1) ((Finset.mem_filter.mp hy).1) hxy
    have heq (f : V → Bool) : ((aux f).card : ℝ) = ∑ x ∈ Q, if f x = true then 1 else 0 := by
      simp [aux]
    calc
      _ = ∑ _x ∈ Q, β := by simp [hQc.card_eq, mul_comm]
      _ ≤ ∑ x ∈ Q, t x := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hxW := hPW (Finset.mem_inter.mp (hQ hx)).2
        simp only [t, hxW, ite_true]
        exact (le_div_iff₀ (hp.trans_le (hmin x hxW))).mpr (hfrac x hxW)
      _ = τ.mean (fun f => ((aux f).card : ℝ)) := by
        simp_rw [heq, τ.mean_sum, τ.mean_indicator, hcoin]
      _ ≤ _ := τ.mean_mono (fun f => by exact_mod_cast card_le_independenceOrder (hsub f) (hQind f))


/-- The common-response guarantee excludes a large set of vertices whose
individual inclusion probabilities are all too small. -/
theorem card_low_marginals_lt (G : SimpleGraph V)
    (μ : FiniteLaw Ω) (S : Ω → Finset V) (W : Finset V)
    {b K cutoff : ℕ} (hb : 0 < b) (hK : 0 < K) {α : ℝ} (hα : 0 < α)
    (family : Finset V → Prop)
    (hFamily : ∀ A : Finset V, A ⊆ W → cutoff ≤ A.card →
      ∃ C : Finset V, C ⊆ A ∧ C.card = b ∧ family C)
    (hSample : ∀ C : Fin K → Finset V, (∀ j, C j ⊆ W ∧ (C j).card = b ∧ family (C j)) →
      (Pairwise fun i j => Disjoint (C i) (C j)) →
      α * K ≤ μ.mean (fun s => (independenceOrder G (S s ∩ Finset.univ.biUnion C) : ℝ))) :
    (W.filter (fun x => μ.event (fun s => x ∈ S s) < α / (2 * (b : ℝ)))).card <
      cutoff + K * b := by
  classical
  let A := W.filter (fun x => μ.event (fun s => x ∈ S s) < α / (2 * (b : ℝ)))
  have hAW : A ⊆ W := Finset.filter_subset _ _
  change A.card < _
  by_contra! hA
  obtain ⟨pack, hPack, hDisjoint, hLeft⟩ :=
    exists_packing (U := A) (d := cutoff) hb family (fun U hU => hFamily U (hU.trans hAW))
  let cover := pack.biUnion id
  have hCover : cover ⊆ A := by
    intro x hx
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
    exact (hPack C hC).1 hxC
  have hCard : cover.card = pack.card * b := by
    change (pack.biUnion (fun C => C)).card = _
    rw [Finset.card_biUnion hDisjoint]
    trans ∑ _C ∈ pack, b
    · exact Finset.sum_congr rfl (fun C hC => (hPack C hC).2.1)
    · simp
  have hSmall : K * b ≤ pack.card * b := by
    have he := Finset.card_sdiff_of_subset hCover
    rw [he, hCard] at hLeft
    have hLe := Finset.card_le_card hCover
    rw [hCard] at hLe
    omega
  obtain ⟨P, hP, hPsize⟩ := Finset.exists_subset_card_eq (Nat.le_of_mul_le_mul_right hSmall hb)
  let e := (Finset.equivFinOfCardEq hPsize).symm
  let C (j : Fin K) := (e j).val
  have hCA (j : Fin K) : C j ⊆ A := (hPack _ (hP (e j).property)).1
  have hCb (j : Fin K) : (C j).card = b := (hPack _ (hP (e j).property)).2.1
  have hCD : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    exact hDisjoint (hP (e i).property) (hP (e j).property)
      (fun h => hij (e.injective (Subtype.ext h)))
  have hTest := hSample C (fun j => ⟨(hCA j).trans hAW, hCb j, (hPack _ (hP (e j).property)).2.2⟩) hCD
  let U := Finset.univ.biUnion C
  have hUA : U ⊆ A := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
    exact hCA j hxj
  have hUb : U.card = K * b := by
    rw [Finset.card_biUnion (fun i _ j _ h => hCD h)]
    simp [hCb]
  have hCount : μ.mean (fun s => ((S s ∩ U).card : ℝ)) ≤ α * K / 2 := by
    have he (s : Ω) : ((S s ∩ U).card : ℝ) = ∑ x ∈ U, if x ∈ S s then 1 else 0 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
      simp
    simp_rw [he, μ.mean_sum, μ.mean_indicator]
    calc
      _ ≤ ∑ _x ∈ U, α / (2 * (b : ℝ)) := Finset.sum_le_sum (fun x hx =>
        (Finset.mem_filter.mp (hUA hx)).2.le)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, hUb, Nat.cast_mul]
        have hB : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
        field_simp
  have hLe : μ.mean (fun s => (independenceOrder G (S s ∩ U) : ℝ)) ≤
      μ.mean (fun s => ((S s ∩ U).card : ℝ)) :=
    μ.mean_mono (fun s => by exact_mod_cast independenceOrder_le_card G (S s ∩ U))
  change α * K ≤ μ.mean (fun s => (independenceOrder G (S s ∩ U) : ℝ)) at hTest
  have hpos : 0 < α * (K : ℝ) := by positivity
  linarith only [hLe, hTest, hCount, hpos]

private theorem exists_doubling_interval {a x : ℝ} (ha : 0 < a) (hx : a ≤ x) {m : ℕ}
    (h : x ≤ 2 ^ m * a) : ∃ k ≤ m, 2 ^ k * a ≤ x ∧ x < 2 ^ (k + 1) * a := by
  induction m with
  | zero =>
    have h' : x = a := le_antisymm (by simpa using h) hx
    exact ⟨0, le_rfl, by simp [h'], by simp [h']; linarith⟩
  | succ m ih =>
    by_cases hk : x ≤ 2 ^ m * a
    · obtain ⟨k, hkm, h₁, h₂⟩ := ih hk
      exact ⟨k, hkm.trans (Nat.le_succ m), h₁, h₂⟩
    · by_cases hl : x < 2 ^ (m + 1) * a
      · exact ⟨m, Nat.le_succ _, (le_of_not_ge hk), hl⟩
      · refine ⟨m + 1, le_rfl, le_of_not_gt hl, ?_⟩
        exact h.trans_lt (by rw [pow_succ' (2 : ℝ) (m + 1)]; nlinarith only [
          show 0 < (2 : ℝ) ^ (m + 1) * a by positivity])

/-- On a large class of comparable inclusion probabilities one can
equalize them while losing at most half the expected order. -/
theorem exists_balanced_sample_on_large_class (G : SimpleGraph V)
    (μ : FiniteLaw Ω) (S : Ω → Finset V) (W : Finset V)
    {pmin pmax : ℝ} (hmin : 0 < pmin) {m size : ℕ}
    (hR : pmax ≤ 2 ^ m * pmin)
    (hBounds : ∀ x ∈ W, pmin ≤ μ.event (fun s => x ∈ S s) ∧ μ.event (fun s => x ∈ S s) ≤ pmax)
    (hSize : (m + 1) * size ≤ W.card) (hSizePos : 0 < size) :
    ∃ (W' : Finset V) (ν : FiniteLaw (Ω × (V → Bool))) (S' : Ω × (V → Bool) → Finset V) (p : ℝ),
      W' ⊆ W ∧ size ≤ W'.card ∧ pmin ≤ p ∧ p ≤ pmax ∧
      (∀ z, S' z ⊆ S z.1 ∩ W') ∧ (∀ x ∈ W', ν.event (fun z => x ∈ S' z) = p) ∧
      ∀ P : Finset V, P ⊆ W' →
        (1 / 2 : ℝ) * μ.mean (fun s => (independenceOrder G (S s ∩ P) : ℝ)) ≤
          ν.mean (fun z => (independenceOrder G (S' z ∩ P) : ℝ)) := by
  classical
  let ρ (x : V) := μ.event (fun s => x ∈ S s)
  have hBin (x : V) (hx : x ∈ W) := exists_doubling_interval hmin
    (hBounds x hx).1 ((hBounds x hx).2.trans hR)
  let bin (x : V) := if hx : x ∈ W then Classical.choose (hBin x hx) else 0
  have hbin (x : V) (hx : x ∈ W) :
      bin x ≤ m ∧ 2 ^ bin x * pmin ≤ ρ x ∧ ρ x < 2 ^ (bin x + 1) * pmin := by
    simpa only [bin, dite_eq_left hx] using Classical.choose_spec (hBin x hx)
  obtain ⟨j, _, hj⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := W) (t := Finset.range (m + 1)) (f := bin)
    (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (hbin x hx).1))
    (Finset.nonempty_range_add_one) (by simpa only [Finset.card_range] using hSize)
  let W' := W.filter (fun x => bin x = j)
  let p := 2 ^ j * pmin
  have hPmin : pmin ≤ p := by
    simpa only [p, one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := j)) hmin.le
  have hlow (x : V) (hx : x ∈ W') : p ≤ ρ x := by
    obtain ⟨hxW, hxj⟩ := Finset.mem_filter.mp hx
    simpa only [hxj] using (hbin x hxW).2.1
  have hfrac (x : V) (hx : x ∈ W') : (1 / 2 : ℝ) * ρ x ≤ p := by
    obtain ⟨hxW, hxj⟩ := Finset.mem_filter.mp hx
    have h := (hbin x hxW).2.2
    rw [hxj, pow_succ] at h
    dsimp [p]
    linarith only [h]
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (hSizePos.trans_le hj)
  have hPmax := (hlow x hx).trans (hBounds x (Finset.filter_subset _ _ hx)).2
  obtain ⟨ν, S', hSub, hMarg, hPay⟩ := exists_equal_marginal_sample G μ S W'
    (hmin.trans_le hPmin) hlow hfrac
  exact ⟨W', ν, S', p, Finset.filter_subset _ _, hj, hPmin, hPmax, hSub, hMarg, hPay⟩

end LocallyRamsey
