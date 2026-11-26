module

public import LocallyRamsey.Lower.StableSampling

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- Reweighting by one sample is averaging over the intersection of that
sample with the original region. -/
theorem intersectionDensity_cons_sample
    (W : Finset V) (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)]
    (s : Ω) {q : ℕ} (ω : Fin q → Ω) :
    let T := W.filter (contains s)
    intersectionDensity (sampleWeight W contains) W (Fin.cons s ω) =
      intersectionDensity (sampleWeight W contains) T ω := by
  classical
  intro T
  let L := sampleWeight W contains
  let ρ := sampleDensity W contains s
  have hc : ρ = (T.card : ℝ) / W.card := by
    change sampleDensity W contains s = _
    unfold sampleDensity
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, T]
  have hw (x : V) (hx : x ∈ W) :
      L s x = if x ∈ T then 1 / ρ else 0 := by
    by_cases h : contains s x <;> simp [L, sampleWeight, T, ρ, h, hx]
  rw [show intersectionDensity L W (Fin.cons s ω) =
    ((T.card : ℝ) * (1 / ρ) / W.card) * intersectionDensity L T ω from
    intersectionDensity_cons_of_constant L W T (Finset.filter_subset _ _) s hw ω]
  by_cases hT : T.Nonempty
  · have hW : W.Nonempty := hT.mono (Finset.filter_subset _ _)
    have hT0 : (T.card : ℝ) ≠ 0 := by exact_mod_cast hT.card_ne_zero
    have hW0 : (W.card : ℝ) ≠ 0 := by exact_mod_cast hW.card_ne_zero
    rw [hc, show (T.card : ℝ) * (1 / ((T.card : ℝ) / W.card)) / W.card = 1 by field_simp, one_mul]
  · have hnil : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [hnil, intersectionDensity]

private theorem card_positions_away_from (k : ℕ) (i : Fin (k + 1)) :
    Fintype.card {j : Fin (k + 1) // j ≠ i} = k := by
  classical
  have he : {j : Fin (k + 1) | j ≠ i} = ({i} : Set (Fin (k + 1)))ᶜ := by ext; simp
  change Fintype.card ↥{j : Fin (k + 1) | j ≠ i} = k
  simp only [he, Fintype.card_compl_set, Fintype.card_fin, Fintype.card_unique, Nat.add_sub_cancel]

/-- Concentration for a full group of biased samples. The only inputs
about the old graph are the stabilized density comparisons for large
intersections of the region with one sample. -/
theorem event_bad_biased_group_le
    (W : Finset V) (hW : W.Nonempty) (μ : FiniteLaw Ω)
    (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)]
    {p τ ε : ℝ} (hp : 0 < p) (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hu : ∀ x ∈ W, μ.event (fun s => contains s x) = p) (k : ℕ)
    (hClose : let π := biasedLaw W hW μ contains p hp hu
      let L := sampleWeight W contains
      ∀ s, τ ≤ sampleDensity W contains s →
        rootDistance (FiniteLaw.product (fun _ : Fin k => π))
          (intersectionDensity L (W.filter (contains s))) (intersectionDensity L W) ≤ 2 * ε) :
    let π := biasedLaw W hW μ contains p hp hu
    let L := sampleWeight W contains
    let Y := intersectionDensity L W
    (FiniteLaw.product (fun _ : Fin (k + 1) => π)).event (fun z =>
      Y z < 1 / 2 ∨ 2 < Y z ∨ ∃ i, sampleDensity W contains (z i) < τ) ≤
      ((k + 1 : ℕ) : ℝ) * (32 * (2 * ε + 2 * (τ / p)) + τ / p) := by
  classical
  intro π L Y
  let e (i : Fin (k + 1)) := Fintype.equivOfCardEq
    (show Fintype.card (Fin k) = Fintype.card {j : Fin (k + 1) // j ≠ i} by
      rw [Fintype.card_fin, card_positions_away_from])
  let omitted (i : Fin (k + 1)) (z : Fin (k + 1) → Ω) :=
    intersectionDensity L W (fun j => z (e i j).val)
  have hY0 (z : Fin (k + 1) → Ω) : 0 ≤ Y z :=
    intersectionDensity_nonneg L (fun s x => by
      change 0 ≤ (if contains s x then 1 else 0) / sampleDensity W contains s
      apply div_nonneg _ (sampleDensity_nonneg W contains s)
      split <;> norm_num) W z
  have hL0 (s : Ω) (x : V) : 0 ≤ L s x := by
    change 0 ≤ (if contains s x then 1 else 0) / sampleDensity W contains s
    apply div_nonneg _ (sampleDensity_nonneg W contains s)
    split <;> norm_num
  have hL1 (x : V) (hx : x ∈ W) : π.mean (fun s => L s x) = 1 :=
    biasedLaw_mean_weight W hW μ contains p hp hu hx
  refine FiniteLaw.event_bad_intersection_group_le π (k + 1) Y omitted ?_ hY0
    (mean_intersectionDensity π L W hW hL1 (k + 1)) _ (biasedLaw_event_small_density_le W hW μ contains hp hτ.le hu) ?_
  · intro i z z' hz
    dsimp [omitted]
    congr 1
    funext j
    exact hz _ (e i j).property
  · intro i
    let extra (s : Ω) (w : Fin k → Ω) :=
      (Real.sqrt (intersectionDensity L (W.filter (contains s)) w) -
        Real.sqrt (intersectionDensity L W w)) ^ 2
    let Q (s : Ω × ({j : Fin (k + 1) // j ≠ i} → Ω)) := extra s.1 (s.2 ∘ e i)
    have hFull (z : Fin (k + 1) → Ω) :
        Y z = intersectionDensity L W (Fin.cons (z i) (fun j => z (e i j).val)) := by
      unfold Y intersectionDensity
      congr 1
      refine Finset.sum_congr rfl (fun x _ => ?_)
      calc
        _ = L (z i) x * ∏ j ∈ Finset.univ.erase i, L (z j) x :=
          (Finset.mul_prod_erase _ (fun j => L (z j) x) (Finset.mem_univ i)).symm
        _ = L (z i) x * ∏ j : Fin k, L (z (e i j).val) x := by
          congr 1
          have hE := Fintype.prod_equiv (e i) (fun j => L (z (e i j).val) x)
            (fun j : {j : Fin (k + 1) // j ≠ i} => L (z j.val) x) (fun _ => rfl)
          rw [hE]
          exact Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp) (fun j => L (z j) x)
        _ = _ := by rw [Fin.prod_univ_succ]; rfl
    have he (z : Fin (k + 1) → Ω) :
        (Real.sqrt (Y z) - Real.sqrt (omitted i z)) ^ 2 = Q (z i, fun j => z j.val) := by
      have ht : intersectionDensity L W (Fin.cons (z i) (fun j => z (e i j).val)) =
          intersectionDensity L (W.filter (contains (z i))) (fun j => z (e i j).val) :=
        intersectionDensity_cons_sample W contains (z i) (fun j => z (e i j).val)
      rw [hFull z, ht]
      rfl
    simp_rw [he]
    rw [FiniteLaw.mean_split_at (fun _ => π) i Q, FiniteLaw.staged_mean]
    have hProj (s : Ω) :
        (FiniteLaw.product (fun _ : {j : Fin (k + 1) // j ≠ i} => π)).mean
          (fun w => Q (s, w)) =
        (FiniteLaw.product (fun _ : Fin k => π)).mean (extra s) :=
      FiniteLaw.mean_injective_projection π (e i) (e i).injective (extra s)
    simp_rw [hProj]
    let ν := FiniteLaw.product (fun _ : Fin k => π)
    have hcond (s : Ω) : ν.mean (extra s) ≤
        2 * ε + 2 * (if sampleDensity W contains s < τ then 1 else 0) := by
      by_cases hs : sampleDensity W contains s < τ
      · let T := W.filter (contains s)
        have hW1 := mean_intersectionDensity π L W hW hL1 k
        have hT1 : ν.mean (intersectionDensity L T) ≤ 1 := by
          by_cases hT : T.Nonempty
          · exact (mean_intersectionDensity π L T hT
              (fun x hx => hL1 x (Finset.filter_subset _ _ hx)) k).le
          · have hn : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
            have hf : intersectionDensity L (∅ : Finset V) = (fun _ : Fin k → Ω => 0) := by
              funext w
              simp [intersectionDensity]
            rw [hn, hf, ν.mean_const]
            norm_num
        have hY (B : Finset V) (w : Fin k → Ω) :
            (Real.sqrt (intersectionDensity L B w)) ^ 2 = intersectionDensity L B w :=
          Real.sq_sqrt (intersectionDensity_nonneg L hL0 B w)
        have ht (w : Fin k → Ω) : extra s w ≤ intersectionDensity L T w + intersectionDensity L W w := by
          change (Real.sqrt (intersectionDensity L T w) - Real.sqrt (intersectionDensity L W w)) ^ 2 ≤ _
          nlinarith only [hY T w, hY W w,
            mul_nonneg (Real.sqrt_nonneg (intersectionDensity L T w)) (Real.sqrt_nonneg (intersectionDensity L W w))]
        have hb := ν.mean_mono ht
        rw [ν.mean_add, hW1] at hb
        simp only [hs, ite_true, mul_one]
        linarith only [hb, hT1, hε]
      · simp only [hs, ite_false, mul_zero, add_zero]
        exact hClose s (le_of_not_gt hs)
    refine (π.mean_mono hcond).trans ?_
    rw [π.mean_add, π.mean_const, π.mean_mul_const, π.mean_indicator]
    have hp' := biasedLaw_event_small_density_le W hW μ contains hp hτ.le hu
    linarith only [hp']


/-- The normalized intersection density is its actual density divided by
the product of the individual sample densities. -/
theorem intersectionDensity_eq_card (W B : Finset V)
    (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)] {q : ℕ} (z : Fin q → Ω) :
    let C := B.filter (fun x => ∀ i, contains (z i) x)
    intersectionDensity (sampleWeight W contains) B z =
      (C.card : ℝ) / ((B.card : ℝ) * ∏ i, sampleDensity W contains (z i)) := by
  classical
  intro C
  have hprod (x : V) : (∏ i, sampleWeight W contains (z i) x) =
      (if ∀ i, contains (z i) x then 1 else 0) / ∏ i, sampleDensity W contains (z i) := by
    rw [show (∏ i, sampleWeight W contains (z i) x) =
      (∏ i, (if contains (z i) x then (1 : ℝ) else 0)) / ∏ i, sampleDensity W contains (z i) from
      Finset.prod_div_distrib _ _]
    congr 1
    by_cases h : ∀ i, contains (z i) x
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [ite_eq_right h]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [hi]
  unfold intersectionDensity
  simp_rw [hprod, ← Finset.sum_div]
  rw [div_div, mul_comm (∏ i, sampleDensity W contains (z i))]
  congr 1
  simp [C]

/-- A good group has a large actual intersection, and its normalized
weight dominates the uniform law on that intersection. -/
theorem good_intersection_support (W : Finset V) (hW : W.Nonempty)
    (contains : Ω → V → Prop) [∀ s, DecidablePred (contains s)] {q : ℕ} (z : Fin q → Ω)
    {τ : ℝ} (hτ : 0 < τ) (hρ : ∀ i, τ ≤ sampleDensity W contains (z i))
    (hY : (1 : ℝ) / 2 ≤ intersectionDensity (sampleWeight W contains) W z) :
    let C := W.filter (fun x => ∀ i, contains (z i) x)
    (W.card : ℝ) * τ ^ q / 2 ≤ C.card ∧
      ∀ x ∈ C, (1 : ℝ) / C.card ≤ 2 * (∏ i, sampleWeight W contains (z i) x) / W.card := by
  classical
  intro C
  let ρ (s : Ω) := sampleDensity W contains s
  let f := ∏ i, ρ (z i)
  have hf : 0 < f := Finset.prod_pos (fun i _ => hτ.trans_le (hρ i))
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hfac : τ ^ q ≤ f := by
    have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin q)))
      (fun _ _ => hτ.le) (fun i _ => hρ i)
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  have hY' : (1 : ℝ) / 2 ≤ (C.card : ℝ) / ((W.card : ℝ) * f) :=
    hY.trans_eq (intersectionDensity_eq_card W W contains z)
  have h := (le_div_iff₀ (mul_pos hWpos hf)).mp hY'
  constructor
  · have hh := mul_le_mul_of_nonneg_left hfac hWpos.le
    linarith only [h, hh]
  · intro x hx
    have hxC : ∀ i, contains (z i) x := (Finset.mem_filter.mp hx).2
    have he : (∏ i, sampleWeight W contains (z i) x) = 1 / f := by
      simp only [sampleWeight, hxC, ite_true, Finset.prod_div_distrib, Finset.prod_const_one, f, ρ]
    have hCpos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
    rw [he, mul_div_assoc, div_div, mul_comm f, mul_one_div,
      div_le_div_iff₀ hCpos (mul_pos hWpos hf), one_mul]
    linarith only [h]

end LocallyRamsey
