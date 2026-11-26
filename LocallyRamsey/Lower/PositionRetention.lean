module

public import LocallyRamsey.Lower.IntersectionDensity
public import LocallyRamsey.Lower.RetentionRule
public import LocallyRamsey.Lower.RepeatedSelection
public import LocallyRamsey.Lower.PrescribedRetention
public import LocallyRamsey.Lower.PackedTests

public section

open scoped BigOperators Classical

namespace LocallyRamsey

section Biased

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

/-- The auxiliary retention draw can follow the biased or the original
sample. Biasing changes the weight of the sample, and it leaves the
conditional law of the retention draw unchanged. -/
theorem biased_staged_mean_retaining (W : Finset V) (hW : W.Nonempty)
    (μ : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    {p : ℝ} (hp : 0 < p) (huniform : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p)
    (ν : Ω → FiniteLaw (Finset V)) {x : V} (hx : x ∈ W)
    (keep : Ω × Finset V → Prop) [DecidablePred keep]
    (hkeep : ∀ z, keep z → contains z.1 x) :
    ((biasedLaw W hW μ contains p hp huniform).staged ν).mean
      (fun z => sampleWeight W contains z.1 x * (if keep z then 1 else 0)) =
      (μ.staged ν).event keep / p := by
  let π := biasedLaw W hW μ contains p hp huniform
  rw [← (μ.staged ν).mean_indicator, FiniteLaw.mean, FiniteLaw.mean, Finset.sum_div]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  change π.prob z.1 * (ν z.1).prob z.2 *
    (sampleWeight W contains z.1 x * (if keep z then 1 else 0)) =
    (μ.prob z.1 * (ν z.1).prob z.2 * (if keep z then 1 else 0)) / p
  by_cases hz : keep z
  · simp only [hz, ite_true, mul_one]
    rw [mul_right_comm, biasedLaw_prob_mul_weight W hW μ contains hp huniform hx]
    simp only [hkeep z hz, ite_true, mul_one, div_mul_eq_mul_div]
  · simp [hz]

/-- The average weight retained at one position is at most the common
retention parameter. Applying the density test can only lower this
average. -/
theorem mean_retained_position_weight_le (W B : Finset V) (hW : W.Nonempty) (hBW : B ⊆ W)
    (μ : FiniteLaw Ω) (contains : Ω → V → Prop) [∀ ω, DecidablePred (contains ω)]
    {p γ : ℝ} (hp : 0 < p) (hγ : 0 ≤ γ)
    (huniform : ∀ x ∈ W, μ.event (fun ω => contains ω x) = p)
    (ν : Ω → FiniteLaw (Finset V)) (F : Ω × Finset V → Finset V)
    (hF : ∀ z x, x ∈ F z → contains z.1 x)
    (hMarginal : ∀ x ∈ B, (μ.staged ν).event (fun z => x ∈ F z) ≤ γ * p)
    (ok : Ω × Finset V → Prop) [DecidablePred ok] :
    let π := (biasedLaw W hW μ contains p hp huniform).staged ν
    let w (z : Ω × Finset V) (x : V) := sampleWeight W contains z.1 x / B.card
    π.mean (fun z => if ok z then mass (w z) (B ∩ F z) else 0) ≤ γ := by
  intro π w
  have hW0 (z : Ω × Finset V) (x : V) : 0 ≤ w z x := by
    dsimp [w, sampleWeight]
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply div_nonneg _ (sampleDensity_nonneg _ _ _)
    split <;> norm_num
  have he (z : Ω × Finset V) : mass (w z) (B ∩ F z) =
      (∑ x ∈ B, sampleWeight W contains z.1 x * (if x ∈ F z then 1 else 0)) / B.card := by
    rw [mass, ← Finset.filter_mem_eq_inter, Finset.sum_filter]
    simp only [w, Finset.sum_div, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro x _
    split <;> simp_all
  by_cases hB : B.Nonempty
  · refine (π.mean_mono (Y := fun z => mass (w z) (B ∩ F z)) (fun z => by
      split
      · rfl
      · exact Finset.sum_nonneg fun x _ => hW0 z x)).trans ?_
    simp_rw [he, div_eq_inv_mul, π.mean_mul_const, π.mean_sum]
    have hx (x : V) (hxB : x ∈ B) : π.mean (fun z =>
        sampleWeight W contains z.1 x * (if x ∈ F z then 1 else 0)) ≤ γ := by
      rw [biased_staged_mean_retaining W hW μ contains hp huniform ν (hBW hxB)
        (fun z => x ∈ F z) (fun z hz => hF z x hz)]
      exact (div_le_iff₀ hp).mpr (hMarginal x hxB)
    have hBc : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB.card_ne_zero
    refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hx) (by positivity)).trans_eq ?_
    simp [← mul_assoc, hBc]
  · have hnil : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    simp [hnil, mass, π.mean_const, hγ]

/-- The degree bound survives the reweighting at a position because all
vertices retained there receive the same weight. -/
theorem weighted_retention_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (S B F : Finset V) (hFS : F ⊆ S ∩ B) {c D η γ : ℝ} (hc : 0 ≤ c)
    (hD : 0 < D) (hη : 0 ≤ η) (hγ : 2 * η ≤ γ)
    (hρ : c * (S ∩ B).card ≤ 2)
    (hdeg : ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) ≤
      (F.card + η * (S ∩ B).card) / D) :
    ∀ x ∈ F, mass (fun _ => c) (neighborsIn G F x) ≤
      (mass (fun _ => c) F + γ) / D := by
  intro x hx
  have h := mul_le_mul_of_nonneg_left (hdeg x hx) hc
  have hm : c * (η * ((S ∩ B).card : ℝ)) ≤ γ := by
    calc
      _ = η * (c * ((S ∩ B).card : ℝ)) := by ring
      _ ≤ η * 2 := mul_le_mul_of_nonneg_left hρ hη
      _ ≤ _ := by linarith only [hγ]
  simp only [mass, Finset.sum_const, nsmul_eq_mul]
  rw [mul_comm ((neighborsIn G F x).card : ℝ) c, mul_comm (F.card : ℝ) c]
  refine h.trans ?_
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hD.le
  rw [mul_add]
  exact add_le_add_right hm _


end Biased

variable {V Ω : Type*} [Fintype V] [Fintype Ω]
/-- Choose a retention law for a prescribed region from the original
sampling rule. The required inequalities state that the encoding and
collision errors leave enough expected independent-set vertices to
pay for the uniformly capped marginals. -/
theorem exists_retention_rule_from_sampler [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : FiniteLaw Ω) (S : Ω → Finset V) (B : Finset V)
    {b K H cutoff stages : ℕ} (hb : 0 < b) (hK : 0 < K)
    (family : Finset V → Prop)
    (hClique : ∀ C, family C → G.IsClique (C : Set V))
    (hPack : ∀ A : Finset V, A ⊆ B → cutoff < A.card →
      ∃ pack : Finset (Finset V),
        (∀ C ∈ pack, C ⊆ A ∧ C.card = b ∧ family C) ∧
        (pack : Set (Finset V)).Pairwise Disjoint ∧
        (A.card : ℝ) / 2 ≤ (pack.card : ℝ) * b)
    {α t rate D η z : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) (hrate : 0 < rate)
    (hD : 1 < D) (hη : 0 < η) (hz : 0 ≤ z)
    (hH : ⌈D * Real.log (1 + 1 / η)⌉₊ ≤ H)
    (hSample : ∀ C : Fin K → Finset V,
      (∀ j, C j ⊆ B ∧ (C j).card = b ∧ family (C j)) →
      (Pairwise fun i j => Disjoint (C i) (C j)) →
      α ≤ μ.mean (fun s => (independenceOrder G (S s ∩ Finset.univ.biUnion C) : ℝ)))
    (hErr : (H : ℝ) + z + K * ((K * b + 1 : ℕ) : ℝ) ^ H * Real.exp (-(Real.log 2 * z)) +
      4 * K * b * rate ≤ α * (1 - (K : ℝ) ^ 2 * (b * (2 * b / (cutoff + 1)))))
    (hCut : B.card / 2 ^ stages ≤ cutoff)
    (hCost : stages * (2 * t / rate) ≤ 1) :
    ∃ ν : Ω → FiniteLaw (Finset V),
      (∀ ω F, 0 < (ν ω).prob F → F ⊆ B ∧ F ⊆ S ω ∧
        ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) ≤
          (F.card + η * (S ω ∩ B).card) / D) ∧
      (∀ x ∈ B, (μ.staged ν).event (fun p => x ∈ p.2) ≤ t) ∧
      (B.filter (fun x => (μ.staged ν).event (fun p => x ∈ p.2) < t)).card ≤ cutoff := by
  let valid (ω : Ω) (F : Finset V) :=
    F ⊆ S ω ∧ ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) ≤ (F.card + η * (S ω ∩ B).card) / D
  refine exists_capped_retention μ B valid (fun _ => by simp [valid]) ht hrate cutoff stages hCut hCost ?_
  intro A hAB hA
  obtain ⟨pack, hP, hDisjoint, hCollect⟩ := hPack A hAB hA
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hPne : pack.Nonempty := by
    apply Finset.card_pos.mp
    have hp := (show (0 : ℝ) < A.card / 2 by positivity).trans_le hCollect
    exact_mod_cast (pos_of_mul_pos_left hp (Nat.cast_nonneg _))
  let _ : Nonempty ↥pack := hPne.to_subtype
  let law := FiniteLaw.uniform ↥pack
  let u := 2 * (b : ℝ) / A.card
  let enum (P : ↥pack) (i : Fin b) : V :=
    ((Finset.equivFinOfCardEq (hP P.val P.property).2.1).symm i).val
  have hen (P : ↥pack) (x : V) (hx : x ∈ P.val) : ∃ k, enum P k = x := by
    let e := Finset.equivFinOfCardEq (hP P.val P.property).2.1
    exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)⟩
  have hMarg (x : V) : law.event (fun P => x ∈ P.val) ≤ u := by
    refine (uniform_packing_marginal_le pack hPne hDisjoint x).trans ?_
    have hp : (0 : ℝ) < pack.card := by exact_mod_cast hPne.card_pos
    dsimp [u]
    rw [div_le_div_iff₀ hp hApos, one_mul]
    nlinarith only [hCollect]
  obtain ⟨F, hF, hSize⟩ :=
    exists_prescribed_retention_from_sampler G μ law S A B hAB Subtype.val
      (fun P => (hP P.val P.property).1) (fun P => hClique _ (hP P.val P.property).2.2)
      (fun P => (hP P.val P.property).2.1.le) enum hen (by dsimp [u]; positivity)
      hα hD hη hz hH hMarg (fun τ hτ => hSample (fun j => (τ j).val) (fun j =>
        ⟨(hP _ (τ j).property).1.trans hAB, (hP _ (τ j).property).2⟩) hτ)
  have hLess : u ≤ 2 * (b : ℝ) / (cutoff + 1) := by
    dsimp [u]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast Nat.succ_le_of_lt hA
  have hColl : α * (1 - (K : ℝ) ^ 2 * (b * (2 * b / (cutoff + 1)))) ≤
      α * (1 - (K : ℝ) ^ 2 * (b * u)) := by gcongr
  have Hsize := hErr.trans (hColl.trans hSize)
  let ν (ω : Ω) := FiniteLaw.single (F ω)
  refine ⟨ν, ?_, ?_⟩
  · intro ω A' hν
    have he : A' = F ω := by
      by_contra hno
      simp [ν, FiniteLaw.single, Ne.symm hno] at hν
    subst A'
    exact ⟨Finset.inter_subset_right.trans' (hF ω).1,
      (hF ω).1.trans Finset.inter_subset_left, (hF ω).2⟩
  · rw [FiniteLaw.staged_mean]
    simp_rw [ν, FiniteLaw.single_mean]
    have hprod : 4 * (K : ℝ) * b * rate ≤
        2 * K * u * μ.mean (fun ω => ((F ω).card : ℝ)) := by linarith only [Hsize]
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    rw [show 2 * (K : ℝ) * u = (4 * K * b) / A.card by dsimp [u]; ring,
      div_mul_eq_mul_div] at hprod
    have hh := (le_div_iff₀ hApos).1 hprod
    apply (mul_le_mul_iff_of_pos_left (show (0 : ℝ) < 4 * K * b by positivity)).1
    simpa only [mul_assoc] using hh

end LocallyRamsey
