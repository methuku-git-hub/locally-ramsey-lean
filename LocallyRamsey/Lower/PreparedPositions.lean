module

public import LocallyRamsey.Lower.PositionRetention
public import LocallyRamsey.Lower.StableSampling
public import LocallyRamsey.Lower.SamplingExperiment

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Conditional on a prescribed region, adjoining the extra random choices
preserves the biased sample law. The density test gives bounded weights
while preserving enough independent chances to retain each vertex. -/
theorem prepared_position_retention (G : SimpleGraph V) [DecidableRel G.Adj]
    (W B : Finset V) (hW : W.Nonempty) (hBW : B ⊆ W)
    (μ : FiniteLaw (Finset V)) {p γ ε δ D θ bound : ℝ}
    (hp : 0 < p) (hγ : 0 ≤ γ) (hδ : 0 < δ) (hB : δ ≤ B.card)
    (hD : 0 < D) (hθ : 0 ≤ θ) (htheta : 2 * θ ≤ γ) (htest : 36 * ε ≤ γ / 2)
    (hu : ∀ x ∈ W, μ.event (fun S => x ∈ S) = p)
    (ν : Finset V → FiniteLaw (Finset V))
    (hν : ∀ S F, 0 < (ν S).prob F → F ⊆ B ∧ F ⊆ S ∧
      ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) ≤ (F.card + θ * (S ∩ B).card) / D)
    (hMarg : ∀ x ∈ B, (μ.staged ν).event (fun z => x ∈ z.2) ≤ γ * p)
    (hE : ((B.filter (fun x => (μ.staged ν).event (fun z => x ∈ z.2) < γ * p)).card : ℝ) ≤
      bound * B.card)
    (hClose : let contains (S : Finset V) x := x ∈ S
      let π := biasedLaw W hW μ contains p hp hu
      let L := sampleWeight W contains
      ∀ A : Finset V, A ⊆ B → δ ≤ A.card →
        rootDistance (FiniteLaw.product (fun _ : Fin 1 => π))
          (intersectionDensity L A) (intersectionDensity L W) ≤ 2 * ε)
    (q : ℕ) :
    let contains (S : Finset V) x := x ∈ S
    let π := biasedLaw W hW μ contains p hp hu
    let α := π.staged ν
    let L (s : Finset V × Finset V) := sampleWeight W contains s.1
    let c (s : Finset V × Finset V) := (sampleDensity W contains s.1)⁻¹
    ∃ F : Finset V × Finset V → Finset V,
      (∀ s, F s ⊆ B ∧ F s ⊆ s.1) ∧
      (∀ s, (F s).card * c s / B.card ∈ Set.Icc (0 : ℝ) 2) ∧
      α.mean (fun s => (F s).card * c s / B.card) ≤ γ ∧
      (∀ s x, x ∈ F s → mass (fun _ => c s / B.card) (neighborsIn G (F s) x) ≤
        ((F s).card * c s / B.card + γ) / D) ∧
      (FiniteLaw.product (fun _ : Fin q => α)).mean (fun ω =>
        (∑ x ∈ B, (∏ i, L (ω i) x) *
          (if ((Finset.univ.filter (fun i => x ∈ F (ω i))).card : ℝ) < γ * q / 4
            then 1 else 0)) / B.card) ≤ bound + δ / B.card + Real.exp (-(γ * q) / 16) := by
  classical
  intro contains π α L c
  let Y (A : Finset V) (s : Finset V) := (∑ x ∈ A, sampleWeight W contains s x) / A.card
  let raw (s : Finset V × Finset V) := if 0 < (ν s.1).prob s.2 then s.2 else ∅
  let bad (s : Finset V × Finset V) := 2 < Y B s.1
  let F (s : Finset V × Finset V) := if bad s then ∅ else raw s
  let E := B.filter (fun x => (μ.staged ν).event (fun z => x ∈ z.2) < γ * p)
  have hB0 : (0 : ℝ) < B.card := hδ.trans_le hB
  have hraw (s : Finset V × Finset V) : raw s ⊆ B ∧ raw s ⊆ s.1 ∧
      ∀ x ∈ raw s, ((neighborsIn G (raw s) x).card : ℝ) ≤
        ((raw s).card + θ * (s.1 ∩ B).card) / D := by
    by_cases hs : 0 < (ν s.1).prob s.2
    · simpa only [raw, hs, ite_true] using hν s.1 s.2 hs
    · simp [raw, hs]
  have hF (s : Finset V × Finset V) : F s ⊆ B ∧ F s ⊆ s.1 := by
    by_cases hs : bad s
    · simp [F, hs]
    · simp only [F, hs, ite_false]
      exact ⟨(hraw s).1, (hraw s).2.1⟩
  have hc (s : Finset V × Finset V) : 0 ≤ c s :=
    inv_nonneg.mpr (sampleDensity_nonneg _ _ _)
  have hL (s : Finset V × Finset V) (x : V) :
      L s x = if x ∈ s.1 then c s else 0 := by
    by_cases hx : x ∈ s.1 <;> simp [L, c, sampleWeight, contains, hx, one_div]
  have hL0 (s : Finset V × Finset V) (x : V) : 0 ≤ L s x := by
    rw [hL]
    split <;> simp [hc s]
  have hY (s : Finset V × Finset V) : Y B s.1 = ((s.1 ∩ B).card : ℝ) * c s / B.card := by
    simp only [Y, ← show ∀ x, L s x = sampleWeight W contains s.1 x from fun _ => rfl,
      hL, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul,
      Finset.inter_comm B s.1]
  have hMass (s : Finset V × Finset V) (A : Finset V) (hA : A ⊆ s.1) :
      mass (fun x => L s x / B.card) A = (A.card : ℝ) * c s / B.card := by
    rw [mass, ← Finset.sum_div]
    simp only [hL, Finset.sum_congr rfl (fun x hx => if_pos (hA hx)),
      Finset.sum_const, nsmul_eq_mul]
  have hRawEvent (x : V) : (μ.staged ν).event (fun s => x ∈ raw s) =
      (μ.staged ν).event (fun s => x ∈ s.2) := by
    simp only [FiniteLaw.staged_event]
    congr 1
    funext s
    simp only [← FiniteLaw.mean_indicator, FiniteLaw.mean]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    by_cases h : 0 < (ν s).prob A
    · simp [raw, h]
    · simp [le_antisymm (le_of_not_gt h) ((ν s).nonneg A)]
  have hMean (x : V) (hx : x ∈ B) :
      α.mean (fun s => L s x * (if x ∈ raw s then 1 else 0)) =
        (μ.staged ν).event (fun s => x ∈ s.2) / p := by
    rw [← hRawEvent]
    exact biased_staged_mean_retaining W hW μ contains hp hu ν (hBW hx)
      (fun s => x ∈ raw s) (fun s hs => (hraw s).2.1 hs)
  have hBtest : rootDistance π (Y B) (Y W) ≤ 2 * ε := by
    rw [← rootDistance_single_intersection π (sampleWeight W contains)]
    exact hClose B (by rfl) hB
  have hStable (A : Finset V) (hAB : A ⊆ B) (hAc : δ ≤ A.card) :
      (∑ x ∈ A, α.mean (fun s => L s x * (if bad s then 1 else 0))) / A.card ≤ γ / 2 := by
    have hAne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hδ.trans_le hAc)
    have hABtest : rootDistance π (Y A) (Y W) ≤ 2 * ε := by
      rw [← rootDistance_single_intersection π (sampleWeight W contains)]
      exact hClose A hAB hAc
    have hv (x : V) : α.mean (fun s => L s x * (if bad s then 1 else 0)) =
        π.mean (fun s => sampleWeight W contains s x * (if 2 < Y B s then 1 else 0)) := by
      rw [show α = π.staged ν from rfl, FiniteLaw.staged_mean]
      congr 1
      funext s
      by_cases hs : 2 < Y B s <;> simp [L, bad, hs, FiniteLaw.mean_const]
    simp_rw [hv]
    exact (mean_weight_of_large_density_le π (sampleWeight W contains) W A B hAne
      (fun s x => hL0 (s, ∅) x)
      (fun x hx => biasedLaw_mean_weight W hW μ contains p hp hu (hBW (hAB hx)))
      (biasedLaw_avg_weight_eq_one W hW μ contains hp hu)
      hABtest hBtest).trans htest
  refine ⟨F, hF, ?_, ?_, ?_, ?_⟩
  · intro s
    refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hc s)) hB0.le, ?_⟩
    by_cases hs : bad s
    · simp [F, hs]
    · calc
        _ ≤ ((s.1 ∩ B).card : ℝ) * c s / B.card := by
          apply div_le_div_of_nonneg_right _ hB0.le
          apply mul_le_mul_of_nonneg_right _ (hc s)
          exact_mod_cast Finset.card_le_card (Finset.subset_inter (hF s).2 (hF s).1)
        _ = Y B s.1 := (hY s).symm
        _ ≤ 2 := le_of_not_gt hs
  · have h := mean_retained_position_weight_le W B hW hBW μ contains hp hγ hu ν raw
      (fun s x hx => (hraw s).2.1 hx) (fun x hx => by rw [hRawEvent]; exact hMarg x hx)
      (fun s => ¬ bad s)
    refine Eq.trans_le ?_ h
    congr 1
    funext s
    rw [← hMass s (F s) (hF s).2]
    by_cases hb : bad s
    · simp [F, hb, mass]
    · simp only [hb, not_false_eq_true, ite_true, F, ite_false]
      rw [Finset.inter_eq_right.mpr (hraw s).1]
  · intro s x hx
    have hb : ¬ bad s := fun h => by simpa [F, h] using hx
    have he : F s = raw s := by simp [F, hb]
    have hd : c s / B.card * ((s.1 ∩ B).card : ℝ) ≤ 2 := by
      rw [show c s / B.card * ((s.1 ∩ B).card : ℝ) = Y B s.1 by rw [hY]; ring]
      exact le_of_not_gt hb
    have h := weighted_retention_degree G s.1 B (F s)
      (Finset.subset_inter (hF s).2 (hF s).1) (div_nonneg (hc s) hB0.le) hD hθ htheta hd
      (by rw [he]; exact (hraw s).2.2) x hx
    convert h using 1
    simp only [mass, Finset.sum_const, nsmul_eq_mul]
    ring
  · have h := trimmed_selection_repeated_le α L hL0 B E (Finset.filter_subset _ _) raw bad
      hγ hδ (fun x hx => by
        simp only [α, FiniteLaw.staged_mean, L, FiniteLaw.mean_const]
        exact biasedLaw_mean_weight W hW μ contains p hp hu (hBW hx))
      (fun x hx hne => by
        rw [hMean x hx, le_div_iff₀ hp]
        exact le_of_not_gt (fun hh => hne (Finset.mem_filter.mpr ⟨hx, hh⟩)))
      hStable q
    refine h.trans (add_le_add_left ?_ _)
    rw [add_div]
    exact add_le_add_left ((div_le_iff₀ hB0).mpr hE) _

end LocallyRamsey
