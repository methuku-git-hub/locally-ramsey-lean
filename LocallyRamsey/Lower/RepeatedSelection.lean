module

public import LocallyRamsey.Lower.IntersectionDensity
public import LocallyRamsey.Lower.PrescribedRetention

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- Trimming a rule on a bad sample loses at most the conditional
probability of that sample. If every sufficiently large vertex set has
small mean conditional loss, the vertices at which the loss is too large
form an exceptional set of smaller order. -/
theorem exists_small_exception_for_trimmed_rule
    (μ : FiniteLaw Ω) (L : Ω → V → ℝ) (hL : ∀ s x, 0 ≤ L s x)
    (B E : Finset V) (hE : E ⊆ B) (F : Ω → Finset V)
    (badSample : Ω → Prop) [DecidablePred badSample]
    {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 < δ)
    (hkeep : ∀ x ∈ B, x ∉ E → γ ≤
      μ.mean (fun s => L s x * (if x ∈ F s then (1 : ℝ) else 0)))
    (hstable : ∀ A : Finset V, A ⊆ B → δ ≤ A.card →
      (∑ x ∈ A, μ.mean (fun s => L s x * (if badSample s then (1 : ℝ) else 0))) / A.card ≤ γ / 2) :
    ∃ E' : Finset V, E' ⊆ B ∧ (E'.card : ℝ) < E.card + δ ∧
      ∀ x ∈ B, x ∉ E' → γ / 2 ≤ μ.mean (fun s =>
        L s x * (if x ∈ (if badSample s then ∅ else F s) then (1 : ℝ) else 0)) := by
  classical
  let loss (x : V) := μ.mean (fun s => L s x * (if badSample s then (1 : ℝ) else 0))
  let exceptions := B.filter (fun x => γ / 2 < loss x)
  have hOver : (exceptions.card : ℝ) < δ := by
    by_contra! h
    have hpos : (0 : ℝ) < exceptions.card := hδ.trans_le h
    have hne : exceptions.Nonempty := Finset.card_pos.mp (by exact_mod_cast hpos)
    have hx : ∀ x ∈ exceptions, γ / 2 < loss x := fun x hx => (Finset.mem_filter.mp hx).2
    have hlt : (exceptions.card : ℝ) * (γ / 2) < ∑ x ∈ exceptions, loss x := by
      simpa using Finset.sum_lt_sum_of_nonempty hne hx
    have hle := (div_le_iff₀ hpos).mp (hstable exceptions (Finset.filter_subset _ _) h)
    linarith only [hlt, hle]
  refine ⟨E ∪ exceptions, Finset.union_subset hE (Finset.filter_subset _ _), ?_, ?_⟩
  · have hcard : ((E ∪ exceptions).card : ℝ) ≤ (E.card : ℝ) + exceptions.card := by
      exact_mod_cast Finset.card_union_le E exceptions
    linarith only [hcard, hOver]
  · intro x hx hnot
    have hxE : x ∉ E := fun h => hnot (Finset.mem_union_left _ h)
    have hxOver : x ∉ exceptions := fun h => hnot (Finset.mem_union_right _ h)
    have hLoss : loss x ≤ γ / 2 :=
      le_of_not_gt fun hh => hxOver (Finset.mem_filter.mpr ⟨hx, hh⟩)
    have hPoint (s : Ω) :
        L s x * (if x ∈ F s then (1 : ℝ) else 0) ≤
          L s x * (if x ∈ (if badSample s then ∅ else F s) then (1 : ℝ) else 0) +
            L s x * (if badSample s then 1 else 0) := by
      by_cases hb : badSample s <;> by_cases hF : x ∈ F s <;> simp [hb, hF, hL s x]
    have hMean := μ.mean_mono hPoint
    rw [μ.mean_add] at hMean
    exact (show γ / 2 ≤ _ by
      linarith only [hkeep x hx hxE, hMean, hLoss])

/-- Combining the trimmed selection with independent repetitions gives
the expected weight of vertices selected too rarely. -/
theorem trimmed_selection_repeated_le
    (μ : FiniteLaw Ω) (L : Ω → V → ℝ) (hL : ∀ s x, 0 ≤ L s x)
    (B E : Finset V) (hE : E ⊆ B) (F : Ω → Finset V)
    (badSample : Ω → Prop) [DecidablePred badSample] {γ δ : ℝ} (hγ : 0 ≤ γ) (hδ : 0 < δ)
    (hm : ∀ x ∈ B, μ.mean (fun s => L s x) = 1)
    (hkeep : ∀ x ∈ B, x ∉ E → γ ≤ μ.mean (fun s => L s x * (if x ∈ F s then (1 : ℝ) else 0)))
    (hstable : ∀ A : Finset V, A ⊆ B → δ ≤ A.card →
      (∑ x ∈ A, μ.mean (fun s => L s x * (if badSample s then (1 : ℝ) else 0))) / A.card ≤ γ / 2)
    (q : ℕ) :
    let retained (s : Ω) := if badSample s then ∅ else F s
    (FiniteLaw.product (fun _ : Fin q => μ)).mean (fun ω =>
      (∑ x ∈ B, (∏ i, L (ω i) x) *
        (if ((Finset.univ.filter (fun i => x ∈ retained (ω i))).card : ℝ) < γ * q / 4
         then 1 else 0)) / B.card) ≤
      ((E.card : ℝ) + δ) / B.card + Real.exp (-(γ * q) / 16) := by
  intro retained
  obtain ⟨E', hE', hEcard, hFreq⟩ := exists_small_exception_for_trimmed_rule μ L hL B E hE F
    badSample hγ hδ hkeep hstable
  apply (mean_weight_too_few_retained_le μ B E' hE' L hL hm retained hγ hFreq).trans
  exact add_le_add_left (div_le_div_of_nonneg_right hEcard.le (Nat.cast_nonneg _)) _

end LocallyRamsey
