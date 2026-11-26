module

public import LocallyRamsey.FiniteProbability

public section

open scoped BigOperators

namespace LocallyRamsey

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem event_union_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.event (fun z => P z ∨ Q z) ≤ μ.event P + μ.event Q := by
  classical
  simp_rw [← μ.mean_indicator, ← μ.mean_add]
  exact μ.mean_mono fun z => by by_cases hP : P z <;> by_cases hQ : Q z <;> simp [hP, hQ]

theorem event_split_disjoint_le (μ : FiniteLaw Ω) {E P Q : Ω → Prop}
    (h : ∀ z, ¬(P z ∧ Q z)) :
    μ.event (fun z => E z ∧ P z) + μ.event (fun z => E z ∧ Q z) ≤ μ.event E := by
  classical
  simp_rw [← μ.mean_indicator, ← μ.mean_add]
  apply μ.mean_mono
  intro z
  by_cases hE : E z <;> by_cases hP : P z <;> by_cases hQ : Q z
  all_goals
    first | exact (h z ⟨hP, hQ⟩).elim | simp [hE, hP, hQ]

theorem event_le_mul_of_prob_le (μ ν : FiniteLaw Ω) (c : ℝ)
    (h : ∀ z, μ.prob z ≤ c * ν.prob z) (E : Ω → Prop) :
    μ.event E ≤ c * ν.event E := by
  classical
  simp_rw [← mean_indicator]
  simp only [mean, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have h' := mul_le_mul_of_nonneg_right (h z) (by split <;> norm_num :
    0 ≤ (if E z then (1 : ℝ) else 0))
  simpa [mul_assoc] using h'

end FiniteLaw

/-- An iteration of separating tests. At each failed step two disjoint
events are available, each recognized with high probability by a specified
fraction of the remaining vertices. The surviving event loses at least
half its mass at every step, but must still be visible from every surviving
vertex. A uniform bound on the likelihood ratio forces the process to stop. -/
theorem exists_stable_set_of_separating_tests {V Ω : Type*} [DecidableEq V] [Fintype Ω]
    (A : Finset V) (hA : A.Nonempty) (μ : FiniteLaw Ω) (R : V → FiniteLaw Ω)
    {c δ L : ℝ} (hc : 0 < c) (hc' : c ≤ 1) (_hδ : 0 ≤ δ) (hL₀ : 0 ≤ L)
    (hL : ∀ x ∈ A, ∀ z, (R x).prob z ≤ L * μ.prob z)
    (stable : Finset V → Prop)
    (hstep : ∀ B : Finset V, B ⊆ A → B.Nonempty → ¬ stable B →
      ∃ (B₁ B₂ : Finset V) (P Q : Ω → Prop),
        B₁ ⊆ B ∧ B₂ ⊆ B ∧ c * B.card ≤ B₁.card ∧ c * B.card ≤ B₂.card ∧
        (∀ z, ¬(P z ∧ Q z)) ∧
        (∀ x ∈ B₁, (R x).event (fun z => ¬ P z) ≤ δ) ∧
        (∀ x ∈ B₂, (R x).event (fun z => ¬ Q z) ≤ δ))
    (k : ℕ) (hstop : L * (1 / 2 : ℝ) ^ k < 1 - (k : ℝ) * δ) :
    ∃ B : Finset V, B ⊆ A ∧ c ^ k * (A.card : ℝ) ≤ B.card ∧ stable B := by
  classical
  by_contra! hbad
  have hA0 : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hrec (n : ℕ) (hn : n ≤ k) : ∃ B : Finset V, ∃ E : Ω → Prop,
      B ⊆ A ∧ c ^ n * (A.card : ℝ) ≤ B.card ∧
      μ.event E ≤ (1 / 2 : ℝ) ^ n ∧
      (∀ x ∈ B, (R x).event (fun z => ¬E z) ≤ (n : ℝ) * δ) := by
    induction n with
    | zero =>
      refine ⟨A, fun _ => True, Finset.Subset.refl A, by simp, ?_, ?_⟩
      · rw [← μ.mean_indicator]
        simp [FiniteLaw.mean_const]
      · intro x hx
        rw [← (R x).mean_indicator]
        simp [FiniteLaw.mean_const]
    | succ n ih =>
      obtain ⟨B, E, hBA, hB, hE, hEx⟩ := ih (by omega)
      have hBpos : (0 : ℝ) < B.card := (mul_pos (pow_pos hc n) hA0).trans_le hB
      have hBne : B.Nonempty := Finset.card_pos.mp (by exact_mod_cast hBpos)
      have hk : c ^ k * (A.card : ℝ) ≤ B.card :=
        (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc.le hc' (by omega)) hA0.le).trans hB
      obtain ⟨B₁, B₂, P, Q, hB₁, hB₂, hB₁card, hB₂card, hdisj, hP, hQ⟩ :=
        hstep B hBA hBne (hbad B hBA hk)
      have hsplit := μ.event_split_disjoint_le (E := E) hdisj
      have hhalf : μ.event (fun z => E z ∧ P z) ≤ μ.event E / 2 ∨
          μ.event (fun z => E z ∧ Q z) ≤ μ.event E / 2 := by
        by_contra! h
        linarith only [hsplit, h.1, h.2]
      have advance (B' : Finset V) (T : Ω → Prop) (hsub : B' ⊆ B)
          (hcard : c * (B.card : ℝ) ≤ B'.card)
          (htest : ∀ x ∈ B', (R x).event (fun z => ¬T z) ≤ δ)
          (hhalf : μ.event (fun z => E z ∧ T z) ≤ μ.event E / 2) :
          ∃ B' : Finset V, ∃ E' : Ω → Prop,
            B' ⊆ A ∧ c ^ (n + 1) * (A.card : ℝ) ≤ B'.card ∧
            μ.event E' ≤ (1 / 2 : ℝ) ^ (n + 1) ∧
            (∀ x ∈ B', (R x).event (fun z => ¬E' z) ≤ ((n + 1 : ℕ) : ℝ) * δ) := by
        refine ⟨B', fun z => E z ∧ T z, hsub.trans hBA, ?_, ?_, ?_⟩
        · rw [pow_succ', mul_assoc]
          exact (mul_le_mul_of_nonneg_left hB hc.le).trans hcard
        · rw [pow_succ]
          exact hhalf.trans (by linarith only [hE])
        · intro x hx
          simp only [not_and_or]
          have h := (R x).event_union_le (fun z => ¬ E z) (fun z => ¬ T z)
          have ht := (add_le_add (hEx x (hsub hx)) (htest x hx))
          push_cast
          linarith only [h, ht]
      exact hhalf.elim (advance B₁ P hB₁ hB₁card hP) (advance B₂ Q hB₂ hB₂card hQ)
  obtain ⟨B, E, hBA, hB, hE, hEx⟩ := hrec k le_rfl
  have hBpos : (0 : ℝ) < B.card := (mul_pos (pow_pos hc k) hA0).trans_le hB
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by exact_mod_cast hBpos)
  have ex := hEx x hx
  rw [(R x).event_not] at ex
  have hR := (R x).event_le_mul_of_prob_le μ L (hL x (hBA hx)) E
  have hcap := mul_le_mul_of_nonneg_left hE hL₀
  linarith only [hstop, ex, hR, hcap]

end LocallyRamsey
