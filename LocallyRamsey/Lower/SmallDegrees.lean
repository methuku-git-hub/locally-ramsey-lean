module

public import LocallyRamsey.Lower.CliqueSupply

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [LinearOrder V]

/-- A lower bound on the number of cliques forces a large set with small
maximum degree in the complementary graph. The same recording procedure
used for the sampling argument suffices: apply it with constant weights,
then count the clique descriptions that would be possible if every
returned set were small. -/
theorem exists_large_low_degree_complement
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj] (A : Finset V) {M r g : ℕ}
    (hG : IsLocallyRamsey G M r) (hr : 2 ≤ r) (hrM : r ≤ M)
    (hMA : M ≤ A.card) (hlarge : 2 * r ≤ A.card) (hM : M ≤ r ^ 6)
    {δ η D L : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) (hD : 1 < D)
    (hL : δ + η ≤ L * D * δ)
    (hg : g ≤ r) (hbudget : ⌈D * Real.log (1 + 1 / η)⌉₊ ≤ g)
    (hcount : ((g + 1 : ℕ) : ℝ) * δ ^ (r - g) < (1 / (r : ℝ) ^ 7) ^ r) :
    ∃ X : Finset V, X ⊆ A ∧ δ * A.card ≤ X.card ∧
      ∀ x ∈ X, ((neighborsIn Gᶜ X x).card : ℝ) ≤ L * X.card := by
  classical
  by_contra! hbad
  let w : V → ℝ := fun _ => 1
  let a : ℝ := A.card
  let Y := fun R : Finset V =>
    recordRemainder Gᶜ (chooseHeavy Gᶜ w (η * a) D) R A.card A
  have ha : 0 < a := by
    change (0 : ℝ) < A.card
    exact_mod_cast (show 0 < A.card by omega)
  have hone : 1 ≤ L * D := by
    by_contra! h
    linarith only [mul_lt_mul_of_pos_right h hδ, hL, hη]
  have hdesc (Q : Finset V) (hQ : Q ∈ cliquesIn G A r) :
      ∃ R : Finset V, R ⊆ Q ∧ R.card ≤ g ∧ Q \ R ⊆ Y R ∧ ((Y R).card : ℝ) ≤ δ * a := by
    obtain ⟨hQA, _, hQc⟩ := mem_cliquesIn.mp hQ
    have hQc' : Gᶜᶜ.IsClique (Q : Set V) := by simpa using hQc
    obtain ⟨R, hRQ, hRcard, hQF, hFA, hdeg⟩ :=
      weighted_recording Gᶜ w (by simp [w]) A Q hQA hQc' D η a hD hη (by simp [mass, w, a])
    let F := R ∪ Y R
    change Q ⊆ F at hQF
    change F ⊆ A at hFA
    change ∀ x ∈ F, mass w (neighborsIn Gᶜ F x) ≤ (mass w F + η * a) / D at hdeg
    have hsmall : (F.card : ℝ) < δ * a := by
      by_contra! hf
      obtain ⟨x, hxF, hx⟩ := hbad F hFA hf
      have hdx : ((neighborsIn Gᶜ F x).card : ℝ) ≤ ((F.card : ℝ) + η * a) / D := by
        simpa [mass, w] using hdeg x hxF
      have hscale : ((F.card : ℝ) + η * a) / D ≤ L * F.card := by
        apply (div_le_iff₀ (by linarith : 0 < D)).mpr
        have h₁ := mul_le_mul_of_nonneg_right hL ha.le
        have h₂ := mul_le_mul_of_nonneg_left hf (show 0 ≤ L * D - 1 by linarith)
        nlinarith only [h₁, h₂]
      exact (not_lt_of_ge (hdx.trans hscale)) hx
    have hYr : Y R ⊆ F := Finset.subset_union_right
    refine ⟨R, hRQ, hRcard.trans hbudget, ?_, (le_trans ?_ hsmall.le)⟩
    · intro z hz
      obtain ⟨hzQ, hzR⟩ := Finset.mem_sdiff.mp hz
      exact (Finset.mem_union.mp (hQF hzQ)).resolve_left hzR
    · exact_mod_cast Finset.card_le_card hYr
  have hlo := cliquesIn_lower hG hr hrM hMA hlarge hM
  have hhi := cliquesIn_upper_recorded Y (mul_nonneg hδ.le ha.le) hdesc
  have hp (j : ℕ) (hj : j ∈ Finset.range (g + 1)) :
      a ^ j * (δ * a) ^ (r - j) ≤ a ^ r * δ ^ (r - g) := by
    have hjg : j ≤ g := by have := Finset.mem_range.mp hj; omega
    rw [mul_pow, mul_left_comm, ← pow_add, Nat.add_sub_of_le (hjg.trans hg), mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hδ.le hδone (by omega)) (pow_nonneg ha.le _)
  have hhi' : ((cliquesIn G A r).card : ℝ) ≤ (g + 1 : ℕ) * (a ^ r * δ ^ (r - g)) := by
    refine hhi.trans ?_
    change ∑ j ∈ Finset.range (g + 1), a ^ j * (δ * a) ^ (r - j) ≤ _
    calc
      _ ≤ ∑ _j ∈ Finset.range (g + 1), a ^ r * δ ^ (r - g) := Finset.sum_le_sum hp
      _ = _ := by simp
  have hlt' : ((g + 1 : ℕ) : ℝ) * (a ^ r * δ ^ (r - g)) < (a / (r : ℝ) ^ 7) ^ r := by
    calc
      _ = a ^ r * (((g + 1 : ℕ) : ℝ) * δ ^ (r - g)) := by ring
      _ < a ^ r * (1 / (r : ℝ) ^ 7) ^ r := mul_lt_mul_of_pos_left hcount (pow_pos ha r)
      _ = _ := by rw [← mul_pow, mul_one_div]
  exact (not_lt_of_ge (hlo.trans hhi')) hlt'

end LocallyRamsey
