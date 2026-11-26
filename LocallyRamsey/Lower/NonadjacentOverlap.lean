module

public import LocallyRamsey.Lower.PermutedGroups
public import LocallyRamsey.Lower.SampleOverlap

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V I : Type*} [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Averaging two groups drawn with replacement from an anchored
partition. The diagonal contributes (1/h). For distinct groups the
permutation makes the second one uniform among compatible companions,
so the same conditional mean bound applies at every first endpoint. -/
theorem mean_nonadjacent_pairs_perm_le {h : ℕ} (hh : 0 < h)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (blocks : Fin h → Finset I) (hdisj : Pairwise (fun a b => Disjoint (blocks a) (blocks b)))
    (k : ℕ) (hblock : ∀ j, (blocks j).card = k)
    (B C : Finset V) (hCB : C ⊆ B) (w : Finset I → V → ℝ)
    (hw : ∀ A x, 0 ≤ w A x)
    (htotal : ∀ A, A.card = k → mass (w A) B ≤ 1)
    {β : ℝ} (hβ : 0 ≤ β)
    (hcomp : ∀ A, A.card = k → ∀ x ∈ C,
      let companion := ((Finset.univ : Finset I).powersetCard k).filter (fun T => Disjoint A T)
      (∑ T ∈ companion, mass (w T) (nonNeighbors G C x)) ≤ β * companion.card) :
    let π := FiniteLaw.uniform (Equiv.Perm I)
    let avg (p : Equiv.Perm I) (x : V) :=
      (h : ℝ)⁻¹ * ∑ j, w ((blocks j).map p.toEmbedding) x
    π.mean (fun p => ∑ x ∈ C, avg p x * mass (avg p) (nonNeighbors G C x)) ≤
      ((h : ℝ)⁻¹ + β) * π.mean (fun p => mass (avg p) C) := by
  classical
  intro π avg
  let n : ℝ := h
  have hn : 0 < n := by
    change (0 : ℝ) < (h : ℝ)
    exact_mod_cast hh
  let W (p : Equiv.Perm I) (j : Fin h) := w ((blocks j).map p.toEmbedding)
  have hmass (p : Equiv.Perm I) (A : Finset V) :
      mass (avg p) A = n⁻¹ * ∑ j, mass (W p j) A := by
    simp only [mass, avg, ← Finset.mul_sum, W]
    rw [Finset.sum_comm]
  have hone (p : Equiv.Perm I) (j : Fin h) (x : V) :
      mass (W p j) (nonNeighbors G C x) ≤ 1 := by
    have hsubset : nonNeighbors G C x ⊆ B := (Finset.filter_subset _ _).trans hCB
    exact (mass_mono (hw _) hsubset).trans (htotal _ (by simp [hblock]))
  have hrow (x : V) (hx : x ∈ C) (j : Fin h) :
      (∑ l, π.mean (fun p => W p j x * mass (W p l) (nonNeighbors G C x))) ≤
        (1 + n * β) * π.mean (fun p => W p j x) := by
    have hdiag : π.mean (fun p => W p j x * mass (W p j) (nonNeighbors G C x)) ≤
        π.mean (fun p => W p j x) := by
      apply π.mean_mono
      intro p
      have hp := mul_le_mul_of_nonneg_left (hone p j x) (hw ((blocks j).map p.toEmbedding) x)
      simpa only [mul_one, W] using hp
    have hcompanion (l : Fin h) (hl : l ≠ j) :
        π.mean (fun p => W p j x * mass (W p l) (nonNeighbors G C x)) ≤
          β * π.mean (fun p => W p j x) := by
      refine mean_perm_disjoint_companion_le (blocks j) (blocks l) (hdisj hl.symm)
        (fun A => w A x) (fun T => mass (w T) (nonNeighbors G C x)) (fun A _ => hw A x) ?_
      intro A hA
      simpa only [hblock] using hcomp A (hA.trans (hblock j)) x hx
    have hsum :
        (∑ l ∈ (Finset.univ.erase j), π.mean (fun p => W p j x * mass (W p l) (nonNeighbors G C x))) ≤
          n * (β * π.mean (fun p => W p j x)) := by
      refine (Finset.sum_le_sum (fun l hl => hcompanion l (Finset.mem_erase.mp hl).1)).trans ?_
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.univ.erase j).card : ℝ) ≤ n := by
        change ((Finset.univ.erase j).card : ℝ) ≤ (h : ℝ)
        have hc' : (Finset.univ.erase j).card ≤ h :=
          (Finset.card_le_card (Finset.erase_subset j (Finset.univ : Finset (Fin h)))).trans_eq (by simp)
        exact_mod_cast hc' 
      exact mul_le_mul_of_nonneg_right hc (mul_nonneg hβ (π.mean_nonneg (fun _ => hw _ _)))
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
    nlinarith only [hdiag, hsum]
  have hterms (x : V) (p : Equiv.Perm I) :
      avg p x * mass (avg p) (nonNeighbors G C x) =
      n⁻¹ * n⁻¹ * ∑ j, ∑ l, W p j x * mass (W p l) (nonNeighbors G C x) := by
    rw [hmass]
    change (n⁻¹ * ∑ j, W p j x) * (n⁻¹ * ∑ l, mass (W p l) (nonNeighbors G C x)) = _
    calc
      _ = n⁻¹ * n⁻¹ * ((∑ j, W p j x) * (∑ l, mass (W p l) (nonNeighbors G C x))) := by ring
      _ = _ := by rw [Finset.sum_mul]; simp only [Finset.mul_sum]
  have rhs : ((h : ℝ)⁻¹ + β) * π.mean (fun p => mass (avg p) C) =
      ∑ x ∈ C, ((h : ℝ)⁻¹ + β) * π.mean (fun p => avg p x) := by
    unfold mass
    rw [π.mean_sum, Finset.mul_sum]
  rw [π.mean_sum, rhs]
  refine Finset.sum_le_sum (fun x hx => ?_)
  simp_rw [hterms, π.mean_mul_const, π.mean_sum]
  have hbound : ∑ j, ∑ l, π.mean (fun p => W p j x * mass (W p l) (nonNeighbors G C x)) ≤
      (1 + n * β) * ∑ j, π.mean (fun p => W p j x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hrow x hx j)
  refine (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq ?_
  have havg : π.mean (fun p => avg p x) = n⁻¹ * ∑ j, π.mean (fun p => W p j x) := by
    change π.mean (fun p => n⁻¹ * (∑ j, W p j x)) = _
    rw [π.mean_mul_const, π.mean_sum]
  rw [havg]
  field_simp
  <;> ring

end LocallyRamsey
