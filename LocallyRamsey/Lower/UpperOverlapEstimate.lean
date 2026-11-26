module

public import LocallyRamsey.Lower.AnchoredGroups
public import LocallyRamsey.Lower.NonadjacentOverlap

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- The upper overlap at one position, measured with uniform permutations
of the other positions. The weights at an anchored group are bounded by
the corresponding kept-group weights divided by the normalizing factor.
The nonadjacent pairs are controlled by conditioning companions to avoid
the first group's other positions. -/
theorem upper_overlap_at_anchor (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset I) {i : I} (hi : i ∈ U) {q h : ℕ} (hq : 2 ≤ q) (hh : 0 < h)
    (hU : U.card = q * h) (hsize : 2 * (q - 1) * (q - 1) ≤ (U.erase i).card)
    (blocks : Fin h → Finset ↥(U.erase i))
    (hdisj : Pairwise (fun j l => Disjoint (blocks j) (blocks l)))
    (hblock : ∀ j, (blocks j).card = q - 1)
    (B C : Finset V) (hCB : C ⊆ B)
    (raw normalized : Finset I → V → ℝ)
    (hraw : ∀ J x, 0 ≤ raw J x) (hnorm : ∀ J x, 0 ≤ normalized J x)
    {ell γ v D : ℝ} (hell : 0 < ell) (hγ : 0 ≤ γ) (hv : 0 ≤ v) (hD : 0 < D)
    (hpt : ∀ J x, normalized J x ≤ raw J x / ell)
    (htotal : ∀ J, J.card = q → mass (normalized J) B ≤ 1)
    (hNon : ∀ x ∈ C,
      (∑ J ∈ U.powersetCard q, mass (raw J) (nonNeighbors G C x)) / (U.powersetCard q).card ≤
        2 * v / ((h : ℝ) * D)) :
    let π := FiniteLaw.uniform (Equiv.Perm ↥(U.erase i))
    let avg (p : Equiv.Perm ↥(U.erase i)) (x : V) :=
      (h : ℝ)⁻¹ * ∑ j, normalized (restoreAnchor U i ((blocks j).map p.toEmbedding)) x
    π.mean (fun p => mass (avg p) (marked G (avg p) B γ)) ≤ ((h : ℝ)⁻¹) ^ 2 →
      ell * π.mean (fun p => mass (avg p) C) ≤ 4 * v / D + (γ + 2 * (h : ℝ)⁻¹) * ell := by
  classical
  intro π avg hmarked
  let w (A : Finset ↥(U.erase i)) := normalized (restoreAnchor U i A)
  let β := 4 * v / (D * ell)
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqU : q ≤ U.card := by rw [hU]; exact Nat.le_mul_of_pos_right _ hh
  have hw (A : Finset ↥(U.erase i)) (x : V) : 0 ≤ w A x := hnorm _ _
  have hmass (A : Finset ↥(U.erase i)) (hA : A.card = q - 1) : mass (w A) B ≤ 1 := by
    apply htotal
    rw [card_restoreAnchor, hA]
    omega
  have hcomp (A : Finset ↥(U.erase i)) (hA : A.card = q - 1) (x : V) (hx : x ∈ C) :
      let candidates := ((Finset.univ : Finset ↥(U.erase i)).powersetCard (q - 1)).filter
        (fun T => Disjoint A T)
      (∑ T ∈ candidates, mass (w T) (nonNeighbors G C x)) ≤ β * candidates.card := by
    intro candidates
    let F := nonNeighbors G C x
    by_cases hzero : candidates.card = 0
    · have he : candidates = ∅ := Finset.card_eq_zero.mp hzero
      simp [he]
    have hpos : (0 : ℝ) < candidates.card := by exact_mod_cast (Nat.pos_of_ne_zero hzero)
    apply (div_le_iff₀ hpos).mp
    let f (J : Finset I) := mass (normalized J) F
    have hf (J : Finset I) : 0 ≤ f J := Finset.sum_nonneg (fun x _ => hnorm J x)
    have hcomp := mean_restored_companions_le U hi q hq hqU A hA hsize f hf
    have hglobal :
        (∑ J ∈ U.powersetCard q, f J) / (U.powersetCard q).card ≤
          (2 * v / ((h : ℝ) * D)) / ell := by
      have hsum : (∑ J ∈ U.powersetCard q, f J) ≤
          (∑ J ∈ U.powersetCard q, mass (raw J) F) / ell := by
        refine (Finset.sum_le_sum (fun J _ => ?_)).trans_eq (Finset.sum_div _ _ _).symm
        simp only [f, mass, Finset.sum_div]
        exact Finset.sum_le_sum (fun y _ => hpt J y)
      refine (div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)).trans ?_
      rw [div_right_comm]
      exact div_le_div_of_nonneg_right (hNon x hx) hell.le
    have hFactor : 2 * (U.card : ℝ) / q = 2 * (h : ℝ) := by
      rw [hU, Nat.cast_mul]
      field_simp
    change (∑ T ∈ candidates, mass (w T) F) / candidates.card ≤ β
    refine hcomp.trans ?_
    rw [hFactor]
    refine (mul_le_mul_of_nonneg_left hglobal (by positivity)).trans_eq ?_
    dsimp only [β]
    field_simp
    ring
  have hpair := mean_nonadjacent_pairs_perm_le hh G blocks hdisj (q - 1) hblock B C hCB w hw
    hmass (β := β) (by positivity) hcomp
  have havg (p : Equiv.Perm ↥(U.erase i)) (x : V) : 0 ≤ avg p x :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => hnorm _ _))
  have havgB (p : Equiv.Perm ↥(U.erase i)) : mass (avg p) B ≤ 1 := by
    have heq : mass (avg p) B = (h : ℝ)⁻¹ *
        ∑ j, mass (w ((blocks j).map p.toEmbedding)) B := by
      simp only [mass, avg, ← Finset.mul_sum, w]
      rw [Finset.sum_comm]
    rw [heq, inv_mul_eq_div]
    apply (div_le_one hhr).mpr
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin h)))
        (fun j _ => hmass ((blocks j).map p.toEmbedding) (by simp [hblock]))
  exact mean_position_mass_le G π avg B C hCB havg havgB hγ (by positivity)
    hv hD hell hmarked hpair

end LocallyRamsey
