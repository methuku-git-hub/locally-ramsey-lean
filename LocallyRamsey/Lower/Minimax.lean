module

public import LocallyRamsey.FiniteProbability
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order.Compact

public section

open scoped BigOperators

namespace LocallyRamsey

private theorem positive_part_sq_step (x y : ℝ) :
    max (x + y) 0 ^ 2 ≤ (max x 0) ^ 2 + 2 * max x 0 * y + y ^ 2 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx]
    by_cases hxy : 0 ≤ x + y
    · rw [max_eq_left hxy]
      ring_nf
      rfl
    · rw [max_eq_right (le_of_not_ge hxy)]
      nlinarith only [sq_nonneg (x + y)]
  · rw [max_eq_right (le_of_not_ge hx)]
    by_cases hxy : 0 ≤ x + y
    · rw [max_eq_left hxy]
      have hpow := pow_le_pow_left₀ hxy (show x + y ≤ y by linarith) 2
      simpa using hpow
    · rw [max_eq_right (le_of_not_ge hxy)]
      simpa using sq_nonneg y

/-- A compact convex set of payoff vectors with a coordinate above (d)
at every point admits one distribution of coordinates with mean above (d)
at every point. Minimize the sum of squared positive parts, then compare
along a line segment through the minimizer. -/
theorem exists_mixed_response {I : Type*} [Fintype I] {X : Set (I → ℝ)}
    (hX : IsCompact X) (hXnonempty : X.Nonempty) (hXconvex : Convex ℝ X)
    (d : ℝ) (hcoords : ∀ z ∈ X, ∃ i, d < z i) :
    ∃ μ : FiniteLaw I, ∀ z ∈ X, d < μ.mean z := by
  let F := fun z : I → ℝ => ∑ i, (max (z i - d) 0) ^ 2
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  obtain ⟨v, hv, hmin⟩ := hX.exists_isMinOn hXnonempty hF.continuousOn
  let w := fun i => max (v i - d) 0
  let W := ∑ i, w i
  have hw (i : I) : 0 ≤ w i := le_max_right _ _
  obtain ⟨k, hk⟩ := hcoords v hv
  have hwk : 0 < w k := (sub_pos.mpr hk).trans_le (le_max_left _ _)
  have hW : 0 < W := hwk.trans_le (Finset.single_le_sum
    (fun i _ => hw i) (Finset.mem_univ k))
  let μ : FiniteLaw I := {
    prob := fun i => w i / W
    nonneg := fun i => div_nonneg (hw i) hW.le
    total := by simp only [← Finset.sum_div, show (∑ i, w i) = W from rfl, div_self hW.ne']
  }
  have hdir (z : I → ℝ) (hz : z ∈ X) : 0 ≤ ∑ i, w i * (z i - v i) := by
    let L := ∑ i, w i * (z i - v i)
    let Q := ∑ i, (z i - v i) ^ 2
    change 0 ≤ L
    by_contra! hL
    have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => sq_nonneg _
    let t := min 1 (-L / (Q + 1))
    have ht : 0 < t := lt_min zero_lt_one (div_pos (neg_pos.mpr hL) (by linarith))
    have ht1 : t ≤ 1 := min_le_left _ _
    have htQ : t * (Q + 1) ≤ -L := (le_div_iff₀ (by linarith : 0 < Q + 1)).mp (min_le_right _ _)
    let y := (1 - t) • v + t • z
    have hy : y ∈ X := hXconvex hv hz (sub_nonneg.mpr ht1) ht.le (by ring)
    have hstep : F y ≤ F v + 2 * t * L + t ^ 2 * Q := by
      have hi (i : I) : y i - d = (v i - d) + t * (z i - v i) := by
        change (1 - t) * v i + t * z i - d = _
        ring
      calc
        _ ≤ ∑ i, (w i ^ 2 + 2 * t * (w i * (z i - v i)) + t ^ 2 * (z i - v i) ^ 2) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [hi]
          convert positive_part_sq_step (v i - d) (t * (z i - v i)) using 1
          dsimp [w]
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, F, w, L, Q]
    have hpress : 2 * L + t * Q < 0 := by nlinarith only [htQ, ht, hL]
    have hstrict : 2 * t * L + t ^ 2 * Q < 0 := by
      nlinarith only [mul_neg_of_pos_of_neg ht hpress]
    exact (not_lt_of_ge (hmin hy)) (hstep.trans_lt (by linarith))
  refine ⟨μ, fun z hz => ?_⟩
  have hpos : 0 < ∑ i, w i * (v i - d) := by
    have hs (i : I) : 0 ≤ w i * (v i - d) := by
      by_cases hi : 0 ≤ v i - d
      · exact mul_nonneg (hw i) hi
      · simp [w, max_eq_right (le_of_not_ge hi)]
    exact (mul_pos hwk (sub_pos.mpr hk)).trans_le (Finset.single_le_sum
      (fun i _ => hs i) (Finset.mem_univ k))
  have hsum : 0 < ∑ i, w i * (z i - d) := by
    have heq : (∑ i, w i * (z i - d)) = (∑ i, w i * (v i - d)) + ∑ i, w i * (z i - v i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [heq]
    exact add_pos_of_pos_of_nonneg hpos (hdir z hz)
  have hweighted : 0 < μ.mean (fun i => z i - d) := by
    change 0 < ∑ i, w i / W * (z i - d)
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
    exact div_pos hsum hW
  change 0 < μ.mean (fun i => z i + -d) at hweighted
  rw [μ.mean_add, μ.mean_const] at hweighted
  linarith

/-- Choose one distribution of responses against all distributions of
tests whose vertex marginals obey the specified caps. -/
theorem exists_common_response {I J V : Type*} [Fintype I] [Fintype J]
    (contains : V → J → Prop) [∀ x, DecidablePred (contains x)]
    (cap : V → ℝ) (payoff : I → J → ℝ) (d : ℝ)
    (hallowed : ∃ ν : FiniteLaw J, ∀ x, ν.event (contains x) ≤ cap x)
    (hresp : ∀ ν : FiniteLaw J, (∀ x, ν.event (contains x) ≤ cap x) →
      ∃ i, d < ν.mean (payoff i)) :
    ∃ μ : FiniteLaw I, ∀ ν : FiniteLaw J, (∀ x, ν.event (contains x) ≤ cap x) →
      d < μ.mean (fun i => ν.mean (payoff i)) := by
  let marginal (x : V) (p : J → ℝ) := ∑ j, p j * (if contains x j then (1 : ℝ) else 0)
  let D := stdSimplex ℝ J ∩ {p : J → ℝ | ∀ x, marginal x p ≤ cap x}
  let eval : (J → ℝ) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun p i => ∑ j, p j * payoff i j
      map_add' := by
        intro p q
        ext i
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t p
        ext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] }
  have hconv : Convex ℝ D := by
    refine (convex_stdSimplex ℝ J).inter ?_
    intro p hp q hq a b ha hb hab x
    change marginal x (a • p + b • q) ≤ cap x
    have heq : marginal x (a • p + b • q) = a * marginal x p + b * marginal x q := by
      simp only [marginal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        add_mul, Finset.sum_add_distrib, mul_assoc]
    rw [heq]
    have hBound := add_le_add (mul_le_mul_of_nonneg_left (hp x) ha)
      (mul_le_mul_of_nonneg_left (hq x) hb)
    rwa [← add_mul, hab, one_mul] at hBound
  have hcomp : IsCompact D := by
    apply (isCompact_stdSimplex ℝ J).inter_right
    rw [show {p : J → ℝ | ∀ x, marginal x p ≤ cap x} =
      ⋂ x, {p : J → ℝ | marginal x p ≤ cap x} by ext p; simp]
    apply isClosed_iInter
    intro x
    exact isClosed_le (by unfold marginal; fun_prop) continuous_const
  have hmem (ν : FiniteLaw J) (hν : ∀ x, ν.event (contains x) ≤ cap x) : ν.prob ∈ D := by
    refine ⟨⟨ν.nonneg, ν.total⟩, fun x => ?_⟩
    change ν.mean (fun j => if contains x j then 1 else 0) ≤ cap x
    rw [ν.mean_indicator]
    exact hν x
  have hcont : Continuous eval := by
    change Continuous (fun p : J → ℝ => fun i => ∑ j, p j * payoff i j)
    fun_prop
  obtain ⟨ν₀, hν₀⟩ := hallowed
  have hnonempty : D.Nonempty := ⟨ν₀.prob, hmem ν₀ hν₀⟩
  have hcoords (z : I → ℝ) (hz : z ∈ eval '' D) : ∃ i, d < z i := by
    obtain ⟨p, hp, rfl⟩ := hz
    have hpSimplex : p ∈ stdSimplex ℝ J := hp.1
    let ν : FiniteLaw J := ⟨p, hpSimplex.1, hpSimplex.2⟩
    have hν (x : V) : ν.event (contains x) ≤ cap x := by
      rw [← ν.mean_indicator]
      exact hp.2 x
    exact hresp ν hν
  obtain ⟨μ, hμ⟩ := exists_mixed_response (hcomp.image hcont)
    (hnonempty.image eval) (hconv.linear_image eval) d hcoords
  exact ⟨μ, fun ν hν => hμ (eval ν.prob) ⟨ν.prob, hmem ν hν, rfl⟩⟩

end LocallyRamsey
