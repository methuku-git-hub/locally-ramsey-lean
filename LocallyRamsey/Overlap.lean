module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import LocallyRamsey.FiniteProbability
public import Mathlib.Tactic

public section

namespace LocallyRamsey

open scoped BigOperators

variable {V : Type*}

/-- A weight function on a finite set of vertices, summed over a subset. -/
@[expose] def mass (w : V → ℝ) (A : Finset V) : ℝ := ∑ x ∈ A, w x

theorem mass_mono {w : V → ℝ} (hw : ∀ x, 0 ≤ w x)
    {A B : Finset V} (hAB : A ⊆ B) : mass w A ≤ mass w B :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun x _ _ => hw x)

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Equal or adjacent second endpoints in the ambient set. -/
@[expose] def closedNeighbors (B : Finset V) (x : V) : Finset V :=
  B.filter (fun y => x = y ∨ G.Adj x y)

/-- Distinct nonadjacent second endpoints in the ambient set. -/
@[expose] def nonNeighbors (B : Finset V) (x : V) : Finset V :=
  B.filter (fun y => ¬(x = y ∨ G.Adj x y))

/-- The vertices whose closed neighbourhood in the whole ambient set has
weight larger than the specified cutoff. -/
noncomputable def marked (w : V → ℝ) (B : Finset V) (γ : ℝ) : Finset V :=
  B.filter (fun x => γ < mass w (closedNeighbors G B x))

theorem mem_marked {w : V → ℝ} {B : Finset V} {γ : ℝ} {x : V} :
    x ∈ marked G w B γ ↔ x ∈ B ∧ γ < mass w (closedNeighbors G B x) := by
  classical
  simp [marked]

/-- The weight of ordered equal or adjacent pairs with both endpoints in
the given set. -/
def adjacentPairMass (w : V → ℝ) (C : Finset V) : ℝ :=
  ∑ x ∈ C, w x * mass w (closedNeighbors G C x)

/-- The pointwise inequality used in Lemma 20. Its error depends on the
ambient set and weights, and simultaneously bounds every subset. -/
theorem adjacentPairMass_le {w : V → ℝ} (hw : ∀ x, 0 ≤ w x)
    {B : Finset V} (hB : mass w B ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∀ C : Finset V, C ⊆ B →
      adjacentPairMass G w C ≤ γ * mass w C + mass w (marked G w B γ) := by
  intro C hCB
  classical
  calc
    adjacentPairMass G w C ≤
        ∑ x ∈ C, (γ * w x + if x ∈ marked G w B γ then w x else 0) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hmarked : x ∈ marked G w B γ
      · have hsub : closedNeighbors G C x ⊆ B :=
          (Finset.filter_subset _ _).trans hCB
        have h := mul_le_mul_of_nonneg_left ((mass_mono hw hsub).trans hB) (hw x)
        simp only [hmarked, ite_true, mul_one] at h ⊢
        linarith [mul_nonneg hγ (hw x)]
      · have hcut : mass w (closedNeighbors G B x) ≤ γ := by
          by_contra! hlarge
          exact hmarked (Finset.mem_filter.mpr ⟨hCB hx, hlarge⟩)
        have hsub : closedNeighbors G C x ⊆ closedNeighbors G B x :=
          Finset.filter_subset_filter _ hCB
        simpa [hmarked, mul_comm] using
          mul_le_mul_of_nonneg_left ((mass_mono hw hsub).trans hcut) (hw x)
    _ = γ * mass w C + mass w (C ∩ marked G w B γ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      rw [← Finset.sum_filter]
      simp [mass, Finset.filter_mem_eq_inter]
    _ ≤ _ := add_le_add_right (mass_mono hw Finset.inter_subset_right) _

/-- The deterministic step is averaged only after the weights have been
fixed. A single mean bound on the marked mass controls all subsets of `B`. -/
theorem mean_adjacentPairMass_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (w : Ω → V → ℝ) (B : Finset V)
    (hw : ∀ ω x, 0 ≤ w ω x) (hB : ∀ ω, mass (w ω) B ≤ 1)
    {γ error : ℝ} (hγ : 0 ≤ γ)
    (herror : μ.mean (fun ω => mass (w ω) (marked G (w ω) B γ)) ≤ error) :
    ∀ C : Finset V, C ⊆ B →
      μ.mean (fun ω => adjacentPairMass G (w ω) C) ≤
        γ * μ.mean (fun ω => mass (w ω) C) + error := by
  intro C hCB
  calc
    _ ≤ μ.mean (fun ω => γ * mass (w ω) C + mass (w ω) (marked G (w ω) B γ)) :=
      μ.mean_mono fun ω => adjacentPairMass_le G (hw ω) (hB ω) hγ C hCB
    _ ≤ _ := by
      rw [μ.mean_add, μ.mean_mul_const]
      exact add_le_add_right herror _

omit [DecidableEq V] in
/-- A companion group's expected mass before the tests is its base
mass at the shared position. The fresh factors have mean one, and the
tests can only reduce the resulting weight. -/
theorem mean_companion_mass_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (μ : ∀ i, FiniteLaw (S i))
    (base : V → ℝ) (L : V → (i : ι) → S i → ℝ)
    (A : Finset V) (hone : ∀ x ∈ A, ∀ i, (μ i).mean (L x i) = 1) (w : ((i : ι) → S i) → V → ℝ)
    (htest : ∀ ω x, w ω x ≤ base x * ∏ i, L x i (ω i)) :
    (FiniteLaw.product μ).mean (fun ω => mass (w ω) A) ≤ mass base A := by
  let ν := FiniteLaw.product μ
  calc
    _ ≤ ν.mean (fun ω => ∑ x ∈ A, base x * ∏ i, L x i (ω i)) :=
      ν.mean_mono fun ω => Finset.sum_le_sum fun x _ => htest ω x
    _ = _ := by
      rw [ν.mean_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [ν.mean_mul_const, FiniteLaw.mean_product μ (L x)]
      simp [hone x hx]

/-- The endpoint group is exposed and its weights are fixed. The other
groups have independent contributions. If a vertex is marked, those groups
must supply at least the cut-off minus one. This bounds the exposed group's
expected weight on the marked set, with no choice of a subset of `B`. -/
theorem mean_marked_endpoint_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (μ : ∀ i, FiniteLaw (S i))
    (B : Finset V) (endpoint : V → ℝ) (hendpoint : ∀ x, 0 ≤ endpoint x)
    (htotal : mass endpoint B ≤ 1)
    (X : V → (i : ι) → S i → ℝ)
    (hX : ∀ x ∈ B, ∀ i ω, X x i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ x ∈ B, 0 < endpoint x → ∑ i, (μ i).mean (X x i) ≤ 1 / 8)
    (H : ((i : ι) → S i) → Finset V)
    (hH : ∀ ω, H ω ⊆ B) (cutoff : ℝ)
    (hmark : ∀ ω x, x ∈ H ω → cutoff - 1 ≤ ∑ i, X x i (ω i)) :
    (FiniteLaw.product μ).mean (fun ω => mass endpoint (H ω)) ≤
      Real.exp (1 / 8 - Real.log 2 * (cutoff - 1)) := by
  classical
  let ν := FiniteLaw.product μ
  let bound := Real.exp (1 / 8 - Real.log 2 * (cutoff - 1))
  have hhit (x : V) (hx : x ∈ B) (hpos : 0 < endpoint x) :
      ν.event (fun ω => x ∈ H ω) ≤ bound := by
    have ht : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc
      _ ≤ ν.event (fun ω => cutoff - 1 ≤ ∑ i, X x i (ω i)) :=
        ν.event_mono (fun ω => hmark ω x)
      _ ≤ Real.exp ((Real.exp (Real.log 2) - 1) * (∑ i, (μ i).mean (X x i)) -
          Real.log 2 * (cutoff - 1)) := by
        exact FiniteLaw.prob_sum_ge_le μ (X x) (hX x hx) ht _
      _ ≤ bound := by
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        apply Real.exp_le_exp.mpr
        linarith [hmean x hx hpos]
  have hmass (ω : (i : ι) → S i) :
      mass endpoint (H ω) = ∑ x ∈ B, endpoint x * (if x ∈ H ω then 1 else 0) := by
    have heq : B.filter (fun x => x ∈ H ω) = H ω := by
      ext x
      exact Finset.mem_filter.trans ⟨And.right, fun hx => ⟨hH ω hx, hx⟩⟩
    simp only [mass, mul_ite, mul_one, mul_zero, ← Finset.sum_filter, heq]
  calc
    _ = ∑ x ∈ B, endpoint x * ν.event (fun ω => x ∈ H ω) := by
      change ν.mean (fun ω => mass endpoint (H ω)) = _
      rw [funext hmass, ν.mean_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [ν.mean_mul_const, ν.mean_indicator]
    _ ≤ ∑ x ∈ B, endpoint x * bound :=
      Finset.sum_le_sum fun x hx => by
        by_cases hpos : 0 < endpoint x
        · exact mul_le_mul_of_nonneg_left (hhit x hx hpos) (hendpoint x)
        · rw [le_antisymm (le_of_not_gt hpos) (hendpoint x), zero_mul, zero_mul]
    _ = mass endpoint B * bound := by rw [← Finset.sum_mul, mass]
    _ ≤ bound := by
      simpa using mul_le_mul_of_nonneg_right htotal (Real.exp_pos _).le

/-- The same exceptional event controls all subsets at all positions and
descriptions. The index type enumerates the possible positions and
descriptions. The two probability laws distinguish the original data
from the random partition. -/
theorem event_exists_bad_overlap_le {Ω Ω' κ : Type*}
    [Fintype Ω] [Fintype Ω'] [Fintype κ]
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw Ω')
    (B : κ → Ω → Finset V) (w : κ → Ω × Ω' → V → ℝ)
    (hw : ∀ k s x, 0 ≤ w k s x) (hB : ∀ k ω ω', mass (w k (ω, ω')) (B k ω) ≤ 1)
    {γ bound limit : ℝ} (hγ : 0 ≤ γ) (hlimit : 0 < limit)
    (hmark : ∀ k, (μ.staged ν).mean (fun s => mass (w k s) (marked G (w k s) (B k s.1) γ)) ≤ bound) :
    μ.event (fun ω => ∃ k C, C ⊆ B k ω ∧
      γ * (ν ω).mean (fun ω' => mass (w k (ω, ω')) C) + limit <
        (ν ω).mean (fun ω' => adjacentPairMass G (w k (ω, ω')) C)) ≤
      (Fintype.card κ : ℝ) * (bound / limit) := by
  let X := fun k (s : Ω × Ω') => mass (w k s) (marked G (w k s) (B k s.1) γ)
  refine (μ.event_mono ?_).trans (μ.bad_inner_mean_le ν X hlimit ?_ hmark)
  · rintro ω ⟨k, C, hCB, hbad⟩
    refine ⟨k, lt_of_not_ge fun hmarkAvg => ?_⟩
    have hgood := mean_adjacentPairMass_le G (ν ω) (fun ω' => w k (ω, ω'))
      (B k ω) (fun ω' x => hw k (ω, ω') x) (hB k ω) hγ hmarkAvg C hCB
    exact (not_lt_of_ge hgood) hbad
  · intro k s
    exact Finset.sum_nonneg fun x _ => hw k s x

/-- The complementary weight counts precisely the ordered distinct nonadjacent pairs. -/
theorem pairMass_split (w : V → ℝ) (C : Finset V) :
    mass w C ^ 2 = adjacentPairMass G w C +
      ∑ x ∈ C, w x * mass w (nonNeighbors G C x) := by
  rw [pow_two]
  simp only [mass, adjacentPairMass, ← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← mul_add]
  congr 1
  exact (Finset.sum_filter_add_sum_filter_not C (fun y => x = y ∨ G.Adj x y) w).symm

/-- The quadratic estimate in Proposition 21, with the weights at one
position normalized by `ell`. -/
theorem position_mass_le {T γ δ v D ell : ℝ}
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hv : 0 ≤ v)
    (hD : 0 < D) (hell : 0 < ell)
    (h : T ^ 2 ≤ (γ + δ + 4 * v / (D * ell)) * T + δ ^ 2) :
    ell * T ≤ 4 * v / D + (γ + 2 * δ) * ell := by
  have hmul : 4 * v / (D * ell) * ell = 4 * v / D := by
    field_simp
  by_cases hsmall : T ≤ δ
  · have hv' : 0 ≤ 4 * v / D := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hell.le,
      mul_nonneg hγ hell.le, mul_nonneg hδ hell.le, hv']
  · have hbig : δ < T := lt_of_not_ge hsmall
    have hδsq : δ ^ 2 ≤ δ * T := by nlinarith only [mul_le_mul_of_nonneg_left hbig.le hδ]
    have hT' : T ≤ γ + 2 * δ + 4 * v / (D * ell) := by
      by_contra! hbad
      nlinarith only [h, hδsq, mul_pos (sub_pos.mpr hbad) (hδ.trans_lt hbig)]
    have hp := mul_le_mul_of_nonneg_right hT' hell.le
    rw [add_mul, hmul] at hp
    simpa only [mul_comm T ell, add_comm (_ * ell)] using hp

/-- The final estimate at a position. After bounding the marked mass,
the only extra input about `C` is the upper bound on its nonadjacent pairs. -/
theorem mean_position_mass_le {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (w : Ω → V → ℝ) (B C : Finset V) (hCB : C ⊆ B)
    (hw : ∀ ω x, 0 ≤ w ω x) (hB : ∀ ω, mass (w ω) B ≤ 1)
    {γ δ v D ell : ℝ}
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hv : 0 ≤ v) (hD : 0 < D) (hell : 0 < ell)
    (hmarked : μ.mean (fun ω => mass (w ω) (marked G (w ω) B γ)) ≤ δ ^ 2)
    (hnonadj : μ.mean (fun ω => ∑ x ∈ C, w ω x * mass (w ω) (nonNeighbors G C x)) ≤
      (δ + 4 * v / (D * ell)) * μ.mean (fun ω => mass (w ω) C)) :
    ell * μ.mean (fun ω => mass (w ω) C) ≤ 4 * v / D + (γ + 2 * δ) * ell := by
  apply position_mass_le hγ hδ hv hD hell
  calc
    _ ≤ μ.mean (fun ω => mass (w ω) C ^ 2) := μ.sq_mean_le_mean_sq _
    _ = μ.mean (fun ω => adjacentPairMass G (w ω) C) +
        μ.mean (fun ω => ∑ x ∈ C, w ω x * mass (w ω) (nonNeighbors G C x)) := by
      simp_rw [pairMass_split G, μ.mean_add]
    _ ≤ _ := by
      have hadj := mean_adjacentPairMass_le G μ w B hw hB hγ hmarked C hCB
      linarith

/-- Numerical contradiction from the overlap bounds at finite parameter
values. In the manuscript their final smallness condition holds asymptotically. -/
theorem overlap_bounds_incompatible {m v g γ D A : ℝ}
    (hg : 0 < g) (hgv : g ≤ v) (hγ : 0 < γ) (hD : 0 < D) (hA : 0 ≤ A)
    (hsmall : 4 / (D * γ) + A * γ / g < 1 / 9)
    (hlower : γ * v / 9 ≤ m) (hupper : m ≤ 4 * v / D + A * γ ^ 2) : False := by
  have hv : 0 < v := hg.trans_le hgv
  have hratio : (1 : ℝ) / 9 ≤ 4 / (D * γ) + A * γ / v := by
    have h := (div_le_div_iff_of_pos_right (mul_pos hγ hv)).2 (hlower.trans hupper)
    have hleft : (γ * v / 9) / (γ * v) = 1 / 9 := by field_simp
    have hright : (4 * v / D + A * γ ^ 2) / (γ * v) = 4 / (D * γ) + A * γ / v := by
      field_simp
    rw [hleft, hright] at h
    exact h
  have hdenom := div_le_div_of_nonneg_left (mul_nonneg hA hγ.le) hg hgv
  linarith

end LocallyRamsey
