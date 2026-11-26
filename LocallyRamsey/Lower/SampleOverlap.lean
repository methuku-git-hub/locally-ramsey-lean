module

public import LocallyRamsey.Lower.GroupOverlap
public import LocallyRamsey.Lower.Recording

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- The weight at the shared position, after its retained set (F) has
been exposed. In the sampling argument (c=1/(
ho(S)|B|)). -/
@[expose] def sharedWeight (F : Finset V) (c : ℝ) (x : V) : ℝ :=
  if x ∈ F then c else 0

/-- The normalized overlap at one position of a group. A group that fails
the eligibility or density test contributes zero. In a kept group the
position contributes only when its mass is at most (16z). -/
@[expose] noncomputable def normalizedOverlap (B : Finset V) (z ell : ℝ)
    (kept : Prop) (raw : V → ℝ) (x : V) : ℝ := by
  classical
  exact if kept ∧ mass raw B ≤ 16 * z then raw x / ell else 0

theorem mass_sharedWeight (F A : Finset V) (c : ℝ) :
    mass (sharedWeight F c) A = ((A ∩ F).card : ℝ) * c := by
  simp only [mass, sharedWeight, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.sum_const, nsmul_eq_mul]

/-- The closed neighbourhood costs the weight of the open neighbourhood
and the possible atom at the distinguished vertex. -/
theorem mass_shared_closed_neighbors_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (F B : Finset V) {x : V} {c : ℝ} (hc : 0 ≤ c) :
    mass (sharedWeight F c) (closedNeighbors G B x) ≤
      ((neighborsIn G F x).card : ℝ) * c + c := by
  classical
  have hsub : closedNeighbors G B x ∩ F ⊆ insert x (neighborsIn G F x) := by
    intro y hy
    obtain ⟨hyB, hyF⟩ := Finset.mem_inter.mp hy
    change y ∈ B.filter (fun y => x = y ∨ G.Adj x y) at hyB
    rcases (Finset.mem_filter.mp hyB).2 with heq | hadj
    · exact Finset.mem_insert.mpr (Or.inl heq.symm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨hyF, hadj⟩))
  have hcard : ((closedNeighbors G B x ∩ F).card : ℝ) ≤
      (neighborsIn G F x).card + 1 := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  rw [mass_sharedWeight]
  linarith only [mul_le_mul_of_nonneg_right hcard hc]

/-- The graph degree estimate in a retained set, together with the bound
on each atom, verifies the conditional moment hypothesis for all first
endpoints in that set. -/
theorem mass_normalized_closed_neighbors_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (F B : Finset V) {c γ D : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ) (hD : 0 < D)
    (hatom : c ≤ γ / D)
    (hdeg : ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) * c ≤
      (mass (sharedWeight F c) B + γ) / D) {x : V} (hx : x ∈ F) :
    mass (fun y => sharedWeight F c y / (16 * (mass (sharedWeight F c) B + γ)))
      (closedNeighbors G B x) ≤ 1 / (8 * D) := by
  have hz0 : 0 ≤ mass (sharedWeight F c) B := by
    rw [mass_sharedWeight]
    positivity
  let z := mass (sharedWeight F c) B
  let ell := 16 * (z + γ)
  have hell : 0 < ell := by dsimp [ell]; linarith
  have hclosed := mass_shared_closed_neighbors_le G F B (x := x) hc
  change mass (fun y => sharedWeight F c y / ell) (closedNeighbors G B x) ≤ _
  simp only [mass, ← Finset.sum_div]
  change mass (sharedWeight F c) (closedNeighbors G B x) / ell ≤ _
  have hraw : mass (sharedWeight F c) (closedNeighbors G B x) ≤ (z + γ) / D + (z + γ) / D := by
    have ha := div_le_div_of_nonneg_right (show γ ≤ z + γ by linarith) hD.le
    have hd := hdeg x hx
    change ((neighborsIn G F x).card : ℝ) * c ≤ (z + γ) / D at hd
    exact hclosed.trans (add_le_add hd (hatom.trans ha))
  refine (div_le_div_of_nonneg_right hraw hell.le).trans_eq ?_
  dsimp [ell]
  field_simp [hD.ne', (show z + γ ≠ 0 by linarith)]
  ring

/-- The one-endpoint estimate for the actual normalized and truncated
group weights, conditional on the exposed anchor sample and retained set.
The exceptional event ranges over all subsets of (B) at once. -/
theorem event_sample_overlap_bad_marked_le {I J P : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype P]
    {U : I → Type*} [∀ i, Fintype (U i)] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hJ : 0 < Fintype.card J) (μ : (i : I) → FiniteLaw (U i)) (π : FiniteLaw P)
    (label : P → I → J)
    (B F : Finset V)
    (kept : (p : P) → (j : J) → FiniteLaw.Block (label p) j U → Prop)
    (L : P → V → (i : I) → U i → ℝ) (hL : ∀ p x i s, 0 ≤ L p x i s)
    (hmean : ∀ p x, x ∈ B → ∀ i, (μ i).mean (L p x i) = 1)
    {c γ D limit : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ) (hD : 0 < D)
    (hsize : (Fintype.card J : ℝ) - 1 ≤ D) (hatom : c ≤ γ / D)
    (hdeg : ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) * c ≤
      (mass (sharedWeight F c) B + γ) / D)
    (hlimit : 0 < limit) :
    let z := mass (sharedWeight F c) B
    let w (p : P) (j : J) (b : FiniteLaw.Block (label p) j U) :=
      normalizedOverlap B z (16 * (z + γ)) (kept p j b) (fun x =>
        sharedWeight F c x * ∏ i : {i // label p i = j}, L p x i.val (b i))
    let avg (ω : (i : I) → U i) (p : P) := avgGroupWeight (w p) (fun _ i => ω i.val)
    (FiniteLaw.product μ).event (fun ω =>
      limit < π.mean (fun p => mass (avg ω p) (marked G (avg ω p) B γ))) ≤
      Real.exp (1 / 8 - Real.log 2 * ((Fintype.card J : ℝ) * γ - 1)) / limit := by
  classical
  intro z w avg
  let ell := 16 * (z + γ)
  let base (x : V) := sharedWeight F c x / ell
  have hz : 0 ≤ z := by dsimp [z]; rw [mass_sharedWeight]; positivity
  have hell : 0 < ell := by dsimp [ell]; linarith
  have hraw (p : P) (j : J) (b : FiniteLaw.Block (label p) j U) (x : V) :
      0 ≤ sharedWeight F c x * ∏ i : {i // label p i = j}, L p x i.val (b i) :=
    mul_nonneg (by simp only [sharedWeight]; split <;> positivity)
      (Finset.prod_nonneg (fun _ _ => hL _ _ _ _))
  refine event_bad_marked_of_product_partition_le G hJ μ π label B w ?_ ?_
    base L hmean ?_ hD hsize ?_ hlimit
  · intro p j b x
    dsimp [w, normalizedOverlap]
    split
    · exact div_nonneg (hraw p j b x) hell.le
    · exact le_rfl
  · intro p j b
    let raw (x : V) := sharedWeight F c x * ∏ i : {i // label p i = j}, L p x i.val (b i)
    have hwEq : w p j b = normalizedOverlap B z ell (kept p j b) raw := rfl
    rw [hwEq]
    by_cases hk : kept p j b ∧ mass raw B ≤ 16 * z
    · have heq : normalizedOverlap B z ell (kept p j b) raw = fun x => raw x / ell := by
        ext x
        simp only [normalizedOverlap, ite_eq_left hk]
      rw [heq]
      simp only [mass, ← Finset.sum_div]
      exact (div_le_one hell).mpr (hk.2.trans (by dsimp [ell]; linarith))
    · have heq : normalizedOverlap B z ell (kept p j b) raw = fun _ => 0 := by
        ext x
        simp only [normalizedOverlap, ite_eq_right hk]
      rw [heq]
      simp [mass]
  · intro p j b x
    dsimp [w, normalizedOverlap, base]
    split
    · dsimp only [ell]
      rw [div_mul_eq_mul_div]
    · exact mul_nonneg (by apply div_nonneg _ hell.le; simp only [sharedWeight]; split <;> positivity)
        (Finset.prod_nonneg fun _ _ => hL _ _ _ _)
  · rintro x _ ⟨p, j, b, hx⟩
    have hxF : x ∈ F := by
      by_contra h
      simp [w, normalizedOverlap, sharedWeight, h] at hx
    exact mass_normalized_closed_neighbors_le G F B hc hγ hD hatom hdeg hxF

end LocallyRamsey
