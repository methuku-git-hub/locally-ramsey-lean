module

public import LocallyRamsey.Lower.RetainedGroups
public import LocallyRamsey.Lower.OverlapIncidence
public import LocallyRamsey.Lower.DisjointSampleOverlap

public section

open scoped BigOperators Classical

namespace LocallyRamsey.RetainedGroups

variable {V I Ω : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype Ω]
variable (u : RetainedGroups V I Ω) {q h : ℕ}

/-- Weight retained at one position, normalized by the factor that
bounds its total mass in every group. -/
@[expose] noncomputable def normalized (i : I) (J : Finset I) : V → ℝ :=
  normalizedOverlap u.region (u.positionMass i) (16 * (u.positionMass i + u.quota))
    (u.kept J) (fun x => if x ∈ u.retained (u.outcome i) then u.weight J x else 0)

@[expose] noncomputable def meanAt (i : I)
    (blocks : Fin h → Finset ↥((Finset.univ : Finset I).erase i))
    (p : Equiv.Perm ↥((Finset.univ : Finset I).erase i)) (x : V) : ℝ :=
  (h : ℝ)⁻¹ * ∑ j, u.normalized i (restoreAnchor Finset.univ i ((blocks j).map p.toEmbedding)) x

/-- Both overlap bounds use the same retained mass. The pointwise
identity compares the order used to index positions in the short-record
argument with the order used in the anchor argument. -/
theorem sum_survivors_eq (J : PositionGroup I q) (C : Finset V)
    (hF : ∀ ω, u.retained ω ⊆ u.region) :
    (∑ i, mass (u.weight J.val) (C ∩ u.survivors J i)) =
      ∑ i ∈ J.val, if u.kept J.val ∧
          mass (u.weight J.val) (u.region ∩ u.retained (u.outcome i)) ≤ 16 * u.positionMass i
        then mass (u.weight J.val) (C ∩ u.retained (u.outcome i)) else 0 := by
  classical
  let X (i : I) := if u.kept J.val ∧
          mass (u.weight J.val) (u.region ∩ u.retained (u.outcome i)) ≤ 16 * u.positionMass i
        then mass (u.weight J.val) (C ∩ u.retained (u.outcome i)) else 0
  calc
    _ = ∑ i : Fin q, X (groupPosition J i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases h : u.kept J.val
      · have hw : u.weight J.val = u.rawWeight J.val := by funext x; simp [weight, h]
        have he := Finset.inter_eq_right.mpr (hF (u.outcome (groupPosition J i)))
        simp only [X, survivors, h, true_and, hw, he]
        split <;> simp_all [mass]
      · have hw : u.weight J.val = fun _ => 0 := by funext x; simp [weight, h]
        simp [X, h, hw, mass]
    _ = ∑ i ∈ J.val, X i := by
      let e := (Finset.equivFinOfCardEq (Finset.mem_powersetCard.mp J.property).2).symm
      exact (Fintype.sum_equiv e (fun i => X (e i).val) (fun i => X i.val) (fun _ => rfl)).trans
        (Finset.sum_coe_sort J.val X)
    _ = _ := rfl

/-- For a fixed experiment, the lower-overlap set cannot exist once the
marking and total weight estimates have been established. -/
theorem overlap_contradiction (G : SimpleGraph V) [DecidableRel G.Adj]
    (hq : 2 ≤ q) (hh : 0 < h) (hI : Fintype.card I = q * h)
    (hsize : ∀ i : I, 2 * (q - 1) * (q - 1) ≤ ((Finset.univ : Finset I).erase i).card)
    [Nonempty (PositionGroup I q)]
    (blocks : (i : I) → Fin h → Finset ↥((Finset.univ : Finset I).erase i))
    (hblock : ∀ i j, (blocks i j).card = q - 1)
    (hdisj : ∀ i, Pairwise (fun j l => Disjoint (blocks i j) (blocks i l)))
    (hF : ∀ ω, u.retained ω ⊆ u.region)
    (hL : ∀ ω x, 0 ≤ u.factor ω x) (hc : ∀ ω, 0 ≤ u.singleFactor ω)
    {D g A : ℝ} (hγ : 0 < u.quota) (hD : 0 < D) (hg : 0 < g) (hA : 0 ≤ A)
    (hhγ : (h : ℝ)⁻¹ ≤ u.quota) (hsmall : 4 / (D * u.quota) + (3 * A) * u.quota / g < 1 / 9)
    (hMean : (∑ i : I, 16 * (u.positionMass i + u.quota)) / Fintype.card I ≤ A * u.quota)
    (hMark : ∀ i, (FiniteLaw.uniform (Equiv.Perm ↥((Finset.univ : Finset I).erase i))).mean
      (fun p => mass (u.meanAt i (blocks i) p) (marked G (u.meanAt i (blocks i) p) u.region u.quota)) ≤
        ((h : ℝ)⁻¹) ^ 2)
    (C : Finset V) (hCB : C ⊆ u.region)
    {v : ℝ} (hv : g ≤ v)
    (hNon : ∀ x ∈ C, (FiniteLaw.uniform (PositionGroup I q)).mean
      (fun j => mass (u.weight j.val) (nonNeighbors G C x)) ≤ 2 * v / ((h : ℝ) * D))
    (hLower : u.quota * v / 9 ≤ (FiniteLaw.uniform (PositionGroup I q)).mean
      (fun j => (∑ i, mass (u.weight j.val) (C ∩ u.survivors j i)) / q)) : False := by
  classical
  let U := (Finset.univ : Finset I)
  have avg_eq (X : Finset I → ℝ) :
      (FiniteLaw.uniform (PositionGroup I q)).mean (fun j => X j.val) =
        (∑ J ∈ U.powersetCard q, X J) / (U.powersetCard q).card := by
    change ∑ j : PositionGroup I q, (Fintype.card (PositionGroup I q) : ℝ)⁻¹ * X j.val = _
    rw [← Finset.mul_sum, inv_mul_eq_div, Fintype.card_coe, Finset.sum_coe_sort]
  refine counted_overlap_impossible G U hq hh (by simpa [U]) (fun i => hsize i.val)
    (fun i => blocks i.val) (fun i j => hblock i.val j) (fun i => hdisj i.val)
    u.region C hCB u.kept u.weight (fun i => u.retained (u.outcome i)) (u.weight_nonneg hL)
    u.positionMass (fun i => div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hc _)) (Nat.cast_nonneg _))
    hγ hD hg hv hA hhγ (by simpa [U] using hMean)
    (fun x hx => by rw [← avg_eq]; exact hNon x hx) (fun i => hMark i.val) hsmall ?_
  simp_rw [u.sum_survivors_eq _ _ hF] at hLower
  let X (J : Finset I) := (∑ i ∈ J, if u.kept J ∧
        mass (u.weight J) (u.region ∩ u.retained (u.outcome i)) ≤ 16 * u.positionMass i
      then mass (u.weight J) (C ∩ u.retained (u.outcome i)) else 0) / q
  change _ ≤ (FiniteLaw.uniform (PositionGroup I q)).mean (fun j => X j.val) at hLower
  rw [avg_eq X] at hLower
  exact hLower

end LocallyRamsey.RetainedGroups
