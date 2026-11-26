module

public import LocallyRamsey.Lower.ParallelGroups
public import LocallyRamsey.Lower.PermutedGroups

public section

open scoped BigOperators

namespace LocallyRamsey

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

/-- Concentration of the mean of a score over all fixed-size groups, when
each score depends only on the samples in its group. A uniformly permuted
partition yields an unbiased copy of the group average. -/
theorem event_average_groups_gt_le (μ : FiniteLaw Ω) {q h : ℕ}
    (hh : 0 < h) (hsize : Fintype.card I = q * h)
    (X : Finset I → (I → Ω) → ℝ)
    (hlocal : ∀ J (u v : I → Ω), (∀ i ∈ J, u i = v i) → X J u = X J v)
    (hX : ∀ J u, J.card = q → X J u ∈ Set.Icc (0 : ℝ) 1)
    {z : ℝ} (hz : 0 ≤ z)
    (hmean : ∀ J, J.card = q → (FiniteLaw.product (fun _ : I => μ)).mean (X J) ≤ z / 4) :
    let groups := (Finset.univ : Finset I).powersetCard q
    (FiniteLaw.product (fun _ : I => μ)).event (fun u =>
      z < (∑ J ∈ groups, X J u) / groups.card) ≤ Real.exp (-((h : ℝ) * z) / 2) := by
  classical
  intro groups
  have hΩ : Nonempty Ω := by
    by_contra! h
    let _ : IsEmpty Ω := h
    simpa using μ.total
  let default := Classical.choice hΩ
  let e : Fin h × Fin q ≃ I := Fintype.equivOfCardEq (by simp [hsize, mul_comm])
  let block (j : Fin h) : Finset I := Finset.univ.map
    (⟨fun t => e (j, t), fun _ _ heq => congrArg Prod.snd (e.injective heq)⟩ : Fin q ↪ I)
  let σ := FiniteLaw.uniform (Equiv.Perm I)
  let label (p : Equiv.Perm I) (i : I) := (e.symm (p.symm i)).1
  let ordered (p : Equiv.Perm I) (j : Fin h) := (block j).map p.toEmbedding
  have hlabel (p : Equiv.Perm I) (j : Fin h) (i : I) :
      i ∈ ordered p j ↔ label p i = j := by
    constructor
    · intro hi
      obtain ⟨r, hr, rfl⟩ := Finset.mem_map.mp hi
      obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hr
      change (e.symm (p.symm (p (e (j, t))))).1 = j
      simp
    · intro hi
      let t := (e.symm (p.symm i)).2
      have he : e (j, t) = p.symm i := by
        apply e.symm.injective
        simp only [e.symm_apply_apply]
        exact Prod.ext hi.symm rfl
      exact Finset.mem_map.mpr ⟨e (j, t), Finset.mem_map.mpr ⟨t, Finset.mem_univ _, rfl⟩,
        by change p (e (j, t)) = i; rw [he, p.apply_symm_apply]⟩
  have hblock (j : Fin h) : (block j).card = q := by simp [block]
  have horder (p : Equiv.Perm I) (j : Fin h) : (ordered p j).card = q := by simp [ordered, hblock]
  let fill (p : Equiv.Perm I) (j : Fin h)
      (s : FiniteLaw.Block (label p) j (fun _ => Ω)) (i : I) :=
    if hi : label p i = j then s ⟨i, hi⟩ else default
  let score (p : Equiv.Perm I) (j : Fin h) (s : FiniteLaw.Block (label p) j (fun _ => Ω)) :=
    X (ordered p j) (fill p j s)
  have hscoreActual (p : Equiv.Perm I) (j : Fin h) (ω : I → Ω) :
      score p j (fun i => ω i.val) = X (ordered p j) ω := by
    apply hlocal
    intro i hi
    simp only [fill, dite_eq_left ((hlabel p j i).mp hi)]
  have hExp (p : Equiv.Perm I) (j : Fin h) :
      (FiniteLaw.product (fun _ : {i // label p i = j} => μ)).mean (score p j) ≤ z / 4 := by
    let laws := fun j : Fin h => FiniteLaw.product (fun _ : {i // label p i = j} => μ)
    have he := FiniteLaw.mean_on_blocks (fun _ : I => μ) (label p) (fun s => score p j (s j))
    rw [FiniteLaw.mean_coordinate laws j (score p j)] at he
    rw [← he]
    simpa only [hscoreActual] using hmean (ordered p j) (horder p j)
  have hAvg (ω : I → Ω) :
      σ.mean (fun p => ∑ j, score p j (fun i => ω i.val)) =
        h * ((∑ J ∈ groups, X J ω) / groups.card) := by
    rw [σ.mean_sum]
    have hAvg' (j : Fin h) :
        σ.mean (fun p => score p j (fun i => ω i.val)) =
          (∑ J ∈ groups, X J ω) / groups.card := by
      simp only [hscoreActual, ordered, σ]
      simpa only [hblock] using mean_uniform_perm_block (block j) (fun J => X J ω)
    rw [Finset.sum_congr rfl (fun j _ => hAvg' j)]
    simp
  have hp := FiniteLaw.event_group_average_gt_le (fun _ : I => μ) σ label score
    (fun p j s => hX (ordered p j) _ (horder p j)) hz hExp
  simp only [Fintype.card_fin] at hp
  refine ((FiniteLaw.product (fun _ : I => μ)).event_mono (fun ω hω => ?_)).trans hp
  rw [hAvg]
  exact mul_lt_mul_of_pos_left hω (by exact_mod_cast hh)

end LocallyRamsey
