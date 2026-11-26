module

public import LocallyRamsey.Lower.SaturatingMixture

public section

open scoped BigOperators

namespace LocallyRamsey.FiniteLaw

variable {I Ω : Type*} [Fintype I] [Fintype Ω]

/-- The marginal of an experiment that first chooses an index and then
draws an outcome using the law specified by that index. -/
def mix (σ : FiniteLaw I) (ν : I → FiniteLaw Ω) : FiniteLaw Ω where
  prob s := ∑ i, σ.prob i * (ν i).prob s
  nonneg s := Finset.sum_nonneg fun i _ => mul_nonneg (σ.nonneg i) ((ν i).nonneg s)
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, fun i => (ν i).total, mul_one, σ.total]

theorem mix_mean (σ : FiniteLaw I) (ν : I → FiniteLaw Ω) (X : Ω → ℝ) :
    (σ.mix ν).mean X = σ.mean (fun i => (ν i).mean X) := by
  simp only [mix, mean, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem mix_event (σ : FiniteLaw I) (ν : I → FiniteLaw Ω) (P : Ω → Prop) :
    (σ.mix ν).event P = σ.mean (fun i => (ν i).event P) := by
  classical
  simp_rw [← mean_indicator]
  exact mix_mean σ ν _

/-- The law with one outcome of probability one. -/
@[expose] def single [DecidableEq Ω] (x : Ω) : FiniteLaw Ω where
  prob y := if x = y then 1 else 0
  nonneg y := by split <;> norm_num
  total := by simp

theorem single_mean [DecidableEq Ω] (x : Ω) (X : Ω → ℝ) :
    (single x).mean X = X x := by
  simp [single, mean, ite_mul]

theorem single_event [DecidableEq Ω] (x : Ω) (P : Ω → Prop) [DecidablePred P] :
    (single x).event P = if P x then 1 else 0 := by
  rw [← mean_indicator, single_mean]

end LocallyRamsey.FiniteLaw

namespace LocallyRamsey

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

/-- Marginals of a retention rule can be capped and equalized on all but
the allowed number of vertices. Each rule is applied to the original
sample, and the unused probability is assigned to the empty set. -/
theorem exists_capped_retention (μ : FiniteLaw Ω) (B : Finset V)
    (valid : Ω → Finset V → Prop) (hEmpty : ∀ ω, valid ω ∅)
    {t d : ℝ} (ht : 0 ≤ t) (hd : 0 < d) (cutoff stages : ℕ)
    (hcut : B.card / 2 ^ stages ≤ cutoff) (hcost : stages * (2 * t / d) ≤ 1)
    (available : ∀ A : Finset V, A ⊆ B → cutoff < A.card →
      ∃ ν : Ω → FiniteLaw (Finset V),
        (∀ ω F, 0 < (ν ω).prob F → F ⊆ A ∧ valid ω F) ∧
        d * A.card ≤ (μ.staged ν).mean (fun p => (p.2.card : ℝ))) :
    ∃ ν : Ω → FiniteLaw (Finset V),
      (∀ ω F, 0 < (ν ω).prob F → F ⊆ B ∧ valid ω F) ∧
      (∀ x ∈ B, (μ.staged ν).event (fun p => x ∈ p.2) ≤ t) ∧
      (B.filter (fun x => (μ.staged ν).event (fun p => x ∈ p.2) < t)).card ≤ cutoff := by
  classical
  let ok (A : Finset V) := A ⊆ B ∧ cutoff < A.card
  let ν (A : Finset V) : Ω → FiniteLaw (Finset V) :=
    if h : ok A then Classical.choose (available A h.1 h.2) else fun _ => FiniteLaw.single ∅
  have hs (A : Finset V) (h : ok A) :
      (∀ ω F, 0 < (ν A ω).prob F → F ⊆ A ∧ valid ω F) ∧
        d * A.card ≤ (μ.staged (ν A)).mean (fun p => (p.2.card : ℝ)) := by
    simpa only [ν, dite_eq_left h] using Classical.choose_spec (available A h.1 h.2)
  let f (A : Finset V) (x : V) := (μ.staged (ν A)).event (fun p => x ∈ p.2)
  have hf0 (A : Finset V) (x : V) : 0 ≤ f A x := FiniteLaw.event_nonneg _ _
  have havail (A : Finset V) (hAB : A ⊆ B) (hA : cutoff < A.card) :
      ∃ r, (∀ x ∈ B, x ∉ A → f r x = 0) ∧ d * A.card ≤ mass (f r) A := by
    have hs' := hs A ⟨hAB, hA⟩
    refine ⟨A, ?_, hs'.2.trans_eq ?_⟩
    · intro x _ hx
      dsimp [f]
      rw [← FiniteLaw.mean_indicator, FiniteLaw.mean]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hp : (μ.staged (ν A)).prob p = 0
      · simp [hp]
      · have hνp : 0 < (ν A p.1).prob p.2 := by
          by_contra! h
          exact hp (by simp only [FiniteLaw.staged, le_antisymm h ((ν A p.1).nonneg p.2), mul_zero])
        have hxp : x ∉ p.2 := fun h => hx ((hs'.1 p.1 p.2 hνp).1 h)
        simp [hxp]
    · have hsum : mass (f A) A = (μ.staged (ν A)).mean (fun p =>
          (∑ x ∈ A, if x ∈ p.2 then (1 : ℝ) else 0)) := by
        simp only [mass, f, FiniteLaw.mean_sum, FiniteLaw.mean_indicator]
      rw [hsum]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : (μ.staged (ν A)).prob p = 0
      · simp [FiniteLaw.mean, hp]
      · have hνp : 0 < (ν A p.1).prob p.2 := by
          by_contra! h
          exact hp (by simp only [FiniteLaw.staged, le_antisymm h ((ν A p.1).nonneg p.2), mul_zero])
        have hsub := (hs'.1 p.1 p.2 hνp).1
        simp [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]
  obtain ⟨a, ha, hmass, hcap, hactive⟩ :=
    exists_capped_mixture B f hf0 ht hd cutoff stages havail hcut hcost
  let α : FiniteLaw (Option (Finset V)) := {
    prob := fun r => r.elim (1 - ∑ A, a A) a
    nonneg := fun r => by cases r with
      | none => exact sub_nonneg.mpr hmass
      | some A => exact ha A
    total := by simp [Fintype.sum_option] }
  let rules (ω : Ω) (r : Option (Finset V)) :=
    r.elim (FiniteLaw.single ∅) (fun A => ν A ω)
  let final (ω : Ω) := α.mix (rules ω)
  have hevents (x : V) : (μ.staged final).event (fun p => x ∈ p.2) = mixtureWeight f a x := by
    rw [FiniteLaw.staged_event]
    simp_rw [final, FiniteLaw.mix_event]
    have hComm : μ.mean (fun ω => α.mean (fun r => (rules ω r).event (fun F => x ∈ F))) =
        α.mean (fun r => μ.mean (fun ω => (rules ω r).event (fun F => x ∈ F))) := by
      simp only [FiniteLaw.mean, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    rw [hComm, mixtureWeight]
    simp [FiniteLaw.mean, α, rules, Fintype.sum_option, FiniteLaw.single_event, f, FiniteLaw.staged_event]
  refine ⟨final, ?_, fun x hx => (hevents x).trans_le (hcap x hx), ?_⟩
  · intro ω F hF
    have he (r : Option (Finset V)) : 0 < (rules ω r).prob F → F ⊆ B ∧ valid ω F := by
      cases r with
      | none =>
        intro hp
        have hEq : F = ∅ := by
          by_contra h
          have h' := Ne.symm h
          simp [rules, FiniteLaw.single, h'] at hp
        subst F
        exact ⟨Finset.empty_subset _, hEmpty ω⟩
      | some A =>
        by_cases h : ok A
        · intro hp
          obtain ⟨hsub, hv⟩ := (hs A h).1 ω F hp
          exact ⟨hsub.trans h.1, hv⟩
        · intro hp
          have hEq : F = ∅ := by
            by_contra hh
            have hh' := Ne.symm hh
            simp [rules, ν, h, FiniteLaw.single, hh'] at hp
          subst F
          exact ⟨Finset.empty_subset _, hEmpty ω⟩
    by_contra h
    have hz (r : Option (Finset V)) : (rules ω r).prob F = 0 :=
      le_antisymm (le_of_not_gt (fun hp => h (he r hp))) ((rules ω r).nonneg F)
    simp [final, FiniteLaw.mix, hz] at hF
  · simpa only [hevents] using hactive

end LocallyRamsey
