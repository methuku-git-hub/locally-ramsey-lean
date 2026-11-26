module

public import LocallyRamsey.Packing
public import LocallyRamsey.Lower.ListExtraction

public section

open scoped BigOperators

namespace LocallyRamsey

universe u

variable {V : Type u} [DecidableEq V]

/-- Pack admissible nonempty sets until the uncovered portion contains no
admissible set. -/
theorem exists_maximal_disjoint_packing (U : Finset V) (family : Finset V → Prop)
    (hne : ∀ P, family P → P.Nonempty) :
    ∃ packing : Finset (Finset V),
      (∀ P ∈ packing, P ⊆ U ∧ family P) ∧
      (packing : Set (Finset V)).Pairwise Disjoint ∧
      ∀ Q : Finset V, Q ⊆ U \ packing.biUnion id → ¬ family Q := by
  classical
  induction hcard : U.card using Nat.strong_induction_on generalizing U with
  | h n ih =>
    by_cases h : ∃ P : Finset V, P ⊆ U ∧ family P
    · obtain ⟨P, hPU, hP⟩ := h
      have ht : (U \ P).card < n := by
        rw [Finset.card_sdiff_of_subset hPU, hcard]
        have hp := Finset.card_pos.mpr (hne P hP)
        have hle := Finset.card_le_card hPU
        omega
      obtain ⟨packing, hall, hpair, hmax⟩ := ih _ ht (U \ P) rfl
      refine ⟨insert P packing, ?_, ?_, ?_⟩
      · intro Q hQ
        rcases Finset.mem_insert.mp hQ with rfl | hQ
        · exact ⟨hPU, hP⟩
        · exact ⟨(hall Q hQ).1.trans Finset.sdiff_subset, (hall Q hQ).2⟩
      · simp only [Finset.coe_insert, Set.pairwise_insert]
        refine ⟨hpair, fun Q hQ _ => ?_⟩
        have hDisj : Disjoint Q P := Finset.disjoint_left.mpr (fun _ hx hxP =>
          (Finset.mem_sdiff.mp ((hall Q hQ).1 hx)).2 hxP)
        exact ⟨hDisj.symm, hDisj⟩
      · intro Q hQU
        apply hmax Q
        intro x hx
        have hxU := hQU hx
        simp only [Finset.biUnion_insert, id_eq] at hxU
        obtain ⟨hxA, hxno⟩ := Finset.mem_sdiff.mp hxU
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxA, ?_⟩, ?_⟩
        · exact fun hxp => hxno (Finset.mem_union_left _ hxp)
        · exact fun hxr => hxno (Finset.mem_union_right _ hxr)
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro Q hQ hF
      exact h ⟨Q, hQ.trans Finset.sdiff_subset, hF⟩

/-- Under the uniform law on a pairwise disjoint packing, each vertex has
inclusion probability at most the reciprocal of the number of sets. -/
theorem uniform_packing_marginal_le (packing : Finset (Finset V)) (hne : packing.Nonempty)
    (hpair : (packing : Set (Finset V)).Pairwise Disjoint) (x : V) :
    letI : Nonempty ↥packing := hne.to_subtype
    (FiniteLaw.uniform ↥packing).event (fun P => x ∈ P.val) ≤ 1 / (packing.card : ℝ) := by
  let _ : Nonempty ↥packing := hne.to_subtype
  rw [FiniteLaw.uniform_event]
  simp only [Fintype.card_coe]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  apply Nat.cast_le_one.mpr
  apply Finset.card_le_one.mpr
  intro P hP Q hQ
  apply Subtype.ext
  by_contra h
  exact (Finset.disjoint_left.mp (hpair P.property Q.property h))
    (Finset.mem_filter.mp hP).2 (Finset.mem_filter.mp hQ).2

/-- If every allowable random test has mean payoff at least (d), all
low-payoff tests can be removed by deleting fewer than one quarter of the
vertices. Each test is a set of the same order. -/
theorem remove_bad_tests (U : Finset V) (hU : U.Nonempty) {b : ℕ} (hb : 0 < b)
    (test : Finset V → Prop) (payoff : Finset V → ℝ) (d : ℝ)
    (hmean : ∀ (I : Type u) [Fintype I] (μ : FiniteLaw I) (value : I → Finset V),
      (∀ i, value i ⊆ U ∧ (value i).card = b ∧ test (value i)) →
      (∀ x, μ.event (fun i => x ∈ value i) ≤ 4 * (b : ℝ) / U.card) →
      d ≤ μ.mean (fun i => payoff (value i))) :
    ∃ W : Finset V, W ⊆ U ∧ (3 / 4 : ℝ) * U.card ≤ W.card ∧
      ∀ P : Finset V, P ⊆ W → P.card = b → test P → d ≤ payoff P := by
  classical
  let bad := fun P : Finset V => P.card = b ∧ test P ∧ payoff P < d
  obtain ⟨packing, hpack, hpair, hmax⟩ := exists_maximal_disjoint_packing U bad
    (fun P h => Finset.card_pos.mp (h.1 ▸ hb))
  let A := packing.biUnion id
  have hAU : A ⊆ U := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx
    exact (hpack P hP).1 hxP
  have hcover : A.card = packing.card * b := by
    change (packing.biUnion (fun P => P)).card = _
    rw [Finset.card_biUnion hpair]
    trans ∑ _P ∈ packing, b
    · exact Finset.sum_congr rfl (fun P hP => (hpack P hP).2.1)
    · simp
  have hsmall : (A.card : ℝ) < (U.card : ℝ) / 4 := by
    by_contra! hbig
    have hcard : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
    have hp : packing.Nonempty := by
      apply Finset.card_pos.mp
      by_contra! h
      have h0 : packing.card = 0 := by omega
      rw [h0, zero_mul] at hcover
      rw [hcover, Nat.cast_zero] at hbig
      linarith
    let _ : Nonempty ↥packing := hp.to_subtype
    let μ := FiniteLaw.uniform ↥packing
    have hcap (x : V) : μ.event (fun i => x ∈ i.val) ≤ 4 * (b : ℝ) / U.card := by
      refine (uniform_packing_marginal_le packing hp hpair x).trans ?_
      have hp' : (0 : ℝ) < packing.card := by exact_mod_cast hp.card_pos
      rw [div_le_div_iff₀ hp' hcard, one_mul]
      rw [hcover, Nat.cast_mul] at hbig
      nlinarith only [hbig]
    have hlo := hmean ↥packing μ Subtype.val (fun i => ⟨(hpack _ i.property).1,
      (hpack _ i.property).2.1, (hpack _ i.property).2.2.1⟩) hcap
    have hhi : μ.mean (fun i => payoff i.val) < d := by
      have hμ (i : ↥packing) : 0 < μ.prob i := by
        change 0 < (Fintype.card ↥packing : ℝ)⁻¹
        positivity
      rw [← μ.mean_const d]
      exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ =>
        mul_lt_mul_of_pos_left (hpack _ i.property).2.2.2 (hμ i))
    exact (not_lt_of_ge hlo) hhi
  refine ⟨U \ A, Finset.sdiff_subset, ?_, ?_⟩
  · rw [Finset.card_sdiff_of_subset hAU, Nat.cast_sub (Finset.card_le_card hAU)]
    linarith only [hsmall]
  · intro P hP hPc hPt
    by_contra! h
    exact hmax P hP ⟨hPc, hPt, h⟩

end LocallyRamsey
