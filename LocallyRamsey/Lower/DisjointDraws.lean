module

public import LocallyRamsey.Lower.IndependentOrder
public import LocallyRamsey.IndependentBlocks

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω : Type*} [DecidableEq V] [Fintype Ω]

/-- Conditioning on the first of two distinct draws lets us apply a test
depending on its value to the second. -/
theorem event_pair_draw_le (μ : FiniteLaw Ω) {I : Type*} [Fintype I] [DecidableEq I]
    {i j : I} (hij : i ≠ j) (test : Ω → Ω → Prop) {c : ℝ}
    (h : ∀ x, μ.event (test x) ≤ c) :
    (FiniteLaw.product (fun _ : I => μ)).event (fun ω => test (ω i) (ω j)) ≤ c := by
  classical
  let j' : {k : I // k ≠ i} := ⟨j, hij.symm⟩
  let ν := FiniteLaw.product (fun _ : {k : I // k ≠ i} => μ)
  let f (s : Ω × ({k : I // k ≠ i} → Ω)) := if test s.1 (s.2 j') then (1 : ℝ) else 0
  rw [← FiniteLaw.mean_indicator]
  have hsplit := FiniteLaw.mean_split_at (S := fun _ : I => Ω) (fun _ => μ) i f
  change (FiniteLaw.product (fun _ : I => μ)).mean
    (fun ω => if test (ω i) (ω j) then 1 else 0) = (μ.staged (fun _ => ν)).mean f at hsplit
  rw [hsplit, FiniteLaw.staged_mean]
  have hmean (x : Ω) : ν.mean (fun ω => f (x, ω)) = μ.event (test x) :=
    (ν.mean_indicator (fun ω => test x (ω j'))).trans
      (FiniteLaw.event_coordinate (fun _ : {k : I // k ≠ i} => μ) j' (test x))
  simp_rw [hmean]
  exact (μ.mean_mono h).trans_eq (μ.mean_const c)

/-- Independently drawn sets fail to be pairwise disjoint with probability
at most (l^2 b p) when a set has at most (b) vertices and every marginal
inclusion probability is at most (p). -/
theorem event_intersecting_draws_le (μ : FiniteLaw Ω) (A : Ω → Finset V) (l b : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hsize : ∀ ω, (A ω).card ≤ b)
    (hmarginal : ∀ x, μ.event (fun ω => x ∈ A ω) ≤ p) :
    (FiniteLaw.product (fun _ : Fin l => μ)).event (fun ω =>
      ∃ i j, i ≠ j ∧ ¬ Disjoint (A (ω i)) (A (ω j))) ≤ (l : ℝ) ^ 2 * (b * p) := by
  classical
  let ν := FiniteLaw.product (fun _ : Fin l => μ)
  let test (d : Fin l × Fin l) (ω : Fin l → Ω) :=
    d.1 ≠ d.2 ∧ ¬ Disjoint (A (ω d.1)) (A (ω d.2))
  have hbound (B : Finset V) : μ.event (fun x => ¬ Disjoint B (A x)) ≤ (B.card : ℝ) * p := by
    refine (μ.event_mono (Q := fun ω => ∃ y : ↥B, y.val ∈ A ω) ?_).trans ?_
    · intro ω h
      obtain ⟨y, hy, hy'⟩ := Finset.not_disjoint_iff.mp h
      exact ⟨⟨y, hy⟩, hy'⟩
    · refine (μ.event_exists_le_sum (fun y : ↥B => fun ω => y.val ∈ A ω)).trans ?_
      calc
        _ ≤ ∑ _y : ↥B, p := Finset.sum_le_sum (fun y _ => hmarginal y.val)
        _ = _ := by simp
  have htest (d : Fin l × Fin l) : ν.event (test d) ≤ (b : ℝ) * p := by
    by_cases h : d.1 = d.2
    · rw [← ν.mean_indicator]
      simpa [test, h, ν.mean_const] using mul_nonneg (Nat.cast_nonneg b) hp
    · refine (ν.event_mono (fun _ ht => ht.2)).trans ?_
      exact event_pair_draw_le μ h (fun x y => ¬ Disjoint (A x) (A y)) (fun a =>
        (hbound (A a)).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsize a) hp))
  have hunion : ν.event (fun ω => ∃ i j, i ≠ j ∧ ¬ Disjoint (A (ω i)) (A (ω j))) ≤
      ∑ d, ν.event (test d) := by
    refine (ν.event_mono ?_).trans (ν.event_exists_le_sum test)
    rintro ω ⟨i, j, h⟩
    exact ⟨(i, j), h⟩
  exact hunion.trans ((Finset.sum_le_sum fun d _ => htest d).trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, pow_two]))

/-- A vertex of an independent set in disjoint unions comes from one draw.
If each draw is covered by (K) cliques, there are at most (K) vertices
assigned to any draw. -/
theorem exists_assignment_in_disjoint_draws {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (G : SimpleGraph V)
    (P : I → Finset V) (hdisj : Pairwise fun i j => Disjoint (P i) (P j))
    (K : I → J → Finset V) (hK : ∀ i j, G.IsClique (K i j : Set V))
    (hcover : ∀ i, P i ⊆ Finset.univ.biUnion (K i))
    {Q : Finset V} (hQ : Gᶜ.IsClique (Q : Set V))
    (hQsub : Q ⊆ Finset.univ.biUnion P) :
    ∃ assign : ↥Q → I, (∀ x, x.val ∈ P (assign x)) ∧
      (∀ x i, x.val ∈ P i → assign x = i) ∧
      ∀ i, (Finset.univ.filter (fun x => assign x = i)).card ≤ Fintype.card J := by
  classical
  have hf (x : ↥Q) : ∃ i, x.val ∈ P i := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hQsub x.property)
    exact ⟨i, hi⟩
  let assign := fun x => Classical.choose (hf x)
  have ha (x : ↥Q) : x.val ∈ P (assign x) := Classical.choose_spec (hf x)
  refine ⟨assign, ha, fun x i hx => ?_, fun i => ?_⟩
  · by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) (ha x) hx
  let cut := Finset.univ.filter (fun x => assign x = i)
  have hmap : cut.image Subtype.val ⊆ Q := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact a.property
  have hmap' : cut.image Subtype.val ⊆ P i := by
    intro x hx
    obtain ⟨a, haCut, rfl⟩ := Finset.mem_image.mp hx
    have hai : assign a = i := (Finset.mem_filter.mp haCut).2
    exact hai ▸ ha a
  have hc : Gᶜ.IsClique (↑(cut.image Subtype.val) : Set V) :=
    fun x hx y hy hxy => hQ (hmap hx) (hmap hy) hxy
  have hh := card_independent_le_clique_cover Finset.univ (K i) (fun j _ => hK i j)
    (cut.image Subtype.val) hc (hmap'.trans (hcover i))
  rwa [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ] at hh

end LocallyRamsey
