module

public import LocallyRamsey.Overlap
public import LocallyRamsey.IndependentBlocks

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {S : J → Type*} [∀ j, Fintype (S j)]

/-- The average weight of the groups through one fixed sample position. -/
@[expose] noncomputable def avgGroupWeight (w : (j : J) → S j → V → ℝ) (ω : (j : J) → S j) (x : V) : ℝ :=
  (Fintype.card J : ℝ)⁻¹ * ∑ j, w j (ω j) x

omit [DecidableEq V] [DecidableEq J] [∀ j, Fintype (S j)] in
theorem mass_avgGroupWeight (w : (j : J) → S j → V → ℝ)
    (ω : (j : J) → S j) (A : Finset V) :
    mass (avgGroupWeight w ω) A = (Fintype.card J : ℝ)⁻¹ * ∑ j, mass (w j (ω j)) A := by
  simp only [mass, avgGroupWeight, ← Finset.mul_sum]
  rw [Finset.sum_comm]

/-- For a fixed partition and fixed shared data, exposing the first endpoint
group leaves independent contributions from the companion groups. The bound
charges only the weight of marked first vertices and therefore requires no
union bound over subsets of the vertex set. -/
theorem mean_marked_group_average_le (hJ : 0 < Fintype.card J) (μ : (j : J) → FiniteLaw (S j))
    (w : (j : J) → S j → V → ℝ) (B : Finset V)
    (hw : ∀ j s x, 0 ≤ w j s x)
    (hB : ∀ j s, mass (w j s) B ≤ 1)
    {D : ℝ} (hD : 0 < D) (hsize : (Fintype.card J : ℝ) - 1 ≤ D)
    (hmean : ∀ j x, x ∈ B → (∃ k a, 0 < w k a x) →
      (μ j).mean (fun s => mass (w j s) (closedNeighbors G B x)) ≤
        1 / (8 * D))
    (γ : ℝ) :
    (FiniteLaw.product μ).mean (fun ω =>
      mass (avgGroupWeight w ω) (marked G (avgGroupWeight w ω) B γ)) ≤
      Real.exp (1 / 8 - Real.log 2 * ((Fintype.card J : ℝ) * γ - 1)) := by
  classical
  let n : ℝ := Fintype.card J
  let bound := Real.exp (1 / 8 - Real.log 2 * (n * γ - 1))
  have hn : 0 < n := by
    change (0 : ℝ) < Fintype.card J
    exact_mod_cast hJ
  let H := fun ω => marked G (avgGroupWeight w ω) B γ
  have hmark (k : J) :
      (FiniteLaw.product μ).mean (fun ω => mass (w k (ω k)) (H ω)) ≤ bound := by
    let Others := {j : J // j ≠ k}
    let e := Equiv.piSplitAt k S
    let μ' := fun (j : Others) => μ j.val
    let A := fun (a : S k) (τ : (j : Others) → S j.val) => e.symm (a, τ)
    let X := fun x (j : Others) s => mass (w j.val s) (closedNeighbors G B x)
    have hsplit (ω : (j : J) → S j) : A (ω k) (fun j => ω j.val) = ω :=
      e.symm_apply_apply ω
    have heq (a : S k) (τ : (j : Others) → S j.val) :
        e (A a τ) = (a, τ) := e.apply_symm_apply _
    have hnow (a : S k) (τ : (j : Others) → S j.val) : A a τ k = a :=
      congrArg Prod.fst (heq a τ)
    have hfresh (a : S k) (τ : (j : Others) → S j.val) (j : Others) :
        A a τ j.val = τ j := congrArg (fun v => v.2 j) (heq a τ)
    have hcard : (Fintype.card Others : ℝ) ≤ D := by
      have hcard' : Fintype.card Others = Fintype.card J - 1 := by
        dsimp only [Others]
        rw [Fintype.card_subtype_compl (fun j => j = k), Fintype.card_subtype_eq]
      rw [hcard', Nat.cast_sub hJ]
      simpa using hsize
    have htail (a : S k) : (FiniteLaw.product μ').mean (fun τ =>
        mass (w k a) (H (A a τ))) ≤ bound := by
      refine mean_marked_endpoint_le μ' B (w k a) (hw k a) (hB k a) X
        (fun x _ j s => ⟨?_, ?_⟩) ?_ (fun τ => H (A a τ)) ?_ (n * γ) ?_
      · exact Finset.sum_nonneg fun y _ => hw j.val s y
      · exact (mass_mono (hw j.val s) (Finset.filter_subset _ _)).trans (hB j.val s)
      · intro x hx hpos
        calc
          _ ≤ ∑ _j : Others, 1 / (8 * D) :=
            Finset.sum_le_sum (fun j _ => hmean j.val x hx ⟨k, a, hpos⟩)
          _ ≤ 1 / 8 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            calc
              (Fintype.card Others : ℝ) * (1 / (8 * D)) ≤ D * (1 / (8 * D)) :=
                mul_le_mul_of_nonneg_right hcard (by positivity)
              _ = _ := by field_simp
      · intro τ x hx
        exact ((mem_marked G).mp hx).1
      · intro τ x hx
        have hm : γ < mass (avgGroupWeight w (A a τ)) (closedNeighbors G B x) :=
          ((mem_marked G).mp hx).2
        rw [mass_avgGroupWeight, inv_mul_eq_div, lt_div_iff₀ hn] at hm
        have hterms : (∑ j, mass (w j (A a τ j)) (closedNeighbors G B x)) =
            mass (w k a) (closedNeighbors G B x) + ∑ j : Others, X x j (τ j) := by
          rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k), hnow]
          congr 1
          rw [Finset.sum_subtype (p := fun j => j ≠ k) (Finset.univ.erase k) (by simp) (fun j =>
            mass (w j (A a τ j)) (closedNeighbors G B x))]
          exact Finset.sum_congr rfl (fun j _ => by simp only [X, hfresh])
        rw [hterms] at hm
        have hsub : closedNeighbors G B x ⊆ B := by
          change B.filter (fun y => x = y ∨ G.Adj x y) ⊆ B
          exact Finset.filter_subset _ _
        have hk := (mass_mono (hw k a) hsub).trans (hB k a)
        linarith only [hm, hk]
    calc
      _ = (FiniteLaw.product μ).mean (fun ω =>
        mass (w k (ω k)) (H (A (ω k) (fun j => ω j.val)))) := by simp only [hsplit]
      _ = ((μ k).staged (fun _ => FiniteLaw.product μ')).mean
          (fun s => mass (w k s.1) (H (A s.1 s.2))) :=
        FiniteLaw.mean_split_at μ k (fun s => mass (w k s.1) (H (A s.1 s.2)))
      _ ≤ bound := by
        rw [FiniteLaw.staged_mean, ← (μ k).mean_const bound]
        exact (μ k).mean_mono htail
  calc
    _ = n⁻¹ * ∑ k, (FiniteLaw.product μ).mean (fun ω => mass (w k (ω k)) (H ω)) := by
      change (FiniteLaw.product μ).mean (fun ω => mass (avgGroupWeight w ω) (H ω)) = _
      simp_rw [mass_avgGroupWeight]
      rw [FiniteLaw.mean_mul_const, FiniteLaw.mean_sum]
    _ ≤ n⁻¹ * ∑ _k : J, bound := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun k _ => hmark k) (by positivity)
    _ = bound := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change n⁻¹ * (n * bound) = bound
      field_simp

section RandomPartition

variable {I P : Type*} [Fintype I] [DecidableEq I] [Fintype P]
variable {U : I → Type*} [∀ i, Fintype (U i)]

/-- Conditional on the shared position and the other exposed data, the
remaining coordinates have a product law. A random partition groups them
into disjoint blocks. The fresh factors have mean one before the tests,
and imposing the tests can only reduce a group's weight. This yields one
exceptional event for the estimate on every subset (C). -/
theorem event_bad_marked_of_product_partition_le
    (hJ : 0 < Fintype.card J) (μ : (i : I) → FiniteLaw (U i)) (π : FiniteLaw P)
    (label : P → I → J) (B : Finset V)
    (w : (p : P) → (j : J) → FiniteLaw.Block (label p) j U → V → ℝ)
    (hw : ∀ p j ξ x, 0 ≤ w p j ξ x) (hB : ∀ p j ξ, mass (w p j ξ) B ≤ 1)
    (base : V → ℝ) (F : P → V → (i : I) → U i → ℝ)
    (hF : ∀ p x, x ∈ B → ∀ i, (μ i).mean (F p x i) = 1)
    (htest : ∀ p j ξ x, w p j ξ x ≤ base x *
      ∏ i : {i // label p i = j}, F p x i.val (ξ i))
    {D : ℝ} (hD : 0 < D) (hsize : (Fintype.card J : ℝ) - 1 ≤ D)
    (hbase : ∀ x ∈ B, (∃ p j ξ, 0 < w p j ξ x) →
      mass base (closedNeighbors G B x) ≤ 1 / (8 * D))
    {γ limit : ℝ} (hlimit : 0 < limit) :
    let avg (ω : (i : I) → U i) (p : P) := avgGroupWeight (w p) (fun _ i => ω i.val)
    (FiniteLaw.product μ).event (fun ω =>
      limit < π.mean (fun p => mass (avg ω p) (marked G (avg ω p) B γ))) ≤
    Real.exp (1 / 8 - Real.log 2 * ((Fintype.card J : ℝ) * γ - 1)) / limit := by
  classical
  intro avg
  let ν := FiniteLaw.product μ
  let Z := fun ω p => mass (avg ω p) (marked G (avg ω p) B γ)
  let bound := Real.exp (1 / 8 - Real.log 2 * ((Fintype.card J : ℝ) * γ - 1))
  have havg (ω : (i : I) → U i) (p : P) (x : V) : 0 ≤ avg ω p x := by
    dsimp [avg, avgGroupWeight]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => hw _ _ _ _)
  have hZ (p : P) : ν.mean (fun ω => Z ω p) ≤ bound := by
    have hblocks := FiniteLaw.mean_on_blocks μ (label p) (fun ξ =>
      mass (avgGroupWeight (w p) ξ) (marked G (avgGroupWeight (w p) ξ) B γ))
    change ν.mean (fun ω => Z ω p) = _ at hblocks
    rw [hblocks]
    refine mean_marked_group_average_le G hJ _ (w p) B (hw p) (hB p) hD hsize ?_ γ
    intro j x hx hpos
    have hsub : closedNeighbors G B x ⊆ B := Finset.filter_subset _ _
    refine (mean_companion_mass_le (fun i : {i // label p i = j} => μ i.val) base
      (fun y i s => F p y i.val s) (closedNeighbors G B x) (fun y hy i => hF p y (hsub hy) i.val)
      (w p j) (htest p j)).trans ?_
    obtain ⟨k, ξ, hξ⟩ := hpos
    exact hbase x hx ⟨p, k, ξ, hξ⟩
  have hmean : ν.mean (fun ω => π.mean (Z ω)) ≤ bound := by
    have hcomm : ν.mean (fun ω => π.mean (Z ω)) = π.mean (fun p => ν.mean (fun ω => Z ω p)) := by
      simp only [FiniteLaw.mean, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun ω _ => by ring))
    rw [hcomm, ← π.mean_const bound]
    exact π.mean_mono hZ
  have hnonneg (ω : (i : I) → U i) : 0 ≤ π.mean (Z ω) :=
    π.mean_nonneg fun p => Finset.sum_nonneg fun x _ => havg ω p x
  exact (ν.event_mono (fun _ h => h.le)).trans
    ((ν.event_ge_le hnonneg hlimit).trans (div_le_div_of_nonneg_right hmean hlimit.le))

/-- One exceptional marked set bounds all subsets simultaneously. -/
theorem event_bad_adjacent_of_product_partition_le
    (hJ : 0 < Fintype.card J) (μ : (i : I) → FiniteLaw (U i)) (π : FiniteLaw P)
    (label : P → I → J) (B : Finset V)
    (w : (p : P) → (j : J) → FiniteLaw.Block (label p) j U → V → ℝ)
    (hw : ∀ p j ξ x, 0 ≤ w p j ξ x) (hB : ∀ p j ξ, mass (w p j ξ) B ≤ 1)
    (base : V → ℝ) (F : V → (i : I) → U i → ℝ)
    (hF : ∀ x ∈ B, ∀ i, (μ i).mean (F x i) = 1)
    (htest : ∀ p j ξ x, w p j ξ x ≤ base x *
      ∏ i : {i // label p i = j}, F x i.val (ξ i))
    {D : ℝ} (hD : 0 < D) (hsize : (Fintype.card J : ℝ) - 1 ≤ D)
    (hbase : ∀ x ∈ B, (∃ p j ξ, 0 < w p j ξ x) →
      mass base (closedNeighbors G B x) ≤ 1 / (8 * D))
    {γ limit : ℝ} (hγ : 0 ≤ γ) (hlimit : 0 < limit) :
    let avg (ω : (i : I) → U i) (p : P) := avgGroupWeight (w p) (fun _ i => ω i.val)
    (FiniteLaw.product μ).event (fun ω => ∃ C, C ⊆ B ∧
      γ * π.mean (fun p => mass (avg ω p) C) + limit <
        π.mean (fun p => adjacentPairMass G (avg ω p) C)) ≤
    Real.exp (1 / 8 - Real.log 2 * ((Fintype.card J : ℝ) * γ - 1)) / limit := by
  classical
  intro avg
  refine ((FiniteLaw.product μ).event_mono ?_).trans
    (event_bad_marked_of_product_partition_le G hJ μ π label B w hw hB base (fun _ => F) (fun _ => hF) htest hD hsize hbase hlimit)
  rintro ω ⟨C, hCB, hbad⟩
  have havg (p : P) (x : V) : 0 ≤ avg ω p x := by
    dsimp [avg, avgGroupWeight]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => hw _ _ _ _)
  have havgB (p : P) : mass (avg ω p) B ≤ 1 := by
    change mass (avgGroupWeight (w p) (fun _ i => ω i.val)) B ≤ 1
    rw [mass_avgGroupWeight]
    have hh : (∑ j, mass (w p j (fun i => ω i.val)) B) ≤ Fintype.card J := by
      simpa using (Finset.sum_le_sum fun j (_ : j ∈ (Finset.univ : Finset J)) =>
        hB p j (fun i => ω i.val))
    rw [inv_mul_eq_div, div_le_iff₀ (by exact_mod_cast hJ), one_mul]
    exact hh
  exact lt_of_not_ge (fun hMark =>
    not_lt_of_ge (mean_adjacentPairMass_le G π (avg ω) B havg havgB hγ hMark C hCB) hbad)

end RandomPartition

end LocallyRamsey
