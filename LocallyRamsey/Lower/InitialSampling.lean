module

public import LocallyRamsey.Lower.RecoveringSample
public import LocallyRamsey.Lower.ListClasses
public import LocallyRamsey.Lower.Stabilization

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

open Classical

/-- The uniform probability of a property on a nonempty set of vertices. -/
theorem uniform_vertex_event (A : Finset V) (hA : A.Nonempty) (p : V → Prop)
    [DecidablePred p] :
    letI : Nonempty ↥A := hA.to_subtype
    (FiniteLaw.uniform ↥A).event (fun x => p x.val) =
      ((A.filter p).card : ℝ) / A.card := by
  classical
  let _ : Nonempty ↥A := hA.to_subtype
  rw [FiniteLaw.uniform_event]
  simp only [Fintype.card_coe]
  congr 2
  let B : Finset ↥A := Finset.univ.filter (fun x => p x.val)
  have heq : B.image Subtype.val = A.filter p := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨y.property, (Finset.mem_filter.mp hy).2⟩
    · intro hx
      obtain ⟨hxA, hxp⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_image.mpr ⟨⟨x, hxA⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxp⟩, rfl⟩
  exact (Finset.card_image_of_injective B Subtype.val_injective).symm.trans
    (congrArg Finset.card heq)

/-- Good outcomes of the list-and-unions experiment give the independent
set and the short record used to recover a small test set. -/
theorem initial_record_from_good_draws {G : SimpleGraph V} (U W : Finset V)
    (hU : U.Nonempty) (hWU : W ⊆ U)
    {m s l K b r M cap limit : ℕ} (hr : 0 < r)
    (L : Fin m → ↥U) (P : Fin l → Finset V)
    (clique : Fin l → Fin K → Finset V)
    (hP : ∀ j, P j ⊆ W)
    (hPcard : ∀ j, (P j).card = K * b)
    (hCl : ∀ j k, G.IsClique (clique j k : Set V))
    (hCover : ∀ j, P j ⊆ Finset.univ.biUnion (clique j))
    (hDisj : Pairwise fun i j => Disjoint (P i) (P j))
    (hLarge : M ≤ l * (K * b))
    (hRamsey : ∀ A : Finset V, A ⊆ U → M ≤ A.card →
      ∃ Q : Finset V, Q ⊆ A ∧ Q.card = r ∧ Gᶜ.IsClique (Q : Set V))
    (hDeg : ∀ (j : Fin m),
      (∑ a : Fin l, ((Finset.univ : Finset (Fin K)).filter
        (fun k => ∃ x ∈ clique a k, Gᶜ.Adj (L j).val x)).card) ≤ cap)
    (hCollision : (s : ℝ) ^ 2 * ((K : ℝ) / r) ≤ 1 / 2)
    (hSmall : (m : ℝ) * ((cap : ℝ) / r) ^ s < ((limit : ℝ) / U.card) * m / 4)
    (hList : letI : Nonempty ↥U := hU.to_subtype
      ∀ (f : Fin s → Fin l) (v : Fin s → V), Function.Injective f →
        (∀ k, v k ∈ P (f k)) →
        ((limit : ℝ) / U.card) ≤ (FiniteLaw.uniform ↥U).event
          (fun y => ∀ k, Gᶜ.Adj y.val (v k)) →
        ((limit : ℝ) / U.card) * m / 2 ≤
          listCommonCount (fun (y : ↥U) x => Gᶜ.Adj y.val x) L v) :
    ∃ (Q : Finset V) (f : Fin s → Fin l) (v : Fin s → V),
      Q ⊆ W ∧ Q ⊆ Finset.univ.biUnion P ∧ Gᶜ.IsClique (Q : Set V) ∧
      r ≤ Q.card ∧ (∀ j, v j ∈ Q ∧ v j ∈ P (f j)) ∧
      (commonNeighborsIn Gᶜ W (Finset.univ.image v)).card ≤ limit := by
  let A := Finset.univ.biUnion P
  have hAW : A ⊆ W := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    exact hP j hj
  have hCard : A.card = l * (K * b) := by
    rw [Finset.card_biUnion (fun a _ b _ h => hDisj h)]
    simp [hPcard]
  obtain ⟨Q, hQA, hQcard, hQcl⟩ := hRamsey A (hAW.trans hWU) (hCard ▸ hLarge)
  obtain ⟨assign, hAssign, _, hCount⟩ :=
    exists_assignment_in_disjoint_draws G P hDisj clique hCl hCover hQcl hQA
  have hQ : Q.Nonempty := Finset.card_pos.mp (hQcard ▸ hr)
  let _ : Nonempty ↥Q := hQ.to_subtype
  let _ : Nonempty ↥U := hU.to_subtype
  let H (y : ↥U) (x : V) := Gᶜ.Adj y.val x
  have hAssignCap (x : ↥Q) : (FiniteLaw.uniform ↥Q).event (fun y => assign x = assign y) ≤
      (K : ℝ) / r := by
    rw [FiniteLaw.uniform_event, Fintype.card_coe, hQcard]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h : (Finset.univ.filter (fun y : ↥Q => assign x = assign y)).card =
        (Finset.univ.filter (fun y : ↥Q => assign y = assign x)).card := by
      congr 1
      ext y
      simp [eq_comm]
    rw [h]
    exact_mod_cast (hCount (assign x)).trans_eq (Fintype.card_fin K)
  have hDegQ (j : Fin m) : (FiniteLaw.uniform ↥Q).event (fun x => H (L j) x.val) ≤
      (cap : ℝ) / r := by
    rw [uniform_vertex_event Q hQ, hQcard]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    let tests (i : Fin l) := (Finset.univ : Finset (Fin K)).filter
      (fun k => ∃ x ∈ clique i k, Gᶜ.Adj (L j).val x)
    let nbr := Q.filter (H (L j))
    have hcover : nbr ⊆ Finset.univ.biUnion (fun i => (tests i).biUnion (clique i)) := by
      intro x hx
      obtain ⟨hxQ, hAdj⟩ := Finset.mem_filter.mp hx
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hQA hxQ)
      obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp (hCover i hi)
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hk, hAdj⟩, hk⟩⟩
    have hcover' : nbr ⊆ Finset.univ.biUnion (fun i => (tests i).biUnion
        (fun k => nbr ∩ clique i k)) := by
      intro x hx
      obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hcover hx)
      obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hxi
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_biUnion.mpr
        ⟨k, hk, Finset.mem_inter.mpr ⟨hx, hxk⟩⟩⟩
    have hSubcl : Gᶜ.IsClique (nbr : Set V) := fun x hx y hy hxy =>
      hQcl (Finset.filter_subset _ _ hx) (Finset.filter_subset _ _ hy) hxy
    have ht (i : Fin l) : ((tests i).biUnion (fun k => nbr ∩ clique i k)).card ≤ (tests i).card := by
      refine Finset.card_biUnion_le.trans ?_
      calc
        _ ≤ ∑ _k ∈ tests i, (1 : ℕ) :=
          Finset.sum_le_sum (fun k _ => by
            rw [Finset.inter_comm]
            exact card_inter_le_one_of_cliques (hCl i k) hSubcl)
        _ = _ := by simp
    have hCardN : nbr.card ≤ cap := ((Finset.card_le_card hcover').trans
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun i _ => ht i))).trans (hDeg j)
    exact_mod_cast hCardN
  obtain ⟨q, _, hsmall⟩ := exists_small_common_with_distinct_draws
    (FiniteLaw.uniform ↥U) (FiniteLaw.uniform ↥Q) Subtype.val assign H L
    (fun i x => x ∈ P i) hAssign (by positivity) (by positivity) (by positivity)
    hAssignCap hCollision hDegQ hSmall hList
  let v : Fin s → V := fun k => (q k).val
  let R := Finset.univ.image v
  refine ⟨Q, assign ∘ q, v, hQA.trans hAW, hQA, hQcl, hQcard.ge, fun j =>
    ⟨(q j).property, hAssign (q j)⟩, ?_⟩
  change (FiniteLaw.uniform ↥U).event (fun y => ∀ k, Gᶜ.Adj y.val (v k)) < _ at hsmall
  rw [uniform_vertex_event U hU (fun y : V => ∀ k, Gᶜ.Adj y (v k))] at hsmall
  have hUpos : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hlt := (div_lt_div_iff_of_pos_right hUpos).mp hsmall
  have hsub : commonNeighborsIn Gᶜ W R ⊆ U.filter (fun y => ∀ k, Gᶜ.Adj (v k) y) := by
    intro y hy
    obtain ⟨hyW, hyR⟩ := mem_commonNeighborsIn.mp hy
    exact Finset.mem_filter.mpr ⟨hWU hyW, fun k =>
      hyR (v k) (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)⟩
  have heq : (U.filter (fun y => ∀ k, Gᶜ.Adj (v k) y)) =
      U.filter (fun y => ∀ k, Gᶜ.Adj y (v k)) := by
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, fun k => (h.2 k).symm⟩,
      fun h => ⟨h.1, fun k => (h.2 k).symm⟩⟩
  rw [heq] at hsub
  have hle : (commonNeighborsIn Gᶜ W R).card ≤
      (U.filter (fun y => ∀ k, Gᶜ.Adj y (v k))).card := Finset.card_le_card hsub
  have hlt' : (U.filter (fun y => ∀ k, Gᶜ.Adj y (v k))).card < limit := by
    change (((U.filter (fun y => ∀ k, Gᶜ.Adj y (v k))).card : ℕ) : ℝ) < limit at hlt
    exact_mod_cast hlt
  exact hle.trans hlt'.le


/-- A union of disjoint cliques that agree within each clique on a test
has exactly one clique hit per (b) vertices that pass the test. -/
theorem card_homogeneous_cliques_hit {K b : ℕ} (C : Fin K → Finset V)
    (hCard : ∀ k, (C k).card = b) (hDisj : Pairwise fun i j => Disjoint (C i) (C j))
    (test : V → Prop) [DecidablePred test]
    (hSame : ∀ k x y, x ∈ C k → y ∈ C k → (test x ↔ test y)) :
    ((Finset.univ.biUnion C).filter test).card =
      ((Finset.univ : Finset (Fin K)).filter (fun k => ∃ x ∈ C k, test x)).card * b := by
  let hit := (Finset.univ : Finset (Fin K)).filter (fun k => ∃ x ∈ C k, test x)
  have heq : (Finset.univ.biUnion C).filter test = hit.biUnion C := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hx).1
      exact Finset.mem_biUnion.mpr ⟨k,
        Finset.mem_filter.mpr ⟨hk, x, hxk, (Finset.mem_filter.mp hx).2⟩, hxk⟩
    · intro hx
      obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨y, hyk, hy⟩ := (Finset.mem_filter.mp hk).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hxk⟩,
        (hSame k y x hyk hxk).mp hy⟩
  rw [heq, Finset.card_biUnion (fun _ _ _ _ h => hDisj h)]
  simp only [hCard, Finset.sum_const, Nat.nsmul_eq_mul]
  congr 2

/-- For one fixed list entry, independent unions of disjoint homogeneous
cliques hit its neighbours in few cliques. The number of such cliques is
the number of sampled neighbours divided by the clique size. -/
theorem event_many_cliques_hit_le {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    {K b l cap : ℕ} (hK : 0 < K) (hb : 0 < b)
    (C : Ω → Fin K → Finset V) (hCard : ∀ ω k, (C ω k).card = b)
    (hDisj : ∀ ω, Pairwise fun i j => Disjoint (C ω i) (C ω j))
    (test : V → Prop) [DecidablePred test]
    (hSame : ∀ ω k x y, x ∈ C ω k → y ∈ C ω k → (test x ↔ test y))
    (N : Finset V) (hN : ∀ ω x, x ∈ Finset.univ.biUnion (C ω) → test x → x ∈ N)
    {p : ℝ} (hMarginal : ∀ x ∈ N,
      μ.event (fun ω => x ∈ Finset.univ.biUnion (C ω)) ≤ p) :
    (FiniteLaw.product (fun _ : Fin l => μ)).event (fun ω =>
      cap < ∑ i : Fin l, ((Finset.univ : Finset (Fin K)).filter
        (fun k => ∃ x ∈ C (ω i) k, test x)).card) ≤
      Real.exp ((l : ℝ) * (N.card * p / (b * K)) - Real.log 2 * (cap / K)) := by
  classical
  let P (ω : Ω) := Finset.univ.biUnion (C ω)
  let count (ω : Ω) := ((Finset.univ : Finset (Fin K)).filter
    (fun k => ∃ x ∈ C ω k, test x)).card
  let X (ω : Ω) : ℝ := (count ω : ℝ) / K
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hBr : (0 : ℝ) < b := by exact_mod_cast hb
  have hRange (ω : Ω) : X ω ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by dsimp [X]; positivity, (div_le_one hKr).mpr ?_⟩
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (by simp : (Finset.univ : Finset (Fin K)).card = K)
  have hpoint (ω : Ω) :
      X ω ≤ (∑ x ∈ N, if x ∈ P ω then (1 : ℝ) else 0) / (b * K) := by
    have hcount : ((P ω).filter test).card = count ω * b :=
      card_homogeneous_cliques_hit (C ω) (hCard ω) (hDisj ω) test (hSame ω)
    have hsub : (P ω).filter test ⊆ N.filter (fun x => x ∈ P ω) := by
      intro x hx
      obtain ⟨hxP, hxTest⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hN ω x hxP hxTest, hxP⟩
    have hcard := Finset.card_le_card hsub
    rw [hcount] at hcard
    have hcard' : (count ω : ℝ) * b ≤ ((N.filter (fun x => x ∈ P ω)).card : ℝ) := by exact_mod_cast hcard
    simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, X]
    rw [div_le_div_iff₀ hKr (mul_pos hBr hKr)]
    have := mul_le_mul_of_nonneg_right hcard' hKr.le
    convert this using 1
    ring
  have hMean : μ.mean X ≤ N.card * p / (b * K) := by
    refine (μ.mean_mono hpoint).trans ?_
    simp_rw [div_eq_inv_mul]
    rw [μ.mean_mul_const, μ.mean_sum]
    simp_rw [μ.mean_indicator]
    gcongr
    calc
      ∑ x ∈ N, μ.event (fun ω => x ∈ P ω) ≤ ∑ _x ∈ N, p := Finset.sum_le_sum hMarginal
      _ = N.card * p := by simp
  let ν := FiniteLaw.product (fun _ : Fin l => μ)
  refine (ν.event_mono (Q := fun ω => (cap : ℝ) / K ≤ ∑ i, X (ω i)) ?_).trans ?_
  · intro ω hw
    have hcast : (cap : ℝ) ≤ ∑ i, (count (ω i) : ℝ) := by exact_mod_cast (Nat.le_of_lt hw)
    simpa only [X, Finset.sum_div] using div_le_div_of_nonneg_right hcast hKr.le
  · refine (FiniteLaw.prob_sum_ge_le (fun _ : Fin l => μ) (fun _ => X)
      (fun _ => hRange) (Real.log_pos (by norm_num : 1 < (2 : ℝ))) (cap / K)).trans ?_
    rw [Real.exp_le_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    exact mul_le_mul_of_nonneg_left hMean (Nat.cast_nonneg l)



/-- The random list can be fixed before the distribution of the union is
specified. The final numerical hypothesis compares the reconstruction
error with the probability of finding the recorded independent set. -/
theorem exists_fixed_list_for_random_unions [Fintype V] {Ω : Type*} [Fintype Ω]
    (G : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    {m s l K b r M cap limit : ℕ} (hK : 0 < K) (hb : 0 < b) (hr : 0 < r)
    (W : (Fin m → ↥U) → Finset V) (hW : ∀ L, W L ⊆ U)
    (C : (Fin m → ↥U) → Ω → Fin K → Finset V)
    (hC : ∀ L ω k, C L ω k ⊆ W L)
    (hClique : ∀ L ω k, G.IsClique (C L ω k : Set V))
    (hCard : ∀ L ω k, (C L ω k).card = b)
    (hDisj : ∀ L ω, Pairwise fun i j => Disjoint (C L ω i) (C L ω j))
    (hSame : ∀ L ω k j x y, x ∈ C L ω k → y ∈ C L ω k →
      (Gᶜ.Adj (L j).val x ↔ Gᶜ.Adj (L j).val y))
    (hRamsey : ∀ A : Finset V, A ⊆ U → M ≤ A.card →
      ∃ Q : Finset V, Q ⊆ A ∧ Q.card = r ∧ Gᶜ.IsClique (Q : Set V))
    (hLarge : M ≤ l * (K * b))
    (hCollision : (s : ℝ) ^ 2 * ((K : ℝ) / r) ≤ 1 / 2)
    (hSmall : (m : ℝ) * ((cap : ℝ) / r) ^ s < ((limit : ℝ) / U.card) * m / 4)
    {p δ a : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a)
    (hDeg : ∀ y ∈ U, ((U.filter (Gᶜ.Adj y)).card : ℝ) ≤ δ)
    (herr :
      ((l * (K * b) : ℕ) : ℝ) ^ s *
          Real.exp ((l : ℝ) * a - Real.log 2 * (((r : ℝ) - s * K) / K)) +
        ((l : ℝ) ^ 2 * ((K * b : ℕ) * p) +
        m * Real.exp ((l : ℝ) * (δ * p / (b * K)) - Real.log 2 * (cap / K)) +
        Real.exp (-(((limit : ℝ) / U.card) * m) / 8) * ((l : ℝ) * (U.card * p)) ^ s) < 1) :
    ∃ L, ∀ μ : FiniteLaw Ω,
      (∀ x : V, μ.event (fun ω => x ∈ Finset.univ.biUnion (C L ω)) ≤ p) →
      ∃ S : Finset V, S ⊆ W L ∧ S.card ≤ limit ∧
        (K : ℝ) * a ≤ μ.mean (fun ω =>
          (independenceOrder G (S ∩ Finset.univ.biUnion (C L ω)) : ℝ)) := by
  let _ : Nonempty ↥U := hU.to_subtype
  let H (y : ↥U) (x : V) := Gᶜ.Adj y.val x
  let P (L : Fin m → ↥U) (ω : Ω) := Finset.univ.biUnion (C L ω)
  let μL := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥U)
  have hPU (L : Fin m → ↥U) (ω : Ω) : P L ω ⊆ W L := by
    intro x hx
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
    exact hC L ω k hk
  have hPcard (L : Fin m → ↥U) (ω : Ω) : (P L ω).card = K * b := by
    rw [Finset.card_biUnion (fun i _ j _ h => hDisj L ω h)]
    simp [hCard]
  have hOrder (L : Fin m → ↥U) (ω : Ω) : independenceOrder G (P L ω) ≤ K := by
    obtain ⟨Q, hQP, hQ⟩ := exists_independenceOrder G (P L ω)
    rw [← hQ.card_eq]
    exact (card_independent_le_clique_cover Finset.univ (C L ω)
      (fun k _ => hClique L ω k) Q hQ.isClique hQP).trans_eq (by simp)
  let enum (L : Fin m → ↥U) (ω : Ω) (j : Fin (K * b)) : V :=
    (Finset.equivFinOfCardEq (hPcard L ω)).symm j
  have hEnum (L : Fin m → ↥U) (ω : Ω) (x : V) (hx : x ∈ P L ω) :
      ∃ j, enum L ω j = x := by
    exact ⟨Finset.equivFinOfCardEq (hPcard L ω) ⟨x, hx⟩,
      congrArg Subtype.val ((Finset.equivFinOfCardEq (hPcard L ω)).symm_apply_apply _)⟩
  refine exists_list_recovering_against_all_laws G μL P W (l := l) (s := s) (r := r)
    hK ha enum hEnum hOrder
    (fun L μ => ∀ x, μ.event (fun ω => x ∈ P L ω) ≤ p) ?_
  intro ν hν
  let full := μL.staged (fun L => FiniteLaw.product (fun _ : Fin l => ν L))
  let tooMany (L : Fin m → ↥U) (j : Fin m) (ω : Fin l → Ω) := cap <
    ∑ i : Fin l, ((Finset.univ : Finset (Fin K)).filter
      (fun k => ∃ x ∈ C L (ω i) k, H (L j) x)).card
  let sharing (z : (Fin m → ↥U) × (Fin l → Ω)) :=
    ∃ i j, i ≠ j ∧ ¬ Disjoint (P z.1 (z.2 i)) (P z.1 (z.2 j))
  let badDegree (z : (Fin m → ↥U) × (Fin l → Ω)) := ∃ j, tooMany z.1 j z.2
  let d := (limit : ℝ) / U.card
  let badList (z : (Fin m → ↥U) × (Fin l → Ω)) :=
    ∃ (f : Fin s → Fin l) (v : Fin s → V), Function.Injective f ∧
      (d ≤ (FiniteLaw.uniform ↥U).event (fun y => ∀ k, H y (v k)) ∧
        listCommonCount H z.1 v < d * m / 2) ∧
      ∀ k, v k ∈ P z.1 (z.2 (f k))
  have hSharing : full.event sharing ≤ (l : ℝ) ^ 2 * ((K * b : ℕ) * p) := by
    rw [FiniteLaw.staged_event]
    refine (μL.mean_mono (Y := fun _ => _ ) ?_).trans_eq (μL.mean_const _)
    intro L
    exact event_intersecting_draws_le (ν L) (P L) l _ hp (fun ω => (hPcard L ω).le) (hν L)
  have hD : full.event badDegree ≤
      m * Real.exp ((l : ℝ) * (δ * p / (b * K)) - Real.log 2 * (cap / K)) := by
    rw [FiniteLaw.staged_event]
    refine (μL.mean_mono (Y := fun _ => _) ?_).trans_eq (μL.mean_const _)
    intro L
    let νL := FiniteLaw.product (fun _ : Fin l => ν L)
    refine (νL.event_exists_le_sum (tooMany L)).trans ?_
    calc
      _ ≤ ∑ _j : Fin m, Real.exp ((l : ℝ) * (δ * p / (b * K)) - Real.log 2 * (cap / K)) := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        let N := U.filter (H (L j))
        refine (event_many_cliques_hit_le (ν L) hK hb (C L) (hCard L) (hDisj L)
          (H (L j)) (fun ω k x y hx hy => hSame L ω k j x y hx hy) N
          (fun ω x hx hn => Finset.mem_filter.mpr ⟨hW L (hPU L ω hx), hn⟩)
          (fun x _ => hν L x)).trans ?_
        apply Real.exp_le_exp.mpr
        gcongr
        exact hDeg (L j).val (L j).property
      _ = _ := by simp
  have hList : full.event badList ≤
      Real.exp (-(d * m) / 8) * ((l : ℝ) * (U.card * p)) ^ s := by
    let a (_ : Fin l) (x : V) : ℝ := if x ∈ U then p else 0
    have ha0 (i : Fin l) (x : V) : 0 ≤ a i x := by
      by_cases h : x ∈ U <;> simp [a, h, hp]
    have hMarginal (L : Fin m → ↥U) (i : Fin l) (x : V) :
        (ν L).event (fun ω => x ∈ P L ω) ≤ a i x := by
      by_cases hx : x ∈ U
      · simpa only [a, hx, ite_true] using hν L x
      · have hp' : ∀ ω, x ∉ P L ω := fun ω hxP => hx (hW L (hPU L ω hxP))
        simp only [← (ν L).mean_indicator, hp', ite_false, (ν L).mean_const, a, hx, le_refl]
    have hs (i : Fin l) : ∑ x : V, a i x = U.card * p := by
      simp only [a, ← Finset.sum_filter]
      have heq : Finset.univ.filter (fun x => x ∈ U) = U := by ext; simp
      rw [heq]
      simp
    refine (FiniteLaw.staged_event_exists_injective_inclusions_le μL
      (fun L _ => ν L) (fun L _ ω x => x ∈ P L ω) a hMarginal ha0 s
      (fun v L => d ≤ (FiniteLaw.uniform ↥U).event (fun y => ∀ k, H y (v k)) ∧
        listCommonCount H L v < d * m / 2) (Real.exp_pos (-(d * m) / 8)).le ?_).trans_eq ?_
    · exact initial_list_tuple_tail (FiniteLaw.uniform ↥U) H d
    · simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  let successful := fun (L : Fin m → ↥U) (ω : Fin l → Ω) =>
    ¬ (sharing (L, ω) ∨ badDegree (L, ω) ∨ badList (L, ω))
  refine ⟨successful, ?_, ?_⟩
  · change _ < full.event (fun z => ¬ (sharing z ∨ badDegree z ∨ badList z))
    rw [full.event_not]
    have h := (full.event_union_le sharing (fun z => badDegree z ∨ badList z)).trans
      (add_le_add hSharing ((full.event_union_le badDegree badList).trans (add_le_add hD hList)))
    dsimp [d] at h
    linarith only [h, herr]
  · intro L ω hw
    have hw' : ¬ (sharing (L, ω) ∨ badDegree (L, ω) ∨ badList (L, ω)) := hw
    refine initial_record_from_good_draws U (W L) hU (hW L) hr L (fun i => P L (ω i))
      (fun i => C L (ω i)) (fun i => hPU L (ω i)) (fun i => hPcard L (ω i))
      (fun i k => hClique L (ω i) k) (fun _ => Finset.Subset.refl _)
      (fun i j hne => by_contra fun h => hw' (Or.inl ⟨i, j, hne, h⟩))
      hLarge hRamsey (fun j => le_of_not_gt (fun h => hw' (Or.inr (Or.inl ⟨j, h⟩))))
      hCollision hSmall ?_
    intro f v hf hv hd
    exact le_of_not_gt (fun h => hw' (Or.inr (Or.inr ⟨f, v, hf, ⟨hd, h⟩, hv⟩)))


end LocallyRamsey
