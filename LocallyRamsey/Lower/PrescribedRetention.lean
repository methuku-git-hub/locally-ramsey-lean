module

public import LocallyRamsey.Lower.RecordedOverlap
public import LocallyRamsey.Lower.DisjointDraws

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V Ω J : Type*} [Fintype Ω] [Fintype J] [LinearOrder V]

/-- Use a largest admissible retained set within each original sample.
The proof compares its size to the number of independent vertices from
the disjoint packed cliques. A small description specifies the retained
set used to count hits in unexposed cliques. -/
theorem exists_prescribed_retention (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : FiniteLaw Ω) (ν : FiniteLaw J) (S : Ω → Finset V)
    (A B : Finset V) (hAB : A ⊆ B)
    (P : J → Finset V) (hPcl : ∀ j, G.IsClique (P j : Set V))
    {K b H : ℕ} (enumerate : J → Fin b → V)
    (hEnum : ∀ j x, x ∈ P j → ∃ k, enumerate j k = x)
    {u : ℝ} (hu : 0 ≤ u)
    (hMarginal : ∀ x, ν.event (fun j => x ∈ P j) ≤ u)
    (Q : Ω → (Fin K → J) → Finset V)
    (hQind : ∀ s ξ, Gᶜ.IsClique (Q s ξ : Set V))
    (hQsub : ∀ s ξ, Q s ξ ⊆ S s ∩ A)
    (hQcover : ∀ s ξ x, x ∈ Q s ξ → ∃ i, x ∈ P (ξ i))
    {α η D z : ℝ} (hD : 1 < D) (hη : 0 < η) (hz : 0 ≤ z)
    (hH : ⌈D * Real.log (1 + 1 / η)⌉₊ ≤ H)
    (hExpected : α ≤ (μ.staged (fun _ => FiniteLaw.product (fun _ : Fin K => ν))).mean
      (fun p => ((Q p.1 p.2).card : ℝ))) :
    ∃ F : Ω → Finset V,
      (∀ s, F s ⊆ S s ∩ A ∧ ∀ x ∈ F s,
        ((neighborsIn G (F s) x).card : ℝ) ≤ ((F s).card + η * (S s ∩ B).card) / D) ∧
      α ≤ (H : ℝ) + 2 * K * u * μ.mean (fun s => ((F s).card : ℝ)) + z +
        K * ((K * b + 1 : ℕ) : ℝ) ^ H * Real.exp (-(Real.log 2 * z)) := by
  classical
  let admissible (s : Ω) (T : Finset V) : Prop :=
    T ⊆ S s ∩ A ∧ ∀ x ∈ T, ((neighborsIn G T x).card : ℝ) ≤
      (T.card + η * (S s ∩ B).card) / D
  let candidates (s : Ω) := (S s ∩ A).powerset.filter (admissible s)
  have hne (s : Ω) : (candidates s).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [admissible]⟩⟩
  have hmax (s : Ω) : ∃ T ∈ candidates s, ∀ T' ∈ candidates s, T'.card ≤ T.card := by
    obtain ⟨T, hT, hEq⟩ := Finset.exists_mem_eq_sup _ (hne s) Finset.card
    exact ⟨T, hT, fun T' hT' => hEq ▸ Finset.le_sup (f := Finset.card) hT'⟩
  let F (s : Ω) := Classical.choose (hmax s)
  have hF (s : Ω) : admissible s (F s) := (Finset.mem_filter.mp (Classical.choose_spec (hmax s)).1).2
  have hFmax (s : Ω) (T : Finset V) (hT : admissible s T) : T.card ≤ (F s).card :=
    (Classical.choose_spec (hmax s)).2 T
      (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT.1, hT⟩)
  refine ⟨F, hF, ?_⟩
  let tau := FiniteLaw.product (fun _ : Fin K => ν)
  let eps := ((K * b + 1 : ℕ) : ℝ) ^ H * Real.exp (-(Real.log 2 * z))
  have hsBound (s : Ω) :
      tau.mean (fun ξ => ((Q s ξ).card : ℝ)) ≤
        H + 2 * K * u * (F s).card + z + K * eps := by
    let m := (K : ℝ) * u * (F s).card
    let decode (a : RecordDescription K b H) (e : {i // i ∈ namedDraws a} → J) :=
      let R := decodeRecordDescription a enumerate e
      R ∪ recordRemainder G (chooseHeavy G (fun _ => 1) (η * (S s ∩ B).card) D) R
        (S s ∩ A).card (S s ∩ A)
    let enabled (a : RecordDescription K b H) (e : {i // i ∈ namedDraws a} → J) :=
      admissible s (decode a e)
    let bad (ξ : Fin K → J) :=
      ∃ a, enabled a (fun i => ξ i.val) ∧
        2 * m + z ≤ ∑ i : {i // i ∉ namedDraws a},
          if ¬Disjoint (decode a (fun j => ξ j.val)) (P (ξ i.val)) then (1 : ℝ) else 0
    let X (a : RecordDescription K b H) (e : {i // i ∈ namedDraws a} → J)
      (_ : {i // i ∉ namedDraws a}) (j : J) : ℝ :=
      if ¬Disjoint (decode a e) (P j) then 1 else 0
    have hit (T : Finset V) : ν.event (fun j => ¬Disjoint T (P j)) ≤ u * T.card := by
      have sub : ∀ j, ¬Disjoint T (P j) → ∃ x : ↥T, x.val ∈ P j := by
        intro j hj
        obtain ⟨x, hxT, hxP⟩ := Finset.not_disjoint_iff.mp hj
        exact ⟨⟨x, hxT⟩, hxP⟩
      refine ((ν.event_mono sub).trans (ν.event_exists_le_sum (fun (x : ↥T) j => x.val ∈ P j))).trans ?_
      calc
        _ ≤ ∑ _x : ↥T, u := Finset.sum_le_sum (fun x _ => hMarginal x.val)
        _ = _ := by simp [mul_comm]
    have hexp (a : RecordDescription K b H) (e : {i // i ∈ namedDraws a} → J)
        (ha : enabled a e) :
        ∑ i : {i // i ∉ namedDraws a}, ν.mean (X a e i) ≤ m := by
      have hX (i : {i // i ∉ namedDraws a}) : ν.mean (X a e i) ≤ u * (F s).card := by
        change ν.mean (fun j => if ¬Disjoint (decode a e) (P j) then 1 else 0) ≤ _
        rw [ν.mean_indicator]
        exact (hit _).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hFmax s (decode a e) ha) hu)
      have hc : (Fintype.card {i // i ∉ namedDraws a} : ℝ) ≤ K := by
        exact_mod_cast (Fintype.card_le_of_injective
          (fun i : {i // i ∉ namedDraws a} => i.val) Subtype.val_injective).trans_eq (Fintype.card_fin K)
      calc
        _ ≤ ∑ _i : {i // i ∉ namedDraws a}, u * (F s).card := Finset.sum_le_sum (fun i _ => hX i)
        _ ≤ _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, m, mul_assoc]
          exact mul_le_mul_of_nonneg_right hc (by positivity)
    have hbad : tau.event bad ≤ eps := by
      have h := FiniteLaw.event_exists_deferred_test_le (fun _ : Fin K => ν) namedDraws enabled X
        (fun a e i j => by dsimp [X]; split <;> norm_num) m (2 * m + z) hexp
      change tau.event bad ≤ _ at h
      refine h.trans ?_
      have hc : (Fintype.card (RecordDescription K b H) : ℝ) = ((K * b + 1 : ℕ) : ℝ) ^ H := by
        norm_num [Fintype.card_fun, Fintype.card_option, Fintype.card_prod]
      rw [hc]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hlog : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith only [mul_le_mul_of_nonneg_right hlog (show 0 ≤ m by dsimp [m]; positivity)]
    have hQsize (ξ : Fin K → J) : (Q s ξ).card ≤ K := by
      have hcover : Q s ξ ⊆ Finset.univ.biUnion (fun i => P (ξ i)) := by
        intro x hx
        obtain ⟨i, hi⟩ := hQcover s ξ x hx
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
      simpa using card_independent_le_clique_cover (Finset.univ : Finset (Fin K)) (fun i => P (ξ i))
        (fun i _ => hPcl (ξ i)) (Q s ξ) (hQind s ξ) hcover
    have hsm (ξ : Fin K → J) (hξ : ¬ bad ξ) : ((Q s ξ).card : ℝ) ≤ H + 2 * m + z := by
      let B₀ := S s ∩ A
      let cap : ℝ := (S s ∩ B).card
      have hsubset : B₀ ⊆ S s ∩ B := by
        intro x hx
        obtain ⟨hxS, hxA⟩ := Finset.mem_inter.mp hx
        exact Finset.mem_inter.mpr ⟨hxS, hAB hxA⟩
      have hmass : mass (fun (_ : V) => (1 : ℝ)) B₀ ≤ cap := by
        simp only [mass, Finset.sum_const, nsmul_eq_mul, mul_one]
        change (B₀.card : ℝ) ≤ ((S s ∩ B).card : ℝ)
        exact_mod_cast Finset.card_le_card hsubset
      obtain ⟨R, hRQ, hRcard, hQF, hFA, hDegree⟩ := weighted_recording G (fun _ => 1)
        (fun _ => zero_le_one) B₀ (Q s ξ) (hQsub s ξ) (hQind s ξ) D η cap hD hη hmass
      let T := R ∪ recordRemainder G (chooseHeavy G (fun _ => 1) (η * cap) D) R B₀.card B₀
      have hAdm : admissible s T := by
        refine ⟨hFA, fun x hx => ?_⟩
        simpa only [mass, Finset.sum_const, nsmul_eq_mul, mul_one] using hDegree x hx
      obtain ⟨a, ha⟩ := exists_recordDescription R (hRcard.trans hH) enumerate ξ (fun x hx => by
        obtain ⟨i, hi⟩ := hQcover s ξ x (hRQ hx)
        obtain ⟨k, hk⟩ := hEnum (ξ i) x hi
        exact ⟨i, k, hk⟩)
      have heq : decode a (fun i => ξ i.val) = T := by dsimp only [decode]; rw [ha]
      have hcount := card_clique_le_named_add_hits Gᶜ (namedDraws a) (fun i => P (ξ i))
        (fun i => by simpa using hPcl (ξ i)) (Q s ξ) T (hQind s ξ) hQF (hQcover s ξ)
      have hsmall : (∑ i : {i // i ∉ namedDraws a},
          if ¬Disjoint T (P (ξ i.val)) then (1 : ℝ) else 0) < 2 * m + z := by
        by_contra! hLarge
        exact hξ ⟨a, by unfold enabled; rw [heq]; exact hAdm, by simpa only [heq] using hLarge⟩
      have hNames : ((namedDraws a).card : ℝ) ≤ H := by exact_mod_cast namedDraws_card_le a
      linarith only [hcount, hNames, hsmall]
    have hpoint (ξ : Fin K → J) : ((Q s ξ).card : ℝ) ≤
        (H + 2 * m + z) + K * (if bad ξ then 1 else 0) := by
      by_cases hc : bad ξ
      · have hk : ((Q s ξ).card : ℝ) ≤ K := by exact_mod_cast hQsize ξ
        simpa [hc] using hk.trans (le_add_of_nonneg_left (by dsimp [m]; positivity))
      · simpa [hc] using hsm ξ hc
    have hh := tau.mean_mono hpoint
    rw [tau.mean_add, tau.mean_const, tau.mean_mul_const, tau.mean_indicator] at hh
    have hb := mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg K)
    dsimp [m] at hh ⊢
    nlinarith only [hh, hb]
  have hp : (μ.staged (fun _ => tau)).mean (fun p => ((Q p.1 p.2).card : ℝ)) ≤
      μ.mean (fun s => (H : ℝ) + 2 * K * u * (F s).card + z + K * eps) := by
    rw [FiniteLaw.staged_mean]
    exact μ.mean_mono hsBound
  refine hExpected.trans (hp.trans_eq ?_)
  simp only [μ.mean_add, μ.mean_const, μ.mean_mul_const, eps]
  ring


/-- The expectation hypothesis for retaining vertices in a prescribed set
comes from the original sampling rule. Draw inside the prescribed set
and use its guarantee whenever the drawn cliques are disjoint. -/
theorem exists_prescribed_retention_from_sampler (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : FiniteLaw Ω) (ν : FiniteLaw J) (S : Ω → Finset V)
    (A B : Finset V) (hAB : A ⊆ B)
    (P : J → Finset V) (hPA : ∀ j, P j ⊆ A)
    (hPcl : ∀ j, G.IsClique (P j : Set V)) {K b H : ℕ}
    (hPcard : ∀ j, (P j).card ≤ b)
    (enumerate : J → Fin b → V)
    (hEnum : ∀ j x, x ∈ P j → ∃ k, enumerate j k = x)
    {u α η D z : ℝ} (hu : 0 ≤ u) (hα : 0 ≤ α) (hD : 1 < D)
    (hη : 0 < η) (hz : 0 ≤ z) (hH : ⌈D * Real.log (1 + 1 / η)⌉₊ ≤ H)
    (hMarginal : ∀ x, ν.event (fun j => x ∈ P j) ≤ u)
    (hSample : ∀ τ : Fin K → J, (Pairwise fun i j => Disjoint (P (τ i)) (P (τ j))) →
      α ≤ μ.mean (fun s => (independenceOrder G
        (S s ∩ Finset.univ.biUnion (fun i => P (τ i))) : ℝ))) :
    ∃ F : Ω → Finset V,
      (∀ s, F s ⊆ S s ∩ A ∧ ∀ x ∈ F s,
        ((neighborsIn G (F s) x).card : ℝ) ≤ ((F s).card + η * (S s ∩ B).card) / D) ∧
      α * (1 - (K : ℝ) ^ 2 * (b * u)) ≤ (H : ℝ) + 2 * K * u * μ.mean
        (fun s => ((F s).card : ℝ)) + z +
        K * ((K * b + 1 : ℕ) : ℝ) ^ H * Real.exp (-(Real.log 2 * z)) := by
  classical
  let U (τ : Fin K → J) := Finset.univ.biUnion (fun i => P (τ i))
  have hUA (τ : Fin K → J) : U τ ⊆ A := by
    intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact hPA (τ i) hi
  choose Q hQ hCard using fun (s : Ω) τ => exists_independenceOrder G (S s ∩ U τ)
  have hQsub (s : Ω) (τ : Fin K → J) : Q s τ ⊆ S s ∩ A := by
    intro x hx
    obtain ⟨hxS, hxU⟩ := Finset.mem_inter.mp (hQ s τ hx)
    exact Finset.mem_inter.mpr ⟨hxS, hUA τ hxU⟩
  have hQcover (s : Ω) (τ : Fin K → J) (x : V) (hx : x ∈ Q s τ) : ∃ i, x ∈ P (τ i) := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp (hQ s τ hx)).2
    exact ⟨i, hi⟩
  let ξ := FiniteLaw.product (fun _ : Fin K => ν)
  let bad (τ : Fin K → J) := ∃ i j, i ≠ j ∧ ¬Disjoint (P (τ i)) (P (τ j))
  have hBad : ξ.event bad ≤ (K : ℝ) ^ 2 * (b * u) :=
    event_intersecting_draws_le ν P K b hu hPcard hMarginal
  have hExpected : α * (1 - (K : ℝ) ^ 2 * (b * u)) ≤
      (μ.staged (fun _ => ξ)).mean (fun x => ((Q x.1 x.2).card : ℝ)) := by
    have hswap : (μ.staged (fun _ => ξ)).mean (fun x => ((Q x.1 x.2).card : ℝ)) =
        ξ.mean (fun τ => μ.mean (fun s => ((Q s τ).card : ℝ))) := by
      rw [μ.staged_mean]
      simp only [FiniteLaw.mean, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [mul_left_comm]
    have ht (τ : Fin K → J) :
        α * (if ¬bad τ then (1 : ℝ) else 0) ≤ μ.mean (fun s => ((Q s τ).card : ℝ)) := by
      by_cases h : bad τ
      · simp only [h, not_true_eq_false, ite_false, mul_zero]
        exact μ.mean_nonneg (fun _ => Nat.cast_nonneg _)
      · have hb : Pairwise fun i j => Disjoint (P (τ i)) (P (τ j)) := fun i j hne =>
          by_contra (fun hn => h ⟨i, j, hne, hn⟩)
        simp only [h, not_false_eq_true, ite_true, mul_one]
        calc
          α ≤ μ.mean (fun s => (independenceOrder G (S s ∩ U τ) : ℝ)) := hSample τ hb
          _ = _ := congrArg μ.mean (funext (fun s =>
            congrArg (fun k : ℕ => (k : ℝ)) (hCard s τ).card_eq.symm))
    rw [hswap]
    calc
      _ ≤ α * (1 - ξ.event bad) := mul_le_mul_of_nonneg_left (sub_le_sub_left hBad 1) hα
      _ = ξ.mean (fun τ => α * (if ¬bad τ then (1 : ℝ) else 0)) := by
        rw [ξ.mean_mul_const, ξ.mean_indicator, ξ.event_not]
      _ ≤ _ := ξ.mean_mono ht
  exact exists_prescribed_retention G μ ν S A B hAB P hPcl enumerate hEnum hu hMarginal Q
    (fun s τ => (hCard s τ).isClique) hQsub hQcover hD hη hz hH hExpected

end LocallyRamsey
