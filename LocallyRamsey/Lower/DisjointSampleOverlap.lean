module

public import LocallyRamsey.Lower.SampleOverlap

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V I J P Ω : Type*} [DecidableEq V] [DecidableEq I] [Fintype I] [Fintype J]
  [DecidableEq J] [Fintype P] [Fintype Ω]

/-- If an anchored partition leaves some positions unused, their factors
are one. Used positions contribute exactly to their own groups. -/
theorem event_bad_marked_of_disjoint_blocks_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hJ : 0 < Fintype.card J) (μ : I → FiniteLaw Ω) (π : FiniteLaw P)
    (block : P → J → Finset I) (hdisj : ∀ p, Pairwise (fun j k => Disjoint (block p j) (block p k)))
    (B F : Finset V)
    (keep : (p : P) → (j : J) → (↥(block p j) → Ω) → Prop)
    (L : V → I → Ω → ℝ) (hL : ∀ x i s, 0 ≤ L x i s)
    (hmean : ∀ x ∈ B, ∀ i, (μ i).mean (L x i) = 1)
    {c γ D limit : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ) (hD : 0 < D)
    (hsize : (Fintype.card J : ℝ) - 1 ≤ D) (hatom : c ≤ γ / D)
    (hdeg : ∀ x ∈ F, ((neighborsIn G F x).card : ℝ) * c ≤
      (mass (sharedWeight F c) B + γ) / D)
    (hlimit : 0 < limit) :
    let z := mass (sharedWeight F c) B
    let w (ω : I → Ω) (p : P) (j : J) :=
      normalizedOverlap B z (16 * (z + γ)) (keep p j (fun i => ω i.val)) (fun x =>
        sharedWeight F c x * ∏ i ∈ block p j, L x i (ω i))
    let avg (ω : I → Ω) (p : P) (x : V) :=
      (Fintype.card J : ℝ)⁻¹ * ∑ j, w ω p j x
    (FiniteLaw.product μ).event (fun ω =>
      limit < π.mean (fun p => mass (avg ω p) (marked G (avg ω p) B γ))) ≤
      Real.exp (1 / 8 - Real.log 2 * ((Fintype.card J : ℝ) * γ - 1)) / limit := by
  classical
  intro z w avg
  let first := Classical.choice (Fintype.card_pos_iff.mp hJ)
  let label (p : P) (i : I) := if hi : ∃ j, i ∈ block p j then Classical.choose hi else first
  have hlabel (p : P) (j : J) (i : I) (hi : i ∈ block p j) : label p i = j := by
    have h : ∃ j, i ∈ block p j := ⟨j, hi⟩
    simp only [label, dite_eq_left h]
    by_contra hn
    exact (Finset.disjoint_left.mp (hdisj p hn)) (Classical.choose_spec h) hi
  let isUsed (p : P) (i : I) := ∃ j, i ∈ block p j
  let L' (p : P) (x : V) (i : I) (s : Ω) := if isUsed p i then L x i s else 1
  let keep' (p : P) (j : J) (s : FiniteLaw.Block (label p) j (fun _ => Ω)) :=
    keep p j (fun i => s ⟨i.val, hlabel p j i.val i.property⟩)
  have hL' (p : P) (x : V) (i : I) (s : Ω) : 0 ≤ L' p x i s := by
    dsimp [L']
    split
    · exact hL _ _ _
    · norm_num
  have hmean' (p : P) (x : V) (hx : x ∈ B) (i : I) : (μ i).mean (L' p x i) = 1 := by
    by_cases hi : isUsed p i
    · simpa only [L', ite_eq_left hi] using hmean x hx i
    · simp only [L', ite_eq_right hi, FiniteLaw.mean_const]
  have hprod (ω : I → Ω) (p : P) (j : J) (x : V) :
      (∏ i : {i // label p i = j}, L' p x i.val (ω i.val)) = ∏ i ∈ block p j, L x i (ω i) := by
    have hfib (i : I) : i ∈ (Finset.univ.filter (fun y => label p y = j)) ↔ label p i = j := by simp
    rw [← Finset.prod_subtype _ hfib (fun i => L' p x i (ω i))]
    have hsub : block p j ⊆ Finset.univ.filter (fun y => label p y = j) :=
      fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlabel p j i hi⟩
    rw [← Finset.prod_subset hsub (fun i hf hn => ?_)]
    · refine Finset.prod_congr rfl (fun i hi => ?_)
      simp only [L', ite_eq_left (show isUsed p i from ⟨j, hi⟩)]
    · have hnUsed : ¬ isUsed p i := by
        rintro ⟨k, hk⟩
        have heq := hlabel p k i hk
        rw [(Finset.mem_filter.mp hf).2] at heq
        exact hn (heq.symm ▸ hk)
      simp only [L', ite_eq_right hnUsed]
  have h' := event_sample_overlap_bad_marked_le G hJ μ π label B F keep' L'
    hL' hmean' hc hγ hD hsize hatom hdeg hlimit
  have heq (ω : I → Ω) (p : P) :
      avgGroupWeight (fun j s =>
        normalizedOverlap B z (16 * (z + γ)) (keep' p j s) (fun x =>
          sharedWeight F c x * ∏ i : {i // label p i = j}, L' p x i.val (s i)))
        (fun _ i => ω i.val) = avg ω p := by
    funext x
    dsimp only [avgGroupWeight, avg, w, keep']
    simp_rw [hprod]
  refine ((FiniteLaw.product μ).event_mono ?_).trans h'
  intro ω hω
  change limit < π.mean (fun p => mass (avgGroupWeight (fun j s =>
    normalizedOverlap B z (16 * (z + γ)) (keep' p j s) (fun x =>
      sharedWeight F c x * ∏ i : {i // label p i = j}, L' p x i.val (s i)))
    (fun _ i => ω i.val)) (marked G (avgGroupWeight (fun j s =>
    normalizedOverlap B z (16 * (z + γ)) (keep' p j s) (fun x =>
      sharedWeight F c x * ∏ i : {i // label p i = j}, L' p x i.val (s i)))
    (fun _ i => ω i.val)) B γ))
  simp only [heq]
  exact hω

end LocallyRamsey
