module

public import LocallyRamsey.Lower.InitialRule
public import LocallyRamsey.Lower.RetentionRule

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At a vertex of small degree, the fraction of list positions occupied
by neighbours exceeds twice its upper mean with exponentially small
probability. The expected number of vertices removed obeys the same
bound times the size of the set. -/
theorem event_many_long_signatures_le (W C : Finset V) (hW : W.Nonempty)
    (adj : V → V → Prop) [DecidableRel adj] (m d : ℕ)
    {density : ℝ} (hl : 0 ≤ density)
    (hdeg : ∀ x ∈ C, ((W.filter (fun y => adj y x)).card : ℝ) ≤ density * W.card) :
    letI : Nonempty ↥W := hW.to_subtype
    let ν := FiniteLaw.product (fun _ : Fin m => FiniteLaw.uniform ↥W)
    let lengthy (L : Fin m → ↥W) := C.filter (fun x =>
      d < (listSignature (fun y x => adj y.val x) L x).card)
    ν.event (fun L => (C.card : ℝ) / 4 < (lengthy L).card) ≤
      4 * Real.exp ((m : ℝ) * density - Real.log 2 * d) := by
  letI : Nonempty ↥W := hW.to_subtype
  intro ν lengthy
  let μ := FiniteLaw.uniform ↥W
  let bound := Real.exp ((m : ℝ) * density - Real.log 2 * d)
  have hx (x : V) (hxC : x ∈ C) : ν.event (fun L => x ∈ lengthy L) ≤ bound := by
    let X (_ : Fin m) (y : ↥W) := if adj y.val x then (1 : ℝ) else 0
    have hX (j : Fin m) : μ.mean (X j) ≤ density := by
      dsimp only [X]
      rw [μ.mean_indicator, uniform_vertex_event W hW (fun y => adj y x)]
      exact (div_le_iff₀ (by exact_mod_cast hW.card_pos : (0 : ℝ) < W.card)).mpr (hdeg x hxC)
    refine (ν.event_mono (Q := fun L => (d : ℝ) ≤ ∑ j, X j (L j)) ?_).trans ?_
    · intro L hL
      have hcast : (d : ℝ) ≤ ((listSignature (fun (y : ↥W) x => adj y.val x) L x).card : ℝ) :=
        by exact_mod_cast (Nat.le_of_lt (Finset.mem_filter.mp hL).2)
      simpa [listSignature, X] using hcast
    · refine (FiniteLaw.prob_sum_ge_le (fun _ : Fin m => μ) X (fun j y => by
          dsimp [X]; split <;> norm_num) (Real.log_pos (by norm_num : (1 : ℝ) < 2)) d).trans ?_
      rw [Real.exp_le_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
      exact (Finset.sum_le_sum (fun i _ => hX i)).trans_eq (by simp)
  by_cases he : C.Nonempty
  · have hmean : ν.mean (fun L => ((lengthy L).card : ℝ)) ≤ C.card * bound := by
      have hf (L : Fin m → ↥W) :
          ((lengthy L).card : ℝ) = ∑ x ∈ C, if x ∈ lengthy L then 1 else 0 := by
        have h : C.filter (fun x => x ∈ lengthy L) = lengthy L := by
          ext x
          exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨Finset.filter_subset _ _ h, h⟩⟩
        rw [← Finset.sum_filter, h]
        simp
      simp_rw [hf, ν.mean_sum, ν.mean_indicator]
      exact (Finset.sum_le_sum hx).trans_eq (by simp)
    have hC : (0 : ℝ) < C.card := by exact_mod_cast he.card_pos
    refine ((ν.event_mono (fun _ h => h.le)).trans
      (ν.event_ge_le (fun _ => Nat.cast_nonneg _) (by positivity : (0 : ℝ) < C.card / 4))).trans ?_
    refine (div_le_div_of_nonneg_right hmean (by positivity)).trans_eq ?_
    dsimp [bound]
    field_simp
  · have hnil : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [← ν.mean_indicator]
    simp [lengthy, hnil, ν.mean_const, (Real.exp_pos _).le]

/-- Keep a packing once it covers half the vertices of the group. The
uniform draw has the vertex marginals and the hit probability for a
neighbourhood of a list entry used to locate the clique. -/
theorem exists_draw_from_list_packing {Y : Type*} {m : ℕ}
    (adj : Y → V → Prop) [DecidableRel adj] (L : Fin m → Y) (C : Finset V) (hC : C.Nonempty)
    {b d k : ℕ} (hb : 0 < b) (family : Finset V → Prop)
    (hsupply : ∀ A : Finset V, A ⊆ C → k ≤ A.card →
      ∃ F : Finset V, F ⊆ A ∧ F.card = b ∧ family F)
    (hNum : (m + 1) ^ d * k * 4 ≤ C.card) :
    ∃ ν : FiniteLaw (Finset V),
      (∀ x, ν.event (fun P => x ∈ P) ≤
        if x ∈ C then 2 * (b : ℝ) / C.card else 0) ∧
      (∀ j, ν.event (fun P => ∃ x ∈ P, adj (L j) x) ≤
        2 * ((C.filter (adj (L j))).card : ℝ) / C.card) ∧
      ν.event (fun P => P ≠ ∅ ∧
        ¬(P ⊆ C ∧ P.card = b ∧ family P ∧
          ∀ x y, x ∈ P → y ∈ P → listSignature adj L x = listSignature adj L y)) = 0 ∧
      ((C.card : ℝ) * 3 / 4 ≤ ((C.filter (fun x =>
        (listSignature adj L x).card ≤ d)).card : ℝ) → ν.event (fun P => P = ∅) = 0) := by
  let A := C.filter (fun x => (listSignature adj L x).card ≤ d)
  have hA : A ⊆ C := Finset.filter_subset _ _
  obtain ⟨packing, hpack, hdisj, hremain⟩ :=
    pack_within_list_classes adj L A d k b hb family
      (fun x hx => (Finset.mem_filter.mp hx).2) (fun B hB => hsupply B (hB.trans hA))
  let cover := packing.biUnion id
  have hcoverA : cover ⊆ A := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx
    exact (hpack P hP).1 hxP
  have hcoverCard : cover.card = packing.card * b := by
    change (packing.biUnion (fun P => P)).card = _
    rw [Finset.card_biUnion hdisj]
    trans ∑ _P ∈ packing, b
    · exact Finset.sum_congr rfl (fun P hP => (hpack P hP).2.1)
    · simp
  have hcover : (C.card : ℝ) * 3 / 4 ≤ A.card → (C.card : ℝ) / 2 ≤ cover.card := by
    intro hAcard
    have hdis : (A \ cover).card + cover.card = A.card := by
      rw [Finset.card_sdiff_of_subset hcoverA]
      exact Nat.sub_add_cancel (Finset.card_le_card hcoverA)
    have h1 : ((A \ cover).card : ℝ) + cover.card = A.card := by exact_mod_cast hdis
    have h2 : ((A \ cover).card : ℝ) ≤ ((m + 1) ^ d * k : ℕ) := by exact_mod_cast hremain
    have h3 : (((m + 1) ^ d * k : ℕ) : ℝ) * 4 ≤ C.card := by exact_mod_cast hNum
    linarith only [hAcard, h1, h2, h3]
  have hCpos : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  by_cases hbig : (C.card : ℝ) / 2 ≤ cover.card
  · have hp : packing.Nonempty := by
      apply Finset.card_pos.mp
      have hh : (0 : ℝ) < cover.card := (by positivity : (0 : ℝ) < C.card / 2).trans_le hbig
      rw [hcoverCard, Nat.cast_mul] at hh
      exact_mod_cast (pos_of_mul_pos_left hh (Nat.cast_nonneg _))
    let _ : Nonempty ↥packing := hp.to_subtype
    let μ := FiniteLaw.uniform ↥packing
    let ν := μ.map Subtype.val
    have hmu (x : V) : ν.event (fun P => x ∈ P) ≤
        if x ∈ C then 2 * (b : ℝ) / C.card else 0 := by
      rw [μ.event_map]
      split
      · refine (uniform_packing_marginal_le packing hp hdisj x).trans ?_
        have hp' : (0 : ℝ) < packing.card := by exact_mod_cast hp.card_pos
        have hbig' : (C.card : ℝ) / 2 ≤ (packing.card : ℝ) * b := by
          simpa only [hcoverCard, Nat.cast_mul] using hbig
        rw [div_le_div_iff₀ hp' hCpos, one_mul]
        nlinarith only [hbig']
      · rename_i hno
        have hn (P : ↥packing) : x ∉ P.val :=
          fun hx => hno (hA ((hpack P.val P.property).1 hx))
        simp [Function.comp_def, hn, ← μ.mean_indicator, μ.mean_const]
    refine ⟨ν, hmu, ?_, ?_, ?_⟩
    · intro j
      let B := C.filter (adj (L j))
      have hsum (P : ↥packing) : ((P.val ∩ B).card : ℝ) =
          (b : ℝ) * (if (∃ x ∈ P.val, adj (L j) x) then 1 else 0) := by
        obtain ⟨hPC, hPb, _, hP⟩ := hpack P.val P.property
        by_cases h : ∃ x ∈ P.val, adj (L j) x
        · obtain ⟨x, hx, hxAdj⟩ := h
          have hj (y : V) (hy : y ∈ P.val) : adj (L j) y := by
            have hsig := hP x y hx hy
            have hj' : j ∈ listSignature adj L x := by simp [listSignature, hxAdj]
            rw [hsig] at hj'
            simpa [listSignature] using hj'
          have hsub : P.val ⊆ B := fun y hy => Finset.mem_filter.mpr ⟨hA (hPC hy), hj y hy⟩
          have ht : ∃ x ∈ P.val, adj (L j) x := ⟨x, hx, hxAdj⟩
          simp only [Finset.inter_eq_left.mpr hsub, hPb, ite_eq_left ht, mul_one]
        · have hD : Disjoint P.val B := Finset.disjoint_left.mpr (fun x hx hxB =>
            h ⟨x, hx, (Finset.mem_filter.mp hxB).2⟩)
          simp [Finset.disjoint_iff_inter_eq_empty.mp hD, h]
      have hEq : (b : ℝ) * ν.event (fun P => ∃ x ∈ P, adj (L j) x) =
          ∑ x ∈ B, ν.event (fun P => x ∈ P) := by
        have hL : (b : ℝ) * ν.event (fun P => ∃ x ∈ P, adj (L j) x) =
            μ.mean (fun P => ((P.val ∩ B).card : ℝ)) := by
          rw [μ.event_map, ← μ.mean_indicator, ← μ.mean_mul_const]
          congr 1
          funext P
          exact (hsum P).symm
        have hR (x : V) : ν.event (fun P => x ∈ P) =
            μ.mean (fun P => if x ∈ P.val then 1 else 0) := by
          rw [μ.event_map, ← μ.mean_indicator]
          rfl
        rw [hL]
        simp_rw [hR]
        rw [← μ.mean_sum]
        congr 1
        funext P
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
        simp
      apply (le_of_mul_le_mul_left ?_ (by exact_mod_cast hb : (0 : ℝ) < b))
      rw [hEq]
      calc
        _ ≤ ∑ _x ∈ B, 2 * (b : ℝ) / C.card := Finset.sum_le_sum (fun x hx =>
          by simpa [(Finset.mem_filter.mp hx).1] using hmu x)
        _ = _ := by simp [B]; ring
    · rw [μ.event_map, ← μ.mean_indicator]
      have he (P : ↥packing) : ¬(P.val ≠ ∅ ∧ ¬(P.val ⊆ C ∧ P.val.card = b ∧ family P.val ∧
          ∀ x y, x ∈ P.val → y ∈ P.val → listSignature adj L x = listSignature adj L y)) := by
        obtain ⟨hP, hp, hf, hs⟩ := hpack P.val P.property
        exact fun h => h.2 ⟨hP.trans hA, hp, hf, hs⟩
      simp only [Function.comp_apply, ite_eq_right (he _), μ.mean_const]
    · intro _
      rw [μ.event_map, ← μ.mean_indicator]
      have he (P : ↥packing) : P.val ≠ ∅ := Finset.nonempty_iff_ne_empty.mp
        (Finset.card_pos.mp ((hpack P.val P.property).2.1 ▸ hb))
      simp [Function.comp_def, he, μ.mean_const]
  · refine ⟨FiniteLaw.single ∅, ?_, ?_, ?_, ?_⟩
    · intro x
      rw [FiniteLaw.single_event]
      simp only [Finset.notMem_empty, ite_false]
      split <;> positivity
    · intro j
      rw [FiniteLaw.single_event]
      simp
      positivity
    · simp [FiniteLaw.single_event]
    · intro h
      exact (hbig (hcover h)).elim


/-- The packed draw can be interpreted as a function on all outcomes.
Outcomes of probability zero are sent to the empty set so that every
reported set satisfies the required family and size conditions. -/
theorem exists_supported_list_draw {Y : Type*} {m : ℕ}
    (adj : Y → V → Prop) [DecidableRel adj] (L : Fin m → Y) (C : Finset V) (hC : C.Nonempty)
    {b d k : ℕ} (hb : 0 < b) (family : Finset V → Prop)
    (hsupply : ∀ A : Finset V, A ⊆ C → k ≤ A.card →
      ∃ F : Finset V, F ⊆ A ∧ F.card = b ∧ family F)
    (hNum : (m + 1) ^ d * k * 4 ≤ C.card) :
    ∃ (ν : FiniteLaw (Finset V)) (draw : Finset V → Finset V),
      (∀ S, draw S = ∅ ∨ (draw S ⊆ C ∧ (draw S).card = b ∧ family (draw S))) ∧
      (∀ x, ν.event (fun S => x ∈ draw S) ≤
        if x ∈ C then 2 * (b : ℝ) / C.card else 0) ∧
      (∀ j, ν.event (fun S => ∃ x ∈ draw S, adj (L j) x) ≤
        2 * ((C.filter (adj (L j))).card : ℝ) / C.card) ∧
      ((C.card : ℝ) * 3 / 4 ≤ ((C.filter (fun x =>
        (listSignature adj L x).card ≤ d)).card : ℝ) → ν.event (fun S => draw S = ∅) = 0) := by
  obtain ⟨ν, hm, hAdj, hInvalid, hEmpty⟩ := exists_draw_from_list_packing adj L C hC hb
    family hsupply hNum
  let valid (S : Finset V) := S ⊆ C ∧ S.card = b ∧ family S
  let draw (S : Finset V) := if valid S then S else ∅
  have he (S : Finset V) (h : 0 < ν.prob S) : draw S = S := by
    by_cases hn : valid S
    · simp [draw, hn]
    · have hz : S = ∅ := by
        by_contra he
        let E (P : Finset V) := P ≠ ∅ ∧
          ¬(P ⊆ C ∧ P.card = b ∧ family P ∧
            ∀ x y, x ∈ P → y ∈ P → listSignature adj L x = listSignature adj L y)
        have hE : E S := ⟨he, fun h => hn ⟨h.1, h.2.1, h.2.2.1⟩⟩
        have hP : ν.prob S ≤ ν.event E := by
          rw [← ν.mean_indicator]
          have h := Finset.single_le_sum (f := fun P => ν.prob P * (if E P then (1 : ℝ) else 0))
            (fun P _ => mul_nonneg (ν.nonneg P) (by split <;> norm_num)) (Finset.mem_univ S)
          simpa only [hE, ite_true, mul_one, FiniteLaw.mean] using h
        change ν.event E = 0 at hInvalid
        linarith only [h, hP, hInvalid]
      simp [draw, hn, hz]
  have hLaw (P : Finset V → Prop) : ν.event (fun S => P (draw S)) = ν.event P := by
    rw [← ν.mean_indicator, ← ν.mean_indicator]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    change ν.prob S * (if P (draw S) then (1 : ℝ) else 0) =
      ν.prob S * (if P S then (1 : ℝ) else 0)
    by_cases h : 0 < ν.prob S
    · rw [he S h]
    · simp only [le_antisymm (le_of_not_gt h) (ν.nonneg S), zero_mul]
  refine ⟨ν, draw, ?_, ?_, ?_, ?_⟩
  · intro S
    by_cases h : valid S
    · exact Or.inr (by simpa only [draw, ite_eq_left h] using h)
    · exact Or.inl (by simp [draw, h])
  · intro x
    exact (hLaw (fun T => x ∈ T)).trans_le (hm x)
  · intro j
    exact (hLaw (fun T => ∃ x ∈ T, adj (L j) x)).trans_le (hAdj j)
  · intro h
    exact (hLaw (fun T => T = ∅)).trans (hEmpty h)

end LocallyRamsey
