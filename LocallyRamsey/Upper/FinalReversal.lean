module

public import LocallyRamsey.Upper.LocalBound
public import LocallyRamsey.Overlap
public import Mathlib.Data.Sym.Card

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*}

/-- Reversing each unordered pair with true flip bit. -/
@[expose] noncomputable def toggleEdges (G : SimpleGraph V) (flip : Sym2 V → Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.Adj x y ↔ flip s(x, y) = false)
  symm := ⟨fun {x y} h => ⟨Ne.symm h.1, by
    rw [Sym2.eq_swap (a := y)]
    exact ⟨fun h' => h.2.mp h'.symm, fun h' => (h.2.mpr h').symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Without a reversal on any pair of a set, its original clique or
independent-set structure is preserved. -/
theorem isNClique_toggle {G : SimpleGraph V} {w : Sym2 V → Bool} {A : Finset V}
    {r : ℕ} (h : G.IsNClique r A) (hflip : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → w s(x, y) = false) :
    (toggleEdges G w).IsNClique r A := by
  refine ⟨?_, h.card_eq⟩
  intro x hx y hy hxy
  exact ⟨hxy, iff_of_true (h.isClique hx hy hxy) (hflip x hx y hy hxy)⟩

theorem isNIndependent_toggle {G : SimpleGraph V} {w : Sym2 V → Bool} {A : Finset V}
    {r : ℕ} (h : Gᶜ.IsNClique r A) (hflip : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → w s(x, y) = false) :
    (toggleEdges G w)ᶜ.IsNClique r A := by
  refine ⟨?_, h.card_eq⟩
  intro x hx y hy hxy
  refine (SimpleGraph.compl_adj _ _ _).mpr ⟨hxy, fun hc => ?_⟩
  exact ((SimpleGraph.compl_adj G x y).mp (h.isClique hx hy hxy)).2
    (hc.2.mpr (hflip x hx y hy hxy))

variable [DecidableEq V] [Fintype V]

/-- For any fixed set, the probability of becoming a clique after
independent reversals is at most the product of the largest possible
pair probabilities. -/
theorem prob_clique_after_toggle_le (G : SimpleGraph V) (A : Finset V)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2) :
    (FiniteLaw.product (fun _ : Sym2 V => FiniteLaw.bernoulli p hp (by linarith))).event
      (fun w => (toggleEdges G w).IsClique (A : Set V)) ≤ (1 - p) ^ A.card.choose 2 := by
  classical
  let edges := A.offDiag.image Sym2.mk.uncurry
  let μ := fun _ : Sym2 V => FiniteLaw.bernoulli p hp (by linarith : p ≤ 1)
  have hex (e : Sym2 V) (he : e ∈ edges) :
      ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ s(x, y) = e := by
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp he
    have hh := Finset.mem_offDiag.mp hxy
    exact ⟨x, hh.1, y, hh.2.1, hh.2.2, heq⟩
  let forbidden (e : Sym2 V) (b : Bool) : Prop :=
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ s(x, y) = e ∧ ¬ (G.Adj x y ↔ b = false)
  have hlower (e : Sym2 V) (he : e ∈ edges) : p ≤ (μ e).event (forbidden e) := by
    obtain ⟨x, hx, y, hy, hxy, heq⟩ := hex e he
    let b := if G.Adj x y then true else false
    have hinc (c : Bool) (hc : c = b) : forbidden e c := by
      subst c
      refine ⟨x, hx, y, hy, hxy, heq, ?_⟩
      by_cases h : G.Adj x y <;> simp [b, h]
    refine le_trans ?_ ((μ e).event_mono hinc)
    rw [← FiniteLaw.mean_indicator]
    cases b <;> simp [μ, FiniteLaw.mean, show p ≤ 1 - p by linarith]
  have hsubset (w : Sym2 V → Bool) (hw : (toggleEdges G w).IsClique (A : Set V)) :
      ∀ e ∈ edges, ¬ forbidden e (w e) := by
    rintro e he ⟨x, hx, y, hy, hxy, rfl, hab⟩
    exact hab (hw hx hy hxy).2
  rw [← Sym2.card_image_offDiag A]
  exact ((FiniteLaw.product μ).event_mono hsubset).trans
    (FiniteLaw.event_no_success_in_coordinates_le μ edges forbidden hlower)

omit [Fintype V] in
/-- Complementation and reversal commute. -/
theorem compl_toggle (G : SimpleGraph V) (w : Sym2 V → Bool) :
    (toggleEdges G w)ᶜ = toggleEdges Gᶜ w := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [SimpleGraph.compl_adj, toggleEdges]
  · cases hw : w s(x, y) <;> simp [SimpleGraph.compl_adj, toggleEdges, hxy, hw]

/-- Union bound over the possible homogeneous sets of the prescribed
size in the graph after the final reversals. -/
theorem prob_homogeneous_after_toggle_le (G : SimpleGraph V) (r : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2) :
    (FiniteLaw.product (fun _ : Sym2 V => FiniteLaw.bernoulli p hp (by linarith))).event
      (fun w => ∃ A : Finset V, A.card = r ∧
        ((toggleEdges G w).IsClique (A : Set V) ∨ (toggleEdges G w)ᶜ.IsClique (A : Set V))) ≤
      2 * ((Fintype.card V).choose r : ℝ) * (1 - p) ^ r.choose 2 := by
  classical
  let μ := FiniteLaw.product (fun _ : Sym2 V => FiniteLaw.bernoulli p hp (by linarith : p ≤ 1))
  let sets := (Finset.univ : Finset V).powersetCard r
  let bad (z : Bool × ↥sets) (w : Sym2 V → Bool) : Prop :=
    (toggleEdges (if z.1 then G else Gᶜ) w).IsClique (z.2.val : Set V)
  have hbad (z : Bool × ↥sets) : μ.event (bad z) ≤ (1 - p) ^ r.choose 2 := by
    have hz := (Finset.mem_powersetCard.mp z.2.property).2
    have h := prob_clique_after_toggle_le (if z.1 then G else Gᶜ) z.2.val hp hp'
    rw [hz] at h
    exact h
  calc
    _ ≤ μ.event (fun w => ∃ z, bad z w) := μ.event_mono (by
      intro w ⟨A, hA, hcl⟩
      have hmem : A ∈ sets := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA⟩
      rcases hcl with h | h
      · exact ⟨(true, ⟨A, hmem⟩), by simpa [bad] using h⟩
      · exact ⟨(false, ⟨A, hmem⟩), by simpa [bad, compl_toggle] using h⟩)
    _ ≤ ∑ z, μ.event (bad z) := μ.event_exists_le_sum _
    _ ≤ ∑ _z : Bool × ↥sets, (1 - p) ^ r.choose 2 := Finset.sum_le_sum fun z _ => hbad z
    _ = _ := by simp [sets, nsmul_eq_mul, Nat.cast_mul]

omit [DecidableEq V] [Fintype V] in
/-- A subset of unaltered pairs of the desired order in each witness
set preserves the original local property at that smaller order. -/
theorem locallyRamsey_toggle_of_unaltered {G : SimpleGraph V} {w : Sym2 V → Bool}
    {m r t : ℕ} (hG : IsLocallyRamsey G m r)
    (hstable : ∀ A : Finset V, A.card = r →
      ∃ I : Finset V, I ⊆ A ∧ I.card = t ∧
        ∀ x ∈ I, ∀ y ∈ I, x ≠ y → w s(x, y) = false) :
    IsLocallyRamsey (toggleEdges G w) m t := by
  intro X hx
  obtain ⟨⟨K, hK, hcl⟩, ⟨I, hI, hind⟩⟩ := hG X hx
  obtain ⟨K', hK', hKcard, hKpairs⟩ := hstable K hcl.card_eq
  obtain ⟨I', hI', hIcard, hIpairs⟩ := hstable I hind.card_eq
  exact ⟨⟨K', hK'.trans hK, isNClique_toggle ⟨hcl.isClique.subset hK', hKcard⟩ hKpairs⟩,
    ⟨I', hI'.trans hI, isNIndependent_toggle ⟨hind.isClique.subset hI', hIcard⟩ hIpairs⟩⟩

/-- Number of unordered pairs reversed inside a specified set. -/
def reversedPairs (A : Finset V) (w : Sym2 V → Bool) : ℕ :=
  ((A.offDiag.image Sym2.mk.uncurry).filter fun e => w e = true).card

omit [Fintype V] in
theorem sum_closedNeighbors_after_reversals (A : Finset V) (w : Sym2 V → Bool)
    [DecidableRel (toggleEdges (⊥ : SimpleGraph V) w).Adj] :
    (∑ x ∈ A, (closedNeighbors (toggleEdges (⊥ : SimpleGraph V) w) A x).card) =
      A.card + 2 * reversedPairs A w := by
  classical
  let edges := A.offDiag.image Sym2.mk.uncurry
  let hit (e : Sym2 V) := if w e = true then (1 : ℕ) else 0
  have hcard (x : V) (hx : x ∈ A) :
      (closedNeighbors (toggleEdges (⊥ : SimpleGraph V) w) A x).card =
        1 + ∑ y ∈ A, if x ≠ y then hit s(x, y) else 0 := by
    simp only [closedNeighbors, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hdecompose (y : V) :
        (if x = y ∨ (toggleEdges (⊥ : SimpleGraph V) w).Adj x y then 1 else 0) =
        (if x = y then 1 else 0) + (if x ≠ y then hit s(x, y) else 0) := by
      by_cases hxy : x = y <;> cases hbit : w s(x, y) <;> simp [hxy, toggleEdges, hit, hbit]
    simp_rw [hdecompose, Finset.sum_add_distrib]
    simp [hx]
  rw [Finset.sum_congr rfl hcard, Finset.sum_add_distrib]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  congr 1
  have hsum : (∑ x ∈ A, ∑ y ∈ A, if x ≠ y then hit s(x, y) else 0) =
      ∑ z ∈ A.offDiag, hit (Sym2.mk.uncurry z) := by
    rw [← Finset.sum_product A A (fun z : V × V => if z.1 ≠ z.2 then hit s(z.1, z.2) else 0)]
    have heq : ((A ×ˢ A).filter (fun z : V × V => z.1 ≠ z.2)) = A.offDiag := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
      tauto
    rw [← Finset.sum_filter, heq]
    rfl
  rw [hsum]
  have hfiber (e : Sym2 V) (he : e ∈ edges) :
      ∑ z ∈ A.offDiag.filter (fun z => Sym2.mk.uncurry z = e), hit (Sym2.mk.uncurry z) =
        2 * hit e := by
    obtain ⟨⟨x, y⟩, hz, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hz
    have hset : A.offDiag.filter (fun z => Sym2.mk.uncurry z = s(x, y)) =
        {(x, y), (y, x)} := by
      ext z
      obtain ⟨u, v⟩ := z
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton]
      change (_ ∧ s(u, v) = s(x, y)) ↔ _
      rw [show s(u, v) = s(x, y) ↔ (u, v) = (x, y) ∨ (u, v) = (y, x) from
        Sym2.mk_eq_mk_iff (p := (u, v)) (q := (x, y))]
      constructor
      · exact And.right
      · rintro (h | h)
        · cases h
          exact ⟨⟨hx, hy, hne⟩, Or.inl rfl⟩
        · cases h
          exact ⟨⟨hy, hx, Ne.symm hne⟩, Or.inr rfl⟩
    change (∑ z ∈ A.offDiag.filter (fun z => Sym2.mk.uncurry z = s(x, y)),
      hit (Sym2.mk.uncurry z)) = 2 * hit s(x, y)
    rw [hset, Finset.sum_pair (fun h => hne (congrArg Prod.fst h))]
    change hit s(x, y) + hit s(y, x) = _
    rw [Sym2.eq_swap (a := y), two_mul]
  calc
    _ = ∑ e ∈ edges, ∑ z ∈ A.offDiag.filter
        (fun z => Sym2.mk.uncurry z = e), hit (Sym2.mk.uncurry z) := by
      exact (Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem _ hz) _).symm
    _ = ∑ e ∈ edges, 2 * hit e := Finset.sum_congr rfl hfiber
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      change ∑ e ∈ edges, (if w e = true then 1 else 0) =
        (edges.filter (fun e => w e = true)).card
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]

/-- Exponential upper tail for the number of altered pairs in a fixed
set. It applies to the last, independent round of reversals. -/
theorem prob_reversedPairs_ge (A : Finset V) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1) {t : ℝ} (ht : 0 < t) (D : ℝ) :
    (FiniteLaw.product (fun _ : Sym2 V => FiniteLaw.bernoulli p hp hp')).event
      (fun w => D ≤ (reversedPairs A w : ℝ)) ≤
      Real.exp ((Real.exp t - 1) * (A.card.choose 2 : ℝ) * p - t * D) := by
  classical
  let edges := A.offDiag.image Sym2.mk.uncurry
  let μ := fun _ : Sym2 V => FiniteLaw.bernoulli p hp hp'
  let X (e : Sym2 V) (b : Bool) := if e ∈ edges ∧ b = true then (1 : ℝ) else 0
  have hX (e b) : X e b ∈ Set.Icc (0 : ℝ) 1 := by dsimp [X]; split <;> norm_num
  have hsum (w : Sym2 V → Bool) : (reversedPairs A w : ℝ) = ∑ e, X e (w e) := by
    have hset : ((Finset.univ : Finset (Sym2 V)).filter
        (fun e => e ∈ edges ∧ w e = true)) = edges.filter (fun e => w e = true) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold reversedPairs
    change ((edges.filter (fun e => w e = true)).card : ℝ) = _
    rw [← hset, Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, Finset.sum_filter, X]
  have hmean (e : Sym2 V) : (μ e).mean (X e) = if e ∈ edges then p else 0 := by
    by_cases he : e ∈ edges <;> simp [FiniteLaw.mean, X, μ, he]
  have hsum_mean : (∑ e, (μ e).mean (X e)) = (A.card.choose 2 : ℝ) * p := by
    simp_rw [hmean, ← Finset.sum_filter]
    rw [show (Finset.univ.filter (fun e => e ∈ edges)) = edges by ext; simp,
      Finset.sum_const, nsmul_eq_mul]
    unfold edges
    rw [Sym2.card_image_offDiag]
  simp_rw [hsum]
  have h := FiniteLaw.prob_sum_ge_le μ X hX ht D
  rw [hsum_mean] at h
  simpa only [mul_assoc] using h

end LocallyRamsey
