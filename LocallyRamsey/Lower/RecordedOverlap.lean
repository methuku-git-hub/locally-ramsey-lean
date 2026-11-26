module

public import LocallyRamsey.Lower.CliqueOverlap
public import LocallyRamsey.Lower.NamedRecords

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- A clique occupies at most one vertex in each independent set drawn.
After exposing a prescribed set of draws, the remaining hit count is
therefore at least the clique order minus the number of exposed draws. -/
theorem card_clique_le_named_add_hits {l : ℕ} (G : SimpleGraph V) (A : Finset (Fin l))
    (draw : Fin l → Finset V) (hdraw : ∀ i, Gᶜ.IsClique (draw i : Set V))
    (Q C : Finset V) (hQ : G.IsClique (Q : Set V)) (hQC : Q ⊆ C)
    (hcover : ∀ x ∈ Q, ∃ i, x ∈ draw i) :
    (Q.card : ℝ) ≤ A.card +
      ∑ i : {i // i ∉ A}, (if ¬Disjoint C (draw i.val) then (1 : ℝ) else 0) := by
  classical
  let fresh := (Finset.univ : Finset {i // i ∉ A}).filter (fun i => ¬Disjoint C (draw i.val))
  let assign (x : ↥Q) := Classical.choose (hcover x.val x.property)
  have has (x : ↥Q) : x.val ∈ draw (assign x) := Classical.choose_spec (hcover x.val x.property)
  have hinj : Function.Injective assign := by
    intro x y h
    apply Subtype.ext
    by_contra hxy
    have hcl := hQ x.property y.property hxy
    have hind := hdraw (assign x) (has x) (h ▸ has y) hxy
    exact ((SimpleGraph.compl_adj G x.val y.val).mp hind).2 hcl
  let f (x : ↥Q) : ↥A ⊕ ↥fresh :=
    if h : assign x ∈ A then Sum.inl ⟨assign x, h⟩
    else Sum.inr ⟨⟨assign x, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hd =>
      Finset.disjoint_left.mp hd (hQC x.property) (has x)⟩⟩
  let π (a : ↥A ⊕ ↥fresh) : Fin l := a.elim Subtype.val (fun i => i.val.val)
  have hπ (x : ↥Q) : π (f x) = assign x := by
    unfold f
    split <;> rfl
  have hfinj : Function.Injective f := by
    intro x y h
    exact hinj ((hπ x).symm.trans ((congrArg π h).trans (hπ y)))
  have hcard := Fintype.card_le_of_injective f hfinj
  rw [Fintype.card_coe, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe] at hcard
  have hfresh : (fresh.card : ℝ) =
      ∑ i : {i // i ∉ A}, (if ¬Disjoint C (draw i.val) then (1 : ℝ) else 0) := by
    rw [← Finset.sum_filter]
    simp only [fresh, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← hfresh]
  exact_mod_cast hcard

variable [LinearOrder V]

/-- Data fixed by one initial description after the list, all samples, and
the named draws have been exposed. The weights include the indicator of
the test that keeps the group. -/
structure CliqueOverlapData (V J Ω : Type*) (q : ℕ) where
  region : Finset V
  groupWeight : J → V → ℝ
  badVertices : J → Finset V
  retained : J → Fin q → Finset V
  keptDraw : Ω → Finset V

/-- Conditional form of the lower overlap after locating the clique.
The further records used by the degree restriction are encoded as draws
and positions within draws. The union bound conditions on exactly those
draws and the draws of the initial description. -/
theorem event_no_lower_overlap_after_location_le {J Ω D₀ : Type*}
    [Fintype J] [Fintype Ω] [Fintype D₀]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (π : FiniteLaw J) (μ : FiniteLaw Ω) {q l b H s r : ℕ} (hq : 0 < q)
    (A₀ : D₀ → Finset (Fin l)) (hA₀ : ∀ a, (A₀ a).card ≤ s)
    (data : (a : D₀) → ({i // i ∈ A₀ a} → Ω) → CliqueOverlapData V J Ω q)
    (valid : (a : D₀) → ({i // i ∈ A₀ a} → Ω) → Prop)
    (enumerate : Ω → Fin b → V)
    (γ g η D K cap : ℝ) (hη : 0 < η) (hD : 1 < D)
    (hγ : 0 ≤ γ) (hg : 0 ≤ g) (hK : 0 ≤ K) (hγg : 9 * γ ≤ g)
    (hηg : η * cap ≤ g) (hH : ⌈D * Real.log (1 + 1 / η)⌉₊ ≤ H)
    (hdata : ∀ a e, valid a e →
      let u := data a e
      (∀ j x, 0 ≤ u.groupWeight j x) ∧
      π.mean (fun j => mass (u.groupWeight j) u.region) ≤ cap ∧
      π.mean (fun j => mass (u.groupWeight j) (u.badVertices j)) ≤ γ ∧
      (∀ j x, x ∈ u.region → x ∉ u.badVertices j →
        γ / 8 * (q : ℝ) ≤ ((Finset.univ.filter (fun i => x ∈ u.retained j i)).card : ℝ)) ∧
      (∀ ω, Gᶜ.IsClique (u.keptDraw ω : Set V)) ∧
      (∀ ω x, x ∈ u.keptDraw ω → ∃ k, enumerate ω k = x) ∧
      (∀ C : Finset V, C ⊆ u.region →
        μ.event (fun ω => ¬Disjoint C (u.keptDraw ω)) ≤
          K * π.mean (fun j => mass (u.groupWeight j) C))) :
    (FiniteLaw.product (fun _ : Fin l => μ)).event (fun ω =>
      ∃ a, valid a (fun i => ω i.val) ∧
        let u := data a (fun i => ω i.val)
        (∃ Q : Finset V, Q ⊆ u.region ∧ G.IsClique (Q : Set V) ∧ r ≤ Q.card ∧
          ∀ x ∈ Q, ∃ i, x ∈ u.keptDraw (ω i)) ∧
        ¬ ∃ C : Finset V, C ⊆ u.region ∧
          let v := π.mean (fun j => mass (u.groupWeight j) C)
          g ≤ v ∧ (∀ x ∈ C, π.mean (fun j => mass (u.groupWeight j) (nonNeighbors G C x)) ≤ 2 * v / D) ∧
          γ * v / 9 ≤ π.mean (fun j => (∑ i, mass (u.groupWeight j) (C ∩ u.retained j i)) / q)) ≤
      ((Fintype.card D₀ : ℝ) * ((l * b : ℕ) + 1 : ℕ) ^ H) *
        Real.exp ((l : ℝ) * (K * g) - Real.log 2 * ((r : ℝ) - s - H)) := by
  classical
  let J' := D₀ × RecordDescription l b H
  let A (j : J') := A₀ j.1 ∪ namedDraws j.2
  let first (j : J') (e : {i // i ∈ A j} → Ω) (i : {i // i ∈ A₀ j.1}) :=
    e ⟨i.val, Finset.mem_union_left _ i.property⟩
  let u (j : J') (e : {i // i ∈ A j} → Ω) := data j.1 (first j e)
  let t (j : J') (e : {i // i ∈ A j} → Ω) (x : V) :=
    π.mean (fun a => (u j e).groupWeight a x)
  let R (j : J') (e : {i // i ∈ A j} → Ω) :=
    decodeRecordDescription j.2 enumerate (fun i => e ⟨i.val, Finset.mem_union_right _ i.property⟩)
  let C (j : J') (e : {i // i ∈ A j} → Ω) :=
    R j e ∪ recordRemainder Gᶜ (chooseHeavy Gᶜ (t j e) (η * cap) D) (R j e)
      (u j e).region.card (u j e).region
  let enabled (j : J') (e : {i // i ∈ A j} → Ω) :=
    valid j.1 (first j e) ∧ C j e ⊆ (u j e).region
  have hmean (j : J') (e : {i // i ∈ A j} → Ω) (F : Finset V) :
      π.mean (fun i => mass ((u j e).groupWeight i) F) = mass (t j e) F := by
    simp only [mass, FiniteLaw.mean_sum, t]
  have hh (j : J') (e : {i // i ∈ A j} → Ω) (h : enabled j e) :
      μ.event (fun ω => ¬Disjoint (C j e) ((u j e).keptDraw ω)) ≤ K * mass (t j e) (C j e) := by
    rw [← hmean]
    exact (hdata j.1 (first j e) h.1).2.2.2.2.2.2 _ h.2
  have hP := event_low_mass_description_le μ l A C t enabled (fun j e => (u j e).keptDraw)
    (target := (r : ℝ) - s - H) hK hg hh
  have hCard : (Fintype.card J' : ℝ) = (Fintype.card D₀ : ℝ) * ((l * b : ℕ) + 1 : ℕ) ^ H := by
    norm_num [J', Fintype.card_prod, Fintype.card_fun, Fintype.card_option, add_comm]
  rw [hCard] at hP
  refine ((FiniteLaw.product (fun _ : Fin l => μ)).event_mono ?_).trans hP
  rintro ω ⟨a, hva, ⟨Q, hQW, hQcl, hQr, hQcover⟩, hbad⟩
  let ua := data a (fun i => ω i.val)
  obtain ⟨hw, hcap, hbadMass, hcount, hdraw, hEnum, _⟩ := hdata a (fun i => ω i.val) hva
  by_contra hnone
  have hrecord (R₀ : Finset V) (hRQ : R₀ ⊆ Q)
      (hRC : R₀.card ≤ ⌈D * Real.log (1 + 1 / η)⌉₊) :
      let t₀ := fun x => π.mean (fun j => ua.groupWeight j x)
      let C₀ := R₀ ∪ recordRemainder Gᶜ (chooseHeavy Gᶜ t₀ (η * cap) D) R₀ ua.region.card ua.region
      Q ⊆ C₀ → C₀ ⊆ ua.region → g ≤ mass t₀ C₀ := by
    intro t₀ C₀ hQsub hCsub
    by_contra! hsmall
    have hVals (x : V) (hx : x ∈ R₀) : ∃ (i : Fin l) (k : Fin b), enumerate (ω i) k = x := by
      obtain ⟨i, hi⟩ := hQcover x (hRQ hx)
      obtain ⟨k, hk⟩ := hEnum (ω i) x hi
      exact ⟨i, k, hk⟩
    obtain ⟨d, hd⟩ := exists_recordDescription R₀ (hRC.trans hH) enumerate ω hVals
    let j : J' := (a, d)
    let e : {i // i ∈ A j} → Ω := fun i => ω i.val
    have hR : R j e = R₀ := hd
    have hC : C j e = C₀ := by dsimp [C, C₀, t₀, t, u, ua, first, j, e]; rw [hR]
    have hCe : C j e ⊆ (u j e).region := hC.symm ▸ hCsub
    have hhit := card_clique_le_named_add_hits G (A j) (fun i => ua.keptDraw (ω i))
      (fun i => hdraw (ω i)) Q C₀ hQcl hQsub hQcover
    have ha : (A j).card ≤ s + H := by
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hA₀ a) (namedDraws_card_le d))
    have ha' : ((A j).card : ℝ) ≤ s + H := by exact_mod_cast ha
    have hQr' : (r : ℝ) ≤ Q.card := by exact_mod_cast hQr
    have hcount' : (r : ℝ) - s - H ≤ ∑ i : {i // i ∉ A j},
        (if ¬Disjoint (C j e) ((u j e).keptDraw (ω i.val)) then (1 : ℝ) else 0) := by
      rw [hC]
      change _ ≤ ∑ i : {i // i ∉ A j},
        (if ¬Disjoint C₀ (ua.keptDraw (ω i.val)) then (1 : ℝ) else 0)
      linarith only [hhit, ha', hQr']
    exact hnone ⟨j, ⟨hva, hCe⟩, by rw [hC]; exact hsmall, hcount'⟩
  obtain ⟨C₀, _, hsub, hOV⟩ := exists_recorded_clique_overlap G π q hq ua.region Q hQW hQcl
    ua.groupWeight hw cap γ g η D hη hD hγ hγg hηg hcap ua.badVertices ua.retained
    hbadMass hcount hrecord
  exact hbad ⟨C₀, hsub, hOV⟩

end LocallyRamsey
