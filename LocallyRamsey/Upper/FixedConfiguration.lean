module

public import LocallyRamsey.Upper.ManyPairs
public import Mathlib.Data.Finset.Powerset

public section

namespace LocallyRamsey.BinaryTree

/-- Failure probability for one fixed choice of the branches and the
candidate cliques. The unordered pairs of branches are counted by
the two-element subsets of the set of branch labels. -/
theorem probability_fixed_configuration {T j : ℕ} (hj : j + 1 ≤ T)
    {a s : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (P : Finset ℕ) (K : ℕ → Finset (Leaf T))
    (hpos : 0 < a) (hK : ∀ u ∈ P, (K u).card = a ∧
      ∀ x ∈ K u, ancestor (j + 1) x = u)
    (hroom : s ≤ a + a)
    (hbudget : (a : ℝ) * a * ((T - (j + 1) : ℕ) * p) / ((a + a - s + 1 : ℕ) : ℝ) ≤ 1 / 2)
    (desired : Bool) :
    (reversalLaw T p hp (by linarith)).event (fun ω =>
      (∀ u ∈ P, (graphFor T (reversals ω) desired).IsClique (K u : Set (Leaf T))) ∧
      (∀ u ∈ P, ∀ v ∈ P, u ≠ v →
        ¬ HasClique (graphFor T (reversals ω) desired) s (K u ∪ K v))) ≤
      (1 - p / 2) ^ P.card.choose 2 := by
  classical
  have hrep (u : {u // u ∈ P}) : ∃ z : Leaf T, ancestor (j + 1) z = u.val := by
    have hc : (K u.val).Nonempty := Finset.card_pos.mp (by rw [(hK u.val u.property).1]; exact hpos)
    obtain ⟨z, hz⟩ := hc
    exact ⟨z, (hK u.val u.property).2 z hz⟩
  choose rep hrep using hrep
  let two := P.powersetCard 2
  have hpair (z : {z // z ∈ two}) :
      ∃ u v : {u // u ∈ P}, u.val ≠ v.val ∧ z.val = {u.val, v.val} := by
    obtain ⟨hsub, hc⟩ := Finset.mem_powersetCard.mp z.property
    obtain ⟨u, v, huv, he⟩ := Finset.card_eq_two.mp hc
    refine ⟨⟨u, hsub ?_⟩, ⟨v, hsub ?_⟩, huv, he⟩ <;> simp [he]
  choose left right hpairs using hpair
  let tag (z : {z // z ∈ two}) : {e : Option (Sym2 (Leaf T)) // e ≠ none} :=
    ⟨some s(node hj (rep (left z)), node hj (rep (right z))), by simp⟩
  have htag : Function.Injective tag := by
    intro z z' he
    have hsym := Option.some.inj (congrArg Subtype.val he)
    rcases (Sym2.mk_eq_mk_iff (p := (node hj (rep (left z)), node hj (rep (right z))))
      (q := (node hj (rep (left z')), node hj (rep (right z'))))).mp hsym with h | h
    · have hl : (left z).val = (left z').val := by
        simpa [node, hrep] using congrArg (fun e : Leaf T × Leaf T => e.1.val) h
      have hr : (right z).val = (right z').val := by
        simpa [node, hrep] using congrArg (fun e : Leaf T × Leaf T => e.2.val) h
      exact Subtype.ext (by rw [(hpairs z).2, (hpairs z').2, hl, hr])
    · have hl : (left z).val = (right z').val := by
        simpa [node, hrep] using congrArg (fun e : Leaf T × Leaf T => e.1.val) h
      have hr : (right z).val = (left z').val := by
        simpa [node, hrep] using congrArg (fun e : Leaf T × Leaf T => e.2.val) h
      exact Subtype.ext (by rw [(hpairs z).2, (hpairs z').2, hl, hr, Finset.pair_comm])
  let active := Finset.univ.image tag
  let index (e : {e : Option (Sym2 (Leaf T)) // e ≠ none}) (he : e ∈ active) :=
    Classical.choose (Finset.mem_image.mp he)
  have hindex (e : {e : Option (Sym2 (Leaf T)) // e ≠ none}) (he : e ∈ active) :
      tag (index e he) = e := (Classical.choose_spec (Finset.mem_image.mp he)).2
  let x (e : {e : Option (Sym2 (Leaf T)) // e ≠ none}) : Leaf T :=
    if he : e ∈ active then rep (left (index e he)) else ⟨0, by positivity⟩
  let y (e : {e : Option (Sym2 (Leaf T)) // e ≠ none}) : Leaf T :=
    if he : e ∈ active then rep (right (index e he)) else ⟨0, by positivity⟩
  let A (e : {e : Option (Sym2 (Leaf T)) // e ≠ none}) : Finset (Leaf T) :=
    if he : e ∈ active then K (left (index e he)).val else ∅
  let B (e : {e : Option (Sym2 (Leaf T)) // e ≠ none}) : Finset (Leaf T) :=
    if he : e ∈ active then K (right (index e he)).val else ∅
  have hx e (he : e ∈ active) : ancestor (j + 1) (x e) = (left (index e he)).val := by
    simp [x, he, hrep]
  have hy e (he : e ∈ active) : ancestor (j + 1) (y e) = (right (index e he)).val := by
    simp [y, he, hrep]
  have ha e (he : e ∈ active) : A e = K (left (index e he)).val := by simp [A, he]
  have hb e (he : e ∈ active) : B e = K (right (index e he)).val := by simp [B, he]
  have hcid : active.card = P.card.choose 2 := by
    rw [show active = Finset.univ.image tag from rfl, Finset.card_image_of_injective _ htag,
      Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard]
  rw [← hcid]
  refine (FiniteLaw.event_mono _ ?_).trans (probability_all_pairs_fail hj active x y A B
    ?_ ?_ ?_ ?_ desired (s := s) ?_ hp hp' ?_)
  · intro ω ⟨hcl, hnone⟩
    constructor
    · intro e he
      rw [ha e he, hb e he]
      exact ⟨hcl _ (left (index e he)).property, hcl _ (right (index e he)).property⟩
    · intro e he
      rw [ha e he, hb e he]
      exact hnone _ (left (index e he)).property _ (right (index e he)).property
        (hpairs (index e he)).1
  · intro e he
    rw [hx e he, hy e he]
    exact (hpairs (index e he)).1
  · intro e he
    have hval := congrArg Subtype.val (hindex e he)
    simpa [x, y, he, tag] using hval.symm
  · intro e he z hz
    rw [hx e he]
    rw [ha e he] at hz
    exact (hK _ (left (index e he)).property).2 _ hz
  · intro e he z hz
    rw [hy e he]
    rw [hb e he] at hz
    exact (hK _ (right (index e he)).property).2 _ hz
  · intro e he
    rw [ha e he, hb e he, (hK _ (left (index e he)).property).1,
      (hK _ (right (index e he)).property).1]
    exact hroom
  · intro e he
    rw [ha e he, hb e he, (hK _ (left (index e he)).property).1,
      (hK _ (right (index e he)).property).1]
    exact hbudget

end LocallyRamsey.BinaryTree
