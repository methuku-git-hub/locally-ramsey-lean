module

public import LocallyRamsey.Upper.PairMerging

public section

namespace LocallyRamsey.BinaryTree

variable {T j : ℕ}

/-- Coin values fixed by the exposure at depth `j`. -/
abbrev ExposedCoin (T j : ℕ) := {c : Coin T // exposureBlock j c = none}

/-- Fill the exposed block, with zero values outside it. -/
def exposedWorld (data : ExposedCoin T j → Bool) (c : Coin T) : Bool :=
  if h : exposureBlock j c = none then data ⟨c, h⟩ else false

theorem exposedWorld_agrees (ω : Coin T → Bool)
    {c : Coin T} (hc : exposureBlock j c = none) :
    exposedWorld (j := j) (fun z => ω z.val) c = ω c := by
  simp [exposedWorld, hc]

theorem read_block {ι β : Type*} {label : ι → β}
    (w : (b : β) → ({c // label c = b} → Bool))
    {c : ι} {b : β} (h : label c = b) : w (label c) ⟨c, rfl⟩ = w b ⟨c, h⟩ := by
  subst b
  rfl

/-- For a fixed collection of pairs of branches with prescribed
endpoint sets, simultaneous failure has a product bound. Validity of
the endpoint cliques is determined from the exposed block. -/
theorem probability_all_pairs_fail {k : ℕ} (ht : k + 1 ≤ T)
    (active : Finset {e : Option (Sym2 (Leaf T)) // e ≠ none})
    (x y : {e : Option (Sym2 (Leaf T)) // e ≠ none} → Leaf T)
    (A B : {e : Option (Sym2 (Leaf T)) // e ≠ none} → Finset (Leaf T))
    (hs : ∀ e ∈ active, ancestor (k + 1) (x e) ≠ ancestor (k + 1) (y e))
    (hid : ∀ e ∈ active, e.1 = some s(node ht (x e), node ht (y e)))
    (hA : ∀ e ∈ active, ∀ v ∈ A e, ancestor (k + 1) v = ancestor (k + 1) (x e))
    (hB : ∀ e ∈ active, ∀ v ∈ B e, ancestor (k + 1) v = ancestor (k + 1) (y e))
    (desired : Bool) {s : ℕ} (hroom : ∀ e ∈ active, s ≤ (A e).card + (B e).card)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hbudget : ∀ e ∈ active, ((A e).card : ℝ) * (B e).card * ((T - (k + 1) : ℕ) * p) /
      (((A e).card + (B e).card - s + 1 : ℕ) : ℝ) ≤ 1 / 2) :
    (reversalLaw T p hp (by linarith)).event (fun ω =>
      (∀ e ∈ active, (graphFor T (reversals ω) desired).IsClique (A e : Set (Leaf T)) ∧
          (graphFor T (reversals ω) desired).IsClique (B e : Set (Leaf T))) ∧
      (∀ e ∈ active, ¬ HasClique (graphFor T (reversals ω) desired) s (A e ∪ B e))) ≤
      (1 - p / 2) ^ active.card := by
  classical
  -- The product of the exposure block and the individual pair blocks
  -- is the original random reversal experiment.
  let label := exposureBlock (T := T) (k + 1)
  let coinLaw := fun _ : Coin T => FiniteLaw.bernoulli p hp (by linarith : p ≤ 1)
  let law (a : Option (Sym2 (Leaf T))) :=
    FiniteLaw.product (fun z : {c : Coin T // label c = a} => coinLaw z.val)
  let Kept (e : Option (Sym2 (Leaf T))) := {c : Coin T // label c = e} → Bool
  let join (ω : (e : Option (Sym2 (Leaf T))) → Kept e) : Coin T → Bool :=
    fun c => ω (label c) ⟨c, rfl⟩
  let P (ω : Coin T → Bool) :=
    (∀ e ∈ active, (graphFor T (reversals ω) desired).IsClique (A e : Set (Leaf T)) ∧
      (graphFor T (reversals ω) desired).IsClique (B e : Set (Leaf T))) ∧
      (∀ e ∈ active, ¬ HasClique (graphFor T (reversals ω) desired) s (A e ∪ B e))
  have hevent :
      (reversalLaw T p hp (by linarith)).event P =
        (FiniteLaw.product law).event (fun w => P (join w)) := by
    let indicator (ω : Coin T → Bool) : ℝ := @ite ℝ (P ω) (Classical.propDecidable _) 1 0
    have h := FiniteLaw.mean_on_blocks coinLaw label (fun w => indicator (join w))
    change (FiniteLaw.product coinLaw).mean indicator =
      (FiniteLaw.product law).mean (fun w => indicator (join w)) at h
    rw [← FiniteLaw.mean_indicator, ← FiniteLaw.mean_indicator]
    exact h
  rw [show (fun ω => (∀ e ∈ active, (graphFor T (reversals ω) desired).IsClique (A e : Set (Leaf T)) ∧
          (graphFor T (reversals ω) desired).IsClique (B e : Set (Leaf T))) ∧
      (∀ e ∈ active, ¬ HasClique (graphFor T (reversals ω) desired) s (A e ∪ B e))) = P from rfl, hevent]
  let enabled (data : Kept none) := ∀ e ∈ active,
    (graphFor T (reversals (exposedWorld data)) desired).IsClique (A e : Set (Leaf T)) ∧
    (graphFor T (reversals (exposedWorld data)) desired).IsClique (B e : Set (Leaf T))
  let attempt (data : Kept none) (e : {z : Option (Sym2 (Leaf T)) // z ≠ none})
      (coins : Kept e.val) : Coin T → Bool :=
    fun c => if hc : label c = e.val then coins ⟨c, hc⟩ else exposedWorld data c
  let good (data : Kept none) (e : {z : Option (Sym2 (Leaf T)) // z ≠ none}) (coins : Kept e.val) :=
    HasClique (graphFor T (reversals (attempt data e coins)) desired) s (A e ∪ B e)
  have hlimit :
      (FiniteLaw.product law).event (fun w =>
        enabled (w none) ∧ ∀ e ∈ active, ¬ good (w none) e (w e.val)) ≤ (1 - p / 2) ^ active.card := by
    apply FiniteLaw.event_no_success_after_exposure law none active enabled good (by linarith)
    intro data hen e he
    obtain ⟨val, hne⟩ := e
    cases val with
    | none => exact (hne rfl).elim
    | some z =>
      have hz := Option.some.inj (hid ⟨some z, hne⟩ he)
      exact probability_merge_pair_at_label ht _ _ (hs _ he) hz
        (exposedWorld data) desired (A _) (B _) (hA _ he) (hB _ he) (hen _ he)
        (hroom _ he) hp hp' (hbudget _ he)
  refine (FiniteLaw.event_mono _ ?_).trans hlimit
  intro w hw
  obtain ⟨hcl, hfail⟩ := hw
  have hbase {c : Coin T} (hc : exposureBlock (k + 1) c = none) :
      exposedWorld (w none) c = join w c := by
    change exposedWorld (w none) c = w (label c) ⟨c, rfl⟩
    rw [exposedWorld, dite_eq_left hc]
    exact (read_block w hc).symm
  constructor
  · intro e he
    constructor
    · intro a ha b hb hab
      apply (graphFor_adj_iff hab).mpr
      rw [adjacency_fixed_on_branch ht ((hA e he a ha).trans (hA e he b hb).symm)
        (fun _ hc => hbase hc)]
      exact (graphFor_adj_iff hab).mp ((hcl e he).1 ha hb hab)
    · intro a ha b hb hab
      apply (graphFor_adj_iff hab).mpr
      rw [adjacency_fixed_on_branch ht ((hB e he a ha).trans (hB e he b hb).symm)
        (fun _ hc => hbase hc)]
      exact (graphFor_adj_iff hab).mp ((hcl e he).2 ha hb hab)
  · intro e he hgood
    apply hfail e he
    obtain ⟨K, hK, hKcl, hKcard⟩ := hgood
    refine ⟨K, hK, ⟨?_, hKcard⟩⟩
    intro a ha b hb hab
    apply (graphFor_adj_iff hab).mpr
    have hgoodAdj := (graphFor_adj_iff hab).mp (hKcl ha hb hab)
    have ht0 {c : Coin T} (hc : exposureBlock (k + 1) c = none) :
        join w c = attempt (w none) e (w e.val) c := by
      simp [attempt, label, hc, e.property.symm, hbase hc]
    have ht1 {c : Coin T} (hc : exposureBlock (k + 1) c = e.val) :
        join w c = attempt (w none) e (w e.val) c := by
      change w (label c) ⟨c, rfl⟩ = attempt (w none) e (w e.val) c
      dsimp only [attempt]
      rw [dite_eq_left hc]
      exact read_block w hc
    have hK' (z : Leaf T) (hz : z ∈ K) : z ∈ A e ∨ z ∈ B e :=
      Finset.mem_union.mp (hK hz)
    rcases hK' a ha with ha' | ha' <;> rcases hK' b hb with hb' | hb'
    · rwa [adjacency_fixed_on_branch ht ((hA e he a ha').trans (hA e he b hb').symm)
        (fun _ hc => ht0 hc)]
    · rw [adjacency_fixed_on_pair ht a b (fun c hc => hc.elim ht0 (fun h => ht1 (h.trans (by
            rw [hid e he]
            congr 2
            · exact Fin.ext (hA e he a ha')
            · exact Fin.ext (hB e he b hb')))))]
      exact hgoodAdj
    · rw [adjacency_fixed_on_pair ht a b (fun c hc => hc.elim ht0 (fun h => ht1 (h.trans (by
            rw [hid e he, Sym2.eq_swap (a := node ht a)]
            congr 2
            · exact Fin.ext (hA e he b hb')
            · exact Fin.ext (hB e he a ha')))))]
      exact hgoodAdj
    · rwa [adjacency_fixed_on_branch ht ((hB e he a ha').trans (hB e he b hb').symm)
        (fun _ hc => ht0 hc)]

end LocallyRamsey.BinaryTree
