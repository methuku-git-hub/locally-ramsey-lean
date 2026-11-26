module

public import LocallyRamsey.Upper.ReversalLaw

@[expose] public section

namespace LocallyRamsey.BinaryTree

variable {T : ℕ}

/-- The cross-branch coins for one unordered pair of branches. -/
abbrev PairCoin (j : ℕ) (e : Sym2 (Leaf T)) :=
  {c : Coin T // exposureBlock j c = some e}

/-- Replace just the coins between the specified branches. -/
def withPairCoins {j : ℕ} {e : Sym2 (Leaf T)}
    (base : Coin T → Bool) (coins : PairCoin j e → Bool) (c : Coin T) : Bool :=
  if hc : exposureBlock j c = some e then coins ⟨c, hc⟩ else base c

theorem withPairCoins_of_mem {j : ℕ} {e : Sym2 (Leaf T)}
    (base : Coin T → Bool) (coins : PairCoin j e → Bool)
    (c : PairCoin j e) : withPairCoins base coins c.val = coins c := by
  simp [withPairCoins, c.property]

theorem withPairCoins_of_exposed {j : ℕ} {e : Sym2 (Leaf T)}
    (base : Coin T → Bool) (coins : PairCoin j e → Bool)
    {c : Coin T} (hc : exposureBlock j c = none) :
    withPairCoins base coins c = base c := by
  simp [withPairCoins, hc]

/-- Lemma 2 for one pair of branches. After fixing all exposed data, the
cross-branch coins give a merge with probability at least `p/2`.
The numerical assumption is the missing-edge budget from Markov's inequality. -/
theorem probability_merge_pair {j : ℕ} (hj : j + 1 ≤ T)
    (x₀ y₀ : Leaf T) (hsep : ancestor (j + 1) x₀ ≠ ancestor (j + 1) y₀)
    (base : Coin T → Bool) (desired : Bool)
    (A B : Finset (Leaf T))
    (hA : ∀ x ∈ A, ancestor (j + 1) x = ancestor (j + 1) x₀)
    (hB : ∀ y ∈ B, ancestor (j + 1) y = ancestor (j + 1) y₀)
    (hcl : (graphFor T (reversals base) desired).IsClique (A : Set (Leaf T)) ∧
      (graphFor T (reversals base) desired).IsClique (B : Set (Leaf T)))
    {s : ℕ} (hroom : s ≤ A.card + B.card) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hbudget : (A.card : ℝ) * B.card * ((T - (j + 1) : ℕ) * p) /
      ((A.card + B.card - s + 1 : ℕ) : ℝ) ≤ 1 / 2) :
    let e := s(node hj x₀, node hj y₀)
    let ν := FiniteLaw.product (fun _ : PairCoin (j + 1) e =>
      FiniteLaw.bernoulli p hp (by linarith : p ≤ 1))
    p / 2 ≤ ν.event (fun coins =>
      HasClique (graphFor T (reversals (withPairCoins base coins)) desired) s (A ∪ B)) := by
  classical
  intro e ν
  let k : PairCoin (j + 1) e := ⟨along hj x₀ y₀, by
    rw [exposureBlock_along le_rfl hj, ite_eq_right hsep]⟩
  let law := fun _ : PairCoin (j + 1) e => FiniteLaw.bernoulli p hp (by linarith : p ≤ 1)
  let b := xor (adjacency (reversals base) x₀ y₀ j) desired
  let P : (PairCoin (j + 1) e → Bool) → Prop := fun coins =>
    HasClique (graphFor T (reversals (withPairCoins base coins)) desired) s (A ∪ B)
  change p / 2 ≤ (FiniteLaw.product law).event P
  apply FiniteLaw.event_ge_of_gate law k b P
  · cases b <;> simp [law, show p ≤ 1 - p by linarith]
  · let fresh (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) :=
      (Equiv.funSplitAt k Bool).symm (b, w)
    let full (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) :=
      withPairCoins base (fresh w)
    let restLaw := FiniteLaw.product (fun i : {i : PairCoin (j + 1) e // i ≠ k} => law i.val)
    have hfix (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) {c : Coin T}
        (hc : exposureBlock (j + 1) c = none) : full w c = base c :=
      withPairCoins_of_exposed base (fresh w) hc
    have hbefore (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) :
        adjacency (reversals (full w)) x₀ y₀ j = adjacency (reversals base) x₀ y₀ j := by
      apply adjacency_congr_reads (by omega)
      intro i _ hi
      exact hfix w (exposureBlock_earlier (by omega) (by omega) x₀ y₀)
    have hgate (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) : full w k.val = b := by
      change withPairCoins base (fresh w) k.val = b
      rw [withPairCoins_of_mem]
      exact congrArg Prod.fst ((Equiv.funSplitAt k Bool).apply_symm_apply (b, w))
    have hjoins (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) (x : Leaf T) (hx : x ∈ A)
        (y : Leaf T) (hy : y ∈ B) : adjacency (reversals (full w)) x y (j + 1) = desired := by
      rw [adjacency_eq_of_ancestor_pair hj _ (hA x hx) (hB y hy), adjacency, ite_eq_right hsep,
        hbefore, reversals_along _ hj, show along hj x₀ y₀ = k.val from rfl, hgate]
      unfold b
      cases adjacency (reversals base) x₀ y₀ j <;> cases desired <;> rfl
    have hpreserve (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) :
        (graphFor T (reversals (full w)) desired).IsClique (A : Set (Leaf T)) ∧
        (graphFor T (reversals (full w)) desired).IsClique (B : Set (Leaf T)) := by
      constructor
      · intro x hx y hy hxy
        apply (graphFor_adj_iff hxy).mpr
        rw [adjacency_fixed_on_branch hj ((hA x hx).trans (hA y hy).symm)
          (fun c hc => hfix w hc)]
        exact (graphFor_adj_iff hxy).mp (hcl.1 hx hy hxy)
      · intro x hx y hy hxy
        apply (graphFor_adj_iff hxy).mpr
        rw [adjacency_fixed_on_branch hj ((hB x hx).trans (hB y hy).symm)
          (fun c hc => hfix w hc)]
        exact (graphFor_adj_iff hxy).mp (hcl.2 hx hy hxy)
    have hprob (x : Leaf T) (hx : x ∈ A) (y : Leaf T) (hy : y ∈ B)
        (i : ℕ) (hji : j + 1 < i) (hi : i ≤ T) :
        restLaw.event (fun w => reversals (full w) i s(ancestor i x, ancestor i y) = true) ≤ p := by
      have hxy : ancestor (j + 1) x ≠ ancestor (j + 1) y := by rw [hA x hx, hB y hy]; exact hsep
      let l : PairCoin (j + 1) e := ⟨along hi x y, by
        rw [exposureBlock_along hji.le hi, ite_eq_right hxy]
        congr 2
        · exact Fin.ext (hA x hx)
        · exact Fin.ext (hB y hy)⟩
      have hlk : l ≠ k := by
        intro h
        have hh := congrArg (fun c : PairCoin (j + 1) e => c.val.1.val) h
        change i = j + 1 at hh
        omega
      have hread (w : {i : PairCoin (j + 1) e // i ≠ k} → Bool) :
          reversals (full w) i s(ancestor i x, ancestor i y) = w ⟨l, hlk⟩ := by
        rw [reversals_along _ hi, show along hi x y = l.val from rfl]
        change withPairCoins base (fresh w) l.val = w ⟨l, hlk⟩
        rw [withPairCoins_of_mem]
        have hh := congrFun (congrArg Prod.snd
          ((Equiv.funSplitAt k Bool).apply_symm_apply (b, w))) ⟨l, hlk⟩
        exact hh
      simp_rw [hread]
      rw [FiniteLaw.event_coordinate (S := fun _ => Bool)
        (fun i : {i : PairCoin (j + 1) e // i ≠ k} => law i.val) ⟨l, hlk⟩ (· = true)]
      rw [← FiniteLaw.mean_indicator]
      simp [law, FiniteLaw.mean]
    change 1 / 2 ≤ restLaw.event (fun w =>
      HasClique (graphFor T (reversals (full w)) desired) s (A ∪ B))
    have hmerge := event_merge_after_join restLaw (fun w => reversals (full w)) desired hj hsep
      hA hB hjoins hpreserve hroom hprob
    linarith

theorem probability_merge_pair_at_label {j : ℕ} (hj : j + 1 ≤ T)
    (x₀ y₀ : Leaf T) (hsep : ancestor (j + 1) x₀ ≠ ancestor (j + 1) y₀)
    {e : Sym2 (Leaf T)} (he : e = s(node hj x₀, node hj y₀))
    (base : Coin T → Bool) (desired : Bool) (A B : Finset (Leaf T))
    (hA : ∀ x ∈ A, ancestor (j + 1) x = ancestor (j + 1) x₀)
    (hB : ∀ y ∈ B, ancestor (j + 1) y = ancestor (j + 1) y₀)
    (hcl : (graphFor T (reversals base) desired).IsClique (A : Set (Leaf T)) ∧
      (graphFor T (reversals base) desired).IsClique (B : Set (Leaf T)))
    {s : ℕ} (hroom : s ≤ A.card + B.card) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (hbudget : (A.card : ℝ) * B.card * ((T - (j + 1) : ℕ) * p) /
      ((A.card + B.card - s + 1 : ℕ) : ℝ) ≤ 1 / 2) :
    let ν := FiniteLaw.product (fun _ : PairCoin (j + 1) e =>
      FiniteLaw.bernoulli p hp (by linarith : p ≤ 1))
    p / 2 ≤ ν.event (fun coins =>
      HasClique (graphFor T (reversals (withPairCoins base coins)) desired) s (A ∪ B)) := by
  subst e
  exact probability_merge_pair hj x₀ y₀ hsep base desired A B hA hB hcl hroom hp hp' hbudget

end LocallyRamsey.BinaryTree
