module

public import LocallyRamsey.Upper.FlipEstimates

@[expose] public section

namespace LocallyRamsey.BinaryTree

variable {T : ℕ}

/-- Coordinates large enough to include every reversal in the construction.
Pairs of node labels that do not occur at a given depth are unused. -/
abbrev Coin (T : ℕ) := Fin (T + 1) × Sym2 (Leaf T)

/-- Finite-space version of all flip values at the depths of the tree. -/
def reversalLaw (T : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    FiniteLaw (Coin T → Bool) :=
  FiniteLaw.product (fun _ => FiniteLaw.bernoulli p hp hp')

/-- Read a reversal from the finite indexed family. -/
def reversals (ω : Coin T → Bool) : Reversals :=
  fun i e =>
    if hi : i ≤ T then
      ω (⟨i, by omega⟩, e.map (fun v => ⟨v % (2 ^ T), Nat.mod_lt v (by positivity)⟩))
    else false

/-- Represent a leaf's ancestor by an element of the ambient label type. -/
def node {i : ℕ} (hi : i ≤ T) (x : Leaf T) : Leaf T :=
  ⟨ancestor i x, (prefix_lt hi x).trans_le (Nat.pow_le_pow_right (by decide) hi)⟩

/-- The coordinate queried along two leaf paths at a valid depth. -/
def along {i : ℕ} (hi : i ≤ T) (x y : Leaf T) : Coin T :=
  (⟨i, by omega⟩, s(node hi x, node hi y))

@[simp]
theorem reversals_along (ω : Coin T → Bool) {i : ℕ} (hi : i ≤ T) (x y : Leaf T) :
    reversals ω i s(ancestor i x, ancestor i y) = ω (along hi x y) := by
  simp only [reversals, dite_eq_left hi, Sym2.map_mk, along]
  have hnode (z : Leaf T) :
      (⟨ancestor i z % (2 ^ T), Nat.mod_lt _ (by positivity)⟩ : Leaf T) = node hi z :=
    Fin.ext (Nat.mod_eq_of_lt (node hi z).isLt)
  rw [hnode x, hnode y]

/-- Each reversal read by the construction has the prescribed marginal. -/
theorem reversal_prob (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    {i : ℕ} (hi : i ≤ T) (x y : Leaf T) :
    (reversalLaw T p hp hp').event
      (fun ω => reversals ω i s(ancestor i x, ancestor i y) = true) = p := by
  rw [show (fun ω : Coin T → Bool => reversals ω i s(ancestor i x, ancestor i y) = true) =
    (fun ω => ω (along hi x y) = true) from funext fun ω => by rw [reversals_along]]
  rw [reversalLaw, FiniteLaw.event_coordinate (S := fun _ => Bool)
    (fun _ => FiniteLaw.bernoulli p hp hp') (along hi x y) (· = true)]
  rw [← FiniteLaw.mean_indicator]
  simp [FiniteLaw.mean]

/-- Locate the depth-`j` ancestor of a node whose depth is `i`. -/
def nodeAt (j i : ℕ) (x : Leaf T) : Leaf T :=
  ⟨x.val / 2 ^ (i - j), (Nat.div_le_self _ _).trans_lt x.isLt⟩

@[simp]
theorem nodeAt_node {j i : ℕ} (hji : j ≤ i) (hi : i ≤ T) (x : Leaf T) :
    nodeAt j i (node hi x) = node (hji.trans hi) x := by
  apply Fin.ext
  change x.val / 2 ^ (T - i) / 2 ^ (i - j) = x.val / 2 ^ (T - j)
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  omega

/-- Partition the coins at an exposure depth. Earlier coins and those
inside a single branch go into the exposed block. All other coins are
classified by the unordered pair of branches they cross. -/
def exposureBlock (j : ℕ) (c : Coin T) : Option (Sym2 (Leaf T)) :=
  let branches := c.2.map (nodeAt j c.1.val)
  if c.1.val < j ∨ branches.IsDiag then none else some branches

theorem exposureBlock_along {j i : ℕ} (hji : j ≤ i) (hi : i ≤ T) (x y : Leaf T) :
    exposureBlock j (along hi x y) =
      if ancestor j x = ancestor j y then none
      else some s(node (hji.trans hi) x, node (hji.trans hi) y) := by
  simp only [exposureBlock, along, Sym2.map_mk, nodeAt_node hji hi, Sym2.mk_isDiag_iff,
    not_lt_of_ge hji, false_or]
  by_cases h : ancestor j x = ancestor j y
  · have he : node (hji.trans hi) x = node (hji.trans hi) y := Fin.ext h
    simp [h, he]
  · have he : node (hji.trans hi) x ≠ node (hji.trans hi) y :=
      fun h' => h (congrArg Fin.val h')
    simp [h, he]

theorem exposureBlock_earlier {j i : ℕ} (h : i < j) (hi : i ≤ T) (x y : Leaf T) :
    exposureBlock j (along hi x y) = none := by
  simp [exposureBlock, along, h]

/-- Within each branch, final edge status is decided by the exposed
block alone, even when all cross-branch coins are left unexposed. -/
theorem adjacency_fixed_on_branch {j : ℕ} (hj : j ≤ T) {x y : Leaf T}
    (hbranch : ancestor j x = ancestor j y) {ω ω' : Coin T → Bool}
    (hagree : ∀ c, exposureBlock j c = none → ω c = ω' c) :
    adjacency (reversals ω) x y T = adjacency (reversals ω') x y T := by
  apply adjacency_congr_after_common_prefix hj hbranch
  intro i hji hi
  rw [reversals_along ω hi, reversals_along ω' hi]
  exact hagree _ (by simp [exposureBlock_along hji.le hi, hbranch])

/-- All edge evaluations read only the coins on the corresponding pair
of paths. -/
theorem adjacency_congr_reads {k : ℕ} (hk : k ≤ T) {x y : Leaf T}
    {ω ω' : Coin T → Bool}
    (h : ∀ i, 0 < i → (hi : i ≤ k) →
      ω (along (hi.trans hk) x y) = ω' (along (hi.trans hk) x y)) :
    adjacency (reversals ω) x y k = adjacency (reversals ω') x y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k ≤ T := by omega
    have hprevious := ih hk' (fun i hip hik => h i hip (by omega))
    simp only [adjacency, hprevious, reversals_along _ hk, h _ (by omega) le_rfl]

/-- The exposed block and a single unordered cross-branch block suffice
for all edge evaluations between that pair of branches. -/
theorem adjacency_fixed_on_pair {j : ℕ} (hj : j ≤ T) (x y : Leaf T)
    {ω ω' : Coin T → Bool}
    (hagree : ∀ c, exposureBlock j c = none ∨
      exposureBlock j c = some s(node hj x, node hj y) → ω c = ω' c) :
    adjacency (reversals ω) x y T = adjacency (reversals ω') x y T := by
  apply adjacency_congr_reads le_rfl
  intro i _ hi
  apply hagree
  by_cases hij : i < j
  · exact Or.inl (exposureBlock_earlier hij hi x y)
  · rw [exposureBlock_along (by omega : j ≤ i) hi]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Changing only the coin at the joining depth leaves the earlier
adjacency fixed and toggles the adjacency at that depth. -/
theorem adjacency_at_join {j : ℕ} (hj : j + 1 ≤ T) (x y : Leaf T)
    (hsep : ancestor (j + 1) x ≠ ancestor (j + 1) y) (ω : Coin T → Bool) (b : Bool) :
    adjacency (reversals (Function.update ω (along hj x y) b)) x y (j + 1) =
      xor (adjacency (reversals ω) x y j) b := by
  have hpast :
      adjacency (reversals (Function.update ω (along hj x y) b)) x y j =
        adjacency (reversals ω) x y j := by
    apply adjacency_congr_reads (by omega)
    intro i _ hi
    apply Function.update_of_ne
    intro h
    have hs := congrArg (fun c : Coin T => c.1.val) h
    change i = j + 1 at hs
    omega
  simp [adjacency, hsep, hpast, reversals_along, hj]

end LocallyRamsey.BinaryTree
