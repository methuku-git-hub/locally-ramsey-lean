module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic

@[expose] public section

namespace LocallyRamsey.BinaryTree

/-- The leaves are binary words of length `T`, represented by their values. -/
abbrev Leaf (T : ℕ) := Fin (2 ^ T)

/-- The first `j` bits of a leaf, as an integer. -/
def ancestor {T : ℕ} (j : ℕ) (x : Leaf T) : ℕ :=
  x.val / 2 ^ (T - j)

theorem prefix_lt {T j : ℕ} (hj : j ≤ T) (x : Leaf T) : ancestor j x < 2 ^ j := by
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (T - j))).2
  rw [← pow_add, Nat.add_sub_of_le hj]
  exact x.isLt

@[simp]
theorem prefix_root {T : ℕ} (x : Leaf T) : ancestor 0 x = 0 := by
  exact Nat.div_eq_of_lt x.isLt

@[simp]
theorem prefix_leaf {T : ℕ} (x : Leaf T) : ancestor T x = x.val := by
  simp [ancestor]

theorem prefix_parent {T j : ℕ} (hj : j < T) (x : Leaf T) :
    ancestor (j + 1) x / 2 = ancestor j x := by
  rw [ancestor, Nat.div_div_eq_div_mul, ← pow_succ, ancestor]
  congr 2
  omega

theorem prefix_of_prefix_eq {T j k : ℕ} (hjk : j ≤ k) (hk : k ≤ T)
    {x y : Leaf T} (h : ancestor k x = ancestor k y) :
    ancestor j x = ancestor j y := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k hjk ih =>
    have h' := congrArg (fun m : ℕ => m / 2) h
    simp only [prefix_parent (by omega : k < T)] at h'
    exact ih (by omega) h'

/-- The leaf set of a node, intersected with a specified set of leaves. -/
def branch {T : ℕ} (X : Finset (Leaf T)) (j v : ℕ) : Finset (Leaf T) :=
  X.filter fun x => ancestor j x = v

@[simp]
theorem mem_branch {T : ℕ} {X : Finset (Leaf T)} {j v : ℕ} {x : Leaf T} :
    x ∈ branch X j v ↔ x ∈ X ∧ ancestor j x = v :=
  Finset.mem_filter

@[simp]
theorem branch_root {T : ℕ} (X : Finset (Leaf T)) : branch X 0 0 = X := by
  ext x
  simp

/-- Each possible reversal is indexed by its depth and the unordered pair
of vertices it acts on. -/
abbrev Reversals := ℕ → Sym2 ℕ → Bool

/-- The adjacency seen at successive depths along two leaf paths. A single
ancestor represents one vertex, which has no loop. If the prefixes first
separate at this depth, the previous value is therefore false. -/
def adjacency {T : ℕ} (flip : Reversals) (x y : Leaf T) : ℕ → Bool
  | 0 => false
  | j + 1 =>
    if ancestor (j + 1) x = ancestor (j + 1) y then false
    else xor (adjacency flip x y j) (flip (j + 1) s(ancestor (j + 1) x, ancestor (j + 1) y))

theorem adjacency_symm {T : ℕ} (flip : Reversals) (x y : Leaf T) (j : ℕ) :
    adjacency flip x y j = adjacency flip y x j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [adjacency, ih, eq_comm (a := ancestor (j + 1) x), Sym2.eq_swap]

theorem adjacency_eq_false_of_prefix_eq {T j : ℕ} {flip : Reversals} {x y : Leaf T}
    (h : ancestor j x = ancestor j y) : adjacency flip x y j = false := by
  cases j <;> simp [adjacency, h]

/-- The random graph once the Boolean reversal variables have been drawn. -/
def graph (T : ℕ) (flip : Reversals) : SimpleGraph (Leaf T) where
  Adj x y := adjacency flip x y T = true
  symm := ⟨fun {x y} h => (adjacency_symm flip y x T).trans h⟩
  loopless := ⟨fun x => by
    simp [adjacency_eq_false_of_prefix_eq (x := x) (y := x) rfl]⟩

/-- With distinct prefixes at the starting depth, later adjacencies agree
with that depth unless at least one of their subsequent flips is true. -/
theorem adjacency_unchanged {T j k : ℕ} (hjk : j ≤ k) (hk : k ≤ T)
    {flip : Reversals} {x y : Leaf T} (hsep : ancestor j x ≠ ancestor j y)
    (hflip : ∀ i, j < i → i ≤ k → flip i s(ancestor i x, ancestor i y) = false) :
    adjacency flip x y k = adjacency flip x y j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    have hne : ancestor (k + 1) x ≠ ancestor (k + 1) y := by
      exact fun heq => hsep (prefix_of_prefix_eq (by omega) hk heq)
    rw [adjacency, ite_eq_right hne, hflip _ (by omega) le_rfl]
    simpa using ih (by omega) (fun i hi hik => hflip i hi (by omega))

/-- Vertices with the same two ancestor labels at depth `j` have the
same adjacency at that depth. -/
theorem adjacency_eq_of_ancestor_pair {T j : ℕ} (hj : j ≤ T) (flip : Reversals)
    {x y x' y' : Leaf T} (hx : ancestor j x = ancestor j x')
    (hy : ancestor j y = ancestor j y') :
    adjacency flip x y j = adjacency flip x' y' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hxp := prefix_of_prefix_eq (by omega : j ≤ j + 1) hj hx
    have hyp := prefix_of_prefix_eq (by omega : j ≤ j + 1) hj hy
    simp [adjacency, hx, hy, ih (by omega) hxp hyp]

/-- Select adjacencies or nonadjacencies at the last level. -/
def graphFor (T : ℕ) (flip : Reversals) (desired : Bool) : SimpleGraph (Leaf T) :=
  if desired then graph T flip else (graph T flip)ᶜ

theorem graphFor_adj_iff {T : ℕ} {flip : Reversals} {desired : Bool} {x y : Leaf T}
    (hxy : x ≠ y) : (graphFor T flip desired).Adj x y ↔ adjacency flip x y T = desired := by
  cases desired <;> simp [graphFor, graph, SimpleGraph.compl_adj, hxy]

/-- Two assignments agreeing on all flips after the paths meet at some
common ancestor give the same adjacency for the two final vertices.
This is the within-branch part of the exposure in Lemma 2. -/
theorem adjacency_congr_after_common_prefix {T j k : ℕ} (hjk : j ≤ k)
    {flip flip' : Reversals} {x y : Leaf T} (hprefix : ancestor j x = ancestor j y)
    (hflip : ∀ i, j < i → i ≤ k →
      flip i s(ancestor i x, ancestor i y) = flip' i s(ancestor i x, ancestor i y)) :
    adjacency flip x y k = adjacency flip' x y k := by
  induction k, hjk using Nat.le_induction with
  | base =>
    rw [adjacency_eq_false_of_prefix_eq hprefix, adjacency_eq_false_of_prefix_eq hprefix]
  | succ k hjk ih =>
    simp only [adjacency]
    rw [ih (fun i hi hik => hflip i hi (by omega)), hflip _ (by omega) (by omega)]

end LocallyRamsey.BinaryTree
