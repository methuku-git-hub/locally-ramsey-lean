module

public import LocallyRamsey.Upper.BinaryTree
public import LocallyRamsey.IndependentBlocks
public import LocallyRamsey.Merging
public import LocallyRamsey.Upper.Recurrence

public section

namespace LocallyRamsey.BinaryTree

open scoped BigOperators

variable {T : ℕ} {Ω : Type*} [Fintype Ω]

/-- An edge status at depth `j` can change by the final depth only when
one of the subsequent reversals on the pair's path takes place. The
bound uses the marginal flip probabilities. -/
theorem event_adjacency_changed_le (μ : FiniteLaw Ω) (flip : Ω → Reversals)
    {j : ℕ} (hj : j ≤ T) (x y : Leaf T) (hsep : ancestor j x ≠ ancestor j y)
    {p : ℝ} (hprob : ∀ i, j < i → i ≤ T →
      μ.event (fun ω => flip ω i s(ancestor i x, ancestor i y) = true) ≤ p) :
    μ.event (fun ω => adjacency (flip ω) x y T ≠ adjacency (flip ω) x y j) ≤
      (T - j : ℕ) * p := by
  classical
  let triggered (k : Fin (T - j)) (ω : Ω) :=
    flip ω (j + 1 + k.val) s(ancestor (j + 1 + k.val) x, ancestor (j + 1 + k.val) y) = true
  have hsubset (ω : Ω) (h : adjacency (flip ω) x y T ≠ adjacency (flip ω) x y j) :
      ∃ k, triggered k ω := by
    by_contra! hn
    apply h
    apply adjacency_unchanged hj le_rfl hsep
    intro i hi hT
    let k : Fin (T - j) := ⟨i - j - 1, by omega⟩
    have hval : j + 1 + k.val = i := by dsimp [k]; omega
    have hnt := hn k
    dsimp [triggered] at hnt
    rw [hval] at hnt
    simpa using hnt
  calc
    _ ≤ μ.event (fun ω => ∃ k, triggered k ω) := μ.event_mono hsubset
    _ ≤ ∑ k, μ.event (triggered k) := μ.event_exists_le_sum _
    _ ≤ ∑ _k : Fin (T - j), p := by
      apply Finset.sum_le_sum
      intro k _
      exact hprob _ (by omega) (by omega)
    _ = _ := by simp

/-- Expected number of missing cross edges, given bounds on the
probabilities of individual missing edges. The edge events can share
reversal variables. -/
theorem mean_missing_cross_le (μ : FiniteLaw Ω) (H : Ω → SimpleGraph (Leaf T))
    [∀ ω, DecidableRel (H ω).Adj] (A B : Finset (Leaf T)) (p : ℝ)
    (hprob : ∀ x ∈ A, ∀ y ∈ B, μ.event (fun ω => ¬(H ω).Adj x y) ≤ p) :
    μ.mean (fun ω => ((missingCrossEdges (H ω) A B).card : ℝ)) ≤
      (A.card : ℝ) * B.card * p := by
  classical
  let f (pair : Leaf T × Leaf T) (ω : Ω) :=
    if ¬(H ω).Adj pair.1 pair.2 then (1 : ℝ) else 0
  have hcard (ω : Ω) :
      ((missingCrossEdges (H ω) A B).card : ℝ) = ∑ e ∈ A ×ˢ B, f e ω := by
    simp only [missingCrossEdges, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter, f]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : (H ω).Adj e.1 e.2 <;> simp [h]
  have hmean (e : Leaf T × Leaf T) : μ.mean (f e) = μ.event (fun ω => ¬(H ω).Adj e.1 e.2) :=
    μ.mean_indicator _
  simp_rw [hcard, μ.mean_sum, hmean]
  calc
    _ ≤ ∑ _e ∈ A ×ˢ B, p :=
      Finset.sum_le_sum fun e he => hprob e.1 (Finset.mem_product.mp he).1
        e.2 (Finset.mem_product.mp he).2
    _ = _ := by simp [Finset.card_product, Nat.cast_mul]

/-- The conditional missing-edge estimate implies a merging estimate.
The hypotheses apply after conditioning on the exposed data and the
reversal joining the two branches. -/
theorem event_no_merge_le (μ : FiniteLaw Ω) (H : Ω → SimpleGraph (Leaf T))
    [∀ ω, DecidableRel (H ω).Adj] {A B : Finset (Leaf T)} {s : ℕ}
    (hdisj : Disjoint A B) (hcl : ∀ ω, (H ω).IsClique (A : Set (Leaf T)) ∧
      (H ω).IsClique (B : Set (Leaf T)))
    (hroom : s ≤ A.card + B.card) (p : ℝ)
    (hprob : ∀ x ∈ A, ∀ y ∈ B, μ.event (fun ω => ¬(H ω).Adj x y) ≤ p) :
    μ.event (fun ω => ¬ HasClique (H ω) s (A ∪ B)) ≤
      ((A.card : ℝ) * B.card * p) / ((A.card + B.card - s + 1 : ℕ) : ℝ) := by
  let n := A.card + B.card - s + 1
  let X (ω : Ω) : ℝ := (missingCrossEdges (H ω) A B).card
  have hn : 0 < (n : ℝ) := by dsimp [n]; positivity
  have hsubset (ω : Ω) (h : ¬ HasClique (H ω) s (A ∪ B)) : (n : ℝ) ≤ X ω := by
    by_contra! hm
    have hk : (missingCrossEdges (H ω) A B).card < n := by
      dsimp [X] at hm
      exact_mod_cast hm
    apply h
    exact merge_cliques (H ω) hdisj (hcl ω).1 (hcl ω).2 (by dsimp [n] at hk; omega)
  calc
    _ ≤ μ.event (fun ω => (n : ℝ) ≤ X ω) := μ.event_mono hsubset
    _ ≤ μ.mean X / n := μ.event_ge_le (fun _ => Nat.cast_nonneg _) hn
    _ ≤ _ := div_le_div_of_nonneg_right (mean_missing_cross_le μ H A B p hprob) hn.le

/-- The conditional merging estimate for a fixed pair of branches, valid
for the graph and its complement. Once the desired status holds at the
joining depth, later changes cost only their marginal probabilities. -/
theorem event_merge_after_join (μ : FiniteLaw Ω) (flip : Ω → Reversals)
    (desired : Bool) {j : ℕ} (hj : j ≤ T) {u v : ℕ} (huv : u ≠ v)
    {A B : Finset (Leaf T)} {s : ℕ} {p : ℝ}
    (hA : ∀ x ∈ A, ancestor j x = u) (hB : ∀ y ∈ B, ancestor j y = v)
    (hjoin : ∀ ω, ∀ x ∈ A, ∀ y ∈ B, adjacency (flip ω) x y j = desired)
    (hcl : ∀ ω, (graphFor T (flip ω) desired).IsClique (A : Set (Leaf T)) ∧
      (graphFor T (flip ω) desired).IsClique (B : Set (Leaf T)))
    (hroom : s ≤ A.card + B.card)
    (hprob : ∀ x ∈ A, ∀ y ∈ B, ∀ i, j < i → i ≤ T →
      μ.event (fun ω => flip ω i s(ancestor i x, ancestor i y) = true) ≤ p) :
    μ.event (fun ω => HasClique (graphFor T (flip ω) desired) s (A ∪ B)) ≥
      1 - ((A.card : ℝ) * B.card * ((T - j : ℕ) * p)) /
        ((A.card + B.card - s + 1 : ℕ) : ℝ) := by
  classical
  let H (ω : Ω) := graphFor T (flip ω) desired
  have hdisj : Disjoint A B :=
    Finset.disjoint_left.mpr fun x hx hy => huv ((hA x hx).symm.trans (hB x hy))
  have hmissing (x : Leaf T) (hx : x ∈ A) (y : Leaf T) (hy : y ∈ B) :
      μ.event (fun ω => ¬(H ω).Adj x y) ≤ (T - j : ℕ) * p := by
    have hsep : ancestor j x ≠ ancestor j y := by rw [hA x hx, hB y hy]; exact huv
    have hxy : x ≠ y := fun he => hsep (congrArg _ he)
    refine (μ.event_mono ?_).trans
      (event_adjacency_changed_le μ flip hj x y hsep (hprob x hx y hy))
    intro ω hbad he
    exact hbad ((graphFor_adj_iff hxy).mpr (he.trans (hjoin ω x hx y hy)))
  have hfail := event_no_merge_le μ H hdisj hcl hroom _ hmissing
  rw [μ.event_not] at hfail
  linarith

end LocallyRamsey.BinaryTree
