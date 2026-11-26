module

public import LocallyRamsey.FiniteProbability

public section

namespace LocallyRamsey.FiniteLaw

open scoped BigOperators

/-- The law of a reversal with probability `p`. -/
@[expose] def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : FiniteLaw Bool where
  prob b := if b then p else 1 - p
  nonneg b := by cases b <;> simp [hp, sub_nonneg.mpr hp']
  total := by rw [Fintype.sum_bool]; simp

@[simp]
theorem bernoulli_prob_true {p : ℝ} {hp hp'} : (bernoulli p hp hp').prob true = p := rfl

@[simp]
theorem bernoulli_prob_false {p : ℝ} {hp hp'} : (bernoulli p hp hp').prob false = 1 - p := rfl

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {S : I → Type*} [∀ i, Fintype (S i)]

/-- A partition of the coordinates of a finite product, represented by a
map sending each coordinate to its block. -/
abbrev Block (label : I → J) (j : J) (S : I → Type*) :=
  (i : {i // label i = j}) → S i.val

/-- Grouping product coordinates into blocks preserves the product law.
A block may be empty. -/
theorem mean_on_blocks (μ : ∀ i, FiniteLaw (S i)) (label : I → J)
    (X : ((j : J) → Block label j S) → ℝ) :
    (product μ).mean (fun ω => X (fun _ i => ω i.val)) =
      (product fun j => product (fun i : {i // label i = j} => μ i.val)).mean X := by
  classical
  let e : ((i : I) → S i) ≃ ((j : J) → Block label j S) :=
    Equiv.piCongrFiberwise (f := label) fun _ => Equiv.refl _
  simp only [mean]
  apply Fintype.sum_equiv e
  intro ω
  have hprod :
      (product μ).prob ω =
        (product fun j => product (fun i : {i // label i = j} => μ i.val)).prob (e ω) := by
    change (∏ i, (μ i).prob (ω i)) = ∏ j, ∏ i : {i // label i = j}, (μ i.val).prob (e ω j i)
    exact (Fintype.prod_fiberwise label (fun i => (μ i).prob (ω i))).symm
  rw [hprod]
  rfl

theorem event_all (μ : ∀ i, FiniteLaw (S i)) (P : ∀ i, S i → Prop) :
    (product μ).event (fun ω => ∀ i, P i (ω i)) = ∏ i, (μ i).event (P i) := by
  classical
  rw [← mean_indicator]
  have h (ω : (i : I) → S i) : (if ∀ i, P i (ω i) then (1 : ℝ) else 0) =
      ∏ i, if P i (ω i) then 1 else 0 := by
    by_cases h : ∀ i, P i (ω i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [ite_eq_right h]
      symm
      apply Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
      simp [hi]
  simp_rw [h]
  rw [mean_product μ (fun i s => if P i s then 1 else 0)]
  simp_rw [mean_indicator]

/-- A failure event in each block gives a product of failure probabilities. -/
theorem event_all_blocks (μ : ∀ i, FiniteLaw (S i)) (label : I → J)
    (P : ∀ j, Block label j S → Prop) :
    (product μ).event (fun ω => ∀ j, P j (fun i => ω i.val)) =
      ∏ j, (product (fun i : {i // label i = j} => μ i.val)).event (P j) := by
  classical
  rw [← mean_indicator, mean_on_blocks μ label
    (fun ω => if ∀ j, P j (ω j) then 1 else 0), mean_indicator]
  exact event_all _ P

theorem event_no_success_in_coordinates_le (μ : ∀ i, FiniteLaw (S i))
    (active : Finset I) (good : ∀ i, S i → Prop)
    {p : ℝ} (h : ∀ i ∈ active, p ≤ (μ i).event (good i)) :
    (product μ).event (fun ω => ∀ i ∈ active, ¬ good i (ω i)) ≤
      (1 - p) ^ active.card := by
  classical
  rw [event_all μ (fun i w => i ∈ active → ¬ good i w)]
  have hterm (i : I) :
      (μ i).event (fun w => i ∈ active → ¬ good i w) ≤
        if i ∈ active then 1 - p else 1 := by
    by_cases hi : i ∈ active
    · simpa [hi, event_not] using sub_le_sub_left (h i hi) (1 : ℝ)
    · simp only [hi, ite_false]
      rw [← mean_indicator]
      simp [mean_const]
  refine (Finset.prod_le_prod₀
    (fun i _ => (μ i).event_nonneg _) (fun i _ => hterm i)).trans_eq ?_
  simp

/-- The product bound for failure in every block of a given collection.
No restrictions are placed on the other coordinates. -/
theorem event_no_success_in_blocks_le (μ : ∀ i, FiniteLaw (S i)) (label : I → J)
    (active : Finset J) (good : ∀ j, Block label j S → Prop)
    {p : ℝ}
    (h : ∀ j ∈ active, p ≤ (product (fun i : {i // label i = j} => μ i.val)).event (good j)) :
    (product μ).event (fun ω => ∀ j ∈ active, ¬ good j (fun i => ω i.val)) ≤
      (1 - p) ^ active.card := by
  classical
  rw [event_all_blocks μ label (fun j ω => j ∈ active → ¬ good j ω)]
  have hterm (j : J) : (product (fun i : {i // label i = j} => μ i.val)).event
      (fun ω => j ∈ active → ¬ good j ω) ≤ if j ∈ active then 1 - p else 1 := by
    by_cases hj : j ∈ active
    · simpa [hj, event_not] using sub_le_sub_left (h j hj) (1 : ℝ)
    · simp only [hj, ite_false]
      rw [← mean_indicator]
      simp [mean_const]
  have hproduct := Finset.prod_le_prod₀ (s := (Finset.univ : Finset J))
    (fun j _ => event_nonneg _ (fun ω => j ∈ active → ¬ good j ω)) (fun j _ => hterm j)
  refine hproduct.trans_eq ?_
  simp

/-- Separating a coordinate from the others gives its original law and an
independent product of all remaining coordinates. -/
theorem mean_split_at (μ : ∀ i, FiniteLaw (S i)) (k : I)
    (X : S k × ((i : {i // i ≠ k}) → S i.val) → ℝ) :
    (product μ).mean (fun ω => X (ω k, fun i => ω i.val)) =
      ((μ k).staged (fun _ => product (fun i : {i // i ≠ k} => μ i.val))).mean X := by
  classical
  let e := Equiv.piSplitAt k S
  simp only [mean]
  apply Fintype.sum_equiv e
  intro ω
  congr 1
  change (∏ i, (μ i).prob (ω i)) = (μ k).prob (ω k) *
    ∏ i : {i // i ≠ k}, (μ i.val).prob (ω i.val)
  rw [← Finset.mul_prod_erase Finset.univ (fun i => (μ i).prob (ω i)) (Finset.mem_univ k)]
  congr 1
  exact Finset.prod_subtype _ (by simp) _

theorem mean_coordinate (μ : ∀ i, FiniteLaw (S i)) (k : I) (f : S k → ℝ) :
    (product μ).mean (fun ω => f (ω k)) = (μ k).mean f := by
  rw [mean_split_at μ k (fun pair => f pair.1), staged_mean]
  simp only [mean_const]

theorem event_coordinate (μ : ∀ i, FiniteLaw (S i)) (k : I) (P : S k → Prop) :
    (product μ).event (fun ω => P (ω k)) = (μ k).event P := by
  classical
  rw [← mean_indicator, ← mean_indicator, mean_coordinate μ k (fun x => if P x then 1 else 0)]

/-- After revealing one distinguished coordinate, all other coordinates
retain their product law, even when the success tests depend on the
revealed value. -/
theorem event_no_success_after_exposure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : ι → Type*} [∀ i, Fintype (F i)]
    (μ : ∀ i, FiniteLaw (F i)) (k : ι) (active : Finset {i : ι // i ≠ k})
    (enabled : F k → Prop) (good : F k → (i : {i : ι // i ≠ k}) → F i.val → Prop)
    {p : ℝ} (hp : p ≤ 1)
    (h : ∀ x, enabled x → ∀ i ∈ active, p ≤ (μ i.val).event (good x i)) :
    (product μ).event (fun ω =>
      enabled (ω k) ∧ ∀ i ∈ active, ¬ good (ω k) i (ω i.val)) ≤ (1 - p) ^ active.card := by
  classical
  let P : F k × ((i : {i : ι // i ≠ k}) → F i.val) → Prop := fun pair =>
    enabled pair.1 ∧ ∀ i ∈ active, ¬ good pair.1 i (pair.2 i)
  rw [← mean_indicator,
    mean_split_at μ k (fun pair => if P pair then 1 else 0), staged_mean]
  let ν := product (fun i : {i : ι // i ≠ k} => μ i.val)
  have hstate (x : F k) : ν.mean (fun w => if P (x, w) then 1 else 0) =
      ν.event (fun w => P (x, w)) := mean_indicator _ _
  rw [← (μ k).mean_const ((1 - p) ^ active.card)]
  apply (μ k).mean_mono
  intro x
  rw [hstate x]
  by_cases hx : enabled x
  · have hP : (fun w => P (x, w)) = fun w => ∀ i, i ∈ active → ¬ good x i (w i) := by
      funext w
      simp [P, hx]
    rw [hP]
    exact event_no_success_in_coordinates_le (fun i => μ i.val) active (good x) (h x hx)
  · have hP : (fun w => P (x, w)) = fun _ => False := by funext w; simp [P, hx]
    rw [hP, ← mean_indicator]
    simpa only [ite_false, mean_const] using (pow_nonneg (sub_nonneg.mpr hp) active.card)

/-- Separating the gate coin from all other coins in an event. -/
theorem event_split_at (μ : I → FiniteLaw Bool) (k : I) (P : (I → Bool) → Prop) :
    (product μ).event P = (μ k).mean (fun b =>
      (product (fun i : {i // i ≠ k} => μ i.val)).event
        (fun w => P ((Equiv.funSplitAt k Bool).symm (b, w)))) := by
  classical
  let e := Equiv.funSplitAt k Bool
  let X : Bool × ({i // i ≠ k} → Bool) → ℝ := fun pair => if P (e.symm pair) then 1 else 0
  have heq : (fun ω => if P ω then (1 : ℝ) else 0) = fun ω => X (ω k, fun i => ω i.val) := by
    funext ω
    change (if P ω then (1 : ℝ) else 0) = if P (e.symm (e ω)) then 1 else 0
    rw [e.symm_apply_apply]
  rw [← mean_indicator, heq, mean_split_at μ k X, staged_mean]
  simp_rw [X, mean_indicator]
  rfl

/-- If one value of a gate coin gives a conditional success probability
of at least one half, and both coin outcomes have probability at least
`p`, the joint success probability is at least `p / 2`. -/
theorem event_ge_of_gate (μ : I → FiniteLaw Bool) (k : I) (b : Bool)
    (P : (I → Bool) → Prop) {p : ℝ}
    (hgate : p ≤ (μ k).prob b)
    (hcond : 1 / 2 ≤ (product (fun i : {i // i ≠ k} => μ i.val)).event
      (fun w => P ((Equiv.funSplitAt k Bool).symm (b, w)))) :
    p / 2 ≤ (product μ).event P := by
  rw [event_split_at μ k]
  let r : Bool → ℝ := fun c => (product (fun i : {i // i ≠ k} => μ i.val)).event
    (fun w => P ((Equiv.funSplitAt k Bool).symm (c, w)))
  change p / 2 ≤ (μ k).mean r
  have he : (μ k).prob b * r b ≤ (μ k).mean r :=
    Finset.single_le_sum (f := fun c => (μ k).prob c * r c)
      (fun c _ => mul_nonneg ((μ k).nonneg c) (by dsimp [r]; exact event_nonneg _ _))
      (Finset.mem_univ b)
  exact (show p / 2 ≤ (μ k).prob b * r b by
    rw [div_eq_mul_inv]
    exact mul_le_mul hgate (by simpa only [one_div, r] using hcond)
      (by norm_num) ((μ k).nonneg b)).trans he

end LocallyRamsey.FiniteLaw
