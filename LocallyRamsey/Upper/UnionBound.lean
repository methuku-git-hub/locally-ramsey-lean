module

public import LocallyRamsey.Upper.FixedConfiguration

public section

open scoped BigOperators

namespace LocallyRamsey.BinaryTree

/-- A bounded encoding of all candidate configurations at one level.
Coordinates are indexed by the selected branches and candidate vertex
number in the clique. Invalid encodings are ignored. -/
abbrev Configuration (T a q : ℕ) :=
  (Fin q → Leaf T) × (Fin q → Fin a → Leaf T)

variable {T a q : ℕ}

def configurationClique (c : Configuration T a q) (i : Fin q) : Finset (Leaf T) :=
  Finset.univ.image (c.2 i)

def configurationValid (j : ℕ) (c : Configuration T a q) : Prop :=
  Function.Injective c.1 ∧ (∀ i, Function.Injective (c.2 i)) ∧
    ∀ i k, ancestor j (c.2 i k) = (c.1 i).val

def configurationFails (G : SimpleGraph (Leaf T)) (j s : ℕ)
    (c : Configuration T a q) : Prop :=
  configurationValid j c ∧
    (∀ i, G.IsClique (configurationClique c i : Set (Leaf T))) ∧
    (∀ i k, i ≠ k → ¬ HasClique G s (configurationClique c i ∪ configurationClique c k))

theorem exists_configuration_failure {G : SimpleGraph (Leaf T)} {j s : ℕ} (hj : j ≤ T)
    (h : ¬ MergesAt G j a s q) : ∃ c : Configuration T a q, configurationFails G j s c := by
  classical
  unfold MergesAt at h
  push Not at h
  obtain ⟨P, hP, hcard, K, hK, hbad⟩ := h
  let indices := (Finset.equivFinOfCardEq hcard).symm
  let root (i : Fin q) : Leaf T :=
    ⟨(indices i).val, (Finset.mem_range.mp (hP (indices i).property)).trans_le
      (Nat.pow_le_pow_right (by decide) hj)⟩
  let vertices (i : Fin q) (k : Fin a) : Leaf T :=
    ((Finset.equivFinOfCardEq (hK _ (indices i).property).2.card_eq).symm k).val
  have hroot : Function.Injective root := fun _ _ h₁ =>
    indices.injective (Subtype.ext (congrArg Fin.val h₁))
  have hvert (i : Fin q) : Function.Injective (vertices i) := by
    intro _ _ he
    exact Equiv.injective _ (Subtype.ext he)
  have hbranch (i : Fin q) (k : Fin a) : ancestor j (vertices i k) = (root i).val := by
    exact (mem_branch.mp ((hK _ (indices i).property).1
      ((Finset.equivFinOfCardEq (hK _ (indices i).property).2.card_eq).symm k).property)).2
  have hset (i : Fin q) : configurationClique (root, vertices) i = K (indices i).val := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      exact ((Finset.equivFinOfCardEq (hK _ (indices i).property).2.card_eq).symm k).property
    · intro hx
      let e := Finset.equivFinOfCardEq (hK _ (indices i).property).2.card_eq
      exact Finset.mem_image.mpr ⟨e ⟨x, hx⟩, Finset.mem_univ _, congrArg Subtype.val (e.symm_apply_apply _)⟩
  refine ⟨(root, vertices), ⟨hroot, hvert, hbranch⟩, ?_, ?_⟩
  · intro i
    rw [hset i]
    exact (hK _ (indices i).property).2.isClique
  · intro i k hik
    rw [hset i, hset k]
    exact hbad _ (indices i).property _ (indices k).property (fun he => hik (indices.injective (Subtype.ext he)))

theorem probability_configuration_fails {j s : ℕ} (hj : j + 1 ≤ T)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2) (c : Configuration T a q)
    (ha : 0 < a) (hroom : s ≤ a + a)
    (hbudget : (a : ℝ) * a * ((T - (j + 1) : ℕ) * p) / ((a + a - s + 1 : ℕ) : ℝ) ≤ 1 / 2)
    (desired : Bool) :
    (reversalLaw T p hp (by linarith)).event
      (fun ω => configurationFails (graphFor T (reversals ω) desired) (j + 1) s c) ≤
      (1 - p / 2) ^ q.choose 2 := by
  classical
  by_cases hvalid : configurationValid (j + 1) c
  · obtain ⟨hi, hk, hbranch⟩ := hvalid
    -- If no branches are selected the bound equals one.
    by_cases hq : q = 0
    · subst q
      norm_num [Nat.choose]
      rw [← sub_nonneg, ← FiniteLaw.event_not]
      exact FiniteLaw.event_nonneg _ _
    have : Nonempty (Fin q) := ⟨⟨0, Nat.pos_of_ne_zero hq⟩⟩
    let index := fun u : ℕ => Function.invFun (fun i : Fin q => (c.1 i).val) u
    let labels := Finset.univ.image (fun i : Fin q => (c.1 i).val)
    let K := fun u => configurationClique c (index u)
    have hindex (u : ℕ) (hu : u ∈ labels) : (c.1 (index u)).val = u := by
      obtain ⟨i, _, h⟩ := Finset.mem_image.mp hu
      exact Function.invFun_eq (f := fun i : Fin q => (c.1 i).val) ⟨i, h⟩
    have hcard : labels.card = q := by
      unfold labels
      rw [Finset.card_image_of_injective _
        (show Function.Injective (fun i => (c.1 i).val) from Fin.val_injective.comp hi),
        Finset.card_univ, Fintype.card_fin]
    have hK (u : ℕ) (hu : u ∈ labels) :
        (K u).card = a ∧ ∀ x ∈ K u, ancestor (j + 1) x = u := by
      constructor
      · simp only [K, configurationClique, Finset.card_image_of_injective _ (hk _),
          Finset.card_univ, Fintype.card_fin]
      · intro z hz
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hz
        exact (hbranch (index u) k).trans (hindex u hu)
    conv_rhs => rw [← hcard]
    refine (FiniteLaw.event_mono _ ?_).trans
      (probability_fixed_configuration hj hp hp' labels K ha hK hroom hbudget desired)
    intro ω hw
    obtain ⟨_, hcl, hfail⟩ := hw
    refine ⟨fun u _ => hcl (index u), ?_⟩
    intro u hu v hv huv
    exact hfail (index u) (index v) (fun he => huv ((hindex u hu).symm.trans
      ((congrArg (fun i => (c.1 i).val) he).trans (hindex v hv))))
  · rw [← FiniteLaw.mean_indicator]
    simp [configurationFails, hvalid, FiniteLaw.mean_const, pow_nonneg (by linarith : 0 ≤ 1 - p / 2)]

/-- The union bound over all choices of branches and candidate cliques
at one level. -/
theorem probability_not_mergesAt {j s : ℕ} (hj : j + 1 ≤ T)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2)
    (ha : 0 < a) (hroom : s ≤ a + a)
    (hbudget : (a : ℝ) * a * ((T - (j + 1) : ℕ) * p) / ((a + a - s + 1 : ℕ) : ℝ) ≤ 1 / 2)
    (desired : Bool) :
    (reversalLaw T p hp (by linarith)).event (fun ω =>
      ¬ MergesAt (graphFor T (reversals ω) desired) (j + 1) a s q) ≤
      ((2 ^ T : ℕ) : ℝ) ^ ((a + 1) * q) * (1 - p / 2) ^ q.choose 2 := by
  classical
  let μ := reversalLaw T p hp (by linarith)
  let fail (c : Configuration T a q) (ω : Coin T → Bool) :=
    configurationFails (graphFor T (reversals ω) desired) (j + 1) s c
  calc
    _ ≤ μ.event (fun ω => ∃ c, fail c ω) := μ.event_mono fun _ h => exists_configuration_failure hj h
    _ ≤ ∑ c, μ.event (fail c) := μ.event_exists_le_sum _
    _ ≤ ∑ _c : Configuration T a q, (1 - p / 2) ^ q.choose 2 :=
      Finset.sum_le_sum fun c _ => probability_configuration_fails hj hp hp' c ha hroom hbudget desired
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow]
      rw [add_mul, one_mul, pow_add, pow_mul]
      ring

/-- One outcome satisfies every required merging property for the graph
and its complement if the sum of the failure bounds is less than one. -/
theorem exists_simultaneous_merges {T r : ℕ} {a q : ℕ → ℕ}
    {p B : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1 / 2) (hB : 0 ≤ B)
    (ha : ∀ s, 2 ≤ s → s ≤ r → 0 < a s ∧ s ≤ a s + a s)
    (hbudget : ∀ s, 2 ≤ s → s ≤ r →
      (a s : ℝ) * a s * ((T : ℝ) * p) /
        ((a s + a s - s + 1 : ℕ) : ℝ) ≤ 1 / 2)
    (hprob : ∀ s, 2 ≤ s → s ≤ r →
      ((2 ^ T : ℕ) : ℝ) ^ ((a s + 1) * q s) * (1 - p / 2) ^ (q s).choose 2 ≤ B)
    (hsum : (2 * T * (r + 1) : ℕ) * B < 1) :
    ∃ G : SimpleGraph (Leaf T), ∀ s, 2 ≤ s → s ≤ r →
      ∀ j, 0 < j → j ≤ T → MergesAt G j (a s) s (q s) ∧ MergesAt Gᶜ j (a s) s (q s) := by
  classical
  let μ := reversalLaw T p hp (by linarith)
  let Bad (c : Bool × Fin T × Fin (r + 1)) (ω : Coin T → Bool) :=
    2 ≤ c.2.2.val ∧ ¬ MergesAt (graphFor T (reversals ω) c.1)
      (c.2.1.val + 1) (a c.2.2.val) c.2.2.val (q c.2.2.val)
  have hcase (c : Bool × Fin T × Fin (r + 1)) : μ.event (Bad c) ≤ B := by
    by_cases h : 2 ≤ c.2.2.val
    · let s := c.2.2.val
      have hs : s ≤ r := by dsimp [s]; omega
      have hbudget' : (a s : ℝ) * a s * ((T - (c.2.1.val + 1) : ℕ) * p) /
          ((a s + a s - s + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
        refine le_trans ?_ (hbudget s h hs)
        gcongr
        exact Nat.sub_le _ _
      have hb := probability_not_mergesAt (q := q s) (by omega : c.2.1.val + 1 ≤ T)
        hp hp' (ha s h hs).1 (ha s h hs).2 hbudget' c.1
      simpa only [Bad, h, true_and] using hb.trans (hprob s h hs)
    · rw [← FiniteLaw.mean_indicator]
      simpa [Bad, h, FiniteLaw.mean_const] using hB
  have hbad : μ.event (fun ω => ∃ c, Bad c ω) < 1 := by
    calc
      _ ≤ ∑ c, μ.event (Bad c) := μ.event_exists_le_sum _
      _ ≤ ∑ _c : Bool × Fin T × Fin (r + 1), B := Finset.sum_le_sum fun c _ => hcase c
      _ < _ := by
        simpa [Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, mul_assoc] using hsum
  obtain ⟨ω, hω⟩ := μ.event_lt_one_exists_not hbad
  refine ⟨graph T (reversals ω), ?_⟩
  intro s hs hr j hj hT
  let j' : Fin T := ⟨j - 1, by omega⟩
  let s' : Fin (r + 1) := ⟨s, by omega⟩
  have hg (b : Bool) : MergesAt (graphFor T (reversals ω) b) j (a s) s (q s) := by
    by_contra hfail
    exact hω ⟨(b, j', s'), hs, by
      simpa only [j', s', Nat.sub_add_cancel (Nat.succ_le_of_lt hj)] using hfail⟩
  exact ⟨by simpa [graphFor] using hg true, by simpa [graphFor] using hg false⟩

end LocallyRamsey.BinaryTree
