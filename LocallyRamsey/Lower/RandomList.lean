module

public import LocallyRamsey.IndependentBlocks

public section

open scoped BigOperators

namespace LocallyRamsey

namespace FiniteLaw

variable {A V J : Type*} [Fintype A] [Fintype V] [Fintype J] [DecidableEq J]
variable {S : J → Type*} [∀ j, Fintype (S j)]

/-- In independent draws, specifying one condition at each of several
distinct coordinates costs the product of its probabilities. -/
theorem event_all_at_injective (μ : (j : J) → FiniteLaw (S j))
    {K : Type*} [Fintype K] (f : K → J) (hf : Function.Injective f)
    (P : (j : J) → S j → Prop) :
    (product μ).event (fun ω => ∀ k, P (f k) (ω (f k))) =
      ∏ k, (μ (f k)).event (P (f k)) := by
  classical
  let Q (j : J) (y : S j) := j ∈ Set.range f → P j y
  have heq (ω : (j : J) → S j) :
      (∀ k, P (f k) (ω (f k))) ↔ ∀ j, Q j (ω j) := by
    constructor
    · rintro H j ⟨k, rfl⟩
      exact H k
    · exact fun H k => H (f k) ⟨k, rfl⟩
  have hyes (j : J) (hj : j ∈ Finset.univ.image f) :
      (μ j).event (Q j) = (μ j).event (P j) := by
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    have hr : f k ∈ Set.range f := ⟨k, rfl⟩
    simp only [Q, hr, true_implies]
  have hno (j : J) (hj : j ∉ Finset.univ.image f) : (μ j).event (Q j) = 1 := by
    have hr : j ∉ Set.range f := by simpa using hj
    rw [← (μ j).mean_indicator (Q j)]
    simp only [Q, hr, false_implies, ite_true, mean_const]
  simp_rw [heq]
  rw [event_all]
  calc
    _ = ∏ j ∈ Finset.univ.image f, (μ j).event (Q j) := by
      symm
      exact Finset.prod_subset (Finset.subset_univ _) (fun j _ hj => hno j hj)
    _ = ∏ j ∈ Finset.univ.image f, (μ j).event (P j) :=
      Finset.prod_congr rfl hyes
    _ = _ := Finset.prod_image (fun _ _ _ _ h => hf h)

omit [Fintype V] in
/-- If a list event is rare, then it is still rare together with prescribed
inclusions in distinct draws. The draws may use the list in choosing their
laws, provided their marginal bounds hold for every list. -/
theorem staged_event_prescribed_inclusions_le (μ : FiniteLaw A)
    (ν : A → (j : J) → FiniteLaw (S j))
    (contains : A → (j : J) → S j → V → Prop) (a : J → V → ℝ)
    (ha : ∀ L j v, (ν L j).event (fun s => contains L j s v) ≤ a j v)
    {K : Type*} [Fintype K] (f : K → J) (hf : Function.Injective f) (v : K → V)
    (P : A → Prop) :
    (μ.staged (fun L => product (ν L))).event (fun Lω =>
      P Lω.1 ∧ ∀ k, contains Lω.1 (f k) (Lω.2 (f k)) (v k)) ≤
      μ.event P * ∏ k, a (f k) (v k) := by
  classical
  let read (L : A) (j : J) (s : S j) := ∀ k, f k = j → contains L j s (v k)
  have hread (L : A) (ω : (j : J) → S j) :
      (∀ k, contains L (f k) (ω (f k)) (v k)) ↔ ∀ k, read L (f k) (ω (f k)) := by
    constructor
    · intro H k l hl
      rw [hf hl]
      exact H k
    · exact fun H k => H k k rfl
  have hsingle (L : A) (k : K) :
      (ν L (f k)).event (read L (f k)) = (ν L (f k)).event (fun s => contains L (f k) s (v k)) := by
    congr 1
    funext s
    apply propext
    exact ⟨fun H => H k rfl, fun H l hl => by rw [hf hl]; exact H⟩
  let bound := ∏ k, a (f k) (v k)
  have htail (L : A) : (product (ν L)).event (fun ω =>
      ∀ k, contains L (f k) (ω (f k)) (v k)) ≤ bound := by
    simp_rw [hread]
    rw [event_all_at_injective (ν L) f hf, show bound = _ by rfl]
    exact Finset.prod_le_prod₀ (fun _ _ => event_nonneg _ _)
      (fun k _ => (hsingle L k).trans_le (ha L (f k) (v k)))
  have hcond (L : A) : (product (ν L)).event (fun ω =>
      P L ∧ ∀ k, contains L (f k) (ω (f k)) (v k)) ≤ (if P L then 1 else 0) * bound := by
    by_cases h : P L
    · simpa [h] using htail L
    · rw [← mean_indicator]
      simp [h, mean_const]
  rw [staged_event, ← mean_indicator]
  calc
    _ ≤ μ.mean (fun L => (if P L then 1 else 0) * bound) := μ.mean_mono hcond
    _ = _ := by simp_rw [mul_comm _ bound]; rw [μ.mean_mul_const, mul_comm]

/-- Sum the list estimate over every choice of (s) vertices and their
assigned draws. A uniform list estimate contributes the same factor
for each tuple. -/
theorem staged_event_exists_injective_inclusions_le (μ : FiniteLaw A)
    (ν : A → (j : J) → FiniteLaw (S j))
    (contains : A → (j : J) → S j → V → Prop) (a : J → V → ℝ)
    (ha : ∀ L j v, (ν L j).event (fun s => contains L j s v) ≤ a j v)
    (ha0 : ∀ j v, 0 ≤ a j v) (s : ℕ) (P : (Fin s → V) → A → Prop)
    {ε : ℝ} (hε : 0 ≤ ε) (hP : ∀ v, μ.event (P v) ≤ ε) :
    (μ.staged (fun L => product (ν L))).event (fun Lω =>
      ∃ (f : Fin s → J) (v : Fin s → V), Function.Injective f ∧ P v Lω.1 ∧
        ∀ k, contains Lω.1 (f k) (Lω.2 (f k)) (v k)) ≤ ε * (∑ j, ∑ v, a j v) ^ s := by
  classical
  let ξ := μ.staged (fun L => product (ν L))
  let Q (d : Fin s → J × V) (Lω : A × ((j : J) → S j)) :=
    Function.Injective (fun k => (d k).1) ∧ P (fun k => (d k).2) Lω.1 ∧
      ∀ k, contains Lω.1 (d k).1 (Lω.2 (d k).1) (d k).2
  have hUnion : ξ.event (fun Lω => ∃ (f : Fin s → J) (v : Fin s → V),
      Function.Injective f ∧ P v Lω.1 ∧
        ∀ k, contains Lω.1 (f k) (Lω.2 (f k)) (v k)) ≤ ∑ d, ξ.event (Q d) :=
    (ξ.event_mono (by rintro Lω ⟨f, v, h⟩; exact ⟨fun k => (f k, v k), h⟩)).trans
      (ξ.event_exists_le_sum Q)
  have hEach (d : Fin s → J × V) :
      ξ.event (Q d) ≤ ε * ∏ k, a (d k).1 (d k).2 := by
    by_cases h : Function.Injective (fun k => (d k).1)
    · refine (ξ.event_mono (fun _ h => h.2)).trans ?_
      exact (staged_event_prescribed_inclusions_le μ ν contains a ha (fun k => (d k).1)
        h (fun k => (d k).2) (P (fun k => (d k).2))).trans
        (mul_le_mul_of_nonneg_right (hP _) (Finset.prod_nonneg fun k _ => ha0 _ _))
    · have hempty : ξ.event (Q d) = 0 := by
        rw [← mean_indicator]
        simp [Q, h, mean_const]
      rw [hempty]
      exact mul_nonneg hε (Finset.prod_nonneg fun k _ => ha0 _ _)
  refine hUnion.trans ((Finset.sum_le_sum fun d _ => hEach d).trans_eq ?_)
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (_ : Fin s) (x : J × V) => a x.1 x.2)]
  simp [Fintype.sum_prod_type]

end FiniteLaw

end LocallyRamsey
