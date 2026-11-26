module

public import LocallyRamsey.IndependentBlocks

public section

open scoped BigOperators

namespace LocallyRamsey.FiniteLaw

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {S : I → Type*} [∀ i, Fintype (S i)]

/-- Revealing a fixed set of coordinates preserves independence and the
original laws at every other coordinate. -/
theorem mean_split_revealed (μ : (i : I) → FiniteLaw (S i)) (A : Finset I)
    (f : ((i : {i // i ∈ A}) → S i.val) × ((i : {i // i ∉ A}) → S i.val) → ℝ) :
    (product μ).mean (fun ω => f (fun i => ω i.val, fun i => ω i.val)) =
      ((product (fun i : {i // i ∈ A} => μ i.val)).staged
        (fun _ => product (fun i : {i // i ∉ A} => μ i.val))).mean f := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun x => x ∈ A) S
  simp only [mean]
  apply Fintype.sum_equiv e
  intro ω
  congr 1
  change (∏ i, (μ i).prob (ω i)) =
    (∏ i : {i // i ∈ A}, (μ i.val).prob (ω i.val)) *
      (∏ i : {i // i ∉ A}, (μ i.val).prob (ω i.val))
  calc
    _ = (∏ i ∈ A, (μ i).prob (ω i)) * ∏ i ∈ Aᶜ, (μ i).prob (ω i) :=
      (Finset.prod_mul_prod_compl A (fun i => (μ i).prob (ω i))).symm
    _ = _ := by
      congr 1
      · exact Finset.prod_subtype (p := fun i => i ∈ A) A (fun _ => Iff.rfl) _
      · exact Finset.prod_subtype (p := fun i => i ∉ A) Aᶜ (by simp) _

/-- Exponential bound for a test chosen from the exposed draws. For each
description the exposed draws may differ, but every unexposed draw uses
its original distribution. -/
theorem event_deferred_test_le (μ : (i : I) → FiniteLaw (S i)) (A : Finset I)
    (enabled : ((i : {i // i ∈ A}) → S i.val) → Prop)
    (X : ((i : {i // i ∈ A}) → S i.val) → (i : {i // i ∉ A}) → S i.val → ℝ)
    (hX : ∀ e i s, X e i s ∈ Set.Icc (0 : ℝ) 1)
    (a b : ℝ)
    (hmeans : ∀ e, enabled e → (∑ i, (μ i.val).mean (X e i)) ≤ a) :
    (product μ).event (fun ω => enabled (fun i => ω i.val) ∧
      b ≤ ∑ i : {i // i ∉ A}, X (fun j => ω j.val) i (ω i.val)) ≤
      Real.exp (a - Real.log 2 * b) := by
  classical
  let μA := product (fun i : {i // i ∈ A} => μ i.val)
  let ν := product (fun i : {i // i ∉ A} => μ i.val)
  let P (s : ((i : {i // i ∈ A}) → S i.val) × ((i : {i // i ∉ A}) → S i.val)) :=
    enabled s.1 ∧ b ≤ ∑ i, X s.1 i (s.2 i)
  have hsplit :
      (product μ).event (fun ω => enabled (fun i => ω i.val) ∧
        b ≤ ∑ i : {i // i ∉ A}, X (fun j => ω j.val) i (ω i.val)) =
      (μA.staged (fun _ => ν)).event P := by
    rw [← mean_indicator, ← mean_indicator]
    exact mean_split_revealed μ A (fun s => if P s then 1 else 0)
  rw [hsplit, staged_event, ← μA.mean_const (Real.exp (a - Real.log 2 * b))]
  apply μA.mean_mono
  intro e
  by_cases he : enabled e
  · simp only [P, he, true_and]
    have h := prob_sum_ge_le (fun i : {i // i ∉ A} => μ i.val) (X e) (hX e)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)) b
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), show (2 : ℝ) - 1 = 1 by norm_num, one_mul] at h
    exact h.trans (Real.exp_le_exp.mpr (sub_le_sub_right (hmeans e he) _))
  · rw [← ν.mean_indicator]
    simp only [P, he, false_and, ite_false, ν.mean_const]
    exact (Real.exp_pos _).le

/-- Union bound over descriptions for tests on draws that were left
unexposed. -/
theorem event_exists_deferred_test_le {D : Type*} [Fintype D]
    (μ : (i : I) → FiniteLaw (S i)) (A : D → Finset I)
    (enabled : (d : D) → ((i : {i // i ∈ A d}) → S i.val) → Prop)
    (X : (d : D) → ((i : {i // i ∈ A d}) → S i.val) → (i : {i // i ∉ A d}) → S i.val → ℝ)
    (hX : ∀ d e i s, X d e i s ∈ Set.Icc (0 : ℝ) 1)
    (a b : ℝ)
    (hmeans : ∀ d e, enabled d e → (∑ i, (μ i.val).mean (X d e i)) ≤ a) :
    (product μ).event (fun ω => ∃ d, enabled d (fun i => ω i.val) ∧
      b ≤ ∑ i : {i // i ∉ A d}, X d (fun j => ω j.val) i (ω i.val)) ≤
      (Fintype.card D : ℝ) * Real.exp (a - Real.log 2 * b) := by
  refine ((product μ).event_exists_le_sum (fun d ω => enabled d (fun i => ω i.val) ∧
    b ≤ ∑ i : {i // i ∉ A d}, X d (fun j => ω j.val) i (ω i.val))).trans ?_
  have h (d : D) := event_deferred_test_le μ (A d) (enabled d) (X d) (hX d) a b (hmeans d)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun d _ => h d)

/-- If successful draws admit a short description with a large remaining
score, at least one admissible test has substantial expected score. This
is the contradiction step after decoding the few recorded vertices. -/
theorem exists_test_of_deferred_reconstruction {D Ω T : Type*} [Fintype D] [Fintype Ω]
    (μ : FiniteLaw Ω) (l : ℕ) (A : D → Finset (Fin l))
    (decode : (d : D) → ({i // i ∈ A d} → Ω) → T)
    (valid : T → Prop) (score : T → Ω → ℝ)
    (hscore : ∀ t ω, score t ω ∈ Set.Icc (0 : ℝ) 1)
    (successful : (Fin l → Ω) → Prop) {a b : ℝ} (ha : 0 ≤ a)
    (hcount : (Fintype.card D : ℝ) * Real.exp ((l : ℝ) * a - Real.log 2 * b) <
      (product (fun _ : Fin l => μ)).event successful)
    (hdecode : ∀ ω, successful ω → ∃ d,
      valid (decode d (fun i => ω i.val)) ∧
        b ≤ ∑ i : {i // i ∉ A d}, score (decode d (fun j => ω j.val)) (ω i.val)) :
    ∃ t, valid t ∧ a ≤ μ.mean (score t) := by
  classical
  by_contra! hbad
  let ν := product (fun _ : Fin l => μ)
  let enabled (d : D) (e : {i // i ∈ A d} → Ω) := valid (decode d e)
  let X (d : D) (e : {i // i ∈ A d} → Ω) (_ : {i // i ∉ A d}) (ω : Ω) := score (decode d e) ω
  have hm (d : D) (e : {i // i ∈ A d} → Ω) (h : enabled d e) :
      ∑ i : {i // i ∉ A d}, μ.mean (X d e i) ≤ (l : ℝ) * a := by
    have hc : (Fintype.card {i // i ∉ A d} : ℝ) ≤ l := by
      exact_mod_cast (Fintype.card_le_of_injective (fun i : {i // i ∉ A d} => i.val)
        Subtype.val_injective).trans_eq (Fintype.card_fin l)
    calc
      _ ≤ ∑ _i : {i // i ∉ A d}, a := Finset.sum_le_sum (fun _ _ => (hbad (decode d e) h).le)
      _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hc ha
  have hprob := event_exists_deferred_test_le (fun _ : Fin l => μ) A enabled X
    (fun d e _ ω => hscore (decode d e) ω) ((l : ℝ) * a) b hm
  exact (not_lt_of_ge ((ν.event_mono hdecode).trans hprob)) hcount

end LocallyRamsey.FiniteLaw
