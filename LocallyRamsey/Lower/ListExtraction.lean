module

public import LocallyRamsey.Lower.RandomList
public import LocallyRamsey.Lower.DisjointDraws

public section

namespace LocallyRamsey

open scoped BigOperators

namespace FiniteLaw

/-- The uniform law on a nonempty finite type. -/
@[expose] noncomputable def uniform (Q : Type*) [Fintype Q] [Nonempty Q] : FiniteLaw Q where
  prob _ := (Fintype.card Q : ℝ)⁻¹
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : (Fintype.card Q : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact mul_inv_cancel₀ h

theorem uniform_event {Q : Type*} [Fintype Q] [Nonempty Q] (P : Q → Prop) [DecidablePred P] :
    (uniform Q).event P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Q := by
  rw [← (uniform Q).mean_indicator P]
  rw [div_eq_mul_inv, mul_comm]
  calc
    _ = (Fintype.card Q : ℝ)⁻¹ * ∑ x, (if P x then 1 else 0) := by
      simp only [mean, uniform, Finset.mul_sum]
    _ = _ := by simp

/-- Exposing one point of an independent tuple bounds the chance that a
second point has the same assigned draw. -/
theorem event_same_label_le {I Q K : Type*} [Fintype I] [DecidableEq I] [Fintype Q]
    (μ : FiniteLaw Q) (label : Q → K) {i j : I} (hij : i ≠ j) {c : ℝ}
    (hcap : ∀ x, μ.event (fun y => label x = label y) ≤ c) :
    (product (fun _ : I => μ)).event (fun ω => label (ω i) = label (ω j)) ≤ c := by
  exact event_pair_draw_le μ hij (fun x y => label x = label y) hcap

theorem event_noninjective_labels_le {Q K : Type*} [Fintype Q]
    (μ : FiniteLaw Q) (label : Q → K) (s : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hcap : ∀ x, μ.event (fun y => label x = label y) ≤ c) :
    (product (fun _ : Fin s => μ)).event (fun ω => ¬Function.Injective (label ∘ ω)) ≤
      (s : ℝ) ^ 2 * c := by
  classical
  let ν := product (fun _ : Fin s => μ)
  let test (d : Fin s × Fin s) (ω : Fin s → Q) :=
    d.1 ≠ d.2 ∧ label (ω d.1) = label (ω d.2)
  have hevent : ν.event (fun ω => ¬ Function.Injective (label ∘ ω)) ≤
      ∑ d, ν.event (test d) := by
    refine (ν.event_mono ?_).trans (ν.event_exists_le_sum test)
    intro ω h
    simp only [Function.Injective, Function.comp_apply, not_forall] at h
    obtain ⟨i, j, heq, hne⟩ := h
    exact ⟨(i, j), hne, heq⟩
  have htest (d : Fin s × Fin s) : ν.event (test d) ≤ c := by
    by_cases h : d.1 = d.2
    · rw [← ν.mean_indicator]
      simpa [test, h, mean_const] using hc
    · refine (ν.event_mono (fun _ ht => ht.2)).trans ?_
      exact event_same_label_le μ label h hcap
  exact hevent.trans ((Finset.sum_le_sum fun d _ => htest d).trans_eq (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul, pow_two]))

end FiniteLaw

/-- Draw several candidate vertices independently from (Q). If all
tuples assigned to distinct draws have many common neighbours on the list,
the expected number of common neighbours is large. But the assumed
degree bound gives a small probability that any individual list entry is
one of those common neighbours. -/
theorem exists_small_common_of_list {Q J Y : Type*} [Fintype Q]
    (μ : FiniteLaw Q) (assign : Q → J) (adj : Y → Q → Prop) [DecidableRel adj]
    {m s : ℕ} (list : Fin m → Y) {c d p : ℝ}
    (hc₀ : 0 ≤ c) (hcollision : (s : ℝ) ^ 2 * c ≤ 1 / 2)
    (hcap : ∀ x, μ.event (fun y => assign x = assign y) ≤ c)
    (hdeg : ∀ j, μ.event (adj (list j)) ≤ d) (_hd : 0 ≤ d)
    (hp : 0 ≤ p) (hsmall : m * d ^ s < p * m / 4)
    (largeCommon : (Fin s → Q) → Prop)
    (hlist : ∀ ω : Fin s → Q, Function.Injective (assign ∘ ω) → largeCommon ω →
      p * m / 2 ≤ ∑ j, if ∀ k, adj (list j) (ω k) then (1 : ℝ) else 0) :
    ∃ ω : Fin s → Q, Function.Injective (assign ∘ ω) ∧ ¬ largeCommon ω := by
  classical
  let ν := FiniteLaw.product (fun _ : Fin s => μ)
  let good (ω : Fin s → Q) := Function.Injective (assign ∘ ω)
  let count (ω : Fin s → Q) : ℝ := ∑ j, if ∀ k, adj (list j) (ω k) then 1 else 0
  by_contra! h
  have hgood : (1 : ℝ) / 2 ≤ ν.event good := by
    have hb := (FiniteLaw.event_noninjective_labels_le μ assign s hc₀ hcap).trans hcollision
    change ν.event (fun ω => ¬ good ω) ≤ 1 / 2 at hb
    rw [ν.event_not] at hb
    linarith
  have hlo : p * m / 4 ≤ ν.mean count := by
    calc
      _ = (p * m / 2) * (1 / 2) := by ring
      _ ≤ (p * m / 2) * ν.event good := mul_le_mul_of_nonneg_left hgood (by positivity)
      _ = ν.mean (fun ω => (p * m / 2) * (if good ω then 1 else 0)) := by
        rw [ν.mean_mul_const, ν.mean_indicator]
      _ ≤ _ := by
        apply ν.mean_mono
        intro ω
        by_cases hw : good ω
        · simpa [hw, count] using hlist ω hw (h ω hw)
        · simp only [hw, ite_false, mul_zero]
          exact Finset.sum_nonneg fun _ _ => by split <;> positivity
  have hhi : ν.mean count ≤ m * d ^ s := by
    change ν.mean (fun ω => ∑ j, if ∀ k, adj (list j) (ω k) then 1 else 0) ≤ _
    rw [ν.mean_sum]
    calc
      _ ≤ ∑ _j : Fin m, d ^ s := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [ν.mean_indicator]
        change (FiniteLaw.product (fun _ : Fin s => μ)).event (fun ω => ∀ k, adj (list j) (ω k)) ≤ _
        rw [FiniteLaw.event_all (fun _ : Fin s => μ) (fun _ => adj (list j))]
        simpa using Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin s)))
          (fun _ _ => μ.event_nonneg (adj (list j))) (fun _ _ => hdeg j)
      _ = _ := by simp
  exact (not_lt_of_ge (hlo.trans hhi)) hsmall

end LocallyRamsey
