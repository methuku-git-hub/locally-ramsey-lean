module

public import LocallyRamsey.Overlap

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V R : Type*} [DecidableEq V] [Fintype R] [DecidableEq R]

/-- Inclusion weights of a collection of partial sampling rules. -/
@[expose] def mixtureWeight (f : R → V → ℝ) (a : R → ℝ) (x : V) : ℝ :=
  ∑ r, a r * f r x

/-- Increase one coefficient until a vertex with positive contribution
first reaches the prescribed marginal. -/
theorem exists_saturating_coefficient (A : Finset V) (w f : V → ℝ) {t : ℝ}
    (hw : ∀ x ∈ A, w x < t) (hf : ∀ x ∈ A, 0 ≤ f x)
    (hsum : 0 < mass f A) :
    ∃ c : ℝ, 0 < c ∧ (∀ x ∈ A, w x + c * f x ≤ t) ∧
      ∃ x ∈ A, w x + c * f x = t := by
  classical
  let D := A.filter (fun x => 0 < f x)
  have hD : D.Nonempty := by
    by_contra h
    have hzero (x : V) (hx : x ∈ A) : f x = 0 :=
      le_antisymm (le_of_not_gt fun hp => h ⟨x, Finset.mem_filter.mpr ⟨hx, hp⟩⟩) (hf x hx)
    have hz : mass f A = 0 := by
      rw [mass, Finset.sum_congr rfl hzero]
      simp
    linarith only [hsum, hz]
  let ratio (x : V) := (t - w x) / f x
  let E := D.image ratio
  let c := E.min' (hD.image ratio)
  have hc : c ∈ E := E.min'_mem _
  obtain ⟨x, hx, hxval⟩ := Finset.mem_image.mp hc
  obtain ⟨hxA, hxf⟩ := Finset.mem_filter.mp hx
  refine ⟨c, hxval ▸ div_pos (sub_pos.mpr (hw x hxA)) hxf, ?_, ⟨x, hxA, ?_⟩⟩
  · intro y hyA
    by_cases hy : 0 < f y
    · have hmin : c ≤ ratio y := E.min'_le _ (Finset.mem_image.mpr
        ⟨y, Finset.mem_filter.mpr ⟨hyA, hy⟩, rfl⟩)
      have hm := (le_div_iff₀ hy).mp hmin
      linarith only [hm]
    · have hzero : f y = 0 := le_antisymm (le_of_not_gt hy) (hf y hyA)
      simpa [hzero] using (hw y hyA).le
  · have hEq := (div_eq_iff hxf.ne').mp hxval
    linarith only [hEq]

/-- One stage of the marginal adjustment. It ends when the number of
unsaturated vertices is below the cutoff or at most half the number at
the start. Its cost is at most (2t/d). -/
theorem saturate_stage (B : Finset V) (f : R → V → ℝ)
    (hf : ∀ r x, 0 ≤ f r x) {t d : ℝ} (ht : 0 ≤ t) (hd : 0 < d)
    (cutoff : ℕ)
    (available : ∀ A : Finset V, A ⊆ B → cutoff < A.card →
      ∃ r, (∀ x ∈ B, x ∉ A → f r x = 0) ∧ d * A.card ≤ mass (f r) A)
    (a : R → ℝ) (ha : ∀ r, 0 ≤ a r) (hacap : ∀ x ∈ B, mixtureWeight f a x ≤ t) :
    ∃ a' : R → ℝ, (∀ r, a r ≤ a' r) ∧ (∀ x ∈ B, mixtureWeight f a' x ≤ t) ∧
      (∑ r, a' r) ≤ (∑ r, a r) + 2 * t / d ∧
      (B.filter (fun x => mixtureWeight f a' x < t)).card ≤
        max cutoff ((B.filter (fun x => mixtureWeight f a x < t)).card / 2) := by
  classical
  let active (p : R → ℝ) := B.filter (fun x => mixtureWeight f p x < t)
  let A₀ := active a
  let k := A₀.card
  let stop := max cutoff (k / 2)
  let rate := d * (k : ℝ) / 2
  have hmono {a₁ a₂ : R → ℝ} (h : ∀ r, a₁ r ≤ a₂ r) (x : V) :
      mixtureWeight f a₁ x ≤ mixtureWeight f a₂ x := by
    exact Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right (h r) (hf r x))
  have hactive {a₁ a₂ : R → ℝ} (h : ∀ r, a₁ r ≤ a₂ r) : active a₂ ⊆ active a₁ := by
    intro x hx
    obtain ⟨hxB, hlt⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxB, (hmono h x).trans_lt hlt⟩
  have hrec (m : ℕ) (a₁ : R → ℝ) (hm : (active a₁).card = m)
      (hmon : ∀ r, a r ≤ a₁ r) (hcap : ∀ x ∈ B, mixtureWeight f a₁ x ≤ t) :
      ∃ a₂ : R → ℝ, (∀ r, a₁ r ≤ a₂ r) ∧ (∀ x ∈ B, mixtureWeight f a₂ x ≤ t) ∧
        (active a₂).card ≤ stop ∧
        rate * ((∑ r, a₂ r) - ∑ r, a₁ r) ≤
          mass (mixtureWeight f a₂) A₀ - mass (mixtureWeight f a₁) A₀ := by
    induction m using Nat.strong_induction_on generalizing a₁ with
    | h m ih =>
      by_cases hmStop : (active a₁).card ≤ stop
      · exact ⟨a₁, fun _ => le_rfl, hcap, hmStop, by simp⟩
      · let A := active a₁
        have hAB : A ⊆ B := Finset.filter_subset _ _
        have hA0 : A ⊆ A₀ := hactive hmon
        have hcut : cutoff < A.card := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hmStop)
        have hhalf : (k : ℝ) / 2 ≤ A.card := by
          have hh : k ≤ 2 * A.card := by
            have hh := lt_of_le_of_lt (le_max_right cutoff (k / 2)) (lt_of_not_ge hmStop)
            change k / 2 < A.card at hh
            omega
          have hh' : (k : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hh
          linarith only [hh']
        obtain ⟨r, hsupport, hmean⟩ := available A hAB hcut
        have hsum : 0 < mass (f r) A := (mul_pos hd (by
          exact_mod_cast (Nat.zero_le cutoff).trans_lt hcut)).trans_le hmean
        obtain ⟨c, hc, hle, x, hx, hxeq⟩ := exists_saturating_coefficient A (mixtureWeight f a₁)
          (f r) (fun y hy => (Finset.mem_filter.mp hy).2) (fun y _ => hf r y) hsum
        let next (u : R) := a₁ u + if u = r then c else 0
        have hnext_mono (u : R) : a₁ u ≤ next u := by
          dsimp [next]
          split <;> linarith
        have hnext_w (y : V) : mixtureWeight f next y = mixtureWeight f a₁ y + c * f r y := by
          simp only [mixtureWeight, next, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        have hnext_sum : (∑ u, next u) = (∑ u, a₁ u) + c := by simp [next, Finset.sum_add_distrib]
        have hnext_cap (y : V) (hy : y ∈ B) : mixtureWeight f next y ≤ t := by
          rw [hnext_w]
          by_cases hyA : y ∈ A
          · exact hle y hyA
          · rw [hsupport y hy hyA, mul_zero, add_zero]
            exact hcap y hy
        have hnext_lt : (active next).card < m := by
          rw [← hm]
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hactive hnext_mono, fun he => ?_⟩
          have hb : x ∈ active next := he ▸ hx
          have hlt := (Finset.mem_filter.mp hb).2
          rw [hnext_w, hxeq] at hlt
          exact (lt_irrefl t) hlt
        obtain ⟨a₂, ha₂, ha₂cap, ha₂stop, ha₂budget⟩ :=
          ih _ hnext_lt next rfl (fun u => (hmon u).trans (hnext_mono u)) hnext_cap
        refine ⟨a₂, fun u => (hnext_mono u).trans (ha₂ u), ha₂cap, ha₂stop, ?_⟩
        have hstep : rate * c ≤ mass (mixtureWeight f next) A₀ - mass (mixtureWeight f a₁) A₀ := by
          have hEq : mass (mixtureWeight f next) A₀ =
              mass (mixtureWeight f a₁) A₀ + c * mass (f r) A₀ := by
            simp only [mass, hnext_w, Finset.sum_add_distrib, Finset.mul_sum]
          rw [hEq, add_sub_cancel_left]
          refine mul_le_mul_of_nonneg_right ?_ hc.le
            |>.trans_eq (mul_comm _ _)
          change d * ↑k / 2 ≤ _
          have hp := mul_le_mul_of_nonneg_left hhalf hd.le
          exact (show d * ↑k / 2 ≤ d * ↑A.card by linarith only [hp]).trans
            (hmean.trans (mass_mono (hf r) hA0))
        rw [hnext_sum] at ha₂budget
        nlinarith only [hstep, ha₂budget]
  by_cases hk : k = 0
  · refine ⟨a, fun _ => le_rfl, hacap, ?_, ?_⟩
    · linarith only [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht) hd.le]
    · change k ≤ stop
      omega
  obtain ⟨a', ha'ge, ha'cap, ha'stop, ha'cost⟩ := hrec _ a rfl (fun _ => le_rfl) hacap
  refine ⟨a', ha'ge, ha'cap, ?_, ha'stop⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
  have hup : mass (mixtureWeight f a') A₀ ≤ k * t := by
    refine (Finset.sum_le_sum (s := A₀) (fun x hx => ha'cap x (Finset.mem_filter.mp hx).1)).trans_eq ?_
    simp [k]
  have hlo : 0 ≤ mass (mixtureWeight f a) A₀ :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun r _ => mul_nonneg (ha r) (hf r x)))
  have hd' : d * k / 2 > 0 := by positivity
  have hProd := ha'cost.trans (sub_le_self _ hlo) |>.trans hup
  have hdiv : ((∑ r, a' r) - ∑ r, a r) ≤ (k * t) / (d * k / 2) :=
    (le_div_iff₀ hd').mpr (by rw [mul_comm]; exact hProd)
  have hcancel : (k * t) / (d * k / 2) = 2 * t / d := by field_simp
  linarith only [hdiv, hcancel]

/-- Repeating the marginal adjustment leaves only the allowed number of
exceptional vertices. The coefficients can be completed to a probability
distribution by assigning the leftover probability to the empty set. -/
theorem exists_capped_mixture (B : Finset V) (f : R → V → ℝ)
    (hf : ∀ r x, 0 ≤ f r x) {t d : ℝ} (ht : 0 ≤ t) (hd : 0 < d)
    (cutoff stages : ℕ)
    (available : ∀ A : Finset V, A ⊆ B → cutoff < A.card →
      ∃ r, (∀ x ∈ B, x ∉ A → f r x = 0) ∧ d * A.card ≤ mass (f r) A)
    (hcut : B.card / 2 ^ stages ≤ cutoff) (hcost : stages * (2 * t / d) ≤ 1) :
    ∃ a : R → ℝ, (∀ r, 0 ≤ a r) ∧ (∑ r, a r) ≤ 1 ∧
      (∀ x ∈ B, mixtureWeight f a x ≤ t) ∧
      (B.filter (fun x => mixtureWeight f a x < t)).card ≤ cutoff := by
  classical
  have stage (k : ℕ) : ∃ a : R → ℝ, (∀ r, 0 ≤ a r) ∧
      (∀ x ∈ B, mixtureWeight f a x ≤ t) ∧
      (∑ r, a r) ≤ k * (2 * t / d) ∧
      (B.filter (fun x => mixtureWeight f a x < t)).card ≤ max cutoff (B.card / 2 ^ k) := by
    induction k with
    | zero =>
      refine ⟨fun _ => 0, fun _ => le_rfl, fun _ _ => ?_, ?_, ?_⟩
      · simpa [mixtureWeight] using ht
      · simp
      · exact (Finset.card_filter_le _ _).trans (by simp)
    | succ k ih =>
      obtain ⟨a, ha, hacap, haCost, haSize⟩ := ih
      obtain ⟨a', ha'ge, ha'cap, ha'cost, ha'stop⟩ :=
        saturate_stage B f hf ht hd cutoff available a ha hacap
      refine ⟨a', fun r => (ha r).trans (ha'ge r), ha'cap, ?_, ?_⟩
      · have hh := ha'cost.trans (add_le_add_left haCost _)
        push_cast
        linarith only [hh]
      · have hdiv := Nat.div_le_div_right (c := 2) haSize
        refine ha'stop.trans ((max_le_max_left _ hdiv).trans ?_)
        rw [pow_succ, ← Nat.div_div_eq_div_mul]
        by_cases h : cutoff ≤ B.card / 2 ^ k
        · rw [max_eq_right h]
        · rw [max_eq_left (le_of_not_ge h)]
          exact max_le (le_max_left _ _) ((Nat.div_le_self _ _).trans (le_max_left _ _))
  obtain ⟨a, ha, hcap, hsum, hactive⟩ := stage stages
  exact ⟨a, ha, hsum.trans hcost, hcap, hactive.trans (max_le le_rfl hcut)⟩

end LocallyRamsey
