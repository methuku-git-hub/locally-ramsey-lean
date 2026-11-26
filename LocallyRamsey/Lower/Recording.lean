module

public import LocallyRamsey.Overlap
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

namespace LocallyRamsey

open scoped BigOperators

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbours of a vertex inside the current set. -/
@[expose] def neighborsIn (X : Finset V) (x : V) : Finset V :=
  X.filter fun y => G.Adj x y

/-- Reconstruct the unrecorded remainder by inspecting vertices in the same
order and removing a neighbourhood exactly at the recorded vertices. -/
def recordRemainder (choose : Finset V → Option V) (R : Finset V) :
    ℕ → Finset V → Finset V
  | 0, X => X
  | n + 1, X => match choose X with
    | none => X
    | some x => recordRemainder choose R n
        (if x ∈ R then nonNeighbors G X x else X.erase x)

/-- The recording procedure preserves all points of the independent set.
The displayed potential decreases multiplicatively at each record, and
the records reconstruct the remainder without the independent set. -/
theorem recording_core (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (c D : ℝ) (hD : 1 < D) (Q : Finset V)
    (hQ : Gᶜ.IsClique (Q : Set V))
    (choose : Finset V → Option V)
    (hnone : ∀ X, choose X = none →
      ∀ x ∈ X, mass w (neighborsIn G X x) ≤ (mass w X + c) / D)
    (hsome : ∀ X x, choose X = some x →
      x ∈ X ∧ (mass w X + c) / D < mass w (neighborsIn G X x))
    (n : ℕ) (X : Finset V) (hcard : X.card ≤ n) :
    ∃ R Y : Finset V,
      R ⊆ Q ∩ X ∧ Y ⊆ X ∧ Disjoint R Y ∧
      Q ∩ X ⊆ R ∪ Y ∧
      (∀ x ∈ R, ∀ y ∈ Y, ¬ G.Adj x y) ∧
      (∀ y ∈ Y, mass w (neighborsIn G Y y) ≤ (mass w Y + c) / D) ∧
      mass w Y + c ≤ (1 - 1 / D) ^ R.card * (mass w X + c) ∧
      ∀ R' : Finset V, Disjoint R' X → recordRemainder G choose (R ∪ R') n X = Y := by
  have hfactor : 0 ≤ 1 - 1 / D := sub_nonneg.mpr (div_le_one (by linarith) |>.mpr hD.le)
  induction n generalizing X with
  | zero =>
    have hX : X = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    subst X
    exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp [mass], by simp [recordRemainder]⟩
  | succ n ih =>
    cases hchoice : choose X with
    | none =>
      exact ⟨∅, X, by simp, fun _ hx => hx, by simp, by simp, by simp,
        hnone X hchoice, by simp, by simp [recordRemainder, hchoice]⟩
    | some x =>
      obtain ⟨hx, hhigh⟩ := hsome X x hchoice
      by_cases hxQ : x ∈ Q
      · let A := nonNeighbors G X x
        have hAsub : A ⊆ X := Finset.filter_subset _ _
        have hxA : x ∉ A := by simp [A, nonNeighbors]
        have hAcard : A.card ≤ n := by
          have h := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, fun h => hxA (h ▸ hx)⟩)
          omega
        obtain ⟨R, Y, hR, hY, hdisj, hcover, hcross, hdeg, hpot, hrec⟩ := ih A hAcard
        have hxR : x ∉ R := fun h => hxA (Finset.mem_inter.mp (hR h)).2
        have hxY : x ∉ Y := fun h => hxA (hY h)
        have hneg (y : V) (hy : y ∈ A) : ¬ G.Adj x y := by
          exact fun hadj => (Finset.mem_filter.mp hy).2 (Or.inr hadj)
        have hpartition : Disjoint A (neighborsIn G X x) :=
          Finset.disjoint_left.mpr fun y hy hy' => hneg y hy (Finset.mem_filter.mp hy').2
        have hsum : mass w A + mass w (neighborsIn G X x) ≤ mass w X := by
          simp only [mass]
          rw [← Finset.sum_union hpartition]
          exact mass_mono hw (Finset.union_subset hAsub (Finset.filter_subset _ _))
        have hstep : mass w A + c ≤ (1 - 1 / D) * (mass w X + c) := by
          rw [sub_mul, one_mul, div_mul_eq_mul_div, one_mul]
          linarith
        refine ⟨insert x R, Y, ?_, hY.trans hAsub, ?_, ?_, ?_, hdeg, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_inter.mpr ⟨hxQ, hx⟩
          · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hR hy)).1,
              hAsub ((Finset.mem_inter.mp (hR hy)).2)⟩
        · exact Finset.disjoint_left.mpr fun y hy hyY => by
            rcases Finset.mem_insert.mp hy with rfl | hy
            · exact hxY hyY
            · exact Finset.disjoint_left.mp hdisj hy hyY
        · intro y hy
          obtain ⟨hyQ, hyX⟩ := Finset.mem_inter.mp hy
          by_cases hyx : y = x
          · simp [hyx]
          · have hyA : y ∈ A := by
              refine Finset.mem_filter.mpr ⟨hyX, ?_⟩
              have hc := hQ hxQ hyQ (Ne.symm hyx)
              exact fun h => h.elim (Ne.symm hyx) ((SimpleGraph.compl_adj G x y).mp hc).2
            have hh := hcover (Finset.mem_inter.mpr ⟨hyQ, hyA⟩)
            rcases Finset.mem_union.mp hh with hh | hh
            · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hh)
            · exact Finset.mem_union_right _ hh
        · intro y hy z hz
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hneg z (hY hz)
          · exact hcross y hy z hz
        · rw [Finset.card_insert_of_notMem hxR, pow_succ, mul_assoc]
          exact hpot.trans (mul_le_mul_of_nonneg_left hstep (pow_nonneg hfactor _))
        · intro R' hR'
          have hR'A : Disjoint (insert x R') A :=
            Finset.disjoint_left.mpr fun y hy hyA => by
              rcases Finset.mem_insert.mp hy with rfl | hy
              · exact hxA hyA
              · exact Finset.disjoint_left.mp hR' hy (hAsub hyA)
          have hrearrange : (insert x R) ∪ R' = R ∪ insert x R' := by
            ext z
            simp only [Finset.mem_union, Finset.mem_insert]
            tauto
          rw [recordRemainder, hchoice]
          simp only [Finset.mem_union, Finset.mem_insert_self, true_or, ite_true]
          rw [hrearrange]
          exact hrec _ hR'A
      · let A := X.erase x
        have hAsub : A ⊆ X := Finset.erase_subset _ _
        have hAcard : A.card ≤ n := by
          have hlt := Finset.card_erase_lt_of_mem hx
          dsimp [A]
          omega
        obtain ⟨R, Y, hR, hY, hdisj, hcover, hcross, hdeg, hpot, hrec⟩ := ih A hAcard
        have hRsub : R ⊆ Q ∩ X := by
          intro y hy
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hR hy)).1,
            hAsub ((Finset.mem_inter.mp (hR hy)).2)⟩
        refine ⟨R, Y, hRsub, hY.trans hAsub, hdisj, ?_, hcross, hdeg, ?_, ?_⟩
        · intro y hy
          obtain ⟨hyQ, hyX⟩ := Finset.mem_inter.mp hy
          exact hcover (Finset.mem_inter.mpr ⟨hyQ, Finset.mem_erase.mpr
            ⟨fun heq => hxQ (heq ▸ hyQ), hyX⟩⟩)
        · exact hpot.trans (mul_le_mul_of_nonneg_left
            (add_le_add_left (mass_mono hw hAsub) c) (pow_nonneg hfactor _))
        · intro R' hR'
          have hxRR' : x ∉ R ∪ R' := by
            simp only [Finset.mem_union, not_or]
            exact ⟨fun h => hxQ (Finset.mem_inter.mp (hR h)).1,
              fun h => Finset.disjoint_left.mp hR' h hx⟩
          simp only [recordRemainder, hchoice, ite_eq_right hxRR']
          exact hrec _ (hR'.mono_right hAsub)

section FixedOrder

variable [LinearOrder V]

/-- The first vertex, in the fixed order, violating the weighted degree
condition, if there is one. -/
noncomputable def chooseHeavy (w : V → ℝ) (c D : ℝ) (X : Finset V) : Option V := by
  classical
  let bad := X.filter fun x => (mass w X + c) / D < mass w (neighborsIn G X x)
  exact if h : bad.Nonempty then some (bad.min' h) else none

omit [DecidableEq V] in
theorem chooseHeavy_none (w : V → ℝ) (c D : ℝ) (X : Finset V)
    (hnone : chooseHeavy G w c D X = none) :
    ∀ x ∈ X, mass w (neighborsIn G X x) ≤ (mass w X + c) / D := by
  classical
  intro x hx
  by_contra! hbad
  unfold chooseHeavy at hnone
  dsimp only at hnone
  split at hnone
  · contradiction
  · rename_i hn
    exact hn (⟨x, Finset.mem_filter.mpr ⟨hx, hbad⟩⟩)

omit [DecidableEq V] in
theorem chooseHeavy_some (w : V → ℝ) (c D : ℝ) (X : Finset V) (x : V)
    (hsome : chooseHeavy G w c D X = some x) :
    x ∈ X ∧ (mass w X + c) / D < mass w (neighborsIn G X x) := by
  classical
  unfold chooseHeavy at hsome
  dsimp only at hsome
  split at hsome
  · rename_i hbad
    injection hsome with hmin
    rw [← hmin]
    exact Finset.mem_filter.mp (Finset.min'_mem _ hbad)
  · contradiction

/-- A bound on the number of recorded vertices from the multiplicative
potential estimate. -/
theorem records_le_of_potential {D η W M Y : ℝ} {k : ℕ}
    (hD : 1 < D) (hη : 0 < η) (hW : 0 < W) (hM : M ≤ W) (hY : 0 ≤ Y)
    (hpot : Y + η * W ≤ (1 - 1 / D) ^ k * (M + η * W)) :
    k ≤ ⌈D * Real.log (1 + 1 / η)⌉₊ := by
  have hDpos : 0 < D := by linarith
  have hfactor : 0 ≤ 1 - 1 / D := sub_nonneg.mpr ((div_le_one hDpos).mpr hD.le)
  have hexp : 1 - 1 / D ≤ Real.exp (-(1 / D)) := by
    linarith [Real.add_one_le_exp (-(1 / D))]
  have hcap : (1 - 1 / D) ^ k * (M + η * W) ≤
      Real.exp (-((k : ℝ) / D)) * ((1 + η) * W) := by
    have hp := pow_le_pow_left₀ hfactor hexp k
    rw [← Real.exp_nat_mul] at hp
    rw [show (k : ℝ) * -(1 / D) = -((k : ℝ) / D) by ring] at hp
    calc
      _ ≤ (1 - 1 / D) ^ k * ((1 + η) * W) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hfactor _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hp (by positivity)
  have hc : η * W ≤ Real.exp (-((k : ℝ) / D)) * ((1 + η) * W) :=
    (le_add_of_nonneg_left hY).trans (hpot.trans hcap)
  have hr := mul_le_mul_of_nonneg_left hc (Real.exp_pos ((k : ℝ) / D)).le
  have hinv : Real.exp ((k : ℝ) / D) * Real.exp (-((k : ℝ) / D)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [← mul_assoc (Real.exp ((k : ℝ) / D)) (Real.exp (-((k : ℝ) / D))),
    hinv, one_mul] at hr
  have he : Real.exp ((k : ℝ) / D) ≤ 1 + 1 / η := by
    have hh := (le_div_iff₀ (mul_pos hη hW)).mpr (by simpa [mul_assoc] using hr)
    have heq : ((1 + η) * W) / (η * W) = 1 + 1 / η := by
      field_simp
      ring
    simpa only [heq] using hh
  have hlog := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hlog
  have hreal := (div_le_iff₀ hDpos).mp hlog
  rw [mul_comm D]
  exact_mod_cast hreal.trans (Nat.le_ceil _)

/-- Weighted recording lemma. The set returned by the procedure contains
the prescribed independent set, obeys the degree bound, and is determined
by the bounded set of records and the fixed order. -/
theorem weighted_recording (w : V → ℝ) (hw : ∀ x, 0 ≤ w x)
    (A Q : Finset V) (hQA : Q ⊆ A) (hQ : Gᶜ.IsClique (Q : Set V))
    (D η W : ℝ) (hD : 1 < D) (hη : 0 < η) (hW : mass w A ≤ W) :
    ∃ R : Finset V, R ⊆ Q ∧ R.card ≤ ⌈D * Real.log (1 + 1 / η)⌉₊ ∧
      let F := R ∪ recordRemainder G (chooseHeavy G w (η * W) D) R A.card A
      Q ⊆ F ∧ F ⊆ A ∧
        ∀ x ∈ F, mass w (neighborsIn G F x) ≤ (mass w F + η * W) / D := by
  classical
  have hW0 : 0 ≤ W := (Finset.sum_nonneg fun x _ => hw x).trans hW
  by_cases hWzero : W = 0
  · have hgood (x : V) (hx : x ∈ A) :
        mass w (neighborsIn G A x) ≤ (mass w A + η * W) / D := by
      have hzero : mass w A = 0 := le_antisymm (hW.trans_eq hWzero)
        (Finset.sum_nonneg fun x _ => hw x)
      simp only [hzero, hWzero, mul_zero, zero_add, zero_div]
      exact (mass_mono hw (Finset.filter_subset _ _)).trans_eq hzero
    have hchoose : chooseHeavy G w (η * W) D A = none := by
      cases hc : chooseHeavy G w (η * W) D A with
      | none => rfl
      | some x =>
        have hh := chooseHeavy_some G w (η * W) D A x hc
        exact (not_lt_of_ge (hgood x hh.1) hh.2).elim
    have hrem : recordRemainder G (chooseHeavy G w (η * W) D) ∅ A.card A = A := by
      cases hc : A.card with
      | zero => rfl
      | succ n => simp [recordRemainder, hchoose]
    refine ⟨∅, Finset.empty_subset _, Nat.zero_le _, ?_⟩
    simpa [hrem] using And.intro hQA (And.intro (Finset.Subset.refl A) hgood)
  · obtain ⟨R, Y, hR, hY, hdisj, hcover, hcross, hdeg, hpot, hrec⟩ :=
      recording_core G w hw (η * W) D hD Q hQ (chooseHeavy G w (η * W) D)
        (chooseHeavy_none G w (η * W) D) (chooseHeavy_some G w (η * W) D) A.card A le_rfl
    have hrestore : recordRemainder G (chooseHeavy G w (η * W) D) R A.card A = Y := by
      simpa using hrec ∅ (by simp : Disjoint (∅ : Finset V) A)
    refine ⟨R, hR.trans Finset.inter_subset_left, ?_, ?_⟩
    · exact records_le_of_potential hD hη (lt_of_le_of_ne hW0 (Ne.symm hWzero)) hW
        (Finset.sum_nonneg fun x _ => hw x) hpot
    · rw [hrestore]
      refine ⟨by simpa [Finset.inter_eq_left.mpr hQA] using hcover,
        Finset.union_subset (hR.trans Finset.inter_subset_right) hY, ?_⟩
      intro x hx
      have hcross' (u : V) (hu : u ∈ R) (v : V) (hv : v ∈ R ∪ Y) : ¬ G.Adj u v := by
        rcases Finset.mem_union.mp hv with hv | hv
        · by_cases h : u = v
          · subst v
            exact G.irrefl
          · exact ((SimpleGraph.compl_adj G u v).mp
              (hQ (Finset.mem_inter.mp (hR hu)).1 (Finset.mem_inter.mp (hR hv)).1 h)).2
        · exact hcross _ hu _ hv
      rcases Finset.mem_union.mp hx with hxR | hxY
      · have hempty : neighborsIn G (R ∪ Y) x = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact hcross' x hxR y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
        rw [hempty, mass, Finset.sum_empty]
        exact div_nonneg (add_nonneg (Finset.sum_nonneg fun y _ => hw y)
          (mul_nonneg hη.le hW0)) (by linarith)
      · have hsubset : neighborsIn G (R ∪ Y) x ⊆ neighborsIn G Y x := by
          intro y hy
          obtain ⟨hy, hadj⟩ := Finset.mem_filter.mp hy
          rcases Finset.mem_union.mp hy with hy | hy
          · exact (hcross y hy x hxY hadj.symm).elim
          · exact Finset.mem_filter.mpr ⟨hy, hadj⟩
        exact (mass_mono hw hsubset).trans ((hdeg x hxY).trans (div_le_div_of_nonneg_right
          (add_le_add_left (mass_mono hw Finset.subset_union_right) _) (by linarith)))

end FixedOrder

end LocallyRamsey
