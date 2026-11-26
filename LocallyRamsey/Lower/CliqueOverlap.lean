module

public import LocallyRamsey.Lower.Recording
public import LocallyRamsey.Lower.DeferredDraws
public import LocallyRamsey.Lower.OverlapAssembly

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V : Type*} [DecidableEq V]

/-- When a draw uses a kept group, the chance it meets (C) is bounded
using the group's vertex marginals. Averaging this bound uses exactly the
weight on (C) in the lower overlap estimate. -/
theorem kept_draw_hit_le {J Ω : Type*} [Fintype J] [Fintype Ω]
    (π : FiniteLaw J) (μ : J → FiniteLaw Ω) (S : J → Ω → Finset V)
    (w : J → V → ℝ) {K : ℝ} (C : Finset V)
    (hmarginal : ∀ j x, x ∈ C → (μ j).event (fun ω => x ∈ S j ω) ≤ K * w j x) :
    (π.staged μ).event (fun p => ¬ Disjoint C (S p.1 p.2)) ≤
      K * π.mean (fun j => mass (w j) C) := by
  classical
  rw [FiniteLaw.staged_event, ← π.mean_mul_const]
  apply π.mean_mono
  intro j
  have hsub : ∀ ω, ¬Disjoint C (S j ω) → ∃ x : ↥C, x.val ∈ S j ω := by
    intro ω h
    obtain ⟨x, hxC, hxS⟩ := Finset.not_disjoint_iff.mp h
    exact ⟨⟨x, hxC⟩, hxS⟩
  refine ((μ j).event_mono hsub).trans (((μ j).event_exists_le_sum (fun (x : ↥C) ω =>
    x.val ∈ S j ω)).trans ?_)
  calc
    _ ≤ ∑ x : ↥C, K * w j x.val := Finset.sum_le_sum (fun x _ => hmarginal j x.val x.property)
    _ = _ := by rw [Finset.sum_coe_sort C (fun x : V => K * w j x), ← Finset.mul_sum, mass]

/-- Reveal the draws named by each description. If the reconstructed set
has mass less than (g), the other draws cannot hit it many times except
on the stated exceptional event. -/
theorem event_low_mass_description_le {J Ω : Type*} [Fintype J] [Fintype Ω]
    (μ : FiniteLaw Ω) (l : ℕ) (A : J → Finset (Fin l))
    (C : (j : J) → ({i // i ∈ A j} → Ω) → Finset V)
    (w : (j : J) → ({i // i ∈ A j} → Ω) → V → ℝ)
    (valid : (j : J) → ({i // i ∈ A j} → Ω) → Prop)
    (draw : (j : J) → ({i // i ∈ A j} → Ω) → Ω → Finset V)
    {K g target : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g)
    (hhit : ∀ j e, valid j e →
      μ.event (fun d => ¬ Disjoint (C j e) (draw j e d)) ≤ K * mass (w j e) (C j e)) :
    (FiniteLaw.product (fun _ : Fin l => μ)).event (fun ω =>
      ∃ j, valid j (fun i => ω i.val) ∧
        mass (w j (fun i => ω i.val)) (C j (fun i => ω i.val)) < g ∧
        target ≤ ∑ i : {i // i ∉ A j}, (if ¬Disjoint (C j (fun k => ω k.val))
          (draw j (fun k => ω k.val) (ω i.val)) then (1 : ℝ) else 0)) ≤
      (Fintype.card J : ℝ) * Real.exp ((l : ℝ) * (K * g) - Real.log 2 * target) := by
  classical
  let enabled (j : J) (e : {i // i ∈ A j} → Ω) :=
    valid j e ∧ mass (w j e) (C j e) < g
  let X (j : J) (e : {i // i ∈ A j} → Ω) (_ : {i // i ∉ A j}) (s : Ω) : ℝ :=
    if ¬Disjoint (C j e) (draw j e s) then 1 else 0
  refine (FiniteLaw.product (fun _ : Fin l => μ)).event_mono (fun ω h => ?_) |>.trans
    (FiniteLaw.event_exists_deferred_test_le (fun _ : Fin l => μ) A enabled X
      (fun j e i s => by dsimp [X]; split <;> norm_num) ((l : ℝ) * (K * g)) target ?_)
  · obtain ⟨j, hv, hmass, hcount⟩ := h
    exact ⟨j, ⟨hv, hmass⟩, hcount⟩
  · intro j e hj
    have hterm (i : {i // i ∉ A j}) : μ.mean (X j e i) ≤ K * g := by
      change μ.mean (fun d => if ¬Disjoint (C j e) (draw j e d) then 1 else 0) ≤ _
      rw [μ.mean_indicator]
      exact (hhit j e hj.1).trans (mul_le_mul_of_nonneg_left hj.2.le hK)
    have hcard : (Fintype.card {i // i ∉ A j} : ℝ) ≤ l := by
      exact_mod_cast (Fintype.card_le_of_injective (fun i : {i // i ∉ A j} => i.val)
        Subtype.val_injective).trans_eq (Fintype.card_fin l)
    calc
      _ ≤ ∑ _i : {i // i ∉ A j}, K * g := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Fintype.card {i // i ∉ A j} : ℝ) * (K * g) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (mul_nonneg hK hg)

/-- A discovered clique is contained in a recorded set of small weighted
nondegree. Once its weight is at least (g), the loss at the counted
positions gives the lower overlap estimate. -/
theorem exists_recorded_clique_overlap {Ω : Type*} [Fintype Ω] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (μ : FiniteLaw Ω) (q : ℕ) (hq : 0 < q)
    (B Q : Finset V) (hQB : Q ⊆ B) (hQ : G.IsClique (Q : Set V))
    (w : Ω → V → ℝ) (hw : ∀ ω x, 0 ≤ w ω x)
    (weightCap γ g η D : ℝ) (hη : 0 < η) (hD : 1 < D) (hγ : 0 ≤ γ)
    (hγg : 9 * γ ≤ g) (hηg : η * weightCap ≤ g)
    (hB : μ.mean (fun ω => mass (w ω) B) ≤ weightCap)
    (bad : Ω → Finset V) (retained : Ω → Fin q → Finset V)
    (hbad : μ.mean (fun ω => mass (w ω) (bad ω)) ≤ γ)
    (hpositions : ∀ ω x, x ∈ B → x ∉ bad ω →
      γ / 8 * (q : ℝ) ≤ ((Finset.univ.filter (fun i => x ∈ retained ω i)).card : ℝ))
    (hrecord_mass : ∀ R : Finset V, R ⊆ Q →
      R.card ≤ ⌈D * Real.log (1 + 1 / η)⌉₊ →
      let vtx := fun x => μ.mean (fun ω => w ω x)
      let C := R ∪ recordRemainder Gᶜ (chooseHeavy Gᶜ vtx (η * weightCap) D) R B.card B
      Q ⊆ C → C ⊆ B → g ≤ mass vtx C) :
    ∃ C : Finset V, Q ⊆ C ∧ C ⊆ B ∧
      let v := μ.mean (fun ω => mass (w ω) C)
      g ≤ v ∧
      (∀ x ∈ C, μ.mean (fun ω => mass (w ω) (nonNeighbors G C x)) ≤ 2 * v / D) ∧
      γ * v / 9 ≤ μ.mean (fun ω => (∑ i, mass (w ω) (C ∩ retained ω i)) / q) := by
  classical
  let t (x : V) := μ.mean (fun ω => w ω x)
  have ht (x : V) : 0 ≤ t x := μ.mean_nonneg (fun ω => hw ω x)
  have hmean (U : Finset V) : μ.mean (fun ω => mass (w ω) U) = mass t U := by
    simp only [mass, μ.mean_sum, t]
  obtain ⟨R, hRQ, hRcard, hcontain, hsub, hdeg⟩ :=
    weighted_recording Gᶜ t ht B Q hQB (by simpa using hQ)
      D η weightCap hD hη (by simpa only [hmean B] using hB)
  let C := R ∪ recordRemainder Gᶜ (chooseHeavy Gᶜ t (η * weightCap) D) R B.card B
  let v := mass t C
  have hv : g ≤ v := hrecord_mass R hRQ hRcard hcontain hsub
  refine ⟨C, hcontain, hsub, ?_⟩
  simp only [hmean]
  refine ⟨hv, ?_, ?_⟩
  · intro x hx
    have heq : nonNeighbors G C x = neighborsIn Gᶜ C x := by
      ext y
      simp only [nonNeighbors, neighborsIn, Finset.mem_filter, SimpleGraph.compl_adj, not_or]
    rw [heq]
    have hh : v + η * weightCap ≤ 2 * v := by linarith only [hηg, hv]
    exact (hdeg x hx).trans (div_le_div_of_nonneg_right hh (by linarith))
  · have hl := mean_retained_positions_ge μ q hq w hw C bad retained
      (div_nonneg hγ (by norm_num : (0 : ℝ) ≤ 8))
      (fun ω x hx hx' => hpositions ω x (hsub hx) hx')
    rw [hmean] at hl
    have hfactor : v / 9 ≤ (v - μ.mean (fun ω => mass (w ω) (bad ω))) / 8 := by
      linarith only [hγg, hv, hbad]
    have hγmul := mul_le_mul_of_nonneg_left hfactor hγ
    exact (show γ * v / 9 ≤ γ / 8 * (v - μ.mean (fun ω => mass (w ω) (bad ω))) by
      linarith only [hγmul]).trans hl

end LocallyRamsey
