module

public import LocallyRamsey.Lower.SamplingExperiment
public import LocallyRamsey.Lower.NamedRecords

public section

open scoped BigOperators Classical

namespace LocallyRamsey.FiniteLaw

variable {I J Ω T F R X : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  [Fintype Ω] [Fintype T] [Fintype F] [Fintype R] [DecidableEq R] [Fintype X]

/-- Conditional on the initial samples, the retention table can be drawn
before the groups and within-group draws. Each row has the law for the
corresponding possible region. -/
@[expose] noncomputable def regionTable (ν : R → Ω → FiniteLaw F)
    (z : I → Ω) : FiniteLaw (R → I → F) :=
  product (fun r => product (fun i => ν r (z i)))

/-- Ignore the fictitious entries of an independent product used to fill
positions that were already exposed. -/
theorem event_fillPositions_bound (A : Finset I) (μ : FiniteLaw Ω)
    (P : (I → Ω) → Prop) (hP : ∀ u v, (∀ i, i ∉ A → u i = v i) → (P u ↔ P v))
    (e : {i // i ∈ A} → Ω) :
    (product (fun _ : {i // i ∉ A} => μ)).event
        (fun fr => P (fillPositions A e fr)) =
      (product (fun _ : I => μ)).event P := by
  have he (ω : I → Ω) : P ω ↔ P (fillPositions A e (fun i => ω i.val)) :=
    hP _ _ (fun i hi => by simp [fillPositions, hi])
  let f (i : {i // i ∉ A}) := i.val
  exact (event_injective_projection μ f Subtype.val_injective (fun fr =>
    P (fillPositions A e fr))).symm.trans (le_antisymm
      (event_mono _ (fun ω h => (he ω).mpr h))
      (event_mono _ (fun ω h => (he ω).mp h)))

/-- An event in the larger experiment that depends on only one row of
the auxiliary table can be integrated using just the law of that row. -/
theorem event_regionTable_row (baseLaw : FiniteLaw X) (sample : X → I → Ω)
    (ν : R → Ω → FiniteLaw F) (r : X → R) (P : X → (I → F) → Prop) :
    (baseLaw.staged (fun x => regionTable ν (sample x))).event
      (fun y => P y.1 (y.2 (r y.1))) =
    (baseLaw.staged (fun x => product (fun i => ν (r x) (sample x i)))).event
      (fun y => P y.1 y.2) := by
  simp only [staged_event]
  congr 1
  funext x
  simp only [← mean_indicator]
  exact mean_coordinate (fun b => product (fun i => ν b (sample x i))) (r x)
    (fun a => if P x a then 1 else 0)

/-- For a fixed description, one can expose its group choices and its
within-group draws after exposing only the samples in those groups.
Given this revealed information the other samples are independent.
The other group choices remain uniform. Auxiliary choices at all
positions use the retention law for the region from those records. -/
theorem event_fixed_description {N : ℕ} (π : FiniteLaw Ω) (ξ : FiniteLaw X) (σ : FiniteLaw J)
    (draw : (I → Ω) → X → J → FiniteLaw T)
    (positions : J → Finset I)
    (hdraw : ∀ u v x j, (∀ i ∈ positions j, u i = v i) → draw u x j = draw v x j)
    (A : Finset (Fin N))
    (active : ({j // j ∈ A} → J) → Finset I)
    (hactive : ∀ g j, positions (g j) ⊆ active g)
    (decode : X → (g : {j // j ∈ A} → J) → ({i // i ∈ active g} → Ω) → ({j // j ∈ A} → T) → R)
    (ν : R → Ω → FiniteLaw F)
    (P : X → (I → Ω) → ({j // j ∈ A} → J) → ({j // j ∈ A} → T) →
      ({j // j ∉ A} → J) → (I → F) → Prop)
    (default : Ω) :
    let base := (product (fun _ : I => π)).staged (fun u => ξ.staged (fun x =>
      product (fun _ : Fin N => σ.staged (draw u x))))
    (base.staged (fun z => regionTable ν z.1)).event (fun w =>
      let x := w.1.2.1
      let g (j : {j // j ∈ A}) := (w.1.2.2 j.val).1
      let t (j : {j // j ∈ A}) := (w.1.2.2 j.val).2
      P x w.1.1 g t (fun j => (w.1.2.2 j.val).1) (w.2 (decode x g (fun i => w.1.1 i.val) t))) =
    ξ.mean (fun x =>
      (product (fun _ : {j // j ∈ A} => σ)).mean (fun g =>
        (product (fun _ : {i // i ∈ active g} => π)).mean (fun e =>
          (product (fun j => draw (fillPositions (active g) e (fun _ => default)) x (g j))).mean (fun t =>
            (product (fun _ : {i // i ∉ active g} => π)).mean (fun fr =>
              let u := fillPositions (active g) e fr
              ((product (fun _ : {j // j ∉ A} => σ)).staged (fun _ =>
                product (fun i : I => ν (decode x g e t) (u i)))).event
                  (fun z => P x u g t z.1 z.2)))))) := by
  classical
  intro base
  rw [event_regionTable_row base (fun z => z.1) ν (fun z =>
    decode z.2.1 (fun j => (z.2.2 j.val).1) (fun i => z.1 i.val) (fun j => (z.2.2 j.val).2))
      (fun z y => P z.2.1 z.1 (fun j => (z.2.2 j.val).1) (fun j => (z.2.2 j.val).2)
        (fun j => (z.2.2 j.val).1) y)]
  simp only [staged_event, base, staged_mean]
  let μ := product (fun _ : I => π)
  let σA := product (fun _ : {j // j ∈ A} => σ)
  let σB := product (fun _ : {j // j ∉ A} => σ)
  let Q (x : X) (u : I → Ω) (g : {j // j ∈ A} → J) (t : {j // j ∈ A} → T)
      (v : {j // j ∉ A} → J) :=
    (product (fun i : I => ν (decode x g (fun i => u i.val) t) (u i))).event (fun y => P x u g t v y)
  let H (x : X) (u : I → Ω) :=
    (product (fun _ : Fin N => σ.staged (draw u x))).mean
      (fun w => Q x u (fun j => (w j.val).1) (fun j => (w j.val).2) (fun j => (w j.val).1))
  change μ.mean (fun u => ξ.mean (fun x => H x u)) = _
  rw [mean_mean_comm]
  congr 1
  funext x
  have hH (u : I → Ω) : H x u = σA.mean (fun g => σB.mean (fun v =>
      (product (fun j => draw u x (g j))).mean (fun t => Q x u g t v))) := by
    dsimp only [H]
    rw [mean_split_revealed (fun _ : Fin N => σ.staged (draw u x)) A
      (fun y => Q x u (fun j => (y.1 j).1) (fun j => (y.1 j).2) (fun j => (y.2 j).1))]
    rw [staged_mean]
    simp_rw [mean_product_of_staged]
    change σA.mean (fun g =>
      (product (fun j => draw u x (g j))).mean (fun t => σB.mean (fun v =>
        (product (fun j => draw u x (v j))).mean (fun _ => Q x u g t v)))) = _
    have he (g : {j // j ∈ A} → J) (t : {j // j ∈ A} → T) (v : {j // j ∉ A} → J) :
        (product (fun j => draw u x (v j))).mean (fun _ => Q x u g t v) = Q x u g t v :=
      (product (fun j => draw u x (v j))).mean_const _
    simp_rw [he]
    congr 1
    funext g
    exact mean_mean_comm _ _ _
  simp_rw [hH]
  rw [mean_mean_comm]
  congr 1
  funext g
  let Z (u : I → Ω) := σB.mean (fun v =>
    (product (fun j => draw u x (g j))).mean (fun t => Q x u g t v))
  change μ.mean Z = _
  have hFill (u : I → Ω) : fillPositions (active g) (fun i => u i.val) (fun i => u i.val) = u := by
    funext i
    by_cases hi : i ∈ active g <;> simp [fillPositions, hi]
  have hsplit := mean_split_revealed (fun _ : I => π) (active g)
    (fun y => Z (fillPositions (active g) y.1 y.2))
  simp only [hFill, staged_mean] at hsplit
  rw [hsplit]
  congr 1
  funext e
  let νt := product (fun j => draw (fillPositions (active g) e (fun _ => default)) x (g j))
  have he (fr : {i // i ∉ active g} → Ω) :
      (product (fun j => draw (fillPositions (active g) e fr) x (g j))) = νt := by
    congr 1
    funext j
    apply hdraw
    intro i hi
    simp [fillPositions, hactive g j hi]
  simp only [Z, he]
  simp_rw [σB.mean_mean_comm νt]
  rw [mean_mean_comm]
  congr 1
  funext t
  congr 1
  funext fr
  have he' : (fun i : {i // i ∈ active g} => fillPositions (active g) e fr i.val) = e := by
    funext i
    simp [fillPositions, i.property]
  simp only [Q, he']
  rfl

/-- A conditional probability bound after exposing a fixed description
also holds in the full experiment. -/
theorem event_fixed_description_le {N : ℕ} (π : FiniteLaw Ω) (ξ : FiniteLaw X) (σ : FiniteLaw J)
    (draw : (I → Ω) → X → J → FiniteLaw T)
    (positions : J → Finset I)
    (hdraw : ∀ u v x j, (∀ i ∈ positions j, u i = v i) → draw u x j = draw v x j)
    (A : Finset (Fin N))
    (active : ({j // j ∈ A} → J) → Finset I)
    (hactive : ∀ g j, positions (g j) ⊆ active g)
    (decode : X → (g : {j // j ∈ A} → J) → ({i // i ∈ active g} → Ω) → ({j // j ∈ A} → T) → R)
    (ν : R → Ω → FiniteLaw F)
    (P : X → (I → Ω) → ({j // j ∈ A} → J) → ({j // j ∈ A} → T) →
      ({j // j ∉ A} → J) → (I → F) → Prop)
    (default : Ω) {err : ℝ}
    (hP : ∀ x g e t,
      (product (fun _ : {i // i ∉ active g} => π)).mean (fun fr =>
        let u := fillPositions (active g) e fr
        ((product (fun _ : {j // j ∉ A} => σ)).staged (fun _ =>
          product (fun i : I => ν (decode x g e t) (u i)))).event
            (fun z => P x u g t z.1 z.2)) ≤ err) :
    let base := (product (fun _ : I => π)).staged (fun u => ξ.staged (fun x =>
      product (fun _ : Fin N => σ.staged (draw u x))))
    (base.staged (fun z => regionTable ν z.1)).event (fun w =>
      let x := w.1.2.1
      let g (j : {j // j ∈ A}) := (w.1.2.2 j.val).1
      let t (j : {j // j ∈ A}) := (w.1.2.2 j.val).2
      P x w.1.1 g t (fun j => (w.1.2.2 j.val).1) (w.2 (decode x g (fun i => w.1.1 i.val) t))) ≤ err := by
  intro base
  rw [event_fixed_description π ξ σ draw positions hdraw A active hactive decode ν P default]
  refine (ξ.mean_mono (Y := fun _ => err) (fun x => ?_)).trans_eq (ξ.mean_const err)
  let Jlaw := product (fun _ : {j // j ∈ A} => σ)
  refine (Jlaw.mean_mono (Y := fun _ => err) (fun g => ?_)).trans_eq (Jlaw.mean_const err)
  let Elaw := product (fun _ : {i // i ∈ active g} => π)
  refine (Elaw.mean_mono (Y := fun _ => err) (fun e => ?_)).trans_eq (Elaw.mean_const err)
  let Tlaw := product (fun j => draw (fillPositions (active g) e (fun _ => default)) x (g j))
  exact (Tlaw.mean_mono (hP x g e)).trans_eq (Tlaw.mean_const err)

/-- After a description is fixed, tests that only use the unexposed
positions may be bounded using independent draws at every position.
The entries at exposed positions are fictitious and ignored by the
test. -/
theorem event_replacing_exposed_with_fresh (A : Finset I)
    (μ : FiniteLaw Ω) (ν : Ω → FiniteLaw F) (σ : FiniteLaw J)
    (P : J → (I → Ω × F) → Prop)
    (hP : ∀ j u v, (∀ i, i ∉ A → u i = v i) → (P j u ↔ P j v)) (default : F)
    (e : {i // i ∈ A} → Ω) :
    (product (fun _ : {i // i ∉ A} => μ)).mean (fun fr =>
      let u := fillPositions A e fr
      (σ.staged (fun _ => product (fun i : I => ν (u i)))).event
        (fun z => P z.1 (fun i => (u i, z.2 i)))) =
    (σ.staged (fun _ => product (fun _ : I => μ.staged ν))).event (fun z => P z.1 z.2) := by
  classical
  rw [staged_event]
  simp_rw [staged_event]
  rw [mean_mean_comm]
  congr 1
  funext j
  let g (i : {i // i ∉ A}) := i.val
  let X (w : {i // i ∉ A} → Ω × F) :=
    P j (fillPositions A (fun i => (e i, default)) w)
  have hX (w : I → Ω × F) : P j w ↔ X (w ∘ g) :=
    hP j _ _ (fun i hi => by simp [X, g, fillPositions, hi])
  rw [show (product (fun _ : I => μ.staged ν)).event (P j) =
      (product (fun _ : I => μ.staged ν)).event (fun w => X (w ∘ g)) by
    exact le_antisymm (event_mono _ (fun w h => (hX w).mp h))
      (event_mono _ (fun w h => (hX w).mpr h))]
  rw [event_injective_projection (μ.staged ν) g Subtype.val_injective X,
    event_product_of_staged]
  congr 1
  funext fr
  let u := fillPositions A e fr
  have hEq (w : I → F) : P j (fun i => (u i, w i)) ↔
      X (fun i => (fr i, w (g i))) := by
    apply hP j
    intro i hi
    simp [X, u, g, fillPositions, hi]
  have hc : (product (fun i : I => ν (u i))).event (fun w => P j (fun i => (u i, w i))) =
      (product (fun i : I => ν (u i))).event (fun w => X (fun i => (fr i, w (g i)))) :=
    le_antisymm (event_mono _ (fun w h => (hEq w).mp h)) (event_mono _ (fun w h => (hEq w).mpr h))
  rw [hc]
  let Z (w : {i // i ∉ A} → F) := X (fun i => (fr i, w i))
  have hp : (product (fun i : I => ν (u i))).event (fun w => Z (w ∘ g)) =
      (product (fun i : {i // i ∉ A} => ν (u (g i)))).event Z := by
    rw [← mean_indicator, ← mean_indicator]
    have hs := mean_split_revealed (fun i : I => ν (u i)) A
      (fun y => if Z y.2 then 1 else 0)
    change (product (fun i : I => ν (u i))).mean
      (fun w => if Z (fun i : {i // i ∉ A} => w i.val) then 1 else 0) = _
    rw [hs, staged_mean]
    exact (product (fun i : {i // i ∈ A} => ν (u i.val))).mean_const
      ((product (fun i : {i // i ∉ A} => ν (u (g i)))).mean (fun w => if Z w then 1 else 0))
  refine hp.trans ?_
  have he (i : {i // i ∉ A}) : u (g i) = fr i := by simp [u, g, fillPositions, i.property]
  simp_rw [he]
  rfl

end LocallyRamsey.FiniteLaw
