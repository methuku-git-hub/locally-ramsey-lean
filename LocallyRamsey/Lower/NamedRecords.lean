module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

public section

open scoped BigOperators

namespace LocallyRamsey

/-- Each slot is vacant or records a draw and a position within that draw. -/
abbrev RecordDescription (l b H : ℕ) := Fin H → Option (Fin l × Fin b)

variable {l b H : ℕ}

/-- The draws exposed by a description. -/
@[expose] def namedDraws (d : RecordDescription l b H) : Finset (Fin l) :=
  Finset.univ.biUnion (fun j => ((d j).map Prod.fst).toFinset)

theorem namedDraws_card_le (d : RecordDescription l b H) : (namedDraws d).card ≤ H := by
  refine (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin H)))).trans ?_
  calc
    _ ≤ ∑ _j : Fin H, 1 := Finset.sum_le_sum (fun j _ => by cases h : d j <;> simp [h])
    _ = _ := by simp

theorem mem_namedDraws_of_record {d : RecordDescription l b H} {j : Fin H}
    {i : Fin l} {k : Fin b} (h : d j = some (i, k)) : i ∈ namedDraws d :=
  Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, by simp [h]⟩

variable {Ω V : Type*} [DecidableEq V]

/-- Reconstruct from only the draws named in the description. -/
@[expose] noncomputable def decodeRecordDescription (d : RecordDescription l b H)
    (enumerate : Ω → Fin b → V) (draw : {i // i ∈ namedDraws d} → Ω) : Finset V :=
  (namedDraws d).attach.biUnion (fun i =>
    (Finset.univ.filter (fun k => ∃ j, d j = some (i.val, k))).image (enumerate (draw i)))

theorem mem_decodeRecordDescription (d : RecordDescription l b H) (enumerate : Ω → Fin b → V)
    (ω : Fin l → Ω) {x : V} :
    x ∈ decodeRecordDescription d enumerate (fun i => ω i.val) ↔
      ∃ (j : Fin H) (i : Fin l) (k : Fin b), d j = some (i, k) ∧ x = enumerate (ω i) k := by
  classical
  constructor
  · intro hx
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hk).2
    exact ⟨j, i.val, k, hj, he.symm⟩
  · rintro ⟨j, i, k, h, rfl⟩
    let a : {i // i ∈ namedDraws d} := ⟨i, mem_namedDraws_of_record h⟩
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_attach _ _, Finset.mem_image.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, ⟨j, h⟩⟩, rfl⟩⟩

/-- Any set of at most (H) records, each represented by a draw and a
position, has a description of length (H). -/
theorem exists_recordDescription (R : Finset V) (hR : R.card ≤ H)
    (enumerate : Ω → Fin b → V) (ω : Fin l → Ω)
    (hValues : ∀ x ∈ R, ∃ (i : Fin l) (k : Fin b), enumerate (ω i) k = x) :
    ∃ d : RecordDescription l b H,
      decodeRecordDescription d enumerate (fun i => ω i.val) = R := by
  classical
  let e := R.equivFin
  let pair (x : ↥R) : Fin l × Fin b :=
    let i := Classical.choose (hValues x.val x.property)
    (i, Classical.choose (Classical.choose_spec (hValues x.val x.property)))
  have hpair (x : ↥R) : enumerate (ω (pair x).1) (pair x).2 = x.val :=
    Classical.choose_spec (Classical.choose_spec (hValues x.val x.property))
  let d (j : Fin H) :=
    if h : j.val < R.card then some (pair (e.symm ⟨j.val, h⟩)) else none
  refine ⟨d, ?_⟩
  ext x
  rw [mem_decodeRecordDescription]
  constructor
  · rintro ⟨j, i, k, hij, rfl⟩
    by_cases hj : j.val < R.card
    · have hh : pair (e.symm ⟨j.val, hj⟩) = (i, k) := by
        simpa only [d, dite_eq_left hj, Option.some.injEq] using hij
      rw [← show (pair (e.symm ⟨j.val, hj⟩)).1 = i from congrArg Prod.fst hh,
        ← show (pair (e.symm ⟨j.val, hj⟩)).2 = k from congrArg Prod.snd hh, hpair]
      exact (e.symm ⟨j.val, hj⟩).property
    · simp [d, hj] at hij
  · intro hx
    let j := Fin.castLE hR (e ⟨x, hx⟩)
    have hj : j.val < R.card := (e ⟨x, hx⟩).isLt
    have hj' : e.symm ⟨j.val, hj⟩ = ⟨x, hx⟩ := e.symm_apply_apply ⟨x, hx⟩
    exact ⟨j, (pair ⟨x, hx⟩).1, (pair ⟨x, hx⟩).2,
      by simp only [d, dite_eq_left hj, hj'], (hpair ⟨x, hx⟩).symm⟩

end LocallyRamsey
