module

public import LocallyRamsey.Lower.CliqueLocation
public import LocallyRamsey.Lower.NamedRecords

public section

open scoped BigOperators Classical

namespace LocallyRamsey

variable {V I Ω : Type*} [DecidableEq V] [DecidableEq I]
variable {b N s : ℕ}

/-- Enumerate a draw of the prescribed order. Empty draws use a fixed
default value, which is never used to encode a vertex in a draw. -/
@[expose] noncomputable def enumerateDraw (b : ℕ) (default : V) (P : Finset V) (i : Fin b) : V :=
  if h : P.card = b then ((Finset.equivFinOfCardEq h).symm i).val else default

theorem exists_enumerateDraw_of_mem (default : V) {P : Finset V} (hP : P.card = b)
    {x : V} (hx : x ∈ P) : ∃ i : Fin b, enumerateDraw b default P i = x := by
  let e := Finset.equivFinOfCardEq hP
  refine ⟨e ⟨x, hx⟩, ?_⟩
  rw [enumerateDraw, dite_eq_left hP]
  exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)

/-- The union of the groups named by a description. -/
@[expose] def describedPositions (d : RecordDescription N b s)
    (g : {j // j ∈ namedDraws d} → Finset I) : Finset I :=
  (namedDraws d).attach.biUnion g

theorem subset_describedPositions (d : RecordDescription N b s)
    (g : {j // j ∈ namedDraws d} → Finset I) (j : {j // j ∈ namedDraws d}) :
    g j ⊆ describedPositions d g := fun _ h => Finset.mem_biUnion.mpr ⟨j, Finset.mem_attach _ _, h⟩

/-- Recode the vertices found by the location argument as offsets in
their draws. The resulting description exposes exactly the named
groups, so it preserves disjointness for every vertex of the located
clique. -/
theorem recode_located_clique (enumerate : Ω → Fin b → V) (ω : Fin N → Ω)
    (P : Ω → Finset V) (group : Ω → Finset I)
    (hEnum : ∀ w x, x ∈ P w → ∃ i, enumerate w i = x)
    (f : Fin s → Fin N) (v : Fin s → V) (hv : ∀ j, v j ∈ P (ω (f j))) :
    ∃ d : RecordDescription N b s,
      decodeRecordDescription d enumerate (fun i => ω i.val) = Finset.univ.image v ∧
      (∀ w : Ω, (∀ j, Disjoint (group (ω (f j))) (group w)) →
        Disjoint (describedPositions d (fun i => group (ω i.val))) (group w)) := by
  classical
  let k (j : Fin s) := Classical.choose (hEnum (ω (f j)) (v j) (hv j))
  let desc (j : Fin s) : Option (Fin N × Fin b) := some (f j, k j)
  have he (j : Fin s) : enumerate (ω (f j)) (k j) = v j :=
    Classical.choose_spec (hEnum (ω (f j)) (v j) (hv j))
  refine ⟨desc, ?_, ?_⟩
  · ext x
    rw [mem_decodeRecordDescription]
    constructor
    · rintro ⟨j, i, a, h, rfl⟩
      have hm : f j = i ∧ k j = a := by simpa [desc] using h
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [← hm.1, ← hm.2, he]⟩
    · rintro hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨j, f j, k j, rfl, (he j).symm⟩
  · intro w h
    apply Finset.disjoint_left.mpr
    intro i hi hiw
    obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hi
    have hj := j.property
    unfold namedDraws at hj
    obtain ⟨j', _, hj'⟩ := Finset.mem_biUnion.mp hj
    have he' : j.val = f j' := by simpa [desc] using hj'
    exact Finset.disjoint_left.mp (h j') (he' ▸ hij) hiw

end LocallyRamsey
