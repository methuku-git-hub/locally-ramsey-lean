module

public import LocallyRamsey.Lower.RetentionEvents
public import LocallyRamsey.Lower.LocationRecords

public section

open scoped BigOperators Classical

namespace LocallyRamsey

open RetainedGroups

variable {V I Ω X T F : Type*} [Fintype V] [LinearOrder V]
  [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype X] [Fintype T] [Fintype F]
variable {q h N b s r region : ℕ} [Nonempty (PositionGroup I q)]

/-- The finite probability space for the final overlap argument. The
retention choices are sampled in a table with one row for each possible
region. A fixed description uses only the row for the region it
determines. -/
structure LowerExperiment (V I Ω X T F : Type*) (q h N b s r region : ℕ)
    [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype X] [Fintype T] [Fintype F] where
  G : SimpleGraph V
  W : Finset V
  samples : FiniteLaw Ω
  list : FiniteLaw X
  drawLaw : (I → Ω) → X → PositionGroup I q → FiniteLaw T
  draw : (I → Ω) → X → PositionGroup I q × T → Finset V
  fallback : V
  sampleDefault : Ω
  aux : Finset V → Ω → FiniteLaw F
  frequency : ℝ
  factor : Ω → V → ℝ
  singleFactor : Ω → ℝ
  good : (Fin q → Ω) → Prop
  retained : Finset V → Ω × F → Finset V
  blocks : (i : I) → Fin h → Finset ↥((Finset.univ : Finset I).erase i)

namespace LowerExperiment

abbrev BaseOutcome (I Ω X T : Type*) [Fintype I] [DecidableEq I] (q N : ℕ) :=
  (I → Ω) × (X × (Fin N → PositionGroup I q × T))

abbrev FullOutcome (V I Ω X T F : Type*) [Fintype I] [DecidableEq I] (q N : ℕ) :=
  BaseOutcome I Ω X T q N × (Finset V → I → F)

variable (e : LowerExperiment V I Ω X T F q h N b s r region)

@[expose] noncomputable def baseLaw : FiniteLaw (BaseOutcome I Ω X T q N) :=
  (FiniteLaw.product (fun _ : I => e.samples)).staged (fun w => e.list.staged (fun x =>
    FiniteLaw.product (fun _ : Fin N => (FiniteLaw.uniform (PositionGroup I q)).staged (e.drawLaw w x))))

@[expose] noncomputable def fullLaw : FiniteLaw (FullOutcome V I Ω X T F q N) :=
  e.baseLaw.staged (fun w => FiniteLaw.regionTable e.aux w.1)

@[expose] noncomputable def decode (ω : I → Ω) (x : X) (d : RecordDescription N b s)
    (t : ↥(namedDraws d) → PositionGroup I q × T) : Finset V :=
  commonRegion e.G e.W (decodeRecordDescription d
    (fun w => enumerateDraw b e.fallback (e.draw ω x w)) t) region

@[expose] noncomputable def tests (B : Finset V) (exposed : Finset I) : Tests V I (Ω × F) q h :=
  ⟨e.G, B, exposed, fun s => e.factor s.1, e.retained B, fun s => e.singleFactor s.1,
    fun w => e.good (Prod.fst ∘ w), e.frequency, e.blocks⟩

@[expose] noncomputable def testsOf (d : RecordDescription N b s)
    (w : BaseOutcome I Ω X T q N) : Tests V I (Ω × F) q h :=
  e.tests (e.decode w.1 w.2.1 d (fun i => w.2.2 i.val))
    (describedPositions d (fun i => (w.2.2 i.val).1.val))

@[expose] def located (cost : ℕ) (w : BaseOutcome I Ω X T q N) : Prop :=
  ∃ (f : Fin s → Fin N) (v : Fin s → V) (Q : Finset V),
    (∀ j, v j ∈ e.draw w.1 w.2.1 (w.2.2 (f j))) ∧
    let B := commonRegion e.G e.W (Finset.univ.image v) region
    B ⊆ e.W ∧ B.card = region ∧ Q ⊆ B ∧ e.G.IsClique (Q : Set V) ∧ r ≤ Q.card + cost ∧
    ∀ x ∈ Q, ∃ i, x ∈ e.draw w.1 w.2.1 (w.2.2 i) ∧
      ∀ j, Disjoint (w.2.2 (f j)).1.val (w.2.2 i).1.val

@[expose] noncomputable def validRegion (B : Finset V) : Prop := B ⊆ e.W ∧ B.card = region

theorem decoded_subset (ω : I → Ω) (x : X) (d : RecordDescription N b s)
    (t : ↥(namedDraws d) → PositionGroup I q × T) : e.decode ω x d t ⊆ e.W := by
  unfold decode commonRegion
  split
  · rename_i hh
    exact (Classical.choose_spec (exists_region_enlarging_common _ _ hh.1 hh.2)).1
  · exact Finset.empty_subset _

@[expose] def badRetention [DecidableRel e.G.Adj]
    (d : RecordDescription N b s) (w : FullOutcome V I Ω X T F q N) : Prop :=
  let u := e.testsOf d w.1
  e.validRegion u.region ∧ u.badEvent N (fun i => (w.1.1 i, w.2 u.region i))
    (fun i : {i // i ∉ namedDraws d} => (w.1.2.2 i.val).1)

/-- The simultaneous retention tests use a union bound over fixed
descriptions. The actual graph and the retained sets used in each
test may depend on the decoded region. -/
theorem event_badRetention_le [DecidableRel e.G.Adj]
    (hLaw : ∀ u v x j, (∀ i ∈ j.val, u i = v i) → e.drawLaw u x j = e.drawLaw v x j)
    (hDraw : ∀ u v x (j : PositionGroup I q) t, (∀ i ∈ j.val, u i = v i) →
      e.draw u x (j, t) = e.draw v x (j, t))
    (default : F) {err : ℝ} (herr : 0 ≤ err)
    (hTest : ∀ (B : Finset V) (exposed : Finset I) (d : RecordDescription N b s),
      e.validRegion B →
      let t := e.tests B exposed
      let μ := e.samples.staged (e.aux B)
      ((FiniteLaw.uniform (PositionGroup I q) |> fun σ =>
          (FiniteLaw.product (fun _ : {j // j ∉ namedDraws d} => σ)).staged (fun _ =>
            FiniteLaw.product (fun _ : I => μ)))).event
        (fun z => t.badEvent N z.2 z.1) ≤ err) :
    e.fullLaw.event (fun w => ∃ d, e.badRetention d w) ≤
      Fintype.card (RecordDescription N b s) * err := by
  classical
  refine (e.fullLaw.event_exists_le_sum (fun d w => e.badRetention d w)).trans ?_
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_le_sum (fun d _ => ?_)
  let A := namedDraws d
  let active (g : ↥A → PositionGroup I q) := describedPositions d (fun j => (g j).val)
  let decode (x : X) (g : ↥A → PositionGroup I q) (S : ↥(active g) → Ω) (t : ↥A → T) :=
    e.decode (FiniteLaw.fillPositions (active g) S (fun _ => e.sampleDefault)) x d (fun j => (g j, t j))
  let P (x : X) (ω : I → Ω) (g : ↥A → PositionGroup I q) (t : ↥A → T)
      (fresh : {j // j ∉ A} → PositionGroup I q) (f : I → F) :=
    let B := e.decode ω x d (fun j => (g j, t j))
    e.validRegion B ∧ (e.tests B (active g)).badEvent N (fun i => (ω i, f i)) fresh
  have hDecode (x : X) (g : ↥A → PositionGroup I q) (t : ↥A → T) (ω : I → Ω) :
      decode x g (fun i => ω i.val) t = e.decode ω x d (fun j => (g j, t j)) := by
    unfold decode LowerExperiment.decode
    congr 1
    unfold decodeRecordDescription
    congr 1
    funext j
    congr 1
    funext k
    apply congrArg (fun P => enumerateDraw b e.fallback P k)
    apply hDraw
    intro i hi
    exact dif_pos (subset_describedPositions d (fun j => (g j).val) j hi)
  have hb := FiniteLaw.event_fixed_description_le e.samples e.list
    (FiniteLaw.uniform (PositionGroup I q)) e.drawLaw Subtype.val hLaw A active
    (fun g j => subset_describedPositions d (fun j => (g j).val) j) decode e.aux P e.sampleDefault
    (err := err) ?_
  · refine le_trans ?_ hb
    apply FiniteLaw.event_mono
    intro w hw
    unfold badRetention testsOf at hw
    simp only [P, hDecode]
    exact hw
  · intro x g S t
    let B := decode x g S t
    have hr (fr : {i // i ∉ active g} → Ω) :
        e.decode (FiniteLaw.fillPositions (active g) S fr) x d (fun j => (g j, t j)) = B := by
      rw [← hDecode]
      congr 1
      funext i
      simp [FiniteLaw.fillPositions, i.property]
    by_cases hB : e.validRegion B
    · simp only [P, hr, hB, true_and]
      let test (j : {j // j ∉ A} → PositionGroup I q) (u : I → Ω × F) :=
        (e.tests B (active g)).badEvent N u j
      refine (FiniteLaw.event_replacing_exposed_with_fresh (active g) e.samples (e.aux B)
        (FiniteLaw.product (fun _ : {j // j ∉ A} => FiniteLaw.uniform (PositionGroup I q))) test
        (fun j u v huv => (e.tests B (active g)).badEvent_local N u v j huv)
        default S).le.trans ?_
      exact hTest B (active g) d hB
    · have hz (fr : {i // i ∉ active g} → Ω) :
          ((FiniteLaw.product
            (fun _ : {j // j ∉ A} => FiniteLaw.uniform (PositionGroup I q))).staged
              (fun _ => FiniteLaw.product (fun i : I => e.aux B (FiniteLaw.fillPositions (active g) S fr i)))).event
            (fun z => P x (FiniteLaw.fillPositions (active g) S fr) g t z.1 z.2) = 0 := by
          rw [← FiniteLaw.mean_indicator]
          simp [P, hr, hB, FiniteLaw.mean_const]
      refine Eq.trans_le ?_ herr
      rw [← (FiniteLaw.product (fun _ : {i // i ∉ active g} => e.samples)).mean_const 0]
      congr 1
      funext fr
      exact hz fr

/-- In the absence of the retention failures, the located clique stays
large after restricting to kept groups. -/
theorem kept_clique_of_located [DecidableRel e.G.Adj]
    (hq : 0 < q) (cost r' : ℕ)
    (hCost : (r' : ℝ) + cost + 2 * (N : ℝ) * e.frequency ≤ r)
    (hInd : ∀ ω x j, e.Gᶜ.IsClique (e.draw ω x j : Set V))
    (hSize : ∀ ω x j, e.draw ω x j = ∅ ∨ (e.draw ω x j).card = b)
    (hGood : ∀ ω x j, (e.draw ω x j).Nonempty → e.good (ω ∘ groupPosition j.1))
    (w : FullOutcome V I Ω X T F q N) (hloc : e.located cost w.1)
    (hNo : ¬ ∃ d, e.badRetention d w) :
    ∃ d : RecordDescription N b s,
      let t := e.testsOf d w.1
      let u := t.experiment (fun i => (w.1.1 i, w.2 t.region i))
      e.validRegion t.region ∧
      ∃ Q : Finset V, Q ⊆ t.region ∧ e.G.IsClique (Q : Set V) ∧ r' ≤ Q.card ∧
        ∀ x ∈ Q, ∃ j, x ∈ e.draw w.1.1 w.1.2.1 (w.1.2.2 j) ∧ u.kept (w.1.2.2 j).1.val := by
  classical
  obtain ⟨f, v, Q, hv, hB, hBc, hQB, hQcl, hQsize, hQ⟩ := hloc
  let P := e.draw w.1.1 w.1.2.1
  let enum (z : PositionGroup I q × T) := enumerateDraw b e.fallback (P z)
  have hEnum (z : PositionGroup I q × T) (x : V) (hx : x ∈ P z) : ∃ i, enum z i = x := by
    rcases hSize w.1.1 w.1.2.1 z with h | h
    · exact False.elim (by simpa [P, h] using hx)
    · exact exists_enumerateDraw_of_mem e.fallback h hx
  obtain ⟨d, he, hdisj⟩ := recode_located_clique enum w.1.2.2 P
    (fun w => w.1.val) hEnum f v hv
  let t := e.testsOf d w.1
  let a (i : I) := (w.1.1 i, w.2 t.region i)
  let u := t.experiment a
  have hReg : t.region = commonRegion e.G e.W (Finset.univ.image v) region := by
    unfold t testsOf tests decode
    change commonRegion e.G e.W (decodeRecordDescription d enum _) region = _
    rw [he]
  have hvReg : e.validRegion t.region := by rw [hReg]; exact ⟨hB, hBc⟩
  have hFresh : ¬ t.badEvent N a
      (fun j : {j // j ∉ namedDraws d} => (w.1.2.2 j.val).1) :=
    fun h => hNo ⟨d, hvReg, h⟩
  have hN (j : Fin N) : (w.1.2.2 j).1.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [(Finset.mem_powersetCard.mp (w.1.2.2 j).1.property).2]
    exact hq
  let rejected := (Finset.univ : Finset (Fin N)).filter (fun j => t.reject a (w.1.2.2 j).1)
  have hreject (j : Fin N) (hj : j ∈ rejected) : j ∉ namedDraws d := by
    intro hn
    have hd := (Finset.mem_filter.mp hj).2.1
    obtain ⟨i, hi⟩ := hN j
    exact Finset.disjoint_left.mp hd
      (subset_describedPositions d (fun j => (w.1.2.2 j.val).1.val) ⟨j, hn⟩ hi) hi
  have hCard : (rejected.card : ℝ) ≤ 2 * (N : ℝ) * e.frequency := by
    let R := (Finset.univ : Finset {j // j ∉ namedDraws d}).filter
      (fun j => t.reject a (w.1.2.2 j.val).1)
    let f (i : ↥rejected) : ↥R :=
      ⟨⟨i.val, hreject i.val i.property⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp i.property).2⟩⟩
    have hinj : Function.Injective f := fun i j heq => Subtype.ext
      (congrArg (fun k : ↥R => k.val.val) heq)
    have hc := Fintype.card_le_of_injective f hinj
    rw [Fintype.card_coe, Fintype.card_coe] at hc
    refine (show (rejected.card : ℝ) ≤ R.card by exact_mod_cast hc).trans ?_
    rw [show (R.card : ℝ) = ∑ j : {j // j ∉ namedDraws d},
        if t.reject a (w.1.2.2 j.val).1 then (1 : ℝ) else 0 by
      rw [← Finset.sum_filter]
      simp [R]]
    exact le_of_not_gt (fun h => hFresh (Or.inl h))
  let assign (x : ↥Q) := Classical.choose (hQ x.val x.property)
  have has (x : ↥Q) := Classical.choose_spec (hQ x.val x.property)
  obtain ⟨Q', hQQ, hcl, hCard', hRet⟩ := clique_after_rejecting_draws Q hQcl
    (fun j => P (w.1.2.2 j)) (fun j => hInd w.1.1 w.1.2.1 _) rejected assign (fun x => (has x).1)
  refine ⟨d, hvReg, Q', hQQ.trans (hReg.symm ▸ hQB), hcl, ?_, ?_⟩
  · have H₁ : (r : ℝ) ≤ Q.card + cost := by exact_mod_cast hQsize
    have H₂ : (Q.card : ℝ) ≤ Q'.card + rejected.card := by exact_mod_cast hCard'
    exact_mod_cast (show (r' : ℝ) ≤ Q'.card by linarith only [hCost, H₁, H₂, hCard])
  · intro x hx
    let y : ↥Q := ⟨x, hQQ hx⟩
    let j := assign y
    have hmem := (has y).1
    have hAvoid := hdisj (w.1.2.2 j) (has y).2
    have hGood' : u.good (w.1.2.2 j).1.val := (isGood_group _ _ _).mpr
      (hGood w.1.1 w.1.2.1 (w.1.2.2 j) ⟨x, hmem⟩)
    have hnot : j ∉ rejected := hRet y hx
    exact ⟨j, hmem, hAvoid, hGood', le_of_not_gt
      (fun hh => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAvoid, hGood', hh⟩))⟩

/-- The set sought in the lower-overlap argument, expressed using the
same weights as the upper-overlap argument. -/
@[expose] def lowerOverlap (u : RetainedGroups V I (Ω × F)) (G : SimpleGraph V) [DecidableRel G.Adj]
    {D g : ℝ} (C : Finset V) : Prop :=
  let σ := FiniteLaw.uniform (PositionGroup I q)
  let v := σ.mean (fun j => mass (u.weight j.val) C)
  C ⊆ u.region ∧ g ≤ v ∧
    (∀ x ∈ C, σ.mean (fun j => mass (u.weight j.val) (nonNeighbors G C x)) ≤ 2 * v / D) ∧
    u.quota * v / 9 ≤ σ.mean (fun j => (∑ i, mass (u.weight j.val) (C ∩ u.survivors j i)) / q)

/-- Conditional on the samples, the list, and the auxiliary table, the
further records can still be counted by exposing their draws only.
Consequently it is unlikely that a kept clique exists without a set
witnessing the lower-overlap bound. -/
theorem event_missing_lower_overlap_le [DecidableRel e.G.Adj] [DecidableRel e.Gᶜ.Adj]
    (hq : 0 < q) {H r' : ℕ} {g η D K : ℝ}
    (hη : 0 < η) (hD : 1 < D) (hγ : 0 ≤ e.frequency) (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hγg : 9 * e.frequency ≤ g) (hηg : 8 * η ≤ g)
    (hH : ⌈D * Real.log (1 + 1 / η)⌉₊ ≤ H)
    (hL : ∀ ω x, 0 ≤ e.factor ω x)
    (hInd : ∀ ω x j, e.Gᶜ.IsClique (e.draw ω x j : Set V))
    (hSize : ∀ ω x j, e.draw ω x j = ∅ ∨ (e.draw ω x j).card = b)
    (hMarg : ∀ (w : I → Ω) (x : X) (J : PositionGroup I q) (B : Finset V) (y : V),
      e.validRegion B → e.good (w ∘ groupPosition J) →
      (e.drawLaw w x J).event (fun z => y ∈ e.draw w x (J, z)) ≤
        K * ((∏ i ∈ J.val, e.factor (w i) y) / B.card)) :
    e.fullLaw.event (fun w => ∃ d : RecordDescription N b s,
      let t := e.testsOf d w.1
      let u := t.experiment (fun i => (w.1.1 i, w.2 t.region i))
      e.validRegion t.region ∧ (FiniteLaw.uniform (PositionGroup I q)).mean (t.loss u.outcome) ≤ e.frequency ∧
      (∃ Q : Finset V, Q ⊆ t.region ∧ e.G.IsClique (Q : Set V) ∧ r' ≤ Q.card ∧
        ∀ x ∈ Q, ∃ j, x ∈ e.draw w.1.1 w.1.2.1 (w.1.2.2 j) ∧ u.kept (w.1.2.2 j).1.val) ∧
      ¬ ∃ C, lowerOverlap (q := q) u e.G (g := g) (D := D) C) ≤
      ((Fintype.card (RecordDescription N b s) : ℝ) * ((N * b : ℕ) + 1 : ℕ) ^ H) *
        Real.exp ((N : ℝ) * (K * g) - Real.log 2 * ((r' : ℝ) - s - H)) := by
  classical
  let σ := FiniteLaw.uniform (PositionGroup I q)
  let err := ((Fintype.card (RecordDescription N b s) : ℝ) * ((N * b : ℕ) + 1 : ℕ) ^ H) *
        Real.exp ((N : ℝ) * (K * g) - Real.log 2 * ((r' : ℝ) - s - H))
  let P (w : FullOutcome V I Ω X T F q N) := ∃ d : RecordDescription N b s,
    let t := e.testsOf d w.1
    let u := t.experiment (fun i => (w.1.1 i, w.2 t.region i))
    e.validRegion t.region ∧ σ.mean (t.loss u.outcome) ≤ e.frequency ∧
    (∃ Q : Finset V, Q ⊆ t.region ∧ e.G.IsClique (Q : Set V) ∧ r' ≤ Q.card ∧
      ∀ x ∈ Q, ∃ j, x ∈ e.draw w.1.1 w.1.2.1 (w.1.2.2 j) ∧ u.kept (w.1.2.2 j).1.val) ∧
    ¬ ∃ C, lowerOverlap (q := q) u e.G (g := g) (D := D) C
  change e.fullLaw.event P ≤ err
  rw [fullLaw, FiniteLaw.staged_event, baseLaw, FiniteLaw.staged_mean]
  simp_rw [FiniteLaw.staged_mean]
  have hBound (w : I → Ω) (x : X) (aux : Finset V → I → F) :
      (FiniteLaw.product (fun _ : Fin N => σ.staged (e.drawLaw w x))).event
        (fun z => P ((w, x, z), aux)) ≤ err := by
    let t (d : RecordDescription N b s) (δ : ↥(namedDraws d) → PositionGroup I q × T) :=
      e.tests (e.decode w x d δ) (describedPositions d (fun j => (δ j).1.val))
    let u (d : RecordDescription N b s) (δ : ↥(namedDraws d) → PositionGroup I q × T) :=
      (t d δ).experiment (fun i => (w i, aux (t d δ).region i))
    let data (d : RecordDescription N b s) (δ : ↥(namedDraws d) → PositionGroup I q × T) :=
      (u d δ).overlapData Prod.fst (e.draw w x)
    let valid (d : RecordDescription N b s) (δ : ↥(namedDraws d) → PositionGroup I q × T) :=
      e.validRegion (t d δ).region ∧ σ.mean ((t d δ).loss (u d δ).outcome) ≤ e.frequency
    let enum (z : PositionGroup I q × T) := enumerateDraw b e.fallback (e.draw w x z)
    have hData (d : RecordDescription N b s) (δ : ↥(namedDraws d) → PositionGroup I q × T)
        (hvalid : valid d δ) :
        (∀ j a, 0 ≤ (data d δ).groupWeight j a) ∧
        σ.mean (fun j => mass ((data d δ).groupWeight j) (data d δ).region) ≤ 8 ∧
        σ.mean (fun j => mass ((data d δ).groupWeight j) ((data d δ).badVertices j)) ≤ e.frequency ∧
        (∀ j a, a ∈ (data d δ).region → a ∉ (data d δ).badVertices j →
          e.frequency / 8 * (q : ℝ) ≤
            ((Finset.univ.filter (fun i => a ∈ (data d δ).retained j i)).card : ℝ)) ∧
        (∀ z, e.Gᶜ.IsClique ((data d δ).keptDraw z : Set V)) ∧
        (∀ z a, a ∈ (data d δ).keptDraw z → ∃ i, enum z i = a) ∧
        (∀ C : Finset V, C ⊆ (data d δ).region →
          (σ.staged (e.drawLaw w x)).event (fun z => ¬ Disjoint C ((data d δ).keptDraw z)) ≤
            K * σ.mean (fun j => mass ((data d δ).groupWeight j) C)) := by
      refine ⟨fun j a => (u d δ).weight_nonneg (fun z a => hL z.1 a) j.val a,
        ?_, hvalid.2, ?_, ?_, ?_, ?_⟩
      · exact (σ.mean_mono (Y := fun _ => (8 : ℝ)) (fun J =>
          (u d δ).mass_weight_le J.val)).trans_eq (σ.mean_const _)
      · intro J a ha hno
        exact le_of_not_gt (fun h => hno (Finset.mem_filter.mpr ⟨ha, h⟩))
      · intro z
        change e.Gᶜ.IsClique ((if (u d δ).kept z.1.val then e.draw w x z else ∅ : Finset V) : Set V)
        split
        · exact hInd w x z
        · simp
      · intro z a ha
        change a ∈ (if (u d δ).kept z.1.val then e.draw w x z else ∅ : Finset V) at ha
        split at ha
        · rcases hSize w x z with hz | hz
          · simp [hz] at ha
          · exact exists_enumerateDraw_of_mem e.fallback hz ha
        · simp at ha
      · intro C hC
        refine (u d δ).kept_draw_hit_le (e.drawLaw w x) (e.draw w x) hK C (fun J y hkeep => ?_)
        exact hMarg w x J (t d δ).region y hvalid.1 ((isGood_group _ _ J).mp hkeep.2.1)
    have h := event_no_lower_overlap_after_location_le e.G σ (σ.staged (e.drawLaw w x))
      (r := r') hq namedDraws namedDraws_card_le data valid enum e.frequency g η D K 8
      hη hD hγ hg hK hγg (by simpa [mul_comm] using hηg) hH hData
    refine le_trans ?_ h
    apply FiniteLaw.event_mono
    intro z hz
    obtain ⟨d, hvalid, hloss, ⟨Q, hQ, hQcl, hQsize, hcover⟩, hno⟩ := hz
    refine ⟨d, ⟨hvalid, hloss⟩, ⟨Q, hQ, hQcl, hQsize, ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨j, hj, hk⟩ := hcover a ha
      have hh : (u d (fun i => z i.val)).kept (z j).1.val := hk
      exact ⟨j, by change a ∈ (if _ then _ else ∅ : Finset V); rw [if_pos hh]; exact hj⟩
    · rintro ⟨C, hC, hv, hnC, hmC⟩
      exact hno ⟨C, hC, hv, hnC, hmC⟩
  refine ((FiniteLaw.product (fun _ : I => e.samples)).mean_mono (Y := fun _ => err) (fun w => ?_)).trans_eq
    (FiniteLaw.mean_const _ _)
  refine (e.list.mean_mono (Y := fun _ => err) (fun x => ?_)).trans_eq (e.list.mean_const err)
  simp_rw [← FiniteLaw.mean_indicator]
  rw [FiniteLaw.mean_mean_comm]
  refine ((FiniteLaw.regionTable e.aux w).mean_mono (Y := fun _ => err) (fun aux => ?_)).trans_eq
    ((FiniteLaw.regionTable e.aux w).mean_const err)
  rw [FiniteLaw.mean_indicator]
  exact hBound w x aux

/-- The final contradiction for the finite experiment. A successful
location and the two probability estimates force incompatible lower
and upper bounds on one retained overlap. -/
theorem impossible [adj : DecidableRel e.G.Adj] [DecidableRel e.Gᶜ.Adj]
    (default : F) (hq : 2 ≤ q) (hh : 0 < h) (hI : Fintype.card I = q * h)
    (hBlockSize : ∀ i : I, 2 * (q - 1) * (q - 1) ≤ ((Finset.univ : Finset I).erase i).card)
    (hblock : ∀ i j, (e.blocks i j).card = q - 1)
    (hdisj : ∀ i, Pairwise (fun j l => Disjoint (e.blocks i j) (e.blocks i l)))
    {cost H r' : ℕ} {g η D K err : ℝ}
    (hη : 0 < η) (hD : 0 < D) (hhD : 1 < (h : ℝ) * D)
    (hγ : 0 < e.frequency) (hg : 0 < g) (hK : 0 ≤ K)
    (hγg : 9 * e.frequency ≤ g) (hηg : 8 * η ≤ g)
    (hH : ⌈(h : ℝ) * D * Real.log (1 + 1 / η)⌉₊ ≤ H)
    (hhγ : (h : ℝ)⁻¹ ≤ e.frequency)
    (hExp : 2 * (s : ℝ) ≤ (h : ℝ) * e.frequency)
    (hsmall : 4 / (D * e.frequency) + 288 * e.frequency / g < 1 / 9)
    (herr : 0 ≤ err)
    (hBudget : (Fintype.card (RecordDescription N b s) : ℝ) * err +
      ((Fintype.card (RecordDescription N b s) : ℝ) * ((N * b : ℕ) + 1 : ℕ) ^ H) *
        Real.exp ((N : ℝ) * (K * g) - Real.log 2 * ((r' : ℝ) - s - H)) < 4 / 5)
    (hCost : (r' : ℝ) + cost + 2 * (N : ℝ) * e.frequency ≤ r)
    (hLoc : 4 / 5 ≤ e.baseLaw.event (e.located cost))
    (hL : ∀ ω x, 0 ≤ e.factor ω x) (hc : ∀ ω, 0 ≤ e.singleFactor ω)
    (hF : ∀ B, e.validRegion B → ∀ ω, e.retained B ω ⊆ B)
    (hz : ∀ B, e.validRegion B → ∀ ω : Ω × F,
      ((e.retained B ω).card : ℝ) * e.singleFactor ω.1 / B.card ≤ 2)
    (hInd : ∀ ω x j, e.Gᶜ.IsClique (e.draw ω x j : Set V))
    (hSize : ∀ ω x j, e.draw ω x j = ∅ ∨ (e.draw ω x j).card = b)
    (hGood : ∀ ω x j, (e.draw ω x j).Nonempty → e.good (ω ∘ groupPosition j.1))
    (hLaw : ∀ u v x j, (∀ i ∈ j.val, u i = v i) → e.drawLaw u x j = e.drawLaw v x j)
    (hDraw : ∀ u v x (j : PositionGroup I q) t, (∀ i ∈ j.val, u i = v i) →
      e.draw u x (j, t) = e.draw v x (j, t))
    (hMarg : ∀ (w : I → Ω) (x : X) (J : PositionGroup I q) (B : Finset V) (y : V),
      e.validRegion B → e.good (w ∘ groupPosition J) →
      (e.drawLaw w x J).event (fun z => y ∈ e.draw w x (J, z)) ≤
        K * ((∏ i ∈ J.val, e.factor (w i) y) / B.card))
    (hTest : ∀ (B : Finset V) (exposed : Finset I) (d : RecordDescription N b s),
      e.validRegion B →
      let t := e.tests B exposed
      let μ := e.samples.staged (e.aux B)
      ((FiniteLaw.product (fun _ : {j // j ∉ namedDraws d} =>
        FiniteLaw.uniform (PositionGroup I q))).staged (fun _ => FiniteLaw.product (fun _ : I => μ))).event
        (fun z => t.badEvent N z.2 z.1) ≤ err) : False := by
  classical
  let σ := FiniteLaw.uniform (PositionGroup I q)
  let retainedBad (w : FullOutcome V I Ω X T F q N) := ∃ d, e.badRetention d w
  let lowerBad (w : FullOutcome V I Ω X T F q N) := ∃ d : RecordDescription N b s,
    let t := e.testsOf d w.1
    let u := t.experiment (fun i => (w.1.1 i, w.2 t.region i))
    e.validRegion t.region ∧ σ.mean (t.loss u.outcome) ≤ e.frequency ∧
    (∃ Q : Finset V, Q ⊆ t.region ∧ e.G.IsClique (Q : Set V) ∧ r' ≤ Q.card ∧
      ∀ x ∈ Q, ∃ j, x ∈ e.draw w.1.1 w.1.2.1 (w.1.2.2 j) ∧ u.kept (w.1.2.2 j).1.val) ∧
    ¬ ∃ C, lowerOverlap (q := q) u e.G (g := g) (D := (h : ℝ) * D) C
  have hRet := e.event_badRetention_le hLaw hDraw default herr hTest
  have hLower := e.event_missing_lower_overlap_le (r' := r') (by omega : 0 < q)
    hη hhD hγ.le hg.le hK hγg hηg hH hL hInd hSize hMarg
  have hLoc' : 4 / 5 ≤ e.fullLaw.event (fun w => e.located cost w.1) := by
    rw [fullLaw, FiniteLaw.staged_event]
    have hInner (w : BaseOutcome I Ω X T q N) :
        (FiniteLaw.regionTable e.aux w.1).event (fun _ => e.located cost w) =
          if e.located cost w then (1 : ℝ) else 0 := by
      rw [← FiniteLaw.mean_indicator, FiniteLaw.mean_const]
    simp_rw [hInner, FiniteLaw.mean_indicator]
    exact hLoc
  have hInc (w : FullOutcome V I Ω X T F q N) (hLoc : e.located cost w.1) :
      retainedBad w ∨ lowerBad w := by
    by_cases hn : retainedBad w
    · exact Or.inl hn
    right
    obtain ⟨d, hReg, Q, hQ, hcl, hs, hCov⟩ :=
      e.kept_clique_of_located (by omega) cost r' hCost hInd hSize hGood w hLoc hn
    let t := e.testsOf d w.1
    let a (i : I) := (w.1.1 i, w.2 t.region i)
    let u := t.experiment a
    have ht : ¬ t.badEvent N a (fun j : {j // j ∉ namedDraws d} => (w.1.2.2 j.val).1) :=
      fun h => hn ⟨d, hReg, h⟩
    have hLoss : σ.mean (t.loss a) ≤ e.frequency := le_of_not_gt (fun h => ht (Or.inr (Or.inl h)))
    have hMark (i : I) : t.markedMass a i ≤ ((h : ℝ)⁻¹) ^ 2 :=
      le_of_not_gt (fun hi => ht (Or.inr (Or.inr (Or.inl ⟨i, hi⟩))))
    have hZm : t.unrevealedMass a ≤ 4 * (Fintype.card I : ℝ) * e.frequency :=
      le_of_not_gt (fun hi => ht (Or.inr (Or.inr (Or.inr hi))))
    have hS : t.exposed.card ≤ s * q := by
      unfold t testsOf tests describedPositions
      refine Finset.card_biUnion_le.trans ?_
      have he (j : ↥(namedDraws d)) : (w.1.2.2 j.val).1.val.card = q :=
        (Finset.mem_powersetCard.mp (w.1.2.2 j.val).1.property).2
      simp only [he, Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
      exact Nat.mul_le_mul_right q (namedDraws_card_le d)
    have hM : (∑ i : I, 16 * (u.positionMass i + e.frequency)) / Fintype.card I ≤ 96 * e.frequency := by
      have hE : ∑ i ∈ t.exposed, u.positionMass i ≤ 2 * (s : ℝ) * q := by
        refine (Finset.sum_le_sum (fun i _ => hz t.region hReg (a i))).trans ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hS' : (t.exposed.card : ℝ) ≤ (s : ℝ) * q := by exact_mod_cast hS
        linarith only [hS']
      have hSum := Finset.sum_sdiff (Finset.subset_univ t.exposed) (f := u.positionMass)
      have hPos : (0 : ℝ) < Fintype.card I := by rw [hI, Nat.cast_mul]; positivity
      have hZsum : ∑ i : I, u.positionMass i ≤ 5 * (Fintype.card I : ℝ) * e.frequency := by
        have he : 2 * (s : ℝ) * q ≤ Fintype.card I * e.frequency := by
          rw [hI, Nat.cast_mul]
          nlinarith only [mul_le_mul_of_nonneg_right hExp (Nat.cast_nonneg q)]
        change (∑ i ∈ Finset.univ \ t.exposed, u.positionMass i) ≤ _ at hZm
        linarith only [hE, hSum, hZm, he]
      rw [div_le_iff₀ hPos, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      nlinarith only [hZsum]
    refine ⟨d, hReg, hLoss, ⟨Q, hQ, hcl, hs, hCov⟩, ?_⟩
    rintro ⟨C, hCB, hv, hNon, hLO⟩
    have hAdjEq : adj = (fun x y => Classical.propDecidable (e.G.Adj x y)) := Subsingleton.elim _ _
    refine @RetainedGroups.overlap_contradiction V I (Ω × F) _ _ _ _ _ u q h e.G adj
      hq hh hI hBlockSize _ e.blocks hblock hdisj
      (hF t.region hReg) (fun w x => hL w.1 x) (fun w => hc w.1)
      D g 96 hγ hD hg (by norm_num) hhγ (by norm_num; exact hsmall)
      hM ?_ C hCB _ hv hNon hLO
    intro i
    rw [hAdjEq]
    exact hMark i

  have hAll := (e.fullLaw.event_mono hInc).trans (e.fullLaw.event_union_le retainedBad lowerBad)
  exact (not_lt_of_ge (hLoc'.trans (hAll.trans (add_le_add hRet hLower)))) hBudget

end LowerExperiment
end LocallyRamsey
