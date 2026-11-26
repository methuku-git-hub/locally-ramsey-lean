module

public import LocallyRamsey.Lower.RetainedOverlap

public section

open scoped BigOperators Classical

namespace LocallyRamsey.RetainedGroups

variable {V I Ω : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype Ω]

set_option maxHeartbeats 1400000 in
/-- The retained weights of the groups in a partition through one
position. The law of the samples away from the position is still the
independent product after fixing its sample and retained set. -/
theorem event_anchor_marked_gt_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : FiniteLaw Ω) (B : Finset V) (revealed : Finset I) (i : I)
    (L : Ω → V → ℝ) (F : Ω → Finset V) (c : Ω → ℝ)
    (good : (I → Ω) → Finset I → Prop)
    (hlocal : ∀ z z' J, (∀ j ∈ J, z j = z' j) → (good z J ↔ good z' J))
    (hF : ∀ s, F s ⊆ B)
    (hrow : ∀ s x, x ∈ F s → L s x = c s)
    (hL : ∀ s x, 0 ≤ L s x)
    (hMean : ∀ x ∈ B, μ.mean (fun s => L s x) = 1)
    (hc : ∀ s, 0 ≤ c s) {γ D : ℝ} (hγ : 0 < γ) (hD : 0 < D)
    (hdeg : ∀ s x, x ∈ F s → ((neighborsIn G (F s) x).card : ℝ) * (c s / B.card) ≤
      ((F s).card * c s / B.card + γ) / D)
    (hatom : ∀ z J, i ∈ J → good z J → c (z i) / B.card ≤ γ / D)
    {h : ℕ} (hh : 0 < h) (hsize : (h : ℝ) - 1 ≤ D)
    (blocks : Fin h → Finset ↥((Finset.univ : Finset I).erase i))
    (hdisj : Pairwise (fun j k => Disjoint (blocks j) (blocks k))) :
    let u (z : I → Ω) : RetainedGroups V I Ω := ⟨B, revealed, z, L, F, c, good z, γ⟩
    let σ := FiniteLaw.uniform (Equiv.Perm ↥((Finset.univ : Finset I).erase i))
    (FiniteLaw.product (fun _ : I => μ)).event (fun z =>
      ((h : ℝ)⁻¹) ^ 2 < σ.mean (fun p =>
        mass ((u z).meanAt i blocks p) (marked G ((u z).meanAt i blocks p) B γ))) ≤
      Real.exp (1 / 8 - Real.log 2 * ((h : ℝ) * γ - 1)) / ((h : ℝ)⁻¹) ^ 2 := by
  classical
  intro u σ
  let U := (Finset.univ : Finset I)
  let limit := ((h : ℝ)⁻¹) ^ 2
  have hlimit : 0 < limit := by dsimp [limit]; positivity
  let extend (s : Ω) (w : {j // j ≠ i} → Ω) (j : I) := if hj : j = i then s else w ⟨j, hj⟩
  have hext (ω : I → Ω) : extend (ω i) (fun j => ω j.val) = ω := by
    funext j
    by_cases hj : j = i <;> simp [extend, hj]
  let P (ω : I → Ω) := limit < σ.mean (fun p =>
    mass ((u ω).meanAt i blocks p) (marked G ((u ω).meanAt i blocks p) B γ))
  rw [← FiniteLaw.mean_indicator, show (fun w => if P w then (1 : ℝ) else 0) =
    (fun w => if P (extend (w i) (fun j => w j.val)) then (1 : ℝ) else 0) by simp_rw [hext],
    FiniteLaw.mean_split_at (fun _ : I => μ) i
      (fun pair => if P (extend pair.1 pair.2) then 1 else 0), FiniteLaw.staged_mean]
  simp_rw [FiniteLaw.mean_indicator]
  let error := Real.exp (1 / 8 - Real.log 2 * ((h : ℝ) * γ - 1)) / limit
  refine (μ.mean_mono (Y := fun _ => error) (fun s => ?_)).trans_eq (μ.mean_const error)
  let μ' := FiniteLaw.product (fun _ : {j // j ≠ i} => μ)
  by_cases ha : c s / B.card ≤ γ / D
  · let expand (p : Equiv.Perm ↥(U.erase i)) (j : Fin h) := (blocks j).map p.toEmbedding
    let e : ↥(U.erase i) ↪ {j : I // j ≠ i} :=
      ⟨fun j => ⟨j.val, (Finset.mem_erase.mp j.property).1⟩,
        fun a b he => Subtype.ext (congrArg (fun a : {j : I // j ≠ i} => a.val) he)⟩
    let block (p : Equiv.Perm ↥(U.erase i)) (j : Fin h) := (expand p j).map e
    let withinBlock (p : Equiv.Perm ↥(U.erase i)) (j : Fin h) (w : ↥(block p j) → Ω) :
        {k // k ≠ i} → Ω := fun k => if hk : k ∈ block p j then w ⟨k, hk⟩ else s
    let keep (p : Equiv.Perm ↥(U.erase i)) (j : Fin h) (w : ↥(block p j) → Ω) :=
      (u (extend s (withinBlock p j w))).kept (restoreAnchor U i (expand p j))
    have hBlock (p : Equiv.Perm ↥(U.erase i)) :
        Pairwise (fun j k => Disjoint (block p j) (block p k)) := by
      intro j k hne
      exact (Finset.disjoint_map e).mpr ((Finset.disjoint_map p.toEmbedding).mpr (hdisj hne))
    have hKeep (p : Equiv.Perm ↥(U.erase i)) (j : Fin h) (w : {k // k ≠ i} → Ω) :
        keep p j (fun k => w k.val) ↔ (u (extend s w)).kept (restoreAnchor U i (expand p j)) := by
      unfold keep kept
      have hag (k : I) (hk : k ∈ restoreAnchor U i (expand p j)) :
          extend s (withinBlock p j (fun k => w k.val)) k = extend s w k := by
        change k ∈ insert i ((expand p j).map _) at hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp [extend]
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hk
          have hne := (Finset.mem_erase.mp a.property).1
          have hm : e a ∈ block p j := Finset.mem_map.mpr ⟨a, ha, rfl⟩
          simp [extend, hne, withinBlock, show (⟨a.val, hne⟩ : {k // k ≠ i}) = e a from rfl, hm]
      have hw (x : V) : (u (extend s (withinBlock p j (fun k => w k.val)))).rawWeight
          (restoreAnchor U i (expand p j)) x =
          (u (extend s w)).rawWeight (restoreAnchor U i (expand p j)) x := by
        simp only [u, rawWeight]
        congr 1
        exact Finset.prod_congr rfl (fun k hk => congrArg (fun a => L a x) (hag k hk))
      have hm : mass ((u (extend s (withinBlock p j (fun k => w k.val)))).rawWeight
          (restoreAnchor U i (expand p j))) B =
          mass ((u (extend s w)).rawWeight (restoreAnchor U i (expand p j))) B :=
        congrArg (fun f => mass f B) (funext hw)
      exact and_congr Iff.rfl (and_congr (hlocal _ _ _ hag) (by rw [hm]))
    have hZ : mass (sharedWeight (F s) (c s / B.card)) B = ((F s).card : ℝ) * c s / B.card := by
      rw [mass_sharedWeight, Finset.inter_eq_right.mpr (hF s)]
      ring
    have hP (p : Equiv.Perm ↥(U.erase i)) (j : Fin h) (w : {k // k ≠ i} → Ω) :
        (u (extend s w)).normalized i (restoreAnchor U i (expand p j)) =
        normalizedOverlap B (mass (sharedWeight (F s) (c s / B.card)) B)
          (16 * (mass (sharedWeight (F s) (c s / B.card)) B + γ))
          (keep p j (fun k => w k.val)) (fun x => sharedWeight (F s) (c s / B.card) x *
            ∏ k ∈ block p j, L (w k) x) := by
      let J := restoreAnchor U i (expand p j)
      have hiJ : i ∈ J := Finset.mem_insert_self _ _
      have he (x : V) (hx : x ∈ F s) : (u (extend s w)).rawWeight J x =
          (c s / B.card) * ∏ k ∈ block p j, L (w k) x := by
        have hai : i ∉ (expand p j).map (⟨Subtype.val, Subtype.val_injective⟩ : ↥(U.erase i) ↪ I) := by
          rintro hmem
          obtain ⟨a, _, ha⟩ := Finset.mem_map.mp hmem
          exact (Finset.mem_erase.mp a.property).1 ha
        have his : extend s w i = s := by simp [extend]
        simp only [u, rawWeight, J, restoreAnchor, Finset.prod_insert hai, block, Finset.prod_map, his, hrow s x hx]
        have hpart (a : ↥(U.erase i)) : extend s w a.val = w (e a) := by
          unfold extend
          rw [dite_eq_right (Finset.mem_erase.mp a.property).1]
          rfl
        have hEq : (∏ a ∈ expand p j, L (extend s w a.val) x) = ∏ a ∈ expand p j, L (w (e a)) x :=
          Finset.prod_congr rfl (fun a _ => congrArg (fun y => L y x) (hpart a))
        change (c s * ∏ a ∈ expand p j, L (extend s w a.val) x) / B.card = _
        rw [hEq]
        ring
      have hpos : (u (extend s w)).positionMass i = ((F s).card : ℝ) * c s / B.card := by
        simp only [u, positionMass, extend, dite_eq_left rfl]
      have hob : (u (extend s w)).outcome i = s := by simp [u, extend]
      by_cases hke : (u (extend s w)).kept J
      · have hk := (hKeep p j w).mpr hke
        have hr : (fun x => if x ∈ (u (extend s w)).retained ((u (extend s w)).outcome i)
            then (u (extend s w)).weight J x else 0) = fun x =>
              sharedWeight (F s) (c s / B.card) x * ∏ k ∈ block p j, L (w k) x := by
          funext x
          rw [hob]
          change (if x ∈ F s then (u (extend s w)).weight J x else 0) = _
          by_cases hx : x ∈ F s
          · simpa only [hx, ite_true, weight, hke, sharedWeight] using he x hx
          · simp [hx, sharedWeight]
        unfold normalized
        rw [hpos, hZ, hr]
        change normalizedOverlap B _ _ ((u (extend s w)).kept J) _ = _
        funext x
        simp only [show (u (extend s w)).quota = γ from rfl, normalizedOverlap, hke, hk, true_and]
      · have hk : ¬ keep p j (fun k => w k.val) := fun h => hke ((hKeep p j w).mp h)
        funext x
        change normalizedOverlap _ _ _ ((u (extend s w)).kept J) _ x = _
        simp only [normalizedOverlap, hke, hk, false_and, ite_false]
    have hBound := event_bad_marked_of_disjoint_blocks_le G
      (by simpa using hh) (fun _ : {k : I // k ≠ i} => μ) σ block hBlock B (F s) keep
      (fun x _ a => L a x) (fun x _ a => hL a x) (fun x hx _ => hMean x hx)
      (div_nonneg (hc s) (Nat.cast_nonneg _)) hγ hD (by simpa using hsize) ha
      (fun x hx => by rw [hZ]; exact hdeg s x hx) hlimit
    simp only [Fintype.card_fin] at hBound
    refine le_trans ?_ hBound
    apply FiniteLaw.event_mono
    intro w hw
    have he (p : Equiv.Perm ↥(U.erase i)) :
        (u (extend s w)).meanAt i blocks p = fun x =>
          (h : ℝ)⁻¹ * ∑ j, normalizedOverlap B (mass (sharedWeight (F s) (c s / B.card)) B)
            (16 * (mass (sharedWeight (F s) (c s / B.card)) B + γ))
            (keep p j (fun k => w k.val)) (fun x => sharedWeight (F s) (c s / B.card) x *
              ∏ k ∈ block p j, L (w k) x) x := by
      funext x
      unfold meanAt
      congr 1
      exact Finset.sum_congr rfl (fun j _ => congrFun (hP p j w) x)
    change P (extend s w) at hw
    dsimp only [P] at hw
    simp_rw [he] at hw
    exact hw
  · have hZero (w : {j // j ≠ i} → Ω) (p : Equiv.Perm ↥(U.erase i)) :
        (u (extend s w)).meanAt i blocks p = fun _ => 0 := by
      funext x
      have hn (j : Fin h) : ¬ (u (extend s w)).kept
          (restoreAnchor U i ((blocks j).map p.toEmbedding)) := fun hk => ha (by
            have hz := hatom (extend s w) (restoreAnchor U i ((blocks j).map p.toEmbedding))
              (by simp [restoreAnchor]) hk.2.1
            simpa [extend] using hz)
      have hz (j : Fin h) : (u (extend s w)).normalized i
          (restoreAnchor U i ((blocks j).map p.toEmbedding)) x = 0 := by
        simp [normalized, normalizedOverlap, hn j]
      change (h : ℝ)⁻¹ * ∑ j, (u (extend s w)).normalized i
        (restoreAnchor U i ((blocks j).map p.toEmbedding)) x = 0
      simp_rw [hz, Finset.sum_const_zero, mul_zero]
    have hf (w : {j // j ≠ i} → Ω) : ¬ P (extend s w) := by
      simp only [P, hZero, mass, Finset.sum_const_zero, FiniteLaw.mean_const, not_lt]
      exact hlimit.le
    simp only [hf, ← FiniteLaw.mean_indicator, ite_false, FiniteLaw.mean_const]
    exact div_nonneg (Real.exp_pos _).le hlimit.le

end LocallyRamsey.RetainedGroups
