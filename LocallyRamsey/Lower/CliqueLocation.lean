module

public import LocallyRamsey.Lower.GroupCollisions
public import LocallyRamsey.Lower.CliqueSupply

public section

open scoped BigOperators

namespace LocallyRamsey

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- Other vertices whose groups intersect the group of a prescribed
vertex. The vertex itself is excluded from this count. -/
def touchingGroups (Q : Finset V) (groups : V → Finset I) (x : V) : Finset V := by
  classical
  exact (Q.erase x).filter (fun y => ¬ Disjoint (groups x) (groups y))

/-- From a bound on the total number of intersections between groups,
discard the vertices belonging to groups with too many intersections. -/
theorem card_light_group_vertices_ge (Q : Finset V) (groups : V → Finset I) (d m : ℕ)
    (hcount : ∑ x ∈ Q, (touchingGroups Q groups x).card ≤ m * (d + 1)) :
    let good := Q.filter (fun x => (touchingGroups Q groups x).card ≤ d)
    Q.card ≤ good.card + m := by
  classical
  intro good
  let bad := Q.filter (fun x => d < (touchingGroups Q groups x).card)
  have hb : bad.card * (d + 1) ≤ m * (d + 1) := by
    calc
      _ = ∑ _x ∈ bad, (d + 1) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
      _ ≤ ∑ x ∈ bad, (touchingGroups Q groups x).card := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        have hx' : x ∈ Q.filter (fun y => d < (touchingGroups Q groups y).card) := hx
        exact (Finset.mem_filter.mp hx').2
      _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)).trans hcount
  have hb' := Nat.le_of_mul_le_mul_right hb (Nat.succ_pos d)
  have he : good.card + bad.card = Q.card := by
    have hbEq : bad = Q.filter (fun x => ¬(touchingGroups Q groups x).card ≤ d) := by
      ext x
      simp [bad]
    rw [hbEq]
    exact Finset.card_filter_add_card_filter_not _
  omega

/-- Restrict a clique to the vertices whose groups avoid the groups of
the recorded vertices. The retained clique lies in the common
neighbourhood of the records. The bound on the cost includes the records
themselves. -/
theorem clique_after_exposing_light_groups {G : SimpleGraph V}
    (W Q R : Finset V) (hQW : Q ⊆ W) (hQR : R ⊆ Q) (hcl : G.IsClique (Q : Set V))
    (group : V → Finset I) (d : ℕ)
    (hlight : ∀ x ∈ R, (touchingGroups Q group x).card ≤ d) :
    ∃ Q' : Finset V, Q' ⊆ Q ∧ Q' ⊆ commonNeighborsIn G W R ∧
      G.IsClique (Q' : Set V) ∧ Q.card ≤ Q'.card + R.card * (d + 1) ∧
      (∀ y ∈ Q', ∀ x ∈ R, Disjoint (group x) (group y)) := by
  classical
  let remove := R.biUnion (fun x => insert x (touchingGroups Q group x))
  let Q' := Q \ remove
  have hsubset : Q' ⊆ Q := Finset.sdiff_subset
  have hnb (y : V) (hy : y ∈ Q') (x : V) (hx : x ∈ R) :
      x ≠ y ∧ y ∉ touchingGroups Q group x := by
    have hno := (Finset.mem_sdiff.mp hy).2
    have hno' : y ∉ insert x (touchingGroups Q group x) := fun h => hno (Finset.mem_biUnion.mpr ⟨x, hx, h⟩)
    exact ⟨fun heq => hno' (Finset.mem_insert.mpr (Or.inl heq.symm)),
      fun h => hno' (Finset.mem_insert.mpr (Or.inr h))⟩
  refine ⟨Q', hsubset, ?_, fun x hx y hy hxy => hcl (hsubset hx) (hsubset hy) hxy, ?_, ?_⟩
  · intro y hy
    exact mem_commonNeighborsIn.mpr ⟨hQW (hsubset hy), fun x hx =>
      hcl (hQR hx) (hsubset hy) (hnb y hy x hx).1⟩
  · have hcount : remove.card ≤ R.card * (d + 1) := by
      refine Finset.card_biUnion_le.trans ?_
      calc
        _ ≤ ∑ _x ∈ R, (d + 1) := Finset.sum_le_sum (fun x hx =>
          (Finset.card_insert_le x _).trans (Nat.add_le_add_right (hlight x hx) 1))
        _ = _ := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
    have hcut := Finset.card_sdiff_add_card_inter Q remove
    have hi : (Q ∩ remove).card ≤ remove.card := Finset.card_le_card Finset.inter_subset_right
    dsimp [Q']
    omega
  · intro y hy x hx
    by_contra h
    apply (hnb y hy x hx).2
    change y ∈ (Q.erase x).filter (fun y => ¬Disjoint (group x) (group y))
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨(hnb y hy x hx).1.symm, hsubset hy⟩, h⟩

/-- Enlarge a small common neighbourhood inside the ambient region using
a choice that is fixed before further draws are revealed. -/
theorem exists_region_enlarging_common {G : SimpleGraph V} (W R : Finset V)
    {m : ℕ} (hmin : (commonNeighborsIn G W R).card ≤ m) (hmax : m ≤ W.card) :
    ∃ B : Finset V, B ⊆ W ∧ B.card = m ∧ commonNeighborsIn G W R ⊆ B := by
  let A := commonNeighborsIn G W R
  change A.card ≤ m at hmin
  have hsub : A ⊆ W := fun x hx => (mem_commonNeighborsIn.mp hx).1
  have hsize : m - A.card ≤ (W \ A).card := by
    rw [Finset.card_sdiff_of_subset hsub]
    omega
  obtain ⟨F, hF, hFcard⟩ := Finset.exists_subset_card_eq hsize
  have hdis : Disjoint A F := Finset.disjoint_left.mpr fun x hx hxf =>
    (Finset.mem_sdiff.mp (hF hxf)).2 hx
  refine ⟨A ∪ F, Finset.union_subset hsub (hF.trans Finset.sdiff_subset), ?_,
    Finset.subset_union_left⟩
  rw [Finset.card_union_of_disjoint hdis, hFcard]
  omega



/-- A fixed enlargement used for every revealed description. -/
@[expose] noncomputable def commonRegion (G : SimpleGraph V) (W R : Finset V) (b : ℕ) :
    Finset V := by
  classical
  exact if h : (commonNeighborsIn G W R).card ≤ b ∧ b ≤ W.card then
    Classical.choose (exists_region_enlarging_common W R h.1 h.2)
    else ∅

theorem commonRegion_spec (G : SimpleGraph V) (W R : Finset V) (b : ℕ)
    (hmin : (commonNeighborsIn G W R).card ≤ b) (hmax : b ≤ W.card) :
    commonRegion G W R b ⊆ W ∧ (commonRegion G W R b).card = b ∧
      commonNeighborsIn G W R ⊆ commonRegion G W R b := by
  classical
  simpa only [commonRegion, dite_eq_left (And.intro hmin hmax)] using
    Classical.choose_spec (exists_region_enlarging_common W R hmin hmax)

/-- A group intersection is counted once for every shared position in
the sum over ordered pairs, so the sum bounds the number of pairs
whose groups touch. -/
theorem touchingGroups_le_groupCollisionCount (Q : Finset V) {r : ℕ}
    (e : Fin r ≃ ↥Q) (group : V → Finset I) :
    ((∑ x ∈ Q, (touchingGroups Q group x).card : ℕ) : ℝ) ≤
      groupCollisionCount group (fun j => (e j).val) := by
  classical
  have heq (x : V) : ((touchingGroups Q group x).card : ℝ) =
      ∑ y ∈ Q, if y ≠ x ∧ ¬Disjoint (group x) (group y) then (1 : ℝ) else 0 := by
    have hf : (Q.erase x).filter (fun y => ¬Disjoint (group x) (group y)) =
        Q.filter (fun y => y ≠ x ∧ ¬Disjoint (group x) (group y)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      tauto
    rw [touchingGroups, hf, ← Finset.sum_filter]
    simp
  rw [Nat.cast_sum]
  simp_rw [heq, ← Finset.sum_coe_sort Q]
  rw [← Fintype.sum_equiv e (fun i => ∑ y : ↥Q,
    if y.val ≠ (e i).val ∧ ¬Disjoint (group (e i).val) (group y.val) then (1 : ℝ) else 0)
    (fun x => ∑ y : ↥Q, if y.val ≠ x.val ∧ ¬Disjoint (group x.val) (group y.val) then (1 : ℝ) else 0)
    (fun _ => rfl)]
  apply Finset.sum_le_sum
  intro i _
  rw [← Fintype.sum_equiv e (fun j =>
    if (e j).val ≠ (e i).val ∧ ¬Disjoint (group (e i).val) (group (e j).val) then (1 : ℝ) else 0)
    (fun y => if y.val ≠ (e i).val ∧ ¬Disjoint (group (e i).val) (group y.val) then (1 : ℝ) else 0)
    (fun _ => rfl)]
  refine Finset.sum_le_sum (fun j _ => ?_)
  by_cases h : i = j
  · subst j
    simp
  · rw [ite_eq_right h]
    split
    · obtain ⟨x, hx, hy⟩ := Finset.not_disjoint_iff.mp ‹_ ∧ _›.2
      have hpos := Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx, hy⟩⟩
      exact_mod_cast hpos
    · positivity

open Classical in
/-- On a good list, a sufficiently large clique whose groups have few
intersections can be recorded using only light groups. The retained
vertices lie in a region determined by the recorded vertices and avoid
all the exposed groups. -/
theorem record_light_clique {G : SimpleGraph V} (W Q : Finset V) (hW : W.Nonempty)
    (hQW : Q ⊆ W) (hcl : G.IsClique (Q : Set V))
    {s m d lost cap limit : ℕ} (L : Fin m → ↥W)
    {J : Type*} (draw : J → Finset V) (group : J → Finset I)
    (assign : ↥Q → J) (hinj : Function.Injective assign)
    (hAssign : ∀ x, x.val ∈ draw (assign x))
    (hTouch : let g (x : V) := if hx : x ∈ Q then group (assign ⟨x, hx⟩) else ∅
      ∑ x ∈ Q, (touchingGroups Q g x).card ≤ lost * (d + 1))
    (hsize : lost < Q.card)
    (hDeg : ∀ j, (Q.filter (G.Adj (L j).val)).card ≤ cap)
    (hCollision : (s : ℝ) ^ 2 / (Q.card - (lost : ℝ)) ≤ 1 / 2)
    (hSmall : (m : ℝ) * ((cap : ℝ) / (Q.card - (lost : ℝ))) ^ s <
      ((limit : ℝ) / W.card) * m / 4)
    (hList : letI : Nonempty ↥W := hW.to_subtype
      letI : DecidableRel (fun (y : ↥W) x => G.Adj y.val x) := fun _ _ => Classical.propDecidable _
      ∀ (f : Fin s → J) (v : Fin s → V), Function.Injective f →
        (∀ k, v k ∈ draw (f k)) →
        ((limit : ℝ) / W.card) ≤ (FiniteLaw.uniform ↥W).event
          (fun y => ∀ k, G.Adj y.val (v k)) →
        ((limit : ℝ) / W.card) * m / 2 ≤
          listCommonCount (fun (y : ↥W) x => G.Adj y.val x) L v)
    (hlimit : limit ≤ W.card) :
    ∃ (q : Fin s → ↥Q) (B Q' : Finset V),
      B = commonRegion G W (Finset.univ.image (fun j => (q j).val)) limit ∧
      B ⊆ W ∧ B.card = limit ∧ Function.Injective (assign ∘ q) ∧
      commonNeighborsIn G W (Finset.univ.image (fun j => (q j).val)) ⊆ B ∧
      Q' ⊆ Q ∧ Q' ⊆ B ∧ G.IsClique (Q' : Set V) ∧ Q.card ≤ Q'.card + s * (d + 1) ∧
      ∀ y : ↥Q, y.val ∈ Q' → ∀ j, Disjoint (group (assign (q j))) (group (assign y)) := by
  classical
  let _ : Nonempty ↥W := hW.to_subtype
  let g (x : V) := if hx : x ∈ Q then group (assign ⟨x, hx⟩) else ∅
  let A := Q.filter (fun x => (touchingGroups Q g x).card ≤ d)
  have hA : A ⊆ Q := Finset.filter_subset _ _
  have hAcard : Q.card ≤ A.card + lost := card_light_group_vertices_ge Q g d lost hTouch
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  let _ : Nonempty ↥A := hAne.to_subtype
  let assignA (x : ↥A) := assign ⟨x.val, hA x.property⟩
  have hinjA : Function.Injective assignA := fun x y h => Subtype.ext (congrArg (fun z : ↥Q => z.val) (hinj h))
  have hApos : 0 < (A.card : ℝ) := by exact_mod_cast hAne.card_pos
  have hBase : 0 < (Q.card : ℝ) - lost := by exact_mod_cast (Int.sub_pos.mpr (show (lost : ℤ) < Q.card by exact_mod_cast hsize))
  have hAlo : (Q.card : ℝ) - lost ≤ A.card := by
    have hcast : (Q.card : ℝ) ≤ A.card + lost := by exact_mod_cast hAcard
    linarith
  let H (y : ↥W) (x : V) := G.Adj y.val x
  let _ : DecidableRel H := fun _ _ => Classical.propDecidable _
  have hAssignCap (x : ↥A) : (FiniteLaw.uniform ↥A).event (fun y => assignA x = assignA y) ≤
      (1 : ℝ) / ((Q.card : ℝ) - lost) := by
    have he : (fun y : ↥A => assignA x = assignA y) = fun y => y = x := by
      funext y
      exact propext ⟨fun h => (hinjA h).symm, fun h => by rw [h]⟩
    rw [he, FiniteLaw.uniform_event]
    simp only [Finset.filter_eq', Finset.mem_univ, ite_true, Finset.card_singleton,
      Fintype.card_coe, Nat.cast_one]
    exact div_le_div_of_nonneg_left zero_le_one hBase hAlo
  have hDegA (j : Fin m) : (FiniteLaw.uniform ↥A).event (fun x => H (L j) x.val) ≤
      (cap : ℝ) / ((Q.card : ℝ) - lost) := by
    rw [uniform_vertex_event A hAne (H (L j))]
    have hs : (A.filter (H (L j))) ⊆ Q.filter (G.Adj (L j).val) :=
      fun x hx => Finset.mem_filter.mpr ⟨hA (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
    have hb := (Finset.card_le_card hs).trans (hDeg j)
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hb) hApos.le).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hBase hAlo)
  obtain ⟨a, ha, hsmall⟩ := exists_small_common_with_distinct_draws
    (FiniteLaw.uniform ↥W) (FiniteLaw.uniform ↥A) Subtype.val assignA H L
    (fun j x => x ∈ draw j) (fun x => hAssign ⟨x.val, hA x.property⟩)
    (by positivity) (by positivity) (by positivity) hAssignCap
    (by simpa only [div_eq_mul_inv, one_mul] using hCollision)
    hDegA hSmall hList
  let q (j : Fin s) : ↥Q := ⟨(a j).val, hA (a j).property⟩
  let R : Finset V := Finset.univ.image (fun j => (q j).val)
  have hRQ : R ⊆ Q := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (q j).property
  have hlight (x : V) (hx : x ∈ R) : (touchingGroups Q g x).card ≤ d := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp (a j).property).2
  have hCommon : (commonNeighborsIn G W R).card ≤ limit := by
    change (FiniteLaw.uniform ↥W).event (fun y => ∀ k, G.Adj y.val (q k).val) < _ at hsmall
    rw [uniform_vertex_event W hW (fun y : V => ∀ k, G.Adj y (q k).val)] at hsmall
    have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
    have hlt := (div_lt_div_iff_of_pos_right hWpos).mp hsmall
    have hs : commonNeighborsIn G W R ⊆ W.filter (fun y => ∀ k, G.Adj y (q k).val) := by
      intro y hy
      obtain ⟨hyW, hyadj⟩ := mem_commonNeighborsIn.mp hy
      exact Finset.mem_filter.mpr ⟨hyW, fun k => (hyadj _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)).symm⟩
    exact (Finset.card_le_card hs).trans (by exact_mod_cast hlt.le)
  let B := commonRegion G W R limit
  obtain ⟨hBW, hBsize, hB⟩ := commonRegion_spec G W R limit hCommon hlimit
  obtain ⟨Q', hQ', hQ'common, hQ'cl, hQ'card, hQ'avoid⟩ :=
    clique_after_exposing_light_groups W Q R hQW hRQ hcl g d hlight
  refine ⟨q, B, Q', rfl, hBW, hBsize, ha, hB, hQ', hQ'common.trans hB, hQ'cl, ?_, ?_⟩
  · exact hQ'card.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Finset.card_image_le.trans_eq (by simp))) _)
  · intro y hy j
    have h := hQ'avoid y.val hy (q j).val (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simpa only [g, dite_eq_left (q j).property, dite_eq_left y.property] using h


open Classical in
/-- When the draws are disjoint, form a clique from their union and read
one draw index for each clique vertex. The sum of group intersections
bounds the number of vertices whose assigned group is not light. -/
theorem locate_clique_from_good_draws {G : SimpleGraph V} (W : Finset V) (hW : W.Nonempty)
    {r N s m d lost cap limit M : ℕ} (L : Fin m → ↥W)
    (P : Fin N → Finset V) (group : Fin N → Finset I)
    (hPW : ∀ i, P i ⊆ W) (hPind : ∀ i, Gᶜ.IsClique (P i : Set V))
    (hDisjoint : Pairwise fun i j => Disjoint (P i) (P j))
    (hLarge : M ≤ (Finset.univ.biUnion P).card)
    (hRamsey : ∀ A : Finset V, A ⊆ W → M ≤ A.card →
      ∃ Q : Finset V, Q ⊆ A ∧ Q.card = r ∧ G.IsClique (Q : Set V))
    (hShared : ∀ f : Fin r → Fin N, Function.Injective f →
      groupCollisionCount group f ≤ (lost * (d + 1) : ℕ))
    (hsize : lost < r)
    (hDeg : ∀ j, ((Finset.univ : Finset (Fin N)).filter
      (fun i => ∃ x ∈ P i, G.Adj (L j).val x)).card ≤ cap)
    (hCollision : (s : ℝ) ^ 2 / (r - (lost : ℝ)) ≤ 1 / 2)
    (hSmall : (m : ℝ) * ((cap : ℝ) / (r - (lost : ℝ))) ^ s <
      ((limit : ℝ) / W.card) * m / 4)
    (hList : letI : Nonempty ↥W := hW.to_subtype
      ∀ (f : Fin s → Fin N) (v : Fin s → V), Function.Injective f →
        (∀ k, v k ∈ P (f k)) →
        ((limit : ℝ) / W.card) ≤ (FiniteLaw.uniform ↥W).event
          (fun y => ∀ k, G.Adj y.val (v k)) →
        ((limit : ℝ) / W.card) * m / 2 ≤
          listCommonCount (fun (y : ↥W) x => G.Adj y.val x) L v)
    (hlimit : limit ≤ W.card) :
    ∃ (f : Fin s → Fin N) (v : Fin s → V) (Q' : Finset V),
      Function.Injective f ∧ (∀ j, v j ∈ P (f j)) ∧
      let B := commonRegion G W (Finset.univ.image v) limit
      B ⊆ W ∧ B.card = limit ∧ Q' ⊆ B ∧ G.IsClique (Q' : Set V) ∧
      r ≤ Q'.card + s * (d + 1) ∧
      ∀ x ∈ Q', ∃ i, x ∈ P i ∧ ∀ j, Disjoint (group (f j)) (group i) := by
  let U := Finset.univ.biUnion P
  have hUW : U ⊆ W := by
    intro x hx
    obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    exact hPW i hxi
  obtain ⟨Q, hQU, hQr, hQcl⟩ := hRamsey U hUW hLarge
  have hin (x : ↥Q) : ∃ i, x.val ∈ P i := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp (hQU x.property)
    exact ⟨i, hi⟩
  let assign (x : ↥Q) := Classical.choose (hin x)
  have hAssign (x : ↥Q) : x.val ∈ P (assign x) := Classical.choose_spec (hin x)
  have hinj : Function.Injective assign := by
    intro x y he
    apply Subtype.ext
    by_contra hn
    have hQ := hQcl x.property y.property hn
    have hI := hPind (assign x) (hAssign x) (he ▸ hAssign y) hn
    exact ((SimpleGraph.compl_adj G x.val y.val).mp hI).2 hQ
  let e : Fin r ≃ ↥Q := (Finset.equivFinOfCardEq hQr).symm
  let g (x : V) := if hx : x ∈ Q then group (assign ⟨x, hx⟩) else ∅
  have hTouch : ∑ x ∈ Q, (touchingGroups Q g x).card ≤ lost * (d + 1) := by
    have hb : groupCollisionCount g (fun j => (e j).val) ≤ (lost * (d + 1) : ℕ) := by
      have he : (fun j => g ((e j).val)) = group ∘ (assign ∘ e) := by
        funext j
        simp only [g, dite_eq_left (e j).property, Function.comp_apply]
      change (∑ i, ∑ j, if i = j then 0 else
        ((g (e i).val ∩ g (e j).val).card : ℝ)) ≤ _
      simp_rw [show ∀ i : Fin r, g ((e i).val) = (group ∘ (assign ∘ e)) i from congrFun he]
      exact hShared (assign ∘ e) (hinj.comp e.injective)
    exact_mod_cast (touchingGroups_le_groupCollisionCount Q e g).trans hb
  have hDegQ (j : Fin m) : (Q.filter (G.Adj (L j).val)).card ≤ cap := by
    let A := Q.filter (G.Adj (L j).val)
    let f (x : ↥A) : Fin N := assign ⟨x.val, Finset.filter_subset _ _ x.property⟩
    have hfi : Function.Injective f := fun x y h =>
      Subtype.ext (congrArg (fun z : ↥Q => z.val) (hinj h))
    let F := (Finset.univ : Finset ↥A).image f
    have hs : F ⊆ Finset.univ.filter (fun i => ∃ x ∈ P i, G.Adj (L j).val x) := by
      intro i hi
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.val, hAssign _,
        (Finset.mem_filter.mp x.property).2⟩
    have hCard := (Finset.card_le_card hs).trans (hDeg j)
    change F.card ≤ cap at hCard
    rwa [Finset.card_image_of_injective _ hfi, Finset.card_univ, Fintype.card_coe] at hCard
  obtain ⟨a, B, Q', hB, hBW, hBsize, ha, _, hQ'Q, hQ'B, hQ'cl, hQ'card, hQ'eligible⟩ :=
    record_light_clique W Q hW (hQU.trans hUW) hQcl L P group assign hinj hAssign hTouch
      (hQr ▸ hsize) hDegQ (by simpa only [hQr] using hCollision)
      (by simpa only [hQr] using hSmall) hList hlimit
  refine ⟨assign ∘ a, fun j => (a j).val, Q', ha, fun j => hAssign (a j), ?_⟩
  rw [← hB]
  refine ⟨hBW, hBsize, hQ'B, hQ'cl, hQr ▸ hQ'card, ?_⟩
  intro x hx
  let z : ↥Q := ⟨x, hQ'Q hx⟩
  exact ⟨assign z, hAssign z, hQ'eligible z hx⟩


/-- Discard the clique vertices belonging to rejected draws. Since each
draw is independent, each rejected draw costs at most one vertex. -/
theorem clique_after_rejecting_draws {G : SimpleGraph V} {J : Type*} [DecidableEq J]
    (Q : Finset V) (hQ : G.IsClique (Q : Set V))
    (P : J → Finset V) (hP : ∀ j, Gᶜ.IsClique (P j : Set V)) (bad : Finset J)
    (assign : ↥Q → J) (hAssign : ∀ x, x.val ∈ P (assign x)) :
    ∃ Q' : Finset V, Q' ⊆ Q ∧ G.IsClique (Q' : Set V) ∧ Q.card ≤ Q'.card + bad.card ∧
      ∀ x : ↥Q, x.val ∈ Q' → assign x ∉ bad := by
  classical
  let good : Finset ↥Q := Finset.univ.filter (fun x => assign x ∉ bad)
  let rejected : Finset ↥Q := Finset.univ.filter (fun x => assign x ∈ bad)
  let Q' : Finset V := good.image Subtype.val
  have hsub : Q' ⊆ Q := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hi : Function.Injective assign := by
    intro x y hxy
    apply Subtype.ext
    by_contra h
    have h1 := hQ x.property y.property h
    have h2 := hP (assign x) (hAssign x) (hxy ▸ hAssign y) h
    exact ((SimpleGraph.compl_adj G x.val y.val).mp h2).2 h1
  have hrej : rejected.card ≤ bad.card := by
    rw [← Finset.card_image_of_injective rejected hi]
    exact Finset.card_le_card (fun i hi => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hx).2)
  have hCard : good.card + rejected.card = Q.card := by
    rw [add_comm, ← Fintype.card_coe Q]
    exact Finset.card_filter_add_card_filter_not _
  refine ⟨Q', hsub, fun x hx y hy h => hQ (hsub hx) (hsub hy) h, ?_, ?_⟩
  · rw [Finset.card_image_of_injective good Subtype.val_injective]
    omega
  · intro x hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    obtain rfl : y = x := Subtype.ext he
    exact (Finset.mem_filter.mp hy).2

open Classical in
/-- From the clique located by a description, retain the vertices whose
groups pass the retention tests. Every one of their draws is eligible
because its group is disjoint from all the revealed groups. -/
theorem retain_located_clique {G : SimpleGraph V} {J : Type*} [Fintype J] [DecidableEq J]
    (Q : Finset V) (hQ : G.IsClique (Q : Set V))
    (P : J → Finset V) (hP : ∀ j, Gᶜ.IsClique (P j : Set V))
    (group : J → Finset I) (recorded : Finset J)
    (hGroup : ∀ j, (group j).Nonempty)
    (keep : J → Prop)
    (assign : ↥Q → J) (hAssign : ∀ x, x.val ∈ P (assign x))
    (hEligible : ∀ x j, j ∈ recorded → Disjoint (group j) (group (assign x)))
    {cost : ℕ} (hCost : ((Finset.univ : Finset J).filter (fun i =>
      (∀ j ∈ recorded, Disjoint (group j) (group i)) ∧
      (P i).Nonempty ∧ ¬keep i)).card ≤ cost) :
    ∃ Q' : Finset V, Q' ⊆ Q ∧ G.IsClique (Q' : Set V) ∧ Q.card ≤ Q'.card + cost ∧
      ∀ x ∈ Q', ∃ j, j ∉ recorded ∧ x ∈ P j ∧ keep j := by
  let rejected := (Finset.univ : Finset J).filter (fun i =>
    (∀ j ∈ recorded, Disjoint (group j) (group i)) ∧ (P i).Nonempty ∧ ¬keep i)
  obtain ⟨Q', hQ'Q, hQ'cl, hSize, hNot⟩ := clique_after_rejecting_draws Q hQ P hP rejected assign hAssign
  refine ⟨Q', hQ'Q, hQ'cl, hSize.trans (Nat.add_le_add_left hCost _), ?_⟩
  intro x hx
  let v : ↥Q := ⟨x, hQ'Q hx⟩
  have hnot : assign v ∉ recorded := by
    intro hmem
    have hdis := hEligible v (assign v) hmem
    obtain ⟨i, hi⟩ := hGroup (assign v)
    exact Finset.disjoint_left.mp hdis hi hi
  refine ⟨assign v, hnot, hAssign v, ?_⟩
  by_contra hn
  exact hNot v hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    hEligible v, ⟨x, hAssign v⟩, hn⟩)

end LocallyRamsey
