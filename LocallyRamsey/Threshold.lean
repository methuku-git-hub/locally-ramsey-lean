module

public import LocallyRamsey.Definitions
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

public section

namespace LocallyRamsey

theorem IsLocallyRamsey.mono {V : Type*} {G : SimpleGraph V} {m m' r : ℕ}
    (h : IsLocallyRamsey G m r) (hm : m ≤ m') : IsLocallyRamsey G m' r := by
  intro A hA
  obtain ⟨A₀, hsub, hcard⟩ := Finset.exists_subset_card_eq (s := A) (hA ▸ hm)
  obtain ⟨⟨K, hK, hclique⟩, ⟨I, hI, hindependent⟩⟩ := h A₀ hcard
  exact ⟨⟨K, hK.trans hsub, hclique⟩, ⟨I, hI.trans hsub, hindependent⟩⟩

theorem exists_graph_at_threshold (n r : ℕ) :
    ∃ G : SimpleGraph (Fin n), IsLocallyRamsey G (threshold n r) r := by
  change sInf {m : ℕ | ∃ G : SimpleGraph (Fin n), IsLocallyRamsey G m r} ∈
    {m : ℕ | ∃ G : SimpleGraph (Fin n), IsLocallyRamsey G m r}
  apply Nat.sInf_mem
  refine ⟨n + 1, (⊥ : SimpleGraph (Fin n)), ?_⟩
  intro A hA
  have hcard := Finset.card_le_univ A
  simp only [Fintype.card_fin, hA] at hcard
  omega

theorem threshold_le_iff {n m r : ℕ} :
    threshold n r ≤ m ↔ ∃ G : SimpleGraph (Fin n), IsLocallyRamsey G m r := by
  constructor
  · intro hm
    obtain ⟨G, hG⟩ := exists_graph_at_threshold n r
    exact ⟨G, hG.mono hm⟩
  · intro hm
    exact Nat.sInf_le hm

/-- Pulling back an induced graph by an embedding commutes with
complementation. -/
theorem comap_complement {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext x y
  simp [SimpleGraph.compl_adj, f.injective.ne_iff]

theorem clique_preimage_of_embedding {V W : Type*} (f : V ↪ W) {G : SimpleGraph W}
    {X : Finset V} {K : Finset W} {r : ℕ} (hK : K ⊆ X.map f) (hcl : G.IsNClique r K) :
    ∃ K' : Finset V, K' ⊆ X ∧ (G.comap f).IsNClique r K' := by
  classical
  let K' := K.preimage f f.injective.injOn
  have heq : K'.map f = K := by
    ext y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_preimage.mp hx
    · intro hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp (hK hy)
      exact Finset.mem_map.mpr ⟨x, Finset.mem_preimage.mpr hy, rfl⟩
  refine ⟨K', Finset.preimage_subset hK, ⟨?_, ?_⟩⟩
  · intro x hx y hy hxy
    exact hcl.isClique (Finset.mem_preimage.mp hx) (Finset.mem_preimage.mp hy) (f.injective.ne hxy)
  · rw [← Finset.card_map (s := K') f, heq, hcl.card_eq]

/-- Restricting to fewer vertices preserves the same local threshold. -/
theorem IsLocallyRamsey.comap {V W : Type*} (f : V ↪ W) {G : SimpleGraph W}
    {m r : ℕ} (h : IsLocallyRamsey G m r) : IsLocallyRamsey (G.comap f) m r := by
  intro X hx
  obtain ⟨⟨K, hK, hcl⟩, ⟨I, hI, hind⟩⟩ := h (X.map f) (by simpa using hx)
  exact ⟨clique_preimage_of_embedding f hK hcl,
    (comap_complement f G).symm ▸ clique_preimage_of_embedding f hI hind⟩

theorem threshold_mono_vertices {n N r : ℕ} (hn : n ≤ N) : threshold n r ≤ threshold N r := by
  obtain ⟨G, hG⟩ := exists_graph_at_threshold N r
  let f : Fin n ↪ Fin N := ⟨Fin.castLE hn, Fin.castLE_injective hn⟩
  exact threshold_le_iff.mpr ⟨G.comap f, hG.comap f⟩

/-- An impossibility result at the rounded-down threshold yields the strict
real-valued inequality used in the lower bound. -/
theorem lt_threshold_iff {n r : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    a < (threshold n r : ℝ) ↔
      ∀ G : SimpleGraph (Fin n), ¬ IsLocallyRamsey G ⌊a⌋₊ r := by
  rw [← Nat.floor_lt ha, ← not_le, threshold_le_iff]
  exact not_exists

theorem target_eq_clog (n : ℕ) : target n = Nat.clog 2 n := by
  simpa [target] using Real.natCeil_logb_natCast 2 n

/-- The stronger real-valued bound with the integer target in its formula
implies the base-two form stated in Theorem 1. -/
theorem lower_bound_of_integer_target
    (h : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ((target n : ℝ) ^ (7 / 2 : ℝ)) / (Real.log (target n : ℝ)) ^ 24
        < (threshold n (target n) : ℝ)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (Real.logb 2 (n : ℝ)) ^ (7 / 2 : ℝ) / (Real.logb 2 (Real.logb 2 (n : ℝ))) ^ 24
        < (threshold n (target n) : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := h
  refine ⟨max n₀ 256, fun n hn => ?_⟩
  let x := Real.logb 2 (n : ℝ)
  have hn' : (256 : ℝ) ≤ n := by exact_mod_cast (le_max_right n₀ 256).trans hn
  have hx : 8 ≤ x := by
    apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith : 0 < (n : ℝ))).2
    norm_num [Real.rpow_natCast]
    exact (le_max_right n₀ 256).trans hn
  have hxt : x ≤ (target n : ℝ) := Nat.le_ceil _
  have ht : (target n : ℝ) ≤ 2 * x := by
    have hround : (target n : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ x)
    linarith
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog₂' : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hlogx : 3 * Real.log 2 ≤ Real.log x := by
    have h8 : (2 : ℝ) ^ (3 : ℕ) ≤ x := by norm_num; exact hx
    simpa [Real.log_pow] using Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ (3 : ℕ)) h8
  have hlogs : Real.log (target n : ℝ) ≤ Real.logb 2 x := by
    have hlogt := Real.log_le_log (show 0 < (target n : ℝ) by linarith) ht
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : x ≠ 0)] at hlogt
    rw [Real.logb, le_div_iff₀ hlog₂]
    nlinarith [mul_nonneg (show 0 ≤ 3 / 4 - Real.log 2 by linarith)
      (show 0 ≤ Real.log x + Real.log 2 by linarith)]
  have hlogt : 0 < Real.log (target n : ℝ) := Real.log_pos (by linarith)
  have hcomp : x ^ (7 / 2 : ℝ) / (Real.logb 2 x) ^ 24 ≤
      ((target n : ℝ) ^ (7 / 2 : ℝ)) / (Real.log (target n : ℝ)) ^ 24 := by
    gcongr
  exact hcomp.trans_lt (hn₀ n ((le_max_left n₀ 256).trans hn))

end LocallyRamsey
