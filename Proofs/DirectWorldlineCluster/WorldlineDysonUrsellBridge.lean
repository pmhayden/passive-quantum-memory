/-
Copyright 2026 The Passive Quantum Memory Authors.
Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in
compliance with the License. You may obtain a copy of the License at
https://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is
distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
implied. See the License for the specific language governing permissions and limitations under the
License.
-/

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellSpanning
import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellPartition
import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellExpLog

/-!
# Worldline Duhamel–Dyson–Ursell Trace Bridge and Zero-Spillover Witness Bound

Defines the RCA-1 spanning support `worldlinePolymerSpanningSupport` of a worldline polymer and verifies the Kotecký–Preiss tree-sum criterion (`worldline_polymer_tree_sum_and_kp_criterion`) and pinned Ursell cluster bounds (`worldline_ursell_pinned_cluster_sum_le_of_kp`, `worldline_ursell_dobrushin_kotecky_preiss_active_bound`). Combines the Duhamel–Dyson–Ursell trace identity (`worldline_duhamel_dyson_ursell_trace_identity`) with spanning-surface root confinement to prove the zero-spillover witness Gibbs bound (`worldline_zero_spillover_witness_gibbs_bound`).

## References

* Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
* Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)
* Kotecký–Preiss (1986), Cluster expansion for abstract polymer models
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace DirectWorldlineCluster

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

/-!
## 1. Polymer Activity Bounds, Dyson–Mayer–Ursell Decomposition, and Zero-Spillover Witness Bound

Combines the spanning-surface collar confinement (`WorldlineDysonUrsellSpanning`), the Dyson–Mayer polymer gas partition identity (`worldline_dyson_mayer_polymer_gas_partition_identity`), and the Mayer–Ursell cluster logarithm identity (`worldline_mayer_ursell_cluster_log_identity`) with the Kotecký–Preiss tree-sum criterion (`worldline_polymer_tree_sum_and_kp_criterion`, `worldline_ursell_pinned_cluster_sum_le_of_kp`) to establish the pinned Ursell cluster bound (`worldline_ursell_dobrushin_kotecky_preiss_active_bound`) and the zero-spillover witness Gibbs bound (`worldline_zero_spillover_witness_gibbs_bound`).
-/

/-- Full spanning check support $\mathrm{Supp}_{\mathrm{span}}(\gamma) = \overline{\mathcal{C}}(\gamma) \cup \alpha(\gamma)$
    of an individual worldline polymer $\gamma$ (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:J-span-full-def`). -/
def worldlinePolymerSpanningSupport
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (γ : WorldlineDysonPolymer L q_code) : Finset (IdxCSS[L, q_code, m_max]) :=
  worldlinePolymerNativeCollar sys C_RCA γ ∪ worldlinePolymerSpanningSurface D_field sys C_RCA γ

private lemma single_scale_worldlineSpanningThreshold_bound
    {R_cut : ℕ} {Δ_RCA C_wl c_wl β J : ℝ} {f : ℕ → ℝ}
    (hf_nn : ∀ r, 0 ≤ f r) (hc_wl : 0 ≤ c_wl) (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 R_cut) :
    64 * Real.exp 1 * C_wl * ((r : ℝ) ^ 6) * (β * J * f r) *
      Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3)) ≤ 1 := by
  let term : ℕ → ℝ := fun s =>
    C_wl * ((s : ℝ) ^ 6) * f s *
      Real.exp (c_wl * (1 + β) * ((s : ℝ) ^ 3))
  have hC : 0 ≤ C_wl := by
    by_contra h_neg
    push_neg at h_neg
    have h_sum_le : worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 0 := by
      unfold worldlineNativeKPSum
      refine Finset.sum_nonpos fun s' _ => ?_
      have hs' := hf_nn s'
      have h1 : 0 ≤ ((s' : ℝ) ^ 6) * f s' * Real.exp (c_wl * (1 + β) * ((s' : ℝ) ^ 3)) := by positivity
      nlinarith
    linarith
  have h_term_nn : ∀ s, 0 ≤ term s := fun s => by
    dsimp [term]; have := hf_nn s; positivity
  have h_term_le_sum : term r ≤ worldlineNativeKPSum f C_wl c_wl β R_cut := by
    unfold worldlineNativeKPSum
    exact Finset.single_le_sum (f := term) (fun s _ => h_term_nn s) hr
  let D := 64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut
  have h_max_pos : 0 < max 1 β := lt_of_lt_of_le zero_lt_one (le_max_left 1 β)
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hJ_le_inv : J ≤ 1 / D := le_trans h_thresh (min_le_right _ _)
  have h_num_le_D : 64 * Real.exp 1 * β * term r ≤ D := by
    dsimp [D]
    have h1 : 64 * Real.exp 1 * β ≤ 64 * Real.exp 1 * max 1 β :=
      mul_le_mul_of_nonneg_left (le_max_right 1 β) (by positivity)
    exact mul_le_mul h1 h_term_le_sum (h_term_nn r) (by positivity)
  calc 64 * Real.exp 1 * C_wl * ((r : ℝ) ^ 6) * (β * J * f r) *
        Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3))
    _ = J * (64 * Real.exp 1 * β * term r) := by dsimp [term]; ring
    _ ≤ J * D := mul_le_mul_of_nonneg_left h_num_le_D hJ
    _ ≤ (1 / D) * D := mul_le_mul_of_nonneg_right hJ_le_inv (le_of_lt hD_pos)
    _ = 1 := one_div_mul_cancel (ne_of_gt hD_pos)

private lemma kpMonomerWeight_bounds_local
    {L r_0 w_0 R_cut : ℕ}
    {C_RCA Δ_RCA C_wl c_wl β J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut)
    (hf_nn : ∀ r, 0 ≤ f r)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {p : ℕ × Finset (Box3D L)} (hp : p ∈ worldlineScaleCubeFinset L R_cut) :
    let Δ_V := (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ)
    0 ≤ kpMonomerWeight c_wl β J f p ∧
    4 * Real.exp 1 * Real.exp ((1 / 8 : ℝ) * Δ_V) * kpMonomerWeight c_wl β J f p ≤
      (1 / 64 : ℝ) * Real.exp (-12 * Δ_V) ∧
    kpMonomerWeight c_wl β J f p ≤ 1 ∧
    4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1) ≤ kpMonomerWeight c_wl β J f p := by
  rcases mem_kpScaleCubeFinset_iff.mp hp with ⟨hp_r, _⟩
  have hr_Icc : p.1 ∈ Finset.Icc 1 R_cut :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp_r).1,
      le_trans (Finset.mem_Icc.mp hp_r).2 (Nat.min_le_left R_cut L)⟩
  have hc_wl_nn : 0 ≤ c_wl := le_trans (Nat.cast_nonneg _) hc_wl_cal
  have h_ss := single_scale_worldlineSpanningThreshold_bound hf_nn hc_wl_nn (by linarith) hJ h_sum_pos h_thresh hr_Icc
  exact kpMonomerWeight_bounds hR_cut hf_nn hC_wl_cal hc_wl_cal hβ hJ hp h_ss

private lemma exp_eighth_worldlinePolymerNativeCollar_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ} (hC_RCA : 0 ≤ C_RCA)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {M : Finset (ℕ × Finset (Box3D L))} (hM_sub : M ⊆ worldlineScaleCubeFinset L R_cut)
    {γ : WorldlineDysonPolymer L q_code} (hγ_M : worldlinePolymerMonomers γ = M) :
    Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)) ≤
      (Real.exp ((1 / 8 : ℝ) * (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ))) ^ M.card := by
  have h_card : (worldlinePolymerNativeCollar sys C_RCA γ).card ≤
      M.card * kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := by
    unfold worldlinePolymerNativeCollar nativeCollarSupport
    rw [hγ_M]
    calc (M.biUnion (fun p => rcaCollarChecks sys C_RCA p.1 p.2)).card
      _ ≤ ∑ p ∈ M, (rcaCollarChecks sys C_RCA p.1 p.2).card := Finset.card_biUnion_le
      _ ≤ M.card • kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := by
          refine Finset.sum_le_card_nsmul M _ _ fun p hp => ?_
          rcases mem_kpScaleCubeFinset_iff.mp (hM_sub hp) with ⟨hr, _⟩
          exact card_kpRCACollarChecks_le D_field sys h_sys_checks h_geom hC_RCA hr p.2
      _ = M.card * kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := smul_eq_mul _ _
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have h_cast : ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ) ≤
      (M.card : ℝ) * (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) := by exact_mod_cast h_card
  linarith

private lemma sum_validPolymers_with_monomers_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (ℱ : Finset (WorldlineDysonPolymer L q_code))
    {M : Finset (ℕ × Finset (Box3D L))} (hM_sub : M ⊆ worldlineScaleCubeFinset L R_cut) :
    (∑ γ ∈ ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
        worldlinePolymerMonomers γ = M),
      |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
        Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))) ≤
      ((1 / 64 : ℝ) *
        Real.exp (-12 * (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ))) ^ M.card := by
  have hβ_nn : 0 ≤ β := by linarith
  let Δ_V : ℕ := kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA
  let C_col : ℝ := Real.exp ((1 / 8 : ℝ) * (Δ_V : ℝ))
  have h_bounds : ∀ {p}, p ∈ M →
      0 ≤ kpMonomerWeight c_wl β J f p ∧
      4 * Real.exp 1 * C_col * kpMonomerWeight c_wl β J f p ≤
        (1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ)) ∧
      kpMonomerWeight c_wl β J f p ≤ 1 ∧
      4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1) ≤ kpMonomerWeight c_wl β J f p :=
    fun {p} hp => kpMonomerWeight_bounds_local hR_cut hf_nn hC_wl_cal hc_wl_cal hβ hJ
      h_sum_pos h_thresh (hM_sub hp)
  let w_J (p : ℕ × Finset (Box3D L)) : ℝ :=
    2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3))
  let w_D (p : ℕ × Finset (Box3D L)) : ℝ :=
    4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1)
  let ℱ_M := ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
    worldlinePolymerMonomers γ = M)
  let F_raw (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    ((γ.1.length.factorial : ℝ)⁻¹) * (γ.1.map (fun ξ => w_J ξ.1)).prod * ∏ ϑ ∈ γ.2, w_D ϑ
  have h_pt : ∀ γ ∈ ℱ_M,
      |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
        Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)) ≤
        (C_col ^ M.card) * F_raw γ := by
    intro γ hγ
    rcases Finset.mem_filter.mp hγ with ⟨_, hγ_val, hγ_M⟩
    have h_w := worldlinePolymerWeight_abs_le_prod hR_cut hβ_nn hJ hf_nn D_field sys
      h_sys_checks h_geom hc_wl_cal V hV_norm d_loc hd_scale ν γ hγ_val σ
    have h_e := exp_eighth_worldlinePolymerNativeCollar_le hC_RCA D_field sys h_sys_checks h_geom hM_sub hγ_M
    calc |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
          Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
      _ ≤ F_raw γ * (C_col ^ M.card) :=
          mul_le_mul h_w h_e (Real.exp_nonneg _) (le_trans (abs_nonneg _) h_w)
      _ = (C_col ^ M.card) * F_raw γ := mul_comm _ _
  let K_max : ℕ := ℱ_M.sup (fun γ => γ.1.length)
  have h_len_mem : ∀ γ ∈ ℱ_M, γ.1.length ∈ Finset.range (K_max + 1) := fun γ hγ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.le_sup (f := fun γ : WorldlineDysonPolymer L q_code => γ.1.length) hγ))
  have h_m_bound : ∀ m ∈ Finset.range (K_max + 1),
      (∑ γ ∈ ℱ_M.filter (fun γ => γ.1.length = m), F_raw γ) ≤
        (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
          ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
    intro m _
    let ℱ_m := ℱ_M.filter (fun γ => γ.1.length = m)
    let monomerTuple (γ : WorldlineDysonPolymer L q_code) (j : Fin m) : WorldlineJumpMonomer L q_code :=
      if h : j.val < γ.1.length then γ.1.get ⟨j.val, h⟩ else ((0, ∅), (0, 0))
    let cubeTuple (γ : WorldlineDysonPolymer L q_code) (j : Fin m) : ℕ × Finset (Box3D L) :=
      (monomerTuple γ j).1
    let P_M := (Fintype.piFinset (fun _ : Fin m => M)) ×ˢ M.powerset
    have h_maps : ∀ γ ∈ ℱ_m, (cubeTuple γ, γ.2) ∈ P_M := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hγ_M_mem, h_len⟩
      rcases Finset.mem_filter.mp hγ_M_mem with ⟨_, _, h_mon⟩
      refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, Finset.mem_powerset.mpr ?_⟩
      · have hj : j.val < γ.1.length := h_len ▸ j.isLt
        dsimp [cubeTuple, monomerTuple]
        rw [dif_pos hj]
        rw [← h_mon]
        exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem (List.get_mem _ _)))
      · rw [← h_mon]
        exact Finset.subset_union_right
    have h_P_bound : ∀ P ∈ P_M,
        (∑ γ ∈ ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P), F_raw γ) ≤
          ((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
      intro P hP
      let ℱ_P := ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P)
      change (∑ γ ∈ ℱ_P, F_raw γ) ≤ _
      by_cases h_emp : ℱ_P = ∅
      · rw [h_emp, Finset.sum_empty]
        exact mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp => (h_bounds hp).1)
      · rcases Finset.nonempty_iff_ne_empty.mpr h_emp with ⟨γ₀, hγ₀⟩
        have h_ofFn_mon : ∀ γ ∈ ℱ_P, List.ofFn (monomerTuple γ) = γ.1 := by
          intro γ hγ
          have h_len : γ.1.length = m := (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
          exact ofFn_get_eq_self γ.1 ((0, ∅), (0, 0)) m h_len
        have h_ofFn_cube : ∀ γ ∈ ℱ_P, List.ofFn P.1 = γ.1.map Prod.fst := by
          intro γ hγ
          have h_eq_P : cubeTuple γ = P.1 := congrArg Prod.fst (Finset.mem_filter.mp hγ).2
          rw [← h_eq_P, ← h_ofFn_mon γ hγ, List.map_ofFn]
          rfl
        have h_union_eq : (List.ofFn P.1).toFinset ∪ P.2 = M := by
          have h_eq_P2 : γ₀.2 = P.2 := congrArg Prod.snd (Finset.mem_filter.mp hγ₀).2
          have h_mon₀ : worldlinePolymerMonomers γ₀ = M :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ₀).1).1).2.2
          rw [h_ofFn_cube γ₀ hγ₀, ← h_eq_P2]
          exact h_mon₀
        have h_F_eq : ∀ γ ∈ ℱ_P,
            F_raw γ = ((m.factorial : ℝ)⁻¹) * (∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ := by
          intro γ hγ
          have h_len : γ.1.length = m := (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
          have h_eq_P2 : γ.2 = P.2 := congrArg Prod.snd (Finset.mem_filter.mp hγ).2
          have h_map_eq : γ.1.map (fun ξ => w_J ξ.1) = List.ofFn (fun j : Fin m => w_J (P.1 j)) := by
            calc γ.1.map (fun ξ => w_J ξ.1)
              _ = (γ.1.map Prod.fst).map w_J := by rw [List.map_map]; rfl
              _ = (List.ofFn P.1).map w_J := by rw [← h_ofFn_cube γ hγ]
              _ = List.ofFn (fun j : Fin m => w_J (P.1 j)) := by rw [List.map_ofFn]; rfl
          dsimp [F_raw]
          rw [h_len, h_eq_P2, h_map_eq, List.prod_ofFn]
        have h_card_P : ℱ_P.card ≤
            ∏ j : Fin m, (validJumpMonomersAtCube D_field sys (P.1 j)).card := by
          rw [← Fintype.card_piFinset]
          refine Finset.card_le_card_of_injOn monomerTuple (fun γ hγ => ?_) (fun γ₁ hγ₁ γ₂ hγ₂ h_eq => ?_)
          · refine Fintype.mem_piFinset.mpr fun j => ?_
            have h_len : γ.1.length = m := (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
            have h_val : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).1).2.1
            have h_eq_P1 : cubeTuple γ j = P.1 j :=
              congrFun (congrArg Prod.fst (Finset.mem_filter.mp hγ).2) j
            have hj : j.val < γ.1.length := h_len ▸ j.isLt
            have h_mon_eq : monomerTuple γ j = γ.1.get ⟨j.val, hj⟩ := dif_pos hj
            rw [← h_eq_P1]
            change monomerTuple γ j ∈ validJumpMonomersAtCube D_field sys (monomerTuple γ j).1
            rw [h_mon_eq]
            exact mem_validJumpMonomersAtCube_of_valid D_field sys
              (fun idx => (h_sys_checks idx).2.1) h_val (List.get_mem _ _)
          · have h1 : γ₁.1 = γ₂.1 := by rw [← h_ofFn_mon γ₁ hγ₁, ← h_ofFn_mon γ₂ hγ₂, h_eq]
            have h2 : γ₁.2 = γ₂.2 := by
              rw [congrArg Prod.snd (Finset.mem_filter.mp hγ₁).2,
                congrArg Prod.snd (Finset.mem_filter.mp hγ₂).2]
            exact Prod.ext h1 h2
        have h_J_prod : ((ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)) ≤
            ∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p := by
          have h_wJ_nn : 0 ≤ ∏ j : Fin m, w_J (P.1 j) :=
            Finset.prod_nonneg fun j _ => by dsimp [w_J]; have := hf_nn (P.1 j).1; positivity
          have h_P1_mem : ∀ j : Fin m, P.1 j ∈ M :=
            Fintype.mem_piFinset.mp (Finset.mem_product.mp hP).1
          calc (ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)
            _ ≤ ((∏ j : Fin m, (validJumpMonomersAtCube D_field sys (P.1 j)).card : ℕ) : ℝ) *
                  ∏ j : Fin m, w_J (P.1 j) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_P) h_wJ_nn
            _ = ∏ j : Fin m, (((validJumpMonomersAtCube D_field sys (P.1 j)).card : ℝ) * w_J (P.1 j)) := by
                push_cast; rw [← Finset.prod_mul_distrib]
            _ ≤ ∏ j : Fin m, kpMonomerWeight c_wl β J f (P.1 j) := by
                refine Finset.prod_le_prod₀ (fun j _ => by
                  have := hf_nn (P.1 j).1; dsimp [w_J]; positivity) (fun j _ => ?_)
                exact validJumpMonomersAtCube_card_mul_le_kpMonomerWeight hR_cut hβ_nn hJ hf_nn
                  D_field sys h_geom hc_wl_cal (hM_sub (h_P1_mem j))
            _ = ((List.ofFn P.1).map (kpMonomerWeight c_wl β J f)).prod := by
                rw [List.map_ofFn, List.prod_ofFn]; rfl
            _ ≤ ∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p := by
                refine list_prod_le_finset_prod_of_le_one (List.ofFn P.1) (kpMonomerWeight c_wl β J f)
                  (fun p hp => ?_) (fun p hp => ?_)
                · rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩
                  exact (h_bounds (h_P1_mem j)).1
                · rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩
                  exact (h_bounds (h_P1_mem j)).2.2.1
        have h_D_prod : (∏ ϑ ∈ P.2, w_D ϑ) ≤ ∏ p ∈ P.2, kpMonomerWeight c_wl β J f p := by
          have hP2_sub : P.2 ⊆ M := Finset.mem_powerset.mp (Finset.mem_product.mp hP).2
          refine Finset.prod_le_prod₀ (fun ϑ _ => by dsimp [w_D]; have := hf_nn ϑ.1; positivity)
            (fun ϑ hϑ => (h_bounds (hP2_sub hϑ)).2.2.2)
        have h_union_prod :
            (∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p) *
              (∏ p ∈ P.2, kpMonomerWeight c_wl β J f p) ≤
              ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
          rw [← h_union_eq]
          refine finset_prod_mul_prod_le_prod_union_of_le_one _ _ _ (fun p hp => ?_) (fun p hp => ?_)
          · rw [h_union_eq] at hp; exact (h_bounds hp).1
          · rw [h_union_eq] at hp; exact (h_bounds hp).2.2.1
        calc (∑ γ ∈ ℱ_P, F_raw γ)
          _ = ∑ _γ ∈ ℱ_P, (((m.factorial : ℝ)⁻¹) * (∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ) :=
              Finset.sum_congr rfl h_F_eq
          _ = ((m.factorial : ℝ)⁻¹) * (((ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ ((m.factorial : ℝ)⁻¹) *
                ((∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p) *
                  ∏ p ∈ P.2, kpMonomerWeight c_wl β J f p) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul h_J_prod h_D_prod
                (Finset.prod_nonneg fun ϑ _ => by dsimp [w_D]; have := hf_nn ϑ.1; positivity)
                (Finset.prod_nonneg fun p hp => ?_)) (by positivity)
              exact (h_bounds (h_union_eq ▸ Finset.mem_union_left _ hp)).1
          _ ≤ ((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
              mul_le_mul_of_nonneg_left h_union_prod (by positivity)
    have h_card_PM : (P_M.card : ℝ) = ((M.card : ℝ) ^ m) * ((2 : ℝ) ^ M.card) := by
      dsimp [P_M]
      rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.card_powerset]
      push_cast
      rfl
    calc (∑ γ ∈ ℱ_m, F_raw γ)
      _ = ∑ P ∈ P_M, ∑ γ ∈ ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P), F_raw γ := by
          rw [Finset.sum_fiberwise_of_maps_to h_maps]
      _ ≤ ∑ _P ∈ P_M, (((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
          Finset.sum_le_sum h_P_bound
      _ = (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
            ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
          rw [Finset.sum_const, nsmul_eq_mul, h_card_PM, div_eq_mul_inv]
          ring
  have h_sum_m :
      (∑ m ∈ Finset.range (K_max + 1), (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card))) ≤
        (4 * Real.exp 1) ^ M.card := by
    rw [← Finset.sum_mul]
    calc (∑ m ∈ Finset.range (K_max + 1), (M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)
      _ ≤ Real.exp (M.card : ℝ) * ((2 : ℝ) ^ M.card) :=
          mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg M.card) (K_max + 1))
            (by positivity)
      _ = (2 * Real.exp 1) ^ M.card := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm]
      _ ≤ (4 * Real.exp 1) ^ M.card := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have := Real.exp_pos 1
          linarith
  have h_prod_M_nn : 0 ≤ ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
    Finset.prod_nonneg fun p hp => (h_bounds hp).1
  have h_raw_total : (∑ γ ∈ ℱ_M, F_raw γ) ≤
      (4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
    calc (∑ γ ∈ ℱ_M, F_raw γ)
      _ = ∑ m ∈ Finset.range (K_max + 1), ∑ γ ∈ ℱ_M.filter (fun γ => γ.1.length = m), F_raw γ := by
          rw [Finset.sum_fiberwise_of_maps_to h_len_mem]
      _ ≤ ∑ m ∈ Finset.range (K_max + 1),
            ((((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
              ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
          Finset.sum_le_sum h_m_bound
      _ = (∑ m ∈ Finset.range (K_max + 1),
            (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card))) *
            ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
          rw [← Finset.sum_mul]
      _ ≤ (4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
          mul_le_mul_of_nonneg_right h_sum_m h_prod_M_nn
  calc (∑ γ ∈ ℱ_M,
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
          Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)))
    _ ≤ ∑ γ ∈ ℱ_M, (C_col ^ M.card) * F_raw γ := Finset.sum_le_sum h_pt
    _ = (C_col ^ M.card) * ∑ γ ∈ ℱ_M, F_raw γ := by rw [← Finset.mul_sum]
    _ ≤ (C_col ^ M.card) * ((4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
        mul_le_mul_of_nonneg_left h_raw_total (pow_nonneg (Real.exp_nonneg _) _)
    _ = ∏ p ∈ M, (4 * Real.exp 1 * C_col * kpMonomerWeight c_wl β J f p) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        ring
    _ ≤ ∏ _p ∈ M, ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) := by
        refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => (h_bounds hp).2.1)
        have hp_nn := (h_bounds hp).1
        dsimp [C_col]
        positivity
    _ = ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card := by
        rw [Finset.prod_const]

/-- **Polymer Tree-Sum Bound and Kotecký–Preiss Criterion**
(Part II, Lemma 3.7 (`lem:peierls-bogoliubov`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equations `eq:w-micro-bound-m`–`eq:KP-sum-4-minus-m`):
Combining the pointwise activity bound `worldlinePolymerWeight_abs_le` with the
Klarner–Rota spanning-tree count and geometric series over multiplicity $m \ge 1$ for
$J \le J_{\mathrm{wl}}(\frac{1}{4}, \Delta_{\mathrm{RCA}})$, and summing over
base cubes $(r_0, A_0)$ whose collar contains check $c \in \mathcal{C}$ under
$J \le J_\star(\Delta_{\mathrm{RCA}}, C_{\mathrm{wl}}, c_{\mathrm{wl}}; \beta, f, R_{\mathrm{cut}})$,
yields both the native-collar Kotecký–Preiss bound (Part II, Proposition 3.10(ii) (`prop:tube-local-ursell-erasure`))
with size function $a(\gamma) = \frac{1}{8}|\mathrm{Supp}_{\mathrm{coll}}(\gamma)|$ (bounded by $\frac{1}{8}$)
and the spanning-support root-pinned polymer sum bound:
for every check $c \in \mathcal{C}$, the weighted sum of
`|worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| * Real.exp ((1 / 8 : ℝ) * |Supp_coll(γ)|)`
over all valid polymers $\gamma$ whose spanning support `worldlinePolymerSpanningSupport D_field sys C_RCA γ`
contains $c$ is at most $\frac{1}{32}\min(\beta, 1)$. -/
theorem worldline_polymer_tree_sum_and_kp_criterion
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (ν : PauliBitstringPair L q_code)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    (∀ u₁ : IdxCSS[L, q_code, m_max],
      Summable (fun γ : WorldlineDysonPolymer L q_code =>
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
          |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
            Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
        else 0) ∧
      (∑' γ : WorldlineDysonPolymer L q_code,
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
          |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
            Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
        else 0) ≤
        1 / 8) ∧
    (∀ c : IdxCSS[L, q_code, m_max],
      Summable (fun γ : WorldlineDysonPolymer L q_code =>
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
          |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
            Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
        else 0) ∧
      (∑' γ : WorldlineDysonPolymer L q_code,
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
          |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
            Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
        else 0) ≤
        (1 / 32 : ℝ) * min β 1) := by
  let w_exp (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
      Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
  have hw_exp_nn : ∀ γ, 0 ≤ w_exp γ := fun γ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  have h_min_β : min β 1 = 1 := min_eq_right (by linarith)
  have h_claim2 : ∀ c : IdxCSS[L, q_code, m_max],
      Summable (fun γ : WorldlineDysonPolymer L q_code =>
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then w_exp γ else 0) ∧
      (∑' γ : WorldlineDysonPolymer L q_code,
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then w_exp γ else 0) ≤
        (1 / 32 : ℝ) * min β 1 := by
    intro c
    let term_c (γ : WorldlineDysonPolymer L q_code) : ℝ :=
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then w_exp γ else 0
    have h_term_c_nn : ∀ γ, 0 ≤ term_c γ := fun γ => by
      dsimp [term_c]; split_ifs <;> [exact hw_exp_nn γ; exact le_refl 0]
    have h_fin_bound : ∀ ℱ : Finset (WorldlineDysonPolymer L q_code),
        (∑ γ ∈ ℱ, term_c γ) ≤ (1 / 32 : ℝ) * min β 1 := by
      intro ℱ
      let U := worldlineScaleCubeFinset L R_cut
      let S_cal : ℕ := 4 * (Nat.ceil C_RCA + 1) * (r_0 + 1) * R_cut
      let Δ_V : ℕ := kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA
      let ℱ_c := ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
        c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ)
      let P_act (M : Finset (ℕ × Finset (Box3D L))) : Prop :=
        ∃ γ ∈ ℱ_c, worldlinePolymerMonomers γ = M
      have hP_act : ∀ M ⊆ U, P_act M →
          KPIsConnectedSubgraph (KPScaleCubeOverlap sys C_RCA) M ∧
          (M.card * S_cal ≤ L_star →
            ∃ p₀ ∈ M, ∀ i : Fin 3,
              kpNatDist (anchorOfCube p₀.1 p₀.2 i).val (kpStaticCSSCheckAnchor c i).val ≤
                M.card * Δ_V) := by
        intro M hM_sub ⟨γ, hγ_mem, hγ_M⟩
        rcases Finset.mem_filter.mp hγ_mem with ⟨_, hγ_val, hc_supp⟩
        refine ⟨hγ_M ▸ hγ_val.2.2.2, fun hM_Lstar => ?_⟩
        have hM_nonempty : M.Nonempty := by
          rw [← hγ_M]
          rcases List.exists_mem_of_length_pos (l := γ.1) (by have := hγ_val.2.2.1.1; omega) with ⟨ξ, hξ⟩
          exact ⟨ξ.1, Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))⟩
        rcases Finset.mem_union.mp hc_supp with hc_col | hc_surf
        · unfold worldlinePolymerNativeCollar nativeCollarSupport at hc_col
          rw [hγ_M] at hc_col
          rcases Finset.mem_biUnion.mp hc_col with ⟨p₀, hp₀, hc_p₀⟩
          rcases mem_kpScaleCubeFinset_iff.mp (hM_sub hp₀) with ⟨hr₀, hA₀⟩
          have hp₀_sub_self : p₀.2 ⊆ boxCube (anchorOfCube p₀.1 p₀.2) p₀.1 := by
            rw [boxCube_anchorOfCube hA₀]
          have hr₀_le_S : p₀.1 ≤ M.card * S_cal := by
            have h1 : p₀.1 ≤ R_cut := le_trans (Finset.mem_Icc.mp hr₀).2 (Nat.min_le_left R_cut L)
            have h2 : R_cut ≤ 1 * S_cal := by
              dsimp [S_cal]
              rw [one_mul]
              exact Nat.le_mul_of_pos_left R_cut (by positivity)
            exact le_trans h1 (le_trans h2 (Nat.mul_le_mul_right S_cal hM_nonempty.card_pos))
          refine ⟨p₀, hp₀, fun i => ?_⟩
          exact kpNatDist_anchor_le_of_enclosing_and_collar hR_cut D_field sys
            (fun idx => (h_sys_checks idx).2.1) hC_RCA (hM_sub hp₀)
            (Finset.mem_Icc.mp hr₀).1 hr₀_le_S hr₀_le_S
            hp₀_sub_self hA₀ hp₀_sub_self hc_p₀ i
        · rcases exists_enclosing_boxCube_of_connected_kpScaleCubeFinset D_field sys
              (fun idx => (h_sys_checks idx).2.1) hC_RCA hM_sub hM_nonempty (hγ_M ▸ hγ_val.2.2.2) with
            ⟨x_enc, h_sub_enc⟩
          have h_ball : ∃ x0 : Box3D L, ∀ p ∈ worldlinePolymerMonomers γ, ∀ v ∈ p.2, v ∈ boxCube x0 L_star := by
            refine ⟨x_enc, fun p hp v hvp => ?_⟩
            have hv := h_sub_enc (Finset.mem_biUnion.mpr ⟨p, hγ_M ▸ hp, hvp⟩)
            rw [mem_boxCube] at hv ⊢
            intro i
            exact ⟨(hv i).1, lt_of_lt_of_le (hv i).2 (Nat.add_le_add_left hM_Lstar _)⟩
          have hc_bbox : c ∈ worldlinePolymerBoundingBoxCollar sys C_RCA γ :=
            (worldline_polymer_rca1_spanning_surface_collar_containment
              D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_cut hR_le hC_RCA h_scale_cal γ hγ_val h_ball).1 hc_surf
          let r_cap := min (M.card * S_cal) L
          have hr_cap_1 : 1 ≤ r_cap := by
            refine le_min ?_ (NeZero.pos L)
            have h1 : 1 ≤ S_cal :=
              Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) (Nat.succ_pos _)) (Nat.succ_pos _)) hR_cut
            exact le_trans h1 (Nat.le_mul_of_pos_left S_cal hM_nonempty.card_pos)
          have hr_cap_L : r_cap ≤ L := Nat.min_le_right _ L
          have h_enc_cap : HasEnclosingPolymerBall γ r_cap := by
            refine ⟨x_enc, fun v hv => ?_⟩
            rcases Finset.mem_biUnion.mp hv with ⟨p, hp, hvp⟩
            have hv_enc := h_sub_enc (Finset.mem_biUnion.mpr ⟨p, hγ_M ▸ hp, hvp⟩)
            rw [mem_boxCube] at hv_enc ⊢
            intro i
            have h1 : (v i).val < (x_enc i).val + M.card * S_cal := (hv_enc i).2
            have h2 := (v i).isLt
            dsimp [r_cap]
            exact ⟨(hv_enc i).1, by omega⟩
          have h_ex_diam : ∃ r ≤ L, 1 ≤ r ∧ HasEnclosingPolymerBall γ r :=
            ⟨r_cap, hr_cap_L, hr_cap_1, h_enc_cap⟩
          let r_diam := worldlinePolymerDiameter γ
          have hr_diam_eq : r_diam = Nat.find h_ex_diam := dif_pos h_ex_diam
          have hr_diam_spec := Nat.find_spec h_ex_diam
          have hr_diam_1 : 1 ≤ r_diam := hr_diam_eq ▸ hr_diam_spec.2.1
          have hr_diam_le : r_diam ≤ M.card * S_cal := by
            refine le_trans ?_ (Nat.min_le_left (M.card * S_cal) L)
            rw [hr_diam_eq]
            exact Nat.find_min' h_ex_diam ⟨hr_cap_L, hr_cap_1, h_enc_cap⟩
          have h_enc_diam : HasEnclosingPolymerBall γ r_diam := hr_diam_eq ▸ hr_diam_spec.2.2
          let x0_diam := Classical.choose h_enc_diam
          have hx0_diam_sub : worldlinePolymerCubeUnion γ ⊆ boxCube x0_diam r_diam :=
            Classical.choose_spec h_enc_diam
          have h_bbox_eq : worldlinePolymerBoundingBox γ = boxCube x0_diam r_diam :=
            dif_pos h_enc_diam
          have hc_col_diam : c ∈ rcaCollarChecks sys C_RCA r_diam (boxCube x0_diam r_diam) := by
            unfold worldlinePolymerBoundingBoxCollar at hc_bbox
            rwa [h_bbox_eq] at hc_bbox
          rcases hM_nonempty with ⟨p₀, hp₀⟩
          have hp₀_sub : p₀.2 ⊆ boxCube x0_diam r_diam := fun x hx =>
            hx0_diam_sub (Finset.mem_biUnion.mpr ⟨p₀, hγ_M ▸ hp₀, hx⟩)
          have hB_cube : boxCube x0_diam r_diam ∈ boxCubes 3 L r_diam :=
            Finset.mem_image_of_mem _ (Finset.mem_univ x0_diam)
          refine ⟨p₀, hp₀, fun i => ?_⟩
          exact kpNatDist_anchor_le_of_enclosing_and_collar hR_cut D_field sys
            (fun idx => (h_sys_checks idx).2.1) hC_RCA (hM_sub hp₀)
            hr_diam_1 hr_diam_le hr_diam_le hp₀_sub hB_cube (Finset.Subset.refl _) hc_col_diam i
      let Pow_act := U.powerset.filter (fun M => 1 ≤ M.card ∧ P_act M)
      have h_maps_M : ∀ γ ∈ ℱ_c, worldlinePolymerMonomers γ ∈ Pow_act := by
        intro γ hγ
        rcases Finset.mem_filter.mp hγ with ⟨_, hγ_val, _⟩
        have hM_sub : worldlinePolymerMonomers γ ⊆ U := hγ_val.1
        have hM_pos : 1 ≤ (worldlinePolymerMonomers γ).card := by
          rcases List.exists_mem_of_length_pos (l := γ.1) (by have := hγ_val.2.2.1.1; omega) with ⟨ξ, hξ⟩
          exact Finset.card_pos.mpr
            ⟨ξ.1, Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hM_sub, hM_pos, γ, hγ, rfl⟩
      have h_fib_le : ∀ M ∈ Pow_act,
          (∑ γ ∈ ℱ_c.filter (fun γ => worldlinePolymerMonomers γ = M), w_exp γ) ≤
            ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card := by
        intro M hM
        have hM_sub : M ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hM).1
        have h_sub_filt : ℱ_c.filter (fun γ => worldlinePolymerMonomers γ = M) ⊆
            ℱ.filter (fun γ => IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              worldlinePolymerMonomers γ = M) := by
          intro γ hγ
          rcases Finset.mem_filter.mp hγ with ⟨hγ_c, hγ_M⟩
          rcases Finset.mem_filter.mp hγ_c with ⟨hγ_ℱ, hγ_val, _⟩
          exact Finset.mem_filter.mpr ⟨hγ_ℱ, hγ_val, hγ_M⟩
        exact le_trans
          (Finset.sum_le_sum_of_subset_of_nonneg h_sub_filt (fun γ _ _ => hw_exp_nn γ))
          (sum_validPolymers_with_monomers_le hR_cut hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
            hΔ_RCA hβ hJ hf_nn hf_le_one h_sum_pos hJ_wl h_thresh D_field sys h_sys_checks
            h_geom V hV_norm d_loc hd_scale ν σ ℱ hM_sub)
      have h_maps_n : ∀ M ∈ Pow_act, M.card ∈ Finset.Icc 1 U.card := by
        intro M hM
        rcases Finset.mem_filter.mp hM with ⟨hM_pow, hM_pos, _⟩
        exact Finset.mem_Icc.mpr ⟨hM_pos, Finset.card_le_card (Finset.mem_powerset.mp hM_pow)⟩
      have h_n_bound : ∀ n ∈ Finset.Icc 1 U.card,
          (∑ M ∈ Pow_act.filter (fun M => M.card = n),
            ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card) ≤ (1 / 64 : ℝ) ^ n := by
        intro n hn
        have hn_pos : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have h_filt_eq : Pow_act.filter (fun M => M.card = n) =
            U.powerset.filter (fun M => M.card = n ∧ P_act M) := by
          ext M
          simp only [Pow_act, Finset.mem_filter]
          constructor
          · rintro ⟨⟨h1, _, h3⟩, h4⟩; exact ⟨h1, h4, h3⟩
          · rintro ⟨h1, h4, h3⟩; exact ⟨⟨h1, h4 ▸ hn_pos, h3⟩, h4⟩
        have h_card_n := card_activeMonomerSets_of_card_le hR_cut D_field sys h_sys_checks h_geom
          hC_RCA h_scale_cal.2.2 (kpStaticCSSCheckAnchor c) P_act hP_act hn_pos
        calc (∑ M ∈ Pow_act.filter (fun M => M.card = n),
              ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card)
          _ = ∑ _M ∈ U.powerset.filter (fun M => M.card = n ∧ P_act M),
              ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ n := by
              rw [h_filt_eq]
              refine Finset.sum_congr rfl fun M hM => by rw [(Finset.mem_filter.mp hM).2.1]
          _ = ((U.powerset.filter (fun M => M.card = n ∧ P_act M)).card : ℝ) *
              (((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ n) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Real.exp (12 * (Δ_V : ℝ))) ^ n *
              (((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ n) :=
              mul_le_mul_of_nonneg_right h_card_n (by positivity)
          _ = ((1 / 64 : ℝ) * (Real.exp (12 * (Δ_V : ℝ)) * Real.exp (-12 * (Δ_V : ℝ)))) ^ n := by
              rw [← mul_pow]; ring
          _ = (1 / 64 : ℝ) ^ n := by
              rw [← Real.exp_add]
              have h_z : (12 : ℝ) * (Δ_V : ℝ) + -12 * (Δ_V : ℝ) = 0 := by ring
              rw [h_z, Real.exp_zero, mul_one]
      calc (∑ γ ∈ ℱ, term_c γ)
        _ = ∑ γ ∈ ℱ_c, w_exp γ := by
            dsimp [term_c, ℱ_c]
            rw [Finset.sum_filter]
            exact Finset.sum_congr rfl fun γ _ => by split_ifs <;> rfl
        _ = ∑ M ∈ Pow_act, ∑ γ ∈ ℱ_c.filter (fun γ => worldlinePolymerMonomers γ = M), w_exp γ := by
            rw [Finset.sum_fiberwise_of_maps_to h_maps_M]
        _ ≤ ∑ M ∈ Pow_act, ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card :=
            Finset.sum_le_sum h_fib_le
        _ = ∑ n ∈ Finset.Icc 1 U.card,
              ∑ M ∈ Pow_act.filter (fun M => M.card = n),
                ((1 / 64 : ℝ) * Real.exp (-12 * (Δ_V : ℝ))) ^ M.card := by
            rw [Finset.sum_fiberwise_of_maps_to h_maps_n]
        _ ≤ ∑ n ∈ Finset.Icc 1 U.card, (1 / 64 : ℝ) ^ n :=
            Finset.sum_le_sum h_n_bound
        _ ≤ 2 * (1 / 64 : ℝ) :=
            sum_Icc_pow_le_two_mul (by norm_num) (by norm_num) U.card
        _ = (1 / 32 : ℝ) * min β 1 := by
            rw [h_min_β]; norm_num
    have h_summable : Summable term_c := summable_of_sum_le h_term_c_nn h_fin_bound
    exact ⟨h_summable, le_of_tendsto' h_summable.hasSum h_fin_bound⟩
  refine ⟨fun u₁ => ?_, h_claim2⟩
  have h_le_c : ∀ γ : WorldlineDysonPolymer L q_code,
      (if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then w_exp γ else 0) ≤
      (if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          u₁ ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then w_exp γ else 0) := by
    intro γ
    split_ifs with h₁ h₂
    · exact le_refl _
    · exfalso
      exact h₂ ⟨h₁.1, Finset.mem_union_left _ h₁.2⟩
    · exact hw_exp_nn γ
    · exact le_refl 0
  have h_sum_u1 : Summable (fun γ : WorldlineDysonPolymer L q_code =>
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then w_exp γ else 0) :=
    Summable.of_nonneg_of_le
      (fun γ => by split_ifs <;> [exact hw_exp_nn γ; exact le_refl 0])
      h_le_c (h_claim2 u₁).1
  refine ⟨h_sum_u1, ?_⟩
  calc (∑' γ : WorldlineDysonPolymer L q_code,
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then w_exp γ else 0)
    _ ≤ ∑' γ : WorldlineDysonPolymer L q_code,
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            u₁ ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then w_exp γ else 0 :=
        h_sum_u1.tsum_le_tsum h_le_c (h_claim2 u₁).1
    _ ≤ (1 / 32 : ℝ) * min β 1 := (h_claim2 u₁).2
    _ ≤ 1 / 8 := by rw [h_min_β]; norm_num

private lemma mem_worldlineClusterMonomers_iff
    {L q_code : ℕ} {K : WorldlineUrsellCluster L q_code} {p : ℕ × Finset (Box3D L)} :
    p ∈ worldlineClusterMonomers K ↔ ∃ γ ∈ K, p ∈ worldlinePolymerMonomers γ := by
  induction K with
  | nil =>
    simp [worldlineClusterMonomers]
  | cons hd tl ih =>
    simp only [worldlineClusterMonomers, List.foldr_cons, Finset.mem_union, List.mem_cons]
    constructor
    · rintro (h_hd | h_tl)
      · exact ⟨hd, Or.inl rfl, h_hd⟩
      · rcases ih.mp h_tl with ⟨γ, hγ, hp⟩
        exact ⟨γ, Or.inr hγ, hp⟩
    · rintro ⟨γ, rfl | hγ, hp⟩
      · exact Or.inl hp
      · exact Or.inr (ih.mpr ⟨γ, hγ, hp⟩)

private lemma mem_worldlineClusterSpanningSurface_iff
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    {K : WorldlineUrsellCluster L q_code} {c : IdxCSS[L, q_code, m_max]} :
    c ∈ worldlineClusterSpanningSurface D_field sys C_RCA K ↔
      ∃ γ ∈ K, c ∈ worldlinePolymerSpanningSurface D_field sys C_RCA γ := by
  induction K with
  | nil =>
    simp [worldlineClusterSpanningSurface]
  | cons hd tl ih =>
    simp only [worldlineClusterSpanningSurface, List.foldr_cons, Finset.mem_union, List.mem_cons]
    constructor
    · rintro (h_hd | h_tl)
      · exact ⟨hd, Or.inl rfl, h_hd⟩
      · rcases ih.mp h_tl with ⟨γ, hγ, hc⟩
        exact ⟨γ, Or.inr hγ, hc⟩
    · rintro ⟨γ, rfl | hγ, hc⟩
      · exact Or.inl hc
      · exact Or.inr (ih.mpr ⟨γ, hγ, hc⟩)

private lemma exists_mem_worldlinePolymerSpanningSupport_of_cluster_footprint
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    {K : WorldlineUrsellCluster L q_code}
    {fp : WorldlineUrsellFootprint L q_code m_max}
    (h_mon : worldlineClusterMonomers K = fp.1)
    (h_surf : worldlineClusterSpanningSurface D_field sys C_RCA K = fp.2)
    {c : IdxCSS[L, q_code, m_max]}
    (hc : c ∈ worldlineUrsellSpanningSupport sys C_RCA fp) :
    ∃ γ ∈ K, c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ := by
  unfold worldlineUrsellSpanningSupport at hc
  rcases Finset.mem_union.mp hc with hc_col | hc_surf
  · rw [← h_mon] at hc_col
    unfold nativeCollarSupport at hc_col
    rcases Finset.mem_biUnion.mp hc_col with ⟨p, hp_cluster, hc_p⟩
    rcases mem_worldlineClusterMonomers_iff.mp hp_cluster with ⟨γ, hγ_K, hp_γ⟩
    refine ⟨γ, hγ_K, Finset.mem_union_left _ ?_⟩
    unfold worldlinePolymerNativeCollar nativeCollarSupport
    exact Finset.mem_biUnion.mpr ⟨p, hp_γ, hc_p⟩
  · rw [← h_surf] at hc_surf
    rcases (mem_worldlineClusterSpanningSurface_iff D_field sys C_RCA).mp hc_surf with ⟨γ, hγ_K, hc_γ⟩
    exact ⟨γ, hγ_K, Finset.mem_union_right _ hc_γ⟩

private def pinnedClusterAbsWeight
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (c : IdxCSS[L, q_code, m_max])
    (K : WorldlineUrsellCluster L q_code) : ℝ :=
  if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
      ∃ γ ∈ K, c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
    |worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ|
  else 0

private lemma pinnedClusterAbsWeight_nonneg
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (c : IdxCSS[L, q_code, m_max])
    (K : WorldlineUrsellCluster L q_code) :
    0 ≤ pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K := by
  unfold pinnedClusterAbsWeight
  split_ifs
  · exact abs_nonneg _
  · exact le_refl 0

private lemma sum_pinnedClusterAbsWeight_le_of_kp
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hβ_pos : 0 < β)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_kp :
      (∀ u₁ : IdxCSS[L, q_code, m_max],
        Summable (fun γ : WorldlineDysonPolymer L q_code =>
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ∧
        (∑' γ : WorldlineDysonPolymer L q_code,
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ≤
          1 / 8) ∧
      (∀ c : IdxCSS[L, q_code, m_max],
        Summable (fun γ : WorldlineDysonPolymer L q_code =>
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ∧
        (∑' γ : WorldlineDysonPolymer L q_code,
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ≤
          (1 / 32 : ℝ) * min β 1))
    (c : IdxCSS[L, q_code, m_max])
    (ℱ : Finset (WorldlineUrsellCluster L q_code)) :
    (∑ K ∈ ℱ, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) ≤
      (1 / 32 : ℝ) * min β 1 := by
  let P₀ : Finset (WorldlineDysonPolymer L q_code) :=
    (ℱ.biUnion List.toFinset).filter (IsValidWorldlinePolymer D_field sys C_RCA R_cut)
  let w (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|
  let a (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    (1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ)
  let incompat := ArePolymersIncompatible sys C_RCA
  have hw : ∀ γ ∈ P₀, 0 ≤ w γ := fun _ _ => abs_nonneg _
  have ha : ∀ γ ∈ P₀, 0 ≤ a γ := fun _ _ => mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have h_kp_a : ∀ γ₀ ∈ P₀, (∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ)) ≤ a γ₀ := by
    intro γ₀ _
    have h_sub : P₀.filter (incompat γ₀) ⊆
        (worldlinePolymerNativeCollar sys C_RCA γ₀).biUnion
          (fun u₁ => P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ)) := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hγ_P₀, h_inc⟩
      rcases Finset.not_disjoint_iff.mp h_inc with ⟨u₁, hu₁_₀, hu₁_γ⟩
      exact Finset.mem_biUnion.mpr ⟨u₁, hu₁_₀, Finset.mem_filter.mpr ⟨hγ_P₀, hu₁_γ⟩⟩
    have h_u₁_le : ∀ u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ₀,
        (∑ γ ∈ P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ), w γ * Real.exp (a γ)) ≤ 1 / 8 := by
      intro u₁ _
      let f_u₁ := fun γ : WorldlineDysonPolymer L q_code =>
        if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
            u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
          w γ * Real.exp (a γ)
        else 0
      have h_eq : ∀ γ ∈ P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ),
          w γ * Real.exp (a γ) = f_u₁ γ := by
        intro γ hγ
        rcases Finset.mem_filter.mp hγ with ⟨hγ_P₀, hu₁⟩
        have h_val : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ := (Finset.mem_filter.mp hγ_P₀).2
        dsimp [f_u₁]; rw [if_pos ⟨h_val, hu₁⟩]
      rw [Finset.sum_congr rfl h_eq]
      exact le_trans (Summable.sum_le_tsum _ (fun γ _ => by split_ifs <;> positivity) (h_kp.1 u₁).1)
        (h_kp.1 u₁).2
    calc (∑ γ ∈ P₀.filter (incompat γ₀), w γ * Real.exp (a γ))
      _ ≤ ∑ γ ∈ (worldlinePolymerNativeCollar sys C_RCA γ₀).biUnion
            (fun u₁ => P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ)),
            w γ * Real.exp (a γ) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
      _ ≤ ∑ u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ₀,
            ∑ γ ∈ P₀.filter (fun γ => u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ),
              w γ * Real.exp (a γ) :=
          sum_biUnion_le_of_nonneg _ _ (fun _ => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))
      _ ≤ ∑ _u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ₀, (1 / 8 : ℝ) :=
          Finset.sum_le_sum h_u₁_le
      _ = a γ₀ := by simp [a, mul_comm]
  let T_c := P₀.filter (fun γ => c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ)
  have h_root_sum : (∑ γ₀ ∈ T_c, w γ₀ * Real.exp (a γ₀)) ≤ (1 / 32 : ℝ) * min β 1 := by
    let f_c := fun γ : WorldlineDysonPolymer L q_code =>
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
          c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
        w γ * Real.exp (a γ)
      else 0
    have h_eq : ∀ γ ∈ T_c, w γ * Real.exp (a γ) = f_c γ := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hγ_P₀, hc_γ⟩
      have h_val : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ := (Finset.mem_filter.mp hγ_P₀).2
      dsimp [f_c]; rw [if_pos ⟨h_val, hc_γ⟩]
    rw [Finset.sum_congr rfl h_eq]
    exact le_trans (Summable.sum_le_tsum _ (fun γ _ => by split_ifs <;> positivity) (h_kp.2 c).1)
      (h_kp.2 c).2
  have h_prod_get : ∀ K : List (WorldlineDysonPolymer L q_code),
      |(K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod| =
        ∏ i : Fin K.length, w (K.get i) := by
    intro K
    have h_abs : |(K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod| =
        (K.map w).prod := by
      induction K with
      | nil => simp
      | cons hd tl ih => simp [List.map_cons, List.prod_cons, abs_mul, ih, w]
    have h_ofFn : K.map w = List.ofFn (fun i : Fin K.length => w (K.get i)) :=
      List.ext_get (by simp) (by simp)
    rw [h_abs, h_ofFn, List.prod_ofFn]
  let tupleTerm (p : ℕ) (r : Fin p) (t : Fin p → WorldlineDysonPolymer L q_code) : ℝ :=
    if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA (t r) then
      ∑ f ∈ (arborescenceForests Finset.univ {r}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin p)) \ {r}, incompat (t (f v)) (t v)),
        ∏ v : Fin p, w (t v)
    else 0
  let tupleBound (p : ℕ) (t : Fin p → WorldlineDysonPolymer L q_code) : ℝ :=
    ((p.factorial : ℝ)⁻¹) * ∑ r : Fin p, tupleTerm p r t
  have h_term_nn : ∀ (p : ℕ) (r : Fin p) (t : Fin p → WorldlineDysonPolymer L q_code),
      0 ≤ tupleTerm p r t := by
    intro p r t; dsimp [tupleTerm]
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => abs_nonneg _
    · exact le_refl 0
  have h_bound_nn : ∀ (p : ℕ) (t : Fin p → WorldlineDysonPolymer L q_code), 0 ≤ tupleBound p t :=
    fun p t => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun r _ => h_term_nn p r t)
  have h_K_le_tuple : ∀ K : WorldlineUrsellCluster L q_code,
      pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K ≤
        tupleBound K.length (fun i => K.get i) := by
    intro K
    unfold pinnedClusterAbsWeight
    split_ifs with h_cond
    · rcases h_cond with ⟨h_val, γ₀, hγ₀_K, hc_γ₀⟩
      have hp : 0 < K.length := List.length_pos_iff.mpr h_val.1
      rcases List.mem_iff_get.mp hγ₀_K with ⟨r₀, rfl⟩
      unfold worldlineClusterUrsellWeight ursellConnectedGraphCoeff
      rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), h_prod_get K, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
      have h_penrose := abs_sum_connGraphs_le_arborescenceForests hp
        (PolymerClusterOverlap sys C_RCA K) (fun u v h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩) r₀
      have h_sub_arb : (arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v : Fin K.length, v ≠ r₀ → PolymerClusterOverlap sys C_RCA K (f v) v) ⊆
          (arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v)) := by
        intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hf_arb, hf_ov⟩
        refine Finset.mem_filter.mpr ⟨hf_arb, fun v hv => ?_⟩
        have hv_ne : v ≠ r₀ := by simpa using hv
        exact (hf_ov v hv_ne).2
      have h_card_le : (((arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v : Fin K.length, v ≠ r₀ → PolymerClusterOverlap sys C_RCA K (f v) v)).card : ℝ) ≤
          (((arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v))).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card h_sub_arb)
      have h_prod_nn : 0 ≤ ∏ i : Fin K.length, w (K.get i) := Finset.prod_nonneg fun _ _ => abs_nonneg _
      have h_r₀_eq : (((arborescenceForests Finset.univ {r₀}).filter
          (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v))).card : ℝ) *
          (∏ i : Fin K.length, w (K.get i)) =
          tupleTerm K.length r₀ (fun i => K.get i) := by
        change _ = if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA (K.get r₀) then
          ∑ f ∈ (arborescenceForests Finset.univ {r₀}).filter
              (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v)),
            ∏ v : Fin K.length, w (K.get v)
        else 0
        rw [if_pos hc_γ₀, Finset.sum_const, nsmul_eq_mul]
      calc |∑ G ∈ (Finset.univ.filter (fun e : Fin K.length × Fin K.length =>
              e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)).powerset.filter
              (fun G => KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
            ((-1 : ℝ) ^ G.card)| * (∏ i : Fin K.length, w (K.get i))
        _ ≤ (((arborescenceForests Finset.univ {r₀}).filter
            (fun f => ∀ v ∈ (Finset.univ : Finset (Fin K.length)) \ {r₀}, incompat (K.get (f v)) (K.get v))).card : ℝ) *
            (∏ i : Fin K.length, w (K.get i)) :=
            mul_le_mul_of_nonneg_right (le_trans h_penrose h_card_le) h_prod_nn
        _ = tupleTerm K.length r₀ (fun i => K.get i) := h_r₀_eq
        _ ≤ ∑ r : Fin K.length, tupleTerm K.length r (fun i => K.get i) :=
            Finset.single_le_sum (fun r _ => h_term_nn K.length r _) (Finset.mem_univ r₀)
    · exact h_bound_nn K.length _
  let P := ℱ.sup List.length
  let ℱ_val := ℱ.filter (fun K => IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K)
  have h_sum_val : (∑ K ∈ ℱ, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) =
      ∑ K ∈ ℱ_val, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun K hK h_not => ?_
    have h_nv : ¬IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K :=
      fun hv => h_not (Finset.mem_filter.mpr ⟨hK, hv⟩)
    unfold pinnedClusterAbsWeight
    rw [if_neg (fun h => h_nv h.1)]
  have h_part_P : ℱ_val = (Finset.Icc 1 P).biUnion (fun p => ℱ_val.filter (fun K => K.length = p)) := by
    ext K; simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro hK
      rcases Finset.mem_filter.mp hK with ⟨hK_ℱ, hK_val⟩
      have hp_pos : 1 ≤ K.length := List.length_pos_iff.mpr hK_val.1
      have hp_le : K.length ≤ P := Finset.le_sup (f := List.length) hK_ℱ
      exact ⟨K.length, ⟨hp_pos, hp_le⟩, hK, rfl⟩
    · rintro ⟨_, _, hK, _⟩; exact hK
  have h_disj_P : Set.PairwiseDisjoint ↑(Finset.Icc 1 P) (fun p => ℱ_val.filter (fun K => K.length = p)) := by
    intro p₁ _ p₂ _ h_ne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro K h₁ h₂
    exact h_ne ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
  let γ_def : WorldlineDysonPolymer L q_code := ([], ∅)
  let toTuple (p : ℕ) (K : WorldlineUrsellCluster L q_code) : Fin p → WorldlineDysonPolymer L q_code :=
    if hp : K.length = p then fun i => K.get (i.cast hp.symm) else fun _ => γ_def
  have h_tuple_cast : ∀ (K : WorldlineUrsellCluster L q_code) (p : ℕ) (hp : K.length = p),
      tupleBound K.length (fun i => K.get i) = tupleBound p (toTuple p K) := by
    intro K p hp; subst hp
    have h_eq : (fun i : Fin K.length => K.get i) = toTuple K.length K := by
      dsimp [toTuple]; rw [dif_pos rfl]
    rw [h_eq]
  have h_p_sum_le : ∀ p ∈ Finset.Icc 1 P,
      (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
        pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) ≤
      ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
    intro p hp_Icc
    have hp_pos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hp_Icc).1
    have h_inj_p : Set.InjOn (toTuple p) (ℱ_val.filter (fun K => K.length = p)) := by
      intro K₁ hK₁ K₂ hK₂ h_eq
      have hp₁ : K₁.length = p := (Finset.mem_filter.mp hK₁).2
      have hp₂ : K₂.length = p := (Finset.mem_filter.mp hK₂).2
      refine List.ext_get (hp₁.trans hp₂.symm) fun n hn₁ hn₂ => ?_
      have h_i := congrFun h_eq ⟨n, hp₁ ▸ hn₁⟩
      dsimp [toTuple] at h_i
      rw [dif_pos hp₁, dif_pos hp₂] at h_i
      exact h_i
    have h_maps_p : ∀ K ∈ ℱ_val.filter (fun K => K.length = p),
        toTuple p K ∈ Fintype.piFinset (fun _ : Fin p => P₀) := by
      intro K hK
      rcases Finset.mem_filter.mp hK with ⟨hK_val, hp_K⟩
      rcases Finset.mem_filter.mp hK_val with ⟨hK_ℱ, h_val⟩
      rw [Fintype.mem_piFinset]
      intro i
      dsimp [toTuple]; rw [dif_pos hp_K]
      have h_mem_K : K.get (i.cast hp_K.symm) ∈ K := List.get_mem K _
      exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨K, hK_ℱ, List.mem_toFinset.mpr h_mem_K⟩,
        h_val.2.1 _ h_mem_K⟩
    have h_step1 : (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
        pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) ≤
        ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleBound p t := by
      calc (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
            pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K)
        _ ≤ ∑ K ∈ ℱ_val.filter (fun K => K.length = p), tupleBound p (toTuple p K) := by
            refine Finset.sum_le_sum fun K hK => ?_
            rw [← h_tuple_cast K p (Finset.mem_filter.mp hK).2]
            exact h_K_le_tuple K
        _ = ∑ t ∈ (ℱ_val.filter (fun K => K.length = p)).image (toTuple p), tupleBound p t :=
            (Finset.sum_image h_inj_p).symm
        _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleBound p t :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr h_maps_p)
              (fun t _ _ => h_bound_nn p t)
    have h_r_bound : ∀ r : Fin p,
        (∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleTerm p r t) ≤
          (((p - 1).factorial : ℝ)) * ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
      intro r
      have h_disj_r : Disjoint ({r} : Finset (Fin p)) (Finset.univ \ {r}) :=
        Finset.disjoint_singleton_left.mpr (by simp)
      have h_pi_eq : Fintype.piFinset (fun _ : Fin p => P₀) =
          Fintype.piFinset (fun v : Fin p =>
            if v ∈ ({r} : Finset (Fin p)) then P₀ else if v ∈ Finset.univ \ {r} then P₀ else {γ_def}) := by
        congr 1; funext v
        by_cases hvr : v = r <;> [subst hvr; skip] <;> simp [*]
      rw [h_pi_eq, piFinset_split_sum {r} (Finset.univ \ {r}) h_disj_r (fun _ => P₀) (fun _ => P₀) (fun _ => γ_def)]
      have h_KR_le : ∀ K_R ∈ Fintype.piFinset (fun v : Fin p => if v ∈ ({r} : Finset (Fin p)) then P₀ else {γ_def}),
          (∑ t ∈ Fintype.piFinset (fun v : Fin p => if v ∈ Finset.univ \ {r} then P₀ else {K_R v}),
            tupleTerm p r t) ≤
          if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA (K_R r) then
            (((p - 1).factorial : ℝ)) * (w (K_R r) * kpForestWeight P₀ incompat w p [K_R r])
          else 0 := by
        intro K_R hK_R
        have h_tr_eq : ∀ t ∈ Fintype.piFinset (fun v : Fin p => if v ∈ Finset.univ \ {r} then P₀ else {K_R v}),
            tupleTerm p r t =
              if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA (K_R r) then
                ∑ f ∈ (arborescenceForests Finset.univ {r}).filter
                    (fun f => ∀ v ∈ (Finset.univ : Finset (Fin p)) \ {r}, incompat (t (f v)) (t v)),
                  w (K_R r) * ∏ v ∈ Finset.univ \ {r}, w (t v)
              else 0 := by
          intro t ht
          have htr : t r = K_R r := by
            have h := Fintype.mem_piFinset.mp ht r
            simpa using h
          dsimp [tupleTerm]; rw [htr]
          split_ifs with hc_r
          · refine Finset.sum_congr rfl fun f _ => ?_
            have h_er : (Finset.univ : Finset (Fin p)).erase r = Finset.univ \ {r} := by
              ext v; simp
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), htr, h_er]
          · rfl
        rw [Finset.sum_congr rfl h_tr_eq]
        by_cases hc_r : c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA (K_R r)
        · simp only [hc_r, if_true]
          have h_fps_eq : (∑ t ∈ Fintype.piFinset (fun v : Fin p => if v ∈ Finset.univ \ {r} then P₀ else {K_R v}),
              ∑ f ∈ (arborescenceForests Finset.univ {r}).filter
                  (fun f => ∀ v ∈ (Finset.univ : Finset (Fin p)) \ {r}, incompat (t (f v)) (t v)),
                w (K_R r) * ∏ v ∈ Finset.univ \ {r}, w (t v)) =
              w (K_R r) * forestPolymerSum P₀ incompat w Finset.univ {r} K_R := by
            unfold forestPolymerSum
            simp only [Finset.sum_filter, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun t _ => ?_
            split_ifs <;> ring
          rw [h_fps_eq]
          have h_fps_le := forestPolymerSum_le_kpForestWeight P₀ incompat hw p Finset.univ [r]
            (by simp) (List.nodup_singleton r) (Finset.subset_univ _) K_R
          have h_r_toFinset : ([r] : List (Fin p)).toFinset = {r} := rfl
          have h_sdiff_card : ((Finset.univ : Finset (Fin p)) \ {r}).card = p - 1 := by
            have h_er : (Finset.univ : Finset (Fin p)) \ {r} = Finset.univ.erase r := by ext v; simp
            rw [h_er, Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
          rw [h_r_toFinset, h_sdiff_card] at h_fps_le
          simpa [List.map_singleton, mul_left_comm, mul_assoc] using
            mul_le_mul_of_nonneg_left h_fps_le (abs_nonneg _)
        · simp [hc_r]
      have h_bij_r : (∑ K_R ∈ Fintype.piFinset (fun v : Fin p => if v ∈ ({r} : Finset (Fin p)) then P₀ else {γ_def}),
          if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA (K_R r) then
            (((p - 1).factorial : ℝ)) * (w (K_R r) * kpForestWeight P₀ incompat w p [K_R r])
          else 0) =
          (((p - 1).factorial : ℝ)) * ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
        have h_bij : (∑ K_R ∈ Fintype.piFinset (fun v : Fin p => if v ∈ ({r} : Finset (Fin p)) then P₀ else {γ_def}),
            if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA (K_R r) then
              (((p - 1).factorial : ℝ)) * (w (K_R r) * kpForestWeight P₀ incompat w p [K_R r])
            else 0) =
            ∑ γ₀ ∈ P₀, if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ₀ then
              (((p - 1).factorial : ℝ)) * (w γ₀ * kpForestWeight P₀ incompat w p [γ₀])
            else 0 := by
          refine Finset.sum_bij (fun K_R _ => K_R r)
            (fun K_R hK_R => by simpa using (Fintype.mem_piFinset.mp hK_R) r) ?_ ?_ (fun _ _ => rfl)
          · intro K₁ hK₁ K₂ hK₂ h_eq; funext v
            rcases eq_or_ne v r with rfl | hvr
            · exact h_eq
            · have h₁ := (Fintype.mem_piFinset.mp hK₁) v
              have h₂ := (Fintype.mem_piFinset.mp hK₂) v
              simp only [Finset.mem_singleton, hvr, if_false] at h₁ h₂
              exact h₁.trans h₂.symm
          · intro γ₀ hγ₀
            refine ⟨Function.update (fun _ => γ_def) r γ₀, Fintype.mem_piFinset.mpr fun v => ?_, by simp⟩
            rcases eq_or_ne v r with rfl | hvr <;> simp [*]
        rw [h_bij, Finset.mul_sum]
        symm
        calc (∑ i ∈ T_c, (((p - 1).factorial : ℝ)) * (w i * kpForestWeight P₀ incompat w p [i]))
          _ = ∑ i ∈ T_c, if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA i then
                (((p - 1).factorial : ℝ)) * (w i * kpForestWeight P₀ incompat w p [i])
              else 0 := Finset.sum_congr rfl fun i hi => (if_pos (Finset.mem_filter.mp hi).2).symm
          _ = ∑ γ₀ ∈ P₀, if c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ₀ then
                (((p - 1).factorial : ℝ)) * (w γ₀ * kpForestWeight P₀ incompat w p [γ₀])
              else 0 := by
              refine Finset.sum_subset (Finset.filter_subset _ P₀) fun γ₀ hγ₀ h_not => ?_
              rw [if_neg (fun hc => h_not (Finset.mem_filter.mpr ⟨hγ₀, hc⟩))]
      exact le_trans (Finset.sum_le_sum h_KR_le) (le_of_eq h_bij_r)
    have h_fac_p : ((p.factorial : ℝ)⁻¹) * ((p : ℝ) * (((p - 1).factorial : ℝ))) = 1 := by
      have h_nat : p * (p - 1).factorial = p.factorial := Nat.mul_factorial_pred (Nat.ne_of_gt hp_pos)
      have h_cast : (p : ℝ) * (((p - 1).factorial : ℝ)) = (p.factorial : ℝ) := by exact_mod_cast h_nat
      rw [h_cast, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p))]
    calc (∑ K ∈ ℱ_val.filter (fun K => K.length = p),
          pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K)
      _ ≤ ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleBound p t := h_step1
      _ = ((p.factorial : ℝ)⁻¹) * ∑ r : Fin p, ∑ t ∈ Fintype.piFinset (fun _ : Fin p => P₀), tupleTerm p r t := by
          dsimp [tupleBound]; rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ ((p.factorial : ℝ)⁻¹) * ∑ _r : Fin p,
          (((p - 1).factorial : ℝ)) * ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => h_r_bound r)
            (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = (((p.factorial : ℝ)⁻¹) * ((p : ℝ) * (((p - 1).factorial : ℝ)))) *
          ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
      _ = ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] := by
          rw [h_fac_p, one_mul]
  rw [h_sum_val, h_part_P, Finset.sum_biUnion h_disj_P]
  calc (∑ p ∈ Finset.Icc 1 P, ∑ K ∈ ℱ_val.filter (fun K => K.length = p),
        pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K)
    _ ≤ ∑ p ∈ Finset.Icc 1 P, ∑ γ₀ ∈ T_c, w γ₀ * kpForestWeight P₀ incompat w p [γ₀] :=
        Finset.sum_le_sum h_p_sum_le
    _ = ∑ γ₀ ∈ T_c, w γ₀ * ∑ p ∈ Finset.Icc 1 P, kpForestWeight P₀ incompat w p [γ₀] := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun γ₀ _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ γ₀ ∈ T_c, w γ₀ * Real.exp (a γ₀) := by
        refine Finset.sum_le_sum fun γ₀ hγ₀ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have h_icc_eq : Finset.Icc 1 P = (Finset.range P).image (· + [γ₀].length) := by
          ext p; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range, List.length_singleton]
          constructor
          · intro hp; exact ⟨p - 1, by omega, by omega⟩
          · rintro ⟨n, hn, rfl⟩; omega
        have h_reidx : (∑ p ∈ Finset.Icc 1 P, kpForestWeight P₀ incompat w p [γ₀]) ≤
            ∑ n ∈ Finset.range (P + 1), kpForestWeight P₀ incompat w (n + [γ₀].length) [γ₀] := by
          rw [h_icc_eq, Finset.sum_image (fun x _ y _ h => Nat.add_right_cancel h)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ P))
            (fun n _ _ => kpForestWeight_nonneg P₀ incompat hw (n + [γ₀].length) [γ₀])
        have h_deg := sum_kpDegWeight_le_exp P₀ incompat hw ha h_kp_a P [γ₀]
          (by intro γ hγ; rcases List.mem_singleton.mp hγ with rfl; exact (Finset.mem_filter.mp hγ₀).1)
        simpa using le_trans h_reidx h_deg
    _ ≤ (1 / 32 : ℝ) * min β 1 := h_root_sum

/-- **Pinned Ursell Cluster Sum Bound from Kotecký–Preiss Criterion**
(Part II, Proposition 3.10(ii) (`prop:tube-local-ursell-erasure`), Equations `eq:touching-ursell-bound` and `eq:KP-sum-4-minus-m`):
Given the native-collar Kotecký–Preiss bound (`≤ 1 / 8`) and the spanning-support root-pinned polymer sum
bound (`≤ (1 / 32 : ℝ) * min β 1`) from `worldline_polymer_tree_sum_and_kp_criterion`,
the Dobrushin–Kotecký–Preiss tree-graph inequality bounds the sum of
`|worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ|` over all Ursell clusters
$\gamma \in \Gamma_{\mathrm{ursell}}$ whose spanning support intersects $W$ by
$\sum_{c \in W} \frac{1}{32}\min(\beta, 1) = \frac{1}{32}\min(\beta, 1)\,|W|$. -/
theorem worldline_ursell_pinned_cluster_sum_le_of_kp
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hβ_pos : 0 < β)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_kp :
      (∀ u₁ : IdxCSS[L, q_code, m_max],
        Summable (fun γ : WorldlineDysonPolymer L q_code =>
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ∧
        (∑' γ : WorldlineDysonPolymer L q_code,
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              u₁ ∈ worldlinePolymerNativeCollar sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ≤
          1 / 8) ∧
      (∀ c : IdxCSS[L, q_code, m_max],
        Summable (fun γ : WorldlineDysonPolymer L q_code =>
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ∧
        (∑' γ : WorldlineDysonPolymer L q_code,
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ ∧
              c ∈ worldlinePolymerSpanningSupport D_field sys C_RCA γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| *
              Real.exp ((1 / 8 : ℝ) * ((worldlinePolymerNativeCollar sys C_RCA γ).card : ℝ))
          else 0) ≤
          (1 / 32 : ℝ) * min β 1)) :
    (∑ γ ∈ (worldlineUrsellIndexFinset L q_code m_max R_cut).filter
        (fun γ => ¬Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) W),
      |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ|) ≤
      (1 / 32 : ℝ) * min β 1 * (W.card : ℝ) := by
  let Γ_act := (worldlineUrsellIndexFinset L q_code m_max R_cut).filter
    (fun γ => ¬Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) W)
  let term (fp : WorldlineUrsellFootprint L q_code m_max) (K : WorldlineUrsellCluster L q_code) : ℝ :=
    if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
        worldlineClusterMonomers K = fp.1 ∧
        worldlineClusterSpanningSurface D_field sys C_RCA K = fp.2 then
      worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
    else 0
  have h_pin_summable : ∀ c : IdxCSS[L, q_code, m_max],
      Summable (pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c) := fun c =>
    summable_of_sum_le
      (pinnedClusterAbsWeight_nonneg D_field sys C_RCA R_cut β V d_loc ν σ c)
      (sum_pinnedClusterAbsWeight_le_of_kp D_field sys V d_loc hβ_pos ν σ h_kp c)
  have h_pin_tsum_le : ∀ c : IdxCSS[L, q_code, m_max],
      (∑' K, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) ≤
        (1 / 32 : ℝ) * min β 1 := fun c =>
    le_of_tendsto' (h_pin_summable c).hasSum
      (sum_pinnedClusterAbsWeight_le_of_kp D_field sys V d_loc hβ_pos ν σ h_kp c)
  have h_term_abs_le : ∀ fp ∈ Γ_act, ∀ K : WorldlineUrsellCluster L q_code,
      |term fp K| ≤ ∑ c ∈ W, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K := by
    intro fp hfp K
    rcases Finset.mem_filter.mp hfp with ⟨_, h_nd⟩
    rcases Finset.not_disjoint_iff.mp h_nd with ⟨c₀, hc₀_fp, hc₀_W⟩
    refine le_trans ?_ (Finset.single_le_sum
      (fun c _ => pinnedClusterAbsWeight_nonneg D_field sys C_RCA R_cut β V d_loc ν σ c K) hc₀_W)
    dsimp [term, pinnedClusterAbsWeight]
    split_ifs with h₁ h₂
    · exact le_refl _
    · exfalso
      exact h₂ ⟨h₁.1, exists_mem_worldlinePolymerSpanningSupport_of_cluster_footprint
        D_field sys C_RCA h₁.2.1 h₁.2.2 hc₀_fp⟩
    · rw [abs_zero]
      exact abs_nonneg _
    · rw [abs_zero]
  have h_sum_W_summable : Summable (fun K =>
      ∑ c ∈ W, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K) :=
    summable_sum fun c _ => h_pin_summable c
  have h_term_summable : ∀ fp ∈ Γ_act, Summable (fun K => |term fp K|) := fun fp hfp =>
    Summable.of_nonneg_of_le (fun K => abs_nonneg _) (h_term_abs_le fp hfp) h_sum_W_summable
  have h_phi_le : ∀ fp ∈ Γ_act,
      |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν fp σ| ≤ ∑' K, |term fp K| := by
    intro fp hfp
    change |∑' K, term fp K| ≤ ∑' K, |term fp K|
    have h_norm := norm_tsum_le_tsum_norm (f := fun K => term fp K)
      (by simpa only [Real.norm_eq_abs] using h_term_summable fp hfp)
    simpa only [Real.norm_eq_abs] using h_norm
  have h_pointwise_K : ∀ K : WorldlineUrsellCluster L q_code,
      (∑ fp ∈ Γ_act, |term fp K|) ≤
        ∑ c ∈ W, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K := by
    intro K
    let fp_K : WorldlineUrsellFootprint L q_code m_max :=
      (worldlineClusterMonomers K, worldlineClusterSpanningSurface D_field sys C_RCA K)
    have h_eq_single : (∑ fp ∈ Γ_act, |term fp K|) =
        if fp_K ∈ Γ_act then |term fp_K K| else 0 := by
      by_cases h_in : fp_K ∈ Γ_act
      · rw [if_pos h_in]
        refine Finset.sum_eq_single fp_K (fun fp _ h_ne => ?_) (fun h_not => False.elim (h_not h_in))
        dsimp [term]
        rw [if_neg]
        · exact abs_zero
        · rintro ⟨_, h_m, h_s⟩
          exact h_ne (Prod.ext h_m.symm h_s.symm)
      · rw [if_neg h_in]
        refine Finset.sum_eq_zero fun fp hfp => ?_
        have h_ne : fp ≠ fp_K := fun h_eq => h_in (h_eq ▸ hfp)
        dsimp [term]
        rw [if_neg]
        · exact abs_zero
        · rintro ⟨_, h_m, h_s⟩
          exact h_ne (Prod.ext h_m.symm h_s.symm)
    rw [h_eq_single]
    split_ifs with h_in
    · exact h_term_abs_le fp_K h_in K
    · exact Finset.sum_nonneg fun c _ =>
        pinnedClusterAbsWeight_nonneg D_field sys C_RCA R_cut β V d_loc ν σ c K
  calc (∑ fp ∈ Γ_act, |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν fp σ|)
    _ ≤ ∑ fp ∈ Γ_act, ∑' K, |term fp K| := Finset.sum_le_sum h_phi_le
    _ = ∑' K, ∑ fp ∈ Γ_act, |term fp K| :=
        (Summable.tsum_finsetSum (fun fp hfp => h_term_summable fp hfp)).symm
    _ ≤ ∑' K, ∑ c ∈ W, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K :=
        (summable_sum h_term_summable).tsum_le_tsum h_pointwise_K h_sum_W_summable
    _ = ∑ c ∈ W, ∑' K, pinnedClusterAbsWeight D_field sys C_RCA R_cut β V d_loc ν σ c K :=
        Summable.tsum_finsetSum (fun c _ => h_pin_summable c)
    _ ≤ ∑ _c ∈ W, (1 / 32 : ℝ) * min β 1 :=
        Finset.sum_le_sum (fun c _ => h_pin_tsum_le c)
    _ = (1 / 32 : ℝ) * min β 1 * (W.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Dobrushin–Kotecký–Preiss Pinned Worldline Ursell Sum Bound**
(Part II, Lemma 3.7 (`lem:peierls-bogoliubov`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), and Proposition 3.10(ii) (`prop:tube-local-ursell-erasure`), Equation `eq:touching-ursell-bound`):
Combines `worldline_polymer_tree_sum_and_kp_criterion` and `worldline_ursell_pinned_cluster_sum_le_of_kp` to bound the active Ursell cluster sum touching a witness $W$. -/
theorem worldline_ursell_dobrushin_kotecky_preiss_active_bound
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (ν : PauliBitstringPair L q_code)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    (∑ γ ∈ (worldlineUrsellIndexFinset L q_code m_max R_cut).filter
        (fun γ => ¬Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) W),
      |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ|) ≤
      (1 / 32 : ℝ) * min β 1 * (W.card : ℝ) :=
  worldline_ursell_pinned_cluster_sum_le_of_kp D_field sys V d_loc (by linarith) W ν σ
    (worldline_polymer_tree_sum_and_kp_criterion
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
      e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal
      hC_wl_cal hc_wl_cal hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh ν hσ)

/-- Total absolute Ursell sum bound over the entire footprint index set
`worldlineUrsellIndexFinset L q_code m_max R_cut` (Part II, Proposition 2.9(i)–(ii) (`prop:tube-local-ursell-erasure`)):
specializing `worldline_ursell_dobrushin_kotecky_preiss_active_bound` to $W = \mathcal{C} = \mathrm{Finset.univ}$
and using `worldlineUrsellPhi_eq_zero_of_disjoint_univ` bounds the full finite sum of
`|worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ|` by
$\frac{1}{32}\min(\beta, 1)\,|\mathcal{C}|$. -/
lemma sum_worldlineUrsellIndexFinset_worldlineUrsellPhi_abs_le
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (ν : PauliBitstringPair L q_code)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    (∑ γ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
      |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ|) ≤
      (1 / 32 : ℝ) * min β 1 * (Fintype.card (IdxCSS[L, q_code, m_max]) : ℝ) := by
  have h_act := worldline_ursell_dobrushin_kotecky_preiss_active_bound
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
    e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal
    hC_wl_cal hc_wl_cal hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh Finset.univ ν hσ
  have h_eq :
      (∑ γ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
        |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ|) =
      ∑ γ ∈ (worldlineUrsellIndexFinset L q_code m_max R_cut).filter
          (fun γ => ¬Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) Finset.univ),
        |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ| := by
    rw [← Finset.sum_filter_add_sum_filter_not (worldlineUrsellIndexFinset L q_code m_max R_cut)
      (fun γ => ¬Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) Finset.univ)]
    have h_zero_rest :
        (∑ γ ∈ (worldlineUrsellIndexFinset L q_code m_max R_cut).filter
            (fun γ => ¬¬Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) Finset.univ),
          |worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ|) = 0 := by
      refine Finset.sum_eq_zero fun γ hγ => ?_
      have h_disj := not_not.mp (Finset.mem_filter.mp hγ).2
      rw [worldlineUrsellPhi_eq_zero_of_disjoint_univ D_field sys
        (fun idx => (h_sys_checks idx).2.1) h_geom h_scale_cal.2.1 V d_loc ν γ σ h_disj, abs_zero]
    rw [h_zero_rest, add_zero]
  rw [h_eq, ← Finset.card_univ]
  exact h_act

/-- **Duhamel–Dyson Worldline Polymer and Ursell Trace Decomposition**
(Part II, Proposition 3.6 (`prop:walsh-coset-dominance`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
Combines `worldline_dyson_mayer_polymer_gas_partition_identity` and `worldline_mayer_ursell_cluster_log_identity` to express both the restricted witness Boltzmann trace and the full partition function as averages over syndrome-closed Pauli fibers of exponentiated Ursell cluster sums. -/
theorem worldline_duhamel_dyson_ursell_trace_identity
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
    let N_closed := ((syndromeClosedPauliFinset D_field).card : ℝ)
    0 < K_norm ∧
    (∀ W : Finset (IdxCSS[L, q_code, m_max]),
      hilbertTrace (gibbsBoltzmannOp
        (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
        (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
          positiveCheckWitnessProj sys W) =
        K_norm * ∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
          ∑ ν ∈ syndromeClosedPauliFinset D_field, N_closed⁻¹ *
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ +
              ∑ γ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
                worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ)) ∧
    (gibbsPartitionZ (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β =
      K_norm * ∑ σ ∈ realizableSyndromes D_field,
        ∑ ν ∈ syndromeClosedPauliFinset D_field, N_closed⁻¹ *
          Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ +
            ∑ γ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
              worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ)) := by
  rcases worldline_dyson_mayer_polymer_gas_partition_identity
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
      e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
      hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh with ⟨hK_pos, h_num, h_den⟩
  refine ⟨hK_pos, fun W => ?_, ?_⟩
  · rw [h_num W]
    congr 1
    refine Finset.sum_congr rfl fun σ hσ => Finset.sum_congr rfl fun ν _ => ?_
    have hσ_R : σ ∈ realizableSyndromes D_field := (Finset.mem_filter.mp hσ).1
    have h_log := worldline_mayer_ursell_cluster_log_identity
        D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
        e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
        hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh ν hσ_R
    rw [h_log, mul_assoc, ← Real.exp_add]
  · rw [h_den]
    congr 1
    refine Finset.sum_congr rfl fun σ hσ_R => Finset.sum_congr rfl fun ν _ => ?_
    have h_log := worldline_mayer_ursell_cluster_log_identity
        D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
        e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
        hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh ν hσ_R
    rw [h_log, mul_assoc, ← Real.exp_add]

/-- Pointwise spectator-cancellation bound on the Pauli-diagonal sector energy under a zero-spillover
coset shift $\sigma_W = \mathbf{1}_W$: for every witness-clean syndrome $\tau \in \mathcal{C}_0(W)$,
$\sigma_W \oplus \tau$ and $\tau$ agree identically on $\mathcal{C} \setminus W$, so all spectator
diagonal collar cubes cancel and the active collar cubes change the energy by at most $\frac{1}{4}|W|$. -/
private lemma zero_spillover_pauliDiagonalSectorEnergy_coset_shift_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA J β : ℝ} (hC_RCA : 0 ≤ C_RCA) (hβ_pos : 0 < β) (hJ : 0 ≤ J)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    {τ : IdxCSS[L, q_code, m_max] → Bool}
    (hτ : τ ∈ witnessCleanRealizableSyndromes D_field W) :
    -β * pauliDiagonalSectorEnergy sys R_cut d_loc
        (syndromeXor (fun idx => decide (idx ∈ W)) τ) ≤
      -(3 / 4 : ℝ) * β * (W.card : ℝ) + -β * pauliDiagonalSectorEnergy sys R_cut d_loc τ := by
  let σ_W : IdxCSS[L, q_code, m_max] → Bool := fun idx => decide (idx ∈ W)
  have hτ_clean : ∀ idx ∈ W, τ idx = false := (Finset.mem_filter.mp hτ).2
  have h_agree_out : ∀ c : IdxCSS[L, q_code, m_max], c ∉ W → syndromeXor σ_W τ c = τ c := by
    intro c hc; dsimp [syndromeXor, σ_W]; rw [decide_eq_false hc]; cases τ c <;> rfl
  have h_spec_eq :
      spectatorPauliDiagonalEnergy sys C_RCA R_cut d_loc W (syndromeXor σ_W τ) =
        spectatorPauliDiagonalEnergy sys C_RCA R_cut d_loc W τ := by
    unfold spectatorPauliDiagonalEnergy
    have h_filt : (Finset.univ \ W).filter (fun c => syndromeXor σ_W τ c = true) =
        (Finset.univ \ W).filter (fun c => τ c = true) :=
      Finset.filter_congr fun c hc => by rw [h_agree_out c (Finset.mem_sdiff.mp hc).2]
    rw [h_filt]
    congr 1
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun A hA => ?_
    rcases Finset.mem_filter.mp hA with ⟨hA_cube, hA_disj⟩
    exact (h_scalar r hr A hA_cube).2.2 _ _ fun c hc =>
      h_agree_out c (Finset.disjoint_left.mp hA_disj hc)
  let K_geom : ℕ :=
    (2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1) ^ 3 * (w_0 + 1)
  have h_split : ∀ η : IdxCSS[L, q_code, m_max] → Bool,
      pauliDiagonalSectorEnergy sys R_cut d_loc η =
        spectatorPauliDiagonalEnergy sys C_RCA R_cut d_loc W η +
          ((W.filter (fun c => η c = true)).card : ℝ) +
          ∑ r ∈ Finset.Icc 1 (min R_cut L),
            ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W),
              d_loc r A η := by
    intro η
    unfold pauliDiagonalSectorEnergy spectatorPauliDiagonalEnergy
      IndexedCommutingProjectorHamiltonian.syndromeEnergy
    have h_wt_sum : (∑ c ∈ Finset.univ.filter (fun c => η c = true), sys.weight c) =
        ((Finset.univ.filter (fun c => η c = true)).card : ℝ) := by
      calc ∑ c ∈ Finset.univ.filter (fun c => η c = true), sys.weight c
        _ = ∑ _c ∈ Finset.univ.filter (fun c => η c = true), (1 : ℝ) :=
            Finset.sum_congr rfl fun c _ => (h_sys_checks c).2.2
        _ = ((Finset.univ.filter (fun c => η c = true)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_card_split : (Finset.univ.filter (fun c => η c = true)).card =
        (W.filter (fun c => η c = true)).card +
          ((Finset.univ \ W).filter (fun c => η c = true)).card := by
      rw [← Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter disjoint_sdiff_self_right),
        ← Finset.filter_union, Finset.union_sdiff_of_subset (Finset.subset_univ W)]
    have h_cube_split : (∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, d_loc r A η) =
        (∑ r ∈ Finset.Icc 1 (min R_cut L),
          ∑ A ∈ (boxCubes 3 L r).filter (fun A => Disjoint (rcaCollarChecks sys C_RCA r A) W),
            d_loc r A η) +
        (∑ r ∈ Finset.Icc 1 (min R_cut L),
          ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W),
            d_loc r A η) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ =>
        (Finset.sum_filter_add_sum_filter_not (boxCubes 3 L r) _ _).symm
    rw [h_wt_sum, h_card_split, Nat.cast_add, h_cube_split]; ring
  have h_act_abs : ∀ η : IdxCSS[L, q_code, m_max] → Bool,
      |∑ r ∈ Finset.Icc 1 (min R_cut L),
        ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W),
          d_loc r A η| ≤ (1 / 8 : ℝ) * (W.card : ℝ) := by
    intro η
    have h_r_le : ∀ r ∈ Finset.Icc 1 (min R_cut L),
        |∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W),
          d_loc r A η| ≤ ((W.card * K_geom : ℕ) : ℝ) * (2 * J) := by
      intro r hr
      have h_sub : (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W) ⊆
          W.biUnion (fun c => (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_RCA r A)) := by
        intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hA_mem, h_nd⟩
        rcases Finset.not_disjoint_iff.mp h_nd with ⟨c, hc_col, hc_W⟩
        exact Finset.mem_biUnion.mpr ⟨c, hc_W, Finset.mem_filter.mpr ⟨hA_mem, hc_col⟩⟩
      have h_card :
          ((boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W)).card ≤
            W.card * K_geom := by
        calc ((boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W)).card
          _ ≤ (W.biUnion (fun c => (boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_RCA r A))).card :=
              Finset.card_le_card h_sub
          _ ≤ ∑ c ∈ W, ((boxCubes 3 L r).filter (fun A => c ∈ rcaCollarChecks sys C_RCA r A)).card :=
              Finset.card_biUnion_le
          _ ≤ W.card • K_geom := Finset.sum_le_card_nsmul W _ K_geom fun c _ =>
              card_filter_mem_rcaCollarChecks_le D_field sys h_sys_checks hC_RCA hr c
          _ = W.card * K_geom := smul_eq_mul _ _
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * J) fun A hA =>
        (h_scalar r hr A (Finset.mem_filter.mp hA).1).1.2 η) ?_
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) (by linarith)
    have h_sum_r := le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_card_nsmul (Finset.Icc 1 (min R_cut L)) _
        (((W.card * K_geom : ℕ) : ℝ) * (2 * J)) h_r_le)
    rw [nsmul_eq_mul] at h_sum_r
    have h_card_Icc : ((Finset.Icc 1 (min R_cut L)).card : ℝ) ≤ (R_cut : ℝ) := by
      have h_nat : (Finset.Icc 1 (min R_cut L)).card ≤ R_cut := by
        rw [Nat.card_Icc]; have := Nat.min_le_left R_cut L; omega
      exact_mod_cast h_nat
    have h_first : |∑ r ∈ Finset.Icc 1 (min R_cut L),
        ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_RCA r A) W),
          d_loc r A η| ≤ 2 * rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA * J * (W.card : ℝ) := by
      refine le_trans h_sum_r (le_trans (mul_le_mul_of_nonneg_right h_card_Icc (by positivity)) ?_)
      unfold rcaDiagonalCoercivityConstant; dsimp [K_geom]; push_cast; linarith
    exact le_trans h_first (mul_le_mul_of_nonneg_right
      (two_mul_rcaDiagonalCoercivityConstant_mul_le_eighth_of_le_collarWalshCouplingThreshold hJ hJ_walsh)
      (Nat.cast_nonneg W.card))
  have h_filt_xor : W.filter (fun c => syndromeXor σ_W τ c = true) = W :=
    Finset.filter_eq_self.mpr fun idx hidx => by
      dsimp [syndromeXor, σ_W]; rw [decide_eq_true hidx, hτ_clean idx hidx]; rfl
  have h_filt_τ : W.filter (fun c => τ c = true) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun idx hidx => by rw [hτ_clean idx hidx]; decide
  have h_en_xor := h_split (syndromeXor σ_W τ)
  rw [h_filt_xor, h_spec_eq] at h_en_xor
  have h_en_τ := h_split τ
  rw [h_filt_τ, Finset.card_empty, Nat.cast_zero] at h_en_τ
  have h_lb := (abs_le.mp (h_act_abs (syndromeXor σ_W τ))).1
  have h_ub := (abs_le.mp (h_act_abs τ)).2
  nlinarith

private lemma exists_local_collar_scalar_family_of_truncated_norm_scale
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (hC_RCA : 0 ≤ C_RCA) (hJ : 0 ≤ J) :
    ∃ (e_loc : ℕ → Finset (Box3D L) → ℝ)
      (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ),
      IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc ∧
      ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
        ∀ σ : IdxCSS[L, q_code, m_max] → Bool, |d_loc r A σ| ≤ 2 * (J * f r) := by
  let V_single (r₀ : ℕ) : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]) :=
    { term := fun r A => if r = r₀ then V.term r A else 0
      is_selfAdjoint := fun r A => by
        (try dsimp only)
        split_ifs
        · exact V.is_selfAdjoint r A
        · exact (scaleSplitTruncatedPerturbation V 0).is_selfAdjoint 1 A
      is_supported := fun r hr A hA => by
        (try dsimp only)
        split_ifs
        · exact V.is_supported r hr A hA
        · exact _root_.isSupportedOn_zero A }
  have h_ex_r : ∀ r₀ ∈ Finset.Icc 1 (min R_cut L),
      ∃ (e₀ : ℕ → Finset (Box3D L) → ℝ)
        (d₀ : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ),
        IsLocalCollarScalarFamily D_field sys R_cut C_RCA (J * f r₀) (V_single r₀) e₀ d₀ := by
    intro r₀ hr₀
    have hV_range : HasFiniteRangeBound (V_single r₀) R_cut (J * f r₀) := by
      intro r hr A hA
      refine ⟨fun _ => ?_, fun hr_gt => ?_⟩
      · unfold V_single
        (try dsimp only)
        split_ifs with h_eq
        · subst h_eq
          exact hV_norm r hr₀ A hA
        · rw [norm_zero]
          exact mul_nonneg hJ (hf_nn r₀)
      · unfold V_single
        (try dsimp only)
        have hr₀_le : r₀ ≤ R_cut := le_trans (Finset.mem_Icc.mp hr₀).2 (Nat.min_le_left R_cut L)
        exact if_neg (by omega)
    rcases exists_pauliDiagonal_local_collar_decomposition
        D_field sys h_sys_checks hR_le h_tqo2 (V_single r₀) hV_range with ⟨e₀, he₀⟩
    rcases exists_local_collar_scalar_family_of_tqo2
        D_field h_valid sys h_sys_checks h_geom hR_cut hR_le hC_RCA
        (mul_nonneg hJ (hf_nn r₀)) h_tqo1 h_tqo2 (V_single r₀) hV_range e₀ he₀ with ⟨d₀, hd₀⟩
    exact ⟨e₀, d₀, hd₀⟩
  let e_loc (r : ℕ) (A : Finset (Box3D L)) : ℝ :=
    if hr : r ∈ Finset.Icc 1 (min R_cut L) then (Classical.choose (h_ex_r r hr)) r A else 0
  let d_loc (r : ℕ) (A : Finset (Box3D L)) (σ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
    if hr : r ∈ Finset.Icc 1 (min R_cut L) then
      (Classical.choose (Classical.choose_spec (h_ex_r r hr))) r A σ
    else 0
  refine ⟨e_loc, d_loc, fun r hr A hA => ?_, fun r hr A hA σ => ?_⟩
  · have h_spec := Classical.choose_spec (Classical.choose_spec (h_ex_r r hr)) r hr A hA
    have h_shift_eq : pauliDiagonalShiftedTerm sys V e_loc r A =
        pauliDiagonalShiftedTerm sys (V_single r) (Classical.choose (h_ex_r r hr)) r A := by
      unfold pauliDiagonalShiftedTerm V_single e_loc
      (try dsimp only)
      rw [if_pos rfl, dif_pos hr]
    have hd_eq : ∀ σ, d_loc r A σ = (Classical.choose (Classical.choose_spec (h_ex_r r hr))) r A σ :=
      fun σ => dif_pos hr
    refine ⟨⟨fun σ hσ => ?_, fun σ => ?_⟩, fun σ h_clean => ?_, fun σ₁ σ₂ h_agree => ?_⟩
    · rw [h_shift_eq, hd_eq]
      exact h_spec.1.1 σ hσ
    · rw [hd_eq]
      calc |(Classical.choose (Classical.choose_spec (h_ex_r r hr))) r A σ|
        _ ≤ 2 * (J * f r) := h_spec.1.2 σ
        _ ≤ 2 * (J * 1) := by nlinarith [hf_le_one r]
        _ = 2 * J := by ring
    · rw [hd_eq]
      exact h_spec.2.1 σ h_clean
    · rw [hd_eq, hd_eq]
      exact h_spec.2.2 σ₁ σ₂ h_agree
  · have h_spec := Classical.choose_spec (Classical.choose_spec (h_ex_r r hr)) r hr A hA
    dsimp [d_loc]
    rw [dif_pos hr]
    exact h_spec.1.2 σ

/-- **Zero-Spillover Worldline Witness Gibbs Bound (`worldline_zero_spillover_witness_gibbs_bound`,
Part II, Proposition 3.10(ii) (`prop:tube-local-ursell-erasure`) and Theorem 5.1(ii) (`thm:direct-worldline-intact-cluster-erasure`))**:
For any positive check witness
$W \subseteq \mathcal{C}$ satisfying the zero-spillover realizability condition
`hW_valid : (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field`, the coset shift
$\tau \mapsto \mathbf{1}_W \oplus \tau$ leaves $\mathcal{C} \setminus W$ pointwise invariant, so both
spectator diagonal collar terms and spectator worldline Ursell clusters cancel identically between
$\mathbf{1}_W \oplus \tau$ and $\tau$, yielding
$\operatorname{Tr}(\rho_\beta(H_0 + V^{\le R_{\mathrm{cut}}})\Pi_W^+) \le \exp(-(\frac{3}{4}\beta - 1)|W|)$. -/
theorem worldline_zero_spillover_witness_gibbs_bound
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (W : Finset (IdxCSS[L, q_code, m_max]))
    (hW_valid : (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes D_field) :
    gibbsFailureProb (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
      (positiveCheckWitnessProj sys W) ≤
      Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ))) := by
  have hβ_pos : 0 < β := by linarith
  rcases exists_local_collar_scalar_family_of_truncated_norm_scale
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
      hR_cut hR_le hC_RCA hJ with ⟨e_loc, d_loc, h_scalar, hd_scale⟩
  rcases worldline_duhamel_dyson_ursell_trace_identity
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
      e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
      hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh with
    ⟨hK_pos, h_trace_num, h_trace_den⟩
  let σ_W : IdxCSS[L, q_code, m_max] → Bool := fun idx => decide (idx ∈ W)
  let Γ_ursell := worldlineUrsellIndexFinset L q_code m_max R_cut
  let Φ_ursell := worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc
  let N_closed : ℝ := ((syndromeClosedPauliFinset D_field).card : ℝ)
  have h_xor_R : ∀ {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool},
      σ₁ ∈ realizableSyndromes D_field → σ₂ ∈ realizableSyndromes D_field →
      syndromeXor σ₁ σ₂ ∈ realizableSyndromes D_field := by
    intro σ₁ σ₂ h₁ h₂
    rw [realizableSyndromes, Finset.mem_filter] at h₁ h₂ ⊢
    rcases h₁.2 with ⟨a₁, b₁, rfl⟩; rcases h₂.2 with ⟨a₂, b₂, rfl⟩
    exact ⟨Finset.mem_univ _, a₁ + a₂, b₁ + b₂, (staticCSSPauliFlip_add D_field a₁ a₂ b₁ b₂).symm⟩
  let F_sec (σ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
    ∑ ν ∈ syndromeClosedPauliFinset D_field, N_closed⁻¹ *
      Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ +
        ∑ γ ∈ Γ_ursell, Φ_ursell ν γ σ)
  have hF_nn : ∀ σ, 0 ≤ F_sec σ := fun σ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (le_of_lt (Real.exp_pos _))
  have h_bij :
      (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true), F_sec σ) =
        ∑ τ ∈ witnessCleanRealizableSyndromes D_field W, F_sec (syndromeXor σ_W τ) := by
    symm
    refine Finset.sum_bij (fun τ _ => syndromeXor σ_W τ) ?_ ?_ ?_ ?_
    · intro τ hτ
      rcases Finset.mem_filter.mp hτ with ⟨hτ_R, hτ_W⟩
      refine Finset.mem_filter.mpr ⟨h_xor_R hW_valid hτ_R, fun idx hidx => ?_⟩
      dsimp [syndromeXor, σ_W]; rw [decide_eq_true hidx, hτ_W idx hidx]; rfl
    · intro τ₁ _ τ₂ _ h_eq; (try dsimp only at h_eq)
      rw [← syndromeXor_cancel_left σ_W τ₁, ← syndromeXor_cancel_left σ_W τ₂, h_eq]
    · intro σ hσ
      rcases Finset.mem_filter.mp hσ with ⟨hσ_R, hσ_W⟩
      refine ⟨syndromeXor σ_W σ, Finset.mem_filter.mpr ⟨h_xor_R hW_valid hσ_R, fun idx hidx => ?_⟩,
        syndromeXor_cancel_left σ_W σ⟩
      dsimp [syndromeXor, σ_W]; rw [decide_eq_true hidx, hσ_W idx hidx]; rfl
    · intro _ _; rfl
  have h_pointwise : ∀ τ ∈ witnessCleanRealizableSyndromes D_field W,
      F_sec (syndromeXor σ_W τ) ≤
        Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ))) * F_sec τ := by
    intro τ hτ
    have hτ_R : τ ∈ realizableSyndromes D_field := (Finset.mem_filter.mp hτ).1
    have h_xor_mem : syndromeXor σ_W τ ∈ realizableSyndromes D_field := h_xor_R hW_valid hτ_R
    have h_diag := zero_spillover_pauliDiagonalSectorEnergy_coset_shift_le
      D_field sys h_sys_checks h_geom hC_RCA hβ_pos hJ hJ_walsh V
      e_loc d_loc h_scalar W hτ
    dsimp [F_sec]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    rw [← mul_assoc, mul_comm (Real.exp _) N_closed⁻¹, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    let Γ_act := Γ_ursell.filter
      (fun γ => ¬Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) W)
    let Γ_spec := Γ_ursell.filter
      (fun γ => Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) W)
    have h_ursell_split : ∀ σ,
        (∑ γ ∈ Γ_ursell, Φ_ursell ν γ σ) =
          (∑ γ ∈ Γ_spec, Φ_ursell ν γ σ) + (∑ γ ∈ Γ_act, Φ_ursell ν γ σ) :=
      fun σ => (Finset.sum_filter_add_sum_filter_not Γ_ursell
        (fun γ => Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) W) _).symm
    have h_spec_cancel :
        (∑ γ ∈ Γ_spec, Φ_ursell ν γ (syndromeXor σ_W τ)) =
          ∑ γ ∈ Γ_spec, Φ_ursell ν γ τ := by
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rcases Finset.mem_filter.mp hγ with ⟨_hγ_mem, hγ_disj⟩
      exact worldline_ursell_spanning_surface_collar_locality
        D_field sys C_RCA R_cut β V d_loc ν γ fun c hc => by
          have hc_not_W : c ∉ W := Finset.disjoint_left.mp hγ_disj hc
          dsimp [syndromeXor, σ_W]; rw [decide_eq_false hc_not_W]; cases τ c <;> rfl
    have h_act_xor := le_trans (le_abs_self _) (le_trans (Finset.abs_sum_le_sum_abs _ _)
      (worldline_ursell_dobrushin_kotecky_preiss_active_bound
        D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
        e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
        hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh W ν h_xor_mem))
    have h_act_τ := le_trans (neg_le_abs _) (le_trans (Finset.abs_sum_le_sum_abs _ _)
      (worldline_ursell_dobrushin_kotecky_preiss_active_bound
        D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
        e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
        hΔ_RCA hβ hJ h_sum_pos hJ_walsh hJ_wl h_thresh W ν hτ_R))
    have h_min_le_one : min β 1 ≤ 1 := min_le_right β 1
    have h_ursell_diff :
        (∑ γ ∈ Γ_ursell, Φ_ursell ν γ (syndromeXor σ_W τ)) -
          (∑ γ ∈ Γ_ursell, Φ_ursell ν γ τ) ≤ (W.card : ℝ) := by
      rw [h_ursell_split (syndromeXor σ_W τ), h_ursell_split τ, h_spec_cancel]
      have h_w_nn : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg W.card
      nlinarith
    linarith
  have h_sum_le :
      (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true), F_sec σ) ≤
        Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ))) *
          ∑ σ ∈ realizableSyndromes D_field, F_sec σ := by
    calc (∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true), F_sec σ)
      _ = ∑ τ ∈ witnessCleanRealizableSyndromes D_field W, F_sec (syndromeXor σ_W τ) := h_bij
      _ ≤ ∑ τ ∈ witnessCleanRealizableSyndromes D_field W,
            Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ))) * F_sec τ :=
          Finset.sum_le_sum h_pointwise
      _ = Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ))) *
            ∑ τ ∈ witnessCleanRealizableSyndromes D_field W, F_sec τ := by
          rw [← Finset.mul_sum]
      _ ≤ Real.exp (-(((3 / 4 : ℝ) * β - 1) * (W.card : ℝ))) *
            ∑ σ ∈ realizableSyndromes D_field, F_sec σ :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun σ _ _ => hF_nn σ)
            (le_of_lt (Real.exp_pos _))
  have hZ_pos : 0 < gibbsPartitionZ (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β :=
    gibbsPartitionZ_pos (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace
    (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β (positiveCheckWitnessProj sys W),
    ← div_eq_inv_mul, div_le_iff₀ hZ_pos, h_trace_num W, h_trace_den]
  have h_mul := mul_le_mul_of_nonneg_left h_sum_le (le_of_lt hK_pos)
  linarith

end DirectWorldlineCluster
end
