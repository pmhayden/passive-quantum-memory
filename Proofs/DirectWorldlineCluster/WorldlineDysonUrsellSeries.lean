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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellHelpers

/-!
# Polymer Incompatibility, Vacuum Normalization, and Native-Collar Trajectory Invariance

Formalizes native-collar polymer incompatibility (`ArePolymersIncompatible`, `PolymerClusterOverlap`) and defines the Mayer polymer cluster weights and partition series (`worldlineMayerPolymerClusterWeight`, `worldlineMayerPolymerPartition`). Proves positivity of the vacuum partition normalization (`vacuumPartitionNorm_pos_of_validDescriptorField`) and native-collar localization of worldline syndrome trajectories (`worldlineTrajectorySyndrome_eq_outside_and_congr_on_nativeCollar`).

## References

* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
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
## 1. Worldline Dyson–Mayer–Ursell Series and Collar Localization Helpers

Develops the Dyson–Mayer–Ursell series definitions (`ArePolymersIncompatible`, `worldlineMayerPolymerClusterWeight`, `worldlineMayerPolymerPartition`) and native-collar localization lemmas (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`) and Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`)).
-/

lemma abs_syndromeEnergy_syndromeXor_sub_le
    {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max])
    (h_wt : ∀ idx, sys.weight idx = 1)
    (δ η : IdxCSS[L, q_code, m_max] → Bool)
    (S : Finset (IdxCSS[L, q_code, m_max]))
    (h_supp : ∀ c, δ c = true → c ∈ S) :
    |sys.syndromeEnergy (syndromeXor δ η) - sys.syndromeEnergy η| ≤ (S.card : ℝ) := by
  have h_en : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      sys.syndromeEnergy σ = ∑ c : IdxCSS[L, q_code, m_max], if σ c = true then (1 : ℝ) else 0 := by
    intro σ
    unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => by rw [h_wt c]
  rw [h_en (syndromeXor δ η), h_en η, ← Finset.sum_sub_distrib]
  have h_sub_S : (∑ c : IdxCSS[L, q_code, m_max],
      ((if syndromeXor δ η c = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0))) =
      ∑ c ∈ S, ((if syndromeXor δ η c = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0)) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ S) fun c _ hc_not => ?_
    have hδ_false : δ c = false := by
      cases hδ : δ c
      · rfl
      · exact False.elim (hc_not (h_supp c hδ))
    have h_xor : syndromeXor δ η c = η c := by
      unfold syndromeXor
      rw [hδ_false]
      cases η c <;> rfl
    rw [h_xor, sub_self]
  rw [h_sub_S]
  calc |∑ c ∈ S, ((if syndromeXor δ η c = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0))|
    _ ≤ ∑ c ∈ S, |(if syndromeXor δ η c = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ S, (1 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        cases syndromeXor δ η c <;> cases η c <;> norm_num
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

lemma abs_syndromeEnergy_foldr_syndromeXor_sub_le
    {α : Type*} {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max])
    (h_wt : ∀ idx, sys.weight idx = 1)
    (δ_fn : α → IdxCSS[L, q_code, m_max] → Bool)
    (S_fn : α → Finset (IdxCSS[L, q_code, m_max]))
    (K : ℝ) (hK_nn : 0 ≤ K)
    (l : List α)
    (h_supp : ∀ x ∈ l, (∀ c, δ_fn x c = true → c ∈ S_fn x) ∧ ((S_fn x).card : ℝ) ≤ K)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    |sys.syndromeEnergy (l.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀) -
      sys.syndromeEnergy σ₀| ≤ (l.length : ℝ) * K := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldr_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    let σ_tl := tl.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀
    have h_hd := h_supp hd List.mem_cons_self
    have h_step1 : |sys.syndromeEnergy (syndromeXor (δ_fn hd) σ_tl) - sys.syndromeEnergy σ_tl| ≤ K :=
      le_trans (abs_syndromeEnergy_syndromeXor_sub_le sys h_wt (δ_fn hd) σ_tl (S_fn hd) h_hd.1) h_hd.2
    have h_step2 : |sys.syndromeEnergy σ_tl - sys.syndromeEnergy σ₀| ≤ (tl.length : ℝ) * K :=
      ih (fun x hx => h_supp x (List.mem_cons_of_mem hd hx))
    have h_tri := abs_add_le
      (sys.syndromeEnergy (syndromeXor (δ_fn hd) σ_tl) - sys.syndromeEnergy σ_tl)
      (sys.syndromeEnergy σ_tl - sys.syndromeEnergy σ₀)
    rw [sub_add_sub_cancel] at h_tri
    linarith

lemma card_cubeIntersectingChecks_le_kpCollarMaxCheckCard
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max])
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (C_RCA : ℝ) {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_cut L))
    {A : Finset (Box3D L)} (hA : A ∈ boxCubes 3 L r) :
    (cubeIntersectingChecks sys A).card ≤ kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA := by
  have hL_pos : 0 < L := NeZero.pos L
  have hr_R : r ≤ R_cut := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_cut L)
  have hA_eq : boxCube (anchorOfCube r A) r = A := boxCube_anchorOfCube hA
  let g : (Fin 3 → Fin r) → Box3D L := fun k i =>
    ⟨min (L - 1) ((anchorOfCube r A i).val + (k i).val),
      Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩
  have hA_sub : A ⊆ Finset.univ.image g := fun y hy => by
    rw [← hA_eq, mem_boxCube] at hy
    have hk_lt : ∀ i : Fin 3, (y i).val - (anchorOfCube r A i).val < r := fun i => by
      have := (hy i).1; have := (hy i).2; omega
    let k : Fin 3 → Fin r := fun i => ⟨(y i).val - (anchorOfCube r A i).val, hk_lt i⟩
    have hy_eq : g k = y := by
      funext i; apply Fin.ext
      have := (hy i).1; have := (y i).isLt
      dsimp [g, k]; omega
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hy_eq⟩
  have hA_card : A.card ≤ r ^ 3 := by
    calc A.card
      _ ≤ (Finset.univ : Finset (Fin 3 → Fin r)).card :=
          le_trans (Finset.card_le_card hA_sub) Finset.card_image_le
      _ = r ^ 3 := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have h_col_sub : cubeIntersectingChecks sys A ⊆
      A.biUnion (fun y => Finset.univ.filter (fun c => y ∈ sys.support c)) := by
    intro c hc
    unfold cubeIntersectingChecks at hc
    rcases Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hc).2 with ⟨y, hy_c, hy_A⟩
    exact Finset.mem_biUnion.mpr ⟨y, hy_A, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hy_c⟩⟩
  have h_card_col : (cubeIntersectingChecks sys A).card ≤ A.card * w_0 :=
    smul_eq_mul A.card w_0 ▸ le_trans (le_trans (Finset.card_le_card h_col_sub) Finset.card_biUnion_le)
      (Finset.sum_le_card_nsmul A _ w_0 (fun y _ => h_geom.2 y))
  have h_base : r ≤ 2 * (R_cut + 2 * linearExpansionRadius C_RCA R_cut + r_0) + 1 := by omega
  unfold kpCollarMaxCheckCard
  exact le_trans h_card_col
    (le_trans (Nat.mul_le_mul (le_trans hA_card (Nat.pow_le_pow_left h_base 3)) (Nat.le_succ w_0))
      (Nat.le_succ _))

lemma shiftOpenBox_neighborhoodOffset_mem_boxBall {L r_0 : ℕ}
    (v : Box3D L) (nb : LocalNeighborhoodIdx r_0)
    (h_in : InOpenBox v (neighborhoodOffset r_0 nb)) :
    shiftOpenBox v (neighborhoodOffset r_0 nb) ∈ boxBall v r_0 := by
  let w := shiftOpenBox v (neighborhoodOffset r_0 nb)
  change w ∈ boxBall v r_0
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
  dsimp [boxDist]
  refine Finset.sup_le fun μ _ => ?_
  have h_nb := (nb μ).isLt
  have h_in_μ := h_in μ
  have h_sh_μ : (w μ).val = ((shiftOpenBox v (neighborhoodOffset r_0 nb)) μ).val := rfl
  dsimp [shiftOpenBox, shiftOpenBoxD] at h_sh_μ
  rw [dif_pos h_in_μ] at h_sh_μ
  dsimp [neighborhoodOffset, coordDist] at h_in_μ h_sh_μ ⊢
  omega

lemma staticCSSPauliFlip_mem_cubeIntersectingChecks
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (A : Finset (Box3D L))
    (a b : BoxSlot3D L q_code → ZMod 2)
    (h_supp : ∀ slot : BoxSlot3D L q_code, a slot ≠ 0 ∨ b slot ≠ 0 → slot.1 ∈ A)
    (c : IdxCSS[L, q_code, m_max])
    (hc : staticCSSPauliFlip D_field a b c = true) :
    c ∈ cubeIntersectingChecks sys A := by
  unfold cubeIntersectingChecks
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ c, Finset.not_disjoint_iff.mpr ?_⟩
  rw [h_sys_supp c]
  rcases c with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
  · dsimp [staticCSSPauliFlip] at hc
    rcases Bool.and_eq_true_iff.mp hc with ⟨_, h_dec⟩
    rcases Finset.exists_ne_zero_of_sum_ne_zero (of_decide_eq_true h_dec) with ⟨p, _, hp_nz⟩
    have h_s : singleSlotChain v s p ≠ 0 := left_ne_zero_of_mul hp_nz
    have hb : b p ≠ 0 := right_ne_zero_of_mul hp_nz
    dsimp [singleSlotChain] at h_s
    split_ifs at h_s with hp_eq
    · refine ⟨p.1, ?_, h_supp p (Or.inr hb)⟩
      rw [staticCSSCheckSupport, congrArg Prod.fst hp_eq]
      exact Finset.mem_singleton_self v
    · exact False.elim (h_s rfl)
  · dsimp [staticCSSPauliFlip] at hc
    rcases Bool.and_eq_true_iff.mp hc with ⟨_, h_dec⟩
    rcases Finset.exists_ne_zero_of_sum_ne_zero (of_decide_eq_true h_dec) with ⟨p, _, hp_nz⟩
    have ha : a p ≠ 0 := left_ne_zero_of_mul hp_nz
    have h_ch : descriptorCheckXChain D_field v idx p ≠ 0 := right_ne_zero_of_mul hp_nz
    dsimp [descriptorCheckXChain] at h_ch
    split_ifs at h_ch with h_cond
    · rcases h_cond with ⟨_, nb, h_in, h_sh, _⟩
      refine ⟨p.1, ?_, h_supp p (Or.inl ha)⟩
      rw [staticCSSCheckSupport, ← h_sh]
      exact shiftOpenBox_neighborhoodOffset_mem_boxBall v nb h_in
    · exact False.elim (h_ch rfl)
  · dsimp [staticCSSPauliFlip] at hc
    rcases Bool.and_eq_true_iff.mp hc with ⟨_, h_dec⟩
    rcases Finset.exists_ne_zero_of_sum_ne_zero (of_decide_eq_true h_dec) with ⟨p, _, hp_nz⟩
    have h_ch : descriptorCheckZChain D_field v idx p ≠ 0 := left_ne_zero_of_mul hp_nz
    have hb : b p ≠ 0 := right_ne_zero_of_mul hp_nz
    dsimp [descriptorCheckZChain] at h_ch
    split_ifs at h_ch with h_cond
    · rcases h_cond with ⟨_, nb, h_in, h_sh, _⟩
      refine ⟨p.1, ?_, h_supp p (Or.inr hb)⟩
      rw [staticCSSCheckSupport, ← h_sh]
      exact shiftOpenBox_neighborhoodOffset_mem_boxBall v nb h_in
    · exact False.elim (h_ch rfl)

lemma abs_worldlineBareAction_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA c_wl β : ℝ} (hβ : 0 ≤ β)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ) :
    |worldlineBareAction D_field sys γ.1 σ₀ β τ| ≤
      c_wl * (γ.1.length : ℝ) * β := by
  unfold worldlineBareAction
  have hc_wl_nn : 0 ≤ c_wl := le_trans (Nat.cast_nonneg _) hc_wl_cal
  have hC_nn : 0 ≤ (γ.1.length : ℝ) * c_wl := mul_nonneg (Nat.cast_nonneg _) hc_wl_nn
  have h_traj_le : ∀ t ∈ Set.Icc 0 β,
      |sys.syndromeEnergy (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) -
        sys.syndromeEnergy σ₀| ≤ (γ.1.length : ℝ) * c_wl := by
    intro t _
    unfold worldlineTrajectorySyndrome
    let l := (List.finRange γ.1.length).filter (fun j => decide (τ j ≤ t))
    have hl_len : (l.length : ℝ) ≤ (γ.1.length : ℝ) := by
      have h_nat : l.length ≤ γ.1.length := by
        calc l.length
          _ ≤ (List.finRange γ.1.length).length := List.length_filter_le _ _
          _ = γ.1.length := List.length_finRange
      exact_mod_cast h_nat
    have h_fold := abs_syndromeEnergy_foldr_syndromeXor_sub_le sys
      (fun idx => (h_sys_checks idx).2.2)
      (fun j => staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2)
      (fun j => cubeIntersectingChecks sys (γ.1.get j).1.2)
      c_wl hc_wl_nn l
      (fun j _ => by
        let ξ := γ.1.get j
        have hξ_mem : ξ ∈ γ.1 := List.get_mem γ.1 j
        have hp_mem : ξ.1 ∈ worldlinePolymerMonomers γ :=
          Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ_mem))
        rcases mem_scaleCubeFinset_iff.mp (hγ.1 ξ.1 hp_mem) with ⟨hr, hA⟩
        refine ⟨fun c hc => staticCSSPauliFlip_mem_cubeIntersectingChecks D_field sys
          (fun idx => (h_sys_checks idx).2.1) ξ.1.2 ξ.2.1 ξ.2.2 (hγ.2.1 ξ hξ_mem).1 c hc,
          le_trans (Nat.cast_le.mpr
            (card_cubeIntersectingChecks_le_kpCollarMaxCheckCard sys h_geom C_RCA hr hA))
            hc_wl_cal⟩)
      σ₀
    exact le_trans h_fold (mul_le_mul_of_nonneg_right hl_len hc_wl_nn)
  calc |∫ t in Set.Icc 0 β,
        (sys.syndromeEnergy (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) -
          sys.syndromeEnergy σ₀)|
    _ ≤ β * ((γ.1.length : ℝ) * c_wl) :=
        abs_setIntegral_Icc_le_of_abs_le hβ hC_nn _ h_traj_le
    _ = c_wl * (γ.1.length : ℝ) * β := by ring

lemma abs_exp_neg_worldlineBareAction_mul_prod_mayer_le
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA c_wl β J : ℝ} {f : ℕ → ℝ}
    (hβ : 0 ≤ β) (hJ : 0 ≤ J) (hf_nn : ∀ r, 0 ≤ f r)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_bound : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ∀ σ,
      |d_loc r A σ| ≤ 2 * (J * f r))
    (γ : WorldlineDysonPolymer L q_code)
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ) :
    |Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
      ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ| ≤
      Real.exp (c_wl * (γ.1.length : ℝ) * β) *
        ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod]
  have h_bare := abs_worldlineBareAction_le hβ D_field sys h_sys_checks h_geom hc_wl_cal γ hγ σ₀ τ
  have h_exp : Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) ≤
      Real.exp (c_wl * (γ.1.length : ℝ) * β) :=
    Real.exp_le_exp.mpr (le_trans (neg_le_abs _) h_bare)
  have h_prod : ∏ ϑ ∈ γ.2, |worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ| ≤
      ∏ ϑ ∈ γ.2, 4 * β * J * f ϑ.1 * Real.exp (4 * β * J * f ϑ.1) := by
    refine Finset.prod_le_prod₀ (fun ϑ _ => abs_nonneg _) (fun ϑ hϑ => ?_)
    exact abs_worldlineMayerBondFactor_le hβ hJ D_field sys f hf_nn d_loc hd_bound γ hγ σ₀ τ hϑ
  exact mul_le_mul h_exp h_prod (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    (Real.exp_nonneg _)

/-- Polymer incompatibility predicate under native-collar overlap `C̄(γ₁) ∩ C̄(γ₂) ≠ ∅`
    (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
def ArePolymersIncompatible {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (γ₁ γ₂ : WorldlineDysonPolymer L q_code) : Prop :=
  ¬Disjoint (worldlinePolymerNativeCollar sys C_RCA γ₁)
    (worldlinePolymerNativeCollar sys C_RCA γ₂)

/-- Hard-core Mayer polymer-gas configuration weight for a polymer tuple `K : WorldlineUrsellCluster L q_code`
    in joint syndrome-logical sector `(σ, ν)` (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
    vanishes unless every polymer in `K` is valid and
    the polymers are pairwise collar-compatible (`¬ArePolymersIncompatible sys C_RCA`), in which
    case it equals `(K.length ! : ℝ)⁻¹ * ∏ γ ∈ K, w_β(γ; σ, ν)`. -/
def worldlineMayerPolymerClusterWeight
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) : ℝ :=
  if (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) then
    (Nat.factorial K.length : ℝ)⁻¹ *
      (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod
  else 0

/-- Exact worldline Mayer polymer-gas partition function $Z_{\mathrm{poly}}(\sigma, \nu)$ in
    joint syndrome-logical sector $(\sigma, \nu)$ (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
def worldlineMayerPolymerPartition
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
  ∑' K : WorldlineUrsellCluster L q_code,
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K

/-- Strict positivity of the vacuum projector trace `hilbertTrace sys.P0 > 0` and vacuum
    normalization constant `K_norm = hilbertTrace sys.P0 * Real.exp (-β * E_vac) > 0`
    under `ValidDescriptorField D_field`. -/
lemma vacuumPartitionNorm_pos_of_validDescriptorField
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (β E_vac : ℝ) :
    0 < hilbertTrace sys.P0 * Real.exp (-β * E_vac) := by
  have h_res := _root_.syndrome_resolution_indexed sys
  have hP0_ne : sys.P0 ≠ 0 := by
    intro hP0
    have h_tr0 : hilbertTrace sys.P0 = 0 := by unfold hilbertTrace; simp [hP0]
    have h_all_zero : ∀ σ, sys.syndromeProjector σ = 0 := fun σ => by
      by_contra h_ne
      have h_eq := (hilbertTrace_syndromeProjector_eq_P0_of_ne_zero
        D_field h_valid sys h_sys_checks σ h_ne).2
      have h_ex : ∃ ω : ManyBodyConfig (SiteCSS[L, q_code]),
          sys.syndromeProjector σ (basisVecGlobal (SiteCSS[L, q_code]) ω) ≠ 0 := by
        by_contra! h_all
        apply h_ne
        ext φ y
        have h_sum : φ = ∑ τ : ManyBodyConfig (SiteCSS[L, q_code]),
            (φ.ofLp τ) • basisVecGlobal (SiteCSS[L, q_code]) τ := by
          ext τ; simp [basisVecGlobal, WithLp.ofLp_sum]
        conv_lhs => rw [h_sum]
        rw [map_sum]; simp [h_all]
      rcases h_ex with ⟨ω₀, hω₀⟩
      have h_tr_eq : hilbertTrace (sys.syndromeProjector σ) =
          ∑ ω : ManyBodyConfig (SiteCSS[L, q_code]),
            ‖sys.syndromeProjector σ (basisVecGlobal (SiteCSS[L, q_code]) ω)‖ ^ 2 := by
        unfold hilbertTrace
        exact Finset.sum_congr rfl fun ω _ =>
          isStarProjection_re_inner_eq_norm_sq (h_res.2.1 σ) (basisVecGlobal (SiteCSS[L, q_code]) ω)
      have h_pos : 0 < hilbertTrace (sys.syndromeProjector σ) := by
        rw [h_tr_eq]
        exact lt_of_lt_of_le (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hω₀))
          (Finset.single_le_sum
            (fun ω _ => sq_nonneg ‖sys.syndromeProjector σ (basisVecGlobal (SiteCSS[L, q_code]) ω)‖)
            (Finset.mem_univ ω₀))
      linarith
    have h_one_zero : (1 : ℬ_CSS[L, q_code]) = 0 := by
      rw [← h_res.2.2.2.1]
      exact Finset.sum_eq_zero fun σ _ => h_all_zero σ
    let ω₀ : ManyBodyConfig (SiteCSS[L, q_code]) := fun _ _ => false
    have h_app := congr_arg
      (fun T : ℬ_CSS[L, q_code] => (T (basisVecGlobal (SiteCSS[L, q_code]) ω₀)).ofLp ω₀)
      h_one_zero
    simp [basisVecGlobal] at h_app
  have h_ex : ∃ ω : ManyBodyConfig (SiteCSS[L, q_code]),
      sys.P0 (basisVecGlobal (SiteCSS[L, q_code]) ω) ≠ 0 := by
    by_contra! h_all
    apply hP0_ne
    ext φ y
    have h_sum : φ = ∑ τ : ManyBodyConfig (SiteCSS[L, q_code]),
        (φ.ofLp τ) • basisVecGlobal (SiteCSS[L, q_code]) τ := by
      ext τ; simp [basisVecGlobal, WithLp.ofLp_sum]
    conv_lhs => rw [h_sum]
    rw [map_sum]; simp [h_all]
  rcases h_ex with ⟨ω₀, hω₀⟩
  have hP0_proj : IsStarProjection sys.P0 := by
    rw [← h_res.1]; exact h_res.2.1 (fun _ => false)
  have h_tr_eq : hilbertTrace sys.P0 =
      ∑ ω : ManyBodyConfig (SiteCSS[L, q_code]),
        ‖sys.P0 (basisVecGlobal (SiteCSS[L, q_code]) ω)‖ ^ 2 := by
    unfold hilbertTrace
    exact Finset.sum_congr rfl fun ω _ =>
      isStarProjection_re_inner_eq_norm_sq hP0_proj (basisVecGlobal (SiteCSS[L, q_code]) ω)
  have hP0_pos : 0 < hilbertTrace sys.P0 := by
    rw [h_tr_eq]
    exact lt_of_lt_of_le (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hω₀))
      (Finset.single_le_sum
        (fun ω _ => sq_nonneg ‖sys.P0 (basisVecGlobal (SiteCSS[L, q_code]) ω)‖)
        (Finset.mem_univ ω₀))
  exact mul_pos hP0_pos (Real.exp_pos _)

/-- **Collar Containment of Cube-Intersecting Checks (`cubeIntersectingChecks_subset_rcaCollarChecks`)**:
    Whenever `1 + 4 * (r_0 : ℝ) ≤ C_RCA` and `1 ≤ r`, every check whose support intersects
    `A ∈ boxCubes 3 L r` is supported inside `rcaCollarCube C_RCA r A`,
    i.e., `cubeIntersectingChecks sys A ⊆ rcaCollarChecks sys C_RCA r A`
    (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:B-delta-shift`). -/
lemma cubeIntersectingChecks_subset_rcaCollarChecks
    {L q_code r_0 m_max w_0 : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max])
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    {r : ℕ} (hr1 : 1 ≤ r) {A : Finset (Box3D L)} (hA : A ∈ boxCubes 3 L r) :
    cubeIntersectingChecks sys A ⊆ rcaCollarChecks sys C_RCA r A := by
  intro c hc
  simp only [cubeIntersectingChecks, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  rcases Finset.not_disjoint_iff.mp hc with ⟨y, hy_supp, hy_A⟩
  rcases h_geom.1 c with ⟨v, hv⟩
  have hyv : y ∈ boxBall v r_0 := hv hy_supp
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hyv
  let x0 := anchorOfCube r A
  have hA_eq : boxCube x0 r = A := boxCube_anchorOfCube hA
  rw [← hA_eq, mem_boxCube] at hy_A
  let R := linearExpansionRadius C_RCA r
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hR_real : ((r + 4 * r_0 : ℕ) : ℝ) ≤ C_RCA * (r : ℝ) := by
    push_cast
    nlinarith
  have hR_bound : r + 4 * r_0 ≤ R :=
    Nat.cast_le (α := ℝ).mp (le_trans hR_real (Nat.le_ceil (C_RCA * (r : ℝ))))
  simp only [rcaCollarChecks, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [rcaCollarCube, enclosingBoxCube]
  intro z hz_supp
  have hzv : z ∈ boxBall v r_0 := hv hz_supp
  simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hzv
  rw [mem_boxCube]
  intro i
  have hy_dist : coordDist (v i) (y i) ≤ r_0 :=
    le_trans (Finset.le_sup (f := fun j => coordDist (v j) (y j)) (Finset.mem_univ i)) hyv
  have hz_dist : coordDist (v i) (z i) ≤ r_0 :=
    le_trans (Finset.le_sup (f := fun j => coordDist (v j) (z j)) (Finset.mem_univ i)) hzv
  have hy_i := hy_A i
  dsimp [coordDist, x0, R] at hy_dist hz_dist hy_i hR_bound ⊢
  omega

/-- **Native-Collar Containment of Jump Flips (`staticCSSPauliFlip_mem_worldlinePolymerNativeCollar`)**:
    For any valid worldline polymer `γ` (`IsValidWorldlinePolymer`) and any jump `ξ ∈ γ.1`, every
    check `c` flipped by `ξ` belongs to the polymer's native collar `worldlinePolymerNativeCollar sys C_RCA γ`
    (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`) and Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma staticCSSPauliFlip_mem_worldlinePolymerNativeCollar
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ξ : WorldlineJumpMonomer L q_code} (hξ : ξ ∈ γ.1)
    {c : IdxCSS[L, q_code, m_max]}
    (hc : staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c = true) :
    c ∈ worldlinePolymerNativeCollar sys C_RCA γ := by
  have hp_mem : ξ.1 ∈ worldlinePolymerMonomers γ :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))
  rcases mem_scaleCubeFinset_iff.mp (hγ.1 ξ.1 hp_mem) with ⟨hr, hA⟩
  have hr1 : 1 ≤ ξ.1.1 := (Finset.mem_Icc.mp hr).1
  have hc_inter : c ∈ cubeIntersectingChecks sys ξ.1.2 :=
    staticCSSPauliFlip_mem_cubeIntersectingChecks D_field sys h_sys_supp ξ.1.2 ξ.2.1 ξ.2.2
      (hγ.2.1 ξ hξ).1 c hc
  have hc_col : c ∈ rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2 :=
    cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le hr1 hA hc_inter
  unfold worldlinePolymerNativeCollar nativeCollarSupport
  exact Finset.mem_biUnion.mpr ⟨ξ.1, hp_mem, hc_col⟩

lemma foldr_syndromeXor_eq_of_all_false
    {α : Type*} {L q_code m_max : ℕ}
    (δ_fn : α → IdxCSS[L, q_code, m_max] → Bool)
    (l : List α) (c : IdxCSS[L, q_code, m_max])
    (h_false : ∀ x ∈ l, δ_fn x c = false)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    (l.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀) c = σ₀ c := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldr_cons]
    have h_hd : δ_fn hd c = false := h_false hd List.mem_cons_self
    have h_tl : (tl.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀) c = σ₀ c :=
      ih (fun x hx => h_false x (List.mem_cons_of_mem hd hx))
    change bne (δ_fn hd c) ((tl.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀) c) = σ₀ c
    rw [h_hd, h_tl]
    cases σ₀ c <;> rfl

lemma foldr_syndromeXor_congr_at_check
    {α : Type*} {L q_code m_max : ℕ}
    (δ_fn : α → IdxCSS[L, q_code, m_max] → Bool)
    (l : List α) (c : IdxCSS[L, q_code, m_max])
    {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool} (h_eq : σ₁ c = σ₂ c) :
    (l.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₁) c =
      (l.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₂) c := by
  induction l with
  | nil => exact h_eq
  | cons hd tl ih =>
    rw [List.foldr_cons, List.foldr_cons]
    change bne (δ_fn hd c) ((tl.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₁) c) =
      bne (δ_fn hd c) ((tl.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₂) c)
    rw [ih]

/-- **Native-Collar Trajectory Invariance (`worldlineTrajectorySyndrome_eq_outside_and_congr_on_nativeCollar`)**:
    For any valid worldline polymer `γ`:
    1. Every check `c ∉ worldlinePolymerNativeCollar sys C_RCA γ` is invariant along the intermediate
       trajectory: `worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t c = σ₀ c`.
    2. If `σ₁` and `σ₂` agree on `worldlinePolymerNativeCollar sys C_RCA γ`, then their trajectories
       agree on `worldlinePolymerNativeCollar sys C_RCA γ` at every Euclidean time `t`, and both
       `worldlineBareAction` and `worldlineMayerBondFactor` (for all `ϑ ∈ γ.2`) are identical on `σ₁` and `σ₂`.
    3. In particular, evaluating `worldlineBareAction` and `worldlineMayerBondFactor` on
       `restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ` gives the exact same
       value as on the full syndrome `σ` (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlineTrajectorySyndrome_eq_outside_and_congr_on_nativeCollar
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA J β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (τ : Fin γ.1.length → ℝ) :
    (∀ (σ₀ : IdxCSS[L, q_code, m_max] → Bool) (t : ℝ) (c : IdxCSS[L, q_code, m_max]),
      c ∉ worldlinePolymerNativeCollar sys C_RCA γ →
      worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t c = σ₀ c) ∧
    (∀ {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool},
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ₁ c = σ₂ c) →
      worldlineBareAction D_field sys γ.1 σ₁ β τ =
        worldlineBareAction D_field sys γ.1 σ₂ β τ ∧
      ∀ ϑ ∈ γ.2,
        worldlineMayerBondFactor D_field γ.1 d_loc σ₁ β ϑ τ =
          worldlineMayerBondFactor D_field γ.1 d_loc σ₂ β ϑ τ) ∧
    (∀ (σ : IdxCSS[L, q_code, m_max] → Bool),
      let σ₀ := restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ
      worldlineBareAction D_field sys γ.1 σ₀ β τ =
        worldlineBareAction D_field sys γ.1 σ β τ ∧
      ∀ ϑ ∈ γ.2,
        worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ =
          worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ) := by
  have h_out : ∀ (σ₀ : IdxCSS[L, q_code, m_max] → Bool) (t : ℝ) (c : IdxCSS[L, q_code, m_max]),
      c ∉ worldlinePolymerNativeCollar sys C_RCA γ →
      worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t c = σ₀ c := by
    intro σ₀ t c hc_not
    unfold worldlineTrajectorySyndrome
    refine foldr_syndromeXor_eq_of_all_false
      (fun j => staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2)
      ((List.finRange γ.1.length).filter (fun j => decide (τ j ≤ t))) c (fun j _ => ?_) σ₀
    (try dsimp only)
    cases h_flip : staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2 c
    · rfl
    · exact False.elim (hc_not (staticCSSPauliFlip_mem_worldlinePolymerNativeCollar
        D_field sys (fun idx => (h_sys_checks idx).2.1) h_geom hr0_le hγ (List.get_mem γ.1 j) h_flip))
  have h_congr : ∀ {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool},
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ₁ c = σ₂ c) →
      worldlineBareAction D_field sys γ.1 σ₁ β τ =
        worldlineBareAction D_field sys γ.1 σ₂ β τ ∧
      ∀ ϑ ∈ γ.2,
        worldlineMayerBondFactor D_field γ.1 d_loc σ₁ β ϑ τ =
          worldlineMayerBondFactor D_field γ.1 d_loc σ₂ β ϑ τ := by
    intro σ₁ σ₂ h_agree
    have h_traj_col : ∀ (t : ℝ) (c : IdxCSS[L, q_code, m_max]),
        c ∈ worldlinePolymerNativeCollar sys C_RCA γ →
        worldlineTrajectorySyndrome D_field γ.1 σ₁ τ t c =
          worldlineTrajectorySyndrome D_field γ.1 σ₂ τ t c := fun t c hc =>
      foldr_syndromeXor_congr_at_check
        (fun j => staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2)
        ((List.finRange γ.1.length).filter (fun j => decide (τ j ≤ t))) c (h_agree c hc)
    refine ⟨?_, fun ϑ hϑ => ?_⟩
    · unfold worldlineBareAction
      congr 1; funext t
      have h_en : ∀ σ₀ : IdxCSS[L, q_code, m_max] → Bool,
          sys.syndromeEnergy (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) -
            sys.syndromeEnergy σ₀ =
          ∑ c ∈ worldlinePolymerNativeCollar sys C_RCA γ,
            ((if worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t c = true then (1 : ℝ) else 0) -
              (if σ₀ c = true then (1 : ℝ) else 0)) := by
        intro σ₀
        have h_wt_eq : ∀ η : IdxCSS[L, q_code, m_max] → Bool,
            sys.syndromeEnergy η =
              ∑ c : IdxCSS[L, q_code, m_max], if η c = true then (1 : ℝ) else 0 := fun η => by
          unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun c _ => by rw [(h_sys_checks c).2.2]
        rw [h_wt_eq, h_wt_eq, ← Finset.sum_sub_distrib]
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun c _ hc_not => ?_
        rw [h_out σ₀ t c hc_not, sub_self]
      rw [h_en σ₁, h_en σ₂]
      exact Finset.sum_congr rfl fun c hc => by rw [h_traj_col t c hc, h_agree c hc]
    · unfold worldlineMayerBondFactor
      have hp_mem : ϑ ∈ worldlinePolymerMonomers γ := Finset.mem_union_right _ hϑ
      rcases mem_scaleCubeFinset_iff.mp (hγ.1 ϑ hp_mem) with ⟨hr, hA⟩
      have h_sub : rcaCollarChecks sys C_RCA ϑ.1 ϑ.2 ⊆ worldlinePolymerNativeCollar sys C_RCA γ := by
        intro c hc
        unfold worldlinePolymerNativeCollar nativeCollarSupport
        exact Finset.mem_biUnion.mpr ⟨ϑ, hp_mem, hc⟩
      have h_int_eq :
          (∫ t in Set.Icc 0 β,
            (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₁ τ t) - d_loc ϑ.1 ϑ.2 σ₁)) =
          ∫ t in Set.Icc 0 β,
            (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₂ τ t) - d_loc ϑ.1 ϑ.2 σ₂) := by
        congr 1; funext t
        have hd_traj := (h_scalar ϑ.1 hr ϑ.2 hA).2.2
          (worldlineTrajectorySyndrome D_field γ.1 σ₁ τ t)
          (worldlineTrajectorySyndrome D_field γ.1 σ₂ τ t)
          (fun c hc => h_traj_col t c (h_sub hc))
        have hd_base := (h_scalar ϑ.1 hr ϑ.2 hA).2.2 σ₁ σ₂ (fun c hc => h_agree c (h_sub hc))
        rw [hd_traj, hd_base]
      rw [h_int_eq]
  refine ⟨h_out, h_congr, fun σ => h_congr fun c hc => ?_⟩
  unfold restrictSyndromeToCollar
  rw [if_pos hc]

/-- **Empty-Witness Partition Identity (`gibbsPartitionZ_eq_hilbertTrace_empty_witness`)**:
    The full Gibbs partition function `gibbsPartitionZ` equals the witness trace at `W = ∅`,
    and filtering `realizableSyndromes D_field` by `∀ idx ∈ (∅ : Finset _), σ idx = true` leaves
    `realizableSyndromes D_field` unchanged. -/
lemma gibbsPartitionZ_eq_hilbertTrace_empty_witness
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (H : ℬ_CSS[L, q_code]) (hH : IsSelfAdjoint H) (β : ℝ) :
    gibbsPartitionZ (opEigenvalues H hH) β =
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
        positiveCheckWitnessProj sys ∅) ∧
    (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ (∅ : Finset (IdxCSS[L, q_code, m_max])),
      σ idx = true) = realizableSyndromes D_field := by
  refine ⟨?_, Finset.filter_eq_self.mpr fun _ _ idx hidx => False.elim (Finset.notMem_empty idx hidx)⟩
  rw [positiveCheckWitnessProj_empty_eq_one sys,
    perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ H hH β]

/-- **Singleton Ursell Coefficient (`ursellConnectedGraphCoeff_singleton`)**:
    For any single worldline polymer `γ`, the Ursell connected-graph coefficient of the singleton
    cluster `[γ]` is `ursellConnectedGraphCoeff sys C_RCA [γ] = 1`, and its cluster Ursell weight
    equals `worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ`. -/
lemma ursellConnectedGraphCoeff_singleton
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (γ : WorldlineDysonPolymer L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    ursellConnectedGraphCoeff sys C_RCA [γ] = 1 ∧
    worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν [γ] σ =
      worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ := by
  have h_coeff : ursellConnectedGraphCoeff sys C_RCA [γ] = 1 := by
    unfold ursellConnectedGraphCoeff
    let E_compat : Finset (Fin ([γ].length) × Fin ([γ].length)) :=
      Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA [γ] e.1 e.2)
    have hE_empty : E_compat = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      have h_lt := (Finset.mem_filter.mp he).2.1
      have h1 := e.1.isLt
      have h2 := e.2.isLt
      change e.1.val < 1 at h1
      change e.2.val < 1 at h2
      have : e.1.val < e.2.val := h_lt
      omega
    have h_conn : KPIsConnectedSubgraph
        (fun a b : Fin ([γ].length) => (a, b) ∈ (∅ : Finset _) ∨ (b, a) ∈ (∅ : Finset _))
        Finset.univ := by
      refine ⟨⟨⟨0, Nat.succ_pos 0⟩, Finset.mem_univ _⟩, fun u _ v _ => ?_⟩
      have hu := u.isLt; have hv := v.isLt
      change u.val < 1 at hu; change v.val < 1 at hv
      have h_eq : u = v := Fin.ext (by omega)
      subst h_eq
      exact Relation.ReflTransGen.refl
    change ((Nat.factorial 1 : ℝ)⁻¹) *
      ∑ G ∈ E_compat.powerset.filter (fun G =>
          KPIsConnectedSubgraph (fun a b => (a, b) ∈ G ∨ (b, a) ∈ G) Finset.univ),
        ((-1 : ℝ) ^ G.card) = 1
    rw [hE_empty, Finset.powerset_empty, Finset.filter_singleton, if_pos h_conn]
    norm_num
  refine ⟨h_coeff, ?_⟩
  unfold worldlineClusterUrsellWeight
  rw [h_coeff, one_mul, List.map_singleton, List.prod_singleton]

/-- **Zero-Weight Mayer–Ursell Cluster Logarithm (`worldlineMayerPolymerPartition_and_ursell_exp_of_zero_weights`)**:
    Whenever all valid worldline polymers have zero weight (`∀ γ, IsValidWorldlinePolymer ... γ → worldlinePolymerWeight ... γ σ = 0`,
    as holds at zero coupling `J = 0`), the Mayer polymer partition function
    `worldlineMayerPolymerPartition` equals `1` (from the empty polymer tuple `K = []`), every
    footprint Ursell weight `worldlineUrsellPhi` vanishes, and the Mayer–Ursell cluster logarithm
    identity `worldlineMayerPolymerPartition = exp (∑ Φ^T)` holds identically. -/
lemma worldlineMayerPolymerPartition_and_ursell_exp_of_zero_weights
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_zero : ∀ γ : WorldlineDysonPolymer L q_code,
      IsValidWorldlinePolymer D_field sys C_RCA R_cut γ →
      worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ = 0) :
    worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ = 1 ∧
    (∀ γ_f : WorldlineUrsellFootprint L q_code m_max,
      worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ_f σ = 0) ∧
    worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ =
      Real.exp (∑ γ_f ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
        worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ_f σ) := by
  have h_part : worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ = 1 := by
    unfold worldlineMayerPolymerPartition
    rw [tsum_eq_single ([] : WorldlineUrsellCluster L q_code)]
    · unfold worldlineMayerPolymerClusterWeight
      rw [if_pos ⟨fun _ h => False.elim (List.not_mem_nil h), List.Pairwise.nil⟩]
      norm_num
    · intro K hK_ne
      unfold worldlineMayerPolymerClusterWeight
      split_ifs with hK
      · rcases List.exists_mem_of_ne_nil K hK_ne with ⟨γ₀, hγ₀⟩
        have h_prod_zero :
            (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod = 0 :=
          List.prod_eq_zero (List.mem_map.mpr ⟨γ₀, hγ₀, h_zero γ₀ (hK.1 γ₀ hγ₀)⟩)
        rw [h_prod_zero, mul_zero]
      · rfl
  have h_phi : ∀ γ_f : WorldlineUrsellFootprint L q_code m_max,
      worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ_f σ = 0 := by
    intro γ_f
    unfold worldlineUrsellPhi
    have h_fn :
        (fun K : WorldlineUrsellCluster L q_code =>
          if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
              worldlineClusterMonomers K = γ_f.1 ∧
              worldlineClusterSpanningSurface D_field sys C_RCA K = γ_f.2
          then worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
          else 0) = fun _ => 0 := by
      funext K
      split_ifs with hK
      · unfold worldlineClusterUrsellWeight
        rcases List.exists_mem_of_ne_nil K hK.1.1 with ⟨γ₀, hγ₀⟩
        have h_prod_zero :
            (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod = 0 :=
          List.prod_eq_zero (List.mem_map.mpr ⟨γ₀, hγ₀, h_zero γ₀ (hK.1.2.1 γ₀ hγ₀)⟩)
        rw [h_prod_zero, mul_zero]
      · rfl
    rw [h_fn, tsum_zero]
  refine ⟨h_part, h_phi, ?_⟩
  rw [h_part, Finset.sum_eq_zero (fun γ_f _ => h_phi γ_f), Real.exp_zero]

/-- The trivial Pauli bitstring pair `(0, 0)` belongs to
`syndromeClosedPauliFinset D_field`, so `(syndromeClosedPauliFinset D_field).card > 0` and
averaging a constant over `ν ∈ syndromeClosedPauliFinset D_field` with weight `N_closed⁻¹`
acts as the identity (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:pinching-group-average`). -/
lemma zero_mem_syndromeClosedPauliFinset_and_sum_inv
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (X : ℝ) :
    ((0, 0) : PauliBitstringPair L q_code) ∈
      syndromeClosedPauliFinset D_field ∧
    0 < ((syndromeClosedPauliFinset D_field).card : ℝ) ∧
    (∑ _ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ * X) = X := by
  have h_mem :
      ((0, 0) : PauliBitstringPair L q_code) ∈
        syndromeClosedPauliFinset D_field := by
    simp only [syndromeClosedPauliFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    funext idx
    rcases idx with ⟨v, s⟩ | ⟨v, i⟩ | ⟨v, i⟩ <;> simp [staticCSSPauliFlip]
  have h_nonempty : (syndromeClosedPauliFinset D_field).Nonempty := ⟨_, h_mem⟩
  have h_card_pos : 0 < ((syndromeClosedPauliFinset D_field).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr h_nonempty
  refine ⟨h_mem, h_card_pos, ?_⟩
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt h_card_pos), one_mul]

lemma worldlinePolymerMonomers_subset_worldlineClusterMonomers'
    {L q_code : ℕ} {K : WorldlineUrsellCluster L q_code} {γ : WorldlineDysonPolymer L q_code}
    (hγ : γ ∈ K) :
    worldlinePolymerMonomers γ ⊆ worldlineClusterMonomers K := by
  induction K with
  | nil => cases hγ
  | cons hd tl ih =>
    rcases List.mem_cons.mp hγ with rfl | h_tl
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih h_tl) Finset.subset_union_right

lemma worldlineClusterMonomers_subset_scaleCubeFinset
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    {K : WorldlineUrsellCluster L q_code}
    (h_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    worldlineClusterMonomers K ⊆ worldlineScaleCubeFinset L R_cut := by
  induction K with
  | nil =>
    intro p hp
    simp [worldlineClusterMonomers] at hp
  | cons hd tl ih =>
    intro p hp
    unfold worldlineClusterMonomers at hp
    rcases Finset.mem_union.mp hp with hp_hd | hp_tl
    · exact (h_valid hd List.mem_cons_self).1 p hp_hd
    · exact ih (fun γ hγ => h_valid γ (List.mem_cons_of_mem hd hγ)) hp_tl

/-- Every valid Ursell cluster `K` (`isValidWorldlineUrsellCluster D_field sys C_RCA R_cut K`)
has its footprint `(worldlineClusterMonomers K, worldlineClusterSpanningSurface D_field sys C_RCA K)`
inside the finite cutoff index set `worldlineUrsellIndexFinset L q_code m_max R_cut`. -/
lemma worldlineClusterFootprint_mem_worldlineUrsellIndexFinset
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    {K : WorldlineUrsellCluster L q_code}
    (hK : IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K) :
    (worldlineClusterMonomers K, worldlineClusterSpanningSurface D_field sys C_RCA K) ∈
      worldlineUrsellIndexFinset L q_code m_max R_cut := by
  unfold worldlineUrsellIndexFinset
  rw [Finset.mem_product]
  refine ⟨?_, Finset.mem_powerset.mpr (Finset.subset_univ _)⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨worldlineClusterMonomers_subset_scaleCubeFinset D_field sys hK.2.1, ?_⟩
  rcases List.exists_mem_of_ne_nil K hK.1 with ⟨γ₀, hγ₀⟩
  have hγ₀_valid := hK.2.1 γ₀ hγ₀
  have h_ne : γ₀.1 ≠ [] := by
    intro h_nil
    have h_len := hγ₀_valid.2.2.1.1
    rw [h_nil, List.length_nil] at h_len
    omega
  rcases List.exists_mem_of_ne_nil γ₀.1 h_ne with ⟨ξ₀, hξ₀⟩
  refine ⟨ξ₀.1, worldlinePolymerMonomers_subset_worldlineClusterMonomers' hγ₀ ?_⟩
  unfold worldlinePolymerMonomers
  exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₀))

/-- **Additivity of Syndrome Energy Shifts for Disjoint Defect Syndromes**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:energy-additivity-disjoint-loops`):
Whenever two syndrome shifts `δ₁, δ₂` have disjoint supports (`∀ idx, δ₁ idx = true → δ₂ idx = false`),
the unperturbed `H_0` energy increment is strictly additive:
$E_{\mathrm{synd}}(\sigma \oplus \delta_1 \oplus \delta_2) - E_{\mathrm{synd}}(\sigma) =
[E_{\mathrm{synd}}(\sigma \oplus \delta_1) - E_{\mathrm{synd}}(\sigma)] +
[E_{\mathrm{synd}}(\sigma \oplus \delta_2) - E_{\mathrm{synd}}(\sigma)]$. -/
lemma syndromeEnergy_syndromeXor_disjoint_add
    {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max])
    (σ δ₁ δ₂ : IdxCSS[L, q_code, m_max] → Bool)
    (h_disj : ∀ idx, δ₁ idx = true → δ₂ idx = false) :
    sys.syndromeEnergy (syndromeXor (syndromeXor σ δ₁) δ₂) - sys.syndromeEnergy σ =
      (sys.syndromeEnergy (syndromeXor σ δ₁) - sys.syndromeEnergy σ) +
        (sys.syndromeEnergy (syndromeXor σ δ₂) - sys.syndromeEnergy σ) := by
  unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy syndromeXor
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  have h_idx := h_disj idx
  cases σ idx <;> cases h1 : δ₁ idx <;> cases h2 : δ₂ idx
  · simp
  · simp
  · simp
  · have := h_idx h1; rw [h2] at this; cases this
  · simp
  · simp
  · simp
  · have := h_idx h1; rw [h2] at this; cases this

/-- For the trivial logical coset `(0, 0) : PauliBitstringPair L q_code`, the symplectic
character `symplecticPauliSign ν (0, 0)` equals `1` for every `ν`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma symplecticPauliSign_zero_right
    {L q_code : ℕ} (ν : PauliBitstringPair L q_code) :
    symplecticPauliSign ν (0, 0) = 1 := by
  unfold symplecticPauliSign
  simp

/-- **Vanishing of Mayer Bond Factors on Spectator Collar Cubes**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Equation `eq:mayer-factor-eta-def`):
If a scale-cube `ϑ = (r, A)` has its check collar `rcaCollarChecks sys C_RCA ϑ.1 ϑ.2` disjoint
from a check set `S` that contains all syndrome flips along a jump trajectory `jumps`, then
`d_loc ϑ.1 ϑ.2` is constant along `worldlineTrajectorySyndrome D_field jumps σ₀ τ t`, so
`worldlineMayerBondFactor D_field jumps d_loc σ₀ β ϑ τ = 0`. -/
lemma worldlineMayerBondFactor_eq_zero_of_agree_on_collar
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (jumps : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (β : ℝ) (ϑ : ℕ × Finset (Box3D L))
    (hϑ_r : ϑ.1 ∈ Finset.Icc 1 (min R_cut L))
    (hϑ_A : ϑ.2 ∈ boxCubes 3 L ϑ.1)
    (τ : Fin jumps.length → ℝ)
    (h_const : ∀ t : ℝ, ∀ c ∈ rcaCollarChecks sys C_RCA ϑ.1 ϑ.2,
      worldlineTrajectorySyndrome D_field jumps σ₀ τ t c = σ₀ c) :
    worldlineMayerBondFactor D_field jumps d_loc σ₀ β ϑ τ = 0 := by
  unfold worldlineMayerBondFactor
  have h_integrand :
      (fun t : ℝ =>
        d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field jumps σ₀ τ t) - d_loc ϑ.1 ϑ.2 σ₀) =
      fun _ => 0 := by
    funext t
    have h_eq := (h_scalar ϑ.1 hϑ_r ϑ.2 hϑ_A).2.2
      (worldlineTrajectorySyndrome D_field jumps σ₀ τ t) σ₀ (h_const t)
    linarith
  rw [h_integrand, MeasureTheory.integral_zero, neg_zero, Real.exp_zero, sub_self]

/-- Classical Mayer inclusion-exclusion identity on the powerset of an incompatibility edge set `E`:
`∑ G ∈ E.powerset, (-1 : ℝ) ^ G.card = if E = ∅ then 1 else 0`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
lemma sum_powerset_neg_one_pow_card
    {α : Type*} [DecidableEq α] (E : Finset α) :
    (∑ G ∈ E.powerset, (-1 : ℝ) ^ G.card) = if E = ∅ then 1 else 0 := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [if_neg (Finset.insert_ne_empty a s), Finset.powerset_insert,
      Finset.sum_union (Finset.disjoint_left.mpr (by
        intro t ht₁ ht₂
        rcases Finset.mem_image.mp ht₂ with ⟨u, _, rfl⟩
        exact ha (Finset.mem_powerset.mp ht₁ (Finset.mem_insert_self a u)))),
      Finset.sum_image (by
        intro x hx y hy hxy
        have hx_a : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
        have hy_a : a ∉ y := fun h => ha (Finset.mem_powerset.mp hy h)
        simpa [Finset.erase_insert hx_a, Finset.erase_insert hy_a] using
          congrArg (fun t => Finset.erase t a) hxy)]
    have h_img :
        (∑ x ∈ s.powerset, (-1 : ℝ) ^ (insert a x).card) =
          -(∑ x ∈ s.powerset, (-1 : ℝ) ^ x.card) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx_a : a ∉ x := fun h => ha (Finset.mem_powerset.mp hx h)
      rw [Finset.card_insert_of_notMem hx_a, pow_succ]
      ring
    rw [h_img, add_neg_cancel]

/-- Equivalence between `K.Pairwise (fun γ₁ γ₂ => ¬arePolymersIncompatible sys C_RCA γ₁ γ₂)`
and emptiness of the polymer incompatibility edge set `E_compat(K)` on `Fin K.length`. -/
lemma pairwise_not_incompatible_iff_edgeFinset_empty
    {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (K : WorldlineUrsellCluster L q_code) :
    K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) ↔
      (Finset.univ.filter (fun e : Fin K.length × Fin K.length =>
        e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)) = ∅ := by
  simp only [List.pairwise_iff_get, Finset.filter_eq_empty_iff, Finset.mem_univ,
    forall_true_left, Prod.forall]
  simp only [PolymerClusterOverlap, ArePolymersIncompatible, not_and]
  constructor
  · intro h_pw i j h_lt _ h_inc
    exact h_pw i j h_lt h_inc
  · intro h_empty i j h_lt h_inc
    exact h_empty i j h_lt (ne_of_lt h_lt) h_inc

/-- Mayer subgraph expansion of `worldlineMayerPolymerClusterWeight`: for any polymer tuple `K`
whose elements are valid worldline polymers, the hard-core exclusion indicator equals the sum
of `(-1) ^ G.card` over all spanning subgraphs `G` of the incompatibility graph `E_compat(K)`. -/
lemma worldlineMayerPolymerClusterWeight_eq_sum_powerset_edges
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    let E_compat : Finset (Fin K.length × Fin K.length) :=
      Finset.univ.filter (fun e => e.1 < e.2 ∧ PolymerClusterOverlap sys C_RCA K e.1 e.2)
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K =
      (Nat.factorial K.length : ℝ)⁻¹ *
        (∑ G ∈ E_compat.powerset, (-1 : ℝ) ^ G.card) *
        (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod := by
  intro E_compat
  unfold worldlineMayerPolymerClusterWeight
  rw [sum_powerset_neg_one_pow_card E_compat]
  by_cases h_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
  · have h_emp : E_compat = ∅ :=
      (pairwise_not_incompatible_iff_edgeFinset_empty sys C_RCA K).mp h_pw
    rw [if_pos ⟨hK_valid, h_pw⟩, if_pos h_emp, mul_one]
  · have h_ne : E_compat ≠ ∅ :=
      fun h_emp => h_pw ((pairwise_not_incompatible_iff_edgeFinset_empty sys C_RCA K).mpr h_emp)
    rw [if_neg (fun h => h_pw h.2), if_neg h_ne, mul_zero, zero_mul]

/-- Every valid worldline polymer `γ` (`IsValidWorldlinePolymer`) has a nonempty native check collar
`worldlinePolymerNativeCollar sys C_RCA γ`, because `2 ≤ γ.1.length` provides at least one jump
`ξ₀ ∈ γ.1` whose syndrome flip is non-trivial and supported inside `worldlinePolymerNativeCollar`. -/
lemma worldlinePolymerNativeCollar_nonempty_of_valid
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    (worldlinePolymerNativeCollar sys C_RCA γ).Nonempty ∧
    1 ≤ (worldlinePolymerNativeCollar sys C_RCA γ).card := by
  have h_ne : γ.1 ≠ [] := by
    intro h_nil
    have h_len := hγ.2.2.1.1
    rw [h_nil, List.length_nil] at h_len
    omega
  rcases List.exists_mem_of_ne_nil γ.1 h_ne with ⟨ξ₀, hξ₀⟩
  have h_flip_ne := (hγ.2.1 ξ₀ hξ₀).2.1
  have h_ex_c : ∃ c : IdxCSS[L, q_code, m_max],
      staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c = true := by
    by_contra! h_all
    apply h_flip_ne
    funext c
    cases h_val : staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c
    · rfl
    · exact False.elim (h_all c h_val)
  rcases h_ex_c with ⟨c, hc⟩
  have hc_mem := staticCSSPauliFlip_mem_worldlinePolymerNativeCollar
    D_field sys h_sys_supp h_geom hr0_le hγ hξ₀ hc
  exact ⟨⟨c, hc_mem⟩, Finset.card_pos.mpr ⟨c, hc_mem⟩⟩

/-- Hard-core finiteness bound for compatible polymer tuples (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`): any polymer tuple `K` whose polymers are valid and pairwise
collar-compatible (`¬ArePolymersIncompatible sys C_RCA`) has `K.length ≤ Fintype.card (IdxCSS[L, q_code, m_max])`,
so `worldlineMayerPolymerClusterWeight` vanishes whenever `K.length > Fintype.card (IdxCSS[L, q_code, m_max])`. -/
lemma length_le_card_checks_of_valid_and_pairwise_compatible
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)) :
    K.length ≤ Fintype.card (IdxCSS[L, q_code, m_max]) := by
  let S : Fin K.length → Finset (IdxCSS[L, q_code, m_max]) :=
    fun i => worldlinePolymerNativeCollar sys C_RCA (K.get i)
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_disj : ( ↑(Finset.univ : Finset (Fin K.length)) : Set (Fin K.length) ).PairwiseDisjoint S := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h_lt | h_gt
    · exact not_not.mp (h_pw_get i j h_lt)
    · exact (not_not.mp (h_pw_get j i h_gt)).symm
  calc K.length
    _ = ∑ _i : Fin K.length, 1 := by simp
    _ ≤ ∑ i : Fin K.length, (S i).card := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (worldlinePolymerNativeCollar_nonempty_of_valid
          D_field sys h_sys_supp h_geom hr0_le (hK_valid (K.get i) (List.get_mem K i))).2
    _ = ((Finset.univ : Finset (Fin K.length)).biUnion S).card :=
        (Finset.card_biUnion h_disj).symm
    _ ≤ (Finset.univ : Finset (IdxCSS[L, q_code, m_max])).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card (IdxCSS[L, q_code, m_max]) := Finset.card_univ

/-- Exact sector-by-sector evaluation of the Gibbs witness trace
`hilbertTrace (gibbsBoltzmannOp ... β * positiveCheckWitnessProj sys W)` whenever
`scaleSplitTruncatedOp V R_cut = pauliDiagonalPart sys V R_cut` (in particular when the
off-diagonal jump part vanishes, such as at `J = 0`). -/
lemma hilbertTrace_gibbsBoltzmannOp_pauliDiagonal_witness_eq
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (h_trunc_eq : scaleSplitTruncatedOp V R_cut = pauliDiagonalPart sys V R_cut)
    (W : Finset (IdxCSS[L, q_code, m_max])) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
    hilbertTrace (gibbsBoltzmannOp
      (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
      (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
        positiveCheckWitnessProj sys W) =
      K_norm * ∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
        Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) := by
  intro E_vac K_norm
  let H := sys.H0 + scaleSplitTruncatedOp V R_cut
  have h_res := _root_.syndrome_resolution_indexed sys
  have h_op : pauliDiagonalPart sys V R_cut - (((E_vac : ℝ) : ℂ) • 1) =
      ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r,
        pauliDiagonalShiftedTerm sys V e_loc r A := by
    ext χ i
    unfold pauliDiagonalPart pauliDiagonalShiftedTerm
    dsimp [E_vac]
    simp [Finset.sum_sub_distrib, Finset.sum_mul]
  have hH_comm : ∀ σ : IdxCSS[L, q_code, m_max] → Bool, Commute H (sys.syndromeProjector σ) := by
    intro σ
    dsimp [H]
    rw [h_trunc_eq]
    exact (Commute.sum_left _ _ _ fun c _ => (h_res.2.2.2.2.2.2.1 σ c).smul_left _).add_left
      (Commute.sum_left _ _ _ fun r _ => Commute.sum_left _ _ _ fun A _ =>
        (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)).2.1 σ |>.2.2)
  have h_sec_trace : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH_trunc)
          (opEigenvalues H hH_trunc) β * sys.syndromeProjector σ) =
        if σ ∈ realizableSyndromes D_field then
          K_norm * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ)
        else 0 := by
    intro σ
    by_cases hσ : σ ∈ realizableSyndromes D_field
    · rw [if_pos hσ]
      have h_tr_P0 : hilbertTrace sys.P0 = hilbertTrace (sys.syndromeProjector σ) := by
        rcases (Finset.mem_filter.mp hσ).2 with ⟨a, b, rfl⟩
        exact (hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0
          D_field h_valid sys h_sys_checks a b).symm
      let E_σ := E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc σ
      have h_shift_act :
          (pauliDiagonalPart sys V R_cut - ((E_vac : ℝ) : ℂ) • 1) * sys.syndromeProjector σ =
            ((∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ : ℝ) : ℂ) •
              sys.syndromeProjector σ := by
        rw [h_op, Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
        exact Finset.sum_congr rfl fun A hA => (h_scalar r hr A hA).1.1 σ hσ
      have h_P_H : sys.syndromeProjector σ * H = ((E_σ : ℝ) : ℂ) • sys.syndromeProjector σ := by
        rw [(hH_comm σ).symm.eq]
        have h_decomp : H = sys.H0 + (pauliDiagonalPart sys V R_cut - ((E_vac : ℝ) : ℂ) • 1) +
            ((E_vac : ℝ) : ℂ) • 1 := by
          dsimp [H]
          rw [h_trunc_eq]
          ext x i; simp; ring
        rw [h_decomp, add_mul, add_mul, h_res.2.2.2.2.1 σ, h_shift_act, smul_mul_assoc, one_mul]
        ext x i
        dsimp [E_σ, pauliDiagonalSectorEnergy]
        simp
        ring
      have h_rhs :
          K_norm * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) =
            ∑ ω : ManyBodyConfig (SiteCSS[L, q_code]),
              RCLike.re (inner ℂ (opEigenbasis H hH_trunc ω)
                (sys.syndromeProjector σ (opEigenbasis H hH_trunc ω))) *
                (Real.exp (-β * E_vac) * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ)) := by
        calc K_norm * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ)
          _ = hilbertTrace (sys.syndromeProjector σ) *
              (Real.exp (-β * E_vac) * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ)) := by
            dsimp [K_norm]; rw [h_tr_P0]; ring
          _ = _ := by
            rw [hilbertTrace_eq_sum_opEigenbasis H hH_trunc (sys.syndromeProjector σ), Finset.sum_mul]
      rw [hilbertTrace_gibbsBoltzmannOp_mul_eq, h_rhs]
      refine Finset.sum_congr rfl fun ω _ => ?_
      let ψ_ω := opEigenbasis H hH_trunc ω
      let E_ω := opEigenvalues H hH_trunc ω
      let t := RCLike.re (inner ℂ ψ_ω (sys.syndromeProjector σ ψ_ω))
      have h1 : (sys.syndromeProjector σ * H) ψ_ω = (E_ω : ℂ) • sys.syndromeProjector σ ψ_ω := by
        change sys.syndromeProjector σ (H ψ_ω) = _
        rw [opEigenbasis_apply_H H hH_trunc ω, map_smul]
      have h2 : (sys.syndromeProjector σ * H) ψ_ω = ((E_σ : ℝ) : ℂ) • sys.syndromeProjector σ ψ_ω := by
        rw [h_P_H, ContinuousLinearMap.smul_apply]
      have h_in := congr_arg (fun v => RCLike.re (inner ℂ ψ_ω v)) (h1.symm.trans h2)
      have h_eq_re : E_ω * t = E_σ * t := by
        simpa only [t, inner_smul_right, re_ofReal_mul] using h_in
      have h_zero : (E_ω - E_σ) * t = 0 := by linarith
      change Real.exp (-β * E_ω) * t =
        t * (Real.exp (-β * E_vac) * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ))
      rcases mul_eq_zero.mp h_zero with hE | ht
      · rw [sub_eq_zero.mp hE]; dsimp [E_σ]
        have h_add : -β * (E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc σ) =
            -β * E_vac + -β * pauliDiagonalSectorEnergy sys R_cut d_loc σ := by ring
        rw [h_add, Real.exp_add]; ring
      · rw [ht]; ring
    · rw [if_neg hσ]
      have h_zero : sys.syndromeProjector σ = 0 := by
        by_contra h_ne
        obtain ⟨⟨a, b, hab⟩, _⟩ :=
          hilbertTrace_syndromeProjector_eq_P0_of_ne_zero D_field h_valid sys h_sys_checks σ h_ne
        exact hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, a, b, hab⟩)
      rw [h_zero, mul_zero]; unfold hilbertTrace; simp
  unfold positiveCheckWitnessProj
  rw [Finset.mul_sum, hilbertTrace_sum]
  refine (Finset.sum_congr rfl fun x _ => h_sec_trace x).trans ?_
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  refine congrArg (K_norm * ·) (Finset.sum_congr ?_ fun _ _ => rfl)
  ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]

/-- **Scale-Split Operator Decomposition into Pauli-Diagonal and Off-Diagonal Jump Parts**
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equations `eq:pinching-def` and `eq:V-off-jump-decomp`):
The truncated perturbation `scaleSplitTruncatedOp V R_cut` decomposes as the sum of
`pauliDiagonalPart sys V R_cut` and the syndrome-off-diagonal jump terms
`∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, pauliOffDiagonalTerm sys V r A`. -/
lemma scaleSplitTruncatedOp_eq_pauliDiagonalPart_add_offDiagonal
    {L q_code m_max R_cut : ℕ}
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) :
    scaleSplitTruncatedOp V R_cut =
      pauliDiagonalPart sys V R_cut +
        ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r,
          pauliOffDiagonalTerm sys V r A := by
  unfold scaleSplitTruncatedOp pauliDiagonalPart pauliOffDiagonalTerm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun A _ => (add_sub_cancel _ _).symm

/-- **Syndrome-Sector Matrix Block Identity for `pauliOffDiagonalTerm`**
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`):
For any two syndrome sectors `σ₁, σ₂`, $\Pi_{\sigma_1} V_{r, A}^{\mathrm{off}} \Pi_{\sigma_2}$
vanishes identically on the diagonal ($\sigma_1 = \sigma_2$) and equals
$\Pi_{\sigma_1} V_{r, A} \Pi_{\sigma_2}$ off the diagonal ($\sigma_1 \ne \sigma_2$). -/
lemma syndromeProjector_mul_pauliOffDiagonalTerm_mul_syndromeProjector
    {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (r : ℕ) (A : Finset (Box3D L))
    (σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool) :
    sys.syndromeProjector σ₁ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₂ =
      if σ₁ = σ₂ then 0
      else sys.syndromeProjector σ₁ * V.term r A * sys.syndromeProjector σ₂ := by
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  unfold pauliOffDiagonalTerm
  rw [mul_sub, sub_mul]
  have h_pinch :
      sys.syndromeProjector σ₁ * syndromePinchOp sys (V.term r A) * sys.syndromeProjector σ₂ =
        (sys.syndromeProjector σ₁ * V.term r A) *
          (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂) := by
    calc sys.syndromeProjector σ₁ * syndromePinchOp sys (V.term r A) * sys.syndromeProjector σ₂
      _ = (sys.syndromeProjector σ₁ * perturbedSyndromeDiagOp sys (V.term r A)) *
            sys.syndromeProjector σ₂ := rfl
      _ = (sys.syndromeProjector σ₁ * V.term r A * sys.syndromeProjector σ₁) *
            sys.syndromeProjector σ₂ := by
          rw [(perturbed_syndromeDiagOp_mul_syndromeProjector sys (V.term r A) σ₁).2.1]
      _ = (sys.syndromeProjector σ₁ * V.term r A) *
            (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂) := by simp only [mul_assoc]
  rw [h_pinch]
  by_cases h_eq : σ₁ = σ₂
  · subst h_eq
    rw [if_pos rfl, (h_res.2.1 σ₁).1, sub_self]
  · rw [if_neg h_eq, h_res.2.2.1 σ₁ σ₂ h_eq, mul_zero, sub_zero]

/-- **Footprint Fiber Summation Identity for Valid Ursell Clusters**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
Because every valid Ursell cluster `K` has its footprint `(worldlineClusterMonomers K, worldlineClusterSpanningSurface D_field sys C_RCA K)`
in `worldlineUrsellIndexFinset L q_code m_max R_cut`, summing the footprint-filtered Ursell weight
over `γ_f ∈ worldlineUrsellIndexFinset L q_code m_max R_cut` recovers the exact cluster weight of `K`. -/
lemma sum_worldlineUrsellIndexFinset_ite_eq_ite_valid
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) :
    (∑ γ_f ∈ worldlineUrsellIndexFinset L q_code m_max R_cut,
      if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
          worldlineClusterMonomers K = γ_f.1 ∧
          worldlineClusterSpanningSurface D_field sys C_RCA K = γ_f.2 then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
      else 0) =
    if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K then
      worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
    else 0 := by
  by_cases hK : IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K
  · rw [if_pos hK]
    let fp₀ : WorldlineUrsellFootprint L q_code m_max :=
      (worldlineClusterMonomers K, worldlineClusterSpanningSurface D_field sys C_RCA K)
    have h_mem : fp₀ ∈ worldlineUrsellIndexFinset L q_code m_max R_cut :=
      worldlineClusterFootprint_mem_worldlineUrsellIndexFinset D_field sys hK
    rw [Finset.sum_eq_single fp₀]
    · exact if_pos ⟨hK, rfl, rfl⟩
    · intro γ_f _ h_ne
      refine if_neg ?_
      rintro ⟨_, h1, h2⟩
      exact h_ne (Prod.ext h1.symm h2.symm)
    · intro h_not
      exact False.elim (h_not h_mem)
  · rw [if_neg hK]
    refine Finset.sum_eq_zero fun γ_f _ => if_neg (fun h => hK h.1)

/-- Elementary parity identities for `spanningSurfaceSign` (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`):
1. `spanningSurfaceSign ∅ σ = 1`
2. `spanningSurfaceSign α σ * spanningSurfaceSign α σ = 1`
3. For `c ∉ s`, `spanningSurfaceSign (insert c s) σ = (if σ c = true then -1 else 1) * spanningSurfaceSign s σ`. -/
lemma spanningSurfaceSign_insert_and_identities
    {L q_code m_max : ℕ}
    (α : Finset (IdxCSS[L, q_code, m_max]))
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    spanningSurfaceSign (∅ : Finset (IdxCSS[L, q_code, m_max])) σ = 1 ∧
    spanningSurfaceSign α σ * spanningSurfaceSign α σ = 1 ∧
    ∀ {c : IdxCSS[L, q_code, m_max]} {s : Finset (IdxCSS[L, q_code, m_max])},
      c ∉ s →
      spanningSurfaceSign (insert c s) σ =
        (if σ c = true then -1 else 1) * spanningSurfaceSign s σ := by
  refine ⟨by simp [spanningSurfaceSign], ?_, fun {c s} hc => ?_⟩
  · unfold spanningSurfaceSign
    split_ifs <;> ring
  · unfold spanningSurfaceSign
    rw [Finset.filter_insert]
    cases hσ : σ c
    · simp
    · have hc_filt : c ∉ s.filter (fun x => σ x = true) :=
        fun h => hc (Finset.mem_filter.mp h).1
      rw [if_pos rfl, if_pos rfl, Finset.card_insert_of_notMem hc_filt]
      by_cases h_mod : (s.filter (fun x => σ x = true)).card % 2 = 1
      · rw [if_pos h_mod, if_neg (by omega)]; ring
      · rw [if_neg h_mod, if_pos (by omega)]; ring

/-- Character multiplicativity of `spanningSurfaceSign` under `syndromeXor` and disjoint check union
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`):
1. `spanningSurfaceSign α (syndromeXor σ₁ σ₂) = spanningSurfaceSign α σ₁ * spanningSurfaceSign α σ₂`
2. If `Disjoint α₁ α₂`, then `spanningSurfaceSign (α₁ ∪ α₂) σ = spanningSurfaceSign α₁ σ * spanningSurfaceSign α₂ σ`. -/
lemma spanningSurfaceSign_syndromeXor_and_union_disjoint
    {L q_code m_max : ℕ} :
    (∀ (α : Finset (IdxCSS[L, q_code, m_max]))
        (σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool),
      spanningSurfaceSign α (syndromeXor σ₁ σ₂) =
        spanningSurfaceSign α σ₁ * spanningSurfaceSign α σ₂) ∧
    (∀ (α₁ α₂ : Finset (IdxCSS[L, q_code, m_max]))
        (σ : IdxCSS[L, q_code, m_max] → Bool),
      Disjoint α₁ α₂ →
      spanningSurfaceSign (α₁ ∪ α₂) σ =
        spanningSurfaceSign α₁ σ * spanningSurfaceSign α₂ σ) := by
  refine ⟨fun α σ₁ σ₂ => ?_, fun α₁ α₂ σ h_disj => ?_⟩
  · induction α using Finset.induction_on with
    | empty => simp [spanningSurfaceSign]
    | @insert c s hc ih =>
      rw [(spanningSurfaceSign_insert_and_identities s (syndromeXor σ₁ σ₂)).2.2 hc,
        (spanningSurfaceSign_insert_and_identities s σ₁).2.2 hc,
        (spanningSurfaceSign_insert_and_identities s σ₂).2.2 hc, ih]
      unfold syndromeXor
      cases σ₁ c <;> cases σ₂ c <;> simp
  · induction α₁ using Finset.induction_on with
    | empty => simp [spanningSurfaceSign]
    | @insert c s hc ih =>
      have hc_not_α₂ : c ∉ α₂ :=
        Finset.disjoint_left.mp h_disj (Finset.mem_insert_self c s)
      have hc_not_union : c ∉ s ∪ α₂ := by
        simp [hc, hc_not_α₂]
      have h_disj_s : Disjoint s α₂ :=
        Finset.disjoint_of_subset_left (Finset.subset_insert c s) h_disj
      rw [Finset.insert_union,
        (spanningSurfaceSign_insert_and_identities (s ∪ α₂) σ).2.2 hc_not_union,
        (spanningSurfaceSign_insert_and_identities s σ).2.2 hc,
        ih h_disj_s, mul_assoc]

/-- Involution identity `symplecticPauliSign ν μ * symplecticPauliSign ν μ = 1` for the symplectic
commutation character (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma symplecticPauliSign_sq_eq_one
    {L q_code : ℕ} (ν μ : PauliBitstringPair L q_code) :
    symplecticPauliSign ν μ * symplecticPauliSign ν μ = 1 := by
  unfold symplecticPauliSign
  split_ifs <;> ring

/-- Closure of `realizableSyndromes D_field` under `syndromeXor` with any Pauli syndrome shift
`staticCSSPauliFlip D_field a b` (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`). -/
lemma syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a b : BoxSlot3D L q_code → ZMod 2)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (hσ : σ ∈ realizableSyndromes D_field) :
    syndromeXor (staticCSSPauliFlip D_field a b) σ ∈ realizableSyndromes D_field := by
  rcases (Finset.mem_filter.mp hσ).2 with ⟨x, y, rfl⟩
  rw [realizableSyndromes, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, a + x, b + y, ?_⟩
  exact (staticCSSPauliFlip_add D_field a x b y).symm

/-- Defining properties of `canonicalJumpPauliRep` (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`):
whenever a syndrome shift `δ` is realized by a Pauli operator supported on `A`,
`rep = canonicalJumpPauliRep D_field A δ` is supported on `A`, has syndrome shift `δ`, and is idempotent
under re-application of `canonicalJumpPauliRep D_field A`. -/
lemma canonicalJumpPauliRep_spec
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (A : Finset (Box3D L))
    (δ : IdxCSS[L, q_code, m_max] → Bool)
    (h_ex : ∃ p : PauliBitstringPair L q_code,
      (∀ slot : BoxSlot3D L q_code, p.1 slot ≠ 0 ∨ p.2 slot ≠ 0 → slot.1 ∈ A) ∧
      staticCSSPauliFlip D_field p.1 p.2 = δ) :
    let rep := canonicalJumpPauliRep D_field A δ
    (∀ slot : BoxSlot3D L q_code, rep.1 slot ≠ 0 ∨ rep.2 slot ≠ 0 → slot.1 ∈ A) ∧
    staticCSSPauliFlip D_field rep.1 rep.2 = δ ∧
    rep = canonicalJumpPauliRep D_field A (staticCSSPauliFlip D_field rep.1 rep.2) := by
  intro rep
  have h_def : rep = Classical.choose h_ex := dif_pos h_ex
  have h_spec := Classical.choose_spec h_ex
  rw [← h_def] at h_spec
  refine ⟨h_spec.1, h_spec.2, ?_⟩
  rw [h_spec.2]

/-- Exact action of `worldlineSyndromeShiftBlockOp` on a syndrome sector projector `sys.syndromeProjector σ₀`
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`):
for any `σ₀ ∈ realizableSyndromes D_field`, multiplying `worldlineSyndromeShiftBlockOp D_field sys V ξ`
on the right by `sys.syndromeProjector σ₀` projects onto the single shifted syndrome sector
`syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀`. -/
lemma worldlineSyndromeShiftBlockOp_mul_syndromeProjector
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (ξ : WorldlineJumpMonomer L q_code)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    let δ := staticCSSPauliFlip D_field ξ.2.1 ξ.2.2
    worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ =
      (if σ₀ ∈ realizableSyndromes D_field then
        sys.syndromeProjector (syndromeXor δ σ₀) *
          pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 *
          sys.syndromeProjector σ₀
      else 0) ∧
    sys.syndromeProjector (syndromeXor δ σ₀) *
        (worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀) =
      worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ := by
  intro δ
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_right :
      worldlineSyndromeShiftBlockOp D_field sys V ξ * sys.syndromeProjector σ₀ =
        if σ₀ ∈ realizableSyndromes D_field then
          sys.syndromeProjector (syndromeXor δ σ₀) *
            pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 *
            sys.syndromeProjector σ₀
        else 0 := by
    unfold worldlineSyndromeShiftBlockOp
    (try dsimp only)
    rw [Finset.sum_mul]
    have h_term : ∀ σ ∈ realizableSyndromes D_field,
        (sys.syndromeProjector (syndromeXor δ σ) *
          pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 *
          sys.syndromeProjector σ) * sys.syndromeProjector σ₀ =
        if σ = σ₀ then
          sys.syndromeProjector (syndromeXor δ σ₀) *
            pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 *
            sys.syndromeProjector σ₀
        else 0 := by
      intro σ _
      rw [mul_assoc (sys.syndromeProjector (syndromeXor δ σ) * pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2)]
      by_cases h_eq : σ = σ₀
      · subst h_eq
        rw [if_pos rfl, (h_res.2.1 σ).1]
      · rw [if_neg h_eq, h_res.2.2.1 σ σ₀ h_eq, mul_zero]
    rw [Finset.sum_congr rfl h_term, Finset.sum_ite_eq']
  refine ⟨h_right, ?_⟩
  rw [h_right]
  split_ifs with hσ₀
  · calc sys.syndromeProjector (syndromeXor δ σ₀) *
          (sys.syndromeProjector (syndromeXor δ σ₀) *
            pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 *
            sys.syndromeProjector σ₀)
      _ = (sys.syndromeProjector (syndromeXor δ σ₀) *
            sys.syndromeProjector (syndromeXor δ σ₀)) *
            pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 *
            sys.syndromeProjector σ₀ := by simp only [mul_assoc]
      _ = sys.syndromeProjector (syndromeXor δ σ₀) *
            pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 *
            sys.syndromeProjector σ₀ := by rw [(h_res.2.1 (syndromeXor δ σ₀)).1]
  · rw [mul_zero]

/-- Binomial expansion of the product of `(1 + f ϑ)` over a finite set `S` into a sum over subsets
`Θ ∈ S.powerset` (Part II, Section 3.5 (`subsec:worldline-expansion`), Equations `eq:H-diag-mayer-split`–`eq:mayer-factor-eta-def`). -/
lemma prod_one_add_eq_sum_powerset
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℝ) :
    (∏ ϑ ∈ S, (1 + f ϑ)) = ∑ Θ ∈ S.powerset, ∏ ϑ ∈ Θ, f ϑ := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have h_disj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro Θ hΘ₁ hΘ₂
      rcases Finset.mem_image.mp hΘ₂ with ⟨Θ', _, rfl⟩
      exact ha (Finset.mem_powerset.mp hΘ₁ (Finset.mem_insert_self a Θ'))
    have h_inj : Set.InjOn (insert a) (s.powerset : Set (Finset α)) := by
      intro Θ₁ hΘ₁ Θ₂ hΘ₂ h_eq
      have ha₁ : a ∉ Θ₁ := fun h => ha (Finset.mem_powerset.mp hΘ₁ h)
      have ha₂ : a ∉ Θ₂ := fun h => ha (Finset.mem_powerset.mp hΘ₂ h)
      rw [← Finset.erase_insert ha₁, h_eq, Finset.erase_insert ha₂]
    rw [Finset.prod_insert ha, ih, Finset.powerset_insert,
      Finset.sum_union h_disj, Finset.sum_image h_inj]
    have h_img_sum :
        (∑ Θ ∈ s.powerset, ∏ ϑ ∈ insert a Θ, f ϑ) =
          f a * ∑ Θ ∈ s.powerset, ∏ ϑ ∈ Θ, f ϑ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun Θ hΘ => ?_
      have ha_not : a ∉ Θ := fun h => ha (Finset.mem_powerset.mp hΘ h)
      rw [Finset.prod_insert ha_not]
    rw [h_img_sum]
    ring

/-- Exact Mayer bond expansion of the diagonal collar fluctuation exponential
(Part II, Section 3.5 (`subsec:worldline-expansion`), Equations `eq:H-diag-mayer-split`–`eq:mayer-factor-eta-def`):
$$\prod_{\vartheta \in S} \exp\!\left(-\int_0^\beta \bigl(d_\vartheta(\sigma(\tau, t)) - d_\vartheta(\sigma_0)\bigr)\,dt\right)
  = \sum_{\Theta \subseteq S} \prod_{\vartheta \in \Theta} \eta_\vartheta(\sigma(\cdot); \sigma_0).$$ -/
lemma prod_exp_neg_integral_eq_sum_powerset_worldlineMayerBondFactor
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (jumps : List (WorldlineJumpMonomer L q_code))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (β : ℝ) (τ : Fin jumps.length → ℝ)
    (S : Finset (ℕ × Finset (Box3D L))) :
    (∏ ϑ ∈ S,
      Real.exp (-∫ t in Set.Icc 0 β,
        (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field jumps σ₀ τ t) -
          d_loc ϑ.1 ϑ.2 σ₀))) =
    ∑ Θ ∈ S.powerset,
      ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field jumps d_loc σ₀ β ϑ τ := by
  have h_term : ∀ ϑ : ℕ × Finset (Box3D L),
      Real.exp (-∫ t in Set.Icc 0 β,
        (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field jumps σ₀ τ t) -
          d_loc ϑ.1 ϑ.2 σ₀)) =
      1 + worldlineMayerBondFactor D_field jumps d_loc σ₀ β ϑ τ := by
    intro ϑ
    unfold worldlineMayerBondFactor
    ring
  simp_rw [h_term]
  exact prod_one_add_eq_sum_powerset S (fun ϑ => worldlineMayerBondFactor D_field jumps d_loc σ₀ β ϑ τ)

/-- Check-support conservation for `pauliOffDiagonalTerm` (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:V-off-jump-decomp`):
when `V.term r A` is supported on `A`, any check `c ∉ cubeIntersectingChecks sys A` is conserved
by `pauliOffDiagonalTerm sys V r A`: if `σ₂ c ≠ σ₁ c`, then
`sys.syndromeProjector σ₁ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₂ = 0`. -/
lemma pauliOffDiagonalTerm_check_support_conservation
    {L q_code m_max : ℕ}
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (r : ℕ) (A : Finset (Box3D L))
    (hV_supp : IsSupportedOn (SiteCSS[L, q_code]) A (V.term r A))
    (σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool)
    {c : IdxCSS[L, q_code, m_max]}
    (hc_not_in : c ∉ cubeIntersectingChecks sys A)
    (h_ne : σ₂ c ≠ σ₁ c) :
    sys.syndromeProjector σ₁ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ₂ = 0 := by
  rw [syndromeProjector_mul_pauliOffDiagonalTerm_mul_syndromeProjector]
  split_ifs with h_eq
  · rfl
  · exact pauliOffDiagonalCubeTerm_check_support_conservation sys hV_supp σ₁ σ₂ hc_not_in h_ne

/-- Defining properties of `canonicalCollarRealizableSyndrome` (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)):
for any realizable syndrome `σ ∈ realizableSyndromes D_field` and any check subset `S`,
the canonical realizable representative `σ_rep = canonicalCollarRealizableSyndrome D_field S (restrictSyndromeToCollar S σ)`
of the restricted collar configuration `σ|_S` belongs to `realizableSyndromes D_field` and agrees
with `σ` on `S`. -/
lemma canonicalCollarRealizableSyndrome_spec
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (S : Finset (IdxCSS[L, q_code, m_max]))
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    let σ₀ := restrictSyndromeToCollar S σ
    let σ_rep := canonicalCollarRealizableSyndrome D_field S σ₀
    σ_rep ∈ realizableSyndromes D_field ∧
    (∀ c ∈ S, σ_rep c = σ₀ c) ∧
    (∀ c ∈ S, σ_rep c = σ c) := by
  intro σ₀ σ_rep
  have h_ex : ∃ τ ∈ realizableSyndromes D_field, ∀ c ∈ S, τ c = σ₀ c := by
    refine ⟨σ, hσ, fun c hc => ?_⟩
    dsimp [σ₀, restrictSyndromeToCollar]
    rw [if_pos hc]
  have h_def : σ_rep = Classical.choose h_ex := dif_pos h_ex
  have h_spec := Classical.choose_spec h_ex
  rw [← h_def] at h_spec
  refine ⟨h_spec.1, h_spec.2, fun c hc => ?_⟩
  rw [h_spec.2 c hc]
  dsimp [σ₀, restrictSyndromeToCollar]
  rw [if_pos hc]

/-- Net syndrome shift `⨁_{ξ ∈ jumps} δ_ξ` of a list of jump monomers `jumps`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`). -/
def worldlineJumpListFlip
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (jumps : List (WorldlineJumpMonomer L q_code)) :
    IdxCSS[L, q_code, m_max] → Bool :=
  jumps.foldr (fun ξ acc => syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) acc)
    (fun _ => false)

/-- Closure of `realizableSyndromes D_field` under `syndromeXor` with `worldlineJumpListFlip D_field jumps`. -/
lemma syndromeXor_worldlineJumpListFlip_mem_realizableSyndromes
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (jumps : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    syndromeXor (worldlineJumpListFlip D_field jumps) σ₀ ∈ realizableSyndromes D_field := by
  induction jumps generalizing σ₀ with
  | nil =>
    have h_xor : syndromeXor (worldlineJumpListFlip D_field []) σ₀ = σ₀ := by
      ext c; unfold worldlineJumpListFlip syndromeXor; cases σ₀ c <;> rfl
    rwa [h_xor]
  | cons hd tl ih =>
    have h_assoc :
        syndromeXor (worldlineJumpListFlip D_field (hd :: tl)) σ₀ =
          syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2)
            (syndromeXor (worldlineJumpListFlip D_field tl) σ₀) := by
      ext c
      change bne (bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c)
          (worldlineJumpListFlip D_field tl c)) (σ₀ c) =
        bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c)
          (bne (worldlineJumpListFlip D_field tl c) (σ₀ c))
      cases staticCSSPauliFlip D_field hd.2.1 hd.2.2 c <;>
        cases worldlineJumpListFlip D_field tl c <;>
        cases σ₀ c <;> rfl
    rw [h_assoc]
    exact syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2
      (syndromeXor (worldlineJumpListFlip D_field tl) σ₀) (ih σ₀ hσ₀)

/-- Ordered jump-block product sector shift (Part II, Section 3.5 (`subsec:worldline-expansion`), Equation `eq:local-pauli-jump-xi`):
for any list of jump monomers `jumps` and any `σ₀ ∈ realizableSyndromes D_field`, the reverse-ordered
product `(jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod * sys.syndromeProjector σ₀`
lands in the realizable syndrome sector shifted by `worldlineJumpListFlip D_field jumps`. -/
lemma list_prod_reverse_worldlineSyndromeShiftBlockOp_mul_syndromeProjector
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (jumps : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    sys.syndromeProjector (syndromeXor (worldlineJumpListFlip D_field jumps) σ₀) *
      ((jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
        sys.syndromeProjector σ₀) =
      (jumps.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
        sys.syndromeProjector σ₀ := by
  induction jumps generalizing σ₀ with
  | nil =>
    have h_xor : syndromeXor (worldlineJumpListFlip D_field []) σ₀ = σ₀ := by
      ext c; unfold worldlineJumpListFlip syndromeXor; cases σ₀ c <;> rfl
    rw [h_xor]
    simp only [List.reverse_nil, List.map_nil, List.prod_nil, one_mul]
    exact ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
  | cons hd tl ih =>
    have h_mem_hd :
        syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2) σ₀ ∈ realizableSyndromes D_field :=
      syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2 σ₀ hσ₀
    have h_xor_assoc :
        syndromeXor (worldlineJumpListFlip D_field (hd :: tl)) σ₀ =
          syndromeXor (worldlineJumpListFlip D_field tl)
            (syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2) σ₀) := by
      ext c
      change bne (bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c)
          (worldlineJumpListFlip D_field tl c)) (σ₀ c) =
        bne (worldlineJumpListFlip D_field tl c)
          (bne (staticCSSPauliFlip D_field hd.2.1 hd.2.2 c) (σ₀ c))
      cases staticCSSPauliFlip D_field hd.2.1 hd.2.2 c <;>
        cases worldlineJumpListFlip D_field tl c <;>
        cases σ₀ c <;> rfl
    have h_prod_rev :
        ((hd :: tl).reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod =
          (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
            worldlineSyndromeShiftBlockOp D_field sys V hd := by
      rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [h_xor_assoc, h_prod_rev]
    have h_hd_abs := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V hd σ₀).2
    (try dsimp only at h_hd_abs)
    have h_tl_abs := ih (syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2) σ₀) h_mem_hd
    let P_tl := sys.syndromeProjector
      (syndromeXor (worldlineJumpListFlip D_field tl)
        (syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2) σ₀))
    let P_hd := sys.syndromeProjector (syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2) σ₀)
    let W_tl := (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod
    let B_hd := worldlineSyndromeShiftBlockOp D_field sys V hd
    change P_tl * ((W_tl * B_hd) * sys.syndromeProjector σ₀) =
      (W_tl * B_hd) * sys.syndromeProjector σ₀
    calc P_tl * ((W_tl * B_hd) * sys.syndromeProjector σ₀)
      _ = P_tl * (W_tl * (P_hd * (B_hd * sys.syndromeProjector σ₀))) := by
          rw [mul_assoc W_tl B_hd, h_hd_abs]
      _ = (P_tl * (W_tl * P_hd)) * (B_hd * sys.syndromeProjector σ₀) := by
          simp only [mul_assoc]
      _ = (W_tl * P_hd) * (B_hd * sys.syndromeProjector σ₀) := by
          rw [h_tl_abs]
      _ = W_tl * (P_hd * (B_hd * sys.syndromeProjector σ₀)) := by
          simp only [mul_assoc]
      _ = (W_tl * B_hd) * sys.syndromeProjector σ₀ := by
          rw [h_hd_abs, ← mul_assoc]

/-- Collar-restriction congruence of `canonicalCollarRealizableSyndrome` and `worldlinePolymerLoopAmplitude`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)):
whenever two syndromes `σ₁` and `σ₂` agree on `S = worldlinePolymerNativeCollar sys C_RCA γ`,
their canonical realizable representatives and loop amplitudes are identical. -/
lemma canonicalCollarRealizableSyndrome_and_loopAmplitude_congr
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code)
    {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool}
    (h_agree : ∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ₁ c = σ₂ c) :
    canonicalCollarRealizableSyndrome D_field (worldlinePolymerNativeCollar sys C_RCA γ) σ₁ =
      canonicalCollarRealizableSyndrome D_field (worldlinePolymerNativeCollar sys C_RCA γ) σ₂ ∧
    worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₁ =
      worldlinePolymerLoopAmplitude D_field sys C_RCA V γ σ₂ := by
  have h_iff : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ c = σ₁ c) ↔
        (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ c = σ₂ c) :=
    fun σ => ⟨fun h1 c hc => (h1 c hc).trans (h_agree c hc),
      fun h2 c hc => (h2 c hc).trans (h_agree c hc).symm⟩
  have h_rep :
      canonicalCollarRealizableSyndrome D_field (worldlinePolymerNativeCollar sys C_RCA γ) σ₁ =
        canonicalCollarRealizableSyndrome D_field (worldlinePolymerNativeCollar sys C_RCA γ) σ₂ := by
    unfold canonicalCollarRealizableSyndrome
    simp only [h_iff]
  refine ⟨h_rep, ?_⟩
  unfold worldlinePolymerLoopAmplitude
  (try dsimp only)
  rw [h_rep]

/-- Exact native-collar locality of `worldlinePolymerMicroWeight` and `worldlinePolymerWeight`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equations `eq:P-gamma-spanning-surface`–`eq:C-bar-span-def`):
for any valid worldline polymer `γ`:
1. If `σ₁` and `σ₂` agree on `worldlinePolymerNativeCollar sys C_RCA γ`, then
   `worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ₁ = worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ₂`.
2. In particular, for every syndrome `σ`, `worldlinePolymerMicroWeight` on `restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ`
   equals `worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ`, so
   `worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ = (-1)^{⟨ν, μ(γ)⟩} (-1)^{|α(γ) ∩ σ|} w_micro(γ; σ)`. -/
lemma worldlinePolymerMicroWeight_congr_on_nativeCollar_and_weight_eq
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA J β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (ν : PauliBitstringPair L q_code)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    (∀ {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool},
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ₁ c = σ₂ c) →
      worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ₁ =
        worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ₂) ∧
    (∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ =
        symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) *
          spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
          worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ) := by
  have h_congr : ∀ {σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool},
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ₁ c = σ₂ c) →
      worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ₁ =
        worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ σ₂ := by
    intro σ₁ σ₂ h_agree
    unfold worldlinePolymerMicroWeight
    rw [(canonicalCollarRealizableSyndrome_and_loopAmplitude_congr D_field sys C_RCA V γ h_agree).2]
    congr 1
    congr 1; funext τ
    split_ifs with h_simp
    · rcases (worldlineTrajectorySyndrome_eq_outside_and_congr_on_nativeCollar
        D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar hγ τ).2.1 h_agree with
        ⟨h_bare, h_mayer⟩
      rw [h_bare]
      congr 1
      exact Finset.prod_congr rfl fun ϑ hϑ => h_mayer ϑ hϑ
    · rfl
  refine ⟨h_congr, fun σ => ?_⟩
  unfold worldlinePolymerWeight
  rw [h_congr (fun c hc => by unfold restrictSyndromeToCollar; rw [if_pos hc])]

/-- Every realizable syndrome sector `σ ∈ realizableSyndromes D_field` has uniform dimension
`hilbertTrace (sys.syndromeProjector σ) = hilbertTrace sys.P0 > 0`
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)). -/
lemma hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    hilbertTrace (sys.syndromeProjector σ) = hilbertTrace sys.P0 ∧
    0 < hilbertTrace (sys.syndromeProjector σ) := by
  rcases (Finset.mem_filter.mp hσ).2 with ⟨x, y, rfl⟩
  have h_eq := hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0
    D_field h_valid sys h_sys_checks x y
  have h_pos_norm := vacuumPartitionNorm_pos_of_validDescriptorField D_field h_valid sys h_sys_checks 0 0
  rw [neg_zero, zero_mul, Real.exp_zero, mul_one] at h_pos_norm
  exact ⟨h_eq, by linarith⟩

/-- For any valid worldline polymer `γ` enclosed in a lattice cube of diameter `L_star`,
RCA guarantees trivial logical coset `worldlinePolymerLogicalCoset D_field sys C_RCA γ = (0, 0)`,
so `symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) = 1` and
`worldlinePolymerWeight` is independent of the character `ν`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equations `eq:P-gamma-spanning-surface`–`eq:C-bar-span-def`). -/
lemma symplecticPauliSign_worldlinePolymerLogicalCoset_eq_one_of_ball
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star) (hC_RCA : 0 ≤ C_RCA)
    (h_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (γ : WorldlineDysonPolymer L q_code)
    (hγ_valid : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (h_ball : ∃ x0 : Box3D L, ∀ p ∈ worldlinePolymerMonomers γ, ∀ v ∈ p.2, v ∈ boxCube x0 L_star) :
    (∀ ν : PauliBitstringPair L q_code,
      symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) = 1) ∧
    (∀ (ν : PauliBitstringPair L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool),
      worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ =
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
          worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ)) := by
  have h_rca := worldline_polymer_rca1_spanning_surface_collar_containment
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_cut hR_le hC_RCA h_cal γ hγ_valid h_ball
  have h_sign : ∀ ν : PauliBitstringPair L q_code,
      symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) = 1 := fun ν => by
    rw [h_rca.2.1, symplecticPauliSign_zero_right]
  refine ⟨h_sign, fun ν σ => ?_⟩
  unfold worldlinePolymerWeight
  rw [h_sign ν, one_mul]

/-- Closure and involution of `syndromeClosedPauliFinset D_field` under bitwise addition (`ZMod 2` XOR)
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:pinching-group-average`). -/
lemma add_mem_syndromeClosedPauliFinset_and_involutive
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {ν₁ ν₂ : PauliBitstringPair L q_code}
    (hν₁ : ν₁ ∈ syndromeClosedPauliFinset D_field)
    (hν₂ : ν₂ ∈ syndromeClosedPauliFinset D_field) :
    ν₁ + ν₂ ∈ syndromeClosedPauliFinset D_field ∧
    (ν₁ + ν₂) + ν₂ = ν₁ := by
  have h1 : staticCSSPauliFlip D_field ν₁.1 ν₁.2 = fun _ => false :=
    (Finset.mem_filter.mp hν₁).2
  have h2 : staticCSSPauliFlip D_field ν₂.1 ν₂.2 = fun _ => false :=
    (Finset.mem_filter.mp hν₂).2
  refine ⟨?_, ?_⟩
  · rw [syndromeClosedPauliFinset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change staticCSSPauliFlip D_field (ν₁.1 + ν₂.1) (ν₁.2 + ν₂.2) = fun _ => false
    rw [staticCSSPauliFlip_add D_field ν₁.1 ν₂.1 ν₁.2 ν₂.2, h1, h2]
    ext c; rfl
  · have h_zmod2 : ∀ x y : ZMod 2, x + y + y = x := by decide
    ext slot
    · exact h_zmod2 (ν₁.1 slot) (ν₂.1 slot)
    · exact h_zmod2 (ν₁.2 slot) (ν₂.2 slot)

/-- Any syndrome-closed Pauli operator `weylPauliZ ν.1 * weylPauliX ν.2` (`ν ∈ syndromeClosedPauliFinset D_field`)
commutes with every check projector `sys.checkProj idx`, every syndrome sector projector
`sys.syndromeProjector σ`, and the bare ground-space projector `sys.P0`
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:pinching-group-average`). -/
lemma weylPauliZX_comm_checkProj_and_syndromeProjector_of_syndromeClosed
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {ν : PauliBitstringPair L q_code}
    (hν : ν ∈ syndromeClosedPauliFinset D_field) :
    (∀ idx, Commute (weylPauliZ ν.1 * weylPauliX ν.2) (sys.checkProj idx)) ∧
    (∀ σ, Commute (weylPauliZ ν.1 * weylPauliX ν.2) (sys.syndromeProjector σ)) ∧
    Commute (weylPauliZ ν.1 * weylPauliX ν.2) sys.P0 := by
  have h_closed : staticCSSPauliFlip D_field ν.1 ν.2 = fun _ => false :=
    (Finset.mem_filter.mp hν).2
  have h_chk : ∀ idx, Commute (weylPauliZ ν.1 * weylPauliX ν.2) (sys.checkProj idx) := fun idx => by
    rw [commute_iff_eq, (h_sys_checks idx).1]
    have h_flip := weylPauliZX_mul_staticCSSCheckProj D_field ν.1 ν.2 idx
    have h_f0 : staticCSSPauliFlip D_field ν.1 ν.2 idx = false := congr_fun h_closed idx
    rwa [h_f0, if_neg Bool.false_ne_true] at h_flip
  have h_syn : ∀ σ, Commute (weylPauliZ ν.1 * weylPauliX ν.2) (sys.syndromeProjector σ) :=
    (indexed_check_commuting_perturbation_commutes_with_syndromeProjector sys
      (weylPauliZ ν.1 * weylPauliX ν.2) h_chk).1
  have h_P0 : Commute (weylPauliZ ν.1 * weylPauliX ν.2) sys.P0 := by
    rw [← (_root_.syndrome_resolution_indexed sys).1]
    exact h_syn (fun _ => false)
  exact ⟨h_chk, h_syn, h_P0⟩

/-- Additivity and real-scalar homogeneity of `hilbertTrace`, together with complex decomposition
`hilbertTrace (P * (c • T)) = c.re * hilbertTrace (P * T) + c.im * hilbertTrace (P * (Complex.I • T))`. -/
lemma hilbertTrace_add_and_complex_smul_decomp
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B P T : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (r : ℝ) (c : ℂ) :
    hilbertTrace (A + B) = hilbertTrace A + hilbertTrace B ∧
    hilbertTrace (((r : ℝ) : ℂ) • A) = r * hilbertTrace A ∧
    hilbertTrace (P * (c • T)) =
      c.re * hilbertTrace (P * T) + c.im * hilbertTrace (P * (Complex.I • T)) := by
  have h_add : ∀ X Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace (X + Y) = hilbertTrace X + hilbertTrace Y := fun X Y => by
    unfold hilbertTrace
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [ContinuousLinearMap.add_apply, inner_add_right, map_add]
  have h_rsmul : ∀ (s : ℝ) (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      hilbertTrace (((s : ℝ) : ℂ) • X) = s * hilbertTrace X := fun s X => by
    unfold hilbertTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, re_ofReal_mul]
  refine ⟨h_add A B, h_rsmul r A, ?_⟩
  have hc_eq : c • T = ((c.re : ℝ) : ℂ) • T + ((c.im : ℝ) : ℂ) • (Complex.I • T) := by
    ext ψ
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc_eq, mul_add, clm_mul_smul, clm_mul_smul, h_add, h_rsmul, h_rsmul]

/-- By ℝ-linearity of `hilbertTrace`, `isSpanningCheckSurfaceForPolymer D_field sys γ μ α` extends
from `L_op` and `Complex.I • L_op` to `c • L_op` for every complex scalar `c : ℂ`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma isSpanningCheckSurfaceForPolymer_complex_smul
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (γ : WorldlineDysonPolymer L q_code)
    (μ : PauliBitstringPair L q_code) (α : Finset (IdxCSS[L, q_code, m_max]))
    (h_span : IsSpanningCheckSurfaceForPolymer D_field sys γ μ α)
    (c : ℂ) {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    let L_op := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ
    hilbertTrace (sys.syndromeProjector σ * (c • L_op)) =
      spanningSurfaceSign α σ * hilbertTrace (sys.P0 * (c • L_op)) := by
  intro L_op
  have h1 := (hilbertTrace_add_and_complex_smul_decomp 0 0 (sys.syndromeProjector σ) L_op 0 c).2.2
  have h2 := (hilbertTrace_add_and_complex_smul_decomp 0 0 sys.P0 L_op 0 c).2.2
  rcases h_span.2 σ hσ with ⟨h_re, h_im⟩
  rw [h1, h2, h_re, h_im]
  ring

private lemma signScalar_sum_zmod2_eq_ite_card_filter {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ZMod 2) :
    signScalar (∑ q ∈ s, f q) =
      (((if (s.filter (fun q => f q ≠ 0)).card % 2 = 1 then (-1 : ℝ) else 1) : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [signScalar_zero]
  | @insert q₀ tl hq₀ ih =>
    rw [Finset.sum_insert hq₀, signScalar_add, ih, Finset.filter_insert]
    rcases _root_.zmod2_eq_zero_or_one (f q₀) with h0 | h1
    · rw [h0, if_neg (not_not.mpr rfl), signScalar_zero, one_mul]
    · have h_ne : f q₀ ≠ 0 := by rw [h1]; decide
      have hq₀_filt : q₀ ∉ tl.filter (fun q => f q ≠ 0) :=
        fun h => hq₀ (Finset.mem_filter.mp h).1
      rw [if_pos h_ne, Finset.card_insert_of_notMem hq₀_filt, h1]
      change (-1 : ℂ) * (((if (tl.filter (fun q => f q ≠ 0)).card % 2 = 1 then (-1 : ℝ) else 1) : ℝ) : ℂ) =
        (((if ((tl.filter (fun q => f q ≠ 0)).card + 1) % 2 = 1 then (-1 : ℝ) else 1) : ℝ) : ℂ)
      by_cases h_mod : (tl.filter (fun q => f q ≠ 0)).card % 2 = 1
      · have h_mod' : ((tl.filter (fun q => f q ≠ 0)).card + 1) % 2 = 0 := by omega
        rw [if_pos h_mod, if_neg (by omega)]; norm_num
      · have h_mod' : ((tl.filter (fun q => f q ≠ 0)).card + 1) % 2 = 1 := by omega
        rw [if_neg h_mod, if_pos h_mod']; norm_num

/-- Equivalence between `symplecticPauliSign ν μ` and `signScalar` of the symplectic inner product
in `ZMod 2`, together with multiplicativity of `symplecticPauliSign` in both arguments
(Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:pinching-group-average`). -/
lemma signScalar_symplectic_eq_symplecticPauliSign_and_mul
    {L q_code : ℕ} (ν ν₁ ν₂ μ μ₁ μ₂ : PauliBitstringPair L q_code) :
    signScalar (∑ q : BoxSlot3D L q_code, (ν.1 q * μ.2 q + ν.2 q * μ.1 q)) =
      ((symplecticPauliSign ν μ : ℝ) : ℂ) ∧
    symplecticPauliSign ν (μ₁ + μ₂) = symplecticPauliSign ν μ₁ * symplecticPauliSign ν μ₂ ∧
    symplecticPauliSign (ν₁ + ν₂) μ = symplecticPauliSign ν₁ μ * symplecticPauliSign ν₂ μ := by
  have h_eq : ∀ x y : PauliBitstringPair L q_code,
      signScalar (∑ q : BoxSlot3D L q_code, (x.1 q * y.2 q + x.2 q * y.1 q)) =
        ((symplecticPauliSign x y : ℝ) : ℂ) := fun x y => by
    unfold symplecticPauliSign
    exact signScalar_sum_zmod2_eq_ite_card_filter Finset.univ
      (fun q => x.1 q * y.2 q + x.2 q * y.1 q)
  refine ⟨h_eq ν μ, ?_, ?_⟩
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, ← h_eq ν (μ₁ + μ₂), ← h_eq ν μ₁, ← h_eq ν μ₂, ← signScalar_add,
      ← Finset.sum_add_distrib]
    refine congrArg signScalar (Finset.sum_congr rfl fun q _ => ?_)
    change ν.1 q * (μ₁.2 q + μ₂.2 q) + ν.2 q * (μ₁.1 q + μ₂.1 q) = _
    ring
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_mul, ← h_eq (ν₁ + ν₂) μ, ← h_eq ν₁ μ, ← h_eq ν₂ μ, ← signScalar_add,
      ← Finset.sum_add_distrib]
    refine congrArg signScalar (Finset.sum_congr rfl fun q _ => ?_)
    change (ν₁.1 q + ν₂.1 q) * μ.2 q + (ν₁.2 q + ν₂.2 q) * μ.1 q = _
    ring

end DirectWorldlineCluster
