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

/-!
# Iterated Duhamel Simplex Integration and Active Mayer-Bond Subset Expansion

Constructs the time-reversal symmetrized weighted loop operator (`worldlinePolymerSymmetrizedWeightedLoopOp`) and multi-polymer Duhamel–Dyson cluster weights (`worldlineDysonMultiPolymerClusterWeight`). Proves the iterated Duhamel integral representation over the ordered Euclidean time simplex (`worldlineIteratedDuhamelIntegral_eq_simplex_integral`) and expands single-sector jump weights into active Mayer-bond subsets (`singleSectorWorldlineDysonJumpWeight_eq_sum_activeMayerSubsets`).

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

/-- Coset-reduced time-reversal symmetrized weighted loop operator $\widetilde{B}(\gamma) = \frac{1}{2}\overline{L}_{\mu(\gamma)}^\dagger(B(\gamma) + B(\gamma^{\mathrm{rev}}))$ of a worldline polymer $\gamma$ (Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
def worldlinePolymerSymmetrizedWeightedLoopOp
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code) : ℬ_CSS[L, q_code] :=
  let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
  (1 / 2 : ℂ) • ((hermitianPauliZX μ.1 μ.2)† *
    (worldlinePolymerWeightedLoopOp D_field sys V γ +
      worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2)))

/-- Duhamel–Dyson multi-polymer cluster weight on a syndrome sector $\sigma_0$ (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`), and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
def worldlineDysonMultiPolymerClusterWeight
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (C_RCA : ℝ) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) : ℝ :=
  if (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) then
    if ∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν
          (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1 then
      ((Nat.factorial K.length : ℝ)⁻¹) *
        (hilbertTrace (sys.syndromeProjector σ₀ *
          (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) /
          hilbertTrace (sys.syndromeProjector σ₀)) *
        (K.map (fun γ =>
          ((-1 : ℝ) ^ γ.1.length) *
            ∫ τ : Fin γ.1.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
                  ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
              else 0)).prod
    else 0
  else 0

/-- Single-sector Duhamel–Dyson jump-sequence weight before connected-component polymer decomposition (Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)): for a fixed realizable syndrome $\sigma$ and a syndrome-closed jump monomer list $\xi = (\xi_1, \dots, \xi_m)$, integrates the unperturbed bare action and diagonal interaction exponential over the ordered Dyson simplex $\Delta_m(\beta)$. -/
def singleSectorWorldlineDysonJumpWeight
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (R_cut : ℕ) (β : ℝ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (ξ_list : List (WorldlineJumpMonomer L q_code)) : ℝ :=
  if ξ_list = [] then 1
  else if (∀ ξ ∈ ξ_list, ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut) ∧
      2 ≤ ξ_list.length ∧
      staticCSSPauliFlip D_field (worldlinePolymerLoopX (ξ_list, ∅))
        (worldlinePolymerLoopZ (ξ_list, ∅)) = (fun _ => false) then
    ((-1 : ℝ) ^ ξ_list.length) *
      (hilbertTrace (sys.syndromeProjector σ *
        worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, ∅)) /
        hilbertTrace (sys.syndromeProjector σ)) *
      ∫ τ : Fin ξ_list.length → ℝ,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
            ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut,
              (1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ)
        else 0
  else 0

lemma mem_worldlineJumpListFinsetOfLength_iff_local
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (R_cut : ℕ) (m : ℕ) (l : List (WorldlineJumpMonomer L q_code)) :
    l ∈ worldlineJumpListFinsetOfLength D_field R_cut m ↔
      l.length = m ∧ ∀ ξ ∈ l, ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut := by
  unfold worldlineJumpListFinsetOfLength
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, _, rfl⟩
    refine ⟨List.length_ofFn, fun ξ hξ => ?_⟩
    rcases List.mem_ofFn.mp hξ with ⟨i, rfl⟩
    exact (g i).2
  · rintro ⟨hlen, hmem⟩
    refine ⟨fun i : Fin m => ⟨l.get (i.cast hlen.symm), hmem _ (List.get_mem l _)⟩,
      Finset.mem_univ _, ?_⟩
    refine List.ext_get (by simp [hlen]) (fun i h1 h2 => ?_)
    simp

lemma card_worldlineJumpListFinsetOfLength_le_pow
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (R_cut : ℕ) (m : ℕ) :
    (worldlineJumpListFinsetOfLength D_field R_cut m).card ≤
      (worldlineAllJumpMonomerFinset D_field R_cut).card ^ m := by
  unfold worldlineJumpListFinsetOfLength
  calc (Finset.univ.image _).card
    _ ≤ (Finset.univ : Finset (Fin m → ↥(worldlineAllJumpMonomerFinset D_field R_cut))).card :=
        Finset.card_image_le
    _ = (worldlineAllJumpMonomerFinset D_field R_cut).card ^ m := by
        simp

/-- `singleSectorWorldlineDysonJumpWeight` is absolutely summable over all jump lists `ξ_list`, and its `tsum` decomposes by list length `m : ℕ` over `worldlineJumpListFinsetOfLength D_field R_cut m`. -/
lemma summable_and_tsum_singleSectorWorldlineDysonJumpWeight
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {β : ℝ} (hβ : 0 ≤ β)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    Summable (singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ) ∧
    Summable (fun m : ℕ => ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list) ∧
    (∑' ξ_list : List (WorldlineJumpMonomer L q_code),
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list) =
    ∑' m : ℕ, ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list := by
  let S_mon := worldlineAllJumpMonomerFinset D_field R_cut
  let M_op : ℝ := ∑ ξ ∈ S_mon, ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖
  have hM_op_nn : 0 ≤ M_op := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let E_max : ℝ := ∑ η : IdxCSS[L, q_code, m_max] → Bool, |sys.syndromeEnergy η - sys.syndromeEnergy σ|
  have hE_max_nn : 0 ≤ E_max := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let D_ϑ (ϑ : ℕ × Finset (Box3D L)) : ℝ :=
    ∑ η : IdxCSS[L, q_code, m_max] → Bool, |d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ|
  have hD_ϑ_nn : ∀ ϑ, 0 ≤ D_ϑ ϑ := fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let B_int : ℝ := Real.exp (β * E_max) *
    ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut, Real.exp (β * D_ϑ ϑ)
  have hB_int_ge_one : 1 ≤ B_int := by
    dsimp [B_int]
    have h1 : 1 ≤ Real.exp (β * E_max) := Real.one_le_exp (mul_nonneg hβ hE_max_nn)
    have h2 : 1 ≤ ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut, Real.exp (β * D_ϑ ϑ) := by
      rw [← Real.exp_sum]
      exact Real.one_le_exp (Finset.sum_nonneg (fun ϑ _ => mul_nonneg hβ (hD_ϑ_nn ϑ)))
    nlinarith
  have hB_int_nn : 0 ≤ B_int := by linarith
  have h_bound_term : ∀ ξ_list : List (WorldlineJumpMonomer L q_code),
      ‖singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list‖ ≤
        if ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut ξ_list.length then
          B_int * ((M_op * β) ^ ξ_list.length / (ξ_list.length.factorial : ℝ))
        else 0 := by
    intro ξ_list
    rw [Real.norm_eq_abs]
    dsimp [singleSectorWorldlineDysonJumpWeight]
    by_cases h_nil : ξ_list = []
    · subst h_nil
      have h_mem0 : ([] : List (WorldlineJumpMonomer L q_code)) ∈
          worldlineJumpListFinsetOfLength D_field R_cut 0 := by
        rw [mem_worldlineJumpListFinsetOfLength_iff_local]
        exact ⟨rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
      simp [h_mem0, hB_int_ge_one]
    · rw [if_neg h_nil]
      split_ifs with h_cond h_in_fin
      · rcases h_cond with ⟨h_mem, _, _⟩
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
        have hP : IsStarProjection (sys.syndromeProjector σ) :=
          (PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ
        have h_tr_le : |hilbertTrace (sys.syndromeProjector σ *
            worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, ∅)) /
            hilbertTrace (sys.syndromeProjector σ)| ≤ M_op ^ ξ_list.length := by
          calc |hilbertTrace (sys.syndromeProjector σ *
                worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, ∅)) /
                hilbertTrace (sys.syndromeProjector σ)|
            _ ≤ ‖worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, ∅)‖ :=
                abs_hilbertTrace_isStarProjection_mul_div_le (sys.syndromeProjector σ) _ hP
            _ ≤ (ξ_list.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod :=
                worldlinePolymerWeightedLoopOp_norm_le D_field sys V (ξ_list, ∅)
            _ ≤ (ξ_list.map (fun _ => M_op)).prod := by
                apply list_prod_le_prod_map _ _ _ (fun _ _ => norm_nonneg _)
                intro ξ hξ
                exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (h_mem ξ hξ)
            _ = M_op ^ ξ_list.length := by simp
        have h_int_le : |∫ τ : Fin ξ_list.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
                ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut,
                  (1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ)
            else 0| ≤ ((β ^ ξ_list.length) / (ξ_list.length.factorial : ℝ)) * B_int := by
          apply SpacetimeWorldlineKP.abs_integral_kpOrderedDysonSimplex_le hβ hB_int_nn
          intro τ _
          have h_bare_le : -worldlineBareAction D_field sys ξ_list σ β τ ≤ β * E_max := by
            refine (neg_le_abs _).trans ?_
            dsimp [worldlineBareAction]
            apply SpacetimeWorldlineKP.abs_setIntegral_Icc_le_of_abs_le hβ hE_max_nn
            intro t _
            exact Finset.single_le_sum
              (f := fun η => |sys.syndromeEnergy η - sys.syndromeEnergy σ|)
              (fun η _ => abs_nonneg _) (Finset.mem_univ _)
          have h_mayer_eq : ∀ ϑ, 1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ =
              Real.exp (-(∫ t in Set.Icc 0 β,
                (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) - d_loc ϑ.1 ϑ.2 σ))) := by
            intro ϑ; dsimp [worldlineMayerBondFactor]; ring
          simp_rw [h_mayer_eq]
          rw [abs_mul, abs_of_pos (Real.exp_pos _),
            abs_of_pos (Finset.prod_pos (fun ϑ _ => Real.exp_pos _))]
          refine mul_le_mul (Real.exp_le_exp.mpr h_bare_le) ?_
            (Finset.prod_nonneg (fun ϑ _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
          refine Finset.prod_le_prod₀ (fun ϑ _ => (Real.exp_pos _).le) (fun ϑ _ => ?_)
          apply Real.exp_le_exp.mpr
          refine (neg_le_abs _).trans ?_
          apply SpacetimeWorldlineKP.abs_setIntegral_Icc_le_of_abs_le hβ (hD_ϑ_nn ϑ)
          intro t _
          exact Finset.single_le_sum
            (f := fun η => |d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ|)
            (fun η _ => abs_nonneg _) (Finset.mem_univ _)
        calc |hilbertTrace (sys.syndromeProjector σ *
              worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, ∅)) /
              hilbertTrace (sys.syndromeProjector σ)| *
            |∫ τ : Fin ξ_list.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
                  ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut,
                    (1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ)
              else 0|
          _ ≤ (M_op ^ ξ_list.length) * (((β ^ ξ_list.length) / (ξ_list.length.factorial : ℝ)) * B_int) :=
              mul_le_mul h_tr_le h_int_le (abs_nonneg _) (pow_nonneg hM_op_nn _)
          _ = B_int * ((M_op * β) ^ ξ_list.length / (ξ_list.length.factorial : ℝ)) := by
              rw [mul_pow]; ring
      · exfalso
        exact h_in_fin ((mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut ξ_list.length ξ_list).mpr
          ⟨rfl, h_cond.1⟩)
      · rw [abs_zero]
        exact mul_nonneg hB_int_nn (div_nonneg (pow_nonneg (mul_nonneg hM_op_nn hβ) _) (Nat.cast_nonneg _))
      · rw [abs_zero]
  have h_zero_outside : ∀ (m : ℕ) (ξ_list : List (WorldlineJumpMonomer L q_code)),
      ξ_list.length = m → ξ_list ∉ worldlineJumpListFinsetOfLength D_field R_cut m →
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list = 0 := by
    intro m ξ_list hlen hnot
    have h_le := h_bound_term ξ_list
    rw [hlen, if_neg hnot, Real.norm_eq_abs] at h_le
    exact abs_nonpos_iff.mp h_le
  let g_dom (ξ_list : List (WorldlineJumpMonomer L q_code)) : ℝ :=
    if ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut ξ_list.length then
      B_int * ((M_op * β) ^ ξ_list.length / (ξ_list.length.factorial : ℝ))
    else 0
  have hg_dom_nn : ∀ ξ_list, 0 ≤ g_dom ξ_list := by
    intro ξ_list
    dsimp [g_dom]
    split_ifs
    · exact mul_nonneg hB_int_nn (div_nonneg (pow_nonneg (mul_nonneg hM_op_nn hβ) _) (Nat.cast_nonneg _))
    · exact le_rfl
  have h_sum_m : Summable (fun m : ℕ =>
      ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m, g_dom ξ_list) := by
    refine Summable.of_nonneg_of_le
      (fun m => Finset.sum_nonneg (fun l _ => hg_dom_nn l))
      (fun m => ?_)
      ((Real.summable_pow_div_factorial ((S_mon.card : ℝ) * (M_op * β))).mul_left B_int)
    calc ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m, g_dom ξ_list
      _ ≤ ∑ _ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
            B_int * ((M_op * β) ^ m / (m.factorial : ℝ)) := by
          refine Finset.sum_le_sum fun ξ_list hξ_in => ?_
          have hlen := ((mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m ξ_list).mp hξ_in).1
          dsimp [g_dom]
          rw [hlen, if_pos hξ_in]
      _ = ((worldlineJumpListFinsetOfLength D_field R_cut m).card : ℝ) *
            (B_int * ((M_op * β) ^ m / (m.factorial : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((S_mon.card : ℝ) ^ m) * (B_int * ((M_op * β) ^ m / (m.factorial : ℝ))) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg hB_int_nn (div_nonneg (pow_nonneg (mul_nonneg hM_op_nn hβ) _) (Nat.cast_nonneg _)))
          exact_mod_cast card_worldlineJumpListFinsetOfLength_le_pow D_field R_cut m
      _ = B_int * (((S_mon.card : ℝ) * (M_op * β)) ^ m / (m.factorial : ℝ)) := by
          rw [mul_pow]; ring
  have h_summable_dom : Summable g_dom := by
    refine summable_of_sum_le hg_dom_nn (c := ∑' m : ℕ, ∑ l ∈ worldlineJumpListFinsetOfLength D_field R_cut m, g_dom l) fun u => ?_
    let N := u.sup List.length
    have h_sub_sum : ∑ l ∈ u, g_dom l ≤
        ∑ m ∈ Finset.range (N + 1), ∑ l ∈ worldlineJumpListFinsetOfLength D_field R_cut m, g_dom l := by
      rw [← Finset.sum_biUnion, ← Finset.sum_filter_ne_zero]
      · refine Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => ?_) (fun l _ _ => hg_dom_nn l)
        obtain ⟨hl_u, hne⟩ := Finset.mem_filter.mp hl
        have h_in : l ∈ worldlineJumpListFinsetOfLength D_field R_cut l.length := by
          by_contra hnot
          dsimp [g_dom] at hne
          rw [if_neg hnot] at hne
          exact hne rfl
        rw [Finset.mem_biUnion]
        refine ⟨l.length, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hl_u)), h_in⟩
      · intro m₁ _ m₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro l hl₁ hl₂
        have h1 := ((mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m₁ l).mp hl₁).1
        have h2 := ((mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m₂ l).mp hl₂).1
        exact hne (h1.symm.trans h2)
    exact h_sub_sum.trans (h_sum_m.sum_le_tsum (Finset.range (N + 1))
      (fun m _ => Finset.sum_nonneg (fun l _ => hg_dom_nn l)))
  have h_summable : Summable (singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ) :=
    Summable.of_norm_bounded h_summable_dom h_bound_term
  have h_sum_by_len : Summable (fun m : ℕ => ∑ ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut m,
      singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list) :=
    Summable.of_norm_bounded h_sum_m (fun m =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun l _ => h_bound_term l)))
  refine ⟨h_summable, h_sum_by_len, ?_⟩
  let e_sigma : (Σ m : ℕ, {l : List (WorldlineJumpMonomer L q_code) // l.length = m}) ≃
      List (WorldlineJumpMonomer L q_code) := Equiv.sigmaFiberEquiv List.length
  have h_summable_sigma : Summable ((singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ) ∘ e_sigma) :=
    (Equiv.summable_iff e_sigma).mpr h_summable
  rw [← Equiv.tsum_eq e_sigma (singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ)]
  change (∑' p, ((singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ) ∘ e_sigma) p) = _
  rw [Summable.tsum_sigma h_summable_sigma]
  refine tsum_congr fun m => ?_
  rw [tsum_eq_sum (s := (worldlineJumpListFinsetOfLength D_field R_cut m).subtype (fun l => l.length = m))]
  · refine Finset.sum_bij (fun (x : {l : List (WorldlineJumpMonomer L q_code) // l.length = m}) _ => x.1)
      (fun x hx => Finset.mem_subtype.mp hx)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun l hl => ⟨⟨l, ((mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut m l).mp hl).1⟩,
        Finset.mem_subtype.mpr hl, rfl⟩)
      (fun _ _ => rfl)
  · intro x hx
    rw [Finset.mem_subtype] at hx
    exact h_zero_outside m x.1 x.2 hx

/-- Self-adjointness of `sys.H0 + pauliDiagonalPart sys V R_cut` and its exact scalar exponential action under `gibbsBoltzmannOp` on every syndrome sector `sys.syndromeProjector η`. -/
private lemma isSelfAdjoint_and_gibbsBoltzmannOp_pauliDiagonal_mul_syndromeProjector
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc) :
    let H_diag := sys.H0 + pauliDiagonalPart sys V R_cut
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    ∃ hH_diag : IsSelfAdjoint H_diag,
      ∀ (s : ℝ) (η : IdxCSS[L, q_code, m_max] → Bool),
        gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) s *
          sys.syndromeProjector η =
        if η ∈ realizableSyndromes D_field then
          ((Real.exp (-s * (E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc η)) : ℝ) : ℂ) •
            sys.syndromeProjector η
        else 0 := by
  intro H_diag E_vac
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have hH0_sa : IsSelfAdjoint sys.H0 := by
    have hH0_eq : sys.H0 = ∑ η : IdxCSS[L, q_code, m_max] → Bool,
        ((sys.syndromeEnergy η : ℝ) : ℂ) • sys.syndromeProjector η := by
      calc sys.H0 = sys.H0 * 1 := (mul_one _).symm
        _ = sys.H0 * ∑ η, sys.syndromeProjector η := by rw [h_res.2.2.2.1]
        _ = ∑ η, sys.H0 * sys.syndromeProjector η := Finset.mul_sum _ _ _
        _ = ∑ η, ((sys.syndromeEnergy η : ℝ) : ℂ) • sys.syndromeProjector η :=
            Finset.sum_congr rfl fun η _ => h_res.2.2.2.2.1 η
    rw [hH0_eq, ContinuousLinearMap.isSelfAdjoint_iff', map_sum]
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [map_smulₛₗ, Complex.conj_ofReal,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (h_res.2.1 η).isSelfAdjoint]
  have hD_sa : IsSelfAdjoint (pauliDiagonalPart sys V R_cut) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    unfold pauliDiagonalPart
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    exact ContinuousLinearMap.isSelfAdjoint_iff'.mp
      (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)).1
  have hH_diag : IsSelfAdjoint H_diag := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    dsimp [H_diag]
    rw [map_add, ContinuousLinearMap.isSelfAdjoint_iff'.mp hH0_sa,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hD_sa]
  refine ⟨hH_diag, fun s η => ?_⟩
  by_cases hη : η ∈ realizableSyndromes D_field
  · rw [if_pos hη]
    have h_op : pauliDiagonalPart sys V R_cut - (((E_vac : ℝ) : ℂ) • 1) =
        ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r,
          pauliDiagonalShiftedTerm sys V e_loc r A := by
      ext χ i
      unfold pauliDiagonalPart pauliDiagonalShiftedTerm
      dsimp [E_vac]
      simp [Finset.sum_sub_distrib, Finset.sum_mul]
    have h_shift_act :
        (pauliDiagonalPart sys V R_cut - ((E_vac : ℝ) : ℂ) • 1) * sys.syndromeProjector η =
          ((∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, d_loc r A η : ℝ) : ℂ) •
            sys.syndromeProjector η := by
      rw [h_op, Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
      exact Finset.sum_congr rfl fun A hA => (h_scalar r hr A hA).1.1 η hη
    have h_H_P : H_diag * sys.syndromeProjector η =
        ((E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc η : ℝ) : ℂ) • sys.syndromeProjector η := by
      have h_decomp : H_diag = sys.H0 + (pauliDiagonalPart sys V R_cut - ((E_vac : ℝ) : ℂ) • 1) +
          ((E_vac : ℝ) : ℂ) • 1 := by
        dsimp [H_diag]; ext x i; simp; ring
      rw [h_decomp, add_mul, add_mul, h_res.2.2.2.2.1 η, h_shift_act, smul_mul_assoc, one_mul]
      ext x i
      dsimp [pauliDiagonalSectorEnergy]
      simp
      ring
    refine ContinuousLinearMap.ext fun ψ => ?_
    change gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) s
      (sys.syndromeProjector η ψ) = _
    have h_eig : H_diag (sys.syndromeProjector η ψ) =
        ((E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc η : ℝ) : ℂ) • (sys.syndromeProjector η ψ) := by
      change (H_diag * sys.syndromeProjector η) ψ = _
      rw [h_H_P, ContinuousLinearMap.smul_apply]
    exact perturbed_gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector H_diag hH_diag h_eig s
  · rw [if_neg hη]
    have h_zero : sys.syndromeProjector η = 0 := by
      by_contra h_ne
      obtain ⟨⟨a, b, hab⟩, _⟩ :=
        hilbertTrace_syndromeProjector_eq_P0_of_ne_zero D_field h_valid sys h_sys_checks η h_ne
      exact hη (Finset.mem_filter.mpr ⟨Finset.mem_univ η, a, b, hab⟩)
    rw [h_zero, mul_zero]

/-- Continuity of `u ↦ hilbertTrace (gibbsBoltzmannOp ψ E (a - b * u) * X)`. -/
private lemma continuous_hilbertTrace_gibbsBoltzmannOp_linear
    {L q_code : ℕ}
    (H X : ℬ_CSS[L, q_code]) (hH : IsSelfAdjoint H) (a b : ℝ) :
    Continuous (fun u : ℝ =>
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) (a - b * u) * X)) := by
  have h_eq : (fun u : ℝ =>
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) (a - b * u) * X)) =
    fun u : ℝ =>
      ∑ ω : ManyBodyConfig (SiteCSS[L, q_code]),
        Real.exp (-(a - b * u) * opEigenvalues H hH ω) *
          RCLike.re (inner ℂ (opEigenbasis H hH ω) (X (opEigenbasis H hH ω))) := by
    ext u
    exact hilbertTrace_gibbsBoltzmannOp_mul_eq (opEigenbasis H hH) (opEigenvalues H hH)
      (a - b * u) X
  rw [h_eq]
  fun_prop

/-- **One-Step Worldline Duhamel Recurrence** (Part II, Section 3.5 (`subsec:worldline-expansion`) and Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)): For any jump monomer list `jumps`, any realizable syndrome `σ ∈ realizableSyndromes D_field`, and any Euclidean time `s : ℝ`, expanding `B_trunc s` against `B_diag s` yields the leading diagonal sector exponential minus the sum over the next jump monomer `ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut` of the 1D Duhamel integral over `u ∈ (0..s)`. -/
private lemma hilbertTrace_gibbsBoltzmannOp_weightedLoopOp_duhamel_step
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    {σ : IdxCSS[L, q_code, m_max] → Bool} (hσ : σ ∈ realizableSyndromes D_field)
    (jumps : List (WorldlineJumpMonomer L q_code)) (s : ℝ) :
    let H_trunc := sys.H0 + scaleSplitTruncatedOp V R_cut
    let B_trunc := gibbsBoltzmannOp (opEigenbasis H_trunc hH_trunc) (opEigenvalues H_trunc hH_trunc)
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let E_full (η : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
      E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc η
    let η_end := syndromeXor (worldlineJumpListFlip D_field jumps) σ
    let W_op (l : List (WorldlineJumpMonomer L q_code)) :=
      worldlinePolymerWeightedLoopOp D_field sys V (l, ∅)
    hilbertTrace (B_trunc s * (W_op jumps * sys.syndromeProjector σ)) =
      Real.exp (-s * E_full η_end) * hilbertTrace (sys.syndromeProjector σ * W_op jumps) -
        ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          ∫ u in (0 : ℝ)..s,
            Real.exp (-u * E_full η_end) *
              hilbertTrace (B_trunc (s - u) * (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ)) := by
  intro H_trunc B_trunc E_vac E_full η_end W_op
  obtain ⟨hH_diag, hB_diag_act⟩ :=
    isSelfAdjoint_and_gibbsBoltzmannOp_pauliDiagonal_mul_syndromeProjector
      D_field h_valid sys h_sys_checks V e_loc d_loc h_scalar
  let H_diag := sys.H0 + pauliDiagonalPart sys V R_cut
  let B_diag := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag)
  let V_off := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, pauliOffDiagonalTerm sys V r A
  have hη_end_mem : η_end ∈ realizableSyndromes D_field :=
    syndromeXor_worldlineJumpListFlip_mem_realizableSyndromes D_field jumps σ hσ
  have h_abs_end : sys.syndromeProjector η_end * (W_op jumps * sys.syndromeProjector σ) =
      W_op jumps * sys.syndromeProjector σ :=
    list_prod_reverse_worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V jumps σ hσ
  have hB_diag_W : ∀ u : ℝ,
      B_diag u * (W_op jumps * sys.syndromeProjector σ) =
        ((Real.exp (-u * E_full η_end) : ℝ) : ℂ) • (W_op jumps * sys.syndromeProjector σ) := by
    intro u
    calc B_diag u * (W_op jumps * sys.syndromeProjector σ)
      _ = (B_diag u * sys.syndromeProjector η_end) * (W_op jumps * sys.syndromeProjector σ) := by
          rw [mul_assoc, h_abs_end]
      _ = (((Real.exp (-u * E_full η_end) : ℝ) : ℂ) • sys.syndromeProjector η_end) *
            (W_op jumps * sys.syndromeProjector σ) := by
          rw [hB_diag_act u η_end, if_pos hη_end_mem]
      _ = ((Real.exp (-u * E_full η_end) : ℝ) : ℂ) • (W_op jumps * sys.syndromeProjector σ) := by
          rw [smul_mul_assoc, h_abs_end]
  have h_lead : hilbertTrace (B_diag s * (W_op jumps * sys.syndromeProjector σ)) =
      Real.exp (-s * E_full η_end) * hilbertTrace (sys.syndromeProjector σ * W_op jumps) := by
    rw [hB_diag_W s,
      (hilbertTrace_add_and_complex_smul_decomp (W_op jumps * sys.syndromeProjector σ) 0 0 0
        (Real.exp (-s * E_full η_end)) 0).2.1,
      hilbertTrace_mul_comm_aux (W_op jumps) (sys.syndromeProjector σ)]
  have h_diff_H : H_diag - H_trunc = -V_off := by
    dsimp [H_diag, H_trunc, V_off]
    rw [scaleSplitTruncatedOp_eq_pauliDiagonalPart_add_offDiagonal sys V]
    abel
  have h_duh := hilbertTrace_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral
    H_trunc H_diag (W_op jumps * sys.syndromeProjector σ) hH_trunc hH_diag s
  (try dsimp only at h_duh)
  change hilbertTrace ((B_diag s - B_trunc s) * (W_op jumps * sys.syndromeProjector σ)) =
    -∫ u in (0 : ℝ)..s,
      hilbertTrace (B_trunc (s - u) * (H_diag - H_trunc) * B_diag u *
        (W_op jumps * sys.syndromeProjector σ)) at h_duh
  rw [sub_mul, PerturbedThermalBarrier.hilbertTrace_sub, h_diff_H] at h_duh
  have h_append_W : ∀ ξ : WorldlineJumpMonomer L q_code,
      worldlineSyndromeShiftBlockOp D_field sys V ξ * (W_op jumps * sys.syndromeProjector σ) =
        W_op (jumps ++ [ξ]) * sys.syndromeProjector σ := by
    intro ξ
    dsimp [W_op, worldlinePolymerWeightedLoopOp]
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.map_cons, List.prod_cons, mul_assoc]
  have h_integrand : ∀ u : ℝ,
      hilbertTrace (B_trunc (s - u) * (-V_off) * B_diag u * (W_op jumps * sys.syndromeProjector σ)) =
        -∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          Real.exp (-u * E_full η_end) *
            hilbertTrace (B_trunc (s - u) * (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ)) := by
    intro u
    have h_step : B_trunc (s - u) * (-V_off) * B_diag u * (W_op jumps * sys.syndromeProjector σ) =
        ((-Real.exp (-u * E_full η_end) : ℝ) : ℂ) •
          ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
            B_trunc (s - u) * (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ) := by
      calc B_trunc (s - u) * (-V_off) * B_diag u * (W_op jumps * sys.syndromeProjector σ)
        _ = B_trunc (s - u) * (-V_off) * (B_diag u * (W_op jumps * sys.syndromeProjector σ)) := by
            simp only [mul_assoc]
        _ = B_trunc (s - u) * (-V_off) *
              (((Real.exp (-u * E_full η_end) : ℝ) : ℂ) •
                (sys.syndromeProjector η_end * (W_op jumps * sys.syndromeProjector σ))) := by
            rw [hB_diag_W u, h_abs_end]
        _ = ((-Real.exp (-u * E_full η_end) : ℝ) : ℂ) •
              (B_trunc (s - u) * ((V_off * sys.syndromeProjector η_end) *
                (W_op jumps * sys.syndromeProjector σ))) := by
            ext ψ; simp
        _ = ((-Real.exp (-u * E_full η_end) : ℝ) : ℂ) •
              ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
                B_trunc (s - u) * (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ) := by
            rw [sum_pauliOffDiagonalTerm_mul_syndromeProjector_eq_sum_worldlineAllJumpMonomerFinset
              D_field sys h_sys_checks V hη_end_mem, Finset.sum_mul, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun ξ _ => ?_
            rw [mul_assoc (worldlineSyndromeShiftBlockOp D_field sys V ξ), h_abs_end, h_append_W ξ]
    rw [h_step,
      (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 (-Real.exp (-u * E_full η_end)) 0).2.1,
      hilbertTrace_sum, neg_mul, Finset.mul_sum]
  have h_duh' :
      hilbertTrace (B_diag s * (W_op jumps * sys.syndromeProjector σ)) -
        hilbertTrace (B_trunc s * (W_op jumps * sys.syndromeProjector σ)) =
      ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
        ∫ u in (0 : ℝ)..s,
          Real.exp (-u * E_full η_end) *
            hilbertTrace (B_trunc (s - u) * (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ)) := by
    rw [h_duh]
    simp_rw [h_integrand, intervalIntegral.integral_neg, neg_neg]
    rw [intervalIntegral.integral_finset_sum]
    intro ξ _
    refine Continuous.intervalIntegrable ?_ 0 s
    exact (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
      ((continuous_hilbertTrace_gibbsBoltzmannOp_linear H_trunc
        (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ) hH_trunc s 1).congr
        (fun x => by rw [one_mul]))
  linarith [h_lead, h_duh']

/-- Composing any function `G` on syndrome configurations with the foldr of filtered jump flips
produces a jointly measurable function of `(τ, t)`. -/
private lemma measurable_foldr_syndromeXor_filter
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    ∀ (l : List (Fin ξ_list.length)) (G : (IdxCSS[L, q_code, m_max] → Bool) → ℝ),
      Measurable (fun p : (Fin ξ_list.length → ℝ) × ℝ =>
        G ((l.filter (fun j => decide (p.1 j ≤ p.2))).foldr
          (fun j acc =>
            syndromeXor (staticCSSPauliFlip D_field (ξ_list.get j).2.1 (ξ_list.get j).2.2) acc)
          σ))
  | [], G => by dsimp; exact measurable_const
  | j :: tl, G => by
    have h_eq : (fun p : (Fin ξ_list.length → ℝ) × ℝ =>
        G (((j :: tl).filter (fun i => decide (p.1 i ≤ p.2))).foldr
          (fun i acc =>
            syndromeXor (staticCSSPauliFlip D_field (ξ_list.get i).2.1 (ξ_list.get i).2.2) acc)
          σ)) =
      fun p : (Fin ξ_list.length → ℝ) × ℝ =>
        if p.1 j ≤ p.2 then
          (fun η => G (syndromeXor
            (staticCSSPauliFlip D_field (ξ_list.get j).2.1 (ξ_list.get j).2.2) η))
            ((tl.filter (fun i => decide (p.1 i ≤ p.2))).foldr
              (fun i acc =>
                syndromeXor (staticCSSPauliFlip D_field (ξ_list.get i).2.1 (ξ_list.get i).2.2) acc)
              σ)
        else
          G ((tl.filter (fun i => decide (p.1 i ≤ p.2))).foldr
            (fun i acc =>
              syndromeXor (staticCSSPauliFlip D_field (ξ_list.get i).2.1 (ξ_list.get i).2.2) acc)
            σ) := by
      ext p
      by_cases h : p.1 j ≤ p.2 <;> simp [List.filter, h]
    rw [h_eq]
    exact Measurable.ite
      (measurableSet_le ((measurable_pi_apply j).comp measurable_fst) measurable_snd)
      (measurable_foldr_syndromeXor_filter D_field ξ_list σ tl
        (fun η => G (syndromeXor
          (staticCSSPauliFlip D_field (ξ_list.get j).2.1 (ξ_list.get j).2.2) η)))
      (measurable_foldr_syndromeXor_filter D_field ξ_list σ tl G)

/-- For any function `G` on syndromes, `(τ, t) ↦ G (worldlineTrajectorySyndrome D_field ξ_list σ τ t)`
is jointly measurable, and its integral over `t ∈ Set.Icc 0 β` is measurable and bounded in `τ`. -/
private lemma measurable_and_bounded_integral_worldlineTrajectorySyndrome
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (σ : IdxCSS[L, q_code, m_max] → Bool) (β : ℝ)
    (G : (IdxCSS[L, q_code, m_max] → Bool) → ℝ) :
    Measurable (fun τ : Fin ξ_list.length → ℝ =>
      ∫ t in Set.Icc 0 β, G (worldlineTrajectorySyndrome D_field ξ_list σ τ t)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : Fin ξ_list.length → ℝ,
      |∫ t in Set.Icc 0 β, G (worldlineTrajectorySyndrome D_field ξ_list σ τ t)| ≤ B := by
  have h_meas_joint : Measurable (fun p : (Fin ξ_list.length → ℝ) × ℝ =>
      G (worldlineTrajectorySyndrome D_field ξ_list σ p.1 p.2)) := by
    simpa [worldlineTrajectorySyndrome] using
      measurable_foldr_syndromeXor_filter D_field ξ_list σ (List.finRange ξ_list.length) G
  have h_meas : Measurable (fun τ : Fin ξ_list.length → ℝ =>
      ∫ t in Set.Icc 0 β, G (worldlineTrajectorySyndrome D_field ξ_list σ τ t)) :=
    (h_meas_joint.stronglyMeasurable.integral_prod_right').measurable
  let M : ℝ := ∑ η : IdxCSS[L, q_code, m_max] → Bool, |G η|
  have hM_nn : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_pt : ∀ τ t, |G (worldlineTrajectorySyndrome D_field ξ_list σ τ t)| ≤ M := by
    intro τ t
    exact Finset.single_le_sum (fun η _ => abs_nonneg (G η)) (Finset.mem_univ _)
  refine ⟨h_meas, (|β| * M), mul_nonneg (abs_nonneg β) hM_nn, fun τ => ?_⟩
  rcases le_or_gt 0 β with hβ | hβ
  · calc
      |∫ t in Set.Icc 0 β, G (worldlineTrajectorySyndrome D_field ξ_list σ τ t)|
        = ‖∫ t in Set.Icc 0 β, G (worldlineTrajectorySyndrome D_field ξ_list σ τ t)‖ := rfl
      _ ≤ M * (MeasureTheory.volume (Set.Icc (0 : ℝ) β)).toReal := by
          apply MeasureTheory.norm_setIntegral_le_of_norm_le_const (isCompact_Icc.measure_lt_top)
          intro t _
          exact h_pt τ t
      _ = |β| * M := by
          rw [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hβ, abs_of_nonneg hβ, mul_comm]
  · have h_empty : Set.Icc (0 : ℝ) β = ∅ := Set.Icc_eq_empty (not_le.mpr hβ)
    rw [h_empty, MeasureTheory.setIntegral_empty, abs_zero]
    exact mul_nonneg (abs_nonneg β) hM_nn

private lemma measurableSet_inOrderedDysonSimplex (k : ℕ) (s : ℝ) :
    MeasurableSet {τ : Fin k → ℝ | InOrderedDysonSimplex s τ} := by
  have h_eq : {τ : Fin k → ℝ | InOrderedDysonSimplex s τ} =
      (⋂ j : Fin k, {τ | 0 ≤ τ j} ∩ {τ | τ j ≤ s}) ∩
      (⋂ i : Fin k, ⋂ j : Fin k, ⋂ (_ : i < j), {τ | τ i < τ j}) := by
    ext τ; simp [InOrderedDysonSimplex, StrictMono]
  rw [h_eq]
  exact (MeasurableSet.iInter fun j =>
    (measurableSet_le measurable_const (measurable_pi_apply j)).inter
      (measurableSet_le (measurable_pi_apply j) measurable_const)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))

private lemma integrable_of_measurable_bounded_support_piFin
    {k : ℕ} {G : (Fin k → ℝ) → ℝ} (hG_meas : Measurable G)
    {B a b : ℝ} (hB : 0 ≤ B) (h_bd : ∀ τ, |G τ| ≤ B)
    (h_supp : ∀ τ : Fin k → ℝ, (¬ ∀ i : Fin k, a ≤ τ i ∧ τ i ≤ b) → G τ = 0) :
    MeasureTheory.Integrable G := by
  let box : Set (Fin k → ℝ) := Set.Icc (fun _ => a) (fun _ => max b a)
  have h_sub : ∀ τ : Fin k → ℝ, (∀ i : Fin k, a ≤ τ i ∧ τ i ≤ b) → τ ∈ box :=
    fun τ h => ⟨fun i => (h i).1, fun i => (h i).2.trans (le_max_left b a)⟩
  have h_int_box : MeasureTheory.IntegrableOn G box := by
    apply MeasureTheory.Integrable.integrableOn
    refine MeasureTheory.Integrable.mono' (g := box.indicator (fun _ => B))
      ((continuousOn_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
      hG_meas.aestronglyMeasurable ?_
    filter_upwards with τ
    by_cases hτ : ∀ i : Fin k, a ≤ τ i ∧ τ i ≤ b
    · rw [Set.indicator_of_mem (h_sub τ hτ), Real.norm_eq_abs]; exact h_bd τ
    · rw [h_supp τ hτ, norm_zero]; exact Set.indicator_nonneg (fun _ _ => hB) τ
  exact h_int_box.integrable_of_ae_notMem_eq_zero
    (Filter.Eventually.of_forall (fun τ hτ => h_supp τ (fun h => hτ (h_sub τ h))))

/-- The ordered-Dyson-simplex integrand in `singleSectorWorldlineDysonJumpWeight` is integrable
for every Mayer bond subset `Θ`. -/
private lemma integrable_inOrderedDysonSimplex_mayerProduct
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (β : ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (Θ : Finset (ℕ × Finset (Box3D L))) :
    MeasureTheory.Integrable (fun τ : Fin ξ_list.length → ℝ =>
      if InOrderedDysonSimplex β τ then
        Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
          ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ
      else 0) := by
  obtain ⟨h_meas_bare, B0, _, hB0⟩ :=
    measurable_and_bounded_integral_worldlineTrajectorySyndrome D_field ξ_list σ β
      (fun η => sys.syndromeEnergy η - sys.syndromeEnergy σ)
  have h_mayer_mb : ∀ ϑ : ℕ × Finset (Box3D L),
      Measurable (worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ) ∧
      ∃ Bϑ : ℝ, 0 ≤ Bϑ ∧ ∀ τ, |worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ| ≤ Bϑ := by
    intro ϑ
    obtain ⟨hm, B, _, hB⟩ :=
      measurable_and_bounded_integral_worldlineTrajectorySyndrome D_field ξ_list σ β
        (fun η => d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ)
    refine ⟨(hm.neg.exp).sub measurable_const, Real.exp B + 1, by positivity, fun τ => ?_⟩
    dsimp [worldlineMayerBondFactor]
    have h_le : -(∫ t in Set.Icc 0 β, (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) -
        d_loc ϑ.1 ϑ.2 σ)) ≤ B := (neg_le_abs _).trans (hB τ)
    calc |Real.exp (-(∫ t in Set.Icc 0 β,
          (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) - d_loc ϑ.1 ϑ.2 σ))) - 1|
      _ ≤ |Real.exp (-(∫ t in Set.Icc 0 β,
            (d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) - d_loc ϑ.1 ϑ.2 σ)))| + |1| :=
          abs_sub _ _
      _ ≤ Real.exp B + 1 := by
          rw [abs_of_pos (Real.exp_pos _), abs_one]; linarith [Real.exp_le_exp.mpr h_le]
  choose Bϑ hBϑ_nn hBϑ using fun ϑ => (h_mayer_mb ϑ).2
  have h_meas_prod : Measurable (fun τ : Fin ξ_list.length → ℝ =>
      Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
        ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ) :=
    (h_meas_bare.neg.exp).mul (Finset.measurable_prod Θ (fun ϑ _ => (h_mayer_mb ϑ).1))
  refine integrable_of_measurable_bounded_support_piFin
    (B := Real.exp B0 * ∏ ϑ ∈ Θ, Bϑ ϑ)
    (Measurable.ite (measurableSet_inOrderedDysonSimplex _ β) h_meas_prod measurable_const)
    (mul_nonneg (Real.exp_pos B0).le (Finset.prod_nonneg (s := Θ) (fun ϑ _ => hBϑ_nn ϑ)))
    (fun τ => ?_) (fun τ h_not => if_neg (fun h_in => h_not h_in.1))
  split_ifs with hτ
  · rw [abs_mul, abs_of_pos (Real.exp_pos _), Finset.abs_prod]
    exact mul_le_mul (Real.exp_le_exp.mpr ((neg_le_abs _).trans (hB0 τ)))
      (Finset.prod_le_prod₀ (fun ϑ _ => abs_nonneg _) (fun ϑ _ => hBϑ ϑ τ))
      (Finset.prod_nonneg (fun ϑ _ => abs_nonneg _)) (Real.exp_pos _).le
  · rw [abs_zero]
    exact mul_nonneg (Real.exp_pos B0).le (Finset.prod_nonneg (s := Θ) (fun ϑ _ => hBϑ_nn ϑ))

/-- Recursive 1D iterated Duhamel integral for a jump monomer list `ξ_list`, starting syndrome `σ₀`,
and total imaginary time `s`. -/
private noncomputable def worldlineIteratedDuhamelIntegral
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (E_full : (IdxCSS[L, q_code, m_max] → Bool) → ℝ) :
    List (WorldlineJumpMonomer L q_code) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ → ℝ
  | [], σ₀, s => Real.exp (-s * E_full σ₀)
  | ξ :: tl, σ₀, s =>
      ∫ u in (0 : ℝ)..s, Real.exp (-u * E_full σ₀) *
        worldlineIteratedDuhamelIntegral D_field E_full tl
          (syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀) (s - u)

private lemma continuous_worldlineIteratedDuhamelIntegral
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (E_full : (IdxCSS[L, q_code, m_max] → Bool) → ℝ) :
    ∀ (l : List (WorldlineJumpMonomer L q_code)) (σ₀ : IdxCSS[L, q_code, m_max] → Bool),
      Continuous (worldlineIteratedDuhamelIntegral D_field E_full l σ₀)
  | [], σ₀ => by
    dsimp [worldlineIteratedDuhamelIntegral]
    exact Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)
  | ξ :: tl, σ₀ => by
    let σ₁ := syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀
    let g := worldlineIteratedDuhamelIntegral D_field E_full tl σ₁
    have hg : Continuous g := continuous_worldlineIteratedDuhamelIntegral D_field E_full tl σ₁
    have h_eq : worldlineIteratedDuhamelIntegral D_field E_full (ξ :: tl) σ₀ =
        fun s => Real.exp (-s * E_full σ₀) * ∫ v in (0 : ℝ)..s, Real.exp (v * E_full σ₀) * g v := by
      ext s; dsimp [worldlineIteratedDuhamelIntegral, g, σ₁]
      have h_sub := intervalIntegral.integral_comp_sub_left
        (a := 0) (b := s) (fun v => Real.exp (-(s - v) * E_full σ₀) * g v) s
      rw [sub_self, sub_zero] at h_sub
      have h_congr : (∫ x in (0 : ℝ)..s, Real.exp (-(s - (s - x)) * E_full σ₀) * g (s - x)) =
          ∫ u in (0 : ℝ)..s, Real.exp (-u * E_full σ₀) * g (s - u) :=
        intervalIntegral.integral_congr (fun u _ => by rw [sub_sub_cancel])
      rw [← h_congr, h_sub, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      have h_exp : Real.exp (-(s - v) * E_full σ₀) =
          Real.exp (-s * E_full σ₀) * Real.exp (v * E_full σ₀) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h_exp, mul_assoc]
    rw [h_eq]
    exact (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
      (intervalIntegral.continuous_primitive (fun a b =>
        (((Real.continuous_exp.comp (continuous_id.mul continuous_const)).mul hg).intervalIntegrable a b)) 0)

lemma worldlineJumpListFinsetOfLength_zero_and_succ
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (R_cut : ℕ) :
    worldlineJumpListFinsetOfLength D_field R_cut 0 = {[]} ∧
    ∀ (j : ℕ) (g : List (WorldlineJumpMonomer L q_code) → ℝ),
      (∑ l ∈ worldlineJumpListFinsetOfLength D_field R_cut (j + 1), g l) =
        ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut j, g (ξ :: tl) := by
  refine ⟨?_, fun j g => ?_⟩
  · ext l
    rw [mem_worldlineJumpListFinsetOfLength_iff_local, Finset.mem_singleton, List.length_eq_zero_iff]
    exact ⟨fun h => h.1, by rintro rfl; exact ⟨rfl, fun _ h => False.elim (List.not_mem_nil h)⟩⟩
  · let S_mon := worldlineAllJumpMonomerFinset D_field R_cut
    let S_j := worldlineJumpListFinsetOfLength D_field R_cut j
    have h_bij : worldlineJumpListFinsetOfLength D_field R_cut (j + 1) =
        (S_mon ×ˢ S_j).image (fun p => p.1 :: p.2) := by
      ext l; rw [mem_worldlineJumpListFinsetOfLength_iff_local, Finset.mem_image]
      constructor
      · rintro ⟨hlen, hmem⟩
        cases l with
        | nil => simp at hlen
        | cons ξ tl =>
          refine ⟨(ξ, tl), Finset.mem_product.mpr ⟨hmem ξ List.mem_cons_self, ?_⟩, rfl⟩
          rw [mem_worldlineJumpListFinsetOfLength_iff_local]
          exact ⟨by simpa using hlen, fun ζ hζ => hmem ζ (List.mem_cons_of_mem ξ hζ)⟩
      · rintro ⟨⟨ξ, tl⟩, hp, rfl⟩
        rcases Finset.mem_product.mp hp with ⟨hξ, htl⟩
        rcases (mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut j tl).mp htl with ⟨hlen, hmem⟩
        refine ⟨by simp [hlen], fun ζ hζ => ?_⟩
        rcases List.mem_cons.mp hζ with rfl | h_tl <;> [exact hξ; exact hmem ζ h_tl]
    rw [h_bij, Finset.sum_image (fun p₁ _ p₂ _ h_eq =>
      Prod.ext (List.cons.inj h_eq).1 (List.cons.inj h_eq).2), Finset.sum_product]

private lemma syndromeXor_worldlineJumpListFlip_append_singleton
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (jumps : List (WorldlineJumpMonomer L q_code))
    (ξ : WorldlineJumpMonomer L q_code) (σ : IdxCSS[L, q_code, m_max] → Bool) :
    syndromeXor (worldlineJumpListFlip D_field (jumps ++ [ξ])) σ =
      syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2)
        (syndromeXor (worldlineJumpListFlip D_field jumps) σ) := by
  have h_flip : ∀ l : List (WorldlineJumpMonomer L q_code),
      worldlineJumpListFlip D_field (l ++ [ξ]) =
        syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) (worldlineJumpListFlip D_field l) := by
    intro l; induction l with
    | nil => ext c; dsimp [worldlineJumpListFlip, syndromeXor]
    | cons hd tl ih =>
      change syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2)
          (worldlineJumpListFlip D_field (tl ++ [ξ])) =
        syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2)
          (syndromeXor (staticCSSPauliFlip D_field hd.2.1 hd.2.2) (worldlineJumpListFlip D_field tl))
      rw [ih]; ext c; dsimp [syndromeXor]
      cases staticCSSPauliFlip D_field hd.2.1 hd.2.2 c <;>
        cases staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c <;>
        cases worldlineJumpListFlip D_field tl c <;> rfl
  rw [h_flip jumps]; ext c; dsimp [syndromeXor]
  cases staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 c <;>
    cases worldlineJumpListFlip D_field jumps c <;> cases σ c <;> rfl

private lemma abs_intervalIntegral_le_of_abs_le_local {s : ℝ} (hs : 0 ≤ s)
    (f g : ℝ → ℝ) (hf : IntervalIntegrable f MeasureTheory.volume 0 s)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 s)
    (h_le : ∀ u ∈ Set.Icc 0 s, |f u| ≤ g u) :
    |∫ u in (0 : ℝ)..s, f u| ≤ ∫ u in (0 : ℝ)..s, g u :=
  (intervalIntegral.abs_integral_le_integral_abs hs).trans
    (intervalIntegral.integral_mono_on hs hf.abs hg h_le)

private lemma intervalIntegral_pow_div_factorial_mul_const_local (n : ℕ) (s C : ℝ) :
    (∫ u in (0 : ℝ)..s, ((s - u) ^ n / (Nat.factorial n : ℝ)) * C) =
      (s ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) * C := by
  have h_sub := intervalIntegral.integral_comp_sub_left
    (a := 0) (b := s) (fun v : ℝ => (v ^ n / (Nat.factorial n : ℝ)) * C) s
  rw [sub_self, sub_zero] at h_sub; rw [h_sub]
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h_deriv : ∀ u : ℝ, HasDerivAt (fun x : ℝ => (x ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) * C)
      ((u ^ n / (Nat.factorial n : ℝ)) * C) u := fun u => by
    have h1 := ((hasDerivAt_pow (n + 1) u).div_const (Nat.factorial (n + 1) : ℝ)).mul_const C
    have h_eq : (((n + 1 : ℕ) : ℝ) * u ^ (n + 1 - 1) / (Nat.factorial (n + 1) : ℝ)) * C =
        (u ^ n / (Nat.factorial n : ℝ)) * C := by
      rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
        mul_div_mul_left (u ^ n) (Nat.factorial n : ℝ) hn1]
    rwa [h_eq] at h1
  have h_int : IntervalIntegrable (fun u : ℝ => (u ^ n / (Nat.factorial n : ℝ)) * C)
      MeasureTheory.volume 0 s :=
    (((continuous_id.pow n).div_const _).mul continuous_const).intervalIntegrable 0 s
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h_deriv u) h_int,
    zero_pow (Nat.succ_ne_zero n), zero_div, zero_mul, sub_zero]

/-- Iterated $r$-step Duhamel remainder bound for
`hilbertTrace (B_trunc s * (W_op jumps * sys.syndromeProjector σ))`. -/
private lemma abs_duhamelRemainder_le
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    {σ : IdxCSS[L, q_code, m_max] → Bool} (hσ : σ ∈ realizableSyndromes D_field) :
    let H_trunc := sys.H0 + scaleSplitTruncatedOp V R_cut
    let B_trunc := gibbsBoltzmannOp (opEigenbasis H_trunc hH_trunc) (opEigenvalues H_trunc hH_trunc)
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let E_full (η : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
      E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc η
    let W_op (l : List (WorldlineJumpMonomer L q_code)) :=
      worldlinePolymerWeightedLoopOp D_field sys V (l, ∅)
    let K_sum : ℝ := ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
      ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖
    let E_max : ℝ := max (∑ ω : ManyBodyConfig (SiteCSS[L, q_code]), |opEigenvalues H_trunc hH_trunc ω|)
      (∑ η : IdxCSS[L, q_code, m_max] → Bool, |E_full η|)
    let C_tr : ℝ := (Fintype.card (ManyBodyConfig (SiteCSS[L, q_code])) : ℝ)
    ∀ (r : ℕ) (jumps : List (WorldlineJumpMonomer L q_code)) {s : ℝ} (hs : 0 ≤ s),
      |hilbertTrace (B_trunc s * (W_op jumps * sys.syndromeProjector σ)) -
        ∑ j ∈ Finset.range r,
          ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut j,
            ((-1 : ℝ) ^ j) * hilbertTrace (sys.syndromeProjector σ * W_op (jumps ++ tl)) *
              worldlineIteratedDuhamelIntegral D_field E_full tl
                (syndromeXor (worldlineJumpListFlip D_field jumps) σ) s| ≤
      C_tr * (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod *
        Real.exp (s * E_max) * ((K_sum * s) ^ r / (Nat.factorial r : ℝ)) := by
  intro H_trunc B_trunc E_vac E_full W_op K_sum E_max C_tr
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have hK_sum_nn : 0 ≤ K_sum := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hE_max_nn : 0 ≤ E_max :=
    le_trans (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (le_max_left _ _)
  have hE_full_le : ∀ η, |E_full η| ≤ E_max := fun η =>
    le_trans (Finset.single_le_sum (f := fun x => |E_full x|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ η)) (le_max_right _ _)
  let Rem (r : ℕ) (jumps : List (WorldlineJumpMonomer L q_code)) (s : ℝ) : ℝ :=
    hilbertTrace (B_trunc s * (W_op jumps * sys.syndromeProjector σ)) -
      ∑ j ∈ Finset.range r,
        ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut j,
          ((-1 : ℝ) ^ j) * hilbertTrace (sys.syndromeProjector σ * W_op (jumps ++ tl)) *
            worldlineIteratedDuhamelIntegral D_field E_full tl
              (syndromeXor (worldlineJumpListFlip D_field jumps) σ) s
  have hRem_cont : ∀ r jumps, Continuous (Rem r jumps) := by
    intro r jumps
    refine (continuous_hilbertTrace_gibbsBoltzmannOp_linear H_trunc
      (W_op jumps * sys.syndromeProjector σ) hH_trunc 0 (-1) |>.congr (fun s => by simp [B_trunc])).sub ?_
    refine continuous_finset_sum _ (fun j _ => continuous_finset_sum _ (fun tl _ => ?_))
    exact continuous_const.mul (continuous_worldlineIteratedDuhamelIntegral D_field E_full tl _)
  have hRem_succ : ∀ r jumps s,
      Rem (r + 1) jumps s =
        -∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          ∫ u in (0 : ℝ)..s,
            Real.exp (-u * E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ)) *
              Rem r (jumps ++ [ξ]) (s - u) := by
    intro r jumps s
    let η_end := syndromeXor (worldlineJumpListFlip D_field jumps) σ
    obtain ⟨h_len0, h_len_succ⟩ := worldlineJumpListFinsetOfLength_zero_and_succ D_field R_cut
    have h_step := hilbertTrace_gibbsBoltzmannOp_weightedLoopOp_duhamel_step
      D_field h_valid sys h_sys_checks V e_loc d_loc h_scalar hH_trunc hσ jumps s
    dsimp only [Rem]
    rw [Finset.sum_range_succ', h_len0, Finset.sum_singleton]
    dsimp only [worldlineIteratedDuhamelIntegral]
    rw [List.append_nil, pow_zero, one_mul, mul_comm (hilbertTrace _)]
    have h_sum_shift :
        (∑ k ∈ Finset.range r,
          ∑ l ∈ worldlineJumpListFinsetOfLength D_field R_cut (k + 1),
            ((-1 : ℝ) ^ (k + 1)) * hilbertTrace (sys.syndromeProjector σ * W_op (jumps ++ l)) *
              worldlineIteratedDuhamelIntegral D_field E_full l η_end s) =
        -∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          ∫ u in (0 : ℝ)..s,
            Real.exp (-u * E_full η_end) *
              ∑ k ∈ Finset.range r,
                ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut k,
                  ((-1 : ℝ) ^ k) * hilbertTrace (sys.syndromeProjector σ * W_op ((jumps ++ [ξ]) ++ tl)) *
                    worldlineIteratedDuhamelIntegral D_field E_full tl
                      (syndromeXor (worldlineJumpListFlip D_field (jumps ++ [ξ])) σ) (s - u) := by
      have h_inner : ∀ k : ℕ,
          (∑ l ∈ worldlineJumpListFinsetOfLength D_field R_cut (k + 1),
            ((-1 : ℝ) ^ (k + 1)) * hilbertTrace (sys.syndromeProjector σ * W_op (jumps ++ l)) *
              worldlineIteratedDuhamelIntegral D_field E_full l η_end s) =
          ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
            -(∫ u in (0 : ℝ)..s,
              Real.exp (-u * E_full η_end) *
                ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut k,
                  ((-1 : ℝ) ^ k) * hilbertTrace (sys.syndromeProjector σ * W_op ((jumps ++ [ξ]) ++ tl)) *
                    worldlineIteratedDuhamelIntegral D_field E_full tl
                      (syndromeXor (worldlineJumpListFlip D_field (jumps ++ [ξ])) σ) (s - u)) := by
        intro k; rw [h_len_succ k]
        refine Finset.sum_congr rfl (fun ξ _ => ?_)
        have h_term : ∀ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut k,
            ((-1 : ℝ) ^ (k + 1)) * hilbertTrace (sys.syndromeProjector σ * W_op (jumps ++ (ξ :: tl))) *
              worldlineIteratedDuhamelIntegral D_field E_full (ξ :: tl) η_end s =
            -(∫ u in (0 : ℝ)..s, Real.exp (-u * E_full η_end) *
              (((-1 : ℝ) ^ k) * hilbertTrace (sys.syndromeProjector σ * W_op ((jumps ++ [ξ]) ++ tl)) *
                worldlineIteratedDuhamelIntegral D_field E_full tl
                  (syndromeXor (worldlineJumpListFlip D_field (jumps ++ [ξ])) σ) (s - u))) := by
          intro tl _; dsimp only [worldlineIteratedDuhamelIntegral]
          rw [pow_succ, mul_neg, mul_one, neg_mul, neg_mul,
            show jumps ++ (ξ :: tl) = (jumps ++ [ξ]) ++ tl by simp,
            syndromeXor_worldlineJumpListFlip_append_singleton D_field jumps ξ σ,
            ← intervalIntegral.integral_const_mul]
          congr 1; exact intervalIntegral.integral_congr (fun u _ => by ring)
        rw [Finset.sum_congr rfl h_term, Finset.sum_neg_distrib]
        congr 1; rw [← intervalIntegral.integral_finset_sum]
        · exact intervalIntegral.integral_congr (fun u _ => by rw [Finset.mul_sum])
        · intro tl _; refine Continuous.intervalIntegrable ?_ 0 s
          exact (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
            (continuous_const.mul ((continuous_worldlineIteratedDuhamelIntegral D_field E_full tl _).comp
              (continuous_const.sub continuous_id)))
      simp_rw [h_inner]; rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      rw [Finset.sum_neg_distrib]; refine congrArg Neg.neg ?_
      rw [← intervalIntegral.integral_finset_sum]
      · exact intervalIntegral.integral_congr (fun u _ => by rw [Finset.mul_sum])
      · intro k _; refine Continuous.intervalIntegrable ?_ 0 s
        refine (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
          (continuous_finset_sum _ (fun tl _ => ?_))
        exact continuous_const.mul ((continuous_worldlineIteratedDuhamelIntegral D_field E_full tl _).comp
          (continuous_const.sub continuous_id))
    change hilbertTrace (B_trunc s * (W_op jumps * sys.syndromeProjector σ)) -
      ((∑ k ∈ Finset.range r,
          ∑ l ∈ worldlineJumpListFinsetOfLength D_field R_cut (k + 1),
            ((-1 : ℝ) ^ (k + 1)) * hilbertTrace (sys.syndromeProjector σ * W_op (jumps ++ l)) *
              worldlineIteratedDuhamelIntegral D_field E_full l η_end s) +
        Real.exp (-s * E_full η_end) * hilbertTrace (sys.syndromeProjector σ * W_op jumps)) = _
    rw [h_sum_shift, h_step]
    have h_merge : ∀ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
        (∫ u in (0 : ℝ)..s, Real.exp (-u * E_full η_end) *
          hilbertTrace (B_trunc (s - u) * (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ))) -
        (∫ u in (0 : ℝ)..s, Real.exp (-u * E_full η_end) *
          ∑ k ∈ Finset.range r, ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut k,
            ((-1 : ℝ) ^ k) * hilbertTrace (sys.syndromeProjector σ * W_op ((jumps ++ [ξ]) ++ tl)) *
              worldlineIteratedDuhamelIntegral D_field E_full tl
                (syndromeXor (worldlineJumpListFlip D_field (jumps ++ [ξ])) σ) (s - u)) =
        ∫ u in (0 : ℝ)..s, Real.exp (-u * E_full η_end) * Rem r (jumps ++ [ξ]) (s - u) := by
      intro ξ _; rw [← intervalIntegral.integral_sub]
      · exact intervalIntegral.integral_congr (fun u _ => by dsimp [Rem]; ring)
      · refine Continuous.intervalIntegrable ?_ 0 s
        exact (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
          ((continuous_hilbertTrace_gibbsBoltzmannOp_linear H_trunc
            (W_op (jumps ++ [ξ]) * sys.syndromeProjector σ) hH_trunc s 1).congr (fun x => by rw [one_mul]))
      · refine Continuous.intervalIntegrable ?_ 0 s
        refine (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
          (continuous_finset_sum _ (fun k _ => continuous_finset_sum _ (fun tl _ => ?_)))
        exact continuous_const.mul ((continuous_worldlineIteratedDuhamelIntegral D_field E_full tl _).comp
          (continuous_const.sub continuous_id))
    rw [← Finset.sum_congr rfl h_merge, Finset.sum_sub_distrib]; ring
  intro r
  induction r with
  | zero =>
    intro jumps s hs; dsimp [Rem]
    rw [sub_zero, pow_zero, Nat.cast_one, div_one, mul_one, hilbertTrace_gibbsBoltzmannOp_mul_eq]
    have h_norm_W : ‖W_op jumps * sys.syndromeProjector σ‖ ≤
        (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod := by
      have hP_le : ‖sys.syndromeProjector σ‖ ≤ 1 := by
        refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun ψ => ?_)
        rw [one_mul]
        have h_sq := isStarProjection_norm_sq_apply_le_bhm (h_res.2.1 σ) ψ
        exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg ψ) (by linarith [sq ‖sys.syndromeProjector σ ψ‖, sq ‖ψ‖])
      calc ‖W_op jumps * sys.syndromeProjector σ‖
        _ ≤ ‖W_op jumps‖ * ‖sys.syndromeProjector σ‖ := norm_mul_le _ _
        _ ≤ ‖W_op jumps‖ * 1 := mul_le_mul_of_nonneg_left hP_le (norm_nonneg _)
        _ = ‖W_op jumps‖ := mul_one _
        _ ≤ (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod :=
            worldlinePolymerWeightedLoopOp_norm_le D_field sys V (jumps, ∅)
    calc |∑ ω : ManyBodyConfig (SiteCSS[L, q_code]),
          Real.exp (-s * opEigenvalues H_trunc hH_trunc ω) *
            RCLike.re (inner ℂ (opEigenbasis H_trunc hH_trunc ω)
              ((W_op jumps * sys.syndromeProjector σ) (opEigenbasis H_trunc hH_trunc ω)))|
      _ ≤ ∑ ω : ManyBodyConfig (SiteCSS[L, q_code]),
          |Real.exp (-s * opEigenvalues H_trunc hH_trunc ω) *
            RCLike.re (inner ℂ (opEigenbasis H_trunc hH_trunc ω)
              ((W_op jumps * sys.syndromeProjector σ) (opEigenbasis H_trunc hH_trunc ω)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ω : ManyBodyConfig (SiteCSS[L, q_code]),
          Real.exp (s * E_max) * (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod := by
          refine Finset.sum_le_sum (fun ω _ => ?_)
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have h_ev : -s * opEigenvalues H_trunc hH_trunc ω ≤ s * E_max := by
            have h1 : |opEigenvalues H_trunc hH_trunc ω| ≤ E_max :=
              le_trans (Finset.single_le_sum (f := fun x => |opEigenvalues H_trunc hH_trunc x|)
                (fun _ _ => abs_nonneg _) (Finset.mem_univ ω)) (le_max_left _ _)
            nlinarith [neg_le_abs (opEigenvalues H_trunc hH_trunc ω)]
          have h_in : |RCLike.re (inner ℂ (opEigenbasis H_trunc hH_trunc ω)
              ((W_op jumps * sys.syndromeProjector σ) (opEigenbasis H_trunc hH_trunc ω)))| ≤
              (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod := by
            have h_norm_sq : ‖opEigenbasis H_trunc hH_trunc ω‖ ^ 2 = 1 := by
              rw [← inner_self_eq_norm_sq (𝕜 := ℂ), opEigenbasis_orthonormal H_trunc hH_trunc ω ω,
                if_pos rfl, RCLike.one_re]
            calc |RCLike.re (inner ℂ (opEigenbasis H_trunc hH_trunc ω)
                  ((W_op jumps * sys.syndromeProjector σ) (opEigenbasis H_trunc hH_trunc ω)))|
              _ ≤ ‖W_op jumps * sys.syndromeProjector σ‖ * ‖opEigenbasis H_trunc hH_trunc ω‖ ^ 2 :=
                  abs_re_inner_le_opNorm_mul_norm_sq _ _
              _ = ‖W_op jumps * sys.syndromeProjector σ‖ := by rw [h_norm_sq, mul_one]
              _ ≤ (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod := h_norm_W
          exact mul_le_mul (Real.exp_le_exp.mpr h_ev) h_in (abs_nonneg _) (Real.exp_pos _).le
      _ = C_tr * (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod *
            Real.exp (s * E_max) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; dsimp [C_tr]; ring
  | succ r ih =>
    intro jumps s hs; change |Rem (r + 1) jumps s| ≤ _
    rw [hRem_succ r jumps s, abs_neg]
    let P_jumps := (jumps.map (fun ξ => ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖)).prod
    have h_term_le : ∀ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
        |∫ u in (0 : ℝ)..s,
          Real.exp (-u * E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ)) *
            Rem r (jumps ++ [ξ]) (s - u)| ≤
        ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖ *
          (C_tr * P_jumps * Real.exp (s * E_max) * (K_sum ^ r * (s ^ (r + 1) / (Nat.factorial (r + 1) : ℝ)))) := by
      intro ξ _
      let C_ξ := ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖ * (C_tr * P_jumps * Real.exp (s * E_max) * K_sum ^ r)
      have h_int_le := abs_intervalIntegral_le_of_abs_le_local hs
        (fun u => Real.exp (-u * E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ)) *
          Rem r (jumps ++ [ξ]) (s - u))
        (fun u => ((s - u) ^ r / (Nat.factorial r : ℝ)) * C_ξ)
        (Continuous.intervalIntegrable
          ((Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)).mul
            ((hRem_cont r (jumps ++ [ξ])).comp (continuous_const.sub continuous_id))) 0 s)
        ((((continuous_const.sub continuous_id).pow r).div_const _).mul continuous_const |>.intervalIntegrable 0 s)
        (fun u hu => by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have h_exp_u : -u * E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ) ≤ u * E_max := by
            have := hE_full_le (syndromeXor (worldlineJumpListFlip D_field jumps) σ)
            nlinarith [hu.1, neg_le_abs (E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ))]
          have h_rem_u := ih (jumps ++ [ξ]) (sub_nonneg.mpr hu.2)
          have h_prod_append :
              ((jumps ++ [ξ]).map (fun ζ => ‖worldlineSyndromeShiftBlockOp D_field sys V ζ‖)).prod =
                P_jumps * ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖ := by
            rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
          rw [h_prod_append] at h_rem_u
          have h_mul := mul_le_mul (Real.exp_le_exp.mpr h_exp_u) h_rem_u (abs_nonneg _) (Real.exp_pos _).le
          calc Real.exp (-u * E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ)) *
                |Rem r (jumps ++ [ξ]) (s - u)|
            _ ≤ Real.exp (u * E_max) *
                  (C_tr * (P_jumps * ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖) *
                    Real.exp ((s - u) * E_max) * ((K_sum * (s - u)) ^ r / (Nat.factorial r : ℝ))) := h_mul
            _ = (Real.exp (u * E_max) * Real.exp ((s - u) * E_max)) *
                  (((s - u) ^ r / (Nat.factorial r : ℝ)) *
                    (‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖ * (C_tr * P_jumps * K_sum ^ r))) := by
                  rw [mul_pow]; ring
            _ = ((s - u) ^ r / (Nat.factorial r : ℝ)) * C_ξ := by
                  rw [← Real.exp_add, show u * E_max + (s - u) * E_max = s * E_max by ring]
                  dsimp [C_ξ]; ring)
      rw [intervalIntegral_pow_div_factorial_mul_const_local r s C_ξ] at h_int_le
      refine le_trans h_int_le (le_of_eq ?_); dsimp [C_ξ]; ring
    calc |∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          ∫ u in (0 : ℝ)..s,
            Real.exp (-u * E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ)) *
              Rem r (jumps ++ [ξ]) (s - u)|
      _ ≤ ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          |∫ u in (0 : ℝ)..s,
            Real.exp (-u * E_full (syndromeXor (worldlineJumpListFlip D_field jumps) σ)) *
              Rem r (jumps ++ [ξ]) (s - u)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
          ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖ *
            (C_tr * P_jumps * Real.exp (s * E_max) * (K_sum ^ r * (s ^ (r + 1) / (Nat.factorial (r + 1) : ℝ)))) :=
          Finset.sum_le_sum h_term_le
      _ = C_tr * P_jumps * Real.exp (s * E_max) * ((K_sum * s) ^ (r + 1) / (Nat.factorial (r + 1) : ℝ)) := by
          rw [← Finset.sum_mul]
          change K_sum * (C_tr * P_jumps * Real.exp (s * E_max) *
            (K_sum ^ r * (s ^ (r + 1) / (Nat.factorial (r + 1) : ℝ)))) = _
          rw [mul_pow, pow_succ']; ring

private lemma integral_shift_piFin_of_support
    {u s B : ℝ} (hu : u ∈ Set.Icc 0 s) (hB : 0 ≤ B) :
    ∀ (k : ℕ) (G : (Fin k → ℝ) → ℝ),
      Measurable G → (∀ τ, |G τ| ≤ B) →
      (∀ τ : Fin k → ℝ, (¬ ∀ i : Fin k, u ≤ τ i ∧ τ i ≤ s) → G τ = 0) →
      (∫ τ : Fin k → ℝ, G (fun i => τ i + u)) = ∫ τ : Fin k → ℝ, G τ
  | 0, G, _, _, _ => by
    have h_eq : ∀ τ : Fin 0 → ℝ, (fun i : Fin 0 => τ i + u) = τ :=
      fun τ => funext (fun i => Fin.elim0 i)
    simp_rw [h_eq]
  | m + 1, G, hG_meas, hG_bd, hG_supp => by
    have h_fub : ∀ (H : (Fin (m + 1) → ℝ) → ℝ), MeasureTheory.Integrable H →
        (∫ τ : Fin (m + 1) → ℝ, H τ) = ∫ x : ℝ, ∫ τ' : Fin m → ℝ, H (Fin.cons x τ') := by
      intro H hH_int
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
      have h_mp := (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
      have hH_prod : MeasureTheory.Integrable (fun p : ℝ × (Fin m → ℝ) => H (e.symm p)) :=
        (h_mp.integrable_comp_emb e.symm.measurableEmbedding).mpr hH_int
      rw [← h_mp.integral_comp' H]
      change (∫ p : ℝ × (Fin m → ℝ), H (e.symm p) ∂(MeasureTheory.volume.prod MeasureTheory.volume)) = _
      rw [MeasureTheory.integral_prod _ hH_prod]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun τ' => ?_))
      change H (Fin.insertNth 0 x τ') = H (Fin.cons x τ'); rw [Fin.insertNth_zero]; rfl
    have hG_int : MeasureTheory.Integrable G :=
      integrable_of_measurable_bounded_support_piFin hG_meas hB hG_bd hG_supp
    have hG_sh_meas : Measurable (fun τ : Fin (m + 1) → ℝ => G (fun i => τ i + u)) :=
      hG_meas.comp (measurable_pi_iff.mpr (fun i => (measurable_pi_apply i).add measurable_const))
    have hG_sh_supp : ∀ τ : Fin (m + 1) → ℝ,
        (¬ ∀ i : Fin (m + 1), 0 ≤ τ i ∧ τ i ≤ s - u) → G (fun i => τ i + u) = 0 :=
      fun τ h_not => hG_supp _ (fun h_all => h_not (fun i =>
        ⟨by linarith [(h_all i).1], by linarith [(h_all i).2]⟩))
    have hG_sh_int : MeasureTheory.Integrable (fun τ : Fin (m + 1) → ℝ => G (fun i => τ i + u)) :=
      integrable_of_measurable_bounded_support_piFin hG_sh_meas hB (fun _ => hG_bd _) hG_sh_supp
    rw [h_fub _ hG_sh_int, h_fub G hG_int]
    let g (x : ℝ) : ℝ := ∫ τ' : Fin m → ℝ, G (Fin.cons x τ')
    have h_inner : ∀ x : ℝ,
        (∫ τ' : Fin m → ℝ, G (fun i => (Fin.cons x τ' : Fin (m + 1) → ℝ) i + u)) = g (x + u) := by
      intro x
      have h_cons_add : ∀ τ' : Fin m → ℝ,
          (fun i : Fin (m + 1) => (Fin.cons x τ' : Fin (m + 1) → ℝ) i + u) =
            Fin.cons (x + u) (fun j => τ' j + u) := by
        intro τ'; ext i; refine Fin.cases rfl (fun _ => rfl) i
      simp_rw [h_cons_add]
      have hx_meas : Measurable (fun τ' : Fin m → ℝ => G (Fin.cons (x + u) τ')) :=
        hG_meas.comp (measurable_pi_iff.mpr (fun j =>
          Fin.cases measurable_const (fun i => measurable_pi_apply i) j))
      have hx_supp : ∀ τ' : Fin m → ℝ,
          (¬ ∀ i : Fin m, u ≤ τ' i ∧ τ' i ≤ s) → G (Fin.cons (x + u) τ') = 0 :=
        fun τ' h_not => hG_supp _ (fun h_all => h_not (fun i => h_all i.succ))
      exact integral_shift_piFin_of_support hu hB m
        (fun τ' => G (Fin.cons (x + u) τ')) hx_meas (fun _ => hG_bd _) hx_supp
    simp_rw [h_inner]
    have hg_supp : ∀ x ∉ Set.Icc u s, g x = 0 := by
      intro x hx; dsimp [g]
      have h_zero : (fun τ' : Fin m → ℝ => G (Fin.cons x τ')) = fun _ => 0 :=
        funext (fun _ => hG_supp _ (fun h_all => hx (h_all 0)))
      rw [h_zero, MeasureTheory.integral_zero]
    have hg_sh_supp : ∀ x ∉ Set.Icc 0 (s - u), g (x + u) = 0 :=
      fun x hx => hg_supp (x + u) (fun h_in => hx ⟨by linarith [h_in.1], by linarith [h_in.2]⟩)
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg_sh_supp,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (sub_nonneg.mpr hu.2),
      intervalIntegral.integral_comp_add_right g u, zero_add, sub_add_cancel,
      intervalIntegral.integral_of_le hu.2,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hg_supp]

private lemma measurable_and_bounded_inOrderedDysonSimplex_exp_trajectory
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (E_full : (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) (s : ℝ) :
    let F := fun τ : Fin ξ_list.length → ℝ =>
      if InOrderedDysonSimplex s τ then
        Real.exp (-(∫ t in Set.Icc 0 s, E_full (worldlineTrajectorySyndrome D_field ξ_list σ₀ τ t)))
      else 0
    Measurable F ∧ (∃ B : ℝ, 0 ≤ B ∧ ∀ τ, |F τ| ≤ B) ∧ MeasureTheory.Integrable F := by
  intro F
  obtain ⟨h_meas_int, B0, _, hB0⟩ :=
    measurable_and_bounded_integral_worldlineTrajectorySyndrome D_field ξ_list σ₀ s E_full
  have hF_meas : Measurable F :=
    Measurable.ite (measurableSet_inOrderedDysonSimplex _ s) h_meas_int.neg.exp measurable_const
  have hF_bd : ∀ τ, |F τ| ≤ Real.exp B0 := fun τ => by
    dsimp [F]; split_ifs with hτ
    · rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr ((neg_le_abs _).trans (hB0 τ))
    · rw [abs_zero]; exact (Real.exp_pos B0).le
  exact ⟨hF_meas, ⟨Real.exp B0, (Real.exp_pos B0).le, hF_bd⟩,
    integrable_of_measurable_bounded_support_piFin hF_meas (Real.exp_pos B0).le hF_bd
      (fun _ h_not => if_neg (fun h_in => h_not h_in.1))⟩

private lemma worldlineTrajectorySyndrome_cons_shift_lt_and_ge
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (ξ : WorldlineJumpMonomer L q_code) (tl : List (WorldlineJumpMonomer L q_code))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) (u : ℝ) (τ_tail : Fin tl.length → ℝ) :
    (∀ t : ℝ, t < u → (∀ i : Fin tl.length, 0 ≤ τ_tail i) →
      worldlineTrajectorySyndrome D_field (ξ :: tl) σ₀
        (Fin.cons u (fun i => τ_tail i + u)) t = σ₀) ∧
    (∀ t : ℝ, u ≤ t →
      worldlineTrajectorySyndrome D_field (ξ :: tl) σ₀
        (Fin.cons u (fun i => τ_tail i + u)) t =
      worldlineTrajectorySyndrome D_field tl
        (syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀) τ_tail (t - u)) := by
  have h_comm : ∀ (l : List (Fin tl.length)) (δ : IdxCSS[L, q_code, m_max] → Bool),
      syndromeXor δ (l.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (tl.get j).2.1 (tl.get j).2.2) acc) σ₀) =
      l.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (tl.get j).2.1 (tl.get j).2.2) acc) (syndromeXor δ σ₀) := by
    intro l δ; induction l with
    | nil => rfl
    | cons j rest ih =>
      dsimp only [List.foldr]; rw [← ih]; ext c; dsimp [syndromeXor]
      cases δ c <;> cases staticCSSPauliFlip D_field (tl.get j).2.1 (tl.get j).2.2 c <;>
        cases (rest.foldr (fun i acc =>
          syndromeXor (staticCSSPauliFlip D_field (tl.get i).2.1 (tl.get i).2.2) acc) σ₀ c) <;> rfl
  let τ_shift : Fin (tl.length + 1) → ℝ := Fin.cons u (fun i => τ_tail i + u)
  have h_map_succ : ∀ (l : List (Fin tl.length)) (t : ℝ),
      ((l.map Fin.succ).filter (fun j : Fin (tl.length + 1) => decide (τ_shift j ≤ t))).foldr
        (fun j acc => syndromeXor (staticCSSPauliFlip D_field ((ξ :: tl).get j).2.1 ((ξ :: tl).get j).2.2) acc) σ₀ =
      (l.filter (fun i : Fin tl.length => decide (τ_tail i ≤ t - u))).foldr
        (fun i acc => syndromeXor (staticCSSPauliFlip D_field (tl.get i).2.1 (tl.get i).2.2) acc) σ₀ := by
    intro l t; induction l with
    | nil => rfl
    | cons i rest ih =>
      have h_dec : decide (τ_shift i.succ ≤ t) = decide (τ_tail i ≤ t - u) := by
        dsimp [τ_shift]; exact decide_eq_decide.mpr le_sub_iff_add_le.symm
      rw [List.map_cons, List.filter_cons, List.filter_cons, h_dec]
      split_ifs with h_b
      · rw [List.foldr_cons, List.foldr_cons, ih]; rfl
      · exact ih
  refine ⟨fun t ht h_nn => ?_, fun t ht => ?_⟩
  · unfold worldlineTrajectorySyndrome
    change (((List.finRange (tl.length + 1)).filter
        (fun j : Fin (tl.length + 1) => decide (τ_shift j ≤ t))).foldr
        (fun j acc => syndromeXor (staticCSSPauliFlip D_field ((ξ :: tl).get j).2.1 ((ξ :: tl).get j).2.2) acc) σ₀) = σ₀
    have h0_neg : decide (τ_shift 0 ≤ t) = false := by
      dsimp [τ_shift]; exact decide_eq_false (not_le.mpr ht)
    rw [List.finRange_succ, List.filter_cons, if_neg (by simp [h0_neg]), h_map_succ]
    have h_nil : (List.finRange tl.length).filter (fun i : Fin tl.length => decide (τ_tail i ≤ t - u)) = [] := by
      rw [List.filter_eq_nil_iff]; intro i _; rw [decide_eq_true_eq]; linarith [h_nn i]
    rw [h_nil]; rfl
  · unfold worldlineTrajectorySyndrome
    change (((List.finRange (tl.length + 1)).filter
        (fun j : Fin (tl.length + 1) => decide (τ_shift j ≤ t))).foldr
        (fun j acc => syndromeXor (staticCSSPauliFlip D_field ((ξ :: tl).get j).2.1 ((ξ :: tl).get j).2.2) acc) σ₀) = _
    have h0_pos : decide (τ_shift 0 ≤ t) = true := by
      dsimp [τ_shift]; exact decide_eq_true ht
    rw [List.finRange_succ, List.filter_cons, if_pos h0_pos,
      List.foldr_cons, List.get_cons_zero, h_map_succ, h_comm]

private lemma inOrderedDysonSimplex_cons_shift_iff_of_ne_zero
    {m : ℕ} {s u : ℝ} (hu : u ∈ Set.Icc 0 s)
    {τ_tail : Fin m → ℝ} (h_ne : ∀ i : Fin m, τ_tail i ≠ 0) :
    InOrderedDysonSimplex s (Fin.cons u (fun i => τ_tail i + u)) ↔
      InOrderedDysonSimplex (s - u) τ_tail := by
  constructor
  · rintro ⟨h_bd, h_mono⟩
    refine ⟨fun j => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · have h_lt := h_mono (Fin.succ_pos j); simp only [Fin.cons_zero, Fin.cons_succ] at h_lt; linarith
    · have h_le := (h_bd j.succ).2; simp only [Fin.cons_succ] at h_le; linarith
    · have h_lt := h_mono (Fin.succ_lt_succ_iff.mpr hij); simp only [Fin.cons_succ] at h_lt; linarith
  · rintro ⟨h_bd, h_mono⟩
    refine ⟨fun k => ?_, fun a b hab => ?_⟩
    · refine Fin.cases ⟨hu.1, hu.2⟩ (fun j => ?_) k
      simp only [Fin.cons_succ]; exact ⟨by linarith [hu.1, (h_bd j).1], by linarith [(h_bd j).2]⟩
    · revert hab; refine Fin.cases ?_ (fun i => ?_) a
      · refine Fin.cases (fun h => False.elim (lt_irrefl _ h)) (fun j _ => ?_) b
        simp only [Fin.cons_zero, Fin.cons_succ]
        linarith [lt_of_le_of_ne (h_bd j).1 (h_ne j).symm]
      · refine Fin.cases (fun h => False.elim (not_lt_of_gt (Fin.succ_pos i) h)) (fun j hij => ?_) b
        simp only [Fin.cons_succ]; linarith [h_mono (Fin.succ_lt_succ_iff.mp hij)]

/-- **Ordered Dyson Simplex Integral Identity**:
For every jump monomer list `ξ_list`, starting syndrome `σ₀`, and `0 ≤ s`, the recursively defined
1D iterated Duhamel integral `worldlineIteratedDuhamelIntegral D_field E_full ξ_list σ₀ s` equals
the integral over the ordered Dyson simplex `inOrderedDysonSimplex s τ` of the trajectory action
exponential `Real.exp (-(∫ t in Set.Icc 0 s, E_full (worldlineTrajectorySyndrome D_field ξ_list σ₀ τ t)))`. -/
private lemma worldlineIteratedDuhamelIntegral_eq_simplex_integral
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (E_full : (IdxCSS[L, q_code, m_max] → Bool) → ℝ) :
    ∀ (ξ_list : List (WorldlineJumpMonomer L q_code))
      (σ₀ : IdxCSS[L, q_code, m_max] → Bool) {s : ℝ} (hs : 0 ≤ s),
      worldlineIteratedDuhamelIntegral D_field E_full ξ_list σ₀ s =
        ∫ τ : Fin ξ_list.length → ℝ,
          if InOrderedDysonSimplex s τ then
            Real.exp (-(∫ t in Set.Icc 0 s,
              E_full (worldlineTrajectorySyndrome D_field ξ_list σ₀ τ t)))
          else 0
  | [], σ₀, s, hs => by
    dsimp [worldlineIteratedDuhamelIntegral]
    have h_simp : ∀ τ : Fin 0 → ℝ, InOrderedDysonSimplex s τ :=
      fun _ => ⟨fun j => Fin.elim0 j, fun i => Fin.elim0 i⟩
    have h_traj : ∀ (τ : Fin 0 → ℝ) (t : ℝ),
        worldlineTrajectorySyndrome D_field [] σ₀ τ t = σ₀ := fun _ _ => rfl
    have h_int_t : (∫ t in Set.Icc 0 s, E_full σ₀) = s * E_full σ₀ := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
        sub_zero, ENNReal.toReal_ofReal hs, smul_eq_mul]
    have h_univ : (Set.univ : Set (Fin 0 → ℝ)) = Set.pi Set.univ (fun _ : Fin 0 => Set.Icc (0 : ℝ) 1) := by
      ext τ; simp
    simp_rw [if_pos (h_simp _), h_traj, h_int_t]
    rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def, h_univ,
      MeasureTheory.volume_pi_pi, Fin.prod_univ_zero, ENNReal.toReal_one, one_smul, neg_mul]
  | ξ :: tl, σ₀, s, hs => by
    let m := tl.length
    let σ₁ := syndromeXor (staticCSSPauliFlip D_field ξ.2.1 ξ.2.2) σ₀
    let F : (Fin (m + 1) → ℝ) → ℝ := fun τ =>
      if InOrderedDysonSimplex s τ then
        Real.exp (-(∫ t in Set.Icc 0 s,
          E_full (worldlineTrajectorySyndrome D_field (ξ :: tl) σ₀ τ t)))
      else 0
    obtain ⟨hF_meas, ⟨B0, hB0_nn, hF_bd⟩, hF_int⟩ :=
      measurable_and_bounded_inOrderedDysonSimplex_exp_trajectory D_field E_full (ξ :: tl) σ₀ s
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have h_mp := (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
    have hF_prod_int : MeasureTheory.Integrable (fun p : ℝ × (Fin m → ℝ) => F (e.symm p)) :=
      (h_mp.integrable_comp_emb e.symm.measurableEmbedding).mpr hF_int
    have h_fub : (∫ τ : Fin (m + 1) → ℝ, F τ) =
        ∫ u : ℝ, ∫ τ' : Fin m → ℝ, F (Fin.cons u τ') := by
      rw [← h_mp.integral_comp' F]
      change (∫ p : ℝ × (Fin m → ℝ), F (e.symm p) ∂(MeasureTheory.volume.prod MeasureTheory.volume)) = _
      rw [MeasureTheory.integral_prod _ hF_prod_int]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun τ' => ?_))
      change F (Fin.insertNth 0 u τ') = F (Fin.cons u τ'); rw [Fin.insertNth_zero]; rfl
    have h_supp_u : ∀ u ∉ Set.Icc 0 s, (∫ τ' : Fin m → ℝ, F (Fin.cons u τ')) = 0 := by
      intro u hu
      have h_zero : (fun τ' : Fin m → ℝ => F (Fin.cons u τ')) = fun _ => 0 := by
        ext τ'; dsimp [F]; rw [if_neg]
        intro h_in; have h0 := h_in.1 0; simp only [Fin.cons_zero] at h0; exact hu h0
      rw [h_zero, MeasureTheory.integral_zero]
    have h_ae_ne_zero : ∀ᵐ (τ_tail : Fin m → ℝ), ∀ i : Fin m, τ_tail i ≠ 0 := by
      rw [Filter.eventually_all]; intro i; rw [MeasureTheory.ae_iff]
      let S_i : Set (Fin m → ℝ) := Set.pi Set.univ (fun j : Fin m => if j = i then {(0 : ℝ)} else Set.univ)
      have h_sub_i : {τ_tail : Fin m → ℝ | ¬ τ_tail i ≠ 0} ⊆ S_i := by
        intro τ_tail hτ j _; (try dsimp at hτ); push_neg at hτ
        by_cases hji : j = i <;> simp [hji, hτ]
      have h_vol_i : MeasureTheory.volume S_i = 0 := by
        dsimp [S_i]; rw [MeasureTheory.volume_pi_pi]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
      exact MeasureTheory.measure_mono_null h_sub_i h_vol_i
    have h_inner_u : ∀ u ∈ Set.Icc 0 s,
        (∫ τ' : Fin m → ℝ, F (Fin.cons u τ')) =
          Real.exp (-u * E_full σ₀) *
            worldlineIteratedDuhamelIntegral D_field E_full tl σ₁ (s - u) := by
      intro u hu
      have h_shift_u : (∫ τ' : Fin m → ℝ, F (Fin.cons u τ')) =
          ∫ τ_tail : Fin m → ℝ, F (Fin.cons u (fun i => τ_tail i + u)) := by
        symm
        refine integral_shift_piFin_of_support hu hB0_nn m (fun τ' => F (Fin.cons u τ'))
          (hF_meas.comp (measurable_pi_iff.mpr (fun j =>
            Fin.cases measurable_const (fun i => measurable_pi_apply i) j)))
          (fun _ => hF_bd _) (fun τ' h_not => ?_)
        dsimp [F]; rw [if_neg]; intro h_in; apply h_not; intro i
        exact ⟨le_of_lt (by simpa using h_in.2 (Fin.succ_pos i)), (h_in.1 i.succ).2⟩
      rw [h_shift_u]
      have h_ae_eq : (fun τ_tail : Fin m → ℝ => F (Fin.cons u (fun i => τ_tail i + u))) =ᵐ[MeasureTheory.volume]
          fun τ_tail : Fin m → ℝ =>
            Real.exp (-u * E_full σ₀) *
              if InOrderedDysonSimplex (s - u) τ_tail then
                Real.exp (-(∫ t' in Set.Icc 0 (s - u),
                  E_full (worldlineTrajectorySyndrome D_field tl σ₁ τ_tail t')))
              else 0 := by
        filter_upwards [h_ae_ne_zero] with τ_tail h_ne
        dsimp [F]
        rw [inOrderedDysonSimplex_cons_shift_iff_of_ne_zero hu h_ne]
        by_cases h_simp : InOrderedDysonSimplex (s - u) τ_tail
        · rw [if_pos h_simp, if_pos h_simp]
          obtain ⟨h_lt, h_ge⟩ :=
            worldlineTrajectorySyndrome_cons_shift_lt_and_ge D_field ξ tl σ₀ u τ_tail
          let f_traj (t : ℝ) : ℝ :=
            E_full (worldlineTrajectorySyndrome D_field (ξ :: tl) σ₀
              (Fin.cons u (fun i => τ_tail i + u)) t)
          have hf_int : ∀ a b : ℝ, IntervalIntegrable f_traj MeasureTheory.volume a b := by
            intro a b; rw [intervalIntegrable_iff]
            have h_meas : Measurable f_traj :=
              (measurable_foldr_syndromeXor_filter D_field (ξ :: tl) σ₀
                (List.finRange (ξ :: tl).length) E_full).comp (measurable_const.prodMk measurable_id)
            refine (MeasureTheory.integrableOn_const
              (C := ∑ η : IdxCSS[L, q_code, m_max] → Bool, |E_full η|)
              (hs := ((MeasureTheory.measure_mono Set.uIoc_subset_uIcc).trans_lt
                isCompact_uIcc.measure_lt_top).ne)).mono' h_meas.aestronglyMeasurable ?_
            exact Filter.Eventually.of_forall (fun t =>
              Finset.single_le_sum (f := fun η => |E_full η|) (fun η _ => abs_nonneg _) (Finset.mem_univ _))
          have h_split_t : (∫ t in Set.Icc 0 s, f_traj t) =
              u * E_full σ₀ +
                ∫ t' in Set.Icc 0 (s - u),
                  E_full (worldlineTrajectorySyndrome D_field tl σ₁ τ_tail t') := by
            rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs,
              ← intervalIntegral.integral_add_adjacent_intervals (hf_int 0 u) (hf_int u s)]
            have h_left : (∫ t in (0 : ℝ)..u, f_traj t) = u * E_full σ₀ := by
              rw [intervalIntegral.integral_of_le hu.1, MeasureTheory.integral_Ioc_eq_integral_Ioo]
              have h_congr : Set.EqOn f_traj (fun _ => E_full σ₀) (Set.Ioo 0 u) :=
                fun t ht => congrArg E_full (h_lt t ht.2 (fun i => (h_simp.1 i).1))
              rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h_congr,
                MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Ioo,
                sub_zero, ENNReal.toReal_ofReal hu.1, smul_eq_mul]
            have h_right : (∫ t in u..s, f_traj t) =
                ∫ t' in Set.Icc 0 (s - u),
                  E_full (worldlineTrajectorySyndrome D_field tl σ₁ τ_tail t') := by
              have h_shift := intervalIntegral.integral_comp_add_right f_traj u (a := 0) (b := s - u)
              rw [zero_add, sub_add_cancel] at h_shift
              rw [← h_shift, intervalIntegral.integral_of_le (sub_nonneg.mpr hu.2),
                ← MeasureTheory.integral_Icc_eq_integral_Ioc]
              refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun t' ht' => ?_)
              dsimp [f_traj]; rw [h_ge (t' + u) (by linarith [ht'.1]), add_sub_cancel_right]
            rw [h_left, h_right]
          change Real.exp (-(∫ t in Set.Icc 0 s, f_traj t)) = _
          rw [h_split_t, neg_add, Real.exp_add, neg_mul]
        · rw [if_neg h_simp, if_neg h_simp, mul_zero]
      rw [MeasureTheory.integral_congr_ae h_ae_eq, MeasureTheory.integral_const_mul,
        ← worldlineIteratedDuhamelIntegral_eq_simplex_integral D_field E_full tl σ₁
          (sub_nonneg.mpr hu.2)]
    dsimp [worldlineIteratedDuhamelIntegral]
    change (∫ u in (0 : ℝ)..s,
        Real.exp (-u * E_full σ₀) *
          worldlineIteratedDuhamelIntegral D_field E_full tl σ₁ (s - u)) =
      ∫ τ : Fin (m + 1) → ℝ, F τ
    rw [h_fub, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h_supp_u,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    refine (intervalIntegral.integral_congr (fun u hu => ?_)).symm
    rw [Set.uIcc_of_le hs] at hu; exact h_inner_u u hu

/-- **Per-Sector Duhamel–Dyson Jump Series Expansion**
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)):
Expanding $\operatorname{Tr}(\mathrm{e}^{-\beta(H_0 + H_{\mathrm{short}}(R_{\mathrm{cut}}))}\Pi_\sigma)$
in a Duhamel–Dyson series with respect to $H_{\mathrm{diag}}^{\le R_{\mathrm{cut}}} = H_0 + D_{\mathrm{diag}}^{\le R_{\mathrm{cut}}}$
and off-diagonal remainder $R_{\mathrm{off}}^{\le R_{\mathrm{cut}}}$ yields the absolutely convergent
sum of `singleSectorWorldlineDysonJumpWeight` over all jump monomer sequences $\xi$. -/
lemma hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_tsum_singleSectorJumpWeight
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
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ_pos : 0 < J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
    Summable (singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ) ∧
    hilbertTrace (gibbsBoltzmannOp
      (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
      (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
        sys.syndromeProjector σ) =
      K_norm *
        (Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
          ∑' ξ_list : List (WorldlineJumpMonomer L q_code),
            singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list) := by
  intro E_vac K_norm
  have hβ_nn : 0 ≤ β := by linarith
  obtain ⟨h_summable, h_sum_by_len, h_tsum_eq⟩ :=
    summable_and_tsum_singleSectorWorldlineDysonJumpWeight hβ_nn D_field sys V d_loc σ
  refine ⟨h_summable, ?_⟩
  let H_trunc := sys.H0 + scaleSplitTruncatedOp V R_cut
  let B_trunc := gibbsBoltzmannOp (opEigenbasis H_trunc hH_trunc) (opEigenvalues H_trunc hH_trunc)
  let E_full (η : IdxCSS[L, q_code, m_max] → Bool) : ℝ :=
    E_vac + pauliDiagonalSectorEnergy sys R_cut d_loc η
  let W_op (l : List (WorldlineJumpMonomer L q_code)) :=
    worldlinePolymerWeightedLoopOp D_field sys V (l, ∅)
  have h_iter_eq : ∀ ξ_list : List (WorldlineJumpMonomer L q_code),
      worldlineIteratedDuhamelIntegral D_field E_full ξ_list σ β =
        Real.exp (-β * E_vac) * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
          ∫ τ : Fin ξ_list.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
                ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut,
                  (1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ)
            else 0 := by
    intro ξ_list
    rw [worldlineIteratedDuhamelIntegral_eq_simplex_integral D_field E_full ξ_list σ hβ_nn,
      ← MeasureTheory.integral_const_mul]
    congr 1; funext τ; split_ifs with h_simp
    · let f_traj (t : ℝ) := worldlineTrajectorySyndrome D_field ξ_list σ τ t
      have h_int_G : ∀ G : (IdxCSS[L, q_code, m_max] → Bool) → ℝ,
          MeasureTheory.Integrable (fun t : ℝ => G (f_traj t))
            (MeasureTheory.volume.restrict (Set.Icc 0 β)) := by
        intro G
        have h_meas : Measurable (fun t : ℝ => G (f_traj t)) :=
          (measurable_foldr_syndromeXor_filter D_field ξ_list σ
            (List.finRange ξ_list.length) G).comp (measurable_const.prodMk measurable_id)
        refine (MeasureTheory.integrableOn_const
          (C := ∑ η : IdxCSS[L, q_code, m_max] → Bool, |G η|)
          (hs := isCompact_Icc.measure_lt_top.ne)).mono' h_meas.aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall (fun t =>
          Finset.single_le_sum (f := fun η => |G η|) (fun η _ => abs_nonneg _) (Finset.mem_univ _))
      have h_E_decomp : ∀ η : IdxCSS[L, q_code, m_max] → Bool,
          E_full η = E_full σ + ((sys.syndromeEnergy η - sys.syndromeEnergy σ) +
            ∑ ϑ ∈ worldlineScaleCubeFinset L R_cut, (d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ)) := by
        intro η; dsimp [E_full, pauliDiagonalSectorEnergy]
        rw [← sum_scaleCubeFinset_eq_nested_sum (fun p : ℕ × Finset (Box3D L) => d_loc p.1 p.2 η),
          ← sum_scaleCubeFinset_eq_nested_sum (fun p : ℕ × Finset (Box3D L) => d_loc p.1 p.2 σ),
          Finset.sum_sub_distrib]; ring
      have h_c_int := h_int_G (fun _ => E_full σ)
      have h_b_int := h_int_G (fun η => sys.syndromeEnergy η - sys.syndromeEnergy σ)
      have h_d_int : ∀ ϑ ∈ worldlineScaleCubeFinset L R_cut,
          MeasureTheory.Integrable (fun t : ℝ => d_loc ϑ.1 ϑ.2 (f_traj t) - d_loc ϑ.1 ϑ.2 σ)
            (MeasureTheory.volume.restrict (Set.Icc 0 β)) :=
        fun ϑ _ => h_int_G (fun η => d_loc ϑ.1 ϑ.2 η - d_loc ϑ.1 ϑ.2 σ)
      have h_sum_int : MeasureTheory.Integrable
          (fun t : ℝ => ∑ ϑ ∈ worldlineScaleCubeFinset L R_cut,
            (d_loc ϑ.1 ϑ.2 (f_traj t) - d_loc ϑ.1 ϑ.2 σ))
          (MeasureTheory.volume.restrict (Set.Icc 0 β)) :=
        MeasureTheory.integrable_finset_sum (worldlineScaleCubeFinset L R_cut) h_d_int
      have h_bs_int : MeasureTheory.Integrable
          (fun t : ℝ => (sys.syndromeEnergy (f_traj t) - sys.syndromeEnergy σ) +
            ∑ ϑ ∈ worldlineScaleCubeFinset L R_cut,
              (d_loc ϑ.1 ϑ.2 (f_traj t) - d_loc ϑ.1 ϑ.2 σ))
          (MeasureTheory.volume.restrict (Set.Icc 0 β)) := h_b_int.add h_sum_int
      have h_int_split :
          (∫ t in Set.Icc 0 β, E_full (f_traj t)) =
            β * E_full σ + (worldlineBareAction D_field sys ξ_list σ β τ +
              ∑ ϑ ∈ worldlineScaleCubeFinset L R_cut,
                ∫ t in Set.Icc 0 β, (d_loc ϑ.1 ϑ.2 (f_traj t) - d_loc ϑ.1 ϑ.2 σ)) := by
        simp_rw [h_E_decomp (f_traj _)]
        rw [MeasureTheory.integral_add h_c_int h_bs_int,
          MeasureTheory.integral_add h_b_int h_sum_int,
          MeasureTheory.integral_finset_sum (worldlineScaleCubeFinset L R_cut) h_d_int,
          MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
          sub_zero, ENNReal.toReal_ofReal hβ_nn, smul_eq_mul]; rfl
      have h_mayer_prod :
          (∏ ϑ ∈ worldlineScaleCubeFinset L R_cut,
            (1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ)) =
          Real.exp (-(∑ ϑ ∈ worldlineScaleCubeFinset L R_cut,
            ∫ t in Set.Icc 0 β, (d_loc ϑ.1 ϑ.2 (f_traj t) - d_loc ϑ.1 ϑ.2 σ))) := by
        have h1 : ∀ ϑ : ℕ × Finset (Box3D L),
            1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ =
              Real.exp (-(∫ t in Set.Icc 0 β, (d_loc ϑ.1 ϑ.2 (f_traj t) - d_loc ϑ.1 ϑ.2 σ))) := by
          intro ϑ; dsimp [worldlineMayerBondFactor, f_traj]; ring
        simp_rw [h1]; rw [← Real.exp_sum, ← Finset.sum_neg_distrib]
      change Real.exp (-(∫ t in Set.Icc 0 β, E_full (f_traj t))) = _
      rw [h_int_split, h_mayer_prod]; dsimp [E_full]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    · exact (mul_zero _).symm
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  obtain ⟨h_tr_eq, h_tr_pos⟩ :=
    hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes D_field h_valid sys h_sys_checks hσ
  have h_tr_ne : hilbertTrace (sys.syndromeProjector σ) ≠ 0 := ne_of_gt h_tr_pos
  have h_term_eq : ∀ (j : ℕ) (ξ_list : List (WorldlineJumpMonomer L q_code)),
      ξ_list ∈ worldlineJumpListFinsetOfLength D_field R_cut j →
      ((-1 : ℝ) ^ j) * hilbertTrace (sys.syndromeProjector σ * W_op ξ_list) *
        worldlineIteratedDuhamelIntegral D_field E_full ξ_list σ β =
      K_norm * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
        singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list := by
    intro j ξ_list hξ_in
    obtain ⟨hlen, hmem⟩ := (mem_worldlineJumpListFinsetOfLength_iff_local D_field R_cut j ξ_list).mp hξ_in
    subst hlen; dsimp [singleSectorWorldlineDysonJumpWeight]
    by_cases h_nil : ξ_list = []
    · subst h_nil; rw [if_pos rfl]
      dsimp [W_op, worldlinePolymerWeightedLoopOp, worldlineIteratedDuhamelIntegral, K_norm, E_full]
      rw [pow_zero, one_mul, List.map_nil, List.prod_nil, mul_one, mul_one, h_tr_eq, mul_assoc, ← Real.exp_add]; ring_nf
    · rw [if_neg h_nil]; split_ifs with h_cond
      · rw [h_iter_eq ξ_list]; dsimp [K_norm, W_op]; rw [← h_tr_eq]; field_simp [h_tr_ne]
      · rw [mul_zero]
        suffices h_tr_zero : hilbertTrace (sys.syndromeProjector σ * W_op ξ_list) = 0 by
          rw [h_tr_zero, mul_zero, zero_mul]
        by_contra h_tr_W_ne
        let η_end := syndromeXor (worldlineJumpListFlip D_field ξ_list) σ
        have h_abs_end : sys.syndromeProjector η_end * (W_op ξ_list * sys.syndromeProjector σ) =
            W_op ξ_list * sys.syndromeProjector σ :=
          list_prod_reverse_worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V ξ_list σ hσ
        have h_flip_zero : worldlineJumpListFlip D_field ξ_list = (fun _ => false) := by
          by_contra h_flip_ne
          have h_η_ne : σ ≠ η_end := by
            intro h_eq_η; apply h_flip_ne; ext c
            have hc := congrFun h_eq_η c; dsimp [η_end, syndromeXor] at hc
            cases h_b : worldlineJumpListFlip D_field ξ_list c <;>
              cases h_s : σ c <;> simp [h_b, h_s] at hc ⊢
          have h_orth : sys.syndromeProjector σ * sys.syndromeProjector η_end = 0 :=
            h_res.2.2.1 σ η_end h_η_ne
          have h_zero : hilbertTrace (sys.syndromeProjector σ * W_op ξ_list) = 0 := by
            calc hilbertTrace (sys.syndromeProjector σ * W_op ξ_list)
              _ = hilbertTrace ((sys.syndromeProjector σ * sys.syndromeProjector σ) * W_op ξ_list) := by
                  rw [(h_res.2.1 σ).1]
              _ = hilbertTrace (sys.syndromeProjector σ * (W_op ξ_list * sys.syndromeProjector σ)) := by
                  rw [mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ) _, mul_assoc]
              _ = hilbertTrace ((sys.syndromeProjector σ * sys.syndromeProjector η_end) *
                    (W_op ξ_list * sys.syndromeProjector σ)) := by rw [mul_assoc, h_abs_end]
              _ = 0 := by
                  have h_tr0 := PerturbedThermalBarrier.hilbertTrace_sub (0 : ℬ_CSS[L, q_code]) 0
                  rw [sub_self, sub_self] at h_tr0
                  rw [h_orth, zero_mul, h_tr0]
          exact h_tr_W_ne h_zero
        have h_loop_zero : staticCSSPauliFlip D_field (worldlinePolymerLoopX (ξ_list, ∅))
            (worldlinePolymerLoopZ (ξ_list, ∅)) = (fun _ => false) := by
          rw [← worldlineJumpListFlip_eq_staticCSSPauliFlip_loop D_field (ξ_list, ∅), h_flip_zero]
        have h_len_ge_two : 2 ≤ ξ_list.length := by
          cases ξ_list with
          | nil => exact False.elim (h_nil rfl)
          | cons ξ tl =>
            cases tl with
            | nil =>
              obtain ⟨_, h_ξ_jump⟩ := (mem_worldlineAllJumpMonomerFinset_iff D_field ξ).mp (hmem ξ List.mem_cons_self)
              have h_ξ_ne := (((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field ξ.1.1 ξ.1.2).1 ξ).mp h_ξ_jump).2.2.1
              have h_ξ_zero : staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 = (fun _ => false) := by
                ext c; have hc := congrFun h_flip_zero c
                dsimp [worldlineJumpListFlip, syndromeXor] at hc; simpa using hc
              exact False.elim (h_ξ_ne h_ξ_zero)
            | cons _ _ => simp
        exact h_cond ⟨hmem, h_len_ge_two, h_loop_zero⟩
  have h_rem := abs_duhamelRemainder_le D_field h_valid sys h_sys_checks V e_loc d_loc h_scalar hH_trunc hσ
  (try dsimp only at h_rem)
  let K_sum : ℝ := ∑ ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut,
    ‖worldlineSyndromeShiftBlockOp D_field sys V ξ‖
  let E_max : ℝ := max (∑ ω : ManyBodyConfig (SiteCSS[L, q_code]), |opEigenvalues H_trunc hH_trunc ω|)
    (∑ η : IdxCSS[L, q_code, m_max] → Bool, |E_full η|)
  let C_tr : ℝ := (Fintype.card (ManyBodyConfig (SiteCSS[L, q_code])) : ℝ)
  let c_pref := K_norm * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ)
  let seq_m (j : ℕ) : ℝ := c_pref * ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut j,
    singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ tl
  have h_rem_nil : ∀ r : ℕ,
      |hilbertTrace (B_trunc β * sys.syndromeProjector σ) - ∑ j ∈ Finset.range r, seq_m j| ≤
        (C_tr * 1 * Real.exp (β * E_max)) * ((K_sum * β) ^ r / (Nat.factorial r : ℝ)) := by
    intro r; have hr := h_rem r [] hβ_nn
    have hW_nil : W_op [] * sys.syndromeProjector σ = sys.syndromeProjector σ := one_mul _
    have h_xor_nil : syndromeXor (worldlineJumpListFlip D_field []) σ = σ := by
      ext c; dsimp [worldlineJumpListFlip, syndromeXor]; cases σ c <;> rfl
    have h_sum_eq : (∑ j ∈ Finset.range r, ∑ tl ∈ worldlineJumpListFinsetOfLength D_field R_cut j,
        ((-1 : ℝ) ^ j) * hilbertTrace (sys.syndromeProjector σ * W_op ([] ++ tl)) *
          worldlineIteratedDuhamelIntegral D_field E_full tl
            (syndromeXor (worldlineJumpListFlip D_field []) σ) β) = ∑ j ∈ Finset.range r, seq_m j := by
      refine Finset.sum_congr rfl (fun j _ => ?_); rw [h_xor_nil]; dsimp [seq_m, c_pref]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun tl htl => h_term_eq j tl htl)
    rw [hW_nil, h_sum_eq, List.map_nil, List.prod_nil] at hr; exact hr
  have h_tendsto_rem : Filter.Tendsto (fun r : ℕ => ∑ j ∈ Finset.range r, seq_m j)
      Filter.atTop (𝓝 (hilbertTrace (B_trunc β * sys.syndromeProjector σ))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_zero : Filter.Tendsto
        (fun r : ℕ => (C_tr * 1 * Real.exp (β * E_max)) * ((K_sum * β) ^ r / (Nat.factorial r : ℝ)))
        Filter.atTop (𝓝 0) := by
      simpa using ((Real.summable_pow_div_factorial (K_sum * β)).tendsto_atTop_zero).const_mul
        (C_tr * 1 * Real.exp (β * E_max))
    refine squeeze_zero (fun r => norm_nonneg _) (fun r => ?_) h_zero
    rw [Real.norm_eq_abs, abs_sub_comm]; exact h_rem_nil r
  have h_tendsto_tsum : Filter.Tendsto (fun r : ℕ => ∑ j ∈ Finset.range r, seq_m j) Filter.atTop
      (𝓝 (K_norm * (Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
        ∑' ξ_list : List (WorldlineJumpMonomer L q_code),
          singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list))) := by
    have h_has := (h_sum_by_len.mul_left c_pref).hasSum.tendsto_sum_nat
    have h_eq_lim : (∑' j : ℕ, seq_m j) = K_norm * (Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
        ∑' ξ_list : List (WorldlineJumpMonomer L q_code),
          singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list) := by
      dsimp [seq_m, c_pref]; rw [tsum_mul_left, h_tsum_eq, mul_assoc]
    rwa [h_eq_lim] at h_has
  exact tendsto_nhds_unique h_tendsto_rem h_tendsto_tsum

/-- If a scale-cube index `ϑ` has collar disjoint from the collar of every jump in `ξ_list`,
then its Mayer bond factor vanishes identically. -/
lemma worldlineMayerBondFactor_eq_zero_of_disjoint_collar
    {L q_code r_0 m_max w_0 : ℕ} [NeZero L] {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0) (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA) (R_cut : ℕ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_collar : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ₁ σ₂, restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₁ =
        restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₂ → d_loc r A σ₁ = d_loc r A σ₂)
    (σ : IdxCSS[L, q_code, m_max] → Bool) (ξ_list : List (WorldlineJumpMonomer L q_code))
    (h_mem : ∀ ξ ∈ ξ_list, ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut)
    (ϑ : ℕ × Finset (Box3D L)) (hϑ : ϑ ∈ worldlineScaleCubeFinset L R_cut)
    (h_disj : ∀ ξ ∈ ξ_list,
      Disjoint (rcaCollarChecks sys C_RCA ϑ.1 ϑ.2) (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2))
    (τ : Fin ξ_list.length → ℝ) :
    worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ = 0 := by
  obtain ⟨hϑ_r, hϑ_A⟩ := mem_scaleCubeFinset_iff.mp hϑ
  have h_eq_d : ∀ t : ℝ,
      d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field ξ_list σ τ t) = d_loc ϑ.1 ϑ.2 σ := by
    intro t; apply hd_collar ϑ.1 hϑ_r ϑ.2 hϑ_A; funext c
    simp only [restrictSyndromeToCollar]; split_ifs with hc
    · dsimp [worldlineTrajectorySyndrome]; apply foldr_syndromeXor_eq_of_all_false; intro j _
      have hξ_in : ξ_list.get j ∈ ξ_list := List.get_mem ξ_list j
      obtain ⟨hξ_sc, hξ_jump⟩ :=
        (mem_worldlineAllJumpMonomerFinset_iff D_field (ξ_list.get j)).mp (h_mem _ hξ_in)
      obtain ⟨hξ_r, hξ_A⟩ := mem_scaleCubeFinset_iff.mp hξ_sc
      have h_supp := (((mem_worldlineScaleCubeJumpFinset_iff_and_injOn D_field
        (ξ_list.get j).1.1 (ξ_list.get j).1.2).1 (ξ_list.get j)).mp hξ_jump).2.1
      by_contra h_flip
      have hc_inter : c ∈ cubeIntersectingChecks sys (ξ_list.get j).1.2 :=
        staticCSSPauliFlip_mem_cubeIntersectingChecks D_field sys h_sys_supp (ξ_list.get j).1.2
          (ξ_list.get j).2.1 (ξ_list.get j).2.2 h_supp c (Bool.eq_true_of_not_eq_false h_flip)
      have hc_collar : c ∈ rcaCollarChecks sys C_RCA (ξ_list.get j).1.1 (ξ_list.get j).1.2 :=
        cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le
          (Finset.mem_Icc.mp hξ_r).1 hξ_A hc_inter
      exact Finset.disjoint_left.mp (h_disj (ξ_list.get j) hξ_in) hc hc_collar
    · rfl
  simp [worldlineMayerBondFactor, h_eq_d]

/-- **Mayer Bond Expansion of the Diagonal Interaction Factor**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Equations `eq:H-diag-mayer-split`–`eq:mayer-factor-eta-def`,
and Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)):
For any jump monomer sequence $\xi$, expanding $\prod_{\vartheta}(1 + \eta_\vartheta(\sigma(\cdot); \sigma))
= \sum_{\Theta \subseteq \mathcal{I}_{\le R_{\mathrm{cut}}}} \prod_{\vartheta \in \Theta} \eta_\vartheta(\sigma(\cdot); \sigma)$
and using the vanishing of $\eta_\vartheta(\sigma(\cdot); \sigma)$ whenever $\mathcal{C}(B^+) \cap
\bigcup_{\xi_j \in \xi} \mathcal{C}(A_{\xi_j}^+) = \emptyset$ expresses `singleSectorWorldlineDysonJumpWeight`
as the sum over active Mayer subsets $\Theta$. -/
lemma singleSectorWorldlineDysonJumpWeight_eq_sum_activeMayerSubsets
    {L q_code r_0 m_max w_0 : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (R_cut : ℕ)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_collar : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ₁ σ₂, restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₁ =
        restrictSyndromeToCollar (rcaCollarChecks sys C_RCA r A) σ₂ →
        d_loc r A σ₁ = d_loc r A σ₂)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (ξ_list : List (WorldlineJumpMonomer L q_code))
    (hξ_ne : ξ_list ≠ []) :
    singleSectorWorldlineDysonJumpWeight D_field sys R_cut β V d_loc σ ξ_list =
      if (∀ ξ ∈ ξ_list, ξ ∈ worldlineAllJumpMonomerFinset D_field R_cut) ∧
          2 ≤ ξ_list.length ∧
          staticCSSPauliFlip D_field (worldlinePolymerLoopX (ξ_list, ∅))
            (worldlinePolymerLoopZ (ξ_list, ∅)) = (fun _ => false) then
        ∑ Θ ∈ (worldlineScaleCubeFinset L R_cut).powerset.filter (fun Θ =>
            ∀ ϑ ∈ Θ, ∃ ξ ∈ ξ_list,
              ¬Disjoint (rcaCollarChecks sys C_RCA ϑ.1 ϑ.2)
                (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2)),
          ((-1 : ℝ) ^ ξ_list.length) *
            (hilbertTrace (sys.syndromeProjector σ *
              worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ)) /
              hilbertTrace (sys.syndromeProjector σ)) *
            ∫ τ : Fin ξ_list.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
                  ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ
              else 0
      else 0 := by
  dsimp only [singleSectorWorldlineDysonJumpWeight]
  rw [if_neg hξ_ne]; split_ifs with h_cond
  · rcases h_cond with ⟨h_mem, _, _⟩
    let S_all := (worldlineScaleCubeFinset L R_cut).powerset
    let S_act := S_all.filter (fun Θ => ∀ ϑ ∈ Θ, ∃ ξ ∈ ξ_list,
      ¬Disjoint (rcaCollarChecks sys C_RCA ϑ.1 ϑ.2) (rcaCollarChecks sys C_RCA ξ.1.1 ξ.1.2))
    have h_loop_eq : ∀ Θ : Finset (ℕ × Finset (Box3D L)),
        worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, Θ) =
          worldlinePolymerWeightedLoopOp D_field sys V (ξ_list, ∅) := fun _ => rfl
    simp_rw [h_loop_eq, ← Finset.mul_sum]; congr 1
    have h_integrand : (fun τ : Fin ξ_list.length → ℝ =>
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
            ∏ ϑ ∈ worldlineScaleCubeFinset L R_cut,
              (1 + worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ)
        else 0) =
      fun τ : Fin ξ_list.length → ℝ => ∑ Θ ∈ S_act,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys ξ_list σ β τ) *
            ∏ ϑ ∈ Θ, worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ
        else 0 := by
      ext τ; by_cases hτ : InOrderedDysonSimplex β τ
      · simp only [if_pos hτ, prod_one_add_eq_sum_powerset, Finset.mul_sum]
        symm; apply Finset.sum_subset (Finset.filter_subset _ _)
        intro Θ hΘ_all hΘ_not_act
        rw [Finset.mem_filter] at hΘ_not_act; push_neg at hΘ_not_act
        obtain ⟨ϑ, hϑ_in_Θ, hϑ_disj⟩ := hΘ_not_act hΘ_all
        have h_zero : worldlineMayerBondFactor D_field ξ_list d_loc σ β ϑ τ = 0 :=
          worldlineMayerBondFactor_eq_zero_of_disjoint_collar D_field sys h_sys_supp h_geom hr0_le
            R_cut d_loc hd_collar σ ξ_list h_mem ϑ (Finset.mem_powerset.mp hΘ_all hϑ_in_Θ) hϑ_disj τ
        rw [Finset.prod_eq_zero hϑ_in_Θ h_zero, mul_zero]
      · simp [if_neg hτ]
    rw [h_integrand, MeasureTheory.integral_finset_sum]
    exact fun Θ _ => integrable_inOrderedDysonSimplex_mayerProduct D_field sys β d_loc σ ξ_list Θ
  · rfl

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

lemma sum_worldlinePolymerLogicalCoset_eq_zero_of_all_symplecticPauliSign_eq_one
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1) :
    (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 0 := by
  let a_μ := ((K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum).1
  let b_μ := ((K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum).2
  have h_mu_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (a_μ, b_μ) = 1 := by
    intro ν hν; change symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 1
    rw [symplecticPauliSign_list_sum_worldlinePolymerLogicalCoset_eq_loop D_field h_valid sys h_sys_checks K hK_valid hν]
    exact h_comm ν hν
  rcases exists_global_spanning_surface_of_commute_syndromeClosed D_field sys h_sys_checks h_mu_comm with ⟨α, hα_eq, _, _⟩
  have ha_eq : a_μ = ∑ c ∈ α, staticCSSCheckPauliZ D_field c := by
    ext q; let δq : BoxSlot3D L q_code → ZMod 2 := fun slot => if slot = q then 1 else 0
    have hq := hα_eq (0, δq); (try dsimp only at hq)
    have h_lhs : (∑ slot : BoxSlot3D L q_code, ((0 : BoxSlot3D L q_code → ZMod 2) slot * b_μ slot + a_μ slot * δq slot)) = a_μ q := by
      rw [Finset.sum_eq_single q] <;> [simp [δq]; (intro slot _ hne; simp [δq, hne]); (intro h_abs; exact False.elim (h_abs (Finset.mem_univ q)))]
    have h_rhs : (∑ c ∈ α, boolToZMod2 (staticCSSPauliFlip D_field 0 δq c)) = (∑ c ∈ α, staticCSSCheckPauliZ D_field c) q := by
      rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun c _ => ?_
      rw [boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (0, δq) c]; (try dsimp only)
      rw [Finset.sum_eq_single q] <;> [simp [δq]; (intro slot _ hne; simp [δq, hne]); (intro h_abs; exact False.elim (h_abs (Finset.mem_univ q)))]
    rw [← h_lhs, hq, h_rhs]
  have hb_eq : b_μ = ∑ c ∈ α, staticCSSCheckPauliX D_field c := by
    ext q; let δq : BoxSlot3D L q_code → ZMod 2 := fun slot => if slot = q then 1 else 0
    have hq := hα_eq (δq, 0); (try dsimp only at hq)
    have h_lhs : (∑ slot : BoxSlot3D L q_code, (δq slot * b_μ slot +
        a_μ slot * (0 : BoxSlot3D L q_code → ZMod 2) slot)) = b_μ q := by
      rw [Finset.sum_eq_single q] <;> [simp [δq]; (intro slot _ hne; simp [δq, hne]);
        (intro h_abs; exact False.elim (h_abs (Finset.mem_univ q)))]
    have h_rhs : (∑ c ∈ α, boolToZMod2 (staticCSSPauliFlip D_field δq 0 c)) =
        (∑ c ∈ α, staticCSSCheckPauliX D_field c) q := by
      rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun c _ => ?_
      rw [boolToZMod2_staticCSSPauliFlip_eq_sum_checkPauli D_field (δq, 0) c]; (try dsimp only)
      rw [Finset.sum_eq_single q] <;> [simp [δq]; (intro slot _ hne; simp [δq, hne]);
        (intro h_abs; exact False.elim (h_abs (Finset.mem_univ q)))]
    rw [← h_lhs, hq, h_rhs]
  have h_mem_stab : (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum ∈
      stabilizerPauliSubmodule D_field := by
    have h_eq_sum : (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum =
        ∑ c ∈ α, (staticCSSCheckPauliZ D_field c, staticCSSCheckPauliX D_field c) := by
      ext slot <;> [change a_μ slot = _; change b_μ slot = _] <;> [rw [ha_eq, Prod.fst_sum]; rw [hb_eq, Prod.snd_sum]]
    rw [h_eq_sum]; exact Submodule.sum_mem _ fun c _ => Submodule.subset_span ⟨c, rfl⟩
  have h_proj_sum : bareLogicalProjection D_field
      (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum =
      (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum := by
    have h_map_sum : ∀ l : List (WorldlineDysonPolymer L q_code),
        bareLogicalProjection D_field (l.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum =
          (l.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum := by
      intro l; induction l with
      | nil => exact map_zero (bareLogicalProjection D_field)
      | cons hd tl ih =>
        rw [List.map_cons, List.sum_cons, map_add, ih]; congr 1
        unfold worldlinePolymerLogicalCoset bareLogicalProjection
        let S := stabilizerPauliSubmodule D_field
        have hQ : IsCompl (Classical.choose S.exists_isCompl) S := (Classical.choose_spec S.exists_isCompl).symm
        dsimp only [LinearMap.comp_apply, Submodule.coe_subtype]
        rw [Submodule.linearProjOfIsCompl_apply_left hQ]
    exact h_map_sum K
  rw [← h_proj_sum]; exact bareLogicalProjection_eq_zero_of_mem_stabilizerPauliSubmodule D_field h_mem_stab

lemma list_prod_hermitianPauliZX_worldlinePolymerLogicalCoset_eq_one
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L] {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (h_coset_zero : (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 0) :
    (K.map (fun γ => hermitianPauliZX
      (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
      (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)).prod = 1 := by
  let μ : Fin K.length → PauliBitstringPair L q_code := fun i => worldlinePolymerLogicalCoset D_field sys C_RCA (K.get i)
  have h_sum_zero : (∑ i : Fin K.length, μ i) = 0 := by
    rw [← List.sum_ofFn, ← h_coset_zero]; congr 1; exact List.ext_get (by simp) (fun i h1 h2 => by simp [μ])
  have h_off_diag : ∀ i j : Fin K.length, i ≠ j → (∑ slot : BoxSlot3D L q_code, (μ j).1 slot * (μ i).2 slot) = 0 := by
    intro i j hij
    have h_compat_ij : ¬ArePolymersIncompatible sys C_RCA (K.get i) (K.get j) := by
      rcases lt_or_gt_of_ne hij with h_lt | h_gt
      · exact List.pairwise_iff_get.mp hK_pw i j h_lt
      · exact fun h_inc => List.pairwise_iff_get.mp hK_pw j i h_gt (fun h_disj => h_inc h_disj.symm)
    exact sum_worldlinePolymerLogicalCoset_fst_mul_snd_eq_zero_of_compatible hC_RCA
      D_field h_valid sys h_sys_checks (hK_valid _ (List.get_mem K i)) (hK_valid _ (List.get_mem K j)) h_compat_ij
  have h_all_pair_zero : ∀ i j : Fin K.length, (∑ slot : BoxSlot3D L q_code, (μ j).1 slot * (μ i).2 slot) = 0 := by
    intro i j; by_cases hij : i = j
    · subst hij
      have h_fst_sum : ∀ slot, (∑ k : Fin K.length, (μ k).1 slot) = 0 := fun slot => by
        have h0 : (∑ k : Fin K.length, μ k).1 slot = 0 := by rw [h_sum_zero]; rfl
        rwa [Prod.fst_sum, Finset.sum_apply] at h0
      have h_eq_erase : ∀ slot, (μ i).1 slot = ∑ k ∈ Finset.univ.erase i, (μ k).1 slot := fun slot => by
        have h_split := Finset.add_sum_erase Finset.univ (fun k => (μ k).1 slot) (Finset.mem_univ i)
        rw [h_fst_sum slot] at h_split
        exact (by decide : ∀ x y : ZMod 2, x + y = 0 → x = y) _ _ h_split
      calc (∑ slot : BoxSlot3D L q_code, (μ i).1 slot * (μ i).2 slot)
        _ = ∑ slot : BoxSlot3D L q_code, (∑ k ∈ Finset.univ.erase i, (μ k).1 slot) * (μ i).2 slot :=
            Finset.sum_congr rfl fun slot _ => by rw [h_eq_erase slot]
        _ = ∑ k ∈ Finset.univ.erase i, ∑ slot : BoxSlot3D L q_code, (μ k).1 slot * (μ i).2 slot := by
            simp only [Finset.sum_mul]; exact Finset.sum_comm
        _ = 0 := Finset.sum_eq_zero fun k hk => h_off_diag i k (Finset.ne_of_mem_erase hk).symm
    · exact h_off_diag i j hij
  have h_list_weyl : ∀ (l : List (PauliBitstringPair L q_code)),
      (∀ p ∈ l, (∑ slot, p.1 slot * p.2 slot) = 0) → (∀ p ∈ l, ∀ q ∈ l, (∑ slot, q.1 slot * p.2 slot) = 0) →
      (l.map (fun p => hermitianPauliZX p.1 p.2)).prod = weylPauliZ (l.map Prod.fst).sum * weylPauliX (l.map Prod.snd).sum := by
    intro l h_diag h_cross; induction l with
    | nil => simp [weylPauliZ_zero, weylPauliX_zero]
    | cons hd tl ih =>
      rw [List.map_cons, List.prod_cons, ih (fun p hp => h_diag p (List.mem_cons_of_mem hd hp))
        (fun p hp q hq => h_cross p (List.mem_cons_of_mem hd hp) q (List.mem_cons_of_mem hd hq))]
      have h_hd : hermitianPauliZX hd.1 hd.2 = weylPauliZ hd.1 * weylPauliX hd.2 := by
        unfold hermitianPauliZX; rw [if_pos (h_diag hd List.mem_cons_self)]
      rw [h_hd, weylPauliZX_mul_weylPauliZX]
      have h_phase_zero : (∑ slot : BoxSlot3D L q_code, (tl.map Prod.fst).sum slot * hd.2 slot) = 0 := by
        have h_tl_sum : ∀ (t : List (PauliBitstringPair L q_code)), (∀ q ∈ t, (∑ slot, q.1 slot * hd.2 slot) = 0) →
            (∑ slot, (t.map Prod.fst).sum slot * hd.2 slot) = 0 := by
          intro t ht; induction t with
          | nil => simp
          | cons x xs ih_t =>
            simp only [List.map_cons, List.sum_cons, Pi.add_apply, add_mul, Finset.sum_add_distrib]
            rw [ht x List.mem_cons_self, ih_t (fun q hq => ht q (List.mem_cons_of_mem x hq)), add_zero]
        exact h_tl_sum tl (fun q hq => h_cross hd List.mem_cons_self q (List.mem_cons_of_mem hd hq))
      rw [h_phase_zero, signScalar_zero, one_smul, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
  have h_mem_idx : ∀ p ∈ K.map (worldlinePolymerLogicalCoset D_field sys C_RCA), ∃ i : Fin K.length, p = μ i := by
    intro p hp; rcases List.mem_map.mp hp with ⟨γ, hγ, rfl⟩; rcases List.mem_iff_get.mp hγ with ⟨i, rfl⟩; exact ⟨i, rfl⟩
  have h_prod := h_list_weyl (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA))
    (fun p hp => by rcases h_mem_idx p hp with ⟨i, rfl⟩; exact h_all_pair_zero i i)
    (fun p hp q hq => by rcases h_mem_idx p hp with ⟨i, rfl⟩; rcases h_mem_idx q hq with ⟨j, rfl⟩; exact h_all_pair_zero i j)
  rw [List.map_map] at h_prod
  have h_fst_zero : ((K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).map Prod.fst).sum = 0 := by
    have h_sum_fst : ∀ l : List (PauliBitstringPair L q_code), (l.map Prod.fst).sum = l.sum.1 := by
      intro l; induction l with | nil => rfl | cons hd tl ih => rw [List.map_cons, List.sum_cons, List.sum_cons, Prod.fst_add, ih]
    rw [h_sum_fst, h_coset_zero]; rfl
  have h_snd_zero : ((K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).map Prod.snd).sum = 0 := by
    have h_sum_snd : ∀ l : List (PauliBitstringPair L q_code), (l.map Prod.snd).sum = l.sum.2 := by
      intro l; induction l with | nil => rfl | cons hd tl ih => rw [List.map_cons, List.sum_cons, List.sum_cons, Prod.snd_add, ih]
    rw [h_sum_snd, h_coset_zero]; rfl
  rw [h_fst_zero, h_snd_zero, weylPauliZ_zero, weylPauliX_zero, mul_one] at h_prod
  exact h_prod

end DirectWorldlineCluster
end
