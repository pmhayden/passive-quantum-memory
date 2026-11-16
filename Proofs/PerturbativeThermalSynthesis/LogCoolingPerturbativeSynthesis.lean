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

import Proofs.ScalingTempCheckGas.BHMFormToScalingGibbsLeakage
import Proofs.TwoAxisMemorySynthesis.Part1TwoAxisMemorySynthesis

/-!
# Logarithmic-Cooling Perturbative Gibbs and KMS Memory Synthesis

Defines `SatisfiesScalingTempPerturbativeThermalAndKMSStability` in namespace `LogCoolingPerturbativeSynthesis` and proves `log_cooling_perturbative_thermal_stability_main`. Establishes stretched-exponential quasi-adiabatic-continuation dressed Gibbs stability and KMS-symmetric Lindblad memory lifetime in the logarithmic-cooling regime under super-polynomially decaying quasi-local perturbations.

## References

* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`)
* Part II, Section 7.1 (`subsec:conceptual-synthesis`)
-/

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge
open ScalingTempCheckGas Part1TwoAxisMemorySynthesis

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace LogCoolingPerturbativeSynthesis

private lemma q_code_BDL_ge_one : 1 ≤ qCodeBDL := by decide
private lemma r_0_BDL_ge_one : 1 ≤ r0BDL := by decide
private lemma w_0_BDL_ge_one : 1 ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by decide
private lemma c_chk_BDL_ge_one : 1 ≤ qCodeBDL + 2 * mMaxBDL := by decide

attribute [local irreducible]
  collarConstRCABDL bdlLambda bBDL bdlHierarchySteps qCodeBDL r0BDL mMaxBDL
  IndexedCommutingProjectorHamiltonian.H0 IndexedCommutingProjectorHamiltonian.groundProj
  IndexedCommutingProjectorHamiltonian.localGroundProj
  IndexedCommutingProjectorHamiltonian.groundSpace IndexedCommutingProjectorHamiltonian.groundDegeneracy
  IndexedCommutingProjectorHamiltonian.syndromeProjector QuasiLocalPerturbation.totalPerturbation
  gibbsFailureProb opKMSNorm opKMSNormSq SatisfiesKMSLindbladODE heisenbergFlow condExp IsSupportedOn
  syndromeSignOp syndromeSubsetProj bdlSafeSyndromeSet bdlWeldedCode bdlLocalDescriptor
  weylPauliZ weylPauliX bdlPushChain

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]
local notation "ℋ_CP[" L ", " Site0 ", " N_checks "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks)
local notation "𝒱_pert[" L ", " Site0 "]" =>
  QuasiLocalPerturbation 3 L (UniformSite3D L Site0)
local notation "ℬ_bath[" L ", " Site0 "]" =>
  BathChannel 3 L (UniformSite3D L Site0)

/-- **Theorem 6.4 (`thm:main-B`) — Scaling-Temperature Perturbative Full-Spectrum, Dressed Gibbs,
    and KMS Lindblad Dynamical Memory Stability
    (`SatisfiesScalingTempPerturbativeThermalAndKMSStability`)**. -/
def SatisfiesScalingTempPerturbativeThermalAndKMSStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    (R_bath : ℕ)
    (C_scale c_F_pert δ_split : ℝ)
    (g_LR : ℕ → ℝ) : Prop :=
  let H := sys.H0 + V.totalPerturbation
  ∃ (U_dress : unitary ℬ[L, Site0]) (E0 : ℝ),
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    IsQuasiLocalUnitary U_dress g_LR ∧
    ‖H * P0_dress - P0_dress * H‖ ≤ δ_split ∧
    ‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_split ∧
    (∀ ψ : ℋ[L, Site0],
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * H * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) ∧
    (∀ O_0 : ℬ[L, Site0], (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      let O_dress := U_dress.1 * O_0 * U_dress.1†
      ‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split ∧
      (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
        IsSupportedOn (UniformSite3D L Site0) {v} A_v →
        ‖Pi_safe_dress * (A_v * O_dress - O_dress * A_v) * Pi_safe_dress‖ ≤ δ_split * ‖A_v‖) ∧
      (∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, Site0],
        IsSupportedOn (UniformSite3D L Site0) W M_W →
        ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_split * ‖M_W‖) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split)) ∧
    (∀ (β : ℝ) (hH : IsSelfAdjoint H),
      C_scale * Real.log (L : ℝ) ≤ β →
      let p_log := ((L ^ 3 : ℕ) : ℝ) * Real.exp (-c_F_pert * β) + δ_split
      gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log ∧
      (∀ (L_diss : ℬ[L, Site0] →L[ℂ] ℬ[L, Site0]) (O_0 : ℬ[L, Site0]) (Γ_diss : ℝ),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        let O_dress := U_dress.1 * O_0 * U_dress.1†
        IsKMSSymmetricDissipativeGenerator H hH β L_diss →
        2 * kmsDissipativeForm H hH β L_diss O_dress O_dress ≤ Γ_diss →
        ∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSDissipativeODE H hH β L_diss O_dress O_t t →
          opKMSNorm H hH β (O_t t - O_dress) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_split) Γ_diss t) ∧
      (∀ (bath : Finset ℬ_bath[L, Site0]) (O_0 : ℬ[L, Site0]),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsCubeRangeBath 3 L R_bath bath →
        let O_dress := U_dress.1 * O_0 * U_dress.1†
        (IsAdjointSymmetricBath bath →
          ∀ t : ℝ, 0 ≤ t →
            SatisfiesKMSLindbladODE H hH β bath O_dress
              (fun s => opKMSLindbladSemigroup H hH β bath s O_dress) t) ∧
        (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSLindbladODE H hH β bath O_dress O_t t →
          opKMSNorm H hH β (O_t t - O_dress) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_split)
              ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split))
              t)))

private lemma reindexHamiltonian_isGeometricallyLocal {L N_checks r_0 w_0 : ℕ}
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Fintype SiteB] [DecidableEq SiteB]
    (e0 : SiteA ≃ SiteB)
    (sys₀ : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteA) (Fin N_checks))
    (h : sys₀.IsGeometricallyLocal r_0 w_0) :
    (reindexHamiltonian (fun _ : Box3D L => e0) sys₀).IsGeometricallyLocal r_0 w_0 := h

private lemma reindexHamiltonian_reindex_weight {L N_checks : ℕ}
    {SiteA SiteB Idx : Type} [Fintype SiteA] [DecidableEq SiteA]
    [Fintype SiteB] [DecidableEq SiteB] [Fintype Idx] [DecidableEq Idx]
    (e0 : SiteA ≃ SiteB) (e_chk : Idx ≃ Fin N_checks)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteA) Idx) (i : Fin N_checks) :
    (reindexHamiltonian (fun _ : Box3D L => e0) (sys.reindex e_chk)).weight i =
      sys.weight (e_chk.symm i) := rfl

private lemma satisfiesDecayBound_reindexPerturbation {L : ℕ}
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Fintype SiteB] [DecidableEq SiteB]
    (e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA)
    (V₁ : QuasiLocalPerturbation 3 L (UniformSite3D L SiteB))
    {J : ℝ} {f : ℕ → ℝ} (hV₁ : V₁.SatisfiesDecayBound J f) :
    (reindexPerturbation e_inv V₁).SatisfiesDecayBound J f := by
  intro r hr A hA
  change ‖conjSiteOp e_inv (V₁.term r A)‖ ≤ J * f r
  rw [norm_conjSiteOp]; exact hV₁ r hr A hA

private lemma card_staticCSSCheckIdx_le (L : ℕ) :
    Fintype.card (StaticCSSCheckIdx L qCodeBDL mMaxBDL) ≤
      (qCodeBDL + 2 * mMaxBDL) * L ^ 3 := by
  have h_surj : Function.Surjective
      (mkStaticCSSCheckIdx (L := L) (q_code := qCodeBDL) (m_max := mMaxBDL)) :=
    fun idx => ⟨(staticCSSCheckSite idx, staticCSSCheckSlot idx), mkStaticCSSCheckIdx_site_slot idx⟩
  calc Fintype.card (StaticCSSCheckIdx L qCodeBDL mMaxBDL)
    _ ≤ Fintype.card (Box3D L × (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)) :=
      Fintype.card_le_of_surjective mkStaticCSSCheckIdx h_surj
    _ = Fintype.card (Box3D L) *
        Fintype.card (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL) := Fintype.card_prod _ _
    _ = (qCodeBDL + 2 * mMaxBDL) * L ^ 3 := by
      have h_box : Fintype.card (Box3D L) = L ^ 3 := by
        dsimp [Box3D, BoxD]; rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      have h_slot : Fintype.card (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL) =
          qCodeBDL + 2 * mMaxBDL := by
        rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
        omega
      rw [h_box, h_slot, mul_comm]

private lemma hilbertTrace_zero_codeSlot {L : ℕ} :
    hilbertTrace (0 : ℬ[L, CodeSlotConfig qCodeBDL]) = 0 := by
  unfold hilbertTrace; simp

private lemma bdlBoxSide_ge_two (k : ℕ) : 2 ≤ bdlBoxSide k := by
  have := (bdlBoxSide_scaling_and_strictMono k).2.1
  omega

private lemma bdlBoxSide_ge_of_le {R_0 k : ℕ} (hk : R_0 ≤ k) : R_0 ≤ bdlBoxSide k := by
  have := (bdlBoxSide_scaling_and_strictMono k).2.1
  omega

private lemma exists_atTop_le_half_of_isSuperpolynomialDecay {δ_split : ℕ → ℝ}
    (hδ : IsSuperpolynomialDecay δ_split) :
    ∃ R_0 : ℕ, ∀ L : ℕ, R_0 ≤ L → δ_split L ≤ 1 / 2 := by
  have h_tend0 : Filter.Tendsto δ_split Filter.atTop (nhds 0) := by
    simpa using hδ.2 0
  obtain ⟨R_0, hR_0⟩ := Metric.tendsto_atTop.mp h_tend0 (1 / 2) (by positivity)
  refine ⟨R_0, fun L hL => ?_⟩
  have h_dist := hR_0 L hL
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hδ.1 L)] at h_dist
  exact le_of_lt h_dist

lemma c_scale_BDL_pos :
    (0 : ℝ) < 4 * ((qCodeBDL + 2 * mMaxBDL : ℕ) : ℝ) + 4 := by positivity

lemma c_F_pert_BDL_pos : (0 : ℝ) < 1 / 4 := by norm_num

/-- Pure assembly of `SatisfiesScalingTempPerturbativeThermalAndKMSStability` from abstract
    reindexed operators and Hamiltonians (no `let`-bindings or structure projections). -/
private lemma satisfiesScalingTemp_of_reindexed_data
    {L N_c C_chk R_bath : ℕ} [NeZero L]
    {SiteB : Type} [Fintype SiteB] [DecidableEq SiteB] [Nonempty SiteB]
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (sys₁ : ℋ_CP[L, SiteB, N_c])
    (sys_raw : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteB) Idx)
    (Pi_safe₁ O_dec_Z₁ O_dec_X₁ : ℬ[L, SiteB])
    (V₁ : 𝒱_pert[L, SiteB])
    (U₁ : unitary ℬ[L, SiteB]) (E0 δ_0 δ_ch' δ_split : ℝ) (g_LR : ℕ → ℝ)
    (hH0_eq : sys₁.H0 = sys_raw.H0) (hP0_eq : sys₁.P0 = sys_raw.P0)
    (h_wt_raw : ∀ idx : Idx, sys_raw.weight idx = 1)
    (h_P0_ne_raw : sys_raw.P0 ≠ 0)
    (h_tr_le_raw : ∀ σ : Idx → Bool, hilbertTrace (sys_raw.syndromeProjector σ) ≤ hilbertTrace sys_raw.P0)
    (hC_chk : 1 ≤ C_chk) (h_card_chk : Fintype.card Idx ≤ C_chk * L ^ 3) (hL2 : 2 ≤ L)
    (hPi₁ : IsStarProjection Pi_safe₁) (hP0_Pi₁ : sys_raw.P0 * Pi_safe₁ = sys_raw.P0)
    (hOZ_sa₁ : IsSelfAdjoint O_dec_Z₁) (hOZ_norm₁ : ‖O_dec_Z₁‖ ≤ 1)
    (hP0_OZ₁ : Commute sys_raw.P0 O_dec_Z₁)
    (hOX_sa₁ : IsSelfAdjoint O_dec_X₁) (hOX_norm₁ : ‖O_dec_X₁‖ ≤ 1)
    (hP0_OX₁ : Commute sys_raw.P0 O_dec_X₁)
    (hδ0_half : δ_0 ≤ 1 / 2) (hδ0_le : δ_0 ≤ δ_split)
    (hδ_ch_nonneg : 0 ≤ δ_ch') (hδ_ch_le_one : δ_ch' ≤ 1) (hδ_ch_nine : 9 * δ_ch' ≤ δ_split)
    (h_ql₁ : IsQuasiLocalUnitary U₁ g_LR)
    (h_comm_P0₁_0 : ‖(sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * sys_raw.P0 * U₁.1†) -
      (U₁.1 * sys_raw.P0 * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)‖ ≤ δ_0 / 6)
    (h_form_q₁_0 : ∀ ψ₁ : ℋ[L, SiteB],
      |RCLike.re (inner ℂ ψ₁
          ((U₁.1† * (sys_raw.H0 + V₁.totalPerturbation) * U₁.1 - sys_raw.H0 - (E0 : ℂ) • 1) ψ₁))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ₁ (sys_raw.H0 ψ₁)) + (δ_0 / 4) * ‖ψ₁‖ ^ 2)
    (h_coh_Z₁_0 : ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
      ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_Z₁ * U₁.1†) -
        (U₁.1 * O_dec_Z₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
      (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0)
    (h_coh_X₁_0 : ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
      ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_X₁ * U₁.1†) -
        (U₁.1 * O_dec_X₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
      (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0)
    (h_1site₁_0 : ∀ (v : Box3D L) (A_v : ℬ[L, SiteB]),
      IsSupportedOn (UniformSite3D L SiteB) {v} A_v →
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (A_v * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * A_v) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0 * ‖A_v‖ ∧
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (A_v * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * A_v) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0 * ‖A_v‖)
    (h_cube₁_ch : ∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, SiteB],
      IsSupportedOn (UniformSite3D L SiteB) W M_W →
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (M_W * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * M_W) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_ch' * ‖M_W‖ ∧
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (M_W * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * M_W) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_ch' * ‖M_W‖) :
    SatisfiesScalingTempPerturbativeThermalAndKMSStability
      sys₁ Pi_safe₁ O_dec_Z₁ O_dec_X₁ V₁ R_bath (4 * (C_chk : ℝ) + 4) (1 / 4) δ_split g_LR := by
  have hδ0_nn : 0 ≤ δ_0 := by linarith [le_trans (norm_nonneg _) h_comm_P0₁_0]
  have hδ_nn : 0 ≤ δ_split := le_trans hδ0_nn hδ0_le
  have h_ch_le_split : δ_ch' ≤ δ_split := by linarith
  have h_comm_P0₁ :
      ‖(sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * sys_raw.P0 * U₁.1†) -
        (U₁.1 * sys_raw.P0 * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)‖ ≤ δ_split / 6 :=
    le_trans h_comm_P0₁_0 (by linarith)
  have h_form_q₁ : ∀ ψ₁ : ℋ[L, SiteB],
      |RCLike.re (inner ℂ ψ₁
          ((U₁.1† * (sys_raw.H0 + V₁.totalPerturbation) * U₁.1 - sys_raw.H0 - (E0 : ℂ) • 1) ψ₁))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ₁ (sys_raw.H0 ψ₁)) + (δ_split / 4) * ‖ψ₁‖ ^ 2 := by
    intro ψ₁
    have h1 := h_form_q₁_0 ψ₁
    have h2 : (δ_0 / 4) * ‖ψ₁‖ ^ 2 ≤ (δ_split / 4) * ‖ψ₁‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  have h_form'₁ : ∀ ψ₁ : ℋ[L, SiteB],
      |RCLike.re (inner ℂ ψ₁
          ((U₁.1† * (sys_raw.H0 + V₁.totalPerturbation) * U₁.1 - sys_raw.H0 - (E0 : ℂ) • 1) ψ₁))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ₁ (sys_raw.H0 ψ₁)) + (δ_split / 2) * ‖ψ₁‖ ^ 2 := by
    intro ψ₁
    have h1 := h_form_q₁ ψ₁
    rw [show bhmSandwichDeviation = (1 / 4 : ℝ) from rfl] at h1
    have h2 : (δ_split / 4) * ‖ψ₁‖ ^ 2 ≤ (δ_split / 2) * ‖ψ₁‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  have h_coh_Z₁ :
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_Z₁ * U₁.1†) -
          (U₁.1 * O_dec_Z₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_split := le_trans h_coh_Z₁_0 hδ0_le
  have h_coh_X₁ :
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_X₁ * U₁.1†) -
          (U₁.1 * O_dec_X₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_split := le_trans h_coh_X₁_0 hδ0_le
  refine ⟨U₁, E0, h_ql₁, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hH0_eq, hP0_eq]; exact le_trans h_comm_P0₁ (by linarith)
  · rw [hH0_eq, hP0_eq]
    exact dressed_ground_subspace_splitting_opNorm_le sys_raw V₁ U₁ h_form'₁
  · intro ψ₁; rw [hH0_eq]; exact h_form'₁ ψ₁
  · intro O_0 hO_cases
    rcases hO_cases with rfl | rfl
    · refine ⟨by rw [hH0_eq]; exact h_coh_Z₁,
        fun v A_v hA_v =>
          le_trans (h_1site₁_0 v A_v hA_v).1 (mul_le_mul_of_nonneg_right hδ0_le (norm_nonneg _)),
        fun r hr W hW M_W hM_W =>
          le_trans (h_cube₁_ch r hr W hW M_W hM_W).1
            (mul_le_mul_of_nonneg_right h_ch_le_split (norm_nonneg _)),
        fun t ht => ?_⟩
      rw [hH0_eq, hP0_eq]
      exact zero_temp_heisenberg_ground_drift_of_relative_form
        sys_raw V₁ U₁ O_0 (E0 := E0) (δ_split := δ_split)
        hP0_OZ₁ hOZ_norm₁ h_comm_P0₁ h_form_q₁ t ht
    · refine ⟨by rw [hH0_eq]; exact h_coh_X₁,
        fun v A_v hA_v =>
          le_trans (h_1site₁_0 v A_v hA_v).2 (mul_le_mul_of_nonneg_right hδ0_le (norm_nonneg _)),
        fun r hr W hW M_W hM_W =>
          le_trans (h_cube₁_ch r hr W hW M_W hM_W).2
            (mul_le_mul_of_nonneg_right h_ch_le_split (norm_nonneg _)),
        fun t ht => ?_⟩
      rw [hH0_eq, hP0_eq]
      exact zero_temp_heisenberg_ground_drift_of_relative_form
        sys_raw V₁ U₁ O_0 (E0 := E0) (δ_split := δ_split)
        hP0_OX₁ hOX_norm₁ h_comm_P0₁ h_form_q₁ t ht
  · rw [hH0_eq]
    intro β hH hβ_scale
    let H := sys_raw.H0 + V₁.totalPerturbation
    let Pi_safe_dress := U₁.1 * Pi_safe₁ * U₁.1†
    let p_log := ((L ^ 3 : ℕ) : ℝ) * Real.exp (-(1 / 4 : ℝ) * β) + δ_split
    have hp_log0 := (gibbsFailureProb_and_kms_bound_of_scaling_temp_bhm_form
      sys_raw h_wt_raw h_P0_ne_raw h_tr_le_raw hC_chk h_card_chk hL2
      V₁ U₁ Pi_safe₁ O_dec_Z₁ O_dec_X₁ hPi₁ hP0_Pi₁ hOZ_sa₁ hOZ_norm₁ hOX_sa₁ hOX_norm₁
      (E0 := E0) (δ_0 := δ_0)
      hδ0_half h_comm_P0₁_0 h_form_q₁_0 h_coh_Z₁_0 h_coh_X₁_0 h_1site₁_0 β hH hβ_scale).1
    have hp_log : gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log :=
      le_trans hp_log0 (by dsimp only [p_log]; linarith)
    have hp_nn : 0 ≤ p_log := by dsimp only [p_log]; positivity
    have hPi_dress : IsStarProjection Pi_safe_dress :=
      KMSPinchedGibbs.isStarProjection_unitary_conj U₁ hPi₁
    have h_obs_kms : ∀ O_0 : ℬ[L, SiteB], (O_0 = O_dec_Z₁ ∨ O_0 = O_dec_X₁) →
        let O_dress := U₁.1 * O_0 * U₁.1†
        IsSelfAdjoint O_dress ∧
        opKMSNorm H hH β (opCommutator H O_dress) ≤
          2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_split ∧
        (∀ bath : Finset ℬ_bath[L, SiteB],
          IsCubeRangeBath 3 L R_bath bath →
          2 * kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) O_dress O_dress ≤
            (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split)) := by
      intro O_0 hO
      rcases hO with hO | hO
      · rw [hO]
        have hO_sa : IsSelfAdjoint (U₁.1 * O_dec_Z₁ * U₁.1†) :=
          isSelfAdjoint_unitary_conj U₁ hOZ_sa₁
        have hO_n : ‖U₁.1 * O_dec_Z₁ * U₁.1†‖ ≤ 1 :=
          le_trans (norm_unitary_conj_le U₁ O_dec_Z₁) hOZ_norm₁
        have h_dr := dressed_cubeRangeBath_drift_and_dissipativeForm_le
          H hH β Pi_safe_dress (U₁.1 * O_dec_Z₁ * U₁.1†) hPi_dress hO_n hp_nn hp_log
          h_coh_Z₁ hδ_ch_nonneg hδ_ch_le_one hδ_ch_nine
          (fun r hr W hW M_W hM_W => (h_cube₁_ch r hr W hW M_W hM_W).1)
        exact ⟨hO_sa, h_dr.1, h_dr.2⟩
      · rw [hO]
        have hO_sa : IsSelfAdjoint (U₁.1 * O_dec_X₁ * U₁.1†) :=
          isSelfAdjoint_unitary_conj U₁ hOX_sa₁
        have hO_n : ‖U₁.1 * O_dec_X₁ * U₁.1†‖ ≤ 1 :=
          le_trans (norm_unitary_conj_le U₁ O_dec_X₁) hOX_norm₁
        have h_dr := dressed_cubeRangeBath_drift_and_dissipativeForm_le
          H hH β Pi_safe_dress (U₁.1 * O_dec_X₁ * U₁.1†) hPi_dress hO_n hp_nn hp_log
          h_coh_X₁ hδ_ch_nonneg hδ_ch_le_one hδ_ch_nine
          (fun r hr W hW M_W hM_W => (h_cube₁_ch r hr W hW M_W hM_W).2)
        exact ⟨hO_sa, h_dr.1, h_dr.2⟩
    refine ⟨hp_log, ?_, ?_⟩
    · intro L_diss O_0 Γ_diss hO O_dress hL_gen h_diss O_t t ht h_ode
      rcases h_obs_kms O_0 hO with ⟨hO_sa, h_coh_kms, _⟩
      have hE_nn : 0 ≤ kmsDissipativeForm H hH β L_diss O_dress O_dress := hL_gen.2.2 O_dress
      have hΓ_diss_nn : 0 ≤ Γ_diss := by linarith
      have hΓ_coh_nn : 0 ≤ 2 * ‖H * O_dress - O_dress * H‖ *
          (p_log ^ (1 / 4 : ℝ)) + δ_split := by positivity
      exact opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE
        H hH β L_diss hL_gen O_dress hO_sa hΓ_coh_nn hΓ_diss_nn ht
        h_coh_kms h_diss h_ode
    · intro bath O_0 hO h_bath
      rcases h_obs_kms O_0 hO with ⟨hO_sa, h_coh_kms, h_bath_form⟩
      refine ⟨fun h_adj t ht =>
        (satisfiesKMSLindbladODE_opKMSLindbladSemigroup
          H hH β bath h_adj (U₁.1 * O_0 * U₁.1†) hO_sa ht).2, ?_⟩
      intro O_t t ht h_ode
      have h_gamma_nn : ∀ ch ∈ bath, 0 ≤ ch.γ := fun ch hch => (h_bath ch hch).1
      have hL_gen := isKMSSymmetricDissipativeGenerator_opKMSLindbladDissipator H hH β bath h_gamma_nn
      have h_diss := h_bath_form bath h_bath
      have hE_nn : 0 ≤ kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath)
          (U₁.1 * O_0 * U₁.1†) (U₁.1 * O_0 * U₁.1†) := hL_gen.2.2 _
      have hΓ_diss_nn : 0 ≤ (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) *
          (16 * (p_log ^ (1 / 2 : ℝ)) + δ_split) := by linarith
      have hΓ_coh_nn : 0 ≤ 2 * ‖H * (U₁.1 * O_0 * U₁.1†) - (U₁.1 * O_0 * U₁.1†) * H‖ *
          (p_log ^ (1 / 4 : ℝ)) + δ_split := by positivity
      exact opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE
        H hH β (opKMSLindbladDissipator H hH β bath) hL_gen (U₁.1 * O_0 * U₁.1†) hO_sa
        hΓ_coh_nn hΓ_diss_nn ht h_coh_kms h_diss
        ((satisfiesKMSLindbladODE_iff_satisfiesKMSDissipativeODE
          H hH β bath (U₁.1 * O_0 * U₁.1†) O_t t).mp h_ode)

/-- Assembles `SatisfiesScalingTempPerturbativeThermalAndKMSStability` on the site-reindexed and
    check-reindexed Hamiltonian `reindexHamiltonian (fun _ => e0) (m.sys.reindex e_chk)` from the
    dressing bundle returned by `bdl_inhomogeneous_zero_temp_dressing_bundle_exists` together with
    dressed cube commutator bounds (`dressed_cube_safe_commutator_telescoping`). -/
lemma satisfiesScalingTempPerturbativeThermalAndKMSStability_of_dressing_bundle
    {L N_c C_chk R_bath : ℕ} [NeZero L]
    {SiteB : Type} [Fintype SiteB] [DecidableEq SiteB] [Nonempty SiteB]
    (e0 : CodeSlotConfig qCodeBDL ≃ SiteB)
    (e_chk : StaticCSSCheckIdx L qCodeBDL mMaxBDL ≃ Fin N_c)
    (m : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
    (V₁ : 𝒱_pert[L, SiteB])
    (V₀ : 𝒱_pert[L, CodeSlotConfig qCodeBDL])
    (hV₀ : V₀ = reindexPerturbation (fun _ => e0.symm) V₁)
    {δ_0 δ_ch' δ_split : ℝ} {g_LR : ℕ → ℝ}
    (hC_chk : 1 ≤ C_chk)
    (h_card_chk : Fintype.card (StaticCSSCheckIdx L qCodeBDL mMaxBDL) ≤ C_chk * L ^ 3)
    (hL2 : 2 ≤ L)
    (hδ0_half : δ_0 ≤ 1 / 2)
    (hδ0_le : δ_0 ≤ δ_split)
    (hδ_ch_nonneg : 0 ≤ δ_ch') (hδ_ch_le_one : δ_ch' ≤ 1) (hδ_ch_nine : 9 * δ_ch' ≤ δ_split)
    (h_tr_le₀ : ∀ σ : StaticCSSCheckIdx L qCodeBDL mMaxBDL → Bool,
      hilbertTrace (m.sys.syndromeProjector σ) ≤ hilbertTrace m.sys.P0)
    (h_bundle : HasZeroTempDressingBundle m V₀ δ_0 g_LR)
    (h_cube_dress₀ : ∀ (U₀ : unitary ℬ[L, CodeSlotConfig qCodeBDL]),
      IsQuasiLocalUnitary U₀ g_LR →
      ∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r,
        ∀ M_W : ℬ[L, CodeSlotConfig qCodeBDL],
          IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) W M_W →
          ‖(U₀.1 * m.Pi_safe * U₀.1†) *
              (M_W * (U₀.1 * m.O_dec_Z * U₀.1†) - (U₀.1 * m.O_dec_Z * U₀.1†) * M_W) *
              (U₀.1 * m.Pi_safe * U₀.1†)‖ ≤ δ_ch' * ‖M_W‖ ∧
          ‖(U₀.1 * m.Pi_safe * U₀.1†) *
              (M_W * (U₀.1 * m.O_dec_X * U₀.1†) - (U₀.1 * m.O_dec_X * U₀.1†) * M_W) *
              (U₀.1 * m.Pi_safe * U₀.1†)‖ ≤ δ_ch' * ‖M_W‖) :
    SatisfiesScalingTempPerturbativeThermalAndKMSStability
      (reindexHamiltonian (fun _ => e0) (m.sys.reindex e_chk))
      (conjSiteOp (fun _ => e0) m.Pi_safe)
      (conjSiteOp (fun _ => e0) m.O_dec_Z)
      (conjSiteOp (fun _ => e0) m.O_dec_X)
      V₁ R_bath (4 * (C_chk : ℝ) + 4) (1 / 4) δ_split g_LR := by
  let e : ∀ _ : Box3D L, CodeSlotConfig qCodeBDL ≃ SiteB := fun _ => e0
  rcases h_bundle with ⟨U₀, E0, h_dress⟩
  let e_inv : ∀ _ : Box3D L, SiteB ≃ CodeSlotConfig qCodeBDL := fun _ => e0.symm
  let sys₀ := m.sys.reindex e_chk
  let sys₁ := reindexHamiltonian e sys₀
  let sys_raw := reindexHamiltonian e m.sys
  let Pi_safe₁ := conjSiteOp e m.Pi_safe
  let O_dec_Z₁ := conjSiteOp e m.O_dec_Z
  let O_dec_X₁ := conjSiteOp e m.O_dec_X
  let U₁ : unitary ℬ[L, SiteB] := conjEuclideanUnitary (cfgEquiv e) U₀
  have h_U₁ : U₁.1 = conjSiteOp e U₀.1 := rfl
  have h_V_tot : V₁.totalPerturbation = conjSiteOp e V₀.totalPerturbation := by
    have h1 := reindexPerturbation_V_tot e V₀
    have h2 : reindexPerturbation e V₀ = V₁ := by
      rw [hV₀]; cases V₁; simp only [reindexPerturbation, conjSiteOp]; congr; funext r A
      exact conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) _
    rwa [h2] at h1
  have h_H0_raw : sys_raw.H0 = conjSiteOp e m.sys.H0 := reindexHamiltonian_H0 e m.sys
  have h_P0_raw : sys_raw.P0 = conjSiteOp e m.sys.P0 := reindexHamiltonian_P0 e m.sys
  have hH0_eq : sys₁.H0 = sys_raw.H0 := by
    rw [reindexHamiltonian_H0, m.sys.reindex_H0 e_chk, ← h_H0_raw]
  have hP0_eq : sys₁.P0 = sys_raw.P0 := by
    rw [reindexHamiltonian_P0, m.sys.reindex_P0 e_chk, ← h_P0_raw]
  have h_H₁ : sys_raw.H0 + V₁.totalPerturbation = conjSiteOp e (m.sys.H0 + V₀.totalPerturbation) := by
    rw [h_H0_raw, h_V_tot]; rfl
  have h_P0_dress : U₁.1 * sys_raw.P0 * U₁.1† = conjSiteOp e (U₀.1 * m.sys.P0 * U₀.1†) := by
    rw [h_U₁, h_P0_raw]; simp only [conjSiteOp_adjoint, conjSiteOp_mul]
  have h_Pi_dress : U₁.1 * Pi_safe₁ * U₁.1† = conjSiteOp e (U₀.1 * m.Pi_safe * U₀.1†) := by
    rw [h_U₁]; simp only [Pi_safe₁, conjSiteOp_adjoint, conjSiteOp_mul]
  have h_OZ_dress : U₁.1 * O_dec_Z₁ * U₁.1† = conjSiteOp e (U₀.1 * m.O_dec_Z * U₀.1†) := by
    rw [h_U₁]; simp only [O_dec_Z₁, conjSiteOp_adjoint, conjSiteOp_mul]
  have h_OX_dress : U₁.1 * O_dec_X₁ * U₁.1† = conjSiteOp e (U₀.1 * m.O_dec_X * U₀.1†) := by
    rw [h_U₁]; simp only [O_dec_X₁, conjSiteOp_adjoint, conjSiteOp_mul]
  have h_ql₁ : IsQuasiLocalUnitary U₁ g_LR := by
    intro v A_v hA_v r
    let A_v₀ := conjSiteOp e_inv A_v
    have hA_v₀_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v₀ :=
      isSupportedOn_conjSiteOp e_inv hA_v
    have hA_v_eq : A_v = conjSiteOp e A_v₀ :=
      (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) A_v).symm
    have h_conj : U₁.1† * A_v * U₁.1 = conjSiteOp e (U₀.1† * A_v₀ * U₀.1) := by
      rw [h_U₁, hA_v_eq]; simp only [conjSiteOp_adjoint, conjSiteOp_mul]
    rw [h_conj, condExp_conjSiteOp, ← conjSiteOp_sub e,
      norm_conjSiteOp, hA_v_eq, norm_conjSiteOp]
    exact h_dress.1 v A_v₀ hA_v₀_supp r
  have h_comm_P0₁_0 :
      ‖(sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * sys_raw.P0 * U₁.1†) -
        (U₁.1 * sys_raw.P0 * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)‖ ≤ δ_0 / 6 := by
    have h_eq :
        (sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * sys_raw.P0 * U₁.1†) -
          (U₁.1 * sys_raw.P0 * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation) =
        conjSiteOp e ((m.sys.H0 + V₀.totalPerturbation) * (U₀.1 * m.sys.P0 * U₀.1†) -
          (U₀.1 * m.sys.P0 * U₀.1†) * (m.sys.H0 + V₀.totalPerturbation)) := by
      rw [h_H₁, h_P0_dress]; simp only [conjSiteOp_mul, conjSiteOp_sub]
    rw [h_eq, norm_conjSiteOp]; exact h_dress.2.1
  have h_form_q₁_0 : ∀ ψ₁ : ℋ[L, SiteB],
      |RCLike.re (inner ℂ ψ₁
          ((U₁.1† * (sys_raw.H0 + V₁.totalPerturbation) * U₁.1 - sys_raw.H0 - (E0 : ℂ) • 1) ψ₁))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ₁ (sys_raw.H0 ψ₁)) +
          (δ_0 / 4) * ‖ψ₁‖ ^ 2 := by
    intro ψ₁
    let ψ₀ := uReindex (cfgEquiv e).symm ψ₁
    have h_op : U₁.1† * (sys_raw.H0 + V₁.totalPerturbation) * U₁.1 - sys_raw.H0 - (E0 : ℂ) • 1 =
        conjSiteOp e (U₀.1† * (m.sys.H0 + V₀.totalPerturbation) * U₀.1 - m.sys.H0 - (E0 : ℂ) • 1) := by
      rw [h_U₁, h_H₁, h_H0_raw]
      simp only [conjSiteOp_adjoint, conjSiteOp_mul, conjSiteOp_sub, conjSiteOp_smul, conjSiteOp_one]
    rw [h_op, inner_conjSiteOp e, h_H0_raw, inner_conjSiteOp e, ← norm_uReindex (cfgEquiv e).symm ψ₁]
    exact h_dress.2.2.1 ψ₀
  have h_coh_Z₁_0 :
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_Z₁ * U₁.1†) -
          (U₁.1 * O_dec_Z₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0 := by
    have h_eq :
        (U₁.1 * Pi_safe₁ * U₁.1†) *
          ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_Z₁ * U₁.1†) -
            (U₁.1 * O_dec_Z₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
          (U₁.1 * Pi_safe₁ * U₁.1†) =
        conjSiteOp e ((U₀.1 * m.Pi_safe * U₀.1†) *
          ((m.sys.H0 + V₀.totalPerturbation) * (U₀.1 * m.O_dec_Z * U₀.1†) -
            (U₀.1 * m.O_dec_Z * U₀.1†) * (m.sys.H0 + V₀.totalPerturbation)) *
          (U₀.1 * m.Pi_safe * U₀.1†)) := by
      rw [h_Pi_dress, h_H₁, h_OZ_dress]; simp only [conjSiteOp_mul, conjSiteOp_sub]
    rw [h_eq, norm_conjSiteOp]; exact h_dress.2.2.2.1
  have h_coh_X₁_0 :
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_X₁ * U₁.1†) -
          (U₁.1 * O_dec_X₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0 := by
    have h_eq :
        (U₁.1 * Pi_safe₁ * U₁.1†) *
          ((sys_raw.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_X₁ * U₁.1†) -
            (U₁.1 * O_dec_X₁ * U₁.1†) * (sys_raw.H0 + V₁.totalPerturbation)) *
          (U₁.1 * Pi_safe₁ * U₁.1†) =
        conjSiteOp e ((U₀.1 * m.Pi_safe * U₀.1†) *
          ((m.sys.H0 + V₀.totalPerturbation) * (U₀.1 * m.O_dec_X * U₀.1†) -
            (U₀.1 * m.O_dec_X * U₀.1†) * (m.sys.H0 + V₀.totalPerturbation)) *
          (U₀.1 * m.Pi_safe * U₀.1†)) := by
      rw [h_Pi_dress, h_H₁, h_OX_dress]; simp only [conjSiteOp_mul, conjSiteOp_sub]
    rw [h_eq, norm_conjSiteOp]; exact h_dress.2.2.2.2.1
  have h_1site₁_0 : ∀ (v : Box3D L) (A_v : ℬ[L, SiteB]),
      IsSupportedOn (UniformSite3D L SiteB) {v} A_v →
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (A_v * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * A_v) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0 * ‖A_v‖ ∧
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (A_v * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * A_v) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_0 * ‖A_v‖ := by
    intro v A_v hA_v
    let A_v₀ := conjSiteOp e_inv A_v
    have hA_v₀_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v₀ :=
      isSupportedOn_conjSiteOp e_inv hA_v
    have hA_v_eq : A_v = conjSiteOp e A_v₀ :=
      (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) A_v).symm
    rcases h_dress.2.2.2.2.2 v A_v₀ hA_v₀_supp with ⟨hZ0, hX0⟩
    refine ⟨?_, ?_⟩
    · have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
          (A_v * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * A_v) *
          (U₁.1 * Pi_safe₁ * U₁.1†) =
          conjSiteOp e ((U₀.1 * m.Pi_safe * U₀.1†) *
            (A_v₀ * (U₀.1 * m.O_dec_Z * U₀.1†) - (U₀.1 * m.O_dec_Z * U₀.1†) * A_v₀) *
            (U₀.1 * m.Pi_safe * U₀.1†)) := by
        rw [h_Pi_dress, h_OZ_dress, hA_v_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
      rw [h_eq, norm_conjSiteOp, hA_v_eq, norm_conjSiteOp]; exact hZ0
    · have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
          (A_v * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * A_v) *
          (U₁.1 * Pi_safe₁ * U₁.1†) =
          conjSiteOp e ((U₀.1 * m.Pi_safe * U₀.1†) *
            (A_v₀ * (U₀.1 * m.O_dec_X * U₀.1†) - (U₀.1 * m.O_dec_X * U₀.1†) * A_v₀) *
            (U₀.1 * m.Pi_safe * U₀.1†)) := by
        rw [h_Pi_dress, h_OX_dress, hA_v_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
      rw [h_eq, norm_conjSiteOp, hA_v_eq, norm_conjSiteOp]; exact hX0
  have h_cube₁_ch : ∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, SiteB],
      IsSupportedOn (UniformSite3D L SiteB) W M_W →
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (M_W * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * M_W) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_ch' * ‖M_W‖ ∧
      ‖(U₁.1 * Pi_safe₁ * U₁.1†) *
        (M_W * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * M_W) *
        (U₁.1 * Pi_safe₁ * U₁.1†)‖ ≤ δ_ch' * ‖M_W‖ := by
    intro r hr W hW M_W hM_W
    let M_W₀ := conjSiteOp e_inv M_W
    have hM_W₀_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) W M_W₀ :=
      isSupportedOn_conjSiteOp e_inv hM_W
    have hM_W_eq : M_W = conjSiteOp e M_W₀ :=
      (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) M_W).symm
    rcases h_cube_dress₀ U₀ h_dress.1 r hr W hW M_W₀ hM_W₀_supp with ⟨hZ0, hX0⟩
    refine ⟨?_, ?_⟩
    · have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
          (M_W * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * M_W) *
          (U₁.1 * Pi_safe₁ * U₁.1†) =
          conjSiteOp e ((U₀.1 * m.Pi_safe * U₀.1†) *
            (M_W₀ * (U₀.1 * m.O_dec_Z * U₀.1†) - (U₀.1 * m.O_dec_Z * U₀.1†) * M_W₀) *
            (U₀.1 * m.Pi_safe * U₀.1†)) := by
        rw [h_Pi_dress, h_OZ_dress, hM_W_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
      rw [h_eq, norm_conjSiteOp, hM_W_eq, norm_conjSiteOp]; exact hZ0
    · have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
          (M_W * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * M_W) *
          (U₁.1 * Pi_safe₁ * U₁.1†) =
          conjSiteOp e ((U₀.1 * m.Pi_safe * U₀.1†) *
            (M_W₀ * (U₀.1 * m.O_dec_X * U₀.1†) - (U₀.1 * m.O_dec_X * U₀.1†) * M_W₀) *
            (U₀.1 * m.Pi_safe * U₀.1†)) := by
        rw [h_Pi_dress, h_OX_dress, hM_W_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
      rw [h_eq, norm_conjSiteOp, hM_W_eq, norm_conjSiteOp]; exact hX0
  have hP0_sa : IsSelfAdjoint m.sys.P0 := m.sys.isStarProjection_P0.isSelfAdjoint
  have hPi_props := m.h_decoder_props.1
  have hOZ := m.h_decoder_props.2.1; have hOX := m.h_decoder_props.2.2.1
  have hZ := m.h_logical_pair.2.1; have hX := m.h_logical_pair.2.2.1
  have hP0_OZ₀ : Commute m.sys.P0 m.O_dec_Z :=
    commute_P0_of_mul_P0_eq hP0_sa hOZ.1 hZ.1 hZ.2.2.2 hOZ.2.2.2.2.1
  have hP0_OX₀ : Commute m.sys.P0 m.O_dec_X :=
    commute_P0_of_mul_P0_eq hP0_sa hOX.1 hX.1 hX.2.2.2 hOX.2.2.2.2.1
  have hP0_OZ₁ : Commute sys_raw.P0 O_dec_Z₁ := by
    rw [h_P0_raw]; exact (conjSiteOp_commute_iff e _ _).mpr hP0_OZ₀
  have hP0_OX₁ : Commute sys_raw.P0 O_dec_X₁ := by
    rw [h_P0_raw]; exact (conjSiteOp_commute_iff e _ _).mpr hP0_OX₀
  have hOZ_sa₁ : IsSelfAdjoint O_dec_Z₁ := conjSiteOp_isSelfAdjoint e hOZ.1
  have hOX_sa₁ : IsSelfAdjoint O_dec_X₁ := conjSiteOp_isSelfAdjoint e hOX.1
  have hOZ_norm₁ : ‖O_dec_Z₁‖ ≤ 1 := by dsimp [O_dec_Z₁]; rw [norm_conjSiteOp]; exact hOZ.2.2.1
  have hOX_norm₁ : ‖O_dec_X₁‖ ≤ 1 := by dsimp [O_dec_X₁]; rw [norm_conjSiteOp]; exact hOX.2.2.1
  have hPi₁ : IsStarProjection Pi_safe₁ := conjSiteOp_isStarProjection e hPi_props.1
  have hP0_Pi₁ : sys_raw.P0 * Pi_safe₁ = sys_raw.P0 := by
    rw [h_P0_raw]; dsimp [Pi_safe₁]; rw [← conjSiteOp_mul, hPi_props.2.2.2.2]
  have h_wt_raw : ∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL, sys_raw.weight idx = 1 :=
    fun idx => (m.h_sys_checks idx).2.2
  have h_P0_ne_raw : sys_raw.P0 ≠ 0 := by
    rw [h_P0_raw]; exact (conjSiteOp_eq_zero_iff e m.sys.P0).not.mpr m.h_logical_pair.1.1
  have h_tr_le_raw : ∀ σ : StaticCSSCheckIdx L qCodeBDL mMaxBDL → Bool,
      hilbertTrace (sys_raw.syndromeProjector σ) ≤ hilbertTrace sys_raw.P0 := by
    intro σ
    rw [reindexHamiltonian_syndromeProjector, reindexHamiltonian_P0,
      hilbertTrace_conjSiteOp, hilbertTrace_conjSiteOp]
    exact h_tr_le₀ σ
  exact satisfiesScalingTemp_of_reindexed_data
    sys₁ sys_raw Pi_safe₁ O_dec_Z₁ O_dec_X₁ V₁ U₁ E0 δ_0 δ_ch' δ_split g_LR
    hH0_eq hP0_eq h_wt_raw h_P0_ne_raw h_tr_le_raw hC_chk h_card_chk hL2
    hPi₁ hP0_Pi₁ hOZ_sa₁ hOZ_norm₁ hP0_OZ₁ hOX_sa₁ hOX_norm₁ hP0_OX₁
    hδ0_half hδ0_le hδ_ch_nonneg hδ_ch_le_one hδ_ch_nine
    h_ql₁ h_comm_P0₁_0 h_form_q₁_0 h_coh_Z₁_0 h_coh_X₁_0 h_1site₁_0 h_cube₁_ch

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  bdlBoxSide HasSafeDecodedLogicalObservables SatisfiesUnperturbedThermalAndKMSStability
  SatisfiesScalingTempPerturbativeThermalAndKMSStability HasZeroTempDressingBundle
  IndexedCommutingProjectorHamiltonian.IsGeometricallyLocal
  IndexedCommutingProjectorHamiltonian.reindex bdlInhomogeneousSystem
  reindexHamiltonian reindexPerturbation conjSiteOp clusterRawWeight bdlClusterStepBase
  dLocBDL equivCodeSlotBDL nChecksBDL equivStaticCSSCheckBDL memBDL safeSyndromeBDL

private lemma bdlInhomogeneousSystem_syndromeProjector_trace_le_P0 (k : ℕ)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :
    hilbertTrace ((bdlInhomogeneousSystem k).syndromeProjector σ) ≤
      hilbertTrace (bdlInhomogeneousSystem k).P0 := by
  by_cases h_nz : (bdlInhomogeneousSystem k).syndromeProjector σ = 0
  · rw [h_nz, hilbertTrace_zero_codeSlot]
    exact (isStarProjection_P0_and_hilbertTrace_nonneg (bdlInhomogeneousSystem k)).2
  · obtain ⟨p, hp, e_X, e_Z, h_eq⟩ := bdl_gibbs_realizable k σ h_nz
    rw [h_eq, bdl_gibbs_tr_eq k p hp e_X e_Z]

private lemma mem_syndromeProjector_trace_le_P0 (k : ℕ)
    (sys : IndexedCommutingProjectorHamiltonian 3 (bdlBoxSide k)
      (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))
      (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL))
    (h_sys : sys = bdlInhomogeneousSystem k)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :
    hilbertTrace (sys.syndromeProjector σ) ≤ hilbertTrace sys.P0 := by
  rw [h_sys]; exact bdlInhomogeneousSystem_syndromeProjector_trace_le_P0 k σ

lemma bdl_inhomogeneous_scaling_temp_stability_of_equiv
    {d_loc : ℕ} [NeZero d_loc] [Nonempty (Fin d_loc)]
    (e0 : CodeSlotConfig qCodeBDL ≃ Fin d_loc)
    {N_checks : ℕ → ℕ}
    (e_chk : ∀ k : ℕ, StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin (N_checks k))
    (mem : ∀ k : ℕ, Inhomogeneous3DMemoryRealization (bdlBoxSide k)
        qCodeBDL r0BDL mMaxBDL cStarBDL (collarConstRCABDL : ℝ)
        betaCritBDL cFBDL etaBDL cMemBDL)
    (h_sys_eq : ∀ k : ℕ, (mem k).sys = bdlInhomogeneousSystem k)
    (h_mem_spec : ∀ k : ℕ,
      (mem k).D_field = bdlLocalDescriptor k ∧
      (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k) (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
          (mem k).Pi_safe * (W.term r A * (mem k).O_dec_Z - (mem k).O_dec_Z * W.term r A) *
            (mem k).Pi_safe = 0 ∧
          (mem k).Pi_safe * (W.term r A * (mem k).O_dec_X - (mem k).O_dec_X * W.term r A) *
            (mem k).Pi_safe = 0))
    (h_obs_spec : ∀ k : ℕ,
      HasSafeDecodedLogicalObservables (N_checks := N_checks k)
        ((mem k).sys.reindex (e_chk k)) (mem k).Pi_safe (mem k).O_dec_Z (mem k).O_dec_X
        (37 * bdlLambda ^ k))
    (f : ℕ → ℝ) (R_bath : ℕ) (hf : IsSuperpolynomialDecay f) (hR_bath : 1 ≤ R_bath) :
    ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
      0 < J_0 ∧ IsSuperpolynomialDecay δ_split ∧ IsSuperpolynomialDecay g_LR ∧
      ∀ (k : ℕ), k_0 ≤ k → ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
        ∀ (V₁ : 𝒱_pert[bdlBoxSide k, Fin d_loc]),
          V₁.SatisfiesDecayBound J f →
          SatisfiesScalingTempPerturbativeThermalAndKMSStability
            (reindexHamiltonian (fun _ => e0) ((mem k).sys.reindex (e_chk k)))
            (conjSiteOp (fun _ => e0) (mem k).Pi_safe)
            (conjSiteOp (fun _ => e0) (mem k).O_dec_Z)
            (conjSiteOp (fun _ => e0) (mem k).O_dec_X)
            V₁ R_bath (4 * ((qCodeBDL + 2 * mMaxBDL : ℕ) : ℝ) + 4) (1 / 4)
            (δ_split (bdlBoxSide k)) g_LR := by
  rcases bdl_inhomogeneous_zero_temp_dressing_bundle_exists mem h_mem_spec f hf with
    ⟨J_0, k_0_qac, δ_0, g_LR, hJ0_pos, hδ0_super, hg_LR, h_bundle_k⟩
  let C_const : ℝ := 18 * ((R_bath ^ 3 : ℕ) : ℝ) *
    ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ)
  have hC_nn : 0 ≤ C_const := by positivity
  have h_resc := isSuperpolynomialDecay_cube_rescaled_profile one_le_bdlLambda hC_nn hδ0_super hg_LR
  let δ_split : ℕ → ℝ := fun n =>
    max (9 * δ_0 n) (C_const * g_LR (Nat.sqrt n / (bdlLambda ^ 2)))
  rcases exists_atTop_le_half_of_isSuperpolynomialDecay h_resc.1 with ⟨R_0, hR_0⟩
  rcases exists_k_pad_le_37_mul_bdlLambda_pow R_bath with ⟨k_pad, hk_pad⟩
  refine ⟨J_0, max (max k_0_qac R_0) k_pad, δ_split, g_LR, hJ0_pos, h_resc.1, hg_LR,
    fun k hk J hJ_nn hJ_le V₁ hV₁_dec => ?_⟩
  have hk_qac : k_0_qac ≤ k := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hk)
  have hk_R0 : R_0 ≤ k := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hk)
  have hk_p : k_pad ≤ k := le_trans (le_max_right _ _) hk
  have hδ_split_half : δ_split (bdlBoxSide k) ≤ 1 / 2 :=
    hR_0 (bdlBoxSide k) (bdlBoxSide_ge_of_le hk_R0)
  have hδ0_nn : 0 ≤ δ_0 (bdlBoxSide k) := hδ0_super.1 (bdlBoxSide k)
  have hδ0_le : δ_0 (bdlBoxSide k) ≤ δ_split (bdlBoxSide k) :=
    le_trans (by linarith) (le_max_left _ _)
  have hδ0_half : δ_0 (bdlBoxSide k) ≤ 1 / 2 := le_trans hδ0_le hδ_split_half
  have h_sqrt_k : Nat.sqrt (bdlBoxSide k) / (bdlLambda ^ 2) = bdlLambda ^ k := by
    rw [bdlBoxSide_eq_bdlLambda_pow k]; exact h_resc.2 k
  have hg_nn : 0 ≤ g_LR (bdlLambda ^ k) := hg_LR.1 (bdlLambda ^ k)
  let δ_ch' : ℝ := 2 * ((R_bath ^ 3 : ℕ) : ℝ) *
    (((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) * g_LR (bdlLambda ^ k))
  have hδ_ch_nn : 0 ≤ δ_ch' := by dsimp only [δ_ch']; positivity
  have hδ_ch_nine : 9 * δ_ch' ≤ δ_split (bdlBoxSide k) := by
    have h_eq : 9 * δ_ch' = C_const * g_LR (bdlLambda ^ k) := by
      dsimp only [δ_ch', C_const]; ring
    rw [h_eq]; dsimp only [δ_split]; rw [h_sqrt_k]; exact le_max_right _ _
  have hδ_ch_le_one : δ_ch' ≤ 1 := by linarith
  have hV₀_dec :
      (reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => e0.symm) V₁).SatisfiesDecayBound J f :=
    satisfiesDecayBound_reindexPerturbation (fun _ => e0.symm) V₁ hV₁_dec
  exact satisfiesScalingTempPerturbativeThermalAndKMSStability_of_dressing_bundle
    e0 (e_chk k) (mem k) V₁
    (reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => e0.symm) V₁) rfl
    c_chk_BDL_ge_one (card_staticCSSCheckIdx_le (bdlBoxSide k))
    (bdlBoxSide_ge_two k) hδ0_half hδ0_le hδ_ch_nn hδ_ch_le_one hδ_ch_nine
    (mem_syndromeProjector_trace_le_P0 k (mem k).sys (h_sys_eq k))
    (h_bundle_k k hk_qac J hJ_nn hJ_le
      (reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => e0.symm) V₁) hV₀_dec)
    (fun U₀ hU r hr W hW M_W hM_W =>
      dressed_cube_commutator_le_of_hasSafeDecodedLogicalObservables
        ((mem k).sys.reindex (e_chk k)) (mem k).Pi_safe (mem k).O_dec_Z (mem k).O_dec_X
        (h_obs_spec k) hg_nn (hk_pad k hk_p) U₀ hU r hr W hW M_W hM_W)

/-- **Master Part II, Theorem 6.4 (`thm:main-B`) Synthesis (`log_cooling_perturbative_thermal_stability_main`)**:
    Establishes QAC-dressed cryogenic Gibbs concentration and KMS-dissipative memory lifetime
    for all superpolynomial decay profiles `f` and finite bath cube ranges `R_bath ≥ 1`. -/
theorem log_cooling_perturbative_thermal_stability_main :
    ∃ (d_loc r_0 w_0 Λ_scale : ℕ)
      (β_c c_F C_scale c_F_pert η : ℝ)
      (L N_checks : ℕ → ℕ)
      (_ : ∀ k : ℕ, NeZero (L k))
      (_ : NeZero d_loc)
      (sys : ∀ k : ℕ, ℋ_CP[L k, Fin d_loc, N_checks k])
      (Pi_safe O_dec_Z O_dec_X : ∀ k : ℕ, ℬ[L k, Fin d_loc]),
      2 ≤ d_loc ∧ 1 ≤ r_0 ∧ 1 ≤ w_0 ∧ 2 ≤ Λ_scale ∧
      0 < β_c ∧ 0 < c_F ∧ 0 < C_scale ∧ 0 < c_F_pert ∧ 0 < η ∧
      (∀ k : ℕ, L k = Λ_scale ^ (2 * k + 4)) ∧
      IsStrictlyIncreasingBoxSequence L ∧
      (∀ k : ℕ,
        (sys k).IsGeometricallyLocal r_0 w_0 ∧
        (∀ i : Fin (N_checks k), (sys k).weight i = 1) ∧
        HasSafeDecodedLogicalObservables (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
          (37 * Λ_scale ^ k) ∧
        SatisfiesUnperturbedThermalAndKMSStability (sys k)
          (Pi_safe k) (O_dec_Z k) (O_dec_X k) (37 * Λ_scale ^ k) w_0 β_c c_F η) ∧
      (∀ (f : ℕ → ℝ) (R_bath : ℕ),
        IsSuperpolynomialDecay f →
        1 ≤ R_bath →
        ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
          0 < J_0 ∧
          IsSuperpolynomialDecay δ_split ∧
          IsSuperpolynomialDecay g_LR ∧
          ∀ (k : ℕ), k_0 ≤ k →
            ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
              ∀ (V : 𝒱_pert[L k, Fin d_loc]),
                V.SatisfiesDecayBound J f →
                SatisfiesScalingTempPerturbativeThermalAndKMSStability
                  (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
                  V R_bath C_scale c_F_pert (δ_split (L k)) g_LR) := by
  refine ⟨dLocBDL, r0BDL, (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL), bdlLambda,
    betaCritBDL, cFBDL, 4 * ((qCodeBDL + 2 * mMaxBDL : ℕ) : ℝ) + 4, (1 / 4 : ℝ), etaBDL,
    bdlBoxSide, nChecksBDL, inferInstance, inferInstance,
    fun k => reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)),
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).Pi_safe,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_Z,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_X,
    two_le_d_loc_bdl, r_0_BDL_ge_one, w_0_BDL_ge_one, two_le_bdlLambda,
    beta_crit_bdl_pos, c_f_bdl_pos, c_scale_BDL_pos, c_F_pert_BDL_pos, eta_bdl_pos,
    bdlBoxSide_eq_bdlLambda_pow,
    fun k => (bdlBoxSide_scaling_and_strictMono k).2, ?_, ?_⟩
  · intro k
    rcases memBDL_spec k with ⟨h_sys_eq, h_Pi_eq, _hD, _h_fw_macro, h_obs₀⟩
    have h_geom : (reindexHamiltonian (fun _ => equivCodeSlotBDL)
        ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))).IsGeometricallyLocal
        r0BDL ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) := by
      refine reindexHamiltonian_isGeometricallyLocal equivCodeSlotBDL
        ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)) ?_
      rw [h_sys_eq]; exact isGeometricallyLocal_bdlInhomogeneousSystem_reindex k (equivStaticCSSCheckBDL k)
    have h_unit : ∀ i : Fin (nChecksBDL k),
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))).weight i = 1 := by
      intro i
      rw [reindexHamiltonian_reindex_weight equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memBDL k).sys i,
        ((memBDL k).h_sys_checks ((equivStaticCSSCheckBDL k).symm i)).2.2]
    have h_obs_k : HasSafeDecodedLogicalObservables
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_X)
        (37 * bdlLambda ^ k) :=
      hasSafeDecodedLogicalObservables_reindexHamiltonian equivCodeSlotBDL
        ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))
        (memBDL k).Pi_safe (memBDL k).O_dec_Z (memBDL k).O_dec_X h_obs₀
    have h_therm_k : SatisfiesUnperturbedThermalAndKMSStability
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_X)
        (37 * bdlLambda ^ k) ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL))
        betaCritBDL cFBDL etaBDL :=
      satisfiesUnperturbedThermalAndKMSStability_reindexHamiltonian
        equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memBDL k).sys (safeSyndromeBDL k)
        (memBDL k).Pi_safe (memBDL k).O_dec_Z (memBDL k).O_dec_X
        h_Pi_eq h_geom h_unit (four_mul_r0BDL_add_one_le_37_mul_pow k)
        (fun β hβ => ((memBDL k).h_unperturbed_thermal_and_kms_lifetime β hβ).1) h_obs_k
    exact ⟨h_geom, h_unit, h_obs_k, h_therm_k⟩
  · intro f R_bath hf hR_bath
    exact bdl_inhomogeneous_scaling_temp_stability_of_equiv
      equivCodeSlotBDL equivStaticCSSCheckBDL memBDL (fun k => (memBDL_spec k).1)
      (fun k => ⟨(memBDL_spec k).2.2.1, (memBDL_spec k).2.2.2.1⟩)
      (fun k => (memBDL_spec k).2.2.2.2) f R_bath hf hR_bath

end LogCoolingPerturbativeSynthesis
end
