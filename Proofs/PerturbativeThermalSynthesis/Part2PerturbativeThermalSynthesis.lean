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

import Proofs.PerturbativeThermalSynthesis.FixedTempPerturbativeGibbsSynthesis

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge
open PerturbedThermalBarrier
open Part1TwoAxisMemorySynthesis FixedTempPerturbativeGibbsSynthesis SpacetimeWorldlineKP

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Part2PerturbativeThermalSynthesis

/-!
# Uniform Fixed-Temperature Perturbative Gibbs and KMS Lifetime Synthesis

Defines `SatisfiesFixedTempWindowThermalAndKMSStability` and `SatisfiesFixedTempPerturbativeThermalAndKMSStability` in namespace `Part2PerturbativeThermalSynthesis` and proves `part2_fixed_temp_perturbative_thermal_and_kms_stability_main`. Synthesizes uniform fixed-temperature perturbative Gibbs stability, cryogenic dressed thermal stability, and stretched-exponential KMS-symmetric dissipative memory lifetime for the 3D three-layer welded quantum memory.

## References

* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.8 (`prop:diagonal-peeling`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.5 (`thm:main-D`)
* Part II, Section 7.1 (`subsec:conceptual-synthesis`)
-/

private lemma q_code_BDL_ge_one : 1 ≤ qCodeBDL := by decide
private lemma r_0_BDL_ge_one : 1 ≤ r0BDL := by decide
private lemma w_0_BDL_ge_one : 1 ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by decide

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

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  betaCritBDL _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor bdlClusterStepBase
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

/-! ## 1. Fixed-Temperature Perturbative Thermal and KMS Stability Predicates -/

/-- Internal fixed-temperature window thermal and KMS stability predicate (`β ∈ (β_c, β_max]`). -/
def SatisfiesFixedTempWindowThermalAndKMSStability
    {L N_checks : ℕ} [NeZero L] {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks]) (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0]) (R_imm R_bath : ℕ)
    (β_c β_max c_F_pert η δ_split : ℝ) (g_LR : ℕ → ℝ) : Prop :=
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
      β > β_c → β ≤ β_max →
      let ΔF_pert := c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η)
      let p_fail := Real.exp (-ΔF_pert)
      gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail ∧
      (∀ (L_diss : ℬ[L, Site0] →L[ℂ] ℬ[L, Site0]) (O_0 : ℬ[L, Site0]) (Γ_diss : ℝ),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsKMSSymmetricDissipativeGenerator H hH β L_diss →
        2 * kmsDissipativeForm H hH β L_diss O_0 O_0 ≤ Γ_diss →
        ∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSDissipativeODE H hH β L_diss O_0 O_t t →
          opKMSNorm H hH β (O_t t - O_0) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ))) Γ_diss t) ∧
      (∀ (bath : Finset ℬ_bath[L, Site0]) (O_0 : ℬ[L, Site0]),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsCubeRangeBath 3 L R_imm bath →
        (IsAdjointSymmetricBath bath →
          ∀ t : ℝ, 0 ≤ t →
            SatisfiesKMSLindbladODE H hH β bath O_0
              (fun s => opKMSLindbladSemigroup H hH β bath s O_0) t) ∧
        (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSLindbladODE H hH β bath O_0 O_t t →
          opKMSNorm H hH β (O_t t - O_0) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ)))
              (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
              t)))

/-- **Fixed-Temperature and Logarithmic-Cooling Perturbative Full-Spectrum,
    Unpinched Gibbs Failure Probability, and KMS Dissipative Dynamical Memory Lifetime Stability
    (`SatisfiesFixedTempPerturbativeThermalAndKMSStability`)**
    (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`) and Theorem 6.5 (`thm:main-D`)). -/
def SatisfiesFixedTempPerturbativeThermalAndKMSStability
    {L N_checks : ℕ} [NeZero L] {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks]) (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0]) (R_imm R_bath : ℕ)
    (β_c β_max c_F_pert C_scale c_F_dress η δ_split : ℝ) (g_LR : ℕ → ℝ) : Prop :=
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
      β > β_c → β ≤ β_max →
      let ΔF_pert := c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η)
      let p_fail := Real.exp (-ΔF_pert)
      gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail ∧
      (∀ (L_diss : ℬ[L, Site0] →L[ℂ] ℬ[L, Site0]) (O_0 : ℬ[L, Site0]) (Γ_diss : ℝ),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsKMSSymmetricDissipativeGenerator H hH β L_diss →
        2 * kmsDissipativeForm H hH β L_diss O_0 O_0 ≤ Γ_diss →
        ∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSDissipativeODE H hH β L_diss O_0 O_t t →
          opKMSNorm H hH β (O_t t - O_0) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ))) Γ_diss t) ∧
      (∀ (bath : Finset ℬ_bath[L, Site0]) (O_0 : ℬ[L, Site0]),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        IsCubeRangeBath 3 L R_imm bath →
        (IsAdjointSymmetricBath bath →
          ∀ t : ℝ, 0 ≤ t →
            SatisfiesKMSLindbladODE H hH β bath O_0
              (fun s => opKMSLindbladSemigroup H hH β bath s O_0) t) ∧
        (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
          0 ≤ t →
          SatisfiesKMSLindbladODE H hH β bath O_0 O_t t →
          opKMSNorm H hH β (O_t t - O_0) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ)))
              (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
              t))) ∧
    (∀ (β : ℝ) (hH : IsSelfAdjoint H),
      C_scale * Real.log (L : ℝ) ≤ β →
      let p_log := ((L ^ 3 : ℕ) : ℝ) * Real.exp (-c_F_dress * β) + δ_split
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

/-! ## 2. Bridge from Unpinched Gibbs Stability to KMS Dissipative Trajectory Stability -/

/-- **KMS Dissipative Trajectory Bridge (`satisfiesFixedTempPerturbativeThermalAndKMSStability_of_gibbsStability`,
    Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`) and Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`))**:
    Upgrades `SatisfiesFixedTempWindowGibbsStability` to
    `SatisfiesFixedTempWindowThermalAndKMSStability` whenever `V` satisfies
    `HasFiniteRangeBound V R_pert J` and all interaction terms `V.term r A` of range
    $1 \le r \le R_{\mathrm{pert}}$ satisfy the safe-subspace logical immunity
    $\Pi_{\mathrm{safe}} [V_{r,A}, O_0] \Pi_{\mathrm{safe}} = 0$. -/
theorem satisfiesFixedTempPerturbativeThermalAndKMSStability_of_gibbsStability
    {L N_checks R_imm R_bath : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0] [Nonempty Site0]
    (sys : ℋ_CP[L, Site0, N_checks]) (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (h_obs : HasSafeDecodedLogicalObservables sys Pi_safe O_dec_Z O_dec_X R_imm)
    (V : 𝒱_pert[L, Site0]) {R_pert : ℕ} {J : ℝ}
    (hV_range : HasFiniteRangeBound V R_pert J)
    (h_term_fw : ∀ r ∈ Finset.Icc 1 R_pert, ∀ A ∈ boxCubes 3 L r,
      Pi_safe * (V.term r A * O_dec_Z - O_dec_Z * V.term r A) * Pi_safe = 0 ∧
      Pi_safe * (V.term r A * O_dec_X - O_dec_X * V.term r A) * Pi_safe = 0)
    {β_c β_max c_F_pert η δ_split : ℝ} {g_LR : ℕ → ℝ}
    (h_gibbs : SatisfiesFixedTempWindowGibbsStability
      sys Pi_safe O_dec_Z O_dec_X V R_bath β_c β_max c_F_pert η δ_split g_LR) :
    SatisfiesFixedTempWindowThermalAndKMSStability
      sys Pi_safe O_dec_Z O_dec_X V R_imm R_bath β_c β_max c_F_pert η δ_split g_LR := by
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L Site0 x) := fun _ => inferInstance
  rcases h_gibbs with ⟨U_dress, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress, h_gibbs_prob⟩
  refine ⟨U_dress, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress, fun β hH hβ hβ_le => ?_⟩
  have h_pfail := h_gibbs_prob β hH hβ hβ_le
  rcases h_obs with ⟨_hP0_ne0, _hP0_ne1, _h_deg,
    hPi_proj, _hPi_ne0, _hPi_ne1, _hH0_Pi, _hP0_Pi,
    hOZ_sa, _hOZ_sq, hOZ_norm, hH0_OZ, _hP0_OZ, _hPi_OZ,
    hOX_sa, _hOX_sq, hOX_norm, hH0_OX, _hP0_OX, _hPi_OX,
    _h_chk, _h_anti, _hOZ_P0_ne, _hOX_P0_ne, _h_1s, h_cube⟩
  let H := sys.H0 + V.totalPerturbation
  let ΔF_pert := c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η)
  let p_fail := Real.exp (-ΔF_pert)
  have hp_nonneg : 0 ≤ p_fail := (Real.exp_pos _).le
  have hO_drift_and_diss : ∀ O_0 : ℬ[L, Site0], (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      IsSelfAdjoint O_0 ∧
      opKMSNorm H hH β (opCommutator H O_0) ≤
        2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ)) ∧
      (∀ bath : Finset ℬ_bath[L, Site0], IsCubeRangeBath 3 L R_imm bath →
        2 * kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) O_0 O_0 ≤
          16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))) := by
    intro O_0 hO0
    have hO_props : IsSelfAdjoint O_0 ∧ ‖O_0‖ ≤ 1 ∧ Commute sys.H0 O_0 ∧
        (∀ r ∈ Finset.Icc 1 R_pert, ∀ A ∈ boxCubes 3 L r,
          Pi_safe * (V.term r A * O_0 - O_0 * V.term r A) * Pi_safe = 0) ∧
        (∀ r ∈ Finset.Icc 1 (min R_imm L), ∀ A ∈ boxCubes 3 L r, ∀ M_A : ℬ[L, Site0],
          IsSupportedOn (UniformSite3D L Site0) A M_A →
          Pi_safe * (M_A * O_0 - O_0 * M_A) * Pi_safe = 0) := by
      rcases hO0 with rfl | rfl
      · exact ⟨hOZ_sa, hOZ_norm, hH0_OZ, fun r hr A hA => (h_term_fw r hr A hA).1,
          fun r hr A hA M_A hM => (h_cube r hr A hA M_A hM).1⟩
      · exact ⟨hOX_sa, hOX_norm, hH0_OX, fun r hr A hA => (h_term_fw r hr A hA).2,
          fun r hr A hA M_A hM => (h_cube r hr A hA M_A hM).2⟩
    rcases hO_props with ⟨hO_sa, hO_norm, hH0_O, hO_term_fw, hO_cube⟩
    have h_V_fw : Pi_safe * (V.totalPerturbation * O_0 - O_0 * V.totalPerturbation) * Pi_safe = 0 := by
      rw [pi_safe_commutator_V_tot_eq_tail_sum V O_0 Pi_safe R_pert (fun r hr A hA =>
        hO_term_fw r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
          by have := (Finset.mem_Icc.mp hr).2; omega⟩) A hA)]
      refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun A hA => ?_
      have hr' := Finset.mem_Icc.mp hr
      have hr_Icc : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨by omega, hr'.2⟩
      have h_term_zero : V.term r A = 0 := (hV_range r hr_Icc A hA).2 (by omega)
      simp [h_term_zero]
    have h_H_fw : Pi_safe * (H * O_0 - O_0 * H) * Pi_safe = 0 := by
      have h_comm_H_eq : H * O_0 - O_0 * H =
          V.totalPerturbation * O_0 - O_0 * V.totalPerturbation := by
        dsimp [H]; rw [add_mul, mul_add, hH0_O.eq, add_sub_add_left_eq_sub]
      rwa [h_comm_H_eq]
    have h_bare := bare_cubeRangeBath_drift_and_dissipativeForm_le
      H hH β Pi_safe O_0 hPi_proj hO_norm hp_nonneg h_pfail hO_cube
    exact ⟨hO_sa, h_bare.1 h_H_fw, h_bare.2⟩
  refine ⟨h_pfail, ?_, ?_⟩
  · intro L_diss O_0 Γ_diss hO0 hL_gen h_diss O_t t ht h_ode
    rcases hO_drift_and_diss O_0 hO0 with ⟨hO_sa, h_coh, _⟩
    have hΓ_coh : 0 ≤ 2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ)) := by positivity
    have h_form_nn : 0 ≤ kmsDissipativeForm H hH β L_diss O_0 O_0 := hL_gen.2.2 O_0
    have hΓ_diss : 0 ≤ Γ_diss := by linarith
    exact opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE
      H hH β L_diss hL_gen O_0 hO_sa hΓ_coh hΓ_diss ht h_coh h_diss h_ode
  · intro bath O_0 hO0 h_bath
    rcases hO_drift_and_diss O_0 hO0 with ⟨hO_sa, h_coh, h_bath_diss⟩
    refine ⟨fun h_adj t ht =>
      (satisfiesKMSLindbladODE_opKMSLindbladSemigroup H hH β bath h_adj O_0 hO_sa ht).2, ?_⟩
    intro O_t t ht h_ode
    have hL_gen : IsKMSSymmetricDissipativeGenerator H hH β
        (opKMSLindbladDissipator H hH β bath) :=
      isKMSSymmetricDissipativeGenerator_opKMSLindbladDissipator H hH β bath
        (fun ch hch => (h_bath ch hch).1)
    have h_diss := h_bath_diss bath h_bath
    have hΓ_coh : 0 ≤ 2 * ‖H * O_0 - O_0 * H‖ * (p_fail ^ (1 / 4 : ℝ)) := by positivity
    have h_form_nn : 0 ≤ kmsDissipativeForm H hH β (opKMSLindbladDissipator H hH β bath) O_0 O_0 :=
      hL_gen.2.2 O_0
    have hΓ_diss : 0 ≤ 16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by linarith
    have h_ode' := (satisfiesKMSLindbladODE_iff_satisfiesKMSDissipativeODE
      H hH β bath O_0 O_t t).mp h_ode
    exact opKMSNorm_sub_le_kmsDriftDirichletBound_of_dissipativeODE
      H hH β (opKMSLindbladDissipator H hH β bath) hL_gen O_0 hO_sa
      hΓ_coh hΓ_diss ht h_coh h_diss h_ode'

/-- Site-alphabet reindexing invariance of `gibbsFailureProb` for any self-adjoint Hamiltonian
    `H₀` and operator `P₀`. -/
lemma gibbsFailureProb_conjSiteOp
    {D L : ℕ} {Site0 Site1 : BoxD D L → Type}
    [∀ x, Fintype (Site0 x)] [∀ x, DecidableEq (Site0 x)] [∀ x, Nonempty (Site0 x)]
    [∀ x, Fintype (Site1 x)] [∀ x, DecidableEq (Site1 x)] [∀ x, Nonempty (Site1 x)]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (H₀ P₀ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0)
    (hH₀ : IsSelfAdjoint H₀) (hH₁ : IsSelfAdjoint (conjSiteOp e H₀)) (β : ℝ) :
    gibbsFailureProb (conjSiteOp e H₀) hH₁ β (conjSiteOp e P₀) =
      gibbsFailureProb H₀ hH₀ β P₀ := by
  let ψ_alt : ManyBodyConfig Site1 → ManyBodyHilbertSpace Site1 :=
    fun ω => uReindex (cfgEquiv e) (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))
  let E_alt : ManyBodyConfig Site1 → ℝ :=
    fun ω => opEigenvalues H₀ hH₀ ((cfgEquiv e).symm ω)
  have h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0 := by
    intro ω₁ ω₂; dsimp [ψ_alt]
    rw [inner_uReindex, opEigenbasis_orthonormal H₀ hH₀]
    simp only [(cfgEquiv e).symm.injective.eq_iff]
  have h_eig : ∀ ω, conjSiteOp e H₀ (ψ_alt ω) = (E_alt ω : ℂ) • ψ_alt ω := by
    intro ω
    change uReindex (cfgEquiv e) (H₀ (uReindex (cfgEquiv e).symm
      (uReindex (cfgEquiv e) (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))))) = _
    rw [uReindex_symm_apply, opEigenbasis_apply_H H₀ hH₀, map_smul]
  have hZ_eq : gibbsPartitionZ (opEigenvalues (conjSiteOp e H₀) hH₁) β =
      gibbsPartitionZ (opEigenvalues H₀ hH₀) β := by
    rw [perturbed_gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis
      (conjSiteOp e H₀) hH₁ ψ_alt E_alt h_onb h_eig β]
    exact (cfgEquiv e).symm.sum_comp (fun σ => Real.exp (-β * opEigenvalues H₀ hH₀ σ))
  have hTr_eq :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis (conjSiteOp e H₀) hH₁)
        (opEigenvalues (conjSiteOp e H₀) hH₁) β * conjSiteOp e P₀) =
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H₀ hH₀) (opEigenvalues H₀ hH₀) β * P₀) := by
    rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
      (conjSiteOp e H₀) hH₁ ψ_alt E_alt h_onb h_eig β (conjSiteOp e P₀),
      hilbertTrace_gibbsBoltzmannOp_mul_eq]
    have h_term : ∀ ω : ManyBodyConfig Site1,
        Real.exp (-β * E_alt ω) * RCLike.re (inner ℂ (ψ_alt ω) (conjSiteOp e P₀ (ψ_alt ω))) =
        Real.exp (-β * opEigenvalues H₀ hH₀ ((cfgEquiv e).symm ω)) *
          RCLike.re (inner ℂ (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))
            (P₀ (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω)))) := by
      intro ω
      have h_apply : conjSiteOp e P₀ (ψ_alt ω) =
          uReindex (cfgEquiv e) (P₀ (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))) := by
        change uReindex (cfgEquiv e) (P₀ (uReindex (cfgEquiv e).symm
          (uReindex (cfgEquiv e) (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))))) = _
        rw [uReindex_symm_apply]
      rw [h_apply]; dsimp [ψ_alt, E_alt]; rw [inner_uReindex]
    refine (Finset.sum_congr rfl fun ω _ => h_term ω).trans ?_
    exact (cfgEquiv e).symm.sum_comp (fun σ =>
      Real.exp (-β * opEigenvalues H₀ hH₀ σ) *
        RCLike.re (inner ℂ (opEigenbasis H₀ hH₀ σ) (P₀ (opEigenbasis H₀ hH₀ σ))))
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace,
    perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace, hZ_eq, hTr_eq]

/-- `HasFiniteRangeBound` is preserved under site-alphabet reindexing `reindexPerturbation`. -/
lemma hasFiniteRangeBound_reindexPerturbation
    {L : ℕ} {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Nonempty SiteA]
    [Fintype SiteB] [DecidableEq SiteB] [Nonempty SiteB]
    (e : ∀ x : Box3D L, UniformSite3D L SiteA x ≃ UniformSite3D L SiteB x)
    {V : 𝒱_pert[L, SiteA]} {R_pert : ℕ} {J : ℝ} (hV : HasFiniteRangeBound V R_pert J) :
    HasFiniteRangeBound (reindexPerturbation e V) R_pert J := by
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteA x) := fun _ => inferInstance
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteB x) := fun _ => inferInstance
  intro r hr A hA
  refine ⟨fun hr_le => ?_, fun hr_gt => ?_⟩
  · change ‖conjEuclidean (cfgEquiv e) (V.term r A)‖ ≤ J
    rw [norm_conjEuclidean]; exact (hV r hr A hA).1 hr_le
  · change conjEuclidean (cfgEquiv e) (V.term r A) = 0
    rw [(hV r hr A hA).2 hr_gt, conjEuclidean_zero]

/-- Transport of `SatisfiesFixedTempWindowGibbsStability` along a uniform site bijection
    `e0 : SiteA ≃ SiteB`. -/
lemma satisfiesFixedTempPerturbativeGibbsStability_reindexHamiltonian
    {L N_checks R_bath : ℕ} [NeZero L]
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Nonempty SiteA]
    [Fintype SiteB] [DecidableEq SiteB] [Nonempty SiteB]
    (e0 : SiteA ≃ SiteB) (sys₀ : ℋ_CP[L, SiteA, N_checks])
    (Pi_safe₀ O_dec_Z₀ O_dec_X₀ : ℬ[L, SiteA])
    (hOZ_norm : ‖O_dec_Z₀‖ ≤ 1) (hOZ_P0 : Commute sys₀.P0 O_dec_Z₀)
    (hOX_norm : ‖O_dec_X₀‖ ≤ 1) (hOX_P0 : Commute sys₀.P0 O_dec_X₀)
    (V₁ : 𝒱_pert[L, SiteB]) {β_c β_max c_F_pert η δ_split : ℝ} {g_LR : ℕ → ℝ}
    (h_gibbs₀ : SatisfiesFixedTempWindowGibbsStability
      sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀
      (reindexPerturbation (fun _ => e0.symm) V₁) R_bath β_c β_max c_F_pert η δ_split g_LR) :
    SatisfiesFixedTempWindowGibbsStability
      (reindexHamiltonian (fun _ => e0) sys₀)
      (conjSiteOp (fun _ => e0) Pi_safe₀)
      (conjSiteOp (fun _ => e0) O_dec_Z₀)
      (conjSiteOp (fun _ => e0) O_dec_X₀)
      V₁ R_bath β_c β_max c_F_pert η δ_split g_LR := by
  let e : ∀ _ : Box3D L, SiteA ≃ SiteB := fun _ => e0
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteA x) := fun _ => inferInstance
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteB x) := fun _ => inferInstance
  let e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA := fun _ => e0.symm
  have h_zero₀ : SatisfiesZeroTempPerturbativeMemoryStability
      sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀ (reindexPerturbation e_inv V₁) R_bath δ_split g_LR := by
    rcases h_gibbs₀ with ⟨U₀, E0, h1, h2, h3, h4, h5, _⟩
    exact ⟨U₀, E0, h1, h2, h3, h4, h5⟩
  have h_zero₁ := satisfiesZeroTempPerturbativeMemoryStability_reindexHamiltonian
    e0 sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀ hOZ_norm hOZ_P0 hOX_norm hOX_P0 V₁ h_zero₀
  rcases h_zero₁ with ⟨U₁, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress⟩
  rcases h_gibbs₀ with ⟨_, _, _, _, _, _, _, h_gibbs_prob₀⟩
  refine ⟨U₁, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress, fun β hH₁ hβ hβ_le => ?_⟩
  let H₀ := sys₀.H0 + (reindexPerturbation e_inv V₁).totalPerturbation
  let H₁ := (reindexHamiltonian e sys₀).H0 + V₁.totalPerturbation
  have h_cfg_inv : cfgEquiv e_inv = (cfgEquiv e).symm := by ext σ x; rfl
  have hV_conj : conjSiteOp e (reindexPerturbation e_inv V₁).totalPerturbation = V₁.totalPerturbation := by
    rw [reindexPerturbation_V_tot]; dsimp [conjSiteOp]
    rw [h_cfg_inv, conjEuclidean_conjEuclidean_symm]
  have hH₁_eq : H₁ = conjSiteOp e H₀ := by
    dsimp [H₁, H₀]; rw [reindexHamiltonian_H0, ← hV_conj]
  have hH₀_eq : H₀ = conjSiteOp e_inv H₁ := by
    rw [hH₁_eq]; dsimp [conjSiteOp]; rw [h_cfg_inv, conjEuclidean_symm_conjEuclidean]
  have hH₀ : IsSelfAdjoint H₀ := by
    rw [hH₀_eq]; exact conjEuclidean_isSelfAdjoint (cfgEquiv e_inv) hH₁
  have h_fail_conj : (1 : ℬ[L, SiteB]) - conjSiteOp e Pi_safe₀ = conjSiteOp e (1 - Pi_safe₀) := by
    rw [conjSiteOp_sub, conjSiteOp_one]
  have h_pfail_eq :
      gibbsFailureProb H₁ hH₁ β (1 - conjSiteOp e Pi_safe₀) =
      gibbsFailureProb H₀ hH₀ β (1 - Pi_safe₀) := by
    have hH₁' : IsSelfAdjoint (conjSiteOp e H₀) := hH₁_eq ▸ hH₁
    have h_congr : gibbsFailureProb H₁ hH₁ β (1 - conjSiteOp e Pi_safe₀) =
        gibbsFailureProb (conjSiteOp e H₀) hH₁' β (conjSiteOp e (1 - Pi_safe₀)) := by
      rw [gibbsFailureProb_congr_H0 hH₁_eq hH₁ hH₁' β (1 - conjSiteOp e Pi_safe₀), h_fail_conj]
    rw [h_congr, gibbsFailureProb_conjSiteOp e H₀ (1 - Pi_safe₀) hH₀ hH₁' β]
  rw [h_pfail_eq]
  exact h_gibbs_prob₀ β hH₀ hβ hβ_le

/-- Conjugating a safe-subspace commutator immunity identity for `reindexPerturbation` along
    `e0 : SiteA ≃ SiteB`. -/
lemma reindexPerturbation_commutator_sandwich_eq_zero
    {L : ℕ} {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Fintype SiteB] [DecidableEq SiteB]
    (e0 : SiteA ≃ SiteB) (Pi₀ O₀ : ℬ[L, SiteA]) (V₁ : 𝒱_pert[L, SiteB])
    (r : ℕ) (A : Finset (Box3D L))
    (h0 : Pi₀ * ((reindexPerturbation (fun _ => e0.symm) V₁).term r A * O₀ -
      O₀ * (reindexPerturbation (fun _ => e0.symm) V₁).term r A) * Pi₀ = 0) :
    conjSiteOp (fun _ => e0) Pi₀ *
      (V₁.term r A * conjSiteOp (fun _ => e0) O₀ - conjSiteOp (fun _ => e0) O₀ * V₁.term r A) *
      conjSiteOp (fun _ => e0) Pi₀ = 0 := by
  let e : ∀ _ : Box3D L, SiteA ≃ SiteB := fun _ => e0
  let e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA := fun _ => e0.symm
  have h_cfg_inv : cfgEquiv e_inv = (cfgEquiv e).symm := by ext σ x; rfl
  have hT : conjEuclidean (cfgEquiv e) (conjEuclidean (cfgEquiv e_inv) (V₁.term r A)) = V₁.term r A := by
    rw [h_cfg_inv, conjEuclidean_conjEuclidean_symm]
  have h_congr := congrArg (conjEuclidean (cfgEquiv e)) h0
  dsimp [reindexPerturbation, conjSiteOp] at h_congr ⊢
  rw [conjEuclidean_zero, conjEuclidean_mul, conjEuclidean_mul, conjEuclidean_sub,
    conjEuclidean_mul, conjEuclidean_mul, hT] at h_congr
  exact h_congr

/-- Combines the fixed-temperature window bound (`SatisfiesFixedTempWindowGibbsStability`) with the
    logarithmic-cooling QAC-dressed bound (`SatisfiesScalingTempPerturbativeThermalAndKMSStability`)
    to establish `SatisfiesFixedTempPerturbativeThermalAndKMSStability`. -/
lemma satisfiesFixedTempPerturbativeThermalAndKMSStability_of_window_and_scaling
    {L N_checks R_imm R_bath_win R_bath : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0] [Nonempty Site0]
    (sys : ℋ_CP[L, Site0, N_checks]) (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (h_obs : HasSafeDecodedLogicalObservables sys Pi_safe O_dec_Z O_dec_X R_imm)
    (V : 𝒱_pert[L, Site0]) {R_pert : ℕ} {J : ℝ}
    (hV_range : HasFiniteRangeBound V R_pert J)
    (h_term_fw : ∀ r ∈ Finset.Icc 1 R_pert, ∀ A ∈ boxCubes 3 L r,
      Pi_safe * (V.term r A * O_dec_Z - O_dec_Z * V.term r A) * Pi_safe = 0 ∧
      Pi_safe * (V.term r A * O_dec_X - O_dec_X * V.term r A) * Pi_safe = 0)
    {β_c β_max c_F_pert C_scale c_F_dress η δ_split_win δ_split : ℝ}
    {g_LR_win g_LR : ℕ → ℝ}
    (h_win : SatisfiesFixedTempWindowGibbsStability
      sys Pi_safe O_dec_Z O_dec_X V R_bath_win β_c β_max c_F_pert η δ_split_win g_LR_win)
    (h_log : LogCoolingPerturbativeSynthesis.SatisfiesScalingTempPerturbativeThermalAndKMSStability
      sys Pi_safe O_dec_Z O_dec_X V R_bath C_scale c_F_dress δ_split g_LR) :
    SatisfiesFixedTempPerturbativeThermalAndKMSStability
      sys Pi_safe O_dec_Z O_dec_X V R_imm R_bath β_c β_max c_F_pert C_scale c_F_dress η δ_split g_LR := by
  have h_win_kms := satisfiesFixedTempPerturbativeThermalAndKMSStability_of_gibbsStability
    sys Pi_safe O_dec_Z O_dec_X h_obs V hV_range h_term_fw h_win
  rcases h_win_kms with ⟨_, _, _, _, _, _, _, h4⟩
  rcases h_log with ⟨U_dress, E0, h1, h2_1, h2_2, h2_3, h3, h5⟩
  exact ⟨U_dress, E0, h1, h2_1, h2_2, h2_3, h3, h4, h5⟩

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  bdlBoxSide HasSafeDecodedLogicalObservables SatisfiesUnperturbedThermalAndKMSStability
  SatisfiesZeroTempPerturbativeMemoryStability SatisfiesFixedTempWindowGibbsStability
  SatisfiesFixedTempWindowThermalAndKMSStability
  SatisfiesFixedTempPerturbativeGibbsStability
  SatisfiesFixedTempPerturbativeThermalAndKMSStability
  LogCoolingPerturbativeSynthesis.SatisfiesScalingTempPerturbativeThermalAndKMSStability
  HasFiniteRangeBound
  IndexedCommutingProjectorHamiltonian.IsGeometricallyLocal
  IndexedCommutingProjectorHamiltonian.reindex bdlInhomogeneousSystem
  reindexHamiltonian reindexPerturbation conjSiteOp clusterRawWeight bdlClusterStepBase
  betaCritBDL _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor
  dLocBDL equivCodeSlotBDL nChecksBDL equivStaticCSSCheckBDL
  memWitnessBDL safeSyndromeWitnessBDL witnessFamilyBDL

/-- **Uniform Fixed-Temperature Perturbative Gibbs and KMS Lifetime Synthesis
    (`part2_fixed_temp_perturbative_thermal_and_kms_stability_main`)**
    (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`) and Theorem 6.5 (`thm:main-D`)). -/
theorem part2_fixed_temp_perturbative_thermal_and_kms_stability_main :
    ∃ (d_loc r_0 w_0 Λ_scale : ℕ)
      (β_c c_F c_F_pert C_scale c_F_dress η : ℝ)
      (L N_checks : ℕ → ℕ)
      (_ : ∀ k : ℕ, NeZero (L k))
      (_ : NeZero d_loc)
      (sys : ∀ k : ℕ, ℋ_CP[L k, Fin d_loc, N_checks k])
      (Pi_safe O_dec_Z O_dec_X : ∀ k : ℕ, ℬ[L k, Fin d_loc]),
      2 ≤ d_loc ∧ 1 ≤ r_0 ∧ 1 ≤ w_0 ∧ 2 ≤ Λ_scale ∧
      0 < β_c ∧ 0 < c_F ∧ 0 < c_F_pert ∧ 0 < C_scale ∧ 0 < c_F_dress ∧ 0 < η ∧
      (∀ k : ℕ, L k = Λ_scale ^ (2 * k + 4)) ∧
      IsStrictlyIncreasingBoxSequence L ∧
      (∀ k : ℕ,
        (sys k).IsGeometricallyLocal r_0 w_0 ∧
        (∀ i : Fin (N_checks k), (sys k).weight i = 1) ∧
        HasSafeDecodedLogicalObservables (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
          (37 * Λ_scale ^ k) ∧
        SatisfiesUnperturbedThermalAndKMSStability (sys k)
          (Pi_safe k) (O_dec_Z k) (O_dec_X k) (37 * Λ_scale ^ k) w_0 β_c c_F η) ∧
      (∀ (R_pert R_bath : ℕ) (β_max : ℝ),
        1 ≤ R_pert →
        1 ≤ R_bath →
        β_c < β_max →
        ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
          0 < J_0 ∧
          IsSuperpolynomialDecay δ_split ∧
          IsSuperpolynomialDecay g_LR ∧
          ∀ (k : ℕ), k_0 ≤ k →
            ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
              ∀ (V : 𝒱_pert[L k, Fin d_loc]),
                HasFiniteRangeBound V R_pert J →
                SatisfiesFixedTempPerturbativeThermalAndKMSStability
                  (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
                  V (37 * Λ_scale ^ k) R_bath
                  β_c β_max c_F_pert C_scale c_F_dress η (δ_split (L k)) g_LR) := by
  have h_ft_ex := bdl_inhomogeneous_fixed_temp_gibbs_stability_codeSlot_of_equiv
    equivStaticCSSCheckBDL memWitnessBDL memWitnessBDL_mem_spec memWitnessBDL_obs_spec
    safeSyndromeWitnessBDL witnessFamilyBDL memWitnessBDL_witness_pkg
  have h_ft_spec := h_ft_ex.choose_spec
  have h_obs₁ : ∀ k : ℕ,
      HasSafeDecodedLogicalObservables
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X)
        (37 * bdlLambda ^ k) :=
    fun k => hasSafeDecodedLogicalObservables_reindexHamiltonian equivCodeSlotBDL
      ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))
      (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
      (memWitnessBDL_obs_spec k)
  refine ⟨dLocBDL, r0BDL, (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL), bdlLambda,
    betaCritBDL, cFBDL, h_ft_ex.choose, 4 * ((qCodeBDL + 2 * mMaxBDL : ℕ) : ℝ) + 4, (1 / 4 : ℝ),
    etaBDL, bdlBoxSide, nChecksBDL, inferInstance, inferInstance,
    fun k => reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)),
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X,
    two_le_d_loc_bdl, r_0_BDL_ge_one, w_0_BDL_ge_one, two_le_bdlLambda,
    beta_crit_bdl_pos, c_f_bdl_pos, h_ft_spec.1, LogCoolingPerturbativeSynthesis.c_scale_BDL_pos,
    LogCoolingPerturbativeSynthesis.c_F_pert_BDL_pos, eta_bdl_pos,
    bdlBoxSide_eq_bdlLambda_pow,
    fun k => (bdlBoxSide_scaling_and_strictMono k).2, ?_, ?_⟩
  · intro k
    rcases memWitnessBDL_spec k with ⟨h_sys_eq, h_Pi_eq, _hD, _h_fw_macro, _h_obs₀⟩
    have h_geom : (reindexHamiltonian (fun _ => equivCodeSlotBDL)
        ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))).IsGeometricallyLocal
        r0BDL ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) := by
      refine reindexHamiltonian_isGeometricallyLocal equivCodeSlotBDL
        ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)) ?_
      rw [h_sys_eq]; exact isGeometricallyLocal_bdlInhomogeneousSystem_reindex k (equivStaticCSSCheckBDL k)
    have h_unit : ∀ i : Fin (nChecksBDL k),
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))).weight i = 1 := by
      intro i
      rw [reindexHamiltonian_reindex_weight equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memWitnessBDL k).sys i,
        ((memWitnessBDL k).h_sys_checks ((equivStaticCSSCheckBDL k).symm i)).2.2]
    have h_therm_k : SatisfiesUnperturbedThermalAndKMSStability
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X)
        (37 * bdlLambda ^ k) ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL))
        betaCritBDL cFBDL etaBDL :=
      satisfiesUnperturbedThermalAndKMSStability_reindexHamiltonian
        equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memWitnessBDL k).sys (safeSyndromeWitnessBDL k)
        (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
        h_Pi_eq h_geom h_unit (four_mul_r0BDL_add_one_le_37_mul_pow k)
        (fun β hβ => ((memWitnessBDL k).h_unperturbed_thermal_and_kms_lifetime β hβ).1) (h_obs₁ k)
    exact ⟨h_geom, h_unit, h_obs₁ k, h_therm_k⟩
  · intro R_pert R_bath β_max hR_pert hR_bath hβ_max
    have h_fix_ex := h_ft_spec.2 R_pert β_max hR_pert hβ_max
    have h_fix1 := h_fix_ex.choose_spec
    have h_fix2 := h_fix1.choose_spec
    have h_fix3 := h_fix2.choose_spec
    have h_fix4 := h_fix3.choose_spec
    have h_log_ex := LogCoolingPerturbativeSynthesis.bdl_inhomogeneous_scaling_temp_stability_of_equiv
      equivCodeSlotBDL equivStaticCSSCheckBDL memWitnessBDL (fun k => (memWitnessBDL_spec k).1)
      memWitnessBDL_mem_spec memWitnessBDL_obs_spec
      (finiteRangeDecayProfile R_pert) R_bath
      (isSuperpolynomialDecay_finiteRangeDecayProfile R_pert) hR_bath
    have h_log1 := h_log_ex.choose_spec
    have h_log2 := h_log1.choose_spec
    have h_log3 := h_log2.choose_spec
    have h_log4 := h_log3.choose_spec
    refine ⟨min h_fix_ex.choose h_log_ex.choose, max h_fix1.choose h_log1.choose,
      h_log2.choose, h_log3.choose,
      lt_min h_fix4.1 h_log4.1, h_log4.2.1, h_log4.2.2.1,
      fun k hk J hJ_nn hJ_le V₁ hV₁_range => ?_⟩
    have hk_fix : h_fix1.choose ≤ k := (le_max_left h_fix1.choose h_log1.choose).trans hk
    have hk_log : h_log1.choose ≤ k := (le_max_right h_fix1.choose h_log1.choose).trans hk
    have hJ_fix : J ≤ h_fix_ex.choose := hJ_le.trans (min_le_left h_fix_ex.choose h_log_ex.choose)
    have hJ_log : J ≤ h_log_ex.choose := hJ_le.trans (min_le_right h_fix_ex.choose h_log_ex.choose)
    have hV₀_range : HasFiniteRangeBound
        (reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => equivCodeSlotBDL.symm) V₁) R_pert J :=
      hasFiniteRangeBound_reindexPerturbation (fun _ => equivCodeSlotBDL.symm) hV₁_range
    have h_gibbs₀ := h_fix4.2.2.2.2 k hk_fix J hJ_nn hJ_fix
      (reindexPerturbation (fun _ => equivCodeSlotBDL.symm) V₁) hV₀_range
    have hP0_sa : IsSelfAdjoint (memWitnessBDL k).sys.P0 := (memWitnessBDL k).sys.isStarProjection_P0.isSelfAdjoint
    have hOZ := (memWitnessBDL k).h_decoder_props.2.1; have hOX := (memWitnessBDL k).h_decoder_props.2.2.1
    have hZ := (memWitnessBDL k).h_logical_pair.2.1; have hX := (memWitnessBDL k).h_logical_pair.2.2.1
    have hP0_OZ : Commute ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)).P0 (memWitnessBDL k).O_dec_Z := by
      rw [(memWitnessBDL k).sys.reindex_P0 (equivStaticCSSCheckBDL k)]; exact commute_P0_of_mul_P0_eq hP0_sa hOZ.1 hZ.1 hZ.2.2.2 hOZ.2.2.2.2.1
    have hP0_OX : Commute ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)).P0 (memWitnessBDL k).O_dec_X := by
      rw [(memWitnessBDL k).sys.reindex_P0 (equivStaticCSSCheckBDL k)]; exact commute_P0_of_mul_P0_eq hP0_sa hOX.1 hX.1 hX.2.2.2 hOX.2.2.2.2.1
    have h_gibbs₁ : SatisfiesFixedTempWindowGibbsStability
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X)
        V₁ 1 betaCritBDL β_max h_ft_ex.choose etaBDL (h_fix2.choose (bdlBoxSide k)) h_fix3.choose :=
      satisfiesFixedTempPerturbativeGibbsStability_reindexHamiltonian
        equivCodeSlotBDL ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))
        (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
        hOZ.2.2.1 hP0_OZ hOX.2.2.1 hP0_OX V₁ h_gibbs₀
    have h_term_fw₁ : ∀ r ∈ Finset.Icc 1 R_pert, ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
        conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe *
          (V₁.term r A * conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z -
            conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z * V₁.term r A) *
          conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe = 0 ∧
        conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe *
          (V₁.term r A * conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X -
            conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X * V₁.term r A) *
          conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe = 0 := by
      intro r hr A hA
      have hr_macro : r ∈ Finset.Icc 1 (bdlLambda ^ k) :=
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
          (Finset.mem_Icc.mp hr).2.trans (h_fix4.2.1.trans (Nat.pow_le_pow_right bdlLambda_pos hk_fix))⟩
      have h_fw₀ := (memWitnessBDL_spec k).2.2.2.1 (reindexPerturbation (fun _ => equivCodeSlotBDL.symm) V₁) r hr_macro A hA
      exact ⟨reindexPerturbation_commutator_sandwich_eq_zero equivCodeSlotBDL (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z V₁ r A h_fw₀.1,
        reindexPerturbation_commutator_sandwich_eq_zero equivCodeSlotBDL (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_X V₁ r A h_fw₀.2⟩
    have hV₁_dec : V₁.SatisfiesDecayBound J (finiteRangeDecayProfile R_pert) :=
      satisfiesDecayBound_of_hasFiniteRangeBound hJ_nn hV₁_range
    have h_log₁ := h_log4.2.2.2 k hk_log J hJ_nn hJ_log V₁ hV₁_dec
    exact satisfiesFixedTempPerturbativeThermalAndKMSStability_of_window_and_scaling
      (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
      (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe)
      (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z)
      (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X)
      (h_obs₁ k) V₁ hV₁_range h_term_fw₁ h_gibbs₁ h_log₁

end Part2PerturbativeThermalSynthesis

end
