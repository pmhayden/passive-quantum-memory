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

import Defs.BoxLattice
import Defs.ManyBodyHilbert
import Defs.LocalHamiltonian
import Defs.KMSAndGibbs
import Defs.F2ChainAndCSS
import Defs.WeylPauli
import Defs.LocalCSSDescriptor
import Defs.SuperpolyDecay
import Defs.FlowAndFilter
import Defs.BHMStability
import Defs.PolymerGas
import Defs.SafeSubspaceAndKMS
import Defs.ContractionAndHPL
import Defs.RescaledRCA
import Defs.BDLParamsAndSeed
import Defs.BDLSubstitutionCode
import Proofs.StaticDescriptorLift
import Proofs.F2TQOToOperatorTQO
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.HastingsKomaLightCone.QACGeneratorScalarInstances
import Proofs.CenteredBallBHM.BaseBHMFormAndBootstrapBridge
import Proofs.DressedSafeSubspace.SectorFilteredAndDressedBHM
import Proofs.DressedSyndromeGibbs.DressedGibbsFailureBridge
import Proofs.DressedThermalDuhamel.PerturbedKMSBallImmunitySynthesis
import Proofs.InhomogeneousPeierls.InhomogeneousPeierlsMain

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap PerturbedThermalBarrier

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Cubic-Grid Realization of the Three-Layer Welded CSS Hierarchy

Instantiates the spatially inhomogeneous cubic-lattice CSS Hamiltonian from the level-k welded-code descriptor field, proving strict box-side growth, collar-scale compatibility, bare logical anticommutation, Peierls Gibbs suppression, and unperturbed KMS-Lindblad lifetime bounds.

## References

* Part I, Section 2 (`sec:bdl-construction`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 3 (`sec:linear-tqo2-proof`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Balasubramanian, Davydova, and Lin (2026)
-/

/-! ## 1. Elementary BDL Box Scaling, Check Support & Free-Energy Barrier Helpers -/

/-- Elementary scaling properties of the open-box side length
    `bdlBoxSide k = b_BDL ^ (bdlHierarchySteps k)`. -/
theorem bdlBoxSide_scaling_and_strictMono (k : ℕ) :
    bdlBoxSide k = bBDL ^ (bdlHierarchySteps k) ∧
    k + 2 ≤ bdlBoxSide k ∧
    bdlBoxSide k < bdlBoxSide (k + 1) := by
  refine ⟨rfl, ?_, ?_⟩
  · have h1 : k + 2 ≤ bdlHierarchySteps k := by dsimp [bdlHierarchySteps]; omega
    have h2 : bdlHierarchySteps k ≤ 2 ^ (bdlHierarchySteps k) := Nat.le_of_lt Nat.lt_two_pow_self
    have h3 : 2 ^ (bdlHierarchySteps k) ≤ bBDL ^ (bdlHierarchySteps k) :=
      Nat.pow_le_pow_left two_le_b_bdl (bdlHierarchySteps k)
    exact le_trans h1 (le_trans h2 h3)
  · dsimp [bdlBoxSide, bdlHierarchySteps]
    have hb : 1 < bBDL := lt_of_lt_of_le (by decide : 1 < 2) two_le_b_bdl
    exact Nat.pow_lt_pow_right hb (by omega)

lemma two_mul_collar_const_mul_c_star_bdl_lt_one : 2 * (collarConstRCABDL : ℝ) * cStarBDL < 1 := by
  dsimp [collarConstRCABDL, cStarBDL, bBDL, bdlLambda]
  norm_num

/-- Every elementary check of `staticCSSCheckSupport D_field idx` is supported in a radius-`r0BDL`
    box ball and has unit weight $w_i = 1 \ge 1$. -/
lemma staticCSSCheckSupport_subset_boxBall_and_weight_ge_one {L : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor qCodeBDL r0BDL mMaxBDL)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig qCodeBDL))
      (StaticCSSCheckIdx L qCodeBDL mMaxBDL))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧
      sys.weight idx = 1) :
    (∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
      ∃ v : Box3D L, sys.support idx ⊆ boxBall v r0BDL) ∧
    (∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL, 1 ≤ sys.weight idx) := by
  refine ⟨fun idx => ?_, fun idx => ?_⟩
  · rw [(h_sys_checks idx).2.1]
    rcases idx with ⟨v, _⟩ | (⟨v, _⟩ | ⟨v, _⟩)
    · refine ⟨v, ?_⟩
      dsimp [staticCSSCheckSupport]
      rw [Finset.singleton_subset_iff]
      simp [boxBall, boxDist, coordDist_self]
    · exact ⟨v, Finset.Subset.refl _⟩
    · exact ⟨v, Finset.Subset.refl _⟩
  · rw [(h_sys_checks idx).2.2]

/-- Dressed vs. bare thermal free-energy barrier comparison for $\beta > \frac{4}{3}\beta_c$. -/
theorem dressedThermalFreeEnergyBarrier_le_bare_and_exp_le_inhomogeneous
    {c_F c_F_pert β β_c N_Q η C_0 : ℝ}
    (hβ_c : 0 < β_c) (hc_pos : 0 < c_F_pert) (hc_le : c_F_pert ≤ c_F)
    (hN_Q : 0 ≤ N_Q) (hC_0 : 0 ≤ C_0) (hβ : β > (4 / 3 : ℝ) * β_c) :
    β > β_c ∧
    dressedThermalFreeEnergyBarrier c_F_pert β β_c N_Q η C_0 ≤
      c_F * (β - β_c) * (N_Q ^ η) ∧
    Real.exp (- (c_F * (β - β_c) * (N_Q ^ η))) ≤
      Real.exp (- dressedThermalFreeEnergyBarrier c_F_pert β β_c N_Q η C_0) := by
  have hβ_gt : β > β_c := by linarith
  have h_three_fourth : 0 < (3 / 4 : ℝ) * β - β_c := by linarith
  have h_gap_le : (3 / 4 : ℝ) * β - β_c ≤ β - β_c := by linarith
  have h_rpow_nn : 0 ≤ N_Q ^ η := Real.rpow_nonneg hN_Q η
  have h_prod_le : c_F_pert * ((3 / 4 : ℝ) * β - β_c) ≤ c_F * (β - β_c) :=
    mul_le_mul hc_le h_gap_le (le_of_lt h_three_fourth) (le_trans (le_of_lt hc_pos) hc_le)
  have h_barrier_le :
      dressedThermalFreeEnergyBarrier c_F_pert β β_c N_Q η C_0 ≤
        c_F * (β - β_c) * (N_Q ^ η) := by
    dsimp [dressedThermalFreeEnergyBarrier]
    have h1 : c_F_pert * ((3 / 4 : ℝ) * β - β_c) * (N_Q ^ η) ≤
        c_F * (β - β_c) * (N_Q ^ η) :=
      mul_le_mul_of_nonneg_right h_prod_le h_rpow_nn
    linarith
  exact ⟨hβ_gt, h_barrier_le, Real.exp_le_exp.mpr (neg_le_neg h_barrier_le)⟩

/-! ## 2. Level-$k$ Spatially Inhomogeneous 3D BDL Memory Realization (`bdl_welded_inhomogeneous_memory_realization_exists`) -/

/-- **Level-$k$ Spatially Inhomogeneous 3D BDL Memory Realization (`bdl_welded_inhomogeneous_memory_realization_exists`)**:
    Instantiates the static CSS Hamiltonian lifted from `bdlLocalDescriptor k` on
    `Box3D (bdlBoxSide k)` together with its bare logical observables, RCA-decoded observables,
    bare Peierls free-energy barrier, and unperturbed KMS Lindblad lifetime. -/
theorem bdl_welded_inhomogeneous_memory_realization_exists :
    ∃ (β_c c_F η C c_star c_mem : ℝ),
      0 < β_c ∧ 0 < c_F ∧ 0 < η ∧ 1 ≤ C ∧ 0 < c_star ∧ 2 * C * c_star < 1 ∧ 0 < c_mem ∧
      ∀ k : ℕ,
        let L := bdlBoxSide k
        let D_target : Box3D L → LocalCSSDescriptor qCodeBDL r0BDL mMaxBDL :=
          bdlLocalDescriptor k
        ∃ (D_field : Box3D L → LocalCSSDescriptor qCodeBDL r0BDL mMaxBDL)
          (sys : IndexedCommutingProjectorHamiltonian 3 L
            (UniformSite3D L (CodeSlotConfig qCodeBDL))
            (StaticCSSCheckIdx L qCodeBDL mMaxBDL))
          (Z_log X_log Pi_safe O_dec_Z O_dec_X :
            ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
              ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
          (D_field = D_target ∧ ValidDescriptorField D_field) ∧
          (∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
            sys.checkProj idx = staticCSSCheckProj D_field idx ∧
            sys.support idx = staticCSSCheckSupport D_field idx ∧
            sys.weight idx = 1) ∧
          (SatisfiesTQO1 sys (Nat.floor (c_star * (L : ℝ))) ∧
            SatisfiesLinearTQO2 sys (Nat.floor (c_star * (L : ℝ))) C ∧
            SatisfiesSectorFilteredLinearTQO2 sys 1 (Nat.floor (c_star * (L : ℝ))) C) ∧
          ((sys.P0 ≠ 0 ∧ sys.P0 ≠ 1) ∧
            (IsSelfAdjoint Z_log ∧ Z_log * Z_log = 1 ∧ Commute sys.H0 Z_log ∧ Commute sys.P0 Z_log) ∧
            (IsSelfAdjoint X_log ∧ X_log * X_log = 1 ∧ Commute sys.H0 X_log ∧ Commute sys.P0 X_log) ∧
            (Z_log * X_log + X_log * Z_log) * sys.P0 = 0 ∧
            (Z_log * sys.P0 ≠ 0 ∧ X_log * sys.P0 ≠ 0)) ∧
          ((IsStarProjection Pi_safe ∧ Pi_safe ≠ 0 ∧ Pi_safe ≠ 1 ∧
              Commute sys.H0 Pi_safe ∧ sys.P0 * Pi_safe = sys.P0) ∧
            (IsSelfAdjoint O_dec_Z ∧ O_dec_Z * O_dec_Z = 1 ∧ ‖O_dec_Z‖ ≤ 1 ∧
              Commute sys.H0 O_dec_Z ∧ O_dec_Z * sys.P0 = Z_log * sys.P0 ∧
              Pi_safe * (sys.P0 - O_dec_Z * sys.P0 * O_dec_Z†) * Pi_safe = 0) ∧
            (IsSelfAdjoint O_dec_X ∧ O_dec_X * O_dec_X = 1 ∧ ‖O_dec_X‖ ≤ 1 ∧
              Commute sys.H0 O_dec_X ∧ O_dec_X * sys.P0 = X_log * sys.P0 ∧
              Pi_safe * (sys.P0 - O_dec_X * sys.P0 * O_dec_X†) * Pi_safe = 0) ∧
            (∀ (v : Box3D L)
               (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
                 ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
               IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v →
               Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
               Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0)) ∧
          (∀ β : ℝ, β > β_c →
            let ΔF := c_F * (β - β_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)
            gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤ Real.exp (-ΔF) ∧
            ∀ (bath : Finset (BathChannel 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))))
              (O_dec : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
                ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
              (O_dec = O_dec_Z ∨ O_dec = O_dec_X) →
              (∀ ch ∈ bath, 0 ≤ ch.γ ∧
                ∃ v : Box3D L, IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} ch.L) →
              ∀ (O_t : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
                  ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
                (t : ℝ),
                0 ≤ t →
                SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_dec O_t t →
                opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_dec) ≤
                  8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) *
                    (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t) := by
  refine ⟨betaCritBDL, cFBDL, etaBDL, (collarConstRCABDL : ℝ), cStarBDL, cMemBDL,
    beta_crit_bdl_pos, c_f_bdl_pos, eta_bdl_pos,
    by dsimp [collarConstRCABDL, bdlLambda]; norm_num,
    c_star_bdl_pos, two_mul_collar_const_mul_c_star_bdl_lt_one, c_mem_bdl_pos, ?_⟩
  intro k
  rcases bdlInhomogeneousSafeProjector_and_decodedLogical_exists_aux k with
    ⟨sys, Z_log, X_log, Pi_safe, O_dec_Z, O_dec_X,
      h_sys_checks, hP0, h_tqo1, h_tqo2, h_sec_tqo2,
      hZ, hX, h_anti, h_log_ne, hPi, hOZ, hOX, h_fw_1site, h_peierls⟩
  refine ⟨bdlLocalDescriptor k, sys, Z_log, X_log, Pi_safe, O_dec_Z, O_dec_X,
    ⟨rfl, bdlLocalDescriptor_validDescriptorField k⟩, h_sys_checks,
    ⟨h_tqo1, h_tqo2, h_sec_tqo2⟩,
    ⟨hP0, hZ, hX, h_anti, h_log_ne⟩,
    ⟨hPi, hOZ, hOX, h_fw_1site⟩, ?_⟩
  intro β hβ
  have h_pfail : gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤
      Real.exp (- (cFBDL * (β - betaCritBDL) * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL))) :=
    h_peierls β hβ
  refine ⟨h_pfail, ?_⟩
  intro bath O_dec hO_cases h_bath_loc O_t t ht h_ode
  rcases hO_cases with hO_eq | hO_eq
  · rw [hO_eq] at h_ode ⊢
    have h_bath_fw : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
        Pi_safe * (ch.L * O_dec_Z - O_dec_Z * ch.L) * Pi_safe = 0 := by
      intro ch hch
      rcases h_bath_loc ch hch with ⟨hγ, v, hv⟩
      exact ⟨hγ, (h_fw_1site v ch.L hv).1⟩
    exact opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed
      sys.isSelfAdjoint_H0 β bath O_dec_Z Pi_safe
      hOZ.1 hOZ.2.1 hOZ.2.2.2.1 hPi.1 h_bath_fw h_pfail O_t t ht h_ode
  · rw [hO_eq] at h_ode ⊢
    have h_bath_fw : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
        Pi_safe * (ch.L * O_dec_X - O_dec_X * ch.L) * Pi_safe = 0 := by
      intro ch hch
      rcases h_bath_loc ch hch with ⟨hγ, v, hv⟩
      exact ⟨hγ, (h_fw_1site v ch.L hv).2⟩
    exact opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed
      sys.isSelfAdjoint_H0 β bath O_dec_X Pi_safe
      hOX.1 hOX.2.1 hOX.2.2.2.1 hPi.1 h_bath_fw h_pfail O_t t ht h_ode

end
