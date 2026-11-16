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

import Proofs.TwoAxisMemorySynthesis.FiniteRangeCheckSupport

/-!
# Spatially Inhomogeneous 3D Welded Memory Realization and Macroscopic Immunity

Defines the level-indexed open-box memory package `Inhomogeneous3DMemoryRealization` and constructs `bdl_inhomogeneous_memory_realization_with_macro_immunity` equipping the 3D three-layer welded code with macroscopic safe-subspace immunity and unperturbed thermal and KMS memory stability.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`)
-/

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

namespace InhomogeneousMemoryChallenge

/-- **Concrete Realization of the Level-$k$ 3D Spatially Inhomogeneous BDL Quantum Memory
    (`Inhomogeneous3DMemoryRealization`)** bundling the valid local CSS descriptor field,
    operator TQO invariants, anticommuting logical operators, safe-subspace decoder projections,
    and unperturbed thermal and KMS stability bounds. -/
structure Inhomogeneous3DMemoryRealization
    (L q_code r_0 m_max : ℕ) [NeZero L]
    (c_star C β_c c_F η c_mem : ℝ) : Type where
  D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max
  h_D_field_valid :
    ValidDescriptorField D_field
  sys : IndexedCommutingProjectorHamiltonian 3 L
    (UniformSite3D L (CodeSlotConfig q_code))
    (StaticCSSCheckIdx L q_code m_max)
  h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
    sys.checkProj idx = staticCSSCheckProj D_field idx ∧
    sys.support idx = staticCSSCheckSupport D_field idx ∧
    sys.weight idx = 1
  h_tqo :
    SatisfiesTQO1 sys (Nat.floor (c_star * (L : ℝ))) ∧
    SatisfiesLinearTQO2 sys (Nat.floor (c_star * (L : ℝ))) C ∧
    SatisfiesSectorFilteredLinearTQO2 sys 1 (Nat.floor (c_star * (L : ℝ))) C
  Z_log : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))
  X_log : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))
  h_logical_pair :
    (sys.P0 ≠ 0 ∧ sys.P0 ≠ 1) ∧
    (IsSelfAdjoint Z_log ∧ Z_log * Z_log = 1 ∧ Commute sys.H0 Z_log ∧ Commute sys.P0 Z_log) ∧
    (IsSelfAdjoint X_log ∧ X_log * X_log = 1 ∧ Commute sys.H0 X_log ∧ Commute sys.P0 X_log) ∧
    (Z_log * X_log + X_log * Z_log) * sys.P0 = 0 ∧
    (Z_log * sys.P0 ≠ 0 ∧ X_log * sys.P0 ≠ 0)
  Pi_safe : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))
  O_dec_Z : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))
  O_dec_X : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))
  h_decoder_props :
    (IsStarProjection Pi_safe ∧ Pi_safe ≠ 0 ∧ Pi_safe ≠ 1 ∧
      Commute sys.H0 Pi_safe ∧ sys.P0 * Pi_safe = sys.P0) ∧
    (IsSelfAdjoint O_dec_Z ∧ O_dec_Z * O_dec_Z = 1 ∧ ‖O_dec_Z‖ ≤ 1 ∧
      Commute sys.H0 O_dec_Z ∧ O_dec_Z * sys.P0 = Z_log * sys.P0 ∧
      Pi_safe * (sys.P0 - O_dec_Z * sys.P0 * O_dec_Z†) * Pi_safe = 0) ∧
    (IsSelfAdjoint O_dec_X ∧ O_dec_X * O_dec_X = 1 ∧ ‖O_dec_X‖ ≤ 1 ∧
      Commute sys.H0 O_dec_X ∧ O_dec_X * sys.P0 = X_log * sys.P0 ∧
      Pi_safe * (sys.P0 - O_dec_X * sys.P0 * O_dec_X†) * Pi_safe = 0) ∧
    (∀ (v : Box3D L)
       (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
         ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))),
       IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) {v} A_v →
       Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
       Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0)
  h_unperturbed_thermal_and_kms_lifetime :
    ∀ β : ℝ, β > β_c →
      let ΔF := c_F * (β - β_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)
      gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤ Real.exp (-ΔF) ∧
      ∀ (bath : Finset (BathChannel 3 L (UniformSite3D L (CodeSlotConfig q_code))))
        (O_dec : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))),
        (O_dec = O_dec_Z ∨ O_dec = O_dec_X) →
        (∀ ch ∈ bath, 0 ≤ ch.γ ∧
          ∃ v : Box3D L, IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) {v} ch.L) →
        ∀ (O_t : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
            ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))))
          (t : ℝ),
          0 ≤ t →
          SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_dec O_t t →
          opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_dec) ≤
            8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) *
              (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t

end InhomogeneousMemoryChallenge

open InhomogeneousMemoryChallenge

/-! ## 1. Level-$k$ BDL Memory Realization with Macroscopic $\Lambda_{\mathrm{BDL}}^k$ Cube Safe-Subspace Immunity -/

/-- **Level-$k$ Concrete BDL Memory Realization with Macroscopic $\Lambda_{\mathrm{BDL}}^k$ Cube
    Safe-Subspace Immunity (`bdl_inhomogeneous_memory_realization_with_macro_immunity`)**. -/
theorem bdl_inhomogeneous_memory_realization_with_macro_immunity (k : ℕ) :
    let L := bdlBoxSide k
    ∃ (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
        cStarBDL (collarConstRCABDL : ℝ)
        betaCritBDL cFBDL etaBDL cMemBDL),
      mem.D_field = bdlLocalDescriptor k ∧
      (∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 L r,
          mem.Pi_safe * (V.term r A * mem.O_dec_Z - mem.O_dec_Z * V.term r A) * mem.Pi_safe = 0 ∧
          mem.Pi_safe * (V.term r A * mem.O_dec_X - mem.O_dec_X * V.term r A) * mem.Pi_safe = 0) := by
  intro L
  rcases bdl_inhomogeneous_safe_projector_and_macroscopic_immunity_exists k with
    ⟨sys, Z_log, X_log, Pi_safe, O_dec_Z, O_dec_X,
      h_sys_checks, hP0, h_tqo1, h_tqo2, h_sec_tqo2, hZ, hX, h_anti, h_log_ne,
      hPi, hOZ, hOX, h_fw_1site, h_fw_macro, h_peierls⟩
  have h_unpert :
      ∀ β : ℝ, β > betaCritBDL →
        let ΔF := cFBDL * (β - betaCritBDL) * (((L ^ 3 : ℕ) : ℝ) ^ etaBDL)
        gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤ Real.exp (-ΔF) ∧
        ∀ (bath : Finset (BathChannel 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))))
          (O_dec : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
            ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
          (O_dec = O_dec_Z ∨ O_dec = O_dec_X) →
          (∀ ch ∈ bath, 0 ≤ ch.γ ∧
            ∃ v : Box3D L, IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} ch.L) →
          ∀ (O_t : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
              ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))) (t : ℝ),
            0 ≤ t →
            SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_dec O_t t →
            opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_dec) ≤
              8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t := by
    intro β hβ
    refine ⟨h_peierls β hβ, fun bath O_dec hO_cases h_bath_loc O_t t ht h_ode => ?_⟩
    rcases hO_cases with hO_eq | hO_eq
    · rw [hO_eq] at h_ode ⊢
      exact opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed
        sys.isSelfAdjoint_H0 β bath O_dec_Z Pi_safe
        hOZ.1 hOZ.2.1 hOZ.2.2.2.1 hPi.1
        (fun ch hch => ⟨(h_bath_loc ch hch).1,
          (h_fw_1site (h_bath_loc ch hch).2.choose ch.L (h_bath_loc ch hch).2.choose_spec).1⟩)
        (h_peierls β hβ) O_t t ht h_ode
    · rw [hO_eq] at h_ode ⊢
      exact opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed
        sys.isSelfAdjoint_H0 β bath O_dec_X Pi_safe
        hOX.1 hOX.2.1 hOX.2.2.2.1 hPi.1
        (fun ch hch => ⟨(h_bath_loc ch hch).1,
          (h_fw_1site (h_bath_loc ch hch).2.choose ch.L (h_bath_loc ch hch).2.choose_spec).2⟩)
        (h_peierls β hβ) O_t t ht h_ode
  let mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ)
      betaCritBDL cFBDL etaBDL cMemBDL := {
    D_field := bdlLocalDescriptor k
    h_D_field_valid := bdlLocalDescriptor_validDescriptorField k
    sys := sys
    h_sys_checks := h_sys_checks
    h_tqo := ⟨h_tqo1, h_tqo2, h_sec_tqo2⟩
    Z_log := Z_log
    X_log := X_log
    h_logical_pair := ⟨hP0, hZ, hX, h_anti, h_log_ne⟩
    Pi_safe := Pi_safe
    O_dec_Z := O_dec_Z
    O_dec_X := O_dec_X
    h_decoder_props := ⟨hPi, hOZ, hOX, h_fw_1site⟩
    h_unperturbed_thermal_and_kms_lifetime := h_unpert
  }
  exact ⟨mem, rfl, h_fw_macro⟩

end
