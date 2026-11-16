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

import Proofs.KatoODE.ContinuationWeightKernel
import Proofs.KatoODE.KatoGeneratorProjectorCommutator
import Proofs.KatoODE.KatoGeneratorQuasiLocalDecomposition
import Proofs.KatoODE.NonAutonomousLinearODEExistence
import Proofs.KatoODE.NonAutonomousUnitaryLightCone
import Proofs.KatoODE.PerturbedSpectralProjectorSmoothness
import Proofs.KatoODE.SchwartzBochnerLightCone

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Kato–Hastings Adiabatic Subspace Intertwining and Light-Cone Synthesis

Defines `SatisfiesKatoHastingsSubspaceIntertwining` and the universal generator decay profile `katoGeneratorUniversalDecayProfile`. Combines the non-autonomous Kato–Hastings ODE flow, the smooth bandpass filter `bandpassFilterWeight`, and centered-ball light-cone estimates (`kato_hastings_subspace_intertwining_of_nonAutonomous_katoFlow`) to establish exact off-diagonal annihilation on gapped coupling intervals.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`), Equation (94) (`eq:dressed-unitary-lr`)
-/

attribute [local irreducible] collarConstRCABDL bdlLambda qCodeBDL r0BDL mMaxBDL

/-- Target predicate for Kato–Hastings subspace intertwining and unitary light-cone bounds. -/
abbrev SatisfiesKatoHastingsSubspaceIntertwining
    (w_BL : ℝ → ℂ) (f f_D g_offDiag : ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) (_hk4 : 4 ≤ k) {L : ℕ} [NeZero L] (_hL : L = bdlBoxSide k),
    ∀ (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
        cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
      (J : ℝ), 0 ≤ J → J ≤ 1 →
      ∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
        V.SatisfiesDecayBound J f →
        ∃ (U_QAC : ℝ → unitary (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))),
          (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
            IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v → ∀ r : ℕ,
              ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
                condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v r) ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤
                (J * hastingsKomaOneSiteTailProfile 3 f_D r) * ‖A_v‖) ∧
          ∀ s ∈ Set.Icc (0 : ℝ) 1,
            (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap mem.sys V u) →
            let V_s := scaleQuasiLocalPerturbation s V
            let H_dress := (U_QAC s).1† * (mem.sys.H0 + V_s.totalPerturbation) * (U_QAC s).1
            (∀ u : Box3D L,
              let X_raw := bochnerFilteredSiteOp H_dress (U_QAC s).1 w_BL
                (sitePerturbationOp V_s u) (mem.sys.siteCheckOp u)
              ‖mem.sys.P0 * X_raw * (1 - mem.sys.P0)‖ ≤ J * g_offDiag (bdlScaleCutoffK k)) ∧
            (∀ j ∈ Finset.Icc 1 (bdlScaleCutoffK k), ∀ u : Box3D L,
              (∀ B_loc : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)),
                IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u (j / 2)) B_loc →
                ‖(U_QAC s).1† * B_loc * (U_QAC s).1 -
                  condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j) ((U_QAC s).1† * B_loc * (U_QAC s).1)‖ ≤
                  hastingsKomaBoxBallHalfTailProfile f_D j * ‖B_loc‖) ∧
              ‖((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u) -
                condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j)
                  ((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u)‖ ≤
                J * hastingsKomaSiteCheckBoxBallTailProfile f_D j) ∧
            (∀ u : Box3D L,
              ‖(U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u‖ ≤
                J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D))

/-- For any star projection `P`, `‖P * X * (1 - P)‖ ≤ ‖twoBlockOffDiagProj P X‖`. -/
theorem norm_mul_mul_one_sub_le_norm_twoBlockOffDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E}
    (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    P * twoBlockOffDiagProj P X * (1 - P) = P * X * (1 - P) ∧
    ‖P * X * (1 - P)‖ ≤ ‖twoBlockOffDiagProj P X‖ := by
  have hP_idem : P * P = P := hP.isIdempotentElem.eq
  have hP1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h1P_idem : (1 - P) * (1 - P) = 1 - P := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hP_idem]; abel
  have h_eq : P * twoBlockOffDiagProj P X * (1 - P) = P * X * (1 - P) := by
    unfold twoBlockOffDiagProj
    calc P * (P * X * (1 - P) + (1 - P) * X * P) * (1 - P)
      _ = (P * P) * X * ((1 - P) * (1 - P)) + (P * (1 - P)) * X * P * (1 - P) := by
        simp only [mul_add, add_mul, mul_assoc]
      _ = P * X * (1 - P) := by rw [hP_idem, h1P_idem, hP1P, zero_mul, zero_mul, zero_mul, add_zero]
  have hP1 : ‖P‖ ≤ 1 := isStarProjection_norm_le_one hP
  have h1P : ‖(1 : E →L[ℂ] E) - P‖ ≤ 1 := isStarProjection_norm_le_one hP.one_sub
  refine ⟨h_eq, ?_⟩; rw [← h_eq]
  exact le_trans (norm_mul_le _ _) (le_trans (mul_le_of_le_one_right (norm_nonneg _) h1P)
    (le_trans (norm_mul_le _ _) (mul_le_of_le_one_left (norm_nonneg _) hP1)))

/-- **Non-Autonomous Kato–Hastings Off-Diagonal Annihilation** -/
theorem twoBlockOffDiagProj_and_norm_bochnerFilteredSiteOp_katoFlowUnitary_eq_zero
    {D L : ℕ} [NeZero L] {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem sys.P0 D_gen U_flow P_flow)
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (J s : ℝ) (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s)
    (hP_eq : P_flow s = perturbedGroundSpectralProj sys V s) (u : BoxD D L) :
    let U_s := katoFlowUnitary hFlow s; let V_s := scaleQuasiLocalPerturbation s V
    let H_dress := U_s.1† * (sys.H0 + V_s.totalPerturbation) * U_s.1
    let X_raw := bochnerFilteredSiteOp H_dress U_s.1 w_BL (sitePerturbationOp V_s u) (sys.siteCheckOp u)
    twoBlockOffDiagProj sys.P0 X_raw = 0 ∧ ‖sys.P0 * X_raw * (1 - sys.P0)‖ ≤ J * 0 := by
  intro U_s V_s H_dress X_raw
  have hHs_sa : IsSelfAdjoint (sys.H0 + V_s.totalPerturbation) :=
    isSelfAdjoint_add_clm sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  rcases siteCheckOp_mul_P0_and_P0_mul_eq_zero sys u with ⟨hQP0, hP0Q⟩
  have h_bare : ∀ Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      twoBlockOffDiagProj (P_flow s) (bochnerFilteredOp (sys.H0 + V_s.totalPerturbation) w_BL Y) = 0 := by
    intro Y; rw [hP_eq]
    exact twoBlockOffDiagProj_perturbedGroundSpectralProj_bochnerFilteredOp_eq_zero
      sys V s hw_int hw_zero h_gap Y
  have h_off0 : twoBlockOffDiagProj sys.P0 X_raw = 0 :=
    (twoBlockOffDiagProj_dressed_bochnerFilteredSiteOp_eq_zero
      hFlow sys.isStarProjection_P0.isIdempotentElem.eq hHs_sa hw_int s hQP0 hP0Q h_bare).1
  refine ⟨h_off0, ?_⟩
  have h_le := (norm_mul_mul_one_sub_le_norm_twoBlockOffDiagProj sys.isStarProjection_P0 X_raw).2
  rw [h_off0, norm_zero] at h_le; rw [mul_zero]; exact h_le

/-- **Master Non-Autonomous Kato–Hastings Assembly** -/
theorem kato_hastings_subspace_intertwining_of_nonAutonomous_katoFlow
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (f : ℕ → ℝ) {f_D : ℕ → ℝ} (hf_D : IsSuperpolynomialDecay f_D)
    (h_nonauto :
      ∀ (k : ℕ) (_hk4 : 4 ≤ k) {L : ℕ} [NeZero L] (_hL : L = bdlBoxSide k),
        ∀ (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
            cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
          (J : ℝ), 0 ≤ J → J ≤ 1 →
          ∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
            V.SatisfiesDecayBound J f →
            ∃ (D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
              (hFlow : IsKatoHastingsFlowSystem mem.sys.P0 D_gen U_flow P_flow),
              let U_QAC := fun s => katoFlowUnitary hFlow s
              (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
                IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v → ∀ r : ℕ,
                  ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
                    condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v r) ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤
                    (J * hastingsKomaOneSiteTailProfile 3 f_D r) * ‖A_v‖) ∧
              ∀ s ∈ Set.Icc (0 : ℝ) 1,
                (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap mem.sys V u) →
                P_flow s = perturbedGroundSpectralProj mem.sys V s ∧
                (∀ j ∈ Finset.Icc 1 (bdlScaleCutoffK k), ∀ u : Box3D L,
                  (∀ B_loc : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)),
                    IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u (j / 2)) B_loc →
                    ‖(U_QAC s).1† * B_loc * (U_QAC s).1 -
                      condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j) ((U_QAC s).1† * B_loc * (U_QAC s).1)‖ ≤
                      hastingsKomaBoxBallHalfTailProfile f_D j * ‖B_loc‖) ∧
                  ‖((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u) -
                    condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j)
                      ((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u)‖ ≤
                    J * hastingsKomaSiteCheckBoxBallTailProfile f_D j) ∧
                (∀ u : Box3D L,
                  ‖(U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u‖ ≤
                    J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D))) :
    ∃ (f_D g_offDiag : ℕ → ℝ), IsSuperpolynomialDecay f_D ∧ IsSuperpolynomialDecay g_offDiag ∧
      SatisfiesKatoHastingsSubspaceIntertwining w_BL f f_D g_offDiag := by
  refine ⟨f_D, fun _ => 0, hf_D, isSuperpolynomialDecay_zero, ?_⟩
  intro k hk4 L _ hL mem J hJ_nn hJ1 V hV_dec
  rcases h_nonauto k hk4 hL mem J hJ_nn hJ1 V hV_dec with ⟨D_gen, U_flow, P_flow, hFlow, h_1site, h_all_s⟩
  refine ⟨fun s => katoFlowUnitary hFlow s, h_1site, ?_⟩
  intro s hs h_gap
  rcases h_all_s s hs h_gap with ⟨hP_eq, h_tails, h_drift⟩
  refine ⟨fun u => (twoBlockOffDiagProj_and_norm_bochnerFilteredSiteOp_katoFlowUnitary_eq_zero
    mem.sys V hFlow hw_int hw_zero J s (h_gap s ⟨hs.1, le_rfl⟩) hP_eq u).2, h_tails, h_drift⟩

/-- **Kato Generator Projector Commutator ODE (`hasDerivAt_perturbedGroundSpectralProj_katoGenerator_commutator_of_gap`)** -/
theorem hasDerivAt_perturbedGroundSpectralProj_katoGenerator_commutator_of_gap
    {D L : ℕ} [NeZero L] {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site) (τ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V τ) :
    let H_τ := sys.H0 + (scaleQuasiLocalPerturbation τ V).totalPerturbation
    let D_τ := katoHastingsGeneratorOp H_τ bandpassContinuationWeight V.totalPerturbation
    let P_τ := perturbedGroundSpectralProj sys V τ
    HasDerivAt (perturbedGroundSpectralProj sys V) ((Complex.I : ℂ) • (D_τ * P_τ - P_τ * D_τ)) τ := by
  rcases differentiableAt_perturbedGroundSpectralProj_of_gap sys V τ h_gap with ⟨P_deriv, hP_deriv⟩
  exact (hasDerivAt_perturbedGroundSpectralProj_eq_katoGenerator_commutator sys V τ h_gap hP_deriv).2

/-- **Quasi-Local Kato Generator Projector Commutator ODE (`hasDerivAt_perturbedGroundSpectralProj_katoGeneratorQuasiLocal_commutator_of_gap`)** -/
theorem hasDerivAt_perturbedGroundSpectralProj_katoGeneratorQuasiLocal_commutator_of_gap
    {D L : ℕ} [NeZero L] {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site) (τ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V τ) :
    let D_τ := (katoGeneratorQuasiLocal sys.H0 sys.isSelfAdjoint_H0
      bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V τ).totalPerturbation
    let P_τ := perturbedGroundSpectralProj sys V τ
    HasDerivAt (perturbedGroundSpectralProj sys V) ((Complex.I : ℂ) • (D_τ * P_τ - P_τ * D_τ)) τ := by
  intro D_τ P_τ
  have hD_eq : D_τ =
      katoHastingsGeneratorOp (sys.H0 + (scaleQuasiLocalPerturbation τ V).totalPerturbation) bandpassContinuationWeight V.totalPerturbation := by
    dsimp [D_τ]; rw [scaleQuasiLocalPerturbation_V_tot, ← clm_real_smul]
    exact katoGeneratorQuasiLocal_V_tot_eq sys.H0 sys.isSelfAdjoint_H0
      bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V τ
  rw [hD_eq]
  exact hasDerivAt_perturbedGroundSpectralProj_katoGenerator_commutator_of_gap sys V τ h_gap

/-- **Non-Autonomous Kato Flow Existence, Intertwining, and Lieb–Robinson Bounds at Fixed `L, K` (`kato_hastings_nonauto_flow_at_L`)** -/
theorem kato_hastings_nonauto_flow_at_L {L K : ℕ} [NeZero L]
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
    {J : ℝ} {f_D : ℕ → ℝ} (hJ_nn : 0 ≤ J) (hJ1 : J ≤ 1) (hf_D : IsSuperpolynomialDecay f_D)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (h_dec : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      (katoGeneratorQuasiLocal mem.sys.H0 mem.sys.isSelfAdjoint_H0
        bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V τ).SatisfiesDecayBound J f_D) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    ∃ (D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
      (hFlow : IsKatoHastingsFlowSystem mem.sys.P0 D_gen U_flow P_flow),
      let U_QAC := fun s => katoFlowUnitary hFlow s
      (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
        IsSupportedOn Site {v} A_v → ∀ r : ℕ,
          ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
            condExp Site (boxBall v r) ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤
            (J * hastingsKomaOneSiteTailProfile 3 f_D r) * ‖A_v‖) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap mem.sys V u) →
        P_flow s = perturbedGroundSpectralProj mem.sys V s ∧
        (∀ j ∈ Finset.Icc 1 K, ∀ u : Box3D L,
          (∀ B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
            IsSupportedOn Site (boxBall u (j / 2)) B_loc →
            ‖(U_QAC s).1† * B_loc * (U_QAC s).1 -
              condExp Site (boxBall u j) ((U_QAC s).1† * B_loc * (U_QAC s).1)‖ ≤
              hastingsKomaBoxBallHalfTailProfile f_D j * ‖B_loc‖) ∧
          ‖((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u) -
            condExp Site (boxBall u j)
              ((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u)‖ ≤
            J * hastingsKomaSiteCheckBoxBallTailProfile f_D j) ∧
        (∀ u : Box3D L,
          ‖(U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u‖ ≤
            J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D)) := by
  intro Site
  let D_loc := katoGeneratorQuasiLocal mem.sys.H0 mem.sys.isSelfAdjoint_H0
    bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V
  have hD_cont : Continuous (fun τ : ℝ => (D_loc τ).totalPerturbation) :=
    continuous_katoGeneratorQuasiLocal_V_tot mem.sys.H0 mem.sys.isSelfAdjoint_H0
      bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V
  rcases exists_isKatoHastingsFlowSystem_of_continuous_selfAdjoint mem.sys.P0
    (fun τ => (D_loc τ).totalPerturbation) hD_cont (fun τ => (D_loc τ).isSelfAdjoint_totalPerturbation) with
    ⟨U_flow, P_flow, hFlow, _⟩
  have h_lr := kato_hastings_nonAutonomous_unitary_light_cone_of_quasiLocal_generator
    mem D_loc hFlow hD_cont hJ_nn hJ1 hf_D h_dec
  refine ⟨fun τ => (D_loc τ).totalPerturbation, U_flow, P_flow, hFlow, h_lr.1, fun s hs h_gap => ?_⟩
  have hP_eq : P_flow s = perturbedGroundSpectralProj mem.sys V s :=
    (katoFlow_intertwines_spectralProj_on_Icc hFlow
      (perturbedGroundSpectralProj mem.sys V) (perturbedGroundSpectralProj_zero_eq_P0 mem.sys V)
      hs.1 (fun τ hτ =>
        hasDerivAt_perturbedGroundSpectralProj_katoGeneratorQuasiLocal_commutator_of_gap
          mem.sys V τ (h_gap τ hτ))).2.2
  exact ⟨hP_eq, fun j _ u => (h_lr.2 s hs).1 j u, (h_lr.2 s hs).2⟩

/-- **ODE, Commutator, Quasi-Local Generator, and Non-Autonomous Lieb–Robinson Assembly (`kato_hastings_subspace_intertwining_of_katoODE_components`)** -/
theorem kato_hastings_subspace_intertwining_of_katoODE_components
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    (f : ℕ → ℝ) {f_D : ℕ → ℝ} (hf_D : IsSuperpolynomialDecay f_D)
    (h_gen_dec :
      ∀ (k : ℕ) (_hk4 : 4 ≤ k) {L : ℕ} [NeZero L] (_hL : L = bdlBoxSide k)
        (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
          cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
        (J : ℝ), 0 ≤ J → J ≤ 1 →
        ∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
          V.SatisfiesDecayBound J f →
          ∀ τ ∈ Set.Icc (0 : ℝ) 1,
            (katoGeneratorQuasiLocal mem.sys.H0 mem.sys.isSelfAdjoint_H0
              bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V τ).SatisfiesDecayBound J f_D) :
    ∃ (f_D g_offDiag : ℕ → ℝ), IsSuperpolynomialDecay f_D ∧ IsSuperpolynomialDecay g_offDiag ∧
      SatisfiesKatoHastingsSubspaceIntertwining w_BL f f_D g_offDiag := by
  apply kato_hastings_subspace_intertwining_of_nonAutonomous_katoFlow hw_int hw_zero f hf_D
  intro k hk4 L _ hL mem J hJ_nn hJ1 V hV_dec
  exact kato_hastings_nonauto_flow_at_L mem hJ_nn hJ1 hf_D V
    (h_gen_dec k hk4 hL mem J hJ_nn hJ1 V hV_dec)

lemma isSuperpolynomialDecay_sub_two {g : ℕ → ℝ} (hg : IsSuperpolynomialDecay g) :
    IsSuperpolynomialDecay (fun r : ℕ => g (r - 2)) := by
  refine ⟨fun r => hg.1 (r - 2), fun n => ?_⟩
  have h_tend : Tendsto (fun r : ℕ => r - 2) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b + 2, fun r hr => by omega⟩)
  have h_comp : Tendsto (fun r : ℕ => ((r - 2 : ℕ) : ℝ) ^ n * g (r - 2)) atTop (𝓝 0) :=
    (hg.2 n).comp h_tend
  have h_upper : Tendsto
      (fun r : ℕ => ((2 : ℕ) : ℝ) ^ n * (((r - 2 : ℕ) : ℝ) ^ n * g (r - 2))) atTop (𝓝 0) := by
    simpa [mul_zero] using h_comp.const_mul (((2 : ℕ) : ℝ) ^ n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper
    (Eventually.of_forall (fun r => mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (hg.1 (r - 2)))) ?_
  rw [Filter.eventually_atTop]; refine ⟨4, fun r hr => ?_⟩
  have hr_le_nat : r ≤ 2 * (r - 2) := by omega
  have hr_le_real : (r : ℝ) ≤ ((2 : ℕ) : ℝ) * ((r - 2 : ℕ) : ℝ) := by exact_mod_cast hr_le_nat
  have h_pow : (r : ℝ) ^ n ≤ (((2 : ℕ) : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg r) hr_le_real n
  calc (r : ℝ) ^ n * g (r - 2)
    _ ≤ (((2 : ℕ) : ℝ) * ((r - 2 : ℕ) : ℝ)) ^ n * g (r - 2) :=
      mul_le_mul_of_nonneg_right h_pow (hg.1 (r - 2))
    _ = ((2 : ℕ) : ℝ) ^ n * (((r - 2 : ℕ) : ℝ) ^ n * g (r - 2)) := by rw [mul_pow, mul_assoc]

/-- Universal ($L$-independent) superpolynomial decay profile for `katoGeneratorQuasiLocal`. -/
def katoGeneratorUniversalDecayProfile (D : ℕ) (W : ℝ → ℂ) (f g_gen : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r < 2 then 2 * ((r : ℝ) ^ D) * (∫ t : ℝ, ‖W t‖) * (∑' q : ℕ, f q)
  else 4 * ((r : ℝ) ^ D) * g_gen (r - 2)

lemma isSuperpolynomialDecay_katoGeneratorUniversalDecayProfile (D : ℕ) (W : ℝ → ℂ)
    {f g_gen : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) (hg : IsSuperpolynomialDecay g_gen) :
    IsSuperpolynomialDecay (katoGeneratorUniversalDecayProfile D W f g_gen) := by
  have h_tail : IsSuperpolynomialDecay (fun r : ℕ => 4 * ((r : ℝ) ^ D * g_gen (r - 2))) :=
    isSuperpolynomialDecay_const_mul
      (isSuperpolynomialDecay_mul_pow (isSuperpolynomialDecay_sub_two hg) D) (by norm_num)
  refine ⟨fun r => ?_, fun n => ?_⟩
  · dsimp [katoGeneratorUniversalDecayProfile]; split_ifs
    · have hW_nn : 0 ≤ ∫ t : ℝ, ‖W t‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
      have hf_nn : 0 ≤ ∑' q : ℕ, f q := tsum_nonneg hf.1
      positivity
    · have hg_nn : 0 ≤ g_gen (r - 2) := hg.1 (r - 2); positivity
  · refine (h_tail.2 n).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 2] with r hr
    have hnot : ¬ (r < 2) := by omega
    dsimp [katoGeneratorUniversalDecayProfile]; rw [if_neg hnot]; ring

/-- Pointwise decay bound `SatisfiesDecayBound J (katoGeneratorUniversalDecayProfile D W f g_gen)`
    for `katoGeneratorQuasiLocal` from `boxBall u (j / 2)` conditional expectation bounds. -/
theorem katoGeneratorQuasiLocal_satisfiesDecayBound_of_boxBall_condExp
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH0 : IsSelfAdjoint H0)
    (W : ℝ → ℂ) (hW_int : Integrable W)
    (hW_real : ∀ t : ℝ, star (W t) = W t) (hW_odd : ∀ t : ℝ, W (-t) = - W t)
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f g_gen : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf : IsSuperpolynomialDecay f) (hg_nn : ∀ j : ℕ, 0 ≤ g_gen j)
    (hV : V.SatisfiesDecayBound J f) (s : ℝ)
    (h_condExp : ∀ (u : BoxD D L) (j : ℕ), j / 4 ≤ L →
      let D_u := katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)
      ‖D_u - condExp Site (boxBall u (j / 2)) D_u‖ ≤ J * g_gen j) :
    (katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).SatisfiesDecayBound
      J (katoGeneratorUniversalDecayProfile D W f g_gen) := by
  intro r hr A hA
  by_cases hr2 : r < 2
  · dsimp [katoGeneratorUniversalDecayProfile]; rw [if_pos hr2]
    have h_term := norm_katoGeneratorQuasiLocal_term_le H0 hH0 W hW_int hW_real hW_odd V
      hJ hf.1 hV s hr hA
    have h_sum : ∑ q ∈ Finset.Icc 1 L, f q ≤ ∑' q : ℕ, f q :=
      (summable_of_isSuperpolynomialDecay hf).sum_le_tsum (Finset.Icc 1 L) (fun q _ => hf.1 q)
    have hW_nn : 0 ≤ ∫ t : ℝ, ‖W t‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
    exact le_trans h_term (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left h_sum (by positivity)) hJ)
  · have hr_ge2 : 2 ≤ r := by omega
    dsimp [katoGeneratorUniversalDecayProfile]; rw [if_neg hr2]
    dsimp [katoGeneratorQuasiLocal]; rw [if_pos ⟨hr, hA⟩]
    let S := Finset.univ.filter (fun u : BoxD D L => shellCube u r = A)
    have h_site : ∀ u ∈ S,
        ‖shellGenSiteOp
          (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r‖ ≤
        4 * (J * g_gen (r - 2)) := by
      intro u _
      have hj_cut : (r - 2) / 4 ≤ L := by have := (Finset.mem_Icc.mp hr).2; omega
      exact le_trans (norm_shellGenSiteOp_le_four_mul_sub_condExp_boxBall _ u hr_ge2)
        (mul_le_mul_of_nonneg_left (h_condExp u (r - 2) hj_cut) (by norm_num))
    have h_card : (S.card : ℝ) ≤ (r : ℝ) ^ D := by
      exact_mod_cast card_filter_shellCube_eq_le_pow (Finset.mem_Icc.mp hr).1 hA
    have hg_r : 0 ≤ g_gen (r - 2) := hg_nn (r - 2)
    calc ‖∑ u ∈ S, shellGenSiteOp
            (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r‖
        ≤ ∑ u ∈ S, ‖shellGenSiteOp
            (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _u ∈ S, 4 * (J * g_gen (r - 2)) := Finset.sum_le_sum h_site
      _ = (S.card : ℝ) * (4 * (J * g_gen (r - 2))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((r : ℝ) ^ D) * (4 * (J * g_gen (r - 2))) :=
          mul_le_mul_of_nonneg_right h_card (by positivity)
      _ = J * (4 * ((r : ℝ) ^ D) * g_gen (r - 2)) := by ring

/-- **Master Reduction of `SatisfiesKatoHastingsSubspaceIntertwining` to `bandpassContinuationWeight` `boxBall` Tail** -/
theorem kato_hastings_subspace_intertwining_of_katoODE_and_boxBall_condExp
    {w_BL : ℝ → ℂ} (hw_int : Integrable w_BL)
    (hw_zero : ∀ ω : ℝ, (1 / 2 : ℝ) ≤ |ω| →
      (∫ t : ℝ, w_BL t * Complex.exp (Complex.I * (ω : ℂ) * (t : ℂ))) = 0)
    {f g_gen : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) (hg_gen : IsSuperpolynomialDecay g_gen)
    (h_W_BP_boxBall :
      ∀ (k : ℕ) (_hk4 : 4 ≤ k) {L : ℕ} [NeZero L] (_hL : L = bdlBoxSide k)
        (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
          cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
        (J : ℝ), 0 ≤ J → J ≤ 1 →
        ∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
          V.SatisfiesDecayBound J f →
          ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ (u : Box3D L) (j : ℕ), j / 4 ≤ L →
            let D_u := katoHastingsGeneratorOp (mem.sys.H0 + τ • V.totalPerturbation) bandpassContinuationWeight (sitePerturbationOp V u)
            ‖D_u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u (j / 2)) D_u‖ ≤
              J * g_gen j) :
    ∃ (f_D g_offDiag : ℕ → ℝ), IsSuperpolynomialDecay f_D ∧ IsSuperpolynomialDecay g_offDiag ∧
      SatisfiesKatoHastingsSubspaceIntertwining w_BL f f_D g_offDiag := by
  haveI : NeZero 3 := ⟨by decide⟩
  exact kato_hastings_subspace_intertwining_of_katoODE_components hw_int hw_zero f
    (isSuperpolynomialDecay_katoGeneratorUniversalDecayProfile 3 bandpassContinuationWeight hf hg_gen)
    (fun k hk4 L _ hL mem J hJ_nn hJ1 V hV_dec τ hτ =>
      katoGeneratorQuasiLocal_satisfiesDecayBound_of_boxBall_condExp
        mem.sys.H0 mem.sys.isSelfAdjoint_H0 bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd
        V hJ_nn hf hg_gen.1 hV_dec τ (h_W_BP_boxBall k hk4 hL mem J hJ_nn hJ1 V hV_dec τ hτ))

/-- **Kato–Hastings Adiabatic Subspace Intertwining & Top-Scale Off-Diagonal Bound** -/
theorem kato_hastings_subspace_intertwining_w_BP_of_gap_bootstrap
    (f : ℕ → ℝ) (hf : IsSuperpolynomialDecay f) :
    ∃ (f_D g_offDiag : ℕ → ℝ), IsSuperpolynomialDecay f_D ∧ IsSuperpolynomialDecay g_offDiag ∧
      SatisfiesKatoHastingsSubspaceIntertwining bandpassFilterWeight f f_D g_offDiag :=
  kato_hastings_subspace_intertwining_of_katoODE_and_boxBall_condExp
    integrable_w_BP (fun _ hω => integral_w_BP_mul_exp_eq_zero_of_abs_ge_half hω) hf
    (isSuperpolynomialDecay_bdlSchwartzPerturbationBoxBallTailProfile hf
      (fun hc => isSuperpolynomialDecay_tail_integral_norm_W_BP hc))
    (fun _ _ _ _ _ mem J hJ0 hJ1 V hV τ hτ u j hj_cut =>
      norm_katoHastingsGeneratorOp_W_BP_sitePerturbationOp_boxBall_sub_condExp_le
        mem V hJ0 hJ1 hτ hf hV u j hj_cut)

end
