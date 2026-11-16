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

import Proofs.KatoODE.SylvesterBlockedOperatorInverse

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Differentiability of Perturbed Ground-Space Spectral Projectors

Defines the explicit off-diagonal derivative operator `perturbedGroundSpectralProjDeriv` via `sylvesterOffDiagInverse` and proves continuous differentiability (`hasDerivAt_perturbedGroundSpectralProj_of_gap`, `continuousOn_deriv_perturbedGroundSpectralProj`) of `perturbedGroundSpectralProj` on coupling intervals with positive spectral gap.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Kato (1950), Journal of the Physical Society of Japan 5, 435–439
-/

/-! ## 1. Pure Ring Helpers & Explicit Derivative Operator `perturbedGroundSpectralProjDeriv` -/

lemma clm_smul_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℂ) (X : E →L[ℂ] E) : a • (-X) = -(a • X) := smul_neg a X

lemma clm_real_smul_eq_coe_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (r : ℝ) (X : E →L[ℂ] E) : r • X = (r : ℂ) • X := RCLike.real_smul_eq_coe_smul r X

lemma ring_offDiag_commutator_idempotent {R : Type*} [Ring R] {P₀ : R} (hP₀ : P₀ * P₀ = P₀)
    (X : R) :
    P₀ * (P₀ * X - X * P₀) * (1 - P₀) + (1 - P₀) * (P₀ * X - X * P₀) * P₀ = P₀ * X - X * P₀ := by
  have hP0_R : ∀ Y : R, Y * P₀ * P₀ = Y * P₀ := fun Y => by rw [mul_assoc, hP₀]
  simp only [mul_sub, sub_mul, one_mul, mul_one, ← mul_assoc, hP₀, hP0_R]; abel

lemma ring_commutator_sub_decomp {R : Type*} [Ring R] (H₀ H_s P₀ P_s : R) :
    H₀ * (P_s - P₀) - (P_s - P₀) * H₀ =
      (H_s * P_s - P_s * H_s) - (H₀ * P₀ - P₀ * H₀) - ((H_s - H₀) * P_s - P_s * (H_s - H₀)) := by
  noncomm_ring

lemma ring_twoBlockDiag_diff_decomp {R : Type*} [Ring R] (P P₀ X : R) :
    (P₀ * X * P₀ + (1 - P₀) * X * (1 - P₀)) - (P * X * P + (1 - P) * X * (1 - P)) =
      -(P - P₀) * X * P₀ - P * X * (P - P₀) + (P - P₀) * X * (1 - P₀) + (1 - P) * X * (P - P₀) := by
  noncomm_ring

lemma ring_jacobi_commute {R : Type*} [Ring R] {H₀ P₀ : R} (hHP₀ : H₀ * P₀ = P₀ * H₀) (D_gen : R) :
    H₀ * (D_gen * P₀ - P₀ * D_gen) - (D_gen * P₀ - P₀ * D_gen) * H₀ =
      P₀ * (D_gen * H₀ - H₀ * D_gen) - (D_gen * H₀ - H₀ * D_gen) * P₀ := by
  calc H₀ * (D_gen * P₀ - P₀ * D_gen) - (D_gen * P₀ - P₀ * D_gen) * H₀
    _ = H₀ * D_gen * P₀ - (H₀ * P₀) * D_gen - D_gen * (P₀ * H₀) + P₀ * D_gen * H₀ := by noncomm_ring
    _ = H₀ * D_gen * P₀ - (P₀ * H₀) * D_gen - D_gen * (H₀ * P₀) + P₀ * D_gen * H₀ := by rw [hHP₀]
    _ = P₀ * (D_gen * H₀ - H₀ * D_gen) - (D_gen * H₀ - H₀ * D_gen) * P₀ := by noncomm_ring

lemma ring_commutator_proj_offDiag {R : Type*} [Ring R] {P₀ : R} (hP₀ : P₀ * P₀ = P₀) (V : R) :
    P₀ * (P₀ * V * (1 - P₀) + (1 - P₀) * V * P₀) -
      (P₀ * V * (1 - P₀) + (1 - P₀) * V * P₀) * P₀ = P₀ * V - V * P₀ := by
  have hP0_R : ∀ Y : R, Y * P₀ * P₀ = Y * P₀ := fun Y => by rw [mul_assoc, hP₀]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, ← mul_assoc, hP₀, hP0_R]; abel

/-- For any idempotent `P₀ * P₀ = P₀` and operator `X`, the commutator `P₀ * X - X * P₀`
    is purely off-diagonal with respect to `P₀`. -/
lemma twoBlockOffDiagProj_commutator_proj_eq_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P₀ : E →L[ℂ] E} (hP₀ : P₀ * P₀ = P₀) (X : E →L[ℂ] E) :
    twoBlockOffDiagProj P₀ (P₀ * X - X * P₀) = P₀ * X - X * P₀ :=
  ring_offDiag_commutator_idempotent hP₀ X

/-- **Explicit Spectral Projector Derivative (`perturbedGroundSpectralProjDeriv`)**. -/
def perturbedGroundSpectralProjDeriv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  sylvesterOffDiagInverse sys V s₀
    (perturbedGroundSpectralProj sys V s₀ * V.totalPerturbation - V.totalPerturbation * perturbedGroundSpectralProj sys V s₀)

/-- `perturbedGroundSpectralProjDeriv sys V s₀` is self-adjoint. -/
theorem isSelfAdjoint_perturbedGroundSpectralProjDeriv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) :
    IsSelfAdjoint (perturbedGroundSpectralProjDeriv sys V s₀) := by
  let P₀ := perturbedGroundSpectralProj sys V s₀
  have hP₀ : star P₀ = P₀ := (isStarProjection_perturbedGroundSpectralProj sys V s₀).isSelfAdjoint.star_eq
  have hV : star V.totalPerturbation = V.totalPerturbation := V.isSelfAdjoint_totalPerturbation.star_eq
  refine isSelfAdjoint_sylvesterOffDiagInverse_of_star_eq_neg sys V s₀ ?_
  change star (P₀ * V.totalPerturbation - V.totalPerturbation * P₀) = -(P₀ * V.totalPerturbation - V.totalPerturbation * P₀)
  rw [clm_star_sub, clm_star_mul, clm_star_mul, hP₀, hV]; abel

/-- `perturbedGroundSpectralProjDeriv sys V s₀` is purely off-diagonal with respect to
    `perturbedGroundSpectralProj sys V s₀`. -/
theorem twoBlockOffDiagProj_perturbedGroundSpectralProjDeriv {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) :
    twoBlockOffDiagProj (perturbedGroundSpectralProj sys V s₀)
      (perturbedGroundSpectralProjDeriv sys V s₀) = perturbedGroundSpectralProjDeriv sys V s₀ :=
  twoBlockOffDiagProj_sylvesterOffDiagInverse_eq_self sys V s₀ _

/-- The `P(s₀)`-diagonal part of `perturbedGroundSpectralProjDeriv sys V s₀` vanishes. -/
theorem twoBlockDiagProj_perturbedGroundSpectralProjDeriv_eq_zero {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) :
    twoBlockDiagProj (perturbedGroundSpectralProj sys V s₀)
      (perturbedGroundSpectralProjDeriv sys V s₀) = 0 := by
  have h_sum := twoBlockDiagProj_add_twoBlockOffDiagProj
    (perturbedGroundSpectralProj sys V s₀) (perturbedGroundSpectralProjDeriv sys V s₀)
  rw [twoBlockOffDiagProj_perturbedGroundSpectralProjDeriv] at h_sum
  calc twoBlockDiagProj (perturbedGroundSpectralProj sys V s₀) (perturbedGroundSpectralProjDeriv sys V s₀)
    _ = (twoBlockDiagProj (perturbedGroundSpectralProj sys V s₀)
          (perturbedGroundSpectralProjDeriv sys V s₀) +
          perturbedGroundSpectralProjDeriv sys V s₀) -
        perturbedGroundSpectralProjDeriv sys V s₀ := by abel
    _ = perturbedGroundSpectralProjDeriv sys V s₀ - perturbedGroundSpectralProjDeriv sys V s₀ := by
        rw [h_sum]
    _ = 0 := sub_self _

/-- Under a band gap `Δ > 0`, `perturbedGroundSpectralProjDeriv sys V s₀` satisfies the exact
    Sylvester commutator equation `[H(s₀), P_deriv(s₀)] = [P(s₀), V.V_tot]`. -/
theorem commutator_H_s_perturbedGroundSpectralProjDeriv_eq_of_band_gap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i) :
    let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
    let P₀ := perturbedGroundSpectralProj sys V s₀
    let P' := perturbedGroundSpectralProjDeriv sys V s₀
    H₀ * P' - P' * H₀ = P₀ * V.totalPerturbation - V.totalPerturbation * P₀ := by
  intro H₀ P₀ P'
  have h_comm := commutator_sylvesterOffDiagInverse_eq_twoBlockOffDiagProj sys V s₀ hΔ h_gap
    (P₀ * V.totalPerturbation - V.totalPerturbation * P₀)
  (try dsimp only at h_comm)
  rw [twoBlockOffDiagProj_commutator_proj_eq_self
    (isStarProjection_perturbedGroundSpectralProj sys V s₀).isIdempotentElem.eq] at h_comm
  exact h_comm

/-- Norm bound on `perturbedGroundSpectralProjDeriv sys V s₀` under a band gap `Δ > 0`. -/
theorem norm_perturbedGroundSpectralProjDeriv_le_of_band_gap {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i) :
    ‖perturbedGroundSpectralProjDeriv sys V s₀‖ ≤
      4 * ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ) *
        Δ⁻¹ * ‖V.totalPerturbation‖ := by
  let P₀ := perturbedGroundSpectralProj sys V s₀
  have hP₀_norm : ‖P₀‖ ≤ 1 :=
    isStarProjection_norm_le_one (isStarProjection_perturbedGroundSpectralProj sys V s₀)
  have h_comm_norm : ‖P₀ * V.totalPerturbation - V.totalPerturbation * P₀‖ ≤ 2 * ‖V.totalPerturbation‖ := by
    calc ‖P₀ * V.totalPerturbation - V.totalPerturbation * P₀‖
      _ ≤ ‖P₀ * V.totalPerturbation‖ + ‖V.totalPerturbation * P₀‖ := norm_sub_le _ _
      _ ≤ ‖P₀‖ * ‖V.totalPerturbation‖ + ‖V.totalPerturbation‖ * ‖P₀‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ 1 * ‖V.totalPerturbation‖ + ‖V.totalPerturbation‖ * 1 :=
          add_le_add (mul_le_mul_of_nonneg_right hP₀_norm (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hP₀_norm (norm_nonneg _))
      _ = 2 * ‖V.totalPerturbation‖ := by ring
  have h_inv := norm_sylvesterOffDiagInverse_le_of_band_gap sys V s₀ hΔ h_gap (P₀ * V.totalPerturbation - V.totalPerturbation * P₀)
  have h_coef_nn : 0 ≤ 2 * ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ) * Δ⁻¹ := by
    positivity
  calc ‖perturbedGroundSpectralProjDeriv sys V s₀‖
    _ ≤ (2 * ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ) * Δ⁻¹) *
          (2 * ‖V.totalPerturbation‖) := le_trans h_inv (mul_le_mul_of_nonneg_left h_comm_norm h_coef_nn)
    _ = 4 * ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ) *
          Δ⁻¹ * ‖V.totalPerturbation‖ := by ring

/-! ## 2. Quadratic Remainder & `HasDerivAt` of `perturbedGroundSpectralProj` -/

/-- Exact commutator identity `[H(s₀), P(s) - P(s₀)] = (s - s₀) • [P(s), V.V_tot]`. -/
lemma commutator_H_s0_perturbedGroundSpectralProj_sub {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ s : ℝ) :
    let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
    let P₀ := perturbedGroundSpectralProj sys V s₀
    let P_s := perturbedGroundSpectralProj sys V s
    H₀ * (P_s - P₀) - (P_s - P₀) * H₀ = ((s - s₀ : ℝ) : ℂ) • (P_s * V.totalPerturbation - V.totalPerturbation * P_s) := by
  intro H₀ P₀ P_s
  let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
  have h_comm0 : H₀ * P₀ - P₀ * H₀ = 0 := sub_eq_zero.mpr (commute_perturbedGroundSpectralProj sys V s₀).eq
  have h_comms : H_s * P_s - P_s * H_s = 0 := sub_eq_zero.mpr (commute_perturbedGroundSpectralProj sys V s).eq
  have h_H_diff := hamiltonian_scaleQuasiLocalPerturbation_sub sys V s₀ s
  calc H₀ * (P_s - P₀) - (P_s - P₀) * H₀
    _ = (H_s * P_s - P_s * H_s) - (H₀ * P₀ - P₀ * H₀) - ((H_s - H₀) * P_s - P_s * (H_s - H₀)) :=
        ring_commutator_sub_decomp H₀ H_s P₀ P_s
    _ = 0 - 0 - ((((s - s₀ : ℝ) : ℂ) • V.totalPerturbation) * P_s - P_s * (((s - s₀ : ℝ) : ℂ) • V.totalPerturbation)) := by
        rw [h_comms, h_comm0, h_H_diff]
    _ = ((s - s₀ : ℝ) : ℂ) • (P_s * V.totalPerturbation - V.totalPerturbation * P_s) := by
        rw [smul_mul_assoc, mul_smul_comm, ← clm_smul_sub, sub_zero, zero_sub, ← clm_smul_neg, neg_sub]

/-- Exact representation of the `P(s₀)`-off-diagonal Taylor remainder of `P(s) - P(s₀)`. -/
theorem twoBlockOffDiagProj_perturbedGroundSpectralProj_sub_eq_of_band_gap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ s : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i) :
    let P₀ := perturbedGroundSpectralProj sys V s₀
    let P_s := perturbedGroundSpectralProj sys V s
    twoBlockOffDiagProj P₀ (P_s - P₀) - (s - s₀) • perturbedGroundSpectralProjDeriv sys V s₀ =
      ((s - s₀ : ℝ) : ℂ) •
        sylvesterOffDiagInverse sys V s₀ ((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)) := by
  intro P₀ P_s
  have h_inv := (sylvesterOffDiagInverse_commutator_eq_twoBlockOffDiagProj
    sys V s₀ hΔ h_gap (P_s - P₀)).symm
  (try dsimp only at h_inv)
  rw [h_inv, commutator_H_s0_perturbedGroundSpectralProj_sub sys V s₀ s, sylvesterOffDiagInverse_smul]
  unfold perturbedGroundSpectralProjDeriv
  rw [clm_real_smul_eq_coe_smul, ← clm_smul_sub, ← sylvesterOffDiagInverse_sub]
  congr 2; simp only [sub_mul, mul_sub]; abel

/-- General calculus helper: a quadratic Taylor remainder bound on a neighborhood of `s₀`
    implies `HasDerivAt f f' s₀`. -/
lemma hasDerivAt_of_quadratic_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {s₀ δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (h_bound : ∀ s : ℝ, |s - s₀| < δ → ‖f s - f s₀ - (s - s₀) • f'‖ ≤ K * |s - s₀| ^ 2) :
    HasDerivAt f f' s₀ := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]; intro c hc
  have hK1_pos : 0 < K + 1 := by linarith
  filter_upwards [Metric.ball_mem_nhds s₀ (lt_min hδ (div_pos hc hK1_pos))] with s hs
  rw [Metric.mem_ball, Real.dist_eq] at hs
  have hs_δ : |s - s₀| < δ := lt_of_lt_of_le hs (min_le_left _ _)
  have hs_c : |s - s₀| ≤ c / (K + 1) := le_of_lt (lt_of_lt_of_le hs (min_le_right _ _))
  have h_K_mul : K * |s - s₀| ≤ c := by
    calc K * |s - s₀|
      _ ≤ (K + 1) * |s - s₀| := by nlinarith [abs_nonneg (s - s₀)]
      _ ≤ (K + 1) * (c / (K + 1)) := mul_le_mul_of_nonneg_left hs_c (le_of_lt hK1_pos)
      _ = c := mul_div_cancel₀ c (ne_of_gt hK1_pos)
  rw [Real.norm_eq_abs]
  calc ‖f s - f s₀ - (s - s₀) • f'‖
    _ ≤ K * |s - s₀| ^ 2 := h_bound s hs_δ
    _ = (K * |s - s₀|) * |s - s₀| := by ring
    _ ≤ c * |s - s₀| := mul_le_mul_of_nonneg_right h_K_mul (abs_nonneg _)

/-- **Parametric Differentiability of `perturbedGroundSpectralProj` (`hasDerivAt_perturbedGroundSpectralProj_of_band_gap`)**. -/
theorem hasDerivAt_perturbedGroundSpectralProj_of_band_gap {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i) :
    HasDerivAt (perturbedGroundSpectralProj sys V)
      (perturbedGroundSpectralProjDeriv sys V s₀) s₀ := by
  let P₀ := perturbedGroundSpectralProj sys V s₀
  let P' := perturbedGroundSpectralProjDeriv sys V s₀
  let N_prod : ℝ := ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ)
  let L_lip : ℝ := 4 * N_prod * Δ⁻¹ * ‖V.totalPerturbation‖; let C_inv : ℝ := 2 * N_prod * Δ⁻¹
  let K_rem : ℝ := 2 * L_lip ^ 2 + C_inv * (2 * ‖V.totalPerturbation‖) * L_lip
  let δ : ℝ := (Δ / 4) / (‖V.totalPerturbation‖ + 1)
  have hV1_pos : 0 < ‖V.totalPerturbation‖ + 1 := by positivity
  have hδ_pos : 0 < δ := div_pos (by linarith) hV1_pos
  have hC_nn : 0 ≤ C_inv := by positivity
  have hK_nn : 0 ≤ K_rem := by positivity
  refine hasDerivAt_of_quadratic_bound hδ_pos hK_nn fun s hs => ?_
  let P_s := perturbedGroundSpectralProj sys V s
  have hs_V : |s - s₀| * ‖V.totalPerturbation‖ ≤ Δ / 4 := by
    calc |s - s₀| * ‖V.totalPerturbation‖
      _ ≤ |s - s₀| * (‖V.totalPerturbation‖ + 1) := by nlinarith [abs_nonneg (s - s₀)]
      _ ≤ δ * (‖V.totalPerturbation‖ + 1) := mul_le_mul_of_nonneg_right (le_of_lt hs) (le_of_lt hV1_pos)
      _ = Δ / 4 := div_mul_cancel₀ (Δ / 4) (ne_of_gt hV1_pos)
  have h_lip : ‖P_s - P₀‖ ≤ L_lip * |s - s₀| := by
    convert norm_perturbedGroundSpectralProj_sub_le_of_band_gap sys V s₀ s hΔ h_gap hs_V using 1; ring
  have h_diag : ‖twoBlockDiagProj P₀ (P_s - P₀)‖ ≤ 2 * L_lip ^ 2 * |s - s₀| ^ 2 := by
    have h1 := norm_twoBlockDiagProj_sub_le_two_mul_norm_sq
      (isStarProjection_perturbedGroundSpectralProj sys V s)
      (isStarProjection_perturbedGroundSpectralProj sys V s₀)
    have h2 : ‖P_s - P₀‖ ^ 2 ≤ (L_lip * |s - s₀|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h_lip 2
    calc ‖twoBlockDiagProj P₀ (P_s - P₀)‖
      _ ≤ 2 * ‖P_s - P₀‖ ^ 2 := h1
      _ ≤ 2 * (L_lip * |s - s₀|) ^ 2 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * L_lip ^ 2 * |s - s₀| ^ 2 := by ring
  have h_off : ‖twoBlockOffDiagProj P₀ (P_s - P₀) - (s - s₀) • P'‖ ≤
      (C_inv * (2 * ‖V.totalPerturbation‖) * L_lip) * |s - s₀| ^ 2 := by
    rw [twoBlockOffDiagProj_perturbedGroundSpectralProj_sub_eq_of_band_gap sys V s₀ s hΔ h_gap,
      norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have h_comm_le : ‖(P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)‖ ≤ 2 * ‖V.totalPerturbation‖ * ‖P_s - P₀‖ := by
      calc ‖(P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)‖
        _ ≤ ‖(P_s - P₀) * V.totalPerturbation‖ + ‖V.totalPerturbation * (P_s - P₀)‖ := norm_sub_le _ _
        _ ≤ ‖P_s - P₀‖ * ‖V.totalPerturbation‖ + ‖V.totalPerturbation‖ * ‖P_s - P₀‖ :=
            add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
        _ = 2 * ‖V.totalPerturbation‖ * ‖P_s - P₀‖ := by ring
    have h_inv_le := norm_sylvesterOffDiagInverse_le_of_band_gap sys V s₀ hΔ h_gap
      ((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀))
    have h_inv_le' : ‖sylvesterOffDiagInverse sys V s₀ ((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀))‖ ≤
        C_inv * (2 * ‖V.totalPerturbation‖) * L_lip * |s - s₀| := by
      calc ‖sylvesterOffDiagInverse sys V s₀ ((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀))‖
        _ ≤ C_inv * ‖(P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)‖ := by convert h_inv_le using 1; ring
        _ ≤ C_inv * (2 * ‖V.totalPerturbation‖ * ‖P_s - P₀‖) := mul_le_mul_of_nonneg_left h_comm_le hC_nn
        _ ≤ C_inv * (2 * ‖V.totalPerturbation‖ * (L_lip * |s - s₀|)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_lip (by positivity)) hC_nn
        _ = C_inv * (2 * ‖V.totalPerturbation‖) * L_lip * |s - s₀| := by ring
    calc |s - s₀| * ‖sylvesterOffDiagInverse sys V s₀ ((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀))‖
      _ ≤ |s - s₀| * (C_inv * (2 * ‖V.totalPerturbation‖) * L_lip * |s - s₀|) :=
          mul_le_mul_of_nonneg_left h_inv_le' (abs_nonneg _)
      _ = (C_inv * (2 * ‖V.totalPerturbation‖) * L_lip) * |s - s₀| ^ 2 := by ring
  have h_decomp : P_s - P₀ - (s - s₀) • P' =
      twoBlockDiagProj P₀ (P_s - P₀) + (twoBlockOffDiagProj P₀ (P_s - P₀) - (s - s₀) • P') := by
    rw [← add_sub_assoc, twoBlockDiagProj_add_twoBlockOffDiagProj]
  rw [h_decomp]
  calc ‖twoBlockDiagProj P₀ (P_s - P₀) + (twoBlockOffDiagProj P₀ (P_s - P₀) - (s - s₀) • P')‖
    _ ≤ ‖twoBlockDiagProj P₀ (P_s - P₀)‖ + ‖twoBlockOffDiagProj P₀ (P_s - P₀) - (s - s₀) • P'‖ :=
        norm_add_le _ _
    _ ≤ 2 * L_lip ^ 2 * |s - s₀| ^ 2 + (C_inv * (2 * ‖V.totalPerturbation‖) * L_lip) * |s - s₀| ^ 2 :=
        add_le_add h_diag h_off
    _ = K_rem * |s - s₀| ^ 2 := by ring

/-- Specialization of `hasDerivAt_perturbedGroundSpectralProj_of_band_gap` to
    `bhmPerturbedGap ≤ indexedSpectralGap sys V s₀`. -/
theorem hasDerivAt_perturbedGroundSpectralProj_of_gap {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s₀) :
    HasDerivAt (perturbedGroundSpectralProj sys V)
      (perturbedGroundSpectralProjDeriv sys V s₀) s₀ :=
  hasDerivAt_perturbedGroundSpectralProj_of_band_gap sys V s₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (fun _ hi _ hj => band_gap_of_bhmPerturbedGap_le_indexedSpectralGap sys V s₀ h_gap hi hj)

/-- **Derivative Existence for Perturbed Ground-Space Spectral Projectors (`exists_hasDerivAt_perturbedGroundSpectralProj_of_gap`)**. -/
theorem exists_hasDerivAt_perturbedGroundSpectralProj_of_gap {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s₀) :
    ∃ P_deriv : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      HasDerivAt (perturbedGroundSpectralProj sys V) P_deriv s₀ ∧
      IsSelfAdjoint P_deriv ∧
      twoBlockOffDiagProj (perturbedGroundSpectralProj sys V s₀) P_deriv = P_deriv :=
  ⟨perturbedGroundSpectralProjDeriv sys V s₀,
    hasDerivAt_perturbedGroundSpectralProj_of_gap sys V s₀ h_gap,
    isSelfAdjoint_perturbedGroundSpectralProjDeriv sys V s₀,
    twoBlockOffDiagProj_perturbedGroundSpectralProjDeriv sys V s₀⟩

/-- **Pointwise Differentiability of Perturbed Ground-Space Spectral Projectors (`differentiableAt_perturbedGroundSpectralProj_of_gap`)**. -/
theorem differentiableAt_perturbedGroundSpectralProj_of_gap {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s₀) :
    ∃ P_deriv : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      HasDerivAt (perturbedGroundSpectralProj sys V) P_deriv s₀ :=
  ⟨perturbedGroundSpectralProjDeriv sys V s₀,
    hasDerivAt_perturbedGroundSpectralProj_of_gap sys V s₀ h_gap⟩

/-! ## 3. $C^1$ Continuity of `deriv (perturbedGroundSpectralProj sys V)` & Kato Generator Bridge -/

/-- Norm bound on the difference of `twoBlockDiagProj` under two projections `P, P₀` of norm `≤ 1`:
    `‖twoBlockDiagProj P₀ X - twoBlockDiagProj P X‖ ≤ 4 * ‖P - P₀‖ * ‖X‖`. -/
lemma norm_twoBlockDiagProj_sub_twoBlockDiagProj_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P P₀ : E →L[ℂ] E} (hP : IsStarProjection P) (hP₀ : IsStarProjection P₀) (X : E →L[ℂ] E) :
    ‖twoBlockDiagProj P₀ X - twoBlockDiagProj P X‖ ≤ 4 * ‖P - P₀‖ * ‖X‖ := by
  have hP_norm : ‖P‖ ≤ 1 := isStarProjection_norm_le_one hP
  have hP₀_norm : ‖P₀‖ ≤ 1 := isStarProjection_norm_le_one hP₀
  have h1P_norm : ‖1 - P‖ ≤ 1 := isStarProjection_norm_le_one (isStarProjection_one_sub hP)
  have h1P₀_norm : ‖1 - P₀‖ ≤ 1 := isStarProjection_norm_le_one (isStarProjection_one_sub hP₀)
  unfold twoBlockDiagProj; rw [ring_twoBlockDiag_diff_decomp P P₀ X]
  have h1 : ‖-(P - P₀) * X * P₀‖ ≤ ‖P - P₀‖ * ‖X‖ := by
    rw [neg_mul, neg_mul, norm_neg]
    exact le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
      (le_trans (mul_le_mul (ContinuousLinearMap.opNorm_comp_le _ _) hP₀_norm (norm_nonneg _) (by positivity))
        (by rw [mul_one]))
  have h2 : ‖P * X * (P - P₀)‖ ≤ ‖P - P₀‖ * ‖X‖ := by
    rw [mul_assoc]
    calc ‖P * (X * (P - P₀))‖
      _ ≤ ‖P‖ * ‖X * (P - P₀)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖X‖ * ‖P - P₀‖) :=
          mul_le_mul hP_norm (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one
      _ = ‖P - P₀‖ * ‖X‖ := by ring
  have h3 : ‖(P - P₀) * X * (1 - P₀)‖ ≤ ‖P - P₀‖ * ‖X‖ :=
    le_trans (ContinuousLinearMap.opNorm_comp_le _ _)
      (le_trans (mul_le_mul (ContinuousLinearMap.opNorm_comp_le _ _) h1P₀_norm (norm_nonneg _) (by positivity))
        (by rw [mul_one]))
  have h4 : ‖(1 - P) * X * (P - P₀)‖ ≤ ‖P - P₀‖ * ‖X‖ := by
    rw [mul_assoc]
    calc ‖(1 - P) * (X * (P - P₀))‖
      _ ≤ ‖1 - P‖ * ‖X * (P - P₀)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (‖X‖ * ‖P - P₀‖) :=
          mul_le_mul h1P_norm (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one
      _ = ‖P - P₀‖ * ‖X‖ := by ring
  calc ‖-(P - P₀) * X * P₀ - P * X * (P - P₀) + (P - P₀) * X * (1 - P₀) + (1 - P) * X * (P - P₀)‖
    _ ≤ ‖-(P - P₀) * X * P₀ - P * X * (P - P₀) + (P - P₀) * X * (1 - P₀)‖ +
          ‖(1 - P) * X * (P - P₀)‖ := norm_add_le _ _
    _ ≤ ‖-(P - P₀) * X * P₀ - P * X * (P - P₀)‖ + ‖(P - P₀) * X * (1 - P₀)‖ +
          ‖(1 - P) * X * (P - P₀)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ ‖-(P - P₀) * X * P₀‖ + ‖P * X * (P - P₀)‖ + ‖(P - P₀) * X * (1 - P₀)‖ +
          ‖(1 - P) * X * (P - P₀)‖ := add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ ‖P - P₀‖ * ‖X‖ + ‖P - P₀‖ * ‖X‖ + ‖P - P₀‖ * ‖X‖ + ‖P - P₀‖ * ‖X‖ :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = 4 * ‖P - P₀‖ * ‖X‖ := by ring

/-- Helper: a local Lipschitz bound `‖g s - g s₀‖ ≤ K * |s - s₀|` on `|s - s₀| < δ` implies
    `ContinuousAt g s₀`. -/
lemma continuousAt_of_local_lipschitz {E : Type*} [SeminormedAddCommGroup E]
    {g : ℝ → E} {s₀ δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (h_lip : ∀ s : ℝ, |s - s₀| < δ → ‖g s - g s₀‖ ≤ K * |s - s₀|) :
    ContinuousAt g s₀ := by
  rw [Metric.continuousAt_iff]; intro ε hε
  have hK1_pos : 0 < K + 1 := by linarith
  refine ⟨min δ (ε / (K + 1)), lt_min hδ (div_pos hε hK1_pos), fun s hs => ?_⟩
  rw [Real.dist_eq] at hs; rw [dist_eq_norm]
  calc ‖g s - g s₀‖
    _ ≤ K * |s - s₀| := h_lip s (lt_of_lt_of_le hs (min_le_left _ _))
    _ ≤ (K + 1) * |s - s₀| := by nlinarith [abs_nonneg (s - s₀)]
    _ < (K + 1) * (ε / (K + 1)) :=
        mul_lt_mul_of_pos_left (lt_of_lt_of_le hs (min_le_right _ _)) hK1_pos
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hK1_pos)

/-- Under a band gap `Δ > 0` at `s₀`, `perturbedGroundSpectralProjDeriv sys V` is continuous at `s₀`. -/
theorem continuousAt_perturbedGroundSpectralProjDeriv_of_band_gap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i) :
    ContinuousAt (perturbedGroundSpectralProjDeriv sys V) s₀ := by
  let P₀ := perturbedGroundSpectralProj sys V s₀; let P'₀ := perturbedGroundSpectralProjDeriv sys V s₀
  let N_prod : ℝ := ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ)
  let L_lip : ℝ := 4 * N_prod * Δ⁻¹ * ‖V.totalPerturbation‖; let C_inv : ℝ := 2 * N_prod * Δ⁻¹
  let M_deriv : ℝ := 4 * N_prod * (Δ / 2)⁻¹ * ‖V.totalPerturbation‖
  let K_lip : ℝ := 4 * L_lip * M_deriv + C_inv * (2 * ‖V.totalPerturbation‖ * L_lip + 2 * ‖V.totalPerturbation‖ * M_deriv)
  let δ : ℝ := (Δ / 4) / (‖V.totalPerturbation‖ + 1)
  have hV1_pos : 0 < ‖V.totalPerturbation‖ + 1 := by positivity
  have hδ_pos : 0 < δ := div_pos (by linarith) hV1_pos
  have hΔ2_pos : 0 < Δ / 2 := half_pos hΔ
  have hC_nn : 0 ≤ C_inv := by positivity
  have hK_nn : 0 ≤ K_lip := by positivity
  refine continuousAt_of_local_lipschitz hδ_pos hK_nn fun s hs => ?_
  let P_s := perturbedGroundSpectralProj sys V s; let P'_s := perturbedGroundSpectralProjDeriv sys V s
  let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
  let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
  have hs_V : |s - s₀| * ‖V.totalPerturbation‖ ≤ Δ / 4 := by
    calc |s - s₀| * ‖V.totalPerturbation‖
      _ ≤ |s - s₀| * (‖V.totalPerturbation‖ + 1) := by nlinarith [abs_nonneg (s - s₀)]
      _ ≤ δ * (‖V.totalPerturbation‖ + 1) := mul_le_mul_of_nonneg_right (le_of_lt hs) (le_of_lt hV1_pos)
      _ = Δ / 4 := div_mul_cancel₀ (Δ / 4) (ne_of_gt hV1_pos)
  have h_gap_s : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
      let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
      Δ / 2 ≤ sortedEigenvalues H_s hHs j - sortedEigenvalues H_s hHs i :=
    fun _ hi _ hj => (cross_band_gap_ge_half_delta_of_norm_mul_le sys V s₀ s h_gap hs_V hi hj).2.2
  have h_lip : ‖P_s - P₀‖ ≤ L_lip * |s - s₀| := by
    convert norm_perturbedGroundSpectralProj_sub_le_of_band_gap sys V s₀ s hΔ h_gap hs_V using 1; ring
  have h_M : ‖P'_s‖ ≤ M_deriv := by
    convert norm_perturbedGroundSpectralProjDeriv_le_of_band_gap sys V s hΔ2_pos h_gap_s using 1; ring
  have h_diag : ‖twoBlockDiagProj P₀ (P'_s - P'₀)‖ ≤ (4 * L_lip * M_deriv) * |s - s₀| := by
    have h_eq : twoBlockDiagProj P₀ (P'_s - P'₀) =
        twoBlockDiagProj P₀ P'_s - twoBlockDiagProj P_s P'_s := by
      have h_d0 := twoBlockDiagProj_perturbedGroundSpectralProjDeriv_eq_zero sys V s₀
      have h_ds := twoBlockDiagProj_perturbedGroundSpectralProjDeriv_eq_zero sys V s
      have h_lin : twoBlockDiagProj P₀ (P'_s - P'₀) =
          twoBlockDiagProj P₀ P'_s - twoBlockDiagProj P₀ P'₀ := by
        unfold twoBlockDiagProj; simp only [mul_sub, sub_mul]; abel
      rw [h_lin, h_d0, h_ds]
    rw [h_eq]
    calc ‖twoBlockDiagProj P₀ P'_s - twoBlockDiagProj P_s P'_s‖
      _ ≤ 4 * ‖P_s - P₀‖ * ‖P'_s‖ := norm_twoBlockDiagProj_sub_twoBlockDiagProj_le
          (isStarProjection_perturbedGroundSpectralProj sys V s)
          (isStarProjection_perturbedGroundSpectralProj sys V s₀) P'_s
      _ ≤ 4 * (L_lip * |s - s₀|) * M_deriv :=
          mul_le_mul (mul_le_mul_of_nonneg_left h_lip (by norm_num)) h_M (norm_nonneg _) (by positivity)
      _ = (4 * L_lip * M_deriv) * |s - s₀| := by ring
  have h_off : ‖twoBlockOffDiagProj P₀ (P'_s - P'₀)‖ ≤
      (C_inv * (2 * ‖V.totalPerturbation‖ * L_lip + 2 * ‖V.totalPerturbation‖ * M_deriv)) * |s - s₀| := by
    have h_inv := (sylvesterOffDiagInverse_commutator_eq_twoBlockOffDiagProj
      sys V s₀ hΔ h_gap (P'_s - P'₀)).symm
    (try dsimp only at h_inv); rw [h_inv]
    have h_comm0 := commutator_H_s_perturbedGroundSpectralProjDeriv_eq_of_band_gap sys V s₀ hΔ h_gap
    have h_comms := commutator_H_s_perturbedGroundSpectralProjDeriv_eq_of_band_gap sys V s hΔ2_pos h_gap_s
    have h_H_diff := hamiltonian_scaleQuasiLocalPerturbation_sub sys V s₀ s
    have h_comm_diff : H₀ * (P'_s - P'₀) - (P'_s - P'₀) * H₀ =
        ((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)) -
          ((s - s₀ : ℝ) : ℂ) • (V.totalPerturbation * P'_s - P'_s * V.totalPerturbation) := by
      calc H₀ * (P'_s - P'₀) - (P'_s - P'₀) * H₀
        _ = (H_s * P'_s - P'_s * H_s) - (H₀ * P'₀ - P'₀ * H₀) -
              ((H_s - H₀) * P'_s - P'_s * (H_s - H₀)) := ring_commutator_sub_decomp H₀ H_s P'₀ P'_s
        _ = (P_s * V.totalPerturbation - V.totalPerturbation * P_s) - (P₀ * V.totalPerturbation - V.totalPerturbation * P₀) -
              ((((s - s₀ : ℝ) : ℂ) • V.totalPerturbation) * P'_s -
                P'_s * (((s - s₀ : ℝ) : ℂ) • V.totalPerturbation)) := by rw [h_comms, h_comm0, h_H_diff]
        _ = ((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)) -
              ((s - s₀ : ℝ) : ℂ) • (V.totalPerturbation * P'_s - P'_s * V.totalPerturbation) := by
            rw [smul_mul_assoc, mul_smul_comm, ← clm_smul_sub]
            congr 1; simp only [sub_mul, mul_sub]; abel
    have h_rhs_norm : ‖H₀ * (P'_s - P'₀) - (P'_s - P'₀) * H₀‖ ≤
        (2 * ‖V.totalPerturbation‖ * L_lip + 2 * ‖V.totalPerturbation‖ * M_deriv) * |s - s₀| := by
      rw [h_comm_diff]
      have h_t1 : ‖(P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)‖ ≤ 2 * ‖V.totalPerturbation‖ * L_lip * |s - s₀| := by
        calc ‖(P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)‖
          _ ≤ ‖(P_s - P₀) * V.totalPerturbation‖ + ‖V.totalPerturbation * (P_s - P₀)‖ := norm_sub_le _ _
          _ ≤ ‖P_s - P₀‖ * ‖V.totalPerturbation‖ + ‖V.totalPerturbation‖ * ‖P_s - P₀‖ :=
              add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
          _ = 2 * ‖V.totalPerturbation‖ * ‖P_s - P₀‖ := by ring
          _ ≤ 2 * ‖V.totalPerturbation‖ * (L_lip * |s - s₀|) := mul_le_mul_of_nonneg_left h_lip (by positivity)
          _ = 2 * ‖V.totalPerturbation‖ * L_lip * |s - s₀| := by ring
      have h_t2 : ‖((s - s₀ : ℝ) : ℂ) • (V.totalPerturbation * P'_s - P'_s * V.totalPerturbation)‖ ≤
          2 * ‖V.totalPerturbation‖ * M_deriv * |s - s₀| := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        have h_vp : ‖V.totalPerturbation * P'_s - P'_s * V.totalPerturbation‖ ≤ 2 * ‖V.totalPerturbation‖ * M_deriv := by
          calc ‖V.totalPerturbation * P'_s - P'_s * V.totalPerturbation‖
            _ ≤ ‖V.totalPerturbation * P'_s‖ + ‖P'_s * V.totalPerturbation‖ := norm_sub_le _ _
            _ ≤ ‖V.totalPerturbation‖ * ‖P'_s‖ + ‖P'_s‖ * ‖V.totalPerturbation‖ :=
                add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
            _ = 2 * ‖V.totalPerturbation‖ * ‖P'_s‖ := by ring
            _ ≤ 2 * ‖V.totalPerturbation‖ * M_deriv := mul_le_mul_of_nonneg_left h_M (by positivity)
        calc |s - s₀| * ‖V.totalPerturbation * P'_s - P'_s * V.totalPerturbation‖
          _ ≤ |s - s₀| * (2 * ‖V.totalPerturbation‖ * M_deriv) := mul_le_mul_of_nonneg_left h_vp (abs_nonneg _)
          _ = 2 * ‖V.totalPerturbation‖ * M_deriv * |s - s₀| := by ring
      calc ‖((P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)) -
            ((s - s₀ : ℝ) : ℂ) • (V.totalPerturbation * P'_s - P'_s * V.totalPerturbation)‖
        _ ≤ ‖(P_s - P₀) * V.totalPerturbation - V.totalPerturbation * (P_s - P₀)‖ +
              ‖((s - s₀ : ℝ) : ℂ) • (V.totalPerturbation * P'_s - P'_s * V.totalPerturbation)‖ := norm_sub_le _ _
        _ ≤ 2 * ‖V.totalPerturbation‖ * L_lip * |s - s₀| + 2 * ‖V.totalPerturbation‖ * M_deriv * |s - s₀| := add_le_add h_t1 h_t2
        _ = (2 * ‖V.totalPerturbation‖ * L_lip + 2 * ‖V.totalPerturbation‖ * M_deriv) * |s - s₀| := by ring
    have h_inv_le := norm_sylvesterOffDiagInverse_le_of_band_gap sys V s₀ hΔ h_gap
      (H₀ * (P'_s - P'₀) - (P'_s - P'₀) * H₀)
    calc ‖sylvesterOffDiagInverse sys V s₀ (H₀ * (P'_s - P'₀) - (P'_s - P'₀) * H₀)‖
      _ ≤ C_inv * ‖H₀ * (P'_s - P'₀) - (P'_s - P'₀) * H₀‖ := by convert h_inv_le using 1; ring
      _ ≤ C_inv * ((2 * ‖V.totalPerturbation‖ * L_lip + 2 * ‖V.totalPerturbation‖ * M_deriv) * |s - s₀|) :=
          mul_le_mul_of_nonneg_left h_rhs_norm hC_nn
      _ = (C_inv * (2 * ‖V.totalPerturbation‖ * L_lip + 2 * ‖V.totalPerturbation‖ * M_deriv)) * |s - s₀| := by ring
  rw [← twoBlockDiagProj_add_twoBlockOffDiagProj P₀ (P'_s - P'₀)]
  calc ‖twoBlockDiagProj P₀ (P'_s - P'₀) + twoBlockOffDiagProj P₀ (P'_s - P'₀)‖
    _ ≤ ‖twoBlockDiagProj P₀ (P'_s - P'₀)‖ + ‖twoBlockOffDiagProj P₀ (P'_s - P'₀)‖ := norm_add_le _ _
    _ ≤ (4 * L_lip * M_deriv) * |s - s₀| +
          (C_inv * (2 * ‖V.totalPerturbation‖ * L_lip + 2 * ‖V.totalPerturbation‖ * M_deriv)) * |s - s₀| := add_le_add h_diag h_off
    _ = K_lip * |s - s₀| := by ring

/-- Whenever `bhmPerturbedGap ≤ indexedSpectralGap sys V s₀`, `deriv (perturbedGroundSpectralProj sys V)`
    is continuous at `s₀`. -/
theorem continuousAt_deriv_perturbedGroundSpectralProj_of_gap {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s₀) :
    ContinuousAt (deriv (perturbedGroundSpectralProj sys V)) s₀ := by
  have h_band : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      (1 / 2 : ℝ) ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i :=
    fun _ hi _ hj => band_gap_of_bhmPerturbedGap_le_indexedSpectralGap sys V s₀ h_gap hi hj
  have h_cont := continuousAt_perturbedGroundSpectralProjDeriv_of_band_gap sys V s₀ (by norm_num) h_band
  let δ : ℝ := ((1 / 2 : ℝ) / 4) / (‖V.totalPerturbation‖ + 1)
  have hV1_pos : 0 < ‖V.totalPerturbation‖ + 1 := by positivity
  have hδ_pos : 0 < δ := div_pos (by norm_num) hV1_pos
  have h_ev : deriv (perturbedGroundSpectralProj sys V) =ᶠ[𝓝 s₀]
      perturbedGroundSpectralProjDeriv sys V := by
    filter_upwards [Metric.ball_mem_nhds s₀ hδ_pos] with s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have hs_V : |s - s₀| * ‖V.totalPerturbation‖ ≤ (1 / 2 : ℝ) / 4 := by
      calc |s - s₀| * ‖V.totalPerturbation‖
        _ ≤ |s - s₀| * (‖V.totalPerturbation‖ + 1) := by nlinarith [abs_nonneg (s - s₀)]
        _ ≤ δ * (‖V.totalPerturbation‖ + 1) := mul_le_mul_of_nonneg_right (le_of_lt hs) (le_of_lt hV1_pos)
        _ = (1 / 2 : ℝ) / 4 := div_mul_cancel₀ _ (ne_of_gt hV1_pos)
    have h_band_s : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
        let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
        let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
        (1 / 2 : ℝ) / 2 ≤ sortedEigenvalues H_s hHs j - sortedEigenvalues H_s hHs i :=
      fun _ hi _ hj => (cross_band_gap_ge_half_delta_of_norm_mul_le sys V s₀ s h_band hs_V hi hj).2.2
    exact (hasDerivAt_perturbedGroundSpectralProj_of_band_gap sys V s (by norm_num) h_band_s).deriv
  exact h_cont.congr_of_eventuallyEq h_ev

/-- **$C^1$ Continuity on the Gapped Regime (`continuousOn_deriv_perturbedGroundSpectralProj`)**:
    `s ↦ deriv (perturbedGroundSpectralProj sys V) s` is continuous on
    `{s : ℝ | bhmPerturbedGap ≤ indexedSpectralGap sys V s}`. -/
theorem continuousOn_deriv_perturbedGroundSpectralProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    ContinuousOn (deriv (perturbedGroundSpectralProj sys V))
      {s : ℝ | bhmPerturbedGap ≤ indexedSpectralGap sys V s} :=
  fun s₀ hs₀ =>
    (continuousAt_deriv_perturbedGroundSpectralProj_of_gap sys V s₀ hs₀).continuousWithinAt

/-- **Kato–Sylvester Commutator Bridge (`perturbedGroundSpectralProjDeriv_eq_commutator_of_sylvester_eq`)**:
    Whenever `bhmPerturbedGap ≤ indexedSpectralGap sys V s₀` and an operator `D` satisfies
    `(Complex.I : ℂ) • (D * H(s₀) - H(s₀) * D) = twoBlockOffDiagProj P(s₀) V.V_tot`,
    `perturbedGroundSpectralProjDeriv sys V s₀ = (Complex.I : ℂ) • (D * P(s₀) - P(s₀) * D)`
    and `HasDerivAt (perturbedGroundSpectralProj sys V) ((Complex.I : ℂ) • (D * P(s₀) - P(s₀) * D)) s₀`. -/
theorem perturbedGroundSpectralProjDeriv_eq_commutator_of_sylvester_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s₀)
    {D_gen : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_sylv :
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let P₀ := perturbedGroundSpectralProj sys V s₀
      (Complex.I : ℂ) • (D_gen * H₀ - H₀ * D_gen) = twoBlockOffDiagProj P₀ V.totalPerturbation) :
    let P₀ := perturbedGroundSpectralProj sys V s₀
    perturbedGroundSpectralProjDeriv sys V s₀ = (Complex.I : ℂ) • (D_gen * P₀ - P₀ * D_gen) ∧
    HasDerivAt (perturbedGroundSpectralProj sys V)
      ((Complex.I : ℂ) • (D_gen * P₀ - P₀ * D_gen)) s₀ := by
  intro P₀
  let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
  let Z := (Complex.I : ℂ) • (D_gen * P₀ - P₀ * D_gen)
  have hP₀_idem : P₀ * P₀ = P₀ :=
    (isStarProjection_perturbedGroundSpectralProj sys V s₀).isIdempotentElem.eq
  have hHP₀ : H₀ * P₀ = P₀ * H₀ := (commute_perturbedGroundSpectralProj sys V s₀).eq
  have hZ_off : twoBlockOffDiagProj P₀ Z = Z := by
    have h_neg : D_gen * P₀ - P₀ * D_gen = -(P₀ * D_gen - D_gen * P₀) := by abel
    dsimp [Z]; rw [h_neg, smul_neg]; unfold twoBlockOffDiagProj
    rw [mul_neg, neg_mul, mul_neg, neg_mul, ← neg_add, mul_smul_comm, smul_mul_assoc,
      mul_smul_comm, smul_mul_assoc, ← clm_smul_add]
    congr 2; exact twoBlockOffDiagProj_commutator_proj_eq_self hP₀_idem D_gen
  have h_jacobi : H₀ * Z - Z * H₀ =
      P₀ * ((Complex.I : ℂ) • (D_gen * H₀ - H₀ * D_gen)) -
        ((Complex.I : ℂ) • (D_gen * H₀ - H₀ * D_gen)) * P₀ := by
    dsimp [Z]
    rw [mul_smul_comm, smul_mul_assoc, ← clm_smul_sub, mul_smul_comm, smul_mul_assoc, ← clm_smul_sub]
    congr 1; exact ring_jacobi_commute hHP₀ D_gen
  have h_comm_Z : H₀ * Z - Z * H₀ = P₀ * V.totalPerturbation - V.totalPerturbation * P₀ := by
    rw [h_jacobi, h_sylv]; exact ring_commutator_proj_offDiag hP₀_idem V.totalPerturbation
  have h_band : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      (1 / 2 : ℝ) ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i :=
    fun _ hi _ hj => band_gap_of_bhmPerturbedGap_le_indexedSpectralGap sys V s₀ h_gap hi hj
  have h_eq : perturbedGroundSpectralProjDeriv sys V s₀ = Z := by
    calc perturbedGroundSpectralProjDeriv sys V s₀
      _ = sylvesterOffDiagInverse sys V s₀ (H₀ * Z - Z * H₀) := by
          unfold perturbedGroundSpectralProjDeriv; rw [h_comm_Z]
      _ = twoBlockOffDiagProj P₀ Z :=
          sylvesterOffDiagInverse_commutator_eq_twoBlockOffDiagProj sys V s₀ (by norm_num) h_band Z
      _ = Z := hZ_off
  refine ⟨h_eq, ?_⟩
  change HasDerivAt (perturbedGroundSpectralProj sys V) Z s₀
  rw [← h_eq]
  exact hasDerivAt_perturbedGroundSpectralProj_of_gap sys V s₀ h_gap

end
