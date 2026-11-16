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

import Proofs.BandLimitedFilter.SmoothBandpassFilterKernel
import Proofs.HastingsKomaLightCone.BareFrameBQLightConeAndTwoBlockNorm

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Band-Limited Tail Profiles and Eigenpair Off-Diagonal Annihilation

Defines universal superpolynomial tail profiles (`bdlBandLimitedBaseMoment`, `bdlBandLimitedTailProfile`, `isSuperpolynomialDecay_bdlBandLimitedTailProfile`), bounds two-block conditional-expectation remainders (`norm_twoBlockDiagProj_sub_condExp_le_add_offDiag_condExp`, `norm_bare_bochnerFilteredOp_sitePerturbationOp_weight_inhomogeneous_le`), and proves eigenpair off-diagonal annihilation for gap-matched Bochner filters (`eigenpair_sandwich_bochnerFilteredOp_eq_zero_of_gap_ge_half`).

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`), Equations (71)–(72) (`eq:bochner-bare-V-tail`, `eq:bochner-bare-Q-tail`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (78) (`eq:Xu-norm-and-tail`)
-/

attribute [local irreducible] collarConstRCABDL bdlLambda qCodeBDL r0BDL mMaxBDL

/-- Conditional expectation error of `twoBlockDiagProj P X` bounded by `X` and `twoBlockOffDiagProj P X`. -/
theorem norm_twoBlockDiagProj_sub_condExp_le_add_offDiag_condExp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (P X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖twoBlockDiagProj P X - condExp Site A (twoBlockDiagProj P X)‖ ≤
      ‖X - condExp Site A X‖ +
      ‖twoBlockOffDiagProj P X - condExp Site A (twoBlockOffDiagProj P X)‖ := by
  have h_eq : twoBlockDiagProj P X = X - twoBlockOffDiagProj P X := by
    rw [← sub_twoBlockDiagProj_eq_twoBlockOffDiagProj, sub_sub_cancel]
  have h_sub : twoBlockDiagProj P X - condExp Site A (twoBlockDiagProj P X) =
      (X - condExp Site A X) -
      (twoBlockOffDiagProj P X - condExp Site A (twoBlockOffDiagProj P X)) := by
    rw [h_eq, condExp_sub_clm]; abel
  rw [h_sub]; exact norm_sub_le _ _

/-- Bare-frame norm bound for `bochnerFilteredOp H_s w (sitePerturbationOp V_s u)`. -/
theorem norm_bare_bochnerFilteredOp_sitePerturbationOp_weight_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem J s : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (w : ℝ → ℂ) (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1)
    (hf : IsSuperpolynomialDecay f) (hV_dec : V.SatisfiesDecayBound J f) (u : Box3D L) :
    let V_s := scaleQuasiLocalPerturbation s V
    let H_s := mem.sys.H0 + V_s.totalPerturbation
    ‖bochnerFilteredOp H_s w (sitePerturbationOp V_s u)‖ ≤
      J * ((∫ t : ℝ, ‖w t‖) * ∑' q : ℕ, (q : ℝ) ^ 3 * f q) := by
  intro V_s H_s
  have hHs_sa : IsSelfAdjoint H_s :=
    isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have h1 := norm_bochnerFilteredOp_le hHs_sa w (sitePerturbationOp V_s u)
  have h2 := norm_sitePerturbationOp_inhomogeneous_le V hJ_nn hs hf hV_dec u
  have hw_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ := integral_nonneg fun _ => norm_nonneg _
  calc ‖bochnerFilteredOp H_s w (sitePerturbationOp V_s u)‖
    _ ≤ (∫ t : ℝ, ‖w t‖) * ‖sitePerturbationOp V_s u‖ := h1
    _ ≤ (∫ t : ℝ, ‖w t‖) * (J * ∑' q : ℕ, (q : ℝ) ^ 3 * f q) :=
      mul_le_mul_of_nonneg_left h2 hw_nn
    _ = J * ((∫ t : ℝ, ‖w t‖) * ∑' q : ℕ, (q : ℝ) ^ 3 * f q) := by ring

/-- Calibrated $L$-independent zero-mode base moment `m_0` for a band-limited filter weight `w`. -/
def bdlBandLimitedBaseMoment (w : ℝ → ℂ) (f : ℕ → ℝ) (c_U_Q : ℝ) : ℝ :=
  2 * ((∫ t : ℝ, ‖w t‖) * (∑' q : ℕ, (q : ℝ) ^ 3 * f q) +
    (∫ t : ℝ, ‖w t‖ * |t|) *
      (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f) +
    c_U_Q)

lemma bdlBandLimitedBaseMoment_nonneg (w : ℝ → ℂ) {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {c_U_Q : ℝ} (hc_UQ : 0 ≤ c_U_Q) :
    0 ≤ bdlBandLimitedBaseMoment w f c_U_Q := by
  unfold bdlBandLimitedBaseMoment
  have hw_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ := integral_nonneg fun _ => norm_nonneg _
  have hwt_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ * |t| :=
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have h1 : 0 ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
    tsum_nonneg fun q => mul_nonneg (by positivity) (hf.1 q)
  have h2 := bdlInhomogeneousSiteWeightBound_nonneg
  have h3 := bdlInhomogeneousCommutatorBound_nonneg hf
  positivity

/-- Calibrated $L$-independent multi-scale `boxBall u j` tail profile for `bochnerFilteredSiteOp`
    with band-limited filter weight `w`. -/
def bdlBandLimitedTailProfile (w : ℝ → ℂ)
    (f g_bare_V g_bare_Q ε_LR_box g_LR_Q : ℕ → ℝ) (j : ℕ) : ℝ :=
  2 * g_bare_V j + 2 * g_bare_Q j +
  ε_LR_box j * ((∫ t : ℝ, ‖w t‖) * (∑' q : ℕ, (q : ℝ) ^ 3 * f q) +
    (∫ t : ℝ, ‖w t‖ * |t|) *
      (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f)) +
  g_LR_Q j

theorem isSuperpolynomialDecay_bdlBandLimitedTailProfile (w : ℝ → ℂ)
    {f g_bare_V g_bare_Q ε_LR_box g_LR_Q : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f)
    (hg_V : IsSuperpolynomialDecay g_bare_V)
    (hg_Q : IsSuperpolynomialDecay g_bare_Q)
    (hε_box : IsSuperpolynomialDecay ε_LR_box)
    (hg_LR_Q : IsSuperpolynomialDecay g_LR_Q) :
    IsSuperpolynomialDecay (bdlBandLimitedTailProfile w f g_bare_V g_bare_Q ε_LR_box g_LR_Q) := by
  have hw_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ := integral_nonneg fun _ => norm_nonneg _
  have hwt_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ * |t| :=
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have h_sum_nn : 0 ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
    tsum_nonneg fun q => mul_nonneg (by positivity) (hf.1 q)
  have hW_nn := bdlInhomogeneousSiteWeightBound_nonneg
  have hC_nn := bdlInhomogeneousCommutatorBound_nonneg hf
  let C_mid : ℝ := (∫ t : ℝ, ‖w t‖) * (∑' q : ℕ, (q : ℝ) ^ 3 * f q) +
    (∫ t : ℝ, ‖w t‖ * |t|) *
      (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f)
  have hC_mid_nn : 0 ≤ C_mid := by positivity
  have h1 := isSuperpolynomialDecay_const_mul hg_V zero_le_two
  have h2 := isSuperpolynomialDecay_const_mul hg_Q zero_le_two
  have h3 : IsSuperpolynomialDecay (fun j => ε_LR_box j * C_mid) := by
    have h3' := isSuperpolynomialDecay_const_mul hε_box hC_mid_nn
    convert h3' using 1; ext j; ring
  exact isSuperpolynomialDecay_add (isSuperpolynomialDecay_add (isSuperpolynomialDecay_add h1 h2) h3)
    hg_LR_Q

/-- For any `IsSmoothBandpassFilterWeight w` (such as `bandpassFilterWeight`), any eigenprojectors `P_A`, `P_B`
    of a self-adjoint `H'` with real eigenvalues `E_A`, `E_B` separated by `(1 / 2 : ℝ) ≤ |E_A - E_B|`
    annihilate `bochnerFilteredOp H' w X` (`P_A * bochnerFilteredOp H' w X * P_B = 0`). -/
theorem eigenpair_sandwich_bochnerFilteredOp_eq_zero_of_gap_ge_half {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P_A P_B H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E_A E_B : ℝ} {w : ℝ → ℂ} (hH' : IsSelfAdjoint H') (hw : IsSmoothBandpassFilterWeight w)
    (hPA : P_A * H' = (E_A : ℂ) • P_A) (hPB : H' * P_B = (E_B : ℂ) • P_B)
    (h_gap : (1 / 2 : ℝ) ≤ |E_A - E_B|)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    P_A * bochnerFilteredOp H' w X * P_B = 0 := by
  have h_sand := clm_sandwich_integral_smul P_A P_B w (fun t => heisenbergFlow H' t X)
    (integrable_smul_heisenbergFlow_of_integrable hH' hw.integrable X)
  change P_A * (∫ t : ℝ, w t • heisenbergFlow H' t X) * P_B = 0
  rw [h_sand]
  have h_pt : (fun t : ℝ => w t • (P_A * heisenbergFlow H' t X * P_B)) =
      (fun t : ℝ => (w t * Complex.exp (Complex.I * ((E_A - E_B : ℝ) : ℂ) * (t : ℂ))) •
        (P_A * X * P_B)) := by
    funext t
    have hL : P_A * timeEvolutionOp H' t =
        NormedSpace.exp ((Complex.I * (t : ℂ) * (E_A : ℂ)) •
          (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) * P_A := by
      change P_A * NormedSpace.exp ((Complex.I * (t : ℂ)) • H') = _
      rw [clm_proj_mul_exp_smul hPA (Complex.I * (t : ℂ)),
        (commute_exp_smul_one (Complex.I * (t : ℂ) * (E_A : ℂ)) P_A).eq]
    have hR : timeEvolutionOp H' (-t) * P_B =
        P_B * NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E_B : ℂ))) •
          (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) := by
      rw [timeEvolutionOp_neg_eq, clm_exp_smul_mul_proj hPB (-(Complex.I * (t : ℂ))), neg_mul,
        (commute_exp_smul_one (-(Complex.I * (t : ℂ) * (E_B : ℂ))) P_B).eq]
    dsimp [heisenbergFlow]
    rw [monoid_sandwich_rew hL hR, clm_exp_smul_one, clm_exp_smul_one,
      clm_smul_one_sandwich, smul_smul, ← Complex.exp_add]
    have h_exp : Complex.I * (t : ℂ) * (E_A : ℂ) + -(Complex.I * (t : ℂ) * (E_B : ℂ)) =
        Complex.I * ((E_A - E_B : ℝ) : ℂ) * (t : ℂ) := by push_cast; ring
    rw [h_exp]
  rw [h_pt, integral_smul_const,
    hw.fourier_eq_zero_of_abs_ge_half (E_A - E_B) h_gap, zero_smul]

end
