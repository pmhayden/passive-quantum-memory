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

import Proofs.DressedThermalDuhamel.PerturbedKMSBallImmunitySynthesis

/-!
# Pinched KMS Norm Commutator Bounds and Bath Dissipator Inner-Product Estimates

Establishes operator KMS-norm bounds for commutators in terms of pinched unsafe-subspace residuals and Gibbs failure probabilities (`opKMSNorm_commutator_le_gibbsFailureProb_of_pinched_le`, `half_opKMSNormSq_opCommutator_le_of_pinched_sq_le`). Combines these bounds with KMS detailed balance to control the real KMS inner product of local bath dissipators (`kms_bath_dissipator_inner_sub_le_of_pinched_sq_le`).

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

set_option maxRecDepth 200000

/-! ## 1. Coherent KMS Drift Bound with Safe-Subspace Residual $\delta_{\mathrm{split}}$ -/

/-- For any self-adjoint Hamiltonian `H` and star-projection `Pi_dress`, the Gibbs failure
probability `gibbsFailureProb H hH β (1 - Pi_dress)` is non-negative. -/
lemma gibbsFailureProb_one_sub_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) {Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_dress) :
    0 ≤ gibbsFailureProb H hH β (1 - Pi_dress) :=
  hilbertTrace_gibbsDensityOp_mul_proj_nonneg
    (opEigenbasis H hH) (opEigenvalues H hH) β
    (opEigenbasis_orthonormal H hH)
    (hilbertTrace_eq_sum_opEigenbasis H hH) hPi.one_sub

/-- **General KMS Norm Bound with Pinched Safe-Subspace Residual (`opKMSNorm_le_two_mul_norm_add_pinched_bound`)**:
For any operator `C`, star-projection `Pi_dress`, failure probability bound
`gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail`, and safe-subspace residual bound
`‖Pi_dress * C * Pi_dress‖ ≤ δ_split`,
$$\|C\|_{\mathrm{KMS}, H} \le 2 \|C\| \, p_{\mathrm{fail}}^{1/4} + \delta_{\mathrm{split}}.$$ -/
theorem opKMSNorm_le_two_mul_norm_add_pinched_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) {Pi_dress C : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_dress)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (h_pinch : ‖Pi_dress * C * Pi_dress‖ ≤ δ_split) :
    opKMSNorm H hH β C ≤ 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) + δ_split := by
  have h_raw := opKMSNorm_le_two_mul_norm_add_sandwich_norm H hH β hPi hp_le (C := C)
  linarith

/-- **Coherent KMS Drift Bound under Approximate Safe-Subspace Commutation
(`opKMSNorm_commutator_le_of_pinched_le`)**:
If `‖Pi_dress * (H * O_dress - O_dress * H) * Pi_dress‖ ≤ δ_split` and
`gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail`, then
$$\|H O_{\mathrm{dress}} - O_{\mathrm{dress}} H\|_{\mathrm{KMS}, H}
  \le 2 \|H O_{\mathrm{dress}} - O_{\mathrm{dress}} H\| \, p_{\mathrm{fail}}^{1/4} + \delta_{\mathrm{split}}.$$ -/
theorem opKMSNorm_commutator_le_of_pinched_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_dress)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (h_pinch : ‖Pi_dress * (H * O_dress - O_dress * H) * Pi_dress‖ ≤ δ_split) :
    opKMSNorm H hH β (H * O_dress - O_dress * H) ≤
      2 * ‖H * O_dress - O_dress * H‖ * (p_fail ^ (1 / 4 : ℝ)) + δ_split :=
  opKMSNorm_le_two_mul_norm_add_pinched_bound H hH β hPi hp_le h_pinch

/-- Specialization of `opKMSNorm_commutator_le_of_pinched_le` with `p_fail` equal to the exact
dressed Gibbs failure probability `gibbsFailureProb H hH β (1 - Pi_dress)`. -/
theorem opKMSNorm_commutator_le_gibbsFailureProb_of_pinched_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_dress)
    {δ_split : ℝ}
    (h_pinch : ‖Pi_dress * (H * O_dress - O_dress * H) * Pi_dress‖ ≤ δ_split) :
    opKMSNorm H hH β (H * O_dress - O_dress * H) ≤
      2 * ‖H * O_dress - O_dress * H‖ *
        ((gibbsFailureProb H hH β (1 - Pi_dress)) ^ (1 / 4 : ℝ)) + δ_split :=
  opKMSNorm_commutator_le_of_pinched_le H hH β O_dress Pi_dress hPi le_rfl h_pinch

/-! ## 2. Single-Channel & Bath-Summed KMS Dirichlet Form Bounds -/

private lemma half_sq_le_add_sq_of_le_add {x a b : ℝ} (hx : 0 ≤ x) (h : x ≤ a + b) :
    (1 / 2 : ℝ) * x ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have h1 : x ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have h2 : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h_diff : 2 * (a ^ 2 + b ^ 2) - (a + b) ^ 2 = (a - b) ^ 2 := by ring
    linarith [sq_nonneg (a - b)]
  linarith

/-- **Single-Channel KMS Dirichlet Form Decomposition (`half_opKMSNormSq_opCommutator_le_add_pinched_sq`)**:
For any operator `L_op`, observable `O_dress` with `‖O_dress‖ ≤ 1`, and star-projection `Pi_dress`
with `gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail`,
$$\frac{1}{2} \|[L_{\mathrm{op}}, O_{\mathrm{dress}}]\|_{\mathrm{KMS}, H}^2
  \le 16 \|L_{\mathrm{op}}\|^2 \, p_{\mathrm{fail}}^{1/2}
    + \|\Pi_{\mathrm{dress}} [L_{\mathrm{op}}, O_{\mathrm{dress}}] \Pi_{\mathrm{dress}}\|^2.$$ -/
theorem half_opKMSNormSq_opCommutator_le_add_pinched_sq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (L_op O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_norm : ‖O_dress‖ ≤ 1)
    (hPi : IsStarProjection Pi_dress)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail) :
    (1 / 2 : ℝ) * opKMSNormSq H hH β (opCommutator L_op O_dress) ≤
      16 * ‖L_op‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) +
        ‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 := by
  have h_onb := opEigenbasis_orthonormal H hH
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H hH
  set ψ_eig := opEigenbasis H hH
  set E_eig := opEigenvalues H hH
  have hP_fail : IsStarProjection (1 - Pi_dress) := hPi.one_sub
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP_fail) hp_le
  have h_rpow_nn : 0 ≤ p_fail ^ (1 / 4 : ℝ) := Real.rpow_nonneg hp_nonneg _
  set C := opCommutator L_op O_dress
  have h_raw : opKMSNorm H hH β C ≤ ‖Pi_dress * C * Pi_dress‖ + 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) :=
    opKMSNorm_le_two_mul_norm_add_sandwich_norm H hH β hPi hp_le (C := C)
  have hC_norm : ‖C‖ ≤ 2 * ‖L_op‖ := norm_opCommutator_le_two_mul L_op hO_norm
  have h_norm_le :
      opKMSNorm H hH β C ≤ 4 * ‖L_op‖ * (p_fail ^ (1 / 4 : ℝ)) + ‖Pi_dress * C * Pi_dress‖ := by
    have h_mul : 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) ≤ 4 * ‖L_op‖ * (p_fail ^ (1 / 4 : ℝ)) := by
      nlinarith
    linarith
  have h_kms_nn : 0 ≤ opKMSNorm H hH β C := Real.sqrt_nonneg _
  have h_sq_eq : opKMSNormSq H hH β C = (opKMSNorm H hH β C) ^ 2 :=
    (Real.sq_sqrt (kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis C)).symm
  have h_half_sq := half_sq_le_add_sq_of_le_add h_kms_nn h_norm_le
  have h_rpow_sq : (p_fail ^ (1 / 4 : ℝ)) ^ 2 = p_fail ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg]
    norm_num
  have h_a_sq : (4 * ‖L_op‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2 = 16 * ‖L_op‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) := by
    calc (4 * ‖L_op‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2
      _ = 16 * ‖L_op‖ ^ 2 * ((p_fail ^ (1 / 4 : ℝ)) ^ 2) := by ring
      _ = 16 * ‖L_op‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) := by rw [h_rpow_sq]
  rw [h_sq_eq]
  change (1 / 2 : ℝ) * (opKMSNorm H hH β C) ^ 2 ≤
    16 * ‖L_op‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) + ‖Pi_dress * C * Pi_dress‖ ^ 2
  linarith

/-- **Single-Channel KMS Dirichlet Bound under Pinched Residual Bound
(`half_opKMSNormSq_opCommutator_le_of_pinched_sq_le`)**:
If `‖O_dress‖ ≤ 1` and `‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split`,
then
$$\frac{1}{2} \|[L_{\mathrm{op}}, O_{\mathrm{dress}}]\|_{\mathrm{KMS}, H}^2
  \le \|L_{\mathrm{op}}\|^2 \bigl(16 \, p_{\mathrm{fail}}^{1/2} + \delta_{\mathrm{split}}\bigr).$$ -/
theorem half_opKMSNormSq_opCommutator_le_of_pinched_sq_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (L_op O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_norm : ‖O_dress‖ ≤ 1)
    (hPi : IsStarProjection Pi_dress)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (h_pinch_sq :
      ‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split) :
    (1 / 2 : ℝ) * opKMSNormSq H hH β (opCommutator L_op O_dress) ≤
      ‖L_op‖ ^ 2 * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split) := by
  have h_decomp := half_opKMSNormSq_opCommutator_le_add_pinched_sq H hH β L_op O_dress Pi_dress
    hO_norm hPi hp_le
  linarith

/-- Helper: `2 * ‖Pi_dress * [L_op, O_dress] * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split` implies
`‖Pi_dress * [L_op, O_dress] * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split`. -/
lemma pinched_sq_le_of_two_mul_pinched_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L_op O_dress Pi_dress : E →L[ℂ] E) {δ_split : ℝ}
    (h : 2 * ‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split) :
    ‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split := by
  have h_nn : 0 ≤ ‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 := sq_nonneg _
  linarith

/-- Helper: Exact safe-subspace vanishing `Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress = 0`
with `0 ≤ δ_split` implies `‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split`. -/
lemma pinched_sq_le_of_pinched_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L_op O_dress Pi_dress : E →L[ℂ] E) {δ_split : ℝ} (hδ : 0 ≤ δ_split)
    (h_zero : Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress = 0) :
    ‖Pi_dress * (L_op * O_dress - O_dress * L_op) * Pi_dress‖ ^ 2 ≤ ‖L_op‖ ^ 2 * δ_split := by
  rw [h_zero, norm_zero, zero_pow (by decide)]
  exact mul_nonneg (sq_nonneg _) hδ

/-- **Bath-Summed KMS Dirichlet Form Bound (`sum_bath_half_opKMSNormSq_le_of_pinched_sq_le`)**:
If every bath channel `ch ∈ bath` has `0 ≤ ch.γ` and satisfies
`‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split`, then
$$\frac{1}{2} \sum_{\mathrm{ch} \in \mathrm{bath}} \gamma_{\mathrm{ch}} \|[L_{\mathrm{ch}}, O_{\mathrm{dress}}]\|_{\mathrm{KMS}, H}^2
  \le \Bigl(\sum_{\mathrm{ch} \in \mathrm{bath}} \gamma_{\mathrm{ch}} \|L_{\mathrm{ch}}\|^2\Bigr)
    \bigl(16 \, p_{\mathrm{fail}}^{1/2} + \delta_{\mathrm{split}}\bigr).$$ -/
theorem sum_bath_half_opKMSNormSq_le_of_pinched_sq_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (bath : Finset (BathChannel D L Site))
    (O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_norm : ‖O_dress‖ ≤ 1)
    (hPi : IsStarProjection Pi_dress)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split) :
    (1 / 2 : ℝ) * (∑ ch ∈ bath, ch.γ * opKMSNormSq H hH β (opCommutator ch.L O_dress)) ≤
      (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun ch hch => ?_
  have h_ch := half_opKMSNormSq_opCommutator_le_of_pinched_sq_le H hH β ch.L O_dress Pi_dress
    hO_norm hPi hp_le (h_bath ch hch).2
  have hγ : 0 ≤ ch.γ := (h_bath ch hch).1
  calc (1 / 2 : ℝ) * (ch.γ * opKMSNormSq H hH β (opCommutator ch.L O_dress))
    _ = ch.γ * ((1 / 2 : ℝ) * opKMSNormSq H hH β (opCommutator ch.L O_dress)) := by ring
    _ ≤ ch.γ * (‖ch.L‖ ^ 2 * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split)) :=
      mul_le_mul_of_nonneg_left h_ch hγ
    _ = ch.γ * ‖ch.L‖ ^ 2 * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split) := by ring

/-! ## 3. KMS-Symmetric Channel Dissipator Inner-Product Bounds -/

/-- **General Single-Channel KMS Dissipator Inner-Product Bound via `opKMSNormSq`
(`kmsInnerReal_channel_dissipator_sub_le_quarter_opKMSNormSq`)**:
For any channel `ch` with `0 ≤ ch.γ` and any operators `O_dress, O_s`, the KMS inner product of
`O_s - O_dress` against the `ch` KMS-Lindblad dissipator of `O_s` satisfies
$$-\frac{1}{2} \gamma_{\mathrm{ch}} \langle O_s - O_{\mathrm{dress}}, \mathcal{D}_{\mathrm{ch}}(O_s)\rangle_{\mathrm{KMS}}
  \le \frac{1}{4} \gamma_{\mathrm{ch}} \Bigl(\frac{1}{2} \|[L_{\mathrm{ch}}, O_{\mathrm{dress}}]\|_{\mathrm{KMS}, H}^2\Bigr).$$ -/
theorem kmsInnerReal_channel_dissipator_sub_le_quarter_opKMSNormSq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (O_dress O_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ch : BathChannel D L Site) (h_ch_γ : 0 ≤ ch.γ) :
    -(1 / 2 : ℝ) * (ch.γ * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s - O_dress)
      (kmsInvSandwich (opEigenbasis H hH) (opEigenvalues H hH) β (opCommutator (ch.L†)
        (kmsSandwich (opEigenbasis H hH) (opEigenvalues H hH) β (opCommutator ch.L O_s))))) ≤
    (1 / 4 : ℝ) * (ch.γ * ((1 / 2 : ℝ) * opKMSNormSq H hH β (opCommutator ch.L O_dress))) := by
  have h_onb := opEigenbasis_orthonormal H hH
  have h_parseval := opEigenbasis_parseval H hH
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H hH
  set ψ_eig := opEigenbasis H hH
  set E_eig := opEigenvalues H hH
  rw [kmsInnerReal_channel_dissipator_eq ψ_eig E_eig β h_onb h_parseval ch.L (O_s - O_dress) O_s]
  have h_sub_comm :
      opCommutator ch.L (O_s - O_dress) = opCommutator ch.L O_s - opCommutator ch.L O_dress := by
    unfold opCommutator; rw [mul_sub, sub_mul]; abel
  have h_sub_inner :
      kmsInnerReal ψ_eig E_eig β (opCommutator ch.L (O_s - O_dress)) (opCommutator ch.L O_s) =
        kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_s) -
          kmsInnerReal ψ_eig E_eig β (opCommutator ch.L O_dress) (opCommutator ch.L O_s) := by
    rw [h_sub_comm]
    unfold kmsNormSq kmsInnerReal
    rw [map_sub, mul_sub, sub_mul, sub_mul, hilbertTrace_sub]
  rw [h_sub_inner]
  let E_O := kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_dress)
  let E_Os := kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_s)
  have hE_O_nn : 0 ≤ E_O := kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis _
  have hE_Os_nn : 0 ≤ E_Os := kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis _
  have h_cs : kmsInnerReal ψ_eig E_eig β (opCommutator ch.L O_dress) (opCommutator ch.L O_s) ≤
      Real.sqrt E_O * Real.sqrt E_Os :=
    kmsInnerReal_le_kmsNorm_mul_kmsNorm ψ_eig E_eig β h_onb h_tr_basis _ _
  have h_young : -E_Os + Real.sqrt E_O * Real.sqrt E_Os ≤ (1 / 4 : ℝ) * E_O :=
    kms_dirichlet_young_ineq hE_O_nn hE_Os_nn
  have h_inner_bound :
      -(E_Os - kmsInnerReal ψ_eig E_eig β (opCommutator ch.L O_dress) (opCommutator ch.L O_s)) ≤
        (1 / 4 : ℝ) * E_O := by linarith
  change -(1 / 2 : ℝ) * (ch.γ * (E_Os -
    kmsInnerReal ψ_eig E_eig β (opCommutator ch.L O_dress) (opCommutator ch.L O_s))) ≤
    (1 / 4 : ℝ) * (ch.γ * ((1 / 2 : ℝ) * E_O))
  nlinarith

/-- **Single-Channel KMS Dissipator Bound under Pinched Residual Bound
(`kmsInnerReal_channel_dissipator_sub_le_of_pinched_sq_le`)**:
Under `‖O_dress‖ ≤ 1`, `gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail`, and
`‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split`,
$$-\frac{1}{2} \gamma_{\mathrm{ch}} \langle O_s - O_{\mathrm{dress}}, \mathcal{D}_{\mathrm{ch}}(O_s)\rangle_{\mathrm{KMS}}
  \le \frac{1}{4} \gamma_{\mathrm{ch}} \|L_{\mathrm{ch}}\|^2
    \bigl(16 \, p_{\mathrm{fail}}^{1/2} + \delta_{\mathrm{split}}\bigr).$$ -/
theorem kmsInnerReal_channel_dissipator_sub_le_of_pinched_sq_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) {Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (O_dress O_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_dress) (hO_norm : ‖O_dress‖ ≤ 1)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (ch : BathChannel D L Site) (h_ch_γ : 0 ≤ ch.γ)
    (h_ch_pinch :
      ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split) :
    -(1 / 2 : ℝ) * (ch.γ * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s - O_dress)
      (kmsInvSandwich (opEigenbasis H hH) (opEigenvalues H hH) β (opCommutator (ch.L†)
        (kmsSandwich (opEigenbasis H hH) (opEigenvalues H hH) β (opCommutator ch.L O_s))))) ≤
    (1 / 4 : ℝ) * (ch.γ * ‖ch.L‖ ^ 2 * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split)) := by
  have h1 := kmsInnerReal_channel_dissipator_sub_le_quarter_opKMSNormSq
    H hH β O_dress O_s ch h_ch_γ
  have h2 := half_opKMSNormSq_opCommutator_le_of_pinched_sq_le
    H hH β ch.L O_dress Pi_dress hO_norm hPi hp_le h_ch_pinch
  nlinarith

/-- **Bath-Summed KMS Dissipator Inner-Product Bound (`kms_bath_dissipator_inner_sub_le_of_pinched_sq_le`)**:
Under `‖O_dress‖ ≤ 1`, `gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail`, and
`∀ ch ∈ bath, 0 ≤ ch.γ ∧ ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split`,
$$-\frac{1}{2} \sum_{\mathrm{ch} \in \mathrm{bath}} \langle O_s - O_{\mathrm{dress}}, \gamma_{\mathrm{ch}} \mathcal{D}_{\mathrm{ch}}(O_s)\rangle_{\mathrm{KMS}}
  \le \frac{1}{4} \Bigl(\sum_{\mathrm{ch} \in \mathrm{bath}} \gamma_{\mathrm{ch}} \|L_{\mathrm{ch}}\|^2\Bigr)
    \bigl(16 \, p_{\mathrm{fail}}^{1/2} + \delta_{\mathrm{split}}\bigr).$$ -/
theorem kms_bath_dissipator_inner_sub_le_of_pinched_sq_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (bath : Finset (BathChannel D L Site))
    {Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (O_dress O_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_dress) (hO_norm : ‖O_dress‖ ≤ 1)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split) :
    -(1 / 2 : ℝ) * (∑ ch ∈ bath, kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s - O_dress)
      ((ch.γ : ℂ) • kmsInvSandwich (opEigenbasis H hH) (opEigenvalues H hH) β
        (opCommutator (ch.L†) (kmsSandwich (opEigenbasis H hH) (opEigenvalues H hH) β
          (opCommutator ch.L O_s))))) ≤
    (1 / 4 : ℝ) * ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split)) := by
  set ψ_eig := opEigenbasis H hH
  set E_eig := opEigenvalues H hH
  have h_smul_right : ∀ (r : ℝ) (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      kmsInnerReal ψ_eig E_eig β A ((r : ℂ) • B) = r * kmsInnerReal ψ_eig E_eig β A B := by
    intro r A B; unfold kmsInnerReal; rw [clm_mul_smul, _root_.hilbertTrace_smul_ofReal]
  rw [Finset.mul_sum]
  calc (∑ ch ∈ bath, -(1 / 2 : ℝ) * kmsInnerReal ψ_eig E_eig β (O_s - O_dress)
        ((ch.γ : ℂ) • kmsInvSandwich ψ_eig E_eig β
          (opCommutator (ch.L†) (kmsSandwich ψ_eig E_eig β (opCommutator ch.L O_s)))))
    _ ≤ ∑ ch ∈ bath, (1 / 4 : ℝ) * (ch.γ * ‖ch.L‖ ^ 2 * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split)) := by
      refine Finset.sum_le_sum fun ch hch => ?_
      rw [h_smul_right]
      exact kmsInnerReal_channel_dissipator_sub_le_of_pinched_sq_le
        H hH β O_dress O_s hPi hO_norm hp_le ch (h_bath ch hch).1 (h_bath ch hch).2
    _ = (1 / 4 : ℝ) * ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split)) := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]

end
