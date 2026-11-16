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

import Proofs.KMSSafeSubspaceODE.SupersolutionODEIntegral
import Proofs.KMSSafeSubspaceODE.KMSFourthRootAndPinchedGibbs
import Proofs.BoxMetricAndCollarLemmas
import Proofs.SupportAndCondExpLemmas
import Proofs.LiebRobinson.SuperpolyDecayClosure

/-!
# Safe-Block KMS Norm Bounds via Fourth-Root Failure Sandwich

Proves fourth-root KMS norm and squared KMS norm bounds for operators with vanishing or bounded safe-subspace sandwich (`opKMSNorm_le_two_mul_norm_of_sandwich_eq_zero`, `opKMSNorm_le_two_mul_norm_add_sandwich_norm`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-! ## 1. Safe-Subspace Immunity & Safe-Block KMS Norm Bounds -/

open KMSPinchedGibbs

/-- Two-sided safe-projector immunity bound in `opKMSNorm` and `opKMSNormSq`
(Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`)):
if `Pi_safe * C * Pi_safe = 0` for an orthogonal projection `Pi_safe` and
`gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail`, then
`opKMSNorm H hH β C ≤ 2 * ‖C‖ * p_fail ^ (1 / 4)` and
`opKMSNormSq H hH β C ≤ 4 * ‖C‖ ^ 2 * p_fail ^ (1 / 2)`. -/
theorem opKMSNorm_le_two_mul_norm_of_sandwich_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) {Pi_safe C : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    (h_fw : Pi_safe * C * Pi_safe = 0)
    {p_fail : ℝ} (hp_le : gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail) :
    opKMSNorm H hH β C ≤ 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) ∧
    opKMSNormSq H hH β C ≤ 4 * (‖C‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  let P_fail := 1 - Pi_safe
  have h_onb := opEigenbasis_orthonormal H hH
  have h_parseval := opEigenbasis_parseval H hH
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H hH
  have hP_fail : IsStarProjection P_fail := hPi.one_sub
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP_fail) hp_le
  have h_one_sub : 1 - P_fail = Pi_safe := sub_sub_cancel 1 Pi_safe
  have h_decomp : C = P_fail * C + (1 - P_fail) * C * P_fail := by
    apply eq_mul_add_one_sub_mul_mul_of_one_sub_sandwich_eq_zero P_fail C
    rw [h_one_sub, h_fw]
  have h1_sub_norm : ‖1 - P_fail‖ ≤ 1 := by
    rw [h_one_sub]; exact isStarProjection_norm_le_one hPi
  have h1_sub_C_norm : ‖(1 - P_fail) * C‖ ≤ ‖C‖ :=
    le_trans (ContinuousLinearMap.opNorm_comp_le (1 - P_fail) C)
      (mul_le_of_le_one_left (norm_nonneg C) h1_sub_norm)
  have h_term1 : kmsNorm ψ_eig E_eig β (P_fail * C) ≤ ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) :=
    (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval hP_fail C hp_le).2.2.1
  have h_term2 : kmsNorm ψ_eig E_eig β ((1 - P_fail) * C * P_fail) ≤ ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) := by
    have h_b := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval
      hP_fail ((1 - P_fail) * C) hp_le).2.2.2
    exact le_trans h_b (mul_le_mul_of_nonneg_right h1_sub_C_norm (by positivity))
  have h_norm_bound : opKMSNorm H hH β C ≤ 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) := by
    change kmsNorm ψ_eig E_eig β C ≤ 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ))
    calc kmsNorm ψ_eig E_eig β C
      _ = kmsNorm ψ_eig E_eig β (P_fail * C + (1 - P_fail) * C * P_fail) := by rw [← h_decomp]
      _ ≤ kmsNorm ψ_eig E_eig β (P_fail * C) + kmsNorm ψ_eig E_eig β ((1 - P_fail) * C * P_fail) :=
        kmsNorm_add_le ψ_eig E_eig β h_onb h_tr_basis _ _
      _ ≤ ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) + ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) :=
        add_le_add h_term1 h_term2
      _ = 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) := by ring
  refine ⟨h_norm_bound, ?_⟩
  change kmsNormSq ψ_eig E_eig β C ≤ 4 * (‖C‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))
  have h_sq_eq : kmsNormSq ψ_eig E_eig β C = (kmsNorm ψ_eig E_eig β C) ^ 2 :=
    (Real.sq_sqrt (kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis C)).symm
  have h_rpow : (p_fail ^ (1 / 4 : ℝ)) ^ 2 = p_fail ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg]; norm_num
  have h_rhs_sq : (2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2 = 4 * (‖C‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
    calc (2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2
      _ = 4 * (‖C‖ ^ 2) * ((p_fail ^ (1 / 4 : ℝ)) ^ 2) := by ring
      _ = 4 * (‖C‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by rw [h_rpow]
  rw [h_sq_eq, ← h_rhs_sq]
  have h_nonneg : 0 ≤ kmsNorm ψ_eig E_eig β C := Real.sqrt_nonneg _
  change kmsNorm ψ_eig E_eig β C ≤ 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) at h_norm_bound
  nlinarith [h_norm_bound, h_nonneg]

private lemma eq_sandwich_add_mul_add_one_sub_mul_mul {R : Type*} [Ring R] (P Pi_s C : R)
    (h : 1 - P = Pi_s) :
    C = Pi_s * C * Pi_s + (P * C + Pi_s * C * P) := by
  rw [← h, sub_mul, one_mul, mul_sub, mul_one]; abel

private lemma hilbertTrace_gibbsDensityOp_mul_proj_le_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) :
    hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) ≤ 1 := by
  rw [hilbertTrace_gibbsDensityOp_mul_eq ψ_eig E_eig β h_onb h_tr_basis P]
  calc ∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω * RCLike.re (inner ℂ (ψ_eig ω) (P (ψ_eig ω)))
    _ ≤ ∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω * 1 := by
      refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (gibbsProb_nonneg E_eig β ω)
      rw [isStarProjection_re_inner_eq_norm_sq hP (ψ_eig ω)]
      have h1 : ‖P (ψ_eig ω)‖ ^ 2 ≤ ‖ψ_eig ω‖ ^ 2 :=
        isStarProjection_norm_sq_apply_le hP (ψ_eig ω)
      rwa [eigenbasis_norm_eq_one ψ_eig h_onb h_parseval ω, one_pow] at h1
    _ = ∑ ω : ManyBodyConfig Site, gibbsProb E_eig β ω := by simp only [mul_one]
    _ = 1 := sum_gibbsProb_eq_one E_eig β

private lemma kmsNorm_le_opNorm_aux {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNorm ψ_eig E_eig β X ≤ ‖X‖ := by
  have h1 : IsStarProjection (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    ⟨IsIdempotentElem.one, IsSelfAdjoint.one _⟩
  have h_tr_one : hilbertTrace (gibbsDensityOp ψ_eig E_eig β * 1) ≤ 1 :=
    hilbertTrace_gibbsDensityOp_mul_proj_le_one ψ_eig E_eig β h_onb h_tr_basis h_parseval h1
  have h_b := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval h1
    X h_tr_one).2.2.1
  have h_lhs : kmsNorm ψ_eig E_eig β (1 * X) = kmsNorm ψ_eig E_eig β X :=
    congrArg (kmsNorm ψ_eig E_eig β) (one_mul X)
  have h_rhs : ‖X‖ * ((1 : ℝ) ^ (1 / 4 : ℝ)) = ‖X‖ := by rw [Real.one_rpow, mul_one]
  linarith

/-- **Unconditional KMS Norm Bound via Safe-Block Decomposition
(`opKMSNorm_le_two_mul_norm_add_sandwich_norm`)**:
For ANY operator $C$ and ANY star projection $\Pi_{\mathrm{safe}}$ with
$\mathrm{gibbsFailureProb}\ H\ hH\ \beta\ (1 - \Pi_{\mathrm{safe}}) \le p_{\mathrm{fail}}$,
$$\|C\|_{\mathrm{KMS}, H} \le \|\Pi_{\mathrm{safe}} C \Pi_{\mathrm{safe}}\| + 2 \|C\| \, p_{\mathrm{fail}}^{1/4}.$$ -/
theorem opKMSNorm_le_two_mul_norm_add_sandwich_norm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) {Pi_safe C : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    {p_fail : ℝ} (hp_le : gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail) :
    opKMSNorm H hH β C ≤ ‖Pi_safe * C * Pi_safe‖ + 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  let P_fail := 1 - Pi_safe
  have h_onb := opEigenbasis_orthonormal H hH
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H hH
  have h_parseval := opEigenbasis_parseval H hH
  have hP_fail : IsStarProjection P_fail := hPi.one_sub
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP_fail) hp_le
  have h_decomp : C = Pi_safe * C * Pi_safe + (P_fail * C + Pi_safe * C * P_fail) :=
    eq_sandwich_add_mul_add_one_sub_mul_mul P_fail Pi_safe C (sub_sub_cancel 1 Pi_safe)
  have hPi_norm : ‖Pi_safe‖ ≤ 1 := isStarProjection_norm_le_one hPi
  have hPi_C_norm : ‖Pi_safe * C‖ ≤ ‖C‖ :=
    le_trans (ContinuousLinearMap.opNorm_comp_le Pi_safe C)
      (mul_le_of_le_one_left (norm_nonneg C) hPi_norm)
  have h_term0 : kmsNorm ψ_eig E_eig β (Pi_safe * C * Pi_safe) ≤ ‖Pi_safe * C * Pi_safe‖ :=
    kmsNorm_le_opNorm_aux ψ_eig E_eig β h_onb h_tr_basis h_parseval (Pi_safe * C * Pi_safe)
  have h_term1 : kmsNorm ψ_eig E_eig β (P_fail * C) ≤ ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) :=
    (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval hP_fail C hp_le).2.2.1
  have h_term2 : kmsNorm ψ_eig E_eig β (Pi_safe * C * P_fail) ≤ ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) := by
    have h_b := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval
      hP_fail (Pi_safe * C) hp_le).2.2.2
    exact le_trans h_b (mul_le_mul_of_nonneg_right hPi_C_norm (by positivity))
  have h_lhs_eq : kmsNorm ψ_eig E_eig β C =
      kmsNorm ψ_eig E_eig β (Pi_safe * C * Pi_safe + (P_fail * C + Pi_safe * C * P_fail)) :=
    congrArg (kmsNorm ψ_eig E_eig β) h_decomp
  have h_tri1 := kmsNorm_add_le ψ_eig E_eig β h_onb h_tr_basis
    (Pi_safe * C * Pi_safe) (P_fail * C + Pi_safe * C * P_fail)
  have h_tri2 := kmsNorm_add_le ψ_eig E_eig β h_onb h_tr_basis
    (P_fail * C) (Pi_safe * C * P_fail)
  change kmsNorm ψ_eig E_eig β C ≤ ‖Pi_safe * C * Pi_safe‖ + 2 * ‖C‖ * (p_fail ^ (1 / 4 : ℝ))
  linarith

end
