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

import Proofs.DressedThermalDuhamel.SafeBlockKMSNormBounds

/-!
# KMS Bath Channel Dissipator Inner-Product and Young Bounds

Proves the symmetric KMS inner-product commutator identity (`kmsInnerReal_channel_dissipator_eq`) for individual bath channels and applies Cauchy–Schwarz, Young's inequality, and the fourth-root safe-block KMS norm bound to establish the dissipative channel Dirichlet estimate (`kmsInnerReal_channel_dissipator_sub_le`).

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

/-! ## 1. KMS Bath Channel Dissipator Inner-Product & Young Bounds -/

private lemma opCommutator_adjoint_aux {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L_op A : H →L[ℂ] H) :
    (opCommutator L_op A)† = A† * (L_op)† - (L_op)† * A† := by
  unfold opCommutator
  change star (L_op * A - A * L_op) = (star A) * (star L_op) - (star L_op) * (star A)
  rw [star_sub, star_mul, star_mul]

private lemma hilbertTrace_sandwich_commutator_channel {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (S S_inv L_op A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_SSinv : S * S_inv = 1) (h_SinvS : S_inv * S = 1) :
    hilbertTrace
      (S * A† * S *
        (S_inv * (L_op† * (S * opCommutator L_op B * S) -
          (S * opCommutator L_op B * S) * L_op†) * S_inv)) =
      hilbertTrace (S * (opCommutator L_op A)† * S * opCommutator L_op B) := by
  have h1 : S * A† * S * (S_inv * (L_op† * (S * opCommutator L_op B * S) -
      (S * opCommutator L_op B * S) * L_op†) * S_inv) =
      (S * A† * (L_op† * (S * opCommutator L_op B * S) -
        (S * opCommutator L_op B * S) * L_op†)) * S_inv := by
    calc S * A† * S * (S_inv * (L_op† * (S * opCommutator L_op B * S) -
          (S * opCommutator L_op B * S) * L_op†) * S_inv)
      _ = (S * A† * (S * S_inv) * (L_op† * (S * opCommutator L_op B * S) -
          (S * opCommutator L_op B * S) * L_op†)) * S_inv := by simp only [mul_assoc]
      _ = _ := by rw [h_SSinv, mul_one]
  have h2 : S_inv * (S * A† * (L_op† * (S * opCommutator L_op B * S) -
      (S * opCommutator L_op B * S) * L_op†)) =
      A† * (L_op† * (S * opCommutator L_op B * S) -
        (S * opCommutator L_op B * S) * L_op†) := by
    calc S_inv * (S * A† * (L_op† * (S * opCommutator L_op B * S) -
          (S * opCommutator L_op B * S) * L_op†))
      _ = (S_inv * S) * A† * (L_op† * (S * opCommutator L_op B * S) -
          (S * opCommutator L_op B * S) * L_op†) := by simp only [mul_assoc]
      _ = _ := by rw [h_SinvS, one_mul]
  have h3 : (A† * L_op†) * (S * opCommutator L_op B * S) -
      L_op† * (A† * (S * opCommutator L_op B * S)) =
      ((opCommutator L_op A)† * S * opCommutator L_op B) * S := by
    rw [← mul_assoc (L_op†) (A†) (S * opCommutator L_op B * S), ← sub_mul,
      ← opCommutator_adjoint_aux L_op A]
    simp only [mul_assoc]
  rw [h1, hilbertTrace_mul_comm_aux _ S_inv, h2, mul_sub,
    ← mul_assoc (A†) (L_op†) (S * opCommutator L_op B * S),
    ← mul_assoc (A†) (S * opCommutator L_op B * S) (L_op†),
    hilbertTrace_sub,
    hilbertTrace_mul_comm_aux (A† * (S * opCommutator L_op B * S)) (L_op†),
    ← hilbertTrace_sub, h3, hilbertTrace_mul_comm_aux _ S]
  simp only [mul_assoc]

lemma kmsInnerReal_channel_dissipator_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    (L_op A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β A
      (kmsInvSandwich ψ_eig E_eig β
        (opCommutator (L_op†) (kmsSandwich ψ_eig E_eig β (opCommutator L_op B)))) =
    kmsInnerReal ψ_eig E_eig β (opCommutator L_op A) (opCommutator L_op B) := by
  have h_SSinv := gibbsSqrtOp_mul_gibbsInvSqrtOp ψ_eig E_eig β h_onb h_parseval
  have h_SinvS := gibbsInvSqrtOp_mul_gibbsSqrtOp ψ_eig E_eig β h_onb h_parseval
  unfold kmsInnerReal kmsInvSandwich kmsSandwich
  exact hilbertTrace_sandwich_commutator_channel
    (gibbsSqrtOp ψ_eig E_eig β) (gibbsInvSqrtOp ψ_eig E_eig β) L_op A B h_SSinv h_SinvS

lemma kmsInnerReal_channel_dissipator_sub_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) {Pi_safe O_dec O_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe) (hO_norm : ‖O_dec‖ ≤ 1)
    {p_fail : ℝ} (hp_le : gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail)
    (ch : BathChannel D L Site)
    (h_ch_γ : 0 ≤ ch.γ)
    (h_ch_fw : Pi_safe * (ch.L * O_dec - O_dec * ch.L) * Pi_safe = 0) :
    -(1 / 2 : ℝ) * (ch.γ * kmsInnerReal (opEigenbasis H hH) (opEigenvalues H hH) β (O_s - O_dec)
      (kmsInvSandwich (opEigenbasis H hH) (opEigenvalues H hH) β (opCommutator (ch.L†)
        (kmsSandwich (opEigenbasis H hH) (opEigenvalues H hH) β (opCommutator ch.L O_s))))) ≤
    2 * (ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
  have h_onb := opEigenbasis_orthonormal H hH
  have h_parseval := opEigenbasis_parseval H hH
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H hH
  set ψ_eig := opEigenbasis H hH
  set E_eig := opEigenvalues H hH
  have hP_fail : IsStarProjection (1 - Pi_safe) := hPi.one_sub
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP_fail) hp_le
  rw [kmsInnerReal_channel_dissipator_eq ψ_eig E_eig β h_onb h_parseval ch.L (O_s - O_dec) O_s]
  have h_sub_comm : opCommutator ch.L (O_s - O_dec) = opCommutator ch.L O_s - opCommutator ch.L O_dec := by
    unfold opCommutator; rw [mul_sub, sub_mul]; abel
  have h_sub_inner : kmsInnerReal ψ_eig E_eig β (opCommutator ch.L (O_s - O_dec)) (opCommutator ch.L O_s) =
      kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_s) -
        kmsInnerReal ψ_eig E_eig β (opCommutator ch.L O_dec) (opCommutator ch.L O_s) := by
    rw [h_sub_comm]
    unfold kmsNormSq kmsInnerReal
    rw [map_sub, mul_sub, sub_mul, sub_mul, hilbertTrace_sub]
  rw [h_sub_inner]
  let E_O := kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_dec)
  let E_Os := kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_s)
  have hE_O_nn : 0 ≤ E_O := kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis _
  have hE_Os_nn : 0 ≤ E_Os := kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis _
  have h_cs : kmsInnerReal ψ_eig E_eig β (opCommutator ch.L O_dec) (opCommutator ch.L O_s) ≤
      Real.sqrt E_O * Real.sqrt E_Os :=
    kmsInnerReal_le_kmsNorm_mul_kmsNorm ψ_eig E_eig β h_onb h_tr_basis _ _
  have h_young : -E_Os + Real.sqrt E_O * Real.sqrt E_Os ≤ (1 / 4 : ℝ) * E_O :=
    kms_dirichlet_young_ineq hE_O_nn hE_Os_nn
  have h_inner_bound : -(E_Os - kmsInnerReal ψ_eig E_eig β (opCommutator ch.L O_dec) (opCommutator ch.L O_s)) ≤
      (1 / 4 : ℝ) * E_O := by linarith
  have h_E_O_bound : E_O ≤ 16 * (‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
    have h_fw' : Pi_safe * opCommutator ch.L O_dec * Pi_safe = 0 := h_ch_fw
    have h_sq := (opKMSNorm_le_two_mul_norm_of_sandwich_eq_zero H hH β hPi h_fw' hp_le).2
    have h_comm_norm : ‖opCommutator ch.L O_dec‖ ≤ 2 * ‖ch.L‖ :=
      norm_opCommutator_le_two_mul ch.L hO_norm
    have h_comm_sq : ‖opCommutator ch.L O_dec‖ ^ 2 ≤ 4 * (‖ch.L‖ ^ 2) := by
      nlinarith [norm_nonneg (opCommutator ch.L O_dec), norm_nonneg ch.L]
    change E_O ≤ 4 * (‖opCommutator ch.L O_dec‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) at h_sq
    calc E_O
      _ ≤ 4 * (‖opCommutator ch.L O_dec‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := h_sq
      _ ≤ 4 * (4 * (‖ch.L‖ ^ 2)) * (p_fail ^ (1 / 2 : ℝ)) := by
        nlinarith [Real.rpow_nonneg hp_nonneg (1 / 2 : ℝ)]
      _ = 16 * (‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by ring
  nlinarith

end
