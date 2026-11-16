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

import Proofs.DressedThermalDuhamel.KMSChannelDissipatorBounds

/-!
# Perturbed KMS-Lindblad ODE Drift–Dissipation Trajectory Bounds

Derives KMS-norm logical drift bounds (`opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound`, `opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE`, `opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE_unconditional`) for observables evolving under `SatisfiesKMSLindbladODE`, together with the squared-norm specialization at zero coherent drift (`opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed`).

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

set_option maxRecDepth 200000

/-! ## 1. Core Unconditional `SatisfiesKMSLindbladODE` Bounds -/

/-- Core KMS Lindblad ODE integration bound parameterized by `C_coh = opCommutator H O_dec`
and any bound `opKMSNorm H hH β C_coh ≤ Γ_coh`. -/
theorem opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe C_coh : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_comm_H : opCommutator H O_dec = C_coh)
    {Γ_coh : ℝ} (hΓ_coh_nn : 0 ≤ Γ_coh)
    (h_V_bound : opKMSNorm H hH β C_coh ≤ Γ_coh)
    (hPi : IsStarProjection Pi_safe)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      Pi_safe * (ch.L * O_dec - O_dec * ch.L) * Pi_safe = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_safe) ≤ p_fail)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) (ht : 0 ≤ t)
    (h_ode : SatisfiesKMSLindbladODE H hH β bath O_dec O_t t) :
    opKMSNorm H hH β (O_t t - O_dec) ≤
      kmsDriftDirichletBound Γ_coh
        (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
        t := by
  have h_onb := opEigenbasis_orthonormal H hH
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H hH
  have h_eig := opEigenbasis_ketBra_props H hH
  set ψ_eig := opEigenbasis H hH
  set E_eig := opEigenvalues H hH
  have hP_fail : IsStarProjection (1 - Pi_safe) := hPi.one_sub
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP_fail) hp_le
  let Γ_diss := 16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))
  have hΓ_diss_nn : 0 ≤ Γ_diss := by
    refine mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun ch hch => ?_)) (by positivity)
    exact mul_nonneg (h_bath ch hch).1 (sq_nonneg _)
  rcases h_ode with ⟨hO0, hOs_sa, f', hf_deriv, h_gen⟩
  have hf0 : opKMSNormSq H hH β (O_t 0 - O_dec) ≤ 0 := by
    change kmsNormSq ψ_eig E_eig β (O_t 0 - O_dec) ≤ 0
    rw [hO0, sub_self, kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis 0]
    simp
  have hf_nonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ opKMSNormSq H hH β (O_t s - O_dec) :=
    fun s _ => kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis (O_t s - O_dec)
  have hf_ineq : ∀ s ∈ Set.Icc 0 t,
      f' s ≤ 2 * Γ_coh * Real.sqrt (opKMSNormSq H hH β (O_t s - O_dec)) +
        (1 / 2 : ℝ) * Γ_diss := by
    intro s hs
    have hΔ_sa : IsSelfAdjoint (O_t s - O_dec) := by
      have h1 := ContinuousLinearMap.isSelfAdjoint_iff'.mp (hOs_sa s hs)
      have h2 := ContinuousLinearMap.isSelfAdjoint_iff'.mp hO_sa
      rw [ContinuousLinearMap.isSelfAdjoint_iff', map_sub, h1, h2]
    have h_gen_s := h_gen s hs
    unfold opKMSLindbladGenerator at h_gen_s
    dsimp only at h_gen_s
    have h_sub_right : ∀ A B₁ B₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        kmsInnerReal ψ_eig E_eig β A (B₁ - B₂) =
          kmsInnerReal ψ_eig E_eig β A B₁ - kmsInnerReal ψ_eig E_eig β A B₂ := by
      intro A B₁ B₂; unfold kmsInnerReal; rw [mul_sub, hilbertTrace_sub]
    have h_smul_right : ∀ (r : ℝ) (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
        kmsInnerReal ψ_eig E_eig β A ((r : ℂ) • B) = r * kmsInnerReal ψ_eig E_eig β A B := by
      intro r A B; unfold kmsInnerReal; rw [clm_mul_smul, _root_.hilbertTrace_smul_ofReal]
    have h_sum_right : ∀ (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
        (g : BathChannel D L Site → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)),
        kmsInnerReal ψ_eig E_eig β A (∑ ch ∈ bath, g ch) =
          ∑ ch ∈ bath, kmsInnerReal ψ_eig E_eig β A (g ch) := by
      intro A g; unfold kmsInnerReal; rw [Finset.mul_sum, hilbertTrace_sum]
    have h_half : ((1 / 2 : ℂ) : ℂ) = (((1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [h_sub_right, h_half, h_smul_right, h_sum_right] at h_gen_s
    have h_coh_split :
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dec) (Complex.I • opCommutator H (O_t s)) =
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dec) (Complex.I • C_coh) := by
      rw [opCommutator_sub_add_cancel H (O_t s) O_dec, kmsInnerReal_add_right,
        kmsInnerReal_commutator_eq_zero H ψ_eig E_eig β h_eig (O_t s - O_dec) hΔ_sa, zero_add,
        h_comm_H]
    have h_coh_bound :
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dec) (Complex.I • C_coh) ≤
        Γ_coh * Real.sqrt (opKMSNormSq H hH β (O_t s - O_dec)) := by
      have h_cs := kmsInnerReal_le_kmsNorm_mul_kmsNorm ψ_eig E_eig β h_onb h_tr_basis
        (O_t s - O_dec) (Complex.I • C_coh)
      rw [kmsNorm_I_smul] at h_cs
      change kmsNorm ψ_eig E_eig β C_coh ≤ Γ_coh at h_V_bound
      have h_norm_nn : 0 ≤ kmsNorm ψ_eig E_eig β (O_t s - O_dec) := Real.sqrt_nonneg _
      change kmsInnerReal ψ_eig E_eig β (O_t s - O_dec) (Complex.I • C_coh) ≤
        Γ_coh * kmsNorm ψ_eig E_eig β (O_t s - O_dec)
      nlinarith
    have h_diss_bound :
        -(1 / 2 : ℝ) * (∑ ch ∈ bath, kmsInnerReal ψ_eig E_eig β (O_t s - O_dec)
          ((ch.γ : ℂ) • kmsInvSandwich ψ_eig E_eig β
            (opCommutator (ch.L†) (kmsSandwich ψ_eig E_eig β (opCommutator ch.L (O_t s)))))) ≤
        (1 / 4 : ℝ) * Γ_diss := by
      rw [Finset.mul_sum]
      have h_sum_le :
          (∑ ch ∈ bath, -(1 / 2 : ℝ) * kmsInnerReal ψ_eig E_eig β (O_t s - O_dec)
            ((ch.γ : ℂ) • kmsInvSandwich ψ_eig E_eig β
              (opCommutator (ch.L†) (kmsSandwich ψ_eig E_eig β (opCommutator ch.L (O_t s)))))) ≤
          ∑ ch ∈ bath, 2 * (ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
        refine Finset.sum_le_sum fun ch hch => ?_
        rw [h_smul_right]
        exact kmsInnerReal_channel_dissipator_sub_le H hH β hPi hO_norm hp_le ch
          (h_bath ch hch).1 (h_bath ch hch).2
      have h_rhs_eq :
          (∑ ch ∈ bath, 2 * (ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))) =
            (1 / 8 : ℝ) * Γ_diss := by
        dsimp [Γ_diss]; rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
      linarith
    linarith
  exact kms_gronwall_ode_integral_bound hΓ_coh_nn hΓ_diss_nn ht hf0 hf_nonneg hf_deriv hf_ineq
    t ⟨ht, le_refl t⟩

/-- **Universal KMS Lindblad ODE Drift-Plus-Dirichlet Bound
(`opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE`)**:
Integrates `SatisfiesKMSLindbladODE` for any self-adjoint Hamiltonian $H = H_0 + V_{\mathrm{tot}}$,
safe projector $\Pi_{\mathrm{safe}}$, and decoded logical observable $O_{\mathrm{dec}}$ with
$\|O_{\mathrm{dec}}\| \le 1$, $[H_0, O_{\mathrm{dec}}] = 0$, and
$\Pi_{\mathrm{safe}} [V_{\mathrm{tot}}, O_{\mathrm{dec}}] \Pi_{\mathrm{safe}} = 0$. -/
theorem opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H0 totalPerturbation : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH_pert : IsSelfAdjoint (H0 + totalPerturbation)) (β : ℝ)
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe_pert : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_comm_H0 : Commute H0 O_dec)
    (h_fw_V : Pi_safe_pert * (totalPerturbation * O_dec - O_dec * totalPerturbation) * Pi_safe_pert = 0)
    (hPi : IsStarProjection Pi_safe_pert)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      Pi_safe_pert * (ch.L * O_dec - O_dec * ch.L) * Pi_safe_pert = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb (H0 + totalPerturbation) hH_pert β (1 - Pi_safe_pert) ≤ p_fail)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) (ht : 0 ≤ t)
    (h_ode : SatisfiesKMSLindbladODE (H0 + totalPerturbation) hH_pert β bath O_dec O_t t) :
    opKMSNorm (H0 + totalPerturbation) hH_pert β (O_t t - O_dec) ≤
      kmsDriftDirichletBound
        (2 * ‖totalPerturbation * O_dec - O_dec * totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)))
        (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
        t := by
  have h_comm_H : opCommutator (H0 + totalPerturbation) O_dec = totalPerturbation * O_dec - O_dec * totalPerturbation := by
    unfold opCommutator; rw [add_mul, mul_add, h_comm_H0.eq]; abel
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg
      (opEigenbasis (H0 + totalPerturbation) hH_pert) (opEigenvalues (H0 + totalPerturbation) hH_pert) β
      (opEigenbasis_orthonormal (H0 + totalPerturbation) hH_pert)
      (hilbertTrace_eq_sum_opEigenbasis (H0 + totalPerturbation) hH_pert) hPi.one_sub) hp_le
  exact opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound (H0 + totalPerturbation) hH_pert β bath
    O_dec Pi_safe_pert (totalPerturbation * O_dec - O_dec * totalPerturbation) hO_sa hO_norm h_comm_H
    (by positivity)
    ((opKMSNorm_le_two_mul_norm_of_sandwich_eq_zero (H0 + totalPerturbation) hH_pert β hPi h_fw_V hp_le).1)
    hPi h_bath hp_le O_t t ht h_ode

/-- **Unconditional Perturbed KMS Lindblad ODE Drift-Plus-Dirichlet Bound
(`opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE_unconditional`)**:
Integrates `SatisfiesKMSLindbladODE` for ANY self-adjoint Hamiltonian $H = H_0 + V_{\mathrm{tot}}$,
star projection $\Pi_{\mathrm{safe}}$, and decoded logical observable $O_{\mathrm{dec}}$ with
$\|O_{\mathrm{dec}}\| \le 1$ and $[H_0, O_{\mathrm{dec}}] = 0$, WITHOUT requiring
$\Pi_{\mathrm{safe}} [V_{\mathrm{tot}}, O_{\mathrm{dec}}] \Pi_{\mathrm{safe}} = 0$. -/
theorem opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE_unconditional {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H0 totalPerturbation : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH_pert : IsSelfAdjoint (H0 + totalPerturbation)) (β : ℝ)
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_comm_H0 : Commute H0 O_dec)
    (hPi : IsStarProjection Pi_safe)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      Pi_safe * (ch.L * O_dec - O_dec * ch.L) * Pi_safe = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb (H0 + totalPerturbation) hH_pert β (1 - Pi_safe) ≤ p_fail)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) (ht : 0 ≤ t)
    (h_ode : SatisfiesKMSLindbladODE (H0 + totalPerturbation) hH_pert β bath O_dec O_t t) :
    opKMSNorm (H0 + totalPerturbation) hH_pert β (O_t t - O_dec) ≤
      kmsDriftDirichletBound
        (‖Pi_safe * (totalPerturbation * O_dec - O_dec * totalPerturbation) * Pi_safe‖ +
          2 * ‖totalPerturbation * O_dec - O_dec * totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)))
        (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
        t := by
  have h_comm_H : opCommutator (H0 + totalPerturbation) O_dec = totalPerturbation * O_dec - O_dec * totalPerturbation := by
    unfold opCommutator; rw [add_mul, mul_add, h_comm_H0.eq]; abel
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg
      (opEigenbasis (H0 + totalPerturbation) hH_pert) (opEigenvalues (H0 + totalPerturbation) hH_pert) β
      (opEigenbasis_orthonormal (H0 + totalPerturbation) hH_pert)
      (hilbertTrace_eq_sum_opEigenbasis (H0 + totalPerturbation) hH_pert) hPi.one_sub) hp_le
  exact opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound (H0 + totalPerturbation) hH_pert β bath
    O_dec Pi_safe (totalPerturbation * O_dec - O_dec * totalPerturbation) hO_sa hO_norm h_comm_H
    (by positivity)
    (opKMSNorm_le_two_mul_norm_add_sandwich_norm (H0 + totalPerturbation) hH_pert β hPi hp_le)
    hPi h_bath hp_le O_t t ht h_ode

/-- **Unperturbed KMS Lindblad ODE Squared Norm Bound
(`opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed`)**:
When $[H_0, O_{\mathrm{dec}}] = 0$, the coherent drift vanishes ($\Gamma_{\mathrm{coh}} = 0$) and
$\|O_t - O_{\mathrm{dec}}\|_{\mathrm{KMS}, H_0}^2 \le 8 \left(\sum_{\mathrm{ch}} \gamma_{\mathrm{ch}} \|L_{\mathrm{ch}}\|^2\right) p_{\mathrm{fail}}^{1/2} t$. -/
theorem opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH0 : IsSelfAdjoint H0) (β : ℝ)
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_sq : O_dec * O_dec = 1)
    (h_comm_H0 : Commute H0 O_dec)
    (hPi : IsStarProjection Pi_safe)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      Pi_safe * (ch.L * O_dec - O_dec * ch.L) * Pi_safe = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb H0 hH0 β (1 - Pi_safe) ≤ p_fail)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) (ht : 0 ≤ t)
    (h_ode : SatisfiesKMSLindbladODE H0 hH0 β bath O_dec O_t t) :
    opKMSNormSq H0 hH0 β (O_t t - O_dec) ≤
      8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) * t := by
  have hO_norm : ‖O_dec‖ ≤ 1 := norm_le_one_of_isSelfAdjoint_sq_eq_one hO_sa hO_sq
  have h_comm_zero : opCommutator H0 O_dec = 0 := sub_eq_zero.mpr h_comm_H0.eq
  have h_onb := opEigenbasis_orthonormal H0 hH0
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H0 hH0
  set ψ_eig := opEigenbasis H0 hH0
  set E_eig := opEigenvalues H0 hH0
  have h0_bound : opKMSNorm H0 hH0 β 0 ≤ 0 := by
    change Real.sqrt (kmsNormSq ψ_eig E_eig β 0) ≤ 0
    rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis 0]
    simp
  have h_bound := opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound H0 hH0 β bath
    O_dec Pi_safe 0 hO_sa hO_norm h_comm_zero le_rfl h0_bound hPi h_bath hp_le O_t t ht h_ode
  dsimp [kmsDriftDirichletBound] at h_bound
  rw [mul_zero, zero_add] at h_bound
  have hP_fail : IsStarProjection (1 - Pi_safe) := hPi.one_sub
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP_fail) hp_le
  have h_rhs_nn : 0 ≤ (t / 2) * (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))) := by
    refine mul_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun ch hch => ?_)) (by positivity))
    exact mul_nonneg (h_bath ch hch).1 (sq_nonneg _)
  have h_lhs_sq : (opKMSNorm H0 hH0 β (O_t t - O_dec)) ^ 2 = opKMSNormSq H0 hH0 β (O_t t - O_dec) :=
    Real.sq_sqrt (kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis (O_t t - O_dec))
  have h_rhs_sq : (Real.sqrt ((t / 2) * (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))))) ^ 2 =
      8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) * t := by
    rw [Real.sq_sqrt h_rhs_nn]; ring
  have h_lhs_nn : 0 ≤ opKMSNorm H0 hH0 β (O_t t - O_dec) := Real.sqrt_nonneg _
  nlinarith

end
