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

import Defs.KMSAndGibbs

/-!
# Fractional Gibbs Powers and KMS Norm Domination

Proves the fractional Boltzmann operator identities `gibbsSqrtOp_mul_self` and `gibbsSqrtOp_mul_gibbsInvSqrtOp`, and shows that the symmetric KMS norm is bounded above by the operator norm (`kmsNorm_le_opNorm`).

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 2 (`sec:setup`), Definition 2.6 (`def:kms-lindblad`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Gibbs Fractional Power Identities and KMS Norm Bounds
-/

/-- Scalar multiplication associativity on `H →L[ℂ] H`. -/
private lemma clm_smul_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c₁ c₂ : ℂ) (A : H →L[ℂ] H) :
    c₁ • (c₂ • A) = (c₁ * c₂) • A := by
  ext φ
  exact smul_smul c₁ c₂ (A φ)

/-- Left scalar multiplication commutes with operator multiplication on `H →L[ℂ] H`. -/
private lemma clm_smul_mul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) :
    (c • A) * B = c • (A * B) := by
  ext φ
  rfl

/-- Right scalar multiplication commutes with operator multiplication on `H →L[ℂ] H`. -/
private lemma clm_mul_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) :
    A * (c • B) = c • (A * B) := by
  ext φ
  exact map_smul A c (B φ)

/-- Real-weighted spectral combination $\sum_\omega w(\omega) |\psi_\omega\rangle\langle\psi_\omega|$. -/
private def spectralWeightOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (w : ManyBodyConfig Site → ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ ω : ManyBodyConfig Site, (w ω : ℂ) • rankOneKetBra (ψ_eig ω)

/-- Product of two real-weighted spectral combinations `spectralWeightOp` on an orthonormal family `ψ_eig`. -/
private lemma spectralWeightOp_mul_spectralWeightOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (w₁ w₂ : ManyBodyConfig Site → ℝ) :
    spectralWeightOp ψ_eig w₁ * spectralWeightOp ψ_eig w₂ =
      spectralWeightOp ψ_eig (fun ω => w₁ ω * w₂ ω) := by
  unfold spectralWeightOp
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω₁ _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single ω₁]
  · rw [clm_smul_mul, clm_mul_smul, clm_smul_smul, onb_ketBra_mul_ketBra ψ_eig h_onb ω₁ ω₁,
      if_pos rfl, Complex.ofReal_mul]
  · intro ω₂ _ hne
    rw [clm_smul_mul, clm_mul_smul, clm_smul_smul, onb_ketBra_mul_ketBra ψ_eig h_onb ω₁ ω₂,
      if_neg (Ne.symm hne), smul_zero]
  · intro h_not_mem
    exact False.elim (h_not_mem (Finset.mem_univ ω₁))

/-- The square of `gibbsSqrtOp` equals `gibbsDensityOp`: $(\rho_\beta^{1/2})^2 = \rho_\beta$. -/
lemma gibbsSqrtOp_mul_self {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0) :
    gibbsSqrtOp ψ_eig E_eig β * gibbsSqrtOp ψ_eig E_eig β = gibbsDensityOp ψ_eig E_eig β := by
  have hZ_pos : 0 < gibbsPartitionZ E_eig β := gibbsPartitionZ_pos E_eig β
  have hZ_sq : (Real.sqrt (gibbsPartitionZ E_eig β)) * (Real.sqrt (gibbsPartitionZ E_eig β)) =
      gibbsPartitionZ E_eig β := Real.mul_self_sqrt (le_of_lt hZ_pos)
  change ((((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2))) *
    ((((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2))) =
    ((gibbsPartitionZ E_eig β : ℂ)⁻¹) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω))
  rw [clm_smul_mul, clm_mul_smul, clm_smul_smul,
    spectralWeightOp_mul_spectralWeightOp ψ_eig h_onb]
  have h_inv : (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) *
      (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) =
      (gibbsPartitionZ E_eig β : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, hZ_sq]
  have h_exp : (fun ω : ManyBodyConfig Site =>
      Real.exp (-β * E_eig ω / 2) * Real.exp (-β * E_eig ω / 2)) =
      (fun ω : ManyBodyConfig Site => Real.exp (-β * E_eig ω)) := by
    ext ω
    rw [← Real.exp_add]
    ring_nf
  rw [h_inv, h_exp]

/-- `gibbsSqrtOp` and `gibbsInvSqrtOp` are mutual inverses on a complete orthonormal eigenbasis. -/
lemma gibbsSqrtOp_mul_gibbsInvSqrtOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site, (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2) :
    gibbsSqrtOp ψ_eig E_eig β * gibbsInvSqrtOp ψ_eig E_eig β = 1 := by
  have hZ_pos : 0 < gibbsPartitionZ E_eig β := gibbsPartitionZ_pos E_eig β
  have hZ_sqrt_ne : (Real.sqrt (gibbsPartitionZ E_eig β) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hZ_pos))
  change ((((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2))) *
    (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (β * E_eig ω / 2))) = 1
  rw [clm_smul_mul, clm_mul_smul, clm_smul_smul, inv_mul_cancel₀ hZ_sqrt_ne, one_smul,
    spectralWeightOp_mul_spectralWeightOp ψ_eig h_onb]
  unfold spectralWeightOp
  have h_exp : ∀ ω : ManyBodyConfig Site,
      Real.exp (-β * E_eig ω / 2) * Real.exp (β * E_eig ω / 2) = 1 := by
    intro ω
    rw [← Real.exp_add]
    have : -β * E_eig ω / 2 + β * E_eig ω / 2 = 0 := by ring
    rw [this, Real.exp_zero]
  simp_rw [h_exp, Complex.ofReal_one, one_smul]
  exact onb_sum_ketBra_eq_one ψ_eig h_onb h_parseval

/-- Unit-norm property $\|\psi_{\mathrm{eig}}(\omega)\| = 1$ of an orthonormal eigenbasis. -/
private lemma eigenbasis_norm_eq_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    (ω : ManyBodyConfig Site) :
    ‖ψ_eig ω‖ = 1 := by
  have h_sq : ‖ψ_eig ω‖ ^ 2 = 1 := by
    rw [← h_parseval (ψ_eig ω), Finset.sum_eq_single ω]
    · rw [h_onb ω ω, if_pos rfl, norm_one, one_pow]
    · intro ω' _ hne
      rw [h_onb ω' ω, if_neg hne, norm_zero, sq, zero_mul]
    · intro h_not_mem
      exact False.elim (h_not_mem (Finset.mem_univ ω))
  nlinarith [norm_nonneg (ψ_eig ω)]

/-- The KMS norm of any operator $A$ is bounded by its operator norm: $\|A\|_{\mathrm{KMS}} \le \|A\|$. -/
lemma kmsNorm_le_opNorm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site, inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site, (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNorm ψ_eig E_eig β A ≤ ‖A‖ := by
  have h_row : ∀ B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      (∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
        gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) (B (ψ_eig ω₁))‖ ^ 2) ≤ ‖B‖ ^ 2 := by
    intro B
    have h_inner : ∀ ω₁ : ManyBodyConfig Site,
        (∑ ω₂ : ManyBodyConfig Site,
          gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) (B (ψ_eig ω₁))‖ ^ 2) ≤
        gibbsProb E_eig β ω₁ * ‖B‖ ^ 2 := by
      intro ω₁
      rw [← Finset.mul_sum, h_parseval (B (ψ_eig ω₁))]
      refine mul_le_mul_of_nonneg_left ?_ (gibbsProb_nonneg E_eig β ω₁)
      have hB_le : ‖B (ψ_eig ω₁)‖ ≤ ‖B‖ := by
        have h1 := B.le_opNorm (ψ_eig ω₁)
        rwa [eigenbasis_norm_eq_one ψ_eig h_onb h_parseval ω₁, mul_one] at h1
      nlinarith [norm_nonneg (B (ψ_eig ω₁)), norm_nonneg B]
    calc ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
          gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) (B (ψ_eig ω₁))‖ ^ 2
      _ ≤ ∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁ * ‖B‖ ^ 2 :=
        Finset.sum_le_sum fun ω₁ _ => h_inner ω₁
      _ = (∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁) * ‖B‖ ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ = ‖B‖ ^ 2 := by rw [sum_gibbsProb_eq_one E_eig β, one_mul]
  have h_col :
      (∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
        gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) ≤ ‖A‖ ^ 2 := by
    have h_eq :
        (∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
          gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) =
        ∑ ω₂ : ManyBodyConfig Site, ∑ ω₁ : ManyBodyConfig Site,
          gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₁) ((A†) (ψ_eig ω₂))‖ ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω₂ _ => Finset.sum_congr rfl fun ω₁ _ => ?_
      have h_adj : ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ =
          ‖inner ℂ (ψ_eig ω₁) ((A†) (ψ_eig ω₂))‖ := by
        rw [← ContinuousLinearMap.adjoint_inner_left A, norm_inner_symm]
      rw [h_adj]
    rw [h_eq]
    have h_adj_norm : ‖A†‖ = ‖A‖ :=
      (ContinuousLinearMap.adjoint :
        (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) ≃ₗᵢ⋆[ℂ]
        (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)).norm_map A
    calc ∑ ω₂ : ManyBodyConfig Site, ∑ ω₁ : ManyBodyConfig Site,
          gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₁) ((A†) (ψ_eig ω₂))‖ ^ 2
      _ ≤ ‖A†‖ ^ 2 := h_row (A†)
      _ = ‖A‖ ^ 2 := by rw [h_adj_norm]
  have h_amgm :
      kmsNormSq ψ_eig E_eig β A ≤ ‖A‖ ^ 2 := by
    rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis A]
    have h_pt : ∀ ω₁ ω₂ : ManyBodyConfig Site,
        Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
          ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2 ≤
        (1 / 2 : ℝ) * (gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2 +
          gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) := by
      intro ω₁ ω₂
      have hp₁ : (Real.sqrt (gibbsProb E_eig β ω₁)) ^ 2 = gibbsProb E_eig β ω₁ :=
        Real.sq_sqrt (gibbsProb_nonneg E_eig β ω₁)
      have hp₂ : (Real.sqrt (gibbsProb E_eig β ω₂)) ^ 2 = gibbsProb E_eig β ω₂ :=
        Real.sq_sqrt (gibbsProb_nonneg E_eig β ω₂)
      have h_sq_diff : 0 ≤ (Real.sqrt (gibbsProb E_eig β ω₁) - Real.sqrt (gibbsProb E_eig β ω₂)) ^ 2 :=
        sq_nonneg _
      have h_prob_amgm :
          Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) ≤
            (1 / 2 : ℝ) * (gibbsProb E_eig β ω₁ + gibbsProb E_eig β ω₂) := by
        nlinarith
      have h_mul := mul_le_mul_of_nonneg_right h_prob_amgm
        (sq_nonneg ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖)
      linarith
    have h_sum_le :
        (∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
          Real.sqrt (gibbsProb E_eig β ω₁) * Real.sqrt (gibbsProb E_eig β ω₂) *
            ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) ≤
        ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
          (1 / 2 : ℝ) * (gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2 +
            gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) :=
      Finset.sum_le_sum fun ω₁ _ => Finset.sum_le_sum fun ω₂ _ => h_pt ω₁ ω₂
    have h_rhs_split :
        (∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
          (1 / 2 : ℝ) * (gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2 +
            gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2)) =
        (1 / 2 : ℝ) * ((∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
            gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2) +
          (∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site,
            gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₂) (A (ψ_eig ω₁))‖ ^ 2)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω₁ _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω₂ _ => by ring
    have h1 := h_row A
    linarith
  unfold kmsNorm
  calc Real.sqrt (kmsNormSq ψ_eig E_eig β A)
    _ ≤ Real.sqrt (‖A‖ ^ 2) := Real.sqrt_le_sqrt h_amgm
    _ = ‖A‖ := Real.sqrt_sq (norm_nonneg A)
