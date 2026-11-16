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

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Defs.SafeSubspaceAndKMS

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

noncomputable section

/-!
# KMS Inner-Product Skew-Symmetry and Lindblad Dirichlet Dissipativity

Proves skew-symmetry of the coherent Liouvillian commutator in the KMS real inner product (`kmsInnerReal_commutator_eq_zero`), the KMS Cauchy–Schwarz inequality (`kmsInnerReal_le_kmsNorm_mul_kmsNorm`), and the coherent commutator drift bound (`kmsInnerReal_coherent_commutator_le`). Establishes non-negativity and Young's inequality for the KMS Dirichlet form (`kmsDirichletForm_nonneg`, `kms_dirichlet_young_ineq`) together with exact KMS inner-product identities for Lindblad dissipators.

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 2 (`subsec:setup`), Definition 2.6 (`def:kms-lindblad`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

lemma clm_smul_mul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) : (c • A) * B = c • (A * B) := by ext φ; rfl

lemma clm_mul_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) : A * (c • B) = c • (A * B) := by ext φ; exact map_smul A c (B φ)

lemma clm_smul_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c₁ c₂ : ℂ) (A : H →L[ℂ] H) : c₁ • (c₂ • A) = (c₁ * c₂) • A := by
  ext φ; exact smul_smul c₁ c₂ (A φ)

private lemma clm_neg_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A : H →L[ℂ] H) : (-c) • A = -(c • A) := by
  ext φ; exact neg_smul c (A φ)

lemma clm_smul_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) : c • (A - B) = c • A - c • B := by
  ext φ; exact smul_sub c (A φ) (B φ)

lemma clm_term1_reassoc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ Δ H_op K : H →L[ℂ] H) (hρH : ρ * H_op = K) :
    ρ * Δ * ρ * (Complex.I • (H_op * Δ)) = Complex.I • (ρ * (Δ * K * Δ)) := by
  rw [clm_mul_smul]; congr 1
  calc ρ * Δ * ρ * (H_op * Δ) = ρ * (Δ * (ρ * H_op) * Δ) := by simp only [mul_assoc]
    _ = ρ * (Δ * K * Δ) := by rw [hρH]

lemma clm_term2_reassoc1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ Δ H_op : H →L[ℂ] H) :
    ρ * Δ * ρ * (Complex.I • (Δ * H_op)) = ρ * (Complex.I • (Δ * ρ * Δ * H_op)) := by
  rw [clm_mul_smul, clm_mul_smul]; simp only [mul_assoc]

lemma clm_term2_reassoc2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ Δ H_op K : H →L[ℂ] H) (hHρ : H_op * ρ = K) :
    (Complex.I • (Δ * ρ * Δ * H_op)) * ρ = Complex.I • ((Δ * ρ * Δ) * K) := by
  rw [clm_smul_mul]; congr 1
  calc (Δ * ρ * Δ * H_op) * ρ = (Δ * ρ * Δ) * (H_op * ρ) := by simp only [mul_assoc]
    _ = (Δ * ρ * Δ) * K := by rw [hHρ]

lemma hilbertTrace_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] :
    hilbertTrace (0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) = 0 := by
  unfold hilbertTrace; apply Finset.sum_eq_zero; intro ψ _
  rw [ContinuousLinearMap.zero_apply, inner_zero_right, map_zero]

lemma hilbertTrace_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (A + B) = hilbertTrace A + hilbertTrace B := by
  unfold hilbertTrace; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [ContinuousLinearMap.add_apply, inner_add_right, map_add]

lemma hilbertTrace_neg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (-A) = -hilbertTrace A := by
  unfold hilbertTrace; rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [ContinuousLinearMap.neg_apply, inner_neg_right, map_neg]

lemma hilbertTrace_sub {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (A - B) = hilbertTrace A - hilbertTrace B := by
  rw [sub_eq_add_neg, hilbertTrace_add, hilbertTrace_neg, ← sub_eq_add_neg]

lemma hilbertTrace_smul_ofReal {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (c : ℝ) (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace ((c : ℂ) • A) = c * hilbertTrace A := by
  unfold hilbertTrace; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right]
  change ((c : ℂ) * inner ℂ (basisVecGlobal Site ψ) (A (basisVecGlobal Site ψ))).re =
    c * (inner ℂ (basisVecGlobal Site ψ) (A (basisVecGlobal Site ψ))).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma hilbertTrace_adjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (A†) = hilbertTrace A := by
  unfold hilbertTrace
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, RCLike.conj_re]

lemma isSelfAdjoint_rankOneKetBra {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (φ : H) :
    IsSelfAdjoint (rankOneKetBra φ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']; ext ψ; apply ext_inner_right ℂ; intro χ
  rw [ContinuousLinearMap.adjoint_inner_left]; dsimp [rankOneKetBra]
  rw [inner_smul_right, inner_smul_left, ← inner_conj_symm ψ φ, mul_comm]

lemma isSelfAdjoint_smul_ofReal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (c : ℝ) {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint ((c : ℂ) • A) := by
  rw [IsSelfAdjoint, star_smul, hA.star_eq, RCLike.star_def, Complex.conj_ofReal]

lemma isSelfAdjoint_conj_self {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {A B : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) : IsSelfAdjoint (A * B * A) := by
  rw [IsSelfAdjoint, star_mul, star_mul, hA.star_eq, hB.star_eq, mul_assoc]

lemma hilbertTrace_I_smul_mul_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (h_tr : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace (A * X) = hilbertTrace (X * A)) :
    hilbertTrace (Complex.I • (A * B)) = 0 ∧ hilbertTrace (Complex.I • (B * A)) = 0 := by
  have h1 : hilbertTrace (Complex.I • (A * B)) = hilbertTrace (Complex.I • (B * A)) := by
    rw [← clm_mul_smul, h_tr (Complex.I • B), clm_smul_mul]
  have h_adj : (Complex.I • (A * B))† = -(Complex.I • (B * A)) := by
    change star (Complex.I • (A * B)) = -(Complex.I • (B * A))
    rw [star_smul, star_mul, hA.star_eq, hB.star_eq, RCLike.star_def, Complex.conj_I, clm_neg_smul]
  have h2 : hilbertTrace (Complex.I • (A * B)) = -hilbertTrace (Complex.I • (B * A)) := by
    rw [← hilbertTrace_adjoint (Complex.I • (A * B)), h_adj, hilbertTrace_neg]
  constructor <;> linarith

def spectralWeightOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (w : ManyBodyConfig Site → ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ ω : ManyBodyConfig Site, (w ω : ℂ) • rankOneKetBra (ψ_eig ω)

lemma isSelfAdjoint_spectralWeightOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (w : ManyBodyConfig Site → ℝ) :
    IsSelfAdjoint (spectralWeightOp ψ_eig w) :=
  isSelfAdjoint_finset_sum Finset.univ _
    (fun ω _ => isSelfAdjoint_smul_ofReal (w ω) (isSelfAdjoint_rankOneKetBra (ψ_eig ω)))

lemma hilbertTrace_spectralWeightOp_mul_comm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (w : ManyBodyConfig Site → ℝ)
    (h_tr_eig : ∀ (ω : ManyBodyConfig Site)
      (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      hilbertTrace (rankOneKetBra (ψ_eig ω) * A) = hilbertTrace (A * rankOneKetBra (ψ_eig ω)))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (spectralWeightOp ψ_eig w * X) = hilbertTrace (X * spectralWeightOp ψ_eig w) := by
  unfold spectralWeightOp
  rw [Finset.sum_mul, Finset.mul_sum, hilbertTrace_sum, hilbertTrace_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [clm_smul_mul, clm_mul_smul, hilbertTrace_smul_ofReal, hilbertTrace_smul_ofReal, h_tr_eig ω X]

lemma gibbsSqrtOp_mul_H_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_right : ∀ ω, rankOneKetBra (ψ_eig ω) * H = (E_eig ω : ℂ) • rankOneKetBra (ψ_eig ω)) :
    gibbsSqrtOp ψ_eig E_eig β * H =
      (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2) * E_eig ω) := by
  unfold gibbsSqrtOp spectralWeightOp; rw [clm_smul_mul, Finset.sum_mul]; congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [clm_smul_mul, h_right ω, clm_smul_smul, Complex.ofReal_mul]

lemma op_mul_gibbsSqrtOp_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_left : ∀ ω, H * rankOneKetBra (ψ_eig ω) = (E_eig ω : ℂ) • rankOneKetBra (ψ_eig ω)) :
    H * gibbsSqrtOp ψ_eig E_eig β =
      (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2) * E_eig ω) := by
  unfold gibbsSqrtOp spectralWeightOp; rw [clm_mul_smul, Finset.mul_sum]; congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [clm_mul_smul, h_left ω, clm_smul_smul, Complex.ofReal_mul]

/-- **KMS Skew-Symmetry of the Coherent Liouvillian (`kmsInnerReal_commutator_eq_zero`)**:
    For every self-adjoint operator $\Delta$,
    $\operatorname{Re}\langle \Delta, i[H, \Delta]\rangle_{\mathrm{KMS}} = 0$. -/
theorem kmsInnerReal_commutator_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_eig : ∀ ω : ManyBodyConfig Site,
      H * rankOneKetBra (ψ_eig ω) = (E_eig ω : ℂ) • rankOneKetBra (ψ_eig ω) ∧
      rankOneKetBra (ψ_eig ω) * H = (E_eig ω : ℂ) • rankOneKetBra (ψ_eig ω) ∧
      ∀ A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        hilbertTrace (rankOneKetBra (ψ_eig ω) * A) =
          hilbertTrace (A * rankOneKetBra (ψ_eig ω)))
    (Δ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hΔ : IsSelfAdjoint Δ) :
    kmsInnerReal ψ_eig E_eig β Δ (Complex.I • opCommutator H Δ) = 0 := by
  have hρ_eq : gibbsSqrtOp ψ_eig E_eig β =
      (((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ : ℝ) : ℂ) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2)) := by
    unfold gibbsSqrtOp spectralWeightOp; rw [Complex.ofReal_inv]
  have hρ_sa : IsSelfAdjoint (gibbsSqrtOp ψ_eig E_eig β) := by
    rw [hρ_eq]; exact isSelfAdjoint_smul_ofReal _ (isSelfAdjoint_spectralWeightOp ψ_eig _)
  have hK_sa : IsSelfAdjoint
      ((((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ : ℝ) : ℂ) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2) * E_eig ω)) :=
    isSelfAdjoint_smul_ofReal _ (isSelfAdjoint_spectralWeightOp ψ_eig _)
  have hρ_tr : ∀ X, hilbertTrace (gibbsSqrtOp ψ_eig E_eig β * X) =
      hilbertTrace (X * gibbsSqrtOp ψ_eig E_eig β) := fun X => by
    rw [hρ_eq, clm_smul_mul, clm_mul_smul, hilbertTrace_smul_ofReal, hilbertTrace_smul_ofReal,
      hilbertTrace_spectralWeightOp_mul_comm ψ_eig _ (fun ω A => (h_eig ω).2.2 A) X]
  have hK_tr : ∀ X, hilbertTrace
      (((((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ : ℝ) : ℂ) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2) * E_eig ω)) * X) =
      hilbertTrace (X * ((((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ : ℝ) : ℂ) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2) * E_eig ω))) := fun X => by
    rw [clm_smul_mul, clm_mul_smul, hilbertTrace_smul_ofReal, hilbertTrace_smul_ofReal,
      hilbertTrace_spectralWeightOp_mul_comm ψ_eig _ (fun ω A => (h_eig ω).2.2 A) X]
  have hρH : gibbsSqrtOp ψ_eig E_eig β * H =
      (((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ : ℝ) : ℂ) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2) * E_eig ω) := by
    rw [Complex.ofReal_inv]; exact gibbsSqrtOp_mul_H_eq H ψ_eig E_eig β (fun ω => (h_eig ω).2.1)
  have hHρ : H * gibbsSqrtOp ψ_eig E_eig β =
      (((Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ : ℝ) : ℂ) •
        spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2) * E_eig ω) := by
    rw [Complex.ofReal_inv]; exact op_mul_gibbsSqrtOp_eq H ψ_eig E_eig β (fun ω => (h_eig ω).1)
  have hΔ_adj : Δ† = Δ := ContinuousLinearMap.isSelfAdjoint_iff'.mp hΔ
  unfold kmsInnerReal opCommutator
  rw [hΔ_adj, clm_smul_sub, mul_sub, hilbertTrace_sub]
  have h_term1_zero : hilbertTrace
      (gibbsSqrtOp ψ_eig E_eig β * Δ * gibbsSqrtOp ψ_eig E_eig β * (Complex.I • (H * Δ))) = 0 := by
    rw [clm_term1_reassoc (gibbsSqrtOp ψ_eig E_eig β) Δ H _ hρH]
    exact (hilbertTrace_I_smul_mul_eq_zero hρ_sa (isSelfAdjoint_conj_self hΔ hK_sa) hρ_tr).1
  have h_term2_zero : hilbertTrace
      (gibbsSqrtOp ψ_eig E_eig β * Δ * gibbsSqrtOp ψ_eig E_eig β * (Complex.I • (Δ * H))) = 0 := by
    rw [clm_term2_reassoc1 (gibbsSqrtOp ψ_eig E_eig β) Δ H, hρ_tr,
      clm_term2_reassoc2 (gibbsSqrtOp ψ_eig E_eig β) Δ H _ hHρ]
    exact (hilbertTrace_I_smul_mul_eq_zero hK_sa (isSelfAdjoint_conj_self hΔ hρ_sa) hK_tr).2
  rw [h_term1_zero, h_term2_zero, sub_self]

lemma kmsInnerReal_add_right {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A B₁ B₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β A (B₁ + B₂) =
      kmsInnerReal ψ_eig E_eig β A B₁ + kmsInnerReal ψ_eig E_eig β A B₂ := by
  unfold kmsInnerReal; rw [mul_add, hilbertTrace_add]

lemma opCommutator_sub_add_cancel {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (H_op O_s O : H →L[ℂ] H) :
    Complex.I • opCommutator H_op O_s =
      Complex.I • opCommutator H_op (O_s - O) + Complex.I • opCommutator H_op O := by
  unfold opCommutator; rw [← smul_add]; congr 1; rw [mul_sub, sub_mul]; abel

lemma kmsNormSq_I_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (C : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNormSq ψ_eig E_eig β (Complex.I • C) = kmsNormSq ψ_eig E_eig β C := by
  unfold kmsNormSq kmsInnerReal
  have h_adj : (Complex.I • C)† = (-Complex.I) • (C†) := by
    change star (Complex.I • C) = (-Complex.I) • (star C)
    rw [star_smul, RCLike.star_def, Complex.conj_I]
  rw [h_adj, clm_mul_smul, clm_mul_smul, clm_smul_mul, clm_smul_mul, clm_smul_smul]
  have hI : Complex.I * (-Complex.I) = (1 : ℂ) := by simp
  rw [hI, one_smul]

lemma kmsNorm_I_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (C : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNorm ψ_eig E_eig β (Complex.I • C) = kmsNorm ψ_eig E_eig β C := by
  dsimp [kmsNorm]; rw [kmsNormSq_I_smul]

/-- **KMS Cauchy–Schwarz Inequality (`kmsInnerReal_le_kmsNorm_mul_kmsNorm`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6 (`sec:lindblad`), Equation (93) (`eq:dirichlet-cs-bound`))**:
    For all operators $A, B \in \mathcal{B}(\mathcal{H})$,
    $\operatorname{Re}\langle A, B\rangle_{\mathrm{KMS}} \le \|A\|_{\mathrm{KMS}} \|B\|_{\mathrm{KMS}}$. -/
theorem kmsInnerReal_le_kmsNorm_mul_kmsNorm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β A B ≤ kmsNorm ψ_eig E_eig β A * kmsNorm ψ_eig E_eig β B := by
  let w : ManyBodyConfig Site × ManyBodyConfig Site → ℝ := fun p =>
    Real.sqrt (Real.sqrt (gibbsProb E_eig β p.1) * Real.sqrt (gibbsProb E_eig β p.2))
  let u : ManyBodyConfig Site × ManyBodyConfig Site → ℝ := fun p =>
    w p * ‖inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))‖
  let v : ManyBodyConfig Site × ManyBodyConfig Site → ℝ := fun p =>
    w p * ‖inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))‖
  have hw_sq : ∀ p, (w p) ^ 2 =
      Real.sqrt (gibbsProb E_eig β p.1) * Real.sqrt (gibbsProb E_eig β p.2) :=
    fun p => Real.sq_sqrt (by positivity)
  have h_lhs_le : kmsInnerReal ψ_eig E_eig β A B ≤
      ∑ p : ManyBodyConfig Site × ManyBodyConfig Site, u p * v p := by
    rw [kmsInnerReal_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis A B, ← Fintype.sum_prod_type']
    refine Finset.sum_le_sum fun p _ => ?_
    have h_re : RCLike.re (starRingEnd ℂ (inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))) *
          inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))) ≤
        ‖inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))‖ * ‖inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))‖ := by
      calc RCLike.re (starRingEnd ℂ (inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))) *
            inner ℂ (ψ_eig p.2) (B (ψ_eig p.1)))
        _ ≤ ‖starRingEnd ℂ (inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))) *
              inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))‖ := RCLike.re_le_norm _
        _ = ‖inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))‖ * ‖inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))‖ := by
          rw [norm_mul, RCLike.norm_conj]
    have h_uv : u p * v p =
        (Real.sqrt (gibbsProb E_eig β p.1) * Real.sqrt (gibbsProb E_eig β p.2)) *
          (‖inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))‖ * ‖inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))‖) := by
      calc u p * v p = (w p) ^ 2 * (‖inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))‖ *
            ‖inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))‖) := by dsimp [u, v]; ring
        _ = _ := by rw [hw_sq p]
    rw [h_uv]; exact mul_le_mul_of_nonneg_left h_re (by positivity)
  have h_u_sq : (∑ p, (u p) ^ 2) = kmsNormSq ψ_eig E_eig β A := by
    rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis A, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun p _ => ?_
    calc (u p) ^ 2 = (w p) ^ 2 * ‖inner ℂ (ψ_eig p.2) (A (ψ_eig p.1))‖ ^ 2 := by dsimp [u]; ring
      _ = _ := by rw [hw_sq p]
  have h_v_sq : (∑ p, (v p) ^ 2) = kmsNormSq ψ_eig E_eig β B := by
    rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis B, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun p _ => ?_
    calc (v p) ^ 2 = (w p) ^ 2 * ‖inner ℂ (ψ_eig p.2) (B (ψ_eig p.1))‖ ^ 2 := by dsimp [v]; ring
      _ = _ := by rw [hw_sq p]
  calc kmsInnerReal ψ_eig E_eig β A B
    _ ≤ ∑ p, u p * v p := h_lhs_le
    _ ≤ Real.sqrt (∑ p, (u p) ^ 2) * Real.sqrt (∑ p, (v p) ^ 2) :=
      fintype_sum_mul_le_sqrt_mul_sqrt u v
    _ = kmsNorm ψ_eig E_eig β A * kmsNorm ψ_eig E_eig β B := by
      dsimp [kmsNorm]; rw [h_u_sq, h_v_sq]

/-- Coherent commutator KMS Cauchy–Schwarz bound (Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`), Equation (90) (`eq:gronwall-sqrt-drift`)):
    $\operatorname{Re}\langle \Delta, i[H_0 + V_{\mathrm{tot}}, O]\rangle_{\mathrm{KMS}}
      \le \|\Delta\|_{\mathrm{KMS}} \, \Gamma_{\mathrm{coh}}(O)$. -/
theorem kmsInnerReal_coherent_commutator_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (V : LocalPerturbation D L Site)
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (Δ O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β Δ (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) O) ≤
      kmsNorm ψ_eig E_eig β Δ * kmsCoherentDrift sys V ψ_eig E_eig β O := by
  calc kmsInnerReal ψ_eig E_eig β Δ (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) O)
    _ ≤ kmsNorm ψ_eig E_eig β Δ *
          kmsNorm ψ_eig E_eig β (Complex.I • opCommutator (sys.H0 + V.totalPerturbation) O) :=
      kmsInnerReal_le_kmsNorm_mul_kmsNorm ψ_eig E_eig β h_onb h_tr_basis Δ _
    _ = kmsNorm ψ_eig E_eig β Δ * kmsCoherentDrift sys V ψ_eig E_eig β O := by
      rw [kmsNorm_I_smul, kmsCoherentDrift]

/-- Non-negativity of the dissipative KMS Dirichlet form `kmsDirichletForm`. -/
theorem kmsDirichletForm_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {BathIdx : Type} [Fintype BathIdx]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (L_jump : BoxD D L → BathIdx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    0 ≤ kmsDirichletForm ψ_eig E_eig β L_jump X := by
  unfold kmsDirichletForm
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun α _ => ?_)
  exact kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis (opCommutator (L_jump q α) X)

/-- Young's inequality for the KMS Dirichlet form:
    $-E(O_s) + \sqrt{E(O)}\sqrt{E(O_s)} \le \frac{1}{4}E(O)$. -/
theorem kms_dirichlet_young_ineq {E_O E_Os : ℝ} (hE_O : 0 ≤ E_O) (hE_Os : 0 ≤ E_Os) :
    -E_Os + Real.sqrt E_O * Real.sqrt E_Os ≤ (1 / 4 : ℝ) * E_O := by
  have h1 : (Real.sqrt E_O) ^ 2 = E_O := Real.sq_sqrt hE_O
  have h2 : (Real.sqrt E_Os) ^ 2 = E_Os := Real.sq_sqrt hE_Os
  have h_sq : 0 ≤ (Real.sqrt E_Os - (1 / 2 : ℝ) * Real.sqrt E_O) ^ 2 := sq_nonneg _
  nlinarith

lemma spectralWeightOp_mul_spectralWeightOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (w₁ w₂ : ManyBodyConfig Site → ℝ) :
    spectralWeightOp ψ_eig w₁ * spectralWeightOp ψ_eig w₂ =
      spectralWeightOp ψ_eig (fun ω => w₁ ω * w₂ ω) := by
  unfold spectralWeightOp; rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω₁ _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single ω₁]
  · rw [clm_smul_mul, clm_mul_smul, clm_smul_smul, onb_ketBra_mul_ketBra ψ_eig h_onb ω₁ ω₁,
      if_pos rfl, Complex.ofReal_mul]
  · intro ω₂ _ hne
    rw [clm_smul_mul, clm_mul_smul, clm_smul_smul, onb_ketBra_mul_ketBra ψ_eig h_onb ω₁ ω₂,
      if_neg (Ne.symm hne), smul_zero]
  · intro h_not_mem; exact False.elim (h_not_mem (Finset.mem_univ ω₁))

lemma gibbsSqrtOp_mul_gibbsInvSqrtOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2) :
    gibbsSqrtOp ψ_eig E_eig β * gibbsInvSqrtOp ψ_eig E_eig β = 1 := by
  have hZ_sqrt_ne : (Real.sqrt (gibbsPartitionZ E_eig β) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (gibbsPartitionZ_pos E_eig β)))
  change ((((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2))) *
    (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (β * E_eig ω / 2))) = 1
  rw [clm_smul_mul, clm_mul_smul, clm_smul_smul, inv_mul_cancel₀ hZ_sqrt_ne, one_smul,
    spectralWeightOp_mul_spectralWeightOp ψ_eig h_onb]
  unfold spectralWeightOp
  have h_exp : ∀ ω, Real.exp (-β * E_eig ω / 2) * Real.exp (β * E_eig ω / 2) = 1 := fun ω => by
    rw [← Real.exp_add]
    have : -β * E_eig ω / 2 + β * E_eig ω / 2 = 0 := by ring
    rw [this, Real.exp_zero]
  simp_rw [h_exp, Complex.ofReal_one, one_smul]
  exact onb_sum_ketBra_eq_one ψ_eig h_onb h_parseval

lemma gibbsInvSqrtOp_mul_gibbsSqrtOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2) :
    gibbsInvSqrtOp ψ_eig E_eig β * gibbsSqrtOp ψ_eig E_eig β = 1 := by
  have hZ_sqrt_ne : (Real.sqrt (gibbsPartitionZ E_eig β) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (gibbsPartitionZ_pos E_eig β)))
  change (((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (β * E_eig ω / 2))) *
    ((((Real.sqrt (gibbsPartitionZ E_eig β)) : ℂ)⁻¹) •
      spectralWeightOp ψ_eig (fun ω => Real.exp (-β * E_eig ω / 2))) = 1
  rw [clm_smul_mul, clm_mul_smul, clm_smul_smul, mul_inv_cancel₀ hZ_sqrt_ne, one_smul,
    spectralWeightOp_mul_spectralWeightOp ψ_eig h_onb]
  unfold spectralWeightOp
  have h_exp : ∀ ω, Real.exp (β * E_eig ω / 2) * Real.exp (-β * E_eig ω / 2) = 1 := fun ω => by
    rw [← Real.exp_add]
    have : β * E_eig ω / 2 + -β * E_eig ω / 2 = 0 := by ring
    rw [this, Real.exp_zero]
  simp_rw [h_exp, Complex.ofReal_one, one_smul]
  exact onb_sum_ketBra_eq_one ψ_eig h_onb h_parseval

private lemma opCommutator_adjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L_op A : H →L[ℂ] H) :
    (opCommutator L_op A)† = A† * (L_op)† - (L_op)† * A† := by
  unfold opCommutator
  change star (L_op * A - A * L_op) = (star A) * (star L_op) - (star L_op) * (star A)
  rw [star_sub, star_mul, star_mul]

private lemma clm_sandwich_inv_step1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S S_inv X C : H →L[ℂ] H) (h_SSinv : S * S_inv = 1) :
    S * X * S * (S_inv * C * S_inv) = (S * X * C) * S_inv := by
  calc S * X * S * (S_inv * C * S_inv)
    _ = (S * X * (S * S_inv) * C) * S_inv := by simp only [mul_assoc]
    _ = (S * X * 1 * C) * S_inv := by rw [h_SSinv]
    _ = (S * X * C) * S_inv := by rw [mul_one]

private lemma clm_sandwich_inv_step2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (S S_inv X C : H →L[ℂ] H) (h_SinvS : S_inv * S = 1) :
    S_inv * (S * X * C) = X * C := by
  calc S_inv * (S * X * C) = (S_inv * S) * X * C := by simp only [mul_assoc]
    _ = 1 * X * C := by rw [h_SinvS]
    _ = X * C := by rw [one_mul]

private lemma clm_mul_sub_reassoc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (X Y K : H →L[ℂ] H) : X * (Y * K - K * Y) = (X * Y) * K - (X * K) * Y := by
  rw [mul_sub, ← mul_assoc X Y K, ← mul_assoc X K Y]

private lemma clm_sub_mul_adjoint_commutator {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L_op A S D_B : H →L[ℂ] H) :
    (A† * L_op†) * (S * D_B * S) - L_op† * (A† * (S * D_B * S)) =
      ((opCommutator L_op A)† * S * D_B) * S := by
  rw [← mul_assoc (L_op†) (A†) (S * D_B * S), ← sub_mul, ← opCommutator_adjoint L_op A]
  simp only [mul_assoc]

private lemma hilbertTrace_sandwich_commutator_aux {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (S S_inv L_op A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_SSinv : S * S_inv = 1) (h_SinvS : S_inv * S = 1) :
    hilbertTrace
      (S * A† * S *
        (S_inv * (L_op† * (S * opCommutator L_op B * S) -
          (S * opCommutator L_op B * S) * L_op†) * S_inv)) =
      hilbertTrace (S * (opCommutator L_op A)† * S * opCommutator L_op B) := by
  rw [clm_sandwich_inv_step1 S S_inv (A†) _ h_SSinv, hilbertTrace_mul_comm_aux _ S_inv,
    clm_sandwich_inv_step2 S S_inv (A†) _ h_SinvS,
    clm_mul_sub_reassoc (A†) (L_op†) (S * opCommutator L_op B * S), hilbertTrace_sub,
    hilbertTrace_mul_comm_aux (A† * (S * opCommutator L_op B * S)) (L_op†), ← hilbertTrace_sub,
    clm_sub_mul_adjoint_commutator L_op A S (opCommutator L_op B), hilbertTrace_mul_comm_aux _ S]
  simp only [mul_assoc]

private lemma opCommutator_sub_right {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L_op X Y : H →L[ℂ] H) : opCommutator L_op (X - Y) = opCommutator L_op X - opCommutator L_op Y := by
  unfold opCommutator; rw [mul_sub, sub_mul]; abel

private lemma kmsInnerReal_sub_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A₁ A₂ B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsInnerReal ψ_eig E_eig β (A₁ - A₂) B =
      kmsInnerReal ψ_eig E_eig β A₁ B - kmsInnerReal ψ_eig E_eig β A₂ B := by
  unfold kmsInnerReal; rw [map_sub, mul_sub, sub_mul, sub_mul, hilbertTrace_sub]

end
