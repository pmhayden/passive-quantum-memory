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
import Proofs.KMSSafeSubspaceODE.SyndromeCollarTelescopingBound

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

noncomputable section

/-!
# Pointwise Kullback–Leibler Inequality and KMS Fourth-Root Parseval Lemmas

Proves syndrome-fiber sum rearrangements (`sum_syndrome_fibers_eq_sum_filter_mem`) and the pointwise Kullback–Leibler inequality (`gibbs_pointwise_kl_ineq`). Establishes the spectral Cauchy–Schwarz and Parseval bounds (`kmsNormSq_proj_mul_le`, `kmsNormSq_mul_proj_le`) underlying the KMS fourth-root projector inequality.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.1 (`lem:duhamel-weyl-ratio`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
-/

namespace KMSPinchedGibbs

lemma hilbertTrace_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] :
    hilbertTrace (0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) = 0 := by
  unfold hilbertTrace; apply Finset.sum_eq_zero; intro ψ _
  rw [ContinuousLinearMap.zero_apply, inner_zero_right, map_zero]

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

lemma rankOneKetBra_mul_eq_self_of_isSelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {ψ : H} {P : H →L[ℂ] H} (hP : IsSelfAdjoint P) (hψ : P ψ = ψ) :
    rankOneKetBra ψ * P = rankOneKetBra ψ := by
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP
  ext φ; change inner ℂ ψ (P φ) • ψ = inner ℂ ψ φ • ψ
  rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj, hψ]

lemma rankOneKetBra_mul_eq_zero_of_isSelfAdjoint {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {ψ : H} {P : H →L[ℂ] H} (hP : IsSelfAdjoint P) (hψ : P ψ = 0) :
    rankOneKetBra ψ * P = 0 := by
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP
  ext φ; change inner ℂ ψ (P φ) • ψ = 0
  rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj, hψ, inner_zero_left, zero_smul]

lemma sum_syndrome_fibers_eq_sum_filter_mem {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (σ_eig : ManyBodyConfig Site → SyndromeConfig D L)
    (S : Finset (SyndromeConfig D L)) (f : ManyBodyConfig Site → ℝ) :
    (∑ σ ∈ S, ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω = σ), f ω) =
      ∑ ω ∈ Finset.univ.filter (fun ω : ManyBodyConfig Site => σ_eig ω ∈ S), f ω := by
  simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => by simp [Finset.sum_ite_eq]

lemma gibbs_pointwise_kl_ineq {p E β Z : ℝ} (hp : 0 ≤ p) (hZ : 0 < Z) :
    let q := Real.exp (-β * E) / Z
    p - q ≤ β * (p * E) + (if p = 0 then 0 else p * Real.log p) + p * Real.log Z := by
  intro q
  have hq_pos : 0 < q := div_pos (Real.exp_pos (-β * E)) hZ
  by_cases hp0 : p = 0
  · subst hp0; simp only [↓reduceIte]; linarith
  · have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    rw [if_neg hp0]
    have h_log_le : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq_pos hp_pos)
    have h_log_qp : Real.log (q / p) = -β * E - Real.log Z - Real.log p := by
      rw [Real.log_div (ne_of_gt hq_pos) (ne_of_gt hp_pos),
        Real.log_div (ne_of_gt (Real.exp_pos (-β * E))) (ne_of_gt hZ), Real.log_exp]
    have h_mul := mul_le_mul_of_nonneg_left h_log_le (le_of_lt hp_pos)
    have h_rhs : p * (q / p - 1) = q - p := by rw [mul_sub, mul_one, mul_div_cancel₀ q hp0]
    rw [h_log_qp, h_rhs] at h_mul; linarith

/-! ## 1. KMS Norm & Fourth-Root Projector Helper Lemmas -/

lemma sqrt_sum_sq_le_of_le_add {ι : Type*} [Fintype ι]
    (u v z : ι → ℝ)
    (hz : ∀ i : ι, 0 ≤ z i) (h_le : ∀ i : ι, z i ≤ u i + v i) :
    Real.sqrt (∑ i : ι, (z i) ^ 2) ≤
      Real.sqrt (∑ i : ι, (u i) ^ 2) + Real.sqrt (∑ i : ι, (v i) ^ 2) := by
  set U := Real.sqrt (∑ i : ι, (u i) ^ 2)
  set V := Real.sqrt (∑ i : ι, (v i) ^ 2)
  have hU_sq : U ^ 2 = ∑ i : ι, (u i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (u i))
  have hV_sq : V ^ 2 = ∑ i : ι, (v i) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))
  have h_cs : (∑ i : ι, u i * v i) ≤ U * V := fintype_sum_mul_le_sqrt_mul_sqrt u v
  have h_pt : ∀ i : ι, (z i) ^ 2 ≤ (u i) ^ 2 + (2 * (u i * v i) + (v i) ^ 2) := by
    intro i; have h1 := h_le i; have h2 := hz i; nlinarith
  have h_sum_le : (∑ i : ι, (z i) ^ 2) ≤ (U + V) ^ 2 := by
    calc ∑ i : ι, (z i) ^ 2
      _ ≤ ∑ i : ι, ((u i) ^ 2 + (2 * (u i * v i) + (v i) ^ 2)) :=
        Finset.sum_le_sum fun i _ => h_pt i
      _ = (∑ i : ι, (u i) ^ 2) + (2 * (∑ i : ι, u i * v i) + (∑ i : ι, (v i) ^ 2)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = U ^ 2 + 2 * (∑ i : ι, u i * v i) + V ^ 2 := by rw [← hU_sq, ← hV_sq]; ring
      _ ≤ U ^ 2 + 2 * (U * V) + V ^ 2 := by linarith
      _ = (U + V) ^ 2 := by ring
  calc Real.sqrt (∑ i : ι, (z i) ^ 2)
    _ ≤ Real.sqrt ((U + V) ^ 2) := Real.sqrt_le_sqrt h_sum_le
    _ = U + V := Real.sqrt_sq (by positivity)

lemma kmsNorm_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω)))) :
    kmsNorm ψ_eig E_eig β 0 = 0 := by
  unfold kmsNorm
  rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis 0]
  simp

lemma eigenbasis_norm_eq_one {D L : ℕ}
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
    · intro ω' _ hne; rw [h_onb ω' ω, if_neg hne, norm_zero, sq, zero_mul]
    · intro h_not_mem; exact False.elim (h_not_mem (Finset.mem_univ ω))
  nlinarith [norm_nonneg (ψ_eig ω)]

lemma hilbertTrace_gibbsDensityOp_mul_proj_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) :
    0 ≤ hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) := by
  rw [hilbertTrace_gibbsDensityOp_mul_eq ψ_eig E_eig β h_onb h_tr_basis P]
  refine Finset.sum_nonneg fun ω _ => ?_
  rw [isStarProjection_re_inner_eq_norm_sq hP (ψ_eig ω)]
  exact mul_nonneg (gibbsProb_nonneg E_eig β ω) (sq_nonneg _)

lemma kmsNormSq_proj_mul_le {D L : ℕ}
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
    (hP : IsStarProjection P)
    (K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNormSq ψ_eig E_eig β (P * K) ≤
      ‖K‖ ^ 2 * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) := by
  let u : ManyBodyConfig Site × ManyBodyConfig Site → ℝ := fun p =>
    Real.sqrt (gibbsProb E_eig β p.2) * ‖inner ℂ (ψ_eig p.2) ((P * K) (ψ_eig p.1))‖
  let v : ManyBodyConfig Site × ManyBodyConfig Site → ℝ := fun p =>
    Real.sqrt (gibbsProb E_eig β p.1) * ‖inner ℂ (ψ_eig p.2) ((P * K) (ψ_eig p.1))‖
  have h_eq_sum :
      kmsNormSq ψ_eig E_eig β (P * K) =
        ∑ p : ManyBodyConfig Site × ManyBodyConfig Site, u p * v p := by
    rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis (P * K),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => ?_
    dsimp [u, v]; ring
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  have h_u_sq_sum :
      (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (u p) ^ 2) ≤
        ‖K‖ ^ 2 * hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) := by
    have h_inner_sum : ∀ ω₂ : ManyBodyConfig Site,
        (∑ ω₁ : ManyBodyConfig Site, (u (ω₁, ω₂)) ^ 2) ≤
          gibbsProb E_eig β ω₂ * (‖K‖ ^ 2 * RCLike.re (inner ℂ (ψ_eig ω₂) (P (ψ_eig ω₂)))) := by
      intro ω₂
      have h_term : ∀ ω₁ : ManyBodyConfig Site,
          (u (ω₁, ω₂)) ^ 2 =
            gibbsProb E_eig β ω₂ * ‖inner ℂ (ψ_eig ω₁) ((K†) (P (ψ_eig ω₂)))‖ ^ 2 := by
        intro ω₁; dsimp [u]
        have h_in : ‖inner ℂ (ψ_eig ω₂) ((P * K) (ψ_eig ω₁))‖ =
            ‖inner ℂ (ψ_eig ω₁) ((K†) (P (ψ_eig ω₂)))‖ := by
          change ‖inner ℂ (ψ_eig ω₂) (P (K (ψ_eig ω₁)))‖ = _
          rw [← ContinuousLinearMap.adjoint_inner_left P, hP_adj,
            ← ContinuousLinearMap.adjoint_inner_left K, norm_inner_symm]
        rw [h_in, mul_pow, Real.sq_sqrt (gibbsProb_nonneg E_eig β ω₂)]
      simp_rw [h_term]
      rw [← Finset.mul_sum, h_parseval ((K†) (P (ψ_eig ω₂)))]
      refine mul_le_mul_of_nonneg_left ?_ (gibbsProb_nonneg E_eig β ω₂)
      have h_op : ‖(K†) (P (ψ_eig ω₂))‖ ≤ ‖K‖ * ‖P (ψ_eig ω₂)‖ := by
        have h1 := (K†).le_opNorm (P (ψ_eig ω₂))
        rwa [norm_adjoint_eq K] at h1
      have h_sq_op : ‖(K†) (P (ψ_eig ω₂))‖ ^ 2 ≤ ‖K‖ ^ 2 * ‖P (ψ_eig ω₂)‖ ^ 2 := by
        nlinarith [norm_nonneg ((K†) (P (ψ_eig ω₂))), norm_nonneg K, norm_nonneg (P (ψ_eig ω₂))]
      rwa [isStarProjection_re_inner_eq_norm_sq hP (ψ_eig ω₂)]
    calc ∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (u p) ^ 2
      _ = ∑ ω₂ : ManyBodyConfig Site, ∑ ω₁ : ManyBodyConfig Site, (u (ω₁, ω₂)) ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ ≤ ∑ ω₂ : ManyBodyConfig Site,
            gibbsProb E_eig β ω₂ * (‖K‖ ^ 2 * RCLike.re (inner ℂ (ψ_eig ω₂) (P (ψ_eig ω₂)))) :=
        Finset.sum_le_sum fun ω₂ _ => h_inner_sum ω₂
      _ = ‖K‖ ^ 2 * ∑ ω₂ : ManyBodyConfig Site,
            gibbsProb E_eig β ω₂ * RCLike.re (inner ℂ (ψ_eig ω₂) (P (ψ_eig ω₂))) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ω₂ _ => by ring
      _ = ‖K‖ ^ 2 * hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) := by
        rw [hilbertTrace_gibbsDensityOp_mul_eq ψ_eig E_eig β h_onb h_tr_basis P]
  have h_v_sq_sum :
      (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (v p) ^ 2) ≤ ‖K‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    have h_inner_sum : ∀ ω₁ : ManyBodyConfig Site,
        (∑ ω₂ : ManyBodyConfig Site, (v (ω₁, ω₂)) ^ 2) ≤
          gibbsProb E_eig β ω₁ * ‖K‖ ^ 2 := by
      intro ω₁
      have h_term : ∀ ω₂ : ManyBodyConfig Site,
          (v (ω₁, ω₂)) ^ 2 =
            gibbsProb E_eig β ω₁ * ‖inner ℂ (ψ_eig ω₂) ((P * K) (ψ_eig ω₁))‖ ^ 2 := by
        intro ω₂; dsimp [v]; rw [mul_pow, Real.sq_sqrt (gibbsProb_nonneg E_eig β ω₁)]
      simp_rw [h_term]
      rw [← Finset.mul_sum, h_parseval ((P * K) (ψ_eig ω₁))]
      refine mul_le_mul_of_nonneg_left ?_ (gibbsProb_nonneg E_eig β ω₁)
      have h_proj_le : ‖(P * K) (ψ_eig ω₁)‖ ^ 2 ≤ ‖K (ψ_eig ω₁)‖ ^ 2 :=
        isStarProjection_norm_sq_apply_le hP (K (ψ_eig ω₁))
      have h_K_le : ‖K (ψ_eig ω₁)‖ ≤ ‖K‖ := by
        have h1 := K.le_opNorm (ψ_eig ω₁)
        rw [eigenbasis_norm_eq_one ψ_eig h_onb h_parseval ω₁, mul_one] at h1
        exact h1
      have h_K_sq_le : ‖K (ψ_eig ω₁)‖ ^ 2 ≤ ‖K‖ ^ 2 := by
        nlinarith [norm_nonneg (K (ψ_eig ω₁)), norm_nonneg K]
      exact le_trans h_proj_le h_K_sq_le
    calc ∑ ω₁ : ManyBodyConfig Site, ∑ ω₂ : ManyBodyConfig Site, (v (ω₁, ω₂)) ^ 2
      _ ≤ ∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁ * ‖K‖ ^ 2 :=
        Finset.sum_le_sum fun ω₁ _ => h_inner_sum ω₁
      _ = (∑ ω₁ : ManyBodyConfig Site, gibbsProb E_eig β ω₁) * ‖K‖ ^ 2 :=
        (Finset.sum_mul _ _ _).symm
      _ = ‖K‖ ^ 2 := by rw [sum_gibbsProb_eq_one E_eig β, one_mul]
  have hp_nonneg : 0 ≤ hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) :=
    hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP
  have h_sqrt_u :
      Real.sqrt (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (u p) ^ 2) ≤
        ‖K‖ * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) := by
    have h_rhs_sq :
        ‖K‖ ^ 2 * hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) =
          (‖K‖ * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P))) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hp_nonneg]
    calc Real.sqrt (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (u p) ^ 2)
      _ ≤ Real.sqrt (‖K‖ ^ 2 * hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) :=
        Real.sqrt_le_sqrt h_u_sq_sum
      _ = Real.sqrt ((‖K‖ * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P))) ^ 2) := by
        rw [h_rhs_sq]
      _ = ‖K‖ * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) :=
        Real.sqrt_sq (by positivity)
  have h_sqrt_v :
      Real.sqrt (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (v p) ^ 2) ≤ ‖K‖ := by
    calc Real.sqrt (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (v p) ^ 2)
      _ ≤ Real.sqrt (‖K‖ ^ 2) := Real.sqrt_le_sqrt h_v_sq_sum
      _ = ‖K‖ := Real.sqrt_sq (norm_nonneg K)
  calc kmsNormSq ψ_eig E_eig β (P * K)
    _ = ∑ p : ManyBodyConfig Site × ManyBodyConfig Site, u p * v p := h_eq_sum
    _ ≤ Real.sqrt (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (u p) ^ 2) *
          Real.sqrt (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (v p) ^ 2) :=
      fintype_sum_mul_le_sqrt_mul_sqrt u v
    _ ≤ (‖K‖ * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P))) * ‖K‖ :=
      mul_le_mul h_sqrt_u h_sqrt_v (Real.sqrt_nonneg _) (by positivity)
    _ = ‖K‖ ^ 2 * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) := by ring

lemma kmsNormSq_mul_proj_le {D L : ℕ}
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
    (hP : IsStarProjection P)
    (K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNormSq ψ_eig E_eig β (K * P) ≤
      ‖K‖ ^ 2 * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) := by
  have hP_star : star P = P := hP.isSelfAdjoint.star_eq
  have h_adj : (K * P)† = P * K† := by
    change star (K * P) = P * star K
    rw [star_mul, hP_star]
  calc kmsNormSq ψ_eig E_eig β (K * P)
    _ = kmsNormSq ψ_eig E_eig β ((K * P)†) :=
      (kmsNormSq_adjoint ψ_eig E_eig β h_onb h_tr_basis (K * P)).symm
    _ = kmsNormSq ψ_eig E_eig β (P * K†) := by rw [h_adj]
    _ ≤ ‖K†‖ ^ 2 * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) :=
      kmsNormSq_proj_mul_le ψ_eig E_eig β h_onb h_tr_basis h_parseval hP (K†)
    _ = ‖K‖ ^ 2 * Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) := by
      rw [norm_adjoint_eq K]

lemma norm_le_one_of_isSelfAdjoint_sq_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {O : E →L[ℂ] E} (hO_sa : IsSelfAdjoint O) (hO_sq : O * O = 1) :
    ‖O‖ ≤ 1 := by
  have hO_adj : O† = O := ContinuousLinearMap.isSelfAdjoint_iff'.mp hO_sa
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  rw [one_mul]
  have h_inner : inner ℂ (O ψ) (O ψ) = inner ℂ ψ ψ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hO_adj]
    change inner ℂ ((O * O) ψ) ψ = inner ℂ ψ ψ
    rw [hO_sq, ContinuousLinearMap.one_apply]
  have h_norm_sq : ‖O ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    have h1 : (((‖O ψ‖ ^ 2 : ℝ) : ℂ)) = (((‖ψ‖ ^ 2 : ℝ) : ℂ)) := by
      simpa [inner_self_eq_norm_sq_to_K] using h_inner
    exact_mod_cast h1
  nlinarith [norm_nonneg (O ψ), norm_nonneg ψ]

lemma norm_opCommutator_le_two_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) {O : E →L[ℂ] E} (hO : ‖O‖ ≤ 1) :
    ‖opCommutator A O‖ ≤ 2 * ‖A‖ := by
  dsimp [opCommutator]
  have h1 : ‖A * O‖ ≤ ‖A‖ := norm_mul_le_of_le_one_right hO
  have h2 : ‖O * A‖ ≤ ‖A‖ := norm_mul_le_of_le_one_left hO
  calc ‖A * O - O * A‖
    _ ≤ ‖A * O‖ + ‖O * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ + ‖A‖ := add_le_add h1 h2
    _ = 2 * ‖A‖ := by ring

end KMSPinchedGibbs

end
