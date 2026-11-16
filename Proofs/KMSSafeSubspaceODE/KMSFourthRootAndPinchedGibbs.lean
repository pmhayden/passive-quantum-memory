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
import Proofs.KMSSafeSubspaceODE.VariationalFreeEnergyAndFourthRoot

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

noncomputable section

/-!
# KMS Fourth-Root Commutator Bounds and Safe-Subspace Drift–Dirichlet Bridges

Proves the KMS norm triangle inequality (`kmsNorm_add_le`, `kmsNorm_sum_le`), the KMS fourth-root projector sandwich inequality (`kms_fourth_root_projector_bound`), and the safe-subspace commutator fourth-root bridge (`kms_safe_commutator_fourth_root_bound`). Derives KMS coherent-drift and Dirichlet-form bounds from two-sided safe-subspace immunity and decoder discrepancy (`kms_drift_dirichlet_fourth_root_from_immunity`, `kms_drift_dirichlet_fourth_root_from_discrepancy`, `two_sided_operator_safe_immunity`).

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part II, Section 6.1 (`subsec:fourth-root-firewall`), Lemma 6.1 (`lem:kms-fourth-root`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.5 (`thm:main-D`)
-/

/-- Triangle inequality for the KMS norm:
    $\|A + B\|_{\mathrm{KMS}} \le \|A\|_{\mathrm{KMS}} + \|B\|_{\mathrm{KMS}}$. -/
theorem kmsNorm_add_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    kmsNorm ψ_eig E_eig β (A + B) ≤
      kmsNorm ψ_eig E_eig β A + kmsNorm ψ_eig E_eig β B := by
  let w : ManyBodyConfig Site × ManyBodyConfig Site → ℝ := fun p =>
    Real.sqrt (Real.sqrt (gibbsProb E_eig β p.1) * Real.sqrt (gibbsProb E_eig β p.2))
  let vec : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →
      ManyBodyConfig Site × ManyBodyConfig Site → ℝ :=
    fun X p => w p * ‖inner ℂ (ψ_eig p.2) (X (ψ_eig p.1))‖
  have h_norm_eq : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      kmsNorm ψ_eig E_eig β X =
        Real.sqrt (∑ p : ManyBodyConfig Site × ManyBodyConfig Site, (vec X p) ^ 2) := by
    intro X
    dsimp [kmsNorm]
    congr 1
    rw [kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis X, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ω₁ _ => Finset.sum_congr rfl fun ω₂ _ => ?_
    dsimp [vec, w]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [h_norm_eq (A + B), h_norm_eq A, h_norm_eq B]
  refine sqrt_sum_sq_le_of_le_add (vec A) (vec B) (vec (A + B))
    (fun p => by dsimp [vec, w]; positivity)
    (fun p => ?_)
  dsimp [vec]
  rw [← mul_add, ContinuousLinearMap.add_apply, inner_add_right]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

/-- Finite-sum subadditivity (triangle inequality) for `kmsNorm`:
    $\|\sum_{i \in s} A_i\|_{\mathrm{KMS}} \le \sum_{i \in s} \|A_i\|_{\mathrm{KMS}}$. -/
theorem kmsNorm_sum_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    {ι : Type*} (s : Finset ι)
    (A : ι → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    kmsNorm ψ_eig E_eig β (∑ i ∈ s, A i) ≤
      ∑ i ∈ s, kmsNorm ψ_eig E_eig β (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, kmsNorm_zero ψ_eig E_eig β h_onb h_tr_basis]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_add := kmsNorm_add_le ψ_eig E_eig β h_onb h_tr_basis (A a) (∑ i ∈ s, A i)
    linarith

/-- **KMS Fourth-Root Projector Bound (`kms_fourth_root_projector_bound`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`), Equation (88) (`eq:exact-fourth-root-cs`))**:
    For any orthogonal projection $P$ (`IsStarProjection P`) and bounded operator $K \in \mathcal{B}(\mathcal{H})$,
    if $\operatorname{Tr}(\rho_\beta P) \le p_{\mathrm{fail}}$, then
    $\|P K\|_{\mathrm{KMS}} \le \|K\| p_{\mathrm{fail}}^{1/4}$ and $\|K P\|_{\mathrm{KMS}} \le \|K\| p_{\mathrm{fail}}^{1/4}$. -/
theorem kms_fourth_root_projector_bound {D L : ℕ}
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
    (K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {p_fail : ℝ}
    (hp_le : hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) ≤ p_fail) :
    kmsNormSq ψ_eig E_eig β (P * K) ≤ ‖K‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) ∧
    kmsNormSq ψ_eig E_eig β (K * P) ≤ ‖K‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) ∧
    kmsNorm ψ_eig E_eig β (P * K) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) ∧
    kmsNorm ψ_eig E_eig β (K * P) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) := by
  have hp_tr_nonneg : 0 ≤ hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P) :=
    hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP
  have hp_nonneg : 0 ≤ p_fail := le_trans hp_tr_nonneg hp_le
  have h_sqrt_le :
      Real.sqrt (hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P)) ≤ p_fail ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hp_le
  have h_sq_PK : kmsNormSq ψ_eig E_eig β (P * K) ≤ ‖K‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) :=
    le_trans (kmsNormSq_proj_mul_le ψ_eig E_eig β h_onb h_tr_basis h_parseval hP K)
      (mul_le_mul_of_nonneg_left h_sqrt_le (sq_nonneg ‖K‖))
  have h_sq_KP : kmsNormSq ψ_eig E_eig β (K * P) ≤ ‖K‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) :=
    le_trans (kmsNormSq_mul_proj_le ψ_eig E_eig β h_onb h_tr_basis h_parseval hP K)
      (mul_le_mul_of_nonneg_left h_sqrt_le (sq_nonneg ‖K‖))
  have h_rpow : (p_fail ^ (1 / 4 : ℝ)) ^ 2 = p_fail ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg]; norm_num
  have h_rpow_sq : (‖K‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2 = ‖K‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ)) := by
    rw [mul_pow, h_rpow]
  have h_norm_PK : kmsNorm ψ_eig E_eig β (P * K) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) := by
    dsimp [kmsNorm]
    calc Real.sqrt (kmsNormSq ψ_eig E_eig β (P * K))
      _ ≤ Real.sqrt (‖K‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ))) := Real.sqrt_le_sqrt h_sq_PK
      _ = Real.sqrt ((‖K‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2) := by rw [h_rpow_sq]
      _ = ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) := Real.sqrt_sq (by positivity)
  have h_norm_KP : kmsNorm ψ_eig E_eig β (K * P) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) := by
    dsimp [kmsNorm]
    calc Real.sqrt (kmsNormSq ψ_eig E_eig β (K * P))
      _ ≤ Real.sqrt (‖K‖ ^ 2 * (p_fail ^ (1 / 2 : ℝ))) := Real.sqrt_le_sqrt h_sq_KP
      _ = Real.sqrt ((‖K‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2) := by rw [h_rpow_sq]
      _ = ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) := Real.sqrt_sq (by positivity)
  exact ⟨h_sq_PK, h_sq_KP, h_norm_PK, h_norm_KP⟩

/-- **KMS Safe-Subspace Commutator Fourth-Root Bound (`kms_safe_commutator_fourth_root_bound`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`), Equation (87) (`eq:kms-commutator-bridge`))**. -/
theorem kms_safe_commutator_fourth_root_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (F_fail : Finset (SyndromeConfig D L))
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    (hP_fail : IsStarProjection (bareFailureProjector sys F_fail))
    {O A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : ‖O‖ ≤ 1)
    (h_fw : SatisfiesTwoSidedOperatorImmunity sys F_fail O A)
    {M p_fail : ℝ}
    (hA_norm : ‖A‖ ≤ M)
    (hp_le : hilbertTrace (gibbsDensityOp ψ_eig E_eig β * bareFailureProjector sys F_fail) ≤ p_fail) :
    kmsNorm ψ_eig E_eig β (opCommutator A O) ≤ 4 * M * (p_fail ^ (1 / 4 : ℝ)) ∧
    kmsNormSq ψ_eig E_eig β (opCommutator A O) ≤ 16 * (M ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
  let P_fail := bareFailureProjector sys F_fail
  let C := opCommutator A O
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg ψ_eig E_eig β h_onb h_tr_basis hP_fail) hp_le
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg A) hA_norm
  have hC_norm : ‖C‖ ≤ 2 * M :=
    le_trans (norm_opCommutator_le_two_mul A hO) (by linarith)
  have h1_sub_norm : ‖1 - P_fail‖ ≤ 1 := isStarProjection_norm_le_one hP_fail.one_sub
  have h1_sub_C_norm : ‖(1 - P_fail) * C‖ ≤ 2 * M :=
    le_trans (norm_mul_le_of_le_one_left h1_sub_norm) hC_norm
  have h_term1 : kmsNorm ψ_eig E_eig β (P_fail * C) ≤ (2 * M) * (p_fail ^ (1 / 4 : ℝ)) := by
    have h_b := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval
      hP_fail C hp_le).2.2.1
    exact le_trans h_b (mul_le_mul_of_nonneg_right hC_norm (by positivity))
  have h_term2 : kmsNorm ψ_eig E_eig β ((1 - P_fail) * C * P_fail) ≤ (2 * M) * (p_fail ^ (1 / 4 : ℝ)) := by
    have h_b := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval
      hP_fail ((1 - P_fail) * C) hp_le).2.2.2
    exact le_trans h_b (mul_le_mul_of_nonneg_right h1_sub_C_norm (by positivity))
  have h_norm_bound : kmsNorm ψ_eig E_eig β C ≤ 4 * M * (p_fail ^ (1 / 4 : ℝ)) := by
    calc kmsNorm ψ_eig E_eig β C
      _ = kmsNorm ψ_eig E_eig β (P_fail * C + (1 - P_fail) * C * P_fail) := by rw [← h_fw.2]
      _ ≤ kmsNorm ψ_eig E_eig β (P_fail * C) + kmsNorm ψ_eig E_eig β ((1 - P_fail) * C * P_fail) :=
        kmsNorm_add_le ψ_eig E_eig β h_onb h_tr_basis _ _
      _ ≤ (2 * M) * (p_fail ^ (1 / 4 : ℝ)) + (2 * M) * (p_fail ^ (1 / 4 : ℝ)) :=
        add_le_add h_term1 h_term2
      _ = 4 * M * (p_fail ^ (1 / 4 : ℝ)) := by ring
  refine ⟨h_norm_bound, ?_⟩
  have h_sq_eq : kmsNormSq ψ_eig E_eig β C = (kmsNorm ψ_eig E_eig β C) ^ 2 :=
    (Real.sq_sqrt (kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis C)).symm
  have h_rhs_sq : (4 * M * (p_fail ^ (1 / 4 : ℝ))) ^ 2 = 16 * (M ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
    have h_rpow : (p_fail ^ (1 / 4 : ℝ)) ^ 2 = p_fail ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg]; norm_num
    calc (4 * M * (p_fail ^ (1 / 4 : ℝ))) ^ 2
      _ = 16 * (M ^ 2) * ((p_fail ^ (1 / 4 : ℝ)) ^ 2) := by ring
      _ = 16 * (M ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by rw [h_rpow]
  rw [h_sq_eq, ← h_rhs_sq]
  have h_nonneg : 0 ≤ kmsNorm ψ_eig E_eig β C := Real.sqrt_nonneg _
  have h_rhs_nonneg : 0 ≤ 4 * M * (p_fail ^ (1 / 4 : ℝ)) := by positivity
  nlinarith

/-- **Complete Fourth-Root Reduction of `kmsCoherentDrift` and `kmsDirichletForm` from Two-Sided Safe-Subspace Immunity
    (`kms_drift_dirichlet_fourth_root_from_immunity`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`))**. -/
theorem kms_drift_dirichlet_fourth_root_from_immunity {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (V : LocalPerturbation D L Site)
    (S_real F_fail : Finset (SyndromeConfig D L))
    (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_dec : SyndromeConfig D L → Bool)
    (hF_sub : F_fail ⊆ S_real)
    (h_sum_one : (∑ σ ∈ S_real, bareSyndromeProjector sys σ) = 1)
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0)
    (hL_sa : IsSelfAdjoint L_bare)
    (hL_sq : L_bare * L_bare = 1)
    (hL_comm : ∀ K ∈ boxCubes D L 2, Commute (sys.Q K) L_bare)
    {BathIdx : Type} [Fintype BathIdx]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    (V_site : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (L_jump : BoxD D L → BathIdx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {β J γ_0 p_fail : ℝ}
    (hV_tot : V.totalPerturbation = ∑ u : BoxD D L, V_site u)
    (hV_norm : ∀ u : BoxD D L, ‖V_site u‖ ≤ J)
    (hV_fw : ∀ u : BoxD D L,
      SatisfiesTwoSidedOperatorImmunity sys F_fail
        (bareDecodedLogicalOp sys S_real L_bare ψ_dec) (V_site u))
    (hL_norm : ∀ (q : BoxD D L) (α : BathIdx), ‖L_jump q α‖ ≤ γ_0)
    (hL_fw : ∀ (q : BoxD D L) (α : BathIdx),
      SatisfiesTwoSidedOperatorImmunity sys F_fail
        (bareDecodedLogicalOp sys S_real L_bare ψ_dec) (L_jump q α))
    (hp_le : hilbertTrace (gibbsDensityOp ψ_eig E_eig β * bareFailureProjector sys F_fail) ≤ p_fail) :
    let O := bareDecodedLogicalOp sys S_real L_bare ψ_dec
    kmsCoherentDrift sys V ψ_eig E_eig β O ≤
      4 * (Fintype.card (BoxD D L) : ℝ) * J * (p_fail ^ (1 / 4 : ℝ)) ∧
    kmsDirichletForm ψ_eig E_eig β L_jump O ≤
      8 * (Fintype.card (BoxD D L) : ℝ) * (Fintype.card BathIdx : ℝ) *
        (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
  intro O
  have h1 := bareDecodedLogicalOp_involution_and_commute sys V S_real L_bare ψ_dec h_sum_one h_orth hL_sa hL_sq hL_comm
  have h2 := isStarProjection_bareFailureProjector_and_compl sys S_real F_fail hF_sub h_sum_one h_orth
  have hO_norm : ‖O‖ ≤ 1 := norm_le_one_of_isSelfAdjoint_sq_eq_one h1.1 h1.2.1
  have hV_site_bound : ∀ u : BoxD D L,
      kmsNorm ψ_eig E_eig β (opCommutator (V_site u) O) ≤ 4 * J * (p_fail ^ (1 / 4 : ℝ)) :=
    fun u => (kms_safe_commutator_fourth_root_bound sys F_fail ψ_eig E_eig β
      h_onb h_tr_basis h_parseval h2.1 hO_norm (hV_fw u) (hV_norm u) hp_le).1
  have hL_jump_bound : ∀ (q : BoxD D L) (α : BathIdx),
      kmsNormSq ψ_eig E_eig β (opCommutator (L_jump q α) O) ≤
        16 * (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ)) :=
    fun q α => (kms_safe_commutator_fourth_root_bound sys F_fail ψ_eig E_eig β
      h_onb h_tr_basis h_parseval h2.1 hO_norm (hL_fw q α) (hL_norm q α) hp_le).2
  have h_comm_sum : opCommutator V.totalPerturbation O = ∑ u : BoxD D L, opCommutator (V_site u) O := by
    dsimp [opCommutator]
    rw [hV_tot, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine ⟨?_, ?_⟩
  · dsimp [kmsCoherentDrift]
    rw [h1.2.2.2.2, h_comm_sum]
    calc kmsNorm ψ_eig E_eig β (∑ u : BoxD D L, opCommutator (V_site u) O)
      _ ≤ ∑ u : BoxD D L, kmsNorm ψ_eig E_eig β (opCommutator (V_site u) O) :=
        kmsNorm_sum_le ψ_eig E_eig β h_onb h_tr_basis Finset.univ _
      _ ≤ ∑ _u : BoxD D L, 4 * J * (p_fail ^ (1 / 4 : ℝ)) :=
        Finset.sum_le_sum (fun u _ => hV_site_bound u)
      _ = 4 * (Fintype.card (BoxD D L) : ℝ) * J * (p_fail ^ (1 / 4 : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  · dsimp [kmsDirichletForm]
    have h_sum_le :
        (∑ q : BoxD D L, ∑ α : BathIdx,
          kmsNormSq ψ_eig E_eig β (opCommutator (L_jump q α) O)) ≤
        ∑ _q : BoxD D L, ∑ _α : BathIdx,
          16 * (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun q _ => Finset.sum_le_sum (fun α _ => hL_jump_bound q α))
    calc (1 / 2 : ℝ) * ∑ q : BoxD D L, ∑ α : BathIdx,
          kmsNormSq ψ_eig E_eig β (opCommutator (L_jump q α) O)
      _ ≤ (1 / 2 : ℝ) * ∑ _q : BoxD D L, ∑ _α : BathIdx,
          16 * (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h_sum_le (by norm_num)
      _ = 8 * (Fintype.card (BoxD D L) : ℝ) * (Fintype.card BathIdx : ℝ) *
          (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          nsmul_eq_mul, nsmul_eq_mul]
        ring

/-- **Complete Fourth-Root Reduction of `kmsCoherentDrift` and `kmsDirichletForm` from Local Coboundary Discrepancy Invariance
    (`kms_drift_dirichlet_fourth_root_from_discrepancy`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`))**. -/
theorem kms_drift_dirichlet_fourth_root_from_discrepancy {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (V : LocalPerturbation D L Site)
    (S_real F_fail : Finset (SyndromeConfig D L))
    (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_dec : SyndromeConfig D L → Bool)
    (hF_sub : F_fail ⊆ S_real)
    (h_sum_one : (∑ σ ∈ S_real, bareSyndromeProjector sys σ) = 1)
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0)
    (hL_sa : IsSelfAdjoint L_bare)
    (hL_sq : L_bare * L_bare = 1)
    (hL_comm : ∀ K ∈ boxCubes D L 2, Commute (sys.Q K) L_bare)
    {BathIdx : Type} [Fintype BathIdx]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂ : ManyBodyConfig Site,
      inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_tr_basis : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω))))
    (h_parseval : ∀ φ : ManyBodyHilbertSpace Site,
      (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2)
    (V_site : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (L_jump : BoxD D L → BathIdx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {β J γ_0 p_fail : ℝ}
    (hV_tot : V.totalPerturbation = ∑ u : BoxD D L, V_site u)
    (hV_norm : ∀ u : BoxD D L, ‖V_site u‖ ≤ J)
    (hV_disc : ∀ u : BoxD D L,
      PreservesDecoderDiscrepancy sys S_real F_fail L_bare ψ_dec (V_site u))
    (hL_norm : ∀ (q : BoxD D L) (α : BathIdx), ‖L_jump q α‖ ≤ γ_0)
    (hL_disc : ∀ (q : BoxD D L) (α : BathIdx),
      PreservesDecoderDiscrepancy sys S_real F_fail L_bare ψ_dec (L_jump q α))
    (hp_le : hilbertTrace (gibbsDensityOp ψ_eig E_eig β * bareFailureProjector sys F_fail) ≤ p_fail) :
    let O := bareDecodedLogicalOp sys S_real L_bare ψ_dec
    (∀ u : BoxD D L, SatisfiesTwoSidedOperatorImmunity sys F_fail O (V_site u)) ∧
    (∀ (q : BoxD D L) (α : BathIdx), SatisfiesTwoSidedOperatorImmunity sys F_fail O (L_jump q α)) ∧
    kmsCoherentDrift sys V ψ_eig E_eig β O ≤
      4 * (Fintype.card (BoxD D L) : ℝ) * J * (p_fail ^ (1 / 4 : ℝ)) ∧
    kmsDirichletForm ψ_eig E_eig β L_jump O ≤
      8 * (Fintype.card (BoxD D L) : ℝ) * (Fintype.card BathIdx : ℝ) *
        (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
  intro O
  have hV_fw : ∀ u : BoxD D L,
      SatisfiesTwoSidedOperatorImmunity sys F_fail O (V_site u) :=
    fun u => satisfiesTwoSidedOperatorImmunity_of_preservesDecoderDiscrepancy sys S_real F_fail
      L_bare ψ_dec hF_sub h_sum_one h_orth hL_comm (hV_disc u)
  have hL_fw : ∀ (q : BoxD D L) (α : BathIdx),
      SatisfiesTwoSidedOperatorImmunity sys F_fail O (L_jump q α) :=
    fun q α => satisfiesTwoSidedOperatorImmunity_of_preservesDecoderDiscrepancy sys S_real F_fail
      L_bare ψ_dec hF_sub h_sum_one h_orth hL_comm (hL_disc q α)
  have h_bounds := kms_drift_dirichlet_fourth_root_from_immunity sys V S_real F_fail L_bare ψ_dec
    hF_sub h_sum_one h_orth hL_sa hL_sq hL_comm ψ_eig E_eig h_onb h_tr_basis h_parseval
    V_site L_jump hV_tot hV_norm hV_fw hL_norm hL_fw hp_le
  exact ⟨hV_fw, hL_fw, h_bounds.1, h_bounds.2⟩

/-- **Two-Sided Safe-Subspace Immunity and Fourth-Root KMS Reduction (`two_sided_operator_safe_immunity`; Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`))**. -/
theorem two_sided_operator_safe_immunity
    (D : ℕ) :
    ∀ (L : ℕ) [NeZero L]
      (Site : BoxD D L → Type)
      [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
      (sys : CommutingProjectorHamiltonian D L Site)
      (V : LocalPerturbation D L Site)
      (S_real F_fail : Finset (SyndromeConfig D L))
      (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
      (ψ_dec : SyndromeConfig D L → Bool),
      F_fail ⊆ S_real →
      (∑ σ ∈ S_real, bareSyndromeProjector sys σ) = 1 →
      (∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
        bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0) →
      IsSelfAdjoint L_bare →
      L_bare * L_bare = 1 →
      (∀ K ∈ boxCubes D L 2, Commute (sys.Q K) L_bare) →
      let O := bareDecodedLogicalOp sys S_real L_bare ψ_dec
      let P_fail := bareFailureProjector sys F_fail
      (IsSelfAdjoint O ∧
       O * O = 1 ∧
       (∀ K ∈ boxCubes D L 2, Commute (sys.Q K) O) ∧
       opCommutator sys.H0 O = 0 ∧
       opCommutator (sys.H0 + V.totalPerturbation) O = opCommutator V.totalPerturbation O) ∧
      (IsStarProjection P_fail ∧
       IsStarProjection (1 - P_fail) ∧
       1 - P_fail = ∑ σ ∈ S_real \ F_fail, bareSyndromeProjector sys σ) ∧
      (∀ (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (b_L : Bool),
        L_bare * A = ((if b_L then (-1 : ℂ) else (1 : ℂ)) • A) * L_bare →
        (∀ σ₁ ∈ S_real \ F_fail, ∀ σ₂ ∈ S_real \ F_fail,
          bareSyndromeProjector sys σ₁ * A * bareSyndromeProjector sys σ₂ = 0 ∨
          Bool.xor (ψ_dec σ₁) (ψ_dec σ₂) = b_L) →
        (∀ σ₁ ∈ S_real \ F_fail, ∀ σ₂ ∈ S_real \ F_fail,
          bareSyndromeProjector sys σ₁ * opCommutator A O * bareSyndromeProjector sys σ₂ = 0) ∧
        SatisfiesTwoSidedOperatorImmunity sys F_fail O A) ∧
      (∀ (BathIdx : Type) [Fintype BathIdx]
        (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
        (E_eig : ManyBodyConfig Site → ℝ)
        (V_site : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
        (L_jump : BoxD D L → BathIdx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
        (β J γ_0 p_fail : ℝ),
        (∀ ω₁ ω₂ : ManyBodyConfig Site,
          inner ℂ (ψ_eig ω₁) (ψ_eig ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0) →
        (∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
          hilbertTrace X = ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_eig ω) (X (ψ_eig ω)))) →
        (∀ φ : ManyBodyHilbertSpace Site,
          (∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) φ‖ ^ 2) = ‖φ‖ ^ 2) →
        V.totalPerturbation = ∑ u : BoxD D L, V_site u →
        (∀ u : BoxD D L, ‖V_site u‖ ≤ J) →
        (∀ u : BoxD D L, PreservesDecoderDiscrepancy sys S_real F_fail L_bare ψ_dec (V_site u)) →
        (∀ (q : BoxD D L) (α : BathIdx), ‖L_jump q α‖ ≤ γ_0) →
        (∀ (q : BoxD D L) (α : BathIdx),
          PreservesDecoderDiscrepancy sys S_real F_fail L_bare ψ_dec (L_jump q α)) →
        hilbertTrace (gibbsDensityOp ψ_eig E_eig β * P_fail) ≤ p_fail →
        (∀ u : BoxD D L, SatisfiesTwoSidedOperatorImmunity sys F_fail O (V_site u)) ∧
        (∀ (q : BoxD D L) (α : BathIdx),
          SatisfiesTwoSidedOperatorImmunity sys F_fail O (L_jump q α)) ∧
        (∀ K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
          kmsNorm ψ_eig E_eig β (P_fail * K) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) ∧
          kmsNorm ψ_eig E_eig β (K * P_fail) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ))) ∧
        (∀ u : BoxD D L,
          kmsNorm ψ_eig E_eig β (opCommutator (V_site u) O) ≤ 4 * J * (p_fail ^ (1 / 4 : ℝ))) ∧
        (∀ (q : BoxD D L) (α : BathIdx),
          kmsNormSq ψ_eig E_eig β (opCommutator (L_jump q α) O) ≤
            16 * (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ))) ∧
        kmsCoherentDrift sys V ψ_eig E_eig β O ≤
          4 * (Fintype.card (BoxD D L) : ℝ) * J * (p_fail ^ (1 / 4 : ℝ)) ∧
        kmsDirichletForm ψ_eig E_eig β L_jump O ≤
          8 * (Fintype.card (BoxD D L) : ℝ) * (Fintype.card BathIdx : ℝ) *
            (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ))) := by
  intro L _ Site _ _ _ sys V S_real F_fail L_bare ψ_dec
    hF_sub h_sum_one h_orth hL_sa hL_sq hL_comm O P_fail
  have h1 := bareDecodedLogicalOp_involution_and_commute sys V S_real L_bare ψ_dec h_sum_one h_orth hL_sa hL_sq hL_comm
  have h2 := isStarProjection_bareFailureProjector_and_compl sys S_real F_fail hF_sub h_sum_one h_orth
  refine ⟨h1, h2, ?_, ?_⟩
  · intro A b_L hA_comm hA_discrep
    exact safe_sector_commutator_zero_of_commute_checks sys S_real F_fail L_bare ψ_dec
      hF_sub h_sum_one h_orth hL_comm A b_L hA_comm hA_discrep
  · intro BathIdx _ ψ_eig E_eig V_site L_jump β J γ_0 p_fail
      h_onb h_tr_basis h_parseval hV_tot hV_norm hV_disc hL_norm hL_disc hp_le
    have hO_norm : ‖O‖ ≤ 1 := norm_le_one_of_isSelfAdjoint_sq_eq_one h1.1 h1.2.1
    have h_disc_bounds := kms_drift_dirichlet_fourth_root_from_discrepancy sys V S_real F_fail
      L_bare ψ_dec hF_sub h_sum_one h_orth hL_sa hL_sq hL_comm ψ_eig E_eig h_onb h_tr_basis
      h_parseval V_site L_jump hV_tot hV_norm hV_disc hL_norm hL_disc hp_le
    have h_proj_K : ∀ K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        kmsNorm ψ_eig E_eig β (P_fail * K) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) ∧
        kmsNorm ψ_eig E_eig β (K * P_fail) ≤ ‖K‖ * (p_fail ^ (1 / 4 : ℝ)) := by
      intro K
      have h_b := kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr_basis h_parseval
        h2.1 K hp_le
      exact ⟨h_b.2.2.1, h_b.2.2.2⟩
    have hV_site_bound : ∀ u : BoxD D L,
        kmsNorm ψ_eig E_eig β (opCommutator (V_site u) O) ≤ 4 * J * (p_fail ^ (1 / 4 : ℝ)) :=
      fun u => (kms_safe_commutator_fourth_root_bound sys F_fail ψ_eig E_eig β
        h_onb h_tr_basis h_parseval h2.1 hO_norm (h_disc_bounds.1 u) (hV_norm u) hp_le).1
    have hL_jump_bound : ∀ (q : BoxD D L) (α : BathIdx),
        kmsNormSq ψ_eig E_eig β (opCommutator (L_jump q α) O) ≤
          16 * (γ_0 ^ 2) * (p_fail ^ (1 / 2 : ℝ)) :=
      fun q α => (kms_safe_commutator_fourth_root_bound sys F_fail ψ_eig E_eig β
        h_onb h_tr_basis h_parseval h2.1 hO_norm (h_disc_bounds.2.1 q α) (hL_norm q α) hp_le).2
    exact ⟨h_disc_bounds.1, h_disc_bounds.2.1, h_proj_K, hV_site_bound, hL_jump_bound,
      h_disc_bounds.2.2.1, h_disc_bounds.2.2.2⟩

end
