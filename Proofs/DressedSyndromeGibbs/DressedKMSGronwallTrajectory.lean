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

import Proofs.DressedSyndromeGibbs.DressedKMSDriftAndDirichlet

/-!
# KMS Drift-Dirichlet Grönwall Inequality and Dressed-Unitary Memory Trajectory Bounds

Introduces the abstract KMS decay-rate predicate (`HasKMSDecayRate`) and integrates the nonlinear drift-Dirichlet differential inequality to obtain `opKMSNorm_le_kmsDriftDirichletBound_of_hasKMSDecayRate`. Specializes this Grönwall bound to QAC-dressed logical observables with exponential thermal barriers to establish `dressed_unitary_kms_trajectory_bound_of_exp_barrier`.

## References

* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.5 (`thm:main-D`)
* Part II, Section 6.2 (`subsec:kms-gronwall`), Theorem 6.2 (`thm:kms-gronwall-bare`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs

set_option maxRecDepth 200000
set_option linter.unusedVariables false

/-! ## 1. Bundled `HasKMSDecayRate` Predicate & Grönwall Trajectory Integration -/

/-- **Bundled Coherent + Dissipative KMS Decay Rate (`HasKMSDecayRate`)**:
Captures the non-negative coherent drift rate `Γ_coh` and KMS Dirichlet dissipation rate `Γ_diss`
controlling the KMS-Lindblad generator of `O_dress`. -/
structure HasKMSDecayRate {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (bath : Finset (BathChannel D L Site))
    (O_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (Γ_coh Γ_diss : ℝ) : Prop where
  hΓ_coh_nn : 0 ≤ Γ_coh
  hΓ_diss_nn : 0 ≤ Γ_diss
  h_bath_γ : ∀ ch ∈ bath, 0 ≤ ch.γ
  h_coh_bound : opKMSNorm H hH β (H * O_dress - O_dress * H) ≤ Γ_coh
  h_dirichlet_bound :
    (1 / 2 : ℝ) * (∑ ch ∈ bath, ch.γ * opKMSNormSq H hH β (opCommutator ch.L O_dress)) ≤ Γ_diss

/-- **Grönwall ODE Integration from `HasKMSDecayRate`
(`opKMSNorm_le_kmsDriftDirichletBound_of_hasKMSDecayRate`)**:
Integrates `SatisfiesKMSLindbladODE H hH β bath O_dress O_t t` whenever `O_dress` is self-adjoint
and satisfies `HasKMSDecayRate H hH β bath O_dress Γ_coh Γ_diss`. -/
theorem opKMSNorm_le_kmsDriftDirichletBound_of_hasKMSDecayRate {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (bath : Finset (BathChannel D L Site))
    (O_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dress)
    {Γ_coh Γ_diss : ℝ}
    (h_rate : HasKMSDecayRate H hH β bath O_dress Γ_coh Γ_diss)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) (ht : 0 ≤ t)
    (h_ode : SatisfiesKMSLindbladODE H hH β bath O_dress O_t t) :
    opKMSNorm H hH β (O_t t - O_dress) ≤ kmsDriftDirichletBound Γ_coh Γ_diss t := by
  rcases h_rate with ⟨hΓ_coh_nn, hΓ_diss_nn, h_bath_γ, h_coh_bound_op, h_dirichlet⟩
  have h_onb := opEigenbasis_orthonormal H hH
  have h_tr_basis := hilbertTrace_eq_sum_opEigenbasis H hH
  have h_eig := opEigenbasis_ketBra_props H hH
  set ψ_eig := opEigenbasis H hH
  set E_eig := opEigenvalues H hH
  rcases h_ode with ⟨hO0, hOs_sa, f', hf_deriv, h_gen⟩
  have hf0 : opKMSNormSq H hH β (O_t 0 - O_dress) ≤ 0 := by
    change kmsNormSq ψ_eig E_eig β (O_t 0 - O_dress) ≤ 0
    rw [hO0, sub_self, kmsNormSq_eq_spectral_sum ψ_eig E_eig β h_onb h_tr_basis 0]
    simp
  have hf_nonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ opKMSNormSq H hH β (O_t s - O_dress) :=
    fun s _ => kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr_basis (O_t s - O_dress)
  have hf_ineq : ∀ s ∈ Set.Icc 0 t,
      f' s ≤ 2 * Γ_coh * Real.sqrt (opKMSNormSq H hH β (O_t s - O_dress)) +
        (1 / 2 : ℝ) * Γ_diss := by
    intro s hs
    have hΔ_sa : IsSelfAdjoint (O_t s - O_dress) := by
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
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dress) (Complex.I • opCommutator H (O_t s)) =
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dress) (Complex.I • opCommutator H O_dress) := by
      rw [opCommutator_sub_add_cancel H (O_t s) O_dress, kmsInnerReal_add_right,
        kmsInnerReal_commutator_eq_zero H ψ_eig E_eig β h_eig (O_t s - O_dress) hΔ_sa, zero_add]
    have h_coh_bound :
        kmsInnerReal ψ_eig E_eig β (O_t s - O_dress) (Complex.I • opCommutator H O_dress) ≤
        Γ_coh * Real.sqrt (opKMSNormSq H hH β (O_t s - O_dress)) := by
      have h_cs := kmsInnerReal_le_kmsNorm_mul_kmsNorm ψ_eig E_eig β h_onb h_tr_basis
        (O_t s - O_dress) (Complex.I • opCommutator H O_dress)
      rw [kmsNorm_I_smul] at h_cs
      change kmsNorm ψ_eig E_eig β (opCommutator H O_dress) ≤ Γ_coh at h_coh_bound_op
      have h_norm_nn : 0 ≤ kmsNorm ψ_eig E_eig β (O_t s - O_dress) := Real.sqrt_nonneg _
      change kmsInnerReal ψ_eig E_eig β (O_t s - O_dress) (Complex.I • opCommutator H O_dress) ≤
        Γ_coh * kmsNorm ψ_eig E_eig β (O_t s - O_dress)
      nlinarith
    have h_diss_bound :
        -(1 / 2 : ℝ) * (∑ ch ∈ bath, kmsInnerReal ψ_eig E_eig β (O_t s - O_dress)
          ((ch.γ : ℂ) • kmsInvSandwich ψ_eig E_eig β
            (opCommutator (ch.L†) (kmsSandwich ψ_eig E_eig β (opCommutator ch.L (O_t s)))))) ≤
        (1 / 4 : ℝ) * Γ_diss := by
      rw [Finset.mul_sum]
      have h_sum_le :
          (∑ ch ∈ bath, -(1 / 2 : ℝ) * kmsInnerReal ψ_eig E_eig β (O_t s - O_dress)
            ((ch.γ : ℂ) • kmsInvSandwich ψ_eig E_eig β
              (opCommutator (ch.L†) (kmsSandwich ψ_eig E_eig β (opCommutator ch.L (O_t s)))))) ≤
          ∑ ch ∈ bath, (1 / 4 : ℝ) * (ch.γ * ((1 / 2 : ℝ) * opKMSNormSq H hH β (opCommutator ch.L O_dress))) := by
        refine Finset.sum_le_sum fun ch hch => ?_
        rw [h_smul_right]
        exact kmsInnerReal_channel_dissipator_sub_le_quarter_opKMSNormSq
          H hH β O_dress (O_t s) ch (h_bath_γ ch hch)
      have h_rhs_eq :
          (∑ ch ∈ bath, (1 / 4 : ℝ) * (ch.γ * ((1 / 2 : ℝ) * opKMSNormSq H hH β (opCommutator ch.L O_dress)))) =
          (1 / 4 : ℝ) * ((1 / 2 : ℝ) * (∑ ch ∈ bath, ch.γ * opKMSNormSq H hH β (opCommutator ch.L O_dress))) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ch _ => by ring
      linarith
    linarith
  have h_gron := kms_gronwall_ode_integral_bound hΓ_coh_nn hΓ_diss_nn ht hf0 hf_nonneg hf_deriv
    hf_ineq t ⟨ht, le_refl t⟩
  exact h_gron

/-! ## 2. `HasKMSDecayRate` and Trajectory Bounds under Pinched Residual $\delta_{\mathrm{split}}$ -/

/-- **Establishing `HasKMSDecayRate` from Pinched Safe-Subspace Commutator Bounds
(`hasKMSDecayRate_of_pinched_commutator_bounds`)**:
Constructs `HasKMSDecayRate` with
- $\Gamma_{\mathrm{coh}} = 2 \|H O_{\mathrm{dress}} - O_{\mathrm{dress}} H\| \, p_{\mathrm{fail}}^{1/4} + \delta_{\mathrm{split}}$,
- $\Gamma_{\mathrm{diss}} = \bigl(\sum_{\mathrm{ch} \in \mathrm{bath}} \gamma_{\mathrm{ch}} \|L_{\mathrm{ch}}\|^2\bigr) \bigl(16 \, p_{\mathrm{fail}}^{1/2} + \delta_{\mathrm{split}}\bigr)$,
via the KMS fourth-root commutator bounds (Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`)). -/
theorem hasKMSDecayRate_of_pinched_commutator_bounds {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (bath : Finset (BathChannel D L Site))
    (O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_norm : ‖O_dress‖ ≤ 1)
    (hPi : IsStarProjection Pi_dress)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (h_pinch_coh : ‖Pi_dress * (H * O_dress - O_dress * H) * Pi_dress‖ ≤ δ_split)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split) :
    HasKMSDecayRate H hH β bath O_dress
      (2 * ‖H * O_dress - O_dress * H‖ * (p_fail ^ (1 / 4 : ℝ)) + δ_split)
      ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split)) := by
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (gibbsFailureProb_one_sub_nonneg H hH β hPi) hp_le
  have hδ_nn : 0 ≤ δ_split :=
    le_trans (norm_nonneg _) h_pinch_coh
  have hp_rpow4 : 0 ≤ p_fail ^ (1 / 4 : ℝ) := Real.rpow_nonneg hp_nonneg _
  have hp_rpow2 : 0 ≤ p_fail ^ (1 / 2 : ℝ) := Real.rpow_nonneg hp_nonneg _
  have hΓ_coh_nn : 0 ≤ 2 * ‖H * O_dress - O_dress * H‖ * (p_fail ^ (1 / 4 : ℝ)) + δ_split :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) hp_rpow4) hδ_nn
  have hΓ_diss_nn :
      0 ≤ (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split) := by
    refine mul_nonneg (Finset.sum_nonneg fun ch hch => ?_)
      (add_nonneg (mul_nonneg (by norm_num) hp_rpow2) hδ_nn)
    exact mul_nonneg (h_bath ch hch).1 (sq_nonneg _)
  have h_coh := opKMSNorm_commutator_le_of_pinched_le
    H hH β O_dress Pi_dress hPi (p_fail := p_fail) (δ_split := δ_split) hp_le h_pinch_coh
  have h_dir := sum_bath_half_opKMSNormSq_le_of_pinched_sq_le
    H hH β bath O_dress Pi_dress hO_norm hPi (p_fail := p_fail) (δ_split := δ_split) hp_le h_bath
  exact ⟨hΓ_coh_nn, hΓ_diss_nn, fun ch hch => (h_bath ch hch).1, h_coh, h_dir⟩

/-- **KMS Trajectory Drift-Plus-Dirichlet Bound under Pinched Residual $\delta_{\mathrm{split}}$
(`opKMSNorm_le_kmsDriftDirichletBound_of_pinched_commutator_bounds`)**:
For any self-adjoint `O_dress` with `‖O_dress‖ ≤ 1` and star-projection `Pi_dress` satisfying
`gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail`,
`‖Pi_dress * (H * O_dress - O_dress * H) * Pi_dress‖ ≤ δ_split`, and
`∀ ch ∈ bath, 0 ≤ ch.γ ∧ ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split`,
any trajectory `SatisfiesKMSLindbladODE H hH β bath O_dress O_t t` ($t \ge 0$) obeys:
$$\|O_t - O_{\mathrm{dress}}\|_{\mathrm{KMS}, H} \le
  \mathrm{kmsDriftDirichletBound}\Bigl(
    2 \|H O_{\mathrm{dress}} - O_{\mathrm{dress}} H\| \, p_{\mathrm{fail}}^{1/4} + \delta_{\mathrm{split}},\;
    \Bigl(\sum_{\mathrm{ch} \in \mathrm{bath}} \gamma_{\mathrm{ch}} \|L_{\mathrm{ch}}\|^2\Bigr)
      \bigl(16 \, p_{\mathrm{fail}}^{1/2} + \delta_{\mathrm{split}}\bigr),\;
    t\Bigr).$$ -/
theorem opKMSNorm_le_kmsDriftDirichletBound_of_pinched_commutator_bounds {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (bath : Finset (BathChannel D L Site))
    (O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dress) (hO_norm : ‖O_dress‖ ≤ 1)
    (hPi : IsStarProjection Pi_dress)
    {p_fail δ_split : ℝ}
    (hp_le : gibbsFailureProb H hH β (1 - Pi_dress) ≤ p_fail)
    (h_pinch_coh : ‖Pi_dress * (H * O_dress - O_dress * H) * Pi_dress‖ ≤ δ_split)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) (ht : 0 ≤ t)
    (h_ode : SatisfiesKMSLindbladODE H hH β bath O_dress O_t t) :
    opKMSNorm H hH β (O_t t - O_dress) ≤
      kmsDriftDirichletBound
        (2 * ‖H * O_dress - O_dress * H‖ * (p_fail ^ (1 / 4 : ℝ)) + δ_split)
        ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_fail ^ (1 / 2 : ℝ)) + δ_split))
        t := by
  have h_rate := hasKMSDecayRate_of_pinched_commutator_bounds
    H hH β bath O_dress Pi_dress hO_norm hPi (p_fail := p_fail) (δ_split := δ_split)
    hp_le h_pinch_coh h_bath
  have h_res := opKMSNorm_le_kmsDriftDirichletBound_of_hasKMSDecayRate
    H hH β bath O_dress hO_sa h_rate O_t t ht h_ode
  exact h_res

/-! ## 3. Exponential Free-Energy Barrier & Unitary-Dressed Specializations -/

/-- **Exponential Free-Energy Barrier KMS Trajectory Bound with Residual $\delta_{\mathrm{split}}$
(`opKMSNorm_le_kmsDriftDirichletBound_of_exp_barrier_and_pinched_bounds`)**:
Specializes `opKMSNorm_le_kmsDriftDirichletBound_of_pinched_commutator_bounds` to an exponential
Gibbs failure probability barrier `gibbsFailureProb H hH β (1 - Pi_dress) ≤ Real.exp (- ΔF_pert)`. -/
theorem opKMSNorm_le_kmsDriftDirichletBound_of_exp_barrier_and_pinched_bounds {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (β : ℝ) (bath : Finset (BathChannel D L Site))
    (O_dress Pi_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dress) (hO_norm : ‖O_dress‖ ≤ 1)
    (hPi : IsStarProjection Pi_dress)
    {ΔF_pert δ_split : ℝ}
    (hp_exp : gibbsFailureProb H hH β (1 - Pi_dress) ≤ Real.exp (- ΔF_pert))
    (h_pinch_coh : ‖Pi_dress * (H * O_dress - O_dress * H) * Pi_dress‖ ≤ δ_split)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      ‖Pi_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_dress‖ ^ 2 ≤ ‖ch.L‖ ^ 2 * δ_split)
    (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (t : ℝ) (ht : 0 ≤ t)
    (h_ode : SatisfiesKMSLindbladODE H hH β bath O_dress O_t t) :
    opKMSNorm H hH β (O_t t - O_dress) ≤
      kmsDriftDirichletBound
        (2 * ‖H * O_dress - O_dress * H‖ * ((Real.exp (- ΔF_pert)) ^ (1 / 4 : ℝ)) + δ_split)
        ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) *
          (16 * ((Real.exp (- ΔF_pert)) ^ (1 / 2 : ℝ)) + δ_split))
        t := by
  have h_res := opKMSNorm_le_kmsDriftDirichletBound_of_pinched_commutator_bounds
    H hH β bath O_dress Pi_dress hO_sa hO_norm hPi
    (p_fail := Real.exp (- ΔF_pert)) (δ_split := δ_split)
    hp_exp h_pinch_coh h_bath O_t t ht h_ode
  exact h_res

/-- **Unitary-Dressed KMS Trajectory Bound under Exact Bath Safe-Subspace Commutation
(`dressed_unitary_kms_trajectory_bound_of_exp_barrier`)**:
For `Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†` and
`O_dec_dress := U_dress.1 * O_dec * U_dress.1†`, if the bath channels satisfy exact dressed
safe-subspace commutation
`∀ ch ∈ bath, 0 ≤ ch.γ ∧ Pi_safe_dress * (ch.L * O_dec_dress - O_dec_dress * ch.L) * Pi_safe_dress = 0`,
and `gibbsFailureProb (sys.H0 + V.V_tot) hH_pert β (1 - Pi_safe_dress) ≤ Real.exp (- ΔF_pert)`,
then both the exact zero-bath-residual trajectory bound (with the
explicit pinched commutator norm `‖Pi_safe_dress * [H, O_dec_dress] * Pi_safe_dress‖` and
zero bath residual) AND the `δ_split`-residual trajectory bound (for any `δ_split` with
`‖Pi_safe_dress * [H, O_dec_dress] * Pi_safe_dress‖ ≤ δ_split`) hold simultaneously. -/
theorem dressed_unitary_kms_trajectory_bound_of_exp_barrier
    {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (β : ℝ)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_sq : O_dec * O_dec = 1)
    (h_comm_H0 : Commute sys.H0 O_dec)
    (hPi : IsStarProjection Pi_safe)
    (h_bath_dress : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      (U_dress.1 * Pi_safe * U_dress.1†) *
        (ch.L * (U_dress.1 * O_dec * U_dress.1†) - (U_dress.1 * O_dec * U_dress.1†) * ch.L) *
        (U_dress.1 * Pi_safe * U_dress.1†) = 0)
    {ΔF_pert : ℝ}
    (hp_exp :
      gibbsFailureProb (sys.H0 + V.totalPerturbation) hH_pert β
        (1 - (U_dress.1 * Pi_safe * U_dress.1†)) ≤ Real.exp (- ΔF_pert)) :
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    let O_dec_dress := U_dress.1 * O_dec * U_dress.1†
    let C_coh_dress := (sys.H0 + V.totalPerturbation) * O_dec_dress - O_dec_dress * (sys.H0 + V.totalPerturbation)
    (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
      0 ≤ t →
      SatisfiesKMSLindbladODE (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec_dress O_t t →
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (O_t t - O_dec_dress) ≤
        kmsDriftDirichletBound
          (‖Pi_safe_dress * C_coh_dress * Pi_safe_dress‖ +
            2 * ‖C_coh_dress‖ * (Real.exp (- ΔF_pert) ^ (1 / 4 : ℝ)))
          (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) *
            (Real.exp (- ΔF_pert) ^ (1 / 2 : ℝ)))
          t) ∧
    (∀ (δ_split : ℝ),
      ‖Pi_safe_dress * C_coh_dress * Pi_safe_dress‖ ≤ δ_split →
      ∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
        0 ≤ t →
        SatisfiesKMSLindbladODE (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec_dress O_t t →
        opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (O_t t - O_dec_dress) ≤
          kmsDriftDirichletBound
            (2 * ‖C_coh_dress‖ * (Real.exp (- ΔF_pert) ^ (1 / 4 : ℝ)) + δ_split)
            ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) *
              (16 * (Real.exp (- ΔF_pert) ^ (1 / 2 : ℝ)) + δ_split))
            t) := by
  intro Pi_safe_dress O_dec_dress C_coh_dress
  have h_main := indexed_dressed_perturbed_kms_memory_lifetime_and_drift_bound
    sys V hH_pert β U_dress bath O_dec Pi_safe hO_sa hO_sq h_comm_H0 hPi h_bath_dress hp_exp
  refine ⟨h_main.2.2.2.2.2.2.2, fun δ_split h_pinch_coh O_t t ht h_ode => ?_⟩
  have hPi_dress : IsStarProjection Pi_safe_dress := h_main.1
  have hO_dress_sa : IsSelfAdjoint O_dec_dress := h_main.2.1
  have hO_dress_norm : ‖O_dec_dress‖ ≤ 1 := h_main.2.2.2.1
  have hδ_nn : 0 ≤ δ_split := le_trans (norm_nonneg _) h_pinch_coh
  have h_bath_sq : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      ‖Pi_safe_dress * (ch.L * O_dec_dress - O_dec_dress * ch.L) * Pi_safe_dress‖ ^ 2 ≤
        ‖ch.L‖ ^ 2 * δ_split := fun ch hch =>
    ⟨(h_bath_dress ch hch).1,
     pinched_sq_le_of_pinched_eq_zero ch.L O_dec_dress Pi_safe_dress hδ_nn (h_bath_dress ch hch).2⟩
  have h_res := opKMSNorm_le_kmsDriftDirichletBound_of_exp_barrier_and_pinched_bounds
    (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec_dress Pi_safe_dress
    hO_dress_sa hO_dress_norm hPi_dress (ΔF_pert := ΔF_pert) (δ_split := δ_split)
    hp_exp h_pinch_coh h_bath_sq O_t t ht h_ode
  exact h_res

end
