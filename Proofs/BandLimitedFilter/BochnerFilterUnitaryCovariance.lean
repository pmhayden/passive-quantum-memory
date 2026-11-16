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

import Defs.FlowAndFilter
import Proofs.BandLimitedFilter.BandLimitedWeightIntegrals
import Proofs.BandLimitedFilter.BandLimitedFourierMoments
import Proofs.LiebRobinson.BochnerQuasiLocality
import Proofs.LiebRobinson.DuhamelAndGronwall
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.BandLimitedFilter.EigenprojEvolutionAndBlockDecomp
import Proofs.LiebRobinson.SuperpolyDecayClosure
import Proofs.BandLimitedFilter.BochnerFilterSelfAdjointness
import Proofs.BandLimitedFilter.BochnerFilteredSiteLinearity
import Proofs.LiebRobinson.LiebRobinsonSeries

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Bochner Filter Unitary Covariance and Three-Term Site Splitting

Establishes unitary conjugation covariance of `bochnerFilteredOp`, the bare-frame three-term algebraic decomposition of `bochnerFilteredSiteOp`, and explicit first-moment bounds for `bhFilterWeight`. Combines bare Bochner conditional expectation bounds with unitary conjugation light-cone tails to control quasi-local filtered site operators.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (79) (`eq:Xu-bare-three-term`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

/-!
## 1. Unitary Submonoid Conjugation Helpers & Unitary Covariance of `bochnerFilteredOp`
-/

/-- For `U : unitary (E →L[ℂ] E)`, both `U.1 * U.1† = 1` and `U.1† * U.1 = 1` hold. -/
lemma unitary_mul_adj_and_adj_mul_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : unitary (E →L[ℂ] E)) :
    U.1 * (U.1†) = 1 ∧ (U.1†) * U.1 = 1 :=
  ⟨Unitary.coe_mul_star_self U, Unitary.coe_star_mul_self U⟩

/-- Both `‖U.1‖ ≤ 1` and `‖U.1†‖ ≤ 1` hold for any `U : unitary (E →L[ℂ] E)`. -/
lemma norm_unitary_and_adj_le_one_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : unitary (E →L[ℂ] E)) :
    ‖U.1‖ ≤ 1 ∧ ‖U.1†‖ ≤ 1 :=
  norm_le_one_of_adjoint_mul_self_eq_one (Unitary.coe_star_mul_self U)

/-- Unitary conjugation `U.1† * X * U.1` is norm-contractive: `‖U.1† * X * U.1‖ ≤ ‖X‖`. -/
lemma norm_unitary_adj_conj_le_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (X : E →L[ℂ] E) :
    ‖(U.1†) * X * U.1‖ ≤ ‖X‖ := by
  rcases norm_unitary_and_adj_le_one_clm U with ⟨hU, hU_adj⟩
  calc ‖(U.1†) * X * U.1‖
    _ ≤ ‖(U.1†) * X‖ * ‖U.1‖ := norm_mul_le _ _
    _ ≤ (‖U.1†‖ * ‖X‖) * ‖U.1‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hU_adj (norm_nonneg X)) hU
        (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg X))
    _ = ‖X‖ := by ring

/-- If `H` is self-adjoint, then `U.1† * H * U.1` is self-adjoint. -/
lemma isSelfAdjoint_unitary_adj_conj_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (U : unitary (E →L[ℂ] E)) :
    IsSelfAdjoint ((U.1†) * H * U.1) :=
  isSelfAdjoint_conj_adjoint hH U.1

/-- Norm preservation of `heisenbergFlow H t X` for self-adjoint `H`: `‖heisenbergFlow H t X‖ ≤ ‖X‖`. -/
lemma norm_heisenbergFlow_le_self {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    (t : ℝ) (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖heisenbergFlow H t X‖ ≤ ‖X‖ := by
  have hU_le : ∀ u : ℝ, ‖timeEvolutionOp H u‖ ≤ 1 := by
    intro u
    let x := (Complex.I * (u : ℂ)) • H
    have h_star_x : star x = -x := by
      dsimp [x]
      rw [star_smul, hH.star_eq, star_mul', RCLike.star_def,
        Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_smul (Complex.I * (u : ℂ)) H]
    have h_adj : (NormedSpace.exp x)† * NormedSpace.exp x = 1 := by
      change star (NormedSpace.exp x) * NormedSpace.exp x = 1
      rw [NormedSpace.star_exp, h_star_x,
        ← clm_exp_add_of_commute (Commute.refl x).neg_left,
        neg_add_cancel, NormedSpace.exp_zero]
    have h_sq : ‖timeEvolutionOp H u‖ ^ 2 ≤ 1 := by
      change ‖NormedSpace.exp x‖ ^ 2 ≤ 1
      rw [sq, ← CStarRing.norm_star_mul_self,
        show star (NormedSpace.exp x) = (NormedSpace.exp x)† from rfl, h_adj]
      exact ContinuousLinearMap.norm_id_le
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp h_sq
  have hU_pos := hU_le t
  have hU_neg := hU_le (-t)
  dsimp [heisenbergFlow]
  calc ‖timeEvolutionOp H t * X * timeEvolutionOp H (-t)‖
    _ ≤ ‖timeEvolutionOp H t * X‖ * ‖timeEvolutionOp H (-t)‖ := norm_mul_le _ _
    _ ≤ (‖timeEvolutionOp H t‖ * ‖X‖) * ‖timeEvolutionOp H (-t)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖X‖) * 1 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hU_pos (norm_nonneg X)) hU_neg
        (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg X))
    _ = ‖X‖ := by ring

/-- For any integrable filter kernel `w : ℝ → ℂ` and any operators `H` and `A`,
    `fun t : ℝ => w t • heisenbergFlow H t A` is Bochner integrable over `ℝ`. -/
lemma integrable_smul_heisenbergFlow_of_integrable {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H) {w : ℝ → ℂ} (hw : Integrable w)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Integrable (fun t : ℝ => w t • heisenbergFlow H t A) := by
  have h_meas : AEStronglyMeasurable (fun t : ℝ => w t • heisenbergFlow H t A) volume :=
    hw.aestronglyMeasurable.smul (continuous_heisenbergFlow H A).aestronglyMeasurable
  refine Integrable.mono' (hw.norm.mul_const ‖A‖) h_meas (Filter.Eventually.of_forall (fun t => ?_))
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_heisenbergFlow_le_self hH t A) (norm_nonneg (w t))

/-- **Unitary Covariance of `bochnerFilteredOp` (`bochnerFilteredOp_unitary_conj`)**:
    For any self-adjoint Hamiltonian $H$, unitary $U$, and integrable filter kernel $w : \mathbb{R} \to \mathbb{C}$,
    $$\mathcal{F}_w^{U^\dagger H U}(U^\dagger A U) = U^\dagger \mathcal{F}_w^H(A) U.$$ -/
theorem bochnerFilteredOp_unitary_conj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw : Integrable w)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    bochnerFilteredOp (U.1† * H * U.1) w (U.1† * A * U.1) =
      U.1† * bochnerFilteredOp H w A * U.1 := by
  rcases unitary_mul_adj_and_adj_mul_clm U with ⟨hUU_adj, hU_adj_U⟩
  exact bochnerFilteredOp_conj_unitary hUU_adj hU_adj_U H w A
    (integrable_smul_heisenbergFlow_of_integrable hH hw A)

/-- Specialization of `bochnerFilteredOp_unitary_conj` to `bhFilterWeight` (requiring no `IsSelfAdjoint H` hypothesis). -/
theorem bochnerFilteredOp_w_BH11_unitary_conj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    bochnerFilteredOp (U.1† * H * U.1) bhFilterWeight (U.1† * A * U.1) =
      U.1† * bochnerFilteredOp H bhFilterWeight A * U.1 := by
  rcases unitary_mul_adj_and_adj_mul_clm U with ⟨hUU_adj, hU_adj_U⟩
  exact bochnerFilteredOp_conj_unitary hUU_adj hU_adj_U H bhFilterWeight A
    (integrable_w_BH11_smul_heisenbergFlow H A)

/-- **Bare-Frame Sum Factorization of `bochnerFilteredSiteOp` (`bochnerFilteredSiteOp_eq_bare_add_sub_check`)**:
    When $H' = U^\dagger H U$, the dressed site operator `bochnerFilteredSiteOp H' U.1 w V_u Q_u` equals
    $$U^\dagger \mathcal{F}_w^H(V_u + Q_u) U - Q_u.$$ -/
theorem bochnerFilteredSiteOp_eq_bare_add_sub_check {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw : Integrable w)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    bochnerFilteredSiteOp (U.1† * H * U.1) U.1 w V_u Q_u =
      U.1† * bochnerFilteredOp H w (V_u + Q_u) * U.1 - Q_u := by
  unfold bochnerFilteredSiteOp
  rw [bochnerFilteredOp_unitary_conj hH U hw V_u,
    bochnerFilteredOp_unitary_conj hH U hw Q_u,
    bochnerFilteredOp_add H w
      (integrable_smul_heisenbergFlow_of_integrable hH hw V_u)
      (integrable_smul_heisenbergFlow_of_integrable hH hw Q_u),
    mul_add (U.1†), add_mul _ _ U.1, add_sub_assoc]

/-- **Bare-Frame Three-Term Decomposition of `bochnerFilteredSiteOp` (`bochnerFilteredSiteOp_eq_bare_three_term`)**:
    $$X_u = U^\dagger \mathcal{F}_w^H(V_u) U + U^\dagger (\mathcal{F}_w^H(Q_u) - Q_u) U + (U^\dagger Q_u U - Q_u).$$ -/
theorem bochnerFilteredSiteOp_eq_bare_three_term {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw : Integrable w)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    bochnerFilteredSiteOp (U.1† * H * U.1) U.1 w V_u Q_u =
      U.1† * bochnerFilteredOp H w V_u * U.1 +
      U.1† * (bochnerFilteredOp H w Q_u - Q_u) * U.1 +
      (U.1† * Q_u * U.1 - Q_u) := by
  rcases unitary_mul_adj_and_adj_mul_clm U with ⟨hUU_adj, hU_adj_U⟩
  exact bochnerFilteredSiteOp_eq_conj_unitary rfl hUU_adj hU_adj_U
    (integrable_smul_heisenbergFlow_of_integrable hH hw V_u)
    (integrable_smul_heisenbergFlow_of_integrable hH hw Q_u)

/-!
## 2. Bare-Frame Commuting-Check FTC Bound (`norm_bochnerFilteredOp_sub_self_le_of_commute_left`)
-/

/-- Three-term triangle inequality `‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖`. -/
lemma norm_add_three_le {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
  le_trans (norm_add_le (a + b) c) (add_le_add (norm_add_le a b) (le_refl ‖c‖))

/-- **Mean-Value Heisenberg Flow Deviation Bound for Commuting Checks (`norm_heisenbergFlow_sub_self_le_of_commute_left`)**:
    When $H_0 + V_{\mathrm{tot}}$ is self-adjoint and $[H_0, Q_u] = 0$,
    $$\|\tau_t^{H_0 + V_{\mathrm{tot}}}(Q_u) - Q_u\| \le \|[V_{\mathrm{tot}}, Q_u]\| \cdot |t|.$$ -/
theorem norm_heisenbergFlow_sub_self_le_of_commute_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint (H0 + totalPerturbation)) (h_comm : Commute H0 Q_u) (t : ℝ) :
    ‖heisenbergFlow (H0 + totalPerturbation) t Q_u - Q_u‖ ≤ ‖opCommutator totalPerturbation Q_u‖ * |t| := by
  have h_deriv_le : ∀ τ ∈ (Set.univ : Set ℝ),
      ‖(Complex.I : ℂ) • heisenbergFlow (H0 + totalPerturbation) τ (opCommutator totalPerturbation Q_u)‖ ≤
        ‖opCommutator totalPerturbation Q_u‖ := by
    intro τ _
    rw [norm_smul, Complex.norm_I, one_mul]
    exact norm_heisenbergFlow_le_self hH τ (opCommutator totalPerturbation Q_u)
  have h_mvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ => heisenbergFlow (H0 + totalPerturbation) τ Q_u)
    (f' := fun τ => (Complex.I : ℂ) • heisenbergFlow (H0 + totalPerturbation) τ (opCommutator totalPerturbation Q_u))
    (s := Set.univ)
    (fun τ _ => (hasDerivAt_heisenbergFlow_of_commute_left h_comm τ).hasDerivWithinAt)
    h_deriv_le
    convex_univ
    (Set.mem_univ (0 : ℝ))
    (Set.mem_univ t)
  have h_at_0 : heisenbergFlow (H0 + totalPerturbation) 0 Q_u = Q_u := by
    unfold heisenbergFlow
    rw [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  have h_norm_t : ‖t - (0 : ℝ)‖ = |t| := by
    rw [sub_zero, Real.norm_eq_abs]
  rw [h_at_0, h_norm_t] at h_mvt
  exact h_mvt

/-- **Bare-Frame Commuting-Check Bochner Filter FTC Bound (`norm_bochnerFilteredOp_sub_self_le_of_commute_left`)**:
    When $H_0 + V_{\mathrm{tot}}$ is self-adjoint, $\int_{-\infty}^\infty w(t)\, dt = 1$, and $[H_0, Q_u] = 0$,
    $$\|\mathcal{F}_w^{H_0 + V_{\mathrm{tot}}}(Q_u) - Q_u\|
      \le \left(\int_{-\infty}^\infty \|w(t)\| |t|\, dt\right) \|[V_{\mathrm{tot}}, Q_u]\|.$$ -/
theorem norm_bochnerFilteredOp_sub_self_le_of_commute_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint (H0 + totalPerturbation)) (h_comm : Commute H0 Q_u)
    {w : ℝ → ℂ} (hw_int : Integrable w) (hw_one : (∫ t : ℝ, w t) = 1)
    (hw_t_int : Integrable (fun t : ℝ => ‖w t‖ * |t|)) :
    ‖bochnerFilteredOp (H0 + totalPerturbation) w Q_u - Q_u‖ ≤
      (∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖ := by
  have h_int_flow : Integrable (fun t : ℝ => w t • heisenbergFlow (H0 + totalPerturbation) t Q_u) :=
    integrable_smul_heisenbergFlow_of_integrable hH hw_int Q_u
  have h_int_const : Integrable (fun t : ℝ => w t • Q_u) := hw_int.smul_const Q_u
  have h_sub_eq : bochnerFilteredOp (H0 + totalPerturbation) w Q_u - Q_u =
      ∫ t : ℝ, w t • (heisenbergFlow (H0 + totalPerturbation) t Q_u - Q_u) := by
    unfold bochnerFilteredOp
    have h_Q : Q_u = ∫ t : ℝ, w t • Q_u := by
      rw [integral_smul_const, hw_one, one_smul]
    conv_lhs => rhs; rw [h_Q]
    rw [← integral_sub h_int_flow h_int_const]
    congr 1; funext t; rw [smul_sub]
  have h_int_diff : Integrable (fun t : ℝ => w t • (heisenbergFlow (H0 + totalPerturbation) t Q_u - Q_u)) :=
    (h_int_flow.sub h_int_const).congr
      (Filter.Eventually.of_forall (fun t => (smul_sub (w t) _ _).symm))
  rw [h_sub_eq]
  calc ‖∫ t : ℝ, w t • (heisenbergFlow (H0 + totalPerturbation) t Q_u - Q_u)‖
    _ ≤ ∫ t : ℝ, ‖w t • (heisenbergFlow (H0 + totalPerturbation) t Q_u - Q_u)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖ := by
      refine integral_mono h_int_diff.norm (hw_t_int.mul_const _) (fun t => ?_)
      dsimp only
      rw [norm_smul, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (w t))
      rw [mul_comm |t| ‖opCommutator totalPerturbation Q_u‖]
      exact norm_heisenbergFlow_sub_self_le_of_commute_left hH h_comm t
    _ = (∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖ :=
      integral_mul_const _ _

/-- `fun t : ℝ => ‖w_BH11 t‖ * |t|` is Bochner integrable over `ℝ` with integral $\le \pi$. -/
theorem integrable_and_integral_norm_w_BH11_mul_abs_le :
    Integrable (fun t : ℝ => ‖bhFilterWeight t‖ * |t|) MeasureTheory.volume ∧
    (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) ≤ Real.pi := by
  have h_ind : (fun t : ℝ => ‖bhFilterWeight t‖ * |t|) =
      (Set.Icc (-Real.pi) Real.pi).indicator (fun t : ℝ => (1 / (2 * Real.pi)) * |t|) := by
    funext t
    rw [norm_w_BH11_eq]
    by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi
    · rw [w_BH11_real_of_mem ht, Set.indicator_of_mem ht]
    · rw [w_BH11_real_of_not_mem ht, zero_mul, Set.indicator_of_notMem ht]
  have h_int : Integrable (fun t : ℝ => ‖bhFilterWeight t‖ * |t|) MeasureTheory.volume := by
    rw [h_ind]
    exact integrable_indicator_Icc_of_continuous (continuous_const.mul continuous_abs)
  refine ⟨h_int, ?_⟩
  have h_pt : ∀ t : ℝ, ‖bhFilterWeight t‖ * |t| ≤ ‖bhFilterWeight t‖ * Real.pi := by
    intro t
    rw [norm_w_BH11_eq]
    by_cases ht : t ∈ Set.Icc (-Real.pi) Real.pi
    · rw [w_BH11_real_of_mem ht]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨ht.1, ht.2⟩) (by positivity)
    · rw [w_BH11_real_of_not_mem ht, zero_mul, zero_mul]
  calc ∫ t : ℝ, ‖bhFilterWeight t‖ * |t|
    _ ≤ ∫ t : ℝ, ‖bhFilterWeight t‖ * Real.pi :=
      integral_mono h_int (integrable_norm_w_BH11.mul_const Real.pi) h_pt
    _ = (∫ t : ℝ, ‖bhFilterWeight t‖) * Real.pi := integral_mul_const Real.pi _
    _ = Real.pi := by rw [integral_norm_w_BH11_eq_one, one_mul]

/-- Specialization of `norm_bochnerFilteredOp_sub_self_le_of_commute_left` to `bhFilterWeight`. -/
theorem norm_bochnerFilteredOp_w_BH11_sub_self_le_of_commute_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint (H0 + totalPerturbation)) (h_comm : Commute H0 Q_u) :
    ‖bochnerFilteredOp (H0 + totalPerturbation) bhFilterWeight Q_u - Q_u‖ ≤
      (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖ ∧
    ‖bochnerFilteredOp (H0 + totalPerturbation) bhFilterWeight Q_u - Q_u‖ ≤
      Real.pi * ‖opCommutator totalPerturbation Q_u‖ := by
  rcases integrable_and_integral_norm_w_BH11_mul_abs_le with ⟨hw_t_int, hw_t_le⟩
  have h1 := norm_bochnerFilteredOp_sub_self_le_of_commute_left hH h_comm
    integrable_w_BH11 integral_w_BH11_eq_one hw_t_int
  refine ⟨h1, le_trans h1 (mul_le_mul_of_nonneg_right hw_t_le (norm_nonneg _))⟩

/-- **Bare-Frame Site Operator Norm Bound (`norm_bochnerFilteredSiteOp_le_of_bare_commute`)**:
    When $H = H_0 + V_{\mathrm{tot}}$ is self-adjoint, $\int w = 1$, and $[H_0, Q_u] = 0$,
    $$\|X_u\| \le \left(\int \|w(t)\|\, dt\right) \|V_u\| +
      \left(\int \|w(t)\| |t|\, dt\right) \|[V_{\mathrm{tot}}, Q_u]\| + \|U^\dagger Q_u U - Q_u\|.$$ -/
theorem norm_bochnerFilteredSiteOp_le_of_bare_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint (H0 + totalPerturbation)) (h_comm : Commute H0 Q_u)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw_int : Integrable w) (hw_one : (∫ t : ℝ, w t) = 1)
    (hw_t_int : Integrable (fun t : ℝ => ‖w t‖ * |t|)) :
    ‖bochnerFilteredSiteOp (U.1† * (H0 + totalPerturbation) * U.1) U.1 w V_u Q_u‖ ≤
      (∫ t : ℝ, ‖w t‖) * ‖V_u‖ +
      (∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖ +
      ‖U.1† * Q_u * U.1 - Q_u‖ := by
  let A1 := U.1† * bochnerFilteredOp (H0 + totalPerturbation) w V_u * U.1
  let A2 := U.1† * (bochnerFilteredOp (H0 + totalPerturbation) w Q_u - Q_u) * U.1
  let A3 := U.1† * Q_u * U.1 - Q_u
  have h_eq : bochnerFilteredSiteOp (U.1† * (H0 + totalPerturbation) * U.1) U.1 w V_u Q_u = A1 + A2 + A3 :=
    bochnerFilteredSiteOp_eq_bare_three_term hH U hw_int V_u Q_u
  have h1 : ‖A1‖ ≤ (∫ t : ℝ, ‖w t‖) * ‖V_u‖ :=
    le_trans (norm_unitary_adj_conj_le_clm U _) (norm_bochnerFilteredOp_le hH w V_u)
  have h2 : ‖A2‖ ≤ (∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖ :=
    le_trans (norm_unitary_adj_conj_le_clm U _)
      (norm_bochnerFilteredOp_sub_self_le_of_commute_left hH h_comm hw_int hw_one hw_t_int)
  rw [h_eq]
  exact le_trans (norm_add_three_le A1 A2 A3) (add_le_add (add_le_add h1 h2) (le_refl ‖A3‖))

/-!
## 3. Two-Stage `condExp` Composition: Bare Lieb–Robinson + Unitary Dressing `condExp` Tail
-/

/-- Subtraction linearity of `condExp Site A`. -/
lemma condExp_sub_clm {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    condExp Site A (O₁ - O₂) = condExp Site A O₁ - condExp Site A O₂ :=
  (condExpCLM Site A).map_sub O₁ O₂

/-- For any operator `X` and region `A`, `‖X - condExp Site A X‖ ≤ 2 * ‖X‖`. -/
lemma norm_sub_condExp_le_two_mul_norm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖X - condExp Site A X‖ ≤ 2 * ‖X‖ := by
  have h_ce : ‖condExp Site A X‖ ≤ ‖X‖ := norm_condExp_le A X
  linarith [norm_sub_le X (condExp Site A X)]

/-- **Two-Stage `condExp` Composition Lemma (`norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail`)**:
    For any bare operator $B$, intermediate bare light-cone region $A_{\mathrm{bare}}$, and target
    region $A_K$: if $\|B - \mathbb{E}_{A_{\mathrm{bare}}}(B)\| \le \varepsilon_{\mathrm{bare}}$ and
    $U_{\mathrm{dress}}$ spreads operators supported on $A_{\mathrm{bare}}$ outside $A_K$ by at most
    $\varepsilon_{\mathrm{LR}}$, then:
    $$\|U_{\mathrm{dress}}^\dagger B U_{\mathrm{dress}} -
      \mathbb{E}_{A_K}(U_{\mathrm{dress}}^\dagger B U_{\mathrm{dress}})\|
      \le 2 \varepsilon_{\mathrm{bare}} + \varepsilon_{\mathrm{LR}} \|B\|.$$ -/
theorem norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (A_bare A_K : Finset (BoxD D L))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {ε_bare ε_LR : ℝ} (hε_LR_nn : 0 ≤ ε_LR)
    (h_bare_tail : ‖B - condExp Site A_bare B‖ ≤ ε_bare)
    (h_U_tail : ∀ B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site A_bare B_loc →
      ‖U_dress.1† * B_loc * U_dress.1 -
        condExp Site A_K (U_dress.1† * B_loc * U_dress.1)‖ ≤ ε_LR * ‖B_loc‖) :
    ‖U_dress.1† * B * U_dress.1 - condExp Site A_K (U_dress.1† * B * U_dress.1)‖ ≤
      2 * ε_bare + ε_LR * ‖B‖ := by
  let B_loc := condExp Site A_bare B
  let R := B - B_loc
  have hB_eq : B = B_loc + R := (add_sub_cancel B_loc B).symm
  have h_conj_eq : U_dress.1† * B * U_dress.1 =
      U_dress.1† * B_loc * U_dress.1 + U_dress.1† * R * U_dress.1 := by
    conv_lhs => rw [hB_eq]
    rw [mul_add (U_dress.1†), add_mul _ _ U_dress.1]
  let T1 := U_dress.1† * R * U_dress.1 - condExp Site A_K (U_dress.1† * R * U_dress.1)
  let T2 := U_dress.1† * B_loc * U_dress.1 - condExp Site A_K (U_dress.1† * B_loc * U_dress.1)
  have h_diff_eq :
      U_dress.1† * B * U_dress.1 - condExp Site A_K (U_dress.1† * B * U_dress.1) = T1 + T2 := by
    dsimp [T1, T2]
    rw [h_conj_eq, condExp_add]
    abel
  have hR_bound : ‖T1‖ ≤ 2 * ε_bare := by
    calc ‖T1‖
      _ ≤ 2 * ‖U_dress.1† * R * U_dress.1‖ := norm_sub_condExp_le_two_mul_norm A_K _
      _ ≤ 2 * ‖R‖ := mul_le_mul_of_nonneg_left (norm_unitary_adj_conj_le_clm U_dress R) (by norm_num)
      _ ≤ 2 * ε_bare := mul_le_mul_of_nonneg_left h_bare_tail (by norm_num)
  have hBloc_bound : ‖T2‖ ≤ ε_LR * ‖B‖ := by
    calc ‖T2‖
      _ ≤ ε_LR * ‖B_loc‖ := h_U_tail B_loc (isSupportedOn_condExp Site A_bare B)
      _ ≤ ε_LR * ‖B‖ := mul_le_mul_of_nonneg_left (norm_condExp_le A_bare B) hε_LR_nn
  rw [h_diff_eq]
  exact le_trans (norm_add_le T1 T2) (add_le_add hR_bound hBloc_bound)

/-- **Bare-Frame Factorization & `condExp` Tail Bound for `bochnerFilteredSiteOp`
    (`norm_bochnerFilteredSiteOp_sub_condExp_le_of_bare_LR_and_unitary_tail`)**:
    Expresses $X_u := \mathrm{bochnerFilteredSiteOp}\ (U^\dagger H U)\ U\ w\ V_u\ Q_u$ via the
    bare-frame filtered sum $\mathcal{F}_w^H(V_u + Q_u)$ conjugated by $U$, and bounds
    $\|X_u - \mathbb{E}_{\mathrm{boxCube}(u, K)}(X_u)\|$ whenever $Q_u$ is supported on $\mathrm{boxCube}(u, K)$. -/
theorem norm_bochnerFilteredSiteOp_sub_condExp_le_of_bare_LR_and_unitary_tail {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw : Integrable w)
    (u : BoxD D L) (K r_bare : ℕ)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {ε_bare ε_LR : ℝ} (hε_LR_nn : 0 ≤ ε_LR)
    (hQ_supp : IsSupportedOn Site (boxCube u K) Q_u)
    (h_bare_tail :
      ‖bochnerFilteredOp H w (V_u + Q_u) -
        condExp Site (boxCube u r_bare) (bochnerFilteredOp H w (V_u + Q_u))‖ ≤ ε_bare)
    (h_U_tail : ∀ B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site (boxCube u r_bare) B_loc →
      ‖U_dress.1† * B_loc * U_dress.1 -
        condExp Site (boxCube u K) (U_dress.1† * B_loc * U_dress.1)‖ ≤ ε_LR * ‖B_loc‖) :
    let X_u := bochnerFilteredSiteOp (U_dress.1† * H * U_dress.1) U_dress.1 w V_u Q_u
    ‖X_u - condExp Site (boxCube u K) X_u‖ ≤
      2 * ε_bare + ε_LR * ‖bochnerFilteredOp H w (V_u + Q_u)‖ := by
  intro X_u
  let B := bochnerFilteredOp H w (V_u + Q_u)
  have hX_eq : X_u = U_dress.1† * B * U_dress.1 - Q_u :=
    bochnerFilteredSiteOp_eq_bare_add_sub_check hH U_dress hw V_u Q_u
  have hQ_ce : condExp Site (boxCube u K) Q_u = Q_u := condExp_eq_self_of_isSupportedOn hQ_supp
  have h_diff_eq : X_u - condExp Site (boxCube u K) X_u =
      U_dress.1† * B * U_dress.1 - condExp Site (boxCube u K) (U_dress.1† * B * U_dress.1) := by
    rw [hX_eq, condExp_sub_clm, hQ_ce]
    abel
  rw [h_diff_eq]
  exact norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail
    U_dress (boxCube u r_bare) (boxCube u K) B hε_LR_nn h_bare_tail h_U_tail

/-- When $Q_u$ is supported on $A_{\mathrm{bare}}$, subtracting $Q_u$ before taking `condExp Site A_bare`
    leaves the bare `condExp` tail unchanged:
    $(\mathcal{F}_w^H(Q_u) - Q_u) - \mathbb{E}_{A_{\mathrm{bare}}}(\mathcal{F}_w^H(Q_u) - Q_u) =
     \mathcal{F}_w^H(Q_u) - \mathbb{E}_{A_{\mathrm{bare}}}(\mathcal{F}_w^H(Q_u))$. -/
lemma bochnerFilteredOp_sub_self_sub_condExp_eq_of_isSupportedOn {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (w : ℝ → ℂ)
    {A_bare : Finset (BoxD D L)}
    {Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hQ_supp : IsSupportedOn Site A_bare Q_u) :
    (bochnerFilteredOp H w Q_u - Q_u) -
      condExp Site A_bare (bochnerFilteredOp H w Q_u - Q_u) =
    bochnerFilteredOp H w Q_u - condExp Site A_bare (bochnerFilteredOp H w Q_u) := by
  rw [condExp_sub_clm, condExp_eq_self_of_isSupportedOn hQ_supp]
  abel

/-- **Three-Term Bare-Split `condExp` Tail Bound (`norm_bochnerFilteredSiteOp_sub_condExp_le_of_bare_split_and_unitary_tail`)**:
    Combines the 3-term bare-frame decomposition `bochnerFilteredSiteOp_eq_bare_three_term`,
    the commuting-check FTC bound `norm_bochnerFilteredOp_sub_self_le_of_commute_left`, and the
    two-stage `condExp` composition `norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail`
    so that every term on the right-hand side carries both an $O(J)$ factor and spatial decay in $K$:
    $$\|X_u - \mathbb{E}_{\mathrm{boxCube}(u, K)}(X_u)\| \le
      2 \varepsilon_{\mathrm{bare}, V} + 2 \varepsilon_{\mathrm{bare}, Q} +
      \varepsilon_{\mathrm{LR}} \left(\left(\int \|w\|\right) \|V_u\| +
        \left(\int \|w(t)\| |t|\right) \|[V_{\mathrm{tot}}, Q_u]\|\right) +
      \varepsilon_{\mathrm{LR}, Q}.$$ -/
theorem norm_bochnerFilteredSiteOp_sub_condExp_le_of_bare_split_and_unitary_tail {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H0 totalPerturbation V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint (H0 + totalPerturbation)) (h_comm : Commute H0 Q_u)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw_int : Integrable w) (hw_one : (∫ t : ℝ, w t) = 1)
    (hw_t_int : Integrable (fun t : ℝ => ‖w t‖ * |t|))
    (u : BoxD D L) (K r_bare : ℕ)
    {ε_bare_V ε_bare_Q ε_LR ε_LR_Q : ℝ} (hε_LR_nn : 0 ≤ ε_LR)
    (hQ_supp_bare : IsSupportedOn Site (boxCube u r_bare) Q_u)
    (hQ_supp_K : IsSupportedOn Site (boxCube u K) Q_u)
    (h_bare_V :
      ‖bochnerFilteredOp (H0 + totalPerturbation) w V_u -
        condExp Site (boxCube u r_bare) (bochnerFilteredOp (H0 + totalPerturbation) w V_u)‖ ≤ ε_bare_V)
    (h_bare_Q :
      ‖bochnerFilteredOp (H0 + totalPerturbation) w Q_u -
        condExp Site (boxCube u r_bare) (bochnerFilteredOp (H0 + totalPerturbation) w Q_u)‖ ≤ ε_bare_Q)
    (h_U_tail : ∀ B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site (boxCube u r_bare) B_loc →
      ‖U_dress.1† * B_loc * U_dress.1 -
        condExp Site (boxCube u K) (U_dress.1† * B_loc * U_dress.1)‖ ≤ ε_LR * ‖B_loc‖)
    (h_U_Q_tail :
      ‖U_dress.1† * Q_u * U_dress.1 -
        condExp Site (boxCube u K) (U_dress.1† * Q_u * U_dress.1)‖ ≤ ε_LR_Q) :
    let X_u := bochnerFilteredSiteOp (U_dress.1† * (H0 + totalPerturbation) * U_dress.1) U_dress.1 w V_u Q_u
    ‖X_u - condExp Site (boxCube u K) X_u‖ ≤
      2 * ε_bare_V + 2 * ε_bare_Q +
      ε_LR * ((∫ t : ℝ, ‖w t‖) * ‖V_u‖ +
        (∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖) +
      ε_LR_Q := by
  intro X_u
  let H := H0 + totalPerturbation
  let B_V := bochnerFilteredOp H w V_u
  let B_Q := bochnerFilteredOp H w Q_u - Q_u
  let D1 := U_dress.1† * B_V * U_dress.1 - condExp Site (boxCube u K) (U_dress.1† * B_V * U_dress.1)
  let D2 := U_dress.1† * B_Q * U_dress.1 - condExp Site (boxCube u K) (U_dress.1† * B_Q * U_dress.1)
  let D3 := U_dress.1† * Q_u * U_dress.1 - condExp Site (boxCube u K) (U_dress.1† * Q_u * U_dress.1)
  have hX_eq : X_u =
      U_dress.1† * B_V * U_dress.1 + U_dress.1† * B_Q * U_dress.1 +
      (U_dress.1† * Q_u * U_dress.1 - Q_u) :=
    bochnerFilteredSiteOp_eq_bare_three_term hH U_dress hw_int V_u Q_u
  have hQ_ce : condExp Site (boxCube u K) Q_u = Q_u := condExp_eq_self_of_isSupportedOn hQ_supp_K
  have h_diff_eq : X_u - condExp Site (boxCube u K) X_u = D1 + D2 + D3 := by
    dsimp [D1, D2, D3]
    rw [hX_eq, condExp_add, condExp_add, condExp_sub_clm, hQ_ce]
    abel
  have h_BV_tail : ‖D1‖ ≤ 2 * ε_bare_V + ε_LR * ((∫ t : ℝ, ‖w t‖) * ‖V_u‖) := by
    have h1 := norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail
      U_dress (boxCube u r_bare) (boxCube u K) B_V hε_LR_nn h_bare_V h_U_tail
    have h2 : ε_LR * ‖B_V‖ ≤ ε_LR * ((∫ t : ℝ, ‖w t‖) * ‖V_u‖) :=
      mul_le_mul_of_nonneg_left (norm_bochnerFilteredOp_le hH w V_u) hε_LR_nn
    linarith
  have h_BQ_bare : ‖B_Q - condExp Site (boxCube u r_bare) B_Q‖ ≤ ε_bare_Q := by
    dsimp [B_Q]
    rw [bochnerFilteredOp_sub_self_sub_condExp_eq_of_isSupportedOn H w hQ_supp_bare]
    exact h_bare_Q
  have h_BQ_tail : ‖D2‖ ≤ 2 * ε_bare_Q + ε_LR * ((∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖) := by
    have h1 := norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail
      U_dress (boxCube u r_bare) (boxCube u K) B_Q hε_LR_nn h_BQ_bare h_U_tail
    have h2 : ε_LR * ‖B_Q‖ ≤ ε_LR * ((∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖) :=
      mul_le_mul_of_nonneg_left
        (norm_bochnerFilteredOp_sub_self_le_of_commute_left hH h_comm hw_int hw_one hw_t_int) hε_LR_nn
    linarith
  rw [h_diff_eq]
  have h_tri := norm_add_three_le D1 D2 D3
  linarith [h_tri, h_BV_tail, h_BQ_tail, h_U_Q_tail]

end
