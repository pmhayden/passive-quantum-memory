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
import Proofs.KatoHastingsFlow.ConstructiveQuasiLocalQAC
import Proofs.LiebRobinson.DuhamelAndGronwall
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.BandLimitedFilter.EigenprojEvolutionAndBlockDecomp

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Self-Adjointness of Bochner-Filtered Operators and Interpolated Hamiltonians

Interchanges the continuous real-linear star operation `starRealCLM` with Bochner time integrals (`star_bochner_integral`) to prove self-adjointness of `heisenbergFlow` (`isSelfAdjoint_heisenbergFlow`) and `bochnerFilteredOp` (`isSelfAdjoint_bochnerFilteredOp`, `isSelfAdjoint_bochnerFilteredOp_w_BH11`) for even real weights. Defines `interpolatedHamiltonian` and proves its coupling-parameter differentiability (`hasDerivAt_interpolatedHamiltonian`, `hasDerivAt_dressedHamiltonian`).

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (69) (`eq:two-bochner-transforms`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (75) (`eq:qac-generator-def`)
-/

/-!
## 1. Adjoint and Self-Adjointness of `timeEvolutionOp`, `heisenbergFlow`, and `bochnerFilteredOp`
-/

/-- The Hilbert-space operator adjoint `star` bundled as a continuous `ℝ`-linear map on `E →L[ℂ] E`. -/
def starRealCLM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) where
  toFun := star
  map_add' := star_add
  map_smul' := star_smul
  cont := continuous_star

/-- The operator adjoint `star` commutes with Bochner integration over `ℝ` on `E →L[ℂ] E`. -/
theorem star_bochner_integral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (F : ℝ → (E →L[ℂ] E)) :
    star (∫ t : ℝ, F t) = ∫ t : ℝ, star (F t) := by
  by_cases hF : Integrable F MeasureTheory.volume
  · exact (starRealCLM.integral_comp_comm hF).symm
  · have hF_star : ¬ Integrable (fun t : ℝ => star (F t)) MeasureTheory.volume := by
      intro h
      apply hF
      have h2 := starRealCLM.integrable_comp h
      have h_eq : (fun t : ℝ => starRealCLM (star (F t))) = F := by
        funext t
        exact star_star (F t)
      rwa [h_eq] at h2
    rw [integral_undef hF, integral_undef hF_star, star_zero]

/-- For a self-adjoint Hamiltonian $H'$, the adjoint of `timeEvolutionOp H' t` is `timeEvolutionOp H' (-t)`. -/
theorem star_timeEvolutionOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (t : ℝ) :
    star (timeEvolutionOp H' t) = timeEvolutionOp H' (-t) := by
  unfold timeEvolutionOp
  rw [NormedSpace.star_exp, star_smul, hH'.star_eq, star_mul',
    RCLike.star_def, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, mul_neg, neg_mul]

/-- Adjoint of `timeEvolutionOp H' (-t)` is `timeEvolutionOp H' t` when $H'$ is self-adjoint. -/
theorem star_timeEvolutionOp_neg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (t : ℝ) :
    star (timeEvolutionOp H' (-t)) = timeEvolutionOp H' t := by
  rw [star_timeEvolutionOp hH' (-t), neg_neg]

/-- For a self-adjoint Hamiltonian $H'$, Heisenberg evolution commutes with `star`:
    `star (heisenbergFlow H' t O) = heisenbergFlow H' t (star O)`. -/
theorem star_heisenbergFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (t : ℝ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    star (heisenbergFlow H' t O) = heisenbergFlow H' t (star O) := by
  unfold heisenbergFlow
  rw [star_mul, star_mul, star_timeEvolutionOp hH' t, star_timeEvolutionOp_neg hH' t, mul_assoc]

/-- If $H'$ and $O$ are self-adjoint, then `heisenbergFlow H' t O` is self-adjoint for all $t \in \mathbb{R}$. -/
theorem isSelfAdjoint_heisenbergFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (hO : IsSelfAdjoint O) (t : ℝ) :
    IsSelfAdjoint (heisenbergFlow H' t O) := by
  rw [isSelfAdjoint_iff, star_heisenbergFlow hH' t O, hO.star_eq]

/-- Adjoint of `bochnerFilteredOp H' w O` for a self-adjoint Hamiltonian $H'$:
    `star (bochnerFilteredOp H' w O) = bochnerFilteredOp H' (fun t => star (w t)) (star O)`. -/
theorem star_bochnerFilteredOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    star (bochnerFilteredOp H' w O) =
      bochnerFilteredOp H' (fun t => star (w t)) (star O) := by
  unfold bochnerFilteredOp
  rw [star_bochner_integral]
  congr 1
  funext t
  rw [star_smul, star_heisenbergFlow hH' t O]

/-- **Self-Adjointness of `bochnerFilteredOp` (`isSelfAdjoint_bochnerFilteredOp`)**:
    Whenever $H'$ and $O$ are self-adjoint and the filter kernel $w : \mathbb{R} \to \mathbb{C}$ is
    real-valued (`∀ t, star (w t) = w t`), `bochnerFilteredOp H' w O` is self-adjoint. -/
theorem isSelfAdjoint_bochnerFilteredOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (hO : IsSelfAdjoint O)
    {w : ℝ → ℂ} (hw : ∀ t : ℝ, star (w t) = w t) :
    IsSelfAdjoint (bochnerFilteredOp H' w O) := by
  rw [isSelfAdjoint_iff, star_bochnerFilteredOp hH' w O, hO.star_eq]
  have hw_eq : (fun t : ℝ => star (w t)) = w := funext hw
  rw [hw_eq]

/-- `bochnerFilteredOp H' w_BH11 O` is self-adjoint whenever $H'$ and $O$ are self-adjoint. -/
theorem isSelfAdjoint_bochnerFilteredOp_w_BH11 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (hO : IsSelfAdjoint O) :
    IsSelfAdjoint (bochnerFilteredOp H' bhFilterWeight O) :=
  isSelfAdjoint_bochnerFilteredOp hH' hO star_w_BH11

/-- Conjugation by any operator $U$ preserves self-adjointness: if $H$ is self-adjoint, then
    $U^\dagger H U$ is self-adjoint. -/
theorem isSelfAdjoint_conj_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (U : E →L[ℂ] E) :
    IsSelfAdjoint (U† * H * U) := by
  rw [isSelfAdjoint_iff]
  change star (star U * H * U) = star U * H * U
  rw [star_mul, star_mul, hH.star_eq, star_star, mul_assoc]

/-!
## 2. Continuous-in-$s$ Linear Interpolation Path $H(s) = H_0 + s V$ & Dressed Hamiltonian Flow
-/

/-- Continuous-in-$s$ linear interpolation Hamiltonian path $H(s) := H_0 + (s : \mathbb{C}) \bullet V$. -/
def interpolatedHamiltonian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H0 V : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E :=
  H0 + (s : ℂ) • V

/-- Endpoint evaluation at $s = 0$: `interpolatedHamiltonian H0 V 0 = H0`. -/
@[simp]
lemma interpolatedHamiltonian_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H0 V : E →L[ℂ] E) :
    interpolatedHamiltonian H0 V 0 = H0 := by
  unfold interpolatedHamiltonian
  rw [Complex.ofReal_zero, zero_smul, add_zero]

/-- Endpoint evaluation at $s = 1$: `interpolatedHamiltonian H0 V 1 = H0 + V`. -/
@[simp]
lemma interpolatedHamiltonian_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (H0 V : E →L[ℂ] E) :
    interpolatedHamiltonian H0 V 1 = H0 + V := by
  unfold interpolatedHamiltonian
  rw [Complex.ofReal_one, one_smul]

/-- Self-adjointness of `interpolatedHamiltonian H0 V s` for all $s \in \mathbb{R}$. -/
theorem isSelfAdjoint_interpolatedHamiltonian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {H0 V : E →L[ℂ] E} (hH0 : IsSelfAdjoint H0) (hV : IsSelfAdjoint V) (s : ℝ) :
    IsSelfAdjoint (interpolatedHamiltonian H0 V s) :=
  hH0.add (isSelfAdjoint_real_smul s hV)

/-- Exact $s$-derivative of `interpolatedHamiltonian H0 V`: $\frac{d}{ds}(H_0 + s V) = V$. -/
theorem hasDerivAt_interpolatedHamiltonian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (H0 V : E →L[ℂ] E) (s : ℝ) :
    HasDerivAt (interpolatedHamiltonian H0 V) V s := by
  have h_lin : HasDerivAt (fun τ : ℝ => (τ : ℂ) • V) V s := by
    have h1 := (hasDerivAt_id s).ofReal_comp.smul_const V
    exact h1.congr_deriv (one_smul ℂ V)
  exact ((hasDerivAt_const s H0).add h_lin).congr_deriv (zero_add V)

/-- **General Non-Autonomous Dressed Hamiltonian Evolution Derivative (`hasDerivAt_dressedHamiltonian`)**:
    Along any `IsKatoHastingsFlowSystem P0 D_gen U P` and any differentiable operator path
    $H : \mathbb{R} \to \mathcal{B}(\mathcal{H})$ with derivative $\frac{dH}{ds}(s) = dH(s)$,
    the dressed operator $H_{\mathrm{dressed}}(s) := U(s)^\dagger H(s) U(s)$ has derivative:
    $$\frac{d}{ds}\big(U(s)^\dagger H(s) U(s)\big)
      = U(s)^\dagger \Big( dH(s) + i \, (H(s) \mathcal{D}(s) - \mathcal{D}(s) H(s)) \Big) U(s).$$ -/
theorem hasDerivAt_dressedHamiltonian {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (D_gen U P H dH : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (hH_deriv : ∀ s : ℝ, HasDerivAt H (dH s) s) (s : ℝ) :
    HasDerivAt (fun τ => (U τ)† * H τ * U τ)
      ((U s)† * (dH s + (Complex.I : ℂ) • (H s * D_gen s - D_gen s * H s)) * U s) s := by
  have h_ode := kato_hastings_ode_abstract P0 D_gen U P
    hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P s
  have h_UH : HasDerivAt (fun τ => (U τ)† * H τ)
      ((-(Complex.I : ℂ) • ((U s)† * D_gen s)) * H s + (U s)† * dH s) s :=
    h_ode.1.mul (hH_deriv s)
  have h_UHU := h_UH.mul (hFlow.hasDerivAt_U s)
  have h_alg :
      ((-(Complex.I : ℂ) • ((U s)† * D_gen s)) * H s + (U s)† * dH s) * U s +
        ((U s)† * H s) * ((Complex.I : ℂ) • (D_gen s * U s)) =
      (U s)† * (dH s + (Complex.I : ℂ) • (H s * D_gen s - D_gen s * H s)) * U s := by
    rw [add_mul, clm_smul_mul, clm_smul_mul, clm_mul_smul, neg_smul,
      mul_add ((U s)†), add_mul, mul_smul_comm, smul_mul_assoc,
      mul_sub ((U s)†) (H s * D_gen s) (D_gen s * H s), sub_mul, smul_sub]
    simp only [mul_assoc]
    abel
  rw [h_alg] at h_UHU
  exact h_UHU

end
