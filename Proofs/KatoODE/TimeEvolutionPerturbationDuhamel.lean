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

import Proofs.HastingsKomaLightCone.PerturbedSpectralLowPassBridge
import Proofs.KatoHastingsFlow.CanonicalQACFlowPackage

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Perturbative Duhamel Derivatives of Heisenberg Evolution and Projectors

Proves perturbative Duhamel finite-difference bounds and coupling-parameter derivatives for `timeEvolutionOp` and `heisenbergFlow` along $H_0 + s V$ (`norm_heisenbergFlow_sub_le_of_isSelfAdjoint`). Derives the Duhamel integral representation `projector_deriv_eq_heisenbergFlow_add_duhamel_integral` for derivatives of Hamiltonian-commuting projector curves.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (68) (`eq:wBP-WBP-ibp`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (75) (`eq:qac-generator-def`), Proposition 6.4 (`prop:qac-block-diagonalization`)
-/

/-! ## 1. Right/Subtracted Time Derivatives of `timeEvolutionOp` -/

/-- Time derivative of `timeEvolutionOp H t` with $H$ on the right: $\frac{d}{dt} U_H(t) = i U_H(t) H$. -/
lemma hasDerivAt_timeEvolutionOp_right {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    HasDerivAt (timeEvolutionOp H) ((Complex.I : ℂ) • (timeEvolutionOp H t * H)) t := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  have h1 := _root_.hasDerivAt_exp_smul_const (𝕂 := ℝ) ((Complex.I : ℂ) • H) t
  have h_fn : (fun u : ℝ => NormedSpace.exp (u • ((Complex.I : ℂ) • H))) = timeEvolutionOp H := by
    funext u; dsimp [timeEvolutionOp]; congr 1; rw [clm_real_smul, smul_smul, mul_comm]
  rw [h_fn] at h1
  refine h1.congr_deriv ?_
  have h_t : t • ((Complex.I : ℂ) • H) = (Complex.I * (t : ℂ)) • H := by
    rw [clm_real_smul, smul_smul, mul_comm]
  rw [h_t, clm_mul_smul_comm]; rfl

/-- Continuity of `u ↦ timeEvolutionOp H u`. -/
lemma continuous_timeEvolutionOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Continuous (timeEvolutionOp H) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_timeEvolutionOp H t).continuousAt

/-- Derivative of $\tau \mapsto \mathrm{timeEvolutionOp}\ B\ (t - \tau)$ with $B$ on the left. -/
lemma hasDerivAt_timeEvolutionOp_sub_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t τ : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp B (t - u))
      ((-Complex.I : ℂ) • (B * timeEvolutionOp B (t - τ))) τ := by
  have h_sub : HasDerivAt (fun u : ℝ => t - u) (-1 : ℝ) τ := by
    have h0 : HasDerivAt (fun u : ℝ => t - u) ((0 : ℝ) - 1) τ :=
      HasDerivAt.sub (hasDerivAt_const τ t) (hasDerivAt_id τ)
    norm_num at h0
    exact h0
  refine ((hasDerivAt_timeEvolutionOp B (t - τ)).scomp τ h_sub).congr_deriv ?_
  rw [clm_real_smul, smul_smul]; congr 1; push_cast; ring

/-- Derivative of $\tau \mapsto \mathrm{timeEvolutionOp}\ B\ (\tau - t)$ with $B$ on the right. -/
lemma hasDerivAt_timeEvolutionOp_sub_const_right {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t τ : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp B (u - t))
      ((Complex.I : ℂ) • (timeEvolutionOp B (τ - t) * B)) τ := by
  have h_sub : HasDerivAt (fun u : ℝ => u - t) (1 : ℝ) τ := by
    simpa using (hasDerivAt_id τ).sub_const t
  refine ((hasDerivAt_timeEvolutionOp_right B (τ - t)).scomp τ h_sub).congr_deriv ?_
  rw [one_smul]

/-- Derivative of $\tau \mapsto \mathrm{timeEvolutionOp}\ A\ (-\tau)$ with $A$ on the left. -/
lemma hasDerivAt_timeEvolutionOp_neg_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (τ : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp A (-u))
      ((-Complex.I : ℂ) • (A * timeEvolutionOp A (-τ))) τ := by
  have h_neg : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) τ := (hasDerivAt_id τ).neg
  refine ((hasDerivAt_timeEvolutionOp A (-τ)).scomp τ h_neg).congr_deriv ?_
  rw [clm_real_smul, smul_smul]; congr 1; push_cast; ring

/-! ## 2. Duhamel Finite-Difference Identity for `timeEvolutionOp` -/

/-- Derivative of the Duhamel interpolation product $u \mapsto U_A(u) U_B(t - u)$. -/
lemma hasDerivAt_duhamel_timeEvolutionOp_product {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t τ : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp A u * timeEvolutionOp B (t - u))
      ((Complex.I : ℂ) • (timeEvolutionOp A τ * (A - B) * timeEvolutionOp B (t - τ))) τ := by
  refine ((hasDerivAt_timeEvolutionOp_right A τ).mul
    (hasDerivAt_timeEvolutionOp_sub_left B t τ)).congr_deriv ?_
  rw [clm_smul_mul_assoc, clm_mul_smul_comm, clm_neg_smul, ← sub_eq_add_neg]
  simp only [mul_sub, sub_mul, smul_sub, mul_assoc]

/-- **Duhamel Finite-Difference Identity for `timeEvolutionOp`**:
    $U_B(t) - U_A(t) = i \int_0^t U_A(\tau) (B - A) U_B(t - \tau)\,d\tau$. -/
theorem timeEvolutionOp_sub_eq_duhamel_intervalIntegral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    timeEvolutionOp B t - timeEvolutionOp A t =
      (Complex.I : ℂ) •
        ∫ τ in (0 : ℝ)..t, timeEvolutionOp A τ * (B - A) * timeEvolutionOp B (t - τ) := by
  let Φ := fun u : ℝ => timeEvolutionOp A u * timeEvolutionOp B (t - u)
  let Φ' := fun u : ℝ => (Complex.I : ℂ) • (timeEvolutionOp A u * (A - B) * timeEvolutionOp B (t - u))
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t, HasDerivAt Φ (Φ' u) u :=
    fun u _ => hasDerivAt_duhamel_timeEvolutionOp_product A B t u
  have hcont : Continuous Φ' :=
    ((((continuous_timeEvolutionOp A).mul continuous_const).mul
      ((continuous_timeEvolutionOp B).comp (continuous_const.sub continuous_id)))).const_smul (Complex.I : ℂ)
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  have h_t : Φ t = timeEvolutionOp A t := by dsimp [Φ]; rw [sub_self, timeEvolutionOp_zero, mul_one]
  have h_0 : Φ 0 = timeEvolutionOp B t := by dsimp [Φ]; rw [sub_zero, timeEvolutionOp_zero, one_mul]
  rw [h_t, h_0] at h_ftc
  have h_neg : timeEvolutionOp B t - timeEvolutionOp A t = - (∫ τ in (0 : ℝ)..t, Φ' τ) := by
    rw [h_ftc, neg_sub]
  rw [h_neg]; dsimp [Φ']
  rw [intervalIntegral.integral_smul, ← smul_neg, ← intervalIntegral.integral_neg]
  congr 1; refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [mul_sub, sub_mul, mul_sub, sub_mul, neg_sub]

/-- Lipschitz norm bound for `timeEvolutionOp B t - timeEvolutionOp A t` for self-adjoint $A, B$. -/
theorem norm_timeEvolutionOp_sub_le_of_isSelfAdjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (t : ℝ) :
    ‖timeEvolutionOp B t - timeEvolutionOp A t‖ ≤ |t| * ‖B - A‖ := by
  rw [timeEvolutionOp_sub_eq_duhamel_intervalIntegral A B t, norm_smul, Complex.norm_I, one_mul]
  have h_bound : ∀ τ ∈ Set.uIoc (0 : ℝ) t,
      ‖timeEvolutionOp A τ * (B - A) * timeEvolutionOp B (t - τ)‖ ≤ ‖B - A‖ := fun τ _ =>
    norm_sandwich_le_of_norm_le_one (timeEvolutionOp_adjoint_and_norm_le_one hA τ).2
      (timeEvolutionOp_adjoint_and_norm_le_one hB (t - τ)).2
  have h_int := intervalIntegral.norm_integral_le_of_norm_le_const h_bound
  rw [sub_zero] at h_int; linarith

/-! ## 3. Quadratic-Remainder Criterion & Duhamel Derivative of `timeEvolutionOp (H s) t` -/

/-- General calculus criterion: $\|f(s) - f(s_0) - (s - s_0) f'\| \le C |s - s_0|^2$ implies `HasDerivAt`. -/
lemma hasDerivAt_of_norm_sub_le_sq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {s₀ C : ℝ} (_hC : 0 ≤ C)
    (h_est : ∀ s : ℝ, ‖f s - f s₀ - (s - s₀) • f'‖ ≤ C * |s - s₀| * |s - s₀|) :
    HasDerivAt f f' s₀ := by
  rw [hasDerivAt_iff_tendsto]
  have h_upper : ∀ s : ℝ, ‖s - s₀‖⁻¹ * ‖f s - f s₀ - (s - s₀) • f'‖ ≤ C * |s - s₀| := by
    intro s; rw [Real.norm_eq_abs]
    by_cases hs : |s - s₀| = 0
    · rw [hs, inv_zero, zero_mul, mul_zero]
    · have hs_pos : 0 < |s - s₀| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hs)
      calc |s - s₀|⁻¹ * ‖f s - f s₀ - (s - s₀) • f'‖
        _ ≤ |s - s₀|⁻¹ * (C * |s - s₀| * |s - s₀|) :=
          mul_le_mul_of_nonneg_left (h_est s) (inv_nonneg.mpr (le_of_lt hs_pos))
        _ = C * |s - s₀| := by
          rw [mul_comm (C * |s - s₀|) |s - s₀|, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  have h_tendsto_upper : Tendsto (fun s : ℝ => C * |s - s₀|) (𝓝 s₀) (𝓝 0) := by
    have h_cont : Continuous (fun s : ℝ => C * |s - s₀|) :=
      continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))
    have h_val : C * |s₀ - s₀| = 0 := by rw [sub_self, abs_zero, mul_zero]
    simpa [h_val] using h_cont.tendsto s₀
  exact squeeze_zero (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    h_upper h_tendsto_upper

/-- If $\tau \in \mathrm{Set.uIoc}\ (0 : \mathbb{R})\ t$, then $|t - \tau| \le |t|$. -/
lemma abs_sub_le_abs_of_mem_uIoc_zero {t τ : ℝ} (hτ : τ ∈ Set.uIoc (0 : ℝ) t) :
    |t - τ| ≤ |t| := by
  rcases Set.mem_uIoc.mp hτ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- **Perturbative Duhamel Derivative of `timeEvolutionOp (H0 + (s : ℂ) • V) t`**. -/
theorem hasDerivAt_timeEvolutionOp_interpolated {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 V : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH0 : IsSelfAdjoint H0) (hV : IsSelfAdjoint V) (s₀ t : ℝ) :
    let H := fun s : ℝ => H0 + (s : ℂ) • V
    HasDerivAt (fun s : ℝ => timeEvolutionOp (H s) t)
      ((Complex.I : ℂ) •
        ∫ τ in (0 : ℝ)..t, timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s₀) (t - τ)) s₀ := by
  intro H
  let I_0 := ∫ τ in (0 : ℝ)..t, timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s₀) (t - τ)
  refine hasDerivAt_of_norm_sub_le_sq (C := (|t| * ‖V‖) ^ 2) (sq_nonneg _) (fun s => ?_)
  have hHs₀ : IsSelfAdjoint (H s₀) := isSelfAdjoint_interpolatedHamiltonian hH0 hV s₀
  have hHs : IsSelfAdjoint (H s) := isSelfAdjoint_interpolatedHamiltonian hH0 hV s
  have h_diff_H : H s - H s₀ = (s - s₀) • V := by
    dsimp [H]; rw [add_sub_add_left_eq_sub, ← clm_real_smul, ← clm_real_smul]
    exact (sub_smul s s₀ V).symm
  have h_duh := timeEvolutionOp_sub_eq_duhamel_intervalIntegral (H s₀) (H s) t
  rw [h_diff_H] at h_duh
  have h_pull : (∫ τ in (0 : ℝ)..t,
      timeEvolutionOp (H s₀) τ * ((s - s₀) • V) * timeEvolutionOp (H s) (t - τ)) =
      (s - s₀) • ∫ τ in (0 : ℝ)..t,
        timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s) (t - τ) := by
    have h_congr : (fun τ : ℝ =>
        timeEvolutionOp (H s₀) τ * ((s - s₀) • V) * timeEvolutionOp (H s) (t - τ)) =
        (fun τ : ℝ => (s - s₀) •
          (timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s) (t - τ))) := by
      funext τ; rw [clm_real_smul, clm_real_smul, clm_mul_smul_comm, clm_smul_mul_assoc]
    rw [h_congr, intervalIntegral.integral_smul]
  rw [h_pull] at h_duh
  have h_rem_eq :
      timeEvolutionOp (H s) t - timeEvolutionOp (H s₀) t - (s - s₀) • ((Complex.I : ℂ) • I_0) =
        (s - s₀) • (Complex.I : ℂ) •
          ((∫ τ in (0 : ℝ)..t, timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s) (t - τ)) -
            I_0) := by
    rw [h_duh, smul_comm (Complex.I : ℂ) (s - s₀)]; simp only [smul_sub]
  have h_cont1 : Continuous (fun τ : ℝ =>
      timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s) (t - τ)) :=
    ((continuous_timeEvolutionOp (H s₀)).mul continuous_const).mul
      ((continuous_timeEvolutionOp (H s)).comp (continuous_const.sub continuous_id))
  have h_cont0 : Continuous (fun τ : ℝ =>
      timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s₀) (t - τ)) :=
    ((continuous_timeEvolutionOp (H s₀)).mul continuous_const).mul
      ((continuous_timeEvolutionOp (H s₀)).comp (continuous_const.sub continuous_id))
  have h_int_sub :
      (∫ τ in (0 : ℝ)..t, timeEvolutionOp (H s₀) τ * V * timeEvolutionOp (H s) (t - τ)) - I_0 =
        ∫ τ in (0 : ℝ)..t, timeEvolutionOp (H s₀) τ * V *
          (timeEvolutionOp (H s) (t - τ) - timeEvolutionOp (H s₀) (t - τ)) := by
    dsimp [I_0]
    rw [← intervalIntegral.integral_sub (h_cont1.intervalIntegrable _ _)
      (h_cont0.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun τ _ => (mul_sub _ _ _).symm
  rw [h_rem_eq, h_int_sub, norm_smul, Real.norm_eq_abs, norm_smul, Complex.norm_I, one_mul]
  have h_integrand_le : ∀ τ ∈ Set.uIoc (0 : ℝ) t,
      ‖timeEvolutionOp (H s₀) τ * V *
        (timeEvolutionOp (H s) (t - τ) - timeEvolutionOp (H s₀) (t - τ))‖ ≤
        |t| * ‖V‖ ^ 2 * |s - s₀| := by
    intro τ hτ
    have hU0 : ‖timeEvolutionOp (H s₀) τ‖ ≤ 1 :=
      (timeEvolutionOp_adjoint_and_norm_le_one hHs₀ τ).2
    have h_diff_U : ‖timeEvolutionOp (H s) (t - τ) - timeEvolutionOp (H s₀) (t - τ)‖ ≤
        |t| * (|s - s₀| * ‖V‖) := by
      calc ‖timeEvolutionOp (H s) (t - τ) - timeEvolutionOp (H s₀) (t - τ)‖
        _ ≤ |t - τ| * ‖H s - H s₀‖ := norm_timeEvolutionOp_sub_le_of_isSelfAdjoint hHs₀ hHs (t - τ)
        _ ≤ |t| * ‖(s - s₀) • V‖ := by
          rw [h_diff_H]
          exact mul_le_mul_of_nonneg_right (abs_sub_le_abs_of_mem_uIoc_zero hτ) (norm_nonneg _)
        _ = |t| * (|s - s₀| * ‖V‖) := by rw [norm_smul, Real.norm_eq_abs]
    calc ‖timeEvolutionOp (H s₀) τ * V *
          (timeEvolutionOp (H s) (t - τ) - timeEvolutionOp (H s₀) (t - τ))‖
      _ ≤ ‖timeEvolutionOp (H s₀) τ * V‖ *
          ‖timeEvolutionOp (H s) (t - τ) - timeEvolutionOp (H s₀) (t - τ)‖ := norm_mul_le _ _
      _ ≤ (1 * ‖V‖) * (|t| * (|s - s₀| * ‖V‖)) := by
        refine mul_le_mul ?_ h_diff_U (norm_nonneg _) (by positivity)
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hU0 (norm_nonneg _))
      _ = |t| * ‖V‖ ^ 2 * |s - s₀| := by ring
  have h_int_norm := intervalIntegral.norm_integral_le_of_norm_le_const h_integrand_le
  rw [sub_zero] at h_int_norm
  calc |s - s₀| * ‖∫ τ in (0 : ℝ)..t, timeEvolutionOp (H s₀) τ * V *
        (timeEvolutionOp (H s) (t - τ) - timeEvolutionOp (H s₀) (t - τ))‖
    _ ≤ |s - s₀| * (|t| * ‖V‖ ^ 2 * |s - s₀| * |t|) :=
      mul_le_mul_of_nonneg_left h_int_norm (abs_nonneg _)
    _ = (|t| * ‖V‖) ^ 2 * |s - s₀| * |s - s₀| := by ring

/-! ## 4. Duhamel Finite-Difference & Derivative for `heisenbergFlow` -/

/-- Derivative of the right-hand Duhamel factor $u \mapsto U_B(u - t) U_A(-u)$. -/
lemma hasDerivAt_duhamel_timeEvolutionOp_right_product {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t τ : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp B (u - t) * timeEvolutionOp A (-u))
      ((-Complex.I : ℂ) • (timeEvolutionOp B (τ - t) * (A - B) * timeEvolutionOp A (-τ))) τ := by
  refine ((hasDerivAt_timeEvolutionOp_sub_const_right B t τ).mul
    (hasDerivAt_timeEvolutionOp_neg_left A τ)).congr_deriv ?_
  rw [clm_smul_mul_assoc, clm_mul_smul_comm, clm_neg_smul, clm_neg_smul, ← sub_eq_add_neg]
  simp only [mul_sub, sub_mul, smul_sub, mul_assoc]; abel

/-- Derivative of the Heisenberg Duhamel interpolation $u \mapsto \tau_u^A(\tau_{t - u}^B(X))$. -/
lemma hasDerivAt_duhamel_heisenbergFlow_comp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t τ : ℝ) :
    HasDerivAt (fun u : ℝ => heisenbergFlow A u (heisenbergFlow B (t - u) X))
      ((Complex.I : ℂ) • heisenbergFlow A τ
        ((A - B) * heisenbergFlow B (t - τ) X - heisenbergFlow B (t - τ) X * (A - B))) τ := by
  have h_fn : (fun u : ℝ => heisenbergFlow A u (heisenbergFlow B (t - u) X)) =
      (fun u : ℝ => (timeEvolutionOp A u * timeEvolutionOp B (t - u)) * X *
        (timeEvolutionOp B (u - t) * timeEvolutionOp A (-u))) := by
    funext u; dsimp [heisenbergFlow]
    have h_neg : -(t - u) = u - t := by ring
    rw [h_neg]; simp only [mul_assoc]
  rw [h_fn]
  have dL := hasDerivAt_duhamel_timeEvolutionOp_product A B t τ
  have dR := hasDerivAt_duhamel_timeEvolutionOp_right_product A B t τ
  refine (((dL.mul (hasDerivAt_const τ X)).mul dR)).congr_deriv ?_
  simp only [mul_zero, add_zero]; dsimp [heisenbergFlow]
  have h_neg : -(t - τ) = τ - t := by ring
  rw [h_neg, clm_smul_mul_assoc, clm_smul_mul_assoc, clm_mul_smul_comm,
    clm_neg_smul, ← sub_eq_add_neg]
  simp only [mul_sub, sub_mul, smul_sub, mul_assoc]

/-- **Duhamel Finite-Difference Identity for `heisenbergFlow`**. -/
theorem heisenbergFlow_sub_eq_duhamel_intervalIntegral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    heisenbergFlow B t X - heisenbergFlow A t X =
      ∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) • heisenbergFlow A τ
        ((B - A) * heisenbergFlow B (t - τ) X - heisenbergFlow B (t - τ) X * (B - A)) := by
  let Ψ := fun u : ℝ => heisenbergFlow A u (heisenbergFlow B (t - u) X)
  let Ψ' := fun u : ℝ => (Complex.I : ℂ) • heisenbergFlow A u
    ((A - B) * heisenbergFlow B (t - u) X - heisenbergFlow B (t - u) X * (A - B))
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t, HasDerivAt Ψ (Ψ' u) u :=
    fun u _ => hasDerivAt_duhamel_heisenbergFlow_comp A B X t u
  have hcont_B : Continuous (fun u : ℝ => heisenbergFlow B (t - u) X) :=
    (continuous_heisenbergFlow B X).comp (continuous_const.sub continuous_id)
  have hcont_comm : Continuous (fun u : ℝ =>
      (A - B) * heisenbergFlow B (t - u) X - heisenbergFlow B (t - u) X * (A - B)) :=
    (continuous_const.mul hcont_B).sub (hcont_B.mul continuous_const)
  have hcont : Continuous Ψ' :=
    ((((continuous_timeEvolutionOp A).mul hcont_comm).mul
      ((continuous_timeEvolutionOp A).comp continuous_neg))).const_smul (Complex.I : ℂ)
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)
  have h_t : Ψ t = heisenbergFlow A t X := by
    dsimp [Ψ, heisenbergFlow]; rw [sub_self, neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  have h_0 : Ψ 0 = heisenbergFlow B t X := by
    dsimp [Ψ, heisenbergFlow]; rw [sub_zero, neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  rw [h_t, h_0] at h_ftc
  have h_neg : heisenbergFlow B t X - heisenbergFlow A t X = - (∫ τ in (0 : ℝ)..t, Ψ' τ) := by
    rw [h_ftc, neg_sub]
  rw [h_neg, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  dsimp [Ψ', heisenbergFlow]; simp only [mul_sub, sub_mul, smul_sub, mul_assoc]; abel

/-- Lipschitz norm bound for `heisenbergFlow B t X - heisenbergFlow A t X` for self-adjoint $A, B$. -/
theorem norm_heisenbergFlow_sub_le_of_isSelfAdjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    ‖heisenbergFlow B t X - heisenbergFlow A t X‖ ≤ 2 * |t| * ‖B - A‖ * ‖X‖ := by
  rw [heisenbergFlow_sub_eq_duhamel_intervalIntegral A B X t]
  have h_bound : ∀ τ ∈ Set.uIoc (0 : ℝ) t,
      ‖(Complex.I : ℂ) • heisenbergFlow A τ
        ((B - A) * heisenbergFlow B (t - τ) X - heisenbergFlow B (t - τ) X * (B - A))‖ ≤
        2 * ‖B - A‖ * ‖X‖ := by
    intro τ _; rw [norm_smul, Complex.norm_I, one_mul]
    calc ‖heisenbergFlow A τ
          ((B - A) * heisenbergFlow B (t - τ) X - heisenbergFlow B (t - τ) X * (B - A))‖
      _ ≤ ‖(B - A) * heisenbergFlow B (t - τ) X - heisenbergFlow B (t - τ) X * (B - A)‖ :=
        norm_heisenbergFlow_le hA τ _
      _ ≤ 2 * ‖B - A‖ * ‖heisenbergFlow B (t - τ) X‖ :=
        norm_opCommutator_le (B - A) (heisenbergFlow B (t - τ) X)
      _ ≤ 2 * ‖B - A‖ * ‖X‖ :=
        mul_le_mul_of_nonneg_left (norm_heisenbergFlow_le hB (t - τ) X) (by positivity)
  have h_int := intervalIntegral.norm_integral_le_of_norm_le_const h_bound
  rw [sub_zero] at h_int; linarith

/-- If `Commute H P`, then `heisenbergFlow H t P = P` for all $t \in \mathbb{R}$. -/
theorem heisenbergFlow_eq_self_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : Commute H P) (t : ℝ) :
    heisenbergFlow H t P = P := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  have h_smul : Commute ((Complex.I * (t : ℂ)) • H) P := by
    rw [commute_iff_eq, clm_smul_mul_assoc, clm_mul_smul_comm, h_comm.eq]
  have h_exp : Commute (timeEvolutionOp H t) P := h_smul.exp_left
  unfold heisenbergFlow
  rw [h_exp.eq, mul_assoc, (timeEvolutionOp_mul_neg H t).1, mul_one]

/-- **Duhamel Derivative of `s ↦ heisenbergFlow (H0 + (s : ℂ) • V) t P_s₀` when `Commute (H s₀) P_s₀`**. -/
theorem hasDerivAt_heisenbergFlow_interpolated_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 V P_s₀ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH0 : IsSelfAdjoint H0) (hV : IsSelfAdjoint V) (s₀ t : ℝ)
    (h_comm : Commute (H0 + (s₀ : ℂ) • V) P_s₀) :
    let H := fun s : ℝ => H0 + (s : ℂ) • V
    HasDerivAt (fun s : ℝ => heisenbergFlow (H s) t P_s₀)
      (∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) •
        (heisenbergFlow (H s₀) τ V * P_s₀ - P_s₀ * heisenbergFlow (H s₀) τ V)) s₀ := by
  intro H
  let J_0 := ∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) •
    (heisenbergFlow (H s₀) τ V * P_s₀ - P_s₀ * heisenbergFlow (H s₀) τ V)
  refine hasDerivAt_of_norm_sub_le_sq
    (C := 4 * |t| ^ 2 * ‖V‖ ^ 2 * ‖P_s₀‖) (by positivity) (fun s => ?_)
  have hHs₀ : IsSelfAdjoint (H s₀) := isSelfAdjoint_interpolatedHamiltonian hH0 hV s₀
  have hHs : IsSelfAdjoint (H s) := isSelfAdjoint_interpolatedHamiltonian hH0 hV s
  have h_diff_H : H s - H s₀ = (s - s₀) • V := by
    dsimp [H]; rw [add_sub_add_left_eq_sub, ← clm_real_smul, ← clm_real_smul]
    exact (sub_smul s s₀ V).symm
  have h_duh := heisenbergFlow_sub_eq_duhamel_intervalIntegral (H s₀) (H s) P_s₀ t
  rw [h_diff_H] at h_duh
  have h_pull :
      (∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
        (((s - s₀) • V) * heisenbergFlow (H s) (t - τ) P_s₀ -
          heisenbergFlow (H s) (t - τ) P_s₀ * ((s - s₀) • V))) =
      (s - s₀) • ∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
        (V * heisenbergFlow (H s) (t - τ) P_s₀ - heisenbergFlow (H s) (t - τ) P_s₀ * V) := by
    have h_congr :
        (fun τ : ℝ => (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
          (((s - s₀) • V) * heisenbergFlow (H s) (t - τ) P_s₀ -
            heisenbergFlow (H s) (t - τ) P_s₀ * ((s - s₀) • V))) =
        (fun τ : ℝ => (s - s₀) • ((Complex.I : ℂ) • heisenbergFlow (H s₀) τ
          (V * heisenbergFlow (H s) (t - τ) P_s₀ - heisenbergFlow (H s) (t - τ) P_s₀ * V))) := by
      funext τ; dsimp [heisenbergFlow]
      simp only [clm_real_smul, clm_smul_mul_assoc, clm_mul_smul_comm, mul_sub, sub_mul,
        smul_sub, smul_comm (Complex.I : ℂ)]
    rw [h_congr, intervalIntegral.integral_smul]
  rw [h_pull] at h_duh
  have h_integrand0 : ∀ τ : ℝ,
      (Complex.I : ℂ) • (heisenbergFlow (H s₀) τ V * P_s₀ - P_s₀ * heisenbergFlow (H s₀) τ V) =
        (Complex.I : ℂ) • heisenbergFlow (H s₀) τ (V * P_s₀ - P_s₀ * V) := by
    intro τ; congr 1
    have hP_inv := heisenbergFlow_eq_self_of_commute h_comm τ
    have h_sub_flow : heisenbergFlow (H s₀) τ (V * P_s₀ - P_s₀ * V) =
        heisenbergFlow (H s₀) τ (V * P_s₀) - heisenbergFlow (H s₀) τ (P_s₀ * V) := by
      dsimp [heisenbergFlow]; rw [mul_sub, sub_mul]
    rw [h_sub_flow, heisenbergFlow_mul, heisenbergFlow_mul, hP_inv]
  have hJ0_eq : J_0 = ∫ τ in (0 : ℝ)..t,
      (Complex.I : ℂ) • heisenbergFlow (H s₀) τ (V * P_s₀ - P_s₀ * V) :=
    intervalIntegral.integral_congr fun τ _ => h_integrand0 τ
  have hcont_P : Continuous (fun τ : ℝ => heisenbergFlow (H s) (t - τ) P_s₀) :=
    (continuous_heisenbergFlow (H s) P_s₀).comp (continuous_const.sub continuous_id)
  have hcont_comm1 : Continuous (fun τ : ℝ =>
      V * heisenbergFlow (H s) (t - τ) P_s₀ - heisenbergFlow (H s) (t - τ) P_s₀ * V) :=
    (continuous_const.mul hcont_P).sub (hcont_P.mul continuous_const)
  have hcont1 : Continuous (fun τ : ℝ => (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
      (V * heisenbergFlow (H s) (t - τ) P_s₀ - heisenbergFlow (H s) (t - τ) P_s₀ * V)) :=
    ((((continuous_timeEvolutionOp (H s₀)).mul hcont_comm1).mul
      ((continuous_timeEvolutionOp (H s₀)).comp continuous_neg))).const_smul (Complex.I : ℂ)
  have hcont0 : Continuous (fun τ : ℝ =>
      (Complex.I : ℂ) • heisenbergFlow (H s₀) τ (V * P_s₀ - P_s₀ * V)) :=
    (continuous_heisenbergFlow (H s₀) (V * P_s₀ - P_s₀ * V)).const_smul (Complex.I : ℂ)
  have h_int_diff :
      (∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
        (V * heisenbergFlow (H s) (t - τ) P_s₀ - heisenbergFlow (H s) (t - τ) P_s₀ * V)) - J_0 =
      ∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
        (V * (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) -
          (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) * V) := by
    rw [hJ0_eq, ← intervalIntegral.integral_sub (hcont1.intervalIntegrable _ _)
      (hcont0.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    dsimp [heisenbergFlow]; simp only [mul_sub, sub_mul, smul_sub, mul_assoc]; abel
  have h_rem_eq :
      heisenbergFlow (H s) t P_s₀ - heisenbergFlow (H s₀) t P_s₀ - (s - s₀) • J_0 =
        (s - s₀) • ∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
          (V * (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) -
            (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) * V) := by
    rw [h_duh, ← h_int_diff]; simp only [smul_sub]
  rw [h_rem_eq, norm_smul, Real.norm_eq_abs]
  have h_integrand_le : ∀ τ ∈ Set.uIoc (0 : ℝ) t,
      ‖(Complex.I : ℂ) • heisenbergFlow (H s₀) τ
        (V * (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) -
          (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) * V)‖ ≤
        4 * |t| * ‖V‖ ^ 2 * ‖P_s₀‖ * |s - s₀| := by
    intro τ hτ; rw [norm_smul, Complex.norm_I, one_mul]
    have hP0_eq := heisenbergFlow_eq_self_of_commute h_comm (t - τ)
    have h_diff_P :
        ‖heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀‖ ≤ 2 * |t| * (|s - s₀| * ‖V‖) * ‖P_s₀‖ := by
      calc ‖heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀‖
        _ = ‖heisenbergFlow (H s) (t - τ) P_s₀ - heisenbergFlow (H s₀) (t - τ) P_s₀‖ := by
          rw [hP0_eq]
        _ ≤ 2 * |t - τ| * ‖H s - H s₀‖ * ‖P_s₀‖ :=
          norm_heisenbergFlow_sub_le_of_isSelfAdjoint hHs₀ hHs P_s₀ (t - τ)
        _ ≤ 2 * |t| * ‖(s - s₀) • V‖ * ‖P_s₀‖ := by
          rw [h_diff_H]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (abs_sub_le_abs_of_mem_uIoc_zero hτ) (by positivity))
            (norm_nonneg _)) (norm_nonneg _)
        _ = 2 * |t| * (|s - s₀| * ‖V‖) * ‖P_s₀‖ := by rw [norm_smul, Real.norm_eq_abs]
    calc ‖heisenbergFlow (H s₀) τ
          (V * (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) -
            (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) * V)‖
      _ ≤ ‖V * (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) -
            (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) * V‖ := norm_heisenbergFlow_le hHs₀ τ _
      _ ≤ 2 * ‖V‖ * ‖heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀‖ := norm_opCommutator_le V _
      _ ≤ 2 * ‖V‖ * (2 * |t| * (|s - s₀| * ‖V‖) * ‖P_s₀‖) :=
        mul_le_mul_of_nonneg_left h_diff_P (by positivity)
      _ = 4 * |t| * ‖V‖ ^ 2 * ‖P_s₀‖ * |s - s₀| := by ring
  have h_int_norm := intervalIntegral.norm_integral_le_of_norm_le_const h_integrand_le
  rw [sub_zero] at h_int_norm
  calc |s - s₀| * ‖∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) • heisenbergFlow (H s₀) τ
        (V * (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) -
          (heisenbergFlow (H s) (t - τ) P_s₀ - P_s₀) * V)‖
    _ ≤ |s - s₀| * (4 * |t| * ‖V‖ ^ 2 * ‖P_s₀‖ * |s - s₀| * |t|) :=
      mul_le_mul_of_nonneg_left h_int_norm (abs_nonneg _)
    _ = 4 * |t| ^ 2 * ‖V‖ ^ 2 * ‖P_s₀‖ * |s - s₀| * |s - s₀| := by ring

/-! ## 5. Projector Derivative Off-Diagonal Identity & Duhamel Decomposition -/

/-- Differentiating $P(s)^2 = P(s)$ at $s_0$ yields `twoBlockOffDiagProj (P s₀) P_deriv = P_deriv`. -/
theorem twoBlockOffDiagProj_eq_self_of_hasDerivAt_idem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : ℝ → (E →L[ℂ] E)} {P_deriv : E →L[ℂ] E} {s₀ : ℝ}
    (hP_idem : ∀ s : ℝ, P s * P s = P s) (hP_deriv : HasDerivAt P P_deriv s₀) :
    twoBlockOffDiagProj (P s₀) P_deriv = P_deriv := by
  have h_off := (proj_hasDerivAt_offDiag_id P hP_idem hP_deriv).2.2.2.1
  unfold twoBlockOffDiagProj; rw [add_comm]; exact h_off.symm

/-- **Time-Dependent Duhamel Decomposition of the Projector Derivative**:
    For any differentiable family $P : \mathbb{R} \to (E \to_L[\mathbb{C}] E)$ of idempotents commuting
    with $H(s) = H_0 + s V$, `twoBlockOffDiagProj (P s₀) P_deriv = P_deriv` and
    $P_{\mathrm{deriv}} = \tau_t^{H(s_0)}(P_{\mathrm{deriv}}) + \int_0^t i [\tau_\tau^{H(s_0)}(V), P(s_0)]\,d\tau$. -/
theorem projector_deriv_eq_heisenbergFlow_add_duhamel_integral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 V : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH0 : IsSelfAdjoint H0) (hV : IsSelfAdjoint V)
    {P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    {P_deriv : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {s₀ : ℝ}
    (hP_idem : ∀ s : ℝ, P s * P s = P s)
    (h_comm : ∀ s : ℝ, Commute (H0 + (s : ℂ) • V) (P s))
    (hP_deriv : HasDerivAt P P_deriv s₀) :
    let H := fun s : ℝ => H0 + (s : ℂ) • V
    twoBlockOffDiagProj (P s₀) P_deriv = P_deriv ∧
    ∀ t : ℝ,
      P_deriv = heisenbergFlow (H s₀) t P_deriv +
        ∫ τ in (0 : ℝ)..t, (Complex.I : ℂ) •
          (heisenbergFlow (H s₀) τ V * P s₀ - P s₀ * heisenbergFlow (H s₀) τ V) := by
  intro H
  refine ⟨twoBlockOffDiagProj_eq_self_of_hasDerivAt_idem hP_idem hP_deriv, fun t => ?_⟩
  have dU_pos := hasDerivAt_timeEvolutionOp_interpolated hH0 hV s₀ t
  have dU_neg := hasDerivAt_timeEvolutionOp_interpolated hH0 hV s₀ (-t)
  have dQ : HasDerivAt (fun s : ℝ => P s - P s₀) P_deriv s₀ := by
    simpa using hP_deriv.sub_const (P s₀)
  have d_first : HasDerivAt
      (fun s : ℝ => timeEvolutionOp (H s) t * (P s - P s₀) * timeEvolutionOp (H s) (-t))
      (heisenbergFlow (H s₀) t P_deriv) s₀ := by
    have d123 := (dU_pos.mul dQ).mul dU_neg
    change HasDerivAt
      (fun s : ℝ => timeEvolutionOp (H s) t * (P s - P s₀) * timeEvolutionOp (H s) (-t)) _ s₀ at d123
    refine d123.congr_deriv ?_
    simp only [Pi.mul_apply, sub_self, mul_zero, zero_mul, add_zero, zero_add]; rfl
  have d_second := hasDerivAt_heisenbergFlow_interpolated_of_commute hH0 hV s₀ t (h_comm s₀)
  have d_sum := d_first.add d_second
  have h_sum_eq_P :
      ((fun s : ℝ => timeEvolutionOp (H s) t * (P s - P s₀) * timeEvolutionOp (H s) (-t)) +
        (fun s : ℝ => heisenbergFlow (H s) t (P s₀))) = P := by
    funext s; dsimp only [Pi.add_apply, heisenbergFlow]
    rw [mul_sub, sub_mul, sub_add_cancel]
    exact heisenbergFlow_eq_self_of_commute (h_comm s) t
  rw [h_sum_eq_P] at d_sum
  exact hP_deriv.unique d_sum

end
