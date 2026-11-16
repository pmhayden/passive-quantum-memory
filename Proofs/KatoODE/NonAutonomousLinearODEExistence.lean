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
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Convergent Dyson Propagator Series and Exact Kato Subspace Tracking

Constructs the norm-convergent Dyson iterated-integral series `nonAutonomousPropagator` (`dysonTerm`, `katoEvolvedProjector`, `clampIcc`) solving the non-autonomous linear operator ODE $\dot{U}(s) = i \mathcal{D}(s) U(s)$ on Banach algebras. Instantiates `IsKatoHastingsFlowSystem` for self-adjoint generators and proves exact intertwining $U(s) P_0 U(s)^\dagger = P_{\mathrm{spec}}(s)$ across gapped intervals.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (77) (`eq:rotated-H-block-decomp`)
* Kato (1950), Journal of the Physical Society of Japan 5, 435–439
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Dyson / Picard Iterated Integral Series for $\dot{U}(s) = i \mathcal{D}(s) U(s)$
-/

/-- The $n$-th Dyson iterated integral term $T_n(s)$ for the non-autonomous linear operator ODE
    $\dot{U}(s) = i \mathcal{D}(s) U(s)$ with $T_0(s) = 1$ and
    $T_{n+1}(s) = \int_0^s i \mathcal{D}(\tau) T_n(\tau)\,d\tau$. -/
def dysonTerm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D_gen : ℝ → (E →L[ℂ] E)) : ℕ → ℝ → (E →L[ℂ] E)
  | 0, _ => 1
  | n + 1, s => ∫ τ in (0 : ℝ)..s, (Complex.I : ℂ) • (D_gen τ * dysonTerm D_gen n τ)

/-- Derivative of the $n$-th Dyson term: $T_0'(s) = 0$ and $T_{n+1}'(s) = i \mathcal{D}(s) T_n(s)$. -/
def dysonTermDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D_gen : ℝ → (E →L[ℂ] E)) : ℕ → ℝ → (E →L[ℂ] E)
  | 0, _ => 0
  | n + 1, s => (Complex.I : ℂ) • (D_gen s * dysonTerm D_gen n s)

/-- Global non-autonomous Dyson propagator $U(s) = \sum_{n=0}^\infty T_n(s)$. -/
def nonAutonomousPropagator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D_gen : ℝ → (E →L[ℂ] E)) (s : ℝ) : E →L[ℂ] E :=
  ∑' n : ℕ, dysonTerm D_gen n s

/-- Globally evolved projector family $P(s) = U(s) P_0 U(s)^\dagger$. -/
def katoEvolvedProjector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P0 : E →L[ℂ] E) (U : ℝ → (E →L[ℂ] E)) (s : ℝ) : E →L[ℂ] E :=
  U s * P0 * (U s)†

/-- Continuous clamping map onto $[0, s_{\max}]$: $\mathrm{clampIcc}(s_{\max}, \tau) = \max(0, \min(\tau, s_{\max}))$. -/
def clampIcc (s_max τ : ℝ) : ℝ :=
  max 0 (min τ s_max)

@[simp]
lemma dysonTerm_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D_gen : ℝ → (E →L[ℂ] E)) (s : ℝ) :
    dysonTerm D_gen 0 s = 1 := rfl

@[simp]
lemma dysonTerm_succ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (D_gen : ℝ → (E →L[ℂ] E)) (n : ℕ) (s : ℝ) :
    dysonTerm D_gen (n + 1) s =
      ∫ τ in (0 : ℝ)..s, (Complex.I : ℂ) • (D_gen τ * dysonTerm D_gen n τ) := rfl

@[simp]
lemma dysonTermDeriv_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D_gen : ℝ → (E →L[ℂ] E)) (s : ℝ) :
    dysonTermDeriv D_gen 0 s = 0 := rfl

@[simp]
lemma dysonTermDeriv_succ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D_gen : ℝ → (E →L[ℂ] E)) (n : ℕ) (s : ℝ) :
    dysonTermDeriv D_gen (n + 1) s = (Complex.I : ℂ) • (D_gen s * dysonTerm D_gen n s) := rfl

/-- At $s = 0$, all higher Dyson terms $T_{n+1}(0)$ vanish identically. -/
lemma dysonTerm_succ_eval_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D_gen : ℝ → (E →L[ℂ] E)) (n : ℕ) :
    dysonTerm D_gen (n + 1) 0 = 0 := by
  simp [dysonTerm]

/-- At $s = 0$, the Dyson series has sum $1$ and is summable. -/
lemma hasSum_dysonTerm_eval_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D_gen : ℝ → (E →L[ℂ] E)) :
    HasSum (fun n : ℕ => dysonTerm D_gen n 0) 1 := by
  refine hasSum_single 0 ?_
  intro n hn
  cases n with
  | zero => exact (hn rfl).elim
  | succ m => exact dysonTerm_succ_eval_zero D_gen m

/-- At $s = 0$, the Dyson propagator evaluates to $U(0) = 1$. -/
lemma nonAutonomousPropagator_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (D_gen : ℝ → (E →L[ℂ] E)) :
    nonAutonomousPropagator D_gen 0 = 1 :=
  (hasSum_dysonTerm_eval_zero D_gen).tsum_eq

/-- For a continuous generator family $D_{\mathrm{gen}}$, each Dyson term $T_n$ is globally
    continuous and satisfies $\frac{d}{ds} T_n(s) = \mathrm{dysonTermDeriv}(D_{\mathrm{gen}}, n, s)$. -/
lemma continuous_and_hasDerivAt_dysonTerm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {D_gen : ℝ → (E →L[ℂ] E)} (hD_cont : Continuous D_gen) (n : ℕ) :
    Continuous (dysonTerm D_gen n) ∧
    ∀ s : ℝ, HasDerivAt (dysonTerm D_gen n) (dysonTermDeriv D_gen n s) s := by
  induction n with
  | zero =>
    exact ⟨continuous_const, fun s => hasDerivAt_const s 1⟩
  | succ m ih =>
    have hf_cont : Continuous (fun τ : ℝ => (Complex.I : ℂ) • (D_gen τ * dysonTerm D_gen m τ)) :=
      (hD_cont.mul ih.1).const_smul (Complex.I : ℂ)
    have h_deriv : ∀ s : ℝ,
        HasDerivAt (dysonTerm D_gen (m + 1)) (dysonTermDeriv D_gen (m + 1) s) s := by
      intro s
      exact intervalIntegral.integral_hasDerivAt_right (hf_cont.intervalIntegrable 0 s)
        hf_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hf_cont.continuousAt
    exact ⟨(intervalIntegral.differentiable_integral_of_continuous hf_cont).continuous, h_deriv⟩

/-!
## 2. Factorial Norm Bound and Uniform Convergence on Bounded Intervals
-/

/-- On any symmetric interval $[-R, R]$ where $\|D_{\mathrm{gen}}(\tau)\| \le M$, the $n$-th Dyson
    term satisfies $\|T_n(s)\| \le (M |s|)^n / n!$. -/
lemma norm_dysonTerm_le_pow_div_factorial {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {D_gen : ℝ → (E →L[ℂ] E)} (hD_cont : Continuous D_gen)
    {R M : ℝ} (hM_nonneg : 0 ≤ M)
    (hD_bound : ∀ τ ∈ Set.Icc (-R) R, ‖D_gen τ‖ ≤ M)
    (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (-R) R) :
    ‖dysonTerm D_gen n s‖ ≤ (M * |s|) ^ n / (n.factorial : ℝ) := by
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-R) R := ⟨by linarith [hs.1, hs.2], by linarith [hs.1, hs.2]⟩
  induction n generalizing s with
  | zero =>
    simp only [dysonTerm_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ContinuousLinearMap.norm_id_le
  | succ m ih =>
    rw [dysonTerm_succ, intervalIntegral.norm_intervalIntegral_eq]
    have h_maj_cont : Continuous (fun τ : ℝ => M ^ (m + 1) * |τ - 0| ^ m / (m.factorial : ℝ)) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).abs.pow m)).div_const _
    calc ‖∫ τ in Set.uIoc (0 : ℝ) s, (Complex.I : ℂ) • (D_gen τ * dysonTerm D_gen m τ)‖
      _ ≤ ∫ τ in Set.uIoc (0 : ℝ) s, M ^ (m + 1) * |τ - 0| ^ m / (m.factorial : ℝ) := by
        apply MeasureTheory.norm_integral_le_of_norm_le h_maj_cont.integrableOn_uIoc
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro τ hτ
        have hτ_mem : τ ∈ Set.Icc (-R) R :=
          Set.uIcc_subset_Icc h0_mem hs (Set.uIoc_subset_uIcc hτ)
        have h_norm_I : ‖(Complex.I : ℂ) • (D_gen τ * dysonTerm D_gen m τ)‖ =
            ‖D_gen τ * dysonTerm D_gen m τ‖ := by
          rw [norm_smul, Complex.norm_I, one_mul]
        rw [h_norm_I, sub_zero]
        calc ‖D_gen τ * dysonTerm D_gen m τ‖
          _ ≤ ‖D_gen τ‖ * ‖dysonTerm D_gen m τ‖ := norm_mul_le _ _
          _ ≤ M * ((M * |τ|) ^ m / (m.factorial : ℝ)) :=
            mul_le_mul (hD_bound τ hτ_mem) (ih hτ_mem) (norm_nonneg _) hM_nonneg
          _ = M ^ (m + 1) * |τ| ^ m / (m.factorial : ℝ) := by
            rw [mul_pow]
            ring
      _ = (M * |s|) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
        rw [MeasureTheory.integral_div, MeasureTheory.integral_const_mul,
          integral_pow_abs_sub_uIoc, sub_zero, ← mul_div_assoc, div_div, ← mul_pow,
          Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- Majorant sequence for `dysonTermDeriv D_gen n y` on $[-R, R]$. -/
def dysonDerivMajorant (M R : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => M * ((M * R) ^ n / (n.factorial : ℝ))

/-- The majorant sequence `dysonDerivMajorant M R` is summable for all $M, R \in \mathbb{R}$. -/
lemma summable_dysonDerivMajorant (M R : ℝ) :
    Summable (dysonDerivMajorant M R) := by
  rw [← summable_nat_add_iff 1]
  exact (Real.summable_pow_div_factorial (M * R)).mul_left M

/-- On $(-R, R)$, `‖dysonTermDeriv D_gen n y‖` is bounded by `dysonDerivMajorant M R n`. -/
lemma norm_dysonTermDeriv_le_majorant {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {D_gen : ℝ → (E →L[ℂ] E)} (hD_cont : Continuous D_gen)
    {R M : ℝ} (_hR_pos : 0 ≤ R) (hM_nonneg : 0 ≤ M)
    (hD_bound : ∀ τ ∈ Set.Icc (-R) R, ‖D_gen τ‖ ≤ M)
    (n : ℕ) {y : ℝ} (hy : y ∈ Set.Ioo (-R) R) :
    ‖dysonTermDeriv D_gen n y‖ ≤ dysonDerivMajorant M R n := by
  have hy_Icc : y ∈ Set.Icc (-R) R := Set.Ioo_subset_Icc_self hy
  have hy_abs : |y| ≤ R := abs_le.mpr ⟨hy_Icc.1, hy_Icc.2⟩
  cases n with
  | zero =>
    simp only [dysonTermDeriv_zero, dysonDerivMajorant, norm_zero, le_refl]
  | succ m =>
    simp only [dysonTermDeriv_succ, dysonDerivMajorant]
    rw [norm_smul, Complex.norm_I, one_mul]
    have h_pow : (M * |y|) ^ m ≤ (M * R) ^ m :=
      pow_le_pow_left₀ (mul_nonneg hM_nonneg (abs_nonneg y))
        (mul_le_mul_of_nonneg_left hy_abs hM_nonneg) m
    calc ‖D_gen y * dysonTerm D_gen m y‖
      _ ≤ ‖D_gen y‖ * ‖dysonTerm D_gen m y‖ := norm_mul_le _ _
      _ ≤ M * ((M * |y|) ^ m / (m.factorial : ℝ)) :=
        mul_le_mul (hD_bound y hy_Icc)
          (norm_dysonTerm_le_pow_div_factorial hD_cont hM_nonneg hD_bound m hy_Icc)
          (norm_nonneg _) hM_nonneg
      _ ≤ M * ((M * R) ^ m / (m.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right h_pow (Nat.cast_nonneg m.factorial)) hM_nonneg

/-- At every $s \in \mathbb{R}$, the Dyson series `fun n => dysonTerm D_gen n s` is summable. -/
lemma summable_dysonTerm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {D_gen : ℝ → (E →L[ℂ] E)} (hD_cont : Continuous D_gen) (s : ℝ) :
    Summable (fun n : ℕ => dysonTerm D_gen n s) := by
  let R : ℝ := |s| + 1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-R) R) hD_cont.continuousOn
  let M : ℝ := max C 0
  have hM_nonneg : 0 ≤ M := le_max_right C 0
  have hD_bound : ∀ τ ∈ Set.Icc (-R) R, ‖D_gen τ‖ ≤ M := fun τ hτ =>
    le_trans (hC τ hτ) (le_max_left C 0)
  have hs_mem : s ∈ Set.Icc (-R) R := by
    refine ⟨?_, ?_⟩ <;> linarith [abs_nonneg s, le_abs_self s, neg_le_abs s]
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial (M * |s|)) (fun n => ?_)
  exact norm_dysonTerm_le_pow_div_factorial hD_cont hM_nonneg hD_bound n hs_mem

/-- At every $s \in \mathbb{R}$, the derivative series `fun n => dysonTermDeriv D_gen n s` is summable
    and sums to `(Complex.I : ℂ) • (D_gen s * nonAutonomousPropagator D_gen s)`. -/
lemma tsum_dysonTermDeriv_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {D_gen : ℝ → (E →L[ℂ] E)} (hD_cont : Continuous D_gen) (s : ℝ) :
    (∑' n : ℕ, dysonTermDeriv D_gen n s) =
      (Complex.I : ℂ) • (D_gen s * nonAutonomousPropagator D_gen s) := by
  have h_sum_T : Summable (fun n : ℕ => dysonTerm D_gen n s) := summable_dysonTerm hD_cont s
  let L_op : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.compL ℂ E E E ((Complex.I : ℂ) • D_gen s)
  have h_succ_eq : ∀ n : ℕ, dysonTermDeriv D_gen (n + 1) s = L_op (dysonTerm D_gen n s) := by
    intro n
    simp only [dysonTermDeriv_succ, L_op, ContinuousLinearMap.compL_apply]
    change (Complex.I : ℂ) • (D_gen s * dysonTerm D_gen n s) =
      ((Complex.I : ℂ) • D_gen s) * dysonTerm D_gen n s
    rw [clm_smul_mul]
  have h_sum_succ : Summable (fun n : ℕ => dysonTermDeriv D_gen (n + 1) s) := by
    simp_rw [h_succ_eq]
    exact L_op.summable h_sum_T
  have h_sum_deriv : Summable (fun n : ℕ => dysonTermDeriv D_gen n s) :=
    (summable_nat_add_iff 1).mp h_sum_succ
  rw [h_sum_deriv.tsum_eq_zero_add, dysonTermDeriv_zero, zero_add]
  simp_rw [h_succ_eq]
  rw [← L_op.map_tsum h_sum_T]
  change (((Complex.I : ℂ) • D_gen s) * nonAutonomousPropagator D_gen s) =
    (Complex.I : ℂ) • (D_gen s * nonAutonomousPropagator D_gen s)
  rw [clm_smul_mul]

/-- The Dyson propagator `nonAutonomousPropagator D_gen` satisfies the global linear operator ODE
    $\frac{d}{ds} U(s) = i \mathcal{D}(s) U(s)$ for all $s \in \mathbb{R}$. -/
theorem hasDerivAt_nonAutonomousPropagator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {D_gen : ℝ → (E →L[ℂ] E)} (hD_cont : Continuous D_gen) (s : ℝ) :
    HasDerivAt (nonAutonomousPropagator D_gen)
      ((Complex.I : ℂ) • (D_gen s * nonAutonomousPropagator D_gen s)) s := by
  let R : ℝ := |s| + 1
  have hR_pos : 0 ≤ R := by positivity
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-R) R) hD_cont.continuousOn
  let M : ℝ := max C 0
  have hM_nonneg : 0 ≤ M := le_max_right C 0
  have hD_bound : ∀ τ ∈ Set.Icc (-R) R, ‖D_gen τ‖ ≤ M := fun τ hτ =>
    le_trans (hC τ hτ) (le_max_left C 0)
  have h0_mem : (0 : ℝ) ∈ Set.Ioo (-R) R := by
    refine ⟨?_, ?_⟩ <;> linarith [abs_nonneg s]
  have hs_mem : s ∈ Set.Ioo (-R) R := by
    refine ⟨?_, ?_⟩ <;> linarith [le_abs_self s, neg_le_abs s]
  have h_tsum := hasDerivAt_tsum_of_isPreconnected
    (hu := summable_dysonDerivMajorant M R)
    (ht := isOpen_Ioo)
    (h't := isPreconnected_Ioo)
    (hg := fun n y _ => (continuous_and_hasDerivAt_dysonTerm hD_cont n).2 y)
    (hg' := fun n y hy => norm_dysonTermDeriv_le_majorant hD_cont hR_pos hM_nonneg hD_bound n hy)
    (hy₀ := h0_mem)
    (hg0 := (hasSum_dysonTerm_eval_zero D_gen).summable)
    (hy := hs_mem)
  rwa [tsum_dysonTermDeriv_eq hD_cont s] at h_tsum

/-- **Global Existence of the Non-Autonomous Linear Operator ODE**:
    For any complete complex Hilbert space $E$ and any continuous operator family
    $D_{\mathrm{gen}} : \mathbb{R} \to (E \to_L[\mathbb{C}] E)$, there exists a global propagator
    $U : \mathbb{R} \to (E \to_L[\mathbb{C}] E)$ with $U(0) = 1$ and
    $\dot{U}(s) = i D_{\mathrm{gen}}(s) U(s)$ for all $s \in \mathbb{R}$. -/
theorem exists_nonAutonomous_linear_ode_solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (D_gen : ℝ → (E →L[ℂ] E)) (hD_cont : Continuous D_gen) :
    ∃ U : ℝ → (E →L[ℂ] E),
      U 0 = 1 ∧
      ∀ s : ℝ, HasDerivAt U ((Complex.I : ℂ) • (D_gen s * U s)) s :=
  ⟨nonAutonomousPropagator D_gen,
   nonAutonomousPropagator_zero D_gen,
   hasDerivAt_nonAutonomousPropagator hD_cont⟩

/-!
## 3. Global Instantiation of `IsKatoHastingsFlowSystem` and Subspace Intertwining on $[0, s]$
-/

/-- Algebraic identity for the derivative of $U(s) P_0 U(s)^\dagger$. -/
lemma alg_evolved_projector_deriv {R : Type*} [Ring R] [Module ℂ R]
    [SMulCommClass ℂ R R] [IsScalarTower ℂ R R] (D A P0 B : R) :
    (((Complex.I : ℂ) • (D * A)) * P0) * B + (A * P0) * (-(Complex.I : ℂ) • (B * D)) =
    (Complex.I : ℂ) • (D * (A * P0 * B) - (A * P0 * B) * D) := by
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, neg_smul, ← sub_eq_add_neg, ← smul_sub]
  congr 1
  simp only [mul_assoc]

/-- For any solution $U$ of $\dot{U}(s) = i D_{\mathrm{gen}}(s) U(s)$ with $U(0) = 1$ and
    self-adjoint $D_{\mathrm{gen}}(s)$, the globally evolved projector
    $P(s) = U(s) P_0 U(s)^\dagger$ satisfies $P(0) = P_0$ and
    $\dot{P}(s) = i [D_{\mathrm{gen}}(s), P(s)]$ for all $s \in \mathbb{R}$. -/
lemma hasDerivAt_katoEvolvedProjector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P0 : E →L[ℂ] E) {D_gen U : ℝ → (E →L[ℂ] E)}
    (hD_sa : ∀ s : ℝ, IsSelfAdjoint (D_gen s))
    (hU0 : U 0 = 1)
    (hU_deriv : ∀ s : ℝ, HasDerivAt U ((Complex.I : ℂ) • (D_gen s * U s)) s) :
    katoEvolvedProjector P0 U 0 = P0 ∧
    ∀ s : ℝ, HasDerivAt (katoEvolvedProjector P0 U)
      ((Complex.I : ℂ) •
        (D_gen s * katoEvolvedProjector P0 U s - katoEvolvedProjector P0 U s * D_gen s)) s := by
  refine ⟨?_, ?_⟩
  · simp only [katoEvolvedProjector, hU0]
    change (1 : E →L[ℂ] E) * P0 * star (1 : E →L[ℂ] E) = P0
    rw [star_one, one_mul, mul_one]
  · intro s
    have hU_adj : HasDerivAt (fun τ => (U τ)†) (-(Complex.I : ℂ) • ((U s)† * D_gen s)) s := by
      have h1 : HasDerivAt (fun τ => star (U τ)) (star ((Complex.I : ℂ) • (D_gen s * U s))) s :=
        (hU_deriv s).star
      have h2 : star ((Complex.I : ℂ) • (D_gen s * U s)) =
          -(Complex.I : ℂ) • ((U s)† * D_gen s) := by
        rw [star_smul, star_mul, (hD_sa s).star_eq, RCLike.star_def, Complex.conj_I]
        rfl
      rwa [h2] at h1
    have hUP0 : HasDerivAt (fun τ => U τ * P0) (((Complex.I : ℂ) • (D_gen s * U s)) * P0) s :=
      ((hU_deriv s).mul (hasDerivAt_const s P0)).congr_deriv (by rw [mul_zero, add_zero])
    have h_prod := hUP0.mul hU_adj
    rw [alg_evolved_projector_deriv (D_gen s) (U s) P0 ((U s)†)] at h_prod
    exact h_prod

/-- **Global `IsKatoHastingsFlowSystem` Existence for Any Continuous Self-Adjoint Generator Family**:
    Given any continuous self-adjoint generator family $D_{\mathrm{gen}} : \mathbb{R} \to \mathcal{B}(\mathcal{H})$,
    there exist global operator families $U_{\mathrm{flow}}, P_{\mathrm{flow}}$ satisfying
    `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow` and
    $P_{\mathrm{flow}}(s) = U_{\mathrm{flow}}(s) P_0 U_{\mathrm{flow}}(s)^\dagger$ for all $s \in \mathbb{R}$. -/
theorem exists_isKatoHastingsFlowSystem_of_continuous_selfAdjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (D_gen : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hD_cont : Continuous D_gen)
    (hD_sa : ∀ s : ℝ, IsSelfAdjoint (D_gen s)) :
    ∃ (U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)),
      IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow ∧
      ∀ s : ℝ, P_flow s = U_flow s * P0 * (U_flow s)† := by
  let U_flow := nonAutonomousPropagator D_gen
  let P_flow := katoEvolvedProjector P0 U_flow
  have hU0 : U_flow 0 = 1 := nonAutonomousPropagator_zero D_gen
  have hU_deriv : ∀ s : ℝ, HasDerivAt U_flow ((Complex.I : ℂ) • (D_gen s * U_flow s)) s :=
    hasDerivAt_nonAutonomousPropagator hD_cont
  obtain ⟨hP0, hP_deriv⟩ := hasDerivAt_katoEvolvedProjector P0 hD_sa hU0 hU_deriv
  exact ⟨U_flow, P_flow,
    { isSelfAdjoint_D := hD_sa
      U_zero := hU0
      P_zero := hP0
      hasDerivAt_U := hU_deriv
      hasDerivAt_P := hP_deriv },
    fun _ => rfl⟩

/-- **Subspace Intertwining on Gapped Interval `[0, s]` via `HasDerivWithinAt`**:
    If `P_spec 0 = P0` and `P_spec` satisfies `HasDerivWithinAt P_spec (i [D_gen τ, P_spec τ]) (Set.Icc 0 s) τ`
    for all $\tau \in [0, s]$, then $(U_{\mathrm{flow}}(s))^\dagger P_{\mathrm{spec}}(s) U_{\mathrm{flow}}(s) = P_0$
    and $P_{\mathrm{flow}}(s) = U_{\mathrm{flow}}(s) P_0 (U_{\mathrm{flow}}(s))^\dagger = P_{\mathrm{spec}}(s)$. -/
theorem katoFlow_intertwines_spectralProj_on_Icc_of_hasDerivWithinAt {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow)
    (P_spec : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hP_spec_zero : P_spec 0 = P0)
    {s : ℝ} (hs : 0 ≤ s)
    (hP_spec_deriv : ∀ τ ∈ Set.Icc 0 s,
      HasDerivWithinAt P_spec
        ((Complex.I : ℂ) • (D_gen τ * P_spec τ - P_spec τ * D_gen τ)) (Set.Icc 0 s) τ) :
    (U_flow s)† * P_spec s * U_flow s = P0 ∧
    U_flow s * P0 * (U_flow s)† = P_spec s ∧
    P_flow s = P_spec s := by
  let g : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun τ => (U_flow τ)† * P_spec τ * U_flow τ
  have hg_deriv : ∀ τ ∈ Set.Icc 0 s, HasDerivWithinAt g 0 (Set.Icc 0 s) τ := by
    intro τ hτ
    have h_abs := kato_hastings_ode_abstract P0 D_gen U_flow P_flow
      hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P τ
    have hU_adj_w : HasDerivWithinAt (fun u => (U_flow u)†)
        (-(Complex.I : ℂ) • ((U_flow τ)† * D_gen τ)) (Set.Icc 0 s) τ :=
      h_abs.1.hasDerivWithinAt
    have hU_w : HasDerivWithinAt U_flow
        ((Complex.I : ℂ) • (D_gen τ * U_flow τ)) (Set.Icc 0 s) τ :=
      (hFlow.hasDerivAt_U τ).hasDerivWithinAt
    have h_UP : HasDerivWithinAt (fun u => (U_flow u)† * P_spec u)
        (-(Complex.I : ℂ) • ((U_flow τ)† * P_spec τ * D_gen τ)) (Set.Icc 0 s) τ := by
      have h_prod := hU_adj_w.mul (hP_spec_deriv τ hτ)
      rw [alg_up_deriv_simp ((U_flow τ)†) (D_gen τ) (P_spec τ)] at h_prod
      exact h_prod
    have h_UPU := h_UP.mul hU_w
    rw [alg_upu_deriv_cancel ((U_flow τ)†) (P_spec τ) (D_gen τ) (U_flow τ)] at h_UPU
    exact h_UPU
  have h0_mem : (0 : ℝ) ∈ Set.Icc 0 s := ⟨le_refl 0, hs⟩
  have hs_mem : s ∈ Set.Icc 0 s := ⟨hs, le_refl s⟩
  have h_norm_le : ‖g s - g 0‖ ≤ (0 : ℝ) * ‖s - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg_deriv
      (fun _ _ => by rw [norm_zero]) (convex_Icc 0 s) h0_mem hs_mem
  rw [zero_mul] at h_norm_le
  have hg_eq : g s = g 0 := sub_eq_zero.mp (norm_le_zero_iff.mp h_norm_le)
  have hg0 : g 0 = P0 := by
    simp only [g, hFlow.U_zero, hP_spec_zero]
    change star (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) * P0 * 1 = P0
    rw [star_one, one_mul, mul_one]
  have h_align1 : (U_flow s)† * P_spec s * U_flow s = P0 := hg_eq.trans hg0
  have h_abs_s := kato_hastings_ode_abstract P0 D_gen U_flow P_flow
    hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P s
  have h_align2 : U_flow s * P0 * (U_flow s)† = P_spec s :=
    monoid_align2 h_abs_s.2.2.1 h_align1
  have hP_flow_eq : P_flow s = P_spec s := h_abs_s.2.2.2.2.1.symm.trans h_align2
  exact ⟨h_align1, h_align2, hP_flow_eq⟩

/-- **Subspace Intertwining on Gapped Interval `[0, s]` via Mean Value Theorem**:
    If `P_spec 0 = P0` and `P_spec` satisfies `HasDerivAt P_spec (i [D_gen τ, P_spec τ]) τ`
    for all $\tau \in [0, s]$, then $(U_{\mathrm{flow}}(s))^\dagger P_{\mathrm{spec}}(s) U_{\mathrm{flow}}(s) = P_0$,
    $U_{\mathrm{flow}}(s) P_0 (U_{\mathrm{flow}}(s))^\dagger = P_{\mathrm{spec}}(s)$, and
    $P_{\mathrm{flow}}(s) = P_{\mathrm{spec}}(s)$. -/
theorem katoFlow_intertwines_spectralProj_on_Icc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow)
    (P_spec : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hP_spec_zero : P_spec 0 = P0)
    {s : ℝ} (hs : 0 ≤ s)
    (hP_spec_deriv : ∀ τ ∈ Set.Icc 0 s,
      HasDerivAt P_spec ((Complex.I : ℂ) • (D_gen τ * P_spec τ - P_spec τ * D_gen τ)) τ) :
    (U_flow s)† * P_spec s * U_flow s = P0 ∧
    U_flow s * P0 * (U_flow s)† = P_spec s ∧
    P_flow s = P_spec s :=
  katoFlow_intertwines_spectralProj_on_Icc_of_hasDerivWithinAt hFlow P_spec hP_spec_zero hs
    (fun τ hτ => (hP_spec_deriv τ hτ).hasDerivWithinAt)

/-- Properties of `clampIcc s_max`: continuity, range in `Set.Icc 0 s_max`, and identity on `Set.Icc 0 s_max`. -/
lemma clampIcc_properties {s_max : ℝ} (hs_max : 0 ≤ s_max) :
    Continuous (clampIcc s_max) ∧
    (∀ τ : ℝ, clampIcc s_max τ ∈ Set.Icc 0 s_max) ∧
    (∀ τ ∈ Set.Icc 0 s_max, clampIcc s_max τ = τ) := by
  refine ⟨continuous_const.max (continuous_id.min continuous_const), ?_, ?_⟩
  · intro τ
    simp only [clampIcc, Set.mem_Icc, le_max_iff, max_le_iff, min_le_iff]
    exact ⟨Or.inl (le_refl 0), hs_max, Or.inr (le_refl s_max)⟩
  · intro τ hτ
    simp only [clampIcc]
    rw [min_eq_left hτ.2, max_eq_right hτ.1]

/-- **Clamped Interval Instantiation of `IsKatoHastingsFlowSystem`**:
    If $D_0$ is continuous and self-adjoint on $[0, s_{\max}]$ ($0 \le s_{\max}$), then clamping
    $D_{\mathrm{gen}}(\tau) := D_0(\mathrm{clampIcc}(s_{\max}, \tau))$ yields a globally valid
    `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow` that agrees with $D_0$ on $[0, s_{\max}]$
    and intertwines any projector family $P_{\mathrm{spec}}$ satisfying the Kato commutator ODE on $[0, s_{\max}]$. -/
theorem exists_clamped_isKatoHastingsFlowSystem_on_Icc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (D_0 : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {s_max : ℝ} (hs_max : 0 ≤ s_max)
    (hD0_cont : ContinuousOn D_0 (Set.Icc 0 s_max))
    (hD0_sa : ∀ τ ∈ Set.Icc 0 s_max, IsSelfAdjoint (D_0 τ)) :
    let D_gen := fun τ : ℝ => D_0 (clampIcc s_max τ)
    ∃ (U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)),
      IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow ∧
      (∀ τ ∈ Set.Icc 0 s_max, D_gen τ = D_0 τ) ∧
      (∀ s : ℝ, P_flow s = U_flow s * P0 * (U_flow s)†) := by
  obtain ⟨hcl_cont, hcl_mem, hcl_id⟩ := clampIcc_properties hs_max
  let D_gen := fun τ : ℝ => D_0 (clampIcc s_max τ)
  have hD_cont : Continuous D_gen := hD0_cont.comp_continuous hcl_cont hcl_mem
  have hD_sa : ∀ s : ℝ, IsSelfAdjoint (D_gen s) := fun s => hD0_sa (clampIcc s_max s) (hcl_mem s)
  obtain ⟨U_flow, P_flow, hFlow, hP_eq⟩ :=
    exists_isKatoHastingsFlowSystem_of_continuous_selfAdjoint P0 D_gen hD_cont hD_sa
  exact ⟨U_flow, P_flow, hFlow, fun τ hτ => congrArg D_0 (hcl_id τ hτ), hP_eq⟩

end
