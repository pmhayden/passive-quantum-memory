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

import Proofs.SpacetimeWorldlineKP.SpectralBoltzmannDuhamelIdentity

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SpacetimeWorldlineKP

/-!
# Scalar Divided-Difference Integral and Dimension-Free Boltzmann Duhamel Identities

Expresses the scalar exponential divided difference `dividedExpDiff` as a Euclidean interval integral (`dividedExpDiff_eq_intervalIntegral`). Lifts the cross-eigenbasis spectral identity to dimension-free trace and operator Duhamel formulas for `gibbsBoltzmannOp` (`hilbertTrace_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral`, `hilbertTrace_mul_gibbsBoltzmannOp_shift_eq_diag_sub_duhamel_integral`).

## References

* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.1 (`lem:duhamel-weyl-ratio`)
-/

/-! ## 1. 1D Real Interval-Integral Representation of `dividedExpDiff` -/

/-- **Exponent Rearrangement for the Duhamel Kernel (`duhamel_exp_mul_eq_exp_linear`)**:
    For all $\beta, \lambda, \mu, s \in \mathbb{R}$,
    $$\exp(-(\beta - s)\lambda) \exp(-s \mu) = \exp(-\beta \lambda + (\lambda - \mu) s).$$ -/
theorem duhamel_exp_mul_eq_exp_linear (β lam μ s : ℝ) :
    Real.exp (-(β - s) * lam) * Real.exp (-s * μ) =
      Real.exp (-β * lam + (lam - μ) * s) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **Continuity and Interval Integrability of the Scalar Duhamel Kernel
    (`continuous_duhamel_exp_kernel` & `intervalIntegrable_duhamel_exp_kernel`)** -/
theorem continuous_duhamel_exp_kernel (β lam μ : ℝ) :
    Continuous (fun s : ℝ => Real.exp (-(β - s) * lam) * Real.exp (-s * μ)) := by
  fun_prop

theorem intervalIntegrable_duhamel_exp_kernel (β lam μ a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.exp (-(β - s) * lam) * Real.exp (-s * μ))
      MeasureTheory.volume a b :=
  (continuous_duhamel_exp_kernel β lam μ).intervalIntegrable a b

/-- **Antiderivative of the Scalar Duhamel Kernel for $\lambda \ne \mu$
    (`hasDerivAt_duhamel_antideriv`)** -/
theorem hasDerivAt_duhamel_antideriv (β lam μ s : ℝ) (h_ne : lam ≠ μ) :
    HasDerivAt
      (fun t : ℝ => Real.exp (-β * lam + (lam - μ) * t) / (lam - μ))
      (Real.exp (-(β - s) * lam) * Real.exp (-s * μ)) s := by
  have h_sub_ne : lam - μ ≠ 0 := sub_ne_zero.mpr h_ne
  have h_lin : HasDerivAt (fun t : ℝ => -β * lam + (lam - μ) * t) (0 + (lam - μ) * 1) s :=
    (hasDerivAt_const s (-β * lam)).add ((hasDerivAt_id s).const_mul (lam - μ))
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (-β * lam + (lam - μ) * t))
      (Real.exp (-β * lam + (lam - μ) * s) * (0 + (lam - μ) * 1)) s :=
    h_lin.exp
  have h_div := h_exp.div_const (lam - μ)
  have h_deriv_eq :
      (Real.exp (-β * lam + (lam - μ) * s) * (0 + (lam - μ) * 1)) / (lam - μ) =
        Real.exp (-(β - s) * lam) * Real.exp (-s * μ) := by
    rw [zero_add, mul_one, mul_div_cancel_right₀ _ h_sub_ne, duhamel_exp_mul_eq_exp_linear]
  rwa [h_deriv_eq] at h_div

/-- **1D Scalar Interval-Integral Representation of `dividedExpDiff`
    (`dividedExpDiff_eq_intervalIntegral`)**:
    For all $\beta, \lambda, \mu \in \mathbb{R}$,
    $$\mathrm{dividedExpDiff}(\beta, \lambda, \mu)
      = \int_0^\beta \exp(-(\beta - s)\lambda) \exp(-s \mu)\,ds.$$ -/
theorem dividedExpDiff_eq_intervalIntegral (β lam μ : ℝ) :
    dividedExpDiff β lam μ =
      ∫ s in (0 : ℝ)..β, Real.exp (-(β - s) * lam) * Real.exp (-s * μ) := by
  unfold dividedExpDiff
  split_ifs with h_eq
  · subst h_eq
    have h_const : ∀ s : ℝ,
        Real.exp (-(β - s) * lam) * Real.exp (-s * lam) = Real.exp (-β * lam) := by
      intro s
      rw [duhamel_exp_mul_eq_exp_linear, sub_self, zero_mul, add_zero]
    simp_rw [h_const]
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  · symm
    have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Real.exp (-β * lam + (lam - μ) * t) / (lam - μ))
      (f' := fun s : ℝ => Real.exp (-(β - s) * lam) * Real.exp (-s * μ))
      (fun s _ => hasDerivAt_duhamel_antideriv β lam μ s h_eq)
      (intervalIntegrable_duhamel_exp_kernel β lam μ 0 β)
    rw [h_ftc]
    (try dsimp only)
    have h_top : -β * lam + (lam - μ) * β = -β * μ := by ring
    have h_bot : -β * lam + (lam - μ) * 0 = -β * lam := by ring
    rw [h_top, h_bot, sub_div]

/-! ## 2. Cross-Eigenbasis & General Inner-Product Duhamel Integral Identities -/

/-- **Cross-Eigenbasis Matrix Element of the Sandwiched Boltzmann Integrand
    (`inner_eigenbasis_boltzmann_sandwiched_eq`)**:
    For eigenstates $\phi_\alpha = \mathrm{opEigenbasis}\;H_0\;hH_0\;\alpha$ and
    $\psi_\omega = \mathrm{opEigenbasis}\;H\;hH\;\omega$ at any Euclidean time $s \in \mathbb{R}$,
    $$\bigl\langle \phi_\alpha, \bigl(B_{H_0}(\beta - s) * (H - H_0) * B_H(s)\bigr) \psi_\omega \bigr\rangle
      = \bigl(\exp(-(\beta - s)\lambda_\alpha) \exp(-s E_\omega) : \mathbb{C}\bigr) \,
        \langle \phi_\alpha, (H - H_0) \psi_\omega \rangle.$$ -/
theorem inner_eigenbasis_boltzmann_sandwiched_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H)
    (β s : ℝ) (α ω : ManyBodyConfig Site) :
    let φ := opEigenbasis H0 hH0
    let lam := opEigenvalues H0 hH0
    let ψ := opEigenbasis H hH
    let E := opEigenvalues H hH
    inner ℂ (φ α)
      ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) (ψ ω)) =
      (((Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω) : ℝ) : ℂ) *
        inner ℂ (φ α) ((H - H0) (ψ ω))) := by
  intro φ lam ψ E
  have h_apply_H :
      gibbsBoltzmannOp ψ E s (ψ ω) = (Real.exp (-s * E ω) : ℂ) • (ψ ω) :=
    perturbed_gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector
      H hH (opEigenbasis_apply_H H hH ω) s
  have h_in_B0 : ∀ χ : ManyBodyHilbertSpace Site,
      inner ℂ (φ α) (gibbsBoltzmannOp φ lam (β - s) χ) =
        (Real.exp (-(β - s) * lam α) : ℂ) * inner ℂ (φ α) χ := by
    intro χ
    unfold gibbsBoltzmannOp
    rw [ContinuousLinearMap.sum_apply, inner_sum, Finset.sum_eq_single α]
    · rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
        inner_smul_right, opEigenbasis_orthonormal H0 hH0 α α, if_pos rfl, mul_one]
    · intro α' _ hne
      rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
        inner_smul_right, opEigenbasis_orthonormal H0 hH0 α α',
        if_neg (Ne.symm hne), mul_zero, mul_zero]
    · intro h_not
      exact False.elim (h_not (Finset.mem_univ α))
  change inner ℂ (φ α)
    (gibbsBoltzmannOp φ lam (β - s) ((H - H0) (gibbsBoltzmannOp ψ E s (ψ ω)))) = _
  rw [h_apply_H, map_smul, h_in_B0, inner_smul_right, Complex.ofReal_mul]
  ring

/-- **Cross-Eigenbasis Real Inner-Product Duhamel Integral Identity
    (`re_inner_eigenbasis_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral`)**:
    For any basis indices $\alpha, \omega$,
    $$\operatorname{Re}\bigl\langle \phi_\alpha, \bigl(B_H(\beta) - B_{H_0}(\beta)\bigr) \psi_\omega \bigr\rangle
      = -\int_0^\beta \operatorname{Re}\bigl\langle \phi_\alpha,
        \bigl(B_{H_0}(\beta - s) * (H - H_0) * B_H(s)\bigr) \psi_\omega \bigr\rangle\,ds.$$ -/
theorem re_inner_eigenbasis_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H)
    (β : ℝ) (α ω : ManyBodyConfig Site) :
    let φ := opEigenbasis H0 hH0
    let lam := opEigenvalues H0 hH0
    let ψ := opEigenbasis H hH
    let E := opEigenvalues H hH
    RCLike.re (inner ℂ (φ α)
      ((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) (ψ ω))) =
      -∫ s in (0 : ℝ)..β,
        RCLike.re (inner ℂ (φ α)
          ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) (ψ ω))) := by
  intro φ lam ψ E
  have h_mat := spectral_boltzmann_duhamel_matrix_element_eq H0 H hH0 hH β α ω
  (try dsimp only at h_mat)
  rw [h_mat, neg_mul, map_neg, re_ofReal_mul]
  have h_integrand : ∀ s : ℝ,
      RCLike.re (inner ℂ (φ α)
        ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) (ψ ω))) =
      (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) *
        RCLike.re (inner ℂ (φ α) ((H - H0) (ψ ω))) := by
    intro s
    have h_s := inner_eigenbasis_boltzmann_sandwiched_eq H0 H hH0 hH β s α ω
    (try dsimp only at h_s)
    rw [h_s, re_ofReal_mul]
  simp_rw [h_integrand]
  rw [intervalIntegral.integral_mul_const, ← dividedExpDiff_eq_intervalIntegral]

private lemma eq_sum_opEigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (χ : ManyBodyHilbertSpace Site) :
    χ = ∑ ω : ManyBodyConfig Site,
      inner ℂ (opEigenbasis H hH ω) χ • opEigenbasis H hH ω := by
  have h_id := onb_sum_ketBra_eq_one (opEigenbasis H hH)
    (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
  calc χ = (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) χ := rfl
    _ = (∑ ω : ManyBodyConfig Site, rankOneKetBra (opEigenbasis H hH ω)) χ := by rw [← h_id]
    _ = ∑ ω : ManyBodyConfig Site, inner ℂ (opEigenbasis H hH ω) χ • opEigenbasis H hH ω := by
        rw [ContinuousLinearMap.sum_apply]
        simp_rw [rankOneKetBra_apply]

private lemma re_inner_eq_sum_opEigenbasis_matrix_elements {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H T : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H)
    (χ₁ χ₂ : ManyBodyHilbertSpace Site) :
    let φ := opEigenbasis H0 hH0
    let ψ := opEigenbasis H hH
    RCLike.re (inner ℂ χ₁ (T χ₂)) =
      ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
        RCLike.re ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
          inner ℂ (φ α) (T (ψ ω))) := by
  intro φ ψ
  have h_expand :
      inner ℂ χ₁ (T χ₂) =
        ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          (starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
            inner ℂ (φ α) (T (ψ ω)) := by
    calc inner ℂ χ₁ (T χ₂)
      _ = inner ℂ (∑ α : ManyBodyConfig Site, inner ℂ (φ α) χ₁ • φ α)
            (T (∑ ω : ManyBodyConfig Site, inner ℂ (ψ ω) χ₂ • ψ ω)) :=
          congrArg₂ (inner ℂ) (eq_sum_opEigenbasis H0 hH0 χ₁)
            (congrArg T (eq_sum_opEigenbasis H hH χ₂))
      _ = ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
            (starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
              inner ℂ (φ α) (T (ψ ω)) := by
          rw [map_sum, sum_inner]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [inner_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [map_smul, inner_smul_left, inner_smul_right, mul_assoc]
  rw [h_expand, map_sum]
  refine Finset.sum_congr rfl fun α _ => map_sum _ _ _

/-- **General Vector Inner-Product Boltzmann Duhamel Integral Identity
    (`inner_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral`)**:
    Expanding arbitrary vectors $\chi_1, \chi_2 \in \mathrm{ManyBodyHilbertSpace}\;\mathrm{Site}$
    in the orthonormal eigenbases $\phi_\alpha$ of $H_0$ and $\psi_\omega$ of $H$ and pulling the
    finite sum $\sum_{\alpha, \omega}$ inside the 1D scalar `intervalIntegral` yields:
    $$\operatorname{Re}\bigl\langle \chi_1, \bigl(B_H(\beta) - B_{H_0}(\beta)\bigr) \chi_2 \bigr\rangle
      = -\int_0^\beta \operatorname{Re}\bigl\langle \chi_1,
        \bigl(B_{H_0}(\beta - s) * (H - H_0) * B_H(s)\bigr) \chi_2 \bigr\rangle\,ds$$
    and show that the integrand is `IntervalIntegrable` on $[0, \beta]$. -/
theorem inner_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H)
    (β : ℝ) (χ₁ χ₂ : ManyBodyHilbertSpace Site) :
    let φ := opEigenbasis H0 hH0
    let lam := opEigenvalues H0 hH0
    let ψ := opEigenbasis H hH
    let E := opEigenvalues H hH
    IntervalIntegrable
      (fun s : ℝ =>
        RCLike.re (inner ℂ χ₁
          ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) χ₂)))
      MeasureTheory.volume 0 β ∧
    RCLike.re (inner ℂ χ₁
      ((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) χ₂)) =
      -∫ s in (0 : ℝ)..β,
        RCLike.re (inner ℂ χ₁
          ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) χ₂)) := by
  intro φ lam ψ E
  let w : ManyBodyConfig Site → ManyBodyConfig Site → ℝ := fun α ω =>
    RCLike.re ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
      inner ℂ (φ α) ((H - H0) (ψ ω)))
  have h_integrand_eq : ∀ s : ℝ,
      RCLike.re (inner ℂ χ₁
        ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) χ₂)) =
      ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
        (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω := by
    intro s
    rw [re_inner_eq_sum_opEigenbasis_matrix_elements H0 H
      (gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) hH0 hH χ₁ χ₂]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun ω _ => ?_
    have h_s := inner_eigenbasis_boltzmann_sandwiched_eq H0 H hH0 hH β s α ω
    (try dsimp only at h_s)
    rw [h_s]
    have h_comm :
        (starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
          (((Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω) : ℝ) : ℂ) *
            inner ℂ (φ α) ((H - H0) (ψ ω))) =
        ((Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω) : ℝ) : ℂ) *
          ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
            inner ℂ (φ α) ((H - H0) (ψ ω))) := by ring
    rw [h_comm, re_ofReal_mul]
  have h_cont_term : ∀ α ω : ManyBodyConfig Site,
      Continuous (fun s : ℝ =>
        (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω) := fun α ω =>
    (continuous_duhamel_exp_kernel β (lam α) (E ω)).mul continuous_const
  have h_cont_inner : ∀ α : ManyBodyConfig Site,
      Continuous (fun s : ℝ => ∑ ω : ManyBodyConfig Site,
        (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω) := fun α =>
    continuous_finset_sum Finset.univ (fun ω _ => h_cont_term α ω)
  have h_cont_outer :
      Continuous (fun s : ℝ => ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
        (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω) :=
    continuous_finset_sum Finset.univ (fun α _ => h_cont_inner α)
  have h_int :
      IntervalIntegrable
        (fun s : ℝ =>
          RCLike.re (inner ℂ χ₁
            ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) χ₂)))
        MeasureTheory.volume 0 β := by
    have h_fun_eq :
        (fun s : ℝ =>
          RCLike.re (inner ℂ χ₁
            ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) χ₂))) =
        (fun s : ℝ => ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω) :=
      funext h_integrand_eq
    rw [h_fun_eq]
    exact h_cont_outer.intervalIntegrable 0 β
  refine ⟨h_int, ?_⟩
  have h_lhs_term : ∀ α ω : ManyBodyConfig Site,
      RCLike.re ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
        inner ℂ (φ α) ((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) (ψ ω))) =
      -∫ s in (0 : ℝ)..β,
        (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω := by
    intro α ω
    have h_mat := spectral_boltzmann_duhamel_matrix_element_eq H0 H hH0 hH β α ω
    (try dsimp only at h_mat)
    rw [h_mat]
    have h_alg :
        (starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
          (-((dividedExpDiff β (lam α) (E ω) : ℝ) : ℂ) * inner ℂ (φ α) ((H - H0) (ψ ω))) =
        -(((dividedExpDiff β (lam α) (E ω) : ℝ) : ℂ) *
          ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
            inner ℂ (φ α) ((H - H0) (ψ ω)))) := by ring
    rw [h_alg, map_neg, re_ofReal_mul, dividedExpDiff_eq_intervalIntegral,
      ← intervalIntegral.integral_mul_const]
  calc RCLike.re (inner ℂ χ₁ ((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) χ₂))
    _ = ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          RCLike.re ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
            inner ℂ (φ α) ((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) (ψ ω))) :=
        re_inner_eq_sum_opEigenbasis_matrix_elements H0 H
          (gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) hH0 hH χ₁ χ₂
    _ = ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          (-∫ s in (0 : ℝ)..β,
            (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω) :=
        Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun ω _ => h_lhs_term α ω
    _ = -∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          ∫ s in (0 : ℝ)..β,
            (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun α _ => by rw [Finset.sum_neg_distrib]
    _ = -∑ α : ManyBodyConfig Site,
          ∫ s in (0 : ℝ)..β,
            ∑ ω : ManyBodyConfig Site,
              (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω := by
        congr 1
        exact Finset.sum_congr rfl fun α _ =>
          (intervalIntegral.integral_finset_sum
            (fun ω _ => (h_cont_term α ω).intervalIntegrable 0 β)).symm
    _ = -∫ s in (0 : ℝ)..β,
          ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
            (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω := by
        congr 1
        exact (intervalIntegral.integral_finset_sum
          (fun α _ => (h_cont_inner α).intervalIntegrable 0 β)).symm
    _ = -∫ s in (0 : ℝ)..β,
          RCLike.re (inner ℂ χ₁
            ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s) χ₂)) := by
        congr 1
        exact intervalIntegral.integral_congr fun s _ => (h_integrand_eq s).symm

/-! ## 3. Exact Operator-Trace Duhamel Integral Formula -/

/-- **Operator-Trace Duhamel Integral Identity for `gibbsBoltzmannOp`
    (`hilbertTrace_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral`)**:
    For any self-adjoint operators $H_0, H$, any observable $A$, and any $\beta \in \mathbb{R}$,
    $$\operatorname{Tr}\!\left(\bigl(B_H(\beta) - B_{H_0}(\beta)\bigr) * A\right)
      = -\int_0^\beta \operatorname{Tr}\!\left(
        B_{H_0}(\beta - s) * (H - H_0) * B_H(s) * A\right) ds.$$ -/
theorem hilbertTrace_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H) (β : ℝ) :
    let φ := opEigenbasis H0 hH0
    let lam := opEigenvalues H0 hH0
    let ψ := opEigenbasis H hH
    let E := opEigenvalues H hH
    hilbertTrace ((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) * A) =
      -∫ s in (0 : ℝ)..β,
        hilbertTrace
          (gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s * A) := by
  intro φ lam ψ E
  unfold hilbertTrace
  have h_each : ∀ x : ManyBodyConfig Site,
      RCLike.re (inner ℂ (basisVecGlobal Site x)
        (((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) * A) (basisVecGlobal Site x))) =
      -∫ s in (0 : ℝ)..β,
        RCLike.re (inner ℂ (basisVecGlobal Site x)
          ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s * A)
            (basisVecGlobal Site x))) := by
    intro x
    exact (inner_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral
      H0 H hH0 hH β (basisVecGlobal Site x) (A (basisVecGlobal Site x))).2
  have h_int : ∀ x ∈ (Finset.univ : Finset (ManyBodyConfig Site)),
      IntervalIntegrable
        (fun s : ℝ =>
          RCLike.re (inner ℂ (basisVecGlobal Site x)
            ((gibbsBoltzmannOp φ lam (β - s) * (H - H0) * gibbsBoltzmannOp ψ E s * A)
              (basisVecGlobal Site x))))
        MeasureTheory.volume 0 β := by
    intro x _
    exact (inner_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral
      H0 H hH0 hH β (basisVecGlobal Site x) (A (basisVecGlobal Site x))).1
  simp_rw [h_each]
  rw [Finset.sum_neg_distrib]
  congr 1
  exact (intervalIntegral.integral_finset_sum h_int).symm

/-- **Interval Integrability of General Sandwiched Boltzmann Traces
    (`intervalIntegrable_hilbertTrace_boltzmann_sandwiched`)**:
    For any self-adjoint $H_0, H$, any bounded operators $K, A$, and any $\beta \in \mathbb{R}$,
    $s \mapsto \operatorname{Tr}(B_{H_0}(\beta - s) * K * B_H(s) * A)$ is interval-integrable on $[0, \beta]$. -/
theorem intervalIntegrable_hilbertTrace_boltzmann_sandwiched {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H K A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H) (β : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H0 hH0) (opEigenvalues H0 hH0) (β - s) *
          K * gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) s * A))
      MeasureTheory.volume 0 β := by
  let φ := opEigenbasis H0 hH0
  let lam := opEigenvalues H0 hH0
  let ψ := opEigenbasis H hH
  let E := opEigenvalues H hH
  have h_in_each : ∀ x : ManyBodyConfig Site,
      Continuous (fun s : ℝ =>
        RCLike.re (inner ℂ (basisVecGlobal Site x)
          ((gibbsBoltzmannOp φ lam (β - s) * K * gibbsBoltzmannOp ψ E s)
            (A (basisVecGlobal Site x))))) := by
    intro x
    let χ₁ := basisVecGlobal Site x
    let χ₂ := A (basisVecGlobal Site x)
    let w : ManyBodyConfig Site → ManyBodyConfig Site → ℝ := fun α ω =>
      RCLike.re ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
        inner ℂ (φ α) (K (ψ ω)))
    have h_eq : (fun s : ℝ =>
        RCLike.re (inner ℂ χ₁
          ((gibbsBoltzmannOp φ lam (β - s) * K * gibbsBoltzmannOp ψ E s) χ₂))) =
        (fun s : ℝ => ∑ α : ManyBodyConfig Site, ∑ ω : ManyBodyConfig Site,
          (Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω)) * w α ω) := by
      funext s
      rw [re_inner_eq_sum_opEigenbasis_matrix_elements H0 H
        (gibbsBoltzmannOp φ lam (β - s) * K * gibbsBoltzmannOp ψ E s) hH0 hH χ₁ χ₂]
      refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun ω _ => ?_
      have h_apply_H : gibbsBoltzmannOp ψ E s (ψ ω) = (Real.exp (-s * E ω) : ℂ) • (ψ ω) :=
        perturbed_gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector H hH (opEigenbasis_apply_H H hH ω) s
      have h_in_B0 : ∀ χ : ManyBodyHilbertSpace Site,
          inner ℂ (φ α) (gibbsBoltzmannOp φ lam (β - s) χ) =
            (Real.exp (-(β - s) * lam α) : ℂ) * inner ℂ (φ α) χ := by
        intro χ; unfold gibbsBoltzmannOp
        rw [ContinuousLinearMap.sum_apply, inner_sum, Finset.sum_eq_single α]
        · rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
            inner_smul_right, opEigenbasis_orthonormal H0 hH0 α α, if_pos rfl, mul_one]
        · intro α' _ hne
          rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
            inner_smul_right, opEigenbasis_orthonormal H0 hH0 α α', if_neg (Ne.symm hne), mul_zero, mul_zero]
        · intro h_not; exact False.elim (h_not (Finset.mem_univ α))
      change RCLike.re ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
        inner ℂ (φ α) (gibbsBoltzmannOp φ lam (β - s) (K (gibbsBoltzmannOp ψ E s (ψ ω))))) = _
      rw [h_apply_H, map_smul, h_in_B0, inner_smul_right]
      have h_ring :
          (starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) *
            ((Real.exp (-(β - s) * lam α) : ℂ) * ((Real.exp (-s * E ω) : ℂ) * inner ℂ (φ α) (K (ψ ω)))) =
          ((Real.exp (-(β - s) * lam α) * Real.exp (-s * E ω) : ℝ) : ℂ) *
            ((starRingEnd ℂ (inner ℂ (φ α) χ₁) * inner ℂ (ψ ω) χ₂) * inner ℂ (φ α) (K (ψ ω))) := by
        rw [Complex.ofReal_mul]; ring
      rw [h_ring, re_ofReal_mul]
    rw [h_eq]
    exact continuous_finset_sum Finset.univ fun α _ =>
      continuous_finset_sum Finset.univ fun ω _ =>
        (continuous_duhamel_exp_kernel β (lam α) (E ω)).mul continuous_const
  unfold hilbertTrace
  exact (continuous_finset_sum Finset.univ fun x _ => h_in_each x).intervalIntegrable 0 β

/-- **Exact Decomposition of the Centered Witness Duhamel Integral into Uncentered Witness
    Duhamel Integral Minus Diagonal Failure Probability Times Partition Shift
    (`centered_duhamel_integral_eq_uncentered_sub_failureProb_mul_partitionZ_diff`)** -/
theorem centered_duhamel_integral_eq_uncentered_sub_failureProb_mul_partitionZ_diff
    {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H_diag H_shift V_off P_W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (hH_shift : IsSelfAdjoint H_shift)
    (h_decomp : H_shift = H_diag + V_off) (β : ℝ) :
    let B_diag := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag)
    let B_shift := gibbsBoltzmannOp (opEigenbasis H_shift hH_shift) (opEigenvalues H_shift hH_shift)
    let A_W := centeredWitnessObservable H_diag hH_diag β P_W
    (-∫ s in (0 : ℝ)..β, hilbertTrace (B_diag (β - s) * V_off * B_shift s * A_W)) =
      (-∫ s in (0 : ℝ)..β, hilbertTrace (B_diag (β - s) * V_off * B_shift s * P_W)) -
        gibbsFailureProb H_diag hH_diag β P_W *
          (gibbsPartitionZ (opEigenvalues H_shift hH_shift) β -
            gibbsPartitionZ (opEigenvalues H_diag hH_diag) β) := by
  intro B_diag B_shift A_W
  have h_sub_H : H_shift - H_diag = V_off := sub_eq_iff_eq_add'.mpr h_decomp
  have h_int_A := (hilbertTrace_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral
    H_diag H_shift A_W hH_diag hH_shift β).symm
  have h_int_P := (hilbertTrace_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral
    H_diag H_shift P_W hH_diag hH_shift β).symm
  dsimp only [B_diag, B_shift] at h_int_A h_int_P ⊢
  simp only [h_sub_H] at h_int_A h_int_P
  rw [h_int_A, h_int_P]
  have h_trace_smul : ∀ (c : ℝ) (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      hilbertTrace (((c : ℝ) : ℂ) • X) = c * hilbertTrace X := by
    intro c X
    unfold hilbertTrace
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, re_ofReal_mul]
  have h_trace_one : ∀ (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
      (hH : IsSelfAdjoint H),
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
        (((gibbsFailureProb H_diag hH_diag β P_W : ℝ) : ℂ) • 1)) =
      gibbsFailureProb H_diag hH_diag β P_W * gibbsPartitionZ (opEigenvalues H hH) β := by
    intro H hH
    rw [mul_smul_comm, h_trace_smul, perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ H hH β]
  change hilbertTrace ((B_shift β - B_diag β) *
      (P_W - ((gibbsFailureProb H_diag hH_diag β P_W : ℝ) : ℂ) • 1)) = _
  rw [mul_sub, PerturbedThermalBarrier.hilbertTrace_sub, sub_mul,
    PerturbedThermalBarrier.hilbertTrace_sub, sub_mul,
    PerturbedThermalBarrier.hilbertTrace_sub]
  dsimp only [B_shift, B_diag]
  rw [h_trace_one H_shift hH_shift, h_trace_one H_diag hH_diag, mul_sub]

/-- **Uncentered Witness Duhamel Upper Bound Under Partition Domination
    (`centered_duhamel_integral_le_uncentered_of_partitionZ_le`)** -/
theorem centered_duhamel_integral_le_uncentered_of_partitionZ_le
    {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D_dim L Site ι)
    (H_diag H_shift V_off : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (hH_shift : IsSelfAdjoint H_shift)
    (h_decomp : H_shift = H_diag + V_off) (W : Finset ι) (β : ℝ)
    (hZ_le : gibbsPartitionZ (opEigenvalues H_diag hH_diag) β ≤
      gibbsPartitionZ (opEigenvalues H_shift hH_shift) β) :
    let B_diag := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag)
    let B_shift := gibbsBoltzmannOp (opEigenbasis H_shift hH_shift) (opEigenvalues H_shift hH_shift)
    let P_W := positiveCheckWitnessProj sys W
    let A_W := centeredWitnessObservable H_diag hH_diag β P_W
    (-∫ s in (0 : ℝ)..β, hilbertTrace (B_diag (β - s) * V_off * B_shift s * A_W)) ≤
      (-∫ s in (0 : ℝ)..β, hilbertTrace (B_diag (β - s) * V_off * B_shift s * P_W)) := by
  intro B_diag B_shift P_W A_W
  rw [centered_duhamel_integral_eq_uncentered_sub_failureProb_mul_partitionZ_diff
    H_diag H_shift V_off P_W hH_diag hH_shift h_decomp β]
  have hZ_pos : 0 < gibbsPartitionZ (opEigenvalues H_diag hH_diag) β :=
    gibbsPartitionZ_pos (opEigenvalues H_diag hH_diag) β
  have h_tr_nn : 0 ≤ hilbertTrace (B_diag β * P_W) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (le_of_lt (Real.exp_pos _))
      ((isStarProjection_positiveCheckWitnessProj sys W).1.re_inner_nonneg _)
  have hp_nn : 0 ≤ gibbsFailureProb H_diag hH_diag β P_W := by
    rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_diag hH_diag β P_W]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hZ_pos)) h_tr_nn
  have h_sub_nn : 0 ≤ gibbsFailureProb H_diag hH_diag β P_W *
      (gibbsPartitionZ (opEigenvalues H_shift hH_shift) β -
        gibbsPartitionZ (opEigenvalues H_diag hH_diag) β) :=
    mul_nonneg hp_nn (sub_nonneg.mpr hZ_le)
  linarith

/-- **Sub-Witness Projector Absorption (`positiveCheckWitnessProj_subset_mul_eq`)** -/
theorem positiveCheckWitnessProj_subset_mul_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {W' W : Finset ι} (h_sub : W' ⊆ W) :
    positiveCheckWitnessProj sys W' * positiveCheckWitnessProj sys W =
      positiveCheckWitnessProj sys W ∧
    positiveCheckWitnessProj sys W * positiveCheckWitnessProj sys W' =
      positiveCheckWitnessProj sys W := by
  have h_left :
      positiveCheckWitnessProj sys W' * positiveCheckWitnessProj sys W =
        positiveCheckWitnessProj sys W := by
    conv_lhs => rhs; unfold positiveCheckWitnessProj
    conv_rhs => unfold positiveCheckWitnessProj
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have hσ_W : ∀ c ∈ W, σ c = true := (Finset.mem_filter.mp hσ).2
    have hσ_W' : ∀ c ∈ W', σ c = true := fun c hc => hσ_W c (h_sub hc)
    rw [(isStarProjection_positiveCheckWitnessProj sys W').2.2 σ, if_pos hσ_W']
  have h_comm :
      Commute (positiveCheckWitnessProj sys W') (positiveCheckWitnessProj sys W) := by
    unfold positiveCheckWitnessProj
    refine Commute.sum_left _ _ _ fun σ _ => ?_
    refine Commute.sum_right _ _ _ fun τ _ => ?_
    by_cases h : σ = τ
    · subst h; rfl
    · have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
      change sys.syndromeProjector σ * sys.syndromeProjector τ =
        sys.syndromeProjector τ * sys.syndromeProjector σ
      rw [h_res.2.2.1 σ τ h, h_res.2.2.1 τ σ (Ne.symm h)]
  exact ⟨h_left, by rw [← h_comm.eq, h_left]⟩

/-- **Explicit Operator-Trace Evaluation of Filtered and Unfiltered 2-Step `worldlineSliceProduct` Sums
    (`sum_filtered_and_unfiltered_two_step_worldlineSliceProduct_eq`)** -/
theorem sum_filtered_and_unfiltered_two_step_worldlineSliceProduct_eq
    {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D_dim L Site ι)
    (H_diag K₁ R_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag)
    (W : Finset ι) (t₀ t₁ : ℝ) :
    let B_diag := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag)
    let P_W := positiveCheckWitnessProj sys W
    (∑ σ₀ ∈ Finset.univ.filter (fun σ₀ : ι → Bool => ∀ c ∈ W, σ₀ c = true),
      ∑ σ₁ : ι → Bool,
        hilbertTrace
          (worldlineSliceProduct sys H_diag hH_diag ![t₀, t₁] ![σ₀, σ₁] ![K₁] * R_op)) =
      hilbertTrace ((B_diag t₀ * P_W) * K₁ * B_diag t₁ * R_op) ∧
    (∑ σ₀ : ι → Bool,
      ∑ σ₁ : ι → Bool,
        hilbertTrace
          (worldlineSliceProduct sys H_diag hH_diag ![t₀, t₁] ![σ₀, σ₁] ![K₁] * R_op)) =
      hilbertTrace (B_diag t₀ * K₁ * B_diag t₁ * R_op) := by
  intro B_diag P_W
  have h_res := (PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.2.2.1
  have h_inner : ∀ σ₀ : ι → Bool,
      (∑ σ₁ : ι → Bool,
        hilbertTrace
          (worldlineSliceProduct sys H_diag hH_diag ![t₀, t₁] ![σ₀, σ₁] ![K₁] * R_op)) =
      hilbertTrace ((B_diag t₀ * sys.syndromeProjector σ₀) * K₁ * B_diag t₁ * R_op) := by
    intro σ₀
    rw [← hilbertTrace_sum, ← Finset.sum_mul]
    congr 2
    change (∑ σ₁ : ι → Bool,
      (B_diag t₀ * sys.syndromeProjector σ₀) * K₁ * (B_diag t₁ * sys.syndromeProjector σ₁)) = _
    rw [← Finset.mul_sum, ← Finset.mul_sum, h_res, mul_one]
  simp_rw [h_inner]
  constructor
  · rw [← hilbertTrace_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    rfl
  · rw [← hilbertTrace_sum, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
      h_res, mul_one]

/-- **Recursive One-Step Duhamel Expansion of Right-Multiplied `B_shift s` Trace
    (`hilbertTrace_mul_gibbsBoltzmannOp_shift_eq_diag_sub_duhamel_integral`)** -/
theorem hilbertTrace_mul_gibbsBoltzmannOp_shift_eq_diag_sub_duhamel_integral
    {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H_diag H_shift V_off X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (hH_shift : IsSelfAdjoint H_shift)
    (h_decomp : H_shift = H_diag + V_off) (s : ℝ) :
    let B_diag := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag)
    let B_shift := gibbsBoltzmannOp (opEigenbasis H_shift hH_shift) (opEigenvalues H_shift hH_shift)
    hilbertTrace (X * B_shift s) =
      hilbertTrace (X * B_diag s) -
        ∫ u in (0 : ℝ)..s, hilbertTrace (B_diag (s - u) * V_off * B_shift u * X) := by
  intro B_diag B_shift
  have h_sub_H : H_shift - H_diag = V_off := sub_eq_iff_eq_add'.mpr h_decomp
  have h_duh := hilbertTrace_gibbsBoltzmannOp_sub_eq_neg_intervalIntegral
    H_diag H_shift X hH_diag hH_shift s
  dsimp only [B_diag, B_shift] at h_duh ⊢
  simp only [h_sub_H] at h_duh
  rw [sub_mul, PerturbedThermalBarrier.hilbertTrace_sub,
    hilbertTrace_mul_comm_aux (B_shift s) X,
    hilbertTrace_mul_comm_aux (B_diag s) X] at h_duh
  linarith

end SpacetimeWorldlineKP

end
