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

import Proofs.SpacetimeWorldlineKP.SpacetimeKoteckyPreissRatio

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SpacetimeWorldlineKP

/-!
# Divided Exponential Differences and Cross-Eigenbasis Boltzmann Duhamel Identity

Defines the symmetric divided exponential difference `dividedExpDiff` and proves its positivity and minimum-endpoint upper bound (`dividedExpDiff_nonneg`, `dividedExpDiff_le_beta_mul_exp_min`). Establishes the exact cross-eigenbasis matrix-element identity (`spectral_boltzmann_duhamel_matrix_element_eq`) relating `gibbsBoltzmannOp` differences to Hamiltonian matrix elements.

## References

* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.1 (`lem:duhamel-weyl-ratio`)
-/

/-! ## 1. Euclidean Duhamel Divided Difference & Elementary Bounds -/

/-- **Euclidean Duhamel Divided Exponential Difference (`dividedExpDiff`)**:
    Closed-form value of the 1-simplex Euclidean time integral
    $\int_0^\beta e^{-(\beta - \tau)\lambda} e^{-\tau \mu}\,d\tau$. -/
def dividedExpDiff (β lam μ : ℝ) : ℝ :=
  if lam = μ then β * Real.exp (-β * lam)
  else (Real.exp (-β * μ) - Real.exp (-β * lam)) / (lam - μ)

/-- **Exact Divided-Difference Factorization (`exp_neg_mul_sub_eq_mul_dividedExpDiff`)**:
    For all $\beta, \lambda, \mu \in \mathbb{R}$,
    $$e^{-\beta \mu} - e^{-\beta \lambda} = (\lambda - \mu) \, \mathrm{dividedExpDiff}(\beta, \lambda, \mu).$$ -/
theorem exp_neg_mul_sub_eq_mul_dividedExpDiff (β lam μ : ℝ) :
    Real.exp (-β * μ) - Real.exp (-β * lam) = (lam - μ) * dividedExpDiff β lam μ := by
  unfold dividedExpDiff
  split_ifs with h
  · subst h; ring
  · have h_ne : lam - μ ≠ 0 := sub_ne_zero.mpr h
    exact (mul_div_cancel₀ (Real.exp (-β * μ) - Real.exp (-β * lam)) h_ne).symm

/-- **Symmetry of `dividedExpDiff` (`dividedExpDiff_symm`)**:
    $\mathrm{dividedExpDiff}(\beta, \lambda, \mu) = \mathrm{dividedExpDiff}(\beta, \mu, \lambda)$. -/
theorem dividedExpDiff_symm (β lam μ : ℝ) :
    dividedExpDiff β lam μ = dividedExpDiff β μ lam := by
  unfold dividedExpDiff
  by_cases h : lam = μ
  · subst h; simp
  · have h_symm : μ ≠ lam := Ne.symm h
    rw [if_neg h, if_neg h_symm, div_eq_div_iff (sub_ne_zero.mpr h) (sub_ne_zero.mpr h_symm)]
    ring

/-- **Non-Negativity of `dividedExpDiff` (`dividedExpDiff_nonneg`)**:
    For all $\beta \ge 0$ and $\lambda, \mu \in \mathbb{R}$,
    $0 \le \mathrm{dividedExpDiff}(\beta, \lambda, \mu)$. -/
theorem dividedExpDiff_nonneg {β : ℝ} (hβ : 0 ≤ β) (lam μ : ℝ) :
    0 ≤ dividedExpDiff β lam μ := by
  unfold dividedExpDiff
  split_ifs with h
  · exact mul_nonneg hβ (le_of_lt (Real.exp_pos _))
  · rcases lt_or_gt_of_ne h with h_lt | h_gt
    · have h_denom : lam - μ ≤ 0 := by linarith
      have h_exp : Real.exp (-β * μ) ≤ Real.exp (-β * lam) := by
        apply Real.exp_le_exp.mpr; nlinarith
      exact div_nonneg_of_nonpos (by linarith) h_denom
    · have h_denom : 0 ≤ lam - μ := by linarith
      have h_exp : Real.exp (-β * lam) ≤ Real.exp (-β * μ) := by
        apply Real.exp_le_exp.mpr; nlinarith
      exact div_nonneg (by linarith) h_denom

/-- **$\beta$-Independent Resolvent Upper Bound on `dividedExpDiff`
    (`dividedExpDiff_le_inv_sub_mul_exp_of_lt`)**:
    Whenever $\mu < \lambda$, for every $\beta \in \mathbb{R}$,
    $$\mathrm{dividedExpDiff}(\beta, \lambda, \mu)
      \le \frac{\exp(-\beta \mu)}{\lambda - \mu}.$$ -/
theorem dividedExpDiff_le_inv_sub_mul_exp_of_lt (β : ℝ) {lam μ : ℝ} (h_lt : μ < lam) :
    dividedExpDiff β lam μ ≤ Real.exp (-β * μ) / (lam - μ) := by
  unfold dividedExpDiff
  rw [if_neg (ne_of_gt h_lt)]
  have h_pos : 0 < lam - μ := sub_pos.mpr h_lt
  have h_exp_pos : 0 ≤ Real.exp (-β * lam) := le_of_lt (Real.exp_pos _)
  exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h_pos)

/-- **Uniform Thermal Envelope Bound on `dividedExpDiff`
    (`dividedExpDiff_le_beta_mul_exp_min`)**:
    For all $\beta \ge 0$ and $\lambda, \mu \in \mathbb{R}$,
    $$\mathrm{dividedExpDiff}(\beta, \lambda, \mu)
      \le \beta \exp\bigl(-\beta \min(\lambda, \mu)\bigr).$$ -/
theorem dividedExpDiff_le_beta_mul_exp_min {β : ℝ} (_hβ : 0 ≤ β) (lam μ : ℝ) :
    dividedExpDiff β lam μ ≤ β * Real.exp (-β * min lam μ) := by
  have h_aux : ∀ a b : ℝ, b < a →
      (Real.exp (-β * b) - Real.exp (-β * a)) / (a - b) ≤ β * Real.exp (-β * b) := by
    intro a b hba
    have h_ab_pos : 0 < a - b := sub_pos.mpr hba
    rw [div_le_iff₀ h_ab_pos]
    have h_one_sub : 1 - Real.exp (-β * (a - b)) ≤ β * (a - b) := by
      have h_exp := Real.add_one_le_exp (-(β * (a - b)))
      have h_eq : -(β * (a - b)) = -β * (a - b) := by ring
      rw [h_eq] at h_exp
      linarith
    have h_split :
        Real.exp (-β * b) - Real.exp (-β * a) =
          Real.exp (-β * b) * (1 - Real.exp (-β * (a - b))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 1; ring
    rw [h_split]
    calc Real.exp (-β * b) * (1 - Real.exp (-β * (a - b)))
      _ ≤ Real.exp (-β * b) * (β * (a - b)) :=
        mul_le_mul_of_nonneg_left h_one_sub (le_of_lt (Real.exp_pos _))
      _ = β * Real.exp (-β * b) * (a - b) := by ring
  by_cases h_eq : lam = μ
  · subst h_eq
    unfold dividedExpDiff
    simp
  · rcases lt_or_gt_of_ne h_eq with h_lt | h_gt
    · rw [dividedExpDiff_symm, min_eq_left (le_of_lt h_lt)]
      unfold dividedExpDiff
      rw [if_neg (ne_of_gt h_lt)]
      exact h_aux μ lam h_lt
    · rw [min_eq_right (le_of_lt h_gt)]
      unfold dividedExpDiff
      rw [if_neg (ne_of_gt h_gt)]
      exact h_aux lam μ h_gt

/-- **Universal Separable Exponential Bound on `dividedExpDiff`
    (`dividedExpDiff_le_beta_exp_mul_add_inv_mul_exp`)**:
    For all $\beta \ge 0$, $\gamma > 0$, and $\lambda, \mu \in \mathbb{R}$,
    $$\mathrm{dividedExpDiff}(\beta, \lambda, \mu)
      \le \beta \exp(\beta \gamma) \exp(-\beta \lambda) + \frac{1}{\gamma} \exp(-\beta \mu).$$ -/
theorem dividedExpDiff_le_beta_exp_mul_add_inv_mul_exp
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) (lam μ : ℝ) :
    dividedExpDiff β lam μ ≤
      β * Real.exp (β * γ) * Real.exp (-β * lam) + (1 / γ) * Real.exp (-β * μ) := by
  have h1_nn : 0 ≤ β * Real.exp (β * γ) * Real.exp (-β * lam) :=
    mul_nonneg (mul_nonneg hβ (le_of_lt (Real.exp_pos _))) (le_of_lt (Real.exp_pos _))
  have h2_nn : 0 ≤ (1 / γ) * Real.exp (-β * μ) :=
    mul_nonneg (one_div_nonneg.mpr (le_of_lt hγ)) (le_of_lt (Real.exp_pos _))
  by_cases h_gap : γ ≤ lam - μ
  · have h_lt : μ < lam := by linarith
    have h_res := dividedExpDiff_le_inv_sub_mul_exp_of_lt β h_lt
    have h_inv : 1 / (lam - μ) ≤ 1 / γ := one_div_le_one_div_of_le hγ h_gap
    have h_second : Real.exp (-β * μ) / (lam - μ) ≤ (1 / γ) * Real.exp (-β * μ) := by
      rw [div_eq_inv_mul, ← one_div]
      exact mul_le_mul_of_nonneg_right h_inv (le_of_lt (Real.exp_pos _))
    linarith
  · push_neg at h_gap
    have h_min : lam - γ ≤ min lam μ := le_min (by linarith) (by linarith)
    have h_env := dividedExpDiff_le_beta_mul_exp_min hβ lam μ
    have h_exp : Real.exp (-β * min lam μ) ≤ Real.exp (β * γ) * Real.exp (-β * lam) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have h_first : β * Real.exp (-β * min lam μ) ≤ β * Real.exp (β * γ) * Real.exp (-β * lam) := by
      calc β * Real.exp (-β * min lam μ)
        _ ≤ β * (Real.exp (β * γ) * Real.exp (-β * lam)) := mul_le_mul_of_nonneg_left h_exp hβ
        _ = β * Real.exp (β * γ) * Real.exp (-β * lam) := by ring
    linarith

/-! ## 2. Cross-Eigenbasis Perturbation & Boltzmann Duhamel Identities -/

/-- **Cross-Eigenbasis Eigenvalue Difference Identity
    (`eigenstate_sub_eigenvalue_mul_inner_eq`)**:
    For any two self-adjoint operators $H_0, H$ on `ManyBodyHilbertSpace Site` and any
    configuration indices $\alpha, \omega : \mathrm{ManyBodyConfig}\;\mathrm{Site}$,
    with $\phi_\alpha = \mathrm{opEigenbasis}\;H_0\;hH_0\;\alpha$,
    $\lambda_\alpha = \mathrm{opEigenvalues}\;H_0\;hH_0\;\alpha$,
    $\psi_\omega = \mathrm{opEigenbasis}\;H\;hH\;\omega$, and
    $E_\omega = \mathrm{opEigenvalues}\;H\;hH\;\omega$,
    $$((\lambda_\alpha - E_\omega : \mathbb{R}) : \mathbb{C}) \, \langle \phi_\alpha, \psi_\omega \rangle
      = -\langle \phi_\alpha, (H - H_0) \psi_\omega \rangle.$$ -/
theorem eigenstate_sub_eigenvalue_mul_inner_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H)
    (α ω : ManyBodyConfig Site) :
    let φ := opEigenbasis H0 hH0
    let lam := opEigenvalues H0 hH0
    let ψ := opEigenbasis H hH
    let E := opEigenvalues H hH
    (((lam α - E ω : ℝ) : ℂ) * inner ℂ (φ α) (ψ ω)) =
      -inner ℂ (φ α) ((H - H0) (ψ ω)) := by
  intro φ lam ψ E
  have hH0_adj : H0† = H0 := ContinuousLinearMap.isSelfAdjoint_iff'.mp hH0
  have h_eig0 : H0 (φ α) = (lam α : ℂ) • (φ α) := opEigenbasis_apply_H H0 hH0 α
  have h_eigH : H (ψ ω) = (E ω : ℂ) • (ψ ω) := opEigenbasis_apply_H H hH ω
  have h_in0 : inner ℂ (φ α) (H0 (ψ ω)) = (lam α : ℂ) * inner ℂ (φ α) (ψ ω) := by
    calc inner ℂ (φ α) (H0 (ψ ω))
      _ = inner ℂ ((H0†) (φ α)) (ψ ω) := (ContinuousLinearMap.adjoint_inner_left H0 (ψ ω) (φ α)).symm
      _ = inner ℂ (H0 (φ α)) (ψ ω) := by rw [hH0_adj]
      _ = inner ℂ ((lam α : ℂ) • (φ α)) (ψ ω) := by rw [h_eig0]
      _ = (lam α : ℂ) * inner ℂ (φ α) (ψ ω) := by
        rw [inner_smul_left, Complex.conj_ofReal]
  have h_inH : inner ℂ (φ α) (H (ψ ω)) = (E ω : ℂ) * inner ℂ (φ α) (ψ ω) := by
    rw [h_eigH, inner_smul_right]
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, h_inH, h_in0, Complex.ofReal_sub]
  ring

/-- **Cross-Eigenbasis Boltzmann Duhamel Matrix-Element Identity
    (`spectral_boltzmann_duhamel_matrix_element_eq`)**:
    For any two self-adjoint operators $H_0, H$ on `ManyBodyHilbertSpace Site`, inverse
    temperature $\beta \in \mathbb{R}$, and configuration indices $\alpha, \omega$:
    $$\langle \phi_\alpha, \bigl(B_H(\beta) - B_{H_0}(\beta)\bigr) \psi_\omega \rangle
      = -\bigl(\mathrm{dividedExpDiff}(\beta, \lambda_\alpha, E_\omega) : \mathbb{C}\bigr) \,
        \langle \phi_\alpha, (H - H_0) \psi_\omega \rangle.$$ -/
theorem spectral_boltzmann_duhamel_matrix_element_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH0 : IsSelfAdjoint H0) (hH : IsSelfAdjoint H)
    (β : ℝ) (α ω : ManyBodyConfig Site) :
    let φ := opEigenbasis H0 hH0
    let lam := opEigenvalues H0 hH0
    let ψ := opEigenbasis H hH
    let E := opEigenvalues H hH
    inner ℂ (φ α) ((gibbsBoltzmannOp ψ E β - gibbsBoltzmannOp φ lam β) (ψ ω)) =
      -((dividedExpDiff β (lam α) (E ω) : ℝ) : ℂ) *
        inner ℂ (φ α) ((H - H0) (ψ ω)) := by
  intro φ lam ψ E
  have h_apply_H :
      gibbsBoltzmannOp ψ E β (ψ ω) = (Real.exp (-β * E ω) : ℂ) • (ψ ω) :=
    perturbed_gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector
      H hH (opEigenbasis_apply_H H hH ω) β
  have h_in_B0 :
      inner ℂ (φ α) (gibbsBoltzmannOp φ lam β (ψ ω)) =
        (Real.exp (-β * lam α) : ℂ) * inner ℂ (φ α) (ψ ω) := by
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
  have h_in_BH :
      inner ℂ (φ α) (gibbsBoltzmannOp ψ E β (ψ ω)) =
        (Real.exp (-β * E ω) : ℂ) * inner ℂ (φ α) (ψ ω) := by
    rw [h_apply_H, inner_smul_right]
  have h_div :
      ((Real.exp (-β * E ω) : ℂ) - (Real.exp (-β * lam α) : ℂ)) =
        (((lam α : ℂ) - (E ω : ℂ)) * (dividedExpDiff β (lam α) (E ω) : ℂ)) := by
    rw [← Complex.ofReal_sub, exp_neg_mul_sub_eq_mul_dividedExpDiff β (lam α) (E ω),
      Complex.ofReal_mul, Complex.ofReal_sub]
  have h_eig_diff := eigenstate_sub_eigenvalue_mul_inner_eq H0 H hH0 hH α ω
  (try dsimp only at h_eig_diff)
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, h_in_BH, h_in_B0]
  calc (Real.exp (-β * E ω) : ℂ) * inner ℂ (φ α) (ψ ω) -
        (Real.exp (-β * lam α) : ℂ) * inner ℂ (φ α) (ψ ω)
    _ = ((Real.exp (-β * E ω) : ℂ) - (Real.exp (-β * lam α) : ℂ)) * inner ℂ (φ α) (ψ ω) := by ring
    _ = (((lam α : ℂ) - (E ω : ℂ)) * (dividedExpDiff β (lam α) (E ω) : ℂ)) *
          inner ℂ (φ α) (ψ ω) := by rw [h_div]
    _ = (dividedExpDiff β (lam α) (E ω) : ℂ) *
          (((lam α - E ω : ℝ) : ℂ) * inner ℂ (φ α) (ψ ω)) := by push_cast; ring
    _ = (dividedExpDiff β (lam α) (E ω) : ℂ) * (-inner ℂ (φ α) ((H - H0) (ψ ω))) := by
          rw [h_eig_diff]
    _ = -((dividedExpDiff β (lam α) (E ω) : ℝ) : ℂ) * inner ℂ (φ α) ((H - H0) (ψ ω)) := by ring

/-- **Syndrome-Resolved `worldlineSliceProduct` Identity for the 2-Step Duhamel Integrand
    (`two_step_duhamel_integrand_eq_sum_worldlineSliceProduct`)** -/
theorem two_step_duhamel_integrand_eq_sum_worldlineSliceProduct
    {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D_dim L Site ι)
    (H_diag H_shift K₁ K₂ A_W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (hH_shift : IsSelfAdjoint H_shift)
    (β s₁ s₂ : ℝ) :
    let B_diag := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag)
    let B_shift := gibbsBoltzmannOp (opEigenbasis H_shift hH_shift) (opEigenvalues H_shift hH_shift)
    hilbertTrace (B_diag (s₁ - s₂) * K₂ * B_shift s₂ * (A_W * B_diag (β - s₁) * K₁)) =
      ∑ σ₀ : ι → Bool, ∑ σ₁ : ι → Bool,
        hilbertTrace
          (A_W * worldlineSliceProduct sys H_diag hH_diag ![β - s₁, s₁ - s₂] ![σ₀, σ₁] ![K₁] *
            K₂ * B_shift s₂) := by
  intro B_diag B_shift
  have h_res := (PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.2.2.1
  have h_cyc :
      hilbertTrace (B_diag (s₁ - s₂) * K₂ * B_shift s₂ * (A_W * B_diag (β - s₁) * K₁)) =
        hilbertTrace (A_W * (B_diag (β - s₁) * K₁ * B_diag (s₁ - s₂)) * K₂ * B_shift s₂) := by
    calc hilbertTrace (B_diag (s₁ - s₂) * K₂ * B_shift s₂ * (A_W * B_diag (β - s₁) * K₁))
      _ = hilbertTrace ((B_diag (s₁ - s₂) * K₂ * B_shift s₂) * (A_W * B_diag (β - s₁) * K₁)) := rfl
      _ = hilbertTrace ((A_W * B_diag (β - s₁) * K₁) * (B_diag (s₁ - s₂) * K₂ * B_shift s₂)) :=
          hilbertTrace_mul_comm_aux _ _
      _ = hilbertTrace (A_W * (B_diag (β - s₁) * K₁ * B_diag (s₁ - s₂)) * K₂ * B_shift s₂) := by
          simp only [mul_assoc]
  have h_arc :
      B_diag (β - s₁) * K₁ * B_diag (s₁ - s₂) =
        ∑ σ₀ : ι → Bool, ∑ σ₁ : ι → Bool,
          worldlineSliceProduct sys H_diag hH_diag ![β - s₁, s₁ - s₂] ![σ₀, σ₁] ![K₁] := by
    calc B_diag (β - s₁) * K₁ * B_diag (s₁ - s₂)
      _ = (B_diag (β - s₁) * 1) * K₁ * (B_diag (s₁ - s₂) * 1) := by rw [mul_one, mul_one]
      _ = (B_diag (β - s₁) * ∑ σ₀ : ι → Bool, sys.syndromeProjector σ₀) * K₁ *
            (B_diag (s₁ - s₂) * ∑ σ₁ : ι → Bool, sys.syndromeProjector σ₁) := by rw [← h_res]
      _ = ∑ σ₀ : ι → Bool, ∑ σ₁ : ι → Bool,
            (B_diag (β - s₁) * sys.syndromeProjector σ₀) * K₁ *
              (B_diag (s₁ - s₂) * sys.syndromeProjector σ₁) := by
          simp_rw [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
      _ = ∑ σ₀ : ι → Bool, ∑ σ₁ : ι → Bool,
            worldlineSliceProduct sys H_diag hH_diag ![β - s₁, s₁ - s₂] ![σ₀, σ₁] ![K₁] := rfl
  rw [h_cyc, h_arc]
  simp_rw [Finset.mul_sum, Finset.sum_mul, hilbertTrace_sum]

/-- **Unfiltered Syndrome Sum of 2-Step `worldlineSliceProduct` Traces
    (`sum_unfiltered_two_step_worldlineSliceProduct_eq`)** -/
theorem sum_unfiltered_two_step_worldlineSliceProduct_eq
    {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D_dim L Site ι)
    (H_diag H_shift K₁ K₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (hH_shift : IsSelfAdjoint H_shift)
    (β s₁ s₂ : ℝ) :
    let B_diag := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag)
    let B_shift := gibbsBoltzmannOp (opEigenbasis H_shift hH_shift) (opEigenvalues H_shift hH_shift)
    (∑ σ₀ : ι → Bool, ∑ σ₁ : ι → Bool,
      hilbertTrace
        (worldlineSliceProduct sys H_diag hH_diag ![β - s₁, s₁ - s₂] ![σ₀, σ₁] ![K₁] *
          (K₂ * B_shift s₂))) =
      hilbertTrace (B_diag (s₁ - s₂) * K₂ * B_shift s₂ * (B_diag (β - s₁) * K₁)) := by
  intro B_diag B_shift
  have h1 := (two_step_duhamel_integrand_eq_sum_worldlineSliceProduct
    sys H_diag H_shift K₁ K₂ 1 hH_diag hH_shift β s₁ s₂).symm
  dsimp only [B_diag, B_shift] at h1 ⊢
  rw [one_mul] at h1
  simp only [one_mul, mul_assoc] at h1 ⊢
  exact h1

/-- **Basis-Free Star-Projection Propagator Damping Bound
    (`norm_gibbsBoltzmannOp_mul_proj_le_of_coercivity`)** -/
theorem norm_gibbsBoltzmannOp_mul_proj_le_of_coercivity {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hP : IsStarProjection P)
    (h_comm : Commute H P) {E_min : ℝ}
    (h_lower : ∀ ψ : ManyBodyHilbertSpace Site,
      E_min * ‖P ψ‖ ^ 2 ≤ RCLike.re (inner ℂ (P ψ) (H (P ψ))))
    {s : ℝ} (hs : 0 ≤ s) :
    ‖gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) s * P‖ ≤
      Real.exp (-s * E_min) := by
  let ψ_eig := opEigenbasis H hH
  let E_eig := opEigenvalues H hH
  let C := Real.exp (-s * E_min)
  have hC_nonneg : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  have h_inner_boltz : ∀ (ω : ManyBodyConfig Site) (ψ : ManyBodyHilbertSpace Site),
      inner ℂ (ψ_eig ω) (gibbsBoltzmannOp ψ_eig E_eig s ψ) =
        (Real.exp (-s * E_eig ω) : ℂ) * inner ℂ (ψ_eig ω) ψ := by
    intro ω ψ; unfold gibbsBoltzmannOp
    rw [ContinuousLinearMap.sum_apply, inner_sum, Finset.sum_eq_single ω]
    · rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
        inner_smul_right, opEigenbasis_orthonormal H hH ω ω, if_pos rfl, mul_one]
    · intro ω' _ hne
      rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
        inner_smul_right, opEigenbasis_orthonormal H hH ω ω',
        if_neg (Ne.symm hne), mul_zero, mul_zero]
    · intro h_not; exact False.elim (h_not (Finset.mem_univ ω))
  apply ContinuousLinearMap.opNorm_le_bound _ hC_nonneg
  intro φ
  have h_term_le : ∀ ω : ManyBodyConfig Site,
      ‖inner ℂ (ψ_eig ω) ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)‖ ^ 2 ≤
        C ^ 2 * ‖inner ℂ (ψ_eig ω) (P φ)‖ ^ 2 := by
    intro ω
    have h_norm_eq :
        ‖inner ℂ (ψ_eig ω) ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)‖ =
          Real.exp (-s * E_eig ω) * ‖inner ℂ (ψ_eig ω) (P φ)‖ := by
      change ‖inner ℂ (ψ_eig ω) (gibbsBoltzmannOp ψ_eig E_eig s (P φ))‖ = _
      rw [h_inner_boltz ω (P φ), norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    have h_lin_le :
        Real.exp (-s * E_eig ω) * ‖inner ℂ (ψ_eig ω) (P φ)‖ ≤
          C * ‖inner ℂ (ψ_eig ω) (P φ)‖ := by
      by_cases h_zero : ‖P (ψ_eig ω)‖ = 0
      · have hP_zero : P (ψ_eig ω) = 0 := norm_eq_zero.mp h_zero
        have h_in_zero : inner ℂ (ψ_eig ω) (P φ) = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj, hP_zero, inner_zero_left]
        rw [h_in_zero, norm_zero, mul_zero, mul_zero]
      · have h_sq_pos : 0 < ‖P (ψ_eig ω)‖ ^ 2 := sq_pos_of_ne_zero h_zero
        have h_quad := (commute_opEigenbasis_quadForm_eq H P hH hP h_comm ω).2.1
        have h_low := h_lower (ψ_eig ω)
        rw [h_quad] at h_low
        have hE_ge : E_min ≤ E_eig ω := le_of_mul_le_mul_right h_low h_sq_pos
        have h_exp_le : Real.exp (-s * E_eig ω) ≤ C := by apply Real.exp_le_exp.mpr; nlinarith
        exact mul_le_mul_of_nonneg_right h_exp_le (norm_nonneg _)
    rw [h_norm_eq]
    have h_lhs_nn : 0 ≤ Real.exp (-s * E_eig ω) * ‖inner ℂ (ψ_eig ω) (P φ)‖ :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (norm_nonneg _)
    nlinarith
  have h_sq_le :
      ‖(gibbsBoltzmannOp ψ_eig E_eig s * P) φ‖ ^ 2 ≤ (C * ‖φ‖) ^ 2 := by
    calc ‖(gibbsBoltzmannOp ψ_eig E_eig s * P) φ‖ ^ 2
      _ = ∑ ω : ManyBodyConfig Site,
            ‖inner ℂ (ψ_eig ω) ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)‖ ^ 2 :=
        (opEigenbasis_parseval H hH _).symm
      _ ≤ ∑ ω : ManyBodyConfig Site, C ^ 2 * ‖inner ℂ (ψ_eig ω) (P φ)‖ ^ 2 :=
        Finset.sum_le_sum fun ω _ => h_term_le ω
      _ = C ^ 2 * ∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) (P φ)‖ ^ 2 := by rw [← Finset.mul_sum]
      _ = C ^ 2 * ‖P φ‖ ^ 2 := by rw [opEigenbasis_parseval H hH (P φ)]
      _ ≤ C ^ 2 * ‖φ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (isStarProjection_norm_sq_apply_le hP φ) (sq_nonneg C)
      _ = (C * ‖φ‖) ^ 2 := by ring
  have h_rhs_nn : 0 ≤ C * ‖φ‖ := mul_nonneg hC_nonneg (norm_nonneg φ)
  nlinarith [norm_nonneg ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)]

/-- **Exponential Decay Absorption Helper for $\beta \ge 16$
    (`beta_exp_neg_half_and_three_quarters_le_one`)** -/
theorem beta_exp_neg_half_and_three_quarters_le_one {β : ℝ} (hβ : 16 ≤ β) :
    β * Real.exp (β * (1 / 4 : ℝ)) * Real.exp (-(3 / 4 : ℝ) * β) ≤ 1 ∧
    2 * β * Real.exp (-(3 / 4 : ℝ) * β) ≤ 1 := by
  have h_e1 : β / 4 + 1 ≤ Real.exp (β / 4) := Real.add_one_le_exp (β / 4)
  have h_sq : β ≤ (Real.exp (β / 4)) ^ 2 := by nlinarith
  have h_exp_half : (Real.exp (β / 4)) ^ 2 = Real.exp (β / 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h_beta_le : β ≤ Real.exp (β / 2) := h_exp_half ▸ h_sq
  have h_two_le : (2 : ℝ) ≤ Real.exp (β / 4) := by linarith
  have h_2beta_le : 2 * β ≤ Real.exp ((3 / 4 : ℝ) * β) := by
    calc 2 * β
      _ ≤ Real.exp (β / 4) * Real.exp (β / 2) :=
          mul_le_mul h_two_le h_beta_le (by linarith) (le_of_lt (Real.exp_pos _))
      _ = Real.exp ((3 / 4 : ℝ) * β) := by rw [← Real.exp_add]; congr 1; ring
  constructor
  · have h_mul := mul_le_mul_of_nonneg_right h_beta_le (le_of_lt (Real.exp_pos (-(β / 2))))
    have h_lhs : β * Real.exp (β * (1 / 4 : ℝ)) * Real.exp (-(3 / 4 : ℝ) * β) =
        β * Real.exp (-(β / 2)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have h_rhs : Real.exp (β / 2) * Real.exp (-(β / 2)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linarith
  · have h_mul := mul_le_mul_of_nonneg_right h_2beta_le (le_of_lt (Real.exp_pos (-(3 / 4 : ℝ) * β)))
    have h_rhs : Real.exp ((3 / 4 : ℝ) * β) * Real.exp (-(3 / 4 : ℝ) * β) = 1 := by
      rw [← Real.exp_add]
      have h_z : (3 / 4 : ℝ) * β + -(3 / 4 : ℝ) * β = 0 := by ring
      rw [h_z, Real.exp_zero]
    linarith

end SpacetimeWorldlineKP

end
