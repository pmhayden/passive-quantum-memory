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
import Proofs.LiebRobinson.BochnerQuasiLocality
import Proofs.LiebRobinson.DuhamelAndGronwall
import Proofs.BandLimitedFilter.EigenprojEvolutionAndBlockDecomp

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Off-Diagonal Fourier Vanishing for Compactly Supported Filter Weights

Proves that the compactly supported raised-cosine filter weight `bhFilterWeight` annihilates off-diagonal harmonic transitions (`offDiag_right_zero_w_BH11_of_int_gap`, `offDiag_left_zero_w_BH11_of_int_gap`) for commuting-projector Hamiltonians with integer spectral excitations. Establishes exact two-block decomposition (`bochnerFilteredOp_w_BH11_offDiag_and_block_decomp_of_int_gap`) across finite multi-frequency operator decompositions separated by at least the spectral gap.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (67) (`eq:wBP-fourier-props`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

/-!
## 1. Banach-Algebra Scalar Exponential Identity $\exp(z \bullet 1) = e^z \bullet 1$
-/

/-- Power of a scalar multiple of the identity operator: $(z \bullet 1)^n = z^n \bullet 1$. -/
lemma clm_smul_one_pow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (z : ℂ) (n : ℕ) :
    (z • (1 : E →L[ℂ] E)) ^ n = (z ^ n) • (1 : E →L[ℂ] E) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_smul]
  | succ n ih =>
    rw [pow_succ', ih, smul_mul_assoc, one_mul, smul_smul, ← pow_succ']

/-- In the operator algebra $E \to_L[\mathbb{C}] E$, the Banach-space exponential of a scalar
    multiple of the identity equals the scalar complex exponential times the identity:
    $\exp(z \bullet 1) = e^z \bullet 1$. -/
theorem clm_exp_smul_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (z : ℂ) :
    NormedSpace.exp (z • (1 : E →L[ℂ] E)) = Complex.exp z • (1 : E →L[ℂ] E) := by
  let L : ℂ →L[ℂ] (E →L[ℂ] E) :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (1 : E →L[ℂ] E)
  have hL_apply : ∀ w : ℂ, L w = w • (1 : E →L[ℂ] E) := fun _ => rfl
  have h_sum_C : Summable (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • z ^ n) :=
    NormedSpace.expSeries_summable_of_mem_ball' (𝕂 := ℂ) z
      ((NormedSpace.expSeries_radius_eq_top ℂ ℂ).symm ▸ edist_lt_top _ _)
  have h_exp_C : Complex.exp z = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • z ^ n := by
    rw [Complex.exp_eq_exp_ℂ]
    exact congrFun (NormedSpace.exp_eq_tsum ℂ) z
  have h_term : ∀ n : ℕ,
      ((Nat.factorial n : ℂ)⁻¹) • (z • (1 : E →L[ℂ] E)) ^ n =
        L (((Nat.factorial n : ℂ)⁻¹) • z ^ n) := by
    intro n
    rw [clm_smul_one_pow, hL_apply, smul_smul, smul_eq_mul]
  calc NormedSpace.exp (z • (1 : E →L[ℂ] E))
    _ = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • (z • (1 : E →L[ℂ] E)) ^ n :=
      clm_exp_eq_tsum (z • (1 : E →L[ℂ] E))
    _ = ∑' n : ℕ, L (((Nat.factorial n : ℂ)⁻¹) • z ^ n) := tsum_congr h_term
    _ = L (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • z ^ n) := (L.map_tsum h_sum_C).symm
    _ = L (Complex.exp z) := by rw [← h_exp_C]
    _ = Complex.exp z • (1 : E →L[ℂ] E) := rfl

/-!
## 2. Exact Off-Diagonal Integrand Reduction and Annihilation for Integer Gaps
-/

/-- Helper: $(a \bullet 1) * M * (b \bullet 1) = (a * b) \bullet M$. -/
lemma clm_smul_one_sandwich {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : ℂ) (M : E →L[ℂ] E) :
    (a • (1 : E →L[ℂ] E)) * M * (b • (1 : E →L[ℂ] E)) = (a * b) • M := by
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul, mul_comm b a]

/-- If $P * P = P$, then $(1 - P) * (1 - P) = 1 - P$. -/
lemma one_sub_idem_of_idem {R : Type*} [Ring R] {P : R} (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  rw [mul_sub, sub_mul, sub_mul, mul_one, mul_one, one_mul, hP, sub_self, sub_zero]

/-- Pointwise evaluation of the right off-diagonal integrand when $(1 - P) H' = (E_0 + \Delta) (1 - P)$:
    $$\exp(i t E_0 \cdot 1) (P X (1 - P)) \exp(-i t H') = e^{-i \Delta t} \bullet (P X (1 - P)).$$ -/
lemma offDiag_right_integrand_eq_of_eigenvalue {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P H' : E →L[ℂ] E} {E0 Δ : ℝ}
    (_hP_idem : P * P = P)
    (h1P_H' : (1 - P) * H' = (((E0 + Δ : ℝ) : ℂ)) • (1 - P))
    (X : E →L[ℂ] E) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) • (1 : E →L[ℂ] E)) *
      (P * X * (1 - P)) *
      NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H') =
    Complex.exp ((Complex.I * ((-Δ : ℝ) : ℂ)) * (t : ℂ)) • (P * X * (1 - P)) := by
  have h_right := clm_proj_mul_exp_smul h1P_H' (-(Complex.I * (t : ℂ)))
  have h_step1 :
      (P * X * (1 - P)) * NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H') =
        (P * X * (1 - P)) *
          NormedSpace.exp (((-(Complex.I * (t : ℂ))) * ((E0 + Δ : ℝ) : ℂ)) • (1 : E →L[ℂ] E)) := by
    rw [mul_assoc (P * X), h_right, ← mul_assoc (P * X)]
  rw [mul_assoc, h_step1, ← mul_assoc, clm_exp_smul_one, clm_exp_smul_one,
    clm_smul_one_sandwich, ← Complex.exp_add]
  have h_exp :
      Complex.I * (t : ℂ) * (E0 : ℂ) + -(Complex.I * (t : ℂ)) * ((E0 + Δ : ℝ) : ℂ) =
        (Complex.I * ((-Δ : ℝ) : ℂ)) * (t : ℂ) := by
    push_cast; ring
  rw [h_exp]

/-- Pointwise evaluation of the left off-diagonal integrand when $H' (1 - P) = (E_0 + \Delta) (1 - P)$:
    $$\exp(i t H') ((1 - P) X P) \exp(-i t E_0 \cdot 1) = e^{i \Delta t} \bullet ((1 - P) X P).$$ -/
lemma offDiag_left_integrand_eq_of_eigenvalue {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P H' : E →L[ℂ] E} {E0 Δ : ℝ}
    (_hP_idem : P * P = P)
    (hH'_1P : H' * (1 - P) = (((E0 + Δ : ℝ) : ℂ)) • (1 - P))
    (X : E →L[ℂ] E) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • H') *
      ((1 - P) * X * P) *
      NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) • (1 : E →L[ℂ] E)) =
    Complex.exp ((Complex.I * (Δ : ℂ)) * (t : ℂ)) • ((1 - P) * X * P) := by
  have h_left := clm_exp_smul_mul_proj hH'_1P (Complex.I * (t : ℂ))
  have h_step1 :
      NormedSpace.exp ((Complex.I * (t : ℂ)) • H') * ((1 - P) * X * P) =
        NormedSpace.exp (((Complex.I * (t : ℂ)) * ((E0 + Δ : ℝ) : ℂ)) • (1 : E →L[ℂ] E)) *
          ((1 - P) * X * P) := by
    rw [mul_assoc (1 - P) X P, ← mul_assoc _ (1 - P), h_left, mul_assoc _ (1 - P), ← mul_assoc (1 - P)]
  rw [h_step1, clm_exp_smul_one, clm_exp_smul_one, clm_smul_one_sandwich, ← Complex.exp_add]
  have h_exp :
      Complex.I * (t : ℂ) * ((E0 + Δ : ℝ) : ℂ) + -(Complex.I * (t : ℂ) * (E0 : ℂ)) =
        (Complex.I * (Δ : ℂ)) * (t : ℂ) := by
    push_cast; ring
  rw [h_exp]

/-- Exact vanishing of the right off-diagonal integral for `bhFilterWeight` under a nonzero integer
    spectral gap $k \in \mathbb{Z} \setminus \{0\}$. -/
theorem offDiag_right_zero_w_BH11_of_int_gap {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P H' : E →L[ℂ] E} {E0 : ℝ} {k : ℤ} (hk : k ≠ 0)
    (hP_idem : P * P = P)
    (h1P_H' : (1 - P) * H' = (((E0 + (k : ℝ) : ℝ) : ℂ)) • (1 - P))
    (X : E →L[ℂ] E) :
    (∫ t : ℝ, bhFilterWeight t •
      (NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) • (1 : E →L[ℂ] E)) *
        (P * X * (1 - P)) *
        NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H'))) = 0 := by
  have h_integrand :
      (fun t : ℝ => bhFilterWeight t •
        (NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) • (1 : E →L[ℂ] E)) *
          (P * X * (1 - P)) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H'))) =
      (fun t : ℝ =>
        (bhFilterWeight t * Complex.exp ((Complex.I * ((-k : ℤ) : ℂ)) * (t : ℂ))) •
          (P * X * (1 - P))) := by
    funext t
    rw [offDiag_right_integrand_eq_of_eigenvalue hP_idem h1P_H' X t, smul_smul]
    push_cast; rfl
  rw [h_integrand]
  exact integral_w_BH11_smul_exp_int_eq_zero (neg_ne_zero.mpr hk) (P * X * (1 - P))

/-- Exact vanishing of the left off-diagonal integral for `bhFilterWeight` under a nonzero integer
    spectral gap $k \in \mathbb{Z} \setminus \{0\}$. -/
theorem offDiag_left_zero_w_BH11_of_int_gap {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {P H' : E →L[ℂ] E} {E0 : ℝ} {k : ℤ} (hk : k ≠ 0)
    (hP_idem : P * P = P)
    (hH'_1P : H' * (1 - P) = (((E0 + (k : ℝ) : ℝ) : ℂ)) • (1 - P))
    (X : E →L[ℂ] E) :
    (∫ t : ℝ, bhFilterWeight t •
      (NormedSpace.exp ((Complex.I * (t : ℂ)) • H') *
        ((1 - P) * X * P) *
        NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) • (1 : E →L[ℂ] E)))) = 0 := by
  have h_integrand :
      (fun t : ℝ => bhFilterWeight t •
        (NormedSpace.exp ((Complex.I * (t : ℂ)) • H') *
          ((1 - P) * X * P) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) • (1 : E →L[ℂ] E)))) =
      (fun t : ℝ =>
        (bhFilterWeight t * Complex.exp ((Complex.I * (k : ℂ)) * (t : ℂ))) •
          ((1 - P) * X * P)) := by
    funext t
    rw [offDiag_left_integrand_eq_of_eigenvalue hP_idem hH'_1P X t, smul_smul]
    push_cast; rfl
  rw [h_integrand]
  exact integral_w_BH11_smul_exp_int_eq_zero hk ((1 - P) * X * P)

/-!
## 3. Multi-Harmonic Spectral Sum Off-Diagonal Annihilation (Commuting Projector Spectrum)
-/

/-- If the excited projector $1 - P = \sum_{a \in S} Q_a$ decomposes into a finite sum of
    eigenprojectors $Q_a$ of $H'$ with nonzero integer excitation energies $k_a \in \mathbb{Z} \setminus \{0\}$
    above $E_0$, then `offDiag_right_zero` holds for `bhFilterWeight`. -/
theorem offDiag_right_zero_w_BH11_of_spectral_sum {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {α : Type*} (S : Finset α) (Q : α → (E →L[ℂ] E)) (k : α → ℤ)
    {P H' : E →L[ℂ] E} {E0 : ℝ}
    (h1P_eq : 1 - P = ∑ a ∈ S, Q a)
    (hk_ne : ∀ a ∈ S, k a ≠ 0)
    (hQ_H' : ∀ a ∈ S, Q a * H' = (((E0 + (k a : ℝ) : ℝ) : ℂ)) • Q a)
    (X : E →L[ℂ] E) :
    (∫ t : ℝ, bhFilterWeight t •
      (NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) • (1 : E →L[ℂ] E)) *
        (P * X * (1 - P)) *
        NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H'))) = 0 := by
  have h_sum_eq : ∀ t : ℝ,
      bhFilterWeight t •
        (NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) • (1 : E →L[ℂ] E)) *
          (P * X * (1 - P)) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H')) =
      ∑ a ∈ S,
        (bhFilterWeight t * Complex.exp ((Complex.I * ((-k a : ℤ) : ℂ)) * (t : ℂ))) •
          (P * X * Q a) := by
    intro t
    rw [h1P_eq, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have h_right := clm_proj_mul_exp_smul (hQ_H' a ha) (-(Complex.I * (t : ℂ)))
    have h_assoc :
        NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) • (1 : E →L[ℂ] E)) *
          (P * X * Q a) * NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H') =
        NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) • (1 : E →L[ℂ] E)) *
          (P * X * Q a) *
          NormedSpace.exp (((-(Complex.I * (t : ℂ))) * ((E0 + (k a : ℝ) : ℝ) : ℂ)) • (1 : E →L[ℂ] E)) := by
      rw [mul_assoc _ (P * X * Q a), mul_assoc (P * X), h_right, ← mul_assoc (P * X), ← mul_assoc]
    rw [h_assoc, clm_exp_smul_one, clm_exp_smul_one, clm_smul_one_sandwich, smul_smul, ← Complex.exp_add]
    have h_exp :
        Complex.I * (t : ℂ) * (E0 : ℂ) + -(Complex.I * (t : ℂ)) * ((E0 + (k a : ℝ) : ℝ) : ℂ) =
          (Complex.I * ((-k a : ℤ) : ℂ)) * (t : ℂ) := by
      push_cast; ring
    rw [h_exp]
  simp_rw [h_sum_eq]
  rw [integral_finset_sum S]
  · refine Finset.sum_eq_zero fun a ha => ?_
    exact integral_w_BH11_smul_exp_int_eq_zero (neg_ne_zero.mpr (hk_ne a ha)) (P * X * Q a)
  · intro a _
    have hcont : Continuous (fun t : ℝ =>
        Complex.exp ((Complex.I * ((-k a : ℤ) : ℂ)) * (t : ℂ)) • (P * X * Q a)) := by fun_prop
    simpa [smul_smul] using (integrable_and_integral_w_BH11_smul_of_continuous hcont).1

/-- If the excited projector $1 - P = \sum_{a \in S} Q_a$ decomposes into a finite sum of
    eigenprojectors $Q_a$ of $H'$ with nonzero integer excitation energies $k_a \in \mathbb{Z} \setminus \{0\}$
    above $E_0$, then `offDiag_left_zero` holds for `bhFilterWeight`. -/
theorem offDiag_left_zero_w_BH11_of_spectral_sum {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {α : Type*} (S : Finset α) (Q : α → (E →L[ℂ] E)) (k : α → ℤ)
    {P H' : E →L[ℂ] E} {E0 : ℝ}
    (h1P_eq : 1 - P = ∑ a ∈ S, Q a)
    (hk_ne : ∀ a ∈ S, k a ≠ 0)
    (hH'_Q : ∀ a ∈ S, H' * Q a = (((E0 + (k a : ℝ) : ℝ) : ℂ)) • Q a)
    (X : E →L[ℂ] E) :
    (∫ t : ℝ, bhFilterWeight t •
      (NormedSpace.exp ((Complex.I * (t : ℂ)) • H') *
        ((1 - P) * X * P) *
        NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) • (1 : E →L[ℂ] E)))) = 0 := by
  have h_sum_eq : ∀ t : ℝ,
      bhFilterWeight t •
        (NormedSpace.exp ((Complex.I * (t : ℂ)) • H') *
          ((1 - P) * X * P) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) • (1 : E →L[ℂ] E))) =
      ∑ a ∈ S,
        (bhFilterWeight t * Complex.exp ((Complex.I * (k a : ℂ)) * (t : ℂ))) •
          (Q a * X * P) := by
    intro t
    rw [h1P_eq, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    have h_left := clm_exp_smul_mul_proj (hH'_Q a ha) (Complex.I * (t : ℂ))
    have h_assoc :
        NormedSpace.exp ((Complex.I * (t : ℂ)) • H') * (Q a * X * P) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) • (1 : E →L[ℂ] E)) =
        NormedSpace.exp (((Complex.I * (t : ℂ)) * ((E0 + (k a : ℝ) : ℝ) : ℂ)) • (1 : E →L[ℂ] E)) *
          (Q a * X * P) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) • (1 : E →L[ℂ] E)) := by
      rw [mul_assoc (Q a) X P, ← mul_assoc _ (Q a), h_left, mul_assoc _ (Q a), ← mul_assoc (Q a)]
    rw [h_assoc, clm_exp_smul_one, clm_exp_smul_one, clm_smul_one_sandwich, smul_smul, ← Complex.exp_add]
    have h_exp :
        Complex.I * (t : ℂ) * ((E0 + (k a : ℝ) : ℝ) : ℂ) + -(Complex.I * (t : ℂ) * (E0 : ℂ)) =
          (Complex.I * (k a : ℂ)) * (t : ℂ) := by
      push_cast; ring
    rw [h_exp]
  simp_rw [h_sum_eq]
  rw [integral_finset_sum S]
  · refine Finset.sum_eq_zero fun a ha => ?_
    exact integral_w_BH11_smul_exp_int_eq_zero (hk_ne a ha) (Q a * X * P)
  · intro a _
    have hcont : Continuous (fun t : ℝ =>
        Complex.exp ((Complex.I * (k a : ℂ)) * (t : ℂ)) • (Q a * X * P)) := by fun_prop
    simpa [smul_smul] using (integrable_and_integral_w_BH11_smul_of_continuous hcont).1

/-!
## 4. Exact Off-Diagonal Block Annihilation of `bochnerFilteredOp H' bhFilterWeight V`
-/

/-- General block decomposition of `bochnerFilteredOp H' w X` directly from ground eigenvalue
    and off-diagonal integral vanishing (without requiring `dressed_relative_form_bound`). -/
lemma bochnerFilteredOp_block_decomp_of_offDiag_zero
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E0 : ℝ} {w : ℝ → ℂ}
    (hP : IsStarProjection P)
    (hHP : H' * P = (E0 : ℂ) • P)
    (hPH : P * H' = (E0 : ℂ) • P)
    (hw_one : (∫ t : ℝ, w t) = 1)
    (hint : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Integrable (fun t : ℝ => w t • heisenbergFlow H' t X))
    (h_right : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      (∫ t : ℝ, w t •
        (NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) •
            (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) *
          (P * X * (1 - P)) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H'))) = 0)
    (h_left : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      (∫ t : ℝ, w t •
        (NormedSpace.exp ((Complex.I * (t : ℂ)) • H') *
          ((1 - P) * X * P) *
          NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) •
            (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)))) = 0)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let Y := bochnerFilteredOp H' w X
    P * Y * P = P * X * P ∧
    P * Y * (1 - P) = 0 ∧
    (1 - P) * Y * P = 0 ∧
    (P * Y * P + (1 - P) * Y * (1 - P) = Y) ∧
    Commute Y P ∧
    (1 - P) * Y * (1 - P) = bochnerFilteredOp H' w ((1 - P) * X * (1 - P)) := by
  intro Y
  have hCommHP : Commute H' P := by rw [commute_iff_eq, hHP, hPH]
  have hP_Upos : ∀ t : ℝ,
      P * timeEvolutionOp H' t =
      NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) * P := by
    intro t
    change P * NormedSpace.exp ((Complex.I * (t : ℂ)) • H') = _
    rw [clm_proj_mul_exp_smul hPH (Complex.I * (t : ℂ)),
      (commute_exp_smul_one (Complex.I * (t : ℂ) * (E0 : ℂ)) P).eq]
  have hUneg_P : ∀ t : ℝ,
      timeEvolutionOp H' (-t) * P =
      P * NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) := by
    intro t
    rw [timeEvolutionOp_neg_eq, clm_exp_smul_mul_proj hHP (-(Complex.I * (t : ℂ))), neg_mul,
      (commute_exp_smul_one (-(Complex.I * (t : ℂ) * (E0 : ℂ))) P).eq]
  have h1P_Upos : ∀ t : ℝ,
      (1 - P) * timeEvolutionOp H' t = timeEvolutionOp H' t * (1 - P) := by
    intro t
    exact ((Commute.one_right _).sub_right
      ((commute_smul_left_clm hCommHP (Complex.I * (t : ℂ))).exp_left)).symm.eq
  have hUneg_1P : ∀ t : ℝ,
      timeEvolutionOp H' (-t) * (1 - P) = (1 - P) * timeEvolutionOp H' (-t) := by
    intro t
    exact ((Commute.one_right _).sub_right
      ((commute_smul_left_clm hCommHP (Complex.I * ((-t : ℝ) : ℂ))).exp_left)).eq
  have h_PYP : P * Y * P = P * X * P := by
    change P * (∫ t : ℝ, w t • heisenbergFlow H' t X) * P = P * X * P
    rw [clm_sandwich_integral_smul P P w _ (hint X)]
    have h_pt : (fun t : ℝ => w t • (P * heisenbergFlow H' t X * P)) =
        (fun t : ℝ => w t • (P * X * P)) := by
      funext t
      dsimp [heisenbergFlow]
      rw [monoid_diag_flow_id (hP_Upos t) (hUneg_P t)
        (commute_exp_smul_one (-(Complex.I * (t : ℂ) * (E0 : ℂ))) (P * X * P))
        (exp_smul_one_mul_neg (Complex.I * (t : ℂ) * (E0 : ℂ)))]
    rw [h_pt, integral_smul_const, hw_one, one_smul]
  have h_PY1P : P * Y * (1 - P) = 0 := by
    change P * (∫ t : ℝ, w t • heisenbergFlow H' t X) * (1 - P) = 0
    rw [clm_sandwich_integral_smul P (1 - P) w _ (hint X), ← h_right X]
    congr 1; funext t; dsimp [heisenbergFlow]
    rw [monoid_sandwich_rew (hP_Upos t) (hUneg_1P t), timeEvolutionOp_neg_eq]
  have h_1PYP : (1 - P) * Y * P = 0 := by
    change (1 - P) * (∫ t : ℝ, w t • heisenbergFlow H' t X) * P = 0
    rw [clm_sandwich_integral_smul (1 - P) P w _ (hint X), ← h_left X]
    congr 1; funext t; dsimp [heisenbergFlow]
    rw [monoid_sandwich_rew (h1P_Upos t) (hUneg_P t)]; rfl
  have h_1PY1P : (1 - P) * Y * (1 - P) = bochnerFilteredOp H' w ((1 - P) * X * (1 - P)) := by
    change (1 - P) * (∫ t : ℝ, w t • heisenbergFlow H' t X) * (1 - P) =
      ∫ t : ℝ, w t • heisenbergFlow H' t ((1 - P) * X * (1 - P))
    rw [clm_sandwich_integral_smul (1 - P) (1 - P) w _ (hint X)]
    congr 1; funext t; dsimp [heisenbergFlow]
    rw [monoid_sandwich_rew (h1P_Upos t) (hUneg_1P t)]
  rcases ring_spectral_decomp_of_offDiag_zero hP.isIdempotentElem.eq h_PY1P h_1PYP with
    ⟨h_spec_eq, h_comm_Y⟩
  exact ⟨h_PYP, h_PY1P, h_1PYP, h_spec_eq, h_comm_Y, h_1PY1P⟩

/-- **Exact Off-Diagonal Annihilation and Block Decomposition for `bhFilterWeight` under Integer Gap**:
    For any star projection $P$ and Hamiltonian $H'$ satisfying $H' P = E_0 P$, $P H' = E_0 P$,
    $(1 - P) H' = (E_0 + k)(1 - P)$, and $H' (1 - P) = (E_0 + k)(1 - P)$ with $k \in \mathbb{Z} \setminus \{0\}$,
    the Bochner filtered operator $\mathcal{I}_{w_{\mathrm{BH11}}}(H', V) = \mathrm{bochnerFilteredOp}\ H'\ w_{\mathrm{BH11}}\ V$
    satisfies:
    1. $P \, \mathcal{I}_{w_{\mathrm{BH11}}}(H', V) \, P = P V P$,
    2. $P \, \mathcal{I}_{w_{\mathrm{BH11}}}(H', V) \, (1 - P) = 0$,
    3. $(1 - P) \, \mathcal{I}_{w_{\mathrm{BH11}}}(H', V) \, P = 0$,
    4. $[\mathcal{I}_{w_{\mathrm{BH11}}}(H', V), P] = 0$,
    5. $(1 - P) \, \mathcal{I}_{w_{\mathrm{BH11}}}(H', V) \, (1 - P) = \mathcal{I}_{w_{\mathrm{BH11}}}(H', (1 - P) V (1 - P))$. -/
theorem bochnerFilteredOp_w_BH11_offDiag_and_block_decomp_of_int_gap
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E0 : ℝ} {k : ℤ} (hk : k ≠ 0)
    (hP : IsStarProjection P)
    (hHP : H' * P = (E0 : ℂ) • P)
    (hPH : P * H' = (E0 : ℂ) • P)
    (h1P_H' : (1 - P) * H' = (((E0 + (k : ℝ) : ℝ) : ℂ)) • (1 - P))
    (hH'_1P : H' * (1 - P) = (((E0 + (k : ℝ) : ℝ) : ℂ)) • (1 - P))
    (V : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let filteredOp := bochnerFilteredOp H' bhFilterWeight V
    P * filteredOp * P = P * V * P ∧
    P * filteredOp * (1 - P) = 0 ∧
    (1 - P) * filteredOp * P = 0 ∧
    Commute filteredOp P ∧
    (1 - P) * filteredOp * (1 - P) = bochnerFilteredOp H' bhFilterWeight ((1 - P) * V * (1 - P)) := by
  have hP_idem : P * P = P := hP.isIdempotentElem.eq
  rcases bochnerFilteredOp_block_decomp_of_offDiag_zero hP hHP hPH integral_w_BH11_eq_one
      (integrable_w_BH11_smul_heisenbergFlow H')
      (offDiag_right_zero_w_BH11_of_int_gap hk hP_idem h1P_H')
      (offDiag_left_zero_w_BH11_of_int_gap hk hP_idem hH'_1P) V with
    ⟨h1, h2, h3, _, h5, h6⟩
  exact ⟨h1, h2, h3, h5, h6⟩

/-- **Special Case $H' = 1 - P$ (`bochnerFilteredOp_one_sub_proj_w_BH11`)**:
    For any star projection $P$ and perturbation $V$, filtering $V$ under the two-level projector
    Hamiltonian $H' = 1 - P$ with `bhFilterWeight` identically annihilates both off-diagonal blocks
    and preserves the diagonal blocks:
    $$\mathrm{bochnerFilteredOp}\ (1 - P)\ w_{\mathrm{BH11}}\ V = P V P + (1 - P) V (1 - P).$$ -/
theorem bochnerFilteredOp_one_sub_proj_w_BH11
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P)
    (V : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let filteredOp := bochnerFilteredOp (1 - P) bhFilterWeight V
    P * filteredOp * P = P * V * P ∧
    P * filteredOp * (1 - P) = 0 ∧
    (1 - P) * filteredOp * P = 0 ∧
    Commute filteredOp P ∧
    filteredOp = P * V * P + (1 - P) * V * (1 - P) := by
  have hP_idem : P * P = P := hP.isIdempotentElem.eq
  have h1P_idem : (1 - P) * (1 - P) = 1 - P := one_sub_idem_of_idem hP_idem
  have hHP : (1 - P) * P = ((0 : ℝ) : ℂ) • P := by
    rw [sub_mul, one_mul, hP_idem, sub_self]
    symm
    exact zero_smul ℂ P
  have hPH : P * (1 - P) = ((0 : ℝ) : ℂ) • P := by
    rw [mul_sub, mul_one, hP_idem, sub_self]
    symm
    exact zero_smul ℂ P
  have h1P_H' : (1 - P) * (1 - P) = (((0 + ((1 : ℤ) : ℝ) : ℝ) : ℂ)) • (1 - P) := by
    simp [h1P_idem]
  have hH'_1P : (1 - P) * (1 - P) = (((0 + ((1 : ℤ) : ℝ) : ℝ) : ℂ)) • (1 - P) := by
    simp [h1P_idem]
  rcases bochnerFilteredOp_w_BH11_offDiag_and_block_decomp_of_int_gap
      (k := 1) (by decide) hP hHP hPH h1P_H' hH'_1P V with
    ⟨hPP, hP1P, h1PP, hComm, h1P1P⟩
  have h_comm_exc : Commute (1 - P) ((1 - P) * V * (1 - P)) := by
    rw [commute_iff_eq]
    calc (1 - P) * ((1 - P) * V * (1 - P))
      _ = ((1 - P) * (1 - P)) * V * (1 - P) := by simp only [mul_assoc]
      _ = (1 - P) * V * ((1 - P) * (1 - P)) := by rw [h1P_idem]
      _ = ((1 - P) * V * (1 - P)) * (1 - P) := by simp only [mul_assoc]
  have h_exc_fixed :
      bochnerFilteredOp (1 - P) bhFilterWeight ((1 - P) * V * (1 - P)) = (1 - P) * V * (1 - P) := by
    unfold bochnerFilteredOp
    have h_flow : ∀ t : ℝ,
        heisenbergFlow (1 - P) t ((1 - P) * V * (1 - P)) = (1 - P) * V * (1 - P) := by
      intro t
      unfold heisenbergFlow
      have h_comm_exp : Commute (timeEvolutionOp (1 - P) t) ((1 - P) * V * (1 - P)) := by
        unfold timeEvolutionOp
        exact (commute_smul_left_clm h_comm_exc (Complex.I * (t : ℂ))).exp_left
      rw [h_comm_exp.eq, mul_assoc, (timeEvolutionOp_mul_neg (1 - P) t).1, mul_one]
    simp_rw [h_flow]
    rw [integral_smul_const, integral_w_BH11_eq_one, one_smul]
  have h_decomp := (ring_spectral_decomp_of_offDiag_zero hP_idem hP1P h1PP).1
  rw [hPP, h1P1P, h_exc_fixed] at h_decomp
  exact ⟨hPP, hP1P, h1PP, hComm, h_decomp.symm⟩

end
