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
import Mathlib.Analysis.PSeries
import Proofs.KMSSafeSubspaceODE.NormTransferAndDiracCancellation

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

noncomputable section

/-!
# Unitary Operator-Norm Helpers, Collar Difference Sandwiches, and Superpolynomial Summability

Establishes unitary operator-norm bounds (`unitary_norm_le_one`, `unitary_star_norm_le_one`), collar difference sandwich estimates (`norm_collar_diff_sandwich_le`, `norm_sub_sandwich_of_le`), and polynomial-weighted summability for superpolynomial decay profiles (`summable_pow_mul_of_superpolynomialDecay`).

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Lemma 6.2 (`lem:dsuper-closure`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
-/

namespace KMSPinchedGibbs

/-! ## 1. Single-Cube Difference Operator Norm Bound -/

lemma unitary_norm_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) :
    ‖U.1‖ ≤ 1 := by
  have hU_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  rw [one_mul]
  have h_inner : inner ℂ (U.1 ψ) (U.1 ψ) = inner ℂ ψ ψ := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ ((U.1† * U.1) ψ) ψ = inner ℂ ψ ψ
    rw [hU_star_self, ContinuousLinearMap.one_apply]
  have h_norm_sq : ‖U.1 ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    have h1 : (((‖U.1 ψ‖ ^ 2 : ℝ) : ℂ)) = (((‖ψ‖ ^ 2 : ℝ) : ℂ)) := by
      simpa [inner_self_eq_norm_sq_to_K] using h_inner
    exact_mod_cast h1
  nlinarith [norm_nonneg (U.1 ψ), norm_nonneg ψ]

lemma norm_adjoint_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) :
    ‖A†‖ = ‖A‖ :=
  ContinuousLinearMap.adjoint.norm_map A

lemma unitary_star_norm_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) :
    ‖U.1†‖ ≤ 1 := by
  rw [norm_adjoint_eq]
  exact unitary_norm_le_one U

lemma norm_mul_le_of_le_one_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : E →L[ℂ] E} (hA : ‖A‖ ≤ 1) : ‖A * B‖ ≤ ‖B‖ :=
  le_trans (ContinuousLinearMap.opNorm_comp_le A B)
    (by simpa [one_mul] using mul_le_mul_of_nonneg_right hA (norm_nonneg B))

lemma norm_mul_le_of_le_one_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : E →L[ℂ] E} (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ ‖A‖ :=
  le_trans (ContinuousLinearMap.opNorm_comp_le A B)
    (by simpa [mul_one] using mul_le_mul_of_nonneg_left hB (norm_nonneg A))

lemma norm_collar_diff_sandwich_le_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (P_σ P_ext D_op : E →L[ℂ] E) (E_K : unitary (E →L[ℂ] E))
    (hPσ : ‖P_σ‖ ≤ 1) (hPext : ‖P_ext‖ ≤ 1) :
    ‖P_σ * D_op * P_σ - E_K.1† * P_ext * D_op * P_ext * E_K.1‖ ≤ 2 * ‖D_op‖ := by
  have hEK : ‖E_K.1‖ ≤ 1 := unitary_norm_le_one E_K
  have hEK_star : ‖E_K.1†‖ ≤ 1 := unitary_star_norm_le_one E_K
  have h1 : ‖P_σ * D_op * P_σ‖ ≤ ‖D_op‖ :=
    le_trans (norm_mul_le_of_le_one_right hPσ) (norm_mul_le_of_le_one_left hPσ)
  have h2 : ‖E_K.1† * P_ext * D_op * P_ext * E_K.1‖ ≤ ‖D_op‖ := by
    calc ‖E_K.1† * P_ext * D_op * P_ext * E_K.1‖
      _ ≤ ‖E_K.1† * P_ext * D_op * P_ext‖ := norm_mul_le_of_le_one_right hEK
      _ ≤ ‖E_K.1† * P_ext * D_op‖ := norm_mul_le_of_le_one_right hPext
      _ = ‖E_K.1† * (P_ext * D_op)‖ := by rw [mul_assoc]
      _ ≤ ‖P_ext * D_op‖ := norm_mul_le_of_le_one_left hEK_star
      _ ≤ ‖D_op‖ := norm_mul_le_of_le_one_left hPext
  calc ‖P_σ * D_op * P_σ - E_K.1† * P_ext * D_op * P_ext * E_K.1‖
    _ ≤ ‖P_σ * D_op * P_σ‖ + ‖E_K.1† * P_ext * D_op * P_ext * E_K.1‖ := norm_sub_le _ _
    _ ≤ ‖D_op‖ + ‖D_op‖ := add_le_add h1 h2
    _ = 2 * ‖D_op‖ := by ring

lemma norm_collar_diff_sandwich_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (σ σ_ext : SyndromeConfig D L)
    (E_K : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (D_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let P_σ := bareSyndromeProjector sys σ
    let P_ext := bareSyndromeProjector sys σ_ext
    ‖P_σ * D_op * P_σ - E_K.1† * P_ext * D_op * P_ext * E_K.1‖ ≤ 2 * ‖D_op‖ := by
  intro P_σ P_ext
  exact norm_collar_diff_sandwich_le_aux P_σ P_ext D_op E_K
    (isStarProjection_norm_le_one (isStarProjection_bareSyndromeProjector sys σ))
    (isStarProjection_norm_le_one (isStarProjection_bareSyndromeProjector sys σ_ext))

lemma ring_sub_sandwich_one_sub {R : Type*} [Ring R] (X S P : R) :
    X - (1 - P) * S * (1 - P) = (X - S) + P * S + (1 - P) * (S * P) := by
  calc X - (1 - P) * S * (1 - P)
    _ = X - ((1 - P) * S - (1 - P) * S * P) := by rw [mul_sub, mul_one]
    _ = X - ((1 - P) * S - (1 - P) * (S * P)) := by rw [mul_assoc]
    _ = X - ((S - P * S) - (1 - P) * (S * P)) := by rw [sub_mul, one_mul]
    _ = (X - S) + P * S + (1 - P) * (S * P) := by abel

lemma norm_sub_sandwich_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X S P : E →L[ℂ] E) {b : ℝ}
    (hXS : ‖X - S‖ ≤ b) (hPS : ‖P * S‖ ≤ b) (hSP : ‖S * P‖ ≤ b) (h1P : ‖1 - P‖ ≤ 1) :
    ‖X - (1 - P) * S * (1 - P)‖ ≤ 3 * b := by
  have h_third : ‖(1 - P) * (S * P)‖ ≤ b :=
    le_trans (norm_mul_le_of_le_one_left h1P) hSP
  rw [ring_sub_sandwich_one_sub X S P]
  have h1 := norm_add_le ((X - S) + P * S) ((1 - P) * (S * P))
  have h2 := norm_add_le (X - S) (P * S)
  linarith

lemma norm_mul_le_of_mul_eq_zero_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P X S : E →L[ℂ] E} {b : ℝ}
    (hPX : P * X = 0) (hP : ‖P‖ ≤ 1) (hXS : ‖X - S‖ ≤ b) :
    ‖P * S‖ ≤ b := by
  have h_eq : P * S = -(P * (X - S)) := by rw [mul_sub, hPX, zero_sub, neg_neg]
  rw [h_eq, norm_neg]
  exact le_trans (norm_mul_le_of_le_one_left hP) hXS

lemma norm_mul_le_of_mul_eq_zero_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P X S : E →L[ℂ] E} {b : ℝ}
    (hXP : X * P = 0) (hP : ‖P‖ ≤ 1) (hXS : ‖X - S‖ ≤ b) :
    ‖S * P‖ ≤ b := by
  have h_eq : S * P = -((X - S) * P) := by rw [sub_mul, hXP, zero_sub, neg_neg]
  rw [h_eq, norm_neg]
  exact le_trans (norm_mul_le_of_le_one_right hP) hXS

lemma norm_mul_selfAdjoint_eq_norm_mul_adjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S P : E →L[ℂ] E) (hP : P† = P) :
    ‖S * P‖ = ‖P * S†‖ := by
  have h_adj : (S * P)† = P * S† := by
    change star (S * P) = P * S†
    rw [star_mul]
    change P† * S† = P * S†
    rw [hP]
  rw [← norm_adjoint_eq (S * P), h_adj]

lemma sub_eq_sub_sub_sub {G : Type*} [AddCommGroup G] (X M_k M_k1 : G) :
    M_k - M_k1 = (X - M_k1) - (X - M_k) := by
  abel

/-! ## 2. Open-Box Syndrome-Collar Multiplicity & Uniform Collar Sum Bound -/

lemma summable_pow_mul_of_superpolynomialDecay {f : ℕ → ℝ}
    (hf_nonneg : ∀ r : ℕ, 0 ≤ f r)
    (hf_decay : SuperpolynomialDecay atTop (fun r : ℕ => (r : ℝ)) f) (n : ℕ) :
    Summable (fun r : ℕ => (r : ℝ) ^ n * f r) := by
  have h_ev : ∀ᶠ r : ℕ in atTop, (r : ℝ) ^ (n + 2) * f r < 1 :=
    (hf_decay (n + 2)).eventually (Iio_mem_nhds zero_lt_one)
  have h_pseries : Summable (fun r : ℕ => ((r : ℝ) ^ 2)⁻¹) := by simp [Real.summable_nat_pow_inv]
  refine Summable.of_norm_bounded_eventually_nat h_pseries ?_
  filter_upwards [h_ev, eventually_ge_atTop 1] with r hr_lt hr_ge
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
  have hr_sq_pos : (0 : ℝ) < (r : ℝ) ^ 2 := pow_pos hr_pos 2
  have h_nonneg : 0 ≤ (r : ℝ) ^ n * f r := mul_nonneg (pow_nonneg (Nat.cast_nonneg r) n) (hf_nonneg r)
  have h_eq : (r : ℝ) ^ n * f r = ((r : ℝ) ^ 2)⁻¹ * ((r : ℝ) ^ (n + 2) * f r) := by
    have h_alg : (r : ℝ) ^ (n + 2) * f r = (r : ℝ) ^ 2 * ((r : ℝ) ^ n * f r) := by rw [pow_add]; ring
    rw [h_alg, inv_mul_cancel_left₀ (ne_of_gt hr_sq_pos)]
  rw [Real.norm_of_nonneg h_nonneg, h_eq]
  exact le_trans (mul_le_mul_of_nonneg_left (le_of_lt hr_lt) (inv_nonneg.mpr (le_of_lt hr_sq_pos))) (mul_one _).le

end KMSPinchedGibbs

end
