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

import Proofs.CenteredBallBHM.BaseBHMFormAndBootstrapBridge

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Ground-Subspace Splitting and Excited-Band Quadratic Form Bounds

Derives quantitative ground-subspace operator-norm splitting bounds and excited-band quadratic form lower bounds from a unitary relative form bound on `U^* (H0 + V) U - H0 - e0 • 1` under ground-projector commutation. Shows that a relative form slope at most `1/4` yields at least `(3/4)` of the unperturbed check energy on the orthogonal complement of the dressed ground space.

## References

* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

/-- Conjugating `sys.P0` by `U_dress` yields a star projection `U_dress.1 * sys.P0 * U_dress.1†`. -/
lemma dressed_ground_proj_isStarProjection {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    IsStarProjection (U_dress.1 * sys.P0 * U_dress.1†) := by
  have hP0 : IsStarProjection sys.P0 := sys.isStarProjection_P0
  have hU_star_self : U_dress.1† * U_dress.1 = 1 := Unitary.coe_star_mul_self U_dress
  have h_idem : IsIdempotentElem (U_dress.1 * sys.P0 * U_dress.1†) := by
    rw [IsIdempotentElem]
    calc (U_dress.1 * sys.P0 * U_dress.1†) * (U_dress.1 * sys.P0 * U_dress.1†)
      _ = U_dress.1 * (sys.P0 * (U_dress.1† * U_dress.1) * sys.P0) * U_dress.1† := by
          simp only [mul_assoc]
      _ = U_dress.1 * (sys.P0 * sys.P0) * U_dress.1† := by rw [hU_star_self, mul_one]
      _ = U_dress.1 * sys.P0 * U_dress.1† := by rw [hP0.isIdempotentElem.eq]
  have h_sa : IsSelfAdjoint (U_dress.1 * sys.P0 * U_dress.1†) := by
    rw [IsSelfAdjoint]
    change star (U_dress.1 * sys.P0 * star U_dress.1) = U_dress.1 * sys.P0 * star U_dress.1
    rw [star_mul, star_mul, star_star, hP0.isSelfAdjoint.star_eq, mul_assoc]
  exact ⟨h_idem, h_sa⟩

/-- **Dressed Ground-Space Star-Projection & Hamiltonian Commutation
    (`dressed_ground_proj_isStarProjection_and_commute`)**:
    Conjugating `sys.P0` by `U_dress` produces a star projection `P0_dress := U_dress.1 * sys.P0 * U_dress.1†`
    that commutes with `H = sys.H0 + V.V_tot` whenever the pulled-back Hamiltonian commutes with `sys.P0`. -/
theorem dressed_ground_proj_isStarProjection_and_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_comm_P0 : Commute (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) sys.P0) :
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    IsStarProjection P0_dress ∧ Commute (sys.H0 + V.totalPerturbation) P0_dress := by
  intro P0_dress
  have hU_self_star : U_dress.1 * U_dress.1† = 1 := Unitary.coe_mul_star_self U_dress
  refine ⟨dressed_ground_proj_isStarProjection sys U_dress, ?_⟩
  rw [commute_iff_eq]
  have h_c : (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) * sys.P0 =
      sys.P0 * (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) := h_comm_P0.eq
  calc (sys.H0 + V.totalPerturbation) * (U_dress.1 * sys.P0 * U_dress.1†)
    _ = (U_dress.1 * U_dress.1†) * (sys.H0 + V.totalPerturbation) * (U_dress.1 * sys.P0 * U_dress.1†) := by
        rw [hU_self_star, one_mul]
    _ = U_dress.1 * ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) * sys.P0) * U_dress.1† := by
        simp only [mul_assoc]
    _ = U_dress.1 * (sys.P0 * (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1)) * U_dress.1† := by
        rw [h_c]
    _ = (U_dress.1 * sys.P0 * U_dress.1†) * (sys.H0 + V.totalPerturbation) * (U_dress.1 * U_dress.1†) := by
        simp only [mul_assoc]
    _ = (U_dress.1 * sys.P0 * U_dress.1†) * (sys.H0 + V.totalPerturbation) := by
        rw [hU_self_star, mul_one]

/-- Operator-norm bound from a quadratic-form bound for a self-adjoint operator on
    `ManyBodyHilbertSpace Site`: if `IsSelfAdjoint A`, `0 ≤ C`, and
    `|Re ⟨ψ, A ψ⟩| ≤ C * ‖ψ‖ ^ 2` for all `ψ`, then `‖A‖ ≤ C`. -/
lemma opNorm_le_of_isSelfAdjoint_and_abs_re_inner_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA : IsSelfAdjoint A) {C : ℝ} (hC : 0 ≤ C)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site, |RCLike.re (inner ℂ ψ (A ψ))| ≤ C * ‖ψ‖ ^ 2) :
    ‖A‖ ≤ C := by
  let b := sortedEigenbasis A hA
  have h_eig_le : ∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      (sortedEigenvalues A hA i) ^ 2 ≤ C ^ 2 := by
    intro i
    have h1 := h_form (b i)
    rw [b.norm_eq_one i, one_pow, mul_one, sortedEigenbasis_apply_H_bhm A hA i,
      inner_smul_right, b.inner_eq_one i, mul_one] at h1
    change |sortedEigenvalues A hA i| ≤ C at h1
    have h2 : |sortedEigenvalues A hA i| ≤ |C| := by rwa [abs_of_nonneg hC]
    exact sq_le_sq.mpr h2
  refine ContinuousLinearMap.opNorm_le_bound A hC (fun ψ => ?_)
  have h_sum_Aψ : ‖A ψ‖ ^ 2 =
      ∑ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
        ‖inner ℂ (b i) (A ψ)‖ ^ 2 :=
    (b.sum_sq_norm_inner_right (A ψ)).symm
  have h_sum_ψ : ‖ψ‖ ^ 2 =
      ∑ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
        ‖inner ℂ (b i) ψ‖ ^ 2 :=
    (b.sum_sq_norm_inner_right ψ).symm
  have h_sq_le : ‖A ψ‖ ^ 2 ≤ (C * ‖ψ‖) ^ 2 := by
    rw [h_sum_Aψ, mul_pow, h_sum_ψ, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [sortedEigenbasis_inner_apply_H A hA i ψ, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right (h_eig_le i) (sq_nonneg _)
  have h_abs : |‖A ψ‖| ≤ |C * ‖ψ‖| := sq_le_sq.mp h_sq_le
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hC (norm_nonneg _))] at h_abs

/-- Dressed ground-subspace quadratic form bound: for any `ψ₀` with `P0_dress ψ₀ = ψ₀`,
    `|Re ⟨ψ₀, (H - E0 • 1) ψ₀⟩| ≤ (δ_split / 2) * ‖ψ₀‖ ^ 2`. -/
theorem dressed_ground_subspace_quadratic_form_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {E0 δ_split : ℝ}
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let H := sys.H0 + V.totalPerturbation
    ∀ ψ₀ : ManyBodyHilbertSpace Site, P0_dress ψ₀ = ψ₀ →
      |RCLike.re (inner ℂ ψ₀ ((H - (E0 : ℂ) • 1) ψ₀))| ≤ (δ_split / 2) * ‖ψ₀‖ ^ 2 := by
  intro P0_dress H ψ₀ hψ₀
  let U_iso := unitaryToLinearIsometryEquiv U_dress
  have hU_star_self : U_dress.1† * U_dress.1 = 1 := Unitary.coe_star_mul_self U_dress
  let ψ : ManyBodyHilbertSpace Site := U_iso.symm ψ₀
  have hU_ψ : U_dress.1 ψ = ψ₀ := U_iso.apply_symm_apply ψ₀
  have h_norm : ‖ψ‖ = ‖ψ₀‖ := U_iso.symm.norm_map ψ₀
  have hP0_ψ : sys.P0 ψ = ψ := by
    have h1 : (U_dress.1†) (P0_dress ψ₀) = (U_dress.1†) ψ₀ := congrArg (U_dress.1†) hψ₀
    have h2 : (U_dress.1†) (P0_dress ψ₀) = sys.P0 ψ := by
      rw [← hU_ψ]
      change (U_dress.1† * (U_dress.1 * sys.P0 * U_dress.1†) * U_dress.1) ψ = sys.P0 ψ
      have h_eq : U_dress.1† * (U_dress.1 * sys.P0 * U_dress.1†) * U_dress.1 = sys.P0 := by
        calc U_dress.1† * (U_dress.1 * sys.P0 * U_dress.1†) * U_dress.1
          _ = (U_dress.1† * U_dress.1) * sys.P0 * (U_dress.1† * U_dress.1) := by
              simp only [mul_assoc]
          _ = sys.P0 := by rw [hU_star_self, one_mul, mul_one]
      rw [h_eq]
    have h3 : (U_dress.1†) ψ₀ = ψ := by
      rw [← hU_ψ]
      change (U_dress.1† * U_dress.1) ψ = ψ
      rw [hU_star_self, ContinuousLinearMap.one_apply]
    rw [← h2, h1, h3]
  have hH0_ψ : sys.H0 ψ = 0 := by
    rw [← hP0_ψ, ← ContinuousLinearMap.mul_apply, sys.ham0_mul_proj0_eq_zero_main,
      ContinuousLinearMap.zero_apply]
  have h_H_conj : inner ℂ ψ₀ (H ψ₀) = inner ℂ ψ ((U_dress.1† * H * U_dress.1) ψ) := by
    rw [← hU_ψ]; exact inner_unitary_conj U_dress H ψ
  have h_eq_re :
      RCLike.re (inner ℂ ψ₀ ((H - (E0 : ℂ) • 1) ψ₀)) =
        RCLike.re (inner ℂ ψ ((U_dress.1† * H * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ)) := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub, h_H_conj, re_inner_smul_one,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one,
      hH0_ψ, inner_zero_right, map_zero, sub_zero, h_norm]
  have hf := h_form ψ
  rw [← h_eq_re, hH0_ψ, inner_zero_right, map_zero, mul_zero, zero_add, h_norm] at hf
  exact hf

/-- Half-width dressed ground-subspace operator-norm bound:
    `‖P0_dress * (sys.H0 + V.V_tot - (E0 : ℂ) • 1) * P0_dress‖ ≤ (δ_split / 2)` and `0 ≤ δ_split`. -/
theorem dressed_ground_subspace_splitting_opNorm_le_half {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {E0 δ_split : ℝ}
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    0 ≤ δ_split ∧
    ‖P0_dress * (sys.H0 + V.totalPerturbation - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_split / 2 := by
  intro P0_dress
  have hP0_ne : sys.P0 ≠ 0 := sys.frustration_free
  have h_ex : ∃ ϕ₀ : ManyBodyHilbertSpace Site, sys.P0 ϕ₀ ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    exact hP0_ne (ContinuousLinearMap.ext h_all)
  rcases h_ex with ⟨ϕ₀, hϕ₀⟩
  have hH0_ϕ₀ : sys.H0 (sys.P0 ϕ₀) = 0 := by
    rw [← ContinuousLinearMap.mul_apply, sys.ham0_mul_proj0_eq_zero_main, ContinuousLinearMap.zero_apply]
  have hf_ϕ₀ := h_form (sys.P0 ϕ₀)
  rw [hH0_ϕ₀, inner_zero_right, map_zero, mul_zero, zero_add] at hf_ϕ₀
  have h_pos_sq : 0 < ‖sys.P0 ϕ₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hϕ₀)
  have h_nonneg_prod : 0 ≤ (δ_split / 2) * ‖sys.P0 ϕ₀‖ ^ 2 := le_trans (abs_nonneg _) hf_ϕ₀
  have hδ_half_nn : 0 ≤ δ_split / 2 := nonneg_of_mul_nonneg_left h_nonneg_prod h_pos_sq
  have hδ_nn : 0 ≤ δ_split := by linarith
  refine ⟨hδ_nn, ?_⟩
  let H := sys.H0 + V.totalPerturbation
  let H' := H - (E0 : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  have hP0_dress : IsStarProjection P0_dress := dressed_ground_proj_isStarProjection sys U_dress
  have hH_sa : IsSelfAdjoint H := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V
  have hE0_sa : IsSelfAdjoint ((E0 : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) := by
    rw [IsSelfAdjoint, star_smul, RCLike.star_def, Complex.conj_ofReal, star_one]
  have hH'_sa : IsSelfAdjoint H' := by
    rw [IsSelfAdjoint]
    change (H - (E0 : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))† =
      H - (E0 : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    rw [map_sub, ContinuousLinearMap.isSelfAdjoint_iff'.mp hH_sa,
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hE0_sa]
  have hA_sa : IsSelfAdjoint (P0_dress * H' * P0_dress) := by
    rw [IsSelfAdjoint]
    calc star (P0_dress * H' * P0_dress)
      _ = star P0_dress * star (P0_dress * H') := star_mul (P0_dress * H') P0_dress
      _ = star P0_dress * (star H' * star P0_dress) := by rw [star_mul P0_dress H']
      _ = P0_dress * (H' * P0_dress) := by rw [hP0_dress.isSelfAdjoint.star_eq, hH'_sa.star_eq]
      _ = P0_dress * H' * P0_dress := (mul_assoc P0_dress H' P0_dress).symm
  apply opNorm_le_of_isSelfAdjoint_and_abs_re_inner_le (P0_dress * H' * P0_dress) hA_sa hδ_half_nn
  intro ψ
  have hP0_adj : P0_dress† = P0_dress :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hP0_dress.isSelfAdjoint
  have h_inner_eq : inner ℂ ψ ((P0_dress * H' * P0_dress) ψ) =
      inner ℂ (P0_dress ψ) (H' (P0_dress ψ)) := by
    calc inner ℂ ψ ((P0_dress * H' * P0_dress) ψ)
      _ = inner ℂ ψ (P0_dress (H' (P0_dress ψ))) := rfl
      _ = inner ℂ ((P0_dress†) ψ) (H' (P0_dress ψ)) :=
          (ContinuousLinearMap.adjoint_inner_left P0_dress (H' (P0_dress ψ)) ψ).symm
      _ = inner ℂ (P0_dress ψ) (H' (P0_dress ψ)) := by rw [hP0_adj]
  rw [h_inner_eq]
  have hP0_idem : P0_dress (P0_dress ψ) = P0_dress ψ :=
    isStarProjection_apply_self_bhm hP0_dress ψ
  have h_qform := dressed_ground_subspace_quadratic_form_le sys V U_dress h_form (P0_dress ψ) hP0_idem
  have h_norm_le : ‖P0_dress ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 :=
    isStarProjection_norm_sq_apply_le_bhm hP0_dress ψ
  exact le_trans h_qform (mul_le_mul_of_nonneg_left h_norm_le hδ_half_nn)

/-- **Dressed Ground-Subspace Operator-Norm Splitting Bound
    (`dressed_ground_subspace_splitting_opNorm_le`)**:
    Under the full-spectrum relative form bound `h_form`, the dressed ground-space pinched Hamiltonian
    satisfies `‖P0_dress * (sys.H0 + V.V_tot - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_split`. -/
theorem dressed_ground_subspace_splitting_opNorm_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {E0 δ_split : ℝ}
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    ‖P0_dress * (sys.H0 + V.totalPerturbation - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_split := by
  rcases dressed_ground_subspace_splitting_opNorm_le_half sys V U_dress h_form with ⟨hδ_nn, h_half⟩
  linarith

/-- **Dressed Ground-Subspace & Excited-Band Quadratic Form Bounds
    (`dressed_ground_and_excited_band_quadratic_form_bounds`)**:
    From `h_form` and `∀ i, 1 ≤ sys.weight i` (via `dressed_energy_sandwich_of_relative_form_bound_main`),
    every vector `ψ₀` in the dressed ground space (`P0_dress ψ₀ = ψ₀`) satisfies
    `|Re ⟨ψ₀, (H - E0 • 1) ψ₀⟩| ≤ (δ_split / 2) * ‖ψ₀‖ ^ 2`, and every vector `ψ_perp` in the
    orthogonal complement (`P0_dress ψ_perp = 0`) satisfies
    `((3 / 4 : ℝ) - δ_split / 2) * ‖ψ_perp‖ ^ 2 ≤ Re ⟨ψ_perp, (H - E0 • 1) ψ_perp⟩`. -/
theorem dressed_ground_and_excited_band_quadratic_form_bounds {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {E0 δ_split : ℝ}
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let H := sys.H0 + V.totalPerturbation
    (∀ ψ₀ : ManyBodyHilbertSpace Site, P0_dress ψ₀ = ψ₀ →
      |RCLike.re (inner ℂ ψ₀ ((H - (E0 : ℂ) • 1) ψ₀))| ≤ (δ_split / 2) * ‖ψ₀‖ ^ 2) ∧
    (∀ ψ_perp : ManyBodyHilbertSpace Site, P0_dress ψ_perp = 0 →
      ((3 / 4 : ℝ) - δ_split / 2) * ‖ψ_perp‖ ^ 2 ≤
        RCLike.re (inner ℂ ψ_perp ((H - (E0 : ℂ) • 1) ψ_perp))) := by
  intro P0_dress H
  let U_iso := unitaryToLinearIsometryEquiv U_dress
  have hU_star_self : U_dress.1† * U_dress.1 = 1 := Unitary.coe_star_mul_self U_dress
  refine ⟨dressed_ground_subspace_quadratic_form_le sys V U_dress h_form, ?_⟩
  · intro ψ_perp hψ_perp
    let ψ : ManyBodyHilbertSpace Site := U_iso.symm ψ_perp
    have hU_ψ : U_dress.1 ψ = ψ_perp := U_iso.apply_symm_apply ψ_perp
    have h_norm : ‖ψ‖ = ‖ψ_perp‖ := U_iso.symm.norm_map ψ_perp
    have hP0_ψ : sys.P0 ψ = 0 := by
      have h1 : (U_dress.1†) (P0_dress ψ_perp) = 0 := by rw [hψ_perp, map_zero]
      have h2 : (U_dress.1†) (P0_dress ψ_perp) = sys.P0 ψ := by
        rw [← hU_ψ]
        change (U_dress.1† * (U_dress.1 * sys.P0 * U_dress.1†) * U_dress.1) ψ = sys.P0 ψ
        have h_eq : U_dress.1† * (U_dress.1 * sys.P0 * U_dress.1†) * U_dress.1 = sys.P0 := by
          calc U_dress.1† * (U_dress.1 * sys.P0 * U_dress.1†) * U_dress.1
            _ = (U_dress.1† * U_dress.1) * sys.P0 * (U_dress.1† * U_dress.1) := by
                simp only [mul_assoc]
            _ = sys.P0 := by rw [hU_star_self, one_mul, mul_one]
        rw [h_eq]
      rw [← h2, h1]
    have h1P_ψ : (1 - sys.P0) ψ = ψ := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hP0_ψ, sub_zero]
    have hH0_gap : ‖ψ_perp‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
      have h_form_gap := sys.one_sub_P0_form_le_H0_main h_weight ψ
      rw [h1P_ψ, inner_self_eq_norm_sq, h_norm] at h_form_gap
      exact h_form_gap
    have h_H_conj : inner ℂ ψ_perp (H ψ_perp) = inner ℂ ψ ((U_dress.1† * H * U_dress.1) ψ) := by
      rw [← hU_ψ]; exact inner_unitary_conj U_dress H ψ
    have h_shift : RCLike.re (inner ℂ ψ_perp ((H - (E0 : ℂ) • 1) ψ_perp)) =
        RCLike.re (inner ℂ ψ ((U_dress.1† * H * U_dress.1) ψ)) - E0 * ‖ψ_perp‖ ^ 2 := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub, h_H_conj, re_inner_smul_one]
    have h_diff : RCLike.re (inner ℂ ψ ((U_dress.1† * H * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ)) =
        RCLike.re (inner ℂ ψ ((U_dress.1† * H * U_dress.1) ψ)) -
          RCLike.re (inner ℂ ψ (sys.H0 ψ)) - E0 * ‖ψ_perp‖ ^ 2 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one, h_norm]
    have h_abs := (abs_le.mp (h_form ψ)).1
    rw [h_diff, h_norm, show bhmSandwichDeviation = 1 / 4 from rfl] at h_abs
    rw [h_shift]
    linarith

end
