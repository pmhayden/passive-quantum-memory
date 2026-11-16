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

import Proofs.DressedThermalDuhamel.SafeComplementProjectorBounds
import Defs.F2ChainAndCSS

/-!
# Syndrome-Pinched Quadratic-Form Comparison and Peierls–Bogoliubov Trace Bounds

Defines the syndrome-block-diagonal pinching `perturbedSyndromeDiagOp` and effective Hamiltonian `perturbedSyndromeDiagHamiltonian`, proving block-sector commutation with all syndrome projectors. Establishes Courant–Fischer unitary sector Boltzmann peeling and Peierls–Bogoliubov diagonal trace monotonicity and Jensen inequalities (`lem:peierls-bogoliubov`).

## References

* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.1 (`lem:duhamel-weyl-ratio`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Lemma 3.7 (`lem:peierls-bogoliubov`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option maxRecDepth 200000
set_option linter.unusedVariables false

/-- If check `i` is unviolated in syndrome `σ` (`σ i = false`), then `sys.checkProj i` annihilates
`sys.syndromeProjector σ` and `1 - sys.checkProj i` fixes `sys.syndromeProjector σ`. -/
theorem perturbed_one_sub_checkProj_mul_syndromeProjector_of_false {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {σ : ι → Bool} {i : ι} (h_clean : σ i = false) :
    sys.checkProj i * sys.syndromeProjector σ = 0 ∧
    (1 - sys.checkProj i) * sys.syndromeProjector σ = sys.syndromeProjector σ := by
  have h_mul := (syndrome_resolution_indexed sys).2.2.2.2.2.1 σ i
  simp only [h_clean, Bool.false_eq_true, if_false] at h_mul
  refine ⟨h_mul, ?_⟩
  rw [sub_mul, one_mul, h_mul, sub_zero]

/-- If every check `i ∈ l` is unviolated in `σ`, `(l.map (1 - sys.checkProj ·)).prod` fixes `Π_σ`. -/
theorem perturbed_list_prod_one_sub_checkProj_mul_syndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (σ : ι → Bool) :
    ∀ (l : List ι), (∀ i ∈ l, σ i = false) →
      (l.map (fun i => 1 - sys.checkProj i)).prod * sys.syndromeProjector σ =
        sys.syndromeProjector σ
  | [], _ => by simp
  | i :: ls, h_clean => by
    rw [List.map_cons, List.prod_cons, mul_assoc]
    have h_tail := perturbed_list_prod_one_sub_checkProj_mul_syndromeProjector sys σ ls
      (fun j hj => h_clean j (List.mem_cons_of_mem i hj))
    rw [h_tail]
    exact (perturbed_one_sub_checkProj_mul_syndromeProjector_of_false sys
      (h_clean i List.mem_cons_self)).2

/-- Clean-cube local telescoping annihilation (`perturbed_local_diff_mul_syndromeProjector_eq_zero`). -/
theorem perturbed_local_diff_mul_syndromeProjector_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {D_loc localGroundProj : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hD_sa : IsSelfAdjoint D_loc) {σ : ι → Bool}
    (hDP : D_loc * localGroundProj = 0)
    (hP_clean : localGroundProj * sys.syndromeProjector σ = sys.syndromeProjector σ) :
    D_loc * sys.syndromeProjector σ = 0 ∧
    sys.syndromeProjector σ * D_loc = 0 ∧
    Commute D_loc (sys.syndromeProjector σ) ∧
    sys.syndromeProjector σ * D_loc * sys.syndromeProjector σ = 0 := by
  have h_right : D_loc * sys.syndromeProjector σ = 0 := by
    calc D_loc * sys.syndromeProjector σ
      _ = D_loc * (localGroundProj * sys.syndromeProjector σ) := by rw [hP_clean]
      _ = (D_loc * localGroundProj) * sys.syndromeProjector σ := (mul_assoc D_loc localGroundProj _).symm
      _ = 0 := by rw [hDP, zero_mul]
  have hP_sa : IsSelfAdjoint (sys.syndromeProjector σ) :=
    ((syndrome_resolution_indexed sys).2.1 σ).isSelfAdjoint
  have h_left : sys.syndromeProjector σ * D_loc = 0 := by
    have h_star := congrArg star h_right
    rw [star_mul, hP_sa.star_eq, hD_sa.star_eq] at h_star
    exact h_star.trans (map_zero ContinuousLinearMap.adjoint)
  have h_comm : Commute D_loc (sys.syndromeProjector σ) := by
    rw [commute_iff_eq, h_right, h_left]
  have h_pinch : sys.syndromeProjector σ * D_loc * sys.syndromeProjector σ = 0 := by
    rw [h_left, zero_mul]
  exact ⟨h_right, h_left, h_comm, h_pinch⟩

/-! ## 1. Syndrome-Diagonal Pinching (`perturbedSyndromeDiagOp`) & BHM Form Bound Preservation -/

/-- Syndrome-sector block-diagonal pinching of an operator `W`:
$$\mathcal{D}_{\mathrm{syn}}(W) := \sum_{\sigma : \iota \to \mathrm{Bool}} \Pi_\sigma W \Pi_\sigma.$$ -/
def perturbedSyndromeDiagOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ : ι → Bool, sys.syndromeProjector σ * W * sys.syndromeProjector σ

/-- `perturbed_syndromeDiagOp sys W` is self-adjoint whenever `W` is self-adjoint. -/
theorem perturbed_isSelfAdjoint_syndromeDiagOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hW : IsSelfAdjoint W) :
    IsSelfAdjoint (perturbedSyndromeDiagOp sys W) := by
  unfold perturbedSyndromeDiagOp
  change ContinuousLinearMap.adjoint
    (∑ σ : ι → Bool, sys.syndromeProjector σ * W * sys.syndromeProjector σ) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact (perturbed_isSelfAdjoint_conj_of_isSelfAdjoint
    ((syndrome_resolution_indexed sys).2.1 σ).isSelfAdjoint hW).star_eq

/-- Multiplication and commutation of `perturbed_syndromeDiagOp sys W` with any bare syndrome
projector `sys.syndromeProjector τ`. -/
theorem perturbed_syndromeDiagOp_mul_syndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (τ : ι → Bool) :
    perturbedSyndromeDiagOp sys W * sys.syndromeProjector τ =
      sys.syndromeProjector τ * W * sys.syndromeProjector τ ∧
    sys.syndromeProjector τ * perturbedSyndromeDiagOp sys W =
      sys.syndromeProjector τ * W * sys.syndromeProjector τ ∧
    Commute (perturbedSyndromeDiagOp sys W) (sys.syndromeProjector τ) := by
  have h_res := syndrome_resolution_indexed sys
  have h_right : perturbedSyndromeDiagOp sys W * sys.syndromeProjector τ =
      sys.syndromeProjector τ * W * sys.syndromeProjector τ := by
    unfold perturbedSyndromeDiagOp
    rw [Finset.sum_mul, Finset.sum_eq_single τ]
    · rw [mul_assoc (sys.syndromeProjector τ * W), (h_res.2.1 τ).isIdempotentElem.eq]
    · intro σ _ hne
      rw [mul_assoc (sys.syndromeProjector σ * W), h_res.2.2.1 σ τ hne, mul_zero]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ τ))
  have h_left : sys.syndromeProjector τ * perturbedSyndromeDiagOp sys W =
      sys.syndromeProjector τ * W * sys.syndromeProjector τ := by
    unfold perturbedSyndromeDiagOp
    rw [Finset.mul_sum, Finset.sum_eq_single τ]
    · rw [← mul_assoc (sys.syndromeProjector τ) (sys.syndromeProjector τ * W),
        ← mul_assoc (sys.syndromeProjector τ) (sys.syndromeProjector τ) W,
        (h_res.2.1 τ).isIdempotentElem.eq]
    · intro σ _ hne
      rw [← mul_assoc (sys.syndromeProjector τ) (sys.syndromeProjector σ * W),
        ← mul_assoc (sys.syndromeProjector τ) (sys.syndromeProjector σ) W,
        h_res.2.2.1 τ σ (Ne.symm hne), zero_mul, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ τ))
  exact ⟨h_right, h_left, h_right.trans h_left.symm⟩

/-- Any operator `A` that commutes with every `sys.syndromeProjector σ` is a fixed point of
`perturbed_syndromeDiagOp sys`. -/
theorem perturbed_syndromeDiagOp_eq_self_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : ∀ σ : ι → Bool, Commute A (sys.syndromeProjector σ)) :
    perturbedSyndromeDiagOp sys A = A := by
  have h_res := syndrome_resolution_indexed sys
  unfold perturbedSyndromeDiagOp
  have h_term : ∀ σ : ι → Bool,
      sys.syndromeProjector σ * A * sys.syndromeProjector σ = A * sys.syndromeProjector σ := by
    intro σ
    rw [(h_comm σ).symm.eq, mul_assoc, (h_res.2.1 σ).isIdempotentElem.eq]
  simp_rw [h_term, ← Finset.mul_sum, h_res.2.2.2.1, mul_one]

/-- Sector-by-sector decomposition of the real quadratic form of `perturbed_syndromeDiagOp sys W`. -/
theorem perturbed_re_inner_syndromeDiagOp_eq_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ (perturbedSyndromeDiagOp sys W ψ)) =
      ∑ σ : ι → Bool,
        RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (W (sys.syndromeProjector σ ψ))) := by
  have h_res := syndrome_resolution_indexed sys
  unfold perturbedSyndromeDiagOp
  rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hP_adj : (sys.syndromeProjector σ)† = sys.syndromeProjector σ :=
    (h_res.2.1 σ).isSelfAdjoint.star_eq
  have h_inner :
      inner ℂ ψ ((sys.syndromeProjector σ * W * sys.syndromeProjector σ) ψ) =
        inner ℂ (sys.syndromeProjector σ ψ) (W (sys.syndromeProjector σ ψ)) := by
    calc inner ℂ ψ ((sys.syndromeProjector σ * W * sys.syndromeProjector σ) ψ)
      _ = inner ℂ ψ (sys.syndromeProjector σ (W (sys.syndromeProjector σ ψ))) := rfl
      _ = inner ℂ (((sys.syndromeProjector σ)†) ψ) (W (sys.syndromeProjector σ ψ)) :=
          (ContinuousLinearMap.adjoint_inner_left (sys.syndromeProjector σ)
            (W (sys.syndromeProjector σ ψ)) ψ).symm
      _ = inner ℂ (sys.syndromeProjector σ ψ) (W (sys.syndromeProjector σ ψ)) := by rw [hP_adj]
  rw [h_inner]

/-- Sector-by-sector decomposition of the bare energy quadratic form `Re ⟨ψ, sys.H0 ψ⟩`. -/
theorem perturbed_re_inner_H0_eq_sum_syndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ (sys.H0 ψ)) =
      ∑ σ : ι → Bool,
        RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (sys.H0 (sys.syndromeProjector σ ψ))) := by
  have h_fixed : perturbedSyndromeDiagOp sys sys.H0 = sys.H0 :=
    perturbed_syndromeDiagOp_eq_self_of_commute sys (syndrome_resolution_indexed sys).2.2.2.2.2.2.2
  conv_lhs => rw [← h_fixed]
  exact perturbed_re_inner_syndromeDiagOp_eq_sum sys sys.H0 ψ

/-- **Zero-Loss BHM Relative Form Bound Preservation under Syndrome-Diagonal Pinching
(`perturbed_bhm_form_bound_syndromeDiagOp`)**:
If `W` satisfies `|Re ⟨ϕ, W ϕ⟩| ≤ γ * Re ⟨ϕ, sys.H0 ϕ⟩` for all `ϕ`, then `perturbed_syndromeDiagOp sys W`
satisfies the exact same global relative form bound and satisfies
`|Re ⟨Π_σ ϕ, (perturbed_syndromeDiagOp sys W) (Π_σ ϕ)⟩| ≤ γ * sys.syndromeEnergy σ * ‖Π_σ ϕ‖^2`. -/
theorem perturbed_bhm_form_bound_syndromeDiagOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) {γ : ℝ}
    (h_bhm : ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ϕ (W ϕ))| ≤ γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ))) :
    (∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ (perturbedSyndromeDiagOp sys W ψ))| ≤
        γ * RCLike.re (inner ℂ ψ (sys.H0 ψ))) ∧
    (∀ (σ : ι → Bool) (ϕ : ManyBodyHilbertSpace Site),
      |RCLike.re (inner ℂ (sys.syndromeProjector σ ϕ)
        (perturbedSyndromeDiagOp sys W (sys.syndromeProjector σ ϕ)))| ≤
        γ * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ϕ‖ ^ 2) := by
  have h_res := syndrome_resolution_indexed sys
  refine ⟨fun ψ => ?_, fun σ ϕ => ?_⟩
  · calc |RCLike.re (inner ℂ ψ (perturbedSyndromeDiagOp sys W ψ))|
      _ = |∑ σ : ι → Bool,
            RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (W (sys.syndromeProjector σ ψ)))| := by
          rw [perturbed_re_inner_syndromeDiagOp_eq_sum]
      _ ≤ ∑ σ : ι → Bool,
            |RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (W (sys.syndromeProjector σ ψ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : ι → Bool,
            γ * RCLike.re (inner ℂ (sys.syndromeProjector σ ψ)
              (sys.H0 (sys.syndromeProjector σ ψ))) :=
          Finset.sum_le_sum (fun σ _ => h_bhm (sys.syndromeProjector σ ψ))
      _ = γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
          rw [← Finset.mul_sum, ← perturbed_re_inner_H0_eq_sum_syndromeProjector]
  · have h_act : perturbedSyndromeDiagOp sys W (sys.syndromeProjector σ ϕ) =
        sys.syndromeProjector σ (W (sys.syndromeProjector σ ϕ)) := by
      calc perturbedSyndromeDiagOp sys W (sys.syndromeProjector σ ϕ)
        _ = (perturbedSyndromeDiagOp sys W * sys.syndromeProjector σ) ϕ := rfl
        _ = (sys.syndromeProjector σ * W * sys.syndromeProjector σ) ϕ := by
            rw [(perturbed_syndromeDiagOp_mul_syndromeProjector sys W σ).1]
        _ = sys.syndromeProjector σ (W (sys.syndromeProjector σ ϕ)) := rfl
    have hP_adj : (sys.syndromeProjector σ)† = sys.syndromeProjector σ :=
      (h_res.2.1 σ).isSelfAdjoint.star_eq
    have hP_idem : sys.syndromeProjector σ (sys.syndromeProjector σ ϕ) =
        sys.syndromeProjector σ ϕ := isStarProjection_apply_self (h_res.2.1 σ) ϕ
    have h_inner_eq :
        inner ℂ (sys.syndromeProjector σ ϕ)
          (perturbedSyndromeDiagOp sys W (sys.syndromeProjector σ ϕ)) =
        inner ℂ (sys.syndromeProjector σ ϕ) (W (sys.syndromeProjector σ ϕ)) := by
      rw [h_act, ← ContinuousLinearMap.adjoint_inner_left, hP_adj, hP_idem]
    rw [h_inner_eq]
    have h1 := h_bhm (sys.syndromeProjector σ ϕ)
    have hH0_act : sys.H0 (sys.syndromeProjector σ ϕ) =
        (sys.syndromeEnergy σ : ℂ) • (sys.syndromeProjector σ ϕ) := by
      calc sys.H0 (sys.syndromeProjector σ ϕ)
        _ = (sys.H0 * sys.syndromeProjector σ) ϕ := rfl
        _ = ((sys.syndromeEnergy σ : ℂ) • sys.syndromeProjector σ) ϕ := by rw [h_res.2.2.2.2.1 σ]
        _ = (sys.syndromeEnergy σ : ℂ) • (sys.syndromeProjector σ ϕ) := rfl
    have hH0_re :
        RCLike.re (inner ℂ (sys.syndromeProjector σ ϕ) (sys.H0 (sys.syndromeProjector σ ϕ))) =
          sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ϕ‖ ^ 2 := by
      rw [hH0_act, inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hH0_re] at h1; linarith

/-! ## 2. Exact Partition Function Identity for Projected Commuting Operators & Courant–Fischer Unitary Sector Peeling -/

/-- Self-adjointness of `H + (M : ℂ) • P` when `IsSelfAdjoint H` and `IsSelfAdjoint P`. -/
lemma perturbed_isSelfAdjoint_add_real_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H) (hP : IsSelfAdjoint P) (M : ℝ) :
    IsSelfAdjoint (H + (M : ℂ) • P) := by
  refine isSelfAdjoint_add hH ?_
  rw [IsSelfAdjoint, star_smul, RCLike.star_def, Complex.conj_ofReal, hP.star_eq]

private lemma perturbed_abs_eigenvalue_le_opNorm_of_ne_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {v : ManyBodyHilbertSpace Site} {μ : ℝ} (hv : v ≠ 0) (h_eig : H v = (μ : ℂ) • v) :
    |μ| ≤ ‖H‖ := by
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h_le : |μ| * ‖v‖ ≤ ‖H‖ * ‖v‖ := by
    calc |μ| * ‖v‖
      _ = ‖(μ : ℂ) • v‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖H v‖ := by rw [← h_eig]
      _ ≤ ‖H‖ * ‖v‖ := H.le_opNorm v
  exact le_of_mul_le_mul_right h_le hv_pos

/-- Spectral dichotomy for safe-penalized eigenbasis when `Commute H P`. -/
theorem perturbed_penalized_eigenbasis_dichotomy_of_commute_proj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P) (h_comm : Commute H P)
    {M : ℝ} (hM : 2 * ‖H‖ < M) (ω : ManyBodyConfig Site) :
    let hH_pen := perturbed_isSelfAdjoint_add_real_smul hH hP.isSelfAdjoint M
    let ψ := opEigenbasis (H + (M : ℂ) • P) hH_pen ω
    let μ := opEigenvalues (H + (M : ℂ) • P) hH_pen ω
    (P ψ = 0 ∧ H ψ = (μ : ℂ) • ψ ∧
      RCLike.re (inner ℂ ψ ((1 - P) ψ)) = 1 ∧ μ ≤ ‖H‖) ∨
    ((1 - P) ψ = 0 ∧ H ψ = ((μ - M : ℝ) : ℂ) • ψ ∧
      RCLike.re (inner ℂ ψ ((1 - P) ψ)) = 0 ∧ M - ‖H‖ ≤ μ) := by
  intro hH_pen ψ μ
  have h_eig : (H + (M : ℂ) • P) ψ = (μ : ℂ) • ψ := opEigenbasis_apply_H _ hH_pen ω
  have h_re_one : RCLike.re (inner ℂ ψ ψ) = 1 := (perturbed_norm_opEigenbasis_le_one _ hH_pen ω).1
  let Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site := 1 - P
  have h_one_sub : H (Q ψ) = (μ : ℂ) • Q ψ := by
    have h1 : Q ((H + (M : ℂ) • P) ψ) = Q ((μ : ℂ) • ψ) := congrArg Q h_eig
    have h_comm_sub : Q (H ψ) = H (Q ψ) := by
      change ((1 - P) * H) ψ = (H * (1 - P)) ψ
      rw [((Commute.one_right H).sub_right h_comm).symm.eq]
    have h_proj_zero : Q (P ψ) = 0 := by
      change ((1 - P) * P) ψ = 0
      rw [sub_mul, one_mul, hP.isIdempotentElem.eq, sub_self, ContinuousLinearMap.zero_apply]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul,
      h_comm_sub, h_proj_zero, smul_zero, add_zero, map_smul] at h1
    exact h1
  have h_proj : H (P ψ) = ((μ - M : ℝ) : ℂ) • P ψ := by
    have h1 : P ((H + (M : ℂ) • P) ψ) = P ((μ : ℂ) • ψ) := congrArg P h_eig
    have h_comm_P : P (H ψ) = H (P ψ) := by
      change (P * H) ψ = (H * P) ψ; rw [h_comm.symm.eq]
    have h_idem : P (P ψ) = P ψ := by
      change (P * P) ψ = P ψ; rw [hP.isIdempotentElem.eq]
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul,
      h_comm_P, h_idem, map_smul] at h1
    rw [Complex.ofReal_sub, sub_smul, ← h1, add_sub_cancel_right]
  by_cases hPψ : P ψ = 0
  · left
    have h1Pψ : Q ψ = ψ := by
      dsimp only [Q]; rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hPψ, sub_zero]
    have hψ_ne : Q ψ ≠ 0 := by
      rw [h1Pψ]; intro h0
      have h_z : RCLike.re (inner ℂ ψ ψ) = 0 := by rw [h0, inner_zero_right, map_zero]
      linarith [h_re_one]
    have hμ_le : μ ≤ ‖H‖ :=
      le_trans (le_abs_self μ) (perturbed_abs_eigenvalue_le_opNorm_of_ne_zero H hψ_ne h_one_sub)
    rw [h1Pψ] at h_one_sub
    refine ⟨hPψ, h_one_sub, ?_, hμ_le⟩
    change RCLike.re (inner ℂ ψ (Q ψ)) = 1; rw [h1Pψ, h_re_one]
  · right
    have hμ_ge : M - ‖H‖ ≤ μ := by
      have h_abs := perturbed_abs_eigenvalue_le_opNorm_of_ne_zero H hPψ h_proj
      linarith [(abs_le.mp h_abs).1]
    have h1Pψ : Q ψ = 0 := by
      by_contra h_ne
      have h_abs := perturbed_abs_eigenvalue_le_opNorm_of_ne_zero H h_ne h_one_sub
      linarith [(abs_le.mp h_abs).2]
    have hPψ_eq : P ψ = ψ := by
      have h_sub : ψ - P ψ = 0 := by simpa [Q, ContinuousLinearMap.sub_apply] using h1Pψ
      exact (sub_eq_zero.mp h_sub).symm
    rw [hPψ_eq] at h_proj
    refine ⟨h1Pψ, h_proj, ?_, hμ_ge⟩
    change RCLike.re (inner ℂ ψ (Q ψ)) = 0; rw [h1Pψ, inner_zero_right, map_zero]

/-- Penalized Boltzmann trace identity on `1 - P`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_one_sub_proj_eq_penalized {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P) (h_comm : Commute H P)
    {M : ℝ} (hM : 2 * ‖H‖ < M) (β : ℝ) :
    let hH_pen := perturbed_isSelfAdjoint_add_real_smul hH hP.isSelfAdjoint M
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * (1 - P)) =
      ∑ ω : ManyBodyConfig Site,
        Real.exp (-β * opEigenvalues (H + (M : ℂ) • P) hH_pen ω) *
          RCLike.re (inner ℂ (opEigenbasis (H + (M : ℂ) • P) hH_pen ω)
            ((1 - P) (opEigenbasis (H + (M : ℂ) • P) hH_pen ω))) := by
  intro hH_pen
  let ψ_pen := opEigenbasis (H + (M : ℂ) • P) hH_pen
  let μ_pen := opEigenvalues (H + (M : ℂ) • P) hH_pen
  let E_true : ManyBodyConfig Site → ℝ := fun ω =>
    if P (ψ_pen ω) = 0 then μ_pen ω else μ_pen ω - M
  have h_eig_true : ∀ ω : ManyBodyConfig Site, H (ψ_pen ω) = (E_true ω : ℂ) • ψ_pen ω := by
    intro ω
    rcases perturbed_penalized_eigenbasis_dichotomy_of_commute_proj H P hH hP h_comm hM ω with h_ker | h_ran
    · dsimp only [E_true]; rw [if_pos h_ker.1]; exact h_ker.2.1
    · have hP_ne : P (ψ_pen ω) ≠ 0 := by
        intro hP0
        have h_zero : ψ_pen ω = 0 := by
          have h1 : (1 - P) (ψ_pen ω) = 0 := h_ran.1
          rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hP0, sub_zero] at h1
          exact h1
        have h_re : RCLike.re (inner ℂ (ψ_pen ω) (ψ_pen ω)) = 1 :=
          (perturbed_norm_opEigenbasis_le_one (H + (M : ℂ) • P) hH_pen ω).1
        rw [h_zero, inner_zero_right, map_zero] at h_re; norm_num at h_re
      dsimp only [E_true]; rw [if_neg hP_ne]; exact h_ran.2.1
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
    H hH ψ_pen E_true (opEigenbasis_orthonormal _ hH_pen) h_eig_true β (1 - P)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rcases perturbed_penalized_eigenbasis_dichotomy_of_commute_proj H P hH hP h_comm hM ω with h_ker | h_ran
  · dsimp only [E_true]; rw [if_pos h_ker.1]
  · change Real.exp (-β * E_true ω) * RCLike.re (inner ℂ (ψ_pen ω) ((1 - P) (ψ_pen ω))) =
      Real.exp (-β * μ_pen ω) * RCLike.re (inner ℂ (ψ_pen ω) ((1 - P) (ψ_pen ω)))
    have h_z : RCLike.re (inner ℂ (ψ_pen ω) ((1 - P) (ψ_pen ω))) = 0 := h_ran.2.2.1
    rw [h_z, mul_zero, mul_zero]

/-- An operator norm bound `‖R_rem‖ ≤ δ_half` implies `|Re ⟨ψ, R_rem ψ⟩| ≤ δ_half * ‖ψ‖ ^ 2`. -/
theorem perturbed_re_inner_le_of_opNorm_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {R_rem : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {δ_half : ℝ}
    (h_norm : ‖R_rem‖ ≤ δ_half) (ψ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ ψ (R_rem ψ))| ≤ δ_half * ‖ψ‖ ^ 2 := by
  calc |RCLike.re (inner ℂ ψ (R_rem ψ))|
    _ ≤ ‖inner ℂ ψ (R_rem ψ)‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖ψ‖ * ‖R_rem ψ‖ := norm_inner_le_norm ψ (R_rem ψ)
    _ ≤ ‖ψ‖ * (‖R_rem‖ * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left (R_rem.le_opNorm ψ) (norm_nonneg ψ)
    _ = ‖R_rem‖ * ‖ψ‖ ^ 2 := by ring
    _ ≤ δ_half * ‖ψ‖ ^ 2 := mul_le_mul_of_nonneg_right h_norm (sq_nonneg ‖ψ‖)

/-- General one-sided Courant–Fischer shift comparison for two self-adjoint operators `A`, `B`. -/
theorem perturbed_opEigenvalues_add_le_of_form_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {d : ℝ}
    (h_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      d * ‖ϕ‖ ^ 2 + RCLike.re (inner ℂ ϕ (A ϕ)) ≤ RCLike.re (inner ℂ ϕ (B ϕ)))
    (ω : ManyBodyConfig Site) :
    d + opEigenvalues A hA ω ≤ opEigenvalues B hB ω := by
  let i := configFinEquiv Site ω
  let E0_low := eigenSpanBelow A hA i.1
  let U_low := eigenSpanBelow B hB (i.1 + 1)
  have h_dim_E0 : Module.finrank ℂ E0_low = i.1 :=
    finrank_eigenSpanBelow A hA i.1 (le_of_lt i.2)
  have h_orth_E0 := E0_low.finrank_add_finrank_orthogonal
  have h_dim_U : Module.finrank ℂ U_low = i.1 + 1 :=
    finrank_eigenSpanBelow B hB (i.1 + 1) i.2
  have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
      Module.finrank ℂ (E0_lowᗮ) + Module.finrank ℂ U_low := by omega
  rcases exists_ne_zero_mem_inf_of_finrank_lt_add (E0_lowᗮ) U_low h_dim_lt with
    ⟨ϕ, hϕ_orth, hϕU, hϕ_ne⟩
  have h_norm_pos : 0 < ‖ϕ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hϕ_ne)
  have h_ray_A : opEigenvalues A hA ω * ‖ϕ‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ (A ϕ)) := by
    apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow A hA i.1
      (sortedEigenvalues A hA i) _ hϕ_orth
    intro j hj; exact sortedEigenvalues_monotone_bhm A hA hj
  have h_ray_B : RCLike.re (inner ℂ ϕ (B ϕ)) ≤ opEigenvalues B hB ω * ‖ϕ‖ ^ 2 := by
    apply re_inner_apply_H_le_of_mem_eigenSpanBelow B hB (i.1 + 1)
      (sortedEigenvalues B hB i) _ hϕU
    intro j hj; exact sortedEigenvalues_monotone_bhm B hB (Nat.lt_succ_iff.mp hj)
  have h_low := h_form ϕ
  have h_chain : (d + opEigenvalues A hA ω) * ‖ϕ‖ ^ 2 ≤ opEigenvalues B hB ω * ‖ϕ‖ ^ 2 := by
    linarith
  exact le_of_mul_le_mul_right h_chain h_norm_pos

/-- Courant–Fischer eigenvalue sandwich between `H_pull` and `H_eff`. -/
theorem perturbed_opEigenvalues_pullback_sandwich_of_remainder_form {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H_eff H_pull : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_eff : IsSelfAdjoint H_eff) (hH_pull : IsSelfAdjoint H_pull)
    {c_shift δ_split : ℝ}
    (h_rem_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ ((H_pull - H_eff - (c_shift : ℂ) • 1) ψ))| ≤
        (δ_split / 2) * ‖ψ‖ ^ 2)
    (ω : ManyBodyConfig Site) :
    c_shift + opEigenvalues H_eff hH_eff ω - (1 / 2 : ℝ) * δ_split ≤
      opEigenvalues H_pull hH_pull ω ∧
    opEigenvalues H_pull hH_pull ω ≤
      c_shift + opEigenvalues H_eff hH_eff ω + (1 / 2 : ℝ) * δ_split := by
  have h_low_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      (c_shift - (1 / 2 : ℝ) * δ_split) * ‖ϕ‖ ^ 2 + RCLike.re (inner ℂ ϕ (H_eff ϕ)) ≤
        RCLike.re (inner ℂ ϕ (H_pull ϕ)) := by
    intro ϕ
    have h1 := (abs_le.mp (h_rem_form ϕ)).1
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one] at h1
    linarith
  have h_up_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      (-c_shift - (1 / 2 : ℝ) * δ_split) * ‖ϕ‖ ^ 2 + RCLike.re (inner ℂ ϕ (H_pull ϕ)) ≤
        RCLike.re (inner ℂ ϕ (H_eff ϕ)) := by
    intro ϕ
    have h2 := (abs_le.mp (h_rem_form ϕ)).2
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one] at h2
    linarith
  have h_low := perturbed_opEigenvalues_add_le_of_form_le H_eff H_pull hH_eff hH_pull h_low_form ω
  have h_up := perturbed_opEigenvalues_add_le_of_form_le H_pull H_eff hH_pull hH_eff h_up_form ω
  constructor <;> linarith

/-- Partition function comparison between `H_eff` and `H_pull`. -/
theorem perturbed_gibbsPartitionZ_effective_le_pullback {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H_eff H_pull : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_eff : IsSelfAdjoint H_eff) (hH_pull : IsSelfAdjoint H_pull)
    {c_shift δ_split β : ℝ} (hβ : 0 ≤ β)
    (h_rem_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ ((H_pull - H_eff - (c_shift : ℂ) • 1) ψ))| ≤
        (δ_split / 2) * ‖ψ‖ ^ 2) :
    Real.exp (-β * c_shift - (1 / 2 : ℝ) * β * δ_split) *
      gibbsPartitionZ (opEigenvalues H_eff hH_eff) β ≤
    gibbsPartitionZ (opEigenvalues H_pull hH_pull) β := by
  unfold gibbsPartitionZ
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h_up := (perturbed_opEigenvalues_pullback_sandwich_of_remainder_form
    H_eff H_pull hH_eff hH_pull h_rem_form ω).2
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- **Exact Partition Function Identity for Projected Commuting Operators
(`perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl`)**:
For any self-adjoint operator `K` and star projection `P` with `Commute K P`:
$$\operatorname{Tr}(e^{-\beta (P K P)}) = \operatorname{Tr}(e^{-\beta K} P) + \operatorname{Tr}(1 - P).$$ -/
theorem perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (K P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hK : IsSelfAdjoint K) (hP : IsStarProjection P) (h_comm : Commute K P) (β : ℝ) :
    let hPKP := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP.isSelfAdjoint hK
    gibbsPartitionZ (opEigenvalues (P * K * P) hPKP) β =
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis K hK) (opEigenvalues K hK) β * P) +
        hilbertTrace (1 - P) := by
  intro hPKP
  let Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have h_comm_Q : Commute K Q := (Commute.one_right K).sub_right h_comm
  let M : ℝ := 2 * ‖K‖ + 1
  have hM : 2 * ‖K‖ < M := by dsimp [M]; linarith
  let hK_pen := perturbed_isSelfAdjoint_add_real_smul hK hQ.isSelfAdjoint M
  let ψ_pen := opEigenbasis (K + (M : ℂ) • Q) hK_pen
  let μ_pen := opEigenvalues (K + (M : ℂ) • Q) hK_pen
  let E_proj : ManyBodyConfig Site → ℝ := fun ω => if Q (ψ_pen ω) = 0 then μ_pen ω else 0
  have h_eig_proj : ∀ ω : ManyBodyConfig Site,
      (P * K * P) (ψ_pen ω) = (E_proj ω : ℂ) • ψ_pen ω := by
    intro ω
    rcases perturbed_penalized_eigenbasis_dichotomy_of_commute_proj K Q hK hQ h_comm_Q hM ω with
      h_ker | h_ran
    · dsimp only [E_proj]; rw [if_pos h_ker.1]
      have hPψ : P (ψ_pen ω) = ψ_pen ω := by
        have h1 : ψ_pen ω - P (ψ_pen ω) = 0 := by simpa [Q, ContinuousLinearMap.sub_apply] using h_ker.1
        exact (sub_eq_zero.mp h1).symm
      change P (K (P (ψ_pen ω))) = (μ_pen ω : ℂ) • ψ_pen ω
      rw [hPψ, h_ker.2.1, map_smul, hPψ]
    · have hQ_ne : Q (ψ_pen ω) ≠ 0 := by
        intro hQ0
        have h1 : (1 - Q) (ψ_pen ω) = 0 := h_ran.1
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hQ0, sub_zero] at h1
        have h_re : RCLike.re (inner ℂ (ψ_pen ω) (ψ_pen ω)) = 1 :=
          (perturbed_norm_opEigenbasis_le_one (K + (M : ℂ) • Q) hK_pen ω).1
        rw [h1, inner_zero_right, map_zero] at h_re; norm_num at h_re
      dsimp only [E_proj]; rw [if_neg hQ_ne, Complex.ofReal_zero, zero_smul]
      have hPψ : P (ψ_pen ω) = 0 := by simpa [Q, sub_sub_self] using h_ran.1
      change P (K (P (ψ_pen ω))) = 0
      rw [hPψ, map_zero, map_zero]
  rw [perturbed_gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis
    (P * K * P) hPKP ψ_pen E_proj (opEigenbasis_orthonormal _ hK_pen) h_eig_proj β]
  have h1Q : 1 - Q = P := sub_sub_self 1 P
  have h_tr_P := perturbed_hilbertTrace_gibbsBoltzmannOp_one_sub_proj_eq_penalized
    K Q hK hQ h_comm_Q hM β
  dsimp only at h_tr_P; rw [h1Q] at h_tr_P
  have h_tr_Q : hilbertTrace (1 - P) =
      ∑ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (ψ_pen ω) (Q (ψ_pen ω))) :=
    hilbertTrace_eq_sum_opEigenbasis (K + (M : ℂ) • Q) hK_pen Q
  rw [h_tr_P, h_tr_Q, ← Finset.sum_add_distrib]
  unfold gibbsPartitionZ
  refine Finset.sum_congr rfl fun ω _ => ?_
  rcases perturbed_penalized_eigenbasis_dichotomy_of_commute_proj K Q hK hQ h_comm_Q hM ω with
    h_ker | h_ran
  · dsimp only [E_proj]
    have h_ker_P : RCLike.re (inner ℂ (ψ_pen ω) (P (ψ_pen ω))) = 1 := by simpa [h1Q] using h_ker.2.2.1
    rw [if_pos h_ker.1, h_ker_P, h_ker.1, inner_zero_right, map_zero, mul_one, add_zero]
  · have hQ_ne : Q (ψ_pen ω) ≠ 0 := by
      intro hQ0
      have h1 : (1 - Q) (ψ_pen ω) = 0 := h_ran.1
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hQ0, sub_zero] at h1
      have h_re : RCLike.re (inner ℂ (ψ_pen ω) (ψ_pen ω)) = 1 :=
        (perturbed_norm_opEigenbasis_le_one (K + (M : ℂ) • Q) hK_pen ω).1
      rw [h1, inner_zero_right, map_zero] at h_re; norm_num at h_re
    have h_ran_P : RCLike.re (inner ℂ (ψ_pen ω) (P (ψ_pen ω))) = 0 := by simpa [h1Q] using h_ran.2.2.1
    have hQψ : Q (ψ_pen ω) = ψ_pen ω := by
      have h1 : ψ_pen ω - Q (ψ_pen ω) = 0 := by simpa [ContinuousLinearMap.sub_apply] using h_ran.1
      exact (sub_eq_zero.mp h1).symm
    have h_re_one : RCLike.re (inner ℂ (ψ_pen ω) (ψ_pen ω)) = 1 :=
      (perturbed_norm_opEigenbasis_le_one (K + (M : ℂ) • Q) hK_pen ω).1
    dsimp only [E_proj]
    rw [if_neg hQ_ne, mul_zero, Real.exp_zero, h_ran_P, mul_zero, zero_add, hQψ, h_re_one]

/-- Scalar energy shift identity for Boltzmann traces:
$$\operatorname{Tr}(e^{-\beta (H + \Delta E \cdot 1)} M) = e^{-\beta \Delta E} \operatorname{Tr}(e^{-\beta H} M).$$ -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_add_smul_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (ΔE β : ℝ) :
    let hH_shift := perturbed_isSelfAdjoint_add_real_smul hH (by rw [IsSelfAdjoint, star_one]) ΔE
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis (H + (ΔE : ℂ) • 1) hH_shift)
      (opEigenvalues (H + (ΔE : ℂ) • 1) hH_shift) β * M) =
    Real.exp (-β * ΔE) *
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * M) := by
  intro hH_shift
  let ψ := opEigenbasis H hH
  let E := opEigenvalues H hH
  have h_eig_shift : ∀ ω : ManyBodyConfig Site,
      (H + (ΔE : ℂ) • 1) (ψ ω) = ((E ω + ΔE : ℝ) : ℂ) • ψ ω := by
    intro ω
    rw [ContinuousLinearMap.add_apply, opEigenbasis_apply_H H hH ω,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
      Complex.ofReal_add, add_smul]
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
    (H + (ΔE : ℂ) • 1) hH_shift ψ (fun ω => E ω + ΔE) (opEigenbasis_orthonormal H hH)
    h_eig_shift β M]
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
    H hH ψ E (opEigenbasis_orthonormal H hH) (opEigenbasis_apply_H H hH) β M, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h_exp : Real.exp (-β * (E ω + ΔE)) = Real.exp (-β * ΔE) * Real.exp (-β * E ω) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h_exp, mul_assoc]

/-- **Courant–Fischer Unitary Sector Boltzmann Peeling Theorem
(`perturbed_sector_boltzmann_peel_of_unitary_form_comparison`)**:
Let `H` be a self-adjoint Hamiltonian commuting with two star projections `P` and `P'`, and let
`E_w` be a unitary operator conjugating `P` to `P'` (`E_w.1† * P * E_w.1 = P'`). If for all `ϕ`,
$$\operatorname{Re}\langle P' \phi, H (P' \phi)\rangle + \Delta E \cdot \|P' \phi\|^2 \le
  \operatorname{Re}\langle E_w.1 (P' \phi), H (E_w.1 (P' \phi))\rangle,$$
then for all $\beta \ge 0$,
$$\operatorname{Tr}(e^{-\beta H} P) \le e^{-\beta \Delta E} \operatorname{Tr}(e^{-\beta H} P').$$ -/
theorem perturbed_sector_boltzmann_peel_of_unitary_form_comparison {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P P' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P) (hP' : IsStarProjection P')
    (h_comm : Commute H P) (h_comm' : Commute H P')
    (E_w : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hEw_conj : E_w.1† * P * E_w.1 = P') {ΔE β : ℝ} (hβ : 0 ≤ β)
    (h_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      RCLike.re (inner ℂ (P' ϕ) (H (P' ϕ))) + ΔE * ‖P' ϕ‖ ^ 2 ≤
        RCLike.re (inner ℂ (E_w.1 (P' ϕ)) (H (E_w.1 (P' ϕ))))) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * P) ≤
      Real.exp (-β * ΔE) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * P') := by
  let H_shift := H + (ΔE : ℂ) • 1
  have h1_sa : IsSelfAdjoint (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by
    rw [IsSelfAdjoint, star_one]
  have hH_shift : IsSelfAdjoint H_shift := perturbed_isSelfAdjoint_add_real_smul hH h1_sa ΔE
  have h_comm_shift : Commute H_shift P' :=
    h_comm'.add_left ((Commute.one_left P').smul_left (ΔE : ℂ))
  let A_0 := P' * H_shift * P'
  have hA_0 : IsSelfAdjoint A_0 :=
    perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP'.isSelfAdjoint hH_shift
  let PHP := P * H * P
  have hPHP : IsSelfAdjoint PHP := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP.isSelfAdjoint hH
  let B_0 := E_w.1† * PHP * E_w.1
  have hB_0 : IsSelfAdjoint B_0 := perturbed_isSelfAdjoint_unitary_pullback E_w hPHP
  have hEw_mul_star : E_w.1 * E_w.1† = 1 := Unitary.coe_mul_star_self E_w
  have hEw_star_mul : E_w.1† * E_w.1 = 1 := Unitary.coe_star_mul_self E_w
  have hPEw : P * E_w.1 = E_w.1 * P' := by
    calc P * E_w.1
      _ = (E_w.1 * E_w.1†) * P * E_w.1 := by rw [hEw_mul_star, one_mul]
      _ = E_w.1 * (E_w.1† * P * E_w.1) := by simp only [mul_assoc]
      _ = E_w.1 * P' := by rw [hEw_conj]
  have h_form_AB : ∀ ϕ : ManyBodyHilbertSpace Site,
      0 * ‖ϕ‖ ^ 2 + RCLike.re (inner ℂ ϕ (A_0 ϕ)) ≤ RCLike.re (inner ℂ ϕ (B_0 ϕ)) := by
    intro ϕ; rw [zero_mul, zero_add]
    have hP'_adj : P'† = P' := hP'.isSelfAdjoint.star_eq
    have hP_adj : P† = P := hP.isSelfAdjoint.star_eq
    have hA_re : RCLike.re (inner ℂ ϕ (A_0 ϕ)) =
        RCLike.re (inner ℂ (P' ϕ) (H (P' ϕ))) + ΔE * ‖P' ϕ‖ ^ 2 := by
      have h1 : inner ℂ ϕ (A_0 ϕ) = inner ℂ (P' ϕ) (H_shift (P' ϕ)) := by
        calc inner ℂ ϕ ((P' * H_shift * P') ϕ)
          _ = inner ℂ ϕ (P' (H_shift (P' ϕ))) := rfl
          _ = inner ℂ ((P'†) ϕ) (H_shift (P' ϕ)) :=
              (ContinuousLinearMap.adjoint_inner_left P' (H_shift (P' ϕ)) ϕ).symm
          _ = inner ℂ (P' ϕ) (H_shift (P' ϕ)) := by rw [hP'_adj]
      rw [h1, ContinuousLinearMap.add_apply, inner_add_right, map_add,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq]
    have hB_re : RCLike.re (inner ℂ ϕ (B_0 ϕ)) =
        RCLike.re (inner ℂ (E_w.1 (P' ϕ)) (H (E_w.1 (P' ϕ)))) := by
      have hPEw_apply : P (E_w.1 ϕ) = E_w.1 (P' ϕ) := congrFun (congrArg DFunLike.coe hPEw) ϕ
      have h1 : inner ℂ ϕ (B_0 ϕ) = inner ℂ (P (E_w.1 ϕ)) (H (P (E_w.1 ϕ))) := by
        calc inner ℂ ϕ ((E_w.1† * (P * H * P) * E_w.1) ϕ)
          _ = inner ℂ ϕ ((E_w.1†) (P (H (P (E_w.1 ϕ))))) := rfl
          _ = inner ℂ (E_w.1 ϕ) (P (H (P (E_w.1 ϕ)))) :=
              ContinuousLinearMap.adjoint_inner_right E_w.1 ϕ (P (H (P (E_w.1 ϕ))))
          _ = inner ℂ ((P†) (E_w.1 ϕ)) (H (P (E_w.1 ϕ))) :=
              (ContinuousLinearMap.adjoint_inner_left P (H (P (E_w.1 ϕ))) (E_w.1 ϕ)).symm
          _ = inner ℂ (P (E_w.1 ϕ)) (H (P (E_w.1 ϕ))) := by rw [hP_adj]
      rw [h1, hPEw_apply]
    rw [hA_re, hB_re]; exact h_form ϕ
  have hZ_le : gibbsPartitionZ (opEigenvalues B_0 hB_0) β ≤
      gibbsPartitionZ (opEigenvalues A_0 hA_0) β := by
    unfold gibbsPartitionZ
    refine Finset.sum_le_sum fun ω _ => Real.exp_le_exp.mpr ?_
    have h_ev := perturbed_opEigenvalues_add_le_of_form_le A_0 B_0 hA_0 hB_0 h_form_AB ω
    rw [zero_add] at h_ev; nlinarith
  have hZ_A : gibbsPartitionZ (opEigenvalues A_0 hA_0) β =
      Real.exp (-β * ΔE) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * P') +
      hilbertTrace (1 - P') := by
    rw [perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl
      H_shift P' hH_shift hP' h_comm_shift β,
      perturbed_hilbertTrace_gibbsBoltzmannOp_add_smul_one H P' hH ΔE β]
  have hZ_B : gibbsPartitionZ (opEigenvalues B_0 hB_0) β =
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * P) +
      hilbertTrace (1 - P) := by
    rw [perturbed_gibbsPartitionZ_unitary_pullback_eq E_w PHP hPHP hB_0 β,
      perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl H P hH hP h_comm β]
  have h_tr_compl_eq : hilbertTrace (1 - P) = hilbertTrace (1 - P') := by
    have h_conj_compl : E_w.1† * (1 - P) * E_w.1 = 1 - P' := by
      rw [mul_sub, sub_mul, mul_one, hEw_star_mul, hEw_conj]
    rw [← h_conj_compl, hilbertTrace_conj_unitary_adj E_w (1 - P)]
  linarith

/-- Syndrome-block-diagonal effective Hamiltonian associated to a telescoping operator `W_tel`:
$$H_{\mathrm{diag}} := H_0 + c_{\mathrm{shift}} \cdot 1 + \sum_{\sigma : \iota \to \mathrm{Bool}} \Pi_\sigma W_{\mathrm{tel}} \Pi_\sigma.$$ -/
abbrev perturbedSyndromeDiagHamiltonian {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (c_shift : ℝ)
    (W_tel : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  sys.H0 + (c_shift : ℂ) • 1 + perturbedSyndromeDiagOp sys W_tel

/-- Self-adjointness and syndrome-sector commutation of `perturbedSyndromeDiagHamiltonian`. -/
theorem perturbed_isSelfAdjoint_and_commute_syndromeDiagHamiltonian {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (c_shift : ℝ)
    {W_tel : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hW_sa : IsSelfAdjoint W_tel) :
    IsSelfAdjoint (perturbedSyndromeDiagHamiltonian sys c_shift W_tel) ∧
    (∀ σ : ι → Bool,
      Commute (perturbedSyndromeDiagHamiltonian sys c_shift W_tel) (sys.syndromeProjector σ)) := by
  have h1_sa : IsSelfAdjoint (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by
    rw [IsSelfAdjoint, star_one]
  have hH0_c : IsSelfAdjoint (sys.H0 + (c_shift : ℂ) • 1) :=
    perturbed_isSelfAdjoint_add_real_smul sys.isSelfAdjoint_H0 h1_sa c_shift
  have hW_diag : IsSelfAdjoint (perturbedSyndromeDiagOp sys W_tel) :=
    perturbed_isSelfAdjoint_syndromeDiagOp sys hW_sa
  refine ⟨isSelfAdjoint_add hH0_c hW_diag, fun σ => ?_⟩
  have h_comm0 : Commute sys.H0 (sys.syndromeProjector σ) :=
    (syndrome_resolution_indexed sys).2.2.2.2.2.2.2 σ
  have h_comm_c : Commute ((c_shift : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
      (sys.syndromeProjector σ) :=
    (Commute.one_left (sys.syndromeProjector σ)).smul_left (c_shift : ℂ)
  have h_comm_W : Commute (perturbedSyndromeDiagOp sys W_tel) (sys.syndromeProjector σ) :=
    (perturbed_syndromeDiagOp_mul_syndromeProjector sys W_tel σ).2.2
  exact (h_comm0.add_left h_comm_c).add_left h_comm_W

/-! ## 3. Peierls–Bogoliubov Diagonal Trace Monotonicity & Jensen Inequalities (Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Lemma 3.7 (`lem:peierls-bogoliubov`)) -/

/-- Vanishing of `hilbertTrace (gibbsBoltzmannOp ... * 0)` and nonnegativity of
`hilbertTrace (gibbsBoltzmannOp ... * P)` for any star projection `P`. -/
theorem perturbed_boltzmann_trace_zero_and_proj_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P) (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * 0) = 0 ∧
    0 ≤ hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * P) := by
  constructor
  · rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    simp only [ContinuousLinearMap.zero_apply, inner_zero_right, map_zero, mul_zero,
      Finset.sum_const_zero]
  · rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) (hP.re_inner_nonneg _)

/-- Exact partition decomposition into failure and safe Boltzmann traces:
$$\operatorname{Tr}\!\left(e^{-\beta H}(1 - P)\right) + \operatorname{Tr}\!\left(e^{-\beta H} P\right)
  = Z(H, \beta).$$ -/
theorem perturbed_boltzmann_trace_one_sub_add_proj_eq_gibbsPartitionZ {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * (1 - P)) +
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * P) =
    gibbsPartitionZ (opEigenvalues H hH) β := by
  rw [hilbertTrace_gibbsBoltzmannOp_mul_eq, hilbertTrace_gibbsBoltzmannOp_mul_eq]
  unfold gibbsPartitionZ
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  let ψ := opEigenbasis H hH ω
  have h_unit : RCLike.re (inner ℂ ψ ψ) = 1 := (perturbed_norm_opEigenbasis_le_one H hH ω).1
  have h_add : RCLike.re (inner ℂ ψ ((1 - P) ψ)) + RCLike.re (inner ℂ ψ (P ψ)) = 1 := by
    rw [← map_add, ← inner_add_right, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, sub_add_cancel, h_unit]
  calc Real.exp (-β * opEigenvalues H hH ω) * RCLike.re (inner ℂ ψ ((1 - P) ψ)) +
        Real.exp (-β * opEigenvalues H hH ω) * RCLike.re (inner ℂ ψ (P ψ))
    _ = Real.exp (-β * opEigenvalues H hH ω) *
          (RCLike.re (inner ℂ ψ ((1 - P) ψ)) + RCLike.re (inner ℂ ψ (P ψ))) := by ring
    _ = Real.exp (-β * opEigenvalues H hH ω) := by rw [h_add, mul_one]

/-- Spectral resolution of `⟨ϕ, ϕ⟩`, `⟨ϕ, K ϕ⟩`, and `⟨ϕ, gibbsBoltzmannOp K β ϕ⟩` in the
orthonormal eigenbasis of any self-adjoint operator `K`. -/
theorem perturbed_re_inner_ketBra_sum_and_apply_H {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hK : IsSelfAdjoint K)
    (β : ℝ) (ϕ : ManyBodyHilbertSpace Site) :
    let χ := opEigenbasis K hK; let ev := opEigenvalues K hK
    let w : ManyBodyConfig Site → ℝ := fun τ => RCLike.re (inner ℂ ϕ (rankOneKetBra (χ τ) ϕ))
    (∀ τ : ManyBodyConfig Site, 0 ≤ w τ) ∧ (∑ τ : ManyBodyConfig Site, w τ) = RCLike.re (inner ℂ ϕ ϕ) ∧
    (∑ τ : ManyBodyConfig Site, ev τ * w τ) = RCLike.re (inner ℂ ϕ (K ϕ)) ∧
    (∑ τ : ManyBodyConfig Site, Real.exp (-β * ev τ) * w τ) =
      RCLike.re (inner ℂ ϕ (gibbsBoltzmannOp χ ev β ϕ)) := by
  intro χ ev w
  have h_id := onb_sum_ketBra_eq_one χ (opEigenbasis_orthonormal K hK) (opEigenbasis_parseval K hK)
  have hw_nn : ∀ τ : ManyBodyConfig Site, 0 ≤ w τ := by
    intro τ
    have h_conj : inner ℂ ϕ (χ τ) = starRingEnd ℂ (inner ℂ (χ τ) ϕ) := by rw [inner_conj_symm]
    have h_norm : inner ℂ (χ τ) ϕ * starRingEnd ℂ (inner ℂ (χ τ) ϕ) =
        ((‖inner ℂ (χ τ) ϕ‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    dsimp [w]; rw [rankOneKetBra_apply, inner_smul_right, h_conj, h_norm]; exact sq_nonneg _
  have hw_sum : (∑ τ : ManyBodyConfig Site, w τ) = RCLike.re (inner ℂ ϕ ϕ) := by
    calc (∑ τ : ManyBodyConfig Site, w τ)
      _ = RCLike.re (inner ℂ ϕ (∑ τ : ManyBodyConfig Site, rankOneKetBra (χ τ) ϕ)) := by rw [inner_sum, map_sum]
      _ = RCLike.re (inner ℂ ϕ ((∑ τ : ManyBodyConfig Site, rankOneKetBra (χ τ)) ϕ)) := by rw [ContinuousLinearMap.sum_apply]
      _ = RCLike.re (inner ℂ ϕ ϕ) := by rw [h_id, ContinuousLinearMap.one_apply]
  have hK_sum : (∑ τ : ManyBodyConfig Site, ev τ * w τ) = RCLike.re (inner ℂ ϕ (K ϕ)) := by
    calc (∑ τ : ManyBodyConfig Site, ev τ * w τ)
      _ = ∑ τ : ManyBodyConfig Site, RCLike.re (inner ℂ ϕ ((K * rankOneKetBra (χ τ)) ϕ)) := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [(opEigenbasis_ketBra_props K hK τ).1, ContinuousLinearMap.smul_apply, inner_smul_right, re_ofReal_mul]
      _ = RCLike.re (inner ℂ ϕ ((∑ τ : ManyBodyConfig Site, K * rankOneKetBra (χ τ)) ϕ)) := by
          rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]
      _ = RCLike.re (inner ℂ ϕ ((K * ∑ τ : ManyBodyConfig Site, rankOneKetBra (χ τ)) ϕ)) := by rw [Finset.mul_sum]
      _ = RCLike.re (inner ℂ ϕ (K ϕ)) := by rw [h_id, mul_one]
  have hB_sum : (∑ τ : ManyBodyConfig Site, Real.exp (-β * ev τ) * w τ) =
      RCLike.re (inner ℂ ϕ (gibbsBoltzmannOp χ ev β ϕ)) := by
    unfold gibbsBoltzmannOp; rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum]
    refine Finset.sum_congr rfl fun τ _ => by rw [ContinuousLinearMap.smul_apply, inner_smul_right, re_ofReal_mul]
  exact ⟨hw_nn, hw_sum, hK_sum, hB_sum⟩

/-- **Vector Peierls–Bogoliubov Jensen Inequality
(`perturbed_exp_neg_mul_re_inner_le_re_inner_gibbsBoltzmannOp`, Part II, Lemma 3.7 (`lem:peierls-bogoliubov`))**:
$$\exp(-\beta \operatorname{Re}\langle \phi, K \phi\rangle) \le
  \operatorname{Re}\langle \phi, e^{-\beta K} \phi\rangle.$$ -/
theorem perturbed_exp_neg_mul_re_inner_le_re_inner_gibbsBoltzmannOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (K : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hK : IsSelfAdjoint K)
    (β : ℝ) {ϕ : ManyBodyHilbertSpace Site} (hϕ : RCLike.re (inner ℂ ϕ ϕ) = 1) :
    Real.exp (-β * RCLike.re (inner ℂ ϕ (K ϕ))) ≤
      RCLike.re (inner ℂ ϕ (gibbsBoltzmannOp (opEigenbasis K hK) (opEigenvalues K hK) β ϕ)) := by
  let χ := opEigenbasis K hK; let ev := opEigenvalues K hK
  let w : ManyBodyConfig Site → ℝ := fun τ => RCLike.re (inner ℂ ϕ (rankOneKetBra (χ τ) ϕ))
  let μ : ℝ := RCLike.re (inner ℂ ϕ (K ϕ))
  rcases perturbed_re_inner_ketBra_sum_and_apply_H K hK β ϕ with ⟨hw_nn, hw_sum, hK_sum, hB_sum⟩
  rw [hϕ] at hw_sum
  have h_pt : ∀ τ : ManyBodyConfig Site,
      Real.exp (-β * μ) * ((1 - β * (ev τ - μ)) * w τ) ≤ Real.exp (-β * ev τ) * w τ := by
    intro τ
    have h_tangent : 1 - β * (ev τ - μ) ≤ Real.exp (-β * (ev τ - μ)) := by
      have h1 := Real.add_one_le_exp (-β * (ev τ - μ)); linarith
    have h_exp_mul : Real.exp (-β * μ) * Real.exp (-β * (ev τ - μ)) = Real.exp (-β * ev τ) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-β * μ) * ((1 - β * (ev τ - μ)) * w τ)
      _ = (Real.exp (-β * μ) * (1 - β * (ev τ - μ))) * w τ := by ring
      _ ≤ (Real.exp (-β * μ) * Real.exp (-β * (ev τ - μ))) * w τ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_tangent (le_of_lt (Real.exp_pos _))) (hw_nn τ)
      _ = Real.exp (-β * ev τ) * w τ := by rw [h_exp_mul]
  have h_sum_le := Finset.sum_le_sum (fun τ (_ : τ ∈ Finset.univ) => h_pt τ)
  rw [← Finset.mul_sum] at h_sum_le
  have h_lin_sum : (∑ τ : ManyBodyConfig Site, (1 - β * (ev τ - μ)) * w τ) = 1 := by
    have h_eq : (∑ τ : ManyBodyConfig Site, (1 - β * (ev τ - μ)) * w τ) =
        (∑ τ : ManyBodyConfig Site, w τ) -
          β * ((∑ τ : ManyBodyConfig Site, ev τ * w τ) - μ * (∑ τ : ManyBodyConfig Site, w τ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => by ring
    rw [h_eq, hw_sum, hK_sum]; dsimp [μ]; ring
  rw [h_lin_sum, mul_one, hB_sum] at h_sum_le; exact h_sum_le

/-- **Unconditional Subspace Peierls–Bogoliubov Inequality
(`perturbed_gibbsPartitionZ_proj_conj_sub_trace_compl_le_boltzmann_trace`, Part II, Lemma 3.7 (`lem:peierls-bogoliubov`))**:
For any self-adjoint operator `K`, any star projection `P`, and any `β : ℝ`:
$$\operatorname{Tr}(e^{-\beta (P K P)}) - \operatorname{Tr}(1 - P) \le \operatorname{Tr}(e^{-\beta K} P).$$ -/
theorem perturbed_gibbsPartitionZ_proj_conj_sub_trace_compl_le_boltzmann_trace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (K P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hK : IsSelfAdjoint K) (hP : IsStarProjection P) (β : ℝ) :
    let hPKP := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP.isSelfAdjoint hK
    gibbsPartitionZ (opEigenvalues (P * K * P) hPKP) β - hilbertTrace (1 - P) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis K hK) (opEigenvalues K hK) β * P) := by
  intro hPKP; let K_P := P * K * P
  have hP_idem : P * P = P := hP.isIdempotentElem.eq
  have h_comm_KP : Commute K_P P := by
    calc (P * K * P) * P = (P * K) * (P * P) := by rw [mul_assoc]
      _ = P * K * P := by rw [hP_idem]
      _ = (P * P) * K * P := by rw [hP_idem]
      _ = P * (P * K * P) := by simp only [mul_assoc]
  let Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have h_comm_KQ : Commute K_P Q := (Commute.one_right K_P).sub_right h_comm_KP
  let M : ℝ := 2 * ‖K_P‖ + 1
  have hM : 2 * ‖K_P‖ < M := by dsimp [M]; linarith
  let hK_pen := perturbed_isSelfAdjoint_add_real_smul hPKP hQ.isSelfAdjoint M
  let ψ_pen := opEigenbasis (K_P + (M : ℂ) • Q) hK_pen
  let μ_pen := opEigenvalues (K_P + (M : ℂ) • Q) hK_pen
  let E_proj : ManyBodyConfig Site → ℝ := fun ω => if Q (ψ_pen ω) = 0 then μ_pen ω else 0
  have h_eig_proj : ∀ ω : ManyBodyConfig Site, (P * K * P) (ψ_pen ω) = (E_proj ω : ℂ) • ψ_pen ω := by
    intro ω
    rcases perturbed_penalized_eigenbasis_dichotomy_of_commute_proj K_P Q hPKP hQ h_comm_KQ hM ω with h_ker | h_ran
    · dsimp only [E_proj]; rw [if_pos h_ker.1]; exact h_ker.2.1
    · have hQ_ne : Q (ψ_pen ω) ≠ 0 := by
        intro hQ0; have h1 : (1 - Q) (ψ_pen ω) = 0 := h_ran.1
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hQ0, sub_zero] at h1
        have h_re : RCLike.re (inner ℂ (ψ_pen ω) (ψ_pen ω)) = 1 :=
          (perturbed_norm_opEigenbasis_le_one (K_P + (M : ℂ) • Q) hK_pen ω).1
        rw [h1, inner_zero_right, map_zero] at h_re; norm_num at h_re
      dsimp only [E_proj]; rw [if_neg hQ_ne, Complex.ofReal_zero, zero_smul]
      have hPψ : P (ψ_pen ω) = 0 := by simpa [Q, sub_sub_self] using h_ran.1
      change P (K (P (ψ_pen ω))) = 0; rw [hPψ, map_zero, map_zero]
  rw [perturbed_gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis
    (P * K * P) hPKP ψ_pen E_proj (opEigenbasis_orthonormal _ hK_pen) h_eig_proj β]
  have h_tr_Q := hilbertTrace_eq_sum_opEigenbasis (K_P + (M : ℂ) • Q) hK_pen Q
  have h_tr_K := hilbertTrace_eq_sum_opEigenbasis (K_P + (M : ℂ) • Q) hK_pen
    (gibbsBoltzmannOp (opEigenbasis K hK) (opEigenvalues K hK) β * P)
  unfold gibbsPartitionZ
  rw [show hilbertTrace (1 - P) = hilbertTrace Q from rfl, h_tr_Q, h_tr_K, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h_re_one : RCLike.re (inner ℂ (ψ_pen ω) (ψ_pen ω)) = 1 :=
    (perturbed_norm_opEigenbasis_le_one (K_P + (M : ℂ) • Q) hK_pen ω).1
  rcases perturbed_penalized_eigenbasis_dichotomy_of_commute_proj K_P Q hPKP hQ h_comm_KQ hM ω with h_ker | h_ran
  · have hQ0 : Q (ψ_pen ω) = 0 := h_ker.1
    dsimp only [E_proj]; rw [if_pos hQ0, hQ0, inner_zero_right, map_zero, sub_zero]
    have hPψ : P (ψ_pen ω) = ψ_pen ω := by
      have h1 : ψ_pen ω - P (ψ_pen ω) = 0 := by simpa [Q, ContinuousLinearMap.sub_apply] using hQ0
      exact (sub_eq_zero.mp h1).symm
    have hP_adj : P† = P := hP.isSelfAdjoint.star_eq
    have h_mu_eq : μ_pen ω = RCLike.re (inner ℂ (ψ_pen ω) (K (ψ_pen ω))) := by
      have h_eig_ker : K_P (ψ_pen ω) = (μ_pen ω : ℂ) • ψ_pen ω := h_ker.2.1
      calc μ_pen ω
        _ = RCLike.re (inner ℂ (ψ_pen ω) ((μ_pen ω : ℂ) • ψ_pen ω)) := by
            rw [inner_smul_right, re_ofReal_mul, h_re_one, mul_one]
        _ = RCLike.re (inner ℂ (ψ_pen ω) (K_P (ψ_pen ω))) := by rw [← h_eig_ker]
        _ = RCLike.re (inner ℂ (ψ_pen ω) (P (K (P (ψ_pen ω))))) := rfl
        _ = RCLike.re (inner ℂ (ψ_pen ω) (K (ψ_pen ω))) := by
            rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj, hPψ]
    change Real.exp (-β * μ_pen ω) ≤ RCLike.re (inner ℂ (ψ_pen ω)
      (gibbsBoltzmannOp (opEigenbasis K hK) (opEigenvalues K hK) β (P (ψ_pen ω))))
    rw [h_mu_eq, hPψ]
    exact perturbed_exp_neg_mul_re_inner_le_re_inner_gibbsBoltzmannOp K hK β h_re_one
  · have hQ_ne : Q (ψ_pen ω) ≠ 0 := by
      intro hQ0; have h1 : (1 - Q) (ψ_pen ω) = 0 := h_ran.1
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hQ0, sub_zero] at h1
      rw [h1, inner_zero_right, map_zero] at h_re_one; norm_num at h_re_one
    have hPψ : P (ψ_pen ω) = 0 := by simpa [Q, sub_sub_self] using h_ran.1
    have hQψ : Q (ψ_pen ω) = ψ_pen ω := by
      have h1 : ψ_pen ω - Q (ψ_pen ω) = 0 := by simpa [ContinuousLinearMap.sub_apply] using h_ran.1
      exact (sub_eq_zero.mp h1).symm
    dsimp only [E_proj]; rw [if_neg hQ_ne, mul_zero, Real.exp_zero, hQψ, h_re_one, sub_self]
    change (0 : ℝ) ≤ RCLike.re (inner ℂ (ψ_pen ω)
      (gibbsBoltzmannOp (opEigenbasis K hK) (opEigenvalues K hK) β (P (ψ_pen ω))))
    rw [hPψ, map_zero, inner_zero_right, map_zero]

/-- **Unconditional Sector Boltzmann Inequality for `perturbedSyndromeDiagHamiltonian`
(`perturbed_syndromeDiagHamiltonian_sector_boltzmann_le_boltzmann_trace`)**:
$$\operatorname{Tr}(e^{-\beta H_{\mathrm{diag}}} \Pi_\sigma) \le
  \operatorname{Tr}(e^{-\beta H_{\mathrm{tel}}} \Pi_\sigma).$$ -/
theorem perturbed_syndromeDiagHamiltonian_sector_boltzmann_le_boltzmann_trace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (c_shift : ℝ)
    {W_tel : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hW_sa : IsSelfAdjoint W_tel) (β : ℝ) (σ : ι → Bool) :
    let h1_sa : IsSelfAdjoint (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by
      rw [IsSelfAdjoint, star_one]
    let H_tel := sys.H0 + (c_shift : ℂ) • 1 + W_tel
    let hH_tel := isSelfAdjoint_add (perturbed_isSelfAdjoint_add_real_smul sys.isSelfAdjoint_H0 h1_sa c_shift) hW_sa
    let H_diag := perturbedSyndromeDiagHamiltonian sys c_shift W_tel
    let hH_diag := (perturbed_isSelfAdjoint_and_commute_syndromeDiagHamiltonian sys c_shift hW_sa).1
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
      (opEigenvalues H_diag hH_diag) β * sys.syndromeProjector σ) ≤
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_tel hH_tel)
      (opEigenvalues H_tel hH_tel) β * sys.syndromeProjector σ) := by
  intro h1_sa H_tel hH_tel H_diag hH_diag; let P := sys.syndromeProjector σ
  have hP : IsStarProjection P := (syndrome_resolution_indexed sys).2.1 σ
  have h_comm_diag : Commute H_diag P := (perturbed_isSelfAdjoint_and_commute_syndromeDiagHamiltonian sys c_shift hW_sa).2 σ
  have hW_proj : P * perturbedSyndromeDiagOp sys W_tel * P = P * W_tel * P := by
    have h1 := (perturbed_syndromeDiagOp_mul_syndromeProjector sys W_tel σ).1
    change perturbedSyndromeDiagOp sys W_tel * P = P * W_tel * P at h1
    rw [mul_assoc P (perturbedSyndromeDiagOp sys W_tel) P, h1, ← mul_assoc P (P * W_tel) P,
      ← mul_assoc P P W_tel, hP.isIdempotentElem.eq]
  have h_proj_eq : P * H_diag * P = P * H_tel * P := by
    dsimp [H_diag, H_tel, perturbedSyndromeDiagHamiltonian]; simp only [mul_add, add_mul, hW_proj]
  have h_id_diag := perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl H_diag P hH_diag hP h_comm_diag β
  have h_pb := perturbed_gibbsPartitionZ_proj_conj_sub_trace_compl_le_boltzmann_trace H_tel P hH_tel hP β
  dsimp only at h_id_diag h_pb
  let hPD := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP.isSelfAdjoint hH_diag
  let hPT := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP.isSelfAdjoint hH_tel
  have h_Z_eq : gibbsPartitionZ (opEigenvalues (P * H_diag * P) hPD) β =
      gibbsPartitionZ (opEigenvalues (P * H_tel * P) hPT) β :=
    perturbed_gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis
      (P * H_diag * P) hPD (opEigenbasis (P * H_tel * P) hPT) (opEigenvalues (P * H_tel * P) hPT)
      (opEigenbasis_orthonormal (P * H_tel * P) hPT)
      (fun ω => by rw [h_proj_eq]; exact opEigenbasis_apply_H (P * H_tel * P) hPT ω) β
  linarith

/-- Decomposition of `hilbertTrace (gibbsBoltzmannOp ... β * P)` across all syndrome sectors `Π_σ`. -/
lemma perturbed_boltzmann_trace_eq_sum_syndromeProjector_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * P) =
      ∑ σ : ι → Bool,
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
          (sys.syndromeProjector σ * P)) := by
  have h_sum_one : (∑ σ : ι → Bool, sys.syndromeProjector σ) = 1 :=
    (syndrome_resolution_indexed sys).2.2.2.1
  have hP_eq : P = ∑ σ : ι → Bool, sys.syndromeProjector σ * P := by
    rw [← Finset.sum_mul, h_sum_one, one_mul]
  conv_lhs => rw [hP_eq]
  simp_rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.sum_apply, inner_sum, map_sum, Finset.mul_sum]

/-- Sum of syndrome-sector Boltzmann traces equals `gibbsPartitionZ`. -/
lemma perturbed_sum_syndromeProjector_boltzmann_trace_eq_gibbsPartitionZ {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    (∑ σ : ι → Bool,
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
        sys.syndromeProjector σ)) =
    gibbsPartitionZ (opEigenvalues H hH) β := by
  have h1 := perturbed_boltzmann_trace_eq_sum_syndromeProjector_mul sys H 1 hH β
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ] at h1
  simp_rw [mul_one] at h1
  exact h1.symm

/-- **Unconditional Partition Function Upper Bound for `perturbedSyndromeDiagHamiltonian`
(`perturbed_gibbsPartitionZ_syndromeDiagHamiltonian_le_unconditional`)**:
$$Z(H_{\mathrm{diag}}, \beta) \le Z(H_{\mathrm{tel}}, \beta) \le \exp(\beta \varepsilon_{\mathrm{rem}}) Z(H_0 + V_{\mathrm{tot}}, \beta).$$ -/
theorem perturbed_gibbsPartitionZ_syndromeDiagHamiltonian_le_unconditional {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (c_shift : ℝ)
    {W_tel : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hW_sa : IsSelfAdjoint W_tel) (β : ℝ) :
    let h1_sa : IsSelfAdjoint (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by rw [IsSelfAdjoint, star_one]
    let H_tel := sys.H0 + (c_shift : ℂ) • 1 + W_tel
    let hH_tel := isSelfAdjoint_add (perturbed_isSelfAdjoint_add_real_smul sys.isSelfAdjoint_H0 h1_sa c_shift) hW_sa
    let H_diag := perturbedSyndromeDiagHamiltonian sys c_shift W_tel
    let hH_diag := (perturbed_isSelfAdjoint_and_commute_syndromeDiagHamiltonian sys c_shift hW_sa).1
    gibbsPartitionZ (opEigenvalues H_diag hH_diag) β ≤ gibbsPartitionZ (opEigenvalues H_tel hH_tel) β ∧
    (∀ (V : QuasiLocalPerturbation D L Site) (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
      (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
      (R_rem : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) {ε_rem : ℝ},
      0 ≤ β → U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 = H_tel + R_rem → ‖R_rem‖ ≤ ε_rem →
      gibbsPartitionZ (opEigenvalues H_diag hH_diag) β ≤
        Real.exp (β * ε_rem) * gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β) := by
  intro h1_sa H_tel hH_tel H_diag hH_diag
  have h_sec_le : gibbsPartitionZ (opEigenvalues H_diag hH_diag) β ≤
      gibbsPartitionZ (opEigenvalues H_tel hH_tel) β := by
    rw [← perturbed_sum_syndromeProjector_boltzmann_trace_eq_gibbsPartitionZ sys H_diag hH_diag β,
        ← perturbed_sum_syndromeProjector_boltzmann_trace_eq_gibbsPartitionZ sys H_tel hH_tel β]
    exact Finset.sum_le_sum fun σ _ =>
      perturbed_syndromeDiagHamiltonian_sector_boltzmann_le_boltzmann_trace sys c_shift hW_sa β σ
  refine ⟨h_sec_le, fun V hH_pert U_dress R_rem ε_rem hβ h_decomp hR_norm => ?_⟩
  let H_pull := U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1
  let hH_pull := perturbed_isSelfAdjoint_unitary_pullback U_dress hH_pert
  have h_form_diff : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ ((H_pull - H_tel - ((0 : ℝ) : ℂ) • 1) ψ))| ≤ ((2 * ε_rem) / 2) * ‖ψ‖ ^ 2 := by
    intro ψ
    have h_sub : H_pull - H_tel - ((0 : ℝ) : ℂ) • 1 = R_rem := by
      change U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - H_tel - ((0 : ℝ) : ℂ) • 1 = R_rem
      rw [Complex.ofReal_zero, zero_smul, sub_zero, h_decomp, add_sub_cancel_left]
    rw [h_sub]; have h1 := perturbed_re_inner_le_of_opNorm_le hR_norm ψ; linarith
  have h_Z_low := perturbed_gibbsPartitionZ_effective_le_pullback H_tel H_pull hH_tel hH_pull hβ h_form_diff
  have h_exp : -β * (0 : ℝ) - (1 / 2 : ℝ) * β * (2 * ε_rem) = -β * ε_rem := by ring
  rw [h_exp, perturbed_gibbsPartitionZ_unitary_pullback_eq U_dress (sys.H0 + V.totalPerturbation) hH_pert hH_pull β] at h_Z_low
  have h_prod_one : Real.exp (β * ε_rem) * Real.exp (-β * ε_rem) = 1 := by
    rw [← Real.exp_add, show β * ε_rem + -β * ε_rem = 0 by ring, Real.exp_zero]
  have h_Z_tel_le : gibbsPartitionZ (opEigenvalues H_tel hH_tel) β ≤
      Real.exp (β * ε_rem) * gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β := by
    calc gibbsPartitionZ (opEigenvalues H_tel hH_tel) β
      _ = (Real.exp (β * ε_rem) * Real.exp (-β * ε_rem)) * gibbsPartitionZ (opEigenvalues H_tel hH_tel) β := by rw [h_prod_one, one_mul]
      _ = Real.exp (β * ε_rem) * (Real.exp (-β * ε_rem) * gibbsPartitionZ (opEigenvalues H_tel hH_tel) β) := by ring
      _ ≤ Real.exp (β * ε_rem) * gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β :=
          mul_le_mul_of_nonneg_left h_Z_low (le_of_lt (Real.exp_pos _))
  exact le_trans h_sec_le h_Z_tel_le

/-- **Basis-Free Courant–Fischer Boltzmann Trace Comparison on `1 - P`
(`perturbed_commute_boltzmann_trace_one_sub_proj_le_of_form_le`)**:
$$\operatorname{Tr}(e^{-\beta A}(1 - P)) \le \exp(\beta \varepsilon) \operatorname{Tr}(e^{-\beta B}(1 - P)).$$ -/
theorem perturbed_commute_boltzmann_trace_one_sub_proj_le_of_form_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hP : IsStarProjection P)
    (h_commA : Commute A P) (h_commB : Commute B P) {ε β : ℝ} (hβ : 0 ≤ β)
    (h_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      let ψ := (1 - P) ϕ; RCLike.re (inner ℂ ψ (B ψ)) - ε * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (A ψ))) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis A hA) (opEigenvalues A hA) β * (1 - P)) ≤
      Real.exp (β * ε) * hilbertTrace (gibbsBoltzmannOp (opEigenbasis B hB) (opEigenvalues B hB) β * (1 - P)) := by
  let Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have h_commAQ : Commute A Q := (Commute.one_right A).sub_right h_commA
  have h_commBQ : Commute B Q := (Commute.one_right B).sub_right h_commB
  have h1_sa : IsSelfAdjoint (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by rw [IsSelfAdjoint, star_one]
  let B_shift := B + ((-ε : ℝ) : ℂ) • 1
  have hB_shift : IsSelfAdjoint B_shift := perturbed_isSelfAdjoint_add_real_smul hB h1_sa (-ε)
  have h_commBsQ : Commute B_shift Q := h_commBQ.add_left ((Commute.one_left Q).smul_left ((-ε : ℝ) : ℂ))
  let hQAQ := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hQ.isSelfAdjoint hA
  let hQBsQ := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hQ.isSelfAdjoint hB_shift
  have hQ_adj : Q† = Q := hQ.isSelfAdjoint.star_eq
  have h_form_Q : ∀ ϕ : ManyBodyHilbertSpace Site,
      (0 : ℝ) * ‖ϕ‖ ^ 2 + RCLike.re (inner ℂ ϕ ((Q * B_shift * Q) ϕ)) ≤ RCLike.re (inner ℂ ϕ ((Q * A * Q) ϕ)) := by
    intro ϕ; rw [zero_mul, zero_add]
    have h_lhs : RCLike.re (inner ℂ ϕ ((Q * B_shift * Q) ϕ)) = RCLike.re (inner ℂ (Q ϕ) (B (Q ϕ))) - ε * ‖Q ϕ‖ ^ 2 := by
      have h1 : inner ℂ ϕ ((Q * B_shift * Q) ϕ) = inner ℂ (Q ϕ) (B_shift (Q ϕ)) := by
        change inner ℂ ϕ (Q (B_shift (Q ϕ))) = _; rw [← ContinuousLinearMap.adjoint_inner_left, hQ_adj]
      rw [h1]; change RCLike.re (inner ℂ (Q ϕ) ((B + ((-ε : ℝ) : ℂ) • 1) (Q ϕ))) = _
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
        inner_add_right, inner_smul_right, map_add, re_ofReal_mul, inner_self_eq_norm_sq]; ring
    have h_rhs : RCLike.re (inner ℂ ϕ ((Q * A * Q) ϕ)) = RCLike.re (inner ℂ (Q ϕ) (A (Q ϕ))) := by
      change RCLike.re (inner ℂ ϕ (Q (A (Q ϕ)))) = _; rw [← ContinuousLinearMap.adjoint_inner_left, hQ_adj]
    rw [h_lhs, h_rhs]; exact h_form ϕ
  have h_Z_le : gibbsPartitionZ (opEigenvalues (Q * A * Q) hQAQ) β ≤ gibbsPartitionZ (opEigenvalues (Q * B_shift * Q) hQBsQ) β := by
    unfold gibbsPartitionZ; refine Finset.sum_le_sum fun ω _ => ?_
    have h_ev := perturbed_opEigenvalues_add_le_of_form_le (Q * B_shift * Q) (Q * A * Q) hQBsQ hQAQ h_form_Q ω
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h_id_A := perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl A Q hA hQ h_commAQ β
  have h_id_Bs := perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl B_shift Q hB_shift hQ h_commBsQ β
  have h_shift_tr := perturbed_hilbertTrace_gibbsBoltzmannOp_add_smul_one B Q hB (-ε) β
  dsimp only at h_id_A h_id_Bs h_shift_tr
  rw [show -β * (-ε) = β * ε by ring] at h_shift_tr; linarith

/-- **Commuting Subspace Peierls–Bogoliubov Upper Bound
(`perturbed_boltzmann_trace_proj_le_of_commute_and_opNorm_le`)**:
$$\operatorname{Tr}\!\left(e^{-\beta(H_w + W_{\mathrm{in}})} P\right) \le
  \exp(\beta \delta_{\mathrm{in}}) \operatorname{Tr}\!\left(e^{-\beta H_w} P\right).$$ -/
theorem perturbed_boltzmann_trace_proj_le_of_commute_and_opNorm_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H_w W_in P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hHw : IsSelfAdjoint H_w) (hWin : IsSelfAdjoint W_in) (hP : IsStarProjection P)
    (h_commHw : Commute H_w P) (h_commWin : Commute W_in P)
    {δ_in β : ℝ} (hβ : 0 ≤ β) (hW_norm : ‖W_in‖ ≤ δ_in) :
    let hH_tel : IsSelfAdjoint (H_w + W_in) := isSelfAdjoint_add hHw hWin
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis (H_w + W_in) hH_tel)
      (opEigenvalues (H_w + W_in) hH_tel) β * P) ≤
    Real.exp (β * δ_in) *
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_w hHw) (opEigenvalues H_w hHw) β * P) := by
  intro hH_tel
  let Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site := 1 - P
  have hQ : IsStarProjection Q := hP.one_sub
  have h1Q : 1 - Q = P := sub_sub_self 1 P
  have h_comm_tel_Q : Commute (H_w + W_in) Q :=
    (Commute.one_right (H_w + W_in)).sub_right (h_commHw.add_left h_commWin)
  have h_comm_Hw_Q : Commute H_w Q := (Commute.one_right H_w).sub_right h_commHw
  have h_step := perturbed_commute_boltzmann_trace_one_sub_proj_le_of_form_le
    (H_w + W_in) H_w Q hH_tel hHw hQ h_comm_tel_Q h_comm_Hw_Q (ε := δ_in) hβ ?_
  · rwa [h1Q] at h_step
  · intro ϕ; dsimp only; let ψ := (1 - Q) ϕ
    have h_add : RCLike.re (inner ℂ ψ ((H_w + W_in) ψ)) =
        RCLike.re (inner ℂ ψ (H_w ψ)) + RCLike.re (inner ℂ ψ (W_in ψ)) := by
      rw [ContinuousLinearMap.add_apply, inner_add_right, map_add]
    have h_W := (abs_le.mp (perturbed_re_inner_le_of_opNorm_le hW_norm ψ)).1
    linarith

/-- **Unconditional Peierls–Bogoliubov + Weyl Subspace Lower Bound
(`perturbed_commute_boltzmann_trace_le_perturbed_of_opNorm_le`)**:
Requires `Commute H_w P'` and `‖W_in‖ ≤ δ_in` (without requiring `Commute W_in P'`):
$$\operatorname{Tr}\!\left(e^{-\beta H_w} P'\right) \le
  \exp(\beta \delta_{\mathrm{in}}) \operatorname{Tr}\!\left(e^{-\beta(H_w + W_{\mathrm{in}})} P'\right).$$ -/
theorem perturbed_commute_boltzmann_trace_le_perturbed_of_opNorm_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H_w W_in P' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hHw : IsSelfAdjoint H_w) (hWin : IsSelfAdjoint W_in) (hP' : IsStarProjection P')
    (h_commHw' : Commute H_w P') {δ_in β : ℝ} (hβ : 0 ≤ β) (hW_norm : ‖W_in‖ ≤ δ_in) :
    let hH_tel : IsSelfAdjoint (H_w + W_in) := isSelfAdjoint_add hHw hWin
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_w hHw) (opEigenvalues H_w hHw) β * P') ≤
    Real.exp (β * δ_in) *
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis (H_w + W_in) hH_tel)
        (opEigenvalues (H_w + W_in) hH_tel) β * P') := by
  intro hH_tel
  have h1_sa : IsSelfAdjoint (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by
    rw [IsSelfAdjoint, star_one]
  let K := (H_w + W_in) + ((-δ_in : ℝ) : ℂ) • 1
  have hK : IsSelfAdjoint K := perturbed_isSelfAdjoint_add_real_smul hH_tel h1_sa (-δ_in)
  let hPKP := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP'.isSelfAdjoint hK
  let hPHwP := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP'.isSelfAdjoint hHw
  have hP'_adj : P'† = P' := hP'.isSelfAdjoint.star_eq
  have h_form_P' : ∀ ϕ : ManyBodyHilbertSpace Site,
      (0 : ℝ) * ‖ϕ‖ ^ 2 + RCLike.re (inner ℂ ϕ ((P' * K * P') ϕ)) ≤
        RCLike.re (inner ℂ ϕ ((P' * H_w * P') ϕ)) := by
    intro ϕ; rw [zero_mul, zero_add]
    have h_lhs : RCLike.re (inner ℂ ϕ ((P' * K * P') ϕ)) =
        RCLike.re (inner ℂ (P' ϕ) (H_w (P' ϕ))) + RCLike.re (inner ℂ (P' ϕ) (W_in (P' ϕ))) -
          δ_in * ‖P' ϕ‖ ^ 2 := by
      have h1 : inner ℂ ϕ ((P' * K * P') ϕ) = inner ℂ (P' ϕ) (K (P' ϕ)) := by
        change inner ℂ ϕ (P' (K (P' ϕ))) = _; rw [← ContinuousLinearMap.adjoint_inner_left, hP'_adj]
      rw [h1]; change RCLike.re (inner ℂ (P' ϕ) (((H_w + W_in) + ((-δ_in : ℝ) : ℂ) • 1) (P' ϕ))) = _
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, inner_add_right, inner_add_right, inner_smul_right,
        map_add, map_add, re_ofReal_mul, inner_self_eq_norm_sq]; ring
    have h_rhs : RCLike.re (inner ℂ ϕ ((P' * H_w * P') ϕ)) = RCLike.re (inner ℂ (P' ϕ) (H_w (P' ϕ))) := by
      change RCLike.re (inner ℂ ϕ (P' (H_w (P' ϕ)))) = _; rw [← ContinuousLinearMap.adjoint_inner_left, hP'_adj]
    rw [h_lhs, h_rhs]; have h_W := (abs_le.mp (perturbed_re_inner_le_of_opNorm_le hW_norm (P' ϕ))).2; linarith
  have h_Z_le : gibbsPartitionZ (opEigenvalues (P' * H_w * P') hPHwP) β ≤
      gibbsPartitionZ (opEigenvalues (P' * K * P') hPKP) β := by
    unfold gibbsPartitionZ; refine Finset.sum_le_sum fun ω _ => ?_
    have h_ev := perturbed_opEigenvalues_add_le_of_form_le (P' * K * P') (P' * H_w * P') hPKP hPHwP h_form_P' ω
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h_eq_Hw := perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl H_w P' hHw hP' h_commHw' β
  have h_pb_K := perturbed_gibbsPartitionZ_proj_conj_sub_trace_compl_le_boltzmann_trace K P' hK hP' β
  have h_shift := perturbed_hilbertTrace_gibbsBoltzmannOp_add_smul_one (H_w + W_in) P' hH_tel (-δ_in) β
  dsimp only at h_eq_Hw h_pb_K h_shift
  rw [show -β * (-δ_in) = β * δ_in by ring] at h_shift; linarith

/-- **Unconditional Safe-Subspace Peierls–Bogoliubov Boltzmann Trace Lower Bound
(`perturbed_commute_boltzmann_trace_le_of_proj_form_le`, Part II, Lemma 3.7 (`lem:peierls-bogoliubov`))**. -/
theorem perturbed_commute_boltzmann_trace_le_of_proj_form_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H_pull H_comm P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pull : IsSelfAdjoint H_pull) (hH_comm : IsSelfAdjoint H_comm)
    (hP : IsStarProjection P) (h_comm : Commute H_comm P)
    {ε_safe β : ℝ} (hβ : 0 ≤ β)
    (h_form_P : ∀ ϕ : ManyBodyHilbertSpace Site,
      let ψ := P ϕ
      RCLike.re (inner ℂ ψ (H_pull ψ)) ≤
        RCLike.re (inner ℂ ψ (H_comm ψ)) + ε_safe * ‖ψ‖ ^ 2) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
      (opEigenvalues H_comm hH_comm) β * P) ≤
      Real.exp (β * ε_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pull hH_pull)
          (opEigenvalues H_pull hH_pull) β * P) ∧
    Real.exp (-β * ε_safe) *
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
        (opEigenvalues H_comm hH_comm) β * P) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pull hH_pull)
        (opEigenvalues H_pull hH_pull) β * P) := by
  have h1_sa : IsSelfAdjoint (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by
    rw [IsSelfAdjoint, star_one]
  let K := H_pull + ((-ε_safe : ℝ) : ℂ) • 1
  have hK : IsSelfAdjoint K := perturbed_isSelfAdjoint_add_real_smul hH_pull h1_sa (-ε_safe)
  let hPKP := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP.isSelfAdjoint hK
  let hPHP := perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hP.isSelfAdjoint hH_comm
  have hP_adj : P† = P := hP.isSelfAdjoint.star_eq
  have h_form_PKP : ∀ ϕ : ManyBodyHilbertSpace Site,
      (0 : ℝ) * ‖ϕ‖ ^ 2 + RCLike.re (inner ℂ ϕ ((P * K * P) ϕ)) ≤
        RCLike.re (inner ℂ ϕ ((P * H_comm * P) ϕ)) := by
    intro ϕ
    rw [zero_mul, zero_add]
    have h_lhs : RCLike.re (inner ℂ ϕ ((P * K * P) ϕ)) =
        RCLike.re (inner ℂ (P ϕ) (H_pull (P ϕ))) - ε_safe * ‖P ϕ‖ ^ 2 := by
      have h1 : inner ℂ ϕ ((P * K * P) ϕ) = inner ℂ (P ϕ) (K (P ϕ)) := by
        change inner ℂ ϕ (P (K (P ϕ))) = _
        rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj]
      rw [h1]
      change RCLike.re (inner ℂ (P ϕ) ((H_pull + ((-ε_safe : ℝ) : ℂ) • 1) (P ϕ))) = _
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply, inner_add_right, inner_smul_right,
        map_add, re_ofReal_mul, inner_self_eq_norm_sq]
      ring
    have h_rhs : RCLike.re (inner ℂ ϕ ((P * H_comm * P) ϕ)) =
        RCLike.re (inner ℂ (P ϕ) (H_comm (P ϕ))) := by
      change RCLike.re (inner ℂ ϕ (P (H_comm (P ϕ)))) = _
      rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj]
    rw [h_lhs, h_rhs]
    have hϕ := h_form_P ϕ
    (try dsimp only at hϕ)
    linarith
  have h_Z_le : gibbsPartitionZ (opEigenvalues (P * H_comm * P) hPHP) β ≤
      gibbsPartitionZ (opEigenvalues (P * K * P) hPKP) β := by
    unfold gibbsPartitionZ
    refine Finset.sum_le_sum fun ω _ => ?_
    have h_ev := perturbed_opEigenvalues_add_le_of_form_le
      (P * K * P) (P * H_comm * P) hPKP hPHP h_form_PKP ω
    exact Real.exp_le_exp.mpr (by nlinarith)
  have h_eq_comm := perturbed_gibbsPartitionZ_proj_conj_eq_boltzmann_trace_add_trace_compl
    H_comm P hH_comm hP h_comm β
  have h_pb_K := perturbed_gibbsPartitionZ_proj_conj_sub_trace_compl_le_boltzmann_trace K P hK hP β
  have h_shift := perturbed_hilbertTrace_gibbsBoltzmannOp_add_smul_one H_pull P hH_pull (-ε_safe) β
  (try dsimp only at h_eq_comm h_pb_K h_shift)
  rw [show -β * (-ε_safe) = β * ε_safe by ring] at h_shift
  have h_first :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
        (opEigenvalues H_comm hH_comm) β * P) ≤
      Real.exp (β * ε_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pull hH_pull)
          (opEigenvalues H_pull hH_pull) β * P) := by
    linarith
  refine ⟨h_first, ?_⟩
  have h_mul := mul_le_mul_of_nonneg_left h_first (le_of_lt (Real.exp_pos (-β * ε_safe)))
  have h_exp_cancel : Real.exp (-β * ε_safe) * Real.exp (β * ε_safe) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rwa [← mul_assoc, h_exp_cancel, one_mul] at h_mul

/-- **Unconditional Peierls–Bogoliubov Pinching Inequalities for `perturbedSafePinchedOp`
(`perturbed_boltzmann_trace_safePinchedOp_le_unconditional`)**. -/
theorem perturbed_boltzmann_trace_safePinchedOp_le_unconditional {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H_pull P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pull : IsSelfAdjoint H_pull) (hP : IsStarProjection P) {β : ℝ} (hβ : 0 ≤ β) :
    let H_pinch := perturbedSafePinchedOp P H_pull
    let hH_pinch := perturbed_isSelfAdjoint_safePinchedOp hP hH_pull
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pinch hH_pinch)
      (opEigenvalues H_pinch hH_pinch) β * P) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pull hH_pull)
        (opEigenvalues H_pull hH_pull) β * P) ∧
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pinch hH_pinch)
      (opEigenvalues H_pinch hH_pinch) β * (1 - P)) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pull hH_pull)
        (opEigenvalues H_pull hH_pull) β * (1 - P)) ∧
    gibbsPartitionZ (opEigenvalues H_pinch hH_pinch) β ≤
      gibbsPartitionZ (opEigenvalues H_pull hH_pull) β ∧
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pull hH_pull)
      (opEigenvalues H_pull hH_pull) β * (1 - P)) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pinch hH_pinch)
        (opEigenvalues H_pinch hH_pinch) β * (1 - P)) +
      (gibbsPartitionZ (opEigenvalues H_pull hH_pull) β -
        gibbsPartitionZ (opEigenvalues H_pinch hH_pinch) β) := by
  intro H_pinch hH_pinch
  have hP_idem : P * P = P := hP.isIdempotentElem
  have h1P_mul_P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP_idem, sub_self]
  have hP_mul_1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h_pinch_P : ∀ ϕ : ManyBodyHilbertSpace Site,
      let ψ := P ϕ
      RCLike.re (inner ℂ ψ (H_pull ψ)) ≤
        RCLike.re (inner ℂ ψ (H_pinch ψ)) + (0 : ℝ) * ‖ψ‖ ^ 2 := by
    intro ϕ
    (try dsimp only)
    rw [zero_mul, add_zero]
    have hP_apply : P (P ϕ) = P ϕ := by
      change (P * P) ϕ = P ϕ; rw [hP_idem]
    have h1P_apply : (1 - P) (P ϕ) = 0 := by
      change ((1 - P) * P) ϕ = 0; rw [h1P_mul_P, ContinuousLinearMap.zero_apply]
    have h_eq : H_pinch (P ϕ) = P (H_pull (P ϕ)) := by
      change (P * H_pull * P + (1 - P) * H_pull * (1 - P)) (P ϕ) = P (H_pull (P ϕ))
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.mul_apply P H_pull, hP_apply,
        ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply (1 - P) H_pull,
        h1P_apply, map_zero, map_zero, add_zero]
    have hP_adj : P† = P := hP.isSelfAdjoint.star_eq
    have h_in : inner ℂ (P ϕ) (H_pinch (P ϕ)) = inner ℂ (P ϕ) (H_pull (P ϕ)) := by
      rw [h_eq, ← ContinuousLinearMap.adjoint_inner_left, hP_adj, hP_apply]
    rw [h_in]
  have h_pinch_1P : ∀ ϕ : ManyBodyHilbertSpace Site,
      let ψ := (1 - P) ϕ
      RCLike.re (inner ℂ ψ (H_pull ψ)) ≤
        RCLike.re (inner ℂ ψ (H_pinch ψ)) + (0 : ℝ) * ‖ψ‖ ^ 2 := by
    intro ϕ
    (try dsimp only)
    rw [zero_mul, add_zero]
    have h1P_idem : (1 - P) * (1 - P) = 1 - P := hP.one_sub.isIdempotentElem
    have h1P_apply2 : (1 - P) ((1 - P) ϕ) = (1 - P) ϕ := by
      change ((1 - P) * (1 - P)) ϕ = (1 - P) ϕ; rw [h1P_idem]
    have hP_apply2 : P ((1 - P) ϕ) = 0 := by
      change (P * (1 - P)) ϕ = 0; rw [hP_mul_1P, ContinuousLinearMap.zero_apply]
    have h_eq : H_pinch ((1 - P) ϕ) = (1 - P) (H_pull ((1 - P) ϕ)) := by
      change (P * H_pull * P + (1 - P) * H_pull * (1 - P)) ((1 - P) ϕ) =
        (1 - P) (H_pull ((1 - P) ϕ))
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.mul_apply P H_pull, hP_apply2, map_zero, map_zero, zero_add,
        ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply (1 - P) H_pull, h1P_apply2]
    have h1P_adj : (1 - P)† = 1 - P := hP.one_sub.isSelfAdjoint.star_eq
    have h_in : inner ℂ ((1 - P) ϕ) (H_pinch ((1 - P) ϕ)) =
        inner ℂ ((1 - P) ϕ) (H_pull ((1 - P) ϕ)) := by
      rw [h_eq, ← ContinuousLinearMap.adjoint_inner_left, h1P_adj, h1P_apply2]
    rw [h_in]
  have h1 := (perturbed_commute_boltzmann_trace_le_of_proj_form_le
    H_pull H_pinch P hH_pull hH_pinch hP (perturbed_commute_safePinchedOp_proj hP H_pull)
    hβ h_pinch_P).1
  have h_comm_1P : Commute H_pinch (1 - P) :=
    (Commute.one_right H_pinch).sub_right (perturbed_commute_safePinchedOp_proj hP H_pull)
  have h2 := (perturbed_commute_boltzmann_trace_le_of_proj_form_le
    H_pull H_pinch (1 - P) hH_pull hH_pinch hP.one_sub h_comm_1P hβ h_pinch_1P).1
  rw [mul_zero, Real.exp_zero, one_mul] at h1 h2
  have h_sum_pull := perturbed_boltzmann_trace_one_sub_add_proj_eq_gibbsPartitionZ H_pull P hH_pull β
  have h_sum_pinch := perturbed_boltzmann_trace_one_sub_add_proj_eq_gibbsPartitionZ H_pinch P hH_pinch β
  refine ⟨h1, h2, by linarith, by linarith⟩

/-- **Complement Failure Boltzmann Trace Bound from Safe-Subspace Quadratic Form Comparison
(`perturbed_boltzmann_trace_one_sub_le_of_commute_and_proj_form_le`)**. -/
theorem perturbed_boltzmann_trace_one_sub_le_of_commute_and_proj_form_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H_pull H_comm P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pull : IsSelfAdjoint H_pull) (hH_comm : IsSelfAdjoint H_comm)
    (hP : IsStarProjection P) (h_comm : Commute H_comm P)
    {ε_safe β : ℝ} (hβ : 0 ≤ β) (hε_safe : 0 ≤ ε_safe)
    (h_form_P : ∀ ϕ : ManyBodyHilbertSpace Site,
      let ψ := P ϕ
      RCLike.re (inner ℂ ψ (H_pull ψ)) ≤
        RCLike.re (inner ℂ ψ (H_comm ψ)) + ε_safe * ‖ψ‖ ^ 2) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pull hH_pull)
      (opEigenvalues H_pull hH_pull) β * (1 - P)) ≤
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
      (opEigenvalues H_comm hH_comm) β * (1 - P)) +
    (gibbsPartitionZ (opEigenvalues H_pull hH_pull) β -
      Real.exp (-β * ε_safe) * gibbsPartitionZ (opEigenvalues H_comm hH_comm) β) := by
  have h_sum_pull := perturbed_boltzmann_trace_one_sub_add_proj_eq_gibbsPartitionZ H_pull P hH_pull β
  have h_sum_comm := perturbed_boltzmann_trace_one_sub_add_proj_eq_gibbsPartitionZ H_comm P hH_comm β
  have h_sum_comm_scaled :
      Real.exp (-β * ε_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
          (opEigenvalues H_comm hH_comm) β * (1 - P)) +
      Real.exp (-β * ε_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
          (opEigenvalues H_comm hH_comm) β * P) =
      Real.exp (-β * ε_safe) * gibbsPartitionZ (opEigenvalues H_comm hH_comm) β := by
    rw [← mul_add, h_sum_comm]
  have h_safe := (perturbed_commute_boltzmann_trace_le_of_proj_form_le
    H_pull H_comm P hH_pull hH_comm hP h_comm hβ h_form_P).2
  have h_tr_1P_nn : 0 ≤ hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
      (opEigenvalues H_comm hH_comm) β * (1 - P)) :=
    (perturbed_boltzmann_trace_zero_and_proj_nonneg H_comm (1 - P) hH_comm hP.one_sub β).2
  have h_exp_le_one : Real.exp (-β * ε_safe) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have h_scale_1P :
      Real.exp (-β * ε_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
          (opEigenvalues H_comm hH_comm) β * (1 - P)) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_comm hH_comm)
        (opEigenvalues H_comm hH_comm) β * (1 - P)) := by
    nlinarith
  linarith

/-- **Peierls–Bogoliubov Diagonal Trace Monotonicity Sandwich
(`peierls_bogoliubov_commute_proj_boltzmann_trace_sandwich`, Part II, Lemma 3.7 (`lem:peierls-bogoliubov`), Equation (44) (`eq:peierls-bogoliubov-bound`))**:
For any self-adjoint operators `D₁`, `D₂` and star projection `P` commuting with `D₁` and `D₂`,
for all `0 ≤ β`,
$$e^{-\beta \|(D_1 - D_2) P\|} \operatorname{Tr}(e^{-\beta D_2} P)
  \le \operatorname{Tr}(e^{-\beta D_1} P)
  \le e^{\beta \|(D_1 - D_2) P\|} \operatorname{Tr}(e^{-\beta D_2} P).$$ -/
theorem peierls_bogoliubov_commute_proj_boltzmann_trace_sandwich {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (D₁ D₂ P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hD₁ : IsSelfAdjoint D₁) (hD₂ : IsSelfAdjoint D₂) (hP : IsStarProjection P)
    (h_comm₁ : Commute D₁ P) (h_comm₂ : Commute D₂ P) {β : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-β * ‖(D₁ - D₂) * P‖) *
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₂ hD₂) (opEigenvalues D₂ hD₂) β * P) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₁ hD₁) (opEigenvalues D₁ hD₁) β * P) ∧
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₁ hD₁) (opEigenvalues D₁ hD₁) β * P) ≤
      Real.exp (β * ‖(D₁ - D₂) * P‖) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₂ hD₂) (opEigenvalues D₂ hD₂) β * P) := by
  have h_form_diff : ∀ ϕ : ManyBodyHilbertSpace Site,
      let ψ := P ϕ
      |RCLike.re (inner ℂ ψ (D₁ ψ)) - RCLike.re (inner ℂ ψ (D₂ ψ))| ≤
        ‖(D₁ - D₂) * P‖ * ‖ψ‖ ^ 2 := by
    intro ϕ; dsimp only; let ψ := P ϕ
    have hPψ : P ψ = ψ := isStarProjection_apply_self hP ϕ
    have h_act : ((D₁ - D₂) * P) ψ = D₁ ψ - D₂ ψ := by
      rw [ContinuousLinearMap.mul_apply, hPψ, ContinuousLinearMap.sub_apply]
    have h_bound := perturbed_re_inner_le_of_opNorm_le (le_refl ‖(D₁ - D₂) * P‖) ψ
    rw [h_act, inner_sub_right, map_sub] at h_bound
    exact h_bound
  have h_low := (perturbed_commute_boltzmann_trace_le_of_proj_form_le
    D₁ D₂ P hD₁ hD₂ hP h_comm₂ (ε_safe := ‖(D₁ - D₂) * P‖) hβ fun ϕ => by
      dsimp only
      have h1 := (abs_le.mp (h_form_diff ϕ)).2
      linarith).2
  have h_high := (perturbed_commute_boltzmann_trace_le_of_proj_form_le
    D₂ D₁ P hD₂ hD₁ hP h_comm₁ (ε_safe := ‖(D₁ - D₂) * P‖) hβ fun ϕ => by
      dsimp only
      have h1 := (abs_le.mp (h_form_diff ϕ)).1
      linarith).1
  exact ⟨h_low, h_high⟩

/-- When a self-adjoint operator `D_op` acts as the real scalar `d σ` on `sys.syndromeProjector σ`,
the Boltzmann trace `Tr(e^{-β D_op} (Π_σ P))` equals `e^{-β d(σ)} Tr(Π_σ P)`. -/
lemma perturbed_boltzmann_trace_syndromeProjector_mul_eq_of_sector_scalar {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (D_op P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hD : IsSelfAdjoint D_op) (d : (ι → Bool) → ℝ)
    (h_scalar : ∀ σ : ι → Bool,
      sys.syndromeProjector σ * D_op = (d σ : ℂ) • sys.syndromeProjector σ)
    (h_commP : ∀ σ : ι → Bool, Commute P (sys.syndromeProjector σ))
    (β : ℝ) (σ : ι → Bool) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis D_op hD) (opEigenvalues D_op hD) β *
      (sys.syndromeProjector σ * P)) =
    Real.exp (-β * d σ) * hilbertTrace (sys.syndromeProjector σ * P) := by
  rw [hilbertTrace_gibbsBoltzmannOp_mul_eq,
      hilbertTrace_eq_sum_opEigenbasis D_op hD (sys.syndromeProjector σ * P),
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  let ψ := opEigenbasis D_op hD ω
  let ev := opEigenvalues D_op hD ω
  by_cases h_zero : sys.syndromeProjector σ ψ = 0
  · have h_comm_eq : sys.syndromeProjector σ * P = P * sys.syndromeProjector σ :=
      (h_commP σ).symm.eq
    have h_app_zero : (sys.syndromeProjector σ * P) ψ = 0 := by
      rw [h_comm_eq, ContinuousLinearMap.mul_apply, h_zero, map_zero]
    change Real.exp (-β * ev) * RCLike.re (inner ℂ ψ ((sys.syndromeProjector σ * P) ψ)) =
      Real.exp (-β * d σ) * RCLike.re (inner ℂ ψ ((sys.syndromeProjector σ * P) ψ))
    rw [h_app_zero, inner_zero_right, map_zero, mul_zero, mul_zero]
  · have h1 : (sys.syndromeProjector σ * D_op) ψ = (ev : ℂ) • sys.syndromeProjector σ ψ := by
      rw [ContinuousLinearMap.mul_apply, opEigenbasis_apply_H D_op hD ω, map_smul]
    have h2 : (sys.syndromeProjector σ * D_op) ψ = (d σ : ℂ) • sys.syndromeProjector σ ψ := by
      rw [h_scalar σ, ContinuousLinearMap.smul_apply]
    have h_sub : ((ev : ℂ) - (d σ : ℂ)) • sys.syndromeProjector σ ψ = 0 := by
      rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h_sub with h_eq | h_abs
    · have h_ev_eq : ev = d σ := Complex.ofReal_injective (sub_eq_zero.mp h_eq)
      change Real.exp (-β * ev) * RCLike.re (inner ℂ ψ ((sys.syndromeProjector σ * P) ψ)) =
        Real.exp (-β * d σ) * RCLike.re (inner ℂ ψ ((sys.syndromeProjector σ * P) ψ))
      rw [h_ev_eq]
    · exact False.elim (h_zero h_abs)

/-- **Syndrome-Sector Peierls–Bogoliubov Jensen Lower Bound
(`peierls_bogoliubov_syndrome_sector_jensen_lower_bound`, Part II, Lemma 3.7 (`lem:peierls-bogoliubov`))**:
Whenever self-adjoint operators `D₁`, `D₂` act as scalars `d₁ σ`, `d₂ σ` on each syndrome sector `Π_σ`
and `P` commutes with every `Π_σ` with non-negative real quadratic form (`0 ≤ Re ⟨ψ, P ψ⟩`) and
`0 < Tr(e^{-β D₂} P)`, Jensen's inequality on the sector probability measure
`μ₂(σ) := Tr(e^{-β D₂}(Π_σ P)) / Tr(e^{-β D₂} P)` yields
$$\operatorname{Tr}(e^{-\beta D_2} P)
  \exp\!\left(-\beta \sum_\sigma \mu_2(\sigma)\bigl(d_1(\sigma) - d_2(\sigma)\bigr)\right)
  \le \operatorname{Tr}(e^{-\beta D_1} P).$$ -/
theorem peierls_bogoliubov_syndrome_sector_jensen_lower_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (D₁ D₂ P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hD₁ : IsSelfAdjoint D₁) (hD₂ : IsSelfAdjoint D₂)
    (d₁ d₂ : (ι → Bool) → ℝ)
    (h_scalar₁ : ∀ σ : ι → Bool,
      sys.syndromeProjector σ * D₁ = (d₁ σ : ℂ) • sys.syndromeProjector σ)
    (h_scalar₂ : ∀ σ : ι → Bool,
      sys.syndromeProjector σ * D₂ = (d₂ σ : ℂ) • sys.syndromeProjector σ)
    (h_commP : ∀ σ : ι → Bool, Commute P (sys.syndromeProjector σ))
    (hP_pos : ∀ ψ : ManyBodyHilbertSpace Site, 0 ≤ RCLike.re (inner ℂ ψ (P ψ)))
    (β : ℝ)
    (hZ₂_pos : 0 < hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₂ hD₂) (opEigenvalues D₂ hD₂) β * P)) :
    let Z₂ := hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₂ hD₂) (opEigenvalues D₂ hD₂) β * P)
    let μ₂ : (ι → Bool) → ℝ := fun σ =>
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₂ hD₂) (opEigenvalues D₂ hD₂) β *
        (sys.syndromeProjector σ * P)) / Z₂
    Z₂ * Real.exp (-β * ∑ σ : ι → Bool, μ₂ σ * (d₁ σ - d₂ σ)) ≤
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₁ hD₁) (opEigenvalues D₁ hD₁) β * P) := by
  intro Z₂ μ₂
  let w : (ι → Bool) → ℝ := fun σ =>
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₂ hD₂) (opEigenvalues D₂ hD₂) β *
      (sys.syndromeProjector σ * P))
  let m : ℝ := ∑ σ : ι → Bool, μ₂ σ * (d₁ σ - d₂ σ)
  have hw_nn : ∀ σ : ι → Bool, 0 ≤ w σ := by
    intro σ
    have h_proj : IsStarProjection (sys.syndromeProjector σ) := (syndrome_resolution_indexed sys).2.1 σ
    have h_pinch : sys.syndromeProjector σ * P =
        sys.syndromeProjector σ * P * sys.syndromeProjector σ := by
      calc sys.syndromeProjector σ * P
        _ = (sys.syndromeProjector σ * sys.syndromeProjector σ) * P := by
            rw [h_proj.isIdempotentElem.eq]
        _ = sys.syndromeProjector σ * (sys.syndromeProjector σ * P) := by rw [mul_assoc]
        _ = sys.syndromeProjector σ * (P * sys.syndromeProjector σ) := by rw [(h_commP σ).symm.eq]
        _ = sys.syndromeProjector σ * P * sys.syndromeProjector σ := by rw [mul_assoc]
    dsimp only [w]
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    refine Finset.sum_nonneg fun ω _ => mul_nonneg (le_of_lt (Real.exp_pos _)) ?_
    let ψ := opEigenbasis D₂ hD₂ ω
    have h_in : inner ℂ ψ ((sys.syndromeProjector σ * P) ψ) =
        inner ℂ (sys.syndromeProjector σ ψ) (P (sys.syndromeProjector σ ψ)) := by
      rw [h_pinch]
      calc inner ℂ ψ ((sys.syndromeProjector σ * P * sys.syndromeProjector σ) ψ)
        _ = inner ℂ ψ (sys.syndromeProjector σ (P (sys.syndromeProjector σ ψ))) := rfl
        _ = inner ℂ (((sys.syndromeProjector σ)†) ψ) (P (sys.syndromeProjector σ ψ)) :=
            (ContinuousLinearMap.adjoint_inner_left (sys.syndromeProjector σ)
              (P (sys.syndromeProjector σ ψ)) ψ).symm
        _ = inner ℂ (sys.syndromeProjector σ ψ) (P (sys.syndromeProjector σ ψ)) := by
            have h_adj : (sys.syndromeProjector σ)† = sys.syndromeProjector σ :=
              h_proj.isSelfAdjoint.star_eq
            rw [h_adj]
    change 0 ≤ RCLike.re (inner ℂ ψ ((sys.syndromeProjector σ * P) ψ))
    rw [h_in]
    exact hP_pos (sys.syndromeProjector σ ψ)
  have hw_sum : (∑ σ : ι → Bool, w σ) = Z₂ :=
    (perturbed_boltzmann_trace_eq_sum_syndromeProjector_mul sys D₂ P hD₂ β).symm
  have hD₁_sum :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis D₁ hD₁) (opEigenvalues D₁ hD₁) β * P) =
      ∑ σ : ι → Bool, Real.exp (-β * (d₁ σ - d₂ σ)) * w σ := by
    rw [perturbed_boltzmann_trace_eq_sum_syndromeProjector_mul sys D₁ P hD₁ β]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 := perturbed_boltzmann_trace_syndromeProjector_mul_eq_of_sector_scalar
      sys D₁ P hD₁ d₁ h_scalar₁ h_commP β σ
    have h2 := perturbed_boltzmann_trace_syndromeProjector_mul_eq_of_sector_scalar
      sys D₂ P hD₂ d₂ h_scalar₂ h_commP β σ
    dsimp only [w]
    rw [h1, h2, ← mul_assoc, ← Real.exp_add]
    congr 1; congr 1; ring
  have h_pt : ∀ σ : ι → Bool,
      Real.exp (-β * m) * ((1 - β * ((d₁ σ - d₂ σ) - m)) * w σ) ≤
        Real.exp (-β * (d₁ σ - d₂ σ)) * w σ := by
    intro σ
    have h_tan : 1 - β * ((d₁ σ - d₂ σ) - m) ≤ Real.exp (-β * ((d₁ σ - d₂ σ) - m)) := by
      have h1 := Real.add_one_le_exp (-β * ((d₁ σ - d₂ σ) - m)); linarith
    have h_exp_mul :
        Real.exp (-β * m) * Real.exp (-β * ((d₁ σ - d₂ σ) - m)) =
          Real.exp (-β * (d₁ σ - d₂ σ)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (-β * m) * ((1 - β * ((d₁ σ - d₂ σ) - m)) * w σ)
      _ = (Real.exp (-β * m) * (1 - β * ((d₁ σ - d₂ σ) - m))) * w σ := by ring
      _ ≤ (Real.exp (-β * m) * Real.exp (-β * ((d₁ σ - d₂ σ) - m))) * w σ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_tan (le_of_lt (Real.exp_pos _))) (hw_nn σ)
      _ = Real.exp (-β * (d₁ σ - d₂ σ)) * w σ := by rw [h_exp_mul]
  have h_sum_le := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => h_pt σ)
  rw [← Finset.mul_sum, ← hD₁_sum] at h_sum_le
  have hZ₂_ne : Z₂ ≠ 0 := ne_of_gt hZ₂_pos
  have h_mean_sum : (∑ σ : ι → Bool, (d₁ σ - d₂ σ) * w σ) = m * Z₂ := by
    dsimp only [m, μ₂]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    change (d₁ σ - d₂ σ) * w σ = ((w σ / Z₂) * (d₁ σ - d₂ σ)) * Z₂
    field_simp [hZ₂_ne]
  have h_lin_sum : (∑ σ : ι → Bool, (1 - β * ((d₁ σ - d₂ σ) - m)) * w σ) = Z₂ := by
    have h_eq : (∑ σ : ι → Bool, (1 - β * ((d₁ σ - d₂ σ) - m)) * w σ) =
        (∑ σ : ι → Bool, w σ) -
          β * ((∑ σ : ι → Bool, (d₁ σ - d₂ σ) * w σ) - m * (∑ σ : ι → Bool, w σ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun σ _ => by ring
    rw [h_eq, hw_sum, h_mean_sum]; ring
  rw [h_lin_sum, mul_comm] at h_sum_le
  exact h_sum_le

end
