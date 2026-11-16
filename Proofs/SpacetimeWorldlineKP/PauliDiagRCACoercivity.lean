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

import Defs.LocalCSSDescriptor
import Proofs.SpacetimeWorldlineKP.PositiveCheckProductWitnessBound

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SpacetimeWorldlineKP

/-!
# Basis-Free Syndrome Pinching and RCA-1 Pauli-Diagonal Coercivity

Introduces the basis-free syndrome-pinching superoperator (`syndromePinchOp`) splitting finite-range perturbations (`totalPerturbation_eq_sum_Icc_min_of_hasFiniteRangeBound`) into `pauliDiagonalPart` and `pauliOffDiagonalPart`. Uses linear TQO and RCA-1 check-collar localization to establish uniform syndrome-diagonal coercivity (`HasSyndromeDiagonalCoercivity`, `hasSyndromeDiagonalCoercivity_of_tqo_and_finiteRange`).

## References

* Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)
-/

/-! ## 1. Check-Diagonal Local Scalar Indistinguishability & Coercivity Predicates -/

/-- **Syndrome-Sector Relative Coercivity Bound (`HasSyndromeDiagonalCoercivity`)**:
    A self-adjoint operator $V_{\mathrm{diag}}$ commuting with every check projector `sys.checkProj c`
    satisfies $\mathrm{RCA1}$ diagonal coercivity with constant $C_{\mathrm{diag}} \ge 0$ and scalar
    shift $E_{\mathrm{shift}} \in \mathbb{R}$ if for every syndrome $\sigma : \iota \to \mathrm{Bool}$
    and state vector $\psi$,
    $$|\operatorname{Re}\langle \Pi_\sigma \psi, (V_{\mathrm{diag}} - E_{\mathrm{shift}} \mathbf{1}) \Pi_\sigma \psi \rangle|
      \le C_{\mathrm{diag}} \, \mathrm{sys.syndromeEnergy}(\sigma) \, \|\Pi_\sigma \psi\|^2.$$ -/
def HasSyndromeDiagonalCoercivity {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (E_shift C_diag : ℝ) : Prop :=
  IsSelfAdjoint V_diag ∧
  (∀ c : ι, Commute V_diag (sys.checkProj c)) ∧
  ∀ (σ : ι → Bool) (ψ : ManyBodyHilbertSpace Site),
    |RCLike.re (inner ℂ (sys.syndromeProjector σ ψ)
        ((V_diag - ((E_shift : ℝ) : ℂ) • 1) (sys.syndromeProjector σ ψ)))| ≤
      C_diag * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2

/-- **Local Check-Violation Support Bound (`HasLocalCheckViolationCover`)**:
    A check-diagonal local term $M$ that vanishes on the local check-unviolated projector
    $\prod_{c \in C_A} P_c$ is supported exclusively on the union of check-violated subspaces
    $1 - P_c$ for $c \in C_A$, so for every syndrome $\sigma$:
    $$(\forall c \in C_A,\; \sigma(c) = \mathrm{false}) \implies M \Pi_\sigma = 0,$$
    and therefore $\|\Pi_\sigma M \Pi_\sigma\| \le \|M\| \sum_{c \in C_A} \mathbf{1}_{\{\sigma(c) = \mathrm{true}\}}$. -/
def HasLocalCheckViolationCover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (C_A : Finset ι) (e_M : ℝ) : Prop :=
  IsSelfAdjoint M ∧
  (∀ c : ι, Commute M (sys.checkProj c)) ∧
  ∀ σ : ι → Bool,
    (∀ c ∈ C_A, σ c = false) →
    (M - ((e_M : ℝ) : ℂ) • 1) * sys.syndromeProjector σ = 0

/-! ## 2. $\mathrm{RCA1}$ Diagonal Syndrome Energy Coercivity (Part II, Proposition 3.4 (`prop:pauli-diag-off`)) -/

/-- **Single-Term Local Check-Violation Energy Bound
    (`inner_syndrome_le_check_violation_sum_of_local_cover`)**:
    If a check-diagonal local term $M$ satisfies `HasLocalCheckViolationCover sys M C_A e_M`, then
    for every syndrome $\sigma : \iota \to \mathrm{Bool}$ and vector $\psi$:
    $$|\operatorname{Re}\langle \Pi_\sigma \psi, (M - e_M \mathbf{1}) \Pi_\sigma \psi \rangle|
      \le \|M - e_M \mathbf{1}\| \Bigl(\sum_{c \in C_A} (if\;\sigma(c)\;then\;1\;else\;0)\Bigr)
        \|\Pi_\sigma \psi\|^2.$$ -/
theorem inner_syndrome_le_check_violation_sum_of_local_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {C_A : Finset ι} {e_M : ℝ}
    (h_cov : HasLocalCheckViolationCover sys M C_A e_M) (σ : ι → Bool) (ψ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ (sys.syndromeProjector σ ψ)
        ((M - ((e_M : ℝ) : ℂ) • 1) (sys.syndromeProjector σ ψ)))| ≤
      ‖M - ((e_M : ℝ) : ℂ) • 1‖ * (∑ c ∈ C_A, if σ c then (1 : ℝ) else 0) *
        ‖sys.syndromeProjector σ ψ‖ ^ 2 := by
  let D_M := M - ((e_M : ℝ) : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  let φ := sys.syndromeProjector σ ψ
  change |RCLike.re (inner ℂ φ (D_M φ))| ≤ ‖D_M‖ * (∑ c ∈ C_A, if σ c then (1 : ℝ) else 0) * ‖φ‖ ^ 2
  by_cases h_clean : ∀ c ∈ C_A, σ c = false
  · have h_apply : D_M φ = 0 := by change (D_M * sys.syndromeProjector σ) ψ = 0; rw [h_cov.2.2 σ h_clean, ContinuousLinearMap.zero_apply]
    rw [h_apply, inner_zero_right, RCLike.zero_re, abs_zero]
    have h_sum_nn : 0 ≤ ∑ c ∈ C_A, if σ c then (1 : ℝ) else 0 := Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num
    positivity
  · push_neg at h_clean; rcases h_clean with ⟨c₀, hc₀_mem, hc₀_ne⟩
    have hc₀_true : σ c₀ = true := Bool.eq_true_of_not_eq_false hc₀_ne
    have h_one_le_sum : (1 : ℝ) ≤ ∑ c ∈ C_A, if σ c then (1 : ℝ) else 0 := by
      have h_le := Finset.single_le_sum (f := fun c => if σ c then (1 : ℝ) else 0)
        (fun c _ => by (try dsimp only); split_ifs <;> norm_num) hc₀_mem; simpa [hc₀_true] using h_le
    have h_re := RCLike.abs_re_le_norm (inner ℂ φ (D_M φ)); have h_cs := norm_inner_le_norm (𝕜 := ℂ) φ (D_M φ)
    have h_op := ContinuousLinearMap.le_opNorm D_M φ
    have h_cs_sq : |RCLike.re (inner ℂ φ (D_M φ))| ≤ ‖D_M‖ * 1 * ‖φ‖ ^ 2 := by
      have h_mul := mul_le_mul_of_nonneg_left h_op (norm_nonneg φ); nlinarith [sq ‖φ‖]
    exact le_trans h_cs_sq (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_one_le_sum (norm_nonneg D_M)) (sq_nonneg ‖φ‖))

/-- **RCA1 Diagonal Syndrome Coercivity Sandwich (`rca1_diagonal_syndrome_coercivity_sandwich`,
    Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`), Equation `eq:H-diag-relative-bound`)**:
    When `V_diag` satisfies `HasSyndromeDiagonalCoercivity sys V_diag E_shift C_diag` with $C_{\mathrm{diag}} \le \frac{1}{4}$,
    the shifted diagonal Hamiltonian $H_{\mathrm{diag}} := H_0 + V_{\mathrm{diag}} - E_{\mathrm{shift}}\mathbf{1}$ commutes with
    every syndrome projector $\Pi_\sigma$ and satisfies the two-sided $\frac{3}{4}$–$\frac{5}{4}$ syndrome-energy sandwich. -/
theorem rca1_diagonal_syndrome_coercivity_sandwich {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {V_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {E_shift C_diag : ℝ}
    (h_coerc : HasSyndromeDiagonalCoercivity sys V_diag E_shift C_diag) (hC_le : C_diag ≤ 1 / 4) :
    let H_diag := sys.H0 + V_diag - ((E_shift : ℝ) : ℂ) • 1
    IsSelfAdjoint H_diag ∧ (∀ σ : ι → Bool, Commute H_diag (sys.syndromeProjector σ)) ∧
    ∀ (σ : ι → Bool) (ψ : ManyBodyHilbertSpace Site),
      (3 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2 ≤
        RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))) ∧
      RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))) ≤
        (5 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2 := by
  (try dsimp only); rcases h_coerc with ⟨hV_sa, hV_comm, hV_bound⟩
  have h_shift_sa : IsSelfAdjoint (((E_shift : ℝ) : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :=
    isSelfAdjoint_real_smul E_shift (IsSelfAdjoint.one _)
  have hH_diag_sa : IsSelfAdjoint (sys.H0 + V_diag - ((E_shift : ℝ) : ℂ) • 1) := by
    have h1 : ContinuousLinearMap.adjoint sys.H0 = sys.H0 := sys.isSelfAdjoint_H0.star_eq
    have h2 : ContinuousLinearMap.adjoint V_diag = V_diag := hV_sa.star_eq
    have h3 : ContinuousLinearMap.adjoint (((E_shift : ℝ) : ℂ) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) = ((E_shift : ℝ) : ℂ) • 1 := h_shift_sa.star_eq
    change ContinuousLinearMap.adjoint (sys.H0 + V_diag - ((E_shift : ℝ) : ℂ) • 1) = _; rw [map_sub, map_add, h1, h2, h3]
  refine ⟨hH_diag_sa, fun σ => ?_, fun σ ψ => ?_⟩
  · exact ((indexed_check_commuting_perturbation_commutes_with_syndromeProjector sys V_diag hV_comm).2.2 σ).sub_left
      ((Commute.one_left (sys.syndromeProjector σ)).smul_left ((E_shift : ℝ) : ℂ))
  · let φ := sys.syndromeProjector σ ψ; have h_res := syndrome_resolution_indexed sys
    have h_act : sys.H0 φ = (sys.syndromeEnergy σ : ℂ) • φ := by
      calc sys.H0 φ = (sys.H0 * sys.syndromeProjector σ) φ := by
            rw [ContinuousLinearMap.mul_apply, isStarProjection_apply_self (h_res.2.1 σ) ψ]
        _ = (sys.syndromeEnergy σ : ℂ) • φ := by
            rw [h_res.2.2.2.2.1 σ, ContinuousLinearMap.smul_apply, isStarProjection_apply_self (h_res.2.1 σ) ψ]
    have h_H0_re : RCLike.re (inner ℂ φ (sys.H0 φ)) = sys.syndromeEnergy σ * ‖φ‖ ^ 2 := by
      rw [h_act, inner_smul_right, re_ofReal_mul, inner_self_eq_norm_sq]
    have h_decomp : RCLike.re (inner ℂ φ ((sys.H0 + V_diag - ((E_shift : ℝ) : ℂ) • 1) φ)) =
        RCLike.re (inner ℂ φ (sys.H0 φ)) + RCLike.re (inner ℂ φ ((V_diag - ((E_shift : ℝ) : ℂ) • 1) φ)) := by
      rw [add_sub_assoc, ContinuousLinearMap.add_apply, inner_add_right, map_add]
    have h_abs := abs_le.mp (hV_bound σ ψ)
    have hE_nn : 0 ≤ sys.syndromeEnergy σ := Finset.sum_nonneg fun i _ => le_trans zero_le_one (sys.weight_ge_one i)
    have h_C_mul : C_diag * sys.syndromeEnergy σ * ‖φ‖ ^ 2 ≤ (1 / 4 : ℝ) * sys.syndromeEnergy σ * ‖φ‖ ^ 2 := by
      have : 0 ≤ sys.syndromeEnergy σ * ‖φ‖ ^ 2 := mul_nonneg hE_nn (sq_nonneg ‖φ‖); nlinarith
    refine ⟨?_, ?_⟩ <;> linarith [h_decomp, h_H0_re, h_abs.1, h_abs.2, h_C_mul]

/-! ## 3. Syndrome-Diagonal Pinching & TQO-1/2 Instantiation of `HasSyndromeDiagonalCoercivity` -/

/-- **Finite-Range Perturbation Bound (`HasFiniteRangeBound`)**:
    Every interaction cube $A \in \mathrm{BoxCubes}\;D\;L\;r$ of side length $r \le R_{\mathrm{pert}}$
    has operator norm $\|V.\mathrm{term}\;r\;A\| \le J$, and $V.\mathrm{term}\;r\;A = 0$ for all $r > R_{\mathrm{pert}}$. -/
abbrev HasFiniteRangeBound
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (R_pert : ℕ) (J : ℝ) : Prop :=
  ∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L r,
    (r ≤ R_pert → ‖V.term r A‖ ≤ J) ∧
    (R_pert < r → V.term r A = 0)

/-- **Syndrome-Diagonal Pinching Operator (`syndromePinchOp`)**:
    Projects any operator $M$ onto its block-diagonal part $\sum_\sigma \Pi_\sigma M \Pi_\sigma$
    in the joint check-syndrome basis of `sys`. -/
def syndromePinchOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ : ι → Bool, sys.syndromeProjector σ * M * sys.syndromeProjector σ

/-- **Finite-Range Pauli Syndrome-Diagonal Perturbation Part (`pauliDiagonalPart`)**:
    Sums the syndrome-diagonal pinched local terms $\mathrm{syndromePinchOp}\;\mathrm{sys}\;(V.\mathrm{term}\;r\;A)$
    over all active interaction scales $1 \le r \le \min(R_{\mathrm{pert}}, L)$ and cubes $A \in \mathrm{BoxCubes}\;D\;L\;r$. -/
def pauliDiagonalPart {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (R_pert : ℕ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes D L r,
    syndromePinchOp sys (V.term r A)

/-- **Finite-Range Pauli Syndrome-Off-Diagonal Jump Part (`pauliOffDiagonalPart`)**:
    Sums the off-diagonal local jump terms $V.\mathrm{term}\;r\;A - \mathrm{syndromePinchOp}\;\mathrm{sys}\;(V.\mathrm{term}\;r\;A)$
    over all active interaction scales $1 \le r \le \min(R_{\mathrm{pert}}, L)$ and cubes $A \in \mathrm{BoxCubes}\;D\;L\;r$. -/
def pauliOffDiagonalPart {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (R_pert : ℕ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes D L r,
    (V.term r A - syndromePinchOp sys (V.term r A))

/-- **Finite-Range Truncation of `QuasiLocalPerturbation.totalPerturbation`
    (`totalPerturbation_eq_sum_Icc_min_of_hasFiniteRangeBound`)**:
    When `V` satisfies `HasFiniteRangeBound V R_pert J`, its total perturbation `V.totalPerturbation`
    truncates identically to active interaction scales $1 \le r \le \min(R_{\mathrm{pert}}, L)$. -/
theorem totalPerturbation_eq_sum_Icc_min_of_hasFiniteRangeBound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {R_pert : ℕ} {J : ℝ} {V : QuasiLocalPerturbation D L Site}
    (h_range : HasFiniteRangeBound V R_pert J) :
    V.totalPerturbation =
      ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes D L r, V.term r A := by
  dsimp [QuasiLocalPerturbation.totalPerturbation]; symm; refine Finset.sum_subset ?_ ?_
  · intro r hr; rw [Finset.mem_Icc] at hr ⊢; exact ⟨hr.1, le_trans hr.2 (Nat.min_le_right R_pert L)⟩
  · intro r hr h_not_min; rw [Finset.mem_Icc] at hr h_not_min; have hr_gt : R_pert < r := by omega
    exact Finset.sum_eq_zero fun A hA => (h_range r (Finset.mem_Icc.mpr hr) A hA).2 hr_gt

/-- **Exact Finite-Range Decomposition `V_tot = pauliDiagonalPart + pauliOffDiagonalPart`
    (`pauliDiagonalPart_add_pauliOffDiagonalPart_eq_V_tot`)**:
    Under `HasFiniteRangeBound V R_pert J`, the total perturbation decomposes identically into
    its syndrome-diagonal and syndrome-off-diagonal parts. -/
theorem pauliDiagonalPart_add_pauliOffDiagonalPart_eq_V_tot {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) {R_pert : ℕ} {J : ℝ}
    (h_range : HasFiniteRangeBound V R_pert J) :
    pauliDiagonalPart sys V R_pert + pauliOffDiagonalPart sys V R_pert = V.totalPerturbation := by
  unfold pauliDiagonalPart pauliOffDiagonalPart; rw [← Finset.sum_add_distrib]
  have h_sum_eq : (∑ r ∈ Finset.Icc 1 (min R_pert L),
      ((∑ A ∈ boxCubes D L r, syndromePinchOp sys (V.term r A)) +
        ∑ A ∈ boxCubes D L r, (V.term r A - syndromePinchOp sys (V.term r A)))) =
      ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes D L r, V.term r A := by
    refine Finset.sum_congr rfl fun r _ => ?_; rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun A _ => add_sub_cancel _ _
  rw [h_sum_eq, ← totalPerturbation_eq_sum_Icc_min_of_hasFiniteRangeBound h_range]

/-- **Self-Adjointness & Check Commutativity of `syndromePinchOp`
    (`syndromePinchOp_isSelfAdjoint_and_commute_checkProj`)**:
    For any self-adjoint operator $M$, `syndromePinchOp sys M` is self-adjoint and commutes with
    every syndrome projector `sys.syndromeProjector σ`, every check projector `sys.checkProj c`,
    and the ground-space projector `sys.P0`. -/
theorem syndromePinchOp_isSelfAdjoint_and_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hM_sa : IsSelfAdjoint M) :
    IsSelfAdjoint (syndromePinchOp sys M) ∧
    (∀ σ : ι → Bool,
      syndromePinchOp sys M * sys.syndromeProjector σ =
        sys.syndromeProjector σ * M * sys.syndromeProjector σ ∧
      sys.syndromeProjector σ * syndromePinchOp sys M =
        sys.syndromeProjector σ * M * sys.syndromeProjector σ ∧
      Commute (syndromePinchOp sys M) (sys.syndromeProjector σ)) ∧
    (∀ c : ι, Commute (syndromePinchOp sys M) (sys.checkProj c)) ∧
    Commute (syndromePinchOp sys M) sys.P0 := by
  have h_res := syndrome_resolution_indexed sys
  refine ⟨perturbed_isSelfAdjoint_syndromeDiagOp sys hM_sa,
    fun σ => perturbed_syndromeDiagOp_mul_syndromeProjector sys M σ, fun c => ?_, ?_⟩
  · unfold syndromePinchOp; refine Commute.sum_left _ _ _ fun σ _ => ?_
    have h_right := h_res.2.2.2.2.2.1 σ c; have h_left := (h_res.2.2.2.2.2.2.1 σ c).symm.eq.trans h_right
    rw [commute_iff_eq, mul_assoc (sys.syndromeProjector σ * M), h_left,
      ← mul_assoc (sys.checkProj c) (sys.syndromeProjector σ * M), ← mul_assoc (sys.checkProj c) (sys.syndromeProjector σ), h_right]
    cases σ c <;> simp
  · rw [← h_res.1]; exact (perturbed_syndromeDiagOp_mul_syndromeProjector sys M (fun _ => false)).2.2

private lemma norm_sq_eq_sum_syndromeProjector_norm_sq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (φ : ManyBodyHilbertSpace Site) : ‖φ‖ ^ 2 = ∑ σ : ι → Bool, ‖sys.syndromeProjector σ φ‖ ^ 2 := by
  have h_one : perturbedSyndromeDiagOp sys 1 = 1 := perturbed_syndromeDiagOp_eq_self_of_commute sys (fun σ => Commute.one_left _)
  have h_re := perturbed_re_inner_syndromeDiagOp_eq_sum sys 1 φ
  rw [h_one] at h_re; simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq] at h_re; exact h_re
private lemma syndromePinchOp_norm_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ‖syndromePinchOp sys M‖ ≤ ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M) fun ψ => ?_; have h_res := syndrome_resolution_indexed sys
  have h_sq : ‖syndromePinchOp sys M ψ‖ ^ 2 ≤ (‖M‖ * ‖ψ‖) ^ 2 := by
    rw [norm_sq_eq_sum_syndromeProjector_norm_sq sys (syndromePinchOp sys M ψ),
      mul_pow, norm_sq_eq_sum_syndromeProjector_norm_sq sys ψ, Finset.mul_sum]; refine Finset.sum_le_sum fun σ _ => ?_
    have h_act : sys.syndromeProjector σ (syndromePinchOp sys M ψ) = sys.syndromeProjector σ (M (sys.syndromeProjector σ ψ)) := by
      change (sys.syndromeProjector σ * perturbedSyndromeDiagOp sys M) ψ = _
      rw [(perturbed_syndromeDiagOp_mul_syndromeProjector sys M σ).2.1]; rfl
    rw [h_act]; have h_proj := isStarProjection_norm_sq_apply_le_bhm (h_res.2.1 σ) (M (sys.syndromeProjector σ ψ))
    have h_op := pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm (sys.syndromeProjector σ ψ)) 2
    linarith [mul_pow ‖M‖ ‖sys.syndromeProjector σ ψ‖ 2]
  exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg M) (norm_nonneg ψ)) (by linarith)
private lemma sum_pauliPhase_eq_diag {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → ZMod 2) :
    (∑ a : ι → ZMod 2, pauliPhase a z) = if z = 0 then (Fintype.card (ι → ZMod 2) : ℂ) else 0 := by
  split_ifs with hz
  · subst hz; simp [pauliPhase]
  · have h_ex : ∃ q₀ : ι, z q₀ ≠ 0 := by by_contra! h_all; exact hz (funext h_all)
    rcases h_ex with ⟨q₀, hzq₀⟩; have hzq₀_one : z q₀ = 1 := zmod2_ne_zero_iff_eq_one _ hzq₀
    let e₀ : ι → ZMod 2 := fun q => if q = q₀ then 1 else 0
    have he₀_phase : pauliPhase e₀ z = -1 := by
      dsimp [pauliPhase, e₀]; have h_sum : (∑ q : ι, (if q = q₀ then (1 : ZMod 2) else 0) * z q) = z q₀ := by simp
      rw [h_sum, hzq₀_one, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
    have h_shift : (∑ a : ι → ZMod 2, pauliPhase a z) = -(∑ a : ι → ZMod 2, pauliPhase a z) := by
      conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight e₀) (fun a => pauliPhase a z)]
      rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun a _ => ?_
      change pauliPhase (a + e₀) z = -pauliPhase a z; rw [pauliPhase_add_left, he₀_phase, mul_neg_one]
    have h_two : (2 : ℂ) * (∑ a : ι → ZMod 2, pauliPhase a z) = 0 := by linear_combination h_shift
    exact (mul_eq_zero.mp h_two).resolve_left two_ne_zero
private abbrev SubSlot3DDiag (L q_code : ℕ) (A : Finset (Box3D L)) : Type := ↥A × Fin q_code
private def extSlotChainDiag {L q_code : ℕ} (A : Finset (Box3D L)) (a : SubSlot3DDiag L q_code A → ZMod 2) :
    BoxSlot3D L q_code → ZMod 2 := fun p => if hp : p.1 ∈ A then a (⟨p.1, hp⟩, p.2) else 0
private def localSlotConfigToSubDiag {L q_code : ℕ} (A : Finset (Box3D L))
    (α : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A) :
    SubSlot3DDiag L q_code A → ZMod 2 := fun p => boolToZMod2 (α p.1 p.2)
private lemma localSlotConfigToSubDiag_injective {L q_code : ℕ} (A : Finset (Box3D L)) :
    Function.Injective (localSlotConfigToSubDiag (L := L) (q_code := q_code) A) := by
  intro α β h; funext x s; have hxs := congr_fun h (x, s); dsimp [localSlotConfigToSubDiag] at hxs
  revert hxs; cases α x s <;> cases β x s <;> decide
private lemma pauliPhase_extSlotChainDiag {L q_code : ℕ} (A : Finset (Box3D L))
    (a : SubSlot3DDiag L q_code A → ZMod 2) (ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    pauliPhase (extSlotChainDiag A a) (codeConfigBits ψ) = pauliPhase a (localSlotConfigToSubDiag A (restrictConfig A ψ)) := by
  dsimp [pauliPhase]
  have h_sum : (∑ p : BoxSlot3D L q_code, extSlotChainDiag A a p * codeConfigBits ψ p) =
      ∑ p : SubSlot3DDiag L q_code A, a p * localSlotConfigToSubDiag A (restrictConfig A ψ) p := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_subset (Finset.subset_univ A)]
    · rw [← Finset.sum_attach A]; refine Finset.sum_congr rfl fun vA _ => Finset.sum_congr rfl fun s _ => ?_
      simp [extSlotChainDiag, codeConfigBits, localSlotConfigToSubDiag, restrictConfig, vA.2]
    · intro v _ hv_not; refine Finset.sum_eq_zero fun s _ => ?_; dsimp [extSlotChainDiag]; rw [dif_neg hv_not, zero_mul]
  rw [h_sum]
private def localDiffSlotChainDiag {L q_code : ℕ} (A : Finset (Box3D L))
    (α β : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A) : BoxSlot3D L q_code → ZMod 2 :=
  extSlotChainDiag A (localSlotConfigToSubDiag A α + localSlotConfigToSubDiag A β)
private lemma flipCodeConfig_localDiffSlotChainDiag {L q_code : ℕ} (A : Finset (Box3D L))
    (α β : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A)
    (ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) (hβ : restrictConfig A ψ = β) :
    flipCodeConfig (localDiffSlotChainDiag A α β) ψ = spliceConfig A α ψ := by
  funext v s; dsimp [flipCodeConfig, spliceConfig, localDiffSlotChainDiag, extSlotChainDiag]
  by_cases hvA : v ∈ A
  · rw [dif_pos hvA, dif_pos hvA]; dsimp [localSlotConfigToSubDiag]
    have hβ_eq : β ⟨v, hvA⟩ s = ψ v s := by rw [← hβ]; rfl
    rw [hβ_eq]; cases ψ v s <;> cases α ⟨v, hvA⟩ s <;> rfl
  · rw [dif_neg hvA, dif_neg hvA]; dsimp [zmod2ToBool]; cases ψ v s <;> rfl
private lemma isSupportedOn_weylPauliZ_extSlotChainDiag {L q_code : ℕ}
    (A : Finset (Box3D L)) (a : SubSlot3DDiag L q_code A → ZMod 2) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (weylPauliZ (extSlotChainDiag A a)) := by
  refine ⟨LinearMap.toContinuousLinearMap
    { toFun := fun ψ_A => WithLp.toLp 2 (fun α => pauliPhase a (localSlotConfigToSubDiag A α) * ψ_A.ofLp α)
      map_add' := fun ψ₁ ψ₂ => by
        ext α; change pauliPhase a (localSlotConfigToSubDiag A α) * (ψ₁.ofLp α + ψ₂.ofLp α) =
          pauliPhase a (localSlotConfigToSubDiag A α) * ψ₁.ofLp α + pauliPhase a (localSlotConfigToSubDiag A α) * ψ₂.ofLp α; ring
      map_smul' := fun c ψ => by
        ext α; change pauliPhase a (localSlotConfigToSubDiag A α) * (c * ψ.ofLp α) =
          c * (pauliPhase a (localSlotConfigToSubDiag A α) * ψ.ofLp α); ring }, ?_⟩
  ext ψ σ; change pauliPhase (extSlotChainDiag A a) (codeConfigBits σ) * ψ.ofLp σ =
    pauliPhase a (localSlotConfigToSubDiag A (restrictConfig A σ)) * ψ.ofLp (spliceConfig A (restrictConfig A σ) σ)
  rw [pauliPhase_extSlotChainDiag A a σ, _root_.spliceConfig_restrictConfig]
private lemma isSupportedOn_weylPauliX_extSlotChainDiag {L q_code : ℕ}
    (A : Finset (Box3D L)) (b : SubSlot3DDiag L q_code A → ZMod 2) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (weylPauliX (extSlotChainDiag A b)) := by
  let flipSub : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A →
      LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A := fun α vA s => xor (α vA s) (zmod2ToBool (b (vA, s)))
  refine ⟨LinearMap.toContinuousLinearMap
    { toFun := fun ψ_A => WithLp.toLp 2 (fun α => ψ_A.ofLp (flipSub α))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, ?_⟩
  ext ψ σ; change ψ.ofLp (flipCodeConfig (extSlotChainDiag A b) σ) = ψ.ofLp (spliceConfig A (flipSub (restrictConfig A σ)) σ)
  refine congrArg ψ.ofLp (funext fun v => funext fun s => ?_); dsimp [flipCodeConfig, spliceConfig, flipSub, restrictConfig, extSlotChainDiag]
  by_cases hvA : v ∈ A
  · rw [dif_pos hvA, dif_pos hvA]
  · rw [dif_neg hvA, dif_neg hvA]; dsimp [zmod2ToBool]; cases σ v s <;> rfl
private lemma exists_local_weylPauli_expansion {L q_code : ℕ} (A : Finset (Box3D L))
    {M : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hM : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A M) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℂ) (a_fam b_fam : ι → BoxSlot3D L q_code → ZMod 2),
      (∀ i : ι, IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (weylPauliZ (a_fam i) * weylPauliX (b_fam i))) ∧
      M = ∑ i : ι, w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) := by
  rcases hM with ⟨O_loc, rfl⟩
  let SubQ := SubSlot3DDiag L q_code A; let Loc := LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A
  let ι := (Loc × Loc) × (SubQ → ZMod 2); let N : ℂ := (Fintype.card (SubQ → ZMod 2) : ℂ)
  have hN_ne : N ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨ι, inferInstance, fun i => (O_loc (_root_.deltaLp i.1.1)).ofLp i.1.2 * N⁻¹ * pauliPhase i.2 (localSlotConfigToSubDiag A i.1.2),
    fun i => extSlotChainDiag A i.2, fun i => localDiffSlotChainDiag A i.1.1 i.1.2,
    fun i => _root_.isSupportedOn_mul A (isSupportedOn_weylPauliZ_extSlotChainDiag A i.2) (isSupportedOn_weylPauliX_extSlotChainDiag A _), ?_⟩
  ext φ ψ; rw [ContinuousLinearMap.sum_apply, _root_.ofLp_sum]
  change (O_loc (WithLp.toLp 2 fun α => φ.ofLp (spliceConfig A α ψ))).ofLp (restrictConfig A ψ) = _
  rw [_root_.clm_apply_ofLp_eq_sum O_loc]; conv_rhs => rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h_inner_sum : ∀ β : Loc, (∑ a : SubQ → ZMod 2, ((((O_loc (_root_.deltaLp α)).ofLp β *
      N⁻¹ * pauliPhase a (localSlotConfigToSubDiag A β)) • (weylPauliZ (extSlotChainDiag A a) *
        weylPauliX (localDiffSlotChainDiag A α β))) φ).ofLp ψ) =
      if β = restrictConfig A ψ then φ.ofLp (spliceConfig A α ψ) * (O_loc (_root_.deltaLp α)).ofLp β else 0 := by
    intro β
    have h_term : ∀ a : SubQ → ZMod 2, ((((O_loc (_root_.deltaLp α)).ofLp β *
        N⁻¹ * pauliPhase a (localSlotConfigToSubDiag A β)) • (weylPauliZ (extSlotChainDiag A a) *
          weylPauliX (localDiffSlotChainDiag A α β))) φ).ofLp ψ =
        ((O_loc (_root_.deltaLp α)).ofLp β * N⁻¹ * φ.ofLp (flipCodeConfig (localDiffSlotChainDiag A α β) ψ)) *
          pauliPhase a (localSlotConfigToSubDiag A (restrictConfig A ψ) + localSlotConfigToSubDiag A β) := fun a => by
      change ((O_loc (_root_.deltaLp α)).ofLp β * N⁻¹ * pauliPhase a (localSlotConfigToSubDiag A β)) *
        (pauliPhase (extSlotChainDiag A a) (codeConfigBits ψ) * φ.ofLp (flipCodeConfig (localDiffSlotChainDiag A α β) ψ)) = _
      rw [pauliPhase_extSlotChainDiag A a ψ, pauliPhase_add_right]; ring
    simp_rw [h_term, ← Finset.mul_sum, sum_pauliPhase_eq_diag]
    have h_zero_iff : localSlotConfigToSubDiag A (restrictConfig A ψ) + localSlotConfigToSubDiag A β = 0 ↔ β = restrictConfig A ψ := by
      constructor
      · intro h_add0; refine localSlotConfigToSubDiag_injective A (funext fun qA => ?_); have hq := congr_fun h_add0 qA; (try dsimp at hq)
        calc localSlotConfigToSubDiag A β qA
          _ = (localSlotConfigToSubDiag A (restrictConfig A ψ) qA + localSlotConfigToSubDiag A (restrictConfig A ψ) qA) +
              localSlotConfigToSubDiag A β qA := by rw [zmod2_add_self, zero_add]
          _ = localSlotConfigToSubDiag A (restrictConfig A ψ) qA +
              (localSlotConfigToSubDiag A (restrictConfig A ψ) qA + localSlotConfigToSubDiag A β qA) := by abel
          _ = localSlotConfigToSubDiag A (restrictConfig A ψ) qA := by rw [hq, add_zero]
      · intro h_eq; subst h_eq; funext qA; exact zmod2_add_self _
    by_cases hβ : β = restrictConfig A ψ
    · rw [if_pos (h_zero_iff.mpr hβ), if_pos hβ]; subst hβ; rw [flipCodeConfig_localDiffSlotChainDiag A α (restrictConfig A ψ) ψ rfl]
      change ((O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) * N⁻¹ * φ.ofLp (spliceConfig A α ψ)) * N = _
      calc ((O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) * N⁻¹ * φ.ofLp (spliceConfig A α ψ)) * N
        _ = (N⁻¹ * N) * φ.ofLp (spliceConfig A α ψ) * (O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) := by ring
        _ = φ.ofLp (spliceConfig A α ψ) * (O_loc (_root_.deltaLp α)).ofLp (restrictConfig A ψ) := by rw [inv_mul_cancel₀ hN_ne, one_mul]
    · rw [if_neg (mt h_zero_iff.mp hβ), if_neg hβ, mul_zero]
  (try dsimp only); rw [Finset.sum_congr rfl (fun β _ => h_inner_sum β), Finset.sum_ite_eq', if_pos (Finset.mem_univ (restrictConfig A ψ))]
private lemma weylPauliZ_comm {L q_code : ℕ} (a₁ a₂ : BoxSlot3D L q_code → ZMod 2) : Commute (weylPauliZ a₁) (weylPauliZ a₂) := by
  rw [commute_iff_eq]; ext ψ σ; change pauliPhase a₁ (codeConfigBits σ) * (pauliPhase a₂ (codeConfigBits σ) * ψ.ofLp σ) =
    pauliPhase a₂ (codeConfigBits σ) * (pauliPhase a₁ (codeConfigBits σ) * ψ.ofLp σ); ring
private lemma weylPauliX_comm {L q_code : ℕ} (b₁ b₂ : BoxSlot3D L q_code → ZMod 2) : Commute (weylPauliX b₁) (weylPauliX b₂) := by
  rw [commute_iff_eq]; ext ψ σ; change ψ.ofLp (flipCodeConfig b₂ (flipCodeConfig b₁ σ)) = ψ.ofLp (flipCodeConfig b₁ (flipCodeConfig b₂ σ))
  refine congrArg ψ.ofLp (funext fun v => funext fun s => ?_); dsimp [flipCodeConfig]
  cases σ v s <;> cases zmod2ToBool (b₁ (v, s)) <;> cases zmod2ToBool (b₂ (v, s)) <;> rfl
private lemma half_one_sub_anticomm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P S : E →L[ℂ] E) (h_anti : S * P + P * S = 0) : ((2 : ℂ)⁻¹ • (1 - S)) * P + P * ((2 : ℂ)⁻¹ • (1 - S)) = P := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, sub_mul, one_mul, mul_sub, mul_one]
  have h_abel : P - S * P + (P - P * S) = (P + P) - (S * P + P * S) := by abel
  rw [h_abel, h_anti, sub_zero, ← two_smul ℂ P, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
private lemma weylPauli_commute_or_anticomm_weylCheckProjZ {L q_code : ℕ} (a b g : BoxSlot3D L q_code → ZMod 2) :
    let P := weylPauliZ a * weylPauliX b; Commute P (weylCheckProjZ g) ∨ weylCheckProjZ g * P + P * weylCheckProjZ g = P := by
  intro P; have h_mul : P * weylPauliZ g = pauliPhase g b • (weylPauliZ g * P) := by
    dsimp [P]; rw [mul_assoc, weylPauliX_mul_weylPauliZ g b, mul_smul_comm, ← mul_assoc, (weylPauliZ_comm a g).eq, mul_assoc]
  by_cases h_ph : (∑ q : BoxSlot3D L q_code, g q * b q) = 0
  · left; have h_p1 : pauliPhase g b = 1 := by simp [pauliPhase, h_ph]
    have h_comm : Commute P (weylPauliZ g) := by rw [commute_iff_eq, h_mul, h_p1, one_smul]
    exact ((Commute.one_right P).sub_right h_comm).smul_right (2 : ℂ)⁻¹
  · right; have h_pm1 : pauliPhase g b = -1 := by simp [pauliPhase, h_ph]
    have h_anti : weylPauliZ g * P + P * weylPauliZ g = 0 := by
      rw [h_mul, h_pm1]; ext ψ σ; change ((weylPauliZ g * P) ψ).ofLp σ + (-1 : ℂ) * ((weylPauliZ g * P) ψ).ofLp σ = 0; ring
    exact half_one_sub_anticomm_eq P (weylPauliZ g) h_anti
private lemma weylPauli_commute_or_anticomm_weylCheckProjX {L q_code : ℕ} (a b g : BoxSlot3D L q_code → ZMod 2) :
    let P := weylPauliZ a * weylPauliX b; Commute P (weylCheckProjX g) ∨ weylCheckProjX g * P + P * weylCheckProjX g = P := by
  intro P; have h_mul : weylPauliX g * P = pauliPhase a g • (P * weylPauliX g) := by
    dsimp [P]; rw [← mul_assoc, weylPauliX_mul_weylPauliZ a g, smul_mul_assoc, mul_assoc, (weylPauliX_comm g b).eq, ← mul_assoc]
  by_cases h_ph : (∑ q : BoxSlot3D L q_code, a q * g q) = 0
  · left; have h_p1 : pauliPhase a g = 1 := by simp [pauliPhase, h_ph]
    have h_comm : Commute P (weylPauliX g) := by rw [commute_iff_eq, h_mul, h_p1, one_smul]
    exact ((Commute.one_right P).sub_right h_comm).smul_right (2 : ℂ)⁻¹
  · right; have h_pm1 : pauliPhase a g = -1 := by simp [pauliPhase, h_ph]
    have h_anti : weylPauliX g * P + P * weylPauliX g = 0 := by
      rw [h_mul, h_pm1]; ext ψ σ; change (-1 : ℂ) * ((P * weylPauliX g) ψ).ofLp σ + ((P * weylPauliX g) ψ).ofLp σ = 0; ring
    exact half_one_sub_anticomm_eq P (weylPauliX g) h_anti
private lemma weylPauli_commute_or_anticomm_staticCSSCheckProj {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (a b : BoxSlot3D L q_code → ZMod 2) (idx : StaticCSSCheckIdx L q_code m_max) :
    let P := weylPauliZ a * weylPauliX b
    Commute P (staticCSSCheckProj D_field idx) ∨ staticCSSCheckProj D_field idx * P + P * staticCSSCheckProj D_field idx = P := by
  intro P; rcases idx with ⟨v, s⟩ | ⟨v, c⟩ | ⟨v, c⟩ <;> dsimp [staticCSSCheckProj] <;> split_ifs
  · exact weylPauli_commute_or_anticomm_weylCheckProjZ a b _
  · left; exact Commute.zero_right P
  · exact weylPauli_commute_or_anticomm_weylCheckProjX a b _
  · left; exact Commute.zero_right P
  · exact weylPauli_commute_or_anticomm_weylCheckProjZ a b _
  · left; exact Commute.zero_right P
private lemma syndromePinchOp_eq_zero_of_checkProj_anticomm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {idx : ι}
    (h_anti : sys.checkProj idx * P + P * sys.checkProj idx = P) : syndromePinchOp sys P = 0 := by
  have h_res := syndrome_resolution_indexed sys; unfold syndromePinchOp; refine Finset.sum_eq_zero fun σ _ => ?_
  have h_right := h_res.2.2.2.2.2.1 σ idx; have h_left := (h_res.2.2.2.2.2.2.1 σ idx).symm.eq.trans h_right
  have h_eq : sys.syndromeProjector σ * P * sys.syndromeProjector σ =
      (sys.syndromeProjector σ * sys.checkProj idx) * P * sys.syndromeProjector σ +
      sys.syndromeProjector σ * P * (sys.checkProj idx * sys.syndromeProjector σ) := by
    calc sys.syndromeProjector σ * P * sys.syndromeProjector σ
      _ = sys.syndromeProjector σ * (sys.checkProj idx * P + P * sys.checkProj idx) * sys.syndromeProjector σ := by rw [h_anti]
      _ = (sys.syndromeProjector σ * sys.checkProj idx) * P * sys.syndromeProjector σ +
            sys.syndromeProjector σ * P * (sys.checkProj idx * sys.syndromeProjector σ) := by noncomm_ring
  rw [h_left, h_right] at h_eq; cases hσ : σ idx <;> { simp [hσ] at h_eq; exact h_eq }

/-- **Norm Contraction & Spatial Support Preservation of `syndromePinchOp` for CSS Checks
    (`syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck`)**:
    For any CSS Hamiltonian `sys` (`h_sys_checks`) and any operator `M` supported on `A`,
    `syndromePinchOp sys M` has operator norm at most `‖M‖` and remains supported on `A`. -/
theorem syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧
      sys.weight idx = 1)
    (A : Finset (Box3D L))
    {M : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hM_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A M) :
    ‖syndromePinchOp sys M‖ ≤ ‖M‖ ∧
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (syndromePinchOp sys M) := by
  refine ⟨syndromePinchOp_norm_le sys M, ?_⟩
  rcases exists_local_weylPauli_expansion A hM_supp with ⟨ι_p, hFin, w, a_fam, b_fam, hP_supp, rfl⟩; letI : Fintype ι_p := hFin
  have h_lin : syndromePinchOp sys (∑ i : ι_p, w i • (weylPauliZ (a_fam i) * weylPauliX (b_fam i))) =
      ∑ i : ι_p, w i • syndromePinchOp sys (weylPauliZ (a_fam i) * weylPauliX (b_fam i)) := by
    unfold syndromePinchOp; simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, Finset.smul_sum]; exact Finset.sum_comm
  rw [h_lin]; refine _root_.isSupportedOn_finset_sum A Finset.univ _ fun i _ => _root_.isSupportedOn_smul A (w i) ?_
  let P_i := weylPauliZ (a_fam i) * weylPauliX (b_fam i)
  by_cases h_all_comm : ∀ idx : StaticCSSCheckIdx L q_code m_max, Commute P_i (sys.checkProj idx)
  · have h_syn_comm : ∀ σ, Commute P_i (sys.syndromeProjector σ) :=
      (indexed_check_commuting_perturbation_commutes_with_syndromeProjector sys P_i h_all_comm).1
    have h_fixed : syndromePinchOp sys P_i = P_i := perturbed_syndromeDiagOp_eq_self_of_commute sys h_syn_comm
    change IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (syndromePinchOp sys P_i); rw [h_fixed]; exact hP_supp i
  · push_neg at h_all_comm; rcases h_all_comm with ⟨idx, h_not_comm⟩
    have h_or := weylPauli_commute_or_anticomm_staticCSSCheckProj D_field (a_fam i) (b_fam i) idx
    rw [← (h_sys_checks idx).1] at h_or; rcases h_or with h_comm | h_anti
    · exact False.elim (h_not_comm h_comm)
    · rw [syndromePinchOp_eq_zero_of_checkProj_anticomm sys h_anti]; exact _root_.isSupportedOn_zero A

/-- **Geometric $\mathrm{RCA1}$ Diagonal Overlap Constant (`rcaDiagonalCoercivityConstant`)**:
    Bounds the maximum number of enlarged TQO-2 check-violation cones
    $B_A = \mathrm{enclosingBoxCube}(x_0, r, \mathrm{linearExpansionRadius}\;C_{\mathrm{rca}}\;r)$
    ($1 \le r \le R_{\mathrm{pert}}$) intersecting the support of a single check of radius $r_0$. -/
def rcaDiagonalCoercivityConstant (D R_pert r_0 w_0 : ℕ) (C_rca : ℝ) : ℝ :=
  (R_pert : ℝ) *
    (((2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 : ℕ) : ℝ) ^ D) *
    ((w_0 + 1 : ℕ) : ℝ)

/-- **Positivity of `rcaDiagonalCoercivityConstant` (`rcaDiagonalCoercivityConstant_pos`)**:
    Whenever $1 \le R_{\mathrm{pert}}$, $0 < \mathrm{rcaDiagonalCoercivityConstant}\;D\;R_{\mathrm{pert}}\;r_0\;w_0\;C_{\mathrm{rca}}$. -/
theorem rcaDiagonalCoercivityConstant_pos {D R_pert r_0 w_0 : ℕ} (hR : 1 ≤ R_pert) (C_rca : ℝ) :
    0 < rcaDiagonalCoercivityConstant D R_pert r_0 w_0 C_rca := by
  unfold rcaDiagonalCoercivityConstant
  have h1 : (0 : ℝ) < (R_pert : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hR)
  positivity

private def staticCSSCheckAnchor {L q_code m_max : ℕ} : StaticCSSCheckIdx L q_code m_max → Box3D L
  | Sum.inl (v, _) => v | Sum.inr (Sum.inl (v, _)) => v | Sum.inr (Sum.inr (v, _)) => v
private lemma staticCSSCheckAnchor_mem_support {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (c : StaticCSSCheckIdx L q_code m_max) :
    staticCSSCheckAnchor c ∈ staticCSSCheckSupport D_field c := by
  rcases c with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
  · exact Finset.mem_singleton_self v
  · exact _root_.mem_boxBall_self v r_0
  · exact _root_.mem_boxBall_self v r_0

/-- **Instantiation of `HasSyndromeDiagonalCoercivity` from TQO-1/2 & Finite Interaction Range
    (`hasSyndromeDiagonalCoercivity_of_tqo_and_finiteRange`,
    Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`))**:
    For any 3D CSS commuting-projector Hamiltonian `sys` specified by a valid local CSS descriptor
    field `D_field` of check radius `r_0` and geometric locality `(r_0, w_0)` satisfying
    `SatisfiesTQO1 sys L_star` and `SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca`, and any
    finite-range perturbation `V` (`HasFiniteRangeBound V R_pert J`) with $1 \le R_{\mathrm{pert}} \le L^*$
    and $0 \le J$, there exists a real vacuum energy shift $E_{\mathrm{vac}} \in \mathbb{R}$ such that
    `pauliDiagonalPart sys V R_pert` satisfies
    `HasSyndromeDiagonalCoercivity sys (pauliDiagonalPart sys V R_pert) E_vac (2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J)`.
    Consequently, whenever $2 \cdot \mathrm{rcaDiagonalCoercivityConstant}\;3\;R_{\mathrm{pert}}\;r_0\;w_0\;C_{\mathrm{rca}} \cdot J \le 1/4$,
    the shifted diagonal Hamiltonian $H_{\mathrm{diag}} = H_0 + V_{\mathrm{diag}} - E_{\mathrm{vac}}\mathbf{1}$
    satisfies the two-sided $\frac{3}{4}$–$\frac{5}{4}$ syndrome-energy sandwich on every syndrome sector $\Pi_\sigma$. -/
theorem hasSyndromeDiagonalCoercivity_of_tqo_and_finiteRange
    {L q_code r_0 m_max w_0 L_star R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧
      sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_rca J : ℝ}
    (hR_pos : 1 ≤ R_pert)
    (hR_le : R_pert ≤ L_star)
    (hC_rca : 0 ≤ C_rca)
    (hJ_nn : 0 ≤ J)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (hV_range : HasFiniteRangeBound V R_pert J) :
    ∃ E_vac : ℝ,
      HasSyndromeDiagonalCoercivity sys (pauliDiagonalPart sys V R_pert) E_vac
        (2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J) := by
  let M (r : ℕ) (A : Finset (Box3D L)) := syndromePinchOp sys (V.term r A)
  let B (r : ℕ) (A : Finset (Box3D L)) := enclosingBoxCube (anchorOfCube r A) r (linearExpansionRadius C_rca r)
  let C_A (r : ℕ) (A : Finset (Box3D L)) : Finset (StaticCSSCheckIdx L q_code m_max) :=
    Finset.univ.filter (fun c => sys.support c ⊆ B r A)
  have hM_props : ∀ r A, IsSelfAdjoint (M r A) ∧ (∀ c, Commute (M r A) (sys.checkProj c)) ∧ Commute (M r A) sys.P0 := fun r A => by
    have h := syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A); exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  have h_ex : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      ∃ e : ℝ, ‖M r A - ((e : ℝ) : ℂ) • 1‖ ≤ 2 * J ∧ HasLocalCheckViolationCover sys (M r A) (C_A r A) e := by
    intro r hr A hA; have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1; have hr_min : r ≤ min R_pert L := (Finset.mem_Icc.mp hr).2
    have hr_R : r ≤ R_pert := le_trans hr_min (Nat.min_le_left R_pert L); have hr_L : r ≤ L := le_trans hr_min (Nat.min_le_right R_pert L)
    have hr_Lstar : r ≤ L_star := le_trans hr_R hR_le; have hr_IccL : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hr1, hr_L⟩
    have hV_supp := V.is_supported r hr_IccL A hA; have hV_norm : ‖V.term r A‖ ≤ J := (hV_range r hr_IccL A hA).1 hr_R
    have hM_ns := syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck D_field sys h_sys_checks A hV_supp
    have hM_supp_cube : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) (boxCube (anchorOfCube r A) r) (M r A) := by
      rw [boxCube_anchorOfCube hA]; exact hM_ns.2
    rcases exists_indexed_sector_sandwich_of_tqo_bhm sys h_tqo2 hr1 hr_Lstar
        (anchorOfCube r A) (M r A) (hM_props r A).1 hM_supp_cube (hM_props r A).2.2 with ⟨e, _, he_norm, he_ann⟩
    rw [mul_one] at he_ann; refine ⟨e, le_trans he_norm (by linarith [hM_ns.1, hV_norm]), ⟨(hM_props r A).1, (hM_props r A).2.1, fun σ h_clean => ?_⟩⟩
    have hP_clean : sys.localGroundProj (B r A) * sys.syndromeProjector σ = sys.syndromeProjector σ :=
      (perturbed_P_loc_mul_syndromeProjector_of_clean_region sys fun c hc => h_clean c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)).1
    rw [← hP_clean, ← mul_assoc, he_ann, zero_mul]
  let e_loc (r : ℕ) (A : Finset (Box3D L)) : ℝ :=
    if h : r ∈ Finset.Icc 1 (min R_pert L) ∧ A ∈ boxCubes 3 L r then Classical.choose (h_ex r h.1 A h.2) else 0
  have he_spec : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      ‖M r A - ((e_loc r A : ℝ) : ℂ) • 1‖ ≤ 2 * J ∧ HasLocalCheckViolationCover sys (M r A) (C_A r A) (e_loc r A) := by
    intro r hr A hA; dsimp only [e_loc]; rw [dif_pos ⟨hr, hA⟩]; exact Classical.choose_spec (h_ex r hr A hA)
  use ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A
  refine ⟨isSelfAdjoint_finset_sum _ _ fun r _ => isSelfAdjoint_finset_sum _ _ fun A _ => (hM_props r A).1,
    fun c => Commute.sum_left _ _ _ fun r _ => Commute.sum_left _ _ _ fun A _ => (hM_props r A).2.1 c, fun σ ψ => ?_⟩
  let φ := sys.syndromeProjector σ ψ
  have h_inner_eq : RCLike.re (inner ℂ φ ((pauliDiagonalPart sys V R_pert -
        (((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A : ℝ) : ℂ) • 1)) φ)) =
      ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, RCLike.re (inner ℂ φ ((M r A - ((e_loc r A : ℝ) : ℂ) • 1) φ)) := by
    have h_op : pauliDiagonalPart sys V R_pert - (((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A : ℝ) : ℂ) • 1) =
        ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, (M r A - ((e_loc r A : ℝ) : ℂ) • 1) := by
      ext χ; unfold pauliDiagonalPart; dsimp only [M]; simp [Finset.sum_smul, Finset.sum_sub_distrib]
    rw [h_op]; simp only [ContinuousLinearMap.sum_apply, inner_sum, map_sum]
  rw [h_inner_eq]
  have h_tri : |∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, RCLike.re (inner ℂ φ ((M r A - ((e_loc r A : ℝ) : ℂ) • 1) φ))| ≤
      ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, (2 * J) * (∑ c ∈ C_A r A, if σ c then (1 : ℝ) else 0) * ‖φ‖ ^ 2 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r hr =>
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun A hA => ?_))
    have h_term := inner_syndrome_le_check_violation_sum_of_local_cover sys (he_spec r hr A hA).2 σ ψ
    have h_sum_nn : 0 ≤ ∑ c ∈ C_A r A, if σ c then (1 : ℝ) else 0 := Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num
    exact le_trans h_term (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he_spec r hr A hA).1 h_sum_nn) (sq_nonneg ‖φ‖))
  refine le_trans h_tri ?_
  let K_geom : ℝ := (((2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 : ℕ) : ℝ) ^ 3) * ((w_0 + 1 : ℕ) : ℝ)
  have h_scale : ∀ r ∈ Finset.Icc 1 (min R_pert L),
      (∑ A ∈ boxCubes 3 L r, (2 * J) * (∑ c ∈ C_A r A, if σ c then (1 : ℝ) else 0) * ‖φ‖ ^ 2) ≤
      (2 * J) * (K_geom * sys.syndromeEnergy σ) * ‖φ‖ ^ 2 := by
    intro r hr; have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
    have h_factor : (∑ A ∈ boxCubes 3 L r, (2 * J) * (∑ c ∈ C_A r A, if σ c then (1 : ℝ) else 0) * ‖φ‖ ^ 2) =
        (2 * J) * (∑ A ∈ boxCubes 3 L r, ∑ c ∈ C_A r A, if σ c then (1 : ℝ) else 0) * ‖φ‖ ^ 2 := by
      simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [h_factor]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by linarith)) (sq_nonneg ‖φ‖)
    have h_swap : (∑ A ∈ boxCubes 3 L r, ∑ c ∈ C_A r A, if σ c then (1 : ℝ) else 0) =
        ∑ c : StaticCSSCheckIdx L q_code m_max,
          (((boxCubes 3 L r).filter (fun A => sys.support c ⊆ B r A)).card : ℝ) * (if σ c then (1 : ℝ) else 0) := by
      simp only [C_A, Finset.sum_filter]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
      have h_ite : ∀ A : Finset (Box3D L), (if sys.support c ⊆ B r A then (if σ c then (1 : ℝ) else 0) else 0) =
          (if sys.support c ⊆ B r A then (1 : ℝ) else 0) * (if σ c then (1 : ℝ) else 0) := fun A => by split_ifs <;> ring
      simp_rw [h_ite, ← Finset.sum_mul, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h_energy : K_geom * sys.syndromeEnergy σ =
        ∑ c : StaticCSSCheckIdx L q_code m_max, K_geom * (if σ c then (1 : ℝ) else 0) := by
      rw [← Finset.mul_sum]; congr 1; unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
      rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun c _ => ?_; rw [(h_sys_checks c).2.2]
    rw [h_swap, h_energy]; refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> norm_num)
    have h_sub_filter : (boxCubes 3 L r).filter (fun A => sys.support c ⊆ B r A) ⊆
        (boxCubes 3 L r).filter (fun A => staticCSSCheckAnchor c ∈ B r A) := by
      intro A hA_f; rw [Finset.mem_filter] at hA_f ⊢; refine ⟨hA_f.1, hA_f.2 ?_⟩; rw [(h_sys_checks c).2.1]
      exact staticCSSCheckAnchor_mem_support D_field c
    have h_card1 : ((boxCubes 3 L r).filter (fun A => sys.support c ⊆ B r A)).card ≤ (2 * linearExpansionRadius C_rca r) ^ 3 :=
      le_trans (Finset.card_le_card h_sub_filter) (card_filter_mem_enclosingBoxCube_le_pow r (linearExpansionRadius C_rca r) (staticCSSCheckAnchor c))
    have h_rad_mono : linearExpansionRadius C_rca r ≤ linearExpansionRadius C_rca R_pert :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr_R) hC_rca)
    have h_base : 2 * linearExpansionRadius C_rca r ≤ 2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 := by omega
    have h_card2 : ((boxCubes 3 L r).filter (fun A => sys.support c ⊆ B r A)).card ≤
        (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1) :=
      le_trans h_card1 (le_trans (Nat.pow_le_pow_left h_base 3) (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)))
    dsimp only [K_geom]; exact_mod_cast h_card2
  have h_sum_r := Finset.sum_le_card_nsmul (Finset.Icc 1 (min R_pert L))
    (fun r => ∑ A ∈ boxCubes 3 L r, (2 * J) * (∑ c ∈ C_A r A, if σ c then (1 : ℝ) else 0) * ‖φ‖ ^ 2)
    ((2 * J) * (K_geom * sys.syndromeEnergy σ) * ‖φ‖ ^ 2) h_scale; rw [nsmul_eq_mul] at h_sum_r
  have h_card_Icc : ((Finset.Icc 1 (min R_pert L)).card : ℝ) ≤ (R_pert : ℝ) := by
    have h_nat : (Finset.Icc 1 (min R_pert L)).card ≤ R_pert := by rw [Nat.card_Icc]; have := Nat.min_le_left R_pert L; omega
    exact_mod_cast h_nat
  have hE_nn : 0 ≤ sys.syndromeEnergy σ := Finset.sum_nonneg fun i _ => le_trans zero_le_one (sys.weight_ge_one i)
  have h_tot := le_trans h_sum_r (mul_le_mul_of_nonneg_right h_card_Icc (by dsimp [K_geom]; positivity))
  have h_ring : (R_pert : ℝ) * ((2 * J) * (K_geom * sys.syndromeEnergy σ) * ‖φ‖ ^ 2) =
      (2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J) * sys.syndromeEnergy σ * ‖φ‖ ^ 2 := by
    unfold rcaDiagonalCoercivityConstant; dsimp [K_geom]; ring
  linarith [h_tot, h_ring]
end SpacetimeWorldlineKP
end
