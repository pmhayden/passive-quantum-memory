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

import Proofs.DressedThermalDuhamel.UnpinchedFailureTracePullback

/-!
# Courant–Fischer Eigenvalue Sandwiches and Safe-Complement Leakage Bounds

Decomposes unperturbed Boltzmann traces into ground and excited contributions and proves two-sided Courant–Fischer eigenvalue sandwiches from the BHM relative form bound. Establishes scalar-shift-cancelling partition lower bounds and excited-band leakage estimates on the safe-subspace complement.

## References

* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option maxRecDepth 200000
set_option linter.unusedVariables false

/-! ## 1. Unperturbed Ground/Excited Boltzmann Trace Decomposition & Partition Lower Bounds -/

/-- `sys.P0` is a star projection and has non-negative `hilbertTrace`. -/
theorem perturbed_isStarProjection_P0_and_hilbertTrace_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    IsStarProjection sys.P0 ∧ 0 ≤ hilbertTrace sys.P0 := by
  have hP0 : IsStarProjection sys.P0 := sys.isStarProjection_P0
  refine ⟨hP0, ?_⟩
  rw [hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 sys.P0]
  exact Finset.sum_nonneg fun ω _ => hP0.re_inner_nonneg _

/-- Unperturbed ground-sector Boltzmann trace identity: `Tr(B_0(β') P_0) = Tr(P_0)`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_unperturbed_P0_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {β' : ℝ} (hβ' : 0 ≤ β') :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
      (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * sys.P0) = hilbertTrace sys.P0 := by
  rw [hilbertTrace_gibbsBoltzmannOp_mul_eq,
      hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 sys.P0]
  refine Finset.sum_congr rfl fun ω _ => ?_
  let ψ := opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω
  let E := opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω
  have h_zero : (E : ℂ) • sys.P0 ψ = 0 := by
    calc (E : ℂ) • sys.P0 ψ
      _ = sys.P0 ((E : ℂ) • ψ) := (map_smul sys.P0 (E : ℂ) ψ).symm
      _ = sys.P0 (sys.H0 ψ) := by rw [← opEigenbasis_apply_H sys.H0 sys.isSelfAdjoint_H0 ω]
      _ = (sys.P0 * sys.H0) ψ := rfl
      _ = (sys.H0 * sys.P0) ψ := by rw [(sys.commute_H0_P0).symm.eq]
      _ = 0 := by rw [sys.ham0_mul_proj0_eq_zero, ContinuousLinearMap.zero_apply]
  rcases smul_eq_zero.mp h_zero with hE | hP0ψ
  · have hE0 : E = 0 := Complex.ofReal_injective hE
    change Real.exp (-β' * E) * RCLike.re (inner ℂ ψ (sys.P0 ψ)) = RCLike.re (inner ℂ ψ (sys.P0 ψ))
    rw [hE0, mul_zero, Real.exp_zero, one_mul]
  · change Real.exp (-β' * E) * RCLike.re (inner ℂ ψ (sys.P0 ψ)) = RCLike.re (inner ℂ ψ (sys.P0 ψ))
    rw [hP0ψ, inner_zero_right, map_zero, mul_zero]

/-- Additivity of `hilbertTrace (gibbsBoltzmannOp ψ E β * (A + B))`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_mul_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_eig : ManyBodyConfig Site → ManyBodyHilbertSpace Site)
    (E_eig : ManyBodyConfig Site → ℝ) (β : ℝ)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * (A + B)) =
      hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * A) +
        hilbertTrace (gibbsBoltzmannOp ψ_eig E_eig β * B) := by
  rw [hilbertTrace_gibbsBoltzmannOp_mul_eq, hilbertTrace_gibbsBoltzmannOp_mul_eq,
    hilbertTrace_gibbsBoltzmannOp_mul_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.add_apply, inner_add_right, map_add, mul_add]

/-- Unperturbed partition function decomposition `Z_0(β') = Tr(P_0) + Tr(B_0(β')(1 - P_0))`. -/
theorem perturbed_unperturbed_gibbsPartitionZ_eq_hilbertTrace_P0_add_excited {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {β' : ℝ} (hβ' : 0 ≤ β') :
    gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' =
      hilbertTrace sys.P0 +
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
          (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) := by
  rw [← perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ sys.H0 sys.isSelfAdjoint_H0 β']
  have h_one : (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) =
      sys.P0 + (1 - sys.P0) := by abel
  conv_lhs => rw [h_one]
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_mul_add,
      perturbed_hilbertTrace_gibbsBoltzmannOp_unperturbed_P0_eq sys hβ']

/-- Exact decomposition of `Tr(B_0(β')(1 - Pi_safe))` into `p_0(β') * Tr(P_0) + p_0(β') * Tr(B_0(β')(1 - P_0))`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_unperturbed_failure_eq_gibbsFailureProb_mul_P0_add_excited
    {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {β' : ℝ} (hβ' : 0 ≤ β') :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
      (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - Pi_safe)) =
    gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β' (1 - Pi_safe) * hilbertTrace sys.P0 +
      gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β' (1 - Pi_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
          (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) := by
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_gibbsFailureProb_mul_partitionZ
    sys.H0 sys.isSelfAdjoint_H0 β' (1 - Pi_safe),
    perturbed_unperturbed_gibbsPartitionZ_eq_hilbertTrace_P0_add_excited sys hβ', mul_add]

/-- Two-sided Courant–Fischer eigenvalue sandwich from unitary relative form bound. -/
theorem perturbed_opEigenvalues_sandwich_of_unitary_form {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {c_shift γ ε : ℝ} (hγ_nn : 0 ≤ γ) (hγ_le : γ ≤ 1)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
        ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
        γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + ε * ‖ψ‖ ^ 2)
    (ω : ManyBodyConfig Site) :
    |opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert ω -
      opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω - c_shift| ≤
      γ * opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω + ε ∧
    c_shift + (1 - γ) * opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω - ε ≤
      opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert ω ∧
    opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert ω ≤
      c_shift + (1 + γ) * opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω + ε := by
  have h_eq : hH_pert = isSelfAdjoint_indexedH0_add_V_tot_bhm sys V := Subsingleton.elim _ _
  subst h_eq
  let U_iso := unitaryToLinearIsometryEquiv U_dress
  have h_iso_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ (U_iso ϕ) ((sys.H0 + V.totalPerturbation) (U_iso ϕ))) -
        RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) - c_shift * ‖ϕ‖ ^ 2| ≤
        γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) + ε * ‖ϕ‖ ^ 2 := by
    intro ϕ
    have h_conj : inner ℂ (U_iso ϕ) ((sys.H0 + V.totalPerturbation) (U_iso ϕ)) =
        inner ℂ ϕ ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) ϕ) :=
      inner_unitary_conj U_dress (sys.H0 + V.totalPerturbation) ϕ
    have h_diff :
        RCLike.re (inner ℂ (U_iso ϕ) ((sys.H0 + V.totalPerturbation) (U_iso ϕ))) -
          RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) - c_shift * ‖ϕ‖ ^ 2 =
        RCLike.re (inner ℂ ϕ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (c_shift : ℂ) • 1) ϕ)) := by
      rw [h_conj, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
        inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one]
    rw [h_diff]
    exact h_form ϕ
  have h_abs := sortedEigenvalues_sub_le_of_isometry_form_bound sys V U_iso
    hγ_nn hγ_le h_iso_form (configFinEquiv Site ω)
  change |opEigenvalues (sys.H0 + V.totalPerturbation) (isSelfAdjoint_indexedH0_add_V_tot_bhm sys V) ω -
    opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω - c_shift| ≤
    γ * opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω + ε at h_abs
  rcases abs_le.mp h_abs with ⟨h_low, h_high⟩
  exact ⟨h_abs, by linarith, by linarith⟩

/-- Partition function lower bound from an eigenvalue upper bound. -/
theorem perturbed_gibbsPartitionZ_lower_bound_of_eigenvalue_upper_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (E_0 E_pert : ManyBodyConfig Site → ℝ) {c_shift γ δ_split β : ℝ} (hβ : 0 ≤ β)
    (h_ev_up : ∀ ω : ManyBodyConfig Site,
      E_pert ω ≤ c_shift + (1 + γ) * E_0 ω + (1 / 2 : ℝ) * δ_split) :
    Real.exp (-β * c_shift - (1 / 2 : ℝ) * β * δ_split) *
      gibbsPartitionZ E_0 ((1 + γ) * β) ≤ gibbsPartitionZ E_pert β := by
  unfold gibbsPartitionZ
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [h_ev_up ω])

/-- Unconditional rescaled unperturbed partition lower bound from `h_form` alone. -/
theorem perturbed_gibbsPartitionZ_unperturbed_rescaled_le_of_bhm_form_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {c_shift δ_split β : ℝ} (hβ : 0 ≤ β)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
        ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    Real.exp (-β * c_shift - (1 / 2 : ℝ) * β * δ_split) *
      gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((5 / 4 : ℝ) * β) ≤
    gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β := by
  have h_five_quarters : (1 + (1 / 4 : ℝ)) = (5 / 4 : ℝ) := by ring
  rw [← h_five_quarters]
  refine perturbed_gibbsPartitionZ_lower_bound_of_eigenvalue_upper_bound
    (opEigenvalues sys.H0 sys.isSelfAdjoint_H0)
    (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) (γ := 1 / 4) hβ fun ω => ?_
  have h_up := (perturbed_opEigenvalues_sandwich_of_unitary_form sys V hH_pert U_dress
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) h_form ω).2.2
  linarith

/-- For any `0 ≤ β'`, `0 ≤ Tr(B_0(β')(1 - sys.P0))` and `hilbertTrace sys.P0 ≤ Z_0(β')`. -/
theorem perturbed_hilbertTrace_unperturbed_excited_nonneg_and_P0_le_partitionZ {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {β' : ℝ} (hβ' : 0 ≤ β') :
    0 ≤ hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
          (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) ∧
    hilbertTrace sys.P0 ≤ gibbsPartitionZ (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' := by
  have hP0 : IsStarProjection sys.P0 := sys.isStarProjection_P0
  have h_exc_nn : 0 ≤ hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
      (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) (hP0.one_sub.re_inner_nonneg _)
  have h_eq := perturbed_unperturbed_gibbsPartitionZ_eq_hilbertTrace_P0_add_excited sys hβ'
  exact ⟨h_exc_nn, by linarith⟩

/-- **Unconditional `c_shift`-Cancelling Partition Lower Bound from `h_form` Alone
(`perturbed_gibbsPartitionZ_lower_bound_of_bhm_form_alone`)**. -/
theorem perturbed_gibbsPartitionZ_lower_bound_of_bhm_form_alone {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {c_shift δ_split β : ℝ} (hβ : 0 ≤ β)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
        ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    Real.exp (-β * c_shift - (1 / 2 : ℝ) * β * δ_split) * hilbertTrace sys.P0 ≤
      gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β ∧
    Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) * hilbertTrace sys.P0 ≤
      Real.exp (β * δ_split) * gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β := by
  have hβ_54 : 0 ≤ (5 / 4 : ℝ) * β := by linarith
  have h_P0_le := (perturbed_hilbertTrace_unperturbed_excited_nonneg_and_P0_le_partitionZ sys hβ_54).2
  have h_Z_le :=
    perturbed_gibbsPartitionZ_unperturbed_rescaled_le_of_bhm_form_bound sys V hH_pert U_dress hβ h_form
  have h_first : Real.exp (-β * c_shift - (1 / 2 : ℝ) * β * δ_split) * hilbertTrace sys.P0 ≤
      gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β :=
    le_trans (mul_le_mul_of_nonneg_left h_P0_le (le_of_lt (Real.exp_pos _))) h_Z_le
  refine ⟨h_first, ?_⟩
  have h_split : Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) * hilbertTrace sys.P0 =
      Real.exp (β * δ_split) *
        (Real.exp (-β * c_shift - (1 / 2 : ℝ) * β * δ_split) * hilbertTrace sys.P0) := by
    rw [← mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring
  rw [h_split]; exact mul_le_mul_of_nonneg_left h_first (le_of_lt (Real.exp_pos _))

/-- Every non-zero star projection `P` on `ManyBodyHilbertSpace Site` satisfies `1 ≤ hilbertTrace P`. -/
theorem perturbed_one_le_hilbertTrace_of_isStarProjection_ne_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) (hP_ne : P ≠ 0) :
    1 ≤ hilbertTrace P := by
  let hP_sa := hP.isSelfAdjoint; let φ := opEigenbasis P hP_sa; let μ := opEigenvalues P hP_sa
  have h_re_φ : ∀ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (φ ω) (φ ω)) = 1 :=
    fun ω => (perturbed_norm_opEigenbasis_le_one P hP_sa ω).1
  have h_re_P : ∀ ω : ManyBodyConfig Site, RCLike.re (inner ℂ (φ ω) (P (φ ω))) = μ ω := fun ω => by
    change RCLike.re (inner ℂ (φ ω) (P (opEigenbasis P hP_sa ω))) = μ ω
    rw [opEigenbasis_apply_H P hP_sa ω, inner_smul_right, re_ofReal_mul, h_re_φ ω, mul_one]
  have h_tr : hilbertTrace P = ∑ ω : ManyBodyConfig Site, μ ω := by
    rw [hilbertTrace_eq_sum_opEigenbasis P hP_sa P]; exact Finset.sum_congr rfl fun ω _ => h_re_P ω
  have h_μ_nn : ∀ ω : ManyBodyConfig Site, 0 ≤ μ ω := fun ω => by
    rw [← h_re_P ω]; exact hP.re_inner_nonneg (φ ω)
  have h_μ_01 : ∀ ω : ManyBodyConfig Site, μ ω = 0 ∨ μ ω = 1 := fun ω => by
    have h_idem : P (P (φ ω)) = P (φ ω) := by
      change (P * P) (φ ω) = P (φ ω); rw [hP.isIdempotentElem.eq]
    have h_eig : P (φ ω) = (μ ω : ℂ) • φ ω := opEigenbasis_apply_H P hP_sa ω
    have h_eq2 : RCLike.re (inner ℂ (φ ω) (P (φ ω))) = μ ω * μ ω := by
      calc RCLike.re (inner ℂ (φ ω) (P (φ ω)))
        _ = RCLike.re (inner ℂ (φ ω) (P (P (φ ω)))) := by rw [h_idem]
        _ = RCLike.re (inner ℂ (φ ω) ((μ ω : ℂ) • ((μ ω : ℂ) • φ ω))) := by rw [h_eig, map_smul, h_eig]
        _ = μ ω * μ ω := by
            rw [inner_smul_right, inner_smul_right, re_ofReal_mul, re_ofReal_mul, h_re_φ ω, mul_one]
    have h_mul : μ ω * (μ ω - 1) = 0 := by linarith [h_re_P ω, h_eq2]
    rcases mul_eq_zero.mp h_mul with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have h_exists : ∃ ω₀ : ManyBodyConfig Site, μ ω₀ ≠ 0 := by
    by_contra h_all; push_neg at h_all; apply hP_ne
    apply ContinuousLinearMap.ext; intro v
    have h_id := onb_sum_ketBra_eq_one φ (opEigenbasis_orthonormal P hP_sa) (opEigenbasis_parseval P hP_sa)
    have hv : v = ∑ ω : ManyBodyConfig Site, rankOneKetBra (φ ω) v := by
      calc v = (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) v := rfl
        _ = (∑ ω : ManyBodyConfig Site, rankOneKetBra (φ ω)) v := by rw [h_id]
        _ = ∑ ω : ManyBodyConfig Site, rankOneKetBra (φ ω) v := ContinuousLinearMap.sum_apply _ _ _
    rw [hv, map_sum, ContinuousLinearMap.zero_apply]
    refine Finset.sum_eq_zero fun ω _ => ?_
    have h_z : opEigenvalues P hP_sa ω = 0 := h_all ω
    rw [rankOneKetBra_apply, map_smul, opEigenbasis_apply_H P hP_sa ω, h_z,
      Complex.ofReal_zero, zero_smul, smul_zero]
  rcases h_exists with ⟨ω₀, hω₀⟩
  have hω₀_eq : μ ω₀ = 1 := (h_μ_01 ω₀).resolve_left hω₀
  rw [h_tr, ← hω₀_eq]; exact Finset.single_le_sum (fun ω _ => h_μ_nn ω) (Finset.mem_univ ω₀)

/-- For any `0 ≤ β'`, `Tr(B_0(β')(1 - sys.P0)) ≤ Fintype.card (ManyBodyConfig Site)`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_unperturbed_excited_le_card {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {β' : ℝ} (hβ' : 0 ≤ β') :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
      (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) ≤
      (Fintype.card (ManyBodyConfig Site) : ℝ) := by
  have hP0 : IsStarProjection sys.P0 := sys.isStarProjection_P0
  have h_H0_nn : ∀ ψ : ManyBodyHilbertSpace Site, 0 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := fun ψ => by
    dsimp [IndexedCommutingProjectorHamiltonian.H0]
    rw [ContinuousLinearMap.sum_apply, inner_sum, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => by
      rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
      exact mul_nonneg (le_trans zero_le_one (sys.weight_ge_one i)) ((sys.is_projector i).re_inner_nonneg ψ)
  rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
  calc ∑ ω : ManyBodyConfig Site,
        Real.exp (-β' * opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω) *
          RCLike.re (inner ℂ (opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω)
            ((1 - sys.P0) (opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω)))
    _ ≤ ∑ _ω : ManyBodyConfig Site, (1 : ℝ) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        let ψ := opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω
        have hE_nn : 0 ≤ opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω := by
          have h_eq : RCLike.re (inner ℂ ψ (sys.H0 ψ)) = opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω := by
            change RCLike.re (inner ℂ ψ (sys.H0 (opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω))) = _
            rw [opEigenbasis_apply_H sys.H0 sys.isSelfAdjoint_H0 ω, inner_smul_right, re_ofReal_mul,
              (perturbed_norm_opEigenbasis_le_one sys.H0 sys.isSelfAdjoint_H0 ω).1, mul_one]
          rw [← h_eq]; exact h_H0_nn ψ
        have h_exp_le1 : Real.exp (-β' * opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω) ≤ 1 := by
          rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
        have h_proj_nn := hP0.one_sub.re_inner_nonneg ψ
        have h_proj_le1 : RCLike.re (inner ℂ ψ ((1 - sys.P0) ψ)) ≤ 1 := by
          rw [isStarProjection_re_inner_eq_norm_sq_bhm hP0.one_sub]
          exact le_trans (isStarProjection_norm_sq_apply_le_bhm hP0.one_sub ψ)
            (by nlinarith [(perturbed_norm_opEigenbasis_le_one sys.H0 sys.isSelfAdjoint_H0 ω).2, norm_nonneg ψ])
        nlinarith [Real.exp_pos (-β' * opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω)]
    _ = (Fintype.card (ManyBodyConfig Site) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Turnkey `h_exc_leak` discharger from BHM form bound and excited trace ratio. -/
theorem perturbed_excited_band_boltzmann_leakage_le_of_bhm_form_bound {D L : ℕ}
    {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {δ_split β R_exc ε_exc : ℝ} (hβ : 0 ≤ β) (hR_nn : 0 ≤ R_exc)
    (h_unpert_exc :
      gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 ((3 / 4 : ℝ) * β) (1 - Pi_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
          (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((3 / 4 : ℝ) * β) * (1 - sys.P0)) ≤
      R_exc * hilbertTrace sys.P0)
    (h_cal : Real.exp (β * δ_split) * R_exc ≤ ε_exc) :
    ∀ (c_shift : ℝ) (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation)),
      (∀ ψ : ManyBodyHilbertSpace Site,
        |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
          (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) →
      Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) *
        (gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 ((3 / 4 : ℝ) * β) (1 - Pi_safe) *
          hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((3 / 4 : ℝ) * β) * (1 - sys.P0))) ≤
      ε_exc * gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β := by
  intro c_shift hH_pert h_form
  have h_Z_low := (perturbed_gibbsPartitionZ_lower_bound_of_bhm_form_alone sys V hH_pert U_dress hβ h_form).2
  have hZ_nn := le_of_lt (gibbsPartitionZ_pos (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β)
  have h1 := mul_le_mul_of_nonneg_left h_unpert_exc
    (le_of_lt (Real.exp_pos (-β * c_shift + (1 / 2 : ℝ) * β * δ_split)))
  have h2 := mul_le_mul_of_nonneg_left h_Z_low hR_nn
  have h3 := mul_le_mul_of_nonneg_right h_cal hZ_nn
  calc Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) *
        (gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 ((3 / 4 : ℝ) * β) (1 - Pi_safe) *
          hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((3 / 4 : ℝ) * β) * (1 - sys.P0)))
    _ ≤ Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) * (R_exc * hilbertTrace sys.P0) := h1
    _ = R_exc * (Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) * hilbertTrace sys.P0) := by ring
    _ ≤ R_exc * (Real.exp (β * δ_split) *
          gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β) := h2
    _ = (Real.exp (β * δ_split) * R_exc) *
          gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β := by ring
    _ ≤ ε_exc * gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β := h3

/-- Turnkey `h_exc_leak` discharger from `sys.P0 ≠ 0` and unperturbed `gibbsFailureProb`. -/
theorem perturbed_excited_band_boltzmann_leakage_le_of_bhm_form_and_P0_ne_zero {D L : ℕ}
    {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe) (hP0_ne : sys.P0 ≠ 0)
    {δ_split β B_peierls ε_exc : ℝ} (hβ : 0 ≤ β)
    (hp0 : gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 ((3 / 4 : ℝ) * β) (1 - Pi_safe) ≤ B_peierls)
    (h_cal : Real.exp (β * δ_split) * (B_peierls * (Fintype.card (ManyBodyConfig Site) : ℝ)) ≤ ε_exc) :
    ∀ (c_shift : ℝ) (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation)),
      (∀ ψ : ManyBodyHilbertSpace Site,
        |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
          (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) →
      Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) *
        (gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 ((3 / 4 : ℝ) * β) (1 - Pi_safe) *
          hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((3 / 4 : ℝ) * β) * (1 - sys.P0))) ≤
      ε_exc * gibbsPartitionZ (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β := by
  have hβ_34 : 0 ≤ (3 / 4 : ℝ) * β := by linarith
  have hP0_proj : IsStarProjection sys.P0 := sys.isStarProjection_P0
  have hP0_ge1 : 1 ≤ hilbertTrace sys.P0 :=
    perturbed_one_le_hilbertTrace_of_isStarProjection_ne_zero hP0_proj hP0_ne
  have h_exc_card := perturbed_hilbertTrace_gibbsBoltzmannOp_unperturbed_excited_le_card sys hβ_34
  have h_exc_nn := (perturbed_hilbertTrace_unperturbed_excited_nonneg_and_P0_le_partitionZ sys hβ_34).1
  have hp0_nn : 0 ≤ gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 ((3 / 4 : ℝ) * β) (1 - Pi_safe) :=
    hilbertTrace_gibbsDensityOp_mul_proj_nonneg
      (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
      (opEigenvalues sys.H0 sys.isSelfAdjoint_H0)
      ((3 / 4 : ℝ) * β)
      (opEigenbasis_orthonormal sys.H0 sys.isSelfAdjoint_H0)
      (hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
      hPi.one_sub
  have hB_nn : 0 ≤ B_peierls := le_trans hp0_nn hp0
  have h_card_nn : 0 ≤ (Fintype.card (ManyBodyConfig Site) : ℝ) := Nat.cast_nonneg _
  refine perturbed_excited_band_boltzmann_leakage_le_of_bhm_form_bound sys V U_dress Pi_safe hβ
    (mul_nonneg hB_nn h_card_nn) ?_ h_cal
  calc gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 ((3 / 4 : ℝ) * β) (1 - Pi_safe) *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
          (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((3 / 4 : ℝ) * β) * (1 - sys.P0))
    _ ≤ B_peierls * (Fintype.card (ManyBodyConfig Site) : ℝ) :=
        mul_le_mul hp0 h_exc_card h_exc_nn hB_nn
    _ = (B_peierls * (Fintype.card (ManyBodyConfig Site) : ℝ)) * 1 := (mul_one _).symm
    _ ≤ (B_peierls * (Fintype.card (ManyBodyConfig Site) : ℝ)) * hilbertTrace sys.P0 :=
        mul_le_mul_of_nonneg_left hP0_ge1 (mul_nonneg hB_nn h_card_nn)

end
