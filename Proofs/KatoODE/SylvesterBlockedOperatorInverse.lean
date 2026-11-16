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

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Blocked Off-Diagonal Sylvester Operator Inverse on Gapped Subspaces

Establishes eigenvalue separation across the perturbed spectral gap, local Lipschitz continuity of `perturbedGroundSpectralProj`, and the bounded off-diagonal Sylvester inverse `sylvesterOffDiagInverse` solving $[H(s_0), Y] = X_{\mathrm{off}}$ with operator norm inversely proportional to the spectral gap.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Kato (1950), Journal of the Physical Society of Japan 5, 435–439
-/

/-! ## 1. Pure Ring Identities & Rank-One Eigenprojector Algebra -/

lemma ring_mul_sub_sandwich {R : Type*} [Ring R] (A B C D : R) :
    A * (B - C) * D = A * (B * D) - (A * C) * D := by noncomm_ring

lemma ring_commutator_sandwich_left {R : Type*} [Ring R] (A H Z B : R) :
    A * (H * Z - Z * H) * B = (A * H) * Z * B - A * Z * (H * B) := by noncomm_ring

lemma ring_commutator_diff_sandwich {R : Type*} [Ring R] (H A Y B : R) :
    H * (A * Y * B - B * Y * A) - (A * Y * B - B * Y * A) * H =
      ((H * A) * Y * B - A * Y * (B * H)) + (B * Y * (A * H) - (H * B) * Y * A) := by
  noncomm_ring

lemma ring_offDiag_diff_left {R : Type*} [Ring R] (P A Y B : R) :
    P * (B * Y * A - A * Y * B) * (1 - P) =
      (P * B) * Y * (A * (1 - P)) - (P * A) * Y * (B * (1 - P)) := by noncomm_ring

lemma ring_offDiag_diff_right {R : Type*} [Ring R] (P A Y B : R) :
    (1 - P) * (B * Y * A - A * Y * B) * P =
      ((1 - P) * B) * Y * (A * P) - ((1 - P) * A) * Y * (B * P) := by noncomm_ring

lemma ring_twoBlockDiag_idempotent_sq {R : Type*} [Ring R] {P P₀ : R}
    (hP : P * P = P) (hP₀ : P₀ * P₀ = P₀) :
    P₀ * (P - P₀) * P₀ + (1 - P₀) * (P - P₀) * (1 - P₀) =
      (1 - P₀) * ((P - P₀) * (P - P₀)) * (1 - P₀) - P₀ * ((P - P₀) * (P - P₀)) * P₀ := by
  have h_sq : (P - P₀) * (P - P₀) = P - P * P₀ - P₀ * P + P₀ := by
    rw [mul_sub, sub_mul, sub_mul, hP, hP₀]; abel
  have hP0_R : ∀ X : R, X * P₀ * P₀ = X * P₀ := fun X => by rw [mul_assoc, hP₀]
  rw [h_sq]
  simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, ← mul_assoc, hP₀, hP0_R]
  abel

lemma clm_smul_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℂ) (X Y : E →L[ℂ] E) : a • (X + Y) = a • X + a • Y := smul_add a X Y

lemma clm_star_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X Y : E →L[ℂ] E) : star (X - Y) = star X - star Y := star_sub X Y

lemma clm_star_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X Y : E →L[ℂ] E) : star (X * Y) = star Y * star X := star_mul X Y

/-- Complement `1 - P` of a star projection is a star projection. -/
lemma isStarProjection_one_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    IsStarProjection (1 - P) := by
  refine ⟨?_, ?_⟩
  · simp only [IsIdempotentElem, mul_sub, sub_mul, mul_one, one_mul,
      hP.isIdempotentElem.eq, sub_self, sub_zero]
  · rw [IsSelfAdjoint, star_sub, star_one, hP.isSelfAdjoint.star_eq]

/-- Each `rankOneEigenvectorProj H hH i` is a star projection. -/
theorem isStarProjection_rankOneEigenvectorProj {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    IsStarProjection (rankOneEigenvectorProj H hH i) := by
  have h := isStarProjection_sum_rankOneEigenvectorProj H hH {i}
  rwa [Finset.sum_singleton] at h

/-- Each `rankOneEigenvectorProj H hH i` is self-adjoint. -/
theorem isSelfAdjoint_rankOneEigenvectorProj {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    IsSelfAdjoint (rankOneEigenvectorProj H hH i) :=
  (isStarProjection_rankOneEigenvectorProj H hH i).isSelfAdjoint

/-- Operator norm bound `‖rankOneEigenvectorProj H hH i‖ ≤ 1`. -/
theorem norm_rankOneEigenvectorProj_le_one {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    ‖rankOneEigenvectorProj H hH i‖ ≤ 1 :=
  isStarProjection_norm_le_one (isStarProjection_rankOneEigenvectorProj H hH i)

/-- Left multiplication of `rankOneEigenvectorProj H hH i` by a spectral sub-band sum. -/
lemma sum_rankOneEigenvectorProj_mul_single {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (S : Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))))
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    (∑ k ∈ S, rankOneEigenvectorProj H hH k) * rankOneEigenvectorProj H hH i =
      if i ∈ S then rankOneEigenvectorProj H hH i else 0 := by
  apply ext_of_orthonormalBasis_eq (sortedEigenbasis H hH); intro m
  rw [ContinuousLinearMap.mul_apply, rankOneEigenvectorProj_apply_eigenbasis]
  by_cases him : i = m
  · subst him; rw [if_pos rfl, sum_rankOneEigenvectorProj_apply_eigenbasis]
    split_ifs with hiS
    · rw [rankOneEigenvectorProj_apply_eigenbasis, if_pos rfl]
    · rw [ContinuousLinearMap.zero_apply]
  · rw [if_neg him, map_zero]
    split_ifs with hiS
    · rw [rankOneEigenvectorProj_apply_eigenbasis, if_neg him]
    · rw [ContinuousLinearMap.zero_apply]

/-- Right multiplication of `rankOneEigenvectorProj H hH i` by a spectral sub-band sum. -/
lemma single_mul_sum_rankOneEigenvectorProj {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (S : Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))))
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    rankOneEigenvectorProj H hH i * (∑ k ∈ S, rankOneEigenvectorProj H hH k) =
      if i ∈ S then rankOneEigenvectorProj H hH i else 0 := by
  apply ext_of_orthonormalBasis_eq (sortedEigenbasis H hH); intro m
  rw [ContinuousLinearMap.mul_apply, sum_rankOneEigenvectorProj_apply_eigenbasis]
  by_cases hmS : m ∈ S
  · rw [if_pos hmS, rankOneEigenvectorProj_apply_eigenbasis]
    by_cases him : i = m
    · subst him; rw [if_pos hmS, rankOneEigenvectorProj_apply_eigenbasis, if_pos rfl]
    · rw [if_neg him]
      split_ifs with hiS
      · rw [rankOneEigenvectorProj_apply_eigenbasis, if_neg him]
      · rw [ContinuousLinearMap.zero_apply]
  · rw [if_neg hmS, map_zero]
    split_ifs with hiS
    · have him : i ≠ m := fun h => hmS (h ▸ hiS)
      rw [rankOneEigenvectorProj_apply_eigenbasis, if_neg him]
    · rw [ContinuousLinearMap.zero_apply]

/-- Disjointness of `groundBandFinset sys` and `excitedBandFinset sys`. -/
lemma not_mem_groundBandFinset_of_mem_excitedBandFinset {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))} (hj : j ∈ excitedBandFinset sys) :
    j ∉ groundBandFinset sys := by
  simp only [groundBandFinset, excitedBandFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  omega

/-- Absorption and annihilation identities between `perturbedGroundSpectralProj sys V s` and
    `rankOneEigenvectorProj` for ground and excited indices. -/
lemma perturbedGroundSpectralProj_rankOne_mul_rules {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (s : ℝ) {i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))}
    (hi : i ∈ groundBandFinset sys) (hj : j ∈ excitedBandFinset sys) :
    let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
    let P := perturbedGroundSpectralProj sys V s
    let R_i := rankOneEigenvectorProj H_s hHs i
    let R_j := rankOneEigenvectorProj H_s hHs j
    P * R_i = R_i ∧ R_i * P = R_i ∧ P * R_j = 0 ∧ R_j * P = 0 ∧
    (1 - P) * R_i = 0 ∧ R_i * (1 - P) = 0 ∧ (1 - P) * R_j = R_j ∧ R_j * (1 - P) = R_j := by
  intro H_s hHs P R_i R_j
  have hj_not := not_mem_groundBandFinset_of_mem_excitedBandFinset sys hj
  have hPRi : P * R_i = R_i := by
    dsimp [P, R_i, perturbedGroundSpectralProj]; rw [sum_rankOneEigenvectorProj_mul_single, if_pos hi]
  have hRiP : R_i * P = R_i := by
    dsimp [P, R_i, perturbedGroundSpectralProj]; rw [single_mul_sum_rankOneEigenvectorProj, if_pos hi]
  have hPRj : P * R_j = 0 := by
    dsimp [P, R_j, perturbedGroundSpectralProj]; rw [sum_rankOneEigenvectorProj_mul_single, if_neg hj_not]
  have hRjP : R_j * P = 0 := by
    dsimp [P, R_j, perturbedGroundSpectralProj]; rw [single_mul_sum_rankOneEigenvectorProj, if_neg hj_not]
  refine ⟨hPRi, hRiP, hPRj, hRjP, ?_, ?_, ?_, ?_⟩
  · rw [sub_mul, one_mul, hPRi, sub_self]
  · rw [mul_sub, mul_one, hRiP, sub_self]
  · rw [sub_mul, one_mul, hPRj, sub_zero]
  · rw [mul_sub, mul_one, hRjP, sub_zero]

/-- Difference of interpolated Hamiltonians $H(s_2) - H(s_1) = (s_2 - s_1) V_{\mathrm{tot}}$. -/
lemma hamiltonian_scaleQuasiLocalPerturbation_sub {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₁ s₂ : ℝ) :
    (sys.H0 + (scaleQuasiLocalPerturbation s₂ V).totalPerturbation) -
      (sys.H0 + (scaleQuasiLocalPerturbation s₁ V).totalPerturbation) = ((s₂ - s₁ : ℝ) : ℂ) • V.totalPerturbation := by
  rw [scaleQuasiLocalPerturbation_V_tot, scaleQuasiLocalPerturbation_V_tot,
    add_sub_add_left_eq_sub, Complex.ofReal_sub, clm_sub_smul]

/-- Cross-basis Sylvester equation for `rankOneEigenvectorProj` at two parameter values `s₁, s₂`. -/
theorem cross_rankOneEigenvectorProj_sylvester_eq {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₁ s₂ : ℝ)
    (i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    let H₁ := sys.H0 + (scaleQuasiLocalPerturbation s₁ V).totalPerturbation
    let H₂ := sys.H0 + (scaleQuasiLocalPerturbation s₂ V).totalPerturbation
    let hH₁ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₁ V)
    let hH₂ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₂ V)
    let R₁ := rankOneEigenvectorProj H₁ hH₁ i
    let R₂ := rankOneEigenvectorProj H₂ hH₂ j
    ((sortedEigenvalues H₂ hH₂ j - sortedEigenvalues H₁ hH₁ i : ℝ) : ℂ) • (R₁ * R₂) =
      ((s₂ - s₁ : ℝ) : ℂ) • (R₁ * V.totalPerturbation * R₂) := by
  intro H₁ H₂ hH₁ hH₂ R₁ R₂
  have h1 : R₁ * (H₂ - H₁) * R₂ =
      ((sortedEigenvalues H₂ hH₂ j - sortedEigenvalues H₁ hH₁ i : ℝ) : ℂ) • (R₁ * R₂) := by
    calc R₁ * (H₂ - H₁) * R₂
      _ = R₁ * (H₂ * R₂) - (R₁ * H₁) * R₂ := ring_mul_sub_sandwich R₁ H₂ H₁ R₂
      _ = R₁ * ((sortedEigenvalues H₂ hH₂ j : ℂ) • R₂) - ((sortedEigenvalues H₁ hH₁ i : ℂ) • R₁) * R₂ := by
          rw [hamiltonian_mul_rankOneEigenvectorProj H₂ hH₂ j, rankOneEigenvectorProj_mul_H H₁ hH₁ i]
      _ = ((sortedEigenvalues H₂ hH₂ j - sortedEigenvalues H₁ hH₁ i : ℝ) : ℂ) • (R₁ * R₂) := by
          rw [mul_smul_comm, smul_mul_assoc, Complex.ofReal_sub, clm_sub_smul]
  have h2 : R₁ * (H₂ - H₁) * R₂ = ((s₂ - s₁ : ℝ) : ℂ) • (R₁ * V.totalPerturbation * R₂) := by
    rw [hamiltonian_scaleQuasiLocalPerturbation_sub sys V s₁ s₂, mul_smul_comm, smul_mul_assoc]
  exact h1.symm.trans h2

/-- Norm bound on cross-basis eigenprojector product `‖R_i(s₁) * R_j(s₂)‖` under an eigenvalue
    separation `0 < δ ≤ |E_j(s₂) - E_i(s₁)|`. -/
theorem norm_cross_rankOneEigenvectorProj_le_of_gap {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₁ s₂ : ℝ)
    (i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) {δ : ℝ} (hδ_pos : 0 < δ)
    (h_gap : δ ≤ |sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s₂ V).totalPerturbation)
        (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₂ V)) j -
      sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s₁ V).totalPerturbation)
        (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₁ V)) i|) :
    let H₁ := sys.H0 + (scaleQuasiLocalPerturbation s₁ V).totalPerturbation
    let H₂ := sys.H0 + (scaleQuasiLocalPerturbation s₂ V).totalPerturbation
    let hH₁ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₁ V)
    let hH₂ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₂ V)
    ‖rankOneEigenvectorProj H₁ hH₁ i * rankOneEigenvectorProj H₂ hH₂ j‖ ≤
      δ⁻¹ * |s₂ - s₁| * ‖V.totalPerturbation‖ := by
  intro H₁ H₂ hH₁ hH₂
  let R₁ := rankOneEigenvectorProj H₁ hH₁ i
  let R₂ := rankOneEigenvectorProj H₂ hH₂ j
  let ΔE := sortedEigenvalues H₂ hH₂ j - sortedEigenvalues H₁ hH₁ i
  have h_eq := congrArg norm (cross_rankOneEigenvectorProj_sylvester_eq sys V s₁ s₂ i j)
  (try dsimp only at h_eq)
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at h_eq
  have h_prod_norm : ‖R₁ * V.totalPerturbation * R₂‖ ≤ ‖V.totalPerturbation‖ :=
    norm_sandwich_le_of_norm_le_one (norm_rankOneEigenvectorProj_le_one H₁ hH₁ i)
      (norm_rankOneEigenvectorProj_le_one H₂ hH₂ j)
  have h_le3 : δ * ‖R₁ * R₂‖ ≤ |s₂ - s₁| * ‖V.totalPerturbation‖ := by
    calc δ * ‖R₁ * R₂‖
      _ ≤ |ΔE| * ‖R₁ * R₂‖ := mul_le_mul_of_nonneg_right h_gap (norm_nonneg _)
      _ = |s₂ - s₁| * ‖R₁ * V.totalPerturbation * R₂‖ := h_eq
      _ ≤ |s₂ - s₁| * ‖V.totalPerturbation‖ := mul_le_mul_of_nonneg_left h_prod_norm (abs_nonneg _)
  calc ‖R₁ * R₂‖
    _ = δ⁻¹ * (δ * ‖R₁ * R₂‖) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hδ_pos), one_mul]
    _ ≤ δ⁻¹ * (|s₂ - s₁| * ‖V.totalPerturbation‖) :=
        mul_le_mul_of_nonneg_left h_le3 (inv_nonneg.mpr (le_of_lt hδ_pos))
    _ = δ⁻¹ * |s₂ - s₁| * ‖V.totalPerturbation‖ := by ring

/-! ## 2. Weyl Gap Persistence & Local Lipschitz Continuity of `perturbedGroundSpectralProj` -/

/-- Whenever `bhmPerturbedGap ≤ indexedSpectralGap sys V s₀`, every ground-band eigenvalue
    `E_i(s₀)` and excited-band eigenvalue `E_j(s₀)` satisfy `1 / 2 ≤ E_j(s₀) - E_i(s₀)`. -/
theorem band_gap_of_bhmPerturbedGap_le_indexedSpectralGap {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (h_gap : bhmPerturbedGap ≤ indexedSpectralGap sys V s₀)
    {i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))}
    (hi : i ∈ groundBandFinset sys) (hj : j ∈ excitedBandFinset sys) :
    let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
    let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
    (1 / 2 : ℝ) ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i := by
  intro H₀ hH₀
  exact le_trans h_gap (indexedSpectralGap_le_indexedEigenvalueGap sys V
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 s₀)

/-- Weyl persistence of cross-band and same-point eigenvalue gaps when `|s - s₀| * ‖V.V_tot‖ ≤ Δ / 4`. -/
theorem cross_band_gap_ge_half_delta_of_norm_mul_le {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ s : ℝ) {Δ : ℝ}
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i)
    (hs : |s - s₀| * ‖V.totalPerturbation‖ ≤ Δ / 4)
    {i j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))}
    (hi : i ∈ groundBandFinset sys) (hj : j ∈ excitedBandFinset sys) :
    let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
    let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
    let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
    Δ / 2 ≤ sortedEigenvalues H_s hHs j - sortedEigenvalues H₀ hH₀ i ∧
    Δ / 2 ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H_s hHs i ∧
    Δ / 2 ≤ sortedEigenvalues H_s hHs j - sortedEigenvalues H_s hHs i := by
  intro H₀ H_s hH₀ hHs
  have h0 := h_gap i hi j hj; (try dsimp only at h0)
  have hi_le := le_trans (abs_sortedEigenvalues_scaleQuasiLocalPerturbation_sub_le sys V i s s₀) hs
  have hj_le := le_trans (abs_sortedEigenvalues_scaleQuasiLocalPerturbation_sub_le sys V j s s₀) hs
  rw [abs_le] at hi_le hj_le
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Universal ring decomposition `P - P₀ = P * (1 - P₀) - (1 - P) * P₀`. -/
lemma proj_sub_eq_offDiag_cross {R : Type*} [Ring R] (P P₀ : R) :
    P - P₀ = P * (1 - P₀) - (1 - P) * P₀ := by noncomm_ring

/-- Quadratic norm bound `‖twoBlockDiagProj P₀ (P - P₀)‖ ≤ 2 * ‖P - P₀‖ ^ 2` for star projections `P, P₀`. -/
theorem norm_twoBlockDiagProj_sub_le_two_mul_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P P₀ : E →L[ℂ] E} (hP : IsStarProjection P) (hP₀ : IsStarProjection P₀) :
    ‖twoBlockDiagProj P₀ (P - P₀)‖ ≤ 2 * ‖P - P₀‖ ^ 2 := by
  unfold twoBlockDiagProj
  rw [ring_twoBlockDiag_idempotent_sq hP.isIdempotentElem.eq hP₀.isIdempotentElem.eq]
  have hP0_norm : ‖P₀‖ ≤ 1 := isStarProjection_norm_le_one hP₀
  have h1P0_norm : ‖1 - P₀‖ ≤ 1 := isStarProjection_norm_le_one (isStarProjection_one_sub hP₀)
  have h_sq_le : ‖(P - P₀) * (P - P₀)‖ ≤ ‖P - P₀‖ ^ 2 := by
    rw [sq]; exact ContinuousLinearMap.opNorm_comp_le (P - P₀) (P - P₀)
  have h_term1 := le_trans (norm_sandwich_le_of_norm_le_one h1P0_norm h1P0_norm) h_sq_le
  have h_term2 := le_trans (norm_sandwich_le_of_norm_le_one hP0_norm hP0_norm) h_sq_le
  calc ‖(1 - P₀) * ((P - P₀) * (P - P₀)) * (1 - P₀) - P₀ * ((P - P₀) * (P - P₀)) * P₀‖
    _ ≤ ‖(1 - P₀) * ((P - P₀) * (P - P₀)) * (1 - P₀)‖ + ‖P₀ * ((P - P₀) * (P - P₀)) * P₀‖ :=
        norm_sub_le _ _
    _ ≤ ‖P - P₀‖ ^ 2 + ‖P - P₀‖ ^ 2 := add_le_add h_term1 h_term2
    _ = 2 * ‖P - P₀‖ ^ 2 := by ring

/-- Local Lipschitz bound on `perturbedGroundSpectralProj sys V` around `s₀` under a band gap `Δ > 0`. -/
theorem norm_perturbedGroundSpectralProj_sub_le_of_band_gap {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ s : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i)
    (hs : |s - s₀| * ‖V.totalPerturbation‖ ≤ Δ / 4) :
    ‖perturbedGroundSpectralProj sys V s - perturbedGroundSpectralProj sys V s₀‖ ≤
      (4 * ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ) *
        Δ⁻¹ * ‖V.totalPerturbation‖) * |s - s₀| := by
  let P_s := perturbedGroundSpectralProj sys V s
  let P₀ := perturbedGroundSpectralProj sys V s₀
  let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
  let H_s := sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
  let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
  let hHs := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s V)
  let G := groundBandFinset sys; let E := excitedBandFinset sys
  have hΔ2_pos : 0 < Δ / 2 := half_pos hΔ
  have h_sub : P_s - P₀ = P_s * (1 - P₀) - (1 - P_s) * P₀ := proj_sub_eq_offDiag_cross P_s P₀
  have h_term1 : ‖P_s * (1 - P₀)‖ ≤
      (G.card : ℝ) * ((E.card : ℝ) * ((Δ / 2)⁻¹ * |s - s₀| * ‖V.totalPerturbation‖)) := by
    dsimp [P_s, P₀]; rw [one_sub_perturbedGroundSpectralProj_eq_sum_excitedBandFinset sys V s₀]
    dsimp [perturbedGroundSpectralProj]; rw [Finset.sum_mul]
    refine le_trans (norm_sum_le G _) ?_; rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul G _ _ fun i hi => ?_; rw [Finset.mul_sum]
    refine le_trans (norm_sum_le E _) ?_; rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul E _ _ fun j hj => ?_
    have h_cross := (cross_band_gap_ge_half_delta_of_norm_mul_le sys V s₀ s h_gap hs hi hj).2.1
    have h_abs : Δ / 2 ≤ |sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H_s hHs i| :=
      le_trans h_cross (le_abs_self _)
    have h_norm := norm_cross_rankOneEigenvectorProj_le_of_gap sys V s s₀ i j hΔ2_pos h_abs
    (try dsimp only at h_norm); rwa [abs_sub_comm s₀ s] at h_norm
  have h_term2 : ‖(1 - P_s) * P₀‖ ≤
      (E.card : ℝ) * ((G.card : ℝ) * ((Δ / 2)⁻¹ * |s - s₀| * ‖V.totalPerturbation‖)) := by
    dsimp [P_s, P₀]; rw [one_sub_perturbedGroundSpectralProj_eq_sum_excitedBandFinset sys V s]
    dsimp [perturbedGroundSpectralProj]; rw [Finset.sum_mul]
    refine le_trans (norm_sum_le E _) ?_; rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul E _ _ fun j hj => ?_; rw [Finset.mul_sum]
    refine le_trans (norm_sum_le G _) ?_; rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul G _ _ fun i hi => ?_
    have h_cross := (cross_band_gap_ge_half_delta_of_norm_mul_le sys V s₀ s h_gap hs hi hj).1
    have h_abs : Δ / 2 ≤ |sortedEigenvalues H₀ hH₀ i - sortedEigenvalues H_s hHs j| := by
      rw [abs_sub_comm]; exact le_trans h_cross (le_abs_self _)
    have h_norm := norm_cross_rankOneEigenvectorProj_le_of_gap sys V s s₀ j i hΔ2_pos h_abs
    (try dsimp only at h_norm); rwa [abs_sub_comm s₀ s] at h_norm
  calc ‖P_s - P₀‖
    _ = ‖P_s * (1 - P₀) - (1 - P_s) * P₀‖ := by rw [h_sub]
    _ ≤ ‖P_s * (1 - P₀)‖ + ‖(1 - P_s) * P₀‖ := norm_sub_le _ _
    _ ≤ (G.card : ℝ) * ((E.card : ℝ) * ((Δ / 2)⁻¹ * |s - s₀| * ‖V.totalPerturbation‖)) +
          (E.card : ℝ) * ((G.card : ℝ) * ((Δ / 2)⁻¹ * |s - s₀| * ‖V.totalPerturbation‖)) :=
        add_le_add h_term1 h_term2
    _ = (4 * (G.card : ℝ) * (E.card : ℝ) * Δ⁻¹ * ‖V.totalPerturbation‖) * |s - s₀| := by ring

/-! ## 3. Blocked Off-Diagonal Sylvester Inverse `sylvesterOffDiagInverse` -/

/-- **Blocked Off-Diagonal Sylvester Operator Inverse (`sylvesterOffDiagInverse`)**. -/
def sylvesterOffDiagInverse {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ i ∈ groundBandFinset sys, ∑ j ∈ excitedBandFinset sys,
    (((sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation)
          (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)) j -
        sortedEigenvalues (sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation)
          (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)) i)⁻¹ : ℝ) : ℂ) •
      (rankOneEigenvectorProj (sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation)
          (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)) j * Y *
        rankOneEigenvectorProj (sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation)
          (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)) i -
       rankOneEigenvectorProj (sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation)
          (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)) i * Y *
        rankOneEigenvectorProj (sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation)
          (isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)) j)

/-- Linearity of `sylvesterOffDiagInverse` over addition. -/
lemma sylvesterOffDiagInverse_add {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (Y₁ Y₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    sylvesterOffDiagInverse sys V s₀ (Y₁ + Y₂) =
      sylvesterOffDiagInverse sys V s₀ Y₁ + sylvesterOffDiagInverse sys V s₀ Y₂ := by
  unfold sylvesterOffDiagInverse
  rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [← clm_smul_add]; congr 1; simp only [mul_add, add_mul]; abel

/-- Linearity of `sylvesterOffDiagInverse` over subtraction. -/
lemma sylvesterOffDiagInverse_sub {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (Y₁ Y₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    sylvesterOffDiagInverse sys V s₀ (Y₁ - Y₂) =
      sylvesterOffDiagInverse sys V s₀ Y₁ - sylvesterOffDiagInverse sys V s₀ Y₂ := by
  unfold sylvesterOffDiagInverse
  rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [← clm_smul_sub]; congr 1; simp only [mul_sub, sub_mul]; abel

/-- Linearity of `sylvesterOffDiagInverse` over scalar multiplication. -/
lemma sylvesterOffDiagInverse_smul {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) (c : ℂ)
    (Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    sylvesterOffDiagInverse sys V s₀ (c • Y) = c • sylvesterOffDiagInverse sys V s₀ Y := by
  unfold sylvesterOffDiagInverse
  rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm]; congr 1
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, clm_smul_sub]

/-- Operator norm bound on `sylvesterOffDiagInverse sys V s₀ Y` under a band gap `Δ > 0`. -/
theorem norm_sylvesterOffDiagInverse_le_of_band_gap {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i)
    (Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖sylvesterOffDiagInverse sys V s₀ Y‖ ≤
      (2 * ((groundBandFinset sys).card : ℝ) * ((excitedBandFinset sys).card : ℝ) * Δ⁻¹) * ‖Y‖ := by
  let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
  let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
  let G := groundBandFinset sys; let E := excitedBandFinset sys
  unfold sylvesterOffDiagInverse
  calc ‖∑ i ∈ G, ∑ j ∈ E,
        (((sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i)⁻¹ : ℝ) : ℂ) •
          (rankOneEigenvectorProj H₀ hH₀ j * Y * rankOneEigenvectorProj H₀ hH₀ i -
            rankOneEigenvectorProj H₀ hH₀ i * Y * rankOneEigenvectorProj H₀ hH₀ j)‖
    _ ≤ (G.card : ℝ) * ((E.card : ℝ) * (Δ⁻¹ * (2 * ‖Y‖))) := by
        refine le_trans (norm_sum_le G _) ?_; rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul G _ _ fun i hi => ?_
        refine le_trans (norm_sum_le E _) ?_; rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul E _ _ fun j hj => ?_
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        have h_ij : Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i := h_gap i hi j hj
        have h_pos : 0 < sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i := lt_of_lt_of_le hΔ h_ij
        have h_inv_le : |(sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i)⁻¹| ≤ Δ⁻¹ := by
          rw [abs_of_pos (inv_pos.mpr h_pos)]; exact inv_anti₀ hΔ h_ij
        have h_sand1 : ‖rankOneEigenvectorProj H₀ hH₀ j * Y * rankOneEigenvectorProj H₀ hH₀ i‖ ≤ ‖Y‖ :=
          norm_sandwich_le_of_norm_le_one (norm_rankOneEigenvectorProj_le_one H₀ hH₀ j)
            (norm_rankOneEigenvectorProj_le_one H₀ hH₀ i)
        have h_sand2 : ‖rankOneEigenvectorProj H₀ hH₀ i * Y * rankOneEigenvectorProj H₀ hH₀ j‖ ≤ ‖Y‖ :=
          norm_sandwich_le_of_norm_le_one (norm_rankOneEigenvectorProj_le_one H₀ hH₀ i)
            (norm_rankOneEigenvectorProj_le_one H₀ hH₀ j)
        have h_diff : ‖rankOneEigenvectorProj H₀ hH₀ j * Y * rankOneEigenvectorProj H₀ hH₀ i -
            rankOneEigenvectorProj H₀ hH₀ i * Y * rankOneEigenvectorProj H₀ hH₀ j‖ ≤ 2 * ‖Y‖ := by
          calc ‖rankOneEigenvectorProj H₀ hH₀ j * Y * rankOneEigenvectorProj H₀ hH₀ i -
                rankOneEigenvectorProj H₀ hH₀ i * Y * rankOneEigenvectorProj H₀ hH₀ j‖
            _ ≤ ‖rankOneEigenvectorProj H₀ hH₀ j * Y * rankOneEigenvectorProj H₀ hH₀ i‖ +
                  ‖rankOneEigenvectorProj H₀ hH₀ i * Y * rankOneEigenvectorProj H₀ hH₀ j‖ := norm_sub_le _ _
            _ ≤ ‖Y‖ + ‖Y‖ := add_le_add h_sand1 h_sand2
            _ = 2 * ‖Y‖ := by ring
        exact mul_le_mul h_inv_le h_diff (norm_nonneg _) (inv_nonneg.mpr (le_of_lt hΔ))
    _ = (2 * (G.card : ℝ) * (E.card : ℝ) * Δ⁻¹) * ‖Y‖ := by ring

/-- `sylvesterOffDiagInverse sys V s₀ Y` is purely off-diagonal with respect to
    `perturbedGroundSpectralProj sys V s₀`. -/
theorem twoBlockOffDiagProj_sylvesterOffDiagInverse_eq_self {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    (Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    twoBlockOffDiagProj (perturbedGroundSpectralProj sys V s₀)
      (sylvesterOffDiagInverse sys V s₀ Y) = sylvesterOffDiagInverse sys V s₀ Y := by
  let P₀ := perturbedGroundSpectralProj sys V s₀
  let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
  let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
  unfold twoBlockOffDiagProj sylvesterOffDiagInverse
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rcases perturbedGroundSpectralProj_rankOne_mul_rules sys V s₀ hi hj with
    ⟨hPRi, hRiP, hPRj, hRjP, h1PRi, hRi1P, h1PRj, hRj1P⟩
  (try dsimp only at hPRi hRiP hPRj hRjP h1PRi hRi1P h1PRj hRj1P)
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, ← clm_smul_add]; congr 1
  let R_i := rankOneEigenvectorProj H₀ hH₀ i; let R_j := rankOneEigenvectorProj H₀ hH₀ j
  have h1 : P₀ * (R_j * Y * R_i - R_i * Y * R_j) * (1 - P₀) = -(R_i * Y * R_j) := by
    rw [ring_offDiag_diff_left P₀ R_i Y R_j, hPRj, hRi1P, hPRi, hRj1P]
    simp only [zero_mul, mul_zero, zero_sub]; rfl
  have h2 : (1 - P₀) * (R_j * Y * R_i - R_i * Y * R_j) * P₀ = R_j * Y * R_i := by
    rw [ring_offDiag_diff_right P₀ R_i Y R_j, h1PRj, hRiP, h1PRi, hRjP]
    simp only [zero_mul, mul_zero, sub_zero]; rfl
  change P₀ * (R_j * Y * R_i - R_i * Y * R_j) * (1 - P₀) +
      (1 - P₀) * (R_j * Y * R_i - R_i * Y * R_j) * P₀ = R_j * Y * R_i - R_i * Y * R_j
  rw [h1, h2]; abel

/-- Whenever `star Y = -Y` (skew-adjoint), `sylvesterOffDiagInverse sys V s₀ Y` is self-adjoint. -/
theorem isSelfAdjoint_sylvesterOffDiagInverse_of_star_eq_neg {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ)
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hY : star Y = -Y) :
    IsSelfAdjoint (sylvesterOffDiagInverse sys V s₀ Y) := by
  let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
  let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
  unfold sylvesterOffDiagInverse
  refine isSelfAdjoint_finset_sum _ _ fun i _ => isSelfAdjoint_finset_sum _ _ fun j _ => ?_
  refine isSelfAdjoint_real_smul _ ?_
  let R_i := rankOneEigenvectorProj H₀ hH₀ i; let R_j := rankOneEigenvectorProj H₀ hH₀ j
  change IsSelfAdjoint (R_j * Y * R_i - R_i * Y * R_j)
  have hRi : star R_i = R_i := (isSelfAdjoint_rankOneEigenvectorProj H₀ hH₀ i).star_eq
  have hRj : star R_j = R_j := (isSelfAdjoint_rankOneEigenvectorProj H₀ hH₀ j).star_eq
  rw [IsSelfAdjoint, clm_star_sub, clm_star_mul, clm_star_mul, clm_star_mul, clm_star_mul, hRi, hRj, hY]
  simp only [neg_mul, mul_neg, ← mul_assoc]; abel

/-- **Left Sylvester Inversion (`sylvesterOffDiagInverse_commutator_eq_twoBlockOffDiagProj`)**. -/
theorem sylvesterOffDiagInverse_commutator_eq_twoBlockOffDiagProj {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i)
    (Z : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
    sylvesterOffDiagInverse sys V s₀ (H₀ * Z - Z * H₀) =
      twoBlockOffDiagProj (perturbedGroundSpectralProj sys V s₀) Z := by
  intro H₀
  let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
  let G := groundBandFinset sys; let E := excitedBandFinset sys
  have h_sum : sylvesterOffDiagInverse sys V s₀ (H₀ * Z - Z * H₀) =
      ∑ i ∈ G, ∑ j ∈ E,
        (rankOneEigenvectorProj H₀ hH₀ j * Z * rankOneEigenvectorProj H₀ hH₀ i +
          rankOneEigenvectorProj H₀ hH₀ i * Z * rankOneEigenvectorProj H₀ hH₀ j) := by
    unfold sylvesterOffDiagInverse
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    let R_i := rankOneEigenvectorProj H₀ hH₀ i; let R_j := rankOneEigenvectorProj H₀ hH₀ j
    let E_i := sortedEigenvalues H₀ hH₀ i; let E_j := sortedEigenvalues H₀ hH₀ j
    have h_ne : (E_j - E_i : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le hΔ (h_gap i hi j hj))
    have h_ji : R_j * (H₀ * Z - Z * H₀) * R_i = ((E_j - E_i : ℝ) : ℂ) • (R_j * Z * R_i) := by
      calc R_j * (H₀ * Z - Z * H₀) * R_i
        _ = (R_j * H₀) * Z * R_i - R_j * Z * (H₀ * R_i) := ring_commutator_sandwich_left R_j H₀ Z R_i
        _ = ((E_j : ℂ) • R_j) * Z * R_i - R_j * Z * ((E_i : ℂ) • R_i) := by
            rw [rankOneEigenvectorProj_mul_H H₀ hH₀ j, hamiltonian_mul_rankOneEigenvectorProj H₀ hH₀ i]
        _ = ((E_j - E_i : ℝ) : ℂ) • (R_j * Z * R_i) := by
            rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, Complex.ofReal_sub, clm_sub_smul]
    have h_ij : R_i * (H₀ * Z - Z * H₀) * R_j = -(((E_j - E_i : ℝ) : ℂ) • (R_i * Z * R_j)) := by
      calc R_i * (H₀ * Z - Z * H₀) * R_j
        _ = (R_i * H₀) * Z * R_j - R_i * Z * (H₀ * R_j) := ring_commutator_sandwich_left R_i H₀ Z R_j
        _ = ((E_i : ℂ) • R_i) * Z * R_j - R_i * Z * ((E_j : ℂ) • R_j) := by
            rw [rankOneEigenvectorProj_mul_H H₀ hH₀ i, hamiltonian_mul_rankOneEigenvectorProj H₀ hH₀ j]
        _ = -(((E_j - E_i : ℝ) : ℂ) • (R_i * Z * R_j)) := by
            rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, Complex.ofReal_sub, clm_sub_smul]; abel
    change (((E_j - E_i)⁻¹ : ℝ) : ℂ) • (R_j * (H₀ * Z - Z * H₀) * R_i - R_i * (H₀ * Z - Z * H₀) * R_j) =
      R_j * Z * R_i + R_i * Z * R_j
    rw [h_ji, h_ij, sub_neg_eq_add, ← clm_smul_add, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ h_ne, Complex.ofReal_one, one_smul]
  rw [h_sum]; unfold twoBlockOffDiagProj
  rw [one_sub_perturbedGroundSpectralProj_eq_sum_excitedBandFinset sys V s₀]
  dsimp [perturbedGroundSpectralProj]
  simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := E) (t := G), add_comm]

/-- **Right Sylvester Inversion (`commutator_sylvesterOffDiagInverse_eq_twoBlockOffDiagProj`)**. -/
theorem commutator_sylvesterOffDiagInverse_eq_twoBlockOffDiagProj {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (s₀ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ)
    (h_gap : ∀ i ∈ groundBandFinset sys, ∀ j ∈ excitedBandFinset sys,
      let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
      let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
      Δ ≤ sortedEigenvalues H₀ hH₀ j - sortedEigenvalues H₀ hH₀ i)
    (Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let H₀ := sys.H0 + (scaleQuasiLocalPerturbation s₀ V).totalPerturbation
    H₀ * sylvesterOffDiagInverse sys V s₀ Y - sylvesterOffDiagInverse sys V s₀ Y * H₀ =
      twoBlockOffDiagProj (perturbedGroundSpectralProj sys V s₀) Y := by
  intro H₀
  let hH₀ := isSelfAdjoint_indexedH0_add_V_tot_bhm sys (scaleQuasiLocalPerturbation s₀ V)
  let G := groundBandFinset sys; let E := excitedBandFinset sys
  have h_comm : H₀ * sylvesterOffDiagInverse sys V s₀ Y - sylvesterOffDiagInverse sys V s₀ Y * H₀ =
      ∑ i ∈ G, ∑ j ∈ E,
        (rankOneEigenvectorProj H₀ hH₀ j * Y * rankOneEigenvectorProj H₀ hH₀ i +
          rankOneEigenvectorProj H₀ hH₀ i * Y * rankOneEigenvectorProj H₀ hH₀ j) := by
    unfold sylvesterOffDiagInverse
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    let R_i := rankOneEigenvectorProj H₀ hH₀ i; let R_j := rankOneEigenvectorProj H₀ hH₀ j
    let E_i := sortedEigenvalues H₀ hH₀ i; let E_j := sortedEigenvalues H₀ hH₀ j
    have h_ne : (E_j - E_i : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le hΔ (h_gap i hi j hj))
    change H₀ * ((((E_j - E_i)⁻¹ : ℝ) : ℂ) • (R_j * Y * R_i - R_i * Y * R_j)) -
        ((((E_j - E_i)⁻¹ : ℝ) : ℂ) • (R_j * Y * R_i - R_i * Y * R_j)) * H₀ =
      R_j * Y * R_i + R_i * Y * R_j
    rw [mul_smul_comm, smul_mul_assoc, ← clm_smul_sub]
    have h_inner :
        H₀ * (R_j * Y * R_i - R_i * Y * R_j) - (R_j * Y * R_i - R_i * Y * R_j) * H₀ =
          ((E_j - E_i : ℝ) : ℂ) • (R_j * Y * R_i + R_i * Y * R_j) := by
      calc H₀ * (R_j * Y * R_i - R_i * Y * R_j) - (R_j * Y * R_i - R_i * Y * R_j) * H₀
        _ = ((H₀ * R_j) * Y * R_i - R_j * Y * (R_i * H₀)) +
              (R_i * Y * (R_j * H₀) - (H₀ * R_i) * Y * R_j) := ring_commutator_diff_sandwich H₀ R_j Y R_i
        _ = (((E_j : ℂ) • R_j) * Y * R_i - R_j * Y * ((E_i : ℂ) • R_i)) +
              (R_i * Y * ((E_j : ℂ) • R_j) - ((E_i : ℂ) • R_i) * Y * R_j) := by
            rw [hamiltonian_mul_rankOneEigenvectorProj H₀ hH₀ j, rankOneEigenvectorProj_mul_H H₀ hH₀ i,
              rankOneEigenvectorProj_mul_H H₀ hH₀ j, hamiltonian_mul_rankOneEigenvectorProj H₀ hH₀ i]
        _ = ((E_j - E_i : ℝ) : ℂ) • (R_j * Y * R_i + R_i * Y * R_j) := by
            simp only [smul_mul_assoc, mul_smul_comm, Complex.ofReal_sub, clm_sub_smul, clm_smul_add]
    rw [h_inner, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ h_ne,
      Complex.ofReal_one, one_smul]
  rw [h_comm]; unfold twoBlockOffDiagProj
  rw [one_sub_perturbedGroundSpectralProj_eq_sum_excitedBandFinset sys V s₀]
  dsimp [perturbedGroundSpectralProj]
  simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := E) (t := G), add_comm]

end
