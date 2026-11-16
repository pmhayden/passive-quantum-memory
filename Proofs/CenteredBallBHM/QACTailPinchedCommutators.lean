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

import Proofs.DressedSyndromeGibbs.DressedKMSGronwallTrajectory
import Proofs.TwoAxisMemorySynthesis.FiniteRangeMemoryRealization

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# QAC-Tail Pinched Commutator Estimates and Spectral Dressing Packages

Establishes abstract Hilbert-space norm bounds for dressed safe-subspace pinched commutators whenever an operator decomposes into a term annihilated on the bare safe subspace plus a small quasi-adiabatic or Lieb–Robinson tail (`norm_dressed_pinched_commutator_le_two_mul_qac_tail_clm`, `coherent_dressed_pinched_commutator_le_split_of_qac_tail_clm`, `sq_norm_dressed_pinched_commutator_le_of_lr_tail_clm`), and defines `BDLDressingPackage`.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
-/

/-! ## 1. Abstract Hilbert-Space QAC-Tail Pinched Commutator Bounds -/

private lemma norm_commutator_le_two_mul_norm_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (X O : E →L[ℂ] E) (hO : ‖O‖ ≤ 1) :
    ‖X * O - O * X‖ ≤ 2 * ‖X‖ := by
  have h1 : ‖X * O‖ ≤ ‖X‖ :=
    le_trans (ContinuousLinearMap.opNorm_comp_le X O)
      (le_trans (mul_le_mul_of_nonneg_left hO (norm_nonneg X)) (by ring_nf; rfl))
  have h2 : ‖O * X‖ ≤ ‖X‖ :=
    le_trans (ContinuousLinearMap.opNorm_comp_le O X)
      (le_trans (mul_le_mul_of_nonneg_right hO (norm_nonneg X)) (by ring_nf; rfl))
  calc ‖X * O - O * X‖
    _ ≤ ‖X * O‖ + ‖O * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ + ‖X‖ := add_le_add h1 h2
    _ = 2 * ‖X‖ := by ring

private lemma norm_pi_safe_sandwich_le_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (Pi_safe M : E →L[ℂ] E) (hPi : IsStarProjection Pi_safe) :
    ‖Pi_safe * M * Pi_safe‖ ≤ ‖M‖ := by
  have h1 : ‖Pi_safe‖ ≤ 1 := isStarProjection_norm_le_one hPi
  calc ‖Pi_safe * M * Pi_safe‖
    _ ≤ ‖Pi_safe * M‖ * ‖Pi_safe‖ := ContinuousLinearMap.opNorm_comp_le (Pi_safe * M) Pi_safe
    _ ≤ ‖Pi_safe * M‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖Pi_safe * M‖ := mul_one _
    _ ≤ ‖Pi_safe‖ * ‖M‖ := ContinuousLinearMap.opNorm_comp_le Pi_safe M
    _ ≤ 1 * ‖M‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖M‖ := one_mul _

/-- **Abstract Hilbert-Space QAC-Tail Pinched Commutator Bound
(`norm_dressed_pinched_commutator_le_two_mul_qac_tail_clm`)**:
If `Pi_safe` is a star-projection, `‖O_dec‖ ≤ 1`, and `X_loc` satisfies bare safe-subspace immunity
`Pi_safe * (X_loc * O_dec - O_dec * X_loc) * Pi_safe = 0`, then
$$\bigl\|(U_{\mathrm{dress}} \Pi_{\mathrm{safe}} U_{\mathrm{dress}}^\dagger)
  \bigl[X, U_{\mathrm{dress}} O_{\mathrm{dec}} U_{\mathrm{dress}}^\dagger\bigr]
  (U_{\mathrm{dress}} \Pi_{\mathrm{safe}} U_{\mathrm{dress}}^\dagger)\bigr\|
  \le 2 \bigl\|U_{\mathrm{dress}}^\dagger X U_{\mathrm{dress}} - X_{\mathrm{loc}}\bigr\|.$$ -/
theorem norm_dressed_pinched_commutator_le_two_mul_qac_tail_clm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U_dress : unitary (E →L[ℂ] E))
    (Pi_safe O_dec X X_loc : E →L[ℂ] E)
    (hPi : IsStarProjection Pi_safe)
    (hO_norm : ‖O_dec‖ ≤ 1)
    (h_fw : Pi_safe * (X_loc * O_dec - O_dec * X_loc) * Pi_safe = 0) :
    ‖(U_dress.1 * Pi_safe * U_dress.1†) *
      (X * (U_dress.1 * O_dec * U_dress.1†) - (U_dress.1 * O_dec * U_dress.1†) * X) *
      (U_dress.1 * Pi_safe * U_dress.1†)‖ ≤
    2 * ‖U_dress.1† * X * U_dress.1 - X_loc‖ := by
  let ΔX := U_dress.1† * X * U_dress.1 - X_loc
  have h_cov := dressed_sandwich_opCommutator_eq U_dress X O_dec Pi_safe
  change (U_dress.1 * Pi_safe * U_dress.1†) *
      (X * (U_dress.1 * O_dec * U_dress.1†) - (U_dress.1 * O_dec * U_dress.1†) * X) *
      (U_dress.1 * Pi_safe * U_dress.1†) =
    U_dress.1 * (Pi_safe * ((U_dress.1† * X * U_dress.1) * O_dec -
      O_dec * (U_dress.1† * X * U_dress.1)) * Pi_safe) * U_dress.1† at h_cov
  have h_sub_eq :
      Pi_safe * ((U_dress.1† * X * U_dress.1) * O_dec -
        O_dec * (U_dress.1† * X * U_dress.1)) * Pi_safe =
      Pi_safe * (ΔX * O_dec - O_dec * ΔX) * Pi_safe := by
    have h_split :
        (U_dress.1† * X * U_dress.1) * O_dec - O_dec * (U_dress.1† * X * U_dress.1) =
          (ΔX * O_dec - O_dec * ΔX) + (X_loc * O_dec - O_dec * X_loc) := by
      dsimp [ΔX]; rw [sub_mul, mul_sub]; abel
    rw [h_split, mul_add, add_mul, h_fw, add_zero]
  rw [h_cov, h_sub_eq]
  calc ‖U_dress.1 * (Pi_safe * (ΔX * O_dec - O_dec * ΔX) * Pi_safe) * U_dress.1†‖
    _ ≤ ‖Pi_safe * (ΔX * O_dec - O_dec * ΔX) * Pi_safe‖ :=
      norm_unitary_conj_le U_dress _
    _ ≤ ‖ΔX * O_dec - O_dec * ΔX‖ :=
      norm_pi_safe_sandwich_le_clm Pi_safe _ hPi
    _ ≤ 2 * ‖ΔX‖ :=
      norm_commutator_le_two_mul_norm_clm ΔX O_dec hO_norm

/-- **Coherent Pinched Commutator Bound from Bare Safe-Subspace Immunity & QAC Tail
(`coherent_dressed_pinched_commutator_le_split_of_qac_tail_clm`)**. -/
theorem coherent_dressed_pinched_commutator_le_split_of_qac_tail_clm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U_dress : unitary (E →L[ℂ] E))
    (Pi_safe O_dec H H_loc : E →L[ℂ] E)
    (hPi : IsStarProjection Pi_safe)
    (hO_norm : ‖O_dec‖ ≤ 1)
    {ε_tail δ_split : ℝ}
    (h_H_fw : Pi_safe * (H_loc * O_dec - O_dec * H_loc) * Pi_safe = 0)
    (h_H_tail : ‖U_dress.1† * H * U_dress.1 - H_loc‖ ≤ ε_tail)
    (h_tail_split : 2 * ε_tail ≤ δ_split) :
    ‖(U_dress.1 * Pi_safe * U_dress.1†) *
      (H * (U_dress.1 * O_dec * U_dress.1†) - (U_dress.1 * O_dec * U_dress.1†) * H) *
      (U_dress.1 * Pi_safe * U_dress.1†)‖ ≤ δ_split := by
  have h1 := norm_dressed_pinched_commutator_le_two_mul_qac_tail_clm
    U_dress Pi_safe O_dec H H_loc hPi hO_norm h_H_fw
  linarith

/-- **Bath Jump Pinched Commutator Squared Bound from Bare Safe-Subspace Immunity & Lieb–Robinson QAC Tail
(`sq_norm_dressed_pinched_commutator_le_of_lr_tail_clm`)**. -/
theorem sq_norm_dressed_pinched_commutator_le_of_lr_tail_clm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (U_dress : unitary (E →L[ℂ] E))
    (Pi_safe O_dec L_op L_loc : E →L[ℂ] E)
    (hPi : IsStarProjection Pi_safe)
    (hO_norm : ‖O_dec‖ ≤ 1)
    {ε_LR δ_split : ℝ}
    (_hε_LR_nn : 0 ≤ ε_LR)
    (h_L_fw : Pi_safe * (L_loc * O_dec - O_dec * L_loc) * Pi_safe = 0)
    (h_L_tail : ‖U_dress.1† * L_op * U_dress.1 - L_loc‖ ≤ ε_LR * ‖L_op‖)
    (h_LR_split : 4 * ε_LR ^ 2 ≤ δ_split) :
    ‖(U_dress.1 * Pi_safe * U_dress.1†) *
      (L_op * (U_dress.1 * O_dec * U_dress.1†) - (U_dress.1 * O_dec * U_dress.1†) * L_op) *
      (U_dress.1 * Pi_safe * U_dress.1†)‖ ^ 2 ≤
    ‖L_op‖ ^ 2 * δ_split := by
  let C_pinch :=
    (U_dress.1 * Pi_safe * U_dress.1†) *
      (L_op * (U_dress.1 * O_dec * U_dress.1†) - (U_dress.1 * O_dec * U_dress.1†) * L_op) *
      (U_dress.1 * Pi_safe * U_dress.1†)
  have h_norm : ‖C_pinch‖ ≤ 2 * ε_LR * ‖L_op‖ := by
    have h1 := norm_dressed_pinched_commutator_le_two_mul_qac_tail_clm
      U_dress Pi_safe O_dec L_op L_loc hPi hO_norm h_L_fw
    change ‖C_pinch‖ ≤ 2 * ‖U_dress.1† * L_op * U_dress.1 - L_loc‖ at h1
    linarith
  have h_sq : ‖C_pinch‖ ^ 2 ≤ (2 * ε_LR * ‖L_op‖) ^ 2 := by
    nlinarith [norm_nonneg C_pinch, h_norm]
  calc ‖C_pinch‖ ^ 2
    _ ≤ (2 * ε_LR * ‖L_op‖) ^ 2 := h_sq
    _ = ‖L_op‖ ^ 2 * (4 * ε_LR ^ 2) := by ring
    _ ≤ ‖L_op‖ ^ 2 * δ_split := mul_le_mul_of_nonneg_left h_LR_split (sq_nonneg _)

/-! ## 2. Quasi-Local Spectral Dressing Package (`BDLDressingPackage`) -/

/-- **Quasi-Local Spectral Dressing Package (`BDLDressingPackage`)**:
Packages the purely spectral and quasi-local dressing outputs (Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`))
with zero dependence on inverse temperature `β`, `gibbsFailureProb`, or `SatisfiesKMSLindbladODE`. -/
structure BDLDressingPackage
    {L q_code r_0 m_max : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L q_code r_0 m_max c_star C β_c c_F η c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (r_pert : ℕ) (δ_split : ℝ) where
  U_dress : unitary (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
  c_shift : ℝ
  h_comm_P0 : Commute (U_dress.1† * (mem.sys.H0 + V.totalPerturbation) * U_dress.1) mem.sys.P0
  h_form : ∀ ψ : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)),
    |RCLike.re (inner ℂ ψ
        ((U_dress.1† * (mem.sys.H0 + V.totalPerturbation) * U_dress.1 - mem.sys.H0 -
          (c_shift : ℂ) • 1) ψ))| ≤
      bhmSandwichDeviation * RCLike.re (inner ℂ ψ (mem.sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2
  h_coh_safe :
    (∀ r : ℕ, r_pert < r → ∀ A : Finset (Box3D L), V.term r A = 0) →
    let Pi_safe_dress := U_dress.1 * mem.Pi_safe * U_dress.1†
    let O_Z_dress := U_dress.1 * mem.O_dec_Z * U_dress.1†
    let O_X_dress := U_dress.1 * mem.O_dec_X * U_dress.1†
    ‖Pi_safe_dress * ((mem.sys.H0 + V.totalPerturbation) * O_Z_dress -
        O_Z_dress * (mem.sys.H0 + V.totalPerturbation)) * Pi_safe_dress‖ ≤ δ_split ∧
    ‖Pi_safe_dress * ((mem.sys.H0 + V.totalPerturbation) * O_X_dress -
        O_X_dress * (mem.sys.H0 + V.totalPerturbation)) * Pi_safe_dress‖ ≤ δ_split
  h_oneSite_safe :
    (∀ r : ℕ, r_pert < r → ∀ A : Finset (Box3D L), V.term r A = 0) →
    let Pi_safe_dress := U_dress.1 * mem.Pi_safe * U_dress.1†
    let O_Z_dress := U_dress.1 * mem.O_dec_Z * U_dress.1†
    let O_X_dress := U_dress.1 * mem.O_dec_X * U_dress.1†
    ∀ (v : Box3D L)
      (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))),
      IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) {v} A_v →
      ‖Pi_safe_dress * (A_v * O_Z_dress - O_Z_dress * A_v) * Pi_safe_dress‖ ^ 2 ≤
        ‖A_v‖ ^ 2 * δ_split ∧
      ‖Pi_safe_dress * (A_v * O_X_dress - O_X_dress * A_v) * Pi_safe_dress‖ ^ 2 ≤
        ‖A_v‖ ^ 2 * δ_split

end
