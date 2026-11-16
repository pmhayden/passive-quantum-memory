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

import Proofs.KatoHastingsFlow.DressedCheckDriftBounds
import Proofs.DressedSafeSubspace.CouplingIntervalGapBootstrap
import Proofs.CenteredBallBHM.TwoBlockFilteredSiteOpNorms

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Safe-Pinched Rescaled Eigenvalue Bounds and Boltzmann Trace Identities

Defines two-block `safePinchedOp` and `offDiagSafeDefect` operators on the rescaled Gibbs side, proves Courant–Fischer safe-penalized rescaled failure trace bounds (`hilbertTrace_gibbsBoltzmannOp_safePinched_pullback_failure_le_rescaled`), and establishes nonnegativity of `hilbertTrace sys.P0` (`isStarProjection_P0_and_hilbertTrace_nonneg`).

## References

* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
-/

/-- Two-block pinching of an operator `A` with respect to a safe-subspace projection `Pi_safe`. -/
def safePinchedOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  Pi_safe * A * Pi_safe + (1 - Pi_safe) * A * (1 - Pi_safe)

/-- Off-diagonal safe/unsafe defect complementing `safePinchedOp Pi_safe A`. -/
def offDiagSafeDefect {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  Pi_safe * A * (1 - Pi_safe) + (1 - Pi_safe) * A * Pi_safe

theorem isSelfAdjoint_conj_of_isSelfAdjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsSelfAdjoint P) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (P * A * P) := by
  rw [IsSelfAdjoint, star_mul, star_mul, hP.star_eq, hA.star_eq, mul_assoc]

theorem isSelfAdjoint_safePinchedOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (safePinchedOp Pi_safe A) :=
  isSelfAdjoint_add
    (isSelfAdjoint_conj_of_isSelfAdjoint hPi.isSelfAdjoint hA)
    (isSelfAdjoint_conj_of_isSelfAdjoint hPi.one_sub.isSelfAdjoint hA)

theorem isSelfAdjoint_unitary_pullback {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (U.1† * H * U.1) := by
  rw [IsSelfAdjoint]
  have h_star_adj : star (U.1†) = U.1 := star_star U.1
  rw [star_mul, star_mul, hH.star_eq, h_star_adj, ← mul_assoc]
  rfl

theorem commute_safePinchedOp_proj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Commute (safePinchedOp Pi_safe A) Pi_safe := by
  rw [commute_iff_eq]; unfold safePinchedOp
  have h_idemp : Pi_safe * Pi_safe = Pi_safe := hPi.isIdempotentElem
  have h_orth1 : (1 - Pi_safe) * Pi_safe = 0 := by rw [sub_mul, one_mul, h_idemp, sub_self]
  have h_orth2 : Pi_safe * (1 - Pi_safe) = 0 := by rw [mul_sub, mul_one, h_idemp, sub_self]
  have h1 : (Pi_safe * A * Pi_safe + (1 - Pi_safe) * A * (1 - Pi_safe)) * Pi_safe =
      Pi_safe * A * Pi_safe := by
    rw [add_mul, mul_assoc (Pi_safe * A), h_idemp, mul_assoc ((1 - Pi_safe) * A),
      h_orth1, mul_zero, add_zero]
  have h2 : Pi_safe * (Pi_safe * A * Pi_safe + (1 - Pi_safe) * A * (1 - Pi_safe)) =
      Pi_safe * A * Pi_safe := by
    rw [mul_add, ← mul_assoc Pi_safe (Pi_safe * A) Pi_safe, ← mul_assoc Pi_safe Pi_safe A,
      h_idemp, ← mul_assoc Pi_safe ((1 - Pi_safe) * A) (1 - Pi_safe),
      ← mul_assoc Pi_safe (1 - Pi_safe) A, h_orth2, zero_mul, zero_mul, add_zero]
  exact h1.trans h2.symm

theorem safePinchedOp_eq_self_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe) (h_comm : Commute A Pi_safe) :
    safePinchedOp Pi_safe A = A := by
  have h_comm_eq : Pi_safe * A = A * Pi_safe := h_comm.symm.eq
  have h_comm_sub : (1 - Pi_safe) * A = A * (1 - Pi_safe) :=
    ((Commute.one_right A).sub_right h_comm).symm.eq
  have h_idemp1 : Pi_safe * Pi_safe = Pi_safe := hPi.isIdempotentElem
  have h_idemp2 : (1 - Pi_safe) * (1 - Pi_safe) = 1 - Pi_safe := hPi.one_sub.isIdempotentElem
  unfold safePinchedOp
  calc Pi_safe * A * Pi_safe + (1 - Pi_safe) * A * (1 - Pi_safe)
    _ = A * (Pi_safe * Pi_safe) + A * ((1 - Pi_safe) * (1 - Pi_safe)) := by
        rw [h_comm_eq, h_comm_sub, mul_assoc, mul_assoc]
    _ = A * Pi_safe + A * (1 - Pi_safe) := by rw [h_idemp1, h_idemp2]
    _ = A * (Pi_safe + (1 - Pi_safe)) := (mul_add A Pi_safe (1 - Pi_safe)).symm
    _ = A := by rw [add_sub_cancel, mul_one]

theorem safePinchedOp_sub {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    safePinchedOp Pi_safe (A - B) = safePinchedOp Pi_safe A - safePinchedOp Pi_safe B := by
  ext ψ; unfold safePinchedOp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, map_sub]; abel

theorem inner_safePinchedOp_eq_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ : ManyBodyHilbertSpace Site) :
    inner ℂ ψ (safePinchedOp Pi_safe A ψ) =
      inner ℂ (Pi_safe ψ) (A (Pi_safe ψ)) +
        inner ℂ ((1 - Pi_safe) ψ) (A ((1 - Pi_safe) ψ)) := by
  unfold safePinchedOp
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  have hPi_adj : Pi_safe† = Pi_safe := hPi.isSelfAdjoint.star_eq
  have hPi_sub_adj : (1 - Pi_safe)† = 1 - Pi_safe := hPi.one_sub.isSelfAdjoint.star_eq
  have h1 : inner ℂ ψ ((Pi_safe * A * Pi_safe) ψ) = inner ℂ (Pi_safe ψ) (A (Pi_safe ψ)) := by
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.adjoint_inner_left Pi_safe (A (Pi_safe ψ)) ψ, hPi_adj]
  have h2 : inner ℂ ψ (((1 - Pi_safe) * A * (1 - Pi_safe)) ψ) =
      inner ℂ ((1 - Pi_safe) ψ) (A ((1 - Pi_safe) ψ)) := by
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
      ← ContinuousLinearMap.adjoint_inner_left (1 - Pi_safe) (A ((1 - Pi_safe) ψ)) ψ, hPi_sub_adj]
  rw [h1, h2]

theorem bhm_form_bound_safePinchedOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H_pull Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe) (h_comm0 : Commute sys.H0 Pi_safe)
    {c_shift γ δ_split : ℝ}
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ ((H_pull - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
        γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2)
    (ψ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ ψ ((safePinchedOp Pi_safe H_pull - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
      γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2 := by
  have h_comm_c : Commute ((c_shift : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) Pi_safe :=
    (Commute.one_left Pi_safe).smul_left (c_shift : ℂ)
  have h_pinch_H0 : safePinchedOp Pi_safe sys.H0 = sys.H0 :=
    safePinchedOp_eq_self_of_commute hPi h_comm0
  have h_pinch_c : safePinchedOp Pi_safe ((c_shift : ℂ) • 1) = (c_shift : ℂ) • 1 :=
    safePinchedOp_eq_self_of_commute hPi h_comm_c
  have h_diff_eq :
      safePinchedOp Pi_safe H_pull - sys.H0 - (c_shift : ℂ) • 1 =
        safePinchedOp Pi_safe (H_pull - sys.H0 - (c_shift : ℂ) • 1) := by
    rw [safePinchedOp_sub, safePinchedOp_sub, h_pinch_H0, h_pinch_c]
  have h_H0_add :
      RCLike.re (inner ℂ ψ (sys.H0 ψ)) =
        RCLike.re (inner ℂ (Pi_safe ψ) (sys.H0 (Pi_safe ψ))) +
          RCLike.re (inner ℂ ((1 - Pi_safe) ψ) (sys.H0 ((1 - Pi_safe) ψ))) := by
    conv_lhs => rw [← h_pinch_H0]
    rw [inner_safePinchedOp_eq_add hPi sys.H0 ψ, map_add]
  have h_norm_add : ‖ψ‖ ^ 2 = ‖Pi_safe ψ‖ ^ 2 + ‖(1 - Pi_safe) ψ‖ ^ 2 :=
    isStarProjection_pythagorean_bhm hPi ψ
  rw [h_diff_eq, inner_safePinchedOp_eq_add hPi (H_pull - sys.H0 - (c_shift : ℂ) • 1) ψ,
    map_add, h_H0_add, h_norm_add]
  have h_tri := abs_add_le
    (RCLike.re (inner ℂ (Pi_safe ψ) ((H_pull - sys.H0 - (c_shift : ℂ) • 1) (Pi_safe ψ))))
    (RCLike.re (inner ℂ ((1 - Pi_safe) ψ) ((H_pull - sys.H0 - (c_shift : ℂ) • 1) ((1 - Pi_safe) ψ))))
  linarith [h_form (Pi_safe ψ), h_form ((1 - Pi_safe) ψ)]

theorem safePinchedOp_add_offDiagSafeDefect {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    safePinchedOp Pi_safe A + offDiagSafeDefect Pi_safe A = A := by
  unfold safePinchedOp offDiagSafeDefect
  have h1 : Pi_safe * A * Pi_safe + Pi_safe * A * (1 - Pi_safe) = Pi_safe * A := by
    rw [← mul_add, add_sub_cancel, mul_one]
  have h2 : (1 - Pi_safe) * A * (1 - Pi_safe) + (1 - Pi_safe) * A * Pi_safe = (1 - Pi_safe) * A := by
    rw [← mul_add, sub_add_cancel, mul_one]
  have h3 : Pi_safe * A + (1 - Pi_safe) * A = A := by rw [← add_mul, add_sub_cancel, one_mul]
  calc (Pi_safe * A * Pi_safe + (1 - Pi_safe) * A * (1 - Pi_safe)) +
        (Pi_safe * A * (1 - Pi_safe) + (1 - Pi_safe) * A * Pi_safe)
    _ = (Pi_safe * A * Pi_safe + Pi_safe * A * (1 - Pi_safe)) +
        ((1 - Pi_safe) * A * (1 - Pi_safe) + (1 - Pi_safe) * A * Pi_safe) := by abel
    _ = Pi_safe * A + (1 - Pi_safe) * A := by rw [h1, h2]
    _ = A := h3

theorem sub_safePinchedOp_eq_offDiagSafeDefect {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    A - safePinchedOp Pi_safe A = offDiagSafeDefect Pi_safe A :=
  eq_sub_of_add_eq' (safePinchedOp_add_offDiagSafeDefect Pi_safe A) |>.symm

theorem offDiagSafeDefect_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    offDiagSafeDefect Pi_safe (A + B) = offDiagSafeDefect Pi_safe A + offDiagSafeDefect Pi_safe B := by
  unfold offDiagSafeDefect; simp only [mul_add, add_mul]; abel

theorem offDiagSafeDefect_eq_zero_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe) (h_comm : Commute A Pi_safe) :
    offDiagSafeDefect Pi_safe A = 0 := by
  rw [← sub_safePinchedOp_eq_offDiagSafeDefect, safePinchedOp_eq_self_of_commute hPi h_comm, sub_self]

theorem offDiagSafeDefect_eq_zero_of_block_diag {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe W_tel : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hW1 : Pi_safe * W_tel * (1 - Pi_safe) = 0)
    (hW2 : (1 - Pi_safe) * W_tel * Pi_safe = 0) :
    offDiagSafeDefect Pi_safe W_tel = 0 := by
  unfold offDiagSafeDefect; rw [hW1, hW2, add_zero]

theorem offDiagSafeDefect_pullback_eq_offDiagSafeDefect_sub_effective {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe H0 W_tel H_pull : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (c_shift : ℝ) (hPi : IsStarProjection Pi_safe) (h_comm0 : Commute H0 Pi_safe)
    (hW1 : Pi_safe * W_tel * (1 - Pi_safe) = 0)
    (hW2 : (1 - Pi_safe) * W_tel * Pi_safe = 0) :
    offDiagSafeDefect Pi_safe H_pull =
      offDiagSafeDefect Pi_safe (H_pull - (H0 + W_tel) - (c_shift : ℂ) • 1) ∧
    H_pull - safePinchedOp Pi_safe H_pull =
      offDiagSafeDefect Pi_safe (H_pull - (H0 + W_tel) - (c_shift : ℂ) • 1) := by
  have h0 : offDiagSafeDefect Pi_safe H0 = 0 := offDiagSafeDefect_eq_zero_of_commute hPi h_comm0
  have hc : offDiagSafeDefect Pi_safe ((c_shift : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) = 0 :=
    offDiagSafeDefect_eq_zero_of_commute hPi ((Commute.one_left Pi_safe).smul_left (c_shift : ℂ))
  have hW : offDiagSafeDefect Pi_safe W_tel = 0 := offDiagSafeDefect_eq_zero_of_block_diag hW1 hW2
  have h_decomp :
      H_pull = H0 + (c_shift : ℂ) • 1 + W_tel + (H_pull - (H0 + W_tel) - (c_shift : ℂ) • 1) := by abel
  have h_def :
      offDiagSafeDefect Pi_safe H_pull =
        offDiagSafeDefect Pi_safe (H_pull - (H0 + W_tel) - (c_shift : ℂ) • 1) := by
    conv_lhs => rw [h_decomp]
    rw [offDiagSafeDefect_add, offDiagSafeDefect_add, offDiagSafeDefect_add,
      h0, hc, hW, zero_add, zero_add, zero_add]
  exact ⟨h_def, by rw [sub_safePinchedOp_eq_offDiagSafeDefect, h_def]⟩

lemma norm_opEigenbasis_le_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ω : ManyBodyConfig Site) :
    RCLike.re (inner ℂ (opEigenbasis H hH ω) (opEigenbasis H hH ω)) = 1 ∧
      ‖opEigenbasis H hH ω‖ ≤ 1 := by
  have h_onb := opEigenbasis_orthonormal H hH ω ω
  rw [if_pos rfl] at h_onb
  have h_re : RCLike.re (inner ℂ (opEigenbasis H hH ω) (opEigenbasis H hH ω)) = 1 := by
    rw [h_onb, RCLike.one_re]
  have h_sq : ‖opEigenbasis H hH ω‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), h_re]
  refine ⟨h_re, ?_⟩; nlinarith [norm_nonneg (opEigenbasis H hH ω)]

theorem gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    {φ : ManyBodyHilbertSpace Site} {E : ℝ} (h_eig : H φ = (E : ℂ) • φ) (β : ℝ) :
    gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β φ =
      (Real.exp (-β * E) : ℂ) • φ := by
  have h_id := onb_sum_ketBra_eq_one (opEigenbasis H hH)
    (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
  have hφ_sum : φ = ∑ ω' : ManyBodyConfig Site, rankOneKetBra (opEigenbasis H hH ω') φ := by
    calc φ = (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) φ := rfl
      _ = (∑ ω' : ManyBodyConfig Site, rankOneKetBra (opEigenbasis H hH ω')) φ := by rw [h_id]
      _ = ∑ ω' : ManyBodyConfig Site, rankOneKetBra (opEigenbasis H hH ω') φ :=
          ContinuousLinearMap.sum_apply _ _ _
  have hφ_smul : (Real.exp (-β * E) : ℂ) • φ =
      ∑ ω' : ManyBodyConfig Site,
        (Real.exp (-β * E) : ℂ) • rankOneKetBra (opEigenbasis H hH ω') φ :=
    (congrArg ((Real.exp (-β * E) : ℂ) • ·) hφ_sum).trans Finset.smul_sum
  unfold gibbsBoltzmannOp
  rw [ContinuousLinearMap.sum_apply, hφ_smul]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [ContinuousLinearMap.smul_apply]
  have h_ket := congrFun (congrArg DFunLike.coe (opEigenbasis_ketBra_props H hH ω').2.1) φ
  change rankOneKetBra (opEigenbasis H hH ω') (H φ) =
    (opEigenvalues H hH ω' : ℂ) • rankOneKetBra (opEigenbasis H hH ω') φ at h_ket
  rw [h_eig, map_smul] at h_ket
  have h_sub : ((opEigenvalues H hH ω' : ℂ) - (E : ℂ)) •
      rankOneKetBra (opEigenbasis H hH ω') φ = 0 := by rw [sub_smul, ← h_ket, sub_self]
  rcases smul_eq_zero.mp h_sub with h_ev | h_zero
  · rw [Complex.ofReal_injective (sub_eq_zero.mp h_ev)]
  · rw [h_zero, smul_zero, smul_zero]

theorem gibbsBoltzmannOp_apply_of_orthonormal_at {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ_alt : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_alt : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (β : ℝ) (ω : ManyBodyConfig Site) :
    gibbsBoltzmannOp ψ_alt E_alt β (ψ_alt ω) = (Real.exp (-β * E_alt ω) : ℂ) • ψ_alt ω := by
  unfold gibbsBoltzmannOp
  rw [ContinuousLinearMap.sum_apply, Finset.sum_eq_single ω]
  · rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, h_onb ω ω, if_pos rfl, one_smul]
  · intro ω' _ hne
    rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, h_onb ω' ω, if_neg hne,
      zero_smul, smul_zero]
  · intro h_not_mem; exact False.elim (h_not_mem (Finset.mem_univ ω))

theorem gibbsBoltzmannOp_eq_of_any_orthonormal_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ψ_alt : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_alt : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_eig : ∀ ω, H (ψ_alt ω) = (E_alt ω : ℂ) • ψ_alt ω) (β : ℝ) :
    gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β =
      gibbsBoltzmannOp ψ_alt E_alt β := by
  have h_ortho : Orthonormal ℂ ψ_alt := orthonormal_iff_ite.mpr h_onb
  have h_card : Fintype.card (ManyBodyConfig Site) =
      Module.finrank ℂ (ManyBodyHilbertSpace Site) := by
    rw [Fintype.card_congr (configFinEquiv Site), Fintype.card_fin]
  let b_alt : Module.Basis (ManyBodyConfig Site) ℂ (ManyBodyHilbertSpace Site) :=
    Module.Basis.mk h_ortho.linearIndependent
      (h_ortho.linearIndependent.span_eq_top_of_card_eq_finrank' h_card).ge
  apply ContinuousLinearMap.coe_inj.mp; apply b_alt.ext; intro ω
  have hb_ω : b_alt ω = ψ_alt ω := by dsimp [b_alt]; rw [Module.Basis.coe_mk]
  change gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β (b_alt ω) =
    gibbsBoltzmannOp ψ_alt E_alt β (b_alt ω)
  rw [hb_ω, gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector H hH (h_eig ω) β,
    gibbsBoltzmannOp_apply_of_orthonormal_at ψ_alt E_alt h_onb β ω]

theorem hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ψ_alt : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_alt : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_eig : ∀ ω, H (ψ_alt ω) = (E_alt ω : ℂ) • ψ_alt ω) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * A) =
      ∑ ω : ManyBodyConfig Site,
        Real.exp (-β * E_alt ω) * RCLike.re (inner ℂ (ψ_alt ω) (A (ψ_alt ω))) := by
  rw [gibbsBoltzmannOp_eq_of_any_orthonormal_eigenbasis H hH ψ_alt E_alt h_onb h_eig β,
    hilbertTrace_gibbsBoltzmannOp_mul_eq]

theorem hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * 1) =
      gibbsPartitionZ (opEigenvalues H hH) β := by
  rw [hilbertTrace_gibbsBoltzmannOp_mul_eq, gibbsPartitionZ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.one_apply, (norm_opEigenbasis_le_one H hH ω).1, mul_one]

theorem gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ψ_alt : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_alt : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_eig : ∀ ω, H (ψ_alt ω) = (E_alt ω : ℂ) • ψ_alt ω) (β : ℝ) :
    gibbsPartitionZ (opEigenvalues H hH) β = gibbsPartitionZ E_alt β := by
  rw [← hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ H hH β,
    hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis H hH ψ_alt E_alt h_onb h_eig β 1,
    gibbsPartitionZ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.one_apply, h_onb ω ω, if_pos rfl, RCLike.one_re, mul_one]

theorem orthonormal_unitary_pullback_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ω₁ ω₂ : ManyBodyConfig Site) :
    inner ℂ ((U.1†) (opEigenbasis H hH ω₁)) ((U.1†) (opEigenbasis H hH ω₂)) =
      if ω₁ = ω₂ then (1 : ℂ) else 0 := by
  have hU_self_star : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  calc inner ℂ ((U.1†) (opEigenbasis H hH ω₁)) ((U.1†) (opEigenbasis H hH ω₂))
    _ = inner ℂ (opEigenbasis H hH ω₁) (U.1 ((U.1†) (opEigenbasis H hH ω₂))) :=
        ContinuousLinearMap.adjoint_inner_left U.1
          ((U.1†) (opEigenbasis H hH ω₂)) (opEigenbasis H hH ω₁)
    _ = inner ℂ (opEigenbasis H hH ω₁) ((U.1 * U.1†) (opEigenbasis H hH ω₂)) := by
        rw [← ContinuousLinearMap.mul_apply]
    _ = if ω₁ = ω₂ then (1 : ℂ) else 0 := by
        rw [hU_self_star, ContinuousLinearMap.one_apply, opEigenbasis_orthonormal H hH ω₁ ω₂]

theorem eigenvalue_eq_unitary_pullback_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ω : ManyBodyConfig Site) :
    (U.1† * H * U.1) ((U.1†) (opEigenbasis H hH ω)) =
      (opEigenvalues H hH ω : ℂ) • ((U.1†) (opEigenbasis H hH ω)) := by
  have hU_self_star : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  calc (U.1† * H * U.1) ((U.1†) (opEigenbasis H hH ω))
    _ = (U.1†) (H ((U.1 * U.1†) (opEigenbasis H hH ω))) := by
        rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
          ← ContinuousLinearMap.mul_apply U.1 (U.1†)]
    _ = (opEigenvalues H hH ω : ℂ) • ((U.1†) (opEigenbasis H hH ω)) := by
        rw [hU_self_star, ContinuousLinearMap.one_apply, opEigenbasis_apply_H H hH ω, map_smul]

theorem hilbertTrace_gibbsBoltzmannOp_unitary_pullback_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (hH_pull : IsSelfAdjoint (U.1† * H * U.1)) (β : ℝ)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis (U.1† * H * U.1) hH_pull)
      (opEigenvalues (U.1† * H * U.1) hH_pull) β * M) =
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
      (U.1 * M * U.1†)) := by
  rw [hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
        (U.1† * H * U.1) hH_pull (fun ω => (U.1†) (opEigenbasis H hH ω)) (opEigenvalues H hH)
        (orthonormal_unitary_pullback_eigenbasis U H hH)
        (eigenvalue_eq_unitary_pullback_eigenbasis U H hH) β M,
      hilbertTrace_gibbsBoltzmannOp_mul_eq]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h_inner :
      inner ℂ ((U.1†) (opEigenbasis H hH ω)) (M ((U.1†) (opEigenbasis H hH ω))) =
        inner ℂ (opEigenbasis H hH ω) ((U.1 * M * U.1†) (opEigenbasis H hH ω)) := by
    rw [ContinuousLinearMap.adjoint_inner_left U.1
          (M ((U.1†) (opEigenbasis H hH ω))) (opEigenbasis H hH ω),
        ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply]
  rw [h_inner]

theorem hilbertTrace_gibbsBoltzmannOp_dressed_failure_eq_pullback_bare_failure {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H_pert Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pert : IsSelfAdjoint H_pert)
    (hH_pull : IsSelfAdjoint (U_dress.1† * H_pert * U_dress.1)) (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pert hH_pert)
      (opEigenvalues H_pert hH_pert) β * (1 - (U_dress.1 * Pi_safe * U_dress.1†))) =
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis (U_dress.1† * H_pert * U_dress.1) hH_pull)
      (opEigenvalues (U_dress.1† * H_pert * U_dress.1) hH_pull) β * (1 - Pi_safe)) := by
  rw [hilbertTrace_gibbsBoltzmannOp_unitary_pullback_eq
    U_dress H_pert hH_pert hH_pull β (1 - Pi_safe)]
  have hU_self_star : U_dress.1 * U_dress.1† = 1 := Unitary.coe_mul_star_self U_dress
  have h_conj : U_dress.1 * (1 - Pi_safe) * U_dress.1† = 1 - (U_dress.1 * Pi_safe * U_dress.1†) := by
    rw [mul_sub, sub_mul, mul_one, hU_self_star]
  rw [h_conj]

theorem gibbsPartitionZ_unitary_pullback_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H_pert : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pert : IsSelfAdjoint H_pert)
    (hH_pull : IsSelfAdjoint (U_dress.1† * H_pert * U_dress.1)) (β : ℝ) :
    gibbsPartitionZ (opEigenvalues (U_dress.1† * H_pert * U_dress.1) hH_pull) β =
      gibbsPartitionZ (opEigenvalues H_pert hH_pert) β :=
  gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis
    (U_dress.1† * H_pert * U_dress.1) hH_pull
    (fun ω => (U_dress.1†) (opEigenbasis H_pert hH_pert ω)) (opEigenvalues H_pert hH_pert)
    (orthonormal_unitary_pullback_eigenbasis U_dress H_pert hH_pert)
    (eigenvalue_eq_unitary_pullback_eigenbasis U_dress H_pert hH_pert) β

lemma isSelfAdjoint_add_real_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H) (hP : IsSelfAdjoint P) (M : ℝ) :
    IsSelfAdjoint (H + (M : ℂ) • P) := by
  refine isSelfAdjoint_add hH ?_
  rw [IsSelfAdjoint, star_smul, RCLike.star_def, Complex.conj_ofReal, hP.star_eq]

private lemma abs_eigenvalue_le_opNorm_of_ne_zero_rescaled {D L : ℕ}
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

theorem penalized_eigenbasis_dichotomy_of_commute_proj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P) (h_comm : Commute H P)
    {M : ℝ} (hM : 2 * ‖H‖ < M) (ω : ManyBodyConfig Site) :
    let hH_pen := isSelfAdjoint_add_real_smul hH hP.isSelfAdjoint M
    let ψ := opEigenbasis (H + (M : ℂ) • P) hH_pen ω
    let μ := opEigenvalues (H + (M : ℂ) • P) hH_pen ω
    (P ψ = 0 ∧ H ψ = (μ : ℂ) • ψ ∧
      RCLike.re (inner ℂ ψ ((1 - P) ψ)) = 1 ∧ μ ≤ ‖H‖) ∨
    ((1 - P) ψ = 0 ∧ H ψ = ((μ - M : ℝ) : ℂ) • ψ ∧
      RCLike.re (inner ℂ ψ ((1 - P) ψ)) = 0 ∧ M - ‖H‖ ≤ μ) := by
  intro hH_pen ψ μ
  have h_eig : (H + (M : ℂ) • P) ψ = (μ : ℂ) • ψ := opEigenbasis_apply_H _ hH_pen ω
  have h_re_one : RCLike.re (inner ℂ ψ ψ) = 1 := (norm_opEigenbasis_le_one _ hH_pen ω).1
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
    have h_comm_P : P (H ψ) = H (P ψ) := by change (P * H) ψ = (H * P) ψ; rw [h_comm.symm.eq]
    have h_idem : P (P ψ) = P ψ := by change (P * P) ψ = P ψ; rw [hP.isIdempotentElem.eq]
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
      le_trans (le_abs_self μ) (abs_eigenvalue_le_opNorm_of_ne_zero_rescaled H hψ_ne h_one_sub)
    rw [h1Pψ] at h_one_sub
    refine ⟨hPψ, h_one_sub, ?_, hμ_le⟩
    change RCLike.re (inner ℂ ψ (Q ψ)) = 1; rw [h1Pψ, h_re_one]
  · right
    have hμ_ge : M - ‖H‖ ≤ μ := by
      have h_abs := abs_eigenvalue_le_opNorm_of_ne_zero_rescaled H hPψ h_proj
      linarith [(abs_le.mp h_abs).1]
    have h1Pψ : Q ψ = 0 := by
      by_contra h_ne
      have h_abs := abs_eigenvalue_le_opNorm_of_ne_zero_rescaled H h_ne h_one_sub
      linarith [(abs_le.mp h_abs).2]
    have hPψ_eq : P ψ = ψ := by
      have h_sub : ψ - P ψ = 0 := by simpa [Q, ContinuousLinearMap.sub_apply] using h1Pψ
      exact (sub_eq_zero.mp h_sub).symm
    rw [hPψ_eq] at h_proj
    refine ⟨h1Pψ, h_proj, ?_, hμ_ge⟩
    change RCLike.re (inner ℂ ψ (Q ψ)) = 0; rw [h1Pψ, inner_zero_right, map_zero]

theorem hilbertTrace_gibbsBoltzmannOp_one_sub_proj_eq_penalized {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (hP : IsStarProjection P) (h_comm : Commute H P)
    {M : ℝ} (hM : 2 * ‖H‖ < M) (β : ℝ) :
    let hH_pen := isSelfAdjoint_add_real_smul hH hP.isSelfAdjoint M
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
    rcases penalized_eigenbasis_dichotomy_of_commute_proj H P hH hP h_comm hM ω with h_ker | h_ran
    · dsimp only [E_true]; rw [if_pos h_ker.1]; exact h_ker.2.1
    · have hP_ne : P (ψ_pen ω) ≠ 0 := by
        intro hP0
        have h_zero : ψ_pen ω = 0 := by
          have h1 : (1 - P) (ψ_pen ω) = 0 := h_ran.1
          rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hP0, sub_zero] at h1
          exact h1
        have h_re : RCLike.re (inner ℂ (ψ_pen ω) (ψ_pen ω)) = 1 :=
          (norm_opEigenbasis_le_one (H + (M : ℂ) • P) hH_pen ω).1
        rw [h_zero, inner_zero_right, map_zero] at h_re; norm_num at h_re
      dsimp only [E_true]; rw [if_neg hP_ne]; exact h_ran.2.1
  rw [hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
    H hH ψ_pen E_true (opEigenbasis_orthonormal _ hH_pen) h_eig_true β (1 - P)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rcases penalized_eigenbasis_dichotomy_of_commute_proj H P hH hP h_comm hM ω with h_ker | h_ran
  · dsimp only [E_true]; rw [if_pos h_ker.1]
  · change Real.exp (-β * E_true ω) * RCLike.re (inner ℂ (ψ_pen ω) ((1 - P) (ψ_pen ω))) =
      Real.exp (-β * μ_pen ω) * RCLike.re (inner ℂ (ψ_pen ω) ((1 - P) (ψ_pen ω)))
    rw [h_ran.2.2.1, mul_zero, mul_zero]

private lemma opEigenvalues_lower_bound_of_rescaled_form {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {c_shift δ_split : ℝ}
    (h_low_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      (c_shift - (1 / 2 : ℝ) * δ_split) * ‖ϕ‖ ^ 2 +
        (3 / 4 : ℝ) * RCLike.re (inner ℂ ϕ (A ϕ)) ≤
      RCLike.re (inner ℂ ϕ (B ϕ)))
    (ω : ManyBodyConfig Site) :
    c_shift + (3 / 4 : ℝ) * opEigenvalues A hA ω - (1 / 2 : ℝ) * δ_split ≤
      opEigenvalues B hB ω := by
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
  have h_A_ge : opEigenvalues A hA ω * ‖ϕ‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ (A ϕ)) := by
    apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow A hA i.1
      (sortedEigenvalues A hA i) _ hϕ_orth
    intro j hj; exact sortedEigenvalues_monotone_bhm A hA hj
  have h_B_le : RCLike.re (inner ℂ ϕ (B ϕ)) ≤ opEigenvalues B hB ω * ‖ϕ‖ ^ 2 := by
    apply re_inner_apply_H_le_of_mem_eigenSpanBelow B hB (i.1 + 1)
      (sortedEigenvalues B hB i) _ hϕU
    intro j hj; exact sortedEigenvalues_monotone_bhm B hB (Nat.lt_succ_iff.mp hj)
  have hb := h_low_form ϕ
  have h_le :
      (c_shift + (3 / 4 : ℝ) * opEigenvalues A hA ω - (1 / 2 : ℝ) * δ_split) * ‖ϕ‖ ^ 2 ≤
        opEigenvalues B hB ω * ‖ϕ‖ ^ 2 := by linarith
  exact le_of_mul_le_mul_right h_le (sq_pos_of_pos (norm_pos_iff.mpr hϕ_ne))

/-- **Unconditional Rescaled $\frac{3}{4}\beta$ Failure Trace Bound for Safe-Pinched Pullback
Hamiltonian (`hilbertTrace_gibbsBoltzmannOp_safePinched_pullback_failure_le_rescaled`)**. -/
theorem hilbertTrace_gibbsBoltzmannOp_safePinched_pullback_failure_le_rescaled {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H_pull Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pull : IsSelfAdjoint H_pull)
    (hPi : IsStarProjection Pi_safe) (h_comm0 : Commute sys.H0 Pi_safe)
    {c_shift δ_split β : ℝ} (hβ : 0 ≤ β)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ ((H_pull - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    hilbertTrace (gibbsBoltzmannOp
      (opEigenbasis (safePinchedOp Pi_safe H_pull) (isSelfAdjoint_safePinchedOp hPi hH_pull))
      (opEigenvalues (safePinchedOp Pi_safe H_pull) (isSelfAdjoint_safePinchedOp hPi hH_pull))
      β * (1 - Pi_safe)) ≤
    Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) *
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((3 / 4 : ℝ) * β) * (1 - Pi_safe)) := by
  let H_pinch := safePinchedOp Pi_safe H_pull
  let hH_pinch := isSelfAdjoint_safePinchedOp hPi hH_pull
  have h_comm_pinch : Commute H_pinch Pi_safe := commute_safePinchedOp_proj hPi H_pull
  have h_form_pinch := bhm_form_bound_safePinchedOp sys H_pull Pi_safe hPi h_comm0 h_form
  let M : ℝ := 4 * (‖sys.H0‖ + ‖H_pinch‖ + |c_shift| + |δ_split| + 1)
  have hH0_nn : 0 ≤ ‖sys.H0‖ := norm_nonneg _
  have hHp_nn : 0 ≤ ‖H_pinch‖ := norm_nonneg _
  have hc_nn : 0 ≤ |c_shift| := abs_nonneg _
  have hδ_nn : 0 ≤ |δ_split| := abs_nonneg _
  have hM0 : 2 * ‖sys.H0‖ < M := by dsimp [M]; linarith
  have hM_pert : 2 * ‖H_pinch‖ < (3 / 4 : ℝ) * M := by dsimp [M]; linarith
  let hH0_pen := isSelfAdjoint_add_real_smul sys.isSelfAdjoint_H0 hPi.isSelfAdjoint M
  let hHp_pen := isSelfAdjoint_add_real_smul hH_pinch hPi.isSelfAdjoint ((3 / 4 : ℝ) * M)
  rw [hilbertTrace_gibbsBoltzmannOp_one_sub_proj_eq_penalized
        H_pinch Pi_safe hH_pinch hPi h_comm_pinch hM_pert β,
      hilbertTrace_gibbsBoltzmannOp_one_sub_proj_eq_penalized
        sys.H0 Pi_safe sys.isSelfAdjoint_H0 hPi h_comm0 hM0 ((3 / 4 : ℝ) * β),
      Finset.mul_sum]
  have h_pen_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      (c_shift - (1 / 2 : ℝ) * δ_split) * ‖ϕ‖ ^ 2 +
        (3 / 4 : ℝ) * RCLike.re (inner ℂ ϕ ((sys.H0 + (M : ℂ) • Pi_safe) ϕ)) ≤
      RCLike.re (inner ℂ ϕ ((H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) ϕ)) := by
    intro ϕ
    have h_low := (abs_le.mp (h_form_pinch ϕ)).1
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one] at h_low
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right, map_add, re_ofReal_mul,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right, map_add, re_ofReal_mul]
    linarith
  refine Finset.sum_le_sum fun ω _ => ?_
  have h_cf := opEigenvalues_lower_bound_of_rescaled_form
    (sys.H0 + (M : ℂ) • Pi_safe) (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe)
    hH0_pen hHp_pen h_pen_form ω
  rcases penalized_eigenbasis_dichotomy_of_commute_proj
      sys.H0 Pi_safe sys.isSelfAdjoint_H0 hPi h_comm0 hM0 ω with h0_ker | h0_ran
  · have h_p_le_one :
        RCLike.re (inner ℂ (opEigenbasis (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω)
          ((1 - Pi_safe)
            (opEigenbasis (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω))) ≤ 1 := by
      rcases penalized_eigenbasis_dichotomy_of_commute_proj
          H_pinch Pi_safe hH_pinch hPi h_comm_pinch hM_pert ω with hp_ker | hp_ran
      · linarith [hp_ker.2.2.1]
      · linarith [hp_ran.2.2.1]
    rw [h0_ker.2.2.1, mul_one]
    have h_exp_le :
        Real.exp (-β * opEigenvalues (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω) ≤
        Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) *
          Real.exp (-((3 / 4 : ℝ) * β) *
            opEigenvalues (sys.H0 + (M : ℂ) • Pi_safe) hH0_pen ω) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [h_cf])
    calc Real.exp (-β * opEigenvalues (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω) *
          RCLike.re (inner ℂ (opEigenbasis (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω)
            ((1 - Pi_safe)
              (opEigenbasis (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω)))
      _ ≤ Real.exp (-β * opEigenvalues (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω) * 1 :=
          mul_le_mul_of_nonneg_left h_p_le_one (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-β * opEigenvalues (H_pinch + (((3 / 4 : ℝ) * M : ℝ) : ℂ) • Pi_safe) hHp_pen ω) :=
          mul_one _
      _ ≤ Real.exp (-β * c_shift + (1 / 2 : ℝ) * β * δ_split) *
            Real.exp (-((3 / 4 : ℝ) * β) *
              opEigenvalues (sys.H0 + (M : ℂ) • Pi_safe) hH0_pen ω) := h_exp_le
  · rcases penalized_eigenbasis_dichotomy_of_commute_proj
        H_pinch Pi_safe hH_pinch hPi h_comm_pinch hM_pert ω with hp_ker | hp_ran
    · exfalso
      have h0_ge := h0_ran.2.2.2; have hp_le := hp_ker.2.2.2
      have h_c : -|c_shift| ≤ c_shift := neg_abs_le c_shift
      have h_d : δ_split ≤ |δ_split| := le_abs_self δ_split
      dsimp [M] at h0_ge h_cf; linarith
    · rw [hp_ran.2.2.1, h0_ran.2.2.1, mul_zero, mul_zero, mul_zero]

theorem isStarProjection_P0_and_hilbertTrace_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    IsStarProjection sys.P0 ∧ 0 ≤ hilbertTrace sys.P0 := by
  have hP0 : IsStarProjection sys.P0 := sys.isStarProjection_P0
  refine ⟨hP0, ?_⟩
  rw [hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 sys.P0]
  exact Finset.sum_nonneg fun ω _ => hP0.re_inner_nonneg _

end
