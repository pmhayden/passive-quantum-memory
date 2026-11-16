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

import Proofs.DressedThermalDuhamel.PerturbedKMSBallImmunitySynthesis
import Proofs.DressedSyndromeGibbs.DressedGibbsFailureBridge
import Proofs.DressedSyndromeGibbs.DressedKMSGronwallTrajectory
import Proofs.CubeTelescoping.SpectralAlignmentUnitary

/-!
# Two-Block Safe-Subspace Pinching and Unitary Pullback Trace Invariance

Defines the two-block safe-subspace pinching `perturbedSafePinchedOp` and off-diagonal defect `perturbedOffDiagSafeDefect`, proving zero-loss preservation of the BHM relative form bound under pinching. Establishes orthonormal eigenbasis decompositions and unitary-pullback invariance of Gibbs traces and partition functions.

## References

* Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option maxRecDepth 200000
set_option linter.unusedVariables false

/-! ## 1. Safe-Subspace Two-Block Pinching & Zero-Loss BHM Form Bound Preservation -/

/-- Two-block pinching of an operator `A` with respect to a safe-subspace projection `Pi_safe`:
$$\mathcal{C}_{\Pi_{\mathrm{safe}}}(A) := \Pi_{\mathrm{safe}} A \Pi_{\mathrm{safe}} + (1 - \Pi_{\mathrm{safe}}) A (1 - \Pi_{\mathrm{safe}}).$$ -/
abbrev perturbedSafePinchedOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  Pi_safe * A * Pi_safe + (1 - Pi_safe) * A * (1 - Pi_safe)

/-- Off-diagonal safe/unsafe block defect complementing `perturbed_safePinchedOp Pi_safe A`:
$$\mathcal{O}_{\Pi_{\mathrm{safe}}}(A) := \Pi_{\mathrm{safe}} A (1 - \Pi_{\mathrm{safe}}) + (1 - \Pi_{\mathrm{safe}}) A \Pi_{\mathrm{safe}}.$$ -/
abbrev perturbedOffDiagSafeDefect {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  Pi_safe * A * (1 - Pi_safe) + (1 - Pi_safe) * A * Pi_safe

/-- Conjugation of a self-adjoint operator `A` by a self-adjoint operator `P` is self-adjoint. -/
theorem perturbed_isSelfAdjoint_conj_of_isSelfAdjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsSelfAdjoint P) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (P * A * P) := by
  rw [IsSelfAdjoint, star_mul, star_mul, hP.star_eq, hA.star_eq, mul_assoc]

/-- `perturbed_safePinchedOp Pi_safe A` is self-adjoint whenever `Pi_safe` is a star projection and
`A` is self-adjoint. -/
theorem perturbed_isSelfAdjoint_safePinchedOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (perturbedSafePinchedOp Pi_safe A) :=
  isSelfAdjoint_add
    (perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hPi.isSelfAdjoint hA)
    (perturbed_isSelfAdjoint_conj_of_isSelfAdjoint hPi.one_sub.isSelfAdjoint hA)

/-- Pullback `U.1† * H * U.1` of a self-adjoint operator `H` by a unitary `U` is self-adjoint. -/
theorem perturbed_isSelfAdjoint_unitary_pullback {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (U.1† * H * U.1) := by
  rw [IsSelfAdjoint]
  have h_star_adj : star (U.1†) = U.1 := star_star U.1
  rw [star_mul, star_mul, hH.star_eq, h_star_adj, ← mul_assoc]
  rfl

/-- Pushforward `U.1 * H * U.1†` of a self-adjoint operator `H` by a unitary `U` is self-adjoint. -/
theorem perturbed_isSelfAdjoint_unitary_pushforward {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H) :
    IsSelfAdjoint (U.1 * H * U.1†) := by
  rw [IsSelfAdjoint]
  have h_star_adj : star (U.1†) = U.1 := star_star U.1
  rw [star_mul, star_mul, hH.star_eq, h_star_adj, ← mul_assoc]
  rfl

/-- Unconditional commutation of `perturbed_safePinchedOp Pi_safe A` with `Pi_safe`. -/
theorem perturbed_commute_safePinchedOp_proj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Commute (perturbedSafePinchedOp Pi_safe A) Pi_safe := by
  rw [commute_iff_eq]; unfold perturbedSafePinchedOp
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

/-- Any operator `A` that commutes with `Pi_safe` is a fixed point of `perturbed_safePinchedOp Pi_safe`. -/
theorem perturbed_safePinchedOp_eq_self_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe) (h_comm : Commute A Pi_safe) :
    perturbedSafePinchedOp Pi_safe A = A := by
  have h_comm_eq : Pi_safe * A = A * Pi_safe := h_comm.symm.eq
  have h_comm_sub : (1 - Pi_safe) * A = A * (1 - Pi_safe) :=
    ((Commute.one_right A).sub_right h_comm).symm.eq
  have h_idemp1 : Pi_safe * Pi_safe = Pi_safe := hPi.isIdempotentElem
  have h_idemp2 : (1 - Pi_safe) * (1 - Pi_safe) = 1 - Pi_safe := hPi.one_sub.isIdempotentElem
  unfold perturbedSafePinchedOp
  calc Pi_safe * A * Pi_safe + (1 - Pi_safe) * A * (1 - Pi_safe)
    _ = A * (Pi_safe * Pi_safe) + A * ((1 - Pi_safe) * (1 - Pi_safe)) := by
        rw [h_comm_eq, h_comm_sub, mul_assoc, mul_assoc]
    _ = A * Pi_safe + A * (1 - Pi_safe) := by rw [h_idemp1, h_idemp2]
    _ = A * (Pi_safe + (1 - Pi_safe)) := (mul_add A Pi_safe (1 - Pi_safe)).symm
    _ = A := by rw [add_sub_cancel, mul_one]

/-- Linearity of `perturbed_safePinchedOp Pi_safe` over subtraction. -/
theorem perturbed_safePinchedOp_sub {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    perturbedSafePinchedOp Pi_safe (A - B) =
      perturbedSafePinchedOp Pi_safe A - perturbedSafePinchedOp Pi_safe B := by
  ext ψ; unfold perturbedSafePinchedOp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.mul_apply, map_sub]
  abel

/-- Quadratic form decomposition of `perturbed_safePinchedOp Pi_safe A`. -/
theorem perturbed_inner_safePinchedOp_eq_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ : ManyBodyHilbertSpace Site) :
    inner ℂ ψ (perturbedSafePinchedOp Pi_safe A ψ) =
      inner ℂ (Pi_safe ψ) (A (Pi_safe ψ)) +
        inner ℂ ((1 - Pi_safe) ψ) (A ((1 - Pi_safe) ψ)) := by
  unfold perturbedSafePinchedOp
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  have hPi_adj : Pi_safe† = Pi_safe := hPi.isSelfAdjoint.star_eq
  have hPi_sub_adj : (1 - Pi_safe)† = 1 - Pi_safe := hPi.one_sub.isSelfAdjoint.star_eq
  have h1 : inner ℂ ψ ((Pi_safe * A * Pi_safe) ψ) = inner ℂ (Pi_safe ψ) (A (Pi_safe ψ)) := by
    calc inner ℂ ψ ((Pi_safe * A * Pi_safe) ψ)
      _ = inner ℂ ψ (Pi_safe (A (Pi_safe ψ))) := rfl
      _ = inner ℂ ((Pi_safe†) ψ) (A (Pi_safe ψ)) :=
          (ContinuousLinearMap.adjoint_inner_left Pi_safe (A (Pi_safe ψ)) ψ).symm
      _ = inner ℂ (Pi_safe ψ) (A (Pi_safe ψ)) := by rw [hPi_adj]
  have h2 : inner ℂ ψ (((1 - Pi_safe) * A * (1 - Pi_safe)) ψ) =
      inner ℂ ((1 - Pi_safe) ψ) (A ((1 - Pi_safe) ψ)) := by
    calc inner ℂ ψ (((1 - Pi_safe) * A * (1 - Pi_safe)) ψ)
      _ = inner ℂ ψ ((1 - Pi_safe) (A ((1 - Pi_safe) ψ))) := rfl
      _ = inner ℂ (((1 - Pi_safe)†) ψ) (A ((1 - Pi_safe) ψ)) :=
          (ContinuousLinearMap.adjoint_inner_left (1 - Pi_safe) (A ((1 - Pi_safe) ψ)) ψ).symm
      _ = inner ℂ ((1 - Pi_safe) ψ) (A ((1 - Pi_safe) ψ)) := by rw [hPi_sub_adj]
  rw [h1, h2]

/-- **Zero-Loss BHM Relative Form Bound Preservation under Safe-Projector Pinching
(`perturbed_bhm_form_bound_safePinchedOp`)**:
If `H_pull` satisfies the BHM relative form bound with constants `(γ, δ_split / 2)` relative to
`sys.H0` and `Commute sys.H0 Pi_safe`, then `perturbed_safePinchedOp Pi_safe H_pull` satisfies the
exact same BHM relative form bound with the exact same constants `(γ, δ_split / 2)`. -/
theorem perturbed_bhm_form_bound_safePinchedOp {D L : ℕ}
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
    |RCLike.re (inner ℂ ψ ((perturbedSafePinchedOp Pi_safe H_pull - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
      γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2 := by
  have h_comm_c :
      Commute ((c_shift : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) Pi_safe :=
    (Commute.one_left Pi_safe).smul_left (c_shift : ℂ)
  have h_pinch_H0 : perturbedSafePinchedOp Pi_safe sys.H0 = sys.H0 :=
    perturbed_safePinchedOp_eq_self_of_commute hPi h_comm0
  have h_pinch_c : perturbedSafePinchedOp Pi_safe ((c_shift : ℂ) • 1) = (c_shift : ℂ) • 1 :=
    perturbed_safePinchedOp_eq_self_of_commute hPi h_comm_c
  have h_diff_eq :
      perturbedSafePinchedOp Pi_safe H_pull - sys.H0 - (c_shift : ℂ) • 1 =
        perturbedSafePinchedOp Pi_safe (H_pull - sys.H0 - (c_shift : ℂ) • 1) := by
    rw [perturbed_safePinchedOp_sub, perturbed_safePinchedOp_sub, h_pinch_H0, h_pinch_c]
  have h_H0_add :
      RCLike.re (inner ℂ ψ (sys.H0 ψ)) =
        RCLike.re (inner ℂ (Pi_safe ψ) (sys.H0 (Pi_safe ψ))) +
          RCLike.re (inner ℂ ((1 - Pi_safe) ψ) (sys.H0 ((1 - Pi_safe) ψ))) := by
    conv_lhs => rw [← h_pinch_H0]
    rw [perturbed_inner_safePinchedOp_eq_add hPi sys.H0 ψ, map_add]
  have h_norm_add : ‖ψ‖ ^ 2 = ‖Pi_safe ψ‖ ^ 2 + ‖(1 - Pi_safe) ψ‖ ^ 2 :=
    isStarProjection_pythagorean hPi ψ
  rw [h_diff_eq, perturbed_inner_safePinchedOp_eq_add hPi (H_pull - sys.H0 - (c_shift : ℂ) • 1) ψ,
    map_add, h_H0_add, h_norm_add]
  have h_tri := abs_add_le
    (RCLike.re (inner ℂ (Pi_safe ψ) ((H_pull - sys.H0 - (c_shift : ℂ) • 1) (Pi_safe ψ))))
    (RCLike.re (inner ℂ ((1 - Pi_safe) ψ) ((H_pull - sys.H0 - (c_shift : ℂ) • 1) ((1 - Pi_safe) ψ))))
  have h_f1 := h_form (Pi_safe ψ); have h_f2 := h_form ((1 - Pi_safe) ψ)
  linarith

/-! ## 2. Orthonormal Eigenbasis & Unitary Pullback Invariance of Boltzmann Traces -/

/-- Action of `gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β` on any eigenvector `φ`
of `H` with eigenvalue `E`. -/
theorem perturbed_gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector {D L : ℕ}
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
      rankOneKetBra (opEigenbasis H hH ω') φ = 0 := by
    rw [sub_smul, ← h_ket, sub_self]
  rcases smul_eq_zero.mp h_sub with h_ev | h_zero
  · rw [Complex.ofReal_injective (sub_eq_zero.mp h_ev)]
  · rw [h_zero, smul_zero, smul_zero]

/-- Action of `gibbsBoltzmannOp ψ_alt E_alt β` on `ψ_alt ω` for any orthonormal family `ψ_alt`. -/
theorem perturbed_gibbsBoltzmannOp_apply_of_orthonormal_at {D L : ℕ}
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

/-- Orthonormal eigenbasis invariance of `gibbsBoltzmannOp`. -/
theorem perturbed_gibbsBoltzmannOp_eq_of_any_orthonormal_eigenbasis {D L : ℕ}
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
  rw [hb_ω, perturbed_gibbsBoltzmannOp_opEigenbasis_apply_of_eigenvector H hH (h_eig ω) β,
    perturbed_gibbsBoltzmannOp_apply_of_orthonormal_at ψ_alt E_alt h_onb β ω]

/-- Orthonormal eigenbasis invariance of `hilbertTrace (gibbsBoltzmannOp ... * A)`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ψ_alt : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_alt : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_eig : ∀ ω, H (ψ_alt ω) = (E_alt ω : ℂ) • ψ_alt ω) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * A) =
      ∑ ω : ManyBodyConfig Site,
        Real.exp (-β * E_alt ω) * RCLike.re (inner ℂ (ψ_alt ω) (A (ψ_alt ω))) := by
  rw [perturbed_gibbsBoltzmannOp_eq_of_any_orthonormal_eigenbasis H hH ψ_alt E_alt h_onb h_eig β,
    hilbertTrace_gibbsBoltzmannOp_mul_eq]

/-- Every eigenvector in `opEigenbasis H hH` has unit inner product and norm at most `1`. -/
lemma perturbed_norm_opEigenbasis_le_one {D L : ℕ}
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
  refine ⟨h_re, ?_⟩
  nlinarith [norm_nonneg (opEigenbasis H hH ω)]

/-- Identity `hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * 1) = gibbsPartitionZ (opEigenvalues H hH) β`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β * 1) =
      gibbsPartitionZ (opEigenvalues H hH) β := by
  rw [hilbertTrace_gibbsBoltzmannOp_mul_eq, gibbsPartitionZ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.one_apply, (perturbed_norm_opEigenbasis_le_one H hH ω).1, mul_one]

/-- Exact identity expressing `gibbsFailureProb` as `(gibbsPartitionZ)⁻¹` times the Boltzmann trace. -/
lemma perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace
    {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H_pert : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pert : IsSelfAdjoint H_pert) (β : ℝ)
    (P_fail : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    gibbsFailureProb H_pert hH_pert β P_fail =
      (gibbsPartitionZ (opEigenvalues H_pert hH_pert) β)⁻¹ *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pert hH_pert)
          (opEigenvalues H_pert hH_pert) β * P_fail) := by
  unfold gibbsFailureProb gibbsDensityOp
  rw [clm_smul_mul, ← Complex.ofReal_inv, _root_.hilbertTrace_smul_ofReal]

/-- Exact identity `hilbertTrace (gibbsBoltzmannOp ... β * P_fail) = gibbsFailureProb ... β P_fail * gibbsPartitionZ ... β`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_eq_gibbsFailureProb_mul_partitionZ {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H_pert : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pert : IsSelfAdjoint H_pert) (β : ℝ)
    (P_fail : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pert hH_pert)
      (opEigenvalues H_pert hH_pert) β * P_fail) =
    gibbsFailureProb H_pert hH_pert β P_fail *
      gibbsPartitionZ (opEigenvalues H_pert hH_pert) β := by
  have hZ_ne : gibbsPartitionZ (opEigenvalues H_pert hH_pert) β ≠ 0 :=
    ne_of_gt (gibbsPartitionZ_pos _ β)
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace, mul_right_comm,
    inv_mul_cancel₀ hZ_ne, one_mul]

/-- Orthonormal eigenbasis invariance of `gibbsPartitionZ`. -/
theorem perturbed_gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ψ_alt : ManyBodyConfig Site → ManyBodyHilbertSpace Site) (E_alt : ManyBodyConfig Site → ℝ)
    (h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0)
    (h_eig : ∀ ω, H (ψ_alt ω) = (E_alt ω : ℂ) • ψ_alt ω) (β : ℝ) :
    gibbsPartitionZ (opEigenvalues H hH) β = gibbsPartitionZ E_alt β := by
  rw [← perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ H hH β,
    perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis H hH ψ_alt E_alt h_onb h_eig β 1,
    gibbsPartitionZ]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ContinuousLinearMap.one_apply, h_onb ω ω, if_pos rfl, RCLike.one_re, mul_one]

/-- Pullback of `opEigenbasis H hH` by `U.1†` is an orthonormal family. -/
theorem perturbed_orthonormal_unitary_pullback_eigenbasis {D L : ℕ}
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
    _ = inner ℂ (opEigenbasis H hH ω₁) ((U.1 * U.1†) (opEigenbasis H hH ω₂)) := rfl
    _ = inner ℂ (opEigenbasis H hH ω₁) (opEigenbasis H hH ω₂) := by
        rw [hU_self_star, ContinuousLinearMap.one_apply]
    _ = if ω₁ = ω₂ then (1 : ℂ) else 0 := opEigenbasis_orthonormal H hH ω₁ ω₂

/-- Each vector `(U.1†) (opEigenbasis H hH ω)` is an eigenvector of `U.1† * H * U.1` with eigenvalue
`opEigenvalues H hH ω`. -/
theorem perturbed_eigenvalue_eq_unitary_pullback_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (ω : ManyBodyConfig Site) :
    (U.1† * H * U.1) ((U.1†) (opEigenbasis H hH ω)) =
      (opEigenvalues H hH ω : ℂ) • ((U.1†) (opEigenbasis H hH ω)) := by
  have hU_self_star : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  calc (U.1† * H * U.1) ((U.1†) (opEigenbasis H hH ω))
    _ = (U.1†) (H ((U.1 * U.1†) (opEigenbasis H hH ω))) := rfl
    _ = (U.1†) (H (opEigenbasis H hH ω)) := by rw [hU_self_star, ContinuousLinearMap.one_apply]
    _ = (U.1†) ((opEigenvalues H hH ω : ℂ) • opEigenbasis H hH ω) := by
        rw [opEigenbasis_apply_H H hH ω]
    _ = (opEigenvalues H hH ω : ℂ) • ((U.1†) (opEigenbasis H hH ω)) := map_smul (U.1†) _ _

/-- Unitary conjugation invariance of `hilbertTrace (gibbsBoltzmannOp ... * M)`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_unitary_pullback_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    (hH_pull : IsSelfAdjoint (U.1† * H * U.1)) (β : ℝ)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis (U.1† * H * U.1) hH_pull)
      (opEigenvalues (U.1† * H * U.1) hH_pull) β * M) =
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
      (U.1 * M * U.1†)) := by
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
        (U.1† * H * U.1) hH_pull (fun ω => (U.1†) (opEigenbasis H hH ω)) (opEigenvalues H hH)
        (perturbed_orthonormal_unitary_pullback_eigenbasis U H hH)
        (perturbed_eigenvalue_eq_unitary_pullback_eigenbasis U H hH) β M,
      hilbertTrace_gibbsBoltzmannOp_mul_eq]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h_inner :
      inner ℂ ((U.1†) (opEigenbasis H hH ω)) (M ((U.1†) (opEigenbasis H hH ω))) =
        inner ℂ (opEigenbasis H hH ω) ((U.1 * M * U.1†) (opEigenbasis H hH ω)) :=
    ContinuousLinearMap.adjoint_inner_left U.1
      (M ((U.1†) (opEigenbasis H hH ω))) (opEigenbasis H hH ω)
  rw [h_inner]

/-- Unitary conjugation invariance of the dressed failure Boltzmann trace:
`Tr(e^{-β H_pert} (1 - U_dress Pi_safe U_dress†)) = Tr(e^{-β (U_dress† H_pert U_dress)} (1 - Pi_safe))`. -/
theorem perturbed_hilbertTrace_gibbsBoltzmannOp_dressed_failure_eq_pullback_bare_failure {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H_pert Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pert : IsSelfAdjoint H_pert)
    (hH_pull : IsSelfAdjoint (U_dress.1† * H_pert * U_dress.1)) (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_pert hH_pert)
      (opEigenvalues H_pert hH_pert) β * (1 - (U_dress.1 * Pi_safe * U_dress.1†))) =
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis (U_dress.1† * H_pert * U_dress.1) hH_pull)
      (opEigenvalues (U_dress.1† * H_pert * U_dress.1) hH_pull) β * (1 - Pi_safe)) := by
  rw [perturbed_hilbertTrace_gibbsBoltzmannOp_unitary_pullback_eq
    U_dress H_pert hH_pert hH_pull β (1 - Pi_safe)]
  have hU_self_star : U_dress.1 * U_dress.1† = 1 := Unitary.coe_mul_star_self U_dress
  have h_conj : U_dress.1 * (1 - Pi_safe) * U_dress.1† = 1 - (U_dress.1 * Pi_safe * U_dress.1†) := by
    rw [mul_sub, sub_mul, mul_one, hU_self_star]
  rw [h_conj]

/-- Unitary conjugation invariance of the partition function `gibbsPartitionZ`. -/
theorem perturbed_gibbsPartitionZ_unitary_pullback_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (H_pert : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pert : IsSelfAdjoint H_pert)
    (hH_pull : IsSelfAdjoint (U_dress.1† * H_pert * U_dress.1)) (β : ℝ) :
    gibbsPartitionZ (opEigenvalues (U_dress.1† * H_pert * U_dress.1) hH_pull) β =
      gibbsPartitionZ (opEigenvalues H_pert hH_pert) β :=
  perturbed_gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis
    (U_dress.1† * H_pert * U_dress.1) hH_pull
    (fun ω => (U_dress.1†) (opEigenbasis H_pert hH_pert ω)) (opEigenvalues H_pert hH_pert)
    (perturbed_orthonormal_unitary_pullback_eigenbasis U_dress H_pert hH_pert)
    (perturbed_eigenvalue_eq_unitary_pullback_eigenbasis U_dress H_pert hH_pert) β

/-- Unitary pullback identity for dressed `gibbsFailureProb`. -/
theorem perturbed_gibbsFailureProb_dressed_eq_pullback_bare {D L : ℕ}
    {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H_pert : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pert : IsSelfAdjoint H_pert) (β : ℝ)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_pull : IsSelfAdjoint (U_dress.1† * H_pert * U_dress.1)) :
    gibbsFailureProb H_pert hH_pert β (1 - (U_dress.1 * Pi_safe * U_dress.1†)) =
      gibbsFailureProb (U_dress.1† * H_pert * U_dress.1) hH_pull β (1 - Pi_safe) := by
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace,
      perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace,
      perturbed_hilbertTrace_gibbsBoltzmannOp_dressed_failure_eq_pullback_bare_failure
        U_dress H_pert Pi_safe hH_pert hH_pull β,
      perturbed_gibbsPartitionZ_unitary_pullback_eq U_dress H_pert hH_pert hH_pull β]

end
