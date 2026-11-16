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

import Proofs.CenteredBallBHM.ExcitedBandGapFromRelativeForm
import Proofs.TwoAxisMemorySynthesis.ZeroOffDiagQACMasterReduction

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Autonomous Ground-Space Heisenberg Drift Under Approximate Commutation

Bounds the autonomous Heisenberg ground-subspace drift of dressed logical observables under a perturbed Hamiltonian from ground-band scalar pinching, relative form bounds, and exact or approximate ground-projector commutation.

## References

* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
-/

/-- If `Commute H P`, then `timeEvolutionOp H u` commutes with `P` for every `u : ℝ`. -/
lemma commute_timeEvolutionOp_of_commute_ground {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : Commute H P) (u : ℝ) :
    Commute (timeEvolutionOp H u) P := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  unfold timeEvolutionOp
  have h_smul : Commute ((Complex.I * (u : ℂ)) • H) P := by
    rw [commute_iff_eq, clm_smul_mul_assoc, clm_mul_smul_comm, h_comm.eq]
  exact h_smul.exp_left

/-- `heisenbergFlow H t` is multiplicative:
    `heisenbergFlow H t (X * Y) = heisenbergFlow H t X * heisenbergFlow H t Y`. -/
lemma heisenbergFlow_mul_ground {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H X Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    heisenbergFlow H t (X * Y) = heisenbergFlow H t X * heisenbergFlow H t Y := by
  unfold heisenbergFlow
  have h_inv : timeEvolutionOp H (-t) * timeEvolutionOp H t = 1 :=
    (timeEvolutionOp_mul_neg H t).2
  calc timeEvolutionOp H t * (X * Y) * timeEvolutionOp H (-t)
    _ = timeEvolutionOp H t * X * (1 * Y) * timeEvolutionOp H (-t) := by
        rw [one_mul]; simp only [mul_assoc]
    _ = timeEvolutionOp H t * X * ((timeEvolutionOp H (-t) * timeEvolutionOp H t) * Y) *
        timeEvolutionOp H (-t) := by rw [h_inv]
    _ = (timeEvolutionOp H t * X * timeEvolutionOp H (-t)) *
        (timeEvolutionOp H t * Y * timeEvolutionOp H (-t)) := by
        simp only [mul_assoc]

/-- Algebraic decomposition of right-projected Heisenberg drift:
    `(heisenbergFlow H t O - O) * P = (heisenbergFlow H t (O * P) - O * P) - heisenbergFlow H t O * (heisenbergFlow H t P - P)`. -/
lemma heisenbergFlow_sub_self_mul_proj_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H O P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    (heisenbergFlow H t O - O) * P =
      (heisenbergFlow H t (O * P) - O * P) -
        heisenbergFlow H t O * (heisenbergFlow H t P - P) := by
  rw [heisenbergFlow_mul_ground H O P t, sub_mul, mul_sub]
  abel

/-- Since `timeEvolutionOp H τ` commutes with `H`, `opCommutator H` intertwines `heisenbergFlow H τ`. -/
lemma opCommutator_heisenbergFlow_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (τ : ℝ) :
    opCommutator H (heisenbergFlow H τ X) = heisenbergFlow H τ (opCommutator H X) := by
  unfold opCommutator heisenbergFlow
  have h_t : H * timeEvolutionOp H τ = timeEvolutionOp H τ * H :=
    (commute_timeEvolutionOp_of_commute_ground (Commute.refl H) τ).symm.eq
  have h_nt : timeEvolutionOp H (-τ) * H = H * timeEvolutionOp H (-τ) :=
    (commute_timeEvolutionOp_of_commute_ground (Commute.refl H) (-τ)).eq
  calc H * (timeEvolutionOp H τ * X * timeEvolutionOp H (-τ)) -
        (timeEvolutionOp H τ * X * timeEvolutionOp H (-τ)) * H
    _ = (H * timeEvolutionOp H τ) * X * timeEvolutionOp H (-τ) -
        timeEvolutionOp H τ * X * (timeEvolutionOp H (-τ) * H) := by
        simp only [mul_assoc]
    _ = timeEvolutionOp H τ * (H * X) * timeEvolutionOp H (-τ) -
        timeEvolutionOp H τ * (X * H) * timeEvolutionOp H (-τ) := by
        rw [h_t, h_nt]; simp only [mul_assoc]
    _ = timeEvolutionOp H τ * (H * X - X * H) * timeEvolutionOp H (-τ) := by
        rw [← sub_mul, ← mul_sub]

/-- Mean-value bound on autonomous Heisenberg evolution for any self-adjoint `H` and `t ≥ 0`:
    `‖heisenbergFlow H t X - X‖ ≤ t * ‖H * X - X * H‖`. -/
lemma norm_heisenbergFlow_sub_self_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖heisenbergFlow H t X - X‖ ≤ t * ‖H * X - X * H‖ := by
  have h_deriv_le : ∀ τ ∈ (Set.univ : Set ℝ),
      ‖(Complex.I : ℂ) • opCommutator H (heisenbergFlow H τ X)‖ ≤ ‖opCommutator H X‖ := by
    intro τ _
    rw [norm_smul, Complex.norm_I, one_mul, opCommutator_heisenbergFlow_eq H X τ]
    exact norm_heisenbergFlow_le hH τ (opCommutator H X)
  have h_mvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => heisenbergFlow H s X)
    (f' := fun τ : ℝ => (Complex.I : ℂ) • opCommutator H (heisenbergFlow H τ X))
    (s := Set.univ)
    (fun τ _ => (hasDerivAt_heisenbergFlow H X τ).hasDerivWithinAt)
    h_deriv_le
    convex_univ
    (Set.mem_univ (0 : ℝ))
    (Set.mem_univ t)
  have h_at_0 : heisenbergFlow H 0 X = X := by
    unfold heisenbergFlow
    rw [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  have h_norm_t : ‖t - (0 : ℝ)‖ = t := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht]
  (try dsimp only at h_mvt)
  rw [h_at_0, h_norm_t, mul_comm] at h_mvt
  exact h_mvt

/-- Operator norm of any star projection `P` is at most `1`. -/
lemma isStarProjection_opNorm_le_one_ground {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound P zero_le_one (fun ψ => ?_)
  have h_sq : ‖P ψ‖ ^ 2 ≤ (1 * ‖ψ‖) ^ 2 := by
    rw [one_mul]
    exact isStarProjection_norm_sq_apply_le_bhm hP ψ
  have h_abs : |‖P ψ‖| ≤ |1 * ‖ψ‖| := sq_le_sq.mp h_sq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg zero_le_one (norm_nonneg _))] at h_abs

/-- Ring decomposition of `[H', O * P]` when `P * P = P` and `O * P = P * O`:
    `H' * (O * P) - (O * P) * H' = ((P * H' * P) * (O * P) - (O * P) * (P * H' * P)) + (H' * P - P * H') * (P * O * P) - (P * O * P) * (P * H' - H' * P)`. -/
lemma opCommutator_mul_proj_decomp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' P O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) (h_comm_O : Commute O P) :
    H' * (O * P) - (O * P) * H' =
      ((P * H' * P) * (O * P) - (O * P) * (P * H' * P)) +
      (H' * P - P * H') * (P * O * P) -
      (P * O * P) * (P * H' - H' * P) := by
  have hP_idem : P * P = P := hP.isIdempotentElem.eq
  have hPA : P * (O * P) = O * P := by
    rw [← mul_assoc P O P, ← h_comm_O.eq, mul_assoc O P P, hP_idem]
  have hAP : (O * P) * P = O * P := by
    rw [mul_assoc O P P, hP_idem]
  have hPOP : P * O * P = O * P := by
    rw [mul_assoc P O P, hPA]
  have h1 : (P * H' * P) * (O * P) = P * H' * (O * P) := by
    rw [mul_assoc (P * H') P (O * P), hPA]
  have h2 : (O * P) * (P * H' * P) = (O * P) * H' * P := by
    calc (O * P) * (P * H' * P)
      _ = ((O * P) * P) * H' * P := by simp only [mul_assoc]
      _ = (O * P) * H' * P := by rw [hAP]
  have h3 : (H' * P - P * H') * (P * O * P) = H' * (O * P) - P * H' * (O * P) := by
    rw [hPOP, sub_mul, mul_assoc H' P (O * P), hPA]
  have h4 : (P * O * P) * (P * H' - H' * P) = (O * P) * H' - (O * P) * H' * P := by
    rw [hPOP, mul_sub, ← mul_assoc (O * P) P H', hAP, ← mul_assoc (O * P) H' P]
  rw [h1, h2, h3, h4]
  abel

/-- Norm bound on `[H, O * P]` under pinched ground splitting `‖P * (H - E0 • 1) * P‖ ≤ δ_pinch`
    and approximate projection commutation `‖H * P - P * H‖ ≤ δ_comm`:
    `‖H * (O * P) - (O * P) * H‖ ≤ 2 * δ_pinch + 2 * δ_comm`. -/
lemma norm_commutator_mul_proj_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {E0 δ_pinch δ_comm : ℝ}
    (hP : IsStarProjection P) (h_comm_O : Commute O P) (hO_norm : ‖O‖ ≤ 1)
    (h_pinch : ‖P * (H - (E0 : ℂ) • 1) * P‖ ≤ δ_pinch)
    (h_comm : ‖H * P - P * H‖ ≤ δ_comm) :
    ‖H * (O * P) - (O * P) * H‖ ≤ 2 * δ_pinch + 2 * δ_comm := by
  let H' := H - (E0 : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  let K := P * H' * P
  have h_shift_X : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      H * X - X * H = H' * X - X * H' := by
    intro X; dsimp [H']
    rw [sub_mul, mul_sub, clm_smul_mul_assoc, clm_mul_smul_comm, one_mul, mul_one,
      sub_sub_sub_cancel_right]
  have hP_norm : ‖P‖ ≤ 1 := isStarProjection_opNorm_le_one_ground hP
  have hOP_norm : ‖O * P‖ ≤ 1 := by
    calc ‖O * P‖
      _ ≤ ‖O‖ * ‖P‖ := norm_mul_le O P
      _ ≤ 1 * 1 := mul_le_mul hO_norm hP_norm (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hPOP_eq : P * O * P = O * P := by
    rw [← h_comm_O.eq, mul_assoc O P P, hP.isIdempotentElem.eq]
  have hPOP_norm : ‖P * O * P‖ ≤ 1 := by rw [hPOP_eq]; exact hOP_norm
  have hH'P_norm : ‖H' * P - P * H'‖ ≤ δ_comm := by
    rw [← h_shift_X P]; exact h_comm
  have hPH'_norm : ‖P * H' - H' * P‖ ≤ δ_comm := by
    rw [norm_sub_rev]; exact hH'P_norm
  have hK_nn : 0 ≤ δ_pinch := le_trans (norm_nonneg K) h_pinch
  have hC_nn : 0 ≤ δ_comm := le_trans (norm_nonneg _) h_comm
  have h_term1 : ‖K * (O * P) - (O * P) * K‖ ≤ 2 * δ_pinch := by
    calc ‖K * (O * P) - (O * P) * K‖
      _ = ‖opCommutator K (O * P)‖ := rfl
      _ ≤ 2 * ‖K‖ * ‖O * P‖ := norm_opCommutator_le K (O * P)
      _ ≤ 2 * δ_pinch * 1 := by
        apply mul_le_mul (by linarith) hOP_norm (norm_nonneg _) (by linarith)
      _ = 2 * δ_pinch := mul_one _
  have h_term2 : ‖(H' * P - P * H') * (P * O * P)‖ ≤ δ_comm := by
    calc ‖(H' * P - P * H') * (P * O * P)‖
      _ ≤ ‖H' * P - P * H'‖ * ‖P * O * P‖ := norm_mul_le _ _
      _ ≤ δ_comm * 1 := mul_le_mul hH'P_norm hPOP_norm (norm_nonneg _) hC_nn
      _ = δ_comm := mul_one _
  have h_term3 : ‖(P * O * P) * (P * H' - H' * P)‖ ≤ δ_comm := by
    calc ‖(P * O * P) * (P * H' - H' * P)‖
      _ ≤ ‖P * O * P‖ * ‖P * H' - H' * P‖ := norm_mul_le _ _
      _ ≤ 1 * δ_comm := mul_le_mul hPOP_norm hPH'_norm (norm_nonneg _) zero_le_one
      _ = δ_comm := one_mul _
  rw [h_shift_X (O * P), opCommutator_mul_proj_decomp hP h_comm_O]
  calc ‖(K * (O * P) - (O * P) * K) + (H' * P - P * H') * (P * O * P) -
          (P * O * P) * (P * H' - H' * P)‖
    _ ≤ ‖(K * (O * P) - (O * P) * K) + (H' * P - P * H') * (P * O * P)‖ +
        ‖(P * O * P) * (P * H' - H' * P)‖ := norm_sub_le _ _
    _ ≤ (‖K * (O * P) - (O * P) * K‖ + ‖(H' * P - P * H') * (P * O * P)‖) +
        ‖(P * O * P) * (P * H' - H' * P)‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 2 * δ_pinch + δ_comm + δ_comm := by linarith
    _ = 2 * δ_pinch + 2 * δ_comm := by ring

/-- **Autonomous Heisenberg Ground-Subspace Drift Under Approximate Commutation
    (`autonomous_heisenberg_ground_subspace_drift_le_of_approx_commute`)**:
    When `IsSelfAdjoint H`, `IsStarProjection P0_dress`, `Commute O_dress P0_dress`, `‖O_dress‖ ≤ 1`,
    `‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_pinch`, and `‖H * P0_dress - P0_dress * H‖ ≤ δ_comm`,
    the autonomous Heisenberg evolution satisfies
    `‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * (2 * δ_pinch + 3 * δ_comm)` for all `t ≥ 0`. -/
theorem autonomous_heisenberg_ground_subspace_drift_le_of_approx_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P0_dress O_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {E0 δ_pinch δ_comm : ℝ}
    (hH : IsSelfAdjoint H) (hP0 : IsStarProjection P0_dress)
    (h_comm_O : Commute O_dress P0_dress) (hO_norm : ‖O_dress‖ ≤ 1)
    (h_pinch : ‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_pinch)
    (h_comm : ‖H * P0_dress - P0_dress * H‖ ≤ δ_comm)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * (2 * δ_pinch + 3 * δ_comm) := by
  have h_OP_drift : ‖heisenbergFlow H t (O_dress * P0_dress) - O_dress * P0_dress‖ ≤
      t * (2 * δ_pinch + 2 * δ_comm) := by
    calc ‖heisenbergFlow H t (O_dress * P0_dress) - O_dress * P0_dress‖
      _ ≤ t * ‖H * (O_dress * P0_dress) - (O_dress * P0_dress) * H‖ :=
        norm_heisenbergFlow_sub_self_le hH (O_dress * P0_dress) ht
      _ ≤ t * (2 * δ_pinch + 2 * δ_comm) :=
        mul_le_mul_of_nonneg_left
          (norm_commutator_mul_proj_le H P0_dress O_dress hP0 h_comm_O hO_norm h_pinch h_comm) ht
  have h_P_drift : ‖heisenbergFlow H t P0_dress - P0_dress‖ ≤ t * δ_comm := by
    calc ‖heisenbergFlow H t P0_dress - P0_dress‖
      _ ≤ t * ‖H * P0_dress - P0_dress * H‖ := norm_heisenbergFlow_sub_self_le hH P0_dress ht
      _ ≤ t * δ_comm := mul_le_mul_of_nonneg_left h_comm ht
  have hO_t_norm : ‖heisenbergFlow H t O_dress‖ ≤ 1 :=
    le_trans (norm_heisenbergFlow_le hH t O_dress) hO_norm
  have h_prod_drift :
      ‖heisenbergFlow H t O_dress * (heisenbergFlow H t P0_dress - P0_dress)‖ ≤ t * δ_comm := by
    calc ‖heisenbergFlow H t O_dress * (heisenbergFlow H t P0_dress - P0_dress)‖
      _ ≤ ‖heisenbergFlow H t O_dress‖ * ‖heisenbergFlow H t P0_dress - P0_dress‖ := norm_mul_le _ _
      _ ≤ 1 * (t * δ_comm) :=
        mul_le_mul hO_t_norm h_P_drift (norm_nonneg _) zero_le_one
      _ = t * δ_comm := one_mul _
  rw [heisenbergFlow_sub_self_mul_proj_eq H O_dress P0_dress t]
  calc ‖(heisenbergFlow H t (O_dress * P0_dress) - O_dress * P0_dress) -
          heisenbergFlow H t O_dress * (heisenbergFlow H t P0_dress - P0_dress)‖
    _ ≤ ‖heisenbergFlow H t (O_dress * P0_dress) - O_dress * P0_dress‖ +
        ‖heisenbergFlow H t O_dress * (heisenbergFlow H t P0_dress - P0_dress)‖ := norm_sub_le _ _
    _ ≤ t * (2 * δ_pinch + 2 * δ_comm) + t * δ_comm := add_le_add h_OP_drift h_prod_drift
    _ = t * (2 * δ_pinch + 3 * δ_comm) := by ring

/-- **Autonomous Heisenberg Ground-Subspace Linear Drift Bound
    (`autonomous_heisenberg_ground_subspace_drift_le`)**:
    When `IsSelfAdjoint H`, `IsStarProjection P0_dress`, `Commute O_dress P0_dress`, `‖O_dress‖ ≤ 1`,
    `‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_pinch`, `‖H * P0_dress - P0_dress * H‖ ≤ δ_comm`,
    and `2 * δ_pinch + 3 * δ_comm ≤ δ_split`, the autonomous Heisenberg drift on the dressed ground
    subspace satisfies `‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split` for all `t ≥ 0`. -/
theorem autonomous_heisenberg_ground_subspace_drift_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H P0_dress O_dress : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {E0 δ_pinch δ_comm δ_split : ℝ}
    (hH : IsSelfAdjoint H) (hP0 : IsStarProjection P0_dress)
    (h_comm_O : Commute O_dress P0_dress) (hO_norm : ‖O_dress‖ ≤ 1)
    (h_pinch : ‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_pinch)
    (h_comm : ‖H * P0_dress - P0_dress * H‖ ≤ δ_comm)
    (h_comb : 2 * δ_pinch + 3 * δ_comm ≤ δ_split)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split :=
  le_trans
    (autonomous_heisenberg_ground_subspace_drift_le_of_approx_commute
      H P0_dress O_dress hH hP0 h_comm_O hO_norm h_pinch h_comm t ht)
    (mul_le_mul_of_nonneg_left h_comb ht)

/-- **Dressed Ground-Space Heisenberg Drift from Approximate Commutation and Relative Form Stability
    (`zero_temp_heisenberg_ground_drift_of_approx_commute_and_relative_form`)**:
    For any commuting-projector Hamiltonian `sys`, quasi-local perturbation `V`, dressing unitary
    `U_dress`, and bare logical observable `O_0` (`Commute sys.P0 O_0`, `‖O_0‖ ≤ 1`), if
    `‖H * P0_dress - P0_dress * H‖ ≤ δ_comm`, the relative form bound holds with additive slack
    `(δ_form / 2) * ‖ψ‖ ^ 2`, and `δ_form + 3 * δ_comm ≤ δ_split`, then
    `‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split` for all `t ≥ 0`. -/
theorem zero_temp_heisenberg_ground_drift_of_approx_commute_and_relative_form {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (O_0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {E0 δ_form δ_comm δ_split : ℝ}
    (hO_P0 : Commute sys.P0 O_0) (hO_norm : ‖O_0‖ ≤ 1)
    (h_comm_P0 :
      let H := sys.H0 + V.totalPerturbation
      let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
      ‖H * P0_dress - P0_dress * H‖ ≤ δ_comm)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_form / 2) * ‖ψ‖ ^ 2)
    (h_comb : δ_form + 3 * δ_comm ≤ δ_split)
    (t : ℝ) (ht : 0 ≤ t) :
    let H := sys.H0 + V.totalPerturbation
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let O_dress := U_dress.1 * O_0 * U_dress.1†
    ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split := by
  intro H P0_dress O_dress
  have hH : IsSelfAdjoint H := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V
  have hP0_dress : IsStarProjection P0_dress := dressed_ground_proj_isStarProjection sys U_dress
  rcases dressed_ground_subspace_splitting_opNorm_le_half sys V U_dress h_form with
    ⟨_hδ_nn, h_split_half⟩
  have hU_star_self : U_dress.1† * U_dress.1 = 1 := Unitary.coe_star_mul_self U_dress
  have h_comm_O : Commute O_dress P0_dress := by
    rw [commute_iff_eq]
    calc (U_dress.1 * O_0 * U_dress.1†) * (U_dress.1 * sys.P0 * U_dress.1†)
      _ = U_dress.1 * (O_0 * (U_dress.1† * U_dress.1) * sys.P0) * U_dress.1† := by
          simp only [mul_assoc]
      _ = U_dress.1 * (O_0 * sys.P0) * U_dress.1† := by rw [hU_star_self, mul_one]
      _ = U_dress.1 * (sys.P0 * O_0) * U_dress.1† := by rw [hO_P0.symm.eq]
      _ = U_dress.1 * (sys.P0 * (U_dress.1† * U_dress.1) * O_0) * U_dress.1† := by
          rw [hU_star_self, mul_one]
      _ = (U_dress.1 * sys.P0 * U_dress.1†) * (U_dress.1 * O_0 * U_dress.1†) := by
          simp only [mul_assoc]
  rcases norm_unitary_and_adj_le_one_clm U_dress with ⟨hU_norm, hU_adj_norm⟩
  have hO_dress_norm : ‖O_dress‖ ≤ 1 := by
    calc ‖U_dress.1 * O_0 * U_dress.1†‖
      _ ≤ ‖U_dress.1 * O_0‖ * ‖U_dress.1†‖ := norm_mul_le _ _
      _ ≤ (‖U_dress.1‖ * ‖O_0‖) * ‖U_dress.1†‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * 1) * 1 := by
          apply mul_le_mul
            (mul_le_mul hU_norm hO_norm (norm_nonneg _) zero_le_one)
            hU_adj_norm (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  exact autonomous_heisenberg_ground_subspace_drift_le H P0_dress O_dress
    hH hP0_dress h_comm_O hO_dress_norm h_split_half h_comm_P0 (by linarith) t ht

/-- **Dressed Ground-Space Heisenberg Drift from Relative Form Stability (`δ_pinch ≤ δ_split / 4`, `δ_comm ≤ δ_split / 6`)
    (`zero_temp_heisenberg_ground_drift_of_relative_form`)**:
    Specializes `zero_temp_heisenberg_ground_drift_of_approx_commute_and_relative_form` to
    `‖H * P0_dress - P0_dress * H‖ ≤ δ_split / 6` and relative form slack `(δ_split / 4) * ‖ψ‖ ^ 2`. -/
theorem zero_temp_heisenberg_ground_drift_of_relative_form {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (O_0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {E0 δ_split : ℝ}
    (hO_P0 : Commute sys.P0 O_0) (hO_norm : ‖O_0‖ ≤ 1)
    (h_comm_P0 :
      let H := sys.H0 + V.totalPerturbation
      let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
      ‖H * P0_dress - P0_dress * H‖ ≤ δ_split / 6)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 4) * ‖ψ‖ ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    let H := sys.H0 + V.totalPerturbation
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let O_dress := U_dress.1 * O_0 * U_dress.1†
    ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split := by
  have h_form_half : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + ((δ_split / 2) / 2) * ‖ψ‖ ^ 2 := by
    intro ψ
    have h := h_form ψ
    ring_nf at h ⊢
    exact h
  exact zero_temp_heisenberg_ground_drift_of_approx_commute_and_relative_form
    sys V U_dress O_0 hO_P0 hO_norm h_comm_P0 h_form_half (by linarith) t ht

/-- Specialization of `zero_temp_heisenberg_ground_drift_of_approx_commute_and_relative_form`
    when `Commute (U_dress.1† * (sys.H0 + V.V_tot) * U_dress.1) sys.P0` holds (`δ_comm = 0`). -/
theorem zero_temp_heisenberg_ground_drift_of_commute_and_relative_form {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (O_0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {E0 δ_split : ℝ}
    (hO_P0 : Commute sys.P0 O_0) (hO_norm : ‖O_0‖ ≤ 1)
    (h_comm_P0 : Commute (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) sys.P0)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2)
    (t : ℝ) (ht : 0 ≤ t) :
    let H := sys.H0 + V.totalPerturbation
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let O_dress := U_dress.1 * O_0 * U_dress.1†
    ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split := by
  have h_comm_H := (dressed_ground_proj_isStarProjection_and_commute sys V U_dress h_comm_P0).2
  have h_comm_zero :
      ‖(sys.H0 + V.totalPerturbation) * (U_dress.1 * sys.P0 * U_dress.1†) -
        (U_dress.1 * sys.P0 * U_dress.1†) * (sys.H0 + V.totalPerturbation)‖ ≤ 0 := by
    rw [sub_eq_zero.mpr h_comm_H.eq, norm_zero]
  exact zero_temp_heisenberg_ground_drift_of_approx_commute_and_relative_form
    sys V U_dress O_0 hO_P0 hO_norm h_comm_zero h_form (by linarith) t ht

end
