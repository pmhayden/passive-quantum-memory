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

import Defs.FlowAndFilter
import Proofs.KatoHastingsFlow.ConstructiveQuasiLocalQAC

/-!
# Algebraic Covariance of Dressed Safe Projectors and Decoded Logical Observables

Defines `dressedSafeProjector` and `dressedDecodedLogicalOp`, proving unitary norm invariance (`norm_unitary_conj_eq`), star-projection and involution preservation (`isStarProjection_dressedSafeProjector`, `isSelfAdjoint_dressedDecodedLogicalOp`, `mul_self_dressedDecodedLogicalOp`), and exact pullback of dressed safe-subspace commutators (`dressedSafeProjector_code_invariance`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Unitary Conjugation & Norm Invariance
-/

/-- Left inverse identity `U.1† * U.1 = 1` for `U : unitary (E →L[ℂ] E)`. -/
lemma unitary_adj_mul_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) :
    (U.1†) * U.1 = 1 :=
  Unitary.coe_star_mul_self U

/-- Right inverse identity `U.1 * U.1† = 1` for `U : unitary (E →L[ℂ] E)`. -/
lemma unitary_mul_adj_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) :
    U.1 * (U.1†) = 1 :=
  Unitary.coe_mul_star_self U

/-- Operator norm bound `‖U.1‖ ≤ 1` and `‖U.1†‖ ≤ 1` for a unitary operator `U`. -/
lemma unitary_opNorm_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) :
    ‖U.1‖ ≤ 1 ∧ ‖U.1†‖ ≤ 1 :=
  norm_le_one_of_adjoint_mul_self_eq_one (unitary_adj_mul_self U)

/-- Unitary conjugation `U.1 * A * U.1†` does not increase the operator norm. -/
lemma norm_unitary_conj_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    ‖U.1 * A * (U.1†)‖ ≤ ‖A‖ := by
  rcases unitary_opNorm_le_one U with ⟨hU, hU_adj⟩
  exact norm_sandwich_le_of_norm_le_one hU hU_adj

/-- Adjoint unitary conjugation `U.1† * A * U.1` does not increase the operator norm. -/
lemma norm_unitary_adj_conj_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    ‖(U.1†) * A * U.1‖ ≤ ‖A‖ := by
  rcases unitary_opNorm_le_one U with ⟨hU, hU_adj⟩
  exact norm_sandwich_le_of_norm_le_one hU_adj hU

/-- Exact operator norm invariance `‖U.1 * A * U.1†‖ = ‖A‖` under unitary conjugation. -/
lemma norm_unitary_conj_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    ‖U.1 * A * (U.1†)‖ = ‖A‖ := by
  apply le_antisymm (norm_unitary_conj_le U A)
  have h_inv : (U.1†) * (U.1 * A * (U.1†)) * U.1 = A := by
    calc (U.1†) * (U.1 * A * (U.1†)) * U.1
      _ = ((U.1†) * U.1) * A * ((U.1†) * U.1) := by simp only [mul_assoc]
      _ = A := by rw [unitary_adj_mul_self U, one_mul, mul_one]
  calc ‖A‖
    _ = ‖(U.1†) * (U.1 * A * (U.1†)) * U.1‖ := by rw [h_inv]
    _ ≤ ‖U.1 * A * (U.1†)‖ := norm_unitary_adj_conj_le U (U.1 * A * (U.1†))

/-- Exact operator norm invariance `‖U.1† * A * U.1‖ = ‖A‖` under adjoint unitary conjugation. -/
lemma norm_unitary_adj_conj_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    ‖(U.1†) * A * U.1‖ = ‖A‖ := by
  apply le_antisymm (norm_unitary_adj_conj_le U A)
  have h_inv : U.1 * ((U.1†) * A * U.1) * (U.1†) = A := by
    calc U.1 * ((U.1†) * A * U.1) * (U.1†)
      _ = (U.1 * (U.1†)) * A * (U.1 * (U.1†)) := by simp only [mul_assoc]
      _ = A := by rw [unitary_mul_adj_self U, one_mul, mul_one]
  calc ‖A‖
    _ = ‖U.1 * ((U.1†) * A * U.1) * (U.1†)‖ := by rw [h_inv]
    _ ≤ ‖(U.1†) * A * U.1‖ := norm_unitary_conj_le U ((U.1†) * A * U.1)

/-!
## 2. Dressed Safe Projector & Dressed Decoded Logical Operator Algebraic Identities
-/

/-- **Dressed Safe Percolation Projector (`dressedSafeProjector`)**:
    $\Pi_{\mathrm{safe}}^{\mathrm{dress}} := U \Pi_{\mathrm{safe}} U^\dagger$. -/
def dressedSafeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  U.1 * Pi_safe * (U.1†)

/-- **Dressed Decoded Logical Operator (`dressedDecodedLogicalOp`)**:
    $O_{\mathrm{dec}}^{\mathrm{dress}} := U O_{\mathrm{dec}} U^\dagger$. -/
def dressedDecodedLogicalOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  U.1 * O_dec * (U.1†)

/-- Multiplicative homomorphism of unitary conjugation `(U.1 * A * U.1†) * (U.1 * B * U.1†) = U.1 * (A * B) * U.1†`. -/
lemma unitary_conj_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) (A B : E →L[ℂ] E) :
    (U.1 * A * (U.1†)) * (U.1 * B * (U.1†)) = U.1 * (A * B) * (U.1†) := by
  calc (U.1 * A * (U.1†)) * (U.1 * B * (U.1†))
    _ = U.1 * A * ((U.1†) * U.1) * B * (U.1†) := by simp only [mul_assoc]
    _ = U.1 * (A * B) * (U.1†) := by rw [unitary_adj_mul_self U, mul_one, mul_assoc U.1 A B]

/-- Adjoint homomorphism of unitary conjugation `(U.1 * A * U.1†)† = U.1 * A† * U.1†`. -/
lemma unitary_conj_adj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) (A : E →L[ℂ] E) :
    (U.1 * A * (U.1†))† = U.1 * (A†) * (U.1†) := by
  change star (U.1 * A * star U.1) = U.1 * star A * star U.1
  rw [star_mul, star_mul, star_star, mul_assoc]

/-- If `Pi_safe` is a star projection, then `U.1 * Pi_safe * U.1†` is a star projection. -/
lemma isStarProjection_dressedSafeProjector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {Pi_safe : E →L[ℂ] E} (hPi : IsStarProjection Pi_safe) :
    IsStarProjection (U.1 * Pi_safe * (U.1†)) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, unitary_conj_mul U Pi_safe Pi_safe, hPi.isIdempotentElem.eq]
  · rw [isSelfAdjoint_iff]
    change star (U.1 * Pi_safe * star U.1) = U.1 * Pi_safe * star U.1
    rw [star_mul, star_mul, star_star, hPi.isSelfAdjoint.star_eq, mul_assoc]

/-- Identity `1 - U.1 * Pi_safe * U.1† = U.1 * (1 - Pi_safe) * U.1†`. -/
lemma one_sub_dressedSafeProjector_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (Pi_safe : E →L[ℂ] E) :
    1 - U.1 * Pi_safe * (U.1†) = U.1 * (1 - Pi_safe) * (U.1†) := by
  rw [mul_sub, mul_one, sub_mul, unitary_mul_adj_self U]

/-- If `Pi_safe` is a star projection, then `1 - U.1 * Pi_safe * U.1†` is a star projection. -/
lemma isStarProjection_one_sub_dressedSafeProjector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {Pi_safe : E →L[ℂ] E} (hPi : IsStarProjection Pi_safe) :
    IsStarProjection (1 - U.1 * Pi_safe * (U.1†)) :=
  (isStarProjection_dressedSafeProjector U hPi).one_sub

/-- If `O_dec` is self-adjoint, then `U.1 * O_dec * U.1†` is self-adjoint. -/
lemma isSelfAdjoint_dressedDecodedLogicalOp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {O_dec : E →L[ℂ] E} (hO : IsSelfAdjoint O_dec) :
    IsSelfAdjoint (U.1 * O_dec * (U.1†)) := by
  rw [isSelfAdjoint_iff]
  change star (U.1 * O_dec * star U.1) = U.1 * O_dec * star U.1
  rw [star_mul, star_mul, star_star, hO.star_eq, mul_assoc]

/-- If `O_dec * O_dec = 1`, then `(U.1 * O_dec * U.1†) * (U.1 * O_dec * U.1†) = 1`. -/
lemma mul_self_dressedDecodedLogicalOp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {O_dec : E →L[ℂ] E} (hO_sq : O_dec * O_dec = 1) :
    (U.1 * O_dec * (U.1†)) * (U.1 * O_dec * (U.1†)) = 1 := by
  rw [unitary_conj_mul U O_dec O_dec, hO_sq, mul_one, unitary_mul_adj_self U]

/-- If `‖O_dec‖ ≤ 1`, then `‖U.1 * O_dec * U.1†‖ ≤ 1`. -/
lemma norm_dressedDecodedLogicalOp_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {O_dec : E →L[ℂ] E} (hO_norm : ‖O_dec‖ ≤ 1) :
    ‖U.1 * O_dec * (U.1†)‖ ≤ 1 :=
  le_trans (norm_unitary_conj_le U O_dec) hO_norm

/-- Unitary covariance of ground-projector safe absorption `P0 * Pi_safe = P0`. -/
lemma dressedGroundProj_mul_dressedSafeProjector {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {P0 Pi_safe : E →L[ℂ] E} (hP0_safe : P0 * Pi_safe = P0) :
    (U.1 * P0 * (U.1†)) * (U.1 * Pi_safe * (U.1†)) = U.1 * P0 * (U.1†) := by
  rw [unitary_conj_mul U P0 Pi_safe, hP0_safe]

/-- Unitary covariance of decoded logical action `O_dec * P0 = L_op * P0`. -/
lemma dressedDecodedLogicalOp_mul_dressedGroundProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {O_dec L_op P0 : E →L[ℂ] E} (hO_P0 : O_dec * P0 = L_op * P0) :
    (U.1 * O_dec * (U.1†)) * (U.1 * P0 * (U.1†)) = (U.1 * L_op * (U.1†)) * (U.1 * P0 * (U.1†)) := by
  rw [unitary_conj_mul U O_dec P0, unitary_conj_mul U L_op P0, hO_P0]

/-- Unitary covariance of safe-subspace code projection invariance
    `Pi_safe * (P0 - O_dec * P0 * O_dec†) * Pi_safe = 0`. -/
lemma dressedSafeProjector_code_invariance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {Pi_safe P0 O_dec : E →L[ℂ] E}
    (h_code : Pi_safe * (P0 - O_dec * P0 * (O_dec†)) * Pi_safe = 0) :
    (U.1 * Pi_safe * (U.1†)) *
      ((U.1 * P0 * (U.1†)) - (U.1 * O_dec * (U.1†)) * (U.1 * P0 * (U.1†)) * ((U.1 * O_dec * (U.1†))†)) *
      (U.1 * Pi_safe * (U.1†)) = 0 := by
  rw [unitary_conj_adj U O_dec, unitary_conj_mul U O_dec P0,
    unitary_conj_mul U (O_dec * P0) (O_dec†), ← sub_mul, ← mul_sub,
    unitary_conj_mul U Pi_safe (P0 - O_dec * P0 * (O_dec†)),
    unitary_conj_mul U (Pi_safe * (P0 - O_dec * P0 * (O_dec†))) Pi_safe,
    h_code, mul_zero, zero_mul]

/-- **Unitary Covariance of Safe-Subspace Commutators (`dressedSafeProjector_commutator_eq_conj`)**:
    For any operator $X$,
    $$\Pi_{\mathrm{safe}}^{\mathrm{dress}} [X, O_{\mathrm{dec}}^{\mathrm{dress}}] \Pi_{\mathrm{safe}}^{\mathrm{dress}}
      = U \big(\Pi_{\mathrm{safe}} [U^\dagger X U, O_{\mathrm{dec}}] \Pi_{\mathrm{safe}}\big) U^\dagger.$$ -/
theorem dressedSafeProjector_commutator_eq_conj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (Pi_safe O_dec X : E →L[ℂ] E) :
    (U.1 * Pi_safe * (U.1†)) * (X * (U.1 * O_dec * (U.1†)) - (U.1 * O_dec * (U.1†)) * X) *
        (U.1 * Pi_safe * (U.1†)) =
      U.1 * (Pi_safe * (((U.1†) * X * U.1) * O_dec - O_dec * ((U.1†) * X * U.1)) * Pi_safe) * (U.1†) := by
  have h1 : (U.1 * Pi_safe * (U.1†)) * (X * (U.1 * O_dec * (U.1†))) * (U.1 * Pi_safe * (U.1†)) =
      U.1 * (Pi_safe * (((U.1†) * X * U.1) * O_dec) * Pi_safe) * (U.1†) := by
    calc (U.1 * Pi_safe * (U.1†)) * (X * (U.1 * O_dec * (U.1†))) * (U.1 * Pi_safe * (U.1†))
      _ = U.1 * Pi_safe * ((U.1†) * X * U.1) * O_dec * ((U.1†) * U.1) * Pi_safe * (U.1†) := by
        simp only [mul_assoc]
      _ = U.1 * (Pi_safe * (((U.1†) * X * U.1) * O_dec) * Pi_safe) * (U.1†) := by
        rw [unitary_adj_mul_self U, mul_one]; simp only [mul_assoc]
  have h2 : (U.1 * Pi_safe * (U.1†)) * ((U.1 * O_dec * (U.1†)) * X) * (U.1 * Pi_safe * (U.1†)) =
      U.1 * (Pi_safe * (O_dec * ((U.1†) * X * U.1)) * Pi_safe) * (U.1†) := by
    calc (U.1 * Pi_safe * (U.1†)) * ((U.1 * O_dec * (U.1†)) * X) * (U.1 * Pi_safe * (U.1†))
      _ = U.1 * Pi_safe * ((U.1†) * U.1) * O_dec * ((U.1†) * X * U.1) * Pi_safe * (U.1†) := by
        simp only [mul_assoc]
      _ = U.1 * (Pi_safe * (O_dec * ((U.1†) * X * U.1)) * Pi_safe) * (U.1†) := by
        rw [unitary_adj_mul_self U, mul_one]; simp only [mul_assoc]
  have h3 :
      U.1 * (Pi_safe * (((U.1†) * X * U.1) * O_dec) * Pi_safe) * (U.1†) -
        U.1 * (Pi_safe * (O_dec * ((U.1†) * X * U.1)) * Pi_safe) * (U.1†) =
      U.1 * (Pi_safe * (((U.1†) * X * U.1) * O_dec - O_dec * ((U.1†) * X * U.1)) * Pi_safe) * (U.1†) := by
    rw [← sub_mul, ← mul_sub, ← sub_mul, ← mul_sub]
  rw [mul_sub, sub_mul, h1, h2, h3]

/-- **Norm Identity for Safe-Subspace Dressed Commutators (`norm_dressedSafeProjector_commutator_eq`)**:
    $$\|\Pi_{\mathrm{safe}}^{\mathrm{dress}} [X, O_{\mathrm{dec}}^{\mathrm{dress}}] \Pi_{\mathrm{safe}}^{\mathrm{dress}}\|
      = \|\Pi_{\mathrm{safe}} [U^\dagger X U, O_{\mathrm{dec}}] \Pi_{\mathrm{safe}}\|.$$ -/
theorem norm_dressedSafeProjector_commutator_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) (Pi_safe O_dec X : E →L[ℂ] E) :
    ‖(U.1 * Pi_safe * (U.1†)) * (X * (U.1 * O_dec * (U.1†)) - (U.1 * O_dec * (U.1†)) * X) *
        (U.1 * Pi_safe * (U.1†))‖ =
      ‖Pi_safe * (((U.1†) * X * U.1) * O_dec - O_dec * ((U.1†) * X * U.1)) * Pi_safe‖ := by
  rw [dressedSafeProjector_commutator_eq_conj U Pi_safe O_dec X, norm_unitary_conj_eq]

/-!
## 3. Symmetry-Sector Preservation of `timeEvolutionOp`
-/

/-- If `U` commutes with `Pi_sec`, then `U.1 * Pi_sec * U.1† = Pi_sec` and `U.1† * Pi_sec * U.1 = Pi_sec`. -/
lemma unitary_conj_eq_self_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {Pi_sec : E →L[ℂ] E} (h_comm : Commute U.1 Pi_sec) :
    U.1 * Pi_sec * (U.1†) = Pi_sec ∧ (U.1†) * Pi_sec * U.1 = Pi_sec := by
  refine ⟨?_, ?_⟩
  · rw [h_comm.eq, mul_assoc, unitary_mul_adj_self U, mul_one]
  · rw [mul_assoc, ← h_comm.eq, ← mul_assoc, unitary_adj_mul_self U, one_mul]

/-- Adjoint of `timeEvolutionOp D_op s` for self-adjoint `D_op` equals `timeEvolutionOp D_op (-s)`. -/
lemma star_timeEvolutionOp_dressing {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (D_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hD : IsSelfAdjoint D_op) (s : ℝ) :
    (timeEvolutionOp D_op s)† = timeEvolutionOp D_op (-s) := by
  let x := (Complex.I * (s : ℂ)) • D_op
  have h_star_x : star x = -x := by
    dsimp [x]
    rw [star_smul, hD.star_eq, star_mul', RCLike.star_def,
      Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_smul (Complex.I * (s : ℂ)) D_op]
  change star (NormedSpace.exp x) = timeEvolutionOp D_op (-s)
  rw [NormedSpace.star_exp, h_star_x, timeEvolutionOp_neg_eq, neg_smul (Complex.I * (s : ℂ)) D_op]

/-- Canonical promotion of `timeEvolutionOp D_op s` for self-adjoint `D_op` to `unitary`. -/
def unitaryOfTimeEvolutionOp {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (D_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hD : IsSelfAdjoint D_op) (s : ℝ) :
    unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  ⟨timeEvolutionOp D_op s, Unitary.mem_iff.mpr ⟨by
    change (timeEvolutionOp D_op s)† * timeEvolutionOp D_op s = 1
    rw [star_timeEvolutionOp_dressing D_op hD s]
    exact (timeEvolutionOp_mul_neg_self D_op s).2,
  by
    change timeEvolutionOp D_op s * ((timeEvolutionOp D_op s)†) = 1
    rw [star_timeEvolutionOp_dressing D_op hD s]
    exact (timeEvolutionOp_mul_neg_self D_op s).1⟩⟩

/-- If `P` and `X` commute with `Pi_sec`, so does `localKatoGeneratorTerm P X`. -/
lemma commute_localKatoGeneratorTerm_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {P X Pi_sec : E →L[ℂ] E}
    (hP : Commute P Pi_sec) (hX : Commute X Pi_sec) :
    Commute (localKatoGeneratorTerm P X) Pi_sec :=
  ((hP.mul_left hX).sub_left (hX.mul_left hP)).smul_left (Complex.I : ℂ)

/-- If every check `sys.checkProj i` commutes with `Pi_sec`, then `sys.P_loc A` commutes with `Pi_sec`. -/
lemma commute_P_loc_of_commute_checkProj_bh11 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_check : ∀ i : ι, Commute (sys.checkProj i) Pi_sec)
    (A : Finset (BoxD D L)) :
    Commute (sys.localGroundProj A) Pi_sec := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  apply Commute.list_prod_left
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  exact (Commute.one_left Pi_sec).sub_left (h_check i)

end
