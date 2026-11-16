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

import Proofs.BandLimitedFilter.AnchoredSitePerturbationOps

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Two-Block Diagonal Projections and Filtered Site Synthesis

Defines the two-block diagonal and off-diagonal operator projections `twoBlockDiagProj` and `twoBlockOffDiagProj` associated with a star projection, proving exact complementarity, norm bounds, and unconditional projector commutation. Introduces `twoBlockBochnerFilteredSiteOp` and proves global sum preservation when the total filtered Hamiltonian commutes with the subspace projector.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (76) (`eq:Xu-direct-def`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

/-!
## 1. Two-Block Diagonal & Off-Diagonal Projections (`twoBlockDiagProj`, `twoBlockOffDiagProj`)
-/

/-- Two-block diagonal projection of an operator `X` with respect to a projector `P`:
    $$\mathrm{twoBlockDiagProj}\ P\ X := P X P + (1 - P) X (1 - P).$$ -/
def twoBlockDiagProj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P X : E →L[ℂ] E) : E →L[ℂ] E :=
  P * X * P + (1 - P) * X * (1 - P)

/-- Off-diagonal complementary part of `X` with respect to `P`:
    $$\mathrm{twoBlockOffDiagProj}\ P\ X := P X (1 - P) + (1 - P) X P.$$ -/
def twoBlockOffDiagProj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P X : E →L[ℂ] E) : E →L[ℂ] E :=
  P * X * (1 - P) + (1 - P) * X * P

/-- Exact four-block partition of unity `twoBlockDiagProj P X + twoBlockOffDiagProj P X = X`
    (holds in any ring without idempotence of `P`). -/
theorem twoBlockDiagProj_add_twoBlockOffDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P X : E →L[ℂ] E) :
    twoBlockDiagProj P X + twoBlockOffDiagProj P X = X := by
  dsimp [twoBlockDiagProj, twoBlockOffDiagProj]
  calc (P * X * P + (1 - P) * X * (1 - P)) + (P * X * (1 - P) + (1 - P) * X * P)
    _ = (P + (1 - P)) * X * (P + (1 - P)) := by
      rw [add_mul, add_mul, mul_add, mul_add]; abel
    _ = 1 * X * 1 := by rw [add_sub_cancel]
    _ = X := by rw [one_mul, mul_one]

/-- The difference `X - twoBlockDiagProj P X` is `twoBlockOffDiagProj P X`. -/
theorem sub_twoBlockDiagProj_eq_twoBlockOffDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P X : E →L[ℂ] E) :
    X - twoBlockDiagProj P X = twoBlockOffDiagProj P X :=
  sub_eq_of_eq_add' (twoBlockDiagProj_add_twoBlockOffDiagProj P X).symm

/-- The difference `twoBlockDiagProj P X - X` is `-twoBlockOffDiagProj P X`. -/
theorem twoBlockDiagProj_sub_self_eq_neg_twoBlockOffDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P X : E →L[ℂ] E) :
    twoBlockDiagProj P X - X = -twoBlockOffDiagProj P X := by
  rw [← sub_twoBlockDiagProj_eq_twoBlockOffDiagProj, neg_sub]

/-- **Unconditional Commutation with $P$ (`commute_twoBlockDiagProj`)**:
    Whenever $P^2 = P$, `twoBlockDiagProj P X` commutes with $P$ for **all** $X$. -/
theorem commute_twoBlockDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP_idem : P * P = P) (X : E →L[ℂ] E) :
    Commute (twoBlockDiagProj P X) P := by
  have h_P_1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h_1P_P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP_idem, sub_self]
  rw [commute_iff_eq]
  dsimp [twoBlockDiagProj]
  rw [add_mul, mul_add,
    mul_assoc (P * X) P P, hP_idem,
    mul_assoc ((1 - P) * X) (1 - P) P, h_1P_P, mul_zero, add_zero,
    ← mul_assoc P (P * X) P, ← mul_assoc P P X, hP_idem,
    ← mul_assoc P ((1 - P) * X) (1 - P), ← mul_assoc P (1 - P) X, h_P_1P,
    zero_mul, zero_mul, add_zero]

/-- Specialization of `commute_twoBlockDiagProj` to any `IsStarProjection P`. -/
theorem commute_twoBlockDiagProj_of_isStarProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    Commute (twoBlockDiagProj P X) P :=
  commute_twoBlockDiagProj hP.isIdempotentElem.eq X

/-- Ground-block sandwiching `P * twoBlockDiagProj P X * P = P * X * P` when $P^2 = P$. -/
theorem mul_P_twoBlockDiagProj_mul_P {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP_idem : P * P = P) (X : E →L[ℂ] E) :
    P * twoBlockDiagProj P X * P = P * X * P := by
  have h_P_1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h1 : P * (P * X * P) * P = P * X * P := by
    calc P * (P * X * P) * P
      _ = (P * P) * X * (P * P) := by simp only [mul_assoc]
      _ = P * X * P := by rw [hP_idem]
  have h2 : P * ((1 - P) * X * (1 - P)) * P = 0 := by
    calc P * ((1 - P) * X * (1 - P)) * P
      _ = (P * (1 - P)) * X * (1 - P) * P := by simp only [mul_assoc]
      _ = 0 := by rw [h_P_1P, zero_mul, zero_mul, zero_mul]
  dsimp [twoBlockDiagProj]
  rw [mul_add, add_mul, h1, h2, add_zero]

/-- Excited-block sandwiching `(1 - P) * twoBlockDiagProj P X * (1 - P) = (1 - P) * X * (1 - P)`
    when $P^2 = P$. -/
theorem mul_one_sub_P_twoBlockDiagProj_mul_one_sub_P {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP_idem : P * P = P) (X : E →L[ℂ] E) :
    (1 - P) * twoBlockDiagProj P X * (1 - P) = (1 - P) * X * (1 - P) := by
  have h_P_1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h_1P_idem : (1 - P) * (1 - P) = 1 - P := by
    rw [mul_sub, sub_mul, one_mul, mul_one, sub_mul, one_mul, hP_idem, sub_self, sub_zero]
  have h1 : (1 - P) * (P * X * P) * (1 - P) = 0 := by
    calc (1 - P) * (P * X * P) * (1 - P)
      _ = (1 - P) * (P * X) * (P * (1 - P)) := by simp only [mul_assoc]
      _ = 0 := by rw [h_P_1P, mul_zero]
  have h2 : (1 - P) * ((1 - P) * X * (1 - P)) * (1 - P) = (1 - P) * X * (1 - P) := by
    calc (1 - P) * ((1 - P) * X * (1 - P)) * (1 - P)
      _ = ((1 - P) * (1 - P)) * X * ((1 - P) * (1 - P)) := by simp only [mul_assoc]
      _ = (1 - P) * X * (1 - P) := by rw [h_1P_idem]
  dsimp [twoBlockDiagProj]
  rw [mul_add, add_mul, h1, h2, zero_add]

/-- Off-diagonal blocks of `twoBlockDiagProj P X` vanish identically whenever $P^2 = P$. -/
theorem twoBlockDiagProj_offDiag_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP_idem : P * P = P) (X : E →L[ℂ] E) :
    P * twoBlockDiagProj P X * (1 - P) = 0 ∧
    (1 - P) * twoBlockDiagProj P X * P = 0 := by
  have h_comm := commute_twoBlockDiagProj hP_idem X
  have h_P_1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h_1P_P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP_idem, sub_self]
  refine ⟨?_, ?_⟩
  · rw [← h_comm.eq, mul_assoc, h_P_1P, mul_zero]
  · rw [mul_assoc, h_comm.eq, ← mul_assoc, h_1P_P, zero_mul]

/-- Idempotence of `twoBlockDiagProj P` whenever $P^2 = P$. -/
theorem twoBlockDiagProj_idem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP_idem : P * P = P) (X : E →L[ℂ] E) :
    twoBlockDiagProj P (twoBlockDiagProj P X) = twoBlockDiagProj P X := by
  change P * twoBlockDiagProj P X * P + (1 - P) * twoBlockDiagProj P X * (1 - P) =
    twoBlockDiagProj P X
  rw [mul_P_twoBlockDiagProj_mul_P hP_idem X,
    mul_one_sub_P_twoBlockDiagProj_mul_one_sub_P hP_idem X]
  rfl

/-- **Self-Adjointness of `twoBlockDiagProj P X` (`isSelfAdjoint_twoBlockDiagProj`)**:
    Whenever $P$ and $X$ are self-adjoint, `twoBlockDiagProj P X` is self-adjoint. -/
theorem isSelfAdjoint_twoBlockDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} (hP_sa : IsSelfAdjoint P) (hX_sa : IsSelfAdjoint X) :
    IsSelfAdjoint (twoBlockDiagProj P X) := by
  have h1P_sa : IsSelfAdjoint (1 - P) := (IsSelfAdjoint.one (E →L[ℂ] E)).sub hP_sa
  have h1 : IsSelfAdjoint (P * X * P) := by
    rw [IsSelfAdjoint, star_mul, star_mul, hP_sa.star_eq, hX_sa.star_eq, mul_assoc]
  have h2 : IsSelfAdjoint ((1 - P) * X * (1 - P)) := by
    rw [IsSelfAdjoint, star_mul, star_mul, h1P_sa.star_eq, hX_sa.star_eq, mul_assoc]
  exact h1.add h2

/-- Specialization of `isSelfAdjoint_twoBlockDiagProj` to `IsStarProjection P`. -/
theorem isSelfAdjoint_twoBlockDiagProj_of_isStarProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} (hP : IsStarProjection P) (hX_sa : IsSelfAdjoint X) :
    IsSelfAdjoint (twoBlockDiagProj P X) :=
  isSelfAdjoint_twoBlockDiagProj hP.isSelfAdjoint hX_sa

/-- Self-adjointness of `twoBlockOffDiagProj P X` when $P$ and $X$ are self-adjoint. -/
theorem isSelfAdjoint_twoBlockOffDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} (hP_sa : IsSelfAdjoint P) (hX_sa : IsSelfAdjoint X) :
    IsSelfAdjoint (twoBlockOffDiagProj P X) := by
  have h_eq : twoBlockOffDiagProj P X = X - twoBlockDiagProj P X :=
    (sub_twoBlockDiagProj_eq_twoBlockOffDiagProj P X).symm
  rw [h_eq]
  exact hX_sa.sub (isSelfAdjoint_twoBlockDiagProj hP_sa hX_sa)

/-- When $P^2 = P$ and `Commute X P`, the off-diagonal projection `twoBlockOffDiagProj P X` vanishes. -/
theorem twoBlockOffDiagProj_eq_zero_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} (hP_idem : P * P = P) (h_comm : Commute X P) :
    twoBlockOffDiagProj P X = 0 := by
  have h_P_1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h_1P_P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP_idem, sub_self]
  have h1 : P * X * (1 - P) = 0 := by
    rw [← h_comm.eq, mul_assoc, h_P_1P, mul_zero]
  have h2 : (1 - P) * X * P = 0 := by
    rw [mul_assoc, h_comm.eq, ← mul_assoc, h_1P_P, zero_mul]
  dsimp [twoBlockOffDiagProj]
  rw [h1, h2, add_zero]

/-- **Fixed-Point Characterization (`twoBlockDiagProj_eq_self_of_commute`)**:
    When $P^2 = P$ and `Commute X P`, `twoBlockDiagProj P X = X`. -/
theorem twoBlockDiagProj_eq_self_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} (hP_idem : P * P = P) (h_comm : Commute X P) :
    twoBlockDiagProj P X = X := by
  have h_part := twoBlockDiagProj_add_twoBlockOffDiagProj P X
  rw [twoBlockOffDiagProj_eq_zero_of_commute hP_idem h_comm, add_zero] at h_part
  exact h_part

/-- Specialization of `twoBlockDiagProj_eq_self_of_commute` to `IsStarProjection P`. -/
theorem twoBlockDiagProj_eq_self_of_isStarProjection_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} (hP : IsStarProjection P) (h_comm : Commute X P) :
    twoBlockDiagProj P X = X :=
  twoBlockDiagProj_eq_self_of_commute hP.isIdempotentElem.eq h_comm

/-- For $P^2 = P$, `Commute X P` holds if and only if `twoBlockDiagProj P X = X`. -/
theorem commute_iff_twoBlockDiagProj_eq_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} (hP_idem : P * P = P) :
    Commute X P ↔ twoBlockDiagProj P X = X := by
  constructor
  · exact twoBlockDiagProj_eq_self_of_commute hP_idem
  · intro h_eq
    rw [← h_eq]
    exact commute_twoBlockDiagProj hP_idem X

/-!
## 2. Linearity, Finite Sums, Sector Commutation & Norm/`condExp` Bounds
-/

@[simp]
theorem twoBlockDiagProj_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P : E →L[ℂ] E) :
    twoBlockDiagProj P 0 = 0 := by
  simp [twoBlockDiagProj]

theorem twoBlockDiagProj_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P X Y : E →L[ℂ] E) :
    twoBlockDiagProj P (X + Y) = twoBlockDiagProj P X + twoBlockDiagProj P Y := by
  dsimp [twoBlockDiagProj]
  rw [mul_add, add_mul, mul_add, add_mul]
  abel

theorem twoBlockDiagProj_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P X Y : E →L[ℂ] E) :
    twoBlockDiagProj P (X - Y) = twoBlockDiagProj P X - twoBlockDiagProj P Y := by
  have h_neg : twoBlockDiagProj P (-Y) = -twoBlockDiagProj P Y := by
    dsimp [twoBlockDiagProj]
    rw [mul_neg, neg_mul, mul_neg, neg_mul, neg_add]
  rw [sub_eq_add_neg, twoBlockDiagProj_add, h_neg, ← sub_eq_add_neg]

theorem twoBlockDiagProj_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P : E →L[ℂ] E) (c : ℂ) (X : E →L[ℂ] E) :
    twoBlockDiagProj P (c • X) = c • twoBlockDiagProj P X := by
  dsimp [twoBlockDiagProj]
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_add]

/-- Finite-sum linearity of `twoBlockDiagProj P`. -/
theorem twoBlockDiagProj_finset_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {α : Type*} (s : Finset α) (P : E →L[ℂ] E) (X : α → (E →L[ℂ] E)) :
    twoBlockDiagProj P (∑ u ∈ s, X u) = ∑ u ∈ s, twoBlockDiagProj P (X u) := by
  dsimp [twoBlockDiagProj]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

/-- **Exact Global Sum Preservation (`sum_twoBlockDiagProj_eq_sum_of_commute`)**:
    If $P^2 = P$ and the finite sum $\sum_{u \in s} X_u$ commutes with $P$, then
    $$\sum_{u \in s} \mathrm{twoBlockDiagProj}\ P\ (X_u) = \sum_{u \in s} X_u.$$ -/
theorem sum_twoBlockDiagProj_eq_sum_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {α : Type*} (s : Finset α) {P : E →L[ℂ] E} (hP_idem : P * P = P)
    (X : α → (E →L[ℂ] E)) (h_comm : Commute (∑ u ∈ s, X u) P) :
    (∑ u ∈ s, twoBlockDiagProj P (X u)) = ∑ u ∈ s, X u := by
  rw [← twoBlockDiagProj_finset_sum, twoBlockDiagProj_eq_self_of_commute hP_idem h_comm]

/-- Specialization of `sum_twoBlockDiagProj_eq_sum_of_commute` to `IsStarProjection P`. -/
theorem sum_twoBlockDiagProj_eq_of_commute_sum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {α : Type*} (s : Finset α) {P : E →L[ℂ] E} (hP : IsStarProjection P)
    (X : α → (E →L[ℂ] E)) (h_comm : Commute (∑ u ∈ s, X u) P) :
    (∑ u ∈ s, twoBlockDiagProj P (X u)) = ∑ u ∈ s, X u :=
  sum_twoBlockDiagProj_eq_sum_of_commute s hP.isIdempotentElem.eq X h_comm

/-- **Sector-Symmetry Preservation (`commute_twoBlockDiagProj_of_commute_both`)**:
    If both $P$ and $X$ commute with $\Pi_{\mathrm{sec}}$, then `twoBlockDiagProj P X` commutes
    with $\Pi_{\mathrm{sec}}$. -/
theorem commute_twoBlockDiagProj_of_commute_both {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X Pi_sec : E →L[ℂ] E} (hP_sec : Commute P Pi_sec) (hX_sec : Commute X Pi_sec) :
    Commute (twoBlockDiagProj P X) Pi_sec := by
  have h1P_sec : Commute (1 - P) Pi_sec := (Commute.one_left Pi_sec).sub_left hP_sec
  exact ((hP_sec.mul_left hX_sec).mul_left hP_sec).add_left
    ((h1P_sec.mul_left hX_sec).mul_left h1P_sec)

/-- Alias for `commute_twoBlockDiagProj_of_commute_both`. -/
theorem commute_twoBlockDiagProj_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X Pi_sec : E →L[ℂ] E} (hP_sec : Commute P Pi_sec) (hX_sec : Commute X Pi_sec) :
    Commute (twoBlockDiagProj P X) Pi_sec :=
  commute_twoBlockDiagProj_of_commute_both hP_sec hX_sec

/-- Operator norm bound `‖P‖ ≤ 1` for any star projection `P`. -/
private lemma isStarProjection_norm_le_one_twoBlock {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 := by
  by_cases h0 : ‖P‖ = 0
  · linarith
  · have h_pos : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg P) (Ne.symm h0)
    have h_sq : ‖P‖ * ‖P‖ ≤ 1 * ‖P‖ := by
      rw [one_mul, ← CStarRing.norm_star_mul_self, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
    exact le_of_mul_le_mul_right h_sq h_pos

/-- Sandwich norm bound `‖A * X * B‖ ≤ ‖X‖` when `‖A‖ ≤ 1` and `‖B‖ ≤ 1`. -/
private lemma norm_sandwich_le_norm_twoBlock {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A B : E →L[ℂ] E}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (X : E →L[ℂ] E) :
    ‖A * X * B‖ ≤ ‖X‖ := by
  calc ‖A * X * B‖
    _ ≤ ‖A * X‖ * ‖B‖ := norm_mul_le (A * X) B
    _ ≤ (‖A‖ * ‖X‖) * ‖B‖ := mul_le_mul_of_nonneg_right (norm_mul_le A X) (norm_nonneg B)
    _ ≤ (1 * ‖X‖) * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hA (norm_nonneg X)) hB
        (norm_nonneg B) (mul_nonneg zero_le_one (norm_nonneg X))
    _ = ‖X‖ := by ring

/-- Operator norm bound `‖twoBlockDiagProj P X‖ ≤ 2 * ‖X‖` for any star projection $P$. -/
theorem norm_twoBlockDiagProj_le_two_mul_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    ‖twoBlockDiagProj P X‖ ≤ 2 * ‖X‖ := by
  have hP_norm : ‖P‖ ≤ 1 := isStarProjection_norm_le_one_twoBlock hP
  have h1P_norm : ‖1 - P‖ ≤ 1 := isStarProjection_norm_le_one_twoBlock hP.one_sub
  have h1 : ‖P * X * P‖ ≤ ‖X‖ := norm_sandwich_le_norm_twoBlock hP_norm hP_norm X
  have h2 : ‖(1 - P) * X * (1 - P)‖ ≤ ‖X‖ := norm_sandwich_le_norm_twoBlock h1P_norm h1P_norm X
  dsimp [twoBlockDiagProj]
  linarith [norm_add_le (P * X * P) ((1 - P) * X * (1 - P))]

/-- Operator norm bound `‖twoBlockOffDiagProj P X‖ ≤ 2 * ‖X‖` for any star projection $P$. -/
theorem norm_twoBlockOffDiagProj_le_two_mul_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P : E →L[ℂ] E} (hP : IsStarProjection P) (X : E →L[ℂ] E) :
    ‖twoBlockOffDiagProj P X‖ ≤ 2 * ‖X‖ := by
  have hP_norm : ‖P‖ ≤ 1 := isStarProjection_norm_le_one_twoBlock hP
  have h1P_norm : ‖1 - P‖ ≤ 1 := isStarProjection_norm_le_one_twoBlock hP.one_sub
  have h1 : ‖P * X * (1 - P)‖ ≤ ‖X‖ := norm_sandwich_le_norm_twoBlock hP_norm h1P_norm X
  have h2 : ‖(1 - P) * X * P‖ ≤ ‖X‖ := norm_sandwich_le_norm_twoBlock h1P_norm hP_norm X
  dsimp [twoBlockOffDiagProj]
  linarith [norm_add_le (P * X * (1 - P)) ((1 - P) * X * P)]

/-- Triangle inequality bound on `twoBlockOffDiagProj P X` from individual off-diagonal block bounds. -/
theorem norm_twoBlockOffDiagProj_le_of_offDiag_bounds {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X : E →L[ℂ] E} {ε₁ ε₂ : ℝ}
    (h1 : ‖P * X * (1 - P)‖ ≤ ε₁) (h2 : ‖(1 - P) * X * P‖ ≤ ε₂) :
    ‖twoBlockOffDiagProj P X‖ ≤ ε₁ + ε₂ := by
  dsimp [twoBlockOffDiagProj]
  exact le_trans (norm_add_le _ _) (add_le_add h1 h2)

/-- **`condExp` Compatibility Bound for `twoBlockDiagProj` (`norm_twoBlockDiagProj_sub_condExp_le`)**:
    For any region $A$ and operators $P, X$,
    $$\|\mathrm{twoBlockDiagProj}\ P\ X - \mathbb{E}_A(\mathrm{twoBlockDiagProj}\ P\ X)\|
      \le \|X - \mathbb{E}_A(X)\| + 2 \|\mathrm{twoBlockOffDiagProj}\ P\ X\|.$$ -/
theorem norm_twoBlockDiagProj_sub_condExp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (P X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖twoBlockDiagProj P X - condExp Site A (twoBlockDiagProj P X)‖ ≤
      ‖X - condExp Site A X‖ + 2 * ‖twoBlockOffDiagProj P X‖ := by
  let Y := twoBlockDiagProj P X
  let R := twoBlockOffDiagProj P X
  have hY_eq : Y = X - R := by
    dsimp [Y, R]
    rw [← sub_twoBlockDiagProj_eq_twoBlockOffDiagProj P X, sub_sub_cancel]
  have h_diff : Y - condExp Site A Y = (X - condExp Site A X) - (R - condExp Site A R) := by
    rw [hY_eq, condExp_sub_clm]
    abel
  have hR_ce : ‖R - condExp Site A R‖ ≤ 2 * ‖R‖ := norm_sub_condExp_le_two_mul_norm A R
  change ‖Y - condExp Site A Y‖ ≤ ‖X - condExp Site A X‖ + 2 * ‖R‖
  rw [h_diff]
  exact le_trans (norm_sub_le _ _) (add_le_add le_rfl hR_ce)

/-- `condExp` tail bound for `twoBlockDiagProj P X` from `‖X - condExp Site A X‖ ≤ ε_tail` and
    off-diagonal bounds `‖P * X * (1 - P)‖ ≤ ε₁`, `‖(1 - P) * X * P‖ ≤ ε₂`. -/
theorem norm_twoBlockDiagProj_sub_condExp_le_of_offDiag_bounds {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    {P X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {ε_tail ε₁ ε₂ : ℝ}
    (h_tail : ‖X - condExp Site A X‖ ≤ ε_tail)
    (h1 : ‖P * X * (1 - P)‖ ≤ ε₁)
    (h2 : ‖(1 - P) * X * P‖ ≤ ε₂) :
    ‖twoBlockDiagProj P X - condExp Site A (twoBlockDiagProj P X)‖ ≤
      ε_tail + 2 * (ε₁ + ε₂) := by
  have h_base := norm_twoBlockDiagProj_sub_condExp_le A P X
  have h_off := norm_twoBlockOffDiagProj_le_of_offDiag_bounds h1 h2
  linarith

/-!
## 3. Two-Block Projected Bochner-Filtered Site Operator (`twoBlockBochnerFilteredSiteOp`)
-/

/-- **Two-Block Projected Bochner-Filtered Site Operator (`twoBlockBochnerFilteredSiteOp`)**:
    Projects `bochnerFilteredSiteOp H' U w V_u Q_u` onto the two diagonal blocks of $P$, ensuring
    exact commutation with $P$ for every unitary $U$ and Hamiltonian $H'$. -/
def twoBlockBochnerFilteredSiteOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  twoBlockDiagProj P (bochnerFilteredSiteOp H' U w V_u Q_u)

/-- `twoBlockBochnerFilteredSiteOp P H' U w V_u Q_u` commutes with $P$ whenever $P^2 = P$. -/
theorem commute_twoBlockBochnerFilteredSiteOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP_idem : P * P = P)
    (H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Commute (twoBlockBochnerFilteredSiteOp P H' U w V_u Q_u) P :=
  commute_twoBlockDiagProj hP_idem (bochnerFilteredSiteOp H' U w V_u Q_u)

/-- Self-adjointness of `twoBlockBochnerFilteredSiteOp` for `bhFilterWeight`. -/
theorem isSelfAdjoint_twoBlockBochnerFilteredSiteOp_w_BH11 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H' U V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP_sa : IsSelfAdjoint P) (hH' : IsSelfAdjoint H')
    (hV_u : IsSelfAdjoint V_u) (hQ_u : IsSelfAdjoint Q_u) :
    IsSelfAdjoint (twoBlockBochnerFilteredSiteOp P H' U bhFilterWeight V_u Q_u) :=
  isSelfAdjoint_twoBlockDiagProj hP_sa (isSelfAdjoint_bochnerFilteredSiteOp_w_BH11 hH' hV_u hQ_u)

/-- Sector-symmetry commutation of `twoBlockBochnerFilteredSiteOp` for `bhFilterWeight`. -/
theorem commute_twoBlockBochnerFilteredSiteOp_w_BH11_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H' U V_u Q_u Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsSelfAdjoint Pi_sec)
    (hP_sec : Commute P Pi_sec) (hH'_sec : Commute H' Pi_sec) (hU_sec : Commute U Pi_sec)
    (hV_sec : Commute V_u Pi_sec) (hQ_sec : Commute Q_u Pi_sec) :
    Commute (twoBlockBochnerFilteredSiteOp P H' U bhFilterWeight V_u Q_u) Pi_sec := by
  have h_conj_V : Commute (U† * V_u * U) Pi_sec := by
    have hU_adj : Commute (U†) Pi_sec := by
      rw [commute_iff_eq]
      have h_star : star (Pi_sec * U) = star (U * Pi_sec) := congrArg star hU_sec.symm.eq
      rw [star_mul, star_mul, hPi.star_eq] at h_star
      exact h_star
    exact (hU_adj.mul_left hV_sec).mul_left hU_sec
  have h_conj_Q : Commute (U† * Q_u * U) Pi_sec := by
    have hU_adj : Commute (U†) Pi_sec := by
      rw [commute_iff_eq]
      have h_star : star (Pi_sec * U) = star (U * Pi_sec) := congrArg star hU_sec.symm.eq
      rw [star_mul, star_mul, hPi.star_eq] at h_star
      exact h_star
    exact (hU_adj.mul_left hQ_sec).mul_left hU_sec
  have h_boch_V : Commute (bochnerFilteredOp H' bhFilterWeight (U† * V_u * U)) Pi_sec :=
    commute_bochnerFilteredOp_of_commute H' Pi_sec bhFilterWeight _ hH'_sec h_conj_V
      (integrable_w_BH11_smul_heisenbergFlow H' _)
  have h_boch_Q : Commute (bochnerFilteredOp H' bhFilterWeight (U† * Q_u * U)) Pi_sec :=
    commute_bochnerFilteredOp_of_commute H' Pi_sec bhFilterWeight _ hH'_sec h_conj_Q
      (integrable_w_BH11_smul_heisenbergFlow H' _)
  exact commute_twoBlockDiagProj_of_commute_both hP_sec
    (h_boch_V.add_left (h_boch_Q.sub_left hQ_sec))

/-- **Unconditional Global Energy Decomposition for `twoBlockBochnerFilteredSiteOp`
    (`sum_twoBlockBochnerFilteredSiteOp_eq_H'_sub_H0`)**:
    Whenever $P^2 = P$, $[H', P] = 0$, $[H_0, P] = 0$, $\sum_u V_u(u) = V_{\mathrm{tot}}$,
    $\sum_u Q_u(u) = H_0$, $H' = U^\dagger (H_0 + V_{\mathrm{tot}}) U$, and $\int w = 1$,
    $$\sum_{u \in \mathrm{BoxD}\ D\ L} \mathrm{twoBlockBochnerFilteredSiteOp}\ P\ H'\ U\ w\ (V_u\ u)\ (Q_u\ u)
      = H' - H_0.$$ -/
theorem sum_twoBlockBochnerFilteredSiteOp_eq_H'_sub_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H0 totalPerturbation H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (w : ℝ → ℂ)
    (V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hP_idem : P * P = P)
    (hH'_comm : Commute H' P) (hH0_comm : Commute H0 P)
    (hV_sum : (∑ u : BoxD D L, V_u u) = totalPerturbation)
    (hQ_sum : (∑ u : BoxD D L, Q_u u) = H0)
    (hH'_eq : H' = U† * (H0 + totalPerturbation) * U)
    (hw_one : (∫ t : ℝ, w t) = 1)
    (hint : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Integrable (fun t : ℝ => w t • heisenbergFlow H' t X)) :
    (∑ u : BoxD D L, twoBlockBochnerFilteredSiteOp P H' U w (V_u u) (Q_u u)) = H' - H0 ∧
    H0 + (∑ u : BoxD D L, twoBlockBochnerFilteredSiteOp P H' U w (V_u u) (Q_u u)) = H' := by
  have h_sum_raw :
      (∑ u : BoxD D L, bochnerFilteredSiteOp H' U w (V_u u) (Q_u u)) = H' - H0 :=
    (sum_bochnerFilteredSiteOp_eq_H'_sub_H0 H0 totalPerturbation H' U w V_u Q_u
      hV_sum hQ_sum hH'_eq hw_one hint).1
  have h_comm_sum :
      Commute (∑ u : BoxD D L, bochnerFilteredSiteOp H' U w (V_u u) (Q_u u)) P := by
    rw [h_sum_raw]
    exact hH'_comm.sub_left hH0_comm
  have h_tot :
      (∑ u : BoxD D L, twoBlockBochnerFilteredSiteOp P H' U w (V_u u) (Q_u u)) = H' - H0 := by
    unfold twoBlockBochnerFilteredSiteOp
    rw [sum_twoBlockDiagProj_eq_sum_of_commute Finset.univ hP_idem _ h_comm_sum, h_sum_raw]
  exact ⟨h_tot, by rw [h_tot, add_sub_cancel]⟩

/-- Specialization of `sum_twoBlockBochnerFilteredSiteOp_eq_H'_sub_H0` to `bhFilterWeight`. -/
theorem sum_twoBlockBochnerFilteredSiteOp_w_BH11_eq_H'_sub_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H0 totalPerturbation H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hP_idem : P * P = P)
    (hH'_comm : Commute H' P) (hH0_comm : Commute H0 P)
    (hV_sum : (∑ u : BoxD D L, V_u u) = totalPerturbation)
    (hQ_sum : (∑ u : BoxD D L, Q_u u) = H0)
    (hH'_eq : H' = U† * (H0 + totalPerturbation) * U) :
    (∑ u : BoxD D L, twoBlockBochnerFilteredSiteOp P H' U bhFilterWeight (V_u u) (Q_u u)) = H' - H0 ∧
    H0 + (∑ u : BoxD D L, twoBlockBochnerFilteredSiteOp P H' U bhFilterWeight (V_u u) (Q_u u)) = H' :=
  sum_twoBlockBochnerFilteredSiteOp_eq_H'_sub_H0 bhFilterWeight V_u Q_u hP_idem hH'_comm hH0_comm
    hV_sum hQ_sum hH'_eq integral_w_BH11_eq_one (integrable_w_BH11_smul_heisenbergFlow H')

/-- Explicit $O(J)$ operator norm bound for `twoBlockBochnerFilteredSiteOp` with `bhFilterWeight`. -/
theorem norm_twoBlockBochnerFilteredSiteOp_w_BH11_le_of_bare_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H0 totalPerturbation V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P)
    (hH : IsSelfAdjoint (H0 + totalPerturbation)) (h_comm : Commute H0 Q_u)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    ‖twoBlockBochnerFilteredSiteOp P (U.1† * (H0 + totalPerturbation) * U.1) U.1 bhFilterWeight V_u Q_u‖ ≤
      2 * (‖V_u‖ + Real.pi * ‖opCommutator totalPerturbation Q_u‖ + ‖U.1† * Q_u * U.1 - Q_u‖) := by
  rcases integrable_and_integral_norm_w_BH11_mul_abs_le with ⟨hw_t_int, hw_t_le⟩
  have h1 := norm_twoBlockDiagProj_le_two_mul_norm hP
    (bochnerFilteredSiteOp (U.1† * (H0 + totalPerturbation) * U.1) U.1 bhFilterWeight V_u Q_u)
  have h2 := norm_bochnerFilteredSiteOp_le_of_bare_commute (V_u := V_u) hH h_comm U
    integrable_w_BH11 integral_w_BH11_eq_one hw_t_int
  rw [integral_norm_w_BH11_eq_one, one_mul] at h2
  have h3 : (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) * ‖opCommutator totalPerturbation Q_u‖ ≤
      Real.pi * ‖opCommutator totalPerturbation Q_u‖ :=
    mul_le_mul_of_nonneg_right hw_t_le (norm_nonneg _)
  unfold twoBlockBochnerFilteredSiteOp
  linarith

end
