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

import Defs.SafeSubspaceAndKMS
import Proofs.SpectralAndGibbsLemmas
import Proofs.CubeTelescoping.SiteAnchoredBochnerDecomposition

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Cartesian Cube-Support Safe Immunity and Conditional-Expectation Commutator Bounds

Proves ground-projector commutation from left ideal stabilization, lifts cube-support safe-subspace immunity from self-adjoint operators to general bounded operators via Hermitian/anti-Hermitian splitting, and derives single-site conditional-expectation bath commutator bounds and enclosing-cube membership helpers.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
-/

/-! ## 1. Ground-Projector Decoder Commutation & Pinched Commutator Algebra -/

/-- If `P0`, `O_dec`, and `L_log` are self-adjoint, `O_dec * P0 = L_log * P0`, and `Commute P0 L_log`,
    then `Commute P0 O_dec` (discharging `Commute sys.P0 O_dec_Z` and `Commute sys.P0 O_dec_X`
    automatically from `h_logical_pair` and `h_decoder_props`). -/
theorem commute_P0_of_mul_P0_eq_and_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P0 O_dec L_log : E →L[ℂ] E}
    (hP0 : IsSelfAdjoint P0) (hO : IsSelfAdjoint O_dec) (hL : IsSelfAdjoint L_log)
    (h_eq : O_dec * P0 = L_log * P0) (h_comm : Commute P0 L_log) :
    Commute P0 O_dec := by
  rw [commute_iff_eq]
  have h_star : star (O_dec * P0) = star (L_log * P0) := congrArg star h_eq
  rw [star_mul, star_mul, hP0.star_eq, hO.star_eq, hL.star_eq, h_comm.eq] at h_star
  exact h_star.trans h_eq.symm

/-- Any operator `X` commuting with `O_dec` has zero pinched commutator `Pi_safe * (X * O_dec - O_dec * X) * Pi_safe = 0`. -/
lemma pi_safe_commutator_eq_zero_of_commute {R : Type*} [Ring R]
    (Pi_safe O_dec X : R) (h : Commute X O_dec) :
    Pi_safe * (X * O_dec - O_dec * X) * Pi_safe = 0 := by
  rw [h.eq, sub_self, mul_zero, zero_mul]

/-- Linearity of the pinched commutator under addition. -/
lemma pi_safe_commutator_add_eq_zero {R : Type*} [Ring R]
    (Pi_safe O_dec X Y : R)
    (hX : Pi_safe * (X * O_dec - O_dec * X) * Pi_safe = 0)
    (hY : Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0) :
    Pi_safe * ((X + Y) * O_dec - O_dec * (X + Y)) * Pi_safe = 0 := by
  have h_split :
      Pi_safe * ((X + Y) * O_dec - O_dec * (X + Y)) * Pi_safe =
        Pi_safe * (X * O_dec - O_dec * X) * Pi_safe +
        Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe := by
    noncomm_ring
  rw [h_split, hX, hY, add_zero]

/-- Linearity of the pinched commutator under subtraction. -/
lemma pi_safe_commutator_sub_eq_zero {R : Type*} [Ring R]
    (Pi_safe O_dec X Y : R)
    (hX : Pi_safe * (X * O_dec - O_dec * X) * Pi_safe = 0)
    (hY : Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0) :
    Pi_safe * ((X - Y) * O_dec - O_dec * (X - Y)) * Pi_safe = 0 := by
  have h_split :
      Pi_safe * ((X - Y) * O_dec - O_dec * (X - Y)) * Pi_safe =
        Pi_safe * (X * O_dec - O_dec * X) * Pi_safe -
        Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe := by
    noncomm_ring
  rw [h_split, hX, hY, sub_zero]

/-- Linearity of the pinched commutator under complex scalar multiplication. -/
lemma pi_safe_commutator_smul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (Pi_safe O_dec X : E →L[ℂ] E) (c : ℂ)
    (hX : Pi_safe * (X * O_dec - O_dec * X) * Pi_safe = 0) :
    Pi_safe * ((c • X) * O_dec - O_dec * (c • X)) * Pi_safe = 0 := by
  have h_smul :
      Pi_safe * ((c • X) * O_dec - O_dec * (c • X)) * Pi_safe =
        c • (Pi_safe * (X * O_dec - O_dec * X) * Pi_safe) := by
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, mul_smul_comm, smul_mul_assoc]
  rw [h_smul, hX, smul_zero]

/-- Linearity of the pinched commutator under finite sums. -/
lemma pi_safe_commutator_finset_sum_eq_zero {α : Type*} {R : Type*} [Ring R]
    (Pi_safe O_dec : R) (s : Finset α) (f : α → R)
    (hf : ∀ a ∈ s, Pi_safe * (f a * O_dec - O_dec * f a) * Pi_safe = 0) :
    Pi_safe * ((∑ a ∈ s, f a) * O_dec - O_dec * (∑ a ∈ s, f a)) * Pi_safe = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact pi_safe_commutator_add_eq_zero Pi_safe O_dec (f a) (∑ b ∈ s, f b)
      (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- Unitary pullback identity for the dressed pinched commutator. -/
lemma dressed_pinched_commutator_pullback {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U_dress : unitary (E →L[ℂ] E)) (Pi_safe O_dec X : E →L[ℂ] E) :
    (U_dress.1 * Pi_safe * (U_dress.1†)) *
      (X * (U_dress.1 * O_dec * (U_dress.1†)) - (U_dress.1 * O_dec * (U_dress.1†)) * X) *
      (U_dress.1 * Pi_safe * (U_dress.1†)) =
    U_dress.1 * (Pi_safe * ((U_dress.1† * X * U_dress.1) * O_dec -
      O_dec * (U_dress.1† * X * U_dress.1)) * Pi_safe) * (U_dress.1†) := by
  have h_star_mul : U_dress.1† * U_dress.1 = 1 := Unitary.coe_star_mul_self U_dress
  have h1 :
      (U_dress.1 * Pi_safe * (U_dress.1†)) * (X * (U_dress.1 * O_dec * (U_dress.1†))) *
        (U_dress.1 * Pi_safe * (U_dress.1†)) =
      U_dress.1 * (Pi_safe * ((U_dress.1† * X * U_dress.1) * O_dec) * Pi_safe) * (U_dress.1†) := by
    calc (U_dress.1 * Pi_safe * (U_dress.1†)) * (X * (U_dress.1 * O_dec * (U_dress.1†))) *
          (U_dress.1 * Pi_safe * (U_dress.1†))
      _ = U_dress.1 * (Pi_safe * (U_dress.1† * X * U_dress.1) * O_dec *
            (U_dress.1† * U_dress.1) * Pi_safe) * (U_dress.1†) := by simp only [mul_assoc]
      _ = U_dress.1 * (Pi_safe * ((U_dress.1† * X * U_dress.1) * O_dec) * Pi_safe) * (U_dress.1†) := by
            rw [h_star_mul, mul_one]; simp only [mul_assoc]
  have h2 :
      (U_dress.1 * Pi_safe * (U_dress.1†)) * ((U_dress.1 * O_dec * (U_dress.1†)) * X) *
        (U_dress.1 * Pi_safe * (U_dress.1†)) =
      U_dress.1 * (Pi_safe * (O_dec * (U_dress.1† * X * U_dress.1)) * Pi_safe) * (U_dress.1†) := by
    calc (U_dress.1 * Pi_safe * (U_dress.1†)) * ((U_dress.1 * O_dec * (U_dress.1†)) * X) *
          (U_dress.1 * Pi_safe * (U_dress.1†))
      _ = U_dress.1 * (Pi_safe * (U_dress.1† * U_dress.1) * O_dec *
            (U_dress.1† * X * U_dress.1) * Pi_safe) * (U_dress.1†) := by simp only [mul_assoc]
      _ = U_dress.1 * (Pi_safe * (O_dec * (U_dress.1† * X * U_dress.1)) * Pi_safe) * (U_dress.1†) := by
            rw [h_star_mul, mul_one]; simp only [mul_assoc]
  rw [mul_sub, sub_mul, h1, h2]
  simp only [mul_sub, sub_mul]

/-- Submultiplicative norm bound `‖U_dress.1 * M * (U_dress.1†)‖ ≤ ‖M‖` for a unitary operator. -/
lemma norm_unitary_conj_le_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U_dress : unitary (E →L[ℂ] E)) (M : E →L[ℂ] E) :
    ‖U_dress.1 * M * (U_dress.1†)‖ ≤ ‖M‖ := by
  let U_iso := unitaryToLinearIsometryEquiv U_dress
  have hU_norm : ∀ ψ : E, ‖U_dress.1 ψ‖ = ‖ψ‖ := U_iso.norm_map
  have hU_adj_norm : ∀ ψ : E, ‖(U_dress.1†) ψ‖ = ‖ψ‖ := U_iso.symm.norm_map
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M)
  intro ψ
  calc ‖(U_dress.1 * M * (U_dress.1†)) ψ‖
    _ = ‖U_dress.1 (M ((U_dress.1†) ψ))‖ := rfl
    _ = ‖M ((U_dress.1†) ψ)‖ := hU_norm _
    _ ≤ ‖M‖ * ‖(U_dress.1†) ψ‖ := ContinuousLinearMap.le_opNorm M _
    _ = ‖M‖ * ‖ψ‖ := by rw [hU_adj_norm]

/-- Abstract Hilbert-space QAC-tail pinched commutator bound:
    if `Pi_safe * (X_loc * O_dec - O_dec * X_loc) * Pi_safe = 0`, `IsStarProjection Pi_safe`, and `‖O_dec‖ ≤ 1`,
    then `‖Pi_safe_dress * [X, O_dec_dress] * Pi_safe_dress‖ ≤ 2 * ‖U_dress.1† * X * U_dress.1 - X_loc‖`. -/
theorem norm_dressed_pinched_commutator_le_two_mul_tail_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U_dress : unitary (E →L[ℂ] E)) (Pi_safe O_dec X X_loc : E →L[ℂ] E)
    (hPi : IsStarProjection Pi_safe) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_fw : Pi_safe * (X_loc * O_dec - O_dec * X_loc) * Pi_safe = 0) :
    ‖(U_dress.1 * Pi_safe * (U_dress.1†)) *
      (X * (U_dress.1 * O_dec * (U_dress.1†)) - (U_dress.1 * O_dec * (U_dress.1†)) * X) *
      (U_dress.1 * Pi_safe * (U_dress.1†))‖ ≤
    2 * ‖U_dress.1† * X * U_dress.1 - X_loc‖ := by
  let ΔX := U_dress.1† * X * U_dress.1 - X_loc
  rw [dressed_pinched_commutator_pullback]
  have h_sub_eq :
      Pi_safe * ((U_dress.1† * X * U_dress.1) * O_dec -
        O_dec * (U_dress.1† * X * U_dress.1)) * Pi_safe =
      Pi_safe * (ΔX * O_dec - O_dec * ΔX) * Pi_safe := by
    have h_split :
        (U_dress.1† * X * U_dress.1) * O_dec - O_dec * (U_dress.1† * X * U_dress.1) =
          (ΔX * O_dec - O_dec * ΔX) + (X_loc * O_dec - O_dec * X_loc) := by
      dsimp [ΔX]; noncomm_ring
    rw [h_split, mul_add, add_mul, h_fw, add_zero]
  rw [h_sub_eq]
  have hPi_norm : ‖Pi_safe‖ ≤ 1 := isStarProjection_norm_le_one_bhm hPi
  have h_sand : ‖Pi_safe * (ΔX * O_dec - O_dec * ΔX) * Pi_safe‖ ≤ ‖ΔX * O_dec - O_dec * ΔX‖ := by
    calc ‖Pi_safe * (ΔX * O_dec - O_dec * ΔX) * Pi_safe‖
      _ ≤ ‖Pi_safe * (ΔX * O_dec - O_dec * ΔX)‖ * ‖Pi_safe‖ := norm_mul_le _ _
      _ ≤ ‖Pi_safe * (ΔX * O_dec - O_dec * ΔX)‖ * 1 :=
        mul_le_mul_of_nonneg_left hPi_norm (norm_nonneg _)
      _ = ‖Pi_safe * (ΔX * O_dec - O_dec * ΔX)‖ := mul_one _
      _ ≤ ‖Pi_safe‖ * ‖ΔX * O_dec - O_dec * ΔX‖ := norm_mul_le _ _
      _ ≤ 1 * ‖ΔX * O_dec - O_dec * ΔX‖ :=
        mul_le_mul_of_nonneg_right hPi_norm (norm_nonneg _)
      _ = ‖ΔX * O_dec - O_dec * ΔX‖ := one_mul _
  have h_comm : ‖ΔX * O_dec - O_dec * ΔX‖ ≤ 2 * ‖ΔX‖ := by
    have h1 : ‖ΔX * O_dec‖ ≤ ‖ΔX‖ :=
      le_trans (norm_mul_le _ _) (le_trans (mul_le_mul_of_nonneg_left hO_norm (norm_nonneg _)) (by ring_nf; rfl))
    have h2 : ‖O_dec * ΔX‖ ≤ ‖ΔX‖ :=
      le_trans (norm_mul_le _ _) (le_trans (mul_le_mul_of_nonneg_right hO_norm (norm_nonneg _)) (by ring_nf; rfl))
    calc ‖ΔX * O_dec - O_dec * ΔX‖
      _ ≤ ‖ΔX * O_dec‖ + ‖O_dec * ΔX‖ := norm_sub_le _ _
      _ ≤ ‖ΔX‖ + ‖ΔX‖ := add_le_add h1 h2
      _ = 2 * ‖ΔX‖ := by ring
  exact le_trans (norm_unitary_conj_le_bhm U_dress _) (le_trans h_sand h_comm)

/-- Squared norm bound for dressed 1-site bath jump pinched commutators from a local approximation `L_loc`. -/
theorem sq_norm_dressed_pinched_commutator_le_of_tail_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U_dress : unitary (E →L[ℂ] E)) (Pi_safe O_dec L_op L_loc : E →L[ℂ] E)
    (hPi : IsStarProjection Pi_safe) (hO_norm : ‖O_dec‖ ≤ 1)
    {ε_LR δ_split : ℝ} (_hε_LR_nn : 0 ≤ ε_LR)
    (h_L_fw : Pi_safe * (L_loc * O_dec - O_dec * L_loc) * Pi_safe = 0)
    (h_L_tail : ‖U_dress.1† * L_op * U_dress.1 - L_loc‖ ≤ ε_LR * ‖L_op‖)
    (h_LR_split : 4 * ε_LR ^ 2 ≤ δ_split) :
    ‖(U_dress.1 * Pi_safe * (U_dress.1†)) *
      (L_op * (U_dress.1 * O_dec * (U_dress.1†)) - (U_dress.1 * O_dec * (U_dress.1†)) * L_op) *
      (U_dress.1 * Pi_safe * (U_dress.1†))‖ ^ 2 ≤
    ‖L_op‖ ^ 2 * δ_split := by
  let C_pinch :=
    (U_dress.1 * Pi_safe * (U_dress.1†)) *
      (L_op * (U_dress.1 * O_dec * (U_dress.1†)) - (U_dress.1 * O_dec * (U_dress.1†)) * L_op) *
      (U_dress.1 * Pi_safe * (U_dress.1†))
  have h_norm : ‖C_pinch‖ ≤ 2 * ε_LR * ‖L_op‖ := by
    have h1 := norm_dressed_pinched_commutator_le_two_mul_tail_bhm
      U_dress Pi_safe O_dec L_op L_loc hPi hO_norm h_L_fw
    change ‖C_pinch‖ ≤ 2 * ‖U_dress.1† * L_op * U_dress.1 - L_loc‖ at h1
    linarith
  have h_sq : ‖C_pinch‖ ^ 2 ≤ (2 * ε_LR * ‖L_op‖) ^ 2 := by
    nlinarith [norm_nonneg C_pinch, h_norm]
  calc ‖C_pinch‖ ^ 2
    _ ≤ (2 * ε_LR * ‖L_op‖) ^ 2 := h_sq
    _ = ‖L_op‖ ^ 2 * (4 * ε_LR ^ 2) := by ring
    _ ≤ ‖L_op‖ ^ 2 * δ_split := mul_le_mul_of_nonneg_left h_LR_split (sq_nonneg _)

/-! ## 2. Universal Cube-Support Safe-Subspace Immunity via Cartesian Decomposition -/

/-- Single-cube `QuasiLocalPerturbation` concentrated at a single scale `r₀` and cube `A₀` for a
    self-adjoint operator `Y` supported on `A₀`. -/
def singleCubePerturbation {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (r₀ : ℕ) (A₀ : Finset (BoxD D L))
    (Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hY_sa : IsSelfAdjoint Y) (hY_supp : IsSupportedOn Site A₀ Y) :
    QuasiLocalPerturbation D L Site where
  term r A := if r = r₀ ∧ A = A₀ then Y else 0
  is_selfAdjoint r A := by
    by_cases h : r = r₀ ∧ A = A₀
    · rw [if_pos h]; exact hY_sa
    · rw [if_neg h]; exact IsSelfAdjoint.zero (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  is_supported r _hr A _hA := by
    by_cases h : r = r₀ ∧ A = A₀
    · rw [if_pos h, h.2]; exact hY_supp
    · rw [if_neg h]; exact isSupportedOn_zero A

/-- Any self-adjoint operator `Y` supported on `A₀ ∈ BoxCubes D L r₀` ($1 \le r_0 \le R_{\mathrm{fw}}$)
    satisfies `Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0` under `QuasiLocalPerturbation` cube safe-subspace immunity. -/
theorem pi_safe_commutator_eq_zero_of_isSupportedOn_cube_selfAdjoint {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    {r₀ : ℕ} (hr₀ : r₀ ∈ Finset.Icc 1 R_fw)
    {A₀ : Finset (BoxD D L)} (hA₀ : A₀ ∈ boxCubes D L r₀)
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hY_sa : IsSelfAdjoint Y) (hY_supp : IsSupportedOn Site A₀ Y) :
    Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0 := by
  have h := h_fw (singleCubePerturbation r₀ A₀ Y hY_sa hY_supp) r₀ hr₀ A₀ hA₀
  dsimp [singleCubePerturbation] at h
  rw [if_pos ⟨rfl, rfl⟩] at h
  exact h

/-- Hermitian (real) Cartesian part $\frac{1}{2}(Y + Y^\dagger)$ of a bounded linear operator $Y$. -/
def hermitianPartOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (Y : E →L[ℂ] E) : E →L[ℂ] E :=
  (1 / 2 : ℂ) • (Y + Y†)

/-- Anti-Hermitian (imaginary) Cartesian part $-\frac{i}{2}(Y - Y^\dagger)$ of a bounded linear operator $Y$. -/
def antiHermitianPartOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (Y : E →L[ℂ] E) : E →L[ℂ] E :=
  (-(1 / 2 : ℂ) * Complex.I) • (Y - Y†)

lemma isSelfAdjoint_hermitianPartOp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (Y : E →L[ℂ] E) :
    IsSelfAdjoint (hermitianPartOp Y) := by
  rw [isSelfAdjoint_iff]
  dsimp [hermitianPartOp]
  rw [star_smul, star_add, show star (Y†) = Y from star_star Y, show star Y = Y† from rfl, add_comm]
  congr 1
  simp

lemma isSelfAdjoint_antiHermitianPartOp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (Y : E →L[ℂ] E) :
    IsSelfAdjoint (antiHermitianPartOp Y) := by
  rw [isSelfAdjoint_iff]
  dsimp [antiHermitianPartOp]
  rw [star_smul, star_sub, show star (Y†) = Y from star_star Y, show star Y = Y† from rfl]
  have h_sub : Y† - Y = -(Y - Y†) := (neg_sub Y (Y†)).symm
  rw [h_sub, smul_neg, ← neg_smul]
  congr 1
  simp [Complex.conj_I]

lemma hermitianPartOp_add_I_smul_antiHermitianPartOp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (Y : E →L[ℂ] E) :
    hermitianPartOp Y + Complex.I • antiHermitianPartOp Y = Y := by
  dsimp [hermitianPartOp, antiHermitianPartOp]
  rw [smul_smul]
  have h_coeff : Complex.I * (-(1 / 2 : ℂ) * Complex.I) = (1 / 2 : ℂ) := by
    calc Complex.I * (-(1 / 2 : ℂ) * Complex.I)
      _ = -(1 / 2 : ℂ) * (Complex.I * Complex.I) := by ring
      _ = -(1 / 2 : ℂ) * (-1) := by rw [Complex.I_mul_I]
      _ = (1 / 2 : ℂ) := by ring
  rw [h_coeff, ← smul_add, add_add_sub_cancel, ← two_smul ℂ Y, smul_smul]
  have h_one : (1 / 2 : ℂ) * 2 = 1 := by norm_num
  rw [h_one, one_smul]

/-- **Universal Cube-Support Safe-Subspace Immunity (`pi_safe_commutator_eq_zero_of_isSupportedOn_cube`)**:
    Under `QuasiLocalPerturbation` cube safe-subspace immunity up to radius `R_fw`, **every** operator `Y`
    (Hermitian or non-Hermitian) supported on any cube `A₀ ∈ BoxCubes D L r₀` ($1 \le r_0 \le R_{\mathrm{fw}}$)
    satisfies `Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0`. -/
theorem pi_safe_commutator_eq_zero_of_isSupportedOn_cube {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    {r₀ : ℕ} (hr₀ : r₀ ∈ Finset.Icc 1 R_fw)
    {A₀ : Finset (BoxD D L)} (hA₀ : A₀ ∈ boxCubes D L r₀)
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hY_supp : IsSupportedOn Site A₀ Y) :
    Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0 := by
  have hY_adj_supp : IsSupportedOn Site A₀ (Y†) := isSupportedOn_adjoint A₀ hY_supp
  have h_re_supp : IsSupportedOn Site A₀ (hermitianPartOp Y) :=
    isSupportedOn_smul A₀ _ (isSupportedOn_add A₀ hY_supp hY_adj_supp)
  have h_im_supp : IsSupportedOn Site A₀ (antiHermitianPartOp Y) :=
    isSupportedOn_smul A₀ _ (isSupportedOn_sub A₀ hY_supp hY_adj_supp)
  have h_re_zero := pi_safe_commutator_eq_zero_of_isSupportedOn_cube_selfAdjoint
    Pi_safe O_dec h_fw hr₀ hA₀ (isSelfAdjoint_hermitianPartOp Y) h_re_supp
  have h_im_zero := pi_safe_commutator_eq_zero_of_isSupportedOn_cube_selfAdjoint
    Pi_safe O_dec h_fw hr₀ hA₀ (isSelfAdjoint_antiHermitianPartOp Y) h_im_supp
  have h_comb := pi_safe_commutator_add_eq_zero Pi_safe O_dec
    (hermitianPartOp Y) (Complex.I • antiHermitianPartOp Y) h_re_zero
    (pi_safe_commutator_smul_eq_zero Pi_safe O_dec (antiHermitianPartOp Y) Complex.I h_im_zero)
  rwa [hermitianPartOp_add_I_smul_antiHermitianPartOp Y] at h_comb

lemma boxCube_mem_BoxCubes {D L : ℕ} (x0 : BoxD D L) (r : ℕ) :
    boxCube x0 r ∈ boxCubes D L r :=
  Finset.mem_image_of_mem _ (Finset.mem_univ x0)

/-- Specialization of `pi_safe_commutator_eq_zero_of_isSupportedOn_cube` to `A₀ = boxCube x0 r₀`. -/
theorem pi_safe_commutator_eq_zero_of_isSupportedOn_boxCube {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    (x0 : BoxD D L) {r₀ : ℕ} (hr₀ : r₀ ∈ Finset.Icc 1 R_fw)
    {Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hY_supp : IsSupportedOn Site (boxCube x0 r₀) Y) :
    Pi_safe * (Y * O_dec - O_dec * Y) * Pi_safe = 0 :=
  pi_safe_commutator_eq_zero_of_isSupportedOn_cube Pi_safe O_dec h_fw hr₀
    (boxCube_mem_BoxCubes x0 r₀) hY_supp

/-! ## 3. Conditional Expectation (`condExp`) Safe-Subspace Immunity & 1-Site Bath Pinched Commutator Bound -/

/-- For any `v : BoxD D L`, `r ∈ Finset.Icc 1 R_fw`, and operator `X`, the local conditional expectation
    `condExp Site (boxCube v r) X` has zero bare pinched commutator with `O_dec` on `Pi_safe`. -/
theorem pi_safe_commutator_condExp_boxCube_eq_zero {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    (v : BoxD D L) {r : ℕ} (hr : r ∈ Finset.Icc 1 R_fw)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Pi_safe * (condExp Site (boxCube v r) X * O_dec -
      O_dec * condExp Site (boxCube v r) X) * Pi_safe = 0 :=
  pi_safe_commutator_eq_zero_of_isSupportedOn_boxCube Pi_safe O_dec h_fw v hr
    (isSupportedOn_condExp Site (boxCube v r) X)

/-- **1-Site Bath Pinched Commutator Squared Bound via `condExp` (`one_site_dressed_pinched_commutator_sq_le_of_condExp_tail`)**:
    Under `QuasiLocalPerturbation` cube safe-subspace immunity up to radius `R_fw`, if `r_LR ∈ Finset.Icc 1 R_fw` and
    `‖U_dress.1† * A_v * U_dress.1 - condExp Site (boxCube v r_LR) (U_dress.1† * A_v * U_dress.1)‖ ≤ ε_LR * ‖A_v‖`
    with `4 * ε_LR ^ 2 ≤ δ_split`, then `h_oneSite_safe` holds with no existential `A_loc` obligations. -/
theorem one_site_dressed_pinched_commutator_sq_le_of_condExp_tail {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    (v : BoxD D L) {r_LR : ℕ} (hr_LR : r_LR ∈ Finset.Icc 1 R_fw)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {ε_LR δ_split : ℝ} (hε_LR_nn : 0 ≤ ε_LR)
    (h_tail : ‖U_dress.1† * A_v * U_dress.1 -
      condExp Site (boxCube v r_LR) (U_dress.1† * A_v * U_dress.1)‖ ≤ ε_LR * ‖A_v‖)
    (h_LR_split : 4 * ε_LR ^ 2 ≤ δ_split) :
    ‖(U_dress.1 * Pi_safe * (U_dress.1†)) *
      (A_v * (U_dress.1 * O_dec * (U_dress.1†)) - (U_dress.1 * O_dec * (U_dress.1†)) * A_v) *
      (U_dress.1 * Pi_safe * (U_dress.1†))‖ ^ 2 ≤
    ‖A_v‖ ^ 2 * δ_split :=
  sq_norm_dressed_pinched_commutator_le_of_tail_bhm U_dress Pi_safe O_dec A_v
    (condExp Site (boxCube v r_LR) (U_dress.1† * A_v * U_dress.1))
    hPi hO_norm hε_LR_nn
    (pi_safe_commutator_condExp_boxCube_eq_zero Pi_safe O_dec h_fw v hr_LR _)
    h_tail h_LR_split

/-! ## 4. Enclosing-Cube Membership & Linear Expansion Radius Monotonicity -/

lemma enclosingBoxCube_mem_BoxCubes {D L : ℕ} (x0 : BoxD D L) (r R : ℕ) :
    enclosingBoxCube x0 r R ∈ boxCubes D L R :=
  boxCube_mem_BoxCubes _ R

lemma singleCubeSupportC_mem_BoxCubes {D L : ℕ} (C : ℝ) (u : BoxD D L) (k : ℕ) :
    singleCubeSupportC C u k ∈
      boxCubes D L (linearExpansionRadius C (k + bhmElementaryCubeSide)) :=
  enclosingBoxCube_mem_BoxCubes _ _ _

lemma one_le_linearExpansionRadius_add_elementary {C : ℝ} (hC : 1 ≤ C) (k : ℕ) :
    1 ≤ linearExpansionRadius C (k + bhmElementaryCubeSide) := by
  have h1 : 1 ≤ k + bhmElementaryCubeSide := by
    dsimp [bhmElementaryCubeSide]; omega
  exact le_trans h1 (self_le_linearExpansionRadius_bhm hC (k + bhmElementaryCubeSide))

lemma linearExpansionRadius_mono {C : ℝ} (hC : 0 ≤ C) {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂) :
    linearExpansionRadius C r₁ ≤ linearExpansionRadius C r₂ :=
  Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr) hC)

end
