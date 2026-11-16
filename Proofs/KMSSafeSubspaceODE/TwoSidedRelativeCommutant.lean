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

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Defs.SafeSubspaceAndKMS

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

noncomputable section

/-!
# Safe-Subspace Relative Commutant and Decoded Observable Immunity

Proves that `bareDecodedLogicalOp` is a self-adjoint involution commuting with all stabilizer check projectors (`bareDecodedLogicalOp_involution_and_commute`) and that `bareFailureProjector` and its safe-subspace complement are orthogonal projections (`isStarProjection_bareFailureProjector_and_compl`). Establishes two-sided commutator annihilation on the safe syndrome subspace from decoder discrepancy invariance (`safe_sector_commutator_zero_of_commute_checks`, `satisfiesTwoSidedOperatorImmunity_of_preservesDecoderDiscrepancy`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 2 (`subsec:setup`), Definition 2.5 (`def:syndrome-safe`)
* Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`)
-/

/-! ## 1. Commuting Star-Projection and Scalar Algebra Helpers -/

lemma commute_one_sub_left {R : Type*} [Ring R] {a b : R} (h : Commute a b) :
    Commute (1 - a) b := by
  rw [commute_iff_eq, sub_mul, mul_sub, one_mul, mul_one, h.eq]

lemma commute_one_sub_right {R : Type*} [Ring R] {a b : R} (h : Commute a b) :
    Commute a (1 - b) := by
  rw [commute_iff_eq, mul_sub, sub_mul, mul_one, one_mul, h.eq]

lemma isStarProjection_apply_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    P (P ψ) = P ψ := by
  change (P * P) ψ = P ψ; rw [hP.isIdempotentElem.eq]

lemma isStarProjection_inner_eq_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    inner ℂ ψ (P ψ) = ((‖P ψ‖ ^ 2 : ℝ) : ℂ) := by
  have h_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  nth_rw 1 [← isStarProjection_apply_self hP ψ]
  rw [← ContinuousLinearMap.adjoint_inner_left, h_adj, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma isStarProjection_re_inner_eq_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    RCLike.re (inner ℂ ψ (P ψ)) = ‖P ψ‖ ^ 2 := by
  rw [isStarProjection_inner_eq_norm_sq hP ψ]; rfl

lemma _root_.IsStarProjection.re_inner_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    0 ≤ RCLike.re (inner ℂ ψ (P ψ)) := by
  rw [isStarProjection_re_inner_eq_norm_sq hP ψ]; positivity

lemma clm_smul_mul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) : (c • A) * B = c • (A * B) := by ext φ; rfl

lemma clm_mul_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (c : ℂ) (A B : H →L[ℂ] H) : A * (c • B) = c • (A * B) := by ext φ; exact map_smul A c (B φ)

lemma isStarProjection_pythagorean {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    ‖ψ‖ ^ 2 = ‖P ψ‖ ^ 2 + ‖(1 - P) ψ‖ ^ 2 := by
  rw [← isStarProjection_re_inner_eq_norm_sq hP ψ,
    ← isStarProjection_re_inner_eq_norm_sq hP.one_sub ψ, ← map_add, ← inner_add_right]
  have h_sum : P ψ + (1 - P) ψ = ψ := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
  rw [h_sum, inner_self_eq_norm_sq_to_K]; norm_cast

lemma isStarProjection_norm_sq_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    ‖P ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  rw [isStarProjection_pythagorean hP ψ]; linarith [sq_nonneg ‖(1 - P) ψ‖]

lemma isStarProjection_norm_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ; rw [one_mul]
  have h_sq := isStarProjection_norm_sq_apply_le hP ψ
  nlinarith [norm_nonneg (P ψ), norm_nonneg ψ]

lemma isStarProjection_list_prod {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E))
    (hl_proj : ∀ p ∈ l, IsStarProjection p) (hl_comm : l.Pairwise Commute) :
    IsStarProjection l.prod := by
  induction l with
  | nil =>
    rw [List.prod_nil]; exact ⟨IsIdempotentElem.one, IsSelfAdjoint.one (E →L[ℂ] E)⟩
  | cons p tail ih =>
    rw [List.prod_cons]
    rcases List.pairwise_cons.mp hl_comm with ⟨h_p_comm, h_tail_comm⟩
    have hp : IsStarProjection p := hl_proj p List.mem_cons_self
    have htail : IsStarProjection tail.prod :=
      ih (fun q hq => hl_proj q (List.mem_cons_of_mem p hq)) h_tail_comm
    exact hp.mul htail (Commute.list_prod_right tail p h_p_comm)

lemma one_sub_mul_list_prod_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E)) (p : E →L[ℂ] E)
    (hp_mem : p ∈ l) (hp_idem : IsIdempotentElem p) (hp_comm : ∀ q ∈ l, Commute p q) :
    (1 - p) * l.prod = 0 := by
  induction l with
  | nil => cases hp_mem
  | cons q tail ih =>
    rw [List.prod_cons, ← mul_assoc]
    rcases List.mem_cons.mp hp_mem with rfl | hp_tail
    · have h_zero : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp_idem.eq, sub_self]
      rw [h_zero, zero_mul]
    · have h_comm : Commute (1 - p) q := commute_one_sub_left (hp_comm q List.mem_cons_self)
      rw [h_comm.eq, mul_assoc, ih hp_tail (fun r hr => hp_comm r (List.mem_cons_of_mem q hr)),
        mul_zero]

lemma list_prod_mul_eq_right {R : Type*} [Monoid R] (l : List R) (x : R)
    (h : ∀ a ∈ l, a * x = x) : l.prod * x = x := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    rw [List.prod_cons, mul_assoc, ih (fun b hb => h b (List.mem_cons_of_mem a hb)),
      h a List.mem_cons_self]

lemma isStarProjection_bareSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (σ : SyndromeConfig D L) :
    IsStarProjection (bareSyndromeProjector sys σ) := by
  dsimp [bareSyndromeProjector]
  apply isStarProjection_list_prod
  · intro p hp
    rcases List.mem_map.mp hp with ⟨K, hK_mem, rfl⟩
    have hK : K ∈ boxCubes D L 2 := Finset.mem_toList.mp hK_mem
    split_ifs
    · exact sys.is_projector K hK
    · exact (sys.is_projector K hK).one_sub
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (boxCubes D L 2).nodup_toList
    intro K₁ K₂ hK₁ hK₂ _
    have h₁ : K₁ ∈ boxCubes D L 2 := Finset.mem_toList.mp hK₁
    have h₂ : K₂ ∈ boxCubes D L 2 := Finset.mem_toList.mp hK₂
    have h_comm := sys.pairwise_commute K₁ h₁ K₂ h₂
    split_ifs
    · exact h_comm
    · exact commute_one_sub_right h_comm
    · exact commute_one_sub_left h_comm
    · exact commute_one_sub_right (commute_one_sub_left h_comm)

lemma clm_sub_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : ℂ) (A : E →L[ℂ] E) : (a - b) • A = a • A - b • A := by
  ext ψ; simp [sub_smul]

lemma clm_zero_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) : (0 : ℂ) • A = 0 := by
  ext ψ; simp

lemma commute_smul_right_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A B : E →L[ℂ] E} (h : Commute A B) (c : ℂ) : Commute A (c • B) := by
  rw [commute_iff_eq, clm_mul_smul, clm_smul_mul, h.eq]

lemma star_ite_neg_one_one (b : Bool) :
    star (if b then (-1 : ℂ) else (1 : ℂ)) = (if b then (-1 : ℂ) else (1 : ℂ)) := by
  cases b <;> simp

lemma ite_neg_one_one_mul_self (b : Bool) :
    (if b then (-1 : ℂ) else (1 : ℂ)) * (if b then (-1 : ℂ) else (1 : ℂ)) = 1 := by
  cases b <;> simp

lemma ite_neg_one_one_eq_mul_of_xor_eq {b₁ b₂ b_L : Bool} (h : Bool.xor b₁ b₂ = b_L) :
    (if b₂ then (-1 : ℂ) else (1 : ℂ)) =
      (if b₁ then (-1 : ℂ) else (1 : ℂ)) * (if b_L then (-1 : ℂ) else (1 : ℂ)) := by
  subst h; cases b₁ <;> cases b₂ <;> simp

lemma isSelfAdjoint_ite_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (b : Bool) {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) :
    IsSelfAdjoint ((if b then (-1 : ℂ) else (1 : ℂ)) • P) := by
  rw [IsSelfAdjoint, star_smul, star_ite_neg_one_one, hP.star_eq]

lemma commute_bareSyndromeProjector_of_commute_Q {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hX : ∀ K ∈ boxCubes D L 2, Commute (sys.Q K) X) (σ : SyndromeConfig D L) :
    Commute X (bareSyndromeProjector sys σ) := by
  dsimp [bareSyndromeProjector]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨K, hK_mem, rfl⟩
  have hK : K ∈ boxCubes D L 2 := Finset.mem_toList.mp hK_mem
  cases σ K
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact commute_one_sub_right (hX K hK).symm
  · simp only [↓reduceIte]; exact (hX K hK).symm

lemma commute_Q_bareSyndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {K : Finset (BoxD D L)} (hK : K ∈ boxCubes D L 2) (σ : SyndromeConfig D L) :
    Commute (sys.Q K) (bareSyndromeProjector sys σ) :=
  commute_bareSyndromeProjector_of_commute_Q sys
    (fun K' hK' => sys.pairwise_commute K' hK' K hK) σ

lemma sum_smul_bareSyndromeProjector_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (S_real : Finset (SyndromeConfig D L))
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0)
    (c : SyndromeConfig D L → ℂ) {σ : SyndromeConfig D L} (hσ : σ ∈ S_real) :
    (∑ τ ∈ S_real, c τ • bareSyndromeProjector sys τ) * bareSyndromeProjector sys σ =
      c σ • bareSyndromeProjector sys σ := by
  rw [Finset.sum_mul, Finset.sum_eq_single σ]
  · rw [clm_smul_mul, (isStarProjection_bareSyndromeProjector sys σ).isIdempotentElem.eq]
  · intro τ hτ hne; rw [clm_smul_mul, h_orth τ hτ σ hσ hne, smul_zero]
  · intro h_not_mem; exact False.elim (h_not_mem hσ)

lemma bareSyndromeProjector_mul_sum_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (S_real : Finset (SyndromeConfig D L))
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0)
    (c : SyndromeConfig D L → ℂ) {σ : SyndromeConfig D L} (hσ : σ ∈ S_real) :
    bareSyndromeProjector sys σ * (∑ τ ∈ S_real, c τ • bareSyndromeProjector sys τ) =
      c σ • bareSyndromeProjector sys σ := by
  rw [Finset.mul_sum, Finset.sum_eq_single σ]
  · rw [clm_mul_smul, (isStarProjection_bareSyndromeProjector sys σ).isIdempotentElem.eq]
  · intro τ hτ hne; rw [clm_mul_smul, h_orth σ hσ τ hτ (Ne.symm hne), smul_zero]
  · intro h_not_mem; exact False.elim (h_not_mem hσ)

lemma eq_mul_add_one_sub_mul_mul_of_one_sub_sandwich_eq_zero
    {R : Type*} [Ring R] (P C : R) (h : (1 - P) * C * (1 - P) = 0) :
    C = P * C + (1 - P) * C * P := by
  have h1 : (1 - P) * C = (1 - P) * C * P := by
    rw [mul_sub, mul_one, sub_eq_zero] at h; exact h
  calc C
    _ = 1 * C := (one_mul C).symm
    _ = (P + (1 - P)) * C := by rw [add_sub_cancel]
    _ = P * C + (1 - P) * C := add_mul P (1 - P) C
    _ = P * C + (1 - P) * C * P := by rw [← h1]

/-! ## 2. Safe-Subspace Projections, Decoded Logical Involutions, and Safe-Subspace Immunity -/

/-- **Decoded Logical Observable Involution and Check Commutation (`bareDecodedLogicalOp_involution_and_commute`; Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`))**:
    For any commuting-projector Hamiltonian `sys`, pairwise orthogonal syndrome resolution
    `S_real`, and self-adjoint logical involution `L_bare` commuting with every check `sys.Q K`,
    the bare homology-decoded observable `O := bareDecodedLogicalOp sys S_real L_bare ψ_dec` is a
    self-adjoint involution commuting with `sys.Q K` and `sys.H0`. -/
theorem bareDecodedLogicalOp_involution_and_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (V : LocalPerturbation D L Site)
    (S_real : Finset (SyndromeConfig D L))
    (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_dec : SyndromeConfig D L → Bool)
    (h_sum_one : (∑ σ ∈ S_real, bareSyndromeProjector sys σ) = 1)
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0)
    (hL_sa : IsSelfAdjoint L_bare)
    (hL_sq : L_bare * L_bare = 1)
    (hL_comm : ∀ K ∈ boxCubes D L 2, Commute (sys.Q K) L_bare) :
    let O := bareDecodedLogicalOp sys S_real L_bare ψ_dec
    IsSelfAdjoint O ∧
    O * O = 1 ∧
    (∀ K ∈ boxCubes D L 2, Commute (sys.Q K) O) ∧
    opCommutator sys.H0 O = 0 ∧
    opCommutator (sys.H0 + V.totalPerturbation) O = opCommutator V.totalPerturbation O := by
  intro O
  let c : SyndromeConfig D L → ℂ := fun σ => if ψ_dec σ then (-1 : ℂ) else (1 : ℂ)
  let S_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
    ∑ σ ∈ S_real, c σ • bareSyndromeProjector sys σ
  have hO_def : O = L_bare * S_op := rfl
  have hL_comm_P : ∀ σ : SyndromeConfig D L, Commute L_bare (bareSyndromeProjector sys σ) :=
    commute_bareSyndromeProjector_of_commute_Q sys hL_comm
  have hL_comm_S : Commute L_bare S_op := by
    dsimp [S_op]; apply Commute.sum_right
    intro σ _; exact commute_smul_right_clm (hL_comm_P σ) (c σ)
  have hS_sa : IsSelfAdjoint S_op := by
    dsimp [S_op, c]; apply isSelfAdjoint_finset_sum
    intro σ _
    exact isSelfAdjoint_ite_smul (ψ_dec σ)
      (isStarProjection_bareSyndromeProjector sys σ).isSelfAdjoint
  have hS_sq : S_op * S_op = 1 := by
    calc S_op * S_op
      _ = ∑ σ ∈ S_real, S_op * (c σ • bareSyndromeProjector sys σ) := Finset.mul_sum _ _ _
      _ = ∑ σ ∈ S_real, bareSyndromeProjector sys σ := by
        refine Finset.sum_congr rfl (fun σ hσ => ?_)
        rw [clm_mul_smul, sum_smul_bareSyndromeProjector_mul sys S_real h_orth c hσ,
          smul_smul, ite_neg_one_one_mul_self, one_smul]
      _ = 1 := h_sum_one
  have hO_sa : IsSelfAdjoint O := by
    rw [IsSelfAdjoint, hO_def, star_mul, hS_sa.star_eq, hL_sa.star_eq, hL_comm_S.eq]
  have hO_sq : O * O = 1 := by
    calc O * O
      _ = L_bare * (S_op * L_bare) * S_op := by rw [hO_def]; simp only [mul_assoc]
      _ = (L_bare * L_bare) * (S_op * S_op) := by rw [← hL_comm_S.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hL_sq, hS_sq, mul_one]
  have hQ_comm_O : ∀ K ∈ boxCubes D L 2, Commute (sys.Q K) O := by
    intro K hK; rw [hO_def]; refine (hL_comm K hK).mul_right ?_
    dsimp [S_op]; apply Commute.sum_right
    intro σ _; exact commute_smul_right_clm (commute_Q_bareSyndromeProjector sys hK σ) (c σ)
  have hH0_comm_O : Commute sys.H0 O := by
    dsimp [CommutingProjectorHamiltonian.H0]; apply Commute.sum_left
    intro K hK; exact hQ_comm_O K hK
  have h_comm_H0_O : opCommutator sys.H0 O = 0 := by
    dsimp [opCommutator]; exact sub_eq_zero.mpr hH0_comm_O.eq
  have h_comm_H0_V_O : opCommutator (sys.H0 + V.totalPerturbation) O = opCommutator V.totalPerturbation O := by
    calc opCommutator (sys.H0 + V.totalPerturbation) O
      _ = opCommutator sys.H0 O + opCommutator V.totalPerturbation O := by
        dsimp [opCommutator]; rw [add_mul, mul_add]; abel
      _ = opCommutator V.totalPerturbation O := by rw [h_comm_H0_O, zero_add]
  exact ⟨hO_sa, hO_sq, hQ_comm_O, h_comm_H0_O, h_comm_H0_V_O⟩

/-- **Failure and Safe-Subspace Star-Projections (`isStarProjection_bareFailureProjector_and_compl`; Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`))**:
    Star-projection properties of `bareFailureProjector` and its complement `1 - P_fail`. -/
theorem isStarProjection_bareFailureProjector_and_compl {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (S_real F_fail : Finset (SyndromeConfig D L))
    (hF_sub : F_fail ⊆ S_real)
    (h_sum_one : (∑ σ ∈ S_real, bareSyndromeProjector sys σ) = 1)
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0) :
    let P_fail := bareFailureProjector sys F_fail
    IsStarProjection P_fail ∧
    IsStarProjection (1 - P_fail) ∧
    1 - P_fail = ∑ σ ∈ S_real \ F_fail, bareSyndromeProjector sys σ := by
  intro P_fail
  have hP_fail_proj : IsStarProjection P_fail := by
    dsimp [P_fail, bareFailureProjector]
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [Finset.sum_mul, Finset.sum_eq_single σ]
      · exact (isStarProjection_bareSyndromeProjector sys σ).isIdempotentElem.eq
      · intro τ hτ hne; exact h_orth τ (hF_sub hτ) σ (hF_sub hσ) hne
      · intro h_not_mem; exact False.elim (h_not_mem hσ)
    · apply isSelfAdjoint_finset_sum
      intro σ _; exact (isStarProjection_bareSyndromeProjector sys σ).isSelfAdjoint
  have h_one_sub_P_fail_eq :
      1 - P_fail = ∑ σ ∈ S_real \ F_fail, bareSyndromeProjector sys σ := by
    dsimp [P_fail, bareFailureProjector]
    have h_split := Finset.sum_sdiff hF_sub (f := fun σ => bareSyndromeProjector sys σ)
    rw [h_sum_one] at h_split
    exact sub_eq_of_eq_add h_split.symm
  exact ⟨hP_fail_proj, hP_fail_proj.one_sub, h_one_sub_P_fail_eq⟩

/-- **Safe-Subspace Commutator Annihilation (`safe_sector_commutator_zero_of_commute_checks`; Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`))**:
    Two-sided safe-subspace immunity annihilation identity: if a local operator $A$ has parity $b_L$
    with respect to $L_{\mathrm{bare}}$ and preserves decoder sign discrepancy across all safe
    syndrome pairs $\sigma_1, \sigma_2 \in S_{\mathrm{real}} \setminus F_{\mathrm{fail}}$, then
    $\Pi_{\sigma_1} [A, O] \Pi_{\sigma_2} = 0$ and `SatisfiesTwoSidedOperatorImmunity sys F_fail O A`. -/
theorem safe_sector_commutator_zero_of_commute_checks {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (S_real F_fail : Finset (SyndromeConfig D L))
    (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_dec : SyndromeConfig D L → Bool)
    (hF_sub : F_fail ⊆ S_real)
    (h_sum_one : (∑ σ ∈ S_real, bareSyndromeProjector sys σ) = 1)
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0)
    (hL_comm : ∀ K ∈ boxCubes D L 2, Commute (sys.Q K) L_bare)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (b_L : Bool)
    (hA_comm : L_bare * A = ((if b_L then (-1 : ℂ) else (1 : ℂ)) • A) * L_bare)
    (hA_discrep : ∀ σ₁ ∈ S_real \ F_fail, ∀ σ₂ ∈ S_real \ F_fail,
      bareSyndromeProjector sys σ₁ * A * bareSyndromeProjector sys σ₂ = 0 ∨
      Bool.xor (ψ_dec σ₁) (ψ_dec σ₂) = b_L) :
    let O := bareDecodedLogicalOp sys S_real L_bare ψ_dec
    (∀ σ₁ ∈ S_real \ F_fail, ∀ σ₂ ∈ S_real \ F_fail,
      bareSyndromeProjector sys σ₁ * opCommutator A O * bareSyndromeProjector sys σ₂ = 0) ∧
    SatisfiesTwoSidedOperatorImmunity sys F_fail O A := by
  intro O
  let c : SyndromeConfig D L → ℂ := fun σ => if ψ_dec σ then (-1 : ℂ) else (1 : ℂ)
  let S_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
    ∑ σ ∈ S_real, c σ • bareSyndromeProjector sys σ
  have hO_def : O = L_bare * S_op := rfl
  have hL_comm_P : ∀ σ : SyndromeConfig D L, Commute L_bare (bareSyndromeProjector sys σ) :=
    commute_bareSyndromeProjector_of_commute_Q sys hL_comm
  have hL_comm_S : Commute L_bare S_op := by
    dsimp [S_op]; apply Commute.sum_right
    intro σ _; exact commute_smul_right_clm (hL_comm_P σ) (c σ)
  have h_O_mul_P : ∀ σ ∈ S_real,
      O * bareSyndromeProjector sys σ = c σ • (bareSyndromeProjector sys σ * L_bare) := by
    intro σ hσ
    calc O * bareSyndromeProjector sys σ
      _ = L_bare * (S_op * bareSyndromeProjector sys σ) := by rw [hO_def, mul_assoc]
      _ = L_bare * (c σ • bareSyndromeProjector sys σ) := by
        rw [sum_smul_bareSyndromeProjector_mul sys S_real h_orth c hσ]
      _ = c σ • (L_bare * bareSyndromeProjector sys σ) := clm_mul_smul _ _ _
      _ = c σ • (bareSyndromeProjector sys σ * L_bare) := by rw [(hL_comm_P σ).eq]
  have h_P_mul_O : ∀ σ ∈ S_real,
      bareSyndromeProjector sys σ * O = c σ • (bareSyndromeProjector sys σ * L_bare) := by
    intro σ hσ
    calc bareSyndromeProjector sys σ * O
      _ = bareSyndromeProjector sys σ * (S_op * L_bare) := by rw [hO_def, hL_comm_S.eq]
      _ = (bareSyndromeProjector sys σ * S_op) * L_bare := (mul_assoc _ _ _).symm
      _ = (c σ • bareSyndromeProjector sys σ) * L_bare := by
        rw [bareSyndromeProjector_mul_sum_smul sys S_real h_orth c hσ]
      _ = c σ • (bareSyndromeProjector sys σ * L_bare) := clm_smul_mul _ _ _
  have h_sector_zero : ∀ σ₁ ∈ S_real \ F_fail, ∀ σ₂ ∈ S_real \ F_fail,
      bareSyndromeProjector sys σ₁ * opCommutator A O * bareSyndromeProjector sys σ₂ = 0 := by
    intro σ₁ hσ₁ σ₂ hσ₂
    have hσ₁_real : σ₁ ∈ S_real := (Finset.mem_sdiff.mp hσ₁).1
    have hσ₂_real : σ₂ ∈ S_real := (Finset.mem_sdiff.mp hσ₂).1
    let P₁ := bareSyndromeProjector sys σ₁
    let P₂ := bareSyndromeProjector sys σ₂
    let s_L : ℂ := if b_L then (-1 : ℂ) else (1 : ℂ)
    have h_O_mul_P₂ : O * P₂ = c σ₂ • (P₂ * L_bare) := h_O_mul_P σ₂ hσ₂_real
    have h_P₁_mul_O : P₁ * O = c σ₁ • (P₁ * L_bare) := h_P_mul_O σ₁ hσ₁_real
    have hL_comm_P₂ : L_bare * P₂ = P₂ * L_bare := (hL_comm_P σ₂).eq
    have h_term1 : P₁ * (A * O) * P₂ = c σ₂ • (P₁ * A * P₂ * L_bare) := by
      calc P₁ * (A * O) * P₂
        _ = P₁ * A * (O * P₂) := by simp only [mul_assoc]
        _ = P₁ * A * (c σ₂ • (P₂ * L_bare)) := by rw [h_O_mul_P₂]
        _ = c σ₂ • (P₁ * A * P₂ * L_bare) := by rw [clm_mul_smul]; simp only [mul_assoc]
    have h_term2 : P₁ * (O * A) * P₂ = (c σ₁ * s_L) • (P₁ * A * P₂ * L_bare) := by
      calc P₁ * (O * A) * P₂
        _ = (P₁ * O) * A * P₂ := by simp only [mul_assoc]
        _ = (c σ₁ • (P₁ * L_bare)) * A * P₂ := by rw [h_P₁_mul_O]
        _ = c σ₁ • (P₁ * (L_bare * A) * P₂) := by
          rw [clm_smul_mul, clm_smul_mul]; simp only [mul_assoc]
        _ = c σ₁ • (P₁ * ((s_L • A) * L_bare) * P₂) := by rw [hA_comm]
        _ = (c σ₁ * s_L) • (P₁ * A * (L_bare * P₂)) := by
          rw [clm_smul_mul, clm_mul_smul, clm_smul_mul, smul_smul]; simp only [mul_assoc]
        _ = (c σ₁ * s_L) • (P₁ * A * P₂ * L_bare) := by rw [hL_comm_P₂]; simp only [mul_assoc]
    have h_diff : P₁ * opCommutator A O * P₂ =
        (c σ₂ - c σ₁ * s_L) • (P₁ * A * P₂ * L_bare) := by
      dsimp [opCommutator]; rw [mul_sub, sub_mul, h_term1, h_term2, ← clm_sub_smul]
    change P₁ * opCommutator A O * P₂ = 0
    rw [h_diff]
    rcases hA_discrep σ₁ hσ₁ σ₂ hσ₂ with h_zero | h_xor
    · have h_zero' : P₁ * A * P₂ = 0 := h_zero
      rw [h_zero', zero_mul, smul_zero]
    · have h_c_eq : c σ₂ = c σ₁ * s_L := ite_neg_one_one_eq_mul_of_xor_eq h_xor
      rw [h_c_eq, sub_self, clm_zero_smul]
  refine ⟨h_sector_zero, ?_⟩
  have h_one_sub_P_fail_eq :
      1 - bareFailureProjector sys F_fail =
        ∑ σ ∈ S_real \ F_fail, bareSyndromeProjector sys σ :=
    (isStarProjection_bareFailureProjector_and_compl sys S_real F_fail hF_sub h_sum_one h_orth).2.2
  have h_sandwich_zero :
      (1 - bareFailureProjector sys F_fail) * opCommutator A O *
        (1 - bareFailureProjector sys F_fail) = 0 := by
    rw [h_one_sub_P_fail_eq, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_eq_zero (fun σ₁ hσ₁ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero (fun σ₂ hσ₂ => h_sector_zero σ₁ hσ₁ σ₂ hσ₂)
  exact ⟨h_sandwich_zero,
    eq_mul_add_one_sub_mul_mul_of_one_sub_sandwich_eq_zero
      (bareFailureProjector sys F_fail) (opCommutator A O) h_sandwich_zero⟩

/-- **Derivation of `SatisfiesTwoSidedOperatorImmunity` from `PreservesDecoderDiscrepancy`
    (`satisfiesTwoSidedOperatorImmunity_of_preservesDecoderDiscrepancy`; Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`); Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`))**. -/
theorem satisfiesTwoSidedOperatorImmunity_of_preservesDecoderDiscrepancy {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (S_real F_fail : Finset (SyndromeConfig D L))
    (L_bare : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ_dec : SyndromeConfig D L → Bool)
    (hF_sub : F_fail ⊆ S_real)
    (h_sum_one : (∑ σ ∈ S_real, bareSyndromeProjector sys σ) = 1)
    (h_orth : ∀ σ₁ ∈ S_real, ∀ σ₂ ∈ S_real, σ₁ ≠ σ₂ →
      bareSyndromeProjector sys σ₁ * bareSyndromeProjector sys σ₂ = 0)
    (hL_comm : ∀ K ∈ boxCubes D L 2, Commute (sys.Q K) L_bare)
    {A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_pres : PreservesDecoderDiscrepancy sys S_real F_fail L_bare ψ_dec A) :
    SatisfiesTwoSidedOperatorImmunity sys F_fail
      (bareDecodedLogicalOp sys S_real L_bare ψ_dec) A := by
  rcases h_pres with ⟨b_L, hA_comm, hA_discrep⟩
  exact (safe_sector_commutator_zero_of_commute_checks sys S_real F_fail L_bare ψ_dec hF_sub h_sum_one h_orth hL_comm
    A b_L hA_comm hA_discrep).2

end
