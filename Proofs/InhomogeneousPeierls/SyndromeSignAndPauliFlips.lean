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

import Proofs.InhomogeneousPeierls.SyndromeResolutionAndBareLogicals
import Proofs.HierarchicalClusterDecoder.ClusterDecoderSynthesis

/-!
# Syndrome-Sign Decoded Observables, Check-Flip Conjugation, and Safe-Subspace Immunity

Constructs the syndrome-sign correction operator `syndromeSignOp` and proves self-adjointness, involution, and safe-subspace commutation for dressed logical observables (`decodedObservable_props`, `syndromeSubsetProj_commutator_eq_zero_of_checkFlip`). Establishes Weyl-Pauli check-flip conjugation on the cubic-grid CSS realization (`weylPauliZX_mul_staticCSSCheckProj`, `hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq`) and characterizes realizable quantum syndromes (`exists_chains_of_syndromeProjector_ne_zero`).

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`), Definition 2.5 (`def:syndrome-safe`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

/-! ## 1. `signScalar`, `syndromeSignOp`, Decoded Observables & Two-Sided Safe-Subspace Commutator Reduction -/

def signScalar (a : ZMod 2) : ℂ :=
  if a = 0 then 1 else -1

@[simp] lemma signScalar_zero : signScalar 0 = 1 := rfl

lemma signScalar_add (a b : ZMod 2) :
    signScalar (a + b) = signScalar a * signScalar b := by
  rcases _root_.zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases _root_.zmod2_eq_zero_or_one b with rfl | rfl <;>
    dsimp [signScalar] <;> ring

lemma signScalar_mul_self (a : ZMod 2) : signScalar a * signScalar a = 1 := by
  rw [← signScalar_add, zmod2_add_self, signScalar_zero]

lemma conj_signScalar (a : ZMod 2) : starRingEnd ℂ (signScalar a) = signScalar a := by
  rcases _root_.zmod2_eq_zero_or_one a with rfl | rfl <;> simp [signScalar]

lemma pauliPhase_eq_signScalar {Q : Type*} [Fintype Q] (a b : Q → ZMod 2) :
    pauliPhase a b = signScalar (∑ q : Q, a q * b q) := rfl

def syndromeSignOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (sgn : (ι → Bool) → ZMod 2) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ σ : ι → Bool, signScalar (sgn σ) • sys.syndromeProjector σ

lemma syndromeSignOp_mul_syndromeProjector {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (sgn : (ι → Bool) → ZMod 2)
    (σ : ι → Bool) :
    syndromeSignOp sys sgn * sys.syndromeProjector σ =
      signScalar (sgn σ) • sys.syndromeProjector σ := by
  have h_res := syndrome_resolution_indexed sys
  dsimp [syndromeSignOp]
  rw [Finset.sum_mul, Finset.sum_eq_single σ]
  · rw [clm_smul_mul, (h_res.2.1 σ).isIdempotentElem.eq]
  · intro τ _ hne
    rw [clm_smul_mul, h_res.2.2.1 τ σ hne, smul_zero]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ σ))

lemma syndromeProjector_mul_syndromeSignOp {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (sgn : (ι → Bool) → ZMod 2)
    (σ : ι → Bool) :
    sys.syndromeProjector σ * syndromeSignOp sys sgn =
      signScalar (sgn σ) • sys.syndromeProjector σ := by
  have h_res := syndrome_resolution_indexed sys
  dsimp [syndromeSignOp]
  rw [Finset.mul_sum, Finset.sum_eq_single σ]
  · rw [clm_mul_smul, (h_res.2.1 σ).isIdempotentElem.eq]
  · intro τ _ hne
    rw [clm_mul_smul, h_res.2.2.1 σ τ (Ne.symm hne), smul_zero]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ σ))

private lemma clm_smul_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : ℂ) :
    c • (0 : E →L[ℂ] E) = 0 := by
  ext φ; simp

private lemma clm_adjoint_signScalar_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : P† = P) (a : ZMod 2) :
    (signScalar a • P)† = signScalar a • P := by
  rcases _root_.zmod2_eq_zero_or_one a with rfl | rfl
  · rw [signScalar_zero, one_smul, hP]
  · change ((-1 : ℂ) • P)† = (-1 : ℂ) • P
    rw [neg_one_smul, map_neg, hP]

private lemma clm_isSelfAdjoint_mul_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A B : E →L[ℂ] E}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (h_comm : Commute A B) :
    IsSelfAdjoint (A * B) := by
  rw [isSelfAdjoint_iff, star_mul, hB.star_eq, hA.star_eq, h_comm.symm.eq]

lemma syndromeSignOp_props {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (sgn : (ι → Bool) → ZMod 2) :
    IsSelfAdjoint (syndromeSignOp sys sgn) ∧
    syndromeSignOp sys sgn * syndromeSignOp sys sgn = 1 ∧
    (∀ i : ι, Commute (sys.checkProj i) (syndromeSignOp sys sgn)) ∧
    Commute sys.H0 (syndromeSignOp sys sgn) ∧
    Commute sys.P0 (syndromeSignOp sys sgn) ∧
    (sgn (fun _ => false) = 0 → syndromeSignOp sys sgn * sys.P0 = sys.P0) := by
  have h_res := syndrome_resolution_indexed sys
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    dsimp [syndromeSignOp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact clm_adjoint_signScalar_smul
      (ContinuousLinearMap.isSelfAdjoint_iff'.mp (h_res.2.1 σ).isSelfAdjoint) (sgn σ)
  · calc syndromeSignOp sys sgn * syndromeSignOp sys sgn
      _ = ∑ σ : ι → Bool,
            syndromeSignOp sys sgn * (signScalar (sgn σ) • sys.syndromeProjector σ) := by
        dsimp [syndromeSignOp]; rw [Finset.mul_sum]
      _ = ∑ σ : ι → Bool, sys.syndromeProjector σ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [clm_mul_smul, syndromeSignOp_mul_syndromeProjector, smul_smul,
          signScalar_mul_self, one_smul]
      _ = 1 := h_res.2.2.2.1
  · intro i
    dsimp [syndromeSignOp]
    apply Commute.sum_right
    intro σ _
    rw [commute_iff_eq, clm_mul_smul, clm_smul_mul, (h_res.2.2.2.2.2.2.1 σ i).eq]
  · dsimp [syndromeSignOp]
    apply Commute.sum_right
    intro σ _
    rw [commute_iff_eq, clm_mul_smul, clm_smul_mul, (h_res.2.2.2.2.2.2.2 σ).eq]
  · rw [← h_res.1, commute_iff_eq, syndromeProjector_mul_syndromeSignOp,
      syndromeSignOp_mul_syndromeProjector]
  · intro h0
    rw [← h_res.1, syndromeSignOp_mul_syndromeProjector, h0, signScalar_zero, one_smul]

lemma commute_syndromeProjector_of_commute_checkProj {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hU : ∀ i : ι, Commute U (sys.checkProj i)) (σ : ι → Bool) :
    Commute U (sys.syndromeProjector σ) := by
  dsimp [IndexedCommutingProjectorHamiltonian.syndromeProjector]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  split_ifs
  · exact hU i
  · exact commute_one_sub_right (hU i)

lemma decodedObservable_props {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {L_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hL_sa : IsSelfAdjoint L_op) (hL_inv : L_op * L_op = 1)
    (hL_comm : ∀ i : ι, Commute L_op (sys.checkProj i))
    (sgn : (ι → Bool) → ZMod 2) (h_sgn0 : sgn (fun _ => false) = 0)
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    let O_dec := L_op * syndromeSignOp sys sgn
    IsSelfAdjoint O_dec ∧ O_dec * O_dec = 1 ∧ ‖O_dec‖ ≤ 1 ∧
    Commute sys.H0 O_dec ∧ O_dec * sys.P0 = L_op * sys.P0 ∧
    Pi_safe * (sys.P0 - O_dec * sys.P0 * O_dec†) * Pi_safe = 0 := by
  intro O_dec
  have hD := syndromeSignOp_props sys sgn
  have hLD_comm : Commute L_op (syndromeSignOp sys sgn) := by
    dsimp [syndromeSignOp]
    apply Commute.sum_right
    intro σ _
    rw [commute_iff_eq, clm_mul_smul, clm_smul_mul,
      (commute_syndromeProjector_of_commute_checkProj sys hL_comm σ).eq]
  have hO_sa : IsSelfAdjoint O_dec := clm_isSelfAdjoint_mul_of_commute hL_sa hD.1 hLD_comm
  have hO_inv : O_dec * O_dec = 1 := by
    calc (L_op * syndromeSignOp sys sgn) * (L_op * syndromeSignOp sys sgn)
      _ = L_op * (syndromeSignOp sys sgn * L_op) * syndromeSignOp sys sgn := by
        simp only [mul_assoc]
      _ = (L_op * L_op) * (syndromeSignOp sys sgn * syndromeSignOp sys sgn) := by
        rw [hLD_comm.symm.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hL_inv, hD.2.1, mul_one]
  have hL_H0 : Commute sys.H0 L_op := commute_with_H0_of_commute_checkProj sys hL_comm
  have hL_P0 : Commute sys.P0 L_op := (commute_with_P0_of_commute_checkProj sys hL_comm).symm
  have hO_P0_comm : Commute sys.P0 O_dec := hL_P0.mul_right hD.2.2.2.2.1
  have h_pinch : sys.P0 - O_dec * sys.P0 * O_dec† = 0 := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hO_sa, ← hO_P0_comm.eq,
      mul_assoc, hO_inv, mul_one, sub_self]
  refine ⟨hO_sa, hO_inv, norm_le_one_of_isSelfAdjoint_and_mul_self_eq_one hO_sa hO_inv,
    hL_H0.mul_right hD.2.2.2.1, ?_, by rw [h_pinch, mul_zero, zero_mul]⟩
  change (L_op * syndromeSignOp sys sgn) * sys.P0 = L_op * sys.P0
  rw [mul_assoc, hD.2.2.2.2.2 h_sgn0]

lemma syndromeSubsetProj_commutator_eq_zero_of_checkFlip {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {L_op : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hL_comm : ∀ i : ι, Commute L_op (sys.checkProj i))
    (sgn : (ι → Bool) → ZMod 2) (S_safe : Finset (ι → Bool))
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {flip : ι → Bool} {phase_bit : ZMod 2}
    (hU_flip : ∀ i : ι, U * sys.checkProj i = (if flip i then 1 - sys.checkProj i else sys.checkProj i) * U)
    (hUL_phase : U * L_op = signScalar phase_bit • (L_op * U))
    (h_sgn_shift : ∀ σ ∈ S_safe, sys.syndromeProjector σ ≠ 0 →
      (fun i => xor (σ i) (flip i)) ∈ S_safe →
      sgn (fun i => xor (σ i) (flip i)) = sgn σ + phase_bit) :
    let Pi_safe := syndromeSubsetProj sys S_safe
    let O_dec := L_op * syndromeSignOp sys sgn
    Pi_safe * (U * O_dec - O_dec * U) * Pi_safe = 0 := by
  intro Pi_safe O_dec
  have h_res := syndrome_resolution_indexed sys
  dsimp [Pi_safe, syndromeSubsetProj]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_eq_zero fun σ₁ hσ₁ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun σ₂ hσ₂ => ?_
  let σ₂' : ι → Bool := fun i => xor (σ₂ i) (flip i)
  have h_inter : U * sys.syndromeProjector σ₂ = sys.syndromeProjector σ₂' * U :=
    intertwine_syndromeProjector_of_checkFlip sys hU_flip σ₂
  have hL_syn₂ : L_op * sys.syndromeProjector σ₂ = sys.syndromeProjector σ₂ * L_op :=
    (commute_syndromeProjector_of_commute_checkProj sys hL_comm σ₂).eq
  have hL_syn₂' : L_op * sys.syndromeProjector σ₂' = sys.syndromeProjector σ₂' * L_op :=
    (commute_syndromeProjector_of_commute_checkProj sys hL_comm σ₂').eq
  have h_T1 : sys.syndromeProjector σ₁ * (U * O_dec) * sys.syndromeProjector σ₂ =
      signScalar (sgn σ₂ + phase_bit) •
        (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂' * L_op * U) := by
    calc sys.syndromeProjector σ₁ * (U * (L_op * syndromeSignOp sys sgn)) * sys.syndromeProjector σ₂
      _ = sys.syndromeProjector σ₁ * U * L_op *
            (syndromeSignOp sys sgn * sys.syndromeProjector σ₂) := by simp only [mul_assoc]
      _ = signScalar (sgn σ₂) •
            ((sys.syndromeProjector σ₁ * (U * L_op)) * sys.syndromeProjector σ₂) := by
        rw [syndromeSignOp_mul_syndromeProjector, clm_mul_smul]; simp only [mul_assoc]
      _ = (signScalar (sgn σ₂) * signScalar phase_bit) •
            (sys.syndromeProjector σ₁ * L_op * (U * sys.syndromeProjector σ₂)) := by
        rw [hUL_phase, clm_mul_smul, clm_smul_mul, smul_smul]; simp only [mul_assoc]
      _ = signScalar (sgn σ₂ + phase_bit) •
            (sys.syndromeProjector σ₁ * (L_op * sys.syndromeProjector σ₂') * U) := by
        rw [← signScalar_add, h_inter]; simp only [mul_assoc]
      _ = signScalar (sgn σ₂ + phase_bit) •
            (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂' * L_op * U) := by
        rw [hL_syn₂']; simp only [mul_assoc]
  have h_T2 : sys.syndromeProjector σ₁ * (O_dec * U) * sys.syndromeProjector σ₂ =
      signScalar (sgn σ₁) •
        (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂' * L_op * U) := by
    have hL_syn₁ : sys.syndromeProjector σ₁ * L_op = L_op * sys.syndromeProjector σ₁ :=
      (commute_syndromeProjector_of_commute_checkProj sys hL_comm σ₁).symm.eq
    calc sys.syndromeProjector σ₁ * ((L_op * syndromeSignOp sys sgn) * U) * sys.syndromeProjector σ₂
      _ = ((sys.syndromeProjector σ₁ * L_op) * syndromeSignOp sys sgn) *
            (U * sys.syndromeProjector σ₂) := by simp only [mul_assoc]
      _ = (L_op * (sys.syndromeProjector σ₁ * syndromeSignOp sys sgn)) *
            (sys.syndromeProjector σ₂' * U) := by rw [hL_syn₁, mul_assoc L_op, h_inter]
      _ = signScalar (sgn σ₁) •
            ((L_op * sys.syndromeProjector σ₁) * sys.syndromeProjector σ₂' * U) := by
        rw [syndromeProjector_mul_syndromeSignOp, clm_mul_smul, clm_smul_mul]
        simp only [mul_assoc]
      _ = signScalar (sgn σ₁) •
            (sys.syndromeProjector σ₁ * (L_op * sys.syndromeProjector σ₂') * U) := by
        rw [← hL_syn₁]; simp only [mul_assoc]
      _ = signScalar (sgn σ₁) •
            (sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂' * L_op * U) := by
        rw [hL_syn₂']; simp only [mul_assoc]
  rw [mul_sub, sub_mul, h_T1, h_T2]
  by_cases h_eq : σ₁ = σ₂'
  · by_cases h_nz : sys.syndromeProjector σ₂ = 0
    · have h0 : sys.syndromeProjector σ₂' * L_op * U =
          L_op * (U * sys.syndromeProjector σ₂) := by
        rw [h_inter, ← mul_assoc, hL_syn₂']
      have h_kill : sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂' * L_op * U = 0 := by
        calc sys.syndromeProjector σ₁ * sys.syndromeProjector σ₂' * L_op * U
          _ = sys.syndromeProjector σ₁ * (sys.syndromeProjector σ₂' * L_op * U) := by
            simp only [mul_assoc]
          _ = sys.syndromeProjector σ₁ * (L_op * (U * sys.syndromeProjector σ₂)) := by rw [h0]
          _ = 0 := by rw [h_nz, mul_zero, mul_zero, mul_zero]
      rw [h_kill, clm_smul_zero, clm_smul_zero, sub_self]
    · have hσ₂'_mem : (fun i => xor (σ₂ i) (flip i)) ∈ S_safe := by
        change σ₂' ∈ S_safe
        rw [← h_eq]
        exact hσ₁
      have h_sgn : sgn σ₂' = sgn σ₂ + phase_bit := h_sgn_shift σ₂ hσ₂ h_nz hσ₂'_mem
      rw [h_eq, h_sgn, sub_self]
  · rw [h_res.2.2.1 σ₁ σ₂' h_eq, zero_mul, zero_mul, clm_smul_zero, clm_smul_zero, sub_self]

/-! ## 2. Check-Flip Conjugation & Realizability of Non-Zero Syndromes on `staticCSSSystem` -/

def staticCSSPauliFlip {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a b : BoxSlot3D L q_code → ZMod 2) :
    StaticCSSCheckIdx L q_code m_max → Bool
  | Sum.inl (v, s) =>
    ((ω v).activeSlot s == false) && decide ((∑ p, singleSlotChain v s p * b p) ≠ 0)
  | Sum.inr (Sum.inl (v, idx)) =>
    decide (idx.val < (ω v).numXChecks.val) &&
      decide ((∑ p, a p * descriptorCheckXChain ω v idx p) ≠ 0)
  | Sum.inr (Sum.inr (v, idx)) =>
    decide (idx.val < (ω v).numZChecks.val) &&
      decide ((∑ p, descriptorCheckZChain ω v idx p * b p) ≠ 0)

lemma staticCSSPauliFlip_xor {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a b : BoxSlot3D L q_code → ZMod 2)
    (i : StaticCSSCheckIdx L q_code m_max) :
    xor (staticCSSPauliFlip ω a 0 i) (staticCSSPauliFlip ω 0 b i) =
      staticCSSPauliFlip ω a b i := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSPauliFlip] <;> simp

private lemma half_one_sub_intertwine_of_comm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {U P : E →L[ℂ] E} (h : U * P = P * U) :
    U * ((2 : ℂ)⁻¹ • (1 - P)) = ((2 : ℂ)⁻¹ • (1 - P)) * U := by
  rw [clm_mul_smul, clm_smul_mul, mul_sub, mul_one, sub_mul, one_mul, h]

private lemma half_one_sub_intertwine_of_anticomm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {U P : E →L[ℂ] E} (h : U * P = -(P * U)) :
    U * ((2 : ℂ)⁻¹ • (1 - P)) = (1 - (2 : ℂ)⁻¹ • (1 - P)) * U := by
  ext φ
  have hφ := congr_fun (congr_arg DFunLike.coe h) φ
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, map_sub, map_smul] at hφ ⊢
  rw [hφ]
  module

lemma weylPauliZ_mul_staticCSSCheckProj {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a : BoxSlot3D L q_code → ZMod 2)
    (i : StaticCSSCheckIdx L q_code m_max) :
    weylPauliZ a * staticCSSCheckProj ω i =
      (if staticCSSPauliFlip ω a 0 i then 1 - staticCSSCheckProj ω i
       else staticCSSCheckProj ω i) * weylPauliZ a := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj]
  · simp only [staticCSSPauliFlip, Pi.zero_apply, mul_zero, Finset.sum_const_zero, ne_self_iff_false,
      decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact half_one_sub_intertwine_of_comm (weylPauliZ_comm a _).eq
    · simp
  · by_cases h_lt : idx.val < (ω v).numXChecks.val
    · rw [if_pos h_lt]
      by_cases h_nz : (∑ p, a p * descriptorCheckXChain ω v idx p) ≠ 0
      · simp only [staticCSSPauliFlip, h_lt, decide_eq_true h_nz, decide_true, Bool.true_and, ↓reduceIte]
        have h_one : (∑ p, a p * descriptorCheckXChain ω v idx p) = 1 :=
          zmod2_ne_zero_iff_eq_one _ h_nz
        have h_anti : weylPauliZ a * weylPauliX (descriptorCheckXChain ω v idx) =
            -(weylPauliX (descriptorCheckXChain ω v idx) * weylPauliZ a) := by
          rw [weylPauliX_anticomm_weylPauliZ_of_symplectic_one a _ h_one, neg_neg]
        exact half_one_sub_intertwine_of_anticomm h_anti
      · push_neg at h_nz
        simp only [staticCSSPauliFlip, h_lt, h_nz, ne_self_iff_false, decide_false,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact half_one_sub_intertwine_of_comm
          (weylPauliX_comm_weylPauliZ_of_symplectic_zero a _ h_nz).symm.eq
    · simp only [staticCSSPauliFlip, h_lt, decide_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, mul_zero, zero_mul]
  · simp only [staticCSSPauliFlip, Pi.zero_apply, mul_zero, Finset.sum_const_zero, ne_self_iff_false,
      decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact half_one_sub_intertwine_of_comm (weylPauliZ_comm a _).eq
    · simp

lemma weylPauliX_mul_staticCSSCheckProj {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (b : BoxSlot3D L q_code → ZMod 2)
    (i : StaticCSSCheckIdx L q_code m_max) :
    weylPauliX b * staticCSSCheckProj ω i =
      (if staticCSSPauliFlip ω 0 b i then 1 - staticCSSCheckProj ω i
       else staticCSSCheckProj ω i) * weylPauliX b := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj]
  · by_cases h_inact : (ω v).activeSlot s = false
    · rw [if_pos h_inact]
      by_cases h_nz : (∑ p, singleSlotChain v s p * b p) ≠ 0
      · simp only [staticCSSPauliFlip, h_inact, Bool.not_false, Bool.true_and, decide_eq_true h_nz, ↓reduceIte]
        have h_one : (∑ p, singleSlotChain v s p * b p) = 1 := zmod2_ne_zero_iff_eq_one _ h_nz
        exact half_one_sub_intertwine_of_anticomm
          (weylPauliX_anticomm_weylPauliZ_of_symplectic_one _ b h_one)
      · push_neg at h_nz
        simp only [staticCSSPauliFlip, h_inact, h_nz, ne_self_iff_false, decide_false,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact half_one_sub_intertwine_of_comm
          (weylPauliX_comm_weylPauliZ_of_symplectic_zero _ b h_nz).eq
    · have h_act : (ω v).activeSlot s = true := Bool.eq_true_of_not_eq_false h_inact
      simp [staticCSSPauliFlip, h_inact, h_act]
  · simp only [staticCSSPauliFlip, Pi.zero_apply, zero_mul, Finset.sum_const_zero, ne_self_iff_false,
      decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    split_ifs
    · exact half_one_sub_intertwine_of_comm (weylPauliX_comm b _).eq
    · simp
  · by_cases h_lt : idx.val < (ω v).numZChecks.val
    · rw [if_pos h_lt]
      by_cases h_nz : (∑ p, descriptorCheckZChain ω v idx p * b p) ≠ 0
      · simp only [staticCSSPauliFlip, h_lt, decide_eq_true h_nz, decide_true, Bool.true_and, ↓reduceIte]
        have h_one : (∑ p, descriptorCheckZChain ω v idx p * b p) = 1 :=
          zmod2_ne_zero_iff_eq_one _ h_nz
        exact half_one_sub_intertwine_of_anticomm
          (weylPauliX_anticomm_weylPauliZ_of_symplectic_one _ b h_one)
      · push_neg at h_nz
        simp only [staticCSSPauliFlip, h_lt, h_nz, ne_self_iff_false, decide_false,
          Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        exact half_one_sub_intertwine_of_comm
          (weylPauliX_comm_weylPauliZ_of_symplectic_zero _ b h_nz).eq
    · simp only [staticCSSPauliFlip, h_lt, decide_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, mul_zero, zero_mul]

private lemma clm_mul_one_sub_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Z P : E →L[ℂ] E} (hZ : Z * P = P * Z) :
    Z * (1 - P) = (1 - P) * Z := by
  rw [mul_sub, mul_one, sub_mul, one_mul, hZ]

private lemma clm_mul_one_sub_anticomm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {Z P : E →L[ℂ] E} (hZ : Z * P = (1 - P) * Z) :
    Z * (1 - P) = P * Z := by
  rw [mul_sub, mul_one, hZ, sub_mul, one_mul, sub_sub_cancel]

lemma weylPauliZX_mul_staticCSSCheckProj {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a b : BoxSlot3D L q_code → ZMod 2)
    (i : StaticCSSCheckIdx L q_code m_max) :
    (weylPauliZ a * weylPauliX b) * staticCSSCheckProj ω i =
      (if staticCSSPauliFlip ω a b i then 1 - staticCSSCheckProj ω i
       else staticCSSCheckProj ω i) * (weylPauliZ a * weylPauliX b) := by
  have hZ := weylPauliZ_mul_staticCSSCheckProj ω a i
  have hX := weylPauliX_mul_staticCSSCheckProj ω b i
  rw [← staticCSSPauliFlip_xor ω a b i]
  cases hfZ : staticCSSPauliFlip ω a 0 i <;>
    cases hfX : staticCSSPauliFlip ω 0 b i <;>
    simp only [hfZ, hfX, Bool.false_eq_true, ↓reduceIte, Bool.xor_false, Bool.false_xor,
      Bool.true_xor, Bool.not_true] at hZ hX ⊢
  · rw [mul_assoc, hX, ← mul_assoc, hZ, mul_assoc]
  · rw [mul_assoc, hX, ← mul_assoc, clm_mul_one_sub_comm hZ, mul_assoc]
  · rw [mul_assoc, hX, ← mul_assoc, hZ, mul_assoc]
  · rw [mul_assoc, hX, ← mul_assoc, clm_mul_one_sub_anticomm hZ, mul_assoc]

lemma hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (a b : BoxSlot3D L q_code → ZMod 2) :
    let sys := staticCSSSystem ω h_valid
    hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip ω a b)) =
      hilbertTrace sys.P0 := by
  intro sys
  have h_res := syndrome_resolution_indexed sys
  have h_eq : staticCSSPauliFlip ω a b =
      fun i => xor (xor false (staticCSSPauliFlip ω 0 b i)) (staticCSSPauliFlip ω a 0 i) := by
    ext i
    rw [Bool.false_xor, Bool.xor_comm, staticCSSPauliFlip_xor]
  rw [h_eq,
    hilbertTrace_syndromeProjector_xor_eq sys (weylPauliZ_sq_eq_one a)
      (weylPauliZ_mul_staticCSSCheckProj ω a),
    hilbertTrace_syndromeProjector_xor_eq sys (weylPauliX_sq_eq_one b)
      (weylPauliX_mul_staticCSSCheckProj ω b),
    h_res.1]

lemma syndrome_bit_eq_of_checkProj_eigenvec {D L : ℕ} {Site : BoxD D L → Type}
    [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (σ : ι → Bool) (i : ι) (b : Bool)
    {v : ManyBodyHilbertSpace Site} (hv_ne : sys.syndromeProjector σ v ≠ 0)
    (hv_eig : sys.checkProj i v = (if b then (1 : ℂ) else 0) • v) :
    σ i = b := by
  have h_res := syndrome_resolution_indexed sys
  have h_lhs : (sys.checkProj i * sys.syndromeProjector σ) v =
      (if σ i then (1 : ℂ) else 0) • sys.syndromeProjector σ v := by
    rw [h_res.2.2.2.2.2.1 σ i]
    split_ifs <;> simp
  have h_rhs : (sys.checkProj i * sys.syndromeProjector σ) v =
      (if b then (1 : ℂ) else 0) • sys.syndromeProjector σ v := by
    rw [(h_res.2.2.2.2.2.2.1 σ i).eq, ContinuousLinearMap.mul_apply, hv_eig, map_smul]
  have h_eq := h_lhs.symm.trans h_rhs
  cases h1 : σ i <;> cases h2 : b <;>
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, zero_smul, one_smul] at h_eq
  · rfl
  · exact False.elim (hv_ne h_eq.symm)
  · exact False.elim (hv_ne h_eq)
  · rfl

def allPlusVec {L q_code : ℕ} :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  WithLp.toLp 2 (fun _ => 1)

private lemma weylCheckProjZ_apply_basisVecGlobal {L q_code : ℕ}
    (c : BoxSlot3D L q_code → ZMod 2)
    (x : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    weylCheckProjZ c (basisVecGlobal _ x) =
      (if decide ((∑ p, c p * codeConfigBits x p) ≠ 0) then (1 : ℂ) else 0) •
        basisVecGlobal _ x := by
  ext y
  change (2 : ℂ)⁻¹ * ((basisVecGlobal _ x).ofLp y -
    pauliPhase c (codeConfigBits y) * (basisVecGlobal _ x).ofLp y) =
    (if decide ((∑ p, c p * codeConfigBits x p) ≠ 0) then (1 : ℂ) else 0) *
      (basisVecGlobal _ x).ofLp y
  by_cases hy : y = x
  · subst hy
    unfold pauliPhase
    by_cases h_nz : (∑ p, c p * codeConfigBits y p) ≠ 0
    · rw [if_neg h_nz, decide_eq_true h_nz, if_pos rfl]; ring
    · push_neg at h_nz
      simp only [if_pos h_nz, decide_eq_false (not_not.mpr h_nz), Bool.false_eq_true, ↓reduceIte]
      ring
  · have h0 : (basisVecGlobal (UniformSite3D L (CodeSlotConfig q_code)) x).ofLp y = 0 := by
      dsimp [basisVecGlobal]; rw [if_neg hy]
    rw [h0]; ring

private lemma weylCheckProjX_apply_weylPauliZ_allPlusVec {L q_code : ℕ}
    (c a : BoxSlot3D L q_code → ZMod 2) :
    weylCheckProjX c (weylPauliZ a allPlusVec) =
      (if decide ((∑ p, a p * c p) ≠ 0) then (1 : ℂ) else 0) •
        (weylPauliZ a allPlusVec) := by
  have hX : weylPauliX c (weylPauliZ a allPlusVec) =
      pauliPhase a c • (weylPauliZ a allPlusVec) := by
    change (weylPauliX c * weylPauliZ a) allPlusVec = _
    rw [weylPauliX_mul_weylPauliZ, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
    have h_all : weylPauliX c allPlusVec = allPlusVec := by ext y; rfl
    rw [h_all]
  change ((2 : ℂ)⁻¹ • (1 - weylPauliX c)) (weylPauliZ a allPlusVec) = _
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, hX]
  unfold pauliPhase
  by_cases h_nz : (∑ p, a p * c p) ≠ 0
  · rw [if_neg h_nz, decide_eq_true h_nz, if_pos rfl]
    ext y; simp; ring
  · push_neg at h_nz
    simp only [if_pos h_nz, decide_eq_false (not_not.mpr h_nz), Bool.false_eq_true, ↓reduceIte]
    ext y; simp

lemma exists_chains_of_syndromeProjector_ne_zero {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (σ : StaticCSSCheckIdx L q_code m_max → Bool)
    (hσ : (staticCSSSystem ω h_valid).syndromeProjector σ ≠ 0) :
    ∃ a b : BoxSlot3D L q_code → ZMod 2,
      σ = staticCSSPauliFlip ω a b ∧
      hilbertTrace ((staticCSSSystem ω h_valid).syndromeProjector σ) =
        hilbertTrace (staticCSSSystem ω h_valid).P0 := by
  let sys := staticCSSSystem ω h_valid
  have h_ex_x : ∃ x : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)),
      sys.syndromeProjector σ (basisVecGlobal _ x) ≠ 0 := by
    by_contra! h_all
    apply hσ
    ext φ y
    rw [clm_apply_ofLp_eq_sum (sys.syndromeProjector σ) φ y]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [← basisVecGlobal_eq_deltaLp x, h_all x]
    exact mul_zero _
  rcases h_ex_x with ⟨x, hx⟩
  have h_ex_a : ∃ a : BoxSlot3D L q_code → ZMod 2,
      sys.syndromeProjector σ (weylPauliZ a allPlusVec) ≠ 0 := by
    by_contra! h_all_a
    have h_decomp : (Fintype.card (BoxSlot3D L q_code → ZMod 2) : ℂ) •
        basisVecGlobal (UniformSite3D L (CodeSlotConfig q_code)) x =
        ∑ a : BoxSlot3D L q_code → ZMod 2,
          pauliPhase a (codeConfigBits x) • weylPauliZ a allPlusVec := by
      ext y
      rw [ofLp_sum]
      change (Fintype.card (BoxSlot3D L q_code → ZMod 2) : ℂ) *
          (if y = x then 1 else 0) =
        ∑ a : BoxSlot3D L q_code → ZMod 2,
          pauliPhase a (codeConfigBits x) * (pauliPhase a (codeConfigBits y) * 1)
      have h_term : ∀ a : BoxSlot3D L q_code → ZMod 2,
          pauliPhase a (codeConfigBits x) * (pauliPhase a (codeConfigBits y) * 1) =
            pauliPhase a (codeConfigBits x + codeConfigBits y) := fun a => by
        rw [mul_one, ← pauliPhase_add_right]
      simp_rw [h_term]
      have h_orth : (∑ a : BoxSlot3D L q_code → ZMod 2,
          pauliPhase a (codeConfigBits x + codeConfigBits y)) =
          if codeConfigBits x + codeConfigBits y = 0 then
            (Fintype.card (BoxSlot3D L q_code → ZMod 2) : ℂ) else 0 := by
        by_cases hz : codeConfigBits x + codeConfigBits y = 0
        · rw [if_pos hz, hz]; simp [pauliPhase]
        · rw [if_neg hz]
          have h_ex_p : ∃ p₀, (codeConfigBits x + codeConfigBits y) p₀ ≠ 0 := by
            by_contra! h0; exact hz (funext h0)
          rcases h_ex_p with ⟨p₀, hp₀⟩
          let e₀ : BoxSlot3D L q_code → ZMod 2 := fun p => if p = p₀ then 1 else 0
          have he₀ : pauliPhase e₀ (codeConfigBits x + codeConfigBits y) = -1 := by
            unfold pauliPhase
            have hs : (∑ p, e₀ p * (codeConfigBits x + codeConfigBits y) p) = 1 := by
              rw [Finset.sum_eq_single p₀]
              · dsimp [e₀]; rw [if_pos rfl, one_mul]; exact zmod2_ne_zero_iff_eq_one _ hp₀
              · intro p _ hne; dsimp [e₀]; rw [if_neg hne, zero_mul]
              · intro h_abs; exact False.elim (h_abs (Finset.mem_univ p₀))
            rw [hs, if_neg (by decide : (1 : ZMod 2) ≠ 0)]
          have h_sh : (∑ a, pauliPhase a (codeConfigBits x + codeConfigBits y)) =
              -(∑ a, pauliPhase a (codeConfigBits x + codeConfigBits y)) := by
            conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight e₀)]
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            change pauliPhase (a + e₀) _ = _
            rw [pauliPhase_add_left, he₀, mul_neg_one]
          linear_combination (1 / 2 : ℂ) * h_sh
      rw [h_orth]
      have h_iff : codeConfigBits x + codeConfigBits y = 0 ↔ y = x := by
        refine ⟨fun h0 => ?_, fun h_eq => by subst h_eq; ext p; exact zmod2_add_self _⟩
        funext v s
        have hvs := congr_fun h0 (v, s)
        dsimp [codeConfigBits, boolToZMod2] at hvs
        revert hvs; cases x v s <;> cases y v s <;> decide
      by_cases hyx : y = x
      · rw [if_pos (h_iff.mpr hyx), if_pos hyx, mul_one]
      · rw [if_neg (mt h_iff.mp hyx), if_neg hyx, mul_zero]
    have h_app := congr_arg (sys.syndromeProjector σ) h_decomp
    rw [map_smul, map_sum] at h_app
    simp_rw [map_smul, h_all_a, smul_zero, Finset.sum_const_zero] at h_app
    have h_card_ne : (Fintype.card (BoxSlot3D L q_code → ZMod 2) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact hx ((smul_eq_zero.mp h_app).resolve_left h_card_ne)
  rcases h_ex_a with ⟨a, ha⟩
  let b := codeConfigBits x
  have h_eq : σ = staticCSSPauliFlip ω a b := by
    ext i
    rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩
    · apply syndrome_bit_eq_of_checkProj_eigenvec sys σ (Sum.inl (v, s))
        (staticCSSPauliFlip ω a b (Sum.inl (v, s))) hx
      dsimp [sys, staticCSSSystem, staticCSSCheckProj]
      by_cases h_inact : (ω v).activeSlot s = false
      · simp only [staticCSSPauliFlip, h_inact, ↓reduceIte, Bool.not_false, Bool.true_and]
        exact weylCheckProjZ_apply_basisVecGlobal (singleSlotChain v s) x
      · have h_act : (ω v).activeSlot s = true := Bool.eq_true_of_not_eq_false h_inact
        simp [staticCSSPauliFlip, h_inact, h_act]
    · apply syndrome_bit_eq_of_checkProj_eigenvec sys σ (Sum.inr (Sum.inl (v, idx)))
        (staticCSSPauliFlip ω a b (Sum.inr (Sum.inl (v, idx)))) ha
      dsimp [sys, staticCSSSystem, staticCSSCheckProj]
      by_cases h_lt : idx.val < (ω v).numXChecks.val
      · simp only [staticCSSPauliFlip, h_lt, decide_true, Bool.true_and, ↓reduceIte]
        exact weylCheckProjX_apply_weylPauliZ_allPlusVec (descriptorCheckXChain ω v idx) a
      · simp [staticCSSPauliFlip, h_lt]
    · apply syndrome_bit_eq_of_checkProj_eigenvec sys σ (Sum.inr (Sum.inr (v, idx)))
        (staticCSSPauliFlip ω a b (Sum.inr (Sum.inr (v, idx)))) hx
      dsimp [sys, staticCSSSystem, staticCSSCheckProj]
      by_cases h_lt : idx.val < (ω v).numZChecks.val
      · simp only [staticCSSPauliFlip, h_lt, decide_true, Bool.true_and, ↓reduceIte]
        exact weylCheckProjZ_apply_basisVecGlobal (descriptorCheckZChain ω v idx) x
      · simp [staticCSSPauliFlip, h_lt]
  exact ⟨a, b, h_eq, h_eq ▸ hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq ω h_valid a b⟩

end
