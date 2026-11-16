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

import Proofs.WeylPhaseAndTrace

/-!
# Weyl-Pauli CSS Check Projector Idempotence, Self-Adjointness, and Commutativity

Proves that the X-type and Z-type Weyl-Pauli check projectors weylCheckProjX and weylCheckProjZ on open-box composite sites are orthogonal projections (weylCheckProjX_isIdempotent, weylCheckProjX_isSelfAdjoint, weylCheckProjZ_isIdempotent, weylCheckProjZ_isSelfAdjoint), commute within each Pauli sector, and commute across sectors whenever their F_2 exponent vectors have vanishing symplectic inner product (weylCheckProjX_comm_weylCheckProjZ_of_symplectic).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

/-! ## 1. Orthogonal Projector Properties of `weylCheckProjX` and `weylCheckProjZ` -/

private lemma isStarProjection_half_one_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {U : E →L[ℂ] E} (hU_sa : IsSelfAdjoint U) (hU_sq : U * U = 1) :
    IsStarProjection ((2 : ℂ)⁻¹ • (1 - U)) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, smul_mul_smul_comm]
    have h_sub : (1 - U) * (1 - U) = (2 : ℂ) • (1 - U) := by
      calc (1 - U) * (1 - U)
        _ = 1 - U - (U - U * U) := by rw [mul_sub, sub_mul, sub_mul, mul_one, mul_one, one_mul]
        _ = (1 - U) + (1 - U) := by rw [hU_sq]; abel
        _ = (2 : ℂ) • (1 - U) := (two_smul ℂ (1 - U)).symm
    rw [h_sub, smul_smul]
    have h_half : ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) * (2 : ℂ) = (2 : ℂ)⁻¹ := by norm_num
    rw [h_half]
  · rw [isSelfAdjoint_iff, star_smul, star_sub, star_one, hU_sa.star_eq]
    have h_star : star (2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by simp
    rw [h_star]

private lemma commute_right_half_one_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {O A : E →L[ℂ] E} (h : Commute O A) :
    Commute O ((2 : ℂ)⁻¹ • (1 - A)) := by
  rw [commute_iff_eq]
  ext x : 1
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul]
  exact congrArg (fun v => (2 : ℂ)⁻¹ • (O x - v))
    (congrFun (congrArg DFunLike.coe h.eq) x)

private lemma commute_half_one_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {A B : E →L[ℂ] E} (h : Commute A B) :
    Commute ((2 : ℂ)⁻¹ • (1 - A)) ((2 : ℂ)⁻¹ • (1 - B)) :=
  commute_right_half_one_sub (commute_right_half_one_sub h.symm).symm

/-- Every $X$-check projector $Q_X(b) = \frac{1}{2}(I - X(b))$ is idempotent and self-adjoint. -/
theorem weylCheckProjX_isIdempotent {L q_code : ℕ}
    (b : BoxSlot3D L q_code → ZMod 2) :
    IsIdempotentElem (weylCheckProjX b) :=
  (isStarProjection_half_one_sub (weylPauliX_isSelfAdjoint b) (weylPauliX_sq_eq_one b)).isIdempotentElem

theorem weylCheckProjX_isSelfAdjoint {L q_code : ℕ}
    (b : BoxSlot3D L q_code → ZMod 2) :
    IsSelfAdjoint (weylCheckProjX b) :=
  (isStarProjection_half_one_sub (weylPauliX_isSelfAdjoint b) (weylPauliX_sq_eq_one b)).isSelfAdjoint

/-- Every $Z$-check projector $Q_Z(a) = \frac{1}{2}(I - Z(a))$ is idempotent and self-adjoint. -/
theorem weylCheckProjZ_isIdempotent {L q_code : ℕ}
    (a : BoxSlot3D L q_code → ZMod 2) :
    IsIdempotentElem (weylCheckProjZ a) :=
  (isStarProjection_half_one_sub (weylPauliZ_isSelfAdjoint a) (weylPauliZ_sq_eq_one a)).isIdempotentElem

theorem weylCheckProjZ_isSelfAdjoint {L q_code : ℕ}
    (a : BoxSlot3D L q_code → ZMod 2) :
    IsSelfAdjoint (weylCheckProjZ a) :=
  (isStarProjection_half_one_sub (weylPauliZ_isSelfAdjoint a) (weylPauliZ_sq_eq_one a)).isSelfAdjoint

/-- Symplectic orthogonality $\langle a, b \rangle_{\mathbb{F}_2} = 0$ implies $[Q_X(b), Q_Z(a)] = 0$. -/
theorem weylCheckProjX_comm_weylCheckProjZ_of_symplectic
    {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2)
    (h_orth : (∑ p : BoxSlot3D L q_code, a p * b p) = 0) :
    Commute (weylCheckProjX b) (weylCheckProjZ a) :=
  commute_half_one_sub (weylPauliX_comm_weylPauliZ_of_symplectic_zero a b h_orth)

/-- All $X$-check projectors commute pairwise, and all $Z$-check projectors commute pairwise. -/
theorem weylCheckProjX_comm {L q_code : ℕ}
    (b₁ b₂ : BoxSlot3D L q_code → ZMod 2) :
    Commute (weylCheckProjX b₁) (weylCheckProjX b₂) :=
  commute_half_one_sub (weylPauliX_comm b₁ b₂)

theorem weylCheckProjZ_comm {L q_code : ℕ}
    (a₁ a₂ : BoxSlot3D L q_code → ZMod 2) :
    Commute (weylCheckProjZ a₁) (weylCheckProjZ a₂) :=
  commute_half_one_sub (weylPauliZ_comm a₁ a₂)

namespace CSSProjector
end CSSProjector
