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

import Defs.LocalCSSDescriptor

/-!
# Weyl–Pauli Symplectic Commutation Relations and Trace Orthogonality

Proves fundamental algebraic identities for multi-qubit pure-X and pure-Z Weyl–Pauli operators `weylPauliX` and `weylPauliZ`, including identity at zero (`weylPauliX_zero`, `weylPauliZ_zero`), self-adjointness, and involutive squares. Establishes symplectic commutation and anticommutation governed by the binary inner product (`weylPauliX_comm_weylPauliZ_of_symplectic_zero`, `weylPauliX_anticomm_weylPauliZ_of_symplectic_one`) and trace orthogonality of nontrivial Pauli products (`hilbertTrace_weylPauli_eq_zero_of_ne_zero`).

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`)
* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.6 (`prop:walsh-coset-dominance`)
* Balasubramanian–Davydova–Lin (2026), Sections 2.1 and 5.4
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

/-! ## 1. Self-Adjointness, Involutive Square, and Symplectic Commutation of `weylPauliX` / `weylPauliZ` -/

/-- The zero-bitstring Weyl–Pauli operators `weylPauliZ 0` and `weylPauliX 0` equal `1`. -/
theorem weylPauliZ_zero {L q_code : ℕ} :
    weylPauliZ (L := L) (q_code := q_code) 0 = 1 := by
  ext ψ σ
  change pauliPhase 0 (codeConfigBits σ) * ψ.ofLp σ = ψ.ofLp σ
  have h0 : pauliPhase (0 : BoxSlot3D L q_code → ZMod 2) (codeConfigBits σ) = 1 := by
    simp [pauliPhase]
  rw [h0, one_mul]

lemma flipCodeConfig_zero {L q_code : ℕ}
    (σ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    flipCodeConfig 0 σ = σ := by
  ext v s
  dsimp [flipCodeConfig, zmod2ToBool]
  cases σ v s <;> rfl

theorem weylPauliX_zero {L q_code : ℕ} :
    weylPauliX (L := L) (q_code := q_code) 0 = 1 := by
  ext ψ σ
  change ψ.ofLp (flipCodeConfig 0 σ) = ψ.ofLp σ
  rw [flipCodeConfig_zero]

/-- Pure-$X$ and pure-$Z$ Weyl–Pauli operators $X(b)$ and $Z(a)$ are self-adjoint. -/
theorem weylPauliX_isSelfAdjoint {L q_code : ℕ}
    (b : BoxSlot3D L q_code → ZMod 2) :
    IsSelfAdjoint (weylPauliX b) := by
  rw [isSelfAdjoint_iff]
  change (weylPauliX b)† = weylPauliX b
  ext φ₁ : 1
  apply ext_inner_right ℂ
  intro φ₂
  rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply]
  rw [← Equiv.sum_comp (flipCodeConfig_involutive b).toPerm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  dsimp [Function.Involutive.toPerm]
  change φ₂.ofLp (flipCodeConfig b (flipCodeConfig b σ)) * (starRingEnd ℂ) (φ₁.ofLp (flipCodeConfig b σ)) =
    φ₂.ofLp σ * (starRingEnd ℂ) (φ₁.ofLp (flipCodeConfig b σ))
  rw [flipCodeConfig_involutive b σ]

theorem weylPauliZ_isSelfAdjoint {L q_code : ℕ}
    (a : BoxSlot3D L q_code → ZMod 2) :
    IsSelfAdjoint (weylPauliZ a) := by
  rw [isSelfAdjoint_iff]
  change (weylPauliZ a)† = weylPauliZ a
  ext φ₁ : 1
  apply ext_inner_right ℂ
  intro φ₂
  rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  change (pauliPhase a (codeConfigBits σ) * φ₂.ofLp σ) * (starRingEnd ℂ) (φ₁.ofLp σ) =
    φ₂.ofLp σ * (starRingEnd ℂ) (pauliPhase a (codeConfigBits σ) * φ₁.ofLp σ)
  simp only [map_mul]
  have h_conj : (starRingEnd ℂ) (pauliPhase a (codeConfigBits σ)) = pauliPhase a (codeConfigBits σ) :=
    star_pauliPhase a (codeConfigBits σ)
  rw [h_conj]
  ring

/-- Pure-$X$ and pure-$Z$ Weyl–Pauli operators square to the identity: $X(b)^2 = I$ and $Z(a)^2 = I$. -/
theorem weylPauliX_sq_eq_one {L q_code : ℕ}
    (b : BoxSlot3D L q_code → ZMod 2) :
    weylPauliX b * weylPauliX b = 1 := by
  ext ψ σ
  change ψ.ofLp (flipCodeConfig b (flipCodeConfig b σ)) = ψ.ofLp σ
  rw [flipCodeConfig_involutive b σ]

theorem weylPauliZ_sq_eq_one {L q_code : ℕ}
    (a : BoxSlot3D L q_code → ZMod 2) :
    weylPauliZ a * weylPauliZ a = 1 := by
  ext ψ σ
  change pauliPhase a (codeConfigBits σ) * (pauliPhase a (codeConfigBits σ) * ψ.ofLp σ) = ψ.ofLp σ
  rw [← mul_assoc, pauliPhase_mul_self, one_mul]

/-- Symplectic commutation law: $X(b)$ and $Z(a)$ commute whenever $\langle a, b \rangle_{\mathbb{F}_2} = 0$,
    and anticommute whenever $\langle a, b \rangle_{\mathbb{F}_2} = 1$. -/
theorem weylPauliX_comm_weylPauliZ_of_symplectic_zero
    {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2)
    (h_orth : (∑ p : BoxSlot3D L q_code, a p * b p) = 0) :
    Commute (weylPauliX b) (weylPauliZ a) :=
  weylPauliX_commute_weylPauliZ_of_ortho a b h_orth

theorem weylPauliX_anticomm_weylPauliZ_of_symplectic_one
    {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2)
    (h_anti : (∑ p : BoxSlot3D L q_code, a p * b p) = 1) :
    weylPauliX b * weylPauliZ a = -(weylPauliZ a * weylPauliX b) := by
  rw [weylPauliX_mul_weylPauliZ]
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have h_phase : pauliPhase a b = -1 := by
    simp [pauliPhase, h_anti, h10]
  rw [h_phase]
  ext ψ σ
  change (-1 : ℂ) * ((weylPauliZ a * weylPauliX b) ψ).ofLp σ =
    -(((weylPauliZ a * weylPauliX b) ψ).ofLp σ)
  ring

/-- Pure-$X$ Weyl–Pauli operators commute with one another, and pure-$Z$ Weyl–Pauli operators commute with one another. -/
theorem weylPauliX_comm {L q_code : ℕ}
    (b₁ b₂ : BoxSlot3D L q_code → ZMod 2) :
    Commute (weylPauliX b₁) (weylPauliX b₂) := by
  rw [commute_iff_eq]
  ext ψ σ
  change ψ.ofLp (flipCodeConfig b₂ (flipCodeConfig b₁ σ)) =
    ψ.ofLp (flipCodeConfig b₁ (flipCodeConfig b₂ σ))
  refine congrArg ψ.ofLp ?_
  ext v s
  dsimp [flipCodeConfig]
  cases σ v s <;> cases zmod2ToBool (b₁ (v, s)) <;> cases zmod2ToBool (b₂ (v, s)) <;> rfl

theorem weylPauliZ_comm {L q_code : ℕ}
    (a₁ a₂ : BoxSlot3D L q_code → ZMod 2) :
    Commute (weylPauliZ a₁) (weylPauliZ a₂) := by
  rw [commute_iff_eq]
  ext ψ σ
  change pauliPhase a₁ (codeConfigBits σ) * (pauliPhase a₂ (codeConfigBits σ) * ψ.ofLp σ) =
    pauliPhase a₂ (codeConfigBits σ) * (pauliPhase a₁ (codeConfigBits σ) * ψ.ofLp σ)
  ring

private lemma inner_basisVecGlobal_apply {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (ψ : ManyBodyConfig Site) (φ : ManyBodyHilbertSpace Site) :
    inner ℂ (basisVecGlobal Site ψ) φ = φ.ofLp ψ := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single ψ]
  · dsimp [basisVecGlobal]
    simp
  · intro τ _ hτ
    dsimp [basisVecGlobal]
    simp [hτ]
  · intro h_not
    exact False.elim (h_not (Finset.mem_univ ψ))

/-- Trace orthogonality: $\mathrm{Tr}(Z(a) X(b)) = 0$ whenever $(a, b) \neq (0, 0)$. -/
theorem hilbertTrace_weylPauli_eq_zero_of_ne_zero
    {L q_code : ℕ}
    (a b : BoxSlot3D L q_code → ZMod 2) (h_ne : a ≠ 0 ∨ b ≠ 0) :
    hilbertTrace (weylPauliZ a * weylPauliX b) = 0 := by
  unfold hilbertTrace
  have h_diag : ∀ ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)),
      RCLike.re (inner ℂ (basisVecGlobal (UniformSite3D L (CodeSlotConfig q_code)) ψ)
        ((weylPauliZ a * weylPauliX b)
          (basisVecGlobal (UniformSite3D L (CodeSlotConfig q_code)) ψ))) =
      RCLike.re (pauliPhase a (codeConfigBits ψ) *
        (if flipCodeConfig b ψ = ψ then (1 : ℂ) else 0)) := by
    intro ψ
    rw [inner_basisVecGlobal_apply]
    rfl
  simp_rw [h_diag]
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := h_ne.resolve_right (not_not.mpr rfl)
    have h_ex : ∃ p₀ : BoxSlot3D L q_code, a p₀ ≠ 0 := by
      by_contra h_all
      push_neg at h_all
      exact ha (funext h_all)
    rcases h_ex with ⟨⟨v₀, s₀⟩, hp₀⟩
    have hp₀_one : a (v₀, s₀) = 1 := zmod2_ne_zero_iff_eq_one _ hp₀
    have h_term0 : ∀ ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)),
        RCLike.re (pauliPhase a (codeConfigBits ψ) *
          (if flipCodeConfig 0 ψ = ψ then (1 : ℂ) else 0)) =
        RCLike.re (pauliPhase a (codeConfigBits ψ)) := by
      intro ψ
      rw [flipCodeConfig_zero, if_pos rfl, mul_one]
    simp_rw [h_term0]
    let e₀ := singleSlotChain v₀ s₀
    have he₀_phase : pauliPhase a e₀ = -1 := by
      unfold pauliPhase
      have h_sum : (∑ p : BoxSlot3D L q_code, a p * e₀ p) = 1 := by
        dsimp [e₀, singleSlotChain]
        rw [Finset.sum_eq_single (v₀, s₀)]
        · rw [if_pos rfl, mul_one, hp₀_one]
        · intro p _ hp; rw [if_neg hp, mul_zero]
        · intro h_not; exact False.elim (h_not (Finset.mem_univ _))
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rw [h_sum, if_neg h10]
    let S := ∑ ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)),
      RCLike.re (pauliPhase a (codeConfigBits ψ))
    change S = 0
    have h_neg : S = -S := by
      calc S
        _ = ∑ ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)),
              RCLike.re (pauliPhase a (codeConfigBits (flipCodeConfig e₀ ψ))) := by
            exact (Equiv.sum_comp (flipCodeConfig_involutive e₀).toPerm
              (fun ψ => RCLike.re (pauliPhase a (codeConfigBits ψ)))).symm
        _ = ∑ ψ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)),
              (- RCLike.re (pauliPhase a (codeConfigBits ψ))) := by
            refine Finset.sum_congr rfl (fun ψ _ => ?_)
            rw [codeConfigBits_flipCodeConfig, pauliPhase_add_right, he₀_phase,
              mul_neg_one, map_neg]
        _ = -S := by rw [Finset.sum_neg_distrib]
    linarith
  · have h_ex : ∃ p₀ : BoxSlot3D L q_code, b p₀ ≠ 0 := by
      by_contra h_all
      push_neg at h_all
      exact hb (funext h_all)
    rcases h_ex with ⟨⟨v₀, s₀⟩, hp₀⟩
    refine Finset.sum_eq_zero (fun ψ _ => ?_)
    have h_ne_ψ : flipCodeConfig b ψ ≠ ψ := by
      intro h_eq
      have h_at := congr_fun (congr_fun h_eq v₀) s₀
      dsimp [flipCodeConfig, zmod2ToBool] at h_at
      have h_true : decide (b (v₀, s₀) ≠ 0) = true := decide_eq_true hp₀
      rw [h_true] at h_at
      revert h_at
      cases ψ v₀ s₀ <;> decide
    rw [if_neg h_ne_ψ, mul_zero, map_zero]
