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

import Proofs.CSSProjectorDecomposition

/-!
# Many-Body Lift and Locality of Static CSS Check Descriptors

Lifts site-indexed local CSS descriptors LocalCSSDescriptor to bounded Hilbert-space check projectors staticCSSCheckProj across active X-checks, active Z-checks, and inactive-slot Z-pins. Proves idempotence (staticCSSCheckProj_isIdempotent), self-adjointness (staticCSSCheckProj_isSelfAdjoint), pairwise commutativity under ValidDescriptorField (staticCSSCheckProj_comm_of_validDescriptorField), and finite-ball spatial locality on open-box balls (staticCSSCheckProj_supportedOn).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

/-! ## 1. Static Descriptor Field Lift (`ValidDescriptorField` $\implies$ Commuting Projectors) -/

/-- Every elementary check projector `staticCSSCheckProj ω i` is idempotent. -/
theorem staticCSSCheckProj_isIdempotent {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (i : StaticCSSCheckIdx L q_code m_max) :
    IsIdempotentElem (staticCSSCheckProj ω i) := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj]
  · split_ifs
    · exact weylCheckProjZ_isIdempotent _
    · exact IsIdempotentElem.zero
  · split_ifs
    · exact weylCheckProjX_isIdempotent _
    · exact IsIdempotentElem.zero
  · split_ifs
    · exact weylCheckProjZ_isIdempotent _
    · exact IsIdempotentElem.zero

/-- Every elementary check projector `staticCSSCheckProj ω i` is self-adjoint. -/
theorem staticCSSCheckProj_isSelfAdjoint {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (i : StaticCSSCheckIdx L q_code m_max) :
    IsSelfAdjoint (staticCSSCheckProj ω i) := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj]
  · split_ifs
    · exact weylCheckProjZ_isSelfAdjoint _
    · exact isSelfAdjoint_iff.mpr (ContinuousLinearMap.adjoint.map_zero)
  · split_ifs
    · exact weylCheckProjX_isSelfAdjoint _
    · exact isSelfAdjoint_iff.mpr (ContinuousLinearMap.adjoint.map_zero)
  · split_ifs
    · exact weylCheckProjZ_isSelfAdjoint _
    · exact isSelfAdjoint_iff.mpr (ContinuousLinearMap.adjoint.map_zero)

private lemma singleSlotChain_ortho_descriptorCheckXChain {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v vX : Box3D L) (s : Fin q_code) (idxX : Fin m_max)
    (h_inact : (ω v).activeSlot s = false) :
    (∑ p : BoxSlot3D L q_code,
      singleSlotChain v s p * descriptorCheckXChain ω vX idxX p) = 0 := by
  rw [Finset.sum_eq_single (v, s)]
  · dsimp [singleSlotChain, descriptorCheckXChain]
    rw [if_pos rfl, one_mul, if_neg]
    rintro ⟨h_lt, nb, _, h_sh, h_mask⟩
    have h_act := (h_valid.1 vX idxX nb s h_lt h_mask).2
    rw [h_sh, h_inact] at h_act
    exact Bool.noConfusion h_act
  · intro p _ hp
    dsimp [singleSlotChain]
    rw [if_neg hp, zero_mul]
  · intro h_not
    exact False.elim (h_not (Finset.mem_univ _))

/-- Under `ValidDescriptorField ω`, all check projectors `staticCSSCheckProj ω i` commute pairwise
    (including inactive-slot $Z$-pins, active $X$-checks, and active $Z$-checks). -/
theorem staticCSSCheckProj_comm_of_validDescriptorField {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (i j : StaticCSSCheckIdx L q_code m_max) :
    Commute (staticCSSCheckProj ω i) (staticCSSCheckProj ω j) := by
  rcases i with ⟨v₁, s₁⟩ | ⟨v₁, idx₁⟩ | ⟨v₁, idx₁⟩ <;>
    rcases j with ⟨v₂, s₂⟩ | ⟨v₂, idx₂⟩ | ⟨v₂, idx₂⟩ <;>
    dsimp [staticCSSCheckProj]
  · split_ifs
    · exact weylCheckProjZ_comm _ _
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs with h₁ h₂
    · exact (weylCheckProjX_comm_weylCheckProjZ_of_symplectic _ _
        (singleSlotChain_ortho_descriptorCheckXChain ω h_valid v₁ v₂ s₁ idx₂ h₁)).symm
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs
    · exact weylCheckProjZ_comm _ _
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs with h₁ h₂
    · exact weylCheckProjX_comm_weylCheckProjZ_of_symplectic _ _
        (singleSlotChain_ortho_descriptorCheckXChain ω h_valid v₂ v₁ s₂ idx₁ h₂)
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs
    · exact weylCheckProjX_comm _ _
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs
    · apply weylCheckProjX_comm_weylCheckProjZ_of_symplectic
      have h_orth := h_valid.2.2 v₁ v₂ idx₁ idx₂
      simpa only [mul_comm] using h_orth
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs
    · exact weylCheckProjZ_comm _ _
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs
    · apply Commute.symm
      apply weylCheckProjX_comm_weylCheckProjZ_of_symplectic
      have h_orth := h_valid.2.2 v₂ v₁ idx₂ idx₁
      simpa only [mul_comm] using h_orth
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _
  · split_ifs
    · exact weylCheckProjZ_comm _ _
    · exact Commute.zero_right _
    · exact Commute.zero_left _
    · exact Commute.zero_left _

private lemma spliceConfig_restrictConfig_self {D L : ℕ} {Site : BoxD D L → Type}
    (A : Finset (BoxD D L)) (σ : ManyBodyConfig Site) :
    spliceConfig A (restrictConfig A σ) σ = σ := by
  ext x
  dsimp [spliceConfig, restrictConfig]
  split_ifs <;> rfl

private lemma isSupportedOn_zero_clm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L)) :
    IsSupportedOn Site A 0 := by
  refine ⟨0, ?_⟩
  ext ψ σ
  rfl

private lemma isSupportedOn_weylCheckProjZ_of_supp {L q_code : ℕ}
    (A : Finset (Box3D L)) (a : BoxSlot3D L q_code → ZMod 2)
    (h_supp : ∀ (w : Box3D L) (s : Fin q_code), a (w, s) ≠ 0 → w ∈ A) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (weylCheckProjZ a) := by
  let zeroCfg : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)) := fun _ _ => false
  let O_loc : LocalHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) A →L[ℂ]
      LocalHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) A :=
    LinearMap.toContinuousLinearMap
      { toFun := fun ψ_A => WithLp.toLp 2 (fun α =>
          (2 : ℂ)⁻¹ * (1 - pauliPhase a (codeConfigBits (spliceConfig A α zeroCfg))) * ψ_A.ofLp α)
        map_add' := fun ψ₁ ψ₂ => by
          ext α
          change (2 : ℂ)⁻¹ * (1 - pauliPhase a _) * (ψ₁.ofLp α + ψ₂.ofLp α) =
            (2 : ℂ)⁻¹ * (1 - pauliPhase a _) * ψ₁.ofLp α +
            (2 : ℂ)⁻¹ * (1 - pauliPhase a _) * ψ₂.ofLp α
          ring
        map_smul' := fun c ψ_A => by
          ext α
          change (2 : ℂ)⁻¹ * (1 - pauliPhase a _) * (c * ψ_A.ofLp α) =
            c * ((2 : ℂ)⁻¹ * (1 - pauliPhase a _) * ψ_A.ofLp α)
          ring }
  refine ⟨O_loc, ?_⟩
  ext ψ σ
  change (2 : ℂ)⁻¹ * (ψ.ofLp σ - pauliPhase a (codeConfigBits σ) * ψ.ofLp σ) =
    (2 : ℂ)⁻¹ * (1 - pauliPhase a (codeConfigBits (spliceConfig A (restrictConfig A σ) zeroCfg))) *
      ψ.ofLp (spliceConfig A (restrictConfig A σ) σ)
  rw [spliceConfig_restrictConfig_self]
  have h_phase :
      pauliPhase a (codeConfigBits (spliceConfig A (restrictConfig A σ) zeroCfg)) =
        pauliPhase a (codeConfigBits σ) := by
    dsimp [pauliPhase]
    have h_sum :
        (∑ p : BoxSlot3D L q_code,
          a p * codeConfigBits (spliceConfig A (restrictConfig A σ) zeroCfg) p) =
        ∑ p : BoxSlot3D L q_code, a p * codeConfigBits σ p := by
      refine Finset.sum_congr rfl (fun ⟨w, s⟩ _ => ?_)
      by_cases ha : a (w, s) = 0
      · simp [ha]
      · have hw : w ∈ A := h_supp w s ha
        dsimp [codeConfigBits, spliceConfig, restrictConfig]
        rw [if_pos hw]
    rw [h_sum]
  rw [h_phase]
  ring

private lemma isSupportedOn_weylCheckProjX_of_supp {L q_code : ℕ}
    (A : Finset (Box3D L)) (b : BoxSlot3D L q_code → ZMod 2)
    (h_supp : ∀ (w : Box3D L) (s : Fin q_code), b (w, s) ≠ 0 → w ∈ A) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (weylCheckProjX b) := by
  let flipLoc : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A →
      LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A :=
    fun α x s => xor (α x s) (zmod2ToBool (b (x.1, s)))
  let O_loc : LocalHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) A →L[ℂ]
      LocalHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) A :=
    LinearMap.toContinuousLinearMap
      { toFun := fun ψ_A => WithLp.toLp 2 (fun α =>
          (2 : ℂ)⁻¹ * (ψ_A.ofLp α - ψ_A.ofLp (flipLoc α)))
        map_add' := fun ψ₁ ψ₂ => by
          ext α
          change (2 : ℂ)⁻¹ * ((ψ₁.ofLp α + ψ₂.ofLp α) - (ψ₁.ofLp (flipLoc α) + ψ₂.ofLp (flipLoc α))) =
            (2 : ℂ)⁻¹ * (ψ₁.ofLp α - ψ₁.ofLp (flipLoc α)) +
            (2 : ℂ)⁻¹ * (ψ₂.ofLp α - ψ₂.ofLp (flipLoc α))
          ring
        map_smul' := fun c ψ_A => by
          ext α
          change (2 : ℂ)⁻¹ * (c * ψ_A.ofLp α - c * ψ_A.ofLp (flipLoc α)) =
            c * ((2 : ℂ)⁻¹ * (ψ_A.ofLp α - ψ_A.ofLp (flipLoc α)))
          ring }
  refine ⟨O_loc, ?_⟩
  ext ψ σ
  change (2 : ℂ)⁻¹ * (ψ.ofLp σ - ψ.ofLp (flipCodeConfig b σ)) =
    (2 : ℂ)⁻¹ * (ψ.ofLp (spliceConfig A (restrictConfig A σ) σ) -
      ψ.ofLp (spliceConfig A (flipLoc (restrictConfig A σ)) σ))
  rw [spliceConfig_restrictConfig_self]
  have h_flip : spliceConfig A (flipLoc (restrictConfig A σ)) σ = flipCodeConfig b σ := by
    ext w s
    dsimp [spliceConfig, flipLoc, restrictConfig, flipCodeConfig]
    by_cases hw : w ∈ A
    · rw [if_pos hw]
    · rw [if_neg hw]
      have hb0 : b (w, s) = 0 := by
        by_contra h_ne
        exact hw (h_supp w s h_ne)
      rw [hb0]
      dsimp [zmod2ToBool]
      cases σ w s <;> rfl
  rw [h_flip]

private lemma shiftOpenBox_neighborhoodOffset_mem_boxBall {L r_0 : ℕ}
    (v : Box3D L) (nb : LocalNeighborhoodIdx r_0) :
    shiftOpenBox v (neighborhoodOffset r_0 nb) ∈ boxBall v r_0 := by
  rw [boxBall, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [boxDist, Finset.sup_le_iff]
  intro μ _
  unfold shiftOpenBox shiftOpenBoxD coordDist neighborhoodOffset
  have h_nb := (nb μ).isLt
  split_ifs with h_in
  · simp only [Fin.val_mk]; omega
  · simp

/-- Every check projector `staticCSSCheckProj ω i` is supported on `staticCSSCheckSupport ω i`. -/
theorem staticCSSCheckProj_supportedOn {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (i : StaticCSSCheckIdx L q_code m_max) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code))
      (staticCSSCheckSupport ω i) (staticCSSCheckProj ω i) := by
  rcases i with ⟨v, s₀⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj, staticCSSCheckSupport]
  · split_ifs
    · apply isSupportedOn_weylCheckProjZ_of_supp
      intro w s h_ne
      dsimp [singleSlotChain] at h_ne
      split_ifs at h_ne with h_eq
      · rw [Finset.mem_singleton]
        exact (Prod.ext_iff.mp h_eq).1
      · exact False.elim (h_ne rfl)
    · exact isSupportedOn_zero_clm _
  · split_ifs
    · apply isSupportedOn_weylCheckProjX_of_supp
      intro w s h_ne
      dsimp [descriptorCheckXChain] at h_ne
      split_ifs at h_ne with h_ex
      · rcases h_ex with ⟨_, nb, _, rfl, _⟩
        exact shiftOpenBox_neighborhoodOffset_mem_boxBall v nb
      · exact False.elim (h_ne rfl)
    · exact isSupportedOn_zero_clm _
  · split_ifs
    · apply isSupportedOn_weylCheckProjZ_of_supp
      intro w s h_ne
      dsimp [descriptorCheckZChain] at h_ne
      split_ifs at h_ne with h_ex
      · rcases h_ex with ⟨_, nb, _, rfl, _⟩
        exact shiftOpenBox_neighborhoodOffset_mem_boxBall v nb
      · exact False.elim (h_ne rfl)
    · exact isSupportedOn_zero_clm _

namespace CSSProjector
end CSSProjector
