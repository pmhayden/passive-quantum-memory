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

import Proofs.StaticDescriptorLift
import Proofs.Step2DegreeAndWeld.BDLSubstitutionRealization
import Proofs.Step2DegreeAndWeld.LogicalChainLiftsAndPreservation
import Defs.BHMStability
import Defs.SafeSubspaceAndKMS
import Proofs.BoxMetricAndCollarLemmas
import Proofs.CylinderAlgebraAndSupport
import Proofs.SupportAndCondExpLemmas
import Proofs.SpectralAndGibbsLemmas
import Proofs.CubeTelescoping.LocalToGlobalNormTransfer
import Proofs.CubeTelescoping.CoarseCubeFunctor
import Proofs.KMSSafeSubspaceODE.TwoSidedRelativeCommutant

/-!
# Frustration-Free Static CSS Commuting-Projector Hamiltonian Realization

Constructs the explicit X-stabilizer superposition state `staticCSSGroundStateUnnorm` and proves that any valid local CSS descriptor field defines a frustration-free `IndexedCommutingProjectorHamiltonian` (`staticCSSSystem`). Establishes ground-projector and local-collar absorption identities for single-slot Z-pins and X/Z stabilizer generators (`weylPauliZ_descriptorCheckZChain_mul_P0`, `weylPauliX_descriptorCheckXChain_mul_P0`).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.2 (`def:tqo`)
* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000

/-! ## 1. Multi-Qubit Weyl–Pauli Group Homomorphism & Commutation Helpers -/

theorem weylPauliZ_add {L q_code : ℕ} (a₁ a₂ : BoxSlot3D L q_code → ZMod 2) :
    weylPauliZ (a₁ + a₂) = weylPauliZ a₁ * weylPauliZ a₂ := by
  ext ψ σ
  change pauliPhase (a₁ + a₂) (codeConfigBits σ) * ψ.ofLp σ =
    pauliPhase a₁ (codeConfigBits σ) * (pauliPhase a₂ (codeConfigBits σ) * ψ.ofLp σ)
  rw [pauliPhase_add_left, mul_assoc]

lemma flipCodeConfig_add {L q_code : ℕ} (b₁ b₂ : BoxSlot3D L q_code → ZMod 2)
    (σ : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code))) :
    flipCodeConfig (b₁ + b₂) σ = flipCodeConfig b₁ (flipCodeConfig b₂ σ) := by
  ext v s
  dsimp [flipCodeConfig, zmod2ToBool]
  rcases zmod2_eq_zero_or_one (b₁ (v, s)) with h1 | h1 <;>
    rcases zmod2_eq_zero_or_one (b₂ (v, s)) with h2 | h2 <;>
    cases σ v s <;>
    simp [h1, h2]

theorem weylPauliX_add {L q_code : ℕ} (b₁ b₂ : BoxSlot3D L q_code → ZMod 2) :
    weylPauliX (b₁ + b₂) = weylPauliX b₁ * weylPauliX b₂ := by
  ext ψ σ
  change ψ.ofLp (flipCodeConfig (b₁ + b₂) σ) =
    ψ.ofLp (flipCodeConfig b₂ (flipCodeConfig b₁ σ))
  rw [add_comm b₁ b₂, flipCodeConfig_add]

lemma commute_right_half_one_sub_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {O A : E →L[ℂ] E} (h : Commute O A) :
    Commute O ((2 : ℂ)⁻¹ • (1 - A)) := by
  rw [commute_iff_eq]
  ext x : 1
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, map_sub, map_smul]
  exact congrArg (fun v => (2 : ℂ)⁻¹ • (O x - v))
    (congrFun (congrArg DFunLike.coe h.eq) x)

lemma sub_eq_zero_of_half_one_sub_mul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {U P : E →L[ℂ] E}
    (h : ((2 : ℂ)⁻¹ • (1 - U)) * P = 0) :
    U * P = P := by
  have h1 : (1 - U) * P = 0 := by
    ext x
    have hx := congrFun (congrArg DFunLike.coe h) x
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.zero_apply] at hx
    exact (smul_eq_zero.mp hx).resolve_left (inv_ne_zero (by norm_num))
  rw [sub_mul, one_mul, sub_eq_zero] at h1
  exact h1.symm

/-! ## 2. Explicit Ground State and Frustration-Free `staticCSSSystem` -/

/-- Canonical unnormalized CSS ground state $\sum_{x \in S_X(\omega)} |x\rangle$ supported on the
    $X$-stabilizer subgroup `descriptorStabilizerX ω`. -/
def staticCSSGroundStateUnnorm {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  WithLp.toLp 2 (fun σ => if codeConfigBits σ ∈ descriptorStabilizerX ω then (1 : ℂ) else 0)

lemma zero_mem_descriptorStabilizerX {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    (0 : F2Chain (BoxSlot3D L q_code)) ∈ descriptorStabilizerX ω := by
  refine ⟨0, ?_⟩
  ext p
  simp

lemma add_mem_descriptorStabilizerX {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {s₁ s₂ : F2Chain (BoxSlot3D L q_code)}
    (hs₁ : s₁ ∈ descriptorStabilizerX ω) (hs₂ : s₂ ∈ descriptorStabilizerX ω) :
    s₁ + s₂ ∈ descriptorStabilizerX ω := by
  rcases hs₁ with ⟨c₁, rfl⟩
  rcases hs₂ with ⟨c₂, rfl⟩
  refine ⟨c₁ + c₂, ?_⟩
  ext p
  change (∑ mX, descriptorCheckXChain ω mX.1 mX.2 p * c₁ mX) +
      (∑ mX, descriptorCheckXChain ω mX.1 mX.2 p * c₂ mX) =
    ∑ mX, descriptorCheckXChain ω mX.1 mX.2 p * (c₁ mX + c₂ mX)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mX _ => (mul_add _ _ _).symm)

lemma descriptorCheckXChain_mem_descriptorStabilizerX {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (v : Box3D L) (idx : Fin m_max) :
    descriptorCheckXChain ω v idx ∈ descriptorStabilizerX ω := by
  refine ⟨fun mX => if mX = (v, idx) then 1 else 0, ?_⟩
  ext p
  rw [Finset.sum_eq_single (v, idx)]
  · simp
  · intro mX _ hmX
    dsimp only
    rw [if_neg hmX, mul_zero]
  · intro h_abs
    exact False.elim (h_abs (Finset.mem_univ _))

lemma add_mem_descriptorStabilizerX_iff {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (z b : F2Chain (BoxSlot3D L q_code))
    (hb : b ∈ descriptorStabilizerX ω) :
    z + b ∈ descriptorStabilizerX ω ↔ z ∈ descriptorStabilizerX ω := by
  constructor
  · intro hzb
    have h_eq : (z + b) + b = z := by
      ext p
      change (z p + b p) + b p = z p
      rw [add_assoc, zmod2_add_self, add_zero]
    rw [← h_eq]
    exact add_mem_descriptorStabilizerX ω hzb hb
  · intro hz
    exact add_mem_descriptorStabilizerX ω hz hb

lemma staticCSSGroundStateUnnorm_ne_zero {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    staticCSSGroundStateUnnorm ω ≠ 0 := by
  intro h0
  let zeroCfg : ManyBodyConfig (UniformSite3D L (CodeSlotConfig q_code)) := fun _ _ => false
  have h_bits : codeConfigBits zeroCfg = 0 := by
    ext ⟨v, s⟩
    rfl
  have h_eval := congr_fun (congrArg WithLp.ofLp h0) zeroCfg
  change (if codeConfigBits zeroCfg ∈ descriptorStabilizerX ω then (1 : ℂ) else 0) = 0 at h_eval
  rw [h_bits, if_pos (zero_mem_descriptorStabilizerX ω)] at h_eval
  exact one_ne_zero h_eval

private lemma singleSlotChain_ortho_of_mem_descriptorStabilizerX {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (s : Fin q_code) (h_inact : (ω v).activeSlot s = false)
    {x : F2Chain (BoxSlot3D L q_code)} (hx : x ∈ descriptorStabilizerX ω) :
    (∑ p : BoxSlot3D L q_code, singleSlotChain v s p * x p) = 0 := by
  rcases hx with ⟨c2, rfl⟩
  rw [Finset.sum_eq_single (v, s)]
  · dsimp [singleSlotChain]
    rw [if_pos rfl, one_mul]
    refine Finset.sum_eq_zero (fun ⟨vX, idxX⟩ _ => ?_)
    have h0 : descriptorCheckXChain ω vX idxX (v, s) = 0 := by
      dsimp [descriptorCheckXChain]
      rw [if_neg]
      rintro ⟨h_lt, nb, _, h_sh, h_mask⟩
      have h_act := (h_valid.1 vX idxX nb s h_lt h_mask).2
      rw [h_sh, h_inact] at h_act
      exact Bool.noConfusion h_act
    rw [h0, zero_mul]
  · intro p _ hp
    dsimp [singleSlotChain]
    rw [if_neg hp, zero_mul]
  · intro h_abs
    exact False.elim (h_abs (Finset.mem_univ _))

private lemma descriptorCheckZChain_ortho_of_mem_descriptorStabilizerX {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (vZ : Box3D L) (idxZ : Fin m_max)
    {x : F2Chain (BoxSlot3D L q_code)} (hx : x ∈ descriptorStabilizerX ω) :
    (∑ p : BoxSlot3D L q_code, descriptorCheckZChain ω vZ idxZ p * x p) = 0 := by
  rcases hx with ⟨c2, rfl⟩
  have h_swap :
      (∑ p : BoxSlot3D L q_code,
        descriptorCheckZChain ω vZ idxZ p *
          (∑ mX : Box3D L × Fin m_max, descriptorCheckXChain ω mX.1 mX.2 p * c2 mX)) =
      ∑ mX : Box3D L × Fin m_max,
        (∑ p : BoxSlot3D L q_code,
          descriptorCheckXChain ω mX.1 mX.2 p * descriptorCheckZChain ω vZ idxZ p) * c2 mX := by
    simp_rw [ Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun mX _ => Finset.sum_congr rfl (fun p _ => ?_))
    ring
  rw [h_swap]
  refine Finset.sum_eq_zero (fun mX _ => ?_)
  rw [h_valid.2.2 mX.1 vZ mX.2 idxZ, zero_mul]

/-- Every elementary check projector `staticCSSCheckProj ω i` annihilates `staticCSSGroundStateUnnorm ω`. -/
theorem staticCSSCheckProj_apply_staticCSSGroundStateUnnorm_eq_zero {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (i : StaticCSSCheckIdx L q_code m_max) :
    staticCSSCheckProj ω i (staticCSSGroundStateUnnorm ω) = 0 := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj]
  · split_ifs with h_inact
    · ext σ
      change (2 : ℂ)⁻¹ * ((staticCSSGroundStateUnnorm ω).ofLp σ -
        pauliPhase (singleSlotChain v s) (codeConfigBits σ) *
          (staticCSSGroundStateUnnorm ω).ofLp σ) = 0
      dsimp [staticCSSGroundStateUnnorm]
      split_ifs with h_mem
      · have h_orth := singleSlotChain_ortho_of_mem_descriptorStabilizerX ω h_valid v s h_inact h_mem
        have h_ph : pauliPhase (singleSlotChain v s) (codeConfigBits σ) = 1 := by
          simp [pauliPhase, h_orth]
        rw [h_ph, mul_one, sub_self, mul_zero]
      · ring
    · rfl
  · split_ifs with h_lt
    · ext σ
      change (2 : ℂ)⁻¹ * ((staticCSSGroundStateUnnorm ω).ofLp σ -
        (staticCSSGroundStateUnnorm ω).ofLp (flipCodeConfig (descriptorCheckXChain ω v idx) σ)) = 0
      dsimp [staticCSSGroundStateUnnorm]
      rw [codeConfigBits_flipCodeConfig]
      have h_iff := add_mem_descriptorStabilizerX_iff ω (codeConfigBits σ)
        (descriptorCheckXChain ω v idx) (descriptorCheckXChain_mem_descriptorStabilizerX ω v idx)
      by_cases h_mem : codeConfigBits σ ∈ descriptorStabilizerX ω
      · rw [if_pos h_mem, if_pos (h_iff.mpr h_mem), sub_self, mul_zero]
      · rw [if_neg h_mem, if_neg (mt h_iff.mp h_mem), sub_self, mul_zero]
    · rfl
  · split_ifs with h_lt
    · ext σ
      change (2 : ℂ)⁻¹ * ((staticCSSGroundStateUnnorm ω).ofLp σ -
        pauliPhase (descriptorCheckZChain ω v idx) (codeConfigBits σ) *
          (staticCSSGroundStateUnnorm ω).ofLp σ) = 0
      dsimp [staticCSSGroundStateUnnorm]
      split_ifs with h_mem
      · have h_orth := descriptorCheckZChain_ortho_of_mem_descriptorStabilizerX ω h_valid v idx h_mem
        have h_ph : pauliPhase (descriptorCheckZChain ω v idx) (codeConfigBits σ) = 1 := by
          simp [pauliPhase, h_orth]
        rw [h_ph, mul_one, sub_self, mul_zero]
      · ring
    · rfl

private lemma list_prod_one_sub_apply_eq_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} (l : List ι) (Q : ι → (E →L[ℂ] E)) (ψ : E)
    (hQ : ∀ i ∈ l, Q i ψ = 0) :
    (l.map (fun i => 1 - Q i)).prod ψ = ψ := by
  induction l with
  | nil => rfl
  | cons i tail ih =>
    rw [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply,
      ih (fun j hj => hQ j (List.mem_cons_of_mem i hj)),
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      hQ i List.mem_cons_self, sub_zero]

/-- **Static CSS `IndexedCommutingProjectorHamiltonian` Lifted from a Valid Descriptor Field $\omega$**:
    Realizes $H_0 = \sum_i Q_i$ on `ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))`
    with unit weights $w_i = 1$ and check supports `staticCSSCheckSupport ω`. -/
def staticCSSSystem {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω) :
    IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max) where
  checkProj := staticCSSCheckProj ω
  weight := fun _ => 1
  support := staticCSSCheckSupport ω
  is_projector := fun i =>
    ⟨staticCSSCheckProj_isIdempotent ω i, staticCSSCheckProj_isSelfAdjoint ω i⟩
  is_supported := staticCSSCheckProj_supportedOn ω
  pairwise_commute := staticCSSCheckProj_comm_of_validDescriptorField ω h_valid
  weight_ge_one := fun _ => le_rfl
  frustration_free := by
    intro h_zero
    have h_fix :
        (((Finset.univ : Finset (StaticCSSCheckIdx L q_code m_max)).toList.map
          (fun i => 1 - staticCSSCheckProj ω i)).prod) (staticCSSGroundStateUnnorm ω) =
        staticCSSGroundStateUnnorm ω :=
      list_prod_one_sub_apply_eq_self _ _ _ (fun i _ =>
        staticCSSCheckProj_apply_staticCSSGroundStateUnnorm_eq_zero ω h_valid i)
    rw [h_zero, ContinuousLinearMap.zero_apply] at h_fix
    exact staticCSSGroundStateUnnorm_ne_zero ω h_fix.symm

lemma staticCSSSystem_P0_apply_groundStateUnnorm {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω) :
    (staticCSSSystem ω h_valid).P0 (staticCSSGroundStateUnnorm ω) =
      staticCSSGroundStateUnnorm ω :=
  list_prod_one_sub_apply_eq_self _ _ _ (fun i _ =>
    staticCSSCheckProj_apply_staticCSSGroundStateUnnorm_eq_zero ω h_valid i)

/-! ## 3. Commutation and Local/Global Ground-Projector Absorption of Stabilizer Generators -/

lemma commute_weylPauliZ_staticCSSCheckProj_of_ortho {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a : BoxSlot3D L q_code → ZMod 2)
    (ha_orth : ∀ (v : Box3D L) (idx : Fin m_max), idx.val < (ω v).numXChecks.val →
      (∑ p : BoxSlot3D L q_code, a p * descriptorCheckXChain ω v idx p) = 0)
    (i : StaticCSSCheckIdx L q_code m_max) :
    Commute (weylPauliZ a) (staticCSSCheckProj ω i) := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj]
  · split_ifs
    · exact commute_right_half_one_sub_clm (weylPauliZ_comm a _)
    · exact Commute.zero_right _
  · split_ifs with h_lt
    · exact commute_right_half_one_sub_clm
        (weylPauliX_comm_weylPauliZ_of_symplectic_zero a _ (ha_orth v idx h_lt)).symm
    · exact Commute.zero_right _
  · split_ifs
    · exact commute_right_half_one_sub_clm (weylPauliZ_comm a _)
    · exact Commute.zero_right _

lemma commute_weylPauliX_staticCSSCheckProj_of_ortho {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (b : BoxSlot3D L q_code → ZMod 2)
    (hb_act : ∀ p : BoxSlot3D L q_code, b p ≠ 0 → (ω p.1).activeSlot p.2 = true)
    (hb_orth : ∀ (v : Box3D L) (idx : Fin m_max), idx.val < (ω v).numZChecks.val →
      (∑ p : BoxSlot3D L q_code, b p * descriptorCheckZChain ω v idx p) = 0)
    (i : StaticCSSCheckIdx L q_code m_max) :
    Commute (weylPauliX b) (staticCSSCheckProj ω i) := by
  rcases i with ⟨v, s⟩ | ⟨v, idx⟩ | ⟨v, idx⟩ <;> dsimp [staticCSSCheckProj]
  · split_ifs with h_inact
    · apply commute_right_half_one_sub_clm
      apply weylPauliX_comm_weylPauliZ_of_symplectic_zero
      rw [Finset.sum_eq_single (v, s)]
      · dsimp [singleSlotChain]
        rw [if_pos rfl, one_mul]
        by_contra hb_ne
        have h_act := hb_act (v, s) hb_ne
        rw [h_inact] at h_act
        exact Bool.noConfusion h_act
      · intro p _ hp
        dsimp [singleSlotChain]
        rw [if_neg hp, zero_mul]
      · intro h_abs
        exact False.elim (h_abs (Finset.mem_univ _))
    · exact Commute.zero_right _
  · split_ifs
    · exact commute_right_half_one_sub_clm (weylPauliX_comm b _)
    · exact Commute.zero_right _
  · split_ifs with h_lt
    · apply commute_right_half_one_sub_clm
      apply weylPauliX_comm_weylPauliZ_of_symplectic_zero
      have h0 := hb_orth v idx h_lt
      simpa only [mul_comm] using h0
    · exact Commute.zero_right _

lemma commute_with_P_loc_of_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : ∀ i : ι, Commute U (sys.checkProj i))
    (B : Finset (BoxD D L)) :
    Commute U (sys.localGroundProj B) := by
  dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
    IndexedCommutingProjectorHamiltonian.localGroundProj]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  exact commute_one_sub_right (h_comm i)

lemma commute_with_P0_of_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : ∀ i : ι, Commute U (sys.checkProj i)) :
    Commute U sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.P0,
    IndexedCommutingProjectorHamiltonian.groundProj]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  exact commute_one_sub_right (h_comm i)

lemma commute_with_H0_of_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : ∀ i : ι, Commute U (sys.checkProj i)) :
    Commute sys.H0 U := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0]
  apply Commute.sum_left
  intro i _
  rw [commute_iff_eq, clm_smul_mul, clm_mul_smul, (h_comm i).symm.eq]

lemma weylPauliZ_singleSlotChain_commute_checkProj {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (s : Fin q_code) (h_inact : (ω v).activeSlot s = false)
    (i : StaticCSSCheckIdx L q_code m_max) :
    Commute (weylPauliZ (singleSlotChain v s)) (staticCSSCheckProj ω i) := by
  apply commute_weylPauliZ_staticCSSCheckProj_of_ortho
  intro vX idxX _
  exact singleSlotChain_ortho_of_mem_descriptorStabilizerX ω h_valid v s h_inact
    (descriptorCheckXChain_mem_descriptorStabilizerX ω vX idxX)

lemma weylPauliZ_descriptorCheckZChain_commute_checkProj {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (idx : Fin m_max)
    (i : StaticCSSCheckIdx L q_code m_max) :
    Commute (weylPauliZ (descriptorCheckZChain ω v idx)) (staticCSSCheckProj ω i) := by
  apply commute_weylPauliZ_staticCSSCheckProj_of_ortho
  intro vX idxX _
  exact descriptorCheckZChain_ortho_of_mem_descriptorStabilizerX ω h_valid v idx
    (descriptorCheckXChain_mem_descriptorStabilizerX ω vX idxX)

lemma weylPauliX_descriptorCheckXChain_commute_checkProj {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (idx : Fin m_max) (h_lt : idx.val < (ω v).numXChecks.val)
    (i : StaticCSSCheckIdx L q_code m_max) :
    Commute (weylPauliX (descriptorCheckXChain ω v idx)) (staticCSSCheckProj ω i) := by
  apply commute_weylPauliX_staticCSSCheckProj_of_ortho
  · intro ⟨w, s⟩ h_ne
    dsimp [descriptorCheckXChain] at h_ne
    split_ifs at h_ne with h_ex
    · rcases h_ex with ⟨_, nb, _, rfl, h_mask⟩
      exact (h_valid.1 v idx nb s h_lt h_mask).2
    · exact False.elim (h_ne rfl)
  · intro vZ idxZ _
    exact h_valid.2.2 v vZ idx idxZ

lemma weylPauliZ_singleSlotChain_mul_P_loc {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (s : Fin q_code) (B : Finset (Box3D L))
    (h_inact : (ω v).activeSlot s = false) (hvB : v ∈ B) :
    weylPauliZ (singleSlotChain v s) * (staticCSSSystem ω h_valid).localGroundProj B =
      (staticCSSSystem ω h_valid).localGroundProj B := by
  have hiB : (staticCSSSystem ω h_valid).support (Sum.inl (v, s)) ⊆ B := by
    dsimp [staticCSSSystem, staticCSSCheckSupport]
    exact Finset.singleton_subset_iff.mpr hvB
  have h_zero := (staticCSSSystem ω h_valid).checkProj_mul_P_loc_eq_zero (Sum.inl (v, s)) B hiB
  dsimp [staticCSSSystem, staticCSSCheckProj] at h_zero
  rw [if_pos h_inact] at h_zero
  exact sub_eq_zero_of_half_one_sub_mul_eq_zero h_zero

lemma weylPauliZ_singleSlotChain_mul_P0 {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (s : Fin q_code) (h_inact : (ω v).activeSlot s = false) :
    weylPauliZ (singleSlotChain v s) * (staticCSSSystem ω h_valid).P0 =
      (staticCSSSystem ω h_valid).P0 := by
  rw [← ((staticCSSSystem ω h_valid).localProj_mul_proj0_eq_proj0 Finset.univ).1, ← mul_assoc,
    weylPauliZ_singleSlotChain_mul_P_loc ω h_valid v s Finset.univ h_inact (Finset.mem_univ v)]

lemma weylPauliZ_descriptorCheckZChain_mul_P_loc {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (idx : Fin m_max) (B : Finset (Box3D L))
    (h_lt : idx.val < (ω v).numZChecks.val) (hB : boxBall v r_0 ⊆ B) :
    weylPauliZ (descriptorCheckZChain ω v idx) * (staticCSSSystem ω h_valid).localGroundProj B =
      (staticCSSSystem ω h_valid).localGroundProj B := by
  have hiB : (staticCSSSystem ω h_valid).support (Sum.inr (Sum.inr (v, idx))) ⊆ B := hB
  have h_zero := (staticCSSSystem ω h_valid).checkProj_mul_P_loc_eq_zero
    (Sum.inr (Sum.inr (v, idx))) B hiB
  dsimp [staticCSSSystem, staticCSSCheckProj] at h_zero
  rw [if_pos h_lt] at h_zero
  exact sub_eq_zero_of_half_one_sub_mul_eq_zero h_zero

lemma weylPauliZ_descriptorCheckZChain_mul_P0 {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (idx : Fin m_max) (h_lt : idx.val < (ω v).numZChecks.val) :
    weylPauliZ (descriptorCheckZChain ω v idx) * (staticCSSSystem ω h_valid).P0 =
      (staticCSSSystem ω h_valid).P0 := by
  rw [← ((staticCSSSystem ω h_valid).localProj_mul_proj0_eq_proj0 Finset.univ).1, ← mul_assoc,
    weylPauliZ_descriptorCheckZChain_mul_P_loc ω h_valid v idx Finset.univ h_lt
      (Finset.subset_univ _)]

lemma weylPauliX_descriptorCheckXChain_mul_P_loc {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (idx : Fin m_max) (B : Finset (Box3D L))
    (h_lt : idx.val < (ω v).numXChecks.val) (hB : boxBall v r_0 ⊆ B) :
    weylPauliX (descriptorCheckXChain ω v idx) * (staticCSSSystem ω h_valid).localGroundProj B =
      (staticCSSSystem ω h_valid).localGroundProj B := by
  have hiB : (staticCSSSystem ω h_valid).support (Sum.inr (Sum.inl (v, idx))) ⊆ B := hB
  have h_zero := (staticCSSSystem ω h_valid).checkProj_mul_P_loc_eq_zero
    (Sum.inr (Sum.inl (v, idx))) B hiB
  dsimp [staticCSSSystem, staticCSSCheckProj] at h_zero
  rw [if_pos h_lt] at h_zero
  exact sub_eq_zero_of_half_one_sub_mul_eq_zero h_zero

lemma weylPauliX_descriptorCheckXChain_mul_P0 {L q_code r_0 m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField ω)
    (v : Box3D L) (idx : Fin m_max) (h_lt : idx.val < (ω v).numXChecks.val) :
    weylPauliX (descriptorCheckXChain ω v idx) * (staticCSSSystem ω h_valid).P0 =
      (staticCSSSystem ω h_valid).P0 := by
  rw [← ((staticCSSSystem ω h_valid).localProj_mul_proj0_eq_proj0 Finset.univ).1, ← mul_assoc,
    weylPauliX_descriptorCheckXChain_mul_P_loc ω h_valid v idx Finset.univ h_lt
      (Finset.subset_univ _)]

/-! ## 4. Finset-Sum Stabilizer Absorption on `P_loc B` and `P0` -/

lemma weylPauliZ_finset_sum_mul_eq {L q_code : ℕ} {α : Type*} [DecidableEq α]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset α) (c : α → ZMod 2) (f : α → BoxSlot3D L q_code → ZMod 2)
    (P : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
    (h_abs : ∀ x ∈ s, c x ≠ 0 → weylPauliZ (f x) * P = P) :
    weylPauliZ (∑ x ∈ s, c x • f x) * P = P := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, weylPauliZ_zero, one_mul]
  | @insert x₀ t hx₀ ih =>
    rw [Finset.sum_insert hx₀, weylPauliZ_add, mul_assoc,
      ih (fun x hx => h_abs x (Finset.mem_insert_of_mem hx))]
    rcases zmod2_eq_zero_or_one (c x₀) with hc0 | hc1
    · rw [hc0, zero_smul, weylPauliZ_zero, one_mul]
    · have hc_ne : c x₀ ≠ 0 := by rw [hc1]; decide
      rw [hc1, one_smul]
      exact h_abs x₀ (Finset.mem_insert_self x₀ t) hc_ne

lemma weylPauliX_finset_sum_mul_eq {L q_code : ℕ} {α : Type*} [DecidableEq α]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset α) (c : α → ZMod 2) (f : α → BoxSlot3D L q_code → ZMod 2)
    (P : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
    (h_abs : ∀ x ∈ s, c x ≠ 0 → weylPauliX (f x) * P = P) :
    weylPauliX (∑ x ∈ s, c x • f x) * P = P := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, weylPauliX_zero, one_mul]
  | @insert x₀ t hx₀ ih =>
    rw [Finset.sum_insert hx₀, weylPauliX_add, mul_assoc,
      ih (fun x hx => h_abs x (Finset.mem_insert_of_mem hx))]
    rcases zmod2_eq_zero_or_one (c x₀) with hc0 | hc1
    · rw [hc0, zero_smul, weylPauliX_zero, one_mul]
    · have hc_ne : c x₀ ≠ 0 := by rw [hc1]; decide
      rw [hc1, one_smul]
      exact h_abs x₀ (Finset.mem_insert_self x₀ t) hc_ne
