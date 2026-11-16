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

import Proofs.RescaledGibbsAndCollarPeeling.SuperpolySplittingThreshold

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Local-to-Global Operator Norm Transfer for the Welded CSS Descriptor System

Proves the $C^*$-norm transfer inequality (`norm_proj_mul_le_of_scalar_sandwich_eq`) and instantiates single-cube local-to-global norm transfer (`bdlInhomogeneousSystem_cor1_loc`, `mem_cor1_loc_of_D_field_eq`) for `bdlInhomogeneousSystem` from relative cone acyclicity (`bdlLocalDescriptor_satisfiesBoxF2LinearTQO`).

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Bravyi and Hastings (2011), Corollary 1
-/

/-! ## 1. Single-Cube Local-to-Global Operator Norm Transfer (`bdlInhomogeneousSystem_cor1_loc`) -/

attribute [local irreducible] collarConstRCABDL bdlLambda qCodeBDL r0BDL mMaxBDL

/-- From the operator sandwich identity `P_B (S S†) P_B = c • P_B` and
`P0 (S S†) P0 = c • P0` for star projections `P_B, P0` with `P0 ≠ 0`, the C*-identity
`‖T‖^2 = ‖T T†‖` yields `‖P_B S‖ ≤ ‖P0 S‖`. -/
theorem norm_proj_mul_le_of_scalar_sandwich_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P0 P_B S : E →L[ℂ] E) (hP0 : IsStarProjection P0) (hPB : IsStarProjection P_B)
    (hP0_ne : P0 ≠ 0)
    (h_sand : ∃ c : ℂ, P_B * (S * S†) * P_B = c • P_B ∧ P0 * (S * S†) * P0 = c • P0) :
    ‖P_B * S‖ ≤ ‖P0 * S‖ := by
  rcases h_sand with ⟨c, hB_eq, h0_eq⟩
  have hPB_sa : P_B† = P_B := hPB.isSelfAdjoint.star_eq
  have hP0_sa : P0† = P0 := hP0.isSelfAdjoint.star_eq
  have h_star_PB : (P_B * S) * (P_B * S)† = c • P_B := by
    have h_adj : (P_B * S)† = S† * P_B† := star_mul P_B S
    calc (P_B * S) * (P_B * S)†
      _ = P_B * S * (S† * P_B†) := by rw [h_adj]
      _ = P_B * (S * S†) * P_B := by rw [hPB_sa]; simp only [mul_assoc]
      _ = c • P_B := hB_eq
  have h_star_P0 : (P0 * S) * (P0 * S)† = c • P0 := by
    have h_adj : (P0 * S)† = S† * P0† := star_mul P0 S
    calc (P0 * S) * (P0 * S)†
      _ = P0 * S * (S† * P0†) := by rw [h_adj]
      _ = P0 * (S * S†) * P0 := by rw [hP0_sa]; simp only [mul_assoc]
      _ = c • P0 := h0_eq
  have h_norm_PB : ‖P_B * S‖ ^ 2 = ‖c‖ * ‖P_B‖ := by
    calc ‖P_B * S‖ ^ 2
      _ = ‖(P_B * S) * (P_B * S)†‖ := by rw [sq, ← CStarRing.norm_self_mul_star]; rfl
      _ = ‖c • P_B‖ := by rw [h_star_PB]
      _ = ‖c‖ * ‖P_B‖ := norm_smul c P_B
  have h_norm_P0_sq : ‖P0 * S‖ ^ 2 = ‖c‖ * ‖P0‖ := by
    calc ‖P0 * S‖ ^ 2
      _ = ‖(P0 * S) * (P0 * S)†‖ := by rw [sq, ← CStarRing.norm_self_mul_star]; rfl
      _ = ‖c • P0‖ := by rw [h_star_P0]
      _ = ‖c‖ * ‖P0‖ := norm_smul c P0
  have h_one_le_P0 : 1 ≤ ‖P0‖ := by
    have h_ex : ∃ ψ : E, P0 ψ ≠ 0 := by
      by_contra h_all; push_neg at h_all
      exact hP0_ne (ContinuousLinearMap.ext h_all)
    rcases h_ex with ⟨ψ₀, hψ₀⟩
    let ϕ := P0 ψ₀
    have hϕ_pos : 0 < ‖ϕ‖ := norm_pos_iff.mpr hψ₀
    have hPϕ : P0 ϕ = ϕ := by
      change (P0 * P0) ψ₀ = P0 ψ₀
      rw [hP0.isIdempotentElem.eq]
    have h_le : 1 * ‖ϕ‖ ≤ ‖P0‖ * ‖ϕ‖ := by
      calc 1 * ‖ϕ‖ = ‖ϕ‖ := one_mul ‖ϕ‖
        _ = ‖P0 ϕ‖ := by rw [hPϕ]
        _ ≤ ‖P0‖ * ‖ϕ‖ := P0.le_opNorm ϕ
    exact le_of_mul_le_mul_right h_le hϕ_pos
  have hPB_le_P0 : ‖P_B‖ ≤ ‖P0‖ :=
    le_trans (isStarProjection_norm_le_one_bhm hPB) h_one_le_P0
  have h_le_sq : ‖P_B * S‖ ^ 2 ≤ ‖P0 * S‖ ^ 2 := by
    rw [h_norm_PB, h_norm_P0_sq]
    exact mul_le_mul_of_nonneg_left hPB_le_P0 (norm_nonneg c)
  nlinarith [norm_nonneg (P_B * S), norm_nonneg (P0 * S)]

/-- Unconditional single-cube local-to-global coral bound for `bdlInhomogeneousSystem k`,
derived directly from `bdlLocalDescriptor_satisfiesBoxF2LinearTQO k` via
`staticCSS_operator_sandwich_eq`. -/
theorem bdlInhomogeneousSystem_cor1_loc (k : ℕ) :
    ∀ (u : Box3D (bdlBoxSide k)) (j : ℕ), 1 ≤ j → j + 2 ≤ bdlLinearTQORadius k →
      ∀ S : ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)),
        IsSupportedOn (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) (boxCube u j) S →
        ‖(bdlInhomogeneousSystem k).localGroundProj (singleCubeSupportC (collarConstRCABDL : ℝ) u j) * S‖ ≤
          ‖(bdlInhomogeneousSystem k).P0 * S‖ := by
  intro u j _hj1 hjL S hS
  let x0 := shiftDownOne u
  let r := j + 2
  have hr1 : 1 ≤ r := by omega
  have h_sub : boxCube u j ⊆ boxCube x0 r := (isOneCollarOf_boxCube_shiftDownOne u j).1
  have hS_x0 : IsSupportedOn (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))
      (boxCube x0 r) S :=
    _root_.isSupportedOn_mono h_sub hS
  have hSS : IsSupportedOn (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))
      (boxCube x0 r) (S * S†) :=
    _root_.isSupportedOn_mul (boxCube x0 r) hS_x0 (_root_.isSupportedOn_adjoint (boxCube x0 r) hS_x0)
  have hC : ((4 * r0BDL + 3 : ℕ) : ℝ) ≤ (collarConstRCABDL : ℝ) := by
    exact_mod_cast (by unfold collarConstRCABDL r0BDL bdlLambda; omega : 4 * r0BDL + 3 ≤ collarConstRCABDL)
  have h_sand := staticCSS_operator_sandwich_eq
    (bdlLocalDescriptor k) (collarConstRCABDL : ℝ)
    (bdlLocalDescriptor_validDescriptorField k)
    (bdlLocalDescriptor_satisfiesBoxF2LinearTQO k)
    hC hr1 hjL x0 (S * S†) hSS
  exact norm_proj_mul_le_of_scalar_sandwich_eq
    (bdlInhomogeneousSystem k).P0
    ((bdlInhomogeneousSystem k).localGroundProj (singleCubeSupportC (collarConstRCABDL : ℝ) u j)) S
    (bdlInhomogeneousSystem k).isStarProjection_P0
    ((bdlInhomogeneousSystem k).isStarProjection_P_loc_bhm _)
    (bdlInhomogeneousSystem k).frustration_free h_sand

/-- Any `Inhomogeneous3DMemoryRealization` whose descriptor field equals `bdlLocalDescriptor k`
inherits the unconditional single-cube coral bound `bdlInhomogeneousSystem_cor1_loc k`. -/
theorem mem_cor1_loc_of_D_field_eq (k : ℕ)
    (mem : Inhomogeneous3DMemoryRealization (bdlBoxSide k) qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
    (hD : mem.D_field = bdlLocalDescriptor k) :
    ∀ (u : Box3D (bdlBoxSide k)) (j : ℕ), 1 ≤ j → j + 2 ≤ bdlLinearTQORadius k →
      ∀ S : ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)),
        IsSupportedOn (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) (boxCube u j) S →
        ‖mem.sys.localGroundProj (singleCubeSupportC (collarConstRCABDL : ℝ) u j) * S‖ ≤ ‖mem.sys.P0 * S‖ := by
  have h_check : mem.sys.checkProj = (bdlInhomogeneousSystem k).checkProj := by
    funext idx; rw [(mem.h_sys_checks idx).1, hD]; rfl
  have h_supp : mem.sys.support = (bdlInhomogeneousSystem k).support := by
    funext idx; rw [(mem.h_sys_checks idx).2.1, hD]; rfl
  have h_Ploc : ∀ B, mem.sys.localGroundProj B = (bdlInhomogeneousSystem k).localGroundProj B := by
    intro B
    dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj,
      IndexedCommutingProjectorHamiltonian.localGroundProj]
    rw [h_check, h_supp]
  have h_P0 : mem.sys.P0 = (bdlInhomogeneousSystem k).P0 := by
    dsimp [IndexedCommutingProjectorHamiltonian.P0,
      IndexedCommutingProjectorHamiltonian.groundProj]
    rw [h_check]
  intro u j hj1 hjL S hS
  rw [h_Ploc, h_P0]
  exact bdlInhomogeneousSystem_cor1_loc k u j hj1 hjL S hS

end
