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

import Proofs.HierarchicalClusterDecoder.HomologyParityPeierlsReduction

/-!
# Iterated Logical Operator Lifts and Layer-Complement Weight Identities

Constructs the primal and dual logical 1-chain representatives (`bdlIteratedLZ`, `bdlIteratedLX`) across the alternated three-layer welded code hierarchy and proves preservation of unique one-qubit logical homology (`hasUniqueLogicalHomology_bdlIterated`). Also establishes subadditive Hamming weight helpers (`zmod2ToNat_add_le`, `zmod2ToNat_sum_le`) and three-layer bit-complement involutions (`layerComplementChain_involutive`).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Proposition 3.7 (`prop:classical-hpl`)
* Part I, Section 4.3 (`subsec:stage2-star`), Lemma 4.2 (`lem:stage2-star-cleaner`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Iterated BDL Logical Operators & Duality Transfer -/

/-- Step-1 perturbed CSS code of a bundled code `B`. -/
noncomputable def bdlPerturbedOfBundled (B : BundledCSSCode3D) :
    CSSCode3D B.Q B.M_Z B.M_X :=
  let c := bdlLLLPerturbation B
  bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2

/-- Lifts a Z-logical representative `L_Z` across `bdlRandomStepX B` via `liftCylinderLZ`. -/
noncomputable def stepXLZ (B : BundledCSSCode3D) (L_Z : B.Q → ZMod 2) : (bdlRandomStepX B).Q → ZMod 2 :=
  liftCylinderLZ (bdlPerturbedOfBundled B) bdlSubdivPred L_Z

/-- Lifts an X-logical representative `L_X` across `bdlRandomStepX B` via `liftCylinderLX`. -/
noncomputable def stepXLX (B : BundledCSSCode3D) (L_X : B.Q → ZMod 2) : (bdlRandomStepX B).Q → ZMod 2 :=
  liftCylinderLX (bdlPerturbedOfBundled B) bdlSubdivPred L_X

/-- Lifts a Z-logical representative `L_Z` across `bdlRandomStepZ B` via `liftCylinderLX` on the dual cylinder step. -/
noncomputable def stepZLZ (B : BundledCSSCode3D) (L_Z : B.Q → ZMod 2) : (bdlRandomStepZ B).Q → ZMod 2 :=
  stepXLX (dualBundled B) L_Z

/-- Lifts an X-logical representative `L_X` across `bdlRandomStepZ B` via `liftCylinderLZ` on the dual cylinder step. -/
noncomputable def stepZLX (B : BundledCSSCode3D) (L_X : B.Q → ZMod 2) : (bdlRandomStepZ B).Q → ZMod 2 :=
  stepXLZ (dualBundled B) L_X

/-- Defines the `n`-th iterated Z-logical representative on `bdlIteratedBundled n`. -/
noncomputable def bdlIteratedLZ : (n : ℕ) → (bdlIteratedBundled n).Q → ZMod 2
  | 0 => surfaceLZ
  | n + 1 => stepZLZ (bdlRandomStepX (bdlIteratedBundled n)) (stepXLZ (bdlIteratedBundled n) (bdlIteratedLZ n))

/-- Defines the `n`-th iterated X-logical representative on `bdlIteratedBundled n`. -/
noncomputable def bdlIteratedLX : (n : ℕ) → (bdlIteratedBundled n).Q → ZMod 2
  | 0 => surfaceLX
  | n + 1 => stepZLX (bdlRandomStepX (bdlIteratedBundled n)) (stepXLX (bdlIteratedBundled n) (bdlIteratedLX n))

/-- Transfers `HasUniqueLogicalHomology code L_Z L_X` to `HasUniqueLogicalHomology (dualCode code) L_X L_Z`. -/
lemma hasUniqueLogicalHomology_dualCode_iff {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_hom : HasUniqueLogicalHomology code L_Z L_X) :
    HasUniqueLogicalHomology (dualCode code) L_X L_Z where
  h_syn_Z := h_hom.h_syn_X
  h_syn_X := h_hom.h_syn_Z
  h_pair := by rw [dualPairing_comm]; exact h_hom.h_pair
  h_exact_Z := by
    intro g hg
    rw [dualPairing_comm]
    exact h_hom.h_exact_X g hg
  h_exact_X := by
    intro h hh
    rw [dualPairing_comm]
    exact h_hom.h_exact_Z h hh

end BDLDecoder

open BDLDecoder

/-! ## 2. Cylinder Step & Iterated Unique Logical Homology -/

/-- Proves that any dual 1-cocycle `h` on `bdlCylinderStepX pcode M` has `cylinderResidualCocycle` equal to `liftCylinderLX (coarseProjCocycle h)`. -/
lemma cylinderResidualCocycle_eq_liftCylinderLX_of_syndrome_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (hq_z : ∀ q, ∃ z, pcode.checkZ z q ≠ 0)
    (h : BDLStepXQ pcode M → ZMod 2)
    (h_syn : syndrome (dualCode (bdlCylinderStepX pcode M)) h = 0) :
    cylinderResidualCocycle pcode M h = liftCylinderLX pcode M (coarseProjCocycle pcode M h) := by
  have h_syn_at : ∀ mZ, syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0 :=
    fun mZ => congr_fun h_syn mZ
  ext q
  rcases q with qX | ⟨v0, b⟩
  · rw [cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h (qXOwnerX pcode M qX)
      (fun _ _ _ => h_syn_at _) (fun _ _ _ _ => h_syn_at _) qX rfl]
    rfl
  · rw [cylinderResidualCocycle_inr_eq_coarse pcode M hq_z h (xq0OwnerQ pcode M v0)
      (fun x _ qX hqX => cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h x
        (fun _ _ _ => h_syn_at _) (fun _ _ _ _ => h_syn_at _) qX hqX)
      (fun _ _ _ _ => h_syn_at _) (fun _ _ _ => h_syn_at _) v0 rfl b]
    rfl

/-- Preservation of `HasUniqueLogicalHomology` across `bdlCylinderStepX pcode M`. -/
lemma hasUniqueLogicalHomology_bdlCylinderStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (hq_z : ∀ q, ∃ z, pcode.checkZ z q ≠ 0)
    {L_Z L_X : Q → ZMod 2}
    (h_hom : HasUniqueLogicalHomology pcode L_Z L_X) :
    HasUniqueLogicalHomology (bdlCylinderStepX pcode M)
      (liftCylinderLZ pcode M L_Z) (liftCylinderLX pcode M L_X) := by
  have h_syn_Z_fine : syndrome (bdlCylinderStepX pcode M) (liftCylinderLZ pcode M L_Z) = 0 :=
    cylinder_syndrome_primal_lift pcode M L_Z h_hom.h_syn_Z
  have h_syn_X_fine : syndrome (dualCode (bdlCylinderStepX pcode M)) (liftCylinderLX pcode M L_X) = 0 :=
    cylinder_syndrome_dual_lift pcode M L_X h_hom.h_syn_X
  have h_pair_fine : dualPairing (liftCylinderLZ pcode M L_Z) (liftCylinderLX pcode M L_X) = 1 := by
    rw [cylinder_dualPairing_lift]
    exact h_hom.h_pair
  apply hasUniqueLogicalHomology_of_exact_X (bdlCylinderStepX pcode M)
    (liftCylinderLZ pcode M L_Z) (liftCylinderLX pcode M L_X)
    h_syn_Z_fine h_syn_X_fine h_pair_fine
  intro h hh_syn
  have h_res := cylinderResidualCocycle_eq_liftCylinderLX_of_syndrome_zero pcode M hov h_conn hq_z h hh_syn
  have h_coarse_syn := syndrome_coarseProjCocycle_global pcode M hov h_conn h hh_syn
  have h_pair_eq : dualPairing (liftCylinderLZ pcode M L_Z) h =
      dualPairing L_Z (coarseProjCocycle pcode M h) := by
    have h_pair_res : dualPairing (liftCylinderLZ pcode M L_Z) (cylinderResidualCocycle pcode M h) =
        dualPairing (liftCylinderLZ pcode M L_Z) h := by
      dsimp [cylinderResidualCocycle, apexResidualCocycle]
      rw [dualPairing_add_right_zmod2, dualPairing_add_right_zmod2,
        dualPairing_checkGen_dual, dualPairing_checkGen_dual, h_syn_Z_fine]
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    rw [← h_pair_res, h_res, cylinder_dualPairing_lift]
  rw [h_pair_eq, ← h_hom.h_exact_X (coarseProjCocycle pcode M h) h_coarse_syn]
  constructor
  · rintro ⟨d2, hd2⟩
    have h_zero : dualPairing (liftCylinderLZ pcode M L_Z) h = 0 := by
      rw [← hd2, dualPairing_checkGen_dual, h_syn_Z_fine]
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    exact (h_hom.h_exact_X (coarseProjCocycle pcode M h) h_coarse_syn).mpr (h_pair_eq.symm.trans h_zero)
  · rintro ⟨c, hc⟩
    exact ⟨fullCylinderCocycle pcode M h c,
      checkGen_fullCylinderCocycle_global pcode M hov h_conn hq_z h c hh_syn hc⟩

/-- Monotonicity of `HasParityWitnessFamily` in the witness family size bound `N ≤ N'`. -/
lemma hasParityWitnessFamily_mono_N {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {code : CSSCode3D Q M_Z M_X} {L_Z L_X : Q → ZMod 2} {w N N' : ℕ}
    (h_le : N ≤ N')
    (h_wit : HasParityWitnessFamily code L_Z L_X w N) :
    HasParityWitnessFamily code L_Z L_X w N' := by
  rcases h_wit with ⟨ψ, W, hψ0, hW_card, hW_wt, hW_fail⟩
  exact ⟨ψ, W, hψ0, hW_card.trans h_le, hW_wt, hW_fail⟩

/-- Preservation of `HasUniqueLogicalHomology` across `bdlRandomStepX B`. -/
lemma hasUniqueLogicalHomology_stepX (B : BundledCSSCode3D) (L_Z L_X : B.Q → ZMod 2)
    (hov_B : HasBoundedCheckDegreeOverlap B)
    (hconn_B : HasConnectedXLinks B.code ∧ HasConnectedXLinks (dualCode B.code))
    (hchk_B : HasEveryQubitChecked B.code)
    (h_hom : HasUniqueLogicalHomology B.code L_Z L_X) :
    HasUniqueLogicalHomology (bdlRandomStepX B).code
      (stepXLZ B L_Z) (stepXLX B L_X) :=
  hasUniqueLogicalHomology_bdlCylinderStepX (bdlPerturbedOfBundled B) bdlSubdivPred
    hov_B.2 hconn_B.1 hchk_B.2 (hasUniqueLogicalHomology_bdlPerturbStep h_hom)

/-- Preservation of `HasUniqueLogicalHomology` across `bdlRandomStepZ B`. -/
lemma hasUniqueLogicalHomology_stepZ (B : BundledCSSCode3D) (L_Z L_X : B.Q → ZMod 2)
    (hov_B : HasBoundedCheckDegreeOverlap B)
    (hconn_B : HasConnectedXLinks B.code ∧ HasConnectedXLinks (dualCode B.code))
    (hchk_B : HasEveryQubitChecked B.code)
    (h_hom : HasUniqueLogicalHomology B.code L_Z L_X) :
    HasUniqueLogicalHomology (bdlRandomStepZ B).code
      (stepZLZ B L_Z) (stepZLX B L_X) := by
  have hov_dB := dualBundled_preserves_bounded_check_degree_overlap B hov_B
  have hconn_dB : HasConnectedXLinks (dualBundled B).code ∧ HasConnectedXLinks (dualCode (dualBundled B).code) :=
    ⟨hconn_B.2, hconn_B.1⟩
  have hchk_dB := hasEveryQubitChecked_dualCode B.code hchk_B
  have h_hom_dB := hasUniqueLogicalHomology_dualCode_iff B.code L_Z L_X h_hom
  have h_step := hasUniqueLogicalHomology_stepX (dualBundled B) L_X L_Z hov_dB hconn_dB hchk_dB h_hom_dB
  exact hasUniqueLogicalHomology_dualCode_iff (bdlRandomStepX (dualBundled B)).code _ _ h_step

/-- Establishes `HasUniqueLogicalHomology (bdlIteratedBundled n).code (bdlIteratedLZ n) (bdlIteratedLX n)` for all `n : ℕ`. -/
lemma hasUniqueLogicalHomology_bdlIterated (n : ℕ) :
    HasUniqueLogicalHomology (bdlIteratedBundled n).code (bdlIteratedLZ n) (bdlIteratedLX n) := by
  induction n with
  | zero => exact hasUniqueLogicalHomology_surfaceSeed
  | succ m ih =>
    let B := bdlIteratedBundled m
    have hov_B : HasBoundedCheckDegreeOverlap B := by
      change HasBoundedCheckDegreeOverlap (bdlIteratedBundled m)
      rw [bdlIteratedBundled_eq]
      exact hasBoundedCheckDegreeOverlap_bdlIterated m
    have hconn_B := hasConnectedXLinks_bdlIterated m
    have hchk_B := hasEveryQubitChecked_bdlIterated m
    have h_B1 := hasUniqueLogicalHomology_stepX B (bdlIteratedLZ m) (bdlIteratedLX m)
      hov_B hconn_B hchk_B ih
    exact hasUniqueLogicalHomology_stepZ (bdlRandomStepX B)
      (stepXLZ B (bdlIteratedLZ m)) (stepXLX B (bdlIteratedLX m))
      (bdlRandomStepX_preserves_bounded_check_degree_overlap B hov_B)
      (hasConnectedXLinks_bdlRandomStepX B hconn_B (hasNoIsolatedQ_bdlIterated m))
      (hasEveryQubitChecked_bdlRandomStepX B hchk_B)
      h_B1

namespace BDLDecoder

/-- Expresses `liftCylinderLZ pcode M L_Z q_fine` as `dualPairing L_Z (projCylinderLX pcode M (singleQubit q_fine))`. -/
lemma liftCylinderLZ_apply_eq_dualPairing_projCylinderLX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L_Z : Q → ZMod 2) (q_fine : BDLStepXQ pcode M) :
    liftCylinderLZ pcode M L_Z q_fine =
      dualPairing L_Z (projCylinderLX pcode M (singleQubit q_fine)) := by
  rcases projCylinderLX_singleQubit_dichotomy pcode M L_Z q_fine with ⟨h0, hl0⟩ | ⟨q0, hq0, hlq0⟩
  · rw [h0, hl0]
    dsimp [dualPairing]
    simp
  · rw [hq0, hlq0, dualPairing_singleQubit_right]

/-- Proves `checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M c_cone)` vanishes on `(Sum.inl q0', 0)`. -/
lemma checkGen_dual_layer1ConeCochain_inr_center0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c_cone : M_X → Fin 2 → ZMod 2) (q0' : Q) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M c_cone)
      (Sum.inr (Sum.inl q0', 0)) = 0 := by
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, dualF2ChainComplex]
  dsimp [bdlStepXCheckX]
  apply Finset.sum_eq_zero
  intro mX _
  rcases mX with ⟨x, b⟩ | ⟨sv, b⟩
  · exact zero_mul _
  · fin_cases b
    · dsimp [layer1ConeCochain]; rw [mul_zero]
    · dsimp [bdlGXQ0]; rw [if_neg (fun hc => by have h10 := hc.2.2; revert h10; decide), zero_mul]
    · dsimp [bdlGXQ0]; rw [if_neg (fun hc => by have h20 := hc.2.2; revert h20; decide), zero_mul]

/-- Expresses `projCylinderLX pcode M h q0` as `apexResidualCocycle pcode M h (Sum.inr (Sum.inl q0, 0))`. -/
lemma projCylinderLX_eq_apexResidualCocycle_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (q0 : Q) :
    projCylinderLX pcode M h q0 = apexResidualCocycle pcode M h (Sum.inr (Sum.inl q0, 0)) := by
  rw [← coarseProjCocycle_eq_projCylinderLX]
  change apexResidualCocycle pcode M h (Sum.inr (Sum.inl q0, 0)) +
    checkGen (dualCode (bdlCylinderStepX pcode M))
      (layer1ConeCochain pcode M (coneLinkVal pcode M h))
      (Sum.inr (Sum.inl q0, 0)) = _
  rw [checkGen_dual_layer1ConeCochain_inr_center0, add_zero]

/-- Unified layer-`b` coned coarse cochain `projCylinderLXLayer pcode M b h`. -/
noncomputable def projCylinderLXLayer {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (b : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (q0 : Q) : ZMod 2 :=
  apexResidualCocycle pcode M h (Sum.inr (Sum.inl q0, b))

/-- Identifies `projCylinderLXLayer pcode M 0 h` with `projCylinderLX pcode M h`. -/
lemma projCylinderLXLayer_zero_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) :
    projCylinderLXLayer pcode M 0 h = projCylinderLX pcode M h := by
  ext q0
  exact (projCylinderLX_eq_apexResidualCocycle_zero pcode M h q0).symm

/-- Adjointness between `liftCylinderLZ` and `projCylinderLX`. -/
lemma dualPairing_liftCylinderLZ_left {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L_Z : Q → ZMod 2) (h : BDLStepXQ pcode M → ZMod 2) :
    dualPairing (liftCylinderLZ pcode M L_Z) h =
      dualPairing L_Z (projCylinderLX pcode M h) := by
  have h_lift : ∀ q_fine : BDLStepXQ pcode M,
      liftCylinderLZ pcode M L_Z q_fine =
      ∑ q0 : Q, L_Z q0 * liftCylinderLZ pcode M (singleQubit q0) q_fine := by
    intro q_fine
    rw [liftCylinderLZ_apply_eq_dualPairing_projCylinderLX pcode M L_Z q_fine]
    dsimp only [dualPairing]
    apply Finset.sum_congr rfl
    intro q0 _
    dsimp only [projCylinderLX]
    rw [dualPairing_singleQubit_right]
  dsimp [dualPairing, projCylinderLX]
  simp_rw [h_lift, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q0 _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q_fine _
  ring

end BDLDecoder

/-! ## 3. Non-Negative Integer Weight on `ZMod 2` and Layer-Complement Involution -/

/-- Canonical lift $|b|_{\mathbb{Z}} \in \{0, 1\} \subset \mathbb{N}$ of a `ZMod 2` element to $\mathbb{N}$. -/
def zmod2ToNat (b : ZMod 2) : ℕ :=
  b.val

/-- `zmod2ToNat b` agrees with the indicator `if b ≠ 0 then 1 else 0`. -/
lemma zmod2ToNat_eq_ite (b : ZMod 2) :
    zmod2ToNat b = if b ≠ 0 then 1 else 0 := by
  fin_cases b <;> rfl

@[simp]
lemma zmod2ToNat_zero : zmod2ToNat 0 = 0 := rfl

@[simp]
lemma zmod2ToNat_one : zmod2ToNat 1 = 1 := rfl

/-- Upper bound `zmod2ToNat b ≤ 1` for all `b : ZMod 2`. -/
lemma zmod2ToNat_le_one (b : ZMod 2) : zmod2ToNat b ≤ 1 := by
  fin_cases b <;> decide

/-- **$\mathbb{Z}_{\ge 0}$-Triangle Inequality:** $|a + b|_{\mathbb{Z}} \le |a|_{\mathbb{Z}} + |b|_{\mathbb{Z}}$ in $\mathbb{N}$. -/
theorem zmod2ToNat_add_le (a b : ZMod 2) :
    zmod2ToNat (a + b) ≤ zmod2ToNat a + zmod2ToNat b := by
  fin_cases a <;> fin_cases b <;> decide

/-- **Finite-Sum $\mathbb{Z}_{\ge 0}$-Subadditivity (`zmod2ToNat_sum_le`):** -/
theorem zmod2ToNat_sum_le {α : Type*} (S : Finset α) (f : α → ZMod 2) :
    zmod2ToNat (∑ x ∈ S, f x) ≤ ∑ x ∈ S, zmod2ToNat (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (zmod2ToNat_add_le (f a) (∑ x ∈ s, f x)).trans (Nat.add_le_add_left ih _)

/-- The layer-complement involution $\bar{c}_1(q) = 1 + c_1(q)$ on a binary 1-chain `c1 : α → ZMod 2`. -/
def layerComplementChain {α : Type*} (c1 : α → ZMod 2) : α → ZMod 2 :=
  fun q => 1 + c1 q

/-- Involution property: complementing twice returns the original 1-chain `c1`. -/
@[simp]
lemma layerComplementChain_involutive {α : Type*} (c1 : α → ZMod 2) :
    layerComplementChain (layerComplementChain c1) = c1 := by
  ext q
  dsimp [layerComplementChain]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [← add_assoc, h11, zero_add]

/-- **Vertical Coboundary Invariance (`layerComplementChain_add_cancel`):** -/
theorem layerComplementChain_add_cancel {α : Type*} (c1 : α → ZMod 2) (q1 q2 : α) :
    layerComplementChain c1 q1 + layerComplementChain c1 q2 = c1 q1 + c1 q2 := by
  dsimp [layerComplementChain]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  calc (1 + c1 q1) + (1 + c1 q2)
    _ = ((1 : ZMod 2) + 1) + (c1 q1 + c1 q2) := by ring
    _ = c1 q1 + c1 q2 := by rw [h11, zero_add]

/-- Pointwise complement identity in $\mathbb{N}$. -/
lemma zmod2ToNat_layerComplementChain_add {α : Type*} (c1 : α → ZMod 2) (q : α) :
    zmod2ToNat (layerComplementChain c1 q) + zmod2ToNat (c1 q) = 1 := by
  dsimp [layerComplementChain]
  generalize c1 q = b
  fin_cases b <;> decide

end WeldedHierarchy
