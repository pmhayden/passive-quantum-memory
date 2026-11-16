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

import Proofs.HierarchicalClusterDecoder.Stage1CylinderSubadditivity

/-!
# Stage-1 Local Cylinder Cleaner Existence and 4/3 Export Bound

Evaluates the horizontal and collar export weights of the four candidate Stage-1 cylinder cleaners (`exportXQ_cylCleanerCand_inl_eq`, `sum_exportXQ_cylCleanerCand_inl_eq`) and bounds azimuthal 1-cocycle obstructions within clean sectors (`h1_azimuthal_eq_zero_of_sector`). Proves `exists_local_cylinder_cleaner`, showing every cylinder admits a local cleaner canceling interior cylinder syndromes with interface export weight at most 4/3 of the local syndrome weight.

## References

* Part I, Section 4.2 (`subsec:stage1-cylinder`), Lemma 4.1 (`lem:stage1-cylinder-cleaner`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Outer Boundary Arm Decomposition and Export Formulas -/

/-- Unified 3-candidate net arm export vector `cylArmVec b0 α σ_c`. -/
def cylArmVec (b0 : Fin 3) (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) : Fin 3 → ZMod 2 :=
  match b0 with
  | 0 => cylArmVec0 α σ_c
  | 1 => cylArmVec1 α σ_c
  | 2 => cylArmVec2 α σ_c

/-- Step-`k` horizontal outer residual bit on sector `s : ActiveZLink pcode`. -/
noncomputable def cylHorizBit {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (s : ActiveZLink pcode) (k : Fin (M + 1)) (b : Fin 3) : ZMod 2 :=
  apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b))))

/-- Step-`k` collar syndrome bit on sector `s : ActiveZLink pcode`. -/
noncomputable def cylCollarBit {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (s : ActiveZLink pcode) (k : Fin (M + 1)) (v : Fin 2) : ZMod 2 :=
  syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inr (s, k, v)))

/-- Sector horizontal residual sum on cylinder `x` and `eZ : ActiveZ pcode`. -/
noncomputable def cylHorizVecX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) (eZ : ActiveZ pcode) (b : Fin 3) : ZMod 2 :=
  if hx : pcode.checkX x eZ.val.1 ≠ 0 then
    ∑ k : Fin (M + 1), cylHorizBit pcode M h ⟨(x, eZ), hx⟩ k b
  else 0

/-- Sector collar syndrome sum on cylinder `x` and `eZ : ActiveZ pcode`. -/
noncomputable def cylCollarVecX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) (eZ : ActiveZ pcode) (v : Fin 2) : ZMod 2 :=
  if hx : pcode.checkX x eZ.val.1 ≠ 0 then
    ∑ k : Fin (M + 1), cylCollarBit pcode M h ⟨(x, eZ), hx⟩ k v
  else 0

/-- Explicit formula for `cylCleanerCand` on outer boundary segment edges. -/
lemma cylCleanerCand_outer_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (s : ActiveZLink pcode) (hs : s.val.1 = x) (k : Fin (M + 1)) (b : Fin 3) :
    cylCleanerCand pcode M b0 h x
      (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b)))) =
    cylArmVec b0 (cylHorizBit pcode M h s k) (cylCollarBit pcode M h s k) b := by
  have h_owner : cX1OwnerX pcode M (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b))) = x := hs
  dsimp [cylCleanerCand, restrictCX1]
  rw [if_pos h_owner]
  change apexResidualCocycle pcode M h
      (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b)))) +
    checkGen (dualCode (bdlCylinderStepX pcode M))
      (outerVertCancelCochain pcode M b0 h)
      (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b)))) = _
  rw [checkGen_outerVertCancelCochain_outer]
  dsimp [outerVertCancelCochain, mkOuterShellVertex]
  rw [if_pos rfl, if_pos rfl]
  have hc0 := collar_vert_sum_eq pcode M h s k 0
  have hc1 := collar_vert_sum_eq pcode M h s k 1
  change apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k, 0)))) +
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, 0)))) =
    cylHorizBit pcode M h s k 0 + cylHorizBit pcode M h s k 1 + cylCollarBit pcode M h s k 0 at hc0
  change apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k, 1)))) +
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, 1)))) =
    cylHorizBit pcode M h s k 0 + cylHorizBit pcode M h s k 2 + cylCollarBit pcode M h s k 1 at hc1
  change cylHorizBit pcode M h s k b + _ = _
  have h_alg1 : ∀ (a0 a1 c0 : ZMod 2), a1 + (a0 + a1 + c0) = a0 + c0 := by decide
  have h_alg2 : ∀ (a0 a2 c1 : ZMod 2), a2 + (a0 + a2 + c1) = a0 + c1 := by decide
  have h_alg3 : ∀ (a0 a1 c0 : ZMod 2), a0 + (a0 + a1 + c0) = a1 + c0 := by decide
  have h_alg4 : ∀ (a0 a1 a2 r0s r1s r0e r1e c0 c1 : ZMod 2),
      r0s + r0e = a0 + a1 + c0 → r1s + r1e = a0 + a2 + c1 →
      a2 + ((r0s + r1s) + (r0e + r1e)) = a1 + c0 + c1 := by decide
  have h_alg5 : ∀ (a0 a2 c1 : ZMod 2), a0 + (a0 + a2 + c1) = a2 + c1 := by decide
  have h_alg6 : ∀ (a0 a1 a2 r0s r1s r0e r1e c0 c1 : ZMod 2),
      r0s + r0e = a0 + a1 + c0 → r1s + r1e = a0 + a2 + c1 →
      a1 + ((r0s + r1s) + (r0e + r1e)) = a2 + c0 + c1 := by decide
  fin_cases b0 <;> fin_cases b <;> dsimp [cylArmVec, cylArmVec0, cylArmVec1, cylArmVec2]
  · simp
  · rw [hc0]; exact h_alg1 _ _ _
  · rw [hc1]; exact h_alg2 _ _ _
  · rw [hc0]; exact h_alg3 _ _ _
  · simp
  · exact h_alg4 _ _ _ _ _ _ _ _ _ hc0 hc1
  · rw [hc1]; exact h_alg5 _ _ _
  · exact h_alg6 _ _ _ _ _ _ _ _ _ hc0 hc1
  · simp

/-- Evaluates `exportXQ` of `cylCleanerCand` on horizontal boundary arm coordinates (`Sum.inl`). -/
lemma exportXQ_cylCleanerCand_inl_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) (b : Fin 3) :
    exportXQ pcode M (cylCleanerCand pcode M b0 h x) (Sum.inl (eZ, k, b)) =
      if hx : pcode.checkX x eZ.val.1 ≠ 0 then
        cylArmVec b0 (cylHorizBit pcode M h ⟨(x, eZ), hx⟩ k) (cylCollarBit pcode M h ⟨(x, eZ), hx⟩ k) b
      else 0 := by
  rw [exportXQ_apply]
  by_cases hx : pcode.checkX x eZ.val.1 ≠ 0
  · rw [dif_pos hx]
    let s : ActiveZLink pcode := ⟨(x, eZ), hx⟩
    rw [Finset.sum_eq_single (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b)))]
    · dsimp [bdlGXQ1, mkOuterShellSegment, s]
      have h_zmod2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      have h_one : pcode.checkX x eZ.val.1 = 1 := h_zmod2 _ hx
      rw [if_pos ⟨rfl, rfl, rfl, rfl⟩, h_one, one_mul]
      exact cylCleanerCand_outer_eq pcode M b0 h x s rfl k b
    · intro qX _ hne
      rcases qX with ⟨rv, bX⟩ | ⟨⟨seg, bX⟩ | ⟨xv, vX⟩⟩
      · exact zero_mul _
      · dsimp [bdlGXQ1]
        by_cases hc : seg.val.2.1 = Fin.last M ∧ seg.val.1.val.2 = eZ ∧ seg.val.2.2 = k ∧ bX = b
        · by_cases h_own : seg.val.1.val.1 = x
          · exfalso
            apply hne
            apply congr_arg Sum.inr
            apply congr_arg Sum.inl
            refine Prod.ext ?_ hc.2.2.2
            apply Subtype.ext
            refine Prod.ext ?_ (Prod.ext hc.1 hc.2.2.1)
            exact Subtype.ext (Prod.ext h_own hc.2.1)
          · rw [if_pos hc]
            have h_own' : cX1OwnerX pcode M (Sum.inr (Sum.inl (seg, bX))) ≠ x := h_own
            dsimp [cylCleanerCand, restrictCX1]
            rw [if_neg h_own', mul_zero]
        · rw [if_neg hc, zero_mul]
      · exact zero_mul _
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · rw [dif_neg hx]
    apply Finset.sum_eq_zero
    intro qX _
    rcases qX with ⟨rv, bX⟩ | ⟨⟨seg, bX⟩ | ⟨xv, vX⟩⟩
    · exact zero_mul _
    · dsimp [bdlGXQ1]
      by_cases hc : seg.val.2.1 = Fin.last M ∧ seg.val.1.val.2 = eZ ∧ seg.val.2.2 = k ∧ bX = b
      · rw [if_pos hc]
        by_cases h_own : seg.val.1.val.1 = x
        · exfalso; exact hx (h_own ▸ hc.2.1 ▸ seg.val.1.property)
        · have h_own' : cX1OwnerX pcode M (Sum.inr (Sum.inl (seg, bX))) ≠ x := h_own
          dsimp [cylCleanerCand, restrictCX1]
          rw [if_neg h_own', mul_zero]
      · rw [if_neg hc, zero_mul]
    · exact zero_mul _

/-- Sums `exportXQ` of `cylCleanerCand` over the three copies `Fin 3` on a horizontal boundary arm. -/
lemma sum_exportXQ_cylCleanerCand_inl_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (eZ : ActiveZ pcode) (b : Fin 3) :
    (∑ k : Fin (M + 1), exportXQ pcode M (cylCleanerCand pcode M b0 h x) (Sum.inl (eZ, k, b))) =
      cylArmVec b0 (cylHorizVecX pcode M h x eZ) (cylCollarVecX pcode M h x eZ) b := by
  simp_rw [exportXQ_cylCleanerCand_inl_eq]
  by_cases hx : pcode.checkX x eZ.val.1 ≠ 0
  · simp_rw [dif_pos hx]
    fin_cases b0 <;> fin_cases b <;>
      dsimp [cylArmVec, cylArmVec0, cylArmVec1, cylArmVec2, cylHorizVecX, cylCollarVecX] <;>
      simp only [dif_pos hx, Finset.sum_add_distrib]
  · simp_rw [dif_neg hx]
    rw [Finset.sum_const_zero]
    fin_cases b0 <;> fin_cases b <;>
      dsimp [cylArmVec, cylArmVec0, cylArmVec1, cylArmVec2, cylHorizVecX, cylCollarVecX] <;>
      simp [dif_neg hx]

/-- Rewrites `weightNetExportXQ` of `cylCleanerCand` as a sum over active Z-edges and radial steps. -/
lemma weightNetExportXQ_cylCleanerCand_eq_sum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    weightNetExportXQ pcode M (cylCleanerCand pcode M b0 h x) =
      ∑ eZ : ActiveZ pcode,
        wt3Cyl (cylArmVec b0 (cylHorizVecX pcode M h x eZ) (cylCollarVecX pcode M h x eZ)) := by
  rw [weightNetExportXQ_cylCleanerCand_eq]
  have h_card : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
      (∑ k : Fin (M + 1), exportXQ pcode M (cylCleanerCand pcode M b0 h x) (Sum.inl (p.1, k, p.2))) ≠ 0)).card =
      ∑ p : ActiveZ pcode × Fin 3,
        if (∑ k : Fin (M + 1), exportXQ pcode M (cylCleanerCand pcode M b0 h x) (Sum.inl (p.1, k, p.2))) ≠ 0 then 1 else 0 := by
    rw [Finset.card_filter]
  rw [h_card, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro eZ _
  simp_rw [sum_exportXQ_cylCleanerCand_inl_eq]
  rw [Fin.sum_univ_three]
  rfl

/-! ## 2. Azimuthal Homotopy Vanishing Outside Active Sector -/

/-- Vanishing of the 1D homotopy sweep `bdlH1X1` on azimuthal edges outside the active cylinder sector. -/
lemma h1_azimuthal_eq_zero_of_sector {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h : BDLStepXQ pcode M → ZMod 2) (s : ActiveZLink pcode) (b : Fin 3)
    (h_syn_pos : ∀ seg' : ShellSegment pcode M, seg'.val.1 = s → seg'.val.2.1.val ≠ 0 →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg', b))) = 0)
    (h_syn_can : s.val.2.val.1 ≠ canonicalSquareQ pcode s.val.1 s.val.2.val.2 ⟨s.val.2.val.1, s.property, s.val.2.property⟩ →
      ∀ seg' : ShellSegment pcode M, seg'.val.1.val.1 = s.val.1 → seg'.val.1.val.2.val.2 = s.val.2.val.2 →
        seg'.val.2.1.val = 0 →
        syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg', b))) = 0)
    (seg : ShellSegment pcode M) (hseg : seg.val.1 = s) :
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 0 := by
  suffices h_ind : ∀ (n : ℕ) (seg : ShellSegment pcode M),
      seg.val.1 = s → seg.val.2.1.val = n →
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 0 from
    h_ind seg.val.2.1.val seg hseg rfl
  intro n
  induction n with
  | zero =>
    intro seg hseg hr0
    have hk0 : seg.val.2.2.val = 0 := by have := seg.property; omega
    let x := s.val.1
    let q := s.val.2.val.1
    let z := s.val.2.val.2
    have hX : pcode.checkX x q ≠ 0 := s.property
    have hZ : pcode.checkZ z q ≠ 0 := s.val.2.property
    have h_seg_eq : seg = cornerSeg pcode M x q z hX hZ := by
      apply Subtype.ext
      refine Prod.ext hseg (Prod.ext (Fin.ext hr0) (Fin.ext hk0))
    rw [h_seg_eq]
    let h_ex : ∃ q' : Q, pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0 := ⟨q, hX, hZ⟩
    let q_can := canonicalSquareQ pcode x z h_ex
    let h_can := canonicalSquareQ_spec pcode x z h_ex
    by_cases hq : q = q_can
    · have h_seg_can : cornerSeg pcode M x q z hX hZ = cornerSeg pcode M x q_can z h_can.1 h_can.2 := by
        apply Subtype.ext; apply Prod.ext
        · apply Subtype.ext; exact Prod.ext rfl (Subtype.ext (Prod.ext hq rfl))
        · rfl
      rw [h_seg_can]
      exact h1_cornerSeg_canonical_eq_zero pcode M h x z h_ex b
    · let seg_can := cornerSeg pcode M x q_can z h_can.1 h_can.2
      have h_syn1 : syndrome (dualCode (bdlCylinderStepX pcode M)) (apexResidualCocycle pcode M h)
          (Sum.inl (Sum.inl (seg_can, b))) = 0 := by
        dsimp [apexResidualCocycle]
        rw [syndrome_add_checkGen_dual]
        exact h_syn_can hq seg_can rfl rfl rfl
      dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX] at h_syn1
      rw [Fintype.sum_sum_type] at h_syn1
      have hQ : (∑ qQ : BDLCQ1 pcode M,
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg_can, b))) (Sum.inr qQ) *
            apexResidualCocycle pcode M h (Sum.inr qQ)) = 0 :=
        Finset.sum_eq_zero (fun _ _ => zero_mul _)
      rw [hQ, add_zero] at h_syn1
      have hX_sum : (∑ qX : BDLCX1 pcode M,
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg_can, b))) (Sum.inl qX) *
            apexResidualCocycle pcode M h (Sum.inl qX)) =
          ∑ q' : Q,
            if hX' : pcode.checkX x q' ≠ 0 then
              if hZ' : pcode.checkZ z q' ≠ 0 then
                apexResidualCocycle pcode M h
                  (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q' z hX' hZ', b))))
              else 0
            else 0 := by
        have h_can_eq : q_can = canonicalSquareQ pcode x z ⟨q_can, h_can.1, h_can.2⟩ := rfl
        have h_delta : ∀ qX : BDLCX1 pcode M,
            bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg_can, b))) (Sum.inl qX) *
              apexResidualCocycle pcode M h (Sum.inl qX) =
            ∑ q' : Q,
              if hX' : pcode.checkX x q' ≠ 0 then
                if hZ' : pcode.checkZ z q' ≠ 0 then
                  ((if qX = Sum.inl (cornerSpokeRadial pcode M x q' hX', b) then 1 else 0) +
                   (if qX = Sum.inr (Sum.inl (cornerSeg pcode M x q' z hX' hZ', b)) then 1 else 0)) *
                    apexResidualCocycle pcode M h (Sum.inl qX)
                else 0
              else 0 := by
          intro qX
          dsimp [bdlStepXCheckZ, bdlDeltaX1, seg_can, cornerSeg]
          rw [if_pos h_can_eq, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q' _
          split_ifs <;> ring
        simp_rw [h_delta]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q' _
        split_ifs with hX' hZ'
        · simp_rw [add_mul, Finset.sum_add_distrib]
          rw [Finset.sum_eq_single (Sum.inl (cornerSpokeRadial pcode M x q' hX', b))]
          · rw [Finset.sum_eq_single (Sum.inr (Sum.inl (cornerSeg pcode M x q' z hX' hZ', b)))]
            · rw [if_pos rfl, if_pos rfl, one_mul, one_mul,
                  h1_radial_eq_zero pcode M h (cornerSpokeRadial pcode M x q' hX') b, zero_add]
            · intro _ _ hne; rw [if_neg hne, zero_mul]
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
          · intro _ _ hne; rw [if_neg hne, zero_mul]
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
        · exact Finset.sum_const_zero
        · exact Finset.sum_const_zero
      rw [hX_sum] at h_syn1
      let S_ov := Finset.univ.filter (fun q' : Q => pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0)
      have h_pair_sub : ({q_can, q} : Finset Q) ⊆ S_ov := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        simp only [S_ov, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hu with rfl | rfl
        · exact h_can
        · exact ⟨hX, hZ⟩
      have h_pair_card : ({q_can, q} : Finset Q).card = 2 := Finset.card_pair (Ne.symm hq)
      have h_S_eq : S_ov = {q_can, q} :=
        (Finset.eq_of_subset_of_card_le h_pair_sub (by rw [h_pair_card]; exact hov x z)).symm
      rw [Finset.sum_eq_single q] at h_syn1
      · rw [dif_pos hX, dif_pos hZ] at h_syn1
        exact h_syn1
      · intro q' _ hne_q
        split_ifs with hX' hZ'
        · have hq'_mem : q' ∈ S_ov := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX', hZ'⟩
          rw [h_S_eq, Finset.mem_insert, Finset.mem_singleton] at hq'_mem
          rcases hq'_mem with rfl | h_eq
          · exact h1_cornerSeg_canonical_eq_zero pcode M h x z h_ex b
          · exact False.elim (hne_q h_eq)
        · rfl
        · rfl
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  | succ m ih =>
    intro seg hseg hrm
    have hr0 : seg.val.2.1.val ≠ 0 := by omega
    have h_syn1 : syndrome (dualCode (bdlCylinderStepX pcode M)) (apexResidualCocycle pcode M h)
        (Sum.inl (Sum.inl (seg, b))) = 0 := by
      dsimp [apexResidualCocycle]
      rw [syndrome_add_checkGen_dual]
      exact h_syn_pos seg hseg hr0
    dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX] at h_syn1
    rw [Fintype.sum_sum_type] at h_syn1
    have hQ : (∑ qQ : BDLCQ1 pcode M,
        bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inr qQ) *
          apexResidualCocycle pcode M h (Sum.inr qQ)) = 0 :=
      Finset.sum_eq_zero (fun _ _ => zero_mul _)
    rw [hQ, add_zero] at h_syn1
    by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · have hX_tri : (∑ qX : BDLCX1 pcode M,
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl qX) *
            apexResidualCocycle pcode M h (Sum.inl qX)) =
          apexResidualCocycle pcode M h (Sum.inl (Sum.inl (shellSegStartRadial pcode M seg, b))) +
          apexResidualCocycle pcode M h (Sum.inl (Sum.inl (shellSegEndRadial pcode M seg hr0, b))) +
          apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, b)))) := by
        dsimp [bdlStepXCheckZ, bdlDeltaX1]
        simp_rw [dif_pos h_tri, dif_neg hr0, add_mul, Finset.sum_add_distrib]
        rw [Finset.sum_eq_single (Sum.inl (shellSegStartRadial pcode M seg, b))]
        · rw [Finset.sum_eq_single (Sum.inl (shellSegEndRadial pcode M seg hr0, b))]
          · rw [Finset.sum_eq_single (Sum.inr (Sum.inl (seg, b)))]
            · simp
            · intro _ _ hne; rw [if_neg hne, zero_mul]
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
          · intro _ _ hne; rw [if_neg hne, zero_mul]
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
        · intro _ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      rw [hX_tri, h1_radial_eq_zero, h1_radial_eq_zero, zero_add, zero_add] at h_syn1
      exact h_syn1
    · have hX_rect : (∑ qX : BDLCX1 pcode M,
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl qX) *
            apexResidualCocycle pcode M h (Sum.inl qX)) =
          apexResidualCocycle pcode M h (Sum.inl (Sum.inl (shellSegStartRadial pcode M seg, b))) +
          apexResidualCocycle pcode M h (Sum.inl (Sum.inl (shellSegEndRadial pcode M seg hr0, b))) +
          apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)))) +
          apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, b)))) := by
        dsimp [bdlStepXCheckZ, bdlDeltaX1]
        simp_rw [dif_neg h_tri, add_mul, Finset.sum_add_distrib]
        rw [Finset.sum_eq_single (Sum.inl (shellSegStartRadial pcode M seg, b))]
        · rw [Finset.sum_eq_single (Sum.inl (shellSegEndRadial pcode M seg hr0, b))]
          · rw [Finset.sum_eq_single (Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)))]
            · rw [Finset.sum_eq_single (Sum.inr (Sum.inl (seg, b)))]
              · simp
              · intro _ _ hne; rw [if_neg hne, zero_mul]
              · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
            · intro _ _ hne; rw [if_neg hne, zero_mul]
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
          · intro _ _ hne; rw [if_neg hne, zero_mul]
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
        · intro _ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      have h_pred_zero : apexResidualCocycle pcode M h
          (Sum.inl (Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)))) = 0 := by
        apply ih (shellSegPred pcode M seg h_tri) hseg
        dsimp [shellSegPred, finPred]
        omega
      rw [hX_rect, h1_radial_eq_zero, h1_radial_eq_zero, h_pred_zero,
          zero_add, zero_add, zero_add] at h_syn1
      exact h_syn1

/-! ## 3. Collar and Sector Weight Bounds -/

/-- Decomposes `weightCX2OnCyl` into collar check cardinality plus interior sector check cardinality. -/
lemma weightCX2OnCyl_eq_card_add_card {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) (x : M_X) :
    weightCX2OnCyl pcode M x S =
      (Finset.univ.filter (fun m : ShellSegment pcode M × Fin 3 =>
        restrictCX2 pcode M x S (Sum.inl (Sum.inl m)) ≠ 0)).card +
      (Finset.univ.filter (fun m : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
        restrictCX2 pcode M x S (Sum.inl (Sum.inr m)) ≠ 0)).card := by
  dsimp [weightCX2OnCyl, syndromeWeightNat]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type]
  have hQZ : (∑ mZQ : BDLCQ2 pcode M ⊕ BDLCZ2 M_Z,
      if restrictCX2 pcode M x S (Sum.inr mZQ) ≠ 0 then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero; intro mZQ _
    rcases mZQ with mQ | mZ <;>
      dsimp [restrictCX2, restrictStepXMZ, stepXMZOwnerTanner, inVX, inVQ, inVZ]
  rw [hQZ, add_zero, Fintype.sum_sum_type]

/-- Bounds the sum of `wt2Cyl` over boundary arms by the cardinality of active collar checks. -/
lemma sum_wt2Cyl_le_card_collar {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    (∑ eZ : ActiveZ pcode, wt2Cyl (cylCollarVecX pcode M h x eZ)) ≤
      (Finset.univ.filter (fun m : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
        restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h)
          (Sum.inl (Sum.inr m)) ≠ 0)).card := by
  let S := syndrome (dualCode (bdlCylinderStepX pcode M)) h
  have h_lhs : (∑ eZ : ActiveZ pcode, wt2Cyl (cylCollarVecX pcode M h x eZ)) =
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 => cylCollarVecX pcode M h x p.1 p.2 ≠ 0)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro eZ _; rw [Fin.sum_univ_two]; rfl
  rw [h_lhs]
  have h_ex : ∀ p : ActiveZ pcode × Fin 2, cylCollarVecX pcode M h x p.1 p.2 ≠ 0 →
      ∃ m : ActiveZLink pcode × Fin (M + 1) × Fin 2,
        m.1.val.2 = p.1 ∧ m.2.2 = p.2 ∧ restrictCX2 pcode M x S (Sum.inl (Sum.inr m)) ≠ 0 := by
    intro ⟨eZ, v⟩ h_nz
    by_cases hx : pcode.checkX x eZ.val.1 ≠ 0
    · dsimp [cylCollarVecX] at h_nz
      rw [dif_pos hx] at h_nz
      obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_nz
      refine ⟨(⟨(x, eZ), hx⟩, k, v), rfl, rfl, ?_⟩
      have hm : stepXMZOwnerTanner pcode M (Sum.inl (Sum.inr (⟨(x, eZ), hx⟩, k, v))) ∈ ({inVX x} : Finset _) := by
        simp [stepXMZOwnerTanner, cX2OwnerX, cX2OwnerLink, inVX]
      dsimp [restrictCX2, restrictStepXMZ]; rw [if_pos hm]; exact hk
    · dsimp [cylCollarVecX] at h_nz; rw [dif_neg hx] at h_nz; exact False.elim (h_nz rfl)
  rcases (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
      cylCollarVecX pcode M h x p.1 p.2 ≠ 0)).eq_empty_or_nonempty with h_emp | ⟨p₀, hp₀⟩
  · rw [h_emp, Finset.card_empty]; exact Nat.zero_le _
  · let m₀ := Classical.choose (h_ex p₀ (Finset.mem_filter.mp hp₀).2)
    let f : ActiveZ pcode × Fin 2 → ActiveZLink pcode × Fin (M + 1) × Fin 2 := fun p =>
      if hp : cylCollarVecX pcode M h x p.1 p.2 ≠ 0 then Classical.choose (h_ex p hp) else m₀
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have h_nz : cylCollarVecX pcode M h x p.1 p.2 ≠ 0 := (Finset.mem_filter.mp hp).2
      dsimp [f]; rw [dif_pos h_nz]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Classical.choose_spec (h_ex p h_nz)).2.2⟩
    · intro p₁ hp₁ p₂ hp₂ h_eq
      have h_nz₁ : cylCollarVecX pcode M h x p₁.1 p₁.2 ≠ 0 := (Finset.mem_filter.mp hp₁).2
      have h_nz₂ : cylCollarVecX pcode M h x p₂.1 p₂.2 ≠ 0 := (Finset.mem_filter.mp hp₂).2
      dsimp [f] at h_eq; rw [dif_pos h_nz₁, dif_pos h_nz₂] at h_eq
      have hs₁ := Classical.choose_spec (h_ex p₁ h_nz₁)
      have hs₂ := Classical.choose_spec (h_ex p₂ h_nz₂)
      exact Prod.ext (hs₁.1.symm.trans (by rw [h_eq]; exact hs₂.1))
        (hs₁.2.1.symm.trans (by rw [h_eq]; exact hs₂.2.1))

/-- Bounds the sum of `wt3Cyl` over boundary arms by the cardinality of active interior sector checks. -/
lemma sum_wt3Cyl_le_card_sector {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    (∑ eZ : ActiveZ pcode, wt3Cyl (cylHorizVecX pcode M h x eZ)) ≤
      (Finset.univ.filter (fun m : ShellSegment pcode M × Fin 3 =>
        restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h)
          (Sum.inl (Sum.inl m)) ≠ 0)).card := by
  let S := syndrome (dualCode (bdlCylinderStepX pcode M)) h
  have h_lhs : (∑ eZ : ActiveZ pcode, wt3Cyl (cylHorizVecX pcode M h x eZ)) =
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 => cylHorizVecX pcode M h x p.1 p.2 ≠ 0)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro eZ _; rw [Fin.sum_univ_three]; rfl
  rw [h_lhs]
  let IsWitness (p : ActiveZ pcode × Fin 3) (m : ShellSegment pcode M × Fin 3) : Prop :=
    m.2 = p.2 ∧
    restrictCX2 pcode M x S (Sum.inl (Sum.inl m)) ≠ 0 ∧
    ((m.1.val.2.1.val ≠ 0 ∧ m.1.val.1.val.2 = p.1) ∨
     (m.1.val.2.1.val = 0 ∧ m.1.val.1.val.2.val.2 = p.1.val.2 ∧
      ∃ hx : pcode.checkX x p.1.val.1 ≠ 0,
        p.1.val.1 ≠ canonicalSquareQ pcode x p.1.val.2 ⟨p.1.val.1, hx, p.1.property⟩))
  have h_ex : ∀ p : ActiveZ pcode × Fin 3, cylHorizVecX pcode M h x p.1 p.2 ≠ 0 →
      ∃ m : ShellSegment pcode M × Fin 3, IsWitness p m := by
    intro ⟨eZ, b⟩ h_nz
    by_cases hx : pcode.checkX x eZ.val.1 ≠ 0
    · dsimp [cylHorizVecX] at h_nz
      rw [dif_pos hx] at h_nz
      obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_nz
      by_contra h_no
      apply hk
      apply h1_azimuthal_eq_zero_of_sector pcode M hov h ⟨(x, eZ), hx⟩ b _ _
        (mkOuterShellSegment pcode M ⟨(x, eZ), hx⟩ k) rfl
      · intro seg' hseg' hr0
        by_contra hS
        apply h_no
        have hm : stepXMZOwnerTanner pcode M (Sum.inl (Sum.inl (seg', b))) ∈ ({inVX x} : Finset _) := by
          simp [stepXMZOwnerTanner, cX2OwnerX, cX2OwnerLink, inVX, hseg']
        refine ⟨(seg', b), rfl, ?_, Or.inl ⟨hr0, congr_arg (fun s : ActiveZLink pcode => s.val.2) hseg'⟩⟩
        dsimp [restrictCX2, restrictStepXMZ]; rw [if_pos hm]; exact hS
      · intro hq_ne seg' hx' hz' hr0
        by_contra hS
        apply h_no
        have hm : stepXMZOwnerTanner pcode M (Sum.inl (Sum.inl (seg', b))) ∈ ({inVX x} : Finset _) := by
          simp [stepXMZOwnerTanner, cX2OwnerX, cX2OwnerLink, inVX, hx']
        refine ⟨(seg', b), rfl, ?_, Or.inr ⟨hr0, hz', hx, hq_ne⟩⟩
        dsimp [restrictCX2, restrictStepXMZ]; rw [if_pos hm]; exact hS
    · dsimp [cylHorizVecX] at h_nz; rw [dif_neg hx] at h_nz; exact False.elim (h_nz rfl)
  rcases (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
      cylHorizVecX pcode M h x p.1 p.2 ≠ 0)).eq_empty_or_nonempty with h_emp | ⟨p₀, hp₀⟩
  · rw [h_emp, Finset.card_empty]; exact Nat.zero_le _
  · let m₀ := Classical.choose (h_ex p₀ (Finset.mem_filter.mp hp₀).2)
    let f : ActiveZ pcode × Fin 3 → ShellSegment pcode M × Fin 3 := fun p =>
      if hp : cylHorizVecX pcode M h x p.1 p.2 ≠ 0 then Classical.choose (h_ex p hp) else m₀
    apply Finset.card_le_card_of_injOn f
    · intro p hp
      have h_nz : cylHorizVecX pcode M h x p.1 p.2 ≠ 0 := (Finset.mem_filter.mp hp).2
      dsimp [f]; rw [dif_pos h_nz]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Classical.choose_spec (h_ex p h_nz)).2.1⟩
    · intro p₁ hp₁ p₂ hp₂ h_eq
      have h_nz₁ : cylHorizVecX pcode M h x p₁.1 p₁.2 ≠ 0 := (Finset.mem_filter.mp hp₁).2
      have h_nz₂ : cylHorizVecX pcode M h x p₂.1 p₂.2 ≠ 0 := (Finset.mem_filter.mp hp₂).2
      dsimp [f] at h_eq; rw [dif_pos h_nz₁, dif_pos h_nz₂] at h_eq
      have hs₁ := Classical.choose_spec (h_ex p₁ h_nz₁)
      have hs₂ := Classical.choose_spec (h_ex p₂ h_nz₂)
      rw [h_eq] at hs₁
      have hb : p₁.2 = p₂.2 := hs₁.1.symm.trans hs₂.1
      rcases hs₁.2.2 with ⟨hr₁, heZ₁⟩ | ⟨hr₁, hz₁, hx₁, hq₁⟩ <;>
        rcases hs₂.2.2 with ⟨hr₂, heZ₂⟩ | ⟨hr₂, hz₂, hx₂, hq₂⟩
      · exact Prod.ext (heZ₁.symm.trans heZ₂) hb
      · exact False.elim (hr₁ hr₂)
      · exact False.elim (hr₂ hr₁)
      · rcases p₁ with ⟨⟨⟨q₁, z₁⟩, hZ₁⟩, b₁⟩
        rcases p₂ with ⟨⟨⟨q₂, z₂⟩, hZ₂⟩, b₂⟩
        have hz : z₁ = z₂ := hz₁.symm.trans hz₂
        subst hz
        have hq_eq : q₁ = q₂ := by
          by_contra hq_ne
          let h_ex_q : ∃ q' : Q, pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z₁ q' ≠ 0 := ⟨q₁, hx₁, hZ₁⟩
          let q_can := canonicalSquareQ pcode x z₁ h_ex_q
          have h_can := canonicalSquareQ_spec pcode x z₁ h_ex_q
          have h_sub : ({q_can, q₁, q₂} : Finset Q) ⊆
              Finset.univ.filter (fun q' : Q => pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z₁ q' ≠ 0) := by
            intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hu with rfl | rfl | rfl
            · exact h_can
            · exact ⟨hx₁, hZ₁⟩
            · exact ⟨hx₂, hZ₂⟩
          have h_c3 : ({q_can, q₁, q₂} : Finset Q).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hq_ne]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨Ne.symm hq₁, Ne.symm hq₂⟩
          have h_le := (Finset.card_le_card h_sub).trans (hov x z₁)
          omega
        exact Prod.ext (Subtype.ext (Prod.ext hq_eq rfl)) hb

/-! ## 4. Existence of Local Cylinder Cleaner -/

/-- Stage-1 Local Cylinder Cleaning Theorem. -/
theorem exists_local_cylinder_cleaner {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    ∃ u_x : BDLStepXQ pcode M → ZMod 2,
      (∀ q, u_x q ≠ 0 → ∃ qX, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x) ∧
      restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) (h + u_x)) = 0 ∧
      3 * weightNetExportXQ pcode M u_x ≤
        4 * weightCX2OnCyl pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h) ∧
      (restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h) = 0 → u_x = 0) := by
  by_cases h0 : restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h) = 0
  · refine ⟨0, ?_, ?_, ?_, fun _ => rfl⟩
    · intro _ h_abs; exact False.elim (h_abs rfl)
    · rw [add_zero]; exact h0
    · have h_exp0 : exportXQ pcode M 0 = 0 := by
        ext mZQ; rw [exportXQ_apply]; exact Finset.sum_eq_zero (fun _ _ => mul_zero _)
      dsimp [weightNetExportXQ]; rw [h_exp0]; simp
  · have h_sum_W : weightNetExportXQ pcode M (cylCleanerCand pcode M 0 h x) +
        weightNetExportXQ pcode M (cylCleanerCand pcode M 1 h x) +
        weightNetExportXQ pcode M (cylCleanerCand pcode M 2 h x) ≤
        4 * weightCX2OnCyl pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h) := by
      have hW0 := weightNetExportXQ_cylCleanerCand_eq_sum pcode M 0 h x
      have hW1 := weightNetExportXQ_cylCleanerCand_eq_sum pcode M 1 h x
      have hW2 := weightNetExportXQ_cylCleanerCand_eq_sum pcode M 2 h x
      have h_pt_sum : weightNetExportXQ pcode M (cylCleanerCand pcode M 0 h x) +
          weightNetExportXQ pcode M (cylCleanerCand pcode M 1 h x) +
          weightNetExportXQ pcode M (cylCleanerCand pcode M 2 h x) ≤
          4 * ((∑ eZ : ActiveZ pcode, wt3Cyl (cylHorizVecX pcode M h x eZ)) +
            (∑ eZ : ActiveZ pcode, wt2Cyl (cylCollarVecX pcode M h x eZ))) := by
        rw [hW0, hW1, hW2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
            ← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_le_sum (fun eZ _ =>
          cyl_sector_pointwise_bound (cylHorizVecX pcode M h x eZ) (cylCollarVecX pcode M h x eZ))
      have h_sec := sum_wt3Cyl_le_card_sector pcode M hov h x
      have h_col := sum_wt2Cyl_le_card_collar pcode M h x
      have h_wt := weightCX2OnCyl_eq_card_add_card pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x
      omega
    by_cases h012 : weightNetExportXQ pcode M (cylCleanerCand pcode M 0 h x) ≤
          weightNetExportXQ pcode M (cylCleanerCand pcode M 1 h x) ∧
        weightNetExportXQ pcode M (cylCleanerCand pcode M 0 h x) ≤
          weightNetExportXQ pcode M (cylCleanerCand pcode M 2 h x)
    · refine ⟨cylCleanerCand pcode M 0 h x, cylCleanerCand_support pcode M 0 h x,
        restrictCX2_syndrome_add_cylCleanerCand_eq_zero pcode M 0 h x, by omega,
        fun h_abs => False.elim (h0 h_abs)⟩
    · by_cases h12 : weightNetExportXQ pcode M (cylCleanerCand pcode M 1 h x) ≤
          weightNetExportXQ pcode M (cylCleanerCand pcode M 2 h x)
      · refine ⟨cylCleanerCand pcode M 1 h x, cylCleanerCand_support pcode M 1 h x,
          restrictCX2_syndrome_add_cylCleanerCand_eq_zero pcode M 1 h x, by omega,
          fun h_abs => False.elim (h0 h_abs)⟩
      · refine ⟨cylCleanerCand pcode M 2 h x, cylCleanerCand_support pcode M 2 h x,
          restrictCX2_syndrome_add_cylCleanerCand_eq_zero pcode M 2 h x, by omega,
          fun h_abs => False.elim (h0 h_abs)⟩

end BDLDecoder
end WeldedHierarchy
