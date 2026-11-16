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

import Proofs.ConeAcyclicityRCA.SymplecticPairingAndCone

/-!
# Layer-1 Cone Cochain, Residual Cylinder Cocycle, and Cylinder Edge Vanishing

Constructs the layer-1 azimuthal cone cochain layer1ConeCochain and the residual cocycles apexResidualCocycle and cylinderResidualCocycle obtained after radial and layer-1 coboundary gauge subtraction. Defines the link-connectivity invariant HasConnectedXLinks, extracts the per-cylinder link constant coneLinkVal, and proves that cylinderResidualCocycle vanishes identically on all cylinder 1-cells (cylinderResidualCocycle_inl_eq_zero).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.6 (`lem:block-sdr`), Proposition 3.7 (`prop:classical-hpl`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Layer-1 Cone Cochain and Corner Segment Incidence -/

/-- **Layer-1/2 Cone Indicator 0-Cochain (`layer1ConeCochain`):**
    Assigns `0` in layer `0`, `c_cone x 0` in layer `1`, and `c_cone x 1` in layer `2` of cone `x`. -/
def layer1ConeCochain {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c_cone : M_X → Fin 2 → ZMod 2) :
    BDLStepXMX pcode M → ZMod 2
  | Sum.inl (x, b) => if b = 1 then c_cone x 0 else if b = 2 then c_cone x 1 else 0
  | Sum.inr (sv, b) =>
    if b = 1 then c_cone sv.val.1.val.1 0
    else if b = 2 then c_cone sv.val.1.val.1 1
    else 0

/-- Computes the dual coboundary of `layer1ConeCochain` on `BDLCX1` 1-cells (`0` on radial/azimuthal, `f xv b` on vertical). -/
lemma checkGen_dual_layer1ConeCochain_inl {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c_cone : M_X → Fin 2 → ZMod 2) (qX : BDLCX1 pcode M) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M c_cone) (Sum.inl qX) =
      match qX with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl _) => 0
      | Sum.inr (Sum.inr (xv, b)) => c_cone xv.val.1 b := by
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  dsimp [bdlStepXCheckX]
  rcases qX with ⟨rv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, b⟩⟩
  · dsimp [bdlDeltaX0]
    by_cases hr0 : rv.val.val.2.val = 0
    · simp_rw [if_pos hr0, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_eq_single (Sum.inl (rv.val.val.1.val.1, b))]
      · rw [Finset.sum_eq_single (Sum.inr (rv.val, b))]
        · dsimp [layer1ConeCochain]
          rw [if_pos rfl, if_pos rfl]
          exact zmod2_add_self _
        · intro mX _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · simp_rw [if_neg hr0, add_mul, Finset.sum_add_distrib]
      rw [Finset.sum_eq_single (Sum.inr (radialParentVertex pcode M rv.val, b))]
      · rw [Finset.sum_eq_single (Sum.inr (rv.val, b))]
        · rw [if_pos rfl, if_pos rfl]
          dsimp [layer1ConeCochain, radialParentVertex, radialParentLink]
          exact zmod2_add_self _
        · intro mX _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · dsimp [bdlDeltaX0]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (shellSegStartVertex pcode M seg, b))]
    · rw [Finset.sum_eq_single (Sum.inr (shellSegEndVertex pcode M seg, b))]
      · rw [if_pos rfl, if_pos rfl]
        dsimp [layer1ConeCochain, shellSegStartVertex, shellSegEndVertex, bxStartLink, shellSegEndLink]
        exact zmod2_add_self _
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · dsimp [bdlDeltaX0]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (mkOuterShellVertex pcode M xv, (0 : Fin 3)))]
    · rw [Finset.sum_eq_single (Sum.inr (mkOuterShellVertex pcode M xv, b.succ))]
      · dsimp [layer1ConeCochain, mkOuterShellVertex]
        fin_cases b <;> simp
      · intro mX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Identifies `shellSegStartVertex` of `cornerSeg pcode M x q z0 hxq hzq` with `(cornerSpokeRadial pcode M x q hxq).val`. -/
lemma shellSegStartVertex_cornerSeg {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (q : Q) (z : M_Z)
    (hX : pcode.checkX x q ≠ 0) (hZ : pcode.checkZ z q ≠ 0) :
    shellSegStartVertex pcode M (cornerSeg pcode M x q z hX hZ) =
      cornerSpoke pcode M x q hX := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [shellSegStartVertex, cornerSeg, bxStartLink, bxStart, armStart, projXq0ToBoundaryX0, cornerSpoke]
  · rfl

/-- Identifies `shellSegEndVertex` of `cornerSeg pcode M x q z0 hxq hzq` with the `r = 0` diagonal Z-vertex. -/
lemma shellSegEndVertex_cornerSeg {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (q : Q) (z : M_Z)
    (hX : pcode.checkX x q ≠ 0) (hZ : pcode.checkZ z q ≠ 0) :
    shellSegEndVertex pcode M (cornerSeg pcode M x q z hX hZ) =
      cornerDiagVertex pcode M x z ⟨q, hX, hZ⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [shellSegEndVertex, cornerSeg, shellSegEndLink, shellSegEndV, cornerDiagVertex]
  · rfl

/-- Computes the dual coboundary of `apexRadialCocycle` on a `cornerSeg` azimuthal segment at `r = 0`. -/
lemma checkGen_dual_apexRadialCocycle_cornerSeg {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (x : M_X) (q : Q) (z : M_Z) (hX : pcode.checkX x q ≠ 0) (hZ : pcode.checkZ z q ≠ 0) (b : Fin 3) :
    let h_ex : ∃ q' : Q, pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0 := ⟨q, hX, hZ⟩
    let q_can := canonicalSquareQ pcode x z h_ex
    let h_can := canonicalSquareQ_spec pcode x z h_ex
    checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h)
      (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q z hX hZ, b)))) =
    h (Sum.inl (Sum.inl (cornerSpokeRadial pcode M x q hX, b))) +
    (h (Sum.inl (Sum.inl (cornerSpokeRadial pcode M x q_can h_can.1, b))) +
     h (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q_can z h_can.1 h_can.2, b))))) := by
  intro h_ex q_can h_can
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (Sum.inr (shellSegStartVertex pcode M (cornerSeg pcode M x q z hX hZ), b))]
  · rw [Finset.sum_eq_single (Sum.inr (shellSegEndVertex pcode M (cornerSeg pcode M x q z hX hZ), b))]
    · rw [if_pos rfl, if_pos rfl, one_mul, one_mul,
          shellSegStartVertex_cornerSeg, shellSegEndVertex_cornerSeg]
      dsimp [apexRadialCocycle]
      rw [radialRaySum_zero _ _ _ _ _ rfl, radialRaySum_zero _ _ _ _ _ rfl]
      have h_start : hRadialShell pcode M h (cornerSpoke pcode M x q hX) b =
          h (Sum.inl (Sum.inl (cornerSpokeRadial pcode M x q hX, b))) := by
        dsimp [hRadialShell]
        rw [dif_pos (cornerSpoke_not_isDiagZeroVertex pcode M x q hX)]
        rfl
      have h_diag : IsDiagZeroVertex pcode M (cornerDiagVertex pcode M x z h_ex) :=
        ⟨rfl, z, rfl⟩
      have h_end : hRadialShell pcode M h (cornerDiagVertex pcode M x z h_ex) b =
          h (Sum.inl (Sum.inl (cornerSpokeRadial pcode M x q_can h_can.1, b))) +
          h (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q_can z h_can.1 h_can.2, b)))) := by
        unfold hRadialShell
        rw [dif_neg (not_not.mpr h_diag)]
        exact dif_pos h_ex
      rw [h_start, h_end]
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro mX _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Specializes `checkGen_dual_apexRadialCocycle_cornerSeg` when `q` equals `canonicalSquareQ`. -/
lemma checkGen_dual_apexRadialCocycle_cornerSeg_canonical {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (x : M_X) (z : M_Z) (h_ex : ∃ q' : Q, pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0) (b : Fin 3) :
    let q_can := canonicalSquareQ pcode x z h_ex
    let h_can := canonicalSquareQ_spec pcode x z h_ex
    checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h)
      (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q_can z h_can.1 h_can.2, b)))) =
    h (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q_can z h_can.1 h_can.2, b)))) := by
  intro q_can h_can
  rw [checkGen_dual_apexRadialCocycle_cornerSeg pcode M h x q_can z h_can.1 h_can.2 b]
  have h2 := zmod2_add_self (h (Sum.inl (Sum.inl (cornerSpokeRadial pcode M x q_can h_can.1, b))))
  linear_combination h2

/-! ## 2. Apex Residual Cocycle and Inner Corner Segment Vanishing -/

/-- Adding a dual coboundary `checkGen (dualCode code) c` leaves the dual syndrome unchanged. -/
lemma syndrome_add_checkGen_dual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (h : Q → ZMod 2) (d : M_X → ZMod 2) (mZ : M_Z) :
    syndrome (dualCode code) (h + checkGen (dualCode code) d) mZ = syndrome (dualCode code) h mZ := by
  have h0 := congr_fun (syndrome_checkGen_zero (dualCode code) d) mZ
  change (∑ q, code.checkZ mZ q * (h q + checkGen (dualCode code) d q)) =
    ∑ q, code.checkZ mZ q * h q
  simp_rw [mul_add, Finset.sum_add_distrib]
  change (∑ q, code.checkZ mZ q * h q) +
    syndrome (dualCode code) (checkGen (dualCode code) d) mZ = _
  rw [h0]
  exact add_zero _

/-- Residual 1-cochain `apexResidualCocycle` after subtracting the radial tree coboundary `apexRadialCocycle`. -/
def apexResidualCocycle {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) :
    BDLStepXQ pcode M → ZMod 2 :=
  h + checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h)

/-- Proves that `apexResidualCocycle pcode M h` vanishes on all radial 1-cells `Sum.inl (Sum.inl (rv, b))`. -/
lemma h1_radial_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (rv : RadialVertex pcode M) (b : Fin 3) :
    apexResidualCocycle pcode M h (Sum.inl (Sum.inl (rv, b))) = 0 := by
  change h _ + checkGen _ _ _ = 0
  rw [checkGen_dual_apexRadialCocycle_radial]
  exact zmod2_add_self _

/-- Proves that `apexResidualCocycle pcode M h` vanishes on canonical `r = 0` corner azimuthal segments. -/
lemma h1_cornerSeg_canonical_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (x : M_X) (z : M_Z) (h_ex : ∃ q' : Q, pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0) (b : Fin 3) :
    let q_can := canonicalSquareQ pcode x z h_ex
    let h_can := canonicalSquareQ_spec pcode x z h_ex
    apexResidualCocycle pcode M h
      (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q_can z h_can.1 h_can.2, b)))) = 0 := by
  intro q_can h_can
  change h _ + checkGen _ _ _ = 0
  rw [checkGen_dual_apexRadialCocycle_cornerSeg_canonical]
  exact zmod2_add_self _

/-- Proves that `apexResidualCocycle pcode M h` vanishes on all `r = 0` corner azimuthal segments under the overlap bound `≤ 2`. -/
lemma h1_cornerSeg_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h : BDLStepXQ pcode M → ZMod 2)
    (x : M_X) (q : Q) (z : M_Z) (hX : pcode.checkX x q ≠ 0) (hZ : pcode.checkZ z q ≠ 0) (b : Fin 3)
    (h_syn : ∀ seg : ShellSegment pcode M, seg.val.1.val.1 = x → seg.val.1.val.2.val.2 = z →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg, b))) = 0) :
    apexResidualCocycle pcode M h
      (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q z hX hZ, b)))) = 0 := by
  let h_ex : ∃ q' : Q, pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0 := ⟨q, hX, hZ⟩
  let q_can := canonicalSquareQ pcode x z h_ex
  let h_can := canonicalSquareQ_spec pcode x z h_ex
  by_cases hq : q = q_can
  · have h_seg : cornerSeg pcode M x q z hX hZ = cornerSeg pcode M x q_can z h_can.1 h_can.2 := by
      apply Subtype.ext; apply Prod.ext
      · apply Subtype.ext; exact Prod.ext rfl (Subtype.ext (Prod.ext hq rfl))
      · rfl
    rw [h_seg]
    exact h1_cornerSeg_canonical_eq_zero pcode M h x z h_ex b
  · let seg_can := cornerSeg pcode M x q_can z h_can.1 h_can.2
    have h_syn1 : syndrome (dualCode (bdlCylinderStepX pcode M)) (apexResidualCocycle pcode M h)
        (Sum.inl (Sum.inl (seg_can, b))) = 0 := by
      dsimp [apexResidualCocycle]
      rw [syndrome_add_checkGen_dual]
      exact h_syn seg_can rfl rfl
    dsimp [syndrome, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex] at h_syn1
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
    let S := Finset.univ.filter (fun q' : Q => pcode.checkX x q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0)
    have h_pair_sub : ({q_can, q} : Finset Q) ⊆ S := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hu with rfl | rfl
      · exact h_can
      · exact ⟨hX, hZ⟩
    have h_pair_card : ({q_can, q} : Finset Q).card = 2 := Finset.card_pair (Ne.symm hq)
    have h_S_eq : S = {q_can, q} :=
      (Finset.eq_of_subset_of_card_le h_pair_sub (by rw [h_pair_card]; exact hov x z)).symm
    rw [Finset.sum_eq_single q] at h_syn1
    · rw [dif_pos hX, dif_pos hZ] at h_syn1
      exact h_syn1
    · intro q' _ hne_q
      split_ifs with hX' hZ'
      · have hq'_mem : q' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX', hZ'⟩
        rw [h_S_eq, Finset.mem_insert, Finset.mem_singleton] at hq'_mem
        rcases hq'_mem with rfl | h_eq
        · exact h1_cornerSeg_canonical_eq_zero pcode M h x z h_ex b
        · exact False.elim (hne_q h_eq)
      · rfl
      · rfl
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-! ## 3. Outward Radial Induction for Azimuthal Segments -/

/-- Inductive radial propagation showing `apexResidualCocycle` vanishes on all azimuthal segments of `Y_x` when Z-checks exist. -/
lemma h1_azimuthal_eq_zero_of_z {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) (z : M_Z) (b : Fin 3)
    (h_syn : ∀ seg' : ShellSegment pcode M, seg'.val.1.val.1 = x → seg'.val.1.val.2.val.2 = z →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg', b))) = 0)
    (seg : ShellSegment pcode M) (hx : seg.val.1.val.1 = x) (hz : seg.val.1.val.2.val.2 = z) :
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 0 := by
  suffices h_ind : ∀ (n : ℕ) (seg : ShellSegment pcode M),
      seg.val.1.val.1 = x → seg.val.1.val.2.val.2 = z → seg.val.2.1.val = n →
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 0 from
    h_ind seg.val.2.1.val seg hx hz rfl
  intro n
  induction n with
  | zero =>
    intro seg hx hz hr0
    have hk0 : seg.val.2.2.val = 0 := by
      have := seg.property; omega
    have h_seg_eq : seg = cornerSeg pcode M x seg.val.1.val.2.val.1 seg.val.1.val.2.val.2
        (hx ▸ seg.val.1.property) seg.val.1.val.2.property := by
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext hx rfl
      · exact Prod.ext (Fin.ext hr0) (Fin.ext hk0)
    rw [h_seg_eq]
    exact h1_cornerSeg_eq_zero pcode M hov h x _ _ _ _ b (fun seg' hx' hz' => h_syn seg' hx' (hz'.trans hz))
  | succ m ih =>
    intro seg hx hz hrm
    have hr0 : seg.val.2.1.val ≠ 0 := by omega
    have h_syn1 : syndrome (dualCode (bdlCylinderStepX pcode M)) (apexResidualCocycle pcode M h)
        (Sum.inl (Sum.inl (seg, b))) = 0 := by
      dsimp [apexResidualCocycle]
      rw [syndrome_add_checkGen_dual]
      exact h_syn seg hx hz
    dsimp [syndrome, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex] at h_syn1
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
        apply ih (shellSegPred pcode M seg h_tri) hx hz
        dsimp [shellSegPred, finPred]
        omega
      rw [hX_rect, h1_radial_eq_zero, h1_radial_eq_zero, h_pred_zero,
          zero_add, zero_add, zero_add] at h_syn1
      exact h_syn1

/-- Proves that `apexResidualCocycle pcode M h` vanishes on all azimuthal segments owned by `x` when dual grid syndromes vanish. -/
lemma h1_azimuthal_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) (b : Fin 3)
    (h_syn : ∀ seg' : ShellSegment pcode M, seg'.val.1.val.1 = x →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg', b))) = 0)
    (seg : ShellSegment pcode M) (hx : seg.val.1.val.1 = x) :
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 0 :=
  h1_azimuthal_eq_zero_of_z pcode M hov h x seg.val.1.val.2.val.2 b
    (fun seg' hx' _ => h_syn seg' hx') seg hx rfl

/-- Induction along the `(M + 1)` collar subdivisions of an active link segment `s : ActiveZLink pcode`:
    `apexResidualCocycle` at `(bxStartLink pcode M s k, b)` and `(bxEndLink pcode M s k, b)` equals its value at `(bxStartLink pcode M s 0, b)`. -/
lemma apexResidualCocycle_bxStartLink_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_syn_grid : ∀ (seg : ShellSegment pcode M) (b : Fin 3), seg.val.1.val.1 = x →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg, b))) = 0)
    (h_syn_collar : ∀ (s' : ActiveZLink pcode) (k' : Fin (M + 1)) (b' : Fin 2), s'.val.1 = x →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inr (s', k', b'))) = 0)
    (s : ActiveZLink pcode) (hs : s.val.1 = x) (k : Fin (M + 1)) (b : Fin 2) :
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k, b)))) =
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s 0, b)))) ∧
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, b)))) =
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s 0, b)))) := by
  have h_step : ∀ k' : Fin (M + 1),
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k', b)))) =
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k', b)))) := by
    intro k'
    apply bdlDeltaX1_collar_const_step pcode M (apexResidualCocycle pcode M h) s k' b
    · exact h1_azimuthal_eq_zero pcode M hov h x _ (fun seg hseg => h_syn_grid seg _ hseg)
        (mkOuterShellSegment pcode M s k') hs
    · exact h1_azimuthal_eq_zero pcode M hov h x _ (fun seg hseg => h_syn_grid seg _ hseg)
        (mkOuterShellSegment pcode M s k') hs
    · dsimp [apexResidualCocycle]
      rw [syndrome_add_checkGen_dual]
      exact h_syn_collar s k' b hs
  suffices h_ind : ∀ (n : ℕ) (hn : n < M + 1),
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s ⟨n, hn⟩, b)))) =
        apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s 0, b)))) ∧
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s ⟨n, hn⟩, b)))) =
        apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s 0, b)))) from
    h_ind k.val k.isLt
  intro n
  induction n with
  | zero =>
    intro hn
    have h0 : (⟨0, hn⟩ : Fin (M + 1)) = 0 := rfl
    rw [h0]
    exact ⟨rfl, (h_step 0).symm⟩
  | succ m ih =>
    intro hm
    have hm' : m < M + 1 := Nat.lt_of_succ_lt hm
    have h_link : bxStartLink pcode M s ⟨m + 1, hm⟩ = bxEndLink pcode M s ⟨m, hm'⟩ := by
      apply Subtype.ext; apply Prod.ext
      · rfl
      · dsimp [bxStartLink, bxEndLink, bxStart, bxEnd, armStart, armEnd, projXq0ToBoundaryX0]
        have h_lt : m < M := Nat.lt_of_succ_lt_succ hm
        rw [dif_pos h_lt]
    have h_start : apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s ⟨m + 1, hm⟩, b)))) =
        apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s 0, b)))) := by
      rw [h_link, (ih hm').2]
    exact ⟨h_start, (h_step ⟨m + 1, hm⟩).symm.trans h_start⟩

/-! ## 4. Link-Connectedness and Interior Cleaning of BDLCX1 -/

/-- Link connectedness of X-checks in `code`: any two qubits `q, q'` in the support of `x : M_X`
    are connected by a chain of shared Z-checks `z : M_Z` within the link of `x`. -/
def HasConnectedXLinks {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Prop :=
  ∀ (x : M_X) (q q' : Q), code.checkX x q ≠ 0 → code.checkX x q' ≠ 0 →
    Relation.ReflTransGen
      (fun a b : Q => code.checkX x a ≠ 0 ∧ code.checkX x b ≠ 0 ∧
        ∃ z : M_Z, code.checkZ z a ≠ 0 ∧ code.checkZ z b ≠ 0)
      q q'

/-- Canonical constant value `coneLinkVal pcode M h x b` of `apexResidualCocycle` on the vertical boundary 1-cells of `Y_x` in bridge `b : Fin 2`. -/
noncomputable def coneLinkVal {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) (b : Fin 2) : ZMod 2 :=
  if hex : ∃ q : Q, pcode.checkX x q ≠ 0 then
    apexResidualCocycle pcode M h
      (Sum.inl (Sum.inr (Sum.inr (⟨(x, Sum.inl (Classical.choose hex)), Classical.choose_spec hex⟩, b))))
  else 0

/-- Shows `apexResidualCocycle` is constant along each connected link component of `Y_x` on vertical boundary 1-cells. -/
lemma apexResidualCocycle_vert_eq_coneLinkVal {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_syn_grid : ∀ (seg : ShellSegment pcode M) (b : Fin 3), seg.val.1.val.1 = x →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg, b))) = 0)
    (h_syn_collar : ∀ (s' : ActiveZLink pcode) (k' : Fin (M + 1)) (b' : Fin 2), s'.val.1 = x →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inr (s', k', b'))) = 0)
    (xv : BoundaryX0Link pcode M) (b : Fin 2) (hxv : xv.val.1 = x) :
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (xv, b)))) = coneLinkVal pcode M h x b := by
  have h_arm_z : ∀ (q : Q) (z : M_Z) (hq : pcode.checkX x q ≠ 0) (hz : pcode.checkZ z q ≠ 0),
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (⟨(x, Sum.inr (Sum.inr z)), ⟨q, hq, hz⟩⟩, b)))) =
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (⟨(x, Sum.inl q), hq⟩, b)))) := by
    intro q z hq hz
    let s : ActiveZLink pcode := ⟨(x, ⟨(q, z), hz⟩), hq⟩
    have h_end := (apexResidualCocycle_bxStartLink_eq_zero pcode M hov h x h_syn_grid h_syn_collar s rfl (Fin.last M) b).2
    have h_l1 : bxEndLink pcode M s (Fin.last M) = ⟨(x, Sum.inr (Sum.inr z)), ⟨q, hq, hz⟩⟩ := by
      apply Subtype.ext; apply Prod.ext
      · rfl
      · dsimp [bxEndLink, bxEnd, armEnd, projXq0ToBoundaryX0, Fin.last]
        rw [dif_neg (Nat.lt_irrefl M)]
    have h_l0 : bxStartLink pcode M s 0 = ⟨(x, Sum.inl q), hq⟩ := rfl
    rw [← h_l1, h_end, h_l0]
  have h_rel : ∀ (q1 q2 : Q) (hq1 : pcode.checkX x q1 ≠ 0) (hq2 : pcode.checkX x q2 ≠ 0),
      Relation.ReflTransGen
        (fun a b : Q => pcode.checkX x a ≠ 0 ∧ pcode.checkX x b ≠ 0 ∧
          ∃ z : M_Z, pcode.checkZ z a ≠ 0 ∧ pcode.checkZ z b ≠ 0)
        q1 q2 →
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (⟨(x, Sum.inl q1), hq1⟩, b)))) =
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (⟨(x, Sum.inl q2), hq2⟩, b)))) := by
    intro q1 q2 hq1 hq2 h_path
    induction h_path with
    | refl => rfl
    | tail _ h_step ih =>
      rcases h_step with ⟨ha, hb, z, hza, hzb⟩
      have h1 := h_arm_z _ z ha hza
      have h2 := h_arm_z _ z hb hzb
      have h_sub : (⟨(x, Sum.inr (Sum.inr z)), ⟨_, ha, hza⟩⟩ : BoundaryX0Link pcode M) =
          ⟨(x, Sum.inr (Sum.inr z)), ⟨_, hb, hzb⟩⟩ := Subtype.ext rfl
      rw [h_sub] at h1
      exact (ih ha).trans (h1.symm.trans h2)
  have h_q_eq : ∀ (q : Q) (hq : pcode.checkX x q ≠ 0),
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (⟨(x, Sum.inl q), hq⟩, b)))) =
      coneLinkVal pcode M h x b := by
    intro q hq
    have hex : ∃ q' : Q, pcode.checkX x q' ≠ 0 := ⟨q, hq⟩
    dsimp [coneLinkVal]
    rw [dif_pos hex]
    exact h_rel q (Classical.choose hex) hq (Classical.choose_spec hex)
      (h_conn x q (Classical.choose hex) hq (Classical.choose_spec hex))
  rcases xv with ⟨⟨x', v⟩, hp⟩
  (try dsimp at hxv)
  subst hxv
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · exact h_q_eq q hp
  · let s : ActiveZLink pcode := ⟨(x', eZ), hp⟩
    have h_j := (apexResidualCocycle_bxStartLink_eq_zero pcode M hov h x' h_syn_grid h_syn_collar s rfl
      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ b).1
    have h_lj : bxStartLink pcode M s ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ =
        ⟨(x', Sum.inr (Sum.inl (eZ, j))), hp⟩ := by
      apply Subtype.ext; apply Prod.ext
      · rfl
      · dsimp [bxStartLink, bxStart, armStart, projXq0ToBoundaryX0]
    have h_l0 : bxStartLink pcode M s 0 = ⟨(x', Sum.inl eZ.val.1), hp⟩ := rfl
    rw [← h_lj, h_j, h_l0]
    exact h_q_eq eZ.val.1 hp
  · rcases hp with ⟨q, hq, hz⟩
    rw [h_arm_z q z hq hz]
    exact h_q_eq q hq

/-- Residual 1-cochain `cylinderResidualCocycle` after subtracting both `apexRadialCocycle` and `layer1ConeCochain`. -/
noncomputable def cylinderResidualCocycle {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) :
    BDLStepXQ pcode M → ZMod 2 :=
  apexResidualCocycle pcode M h +
    checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M (coneLinkVal pcode M h))

/-- Owner coarse X-check `qXOwnerX` of a fine 1-cell `qX ∈ BDLCX1 pcode M`. -/
def qXOwnerX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : BDLCX1 pcode M → M_X
  | Sum.inl (rv, _) => rv.val.val.1.val.1
  | Sum.inr (Sum.inl (seg, _)) => seg.val.1.val.1
  | Sum.inr (Sum.inr (xv, _)) => xv.val.1

/-- Proves that `cylinderResidualCocycle pcode M h` vanishes identically on all cylinder 1-cells `Sum.inl qX` owned by `x`. -/
lemma cylinderResidualCocycle_inl_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_syn_grid : ∀ (seg : ShellSegment pcode M) (b : Fin 3), seg.val.1.val.1 = x →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inl (seg, b))) = 0)
    (h_syn_collar : ∀ (s' : ActiveZLink pcode) (k' : Fin (M + 1)) (b' : Fin 2), s'.val.1 = x →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inr (s', k', b'))) = 0)
    (qX : BDLCX1 pcode M) (hqX : qXOwnerX pcode M qX = x) :
    cylinderResidualCocycle pcode M h (Sum.inl qX) = 0 := by
  change apexResidualCocycle pcode M h (Sum.inl qX) +
    checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M (coneLinkVal pcode M h)) (Sum.inl qX) = 0
  rw [checkGen_dual_layer1ConeCochain_inl]
  rcases qX with ⟨rv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, b⟩⟩
  · dsimp
    rw [h1_radial_eq_zero, add_zero]
  · dsimp
    rw [h1_azimuthal_eq_zero pcode M hov h x b (fun seg' hs' => h_syn_grid seg' b hs') seg hqX, add_zero]
  · dsimp
    dsimp [qXOwnerX] at hqX
    rw [apexResidualCocycle_vert_eq_coneLinkVal pcode M hov h_conn h x h_syn_grid h_syn_collar xv b hqX, hqX]
    exact zmod2_add_self _

end WeldedHierarchy
