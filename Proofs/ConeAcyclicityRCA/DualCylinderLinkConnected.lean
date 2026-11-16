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

import Proofs.ConeAcyclicityRCA.CoarseProjCocycleAndSeedLinks

/-!
# Dual Three-Layer Cylinder Link Connectivity and Global Cocycle Coboundary Decomposition

Proves that the dual of the three-layer cylinder weld bdlCylinderStepX preserves connected X-check links across all interior grid, collar, star-arm, and vertical sectors (hasConnectedXLinks_dual_bdlCylinderStepX). Completes the global degree-1 cohomology reduction showing that coarseProjCocycle is a coarse cocycle (syndrome_coarseProjCocycle_global) and differs from the fine cocycle by the coboundary of fullCylinderCocycle (checkGen_fullCylinderCocycle_global).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.6 (`lem:block-sdr`), Proposition 3.7 (`prop:classical-hpl`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Dual Cylinder Step Link-Connectedness Theorem -/

/-- Preservation of `HasConnectedXLinks` for `dualCode (bdlCylinderStepX pcode M)` across a cylinder thickening step. -/
theorem hasConnectedXLinks_dual_bdlCylinderStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h_dual_conn : HasConnectedXLinks (dualCode pcode))
    (hq : HasNoIsolatedQ pcode) :
    HasConnectedXLinks (dualCode (bdlCylinderStepX pcode M)) := by
  intro mZ q q' hq_chk hq'_chk
  rcases mZ with ⟨⟨seg, b⟩ | ⟨s, k, b⟩⟩ | ⟨⟨⟨eZ, k, b⟩ | ⟨eZ, b⟩⟩ | ⟨z0, b⟩⟩
  · -- Case 1: Grid 2-cell `mZ = Sum.inl (Sum.inl (seg, b))`
    by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · by_cases hr0 : seg.val.2.1.val = 0
      · -- Subcase 1a: `r = 0` canonical corner square
        by_cases h_can : seg.val.1.val.2.val.1 = canonicalSquareQ pcode seg.val.1.val.1 seg.val.1.val.2.val.2
            ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩
        · let x := seg.val.1.val.1
          let q0 := seg.val.1.val.2.val.1
          let z := seg.val.1.val.2.val.2
          have hX0 : pcode.checkX x q0 ≠ 0 := seg.val.1.property
          have hZ0 : pcode.checkZ z q0 ≠ 0 := seg.val.1.val.2.property
          let q_hub : BDLStepXQ pcode M := Sum.inl (Sum.inl (cornerSpokeRadial pcode M x q0 hX0, b))
          have h_hub_chk : (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inl (Sum.inl (seg, b))) q_hub ≠ 0 := by
            simp only [dualCode_checkX, bdlCylinderStepX_checkZ]
            rw [bdlDeltaX1_canonical_spoke_eq_one pcode M seg b h_tri hr0 h_can q0 hX0 hZ0]
            decide
          apply reflTransGen_XLinkStep_of_hub (dualCode (bdlCylinderStepX pcode M))
            (Sum.inl (Sum.inl (seg, b))) q_hub _ hq_chk hq'_chk
          intro a ha
          have ha_orig := ha
          rcases a with qX | qQ
          · change bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX ≠ 0 at ha
            dsimp [bdlDeltaX1] at ha
            rw [dif_pos h_tri, dif_pos hr0, if_pos h_can] at ha
            obtain ⟨q1, _, hq1_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
            by_cases hX1 : pcode.checkX x q1 ≠ 0
            · rw [dif_pos hX1] at hq1_ne
              by_cases hZ1 : pcode.checkZ z q1 ≠ 0
              · rw [dif_pos hZ1] at hq1_ne
                by_cases h_sp : qX = Sum.inl (cornerSpokeRadial pcode M x q1 hX1, b)
                · rw [h_sp]
                  exact Relation.ReflTransGen.single ⟨by rw [← h_sp]; exact ha_orig, h_hub_chk, Sum.inl (x, b),
                    by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_apex_eq_one pcode M (cornerSpokeRadial pcode M x q1 hX1) b rfl) (by decide),
                    by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_apex_eq_one pcode M (cornerSpokeRadial pcode M x q0 hX0) b rfl) (by decide)⟩
                · by_cases h_cs : qX = Sum.inr (Sum.inl (cornerSeg pcode M x q1 z hX1 hZ1, b))
                  · rw [h_cs]
                    let q_sp1 : BDLStepXQ pcode M := Sum.inl (Sum.inl (cornerSpokeRadial pcode M x q1 hX1, b))
                    have h_sp1_chk : (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inl (Sum.inl (seg, b))) q_sp1 ≠ 0 := by
                      simp only [dualCode_checkX, bdlCylinderStepX_checkZ]
                      rw [bdlDeltaX1_canonical_spoke_eq_one pcode M seg b h_tri hr0 h_can q1 hX1 hZ1]
                      decide
                    have h_step1 : XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inl (Sum.inl (seg, b)))
                        (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M x q1 z hX1 hZ1, b)))) q_sp1 := by
                      refine ⟨by rw [← h_cs]; exact ha_orig, h_sp1_chk, Sum.inr (cornerSpoke pcode M x q1 hX1, b), ?_, ?_⟩
                      · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
                        rw [← cornerSeg_startVertex_eq_cornerSpoke pcode M x q1 z hX1 hZ1,
                            bdlDeltaX0_seg_start_eq_one pcode M (cornerSeg pcode M x q1 z hX1 hZ1) b]
                        decide
                      · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
                        exact ne_of_eq_of_ne (bdlDeltaX0_radial_self_eq_one pcode M (cornerSpokeRadial pcode M x q1 hX1) b) (by decide)
                    have h_step2 : XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inl (Sum.inl (seg, b)))
                        q_sp1 q_hub :=
                      ⟨h_sp1_chk, h_hub_chk, Sum.inl (x, b),
                        by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_apex_eq_one pcode M (cornerSpokeRadial pcode M x q1 hX1) b rfl) (by decide),
                        by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_apex_eq_one pcode M (cornerSpokeRadial pcode M x q0 hX0) b rfl) (by decide)⟩
                    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h_step1) h_step2
                  · rw [if_neg h_sp, if_neg h_cs] at hq1_ne; exact False.elim (hq1_ne rfl)
              · rw [dif_neg hZ1] at hq1_ne; exact False.elim (hq1_ne rfl)
            · rw [dif_neg hX1] at hq1_ne; exact False.elim (hq1_ne rfl)
          · exact False.elim (ha rfl)
        · exfalso
          rcases q with qX | qQ
          · change bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX ≠ 0 at hq_chk
            dsimp [bdlDeltaX1] at hq_chk
            rw [dif_pos h_tri, dif_pos hr0, if_neg h_can] at hq_chk
            exact hq_chk rfl
          · exact hq_chk rfl
      · -- Subcase 1b: `r > 0` triangle (`seg.val.2.2 = seg.val.2.1`)
        let q_hub : BDLStepXQ pcode M := Sum.inl (Sum.inr (Sum.inl (seg, b)))
        have h_hub_chk : (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inl (Sum.inl (seg, b))) q_hub ≠ 0 := by
          simp only [dualCode_checkX, bdlCylinderStepX_checkZ]
          rw [bdlDeltaX1_pos_seg_eq_one pcode M seg b hr0]; decide
        apply reflTransGen_XLinkStep_of_hub (dualCode (bdlCylinderStepX pcode M))
          (Sum.inl (Sum.inl (seg, b))) q_hub _ hq_chk hq'_chk
        intro a ha
        have ha_orig := ha
        rcases a with qX | qQ
        · change bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX ≠ 0 at ha
          dsimp [bdlDeltaX1] at ha
          rw [dif_pos h_tri, dif_neg hr0] at ha
          by_cases h1 : qX = Sum.inl (shellSegStartRadial pcode M seg, b)
          · rw [h1]
            exact Relation.ReflTransGen.single ⟨by rw [← h1]; exact ha_orig, h_hub_chk,
              Sum.inr (shellSegStartVertex pcode M seg, b),
              by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_self_eq_one pcode M (shellSegStartRadial pcode M seg) b) (by decide),
              by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; rw [bdlDeltaX0_seg_start_eq_one pcode M seg b]; decide⟩
          · by_cases h2 : qX = Sum.inl (shellSegEndRadial pcode M seg hr0, b)
            · rw [h2]
              exact Relation.ReflTransGen.single ⟨by rw [← h2]; exact ha_orig, h_hub_chk,
                Sum.inr (shellSegEndVertex pcode M seg, b),
                by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_self_eq_one pcode M (shellSegEndRadial pcode M seg hr0) b) (by decide),
                by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; rw [bdlDeltaX0_seg_end_eq_one pcode M seg b]; decide⟩
            · by_cases h3 : qX = Sum.inr (Sum.inl (seg, b))
              · rw [h3]
              · rw [if_neg h1, if_neg h2, if_neg h3] at ha; exact False.elim (ha rfl)
        · exact False.elim (ha rfl)
    · -- Subcase 1c: `r > 0` rectangle (`seg.val.2.2 < seg.val.2.1`)
      have hr0 : seg.val.2.1.val ≠ 0 := by have := seg.property; omega
      let q_hub : BDLStepXQ pcode M := Sum.inl (Sum.inr (Sum.inl (seg, b)))
      have h_hub_chk : (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inl (Sum.inl (seg, b))) q_hub ≠ 0 := by
        simp only [dualCode_checkX, bdlCylinderStepX_checkZ]
        rw [bdlDeltaX1_pos_seg_eq_one pcode M seg b hr0]; decide
      let q_start : BDLStepXQ pcode M := Sum.inl (Sum.inl (shellSegStartRadial pcode M seg, b))
      have h_start_chk : (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inl (Sum.inl (seg, b))) q_start ≠ 0 := by
        simp only [dualCode_checkX, bdlCylinderStepX_checkZ]
        rw [bdlDeltaX1_pos_startRadial_eq_one pcode M seg b hr0]; decide
      have h_start_to_hub : XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inl (Sum.inl (seg, b)))
          q_start q_hub :=
        ⟨h_start_chk, h_hub_chk, Sum.inr (shellSegStartVertex pcode M seg, b),
          by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_self_eq_one pcode M (shellSegStartRadial pcode M seg) b) (by decide),
          by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; rw [bdlDeltaX0_seg_start_eq_one pcode M seg b]; decide⟩
      apply reflTransGen_XLinkStep_of_hub (dualCode (bdlCylinderStepX pcode M))
        (Sum.inl (Sum.inl (seg, b))) q_hub _ hq_chk hq'_chk
      intro a ha
      have ha_orig := ha
      rcases a with qX | qQ
      · change bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX ≠ 0 at ha
        dsimp [bdlDeltaX1] at ha
        rw [dif_neg h_tri] at ha
        by_cases h1 : qX = Sum.inl (shellSegStartRadial pcode M seg, b)
        · rw [h1]; exact Relation.ReflTransGen.single h_start_to_hub
        · by_cases h2 : qX = Sum.inl (shellSegEndRadial pcode M seg hr0, b)
          · rw [h2]
            exact Relation.ReflTransGen.single ⟨by rw [← h2]; exact ha_orig, h_hub_chk,
              Sum.inr (shellSegEndVertex pcode M seg, b),
              by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_self_eq_one pcode M (shellSegEndRadial pcode M seg hr0) b) (by decide),
              by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; rw [bdlDeltaX0_seg_end_eq_one pcode M seg b]; decide⟩
          · by_cases h3 : qX = Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b))
            · rw [h3]
              have h_pred_to_start : XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inl (Sum.inl (seg, b)))
                  (Sum.inl (Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)))) q_start := by
                refine ⟨by rw [← h3]; exact ha_orig, h_start_chk,
                  Sum.inr (shellSegStartVertex pcode M (shellSegPred pcode M seg h_tri), b), ?_, ?_⟩
                · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
                  rw [bdlDeltaX0_seg_start_eq_one pcode M (shellSegPred pcode M seg h_tri) b]; decide
                · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
                  rw [← radialParent_start_eq_start_pred pcode M seg h_tri]
                  exact ne_of_eq_of_ne (bdlDeltaX0_radial_parent_eq_one pcode M (shellSegStartRadial pcode M seg) b hr0) (by decide)
              exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h_pred_to_start) h_start_to_hub
            · by_cases h4 : qX = Sum.inr (Sum.inl (seg, b))
              · rw [h4]
              · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4] at ha; exact False.elim (ha rfl)
      · exact False.elim (ha rfl)
  · -- Case 2: Collar 2-cell `mZ = Sum.inl (Sum.inr (s, k, b))`
    let seg_out := mkOuterShellSegment pcode M s k
    let xv_start := bxStartLink pcode M s k
    let xv_end := bxEndLink pcode M s k
    let b0 : Fin 3 := 0
    let b1 : Fin 3 := b.succ
    let q_hub : BDLStepXQ pcode M := Sum.inl (Sum.inr (Sum.inr (xv_start, b)))
    let q_seg0 : BDLStepXQ pcode M := Sum.inl (Sum.inr (Sum.inl (seg_out, b0)))
    have h_xv_ne : xv_start ≠ xv_end := by
      intro hc
      have h_sv : mkOuterShellVertex pcode M xv_start = mkOuterShellVertex pcode M xv_end := by rw [hc]
      rw [← shellSegStartVertex_outer pcode M s k, ← shellSegEndVertex_outer pcode M s k] at h_sv
      exact shellSegStartVertex_ne_end pcode M seg_out h_sv
    have h_hub_chk : (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inl (Sum.inr (s, k, b))) q_hub ≠ 0 := by
      change bdlDeltaX1 pcode M (Sum.inr (s, k, b)) (Sum.inr (Sum.inr (xv_start, b))) ≠ 0
      dsimp [bdlDeltaX1]
      have h_ne_end : (Sum.inr (Sum.inr (xv_start, b)) : BDLCX1 pcode M) ≠ Sum.inr (Sum.inr (xv_end, b)) := by
        intro hc; injection hc with hc1; injection hc1 with hc2; injection hc2 with hc3 _; exact h_xv_ne hc3
      rw [if_pos rfl, if_neg h_ne_end]; decide
    have h_seg0_chk : (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inl (Sum.inr (s, k, b))) q_seg0 ≠ 0 := by
      change bdlDeltaX1 pcode M (Sum.inr (s, k, b)) (Sum.inr (Sum.inl (seg_out, b0))) ≠ 0
      dsimp [bdlDeltaX1, seg_out, b0]
      fin_cases b <;> simp
    have h_seg0_to_hub : XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inl (Sum.inr (s, k, b)))
        q_seg0 q_hub := by
      refine ⟨h_seg0_chk, h_hub_chk, Sum.inr (mkOuterShellVertex pcode M xv_start, b0), ?_, ?_⟩
      · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
        rw [← shellSegStartVertex_outer pcode M s k, bdlDeltaX0_seg_start_eq_one pcode M seg_out b0]; decide
      · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
        rw [bdlDeltaX0_vert_eq_one pcode M xv_start b]; decide
    apply reflTransGen_XLinkStep_of_hub (dualCode (bdlCylinderStepX pcode M))
      (Sum.inl (Sum.inr (s, k, b))) q_hub _ hq_chk hq'_chk
    intro a ha
    have ha_orig := ha
    rcases a with qX | qQ
    · change bdlDeltaX1 pcode M (Sum.inr (s, k, b)) qX ≠ 0 at ha
      dsimp [bdlDeltaX1] at ha
      by_cases h1 : qX = Sum.inr (Sum.inl (seg_out, b0))
      · rw [h1]; exact Relation.ReflTransGen.single h_seg0_to_hub
      · by_cases h2 : qX = Sum.inr (Sum.inl (seg_out, b1))
        · rw [h2]
          exact Relation.ReflTransGen.single ⟨by rw [← h2]; exact ha_orig, h_hub_chk,
            Sum.inr (mkOuterShellVertex pcode M xv_start, b1),
            by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; rw [← shellSegStartVertex_outer pcode M s k, bdlDeltaX0_seg_start_eq_one pcode M seg_out b1]; decide,
            by simp only [dualCode_checkZ, bdlCylinderStepX_checkX]; rw [bdlDeltaX0_vert_succ_eq_one pcode M xv_start b]; decide⟩
        · by_cases h3 : qX = Sum.inr (Sum.inr (xv_start, b))
          · rw [h3]
          · by_cases h4 : qX = Sum.inr (Sum.inr (xv_end, b))
            · rw [h4]
              have h_end_to_seg0 : XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inl (Sum.inr (s, k, b)))
                  (Sum.inl (Sum.inr (Sum.inr (xv_end, b)))) q_seg0 := by
                refine ⟨by rw [← h4]; exact ha_orig, h_seg0_chk, Sum.inr (mkOuterShellVertex pcode M xv_end, b0), ?_, ?_⟩
                · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
                  rw [bdlDeltaX0_vert_eq_one pcode M xv_end b]; decide
                · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
                  rw [← shellSegEndVertex_outer pcode M s k, bdlDeltaX0_seg_end_eq_one pcode M seg_out b0]; decide
              exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h_end_to_seg0) h_seg0_to_hub
            · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4] at ha; exact False.elim (ha rfl)
    · exact False.elim (ha rfl)
  · -- Case 3: Subdivided arm 2-cell `mZ = Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))`
    let q_hub : BDLStepXQ pcode M := Sum.inr (armStart pcode M eZ k, b)
    have h_hub_chk : (dualCode (bdlCylinderStepX pcode M)).checkX
        (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) q_hub ≠ 0 := by
      change bdlDeltaQ1 pcode M (Sum.inl (eZ, k, b)) (armStart pcode M eZ k, b) ≠ 0
      dsimp [bdlDeltaQ1]
      have h_ne : ((armStart pcode M eZ k, b) : BDLCQ1 pcode M) ≠ (armEnd pcode M eZ k, b) := by
        intro hc; injection hc with hc1 _; exact armStart_ne_armEnd pcode M eZ k hc1
      rw [if_pos rfl, if_neg h_ne]; decide
    have h_seg_to_hub : ∀ (x : M_X) (hx : pcode.checkX x eZ.val.1 ≠ 0),
        XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))
          (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M ⟨(x, eZ), hx⟩ k, b)))) q_hub := by
      intro x hx
      let s_x : ActiveZLink pcode := ⟨(x, eZ), hx⟩
      let seg_x := mkOuterShellSegment pcode M s_x k
      have h_seg_chk : (dualCode (bdlCylinderStepX pcode M)).checkX
          (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) (Sum.inl (Sum.inr (Sum.inl (seg_x, b)))) ≠ 0 := by
        change bdlGXQ1 pcode M (Sum.inl (eZ, k, b)) (Sum.inr (Sum.inl (seg_x, b))) ≠ 0
        dsimp [bdlGXQ1, seg_x, mkOuterShellSegment]
        rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]; exact hx
      refine ⟨h_seg_chk, h_hub_chk, Sum.inr (mkOuterShellVertex pcode M (bxStartLink pcode M s_x k), b), ?_, ?_⟩
      · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
        rw [← shellSegStartVertex_outer pcode M s_x k, bdlDeltaX0_seg_start_eq_one pcode M seg_x b]; decide
      · change bdlGXQ0 pcode M (Sum.inr (mkOuterShellVertex pcode M (bxStartLink pcode M s_x k), b))
          (armStart pcode M eZ k, b) ≠ 0
        dsimp [bdlGXQ0, mkOuterShellVertex, bxStartLink, bxStart]
        rw [if_pos ⟨rfl, rfl, rfl⟩, xq0OwnerQ_armStart]
        exact hx
    apply reflTransGen_XLinkStep_of_hub (dualCode (bdlCylinderStepX pcode M))
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) q_hub _ hq_chk hq'_chk
    intro a ha
    have ha_orig := ha
    rcases a with qX | qQ
    · change bdlGXQ1 pcode M (Sum.inl (eZ, k, b)) qX ≠ 0 at ha
      rcases qX with _ | ⟨⟨seg, bX⟩ | _⟩
      · exact False.elim (ha rfl)
      · dsimp [bdlGXQ1] at ha
        split_ifs at ha with h_cond
        · rcases h_cond with ⟨hr_eq, heZ_eq, hk_eq, hb_eq⟩
          have hx : pcode.checkX seg.val.1.val.1 eZ.val.1 ≠ 0 := ha
          have h_seg_eq : seg = mkOuterShellSegment pcode M ⟨(seg.val.1.val.1, eZ), hx⟩ k := by
            apply Subtype.ext; apply Prod.ext
            · apply Subtype.ext; apply Prod.ext; · rfl
              · exact heZ_eq
            · exact Prod.ext hr_eq hk_eq
          subst hb_eq
          rw [h_seg_eq]
          exact Relation.ReflTransGen.single (h_seg_to_hub seg.val.1.val.1 hx)
        · exact False.elim (ha rfl)
      · exact False.elim (ha rfl)
    · change bdlDeltaQ1 pcode M (Sum.inl (eZ, k, b)) qQ ≠ 0 at ha
      dsimp [bdlDeltaQ1] at ha
      by_cases h1 : qQ = (armStart pcode M eZ k, b)
      · rw [h1]
      · by_cases h2 : qQ = (armEnd pcode M eZ k, b)
        · rw [h2]
          obtain ⟨x0, hx0⟩ := hq.2 eZ.val.1 ⟨eZ.val.2, eZ.property⟩
          let s0 : ActiveZLink pcode := ⟨(x0, eZ), hx0⟩
          let seg0 := mkOuterShellSegment pcode M s0 k
          have h_seg0 := h_seg_to_hub x0 hx0
          have h_end_to_seg0 : XLinkStep (dualCode (bdlCylinderStepX pcode M))
              (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))
              (Sum.inr (armEnd pcode M eZ k, b)) (Sum.inl (Sum.inr (Sum.inl (seg0, b)))) := by
            refine ⟨by rw [← h2]; exact ha_orig, h_seg0.1,
              Sum.inr (mkOuterShellVertex pcode M (bxEndLink pcode M s0 k), b), ?_, ?_⟩
            · change bdlGXQ0 pcode M (Sum.inr (mkOuterShellVertex pcode M (bxEndLink pcode M s0 k), b))
                (armEnd pcode M eZ k, b) ≠ 0
              dsimp [bdlGXQ0, mkOuterShellVertex, bxEndLink, bxEnd]
              rw [if_pos ⟨rfl, rfl, rfl⟩, xq0OwnerQ_armEnd]
              exact hx0
            · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
              rw [← shellSegEndVertex_outer pcode M s0 k, bdlDeltaX0_seg_end_eq_one pcode M seg0 b]; decide
          exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h_end_to_seg0) h_seg0
        · rw [if_neg h1, if_neg h2] at ha; exact False.elim (ha rfl)
  · -- Case 4: Terminal vertical 2-cell `mZ = Sum.inr (Sum.inl (Sum.inr (eZ, b)))`
    let b0 : Fin 3 := 0
    let b1 : Fin 3 := b.succ
    let q_hub : BDLStepXQ pcode M := Sum.inr (Sum.inr (Sum.inr eZ), b0)
    have h_hub_chk : (dualCode (bdlCylinderStepX pcode M)).checkX
        (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) q_hub ≠ 0 := by
      change bdlDeltaQ1 pcode M (Sum.inr (eZ, b)) (Sum.inr (Sum.inr eZ), b0) ≠ 0
      dsimp [bdlDeltaQ1, b0]; fin_cases b <;> simp
    have h_vert_to_hub : ∀ (xv : BoundaryX0Link pcode M)
        (hv : xv.val.2 = Sum.inr (Sum.inr eZ.val.2)) (hx : pcode.checkX xv.val.1 eZ.val.1 ≠ 0),
        XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inr (Sum.inl (Sum.inr (eZ, b))))
          (Sum.inl (Sum.inr (Sum.inr (xv, b)))) q_hub := by
      intro xv hv hx
      have h_xv_chk : (dualCode (bdlCylinderStepX pcode M)).checkX
          (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) (Sum.inl (Sum.inr (Sum.inr (xv, b)))) ≠ 0 := by
        change bdlGXQ1 pcode M (Sum.inr (eZ, b)) (Sum.inr (Sum.inr (xv, b))) ≠ 0
        dsimp [bdlGXQ1]; rw [if_pos ⟨hv, rfl⟩]; exact hx
      refine ⟨h_xv_chk, h_hub_chk, Sum.inr (mkOuterShellVertex pcode M xv, b0), ?_, ?_⟩
      · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
        rw [bdlDeltaX0_vert_eq_one pcode M xv b]; decide
      · change bdlGXQ0 pcode M (Sum.inr (mkOuterShellVertex pcode M xv, b0)) (Sum.inr (Sum.inr eZ), b0) ≠ 0
        dsimp [bdlGXQ0, mkOuterShellVertex]
        rw [if_pos ⟨rfl, hv, rfl⟩]; exact hx
    apply reflTransGen_XLinkStep_of_hub (dualCode (bdlCylinderStepX pcode M))
      (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) q_hub _ hq_chk hq'_chk
    intro a ha
    have ha_orig := ha
    rcases a with qX | qQ
    · change bdlGXQ1 pcode M (Sum.inr (eZ, b)) qX ≠ 0 at ha
      rcases qX with _ | ⟨_ | ⟨xv, bX⟩⟩
      · exact False.elim (ha rfl)
      · exact False.elim (ha rfl)
      · dsimp [bdlGXQ1] at ha
        split_ifs at ha with hv
        · rcases hv with ⟨hv, rfl⟩
          exact Relation.ReflTransGen.single (h_vert_to_hub xv hv ha)
        · exact False.elim (ha rfl)
    · change bdlDeltaQ1 pcode M (Sum.inr (eZ, b)) qQ ≠ 0 at ha
      dsimp [bdlDeltaQ1] at ha
      by_cases h1 : qQ = (Sum.inr (Sum.inr eZ), b0)
      · rw [h1]
      · by_cases h2 : qQ = (Sum.inr (Sum.inr eZ), b1)
        · rw [h2]
          obtain ⟨x0, hx0⟩ := hq.2 eZ.val.1 ⟨eZ.val.2, eZ.property⟩
          let xv0 : BoundaryX0Link pcode M := ⟨(x0, Sum.inr (Sum.inr eZ.val.2)), ⟨eZ.val.1, hx0, eZ.property⟩⟩
          have h_v0 := h_vert_to_hub xv0 rfl hx0
          have h_1_to_v0 : XLinkStep (dualCode (bdlCylinderStepX pcode M)) (Sum.inr (Sum.inl (Sum.inr (eZ, b))))
              (Sum.inr (Sum.inr (Sum.inr eZ), b1)) (Sum.inl (Sum.inr (Sum.inr (xv0, b)))) := by
            refine ⟨by rw [← h2]; exact ha_orig, h_v0.1, Sum.inr (mkOuterShellVertex pcode M xv0, b1), ?_, ?_⟩
            · change bdlGXQ0 pcode M (Sum.inr (mkOuterShellVertex pcode M xv0, b1)) (Sum.inr (Sum.inr eZ), b1) ≠ 0
              dsimp [bdlGXQ0, mkOuterShellVertex, xv0]
              rw [if_pos ⟨rfl, rfl, rfl⟩]; exact hx0
            · simp only [dualCode_checkZ, bdlCylinderStepX_checkX]
              rw [bdlDeltaX0_vert_succ_eq_one pcode M xv0 b]; decide
          exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h_1_to_v0) h_v0
        · rw [if_neg h1, if_neg h2] at ha; exact False.elim (ha rfl)
  · -- Case 5: Coarse Z-check `mZ = Sum.inr (Sum.inr (z0, b))`
    have h_extract : ∀ a : BDLStepXQ pcode M,
        (dualCode (bdlCylinderStepX pcode M)).checkX (Sum.inr (Sum.inr (z0, b))) a ≠ 0 →
        ∃ (qa : Q) (hza : pcode.checkZ z0 qa ≠ 0),
          a = Sum.inr (Sum.inr (Sum.inr ⟨(qa, z0), hza⟩), b) := by
      intro a ha
      rcases a with _ | ⟨v0, b'⟩
      · exact False.elim (ha rfl)
      · change bdlGQZ1 pcode M (z0, b) (v0, b') ≠ 0 at ha
        rcases v0 with _ | ⟨_ | eZ⟩
        · exact False.elim (ha rfl)
        · exact False.elim (ha rfl)
        · dsimp [bdlGQZ1] at ha
          split_ifs at ha with h_cond
          · rcases h_cond with ⟨hz_eq, hb_eq⟩
            refine ⟨eZ.val.1, hz_eq ▸ eZ.property, ?_⟩
            congr 1
            apply Prod.ext
            · apply congr_arg Sum.inr
              apply congr_arg Sum.inr
              exact Subtype.ext (Prod.ext rfl hz_eq)
            · exact hb_eq
          · exact False.elim (ha rfl)
    obtain ⟨q1, hzq1, rfl⟩ := h_extract q hq_chk
    obtain ⟨q2, hzq2, rfl⟩ := h_extract q' hq'_chk
    have h_path := h_dual_conn z0 q1 q2 hzq1 hzq2
    clear hq_chk hq'_chk
    induction h_path with
    | refl => rfl
    | tail _ h_step ih =>
      rcases h_step with ⟨hza, hzc, x, hxa, hxc⟩
      have h_ih := ih hza
      let a_fine : BDLStepXQ pcode M := Sum.inr (Sum.inr (Sum.inr ⟨(_, z0), hza⟩), b)
      let c_fine : BDLStepXQ pcode M := Sum.inr (Sum.inr (Sum.inr ⟨(_, z0), hzc⟩), b)
      let xv : BoundaryX0Link pcode M := ⟨(x, Sum.inr (Sum.inr z0)), ⟨_, hxa, hza⟩⟩
      have h_fine_step : XLinkStep (dualCode (bdlCylinderStepX pcode M))
          (Sum.inr (Sum.inr (z0, b))) a_fine c_fine := by
        refine ⟨?_, ?_, Sum.inr (mkOuterShellVertex pcode M xv, b), ?_, ?_⟩
        · simp only [dualCode_checkX, bdlCylinderStepX_checkZ]
          dsimp [bdlStepXCheckZ, bdlGQZ1, bdlDeltaQ1, a_fine]; simp
        · simp only [dualCode_checkX, bdlCylinderStepX_checkZ]
          dsimp [bdlStepXCheckZ, bdlGQZ1, bdlDeltaQ1, c_fine]; simp
        · change bdlGXQ0 pcode M (Sum.inr (mkOuterShellVertex pcode M xv, b)) _ ≠ 0
          dsimp [bdlGXQ0, mkOuterShellVertex, xv]
          rw [if_pos ⟨rfl, rfl, rfl⟩]; exact hxa
        · change bdlGXQ0 pcode M (Sum.inr (mkOuterShellVertex pcode M xv, b)) _ ≠ 0
          dsimp [bdlGXQ0, mkOuterShellVertex, xv]
          rw [if_pos ⟨rfl, rfl, rfl⟩]; exact hxc
      exact Relation.ReflTransGen.tail h_ih h_fine_step

/-! ## 2. Azimuthal Segment Hub Connectivity at Shell Vertices -/

/-- Connects any azimuthal segment incident to shell vertex `(sv, b)` to the canonical hub segment `(svIncidentSeg sv, b)` in the X-link. -/
lemma bdlCylinderStepX_azimuthal_incident_connected {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (sv : ShellVertex pcode M) (b : Fin 3)
    (seg : ShellSegment pcode M)
    (h_inc : sv = shellSegStartVertex pcode M seg ∨ sv = shellSegEndVertex pcode M seg) :
    Relation.ReflTransGen (XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b)))
      (Sum.inl (Sum.inr (Sum.inl (seg, b))))
      (Sum.inl (Sum.inr (Sum.inl (svIncidentSeg pcode M hq sv, b)))) := by
  let seg0 := svIncidentSeg pcode M hq sv
  have h_inc0 := (svIncidentSeg_start_or_end pcode M hq sv).2
  have h_seg_chk : ∀ (s : ShellSegment pcode M),
      (sv = shellSegStartVertex pcode M s ∨ sv = shellSegEndVertex pcode M s) →
      (bdlCylinderStepX pcode M).checkX (Sum.inr (sv, b)) (Sum.inl (Sum.inr (Sum.inl (s, b)))) ≠ 0 := by
    intro s hs
    simp only [bdlCylinderStepX_checkX]
    rcases hs with rfl | rfl
    · rw [bdlDeltaX0_seg_start_eq_one]; decide
    · rw [bdlDeltaX0_seg_end_eq_one]; decide
  have hr_eq : seg.val.2.1 = sv.val.2 := by
    rcases h_inc with h_s | h_e
    · exact (congr_arg (fun w : ShellVertex pcode M => w.val.2) h_s).symm
    · exact (congr_arg (fun w : ShellVertex pcode M => w.val.2) h_e).symm
  have hr0_eq : seg0.val.2.1 = sv.val.2 := (svIncidentSeg_start_or_end pcode M hq sv).1
  by_cases hr_nz : sv.val.2.val ≠ 0
  · let rv : RadialVertex pcode M := ⟨sv, fun h => hr_nz h.1⟩
    let q_rad : BDLStepXQ pcode M := Sum.inl (Sum.inl (rv, b))
    have h_rad_chk : (bdlCylinderStepX pcode M).checkX (Sum.inr (sv, b)) q_rad ≠ 0 := by
      simp only [bdlCylinderStepX_checkX]
      change bdlStepXCheckX pcode M (Sum.inr (rv.val, b)) q_rad ≠ 0
      rw [bdlDeltaX0_radial_self_eq_one]; decide
    have h_to_rad : ∀ (s : ShellSegment pcode M) (hs : sv = shellSegStartVertex pcode M s ∨ sv = shellSegEndVertex pcode M s),
        XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
          (Sum.inl (Sum.inr (Sum.inl (s, b)))) q_rad := by
      intro s hs
      have hrs_nz : s.val.2.1.val ≠ 0 := by
        rcases hs with h_s | h_e
        · have h_r := congr_arg (fun w : ShellVertex pcode M => w.val.2.val) h_s
          dsimp [shellSegStartVertex] at h_r
          omega
        · have h_r := congr_arg (fun w : ShellVertex pcode M => w.val.2.val) h_e
          dsimp [shellSegEndVertex] at h_r
          omega
      refine ⟨h_seg_chk s hs, h_rad_chk, Sum.inl (Sum.inl (s, b)), ?_, ?_⟩
      · simp only [bdlCylinderStepX_checkZ]
        rw [bdlDeltaX1_pos_seg_eq_one pcode M s b hrs_nz]; decide
      · simp only [bdlCylinderStepX_checkZ]
        dsimp [q_rad]
        rcases hs with h_s | h_e
        · have h_rv : rv = shellSegStartRadial pcode M s := Subtype.ext h_s
          rw [h_rv, bdlDeltaX1_pos_startRadial_eq_one pcode M s b hrs_nz]; decide
        · have h_rv : rv = shellSegEndRadial pcode M s hrs_nz := Subtype.ext h_e
          rw [h_rv, bdlDeltaX1_pos_endRadial_eq_one pcode M s b hrs_nz]; decide
    exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.single (h_to_rad seg h_inc))
      (xLinkStep_symm (bdlCylinderStepX pcode M) (Sum.inr (sv, b)) (h_to_rad seg0 h_inc0))
  · push_neg at hr_nz
    have hr_seg0 : seg.val.2.1.val = 0 := by rw [hr_eq]; exact hr_nz
    have hk_seg0 : seg.val.2.2.val = 0 := by have := seg.property; omega
    have h_tri_seg : seg.val.2.2.val = seg.val.2.1.val := by omega
    have hr_seg0_0 : seg0.val.2.1.val = 0 := by rw [hr0_eq]; exact hr_nz
    have hk_seg0_0 : seg0.val.2.2.val = 0 := by have := seg0.property; omega
    have h_tri_seg0 : seg0.val.2.2.val = seg0.val.2.1.val := by omega
    rcases sv with ⟨⟨⟨⟨x, v⟩, hp⟩, r⟩, h_in⟩
    (try dsimp at hr_nz)
    rcases v with q0 | ⟨⟨eZ, j⟩ | z0⟩
    · let rv : RadialVertex pcode M := cornerSpokeRadial pcode M x q0 hp
      have h_sv_eq : (⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩ : ShellVertex pcode M) = cornerSpoke pcode M x q0 hp := by
        apply Subtype.ext; apply Prod.ext; · rfl
        · exact Fin.ext hr_nz
      let q_rad : BDLStepXQ pcode M := Sum.inl (Sum.inl (rv, b))
      have h_rad_chk : (bdlCylinderStepX pcode M).checkX
          (Sum.inr (⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩, b)) q_rad ≠ 0 := by
        rw [h_sv_eq]
        simp only [bdlCylinderStepX_checkX]
        change bdlStepXCheckX pcode M (Sum.inr (rv.val, b)) q_rad ≠ 0
        rw [bdlDeltaX0_radial_self_eq_one]; decide
      have h_to_rad : ∀ (s : ShellSegment pcode M)
          (hs : (⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩ : ShellVertex pcode M) = shellSegStartVertex pcode M s ∨
                (⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩ : ShellVertex pcode M) = shellSegEndVertex pcode M s),
          XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩, b))
            (Sum.inl (Sum.inr (Sum.inl (s, b)))) q_rad := by
        intro s hs
        have hrs0 : s.val.2.1.val = 0 := by
          rcases hs with h_s | h_e
          · exact (congr_arg (fun w : ShellVertex pcode M => w.val.2.val) h_s).symm.trans hr_nz
          · exact (congr_arg (fun w : ShellVertex pcode M => w.val.2.val) h_e).symm.trans hr_nz
        have hks0 : s.val.2.2.val = 0 := by have := s.property; omega
        have h_s_start : (⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩ : ShellVertex pcode M) = shellSegStartVertex pcode M s := by
          rcases hs with h_s | h_e
          · exact h_s
          · exfalso
            have hv := congr_arg (fun w : ShellVertex pcode M => w.val.1.val.2) h_e
            dsimp [shellSegEndVertex, shellSegEndLink, shellSegEndV] at hv
            have h_not_lt : ¬ s.val.2.2.val < s.val.2.1.val := by omega
            rw [dif_neg h_not_lt] at hv
            exact Sum.inl_ne_inr hv
        have hx_s : s.val.1.val.1 = x :=
          (congr_arg (fun w : ShellVertex pcode M => w.val.1.val.1) h_s_start).symm
        have hq_s : s.val.1.val.2.val.1 = q0 := by
          have hv := congr_arg (fun w : ShellVertex pcode M => w.val.1.val.2) h_s_start
          dsimp [shellSegStartVertex, bxStartLink, bxStart, armStart, projXq0ToBoundaryX0] at hv
          rw [dif_pos hks0] at hv
          injection hv with hq_eq
          exact hq_eq.symm
        let zs := s.val.1.val.2.val.2
        have hZs : pcode.checkZ zs q0 ≠ 0 := hq_s ▸ s.val.1.val.2.property
        have h_ex : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ zs q ≠ 0 := ⟨q0, hp, hZs⟩
        let q_can := canonicalSquareQ pcode x zs h_ex
        have h_can_spec := canonicalSquareQ_spec pcode x zs h_ex
        let s_can := cornerSeg pcode M x q_can zs h_can_spec.1 h_can_spec.2
        refine ⟨h_seg_chk s hs, h_rad_chk, Sum.inl (Sum.inl (s_can, b)), ?_, ?_⟩
        · have hs_eq : s = cornerSeg pcode M x q0 zs hp hZs := by
            apply Subtype.ext; apply Prod.ext
            · apply Subtype.ext; apply Prod.ext
              · exact hx_s
              · apply Subtype.ext; apply Prod.ext; exact hq_s; rfl
            · exact Prod.ext (Fin.ext hrs0) (Fin.ext hks0)
          rw [hs_eq]
          simp only [bdlCylinderStepX_checkZ]
          exact ne_of_eq_of_ne (bdlDeltaX1_canonical_seg_eq_one pcode M s_can b rfl rfl rfl q0 hp hZs) (by decide)
        · simp only [bdlCylinderStepX_checkZ]
          exact ne_of_eq_of_ne (bdlDeltaX1_canonical_spoke_eq_one pcode M s_can b rfl rfl rfl q0 hp hZs) (by decide)
      exact Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single (h_to_rad seg h_inc))
        (xLinkStep_symm (bdlCylinderStepX pcode M) _ (h_to_rad seg0 h_inc0))
    · dsimp [InShellR] at h_in; omega
    · let q_can := canonicalSquareQ pcode x z0 hp
      have h_can_spec := canonicalSquareQ_spec pcode x z0 hp
      let s_can := cornerSeg pcode M x q_can z0 h_can_spec.1 h_can_spec.2
      have h_in_can : ∀ (s : ShellSegment pcode M),
          ((⟨(⟨(x, Sum.inr (Sum.inr z0)), hp⟩, r), h_in⟩ : ShellVertex pcode M) = shellSegStartVertex pcode M s ∨
           (⟨(⟨(x, Sum.inr (Sum.inr z0)), hp⟩, r), h_in⟩ : ShellVertex pcode M) = shellSegEndVertex pcode M s) →
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (s_can, b))) (Sum.inl (Sum.inr (Sum.inl (s, b)))) = 1 := by
        intro s hs
        have hrs0 : s.val.2.1.val = 0 := by
          rcases hs with h_s | h_e
          · exact (congr_arg (fun w : ShellVertex pcode M => w.val.2.val) h_s).symm.trans hr_nz
          · exact (congr_arg (fun w : ShellVertex pcode M => w.val.2.val) h_e).symm.trans hr_nz
        have hks0 : s.val.2.2.val = 0 := by have := s.property; omega
        have h_s_end : (⟨(⟨(x, Sum.inr (Sum.inr z0)), hp⟩, r), h_in⟩ : ShellVertex pcode M) = shellSegEndVertex pcode M s := by
          rcases hs with h_s | h_e
          · exfalso
            have hv := congr_arg (fun w : ShellVertex pcode M => w.val.1.val.2) h_s
            dsimp [shellSegStartVertex, bxStartLink, bxStart, armStart, projXq0ToBoundaryX0] at hv
            rw [dif_pos hks0] at hv
            exact Sum.inr_ne_inl hv
          · exact h_e
        have hx_s : s.val.1.val.1 = x :=
          (congr_arg (fun w : ShellVertex pcode M => w.val.1.val.1) h_s_end).symm
        have hz_s : s.val.1.val.2.val.2 = z0 := by
          have hv := congr_arg (fun w : ShellVertex pcode M => w.val.1.val.2) h_s_end
          dsimp [shellSegEndVertex, shellSegEndLink, shellSegEndV] at hv
          have h_not_lt : ¬ s.val.2.2.val < s.val.2.1.val := by omega
          rw [dif_neg h_not_lt] at hv
          injection hv with h1; injection h1 with hz_eq
          exact hz_eq.symm
        let qs := s.val.1.val.2.val.1
        have hXs : pcode.checkX x qs ≠ 0 := hx_s ▸ s.val.1.property
        have hZs : pcode.checkZ z0 qs ≠ 0 := hz_s ▸ s.val.1.val.2.property
        have hs_eq : s = cornerSeg pcode M x qs z0 hXs hZs := by
          apply Subtype.ext; apply Prod.ext
          · apply Subtype.ext; apply Prod.ext
            · exact hx_s
            · apply Subtype.ext; apply Prod.ext; rfl; exact hz_s
          · exact Prod.ext (Fin.ext hrs0) (Fin.ext hks0)
        rw [hs_eq]
        exact bdlDeltaX1_canonical_seg_eq_one pcode M s_can b rfl rfl rfl qs hXs hZs
      exact Relation.ReflTransGen.single ⟨h_seg_chk seg h_inc, h_seg_chk seg0 h_inc0,
        Sum.inl (Sum.inl (s_can, b)),
        by simp only [bdlCylinderStepX_checkZ]; rw [h_in_can seg h_inc]; decide,
        by simp only [bdlCylinderStepX_checkZ]; rw [h_in_can seg0 h_inc0]; decide⟩

/-- Explicit formula for the subdivision index `(svIncidentSeg pcode M hq sv).val.2.2.val` of a shell vertex. -/
lemma svIncidentSeg_k_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (sv : ShellVertex pcode M) :
    (svIncidentSeg pcode M hq sv).val.2.2.val =
      match sv.val.1.val.2 with
      | Sum.inl _ => 0
      | Sum.inr (Sum.inl (_, j)) => j.val
      | Sum.inr (Sum.inr _) => sv.val.2.val := by
  rcases sv with ⟨⟨⟨⟨x, v⟩, hp⟩, r⟩, h_in⟩
  rcases v with q0 | ⟨⟨eZ, j⟩ | z0⟩ <;> rfl

/-! ## 3. Global Cylinder Cocycle Exactness -/

/-- Direct layer-0 terminal constancy from `cylinderResidualCocycle_arm_eq_center` without needing `hq_z`. -/
lemma cylinderResidualCocycle_term_eq_coarse {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (eZ : ActiveZ pcode)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x eZ.val.1 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h (Sum.inl qX) = 0)
    (h_syn_arm : ∀ k' : Fin (M + 1),
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inr (Sum.inl (Sum.inl (eZ, k', 0)))) = 0) :
    cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), 0)) =
      coarseProjCocycle pcode M h eZ.val.1 := by
  have h_end := (cylinderResidualCocycle_arm_eq_center pcode M h eZ 0 h_zero_X h_syn_arm (Fin.last M)).2
  have h_last : armEnd pcode M eZ (Fin.last M) = Sum.inr (Sum.inr eZ) := by
    dsimp [armEnd, Fin.last]
    rw [dif_neg (Nat.lt_irrefl M)]
  rw [← h_last, h_end]
  rfl

/-- Global syndrome preservation for `coarseProjCocycle`: if `syndrome (dualCode (bdlCylinderStepX pcode M)) h = 0`,
    then `syndrome (dualCode pcode) (coarseProjCocycle pcode M h) = 0`. -/
theorem syndrome_coarseProjCocycle_global {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2)
    (h_syn : syndrome (dualCode (bdlCylinderStepX pcode M)) h = 0) :
    syndrome (dualCode pcode) (coarseProjCocycle pcode M h) = 0 := by
  have h_syn_at : ∀ mZ, syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0 :=
    fun mZ => congr_fun h_syn mZ
  ext z0
  apply syndrome_coarseProjCocycle_eq pcode M h z0
  · intro eZ _
    exact cylinderResidualCocycle_term_eq_coarse pcode M h eZ
      (fun x _ qX hqX => cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h x
        (fun _ _ _ => h_syn_at _) (fun _ _ _ _ => h_syn_at _) qX hqX)
      (fun _ => h_syn_at _)
  · exact h_syn_at _

/-- Global coboundary exactness for `fullCylinderCocycle`:
    if `syndrome (dualCode (bdlCylinderStepX pcode M)) h = 0` and `checkGen (dualCode pcode) c = coarseProjCocycle pcode M h`,
    then `checkGen (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) = h`. -/
theorem checkGen_fullCylinderCocycle_global {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (hq_z : ∀ q : Q, ∃ z : M_Z, pcode.checkZ z q ≠ 0)
    (h : BDLStepXQ pcode M → ZMod 2) (c : M_X → ZMod 2)
    (h_syn : syndrome (dualCode (bdlCylinderStepX pcode M)) h = 0)
    (hc_eq : checkGen (dualCode pcode) c = coarseProjCocycle pcode M h) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) = h := by
  have h_syn_at : ∀ mZ, syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0 :=
    fun mZ => congr_fun h_syn mZ
  ext q
  symm
  apply fullCylinderCocycle_eq_of_residual pcode M h c q
  rw [checkGen_dual_liftStepXMX]
  rcases q with qX | ⟨v0, b⟩
  · rw [cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h (qXOwnerX pcode M qX)
      (fun _ _ _ => h_syn_at _) (fun _ _ _ _ => h_syn_at _) qX rfl]
    rfl
  · rw [cylinderResidualCocycle_inr_eq_coarse pcode M hq_z h (xq0OwnerQ pcode M v0)
      (fun x _ qX hqX => cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h x
        (fun _ _ _ => h_syn_at _) (fun _ _ _ _ => h_syn_at _) qX hqX)
      (fun _ _ _ _ => h_syn_at _) (fun _ _ _ => h_syn_at _) v0 rfl b, ← hc_eq]
    rfl

end WeldedHierarchy
