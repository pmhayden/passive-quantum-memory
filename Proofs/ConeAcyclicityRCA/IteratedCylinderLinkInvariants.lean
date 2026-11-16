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

import Proofs.ConeAcyclicityRCA.DualCylinderLinkConnected

/-!
# Primal Cylinder Link Connectivity and Non-Isolation Invariants Across Iterated Welds

Proves primal X-check link connectivity for the three-layer cylinder weld (hasConnectedXLinks_bdlCylinderStepX) and lifts both primal and dual link connectivity across randomized X-welding and Z-welding steps (hasConnectedXLinks_bdlRandomStepX, hasConnectedXLinks_bdlRandomStepZ). Introduces HasEveryQubitChecked and establishes inductive non-isolation and link-connectivity invariants across the iterated welded hierarchy bdlIteratedBundled.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Proposition 3.7 (`prop:classical-hpl`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Definition 4.2 (`def:multiscale-cluster-decoder`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Primal Cylinder Step Link-Connectedness Theorem -/

/-- Preservation of `HasConnectedXLinks` for `bdlCylinderStepX pcode M` across a cylinder thickening step. -/
theorem hasConnectedXLinks_bdlCylinderStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h_conn : HasConnectedXLinks pcode)
    (hq : HasNoIsolatedQ pcode) :
    HasConnectedXLinks (bdlCylinderStepX pcode M) := by
  intro mX q q' hq_chk hq'_chk
  rcases mX with ⟨x, b⟩ | ⟨sv, b⟩
  · -- Case 1: Apex X-check `mX = Sum.inl (x, b)`
    have h_extract : ∀ a : BDLStepXQ pcode M,
        (bdlCylinderStepX pcode M).checkX (Sum.inl (x, b)) a ≠ 0 →
        ∃ (qa : Q) (hxa : pcode.checkX x qa ≠ 0),
          a = Sum.inl (Sum.inl (cornerSpokeRadial pcode M x qa hxa, b)) := by
      intro a ha
      rcases a with ⟨⟨rv, b'⟩ | ⟨⟨seg, b'⟩ | ⟨xv, b'⟩⟩⟩ | qQ
      · change bdlDeltaX0 pcode M (Sum.inl (x, b)) (Sum.inl (rv, b')) ≠ 0 at ha
        dsimp [bdlDeltaX0] at ha
        by_cases hr0 : rv.val.val.2.val = 0
        · rw [if_pos hr0] at ha
          by_cases h_eq : (Sum.inl (x, b) : BDLStepXMX pcode M) = Sum.inl (rv.val.val.1.val.1, b')
          · injection h_eq with hp_eq
            injection hp_eq with hx_eq hb_eq
            subst hx_eq hb_eq
            rcases rv with ⟨⟨⟨⟨⟨x', v⟩, hp⟩, r⟩, h_in⟩, h_not_diag⟩
            (try dsimp at hr0 ⊢)
            rcases v with qa | ⟨⟨eZ, j⟩ | z0⟩
            · refine ⟨qa, hp, ?_⟩
              apply congr_arg Sum.inl
              apply congr_arg Sum.inl
              apply Prod.ext
              · apply Subtype.ext; apply Subtype.ext; apply Prod.ext
                · rfl
                · exact Fin.ext hr0
              · rfl
            · dsimp [InShellR] at h_in; omega
            · exact False.elim (h_not_diag ⟨hr0, z0, rfl⟩)
          · rw [if_neg h_eq] at ha; exact False.elim (ha rfl)
        · rw [if_neg hr0] at ha
          exact False.elim (ha rfl)
      · change bdlDeltaX0 pcode M (Sum.inl (x, b)) (Sum.inr (Sum.inl (seg, b'))) ≠ 0 at ha
        dsimp [bdlDeltaX0] at ha
        exact False.elim (ha rfl)
      · change bdlDeltaX0 pcode M (Sum.inl (x, b)) (Sum.inr (Sum.inr (xv, b'))) ≠ 0 at ha
        dsimp [bdlDeltaX0] at ha
        exact False.elim (ha rfl)
      · exact False.elim (ha rfl)
    obtain ⟨q1, hxq1, rfl⟩ := h_extract q hq_chk
    obtain ⟨q2, hxq2, rfl⟩ := h_extract q' hq'_chk
    have h_path := h_conn x q1 q2 hxq1 hxq2
    clear hq_chk hq'_chk
    induction h_path with
    | refl => rfl
    | tail _ h_step ih =>
      rcases h_step with ⟨hxa, hxc, z0, hza, hzc⟩
      have h_ih := ih hxa
      have h_ex : ∃ q0 : Q, pcode.checkX x q0 ≠ 0 ∧ pcode.checkZ z0 q0 ≠ 0 := ⟨_, hxa, hza⟩
      let q_can := canonicalSquareQ pcode x z0 h_ex
      have h_can_spec := canonicalSquareQ_spec pcode x z0 h_ex
      let s_can := cornerSeg pcode M x q_can z0 h_can_spec.1 h_can_spec.2
      have h_fine_step : XLinkStep (bdlCylinderStepX pcode M) (Sum.inl (x, b))
          (Sum.inl (Sum.inl (cornerSpokeRadial pcode M x _ hxa, b)))
          (Sum.inl (Sum.inl (cornerSpokeRadial pcode M x _ hxc, b))) := by
        refine ⟨?_, ?_, Sum.inl (Sum.inl (s_can, b)), ?_, ?_⟩
        · simp only [bdlCylinderStepX_checkX]
          exact ne_of_eq_of_ne (bdlDeltaX0_radial_apex_eq_one pcode M (cornerSpokeRadial pcode M x _ hxa) b rfl) (by decide)
        · simp only [bdlCylinderStepX_checkX]
          exact ne_of_eq_of_ne (bdlDeltaX0_radial_apex_eq_one pcode M (cornerSpokeRadial pcode M x _ hxc) b rfl) (by decide)
        · simp only [bdlCylinderStepX_checkZ]
          exact ne_of_eq_of_ne (bdlDeltaX1_canonical_spoke_eq_one pcode M s_can b rfl rfl rfl _ hxa hza) (by decide)
        · simp only [bdlCylinderStepX_checkZ]
          exact ne_of_eq_of_ne (bdlDeltaX1_canonical_spoke_eq_one pcode M s_can b rfl rfl rfl _ hxc hzc) (by decide)
      exact Relation.ReflTransGen.tail h_ih h_fine_step
  · -- Case 2: Shell vertex X-check `mX = Sum.inr (sv, b)`
    let seg0 := svIncidentSeg pcode M hq sv
    let q_hub : BDLStepXQ pcode M := Sum.inl (Sum.inr (Sum.inl (seg0, b)))
    have h_inc0 := (svIncidentSeg_start_or_end pcode M hq sv).2
    have h_hub_chk : (bdlCylinderStepX pcode M).checkX (Sum.inr (sv, b)) q_hub ≠ 0 := by
      simp only [bdlCylinderStepX_checkX]
      rcases h_inc0 with h_s | h_e
      · rw [h_s, bdlDeltaX0_seg_start_eq_one]; decide
      · rw [h_e, bdlDeltaX0_seg_end_eq_one]; decide
    apply reflTransGen_XLinkStep_of_hub (bdlCylinderStepX pcode M)
      (Sum.inr (sv, b)) q_hub _ hq_chk hq'_chk
    intro a ha
    rcases a with ⟨⟨rv, b'⟩ | ⟨⟨seg, b'⟩ | ⟨xv, b'⟩⟩⟩ | ⟨v0, b'⟩
    · -- Subcase 2a: Radial 1-cell `Sum.inl (Sum.inl (rv, b'))`
      change bdlDeltaX0 pcode M (Sum.inr (sv, b)) (Sum.inl (rv, b')) ≠ 0 at ha
      dsimp [bdlDeltaX0] at ha
      by_cases hr0 : rv.val.val.2.val = 0
      · rw [if_pos hr0] at ha
        by_cases h_self : (Sum.inr (sv, b) : BDLStepXMX pcode M) = Sum.inr (rv.val, b')
        · injection h_self with hp_eq
          injection hp_eq with hsv_eq hb_eq
          subst hsv_eq hb_eq
          have h_step : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (rv.val, b))
              (Sum.inl (Sum.inl (rv, b))) q_hub := by
            rcases rv with ⟨⟨⟨⟨⟨x, v⟩, hp⟩, r⟩, h_in⟩, h_not_diag⟩
            (try dsimp at hr0 ⊢)
            rcases v with q0 | ⟨⟨eZ, j⟩ | z0⟩
            · let z0 := Classical.choose (hq.1 q0 ⟨x, hp⟩)
              have hz0 := Classical.choose_spec (hq.1 q0 ⟨x, hp⟩)
              have h_ex : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0 := ⟨q0, hp, hz0⟩
              let q_can := canonicalSquareQ pcode x z0 h_ex
              have h_can_spec := canonicalSquareQ_spec pcode x z0 h_ex
              let s_can := cornerSeg pcode M x q_can z0 h_can_spec.1 h_can_spec.2
              refine ⟨by simp only [bdlCylinderStepX_checkX]; exact ne_of_eq_of_ne (bdlDeltaX0_radial_self_eq_one pcode M _ b) (by decide), h_hub_chk,
                Sum.inl (Sum.inl (s_can, b)), ?_, ?_⟩
              · have h_rv_eq : (⟨⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩, h_not_diag⟩ : RadialVertex pcode M) =
                    cornerSpokeRadial pcode M x q0 hp := by
                  apply Subtype.ext; apply Subtype.ext; apply Prod.ext; · rfl
                  · exact Fin.ext hr0
                rw [h_rv_eq]
                simp only [bdlCylinderStepX_checkZ]
                exact ne_of_eq_of_ne (bdlDeltaX1_canonical_spoke_eq_one pcode M s_can b rfl rfl rfl q0 hp hz0) (by decide)
              · have h_seg0_eq : seg0 = cornerSeg pcode M x q0 z0 hp hz0 := by
                  apply Subtype.ext; apply Prod.ext; · rfl
                  · exact Prod.ext (Fin.ext hr0) rfl
                dsimp [q_hub]
                rw [h_seg0_eq]
                exact ne_of_eq_of_ne (bdlDeltaX1_canonical_seg_eq_one pcode M s_can b rfl rfl rfl q0 hp hz0) (by decide)
            · dsimp [InShellR] at h_in; omega
            · exact False.elim (h_not_diag ⟨hr0, z0, rfl⟩)
          exact Relation.ReflTransGen.single h_step
        · rw [if_neg h_self] at ha; exact False.elim (ha rfl)
      · rw [if_neg hr0] at ha
        by_cases h_self : (Sum.inr (sv, b) : BDLStepXMX pcode M) = Sum.inr (rv.val, b')
        · injection h_self with hp_eq
          injection hp_eq with hsv_eq hb_eq
          subst hsv_eq hb_eq
          have hrs0_nz : seg0.val.2.1.val ≠ 0 := by
            rw [(svIncidentSeg_start_or_end pcode M hq rv.val).1]; exact hr0
          have h_step : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (rv.val, b))
              (Sum.inl (Sum.inl (rv, b))) q_hub := by
            refine ⟨by simp only [bdlCylinderStepX_checkX]; rw [bdlDeltaX0_radial_self_eq_one]; decide, h_hub_chk,
              Sum.inl (Sum.inl (seg0, b)), ?_, ?_⟩
            · simp only [bdlCylinderStepX_checkZ]
              rcases h_inc0 with h_s | h_e
              · have h_rv : rv = shellSegStartRadial pcode M seg0 := Subtype.ext h_s
                rw [h_rv, bdlDeltaX1_pos_startRadial_eq_one pcode M seg0 b hrs0_nz]; decide
              · have h_rv : rv = shellSegEndRadial pcode M seg0 hrs0_nz := Subtype.ext h_e
                rw [h_rv, bdlDeltaX1_pos_endRadial_eq_one pcode M seg0 b hrs0_nz]; decide
            · simp only [bdlCylinderStepX_checkZ]
              rw [bdlDeltaX1_pos_seg_eq_one pcode M seg0 b hrs0_nz]; decide
          exact Relation.ReflTransGen.single h_step
        · by_cases h_par : (Sum.inr (sv, b) : BDLStepXMX pcode M) = Sum.inr (radialParentVertex pcode M rv.val, b')
          · injection h_par with hp_eq
            injection hp_eq with hpar_eq hb_eq
            subst hb_eq
            have h_child_non_z : ∀ (rv' : RadialVertex pcode M) (hr' : rv'.val.val.2.val ≠ 0)
                (hpar' : radialParentVertex pcode M rv'.val = sv)
                (h_nz : ∀ z0, rv'.val.val.1.val.2 ≠ Sum.inr (Sum.inr z0)),
                Relation.ReflTransGen (XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b)))
                  (Sum.inl (Sum.inl (rv', b))) q_hub := by
              intro rv' hr' hpar' h_nz
              let seg' := svIncidentSeg pcode M hq rv'.val
              have h_inc' := (svIncidentSeg_start_or_end pcode M hq rv'.val)
              have hr_seg' : seg'.val.2.1.val ≠ 0 := by rw [h_inc'.1]; exact hr'
              have h_tri' : seg'.val.2.2.val ≠ seg'.val.2.1.val := by
                have hk : seg'.val.2.2.val =
                    match rv'.val.val.1.val.2 with
                    | Sum.inl _ => 0
                    | Sum.inr (Sum.inl (_, j)) => j.val
                    | Sum.inr (Sum.inr _) => rv'.val.val.2.val :=
                  svIncidentSeg_k_eq pcode M hq rv'.val
                have hr_eq' : seg'.val.2.1.val = rv'.val.val.2.val := congr_arg Fin.val h_inc'.1
                rcases h : rv'.val.val.1.val.2 with q0 | ⟨⟨eZ, j⟩ | z0⟩
                · rw [h] at hk; (try dsimp at hk); omega
                · rw [h] at hk; (try dsimp at hk)
                  have hin' := rv'.val.property
                  dsimp [InShellR] at hin'
                  rw [h] at hin'
                  omega
                · exact False.elim (h_nz z0 h)
              let seg_pred := shellSegPred pcode M seg' h_tri'
              have h_pred_inc : sv = shellSegStartVertex pcode M seg_pred ∨ sv = shellSegEndVertex pcode M seg_pred := by
                rcases h_inc'.2 with h_s | h_e
                · left
                  rw [← hpar', h_s]
                  exact radialParent_start_eq_start_pred pcode M seg' h_tri'
                · right
                  rw [← hpar', h_e]
                  exact radialParent_end_eq_end_pred pcode M seg' h_tri'
              have h_step1 : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
                  (Sum.inl (Sum.inl (rv', b))) (Sum.inl (Sum.inr (Sum.inl (seg_pred, b)))) := by
                refine ⟨?_, ?_, Sum.inl (Sum.inl (seg', b)), ?_, ?_⟩
                · simp only [bdlCylinderStepX_checkX]
                  rw [← hpar', bdlDeltaX0_radial_parent_eq_one pcode M rv' b hr']; decide
                · simp only [bdlCylinderStepX_checkX]
                  rcases h_pred_inc with h_s | h_e
                  · rw [h_s, bdlDeltaX0_seg_start_eq_one]; decide
                  · rw [h_e, bdlDeltaX0_seg_end_eq_one]; decide
                · simp only [bdlCylinderStepX_checkZ]
                  rcases h_inc'.2 with h_s | h_e
                  · have h_rv' : rv' = shellSegStartRadial pcode M seg' := Subtype.ext h_s
                    rw [h_rv', bdlDeltaX1_pos_startRadial_eq_one pcode M seg' b hr_seg']; decide
                  · have h_rv' : rv' = shellSegEndRadial pcode M seg' hr_seg' := Subtype.ext h_e
                    rw [h_rv', bdlDeltaX1_pos_endRadial_eq_one pcode M seg' b hr_seg']; decide
                · simp only [bdlCylinderStepX_checkZ]
                  rw [bdlDeltaX1_pos_pred_eq_one pcode M seg' b h_tri']; decide
              exact (Relation.ReflTransGen.single h_step1).trans
                (bdlCylinderStepX_azimuthal_incident_connected pcode M hq sv b seg_pred h_pred_inc)
            by_cases h_z : ∃ z0 : M_Z, rv.val.val.1.val.2 = Sum.inr (Sum.inr z0)
            · rcases h_z with ⟨z0, hz0⟩
              let seg_tri := svIncidentSeg pcode M hq rv.val
              have h_tri_eq : seg_tri.val.2.2.val = seg_tri.val.2.1.val := by
                have hk : seg_tri.val.2.2.val =
                    match rv.val.val.1.val.2 with
                    | Sum.inl _ => 0
                    | Sum.inr (Sum.inl (_, j)) => j.val
                    | Sum.inr (Sum.inr _) => rv.val.val.2.val :=
                  svIncidentSeg_k_eq pcode M hq rv.val
                rw [hz0] at hk; (try dsimp at hk)
                have hr_eq_tri : seg_tri.val.2.1.val = rv.val.val.2.val :=
                  congr_arg Fin.val (svIncidentSeg_start_or_end pcode M hq rv.val).1
                omega
              have hr_tri : seg_tri.val.2.1.val ≠ 0 := by
                rw [(svIncidentSeg_start_or_end pcode M hq rv.val).1]; exact hr0
              have h_end_tri : rv.val = shellSegEndVertex pcode M seg_tri := by
                rcases (svIncidentSeg_start_or_end pcode M hq rv.val).2 with h_s | h_e
                · exfalso
                  have hv := congr_arg (fun w : ShellVertex pcode M => w.val.1.val.2) h_s
                  (try dsimp at hv)
                  rw [hz0] at hv
                  dsimp [shellSegStartVertex, bxStartLink, bxStart, armStart, projXq0ToBoundaryX0] at hv
                  split_ifs at hv; nomatch hv
                · exact h_e
              let rv_start := shellSegStartRadial pcode M seg_tri
              have h_par_start : radialParentVertex pcode M rv_start.val = sv := by
                dsimp [rv_start, shellSegStartRadial]
                rw [radialParent_start_eq_end_of_eq pcode M seg_tri hr_tri h_tri_eq, ← h_end_tri]
                exact hpar_eq.symm
              have hr_start : rv_start.val.val.2.val ≠ 0 := hr_tri
              have h_nz_start : ∀ z1, rv_start.val.val.1.val.2 ≠ Sum.inr (Sum.inr z1) := by
                intro z1 hc
                dsimp [rv_start, shellSegStartRadial, shellSegStartVertex, bxStartLink, bxStart,
                  armStart, projXq0ToBoundaryX0] at hc
                split_ifs at hc; nomatch hc
              have h_step_to_start : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
                  (Sum.inl (Sum.inl (rv, b))) (Sum.inl (Sum.inl (rv_start, b))) := by
                refine ⟨?_, ?_, Sum.inl (Sum.inl (seg_tri, b)), ?_, ?_⟩
                · simp only [bdlCylinderStepX_checkX]
                  rw [hpar_eq, bdlDeltaX0_radial_parent_eq_one pcode M rv b hr0]; decide
                · simp only [bdlCylinderStepX_checkX]
                  rw [← h_par_start, bdlDeltaX0_radial_parent_eq_one pcode M rv_start b hr_start]; decide
                · simp only [bdlCylinderStepX_checkZ]
                  have h_rv_end : rv = shellSegEndRadial pcode M seg_tri hr_tri := Subtype.ext h_end_tri
                  rw [h_rv_end, bdlDeltaX1_pos_endRadial_eq_one pcode M seg_tri b hr_tri]; decide
                · simp only [bdlCylinderStepX_checkZ]
                  rw [bdlDeltaX1_pos_startRadial_eq_one pcode M seg_tri b hr_tri]; decide
              exact (Relation.ReflTransGen.single h_step_to_start).trans
                (h_child_non_z rv_start hr_start h_par_start h_nz_start)
            · push_neg at h_z
              exact h_child_non_z rv hr0 hpar_eq.symm h_z
          · rw [if_neg h_par, if_neg h_self] at ha; exact False.elim (ha rfl)
    · -- Subcase 2b: Azimuthal segment `Sum.inl (Sum.inr (Sum.inl (seg, b')))`
      change bdlDeltaX0 pcode M (Sum.inr (sv, b)) (Sum.inr (Sum.inl (seg, b'))) ≠ 0 at ha
      dsimp [bdlDeltaX0] at ha
      by_cases h_s : (Sum.inr (sv, b) : BDLStepXMX pcode M) = Sum.inr (shellSegStartVertex pcode M seg, b')
      · injection h_s with hp_eq
        injection hp_eq with hsv_eq hb_eq
        subst hb_eq
        exact bdlCylinderStepX_azimuthal_incident_connected pcode M hq sv b seg (Or.inl hsv_eq)
      · by_cases h_e : (Sum.inr (sv, b) : BDLStepXMX pcode M) = Sum.inr (shellSegEndVertex pcode M seg, b')
        · injection h_e with hp_eq
          injection hp_eq with hsv_eq hb_eq
          subst hb_eq
          exact bdlCylinderStepX_azimuthal_incident_connected pcode M hq sv b seg (Or.inr hsv_eq)
        · rw [if_neg h_s, if_neg h_e] at ha; exact False.elim (ha rfl)
    · -- Subcase 2c: Vertical boundary 1-cell `Sum.inl (Sum.inr (Sum.inr (xv, b')))`
      have ha_orig := ha
      change bdlDeltaX0 pcode M (Sum.inr (sv, b)) (Sum.inr (Sum.inr (xv, b'))) ≠ 0 at ha
      dsimp [bdlDeltaX0] at ha
      have h_sv_outer : sv = mkOuterShellVertex pcode M xv ∧ (b = 0 ∨ b = b'.succ) := by
        by_cases h0 : (Sum.inr (sv, b) : BDLStepXMX pcode M) = Sum.inr (mkOuterShellVertex pcode M xv, 0)
        · injection h0 with hp_eq; exact ⟨congr_arg Prod.fst hp_eq, Or.inl (congr_arg Prod.snd hp_eq)⟩
        · by_cases h1 : (Sum.inr (sv, b) : BDLStepXMX pcode M) = Sum.inr (mkOuterShellVertex pcode M xv, b'.succ)
          · injection h1 with hp_eq; exact ⟨congr_arg Prod.fst hp_eq, Or.inr (congr_arg Prod.snd hp_eq)⟩
          · rw [if_neg h0, if_neg h1] at ha; exact False.elim (ha rfl)
      rcases h_sv_outer with ⟨h_sv_outer, hb_b'⟩
      have h_seg0_outer : mkOuterShellSegment pcode M seg0.val.1 seg0.val.2.2 = seg0 := by
        apply Subtype.ext; apply Prod.ext; · rfl
        · apply Prod.ext
          · exact ((svIncidentSeg_start_or_end pcode M hq sv).1.trans
              (congr_arg (fun w : ShellVertex pcode M => w.val.2) h_sv_outer)).symm
          · rfl
      have h_step : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
          (Sum.inl (Sum.inr (Sum.inr (xv, b')))) q_hub := by
        refine ⟨ha_orig, h_hub_chk,
          Sum.inl (Sum.inr (seg0.val.1, seg0.val.2.2, b')), ?_, ?_⟩
        · change bdlDeltaX1 pcode M (Sum.inr (seg0.val.1, seg0.val.2.2, b')) (Sum.inr (Sum.inr (xv, b'))) ≠ 0
          dsimp [bdlDeltaX1]
          have h_ne := shellSegStartVertex_ne_end pcode M seg0
          rcases h_inc0 with h_s | h_e
          · have h1 : xv = bxStartLink pcode M seg0.val.1 seg0.val.2.2 := by
              have hs := shellSegStartVertex_outer pcode M seg0.val.1 seg0.val.2.2
              rw [h_seg0_outer, ← h_s, h_sv_outer] at hs
              exact congr_arg (fun w : ShellVertex pcode M => w.val.1) hs
            have h2 : xv ≠ bxEndLink pcode M seg0.val.1 seg0.val.2.2 := by
              intro hc
              have he := shellSegEndVertex_outer pcode M seg0.val.1 seg0.val.2.2
              rw [h_seg0_outer, ← hc, ← h_sv_outer] at he
              exact h_ne (h_s.symm.trans he.symm)
            have h1_eq : (Sum.inr (Sum.inr (xv, b')) : BDLCX1 pcode M) =
                Sum.inr (Sum.inr (bxStartLink pcode M seg0.val.1 seg0.val.2.2, b')) := by rw [h1]
            have h2_ne : (Sum.inr (Sum.inr (xv, b')) : BDLCX1 pcode M) ≠
                Sum.inr (Sum.inr (bxEndLink pcode M seg0.val.1 seg0.val.2.2, b')) := by
              intro hc; injection hc with hc1; injection hc1 with hc2; injection hc2 with hc3 _; exact h2 hc3
            rw [if_pos h1_eq, if_neg h2_ne]; decide
          · have h2 : xv = bxEndLink pcode M seg0.val.1 seg0.val.2.2 := by
              have he := shellSegEndVertex_outer pcode M seg0.val.1 seg0.val.2.2
              rw [h_seg0_outer, ← h_e, h_sv_outer] at he
              exact congr_arg (fun w : ShellVertex pcode M => w.val.1) he
            have h1 : xv ≠ bxStartLink pcode M seg0.val.1 seg0.val.2.2 := by
              intro hc
              have hs := shellSegStartVertex_outer pcode M seg0.val.1 seg0.val.2.2
              rw [h_seg0_outer, ← hc, ← h_sv_outer] at hs
              exact h_ne (hs.trans h_e)
            have h1_ne : (Sum.inr (Sum.inr (xv, b')) : BDLCX1 pcode M) ≠
                Sum.inr (Sum.inr (bxStartLink pcode M seg0.val.1 seg0.val.2.2, b')) := by
              intro hc; injection hc with hc1; injection hc1 with hc2; injection hc2 with hc3 _; exact h1 hc3
            have h2_eq : (Sum.inr (Sum.inr (xv, b')) : BDLCX1 pcode M) =
                Sum.inr (Sum.inr (bxEndLink pcode M seg0.val.1 seg0.val.2.2, b')) := by rw [h2]
            rw [if_neg h1_ne, if_pos h2_eq]; decide
        · change bdlDeltaX1 pcode M (Sum.inr (seg0.val.1, seg0.val.2.2, b')) (Sum.inr (Sum.inl (seg0, b))) ≠ 0
          dsimp [bdlDeltaX1]
          rw [h_seg0_outer]
          rcases hb_b' with rfl | rfl <;> fin_cases b' <;> simp
      exact Relation.ReflTransGen.single h_step
    · -- Subcase 2d: Boundary `BDLCQ1` 1-cell `Sum.inr (v0, b')`
      change bdlGXQ0 pcode M (Sum.inr (sv, b)) (v0, b') ≠ 0 at ha
      dsimp [bdlGXQ0] at ha
      split_ifs at ha with h_cond
      · rcases h_cond with ⟨hr_last, hv_eq, hb_eq⟩
        subst hb_eq
        let x := sv.val.1.val.1
        have hx : pcode.checkX x (xq0OwnerQ pcode M v0) ≠ 0 := ha
        rcases v0 with q0 | ⟨⟨eZ, j⟩ | eZ⟩
        · let z0 := Classical.choose (hq.1 q0 ⟨x, hx⟩)
          have hz0 := Classical.choose_spec (hq.1 q0 ⟨x, hx⟩)
          let eZ : ActiveZ pcode := ⟨(q0, z0), hz0⟩
          let s : ActiveZLink pcode := ⟨(x, eZ), hx⟩
          let seg_s := mkOuterShellSegment pcode M s 0
          have h_inc_s : sv = shellSegStartVertex pcode M seg_s := by
            apply Subtype.ext; apply Prod.ext
            · apply Subtype.ext; apply Prod.ext; · rfl
              · exact hv_eq
            · exact hr_last
          have h_step1 : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
              (Sum.inr (Sum.inl q0, b)) (Sum.inl (Sum.inr (Sum.inl (seg_s, b)))) := by
            refine ⟨?_, ?_, Sum.inr (Sum.inl (Sum.inl (eZ, 0, b))), ?_, ?_⟩
            · change bdlGXQ0 pcode M (Sum.inr (sv, b)) (Sum.inl q0, b) ≠ 0
              dsimp [bdlGXQ0]; rw [if_pos ⟨hr_last, hv_eq, rfl⟩]; exact hx
            · simp only [bdlCylinderStepX_checkX]
              rw [h_inc_s, bdlDeltaX0_seg_start_eq_one]; decide
            · change bdlDeltaQ1 pcode M (Sum.inl (eZ, 0, b)) (Sum.inl q0, b) ≠ 0
              have h_ne : ((Sum.inl q0, b) : BDLCQ1 pcode M) ≠ (armEnd pcode M eZ 0, b) := by
                intro hc; injection hc with hc1 _; exact armStart_ne_armEnd pcode M eZ 0 hc1
              have h_eq : ((Sum.inl q0, b) : BDLCQ1 pcode M) = (armStart pcode M eZ 0, b) := rfl
              dsimp [bdlDeltaQ1]
              rw [if_pos h_eq, if_neg h_ne]; decide
            · change bdlGXQ1 pcode M (Sum.inl (eZ, 0, b)) (Sum.inr (Sum.inl (seg_s, b))) ≠ 0
              dsimp [bdlGXQ1, seg_s, mkOuterShellSegment]
              rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]; exact hx
          exact (Relation.ReflTransGen.single h_step1).trans
            (bdlCylinderStepX_azimuthal_incident_connected pcode M hq sv b seg_s (Or.inl h_inc_s))
        · let k : Fin (M + 1) := ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self M)⟩
          let s : ActiveZLink pcode := ⟨(x, eZ), hx⟩
          let seg_s := mkOuterShellSegment pcode M s k
          have h_inc_s : sv = shellSegEndVertex pcode M seg_s := by
            apply Subtype.ext; apply Prod.ext
            · apply Subtype.ext; apply Prod.ext; · rfl
              · dsimp [seg_s, mkOuterShellSegment, shellSegEndVertex, shellSegEndLink, shellSegEndV, Fin.last]
                rw [dif_pos j.isLt]
                exact hv_eq
            · exact hr_last
          have h_step1 : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
              (Sum.inr (Sum.inr (Sum.inl (eZ, j)), b)) (Sum.inl (Sum.inr (Sum.inl (seg_s, b)))) := by
            refine ⟨?_, ?_, Sum.inr (Sum.inl (Sum.inl (eZ, k, b))), ?_, ?_⟩
            · change bdlGXQ0 pcode M (Sum.inr (sv, b)) (Sum.inr (Sum.inl (eZ, j)), b) ≠ 0
              dsimp [bdlGXQ0]; rw [if_pos ⟨hr_last, hv_eq, rfl⟩]; exact hx
            · simp only [bdlCylinderStepX_checkX]
              rw [h_inc_s, bdlDeltaX0_seg_end_eq_one]; decide
            · change bdlDeltaQ1 pcode M (Sum.inl (eZ, k, b)) (Sum.inr (Sum.inl (eZ, j)), b) ≠ 0
              dsimp [bdlDeltaQ1]
              have h_end_eq : (Sum.inr (Sum.inl (eZ, j)) : Xq0 pcode M) = armEnd pcode M eZ k := by
                dsimp [armEnd, k]; rw [if_pos j.isLt]
              have h1 : ((Sum.inr (Sum.inl (eZ, j)), b) : BDLCQ1 pcode M) ≠ (armStart pcode M eZ k, b) := by
                intro hc; injection hc with hc1 _; exact armStart_ne_armEnd pcode M eZ k (hc1.symm.trans h_end_eq)
              have h2 : ((Sum.inr (Sum.inl (eZ, j)), b) : BDLCQ1 pcode M) = (armEnd pcode M eZ k, b) := by
                rw [h_end_eq]
              rw [if_neg h1, if_pos h2]; decide
            · change bdlGXQ1 pcode M (Sum.inl (eZ, k, b)) (Sum.inr (Sum.inl (seg_s, b))) ≠ 0
              dsimp [bdlGXQ1, seg_s, mkOuterShellSegment]
              rw [if_pos ⟨rfl, rfl, rfl, rfl⟩]; exact hx
          exact (Relation.ReflTransGen.single h_step1).trans
            (bdlCylinderStepX_azimuthal_incident_connected pcode M hq sv b seg_s (Or.inr h_inc_s))
        · let xv := sv.val.1
          let b_v : Fin 2 := if b = 2 then 1 else 0
          have h_sv_outer : sv = mkOuterShellVertex pcode M xv := by
            apply Subtype.ext; exact Prod.ext rfl hr_last
          have h_xv_chk : (bdlCylinderStepX pcode M).checkX (Sum.inr (sv, b))
              (Sum.inl (Sum.inr (Sum.inr (xv, b_v)))) ≠ 0 := by
            simp only [bdlCylinderStepX_checkX]
            rw [h_sv_outer]
            dsimp [bdlStepXCheckX, bdlDeltaX0, b_v]
            fin_cases b <;> simp
          have h_step1 : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
              (Sum.inr (Sum.inr (Sum.inr eZ), b)) (Sum.inl (Sum.inr (Sum.inr (xv, b_v)))) := by
            refine ⟨?_, h_xv_chk, Sum.inr (Sum.inl (Sum.inr (eZ, b_v))), ?_, ?_⟩
            · change bdlGXQ0 pcode M (Sum.inr (sv, b)) (Sum.inr (Sum.inr eZ), b) ≠ 0
              dsimp [bdlGXQ0]; rw [if_pos ⟨hr_last, hv_eq, rfl⟩]; exact hx
            · change bdlDeltaQ1 pcode M (Sum.inr (eZ, b_v)) (Sum.inr (Sum.inr eZ), b) ≠ 0
              dsimp [bdlDeltaQ1, b_v]; fin_cases b <;> simp
            · change bdlGXQ1 pcode M (Sum.inr (eZ, b_v)) (Sum.inr (Sum.inr (xv, b_v))) ≠ 0
              dsimp [bdlGXQ1]
              have hv_xv : xv.val.2 = Sum.inr (Sum.inr eZ.val.2) := hv_eq
              rw [if_pos ⟨hv_xv, rfl⟩]; exact hx
          have h_seg0_outer : mkOuterShellSegment pcode M seg0.val.1 seg0.val.2.2 = seg0 := by
            apply Subtype.ext; apply Prod.ext; · rfl
            · apply Prod.ext
              · exact ((svIncidentSeg_start_or_end pcode M hq sv).1.trans hr_last).symm
              · rfl
          have h_step2 : XLinkStep (bdlCylinderStepX pcode M) (Sum.inr (sv, b))
              (Sum.inl (Sum.inr (Sum.inr (xv, b_v)))) q_hub := by
            refine ⟨h_xv_chk, h_hub_chk,
              Sum.inl (Sum.inr (seg0.val.1, seg0.val.2.2, b_v)), ?_, ?_⟩
            · change bdlDeltaX1 pcode M (Sum.inr (seg0.val.1, seg0.val.2.2, b_v)) (Sum.inr (Sum.inr (xv, b_v))) ≠ 0
              dsimp [bdlDeltaX1]
              have h_ne := shellSegStartVertex_ne_end pcode M seg0
              rcases h_inc0 with h_s | h_e
              · have h1 : xv = bxStartLink pcode M seg0.val.1 seg0.val.2.2 := by
                  have hs := shellSegStartVertex_outer pcode M seg0.val.1 seg0.val.2.2
                  rw [h_seg0_outer, ← h_s, h_sv_outer] at hs
                  exact congr_arg (fun w : ShellVertex pcode M => w.val.1) hs
                have h2 : xv ≠ bxEndLink pcode M seg0.val.1 seg0.val.2.2 := by
                  intro hc
                  have he := shellSegEndVertex_outer pcode M seg0.val.1 seg0.val.2.2
                  rw [h_seg0_outer, ← hc, ← h_sv_outer] at he
                  exact h_ne (h_s.symm.trans he.symm)
                have h1_eq : (Sum.inr (Sum.inr (xv, b_v)) : BDLCX1 pcode M) =
                    Sum.inr (Sum.inr (bxStartLink pcode M seg0.val.1 seg0.val.2.2, b_v)) := by rw [h1]
                have h2_ne : (Sum.inr (Sum.inr (xv, b_v)) : BDLCX1 pcode M) ≠
                    Sum.inr (Sum.inr (bxEndLink pcode M seg0.val.1 seg0.val.2.2, b_v)) := by
                  intro hc; injection hc with hc1; injection hc1 with hc2; injection hc2 with hc3 _; exact h2 hc3
                rw [if_pos h1_eq, if_neg h2_ne]; decide
              · have h2 : xv = bxEndLink pcode M seg0.val.1 seg0.val.2.2 := by
                  have he := shellSegEndVertex_outer pcode M seg0.val.1 seg0.val.2.2
                  rw [h_seg0_outer, ← h_e, h_sv_outer] at he
                  exact congr_arg (fun w : ShellVertex pcode M => w.val.1) he
                have h1 : xv ≠ bxStartLink pcode M seg0.val.1 seg0.val.2.2 := by
                  intro hc
                  have hs := shellSegStartVertex_outer pcode M seg0.val.1 seg0.val.2.2
                  rw [h_seg0_outer, ← hc, ← h_sv_outer] at hs
                  exact h_ne (hs.trans h_e)
                have h1_ne : (Sum.inr (Sum.inr (xv, b_v)) : BDLCX1 pcode M) ≠
                    Sum.inr (Sum.inr (bxStartLink pcode M seg0.val.1 seg0.val.2.2, b_v)) := by
                  intro hc; injection hc with hc1; injection hc1 with hc2; injection hc2 with hc3 _; exact h1 hc3
                have h2_eq : (Sum.inr (Sum.inr (xv, b_v)) : BDLCX1 pcode M) =
                    Sum.inr (Sum.inr (bxEndLink pcode M seg0.val.1 seg0.val.2.2, b_v)) := by rw [h2]
                rw [if_neg h1_ne, if_pos h2_eq]; decide
            · change bdlDeltaX1 pcode M (Sum.inr (seg0.val.1, seg0.val.2.2, b_v)) (Sum.inr (Sum.inl (seg0, b))) ≠ 0
              dsimp [bdlDeltaX1, b_v]
              rw [h_seg0_outer]
              fin_cases b <;> simp
          exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h_step1) h_step2
      · exact False.elim (ha rfl)

/-! ## 2. Combined Primal and Dual Link-Connectedness & Every-Qubit-Checked -/

/-- Preservation of primal and dual `HasConnectedXLinks` across `bdlRandomStepX`. -/
theorem hasConnectedXLinks_bdlRandomStepX (B : BundledCSSCode3D)
    (h_conn : HasConnectedXLinks B.code ∧ HasConnectedXLinks (dualCode B.code))
    (hq : HasNoIsolatedQ B.code) :
    HasConnectedXLinks (bdlRandomStepX B).code ∧
    HasConnectedXLinks (dualCode (bdlRandomStepX B).code) := by
  let c := bdlLLLPerturbation B
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  have hp_conn : HasConnectedXLinks pcode := h_conn.1
  have hp_dual_conn : HasConnectedXLinks (dualCode pcode) := h_conn.2
  have hp_hq : HasNoIsolatedQ pcode := hq
  exact ⟨hasConnectedXLinks_bdlCylinderStepX pcode bdlSubdivPred hp_conn hp_hq,
         hasConnectedXLinks_dual_bdlCylinderStepX pcode bdlSubdivPred hp_dual_conn hp_hq⟩

/-- Preservation of primal and dual `HasConnectedXLinks` across `bdlRandomStepZ`. -/
theorem hasConnectedXLinks_bdlRandomStepZ (B : BundledCSSCode3D)
    (h_conn : HasConnectedXLinks B.code ∧ HasConnectedXLinks (dualCode B.code))
    (hq : HasNoIsolatedQ B.code) :
    HasConnectedXLinks (bdlRandomStepZ B).code ∧
    HasConnectedXLinks (dualCode (bdlRandomStepZ B).code) := by
  have h_dual := hasConnectedXLinks_bdlRandomStepX (dualBundled B)
    ⟨h_conn.2, h_conn.1⟩ (hasNoIsolatedQ_dualCode B.code hq)
  exact ⟨h_dual.2, h_dual.1⟩

/-- Predicate asserting that every qubit in `code` participates in at least one X-check and at least one Z-check. -/
def HasEveryQubitChecked {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Prop :=
  (∀ q : Q, ∃ x : M_X, code.checkX x q ≠ 0) ∧
  (∀ q : Q, ∃ z : M_Z, code.checkZ z q ≠ 0)

/-- Symmetry of `HasEveryQubitChecked` under `dualCode`. -/
lemma hasEveryQubitChecked_dualCode {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (h : HasEveryQubitChecked code) :
    HasEveryQubitChecked (dualCode code) :=
  ⟨h.2, h.1⟩

/-- Establishes `HasEveryQubitChecked` for `bdlSurfaceSeedCode`. -/
lemma hasEveryQubitChecked_surfaceSeed : HasEveryQubitChecked bdlSurfaceSeedCode := by
  refine ⟨?_, ?_⟩ <;> intro q <;> fin_cases q <;> decide

/-- Preservation of `HasEveryQubitChecked` across `bdlCylinderStepX pcode M`. -/
lemma hasEveryQubitChecked_bdlCylinderStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h_chk : HasEveryQubitChecked pcode) :
    HasEveryQubitChecked (bdlCylinderStepX pcode M) := by
  have hq : HasNoIsolatedQ pcode :=
    ⟨fun q _ => h_chk.2 q, fun q _ => h_chk.1 q⟩
  have hq_step : HasNoIsolatedQ (bdlCylinderStepX pcode M) :=
    hasNoIsolatedQ_bdlCylinderStepX pcode M hq
  have hX : ∀ q : BDLStepXQ pcode M, ∃ mX : BDLStepXMX pcode M,
      (bdlCylinderStepX pcode M).checkX mX q ≠ 0 := by
    intro q
    rcases q with ⟨⟨rv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, b⟩⟩⟩ | ⟨v0, b⟩
    · refine ⟨Sum.inr (rv.val, b), ?_⟩
      change bdlStepXCheckX pcode M (Sum.inr (rv.val, b)) (Sum.inl (Sum.inl (rv, b))) ≠ 0
      rw [bdlDeltaX0_radial_self_eq_one]; decide
    · refine ⟨Sum.inr (shellSegStartVertex pcode M seg, b), ?_⟩
      change bdlStepXCheckX pcode M _ (Sum.inl (Sum.inr (Sum.inl (seg, b)))) ≠ 0
      rw [bdlDeltaX0_seg_start_eq_one]; decide
    · refine ⟨Sum.inr (mkOuterShellVertex pcode M xv, 0), ?_⟩
      change bdlStepXCheckX pcode M _ (Sum.inl (Sum.inr (Sum.inr (xv, b)))) ≠ 0
      rw [bdlDeltaX0_vert_eq_one]; decide
    · obtain ⟨x0, hx0⟩ := h_chk.1 (xq0OwnerQ pcode M v0)
      let xv : BoundaryX0Link pcode M :=
        ⟨(x0, projXq0ToBoundaryX0 pcode M v0), inLinkOfX_projXq0_of_checkX_ne_zero pcode M x0 v0 hx0⟩
      refine ⟨Sum.inr (mkOuterShellVertex pcode M xv, b), ?_⟩
      change bdlGXQ0 pcode M (Sum.inr (mkOuterShellVertex pcode M xv, b)) (v0, b) ≠ 0
      dsimp [bdlGXQ0, mkOuterShellVertex, xv]
      rw [if_pos ⟨rfl, rfl, rfl⟩]; exact hx0
  exact ⟨hX, fun q => hq_step.1 q (hX q)⟩

/-- Preservation of `HasEveryQubitChecked` across `bdlRandomStepX B`. -/
lemma hasEveryQubitChecked_bdlRandomStepX (B : BundledCSSCode3D)
    (h_chk : HasEveryQubitChecked B.code) :
    HasEveryQubitChecked (bdlRandomStepX B).code := by
  let c := bdlLLLPerturbation B
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  exact hasEveryQubitChecked_bdlCylinderStepX pcode bdlSubdivPred h_chk

/-- Preservation of `HasEveryQubitChecked` across `bdlRandomStepZ B`. -/
lemma hasEveryQubitChecked_bdlRandomStepZ (B : BundledCSSCode3D)
    (h_chk : HasEveryQubitChecked B.code) :
    HasEveryQubitChecked (bdlRandomStepZ B).code :=
  hasEveryQubitChecked_dualCode _
    (hasEveryQubitChecked_bdlRandomStepX (dualBundled B) (hasEveryQubitChecked_dualCode B.code h_chk))

/-- Iterated BDL bundled code after `n` full `(bdlRandomStepZ ∘ bdlRandomStepX)` pairs. -/
noncomputable def bdlIteratedBundled : ℕ → BundledCSSCode3D
  | 0 => bdlSurfaceSeedBundled
  | n + 1 => bdlRandomStepZ (bdlRandomStepX (bdlIteratedBundled n))

lemma bdlIteratedBundled_eq (n : ℕ) :
    bdlIteratedBundled n = (bdlRandomStepZ ∘ bdlRandomStepX)^[n] bdlSurfaceSeedBundled := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    dsimp [bdlIteratedBundled]
    rw [ih]

/-- Establishes `HasEveryQubitChecked (bdlIteratedBundled n).code` for all `n : ℕ`. -/
lemma hasEveryQubitChecked_bdlIterated (n : ℕ) :
    HasEveryQubitChecked (bdlIteratedBundled n).code := by
  induction n with
  | zero => exact hasEveryQubitChecked_surfaceSeed
  | succ m ih =>
    dsimp only [bdlIteratedBundled]
    exact hasEveryQubitChecked_bdlRandomStepZ _
      (hasEveryQubitChecked_bdlRandomStepX (bdlIteratedBundled m) ih)

/-- Establishes `HasNoIsolatedQ (bdlIteratedBundled n).code` for all `n : ℕ`. -/
lemma hasNoIsolatedQ_bdlIterated (n : ℕ) :
    HasNoIsolatedQ (bdlIteratedBundled n).code := by
  rw [bdlIteratedBundled_eq]
  exact hasNoIsolatedQ_iterate_stepZX n

/-- Establishes primal and dual `HasConnectedXLinks` for `(bdlIteratedBundled n).code` for all `n : ℕ`. -/
lemma hasConnectedXLinks_bdlIterated (n : ℕ) :
    HasConnectedXLinks (bdlIteratedBundled n).code ∧
    HasConnectedXLinks (dualCode (bdlIteratedBundled n).code) := by
  induction n with
  | zero => exact hasConnectedXLinks_surfaceSeed
  | succ m ih =>
    dsimp only [bdlIteratedBundled]
    have hq_m : HasNoIsolatedQ (bdlIteratedBundled m).code := hasNoIsolatedQ_bdlIterated m
    have hq_X : HasNoIsolatedQ (bdlRandomStepX (bdlIteratedBundled m)).code :=
      hasNoIsolatedQ_bdlCylinderStepX _ bdlSubdivPred hq_m
    exact hasConnectedXLinks_bdlRandomStepZ _ (hasConnectedXLinks_bdlRandomStepX _ ih hq_m) hq_X

end WeldedHierarchy
