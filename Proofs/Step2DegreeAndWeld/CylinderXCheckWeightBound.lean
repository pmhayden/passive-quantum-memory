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

import Proofs.Step2DegreeAndWeld.ShellVertexCheckSectorBounds

/-!
# Uniform X-Check Qubit Weight Bound for Three-Layer Cylinder Welding

Combines apex $X$-check degree bounds and shell-vertex sector support bounds to prove `card_filter_bdlStepXCheckX_q1_le`, showing that every $X$-check under `bdlStepXCheckX` has qubit weight at most 8 whenever input $X$-checks have weight at most 8 and input $X$/$Z$-check overlap is at most 2. Also proves the two-plaquette azimuthal coboundary support helper `bdlDeltaX1_inr_inl_ne_zero_imp2`.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Equation (4) (`eq:dx-coboundary`), Equation (8) (`eq:Psi-XQ-def`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Total X-Check Qubit Weight Bound (≤ 8) Across Apex and Shell Sectors -/

lemma card_filter_bdlStepXCheckX_q1_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdX : ∀ x : M_X, (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0)).card ≤ 8)
    (hdQZ : ∀ q : Q, (Finset.univ.filter (fun z : M_Z => pcode.checkZ z q ≠ 0)).card ≤ 4)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (mX : BDLStepXMX pcode M) :
    (Finset.univ.filter (fun q1 : BDLStepXQ pcode M => bdlStepXCheckX pcode M mX q1 ≠ 0)).card ≤ 8 := by
  rw [card_filter_sum_eq']
  -- Step 1: Case split on coarse apex X-checks (x0, b0) vs. shell-vertex X-checks (sv0, b0).
  rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
  · have h_cq1 : (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
        bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inr qQ) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
    rw [card_filter_sum_eq']
    have h_cx1_inr : (Finset.univ.filter (fun rest : (ShellSegment pcode M × Fin 3) ⊕ (BoundaryX0Link pcode M × Fin 2) =>
        bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inl (Sum.inr rest)) ≠ 0)).card = 0 := by
      apply card_filter_eq_zero_of_imp_false
      intro rest h
      rcases rest with _ | _ <;> exact h rfl
    have h_cx1_inl : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
        bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inl (Sum.inl p)) ≠ 0)).card ≤ 8 := by
      have h_inj_v : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
          bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inl (Sum.inl p)) ≠ 0)).card ≤
          (Finset.univ.filter (fun v : BoundaryX0 pcode M =>
            match v with | Sum.inl q => pcode.checkX x0 q ≠ 0 | Sum.inr _ => False)).card := by
        refine card_filter_le_of_injOn_filter _ _ (fun p => p.1.val.val.1.val.2) ?_ ?_
        · intro ⟨⟨sv, h_nd⟩, b⟩ hp
          dsimp only at hp ⊢
          unfold bdlStepXCheckX bdlDeltaX0 at hp; dsimp only at hp
          by_cases hr0 : sv.val.2.val = 0
          · rw [if_pos hr0] at hp
            rcases add_ite_one_ne_zero_imp hp with hc | hc <;> [skip; injection hc]
            injection hc with hc; injection hc with hx hb
            rcases hv : sv.val.1.val.2 with q | ⟨⟨eZ, j⟩ | z⟩
            · have h_link := sv.val.1.property
              rw [hv, ← hx] at h_link
              exact h_link
            · have h_in := sv.property
              dsimp [InShellR] at h_in
              rw [hv] at h_in
              omega
            · exact False.elim (h_nd ⟨hr0, z, hv⟩)
          · rw [if_neg hr0] at hp
            rcases add_ite_one_ne_zero_imp hp with hc | hc <;> injection hc
        · intro ⟨⟨sv1, h_nd1⟩, b1⟩ hp1 ⟨⟨sv2, h_nd2⟩, b2⟩ hp2 h_eq
          dsimp only at hp1 hp2 h_eq
          unfold bdlStepXCheckX bdlDeltaX0 at hp1 hp2; dsimp only at hp1 hp2
          by_cases hr1 : sv1.val.2.val = 0
          · rw [if_pos hr1] at hp1
            by_cases hr2 : sv2.val.2.val = 0
            · rw [if_pos hr2] at hp2
              rcases add_ite_one_ne_zero_imp hp1 with hc1 | hc1 <;> [skip; injection hc1]
              rcases add_ite_one_ne_zero_imp hp2 with hc2 | hc2 <;> [skip; injection hc2]
              injection hc1 with hc1; injection hc1 with hx1 hb1
              injection hc2 with hc2; injection hc2 with hx2 hb2
              have h_xv : sv1.val.1 = sv2.val.1 := Subtype.ext (Prod.ext (hx1.symm.trans hx2) h_eq)
              exact Prod.ext (Subtype.ext (Subtype.ext (Prod.ext h_xv (Fin.ext (by dsimp only; omega))))) (hb1.symm.trans hb2)
            · rw [if_neg hr2] at hp2
              rcases add_ite_one_ne_zero_imp hp2 with hc2 | hc2 <;> injection hc2
          · rw [if_neg hr1] at hp1
            rcases add_ite_one_ne_zero_imp hp1 with hc1 | hc1 <;> injection hc1
      rw [card_filter_sum_eq', card_filter_eq_zero_of_imp_false _ (fun _ h => h), add_zero] at h_inj_v
      exact h_inj_v.trans (hdX x0)
    omega
  -- Step 2: For shell-vertex X-checks, decompose support into radial, azimuthal, vertical, and BDLCQ1.
  · rw [card_filter_sum_eq', card_filter_sum_eq']
    have h_rad_eq : (Finset.univ.filter (fun a : RadialVertex pcode M × Fin 3 =>
        bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inl (Sum.inl a)) ≠ 0)).card ≤
      (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
        p = (sv0, b0) ∨ (p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0))).card := by
      refine card_filter_le_of_injOn_filter _ _ (fun a => (a.1.val, a.2)) ?_ ?_
      · intro a ha
        exact bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b0 a ha
      · intro ⟨rv1, b1⟩ _ ⟨rv2, b2⟩ _ h_eq
        injection h_eq with h1 h2
        exact Prod.ext (Subtype.ext h1) h2
    have h_azim_eq : (Finset.univ.filter (fun a : ShellSegment pcode M × Fin 3 =>
        bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inl (Sum.inr (Sum.inl a))) ≠ 0)).card =
      (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
        bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inl p)) ≠ 0)).card :=
      card_filter_iff _ _ (fun _ => Iff.rfl)
    have h_vert_eq : (Finset.univ.filter (fun b : BoundaryX0Link pcode M × Fin 2 =>
        bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inl (Sum.inr (Sum.inr b))) ≠ 0)).card =
      (Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin 2 =>
        bdlDeltaX0 pcode M (Sum.inr (sv0, b0)) (Sum.inr (Sum.inr p)) ≠ 0)).card :=
      card_filter_iff _ _ (fun _ => Iff.rfl)
    have h_cq1_eq : (Finset.univ.filter (fun b : BDLCQ1 pcode M =>
        bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inr b) ≠ 0)).card =
      (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
        bdlGXQ0 pcode M (Sum.inr (sv0, b0)) qQ ≠ 0)).card :=
      card_filter_iff _ _ (fun _ => Iff.rfl)
    have h_rad_split := card_filter_le_add_of_or
      (fun p : ShellVertex pcode M × Fin 3 =>
        p = (sv0, b0) ∨ (p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0))
      (fun p => p = (sv0, b0))
      (fun p => p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0)
      (fun _ h => h)
    have h_self : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 => p = (sv0, b0))).card ≤ 1 :=
      card_filter_le_one_of_unique _ (fun _ h1 _ h2 => h1.trans h2.symm)
  -- Step 3: Bound total weight across the three link sectors (qubit ≤ 7, Z-arm ≤ 7, Z-check ≤ 7).
    rcases hv0 : sv0.val.1.val.2 with q0 | ⟨⟨eZ0, j0⟩ | z0⟩
    · have h_not_z : ∀ z : M_Z, sv0.val.1.val.2 ≠ Sum.inr (Sum.inr z) := by
        intro z hz; rw [hv0] at hz; injection hz
      have h_azim := card_filter_bdlDeltaX0_azim_inl_le_four pcode M hdQZ sv0 b0 q0 hv0
      by_cases h_last : sv0.val.2 = Fin.last M
      · have h_child : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
            p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0)).card = 0 :=
          card_filter_eq_zero_of_imp_false _ (fun p ⟨hr, hpar, _⟩ =>
            radialParentVertex_ne_of_last pcode M p.1 sv0 hr h_last hpar)
        have h_vert := card_filter_bdlDeltaX0_vert_le_two pcode M sv0 b0
        have h_cq1 := card_filter_bdlGXQ0_le_one_of_ne_inr_inr pcode M sv0 b0 h_not_z
        omega
      · have h_child : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
            p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨sv1, b1⟩ ⟨hr1, hpar1, hb1⟩ ⟨sv2, b2⟩ ⟨hr2, hpar2, hb2⟩
          dsimp only at hr1 hpar1 hb1 hr2 hpar2 hb2
          have hv1 : sv1.val.1.val.2 = sv0.val.1.val.2 :=
            radialParentV_eq_imp_eq_of_ne_inr_inr pcode M sv1.val.1.val.2 sv0.val.1.val.2 sv1.val.2 h_not_z
              (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hpar1)
          have hv2 : sv2.val.1.val.2 = sv0.val.1.val.2 :=
            radialParentV_eq_imp_eq_of_ne_inr_inr pcode M sv2.val.1.val.2 sv0.val.1.val.2 sv2.val.2 h_not_z
              (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hpar2)
          have hx1 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar1
          have hx2 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar2
          have hfp1 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar1
          have hfp2 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar2
          dsimp [radialParentVertex, finPred] at hfp1 hfp2
          have h_xv : sv1.val.1 = sv2.val.1 := Subtype.ext (Prod.ext (hx1.trans hx2.symm) (hv1.trans hv2.symm))
          exact Prod.ext (Subtype.ext (Prod.ext h_xv (Fin.ext (by dsimp only; omega)))) (hb1.trans hb2.symm)
        have h_vert := card_filter_bdlDeltaX0_vert_eq_zero_of_ne_last pcode M sv0 b0 h_last
        have h_cq1 := card_filter_bdlGXQ0_eq_zero_of_ne_last pcode M sv0 b0 h_last
        omega
    · have h_not_z : ∀ z : M_Z, sv0.val.1.val.2 ≠ Sum.inr (Sum.inr z) := by
        intro z hz; rw [hv0] at hz; injection hz with hz; injection hz
      have h_azim := card_filter_bdlDeltaX0_azim_inr_inl_le_two pcode M sv0 b0 eZ0 j0 hv0
      have h_child : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
           p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0)).card ≤ 1 := by
        apply card_filter_le_one_of_unique
        intro ⟨sv1, b1⟩ ⟨hr1, hpar1, hb1⟩ ⟨sv2, b2⟩ ⟨hr2, hpar2, hb2⟩
        dsimp only at hr1 hpar1 hb1 hr2 hpar2 hb2
        have hv1 : sv1.val.1.val.2 = sv0.val.1.val.2 :=
          radialParentV_eq_imp_eq_of_ne_inr_inr pcode M sv1.val.1.val.2 sv0.val.1.val.2 sv1.val.2 h_not_z
            (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hpar1)
        have hv2 : sv2.val.1.val.2 = sv0.val.1.val.2 :=
          radialParentV_eq_imp_eq_of_ne_inr_inr pcode M sv2.val.1.val.2 sv0.val.1.val.2 sv2.val.2 h_not_z
            (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hpar2)
        have hx1 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar1
        have hx2 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar2
        have hfp1 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar1
        have hfp2 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar2
        dsimp [radialParentVertex, finPred] at hfp1 hfp2
        have h_xv : sv1.val.1 = sv2.val.1 := Subtype.ext (Prod.ext (hx1.trans hx2.symm) (hv1.trans hv2.symm))
        exact Prod.ext (Subtype.ext (Prod.ext h_xv (Fin.ext (by dsimp only; omega)))) (hb1.trans hb2.symm)
      have h_vert := card_filter_bdlDeltaX0_vert_le_two pcode M sv0 b0
      have h_cq1 := card_filter_bdlGXQ0_le_one_of_ne_inr_inr pcode M sv0 b0 h_not_z
      omega
    · have h_azim := card_filter_bdlDeltaX0_azim_inr_inr_le_two pcode M hov sv0 b0 z0 hv0
      by_cases h_last : sv0.val.2 = Fin.last M
      · have h_child : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
            p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0)).card = 0 :=
          card_filter_eq_zero_of_imp_false _ (fun p ⟨hr, hpar, _⟩ =>
            radialParentVertex_ne_of_last pcode M p.1 sv0 hr h_last hpar)
        have h_vert := card_filter_bdlDeltaX0_vert_le_two pcode M sv0 b0
        have h_cq1 := card_filter_bdlGXQ0_le_two_of_inr_inr pcode M sv0 b0 z0 hov hv0
        omega
      · have h_child_split := card_filter_le_add_of_or
          (fun p : ShellVertex pcode M × Fin 3 =>
            p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0)
          (fun p => p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0 ∧
            p.1.val.1.val.2 = Sum.inr (Sum.inr z0))
          (fun p => p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0 ∧
            p.1.val.1.val.2 ≠ Sum.inr (Sum.inr z0))
          (fun p hp => by
            by_cases hz : p.1.val.1.val.2 = Sum.inr (Sum.inr z0)
            · exact Or.inl ⟨hp.1, hp.2.1, hp.2.2, hz⟩
            · exact Or.inr ⟨hp.1, hp.2.1, hp.2.2, hz⟩)
        have h_child_z : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
            p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0 ∧
            p.1.val.1.val.2 = Sum.inr (Sum.inr z0))).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨sv1, b1⟩ ⟨hr1, hpar1, hb1, hz1⟩ ⟨sv2, b2⟩ ⟨hr2, hpar2, hb2, hz2⟩
          dsimp only at hr1 hpar1 hb1 hz1 hr2 hpar2 hb2 hz2
          have hx1 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar1
          have hx2 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar2
          have hfp1 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar1
          have hfp2 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar2
          dsimp [radialParentVertex, finPred] at hfp1 hfp2
          have h_xv : sv1.val.1 = sv2.val.1 := Subtype.ext (Prod.ext (hx1.trans hx2.symm) (hz1.trans hz2.symm))
          exact Prod.ext (Subtype.ext (Prod.ext h_xv (Fin.ext (by dsimp only; omega)))) (hb1.trans hb2.symm)
        have h_child_eZ : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
            p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0 ∧
            p.1.val.1.val.2 ≠ Sum.inr (Sum.inr z0))).card ≤ 2 := by
          have h_inj_v : (Finset.univ.filter (fun p : ShellVertex pcode M × Fin 3 =>
              p.1.val.2.val ≠ 0 ∧ radialParentVertex pcode M p.1 = sv0 ∧ p.2 = b0 ∧
              p.1.val.1.val.2 ≠ Sum.inr (Sum.inr z0))).card ≤
              (Finset.univ.filter (fun v : BoundaryX0 pcode M =>
                match v with
                | Sum.inl q => pcode.checkX sv0.val.1.val.1 q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0
                | Sum.inr _ => False)).card := by
            refine card_filter_le_of_injOn_filter _ _
              (fun p => match p.1.val.1.val.2 with
                | Sum.inr (Sum.inl (eZ, _)) => Sum.inl eZ.val.1
                | v => v) ?_ ?_
            · intro ⟨sv, b⟩ ⟨hr, hpar, _, hne_z⟩
              dsimp only at hr hpar hne_z ⊢
              have hv_par := (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hpar).trans hv0
              have hx := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar
              dsimp [radialParentVertex, radialParentLink] at hv_par hx
              rcases hv : sv.val.1.val.2 with q | ⟨⟨eZ, j⟩ | z⟩ <;> rw [hv] at hv_par hne_z
              · injection hv_par
              · dsimp [radialParentV] at hv_par
                split_ifs at hv_par with hj <;> [(injection hv_par with hv_par; injection hv_par); skip]
                injection hv_par with hv_par; injection hv_par with hz_eq
                have h_link := sv.val.1.property
                rw [hv, hx] at h_link
                exact ⟨h_link, hz_eq ▸ eZ.property⟩
              · exact False.elim (hne_z (congr_arg (fun z => Sum.inr (Sum.inr z)) (by injection hv_par with h1; injection h1)))
            · intro ⟨sv1, b1⟩ ⟨hr1, hpar1, hb1, hne1⟩ ⟨sv2, b2⟩ ⟨hr2, hpar2, hb2, hne2⟩ h_eq
              dsimp only at hr1 hpar1 hb1 hne1 hr2 hpar2 hb2 hne2 h_eq
              have hv_par1 := (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hpar1).trans hv0
              have hv_par2 := (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hpar2).trans hv0
              dsimp [radialParentVertex, radialParentLink] at hv_par1 hv_par2
              rcases hv1 : sv1.val.1.val.2 with _ | ⟨⟨eZ1, j1⟩ | z1⟩ <;> rw [hv1] at hv_par1 hne1 h_eq
              · injection hv_par1
              · rcases hv2 : sv2.val.1.val.2 with _ | ⟨⟨eZ2, j2⟩ | z2⟩ <;> rw [hv2] at hv_par2 hne2 h_eq
                · injection hv_par2
                · dsimp [radialParentV] at hv_par1 hv_par2
                  split_ifs at hv_par1 with hj1 <;> [(injection hv_par1 with h; injection h); skip]
                  split_ifs at hv_par2 with hj2 <;> [(injection hv_par2 with h; injection h); skip]
                  injection hv_par1 with h; injection h with hz1
                  injection hv_par2 with h; injection h with hz2
                  injection h_eq with hq_eq
                  have h_in1 := sv1.property; have h_in2 := sv2.property
                  dsimp [InShellR] at h_in1 h_in2
                  rw [hv1] at h_in1; rw [hv2] at h_in2
                  have hfp1 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar1
                  have hfp2 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar2
                  dsimp [radialParentVertex, finPred] at hfp1 hfp2 hj1 hj2
                  have hj_eq : j1 = j2 := Fin.ext (by omega)
                  have heZ_eq : eZ1 = eZ2 := Subtype.ext (Prod.ext hq_eq (hz1.trans hz2.symm))
                  have hx1 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar1
                  have hx2 := congr_arg (fun s : ShellVertex pcode M => s.val.1.val.1) hpar2
                  dsimp [radialParentVertex, radialParentLink] at hx1 hx2
                  have h_xv : sv1.val.1 = sv2.val.1 := Subtype.ext (Prod.ext (hx1.trans hx2.symm)
                    (hv1.trans (congr_arg (fun p => Sum.inr (Sum.inl p)) (Prod.ext heZ_eq hj_eq) |>.trans hv2.symm)))
                  exact Prod.ext (Subtype.ext (Prod.ext h_xv (Fin.ext (by dsimp only; omega)))) (hb1.trans hb2.symm)
                · exact False.elim (hne2 (congr_arg (fun z => Sum.inr (Sum.inr z)) (by injection hv_par2 with h1; injection h1)))
              · exact False.elim (hne1 (congr_arg (fun z => Sum.inr (Sum.inr z)) (by injection hv_par1 with h1; injection h1)))
          rw [card_filter_sum_eq', card_filter_eq_zero_of_imp_false _ (fun _ h => h), add_zero] at h_inj_v
          exact h_inj_v.trans (hov sv0.val.1.val.1 z0)
        have h_vert := card_filter_bdlDeltaX0_vert_eq_zero_of_ne_last pcode M sv0 b0 h_last
        have h_cq1 := card_filter_bdlGXQ0_eq_zero_of_ne_last pcode M sv0 b0 h_last
        omega

/-! ## 2. Azimuthal Segment Support Characterization for bdlDeltaX1 -/

lemma bdlDeltaX1_inr_inl_ne_zero_imp2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (seg : ShellSegment pcode M) (b : Fin 3) (seg0 : ShellSegment pcode M) (b0 : Fin 3)
    (hne : bdlDeltaX1 pcode M (Sum.inl (seg, b)) (Sum.inr (Sum.inl (seg0, b0))) ≠ 0) :
    True ∧ b = b0 ∧
    ((seg.val.2.1.val = 0 ∧
      ∃ (q' : Q) (hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0) (hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0),
        seg0 = cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ') ∨
     (seg.val.2.1.val ≠ 0 ∧
      (seg = seg0 ∨ ∃ h_tri : seg.val.2.2.val ≠ seg.val.2.1.val, shellSegPred pcode M seg h_tri = seg0))) := by
  by_cases hr0 : seg.val.2.1.val = 0
  · obtain ⟨_, q', hX', hZ', h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inr (Sum.inl (seg0, b0))) hne
    rcases h_or with h_eq | h_eq
    · injection h_eq
    · injection h_eq with h_eq; injection h_eq with hp; injection hp with hseg hb
      exact ⟨trivial, hb.symm, Or.inl ⟨hr0, q', hX', hZ', hseg⟩⟩
  · rcases bdlDeltaX1_inr_inl_ne_zero_imp pcode M seg b seg0 b0 hne with ⟨hb, ⟨hr0', _⟩ | ⟨_, hseg⟩⟩ | ⟨hb, h_tri, hpred⟩
    · exact False.elim (hr0 hr0')
    · exact ⟨trivial, hb, Or.inr ⟨hr0, Or.inl hseg⟩⟩
    · exact ⟨trivial, hb, Or.inr ⟨hr0, Or.inr ⟨h_tri, hpred⟩⟩⟩

end WeldedHierarchy
