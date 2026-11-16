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

import Proofs.Step2DegreeAndWeld.CylinderXCheckWeightBound

/-!
# Shared-Support Overlap Bound for Shell-Plaquette and Outer-Boundary Z-Checks

Proves `card_filter_bdlStepX_overlap_seg_le_two` and `card_filter_bdlStepX_overlap_outer_le_two`, showing that any $X$-check (`bdlStepXCheckX`) and any interior shell-plaquette or outer-boundary link $Z$-check (`bdlStepXCheckZ`) in the three-layer cylinder welding step share at most two qubits in their common support.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Equation (4) (`eq:dx-coboundary`), Equation (8) (`eq:Psi-XQ-def`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Interior Shell-Segment Z-Check Overlap Bound (≤ 2) -/

set_option maxHeartbeats 800000 in
/-- **Cylinder Shared-Check Overlap Bound (Interior Shell Segment $Z$-Checks)**:
    For any $X$-check $m_X$ and any shell-segment $Z$-check `Sum.inl (Sum.inl (seg, b))`,
    at most $2$ qubits in `BDLStepXQ pcode M` lie in the support of both checks. -/
lemma card_filter_bdlStepX_overlap_seg_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (mX : BDLStepXMX pcode M) (seg : ShellSegment pcode M) (b : Fin 3) :
    (Finset.univ.filter (fun q1 : BDLStepXQ pcode M =>
      bdlStepXCheckX pcode M mX q1 ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) q1 ≠ 0)).card ≤ 2 := by
  -- Step 1: Vanish BDLCQ1 and vertical boundary sectors for shell-segment Z-checks.
  rw [card_filter_sum_eq']
  have h_cq1 : (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
      bdlStepXCheckX pcode M mX (Sum.inr qQ) ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inr qQ) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun _ h => h.2 rfl)
  rw [card_filter_sum_eq', card_filter_sum_eq']
  have h_vert : (Finset.univ.filter (fun xv : BoundaryX0Link pcode M × Fin 2 =>
      bdlStepXCheckX pcode M mX (Sum.inl (Sum.inr (Sum.inr xv))) ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inr (Sum.inr xv))) ≠ 0)).card = 0 := by
    apply card_filter_eq_zero_of_imp_false
    intro xv ⟨_, hZ⟩
    by_cases hr0 : seg.val.2.1.val = 0
    · obtain ⟨_, _, _, _, h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inr (Sum.inr xv)) hZ
      rcases h_or with h | h
      · injection h
      · injection h with h; injection h
    · unfold bdlStepXCheckZ bdlDeltaX1 at hZ; dsimp only at hZ
      by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
      · rw [dif_pos h_tri, dif_neg hr0] at hZ
        rcases add_ne_zero_imp hZ with h12 | h3
        · rcases add_ne_zero_imp h12 with h1 | h2
          · have h := ite_one_ne_zero_imp h1; injection h
          · have h := ite_one_ne_zero_imp h2; injection h
        · have h := ite_one_ne_zero_imp h3; injection h with h; injection h
      · rw [dif_neg h_tri] at hZ
        rcases add_ne_zero_imp hZ with h123 | h4
        · rcases add_ne_zero_imp h123 with h12 | h3
          · rcases add_ne_zero_imp h12 with h1 | h2
            · have h := ite_one_ne_zero_imp h1; injection h
            · have h := ite_one_ne_zero_imp h2; injection h
          · have h := ite_one_ne_zero_imp h3; injection h with h; injection h
        · have h := ite_one_ne_zero_imp h4; injection h with h; injection h
  -- Step 2: Split on innermost shell r = 0 vs. interior shells r > 0.
  by_cases hr0 : seg.val.2.1.val = 0
  · rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
    · have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
          bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0 ∧
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0)).card = 0 :=
        card_filter_eq_zero_of_imp_false _ (fun _ h => h.1 rfl)
      have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
          bdlStepXCheckX pcode M (Sum.inl (x0, b0)) (Sum.inl (Sum.inl p)) ≠ 0 ∧
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inl p)) ≠ 0)).card ≤ 2 := by
        refine (card_filter_le_of_injOn_filter _
          (fun q' : Q => pcode.checkX seg.val.1.val.1 q' ≠ 0 ∧ pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0)
          (fun p => match p.1.val.val.1.val.2 with | Sum.inl q => q | _ => seg.val.1.val.2.val.1)
          ?_ ?_).trans (hov seg.val.1.val.1 seg.val.1.val.2.val.2)
        · intro p ⟨_, hp⟩
          obtain ⟨_, q', hX', hZ', h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p) hp
          rcases h_or with h | h <;> [skip; injection h]
          injection h with hp_eq
          rcases p with ⟨sv, bX⟩; injection hp_eq with hsv _
          subst hsv; dsimp [cornerSpokeRadial, cornerSpoke]; exact ⟨hX', hZ'⟩
        · intro p1 ⟨_, hp1⟩ p2 ⟨_, hp2⟩ h_eq
          obtain ⟨_, q1, hX1, _, h_or1⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p1) hp1
          obtain ⟨_, q2, hX2, _, h_or2⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p2) hp2
          rcases h_or1 with h1 | h1 <;> [skip; injection h1]
          rcases h_or2 with h2 | h2 <;> [skip; injection h2]
          injection h1 with hp1_eq; injection h2 with hp2_eq
          rcases p1 with ⟨sv1, b1⟩; rcases p2 with ⟨sv2, b2⟩
          injection hp1_eq with hsv1 hb1; injection hp2_eq with hsv2 hb2
          subst hsv1 hb1 hsv2 hb2; dsimp [cornerSpokeRadial, cornerSpoke] at h_eq; subst h_eq; rfl
      omega
    · by_cases h_inl : ∃ q0 : Q, sv0.val.1.val.2 = Sum.inl q0
      · obtain ⟨q0, hq0⟩ := h_inl
        have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
             bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inl (Sum.inl p)) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inl p)) ≠ 0)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro p1 ⟨hX1, hZ1⟩ p2 ⟨hX2, hZ2⟩
          obtain ⟨_, q1, hXq1, _, h_or1⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p1) hZ1
          obtain ⟨_, q2, hXq2, _, h_or2⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p2) hZ2
          rcases h_or1 with h1 | h1 <;> [skip; injection h1]
          rcases h_or2 with h2 | h2 <;> [skip; injection h2]
          injection h1 with hp1_eq; injection h2 with hp2_eq
          have hrp1 : p1.1.val.val.2.val = 0 := by rw [hp1_eq]; rfl
          have hrp2 : p2.1.val.val.2.val = 0 := by rw [hp2_eq]; rfl
          rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b0 p1 hX1 with heq1 | ⟨hne1, _⟩
          · rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b0 p2 hX2 with heq2 | ⟨hne2, _⟩
            · have h_val := heq1.trans heq2.symm
              injection h_val with h1 h2
              exact Prod.ext (Subtype.ext h1) h2
            · exact False.elim (hne2 hrp2)
          · exact False.elim (hne1 hrp1)
        have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
             bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨seg1, b1⟩ ⟨hX1, hZ1⟩ ⟨seg2, b2⟩ ⟨hX2, hZ2⟩
          unfold bdlStepXCheckX bdlDeltaX0 at hX1 hX2; dsimp only at hX1 hX2
          obtain ⟨_, h_b1, h_or1⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg1 b1 hZ1
          obtain ⟨_, h_b2, h_or2⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg2 b2 hZ2
          rcases h_or1 with ⟨_, q1, hXq1, hZq1, hseg1⟩ | ⟨hne1, _⟩ <;> [skip; exact False.elim (hne1 hr0)]
          rcases h_or2 with ⟨_, q2, hXq2, hZq2, hseg2⟩ | ⟨hne2, _⟩ <;> [skip; exact False.elim (hne2 hr0)]
          rcases add_ite_one_ne_zero_imp hX1 with hs1 | he1 <;>
            [skip; (injection he1 with he1; injection he1 with hsv1 _;
                    exact False.elim (shellSegEndV_ne_inl pcode M seg1 q0
                      ((congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).symm.trans hq0)))]
          rcases add_ite_one_ne_zero_imp hX2 with hs2 | he2 <;>
            [skip; (injection he2 with he2; injection he2 with hsv2 _;
                    exact False.elim (shellSegEndV_ne_inl pcode M seg2 q0
                      ((congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).symm.trans hq0)))]
          injection hs1 with hs1; injection hs1 with hsv1 _
          injection hs2 with hs2; injection hs2 with hsv2 _
          have hv1 : bxStart pcode M seg1.val.1.val.2 seg1.val.2.2 = Sum.inl q0 :=
            (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv1).symm.trans hq0
          have hv2 : bxStart pcode M seg2.val.1.val.2 seg2.val.2.2 = Sum.inl q0 :=
            (congr_arg (fun s : ShellVertex pcode M => s.val.1.val.2) hsv2).symm.trans hq0
          rw [hseg1] at hv1; rw [hseg2] at hv2
          dsimp [cornerSeg, bxStart, armStart, projXq0ToBoundaryX0] at hv1 hv2
          injection hv1 with hq1_eq; injection hv2 with hq2_eq
          subst hq1_eq hq2_eq
          exact Prod.ext (hseg1.trans hseg2.symm) (h_b1.symm.trans h_b2)
        omega
      · have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
             bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inl (Sum.inl p)) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inl p)) ≠ 0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro p ⟨hX, hZ⟩
          obtain ⟨_, q', hX', _, h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p) hZ
          rcases h_or with h | h <;> [skip; injection h]
          injection h with hp_eq
          have hrp : p.1.val.val.2.val = 0 := by rw [hp_eq]; rfl
          rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b0 p hX with heq | ⟨hne, _⟩
          · have hv : sv0.val.1.val.2 = Sum.inl q' := by
              have := congr_arg (fun x : ShellVertex pcode M × Fin 3 => x.1.val.1.val.2)
                (heq.symm.trans (congr_arg (fun a : RadialVertex pcode M × Fin 3 => (a.1.val, a.2)) hp_eq))
              exact this
            exact h_inl ⟨q', hv⟩
          · exact hne hrp
        have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
             bdlStepXCheckX pcode M (Sum.inr (sv0, b0)) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0)).card ≤ 2 := by
          refine (card_filter_le_of_injOn_filter _
            (fun q' : Q => pcode.checkX seg.val.1.val.1 q' ≠ 0 ∧ pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0)
            (fun p => p.1.val.1.val.2.val.1) ?_ ?_).trans (hov seg.val.1.val.1 seg.val.1.val.2.val.2)
          · intro ⟨seg', b'⟩ ⟨_, hZ⟩
            obtain ⟨_, _, h_or⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg' b' hZ
            rcases h_or with ⟨_, q', hX', hZ', hseg'⟩ | ⟨hne, _⟩ <;> [skip; exact False.elim (hne hr0)]
            rw [hseg']; exact ⟨hX', hZ'⟩
          · intro ⟨seg1, b1⟩ ⟨_, hZ1⟩ ⟨seg2, b2⟩ ⟨_, hZ2⟩ h_eq
            obtain ⟨_, hb1, h_or1⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg1 b1 hZ1
            obtain ⟨_, hb2, h_or2⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg2 b2 hZ2
            rcases h_or1 with ⟨_, q1, hX1, hZ1', hseg1⟩ | ⟨hne1, _⟩ <;> [skip; exact False.elim (hne1 hr0)]
            rcases h_or2 with ⟨_, q2, hX2, hZ2', hseg2⟩ | ⟨hne2, _⟩ <;> [skip; exact False.elim (hne2 hr0)]
            rw [hseg1, hseg2] at h_eq
            dsimp [cornerSeg] at h_eq
            subst h_eq
            exact Prod.ext (hseg1.trans hseg2.symm) (hb1.symm.trans hb2)
        omega
  -- Step 3: For r > 0, split on triangular (k = r) vs. non-triangular (k < r) shell segments.
  · by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · by_cases h_mX_same : ∃ sv0 : ShellVertex pcode M, mX = Sum.inr (sv0, b) ∧ sv0.val.2 = seg.val.2.1
      · obtain ⟨sv0, rfl, hsv0_r⟩ := h_mX_same
        have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
             bdlStepXCheckX pcode M (Sum.inr (sv0, b)) (Sum.inl (Sum.inl p)) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inl p)) ≠ 0)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨rv1, b1⟩ ⟨hX1, hZ1⟩ ⟨rv2, b2⟩ ⟨hX2, hZ2⟩
          obtain ⟨hr1, _, _⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv1 b1 hZ1
          obtain ⟨hr2, _, _⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv2 b2 hZ2
          rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b (rv1, b1) hX1 with heq1 | ⟨hne1, hpar1, _⟩
          · rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b (rv2, b2) hX2 with heq2 | ⟨hne2, hpar2, _⟩
            · have h_val := heq1.trans heq2.symm
              injection h_val with h1 h2
              exact Prod.ext (Subtype.ext h1) h2
            · dsimp only at hpar2
              have hfp2 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar2
              dsimp [radialParentVertex, finPred] at hfp2
              have hr2_val : seg.val.2.1.val = rv2.val.val.2.val := congr_arg Fin.val hr2
              have hsv0_val : sv0.val.2.val = seg.val.2.1.val := congr_arg Fin.val hsv0_r
              omega
          · dsimp only at hpar1
            have hfp1 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar1
            dsimp [radialParentVertex, finPred] at hfp1
            have hr1_val : seg.val.2.1.val = rv1.val.val.2.val := congr_arg Fin.val hr1
            have hsv0_val : sv0.val.2.val = seg.val.2.1.val := congr_arg Fin.val hsv0_r
            omega
        have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
             bdlStepXCheckX pcode M (Sum.inr (sv0, b)) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨seg1, b1⟩ ⟨_, hZ1⟩ ⟨seg2, b2⟩ ⟨_, hZ2⟩
          obtain ⟨_, hb1, h_or1⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg1 b1 hZ1
          obtain ⟨_, hb2, h_or2⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg2 b2 hZ2
          rcases h_or1 with ⟨hr0', _⟩ | ⟨_, hseg1 | ⟨hne1, _⟩⟩
          · exact False.elim (hr0 hr0')
          · rcases h_or2 with ⟨hr0', _⟩ | ⟨_, hseg2 | ⟨hne2, _⟩⟩
            · exact False.elim (hr0 hr0')
            · exact Prod.ext (hseg1.symm.trans hseg2) (hb1.symm.trans hb2)
            · exact False.elim (hne2 h_tri)
          · exact False.elim (hne1 h_tri)
        omega
      · have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
             bdlStepXCheckX pcode M mX (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨seg', b'⟩ ⟨hX, hZ⟩
          obtain ⟨_, hb', h_or⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg' b' hZ
          rcases h_or with ⟨hr0', _⟩ | ⟨_, hseg' | ⟨hne, _⟩⟩
          · exact hr0 hr0'
          · subst hb' hseg'
            rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
            · exact hX rfl
            · unfold bdlStepXCheckX bdlDeltaX0 at hX; dsimp only at hX
              rcases add_ite_one_ne_zero_imp hX with hs | he
              · exact h_mX_same ⟨shellSegStartVertex pcode M seg, hs, rfl⟩
              · exact h_mX_same ⟨shellSegEndVertex pcode M seg, he, rfl⟩
          · exact hne h_tri
        have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
             bdlStepXCheckX pcode M mX (Sum.inl (Sum.inl p)) ≠ 0 ∧
             bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inl p)) ≠ 0)).card ≤ 2 := by
          have h_sub := card_filter_le_add_of_or
            (fun p : RadialVertex pcode M × Fin 3 =>
              bdlStepXCheckX pcode M mX (Sum.inl (Sum.inl p)) ≠ 0 ∧
              bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inl p)) ≠ 0)
            (fun p => p = (shellSegStartRadial pcode M seg, b))
            (fun p => p = (shellSegEndRadial pcode M seg hr0, b))
            (fun ⟨rv', b'⟩ ⟨_, hZ⟩ => by
              obtain ⟨_, hb', h_or⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv' b' hZ
              rcases h_or with ⟨hr0', _⟩ | ⟨_, hsv' | hsv'⟩
              · exact False.elim (hr0 hr0')
              · exact Or.inl (Prod.ext (Subtype.ext hsv') hb'.symm)
              · exact Or.inr (Prod.ext (Subtype.ext hsv') hb'.symm))
          have h1 : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
              p = (shellSegStartRadial pcode M seg, b))).card ≤ 1 :=
            card_filter_le_one_of_unique _ (fun _ h1 _ h2 => h1.trans h2.symm)
          have h2 : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
              p = (shellSegEndRadial pcode M seg hr0, b))).card ≤ 1 :=
            card_filter_le_one_of_unique _ (fun _ h1 _ h2 => h1.trans h2.symm)
          omega
        omega
    · -- Subcase hr0 : seg.val.2.1.val ≠ 0 and h_tri : seg.val.2.2.val ≠ seg.val.2.1.val
      have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
          bdlStepXCheckX pcode M mX (Sum.inl (Sum.inl p)) ≠ 0 ∧
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inl p)) ≠ 0)).card ≤ 1 := by
        apply card_filter_le_one_of_unique
        intro ⟨rv1, b1⟩ ⟨hX1, hZ1⟩ ⟨rv2, b2⟩ ⟨hX2, hZ2⟩
        obtain ⟨hr1, hb1, h_or1⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv1 b1 hZ1
        obtain ⟨hr2, hb2, h_or2⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv2 b2 hZ2
        subst hb1 hb2
        rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
        · unfold bdlStepXCheckX bdlDeltaX0 at hX1; dsimp only at hX1
          rw [if_neg (hr1 ▸ hr0)] at hX1
          rcases add_ite_one_ne_zero_imp hX1 with h | h <;> injection h
        · rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b0 (rv1, b) hX1 with heq1 | ⟨_, hpar1, hb0_1⟩
          · rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b0 (rv2, b) hX2 with heq2 | ⟨_, hpar2, _⟩
            · have h_val := heq1.trans heq2.symm
              injection h_val with h1 h2
              exact Prod.ext (Subtype.ext h1) h2
            · injection heq1 with hsv1_eq _
              dsimp only at hpar2
              have hfp2 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar2
              dsimp [radialParentVertex, finPred] at hfp2
              have hr1_val : seg.val.2.1.val = sv0.val.2.val :=
                congr_arg Fin.val (hr1.trans (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv1_eq))
              have hr2_val : seg.val.2.1.val = rv2.val.val.2.val := congr_arg Fin.val hr2
              omega
          · rcases bdlDeltaX0_radial_inr_ne_zero_imp pcode M sv0 b0 (rv2, b) hX2 with heq2 | ⟨_, hpar2, _⟩
            · injection heq2 with hsv2_eq _
              dsimp only at hpar1
              have hfp1 := congr_arg (fun s : ShellVertex pcode M => s.val.2.val) hpar1
              dsimp [radialParentVertex, finPred] at hfp1
              have hr2_val : seg.val.2.1.val = sv0.val.2.val :=
                congr_arg Fin.val (hr2.trans (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv2_eq))
              have hr1_val : seg.val.2.1.val = rv1.val.val.2.val := congr_arg Fin.val hr1
              omega
            · dsimp only at hpar1 hpar2
              rcases h_or1 with ⟨hr0', _⟩ | ⟨_, hsv1 | hsv1⟩ <;> [exact False.elim (hr0 hr0'); skip; skip]
              · rcases h_or2 with ⟨hr0', _⟩ | ⟨_, hsv2 | hsv2⟩ <;> [exact False.elim (hr0 hr0'); skip; skip]
                · exact Prod.ext (Subtype.ext (hsv1.trans hsv2.symm)) rfl
                · rw [hsv1] at hpar1; rw [hsv2] at hpar2
                  exact False.elim (radialParent_start_ne_radialParent_end pcode M seg h_tri (hpar1.trans hpar2.symm))
              · rcases h_or2 with ⟨hr0', _⟩ | ⟨_, hsv2 | hsv2⟩ <;> [exact False.elim (hr0 hr0'); skip; skip]
                · rw [hsv1] at hpar1; rw [hsv2] at hpar2
                  exact False.elim (radialParent_start_ne_radialParent_end pcode M seg h_tri (hpar2.trans hpar1.symm))
                · exact Prod.ext (Subtype.ext (hsv1.trans hsv2.symm)) rfl
      have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
          bdlStepXCheckX pcode M mX (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0 ∧
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b))) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0)).card ≤ 1 := by
        apply card_filter_le_one_of_unique
        intro ⟨seg1, b1⟩ ⟨hX1, hZ1⟩ ⟨seg2, b2⟩ ⟨hX2, hZ2⟩
        obtain ⟨_, hb1, h_or1⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg1 b1 hZ1
        obtain ⟨_, hb2, h_or2⟩ := bdlDeltaX1_inr_inl_ne_zero_imp2 pcode M seg b seg2 b2 hZ2
        subst hb1 hb2
        rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
        · exact False.elim (hX1 rfl)
        · have hr_seg1 : seg1.val.2.1 = sv0.val.2 := by
            unfold bdlStepXCheckX bdlDeltaX0 at hX1; dsimp only at hX1
            rcases add_ite_one_ne_zero_imp hX1 with h | h <;>
              (injection h with h; injection h with hsv _;
               exact (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv).symm)
          have hr_seg2 : seg2.val.2.1 = sv0.val.2 := by
            unfold bdlStepXCheckX bdlDeltaX0 at hX2; dsimp only at hX2
            rcases add_ite_one_ne_zero_imp hX2 with h | h <;>
              (injection h with h; injection h with hsv _;
               exact (congr_arg (fun s : ShellVertex pcode M => s.val.2) hsv).symm)
          have hr_eq : seg1.val.2.1.val = seg2.val.2.1.val :=
            congr_arg Fin.val (hr_seg1.trans hr_seg2.symm)
          rcases h_or1 with ⟨hr0', _⟩ | ⟨_, hseg1 | ⟨_, hseg1⟩⟩ <;> [exact False.elim (hr0 hr0'); skip; skip]
          · rcases h_or2 with ⟨hr0', _⟩ | ⟨_, hseg2 | ⟨_, hseg2⟩⟩ <;> [exact False.elim (hr0 hr0'); skip; skip]
            · exact Prod.ext (hseg1.symm.trans hseg2) rfl
            · rw [← hseg1, ← hseg2] at hr_eq
              dsimp [shellSegPred, finPred] at hr_eq
              omega
          · rcases h_or2 with ⟨hr0', _⟩ | ⟨_, hseg2 | ⟨_, hseg2⟩⟩ <;> [exact False.elim (hr0 hr0'); skip; skip]
            · rw [← hseg1, ← hseg2] at hr_eq
              dsimp [shellSegPred, finPred] at hr_eq
              omega
            · exact Prod.ext (hseg1.symm.trans hseg2) rfl
      omega

/-! ## 2. Outer Boundary Link Z-Check Overlap Bound (≤ 2) -/

set_option maxHeartbeats 800000 in
/-- **Cylinder Shared-Check Overlap Bound (Outer Boundary Link $Z$-Checks)**:
    For any $X$-check $m_X$ and any outer-boundary $Z$-check `Sum.inl (Sum.inr (s, k, v))`,
    at most $2$ qubits in `BDLStepXQ pcode M` lie in the support of both checks. -/
lemma card_filter_bdlStepX_overlap_outer_le_two {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mX : BDLStepXMX pcode M) (s : ActiveZLink pcode) (k : Fin (M + 1)) (v : Fin 2) :
    (Finset.univ.filter (fun q1 : BDLStepXQ pcode M =>
      bdlStepXCheckX pcode M mX q1 ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, v))) q1 ≠ 0)).card ≤ 2 := by
  -- Step 1: Vanish BDLCQ1 and radial vertex sectors for outer boundary Z-checks.
  rw [card_filter_sum_eq']
  have h_cq1 : (Finset.univ.filter (fun qQ : BDLCQ1 pcode M =>
      bdlStepXCheckX pcode M mX (Sum.inr qQ) ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, v))) (Sum.inr qQ) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun _ h => h.2 rfl)
  rw [card_filter_sum_eq', card_filter_sum_eq']
  have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
      bdlStepXCheckX pcode M mX (Sum.inl (Sum.inl p)) ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, v))) (Sum.inl (Sum.inl p)) ≠ 0)).card = 0 := by
    apply card_filter_eq_zero_of_imp_false
    intro p ⟨_, hZ⟩
    unfold bdlStepXCheckZ bdlDeltaX1 at hZ; dsimp only at hZ
    rcases add_ne_zero_imp hZ with h123 | h4
    · rcases add_ne_zero_imp h123 with h12 | h3
      · rcases add_ne_zero_imp h12 with h1 | h2
        · have h := ite_one_ne_zero_imp h1; injection h
        · have h := ite_one_ne_zero_imp h2; injection h
      · have h := ite_one_ne_zero_imp h3; injection h
    · have h := ite_one_ne_zero_imp h4; injection h
  -- Step 2: Bound azimuthal segment and vertical boundary overlaps by at most 1 each.
  have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      bdlStepXCheckX pcode M mX (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, v))) (Sum.inl (Sum.inr (Sum.inl p))) ≠ 0)).card ≤ 1 := by
    apply card_filter_le_one_of_unique
    intro ⟨seg1, b1⟩ ⟨hX1, hZ1⟩ ⟨seg2, b2⟩ ⟨hX2, hZ2⟩
    rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
    · exact False.elim (hX1 rfl)
    · have hb1 : b1 = b0 := by
        unfold bdlStepXCheckX bdlDeltaX0 at hX1; dsimp only at hX1
        rcases add_ite_one_ne_zero_imp hX1 with h | h <;> (injection h with h; injection h with _ hb; exact hb.symm)
      have hb2 : b2 = b0 := by
        unfold bdlStepXCheckX bdlDeltaX0 at hX2; dsimp only at hX2
        rcases add_ite_one_ne_zero_imp hX2 with h | h <;> (injection h with h; injection h with _ hb; exact hb.symm)
      have hseg1 : seg1 = mkOuterShellSegment pcode M s k := by
        unfold bdlStepXCheckZ bdlDeltaX1 at hZ1; dsimp only at hZ1
        rcases add_ne_zero_imp hZ1 with h123 | h4
        · rcases add_ne_zero_imp h123 with h12 | h3
          · rcases add_ne_zero_imp h12 with h1 | h2
            · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inl p) => p.1 | _ => seg1) (ite_one_ne_zero_imp h1)
            · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inl p) => p.1 | _ => seg1) (ite_one_ne_zero_imp h2)
          · have h := ite_one_ne_zero_imp h3; injection h with h; injection h
        · have h := ite_one_ne_zero_imp h4; injection h with h; injection h
      have hseg2 : seg2 = mkOuterShellSegment pcode M s k := by
        unfold bdlStepXCheckZ bdlDeltaX1 at hZ2; dsimp only at hZ2
        rcases add_ne_zero_imp hZ2 with h123 | h4
        · rcases add_ne_zero_imp h123 with h12 | h3
          · rcases add_ne_zero_imp h12 with h1 | h2
            · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inl p) => p.1 | _ => seg2) (ite_one_ne_zero_imp h1)
            · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inl p) => p.1 | _ => seg2) (ite_one_ne_zero_imp h2)
          · have h := ite_one_ne_zero_imp h3; injection h with h; injection h
        · have h := ite_one_ne_zero_imp h4; injection h with h; injection h
      exact Prod.ext (hseg1.trans hseg2.symm) (hb1.trans hb2.symm)
  have h_vert : (Finset.univ.filter (fun xv : BoundaryX0Link pcode M × Fin 2 =>
      bdlStepXCheckX pcode M mX (Sum.inl (Sum.inr (Sum.inr xv))) ≠ 0 ∧
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, v))) (Sum.inl (Sum.inr (Sum.inr xv))) ≠ 0)).card ≤ 1 := by
    apply card_filter_le_one_of_unique
    intro ⟨xv1, v1⟩ ⟨hX1, hZ1⟩ ⟨xv2, v2⟩ ⟨hX2, hZ2⟩
    rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
    · exact False.elim (hX1 rfl)
    · have hxv1 : xv1 = sv0.val.1 := by
        unfold bdlStepXCheckX bdlDeltaX0 at hX1; dsimp only at hX1
        rcases add_ite_one_ne_zero_imp hX1 with h | h <;>
          (injection h with h; injection h with hsv _;
           exact (congr_arg (fun sv : ShellVertex pcode M => sv.val.1) hsv).symm)
      have hxv2 : xv2 = sv0.val.1 := by
        unfold bdlStepXCheckX bdlDeltaX0 at hX2; dsimp only at hX2
        rcases add_ite_one_ne_zero_imp hX2 with h | h <;>
          (injection h with h; injection h with hsv _;
           exact (congr_arg (fun sv : ShellVertex pcode M => sv.val.1) hsv).symm)
      have hv1 : v1 = v := by
        unfold bdlStepXCheckZ bdlDeltaX1 at hZ1; dsimp only at hZ1
        rcases add_ne_zero_imp hZ1 with h123 | h4
        · rcases add_ne_zero_imp h123 with h12 | h3
          · rcases add_ne_zero_imp h12 with h1 | h2
            · have h := ite_one_ne_zero_imp h1; injection h with h; injection h
            · have h := ite_one_ne_zero_imp h2; injection h with h; injection h
          · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inr p) => p.2 | _ => v1) (ite_one_ne_zero_imp h3)
        · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inr p) => p.2 | _ => v1) (ite_one_ne_zero_imp h4)
      have hv2 : v2 = v := by
        unfold bdlStepXCheckZ bdlDeltaX1 at hZ2; dsimp only at hZ2
        rcases add_ne_zero_imp hZ2 with h123 | h4
        · rcases add_ne_zero_imp h123 with h12 | h3
          · rcases add_ne_zero_imp h12 with h1 | h2
            · have h := ite_one_ne_zero_imp h1; injection h with h; injection h
            · have h := ite_one_ne_zero_imp h2; injection h with h; injection h
          · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inr p) => p.2 | _ => v2) (ite_one_ne_zero_imp h3)
        · exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inr p) => p.2 | _ => v2) (ite_one_ne_zero_imp h4)
      exact Prod.ext (hxv1.trans hxv2.symm) (hv1.trans hv2.symm)
  omega

end WeldedHierarchy
