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

import Proofs.Step2DegreeAndWeld.CylinderZCheckWeightBound

/-!
# Interior Radial and Azimuthal Qubit Z-Check Degree Bounds

Characterizes non-zero entries of `bdlDeltaX1` on radial and azimuthal cylinder 1-cells (`bdlDeltaX1_inl_ne_zero_imp`, `bdlDeltaX1_inr_inl_ne_zero_imp`). Proves that every `RadialVertex` qubit and every azimuthal `ShellSegment` qubit participates in at most 4 $Z$-checks under `bdlStepXCheckZ` (`card_filter_bdlStepXCheckZ_mZ_rv_le`, `card_filter_bdlStepXCheckZ_mZ_seg_le`).

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Equation (4) (`eq:dx-coboundary`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Support Characterizations for bdlDeltaX1 on Radial and Azimuthal Qubits -/

/-- Characterizes which shell segments `(seg, b)` have non-zero coboundary `bdlDeltaX1` on a
    radial vertex `(rv0, b0)`: either $r = 0$ corner spokes or radial endpoints at $r > 0$. -/
lemma bdlDeltaX1_inl_ne_zero_imp {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (rv0 : RadialVertex pcode M) (b0 : Fin 3)
    (hne : bdlDeltaX1 pcode M (Sum.inl (seg, b)) (Sum.inl (rv0, b0)) ≠ 0) :
    seg.val.2.1 = rv0.val.val.2 ∧ b = b0 ∧
    ((seg.val.2.1.val = 0 ∧
      seg.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg.val.1.val.1 seg.val.1.val.2.val.2
        ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩ ∧
  -- Step 1: Split on innermost shell r = 0 vs. interior shells r > 0.
      ∃ (q' : Q) (hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0),
        pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0 ∧
        rv0.val = cornerSpoke pcode M seg.val.1.val.1 q' hX') ∨
     (seg.val.2.1.val ≠ 0 ∧
      (rv0.val = shellSegStartVertex pcode M seg ∨ rv0.val = shellSegEndVertex pcode M seg))) := by
  by_cases hr0 : seg.val.2.1.val = 0
  · obtain ⟨h_can, q', hX', hZ', h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl (rv0, b0)) hne
    rcases h_or with h_eq | h_eq
  -- Step 2: For r > 0, split on triangular (k = r) vs. non-triangular (k < r) segments.
    · injection h_eq with h_prod
      injection h_prod with hsv hb
      subst hsv hb
      exact ⟨Fin.ext hr0, rfl, Or.inl ⟨hr0, h_can, q', hX', hZ', rfl⟩⟩
    · injection h_eq
  · unfold bdlDeltaX1 at hne
    dsimp only at hne
    by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · rw [dif_pos h_tri, dif_neg hr0] at hne
      have h_zero : (if (Sum.inl (rv0, b0) : BDLCX1 pcode M) = Sum.inr (Sum.inl (seg, b)) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h)
      rw [h_zero, add_zero] at hne
      rcases add_ite_one_ne_zero_imp hne with h1 | h2
      · injection h1 with hp; injection hp with hsv hb; subst hsv hb
        exact ⟨rfl, rfl, Or.inr ⟨hr0, Or.inl rfl⟩⟩
      · injection h2 with hp; injection hp with hsv hb; subst hsv hb
        exact ⟨rfl, rfl, Or.inr ⟨hr0, Or.inr rfl⟩⟩
    · rw [dif_neg h_tri] at hne
      have h_z1 : (if (Sum.inl (rv0, b0) : BDLCX1 pcode M) = Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h)
      have h_z2 : (if (Sum.inl (rv0, b0) : BDLCX1 pcode M) = Sum.inr (Sum.inl (seg, b)) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h)
      rw [h_z1, h_z2, add_zero, add_zero] at hne
      rcases add_ite_one_ne_zero_imp hne with h1 | h2
      · injection h1 with hp; injection hp with hsv hb; subst hsv hb
        exact ⟨rfl, rfl, Or.inr ⟨hr0, Or.inl rfl⟩⟩
      · injection h2 with hp; injection hp with hsv hb; subst hsv hb
        exact ⟨rfl, rfl, Or.inr ⟨hr0, Or.inr rfl⟩⟩

/-- Characterizes which shell segments `(seg, b)` have non-zero coboundary `bdlDeltaX1` on an
    azimuthal segment `(seg0, b0)`: either $r = 0$ canonical square spokes, `seg = seg0`, or `shellSegPred seg = seg0`. -/
lemma bdlDeltaX1_inr_inl_ne_zero_imp {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (seg0 : ShellSegment pcode M) (b0 : Fin 3)
    (hne : bdlDeltaX1 pcode M (Sum.inl (seg, b)) (Sum.inr (Sum.inl (seg0, b0))) ≠ 0) :
    ((b = b0 ∧
      ((seg.val.2.1.val = 0 ∧ seg0.val.2.1.val = 0 ∧
        seg.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg.val.1.val.1 seg.val.1.val.2.val.2
          ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩ ∧
  -- Step 1: Split on innermost shell r = 0 vs. interior shells r > 0.
        seg.val.1.val.1 = seg0.val.1.val.1 ∧
        seg.val.1.val.2.val.2 = seg0.val.1.val.2.val.2) ∨
       (seg0.val.2.1.val ≠ 0 ∧ seg = seg0))) ∨
     (b = b0 ∧ ∃ h_tri : seg.val.2.2.val ≠ seg.val.2.1.val, shellSegPred pcode M seg h_tri = seg0)) := by
  by_cases hr0 : seg.val.2.1.val = 0
  · obtain ⟨h_can, q', hX', hZ', h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inr (Sum.inl (seg0, b0))) hne
    rcases h_or with h_eq | h_eq
    · injection h_eq
    · injection h_eq with h_eq; injection h_eq with h_prod; injection h_prod with hseg hb
      subst hseg hb
      exact Or.inl ⟨rfl, Or.inl ⟨hr0, rfl, h_can, rfl, rfl⟩⟩
  · unfold bdlDeltaX1 at hne
    dsimp only at hne
    by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · rw [dif_pos h_tri, dif_neg hr0] at hne
      have h_z1 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inl (shellSegStartRadial pcode M seg, b) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h)
  -- Step 2: For r > 0, extract either seg = seg0 or shellSegPred seg = seg0.
      have h_z2 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inl (shellSegEndRadial pcode M seg hr0, b) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h)
      rw [h_z1, h_z2, add_zero, zero_add] at hne
      by_cases h_eq : (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inr (Sum.inl (seg, b))
      · injection h_eq with h_eq; injection h_eq with hp; injection hp with hseg hb
        subst hseg hb
        exact Or.inl ⟨rfl, Or.inr ⟨hr0, rfl⟩⟩
      · rw [if_neg h_eq] at hne; exact False.elim (hne rfl)
    · rw [dif_neg h_tri] at hne
      have h_z1 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inl (shellSegStartRadial pcode M seg, b) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h)
      have h_z2 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inl (shellSegEndRadial pcode M seg (by have := seg.property; omega), b) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h)
      rw [h_z1, h_z2, add_zero, zero_add] at hne
      rcases add_ite_one_ne_zero_imp hne with h1 | h2
      · injection h1 with h1; injection h1 with hp; injection hp with hseg hb
        exact Or.inr ⟨hb.symm, h_tri, hseg.symm⟩
      · injection h2 with h2; injection h2 with hp; injection hp with hseg hb
        subst hseg hb
        exact Or.inl ⟨rfl, Or.inr ⟨hr0, rfl⟩⟩

/-! ## 2. Radial Vertex Qubit Z-Check Degree Bound (≤ 4) -/

set_option maxHeartbeats 800000 in
/-- **Cylinder Qubit $Z$-Degree Bound (Radial Vertex Sector)**:
    Shows that any radial vertex qubit `Sum.inl (Sum.inl (rv0, b0))` participates in at
    most $4$ $Z$-checks of `bdlCylinderStepX pcode M`. -/
lemma card_filter_bdlStepXCheckZ_mZ_rv_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdQZ : ∀ q : Q, (Finset.univ.filter (fun z : M_Z => pcode.checkZ z q ≠ 0)).card ≤ 4)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (rv0 : RadialVertex pcode M) (b0 : Fin 3) :
    (Finset.univ.filter (fun mZ : BDLStepXMZ pcode M =>
      bdlStepXCheckZ pcode M mZ (Sum.inl (Sum.inl (rv0, b0))) ≠ 0)).card ≤ 4 := by
  rw [card_filter_sum_eq', card_filter_sum_eq']
  have h_zz : (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inl (Sum.inl (rv0, b0))) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
  -- Step 1: Vanish the BDLCQ2 and outer ActiveZLink sectors and isolate ShellSegment Z-checks.
  let sv0 : ShellVertex pcode M := rv0.val
  have h_zq : (Finset.univ.filter (fun mZQ : BDLCQ2 pcode M =>
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl mZQ)) (Sum.inl (Sum.inl (rv0, b0))) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun mZQ h => by rcases mZQ with _ | _ <;> exact h rfl)
  rw [card_filter_sum_eq']
  have h_zx_inr : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr p)) (Sum.inl (Sum.inl (rv0, b0))) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
  have h_zx_inl : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl (rv0, b0))) ≠ 0)).card ≤ 4 := by
    -- Step 2: Split on innermost shell r0 = 0 vs. interior shells r0 > 0.
    by_cases hr0 : sv0.val.2.val = 0
    · rcases h_v : sv0.val.1.val.2 with q0 | ⟨_ | _⟩
      · refine (card_filter_le_of_injOn_filter _
          (fun z : M_Z => pcode.checkZ z q0 ≠ 0)
          (fun p => p.1.val.1.val.2.val.2) ?_ ?_).trans (hdQZ q0)
        · intro ⟨seg, b⟩ hp
          obtain ⟨_, _, h_or⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv0 b0 hp
          rcases h_or with ⟨_, _, q', hX', hZ', hsv⟩ | ⟨hr_ne, _⟩
          · have hv_eq : sv0.val.1.val.2 = Sum.inl q' := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hsv
            rw [h_v] at hv_eq; injection hv_eq with hq_eq; subst hq_eq; exact hZ'
          · obtain ⟨hr_eq, _, _⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv0 b0 hp
            exact False.elim (hr_ne (hr_eq ▸ hr0))
        · intro ⟨seg1, b1⟩ hp1 ⟨seg2, b2⟩ hp2 h_eq
          obtain ⟨hr1, hb1, h_or1⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg1 b1 rv0 b0 hp1
          obtain ⟨hr2, hb2, h_or2⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg2 b2 rv0 b0 hp2
          rcases h_or1 with ⟨hr1_0, hcan1, q1', hX1', _, hsv1⟩ | ⟨hr_ne, _⟩
          · rcases h_or2 with ⟨hr2_0, hcan2, q2', hX2', _, hsv2⟩ | ⟨hr_ne, _⟩
            · have hx1 : sv0.val.1.val.1 = seg1.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv1
              have hx2 : sv0.val.1.val.1 = seg2.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hsv2
              have hx : seg1.val.1.val.1 = seg2.val.1.val.1 := hx1.symm.trans hx2
              (try dsimp at h_eq)
              have hq : seg1.val.1.val.2.val.1 = seg2.val.1.val.2.val.1 := by
                rw [hcan1, hcan2]; congr 1
              have hk1 : seg1.val.2.2.val = 0 := by have := seg1.property; omega
              have hk2 : seg2.val.2.2.val = 0 := by have := seg2.property; omega
              apply Prod.ext
              · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hx (Subtype.ext (Prod.ext hq h_eq))))
                  (Prod.ext (hr1.trans hr2.symm) (Fin.ext (hk1.trans hk2.symm))))
              · exact hb1.trans hb2.symm
            · exact False.elim (hr_ne (hr2 ▸ hr0))
          · exact False.elim (hr_ne (hr1 ▸ hr0))
      · refine Nat.le_trans (Nat.le_of_eq (card_filter_eq_zero_of_imp_false _ ?_)) (Nat.zero_le 4)
        intro ⟨seg, b⟩ hp
        obtain ⟨hr_eq, _, h_or⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv0 b0 hp
        rcases h_or with ⟨_, _, q', _, _, hsv⟩ | ⟨hr_ne, _⟩
        · have hv_eq : sv0.val.1.val.2 = Sum.inl q' := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hsv
          rw [h_v] at hv_eq; injection hv_eq
    -- Step 3: For r0 > 0, split into start-endpoint and end-endpoint shell segments.
        · exact hr_ne (hr_eq ▸ hr0)
      · refine Nat.le_trans (Nat.le_of_eq (card_filter_eq_zero_of_imp_false _ ?_)) (Nat.zero_le 4)
        intro ⟨seg, b⟩ hp
        obtain ⟨hr_eq, _, h_or⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv0 b0 hp
        rcases h_or with ⟨_, _, q', _, _, hsv⟩ | ⟨hr_ne, _⟩
        · have hv_eq : sv0.val.1.val.2 = Sum.inl q' := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hsv
          rw [h_v] at hv_eq; injection hv_eq
        · exact hr_ne (hr_eq ▸ hr0)
    · have h_split := card_filter_le_add_of_or
        (fun p : ShellSegment pcode M × Fin 3 =>
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl (rv0, b0))) ≠ 0)
        (fun p : ShellSegment pcode M × Fin 3 => sv0 = shellSegStartVertex pcode M p.1 ∧ p.2 = b0)
        (fun p : ShellSegment pcode M × Fin 3 => sv0 = shellSegEndVertex pcode M p.1 ∧ p.2 = b0)
        (fun ⟨seg, b⟩ hp => by
          obtain ⟨hr_eq, hb_eq, h_or⟩ := bdlDeltaX1_inl_ne_zero_imp pcode M seg b rv0 b0 hp
          rcases h_or with ⟨hr_z, _⟩ | ⟨_, h_se⟩
          · exact False.elim (hr0 (hr_eq ▸ hr_z))
          · rcases h_se with hs | he
            · exact Or.inl ⟨hs, hb_eq⟩
            · exact Or.inr ⟨he, hb_eq⟩)
      rcases h_v : sv0.val.1.val.2 with q0 | ⟨⟨eZ0, j0⟩ | z0⟩
      · have h_end0 : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
            sv0 = shellSegEndVertex pcode M p.1 ∧ p.2 = b0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨seg, b⟩ ⟨he, _⟩
          have hv_eq : sv0.val.1.val.2 = shellSegEndV pcode M seg :=
            congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) he
          rw [h_v] at hv_eq
          exact shellSegEndV_ne_inl pcode M seg q0 hv_eq.symm
        have h_start_le : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
            sv0 = shellSegStartVertex pcode M p.1 ∧ p.2 = b0)).card ≤ 4 := by
          refine (card_filter_le_of_injOn_filter _
            (fun z : M_Z => pcode.checkZ z q0 ≠ 0)
            (fun p => p.1.val.1.val.2.val.2) ?_ ?_).trans (hdQZ q0)
          · intro ⟨seg, b⟩ ⟨hs, _⟩
            have hv_eq : sv0.val.1.val.2 = bxStart pcode M seg.val.1.val.2 seg.val.2.2 :=
              congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hs
            rw [h_v] at hv_eq
            dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv_eq
            split_ifs at hv_eq with hk0
            injection hv_eq with hq_eq; rw [hq_eq]; exact seg.val.1.val.2.property
          · intro ⟨seg1, b1⟩ ⟨hs1, hb1⟩ ⟨seg2, b2⟩ ⟨hs2, hb2⟩ h_eq
            have hv1 : sv0.val.1.val.2 = bxStart pcode M seg1.val.1.val.2 seg1.val.2.2 :=
              congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hs1
            have hv2 : sv0.val.1.val.2 = bxStart pcode M seg2.val.1.val.2 seg2.val.2.2 :=
              congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hs2
            rw [h_v] at hv1 hv2
            dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv1 hv2
            split_ifs at hv1 with hk1
            split_ifs at hv2 with hk2
            injection hv1 with hq1; injection hv2 with hq2
            have hx1 : sv0.val.1.val.1 = seg1.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hs1
            have hx2 : sv0.val.1.val.1 = seg2.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hs2
            have hr1 : sv0.val.2 = seg1.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) hs1
            have hr2 : sv0.val.2 = seg2.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) hs2
            apply Prod.ext
            · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2)
                (Subtype.ext (Prod.ext (hq1.symm.trans hq2) h_eq))))
                (Prod.ext (hr1.symm.trans hr2) (Fin.ext (hk1.trans hk2.symm))))
            · exact hb1.trans hb2.symm
        omega
      · have h_start1 : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
            sv0 = shellSegStartVertex pcode M p.1 ∧ p.2 = b0)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨seg1, b1⟩ ⟨hs1, hb1⟩ ⟨seg2, b2⟩ ⟨hs2, hb2⟩
          dsimp only at hs1 hb1 hs2 hb2
          have hv1 : sv0.val.1.val.2 = bxStart pcode M seg1.val.1.val.2 seg1.val.2.2 :=
            congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hs1
          have hv2 : sv0.val.1.val.2 = bxStart pcode M seg2.val.1.val.2 seg2.val.2.2 :=
            congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hs2
          rw [h_v] at hv1 hv2
          dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv1 hv2
          split_ifs at hv1 with hk1
          split_ifs at hv2 with hk2
          injection hv1 with hv1; injection hv1 with hv1; injection hv1 with heZ1 hj1
          injection hv2 with hv2; injection hv2 with hv2; injection hv2 with heZ2 hj2
          have hj1_val := congr_arg Fin.val hj1; (try dsimp at hj1_val)
          have hj2_val := congr_arg Fin.val hj2; (try dsimp at hj2_val)
          have hx1 : sv0.val.1.val.1 = seg1.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hs1
          have hx2 : sv0.val.1.val.1 = seg2.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) hs2
          have hr1 : sv0.val.2 = seg1.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) hs1
          have hr2 : sv0.val.2 = seg2.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) hs2
          apply Prod.ext
          · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2) (heZ1.symm.trans heZ2)))
              (Prod.ext (hr1.symm.trans hr2) (Fin.ext (by dsimp only; omega))))
          · exact hb1.trans hb2.symm
        have h_end1 : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
            sv0 = shellSegEndVertex pcode M p.1 ∧ p.2 = b0)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨seg1, b1⟩ ⟨he1, hb1⟩ ⟨seg2, b2⟩ ⟨he2, hb2⟩
          dsimp only at he1 hb1 he2 hb2
          have hv1 : sv0.val.1.val.2 = shellSegEndV pcode M seg1 :=
            congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) he1
          have hv2 : sv0.val.1.val.2 = shellSegEndV pcode M seg2 :=
            congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) he2
          rw [h_v] at hv1 hv2
          dsimp [shellSegEndV] at hv1 hv2
          split_ifs at hv1 with hk1 <;> [skip; (injection hv1 with hv1; injection hv1)]
          split_ifs at hv2 with hk2 <;> [skip; (injection hv2 with hv2; injection hv2)]
          injection hv1 with hv1; injection hv1 with hv1; injection hv1 with heZ1 hj1
          injection hv2 with hv2; injection hv2 with hv2; injection hv2 with heZ2 hj2
          have hj1_val := congr_arg Fin.val hj1; (try dsimp at hj1_val)
          have hj2_val := congr_arg Fin.val hj2; (try dsimp at hj2_val)
          have hx1 : sv0.val.1.val.1 = seg1.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) he1
          have hx2 : sv0.val.1.val.1 = seg2.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) he2
          have hr1 : sv0.val.2 = seg1.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) he1
          have hr2 : sv0.val.2 = seg2.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) he2
          apply Prod.ext
          · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2) (heZ1.symm.trans heZ2)))
              (Prod.ext (hr1.symm.trans hr2) (Fin.ext (by dsimp only; omega))))
          · exact hb1.trans hb2.symm
        omega
      · have h_start0 : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
            sv0 = shellSegStartVertex pcode M p.1 ∧ p.2 = b0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨seg, b⟩ ⟨hs, _⟩
          have hv_eq : sv0.val.1.val.2 = bxStart pcode M seg.val.1.val.2 seg.val.2.2 :=
            congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) hs
          rw [h_v] at hv_eq
          exact bxStart_ne_inr_inr pcode M seg.val.1.val.2 seg.val.2.2 z0 hv_eq.symm
        have h_end2 : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
            sv0 = shellSegEndVertex pcode M p.1 ∧ p.2 = b0)).card ≤ 2 := by
          refine (card_filter_le_of_injOn_filter _
            (fun q : Q => pcode.checkX sv0.val.1.val.1 q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0)
            (fun p => p.1.val.1.val.2.val.1) ?_ ?_).trans (hov sv0.val.1.val.1 z0)
          · intro ⟨seg, b⟩ ⟨he, _⟩
            have hx : sv0.val.1.val.1 = seg.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) he
            have hv_eq : sv0.val.1.val.2 = shellSegEndV pcode M seg :=
              congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) he
            rw [h_v] at hv_eq
            dsimp [shellSegEndV] at hv_eq
            split_ifs at hv_eq with hk
            · injection hv_eq with hv_eq; injection hv_eq
            · injection hv_eq with hv_eq; injection hv_eq with hz_eq
              rw [hx, hz_eq]
              exact ⟨seg.val.1.property, seg.val.1.val.2.property⟩
          · intro ⟨seg1, b1⟩ ⟨he1, hb1⟩ ⟨seg2, b2⟩ ⟨he2, hb2⟩ h_eq
            have hx1 : sv0.val.1.val.1 = seg1.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) he1
            have hx2 : sv0.val.1.val.1 = seg2.val.1.val.1 := congr_arg (fun u : ShellVertex pcode M => u.val.1.val.1) he2
            have hr1 : sv0.val.2 = seg1.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) he1
            have hr2 : sv0.val.2 = seg2.val.2.1 := congr_arg (fun u : ShellVertex pcode M => u.val.2) he2
            have hv1 : sv0.val.1.val.2 = shellSegEndV pcode M seg1 :=
              congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) he1
            have hv2 : sv0.val.1.val.2 = shellSegEndV pcode M seg2 :=
              congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) he2
            rw [h_v] at hv1 hv2
            dsimp [shellSegEndV] at hv1 hv2
            split_ifs at hv1 with hk1 <;> [injection hv1 with hv1; skip]; (try injection hv1)
            split_ifs at hv2 with hk2 <;> [injection hv2 with hv2; skip]; (try injection hv2)
            injection hv1 with hv1; injection hv1 with hz1
            injection hv2 with hv2; injection hv2 with hz2
            have hk1_eq : seg1.val.2.2 = seg1.val.2.1 := Fin.ext (by have := seg1.property; omega)
            have hk2_eq : seg2.val.2.2 = seg2.val.2.1 := Fin.ext (by have := seg2.property; omega)
            apply Prod.ext
            · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2)
                (Subtype.ext (Prod.ext h_eq (hz1.symm.trans hz2)))))
                (Prod.ext (hr1.symm.trans hr2) (hk1_eq.trans ((hr1.symm.trans hr2).trans hk2_eq.symm))))
            · exact hb1.trans hb2.symm
        omega
  omega

/-! ## 3. Azimuthal Segment Qubit Z-Check Degree Bound (≤ 4) -/

set_option maxHeartbeats 800000 in
/-- **Cylinder Qubit $Z$-Degree Bound (Azimuthal Segment Sector)**:
    Shows that any azimuthal segment qubit `Sum.inl (Sum.inr (Sum.inl (seg0, b0)))`
    participates in at most $4$ $Z$-checks of `bdlCylinderStepX pcode M`. -/
lemma card_filter_bdlStepXCheckZ_mZ_seg_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (seg0 : ShellSegment pcode M) (b0 : Fin 3) :
    (Finset.univ.filter (fun mZ : BDLStepXMZ pcode M =>
      bdlStepXCheckZ pcode M mZ (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)).card ≤ 4 := by
  rw [card_filter_sum_eq', card_filter_sum_eq']
  have h_zz : (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
  -- Step 1: Decompose BDLCQ2 and BDLCX2 and bound the coupling and outer-boundary contributions.
  rw [card_filter_sum_eq', card_filter_sum_eq']
  have h_zq_inr : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
  have h_zq_inl : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl p))) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)).card ≤ 1 := by
    apply card_filter_le_one_of_unique
    intro ⟨eZ1, k1, bZ1⟩ hp1 ⟨eZ2, k2, bZ2⟩ hp2
    dsimp [bdlStepXCheckZ, bdlGXQ1] at hp1 hp2
    split_ifs at hp1 with hc1 <;> [skip; exact False.elim (hp1 rfl)]
    split_ifs at hp2 with hc2 <;> [skip; exact False.elim (hp2 rfl)]
    exact Prod.ext (hc1.2.1.symm.trans hc2.2.1) (Prod.ext (hc1.2.2.1.symm.trans hc2.2.2.1) (hc1.2.2.2.symm.trans hc2.2.2.2))
  have h_zx_inr : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inr p)) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)).card ≤ 2 := by
    have h_sub : Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
        bdlStepXCheckZ pcode M (Sum.inl (Sum.inr p)) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0) ⊆
        {(seg0.val.1, seg0.val.2.2, 0), (seg0.val.1, seg0.val.2.2, 1)} := by
      intro ⟨s, k, v⟩ hp
      rw [Finset.mem_filter] at hp
      have hp1 := hp.2
      unfold bdlStepXCheckZ bdlDeltaX1 at hp1; dsimp only at hp1
      have hz3 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inr (Sum.inr (bxStartLink pcode M s k, v)) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h with h; injection h)
      have hz4 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inr (Sum.inr (bxEndLink pcode M s k, v)) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h with h; injection h)
      rw [hz3, hz4, add_zero, add_zero] at hp1
      have h_seg : seg0 = mkOuterShellSegment pcode M s k := by
        rcases add_ite_one_ne_zero_imp hp1 with h | h <;>
          exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inl p) => p.1 | _ => seg0) h
      have hs_eq : s = seg0.val.1 := (congr_arg (fun u : ShellSegment pcode M => u.val.1) h_seg).symm
      have hk_eq : k = seg0.val.2.2 := (congr_arg (fun u : ShellSegment pcode M => u.val.2.2) h_seg).symm
      subst hs_eq hk_eq
      rw [Finset.mem_insert, Finset.mem_singleton]
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact (Finset.card_le_card h_sub).trans Finset.card_le_two
  -- Step 2: Split ShellSegment Z-checks into same-shell (h_p1) and next-shell predecessor (h_p2) terms.
  have h_split := card_filter_le_add_of_or
    (fun p : ShellSegment pcode M × Fin 3 =>
      bdlStepXCheckZ pcode M (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)
    (fun p : ShellSegment pcode M × Fin 3 =>
      p.2 = b0 ∧
      ((p.1.val.2.1.val = 0 ∧ seg0.val.2.1.val = 0 ∧
        p.1.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) p.1.val.1.val.1 p.1.val.1.val.2.val.2
          ⟨p.1.val.1.val.2.val.1, p.1.val.1.property, p.1.val.1.val.2.property⟩ ∧
        p.1.val.1.val.1 = seg0.val.1.val.1 ∧
        p.1.val.1.val.2.val.2 = seg0.val.1.val.2.val.2) ∨
       (seg0.val.2.1.val ≠ 0 ∧ p.1 = seg0)))
    (fun p : ShellSegment pcode M × Fin 3 =>
      p.2 = b0 ∧ ∃ h_tri : p.1.val.2.2.val ≠ p.1.val.2.1.val, shellSegPred pcode M p.1 h_tri = seg0)
    (fun ⟨seg, b⟩ hp => bdlDeltaX1_inr_inl_ne_zero_imp pcode M seg b seg0 b0 hp)
  have h_p1 : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
      p.2 = b0 ∧
      ((p.1.val.2.1.val = 0 ∧ seg0.val.2.1.val = 0 ∧
        p.1.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) p.1.val.1.val.1 p.1.val.1.val.2.val.2
          ⟨p.1.val.1.val.2.val.1, p.1.val.1.property, p.1.val.1.val.2.property⟩ ∧
        p.1.val.1.val.1 = seg0.val.1.val.1 ∧
        p.1.val.1.val.2.val.2 = seg0.val.1.val.2.val.2) ∨
       (seg0.val.2.1.val ≠ 0 ∧ p.1 = seg0)))).card ≤ 1 := by
    apply card_filter_le_one_of_unique
    intro ⟨seg1, b1⟩ ⟨hb1, hor1⟩ ⟨seg2, b2⟩ ⟨hb2, hor2⟩
    dsimp only at hb1 hor1 hb2 hor2
    rcases hor1 with ⟨hr1, hr0, hcan1, hx1, hz1⟩ | ⟨hr_ne, hseg1⟩
    · rcases hor2 with ⟨hr2, _, hcan2, hx2, hz2⟩ | ⟨hr_ne, _⟩
      · have hx := hx1.trans hx2.symm
        have hz := hz1.trans hz2.symm
        have hq : seg1.val.1.val.2.val.1 = seg2.val.1.val.2.val.1 := by rw [hcan1, hcan2]; congr 1
        have hk1 : seg1.val.2.2.val = 0 := by have := seg1.property; omega
        have hk2 : seg2.val.2.2.val = 0 := by have := seg2.property; omega
        exact Prod.ext (Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hx (Subtype.ext (Prod.ext hq hz))))
          (Prod.ext (Fin.ext (hr1.trans hr2.symm)) (Fin.ext (hk1.trans hk2.symm))))) (hb1.trans hb2.symm)
      · exact False.elim (hr_ne hr0)
    · rcases hor2 with ⟨_, hr0, _⟩ | ⟨_, hseg2⟩
      · exact False.elim (hr_ne hr0)
      · exact Prod.ext (hseg1.trans hseg2.symm) (hb1.trans hb2.symm)
  -- Step 3: Case split on outer shell seg0.r = M (where h_p2 = 0) vs. interior shell seg0.r < M.
  by_cases h_last : seg0.val.2.1 = Fin.last M
  · have h_p2_zero : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
        p.2 = b0 ∧ ∃ h_tri : p.1.val.2.2.val ≠ p.1.val.2.1.val, shellSegPred pcode M p.1 h_tri = seg0)).card = 0 := by
      apply card_filter_eq_zero_of_imp_false
      intro ⟨seg, b⟩ ⟨_, h_tri, hpred⟩
      have hr_eq : finPred seg.val.2.1 = seg0.val.2.1 :=
        congr_arg (fun u : ShellSegment pcode M => u.val.2.1) hpred
      rw [h_last] at hr_eq
      have hr_val : seg.val.2.1.val - 1 = M := congr_arg Fin.val hr_eq
      have h_lt := seg.val.2.1.isLt
      omega
    omega
  · have h_zx_inr_zero : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
        bdlStepXCheckZ pcode M (Sum.inl (Sum.inr p)) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)).card = 0 := by
      apply card_filter_eq_zero_of_imp_false
      intro ⟨s, k, v⟩ hp
      unfold bdlStepXCheckZ bdlDeltaX1 at hp; dsimp only at hp
      have hz3 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inr (Sum.inr (bxStartLink pcode M s k, v)) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h with h; injection h)
      have hz4 : (if (Sum.inr (Sum.inl (seg0, b0)) : BDLCX1 pcode M) = Sum.inr (Sum.inr (bxEndLink pcode M s k, v)) then (1 : ZMod 2) else 0) = 0 :=
        if_neg (by intro h; injection h with h; injection h)
      rw [hz3, hz4, add_zero, add_zero] at hp
      have h_seg : seg0 = mkOuterShellSegment pcode M s k := by
        rcases add_ite_one_ne_zero_imp hp with h | h <;>
          exact congr_arg (fun x : BDLCX1 pcode M => match x with | Sum.inr (Sum.inl p) => p.1 | _ => seg0) h
      exact h_last (congr_arg (fun u : ShellSegment pcode M => u.val.2.1) h_seg)
    have h_zq_inl_zero : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl p))) (Sum.inl (Sum.inr (Sum.inl (seg0, b0)))) ≠ 0)).card = 0 := by
      apply card_filter_eq_zero_of_imp_false
      intro ⟨eZ, k, bZ⟩ hp
      dsimp [bdlStepXCheckZ, bdlGXQ1] at hp
      split_ifs at hp with hc
      · exact h_last hc.1
      · exact hp rfl
    have h_p2 : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
        p.2 = b0 ∧ ∃ h_tri : p.1.val.2.2.val ≠ p.1.val.2.1.val, shellSegPred pcode M p.1 h_tri = seg0)).card ≤ 1 := by
      apply card_filter_le_one_of_unique
      intro ⟨seg1, b1⟩ ⟨hb1, htri1, hpred1⟩ ⟨seg2, b2⟩ ⟨hb2, htri2, hpred2⟩
      dsimp only at hb1 htri1 hpred1 hb2 htri2 hpred2
      have hs1 := congr_arg (fun u : ShellSegment pcode M => u.val.1) hpred1
      have hs2 := congr_arg (fun u : ShellSegment pcode M => u.val.1) hpred2
      have hk1 := congr_arg (fun u : ShellSegment pcode M => u.val.2.2) hpred1
      have hk2 := congr_arg (fun u : ShellSegment pcode M => u.val.2.2) hpred2
      have hr1 := congr_arg (fun u : ShellSegment pcode M => u.val.2.1.val) hpred1
      have hr2 := congr_arg (fun u : ShellSegment pcode M => u.val.2.1.val) hpred2
      have hr1_pos : 0 < seg1.val.2.1.val := by have := seg1.property; omega
      have hr2_pos : 0 < seg2.val.2.1.val := by have := seg2.property; omega
      dsimp [shellSegPred, finPred] at hs1 hs2 hk1 hk2 hr1 hr2
      exact Prod.ext (Subtype.ext (Prod.ext (hs1.trans hs2.symm)
        (Prod.ext (Fin.ext (by dsimp only; omega)) (hk1.trans hk2.symm)))) (hb1.trans hb2.symm)
    omega

end WeldedHierarchy
