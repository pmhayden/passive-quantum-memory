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

import Proofs.Step1LLLDensity.Step2UnitBallDensityBound

/-!
# Preservation of the Non-Isolated Qubits Invariant Across Cylinder Welding Steps

Proves `hasNoIsolatedQ_bdlCylinderStepX`, showing that three-layer cylinder welding preserves `HasNoIsolatedQ`, and lifts this invariant inductively across arbitrary `(bdlStepZ ∘ bdlStepX)` iterations from the planar surface code seed (`hasNoIsolatedQ_iterate_stepZX`). Also establishes the numerical spherical-cap separation bound `bdlGamma_le_five_halves` and coordinate-difference bounds under squared Euclidean distance 64.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Preservation of HasNoIsolatedQ Under Cylinder Replacement -/

lemma hasNoIsolatedQ_bdlCylinderStepX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode) :
    HasNoIsolatedQ (bdlCylinderStepX pcode M) := by
  constructor
  -- Step 1: Prove every qubit in an active X-check participates in at least one Z-check.
  · -- 1. Every active X-check qubit has a non-zero Z-check
    intro q ⟨mX, hmX⟩
    rcases q with ⟨⟨sv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, v⟩⟩⟩ | ⟨v0, b⟩
    · by_cases hr0 : sv.val.val.2.val = 0
      · rcases sv with ⟨⟨⟨⟨⟨x, v⟩, hp⟩, r⟩, h_in⟩, h_not_diag⟩
        (try dsimp at hr0)
        rcases v with q0 | ⟨⟨eZ, j⟩ | z0⟩
        · let hz_ex := hq.1 q0 ⟨x, hp⟩
          let z0 := Classical.choose hz_ex
          have hz0 : pcode.checkZ z0 q0 ≠ 0 := Classical.choose_spec hz_ex
          have h_ex : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0 := ⟨q0, hp, hz0⟩
          let q_can := canonicalSquareQ pcode (fun _ => 0) x z0 h_ex
          have h_can : pcode.checkX x q_can ≠ 0 ∧ pcode.checkZ z0 q_can ≠ 0 := canonicalSquareQ_spec pcode (fun _ => 0) x z0 h_ex
          let seg_can := cornerSeg pcode M x q_can z0 h_can.1 h_can.2
          use Sum.inl (Sum.inl (seg_can, b))
          dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaX1]
          have h_tri_can : seg_can.val.2.2.val = seg_can.val.2.1.val := rfl
          have hr0_can : seg_can.val.2.1.val = 0 := rfl
          have h_can_eq : seg_can.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg_can.val.1.val.1 seg_can.val.1.val.2.val.2
              ⟨seg_can.val.1.val.2.val.1, seg_can.val.1.property, seg_can.val.1.val.2.property⟩ := rfl
          rw [dif_pos h_tri_can, dif_pos hr0_can, if_pos h_can_eq]
          have h_sum : (∑ q' : Q,
              if hX' : pcode.checkX seg_can.val.1.val.1 q' ≠ 0 then
                if pcode.checkZ seg_can.val.1.val.2.val.2 q' ≠ 0 then
                  (if (Sum.inl (⟨⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩, h_not_diag⟩, b) : BDLCX1 pcode M) =
                      Sum.inl (cornerSpokeRadial pcode M seg_can.val.1.val.1 q' hX', b) then (1 : ZMod 2) else 0) + 0
                else 0
              else 0) = 1 := by
            rw [Finset.sum_eq_single q0]
            · have hX0 : pcode.checkX seg_can.val.1.val.1 q0 ≠ 0 := hp
              have hZ0 : pcode.checkZ seg_can.val.1.val.2.val.2 q0 ≠ 0 := hz0
              rw [dif_pos hX0, if_pos hZ0]
              have h_sp_eq : (Sum.inl (⟨⟨(⟨(x, Sum.inl q0), hp⟩, r), h_in⟩, h_not_diag⟩, b) : BDLCX1 pcode M) =
                  Sum.inl (cornerSpokeRadial pcode M seg_can.val.1.val.1 q0 hX0, b) := by
                congr 2
                apply Subtype.ext; apply Subtype.ext; apply Prod.ext
                · rfl
                · exact Fin.ext hr0
              rw [if_pos h_sp_eq, add_zero]
            · intro q' _ hne
              split_ifs with hX' hZ' h_sp
              · exfalso; apply hne
                injection h_sp with h1; injection h1 with h2 _
                have hv := congr_arg (fun w : RadialVertex pcode M => w.val.val.1.val.2) h2
                dsimp [cornerSpokeRadial, cornerSpoke] at hv
                injection hv with hq_eq
                exact hq_eq.symm
              · rfl
              · rfl
              · rfl
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0))
          rw [h_sum]; decide
        · dsimp [InShellR] at h_in; omega
        · exact False.elim (h_not_diag ⟨hr0, z0, rfl⟩)
      · let seg := svIncidentSeg pcode M hq sv.val
        use Sum.inl (Sum.inl (seg, b))
        obtain ⟨hr_eq, h_or⟩ := svIncidentSeg_start_or_end pcode M hq sv.val
        have hr0_seg : seg.val.2.1.val ≠ 0 := by rw [hr_eq]; exact hr0
        have h_ne := shellSegStartVertex_ne_end pcode M seg
        dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaX1]
        rcases h_or with h_start | h_end
        · have h1 : (Sum.inl (sv, b) : BDLCX1 pcode M) = Sum.inl (shellSegStartRadial pcode M seg, b) := by
            congr 2; exact Subtype.ext h_start
          have h2 : (Sum.inl (sv, b) : BDLCX1 pcode M) ≠ Sum.inl (shellSegEndRadial pcode M seg hr0_seg, b) := by
            intro hc; injection hc with hc'; injection hc' with hc''
            exact h_ne (h_start.symm.trans (congr_arg Subtype.val hc''))
          by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
          · rw [dif_pos h_tri, dif_neg hr0_seg, if_pos h1, if_neg h2]; decide
          · rw [dif_neg h_tri, if_pos h1, if_neg h2]; decide
        · have h1 : (Sum.inl (sv, b) : BDLCX1 pcode M) ≠ Sum.inl (shellSegStartRadial pcode M seg, b) := by
            intro hc; injection hc with hc'; injection hc' with hc''
            exact h_ne ((congr_arg Subtype.val hc'').symm.trans h_end)
          have h2 : (Sum.inl (sv, b) : BDLCX1 pcode M) = Sum.inl (shellSegEndRadial pcode M seg hr0_seg, b) := by
            congr 2; exact Subtype.ext h_end
          by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
          · rw [dif_pos h_tri, dif_neg hr0_seg, if_neg h1, if_pos h2]; decide
          · rw [dif_neg h_tri, if_neg h1, if_pos h2]; decide
  -- Step 2: Handle azimuthal segment, outer boundary, and Xq0 qubit sectors for Z-check incidence.
    · by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
      · by_cases hr0 : seg.val.2.1.val = 0
        · let x := seg.val.1.val.1
          let q0 := seg.val.1.val.2.val.1
          let z0 := seg.val.1.val.2.val.2
          have hX0 : pcode.checkX x q0 ≠ 0 := seg.val.1.property
          have hZ0 : pcode.checkZ z0 q0 ≠ 0 := seg.val.1.val.2.property
          have h_ex : ∃ q : Q, pcode.checkX x q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0 := ⟨q0, hX0, hZ0⟩
          let q_can := canonicalSquareQ pcode (fun _ => 0) x z0 h_ex
          have h_can : pcode.checkX x q_can ≠ 0 ∧ pcode.checkZ z0 q_can ≠ 0 := canonicalSquareQ_spec pcode (fun _ => 0) x z0 h_ex
          let seg_can := cornerSeg pcode M x q_can z0 h_can.1 h_can.2
          use Sum.inl (Sum.inl (seg_can, b))
          dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaX1]
          have h_tri_can : seg_can.val.2.2.val = seg_can.val.2.1.val := rfl
          have hr0_can : seg_can.val.2.1.val = 0 := rfl
          have h_can_eq : seg_can.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg_can.val.1.val.1 seg_can.val.1.val.2.val.2
              ⟨seg_can.val.1.val.2.val.1, seg_can.val.1.property, seg_can.val.1.val.2.property⟩ := rfl
          rw [dif_pos h_tri_can, if_pos hr0_can, if_pos h_can_eq]
          have h_sum : (∑ q' : Q,
              if hX' : pcode.checkX seg_can.val.1.val.1 q' ≠ 0 then
                if hZ' : pcode.checkZ seg_can.val.1.val.2.val.2 q' ≠ 0 then
                  0 +
                  (if (Sum.inr (Sum.inl (seg, b)) : BDLCX1 pcode M) =
                      Sum.inr (Sum.inl (cornerSeg pcode M seg_can.val.1.val.1 q' seg_can.val.1.val.2.val.2 hX' hZ', b)) then (1 : ZMod 2) else 0)
                else 0
              else 0) = 1 := by
            rw [Finset.sum_eq_single q0]
            · have hX0' : pcode.checkX seg_can.val.1.val.1 q0 ≠ 0 := hX0
              have hZ0' : pcode.checkZ seg_can.val.1.val.2.val.2 q0 ≠ 0 := hZ0
              rw [dif_pos hX0', dif_pos hZ0']
              have h_seg_eq : (Sum.inr (Sum.inl (seg, b)) : BDLCX1 pcode M) =
                  Sum.inr (Sum.inl (cornerSeg pcode M seg_can.val.1.val.1 q0 seg_can.val.1.val.2.val.2 hX0' hZ0', b)) := by
                congr 3
                apply Subtype.ext; apply Prod.ext
                · rfl
                · apply Prod.ext
                  · exact Fin.ext hr0
                  · exact Fin.ext (h_tri.trans hr0)
              rw [if_pos h_seg_eq, zero_add]
            · intro q' _ hne
              split_ifs with hX' hZ' h_cs
              · exfalso; apply hne
                injection h_cs with h1; injection h1 with h2; injection h2 with h3 _
                have hq_eq := congr_arg (fun s : ShellSegment pcode M => s.val.1.val.2.val.1) h3
                exact hq_eq.symm
              · rfl
              · rfl
              · rfl
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0))
          rw [h_sum]; decide
        · use Sum.inl (Sum.inl (seg, b))
          dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaX1]
          rw [dif_pos h_tri, if_neg hr0, if_pos rfl]; decide
      · use Sum.inl (Sum.inl (seg, b))
        dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaX1]
        have h_pred_ne : (Sum.inr (Sum.inl (seg, b)) : BDLCX1 pcode M) ≠
            Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)) := by
          intro hc
          injection hc with hc1
          injection hc1 with hc2
          injection hc2 with hc3
          have hr := congr_arg (fun s : ShellSegment pcode M => s.val.2.1.val) hc3
          dsimp [shellSegPred, finPred] at hr
          have h_lt : seg.val.2.2.val < seg.val.2.1.val := Nat.lt_of_le_of_ne seg.property h_tri
          omega
        rw [dif_neg h_tri, if_neg h_pred_ne, if_pos rfl]; decide
    · let sv := mkOuterShellVertex pcode M xv
      let seg := svIncidentSeg pcode M hq sv
      use Sum.inl (Sum.inr (seg.val.1, seg.val.2.2, v))
      obtain ⟨hr_eq, h_or⟩ := svIncidentSeg_start_or_end pcode M hq sv
      have h_seg_eq : mkOuterShellSegment pcode M seg.val.1 seg.val.2.2 = seg := by
        apply Subtype.ext; apply Prod.ext; · rfl
        · apply Prod.ext; · exact hr_eq.symm
          · rfl
      have h_ne := shellSegStartVertex_ne_end pcode M seg
      dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaX1]
      rcases h_or with h_start | h_end
      · have h1 : xv = bxStartLink pcode M seg.val.1 seg.val.2.2 := by
          have hs := shellSegStartVertex_outer pcode M seg.val.1 seg.val.2.2
          rw [h_seg_eq, ← h_start] at hs
          exact congr_arg (fun w : ShellVertex pcode M => w.val.1) hs
        have h2 : xv ≠ bxEndLink pcode M seg.val.1 seg.val.2.2 := by
          intro hc
          have he := shellSegEndVertex_outer pcode M seg.val.1 seg.val.2.2
          rw [h_seg_eq, ← hc] at he
          exact h_ne (h_start.symm.trans he.symm)
        have h1_eq : (Sum.inr (Sum.inr (xv, v)) : BDLCX1 pcode M) = Sum.inr (Sum.inr (bxStartLink pcode M seg.val.1 seg.val.2.2, v)) := by rw [h1]
        have h2_ne : (Sum.inr (Sum.inr (xv, v)) : BDLCX1 pcode M) ≠ Sum.inr (Sum.inr (bxEndLink pcode M seg.val.1 seg.val.2.2, v)) := by
          intro hc; injection hc with hc'; injection hc' with hc''; injection hc'' with hc''' _; exact h2 hc'''
        rw [if_pos h1_eq, if_neg h2_ne]; decide
      · have h2 : xv = bxEndLink pcode M seg.val.1 seg.val.2.2 := by
          have he := shellSegEndVertex_outer pcode M seg.val.1 seg.val.2.2
          rw [h_seg_eq, ← h_end] at he
          exact congr_arg (fun w : ShellVertex pcode M => w.val.1) he
        have h1 : xv ≠ bxStartLink pcode M seg.val.1 seg.val.2.2 := by
          intro hc
          have hs := shellSegStartVertex_outer pcode M seg.val.1 seg.val.2.2
          rw [h_seg_eq, ← hc] at hs
          exact h_ne (hs.trans h_end)
        have h1_ne : (Sum.inr (Sum.inr (xv, v)) : BDLCX1 pcode M) ≠ Sum.inr (Sum.inr (bxStartLink pcode M seg.val.1 seg.val.2.2, v)) := by
          intro hc; injection hc with hc'; injection hc' with hc''; injection hc'' with hc''' _; exact h1 hc'''
        have h2_eq : (Sum.inr (Sum.inr (xv, v)) : BDLCX1 pcode M) = Sum.inr (Sum.inr (bxEndLink pcode M seg.val.1 seg.val.2.2, v)) := by rw [h2]
        rw [if_neg h1_ne, if_pos h2_eq]; decide
    · rcases v0 with q0 | ⟨⟨eZ, j⟩ | eZ⟩
      · have hx_ex : ∃ x : M_X, pcode.checkX x q0 ≠ 0 := by
          rcases mX with ⟨x0, b0⟩ | ⟨sv0, b0⟩
          · dsimp [bdlCylinderStepX, bdlStepXCheckX, bdlGXQ0] at hmX
            exact False.elim (hmX rfl)
          · dsimp [bdlCylinderStepX, bdlStepXCheckX, bdlGXQ0, xq0OwnerQ] at hmX
            split_ifs at hmX with h_cond
            · exact ⟨sv0.val.1.val.1, hmX⟩
            · exact False.elim (hmX rfl)
        let hz_ex := hq.1 q0 hx_ex
        let z0 := Classical.choose hz_ex
        let hz0 := Classical.choose_spec hz_ex
        let eZ : ActiveZ pcode := ⟨(q0, z0), hz0⟩
        use Sum.inr (Sum.inl (Sum.inl (eZ, 0, b)))
        have h1 : ((Sum.inl q0, b) : BDLCQ1 pcode M) = (armStart pcode M eZ 0, b) := rfl
        have h2 : ((Sum.inl q0, b) : BDLCQ1 pcode M) ≠ (armEnd pcode M eZ 0, b) := by
          intro hc; injection hc with hc1 _; exact armStart_ne_armEnd pcode M eZ 0 hc1
        dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaQ1]
        rw [if_pos h1, if_neg h2]; decide
      · let k : Fin (M + 1) := ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self M)⟩
        use Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))
        have h2_v : (Sum.inr (Sum.inl (eZ, j)) : Xq0 pcode M) = armEnd pcode M eZ k := by
          dsimp [armEnd, k]; rw [if_pos j.isLt]
        have h2 : ((Sum.inr (Sum.inl (eZ, j)), b) : BDLCQ1 pcode M) = (armEnd pcode M eZ k, b) := by rw [h2_v]
        have h1 : ((Sum.inr (Sum.inl (eZ, j)), b) : BDLCQ1 pcode M) ≠ (armStart pcode M eZ k, b) := by
          intro hc; injection hc with hc1 _; exact armStart_ne_armEnd pcode M eZ k (hc1.symm.trans h2_v)
        dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaQ1]
        rw [if_neg h1, if_pos h2]; decide
      · use Sum.inr (Sum.inr (eZ.val.2, b))
        dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlGQZ1]
        simp
  -- Step 3: Prove every qubit in an active Z-check participates in at least one X-check.
  · -- 2. Every active Z-check qubit has a non-zero X-check
    intro q ⟨mZ, hmZ⟩
    rcases q with ⟨⟨sv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, v⟩⟩⟩ | ⟨v0, b⟩
    · use Sum.inr (sv.val, b)
      dsimp [bdlCylinderStepX, bdlStepXCheckX, bdlDeltaX0]
      by_cases hr0 : sv.val.val.2.val = 0
      · rw [if_pos hr0, if_pos rfl]; decide
      · have h_ne : (Sum.inr (sv.val, b) : BDLStepXMX pcode M) ≠ Sum.inr (radialParentVertex pcode M sv.val, b) := by
          intro hc
          injection hc with hc1
          injection hc1 with hc2
          have hr := congr_arg (fun w : ShellVertex pcode M => w.val.2.val) hc2
          dsimp [radialParentVertex, finPred] at hr
          omega
        rw [if_neg hr0, if_neg h_ne, if_pos rfl]; decide
    · use Sum.inr (shellSegStartVertex pcode M seg, b)
      have h_ne : (Sum.inr (shellSegStartVertex pcode M seg, b) : BDLStepXMX pcode M) ≠
          Sum.inr (shellSegEndVertex pcode M seg, b) := by
        intro hc; injection hc with hc1; injection hc1 with hc2
        exact shellSegStartVertex_ne_end pcode M seg hc2
      dsimp [bdlCylinderStepX, bdlStepXCheckX, bdlDeltaX0]
      rw [if_pos rfl, if_neg h_ne]; decide
    · use Sum.inr (mkOuterShellVertex pcode M xv, 0)
      have hv_ne : (Sum.inr (mkOuterShellVertex pcode M xv, (0 : Fin 3)) : BDLStepXMX pcode M) ≠
          Sum.inr (mkOuterShellVertex pcode M xv, v.succ) := by
        intro hc; injection hc with hc1; injection hc1 with _ hc2
        exact (Fin.succ_ne_zero v) hc2.symm
      dsimp [bdlCylinderStepX, bdlStepXCheckX, bdlDeltaX0]
      rw [if_pos rfl, if_neg hv_ne]; decide
    · let q0 := xq0OwnerQ pcode M v0
      have hz_ex : ∃ z : M_Z, pcode.checkZ z q0 ≠ 0 := by
        rcases v0 with q_in | ⟨⟨eZ, j⟩ | eZ⟩
        · rcases mZ with mZX | ⟨⟨⟨eZ, k, bZ⟩ | ⟨eZ, vZ⟩⟩ | mZZ⟩
          · dsimp [bdlCylinderStepX, bdlStepXCheckZ] at hmZ; exact False.elim (hmZ rfl)
          · dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaQ1] at hmZ
            by_cases h1 : ((Sum.inl q_in, b) : BDLCQ1 pcode M) = (armStart pcode M eZ k, bZ)
            · have hq_eq : q0 = eZ.val.1 :=
                (congr_arg (xq0OwnerQ pcode M) (congr_arg Prod.fst h1)).trans (xq0OwnerQ_armStart pcode M eZ k)
              exact ⟨eZ.val.2, hq_eq.symm ▸ eZ.property⟩
            · by_cases h2 : ((Sum.inl q_in, b) : BDLCQ1 pcode M) = (armEnd pcode M eZ k, bZ)
              · have hq_eq : q0 = eZ.val.1 :=
                  (congr_arg (xq0OwnerQ pcode M) (congr_arg Prod.fst h2)).trans (xq0OwnerQ_armEnd pcode M eZ k)
                exact ⟨eZ.val.2, hq_eq.symm ▸ eZ.property⟩
              · rw [if_neg h1, if_neg h2] at hmZ; exact False.elim (hmZ rfl)
          · dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlDeltaQ1] at hmZ
            exact False.elim (hmZ rfl)
          · dsimp [bdlCylinderStepX, bdlStepXCheckZ, bdlGQZ1] at hmZ
            exact False.elim (hmZ rfl)
        · exact ⟨eZ.val.2, eZ.property⟩
        · exact ⟨eZ.val.2, eZ.property⟩
      let hx_ex := hq.2 q0 hz_ex
      let x0 := Classical.choose hx_ex
      let hx0 := Classical.choose_spec hx_ex
      have hlink : InLinkOfX pcode M x0 (projXq0ToBoundaryX0 pcode M v0) := by
        rcases v0 with q_in | ⟨⟨eZ, j⟩ | eZ⟩
        · exact hx0
        · exact hx0
        · exact ⟨eZ.val.1, hx0, eZ.property⟩
      let xv : BoundaryX0Link pcode M := ⟨(x0, projXq0ToBoundaryX0 pcode M v0), hlink⟩
      use Sum.inr (mkOuterShellVertex pcode M xv, b)
      dsimp [bdlCylinderStepX, bdlStepXCheckX, bdlGXQ0, mkOuterShellVertex, xv, q0]
      rw [if_pos ⟨rfl, rfl, rfl⟩]
      exact hx0

/-! ## 2. Iterated Hierarchy Preservation & Coordinate Difference Bounds -/

lemma hasNoIsolatedQ_bdlRandomStepX (B : BundledCSSCode3D) (hq : HasNoIsolatedQ B.code) :
    HasNoIsolatedQ (bdlRandomStepX B).code :=
  hasNoIsolatedQ_bdlCylinderStepX _ _ hq

/-- Proves that the $Z$-side random welded replacement step `bdlRandomStepZ` preserves `HasNoIsolatedQ`. -/
lemma hasNoIsolatedQ_bdlRandomStepZ (B : BundledCSSCode3D) (hq : HasNoIsolatedQ B.code) :
    HasNoIsolatedQ (bdlRandomStepZ B).code :=
  hasNoIsolatedQ_dualCode _ (hasNoIsolatedQ_bdlRandomStepX (dualBundled B) (hasNoIsolatedQ_dualCode _ hq))

/-- Proves by induction on $n$ that `(bdlRandomStepZ ∘ bdlRandomStepX)^[n] bdlSurfaceSeedBundled`
    satisfies `HasNoIsolatedQ`. -/
lemma hasNoIsolatedQ_iterate_stepZX (n : ℕ) :
    HasNoIsolatedQ (((bdlRandomStepZ ∘ bdlRandomStepX)^[n] bdlSurfaceSeedBundled).code) := by
  induction n with
  | zero => exact hasNoIsolatedQ_surfaceSeed
  | succ m ih =>
    rw [Function.iterate_succ']
    exact hasNoIsolatedQ_bdlRandomStepZ _ (hasNoIsolatedQ_bdlRandomStepX _ ih)

/-- Establishes the explicit numerical upper bound $\gamma = \mathrm{bdlGamma} \le 5/2$. -/
lemma bdlGamma_le_five_halves : bdlGamma ≤ 5 / 2 := by
  dsimp [bdlGamma, bdlAlpha, bdlAlphaNat, bdlAlpha2, bdlAlpha1]
  have h_abs : |(139 / 2 / 1000 : ℝ)| ≤ 1 := by norm_num
  have h_cb := (abs_le.mp (Real.cos_bound h_abs)).1
  rw [abs_of_nonneg (by norm_num)] at h_cb
  linarith

/-- Coordinatewise bound $|p_1(a) - p_2(a)| \le 8$ whenever $\|p_1 - p_2\|^2 \le 8^2$. -/
lemma abs_coord_sub_le_of_distSq3D_le_eight_sq (p1 p2 : Point3D)
    (h : distSq3D p1 p2 ≤ 8 ^ 2) (axis : Fin 3) :
    |p1 axis - p2 axis| ≤ 8 := by
  dsimp [distSq3D] at h
  have h0 : 0 ≤ (p1 0 - p2 0) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (p1 1 - p2 1) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (p1 2 - p2 2) ^ 2 := sq_nonneg _
  have h_sq : (p1 axis - p2 axis) ^ 2 ≤ 8 ^ 2 := by
    fin_cases axis <;> { dsimp; nlinarith }
  exact abs_le.mpr (abs_le_of_sq_le_sq' h_sq (by norm_num))

end WeldedHierarchy
