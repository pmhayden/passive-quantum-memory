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

import Proofs.Step2DegreeAndWeld.CheckToSimplexDegreeReduction

/-!
# Uniform Z-Check Qubit Weight Bound for Three-Layer Cylinder Welding

Establishes endpoint distinctness for cylinder boundary, shell-segment, and star-arm cells, and bounds row weights of the coboundary and welding blocks `bdlDeltaX1` (`card_filter_bdlDeltaX1_qX_le_four`), `bdlGXQ1` (`card_filter_bdlGXQ1_qX_le`), and `bdlGQZ1` (`card_filter_bdlGQZ1_qQ_le`). Combines these block estimates to prove the uniform $Z$-check qubit weight bound `card_filter_bdlStepXCheckZ_q1_le` (at most 8) for `bdlStepXCheckZ`.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Equation (4) (`eq:dx-coboundary`), Equation (8) (`eq:Psi-XQ-def`), Equation (9) (`eq:Psi-QZ-def`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Boundary & Shell Segment Endpoint Distinctness Lemmas -/

lemma bxStart_ne_inr_inr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) (z : M_Z) :
    bxStart pcode M eZ k ≠ Sum.inr (Sum.inr z) := by
  dsimp [bxStart, armStart, projXq0ToBoundaryX0]
  split_ifs <;> simp

/-- Shows that the end vertex `shellSegEndV` of a shell segment is never a coarse qubit vertex. -/
lemma shellSegEndV_ne_inl {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (q : Q) :
    shellSegEndV pcode M seg ≠ Sum.inl q := by
  dsimp [shellSegEndV]
  split_ifs <;> simp

/-- Shows that the end vertex `bxEnd` of a boundary link segment is never a coarse qubit vertex. -/
lemma bxEnd_ne_inl {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) (q : Q) :
    bxEnd pcode M eZ k ≠ Sum.inl q := by
  dsimp [bxEnd, armEnd, projXq0ToBoundaryX0]
  split_ifs <;> simp

/-- Shows that the start vertex `armStart` of a subdivided $Z$-arm segment is never the terminal $Z$-endpoint. -/
lemma armStart_ne_inr_inr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) (eZ0 : ActiveZ pcode) :
    armStart pcode M eZ k ≠ Sum.inr (Sum.inr eZ0) := by
  dsimp [armStart]
  split_ifs <;> simp

/-- Shows that the end vertex `armEnd` of a subdivided $Z$-arm segment is never the initial qubit endpoint. -/
lemma armEnd_ne_inl {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) (q : Q) :
    armEnd pcode M eZ k ≠ Sum.inl q := by
  dsimp [armEnd]
  split_ifs <;> simp

/-- Proves that the start and end vertices `bxStart` and `bxEnd` of any boundary segment are distinct. -/
lemma bxStart_ne_bxEnd {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) :
    bxStart pcode M eZ k ≠ bxEnd pcode M eZ k := by
  dsimp [bxStart, bxEnd, armStart, armEnd, projXq0ToBoundaryX0]
  split_ifs with hk0 hkM
  · simp
  · simp
  · intro h
    injection h with h
    injection h with h
    injection h with _ hj
    have hj_val := congr_arg Fin.val hj
    (try dsimp at hj_val)
    omega
  · simp

/-- Proves that `bxStart` and `shellSegEndV` of any shell segment are distinct boundary vertices. -/
lemma bxStart_ne_shellSegEndV {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    bxStart pcode M seg.val.1.val.2 seg.val.2.2 ≠ shellSegEndV pcode M seg := by
  dsimp [bxStart, armStart, projXq0ToBoundaryX0, shellSegEndV]
  split_ifs with hk0 hkr
  · simp
  · simp
  · intro h
    injection h with h
    injection h with h
    injection h with _ hj
    have hj_val := congr_arg Fin.val hj
    (try dsimp at hj_val)
    omega
  · simp

/-- Proves that the start and end `ShellVertex` of any shell segment are distinct. -/
lemma shellSegStartVertex_ne_shellSegEndVertex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    shellSegStartVertex pcode M seg ≠ shellSegEndVertex pcode M seg := by
  intro h
  have hv : (shellSegStartVertex pcode M seg).val.1.val.2 = (shellSegEndVertex pcode M seg).val.1.val.2 :=
    congr_arg (fun u : ShellVertex pcode M => u.val.1.val.2) h
  exact bxStart_ne_shellSegEndV pcode M seg hv

/-- Proves that on a non-triangular shell segment ($k \ne r$), the radial parents of its
    start and end vertices are distinct. -/
lemma radialParent_start_ne_radialParent_end {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M)
    (hne : seg.val.2.2.val ≠ seg.val.2.1.val) :
    radialParentVertex pcode M (shellSegStartVertex pcode M seg) ≠
    radialParentVertex pcode M (shellSegEndVertex pcode M seg) := by
  rw [radialParent_start_eq_start_pred pcode M seg hne,
      radialParent_end_eq_end_pred pcode M seg hne]
  exact shellSegStartVertex_ne_shellSegEndVertex pcode M (shellSegPred pcode M seg hne)

/-! ## 2. Coboundary bdlDeltaX1 Qubit Support Bound (≤ 4) -/

lemma bdlDeltaX1_r0_ne_zero_imp {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (hr0 : seg.val.2.1.val = 0) (qX : BDLCX1 pcode M)
    (hne : bdlDeltaX1 pcode M (Sum.inl (seg, b)) qX ≠ 0) :
    seg.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg.val.1.val.1 seg.val.1.val.2.val.2
      ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩ ∧
    ∃ (q' : Q) (hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0)
      (hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0),
      qX = Sum.inl (cornerSpokeRadial pcode M seg.val.1.val.1 q' hX', b) ∨
      qX = Sum.inr (Sum.inl (cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ', b)) := by
  have h_le : seg.val.2.2.val ≤ seg.val.2.1.val := seg.property
  have h_tri : seg.val.2.2.val = seg.val.2.1.val := by omega
  unfold bdlDeltaX1 at hne
  dsimp only at hne
  rw [dif_pos h_tri, dif_pos hr0] at hne
  by_cases h_can : seg.val.1.val.2.val.1 = canonicalSquareQ pcode (fun _ => 0) seg.val.1.val.1 seg.val.1.val.2.val.2
      ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩
  · rw [if_pos h_can] at hne
    refine ⟨h_can, ?_⟩
    obtain ⟨q', _, hq'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    by_cases hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0
    · rw [dif_pos hX'] at hq'
      by_cases hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0
      · rw [dif_pos hZ'] at hq'
        exact ⟨q', hX', hZ', add_ite_one_ne_zero_imp hq'⟩
      · rw [dif_neg hZ'] at hq'; exact False.elim (hq' rfl)
    · rw [dif_neg hX'] at hq'; exact False.elim (hq' rfl)
  · rw [if_neg h_can] at hne; exact False.elim (hne rfl)

set_option maxHeartbeats 800000 in
/-- Bounds the qubit weight of any $Z$-check $m_{ZX} \in \mathrm{BDLCX2}(pcode, M)$ under
    `bdlDeltaX1` by $4$ whenever coarse check overlap is at most $2$. -/
lemma card_filter_bdlDeltaX1_qX_le_four {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (mZX : BDLCX2 pcode M) :
    (Finset.univ.filter (fun qX : BDLCX1 pcode M => bdlDeltaX1 pcode M mZX qX ≠ 0)).card ≤ 4 := by
  -- Step 1: Case split on interior shell segment Z-checks vs. outer boundary Z-checks.
  rcases mZX with ⟨seg, b⟩ | ⟨s, k, v⟩
  · by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · by_cases hr0 : seg.val.2.1.val = 0
  -- Step 2: For r = 0 triangular segments, bound corner spokes by 2 via hov and azimuthal edges by 2.
      · rw [card_filter_sum_eq', card_filter_sum_eq']
        have h_vert : (Finset.univ.filter (fun xv : BoundaryX0Link pcode M × Fin 2 =>
            bdlDeltaX1 pcode M (Sum.inl (seg, b)) (Sum.inr (Sum.inr xv)) ≠ 0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro xv hne
          obtain ⟨_, _, _, _, h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 _ hne
          rcases h_or with h | h
          · injection h
          · injection h with h; injection h
        have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
            bdlDeltaX1 pcode M (Sum.inl (seg, b)) (Sum.inl p) ≠ 0)).card ≤ 2 := by
          refine (card_filter_le_of_injOn_filter _
            (fun q' : Q => pcode.checkX seg.val.1.val.1 q' ≠ 0 ∧ pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0)
            (fun p => match p.1.val.val.1.val.2 with | Sum.inl q => q | _ => seg.val.1.val.2.val.1)
            ?_ ?_).trans (hov seg.val.1.val.1 seg.val.1.val.2.val.2)
          · intro p hp
            obtain ⟨_, q', hX', hZ', h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p) hp
            rcases h_or with h | h
            · injection h with hp_eq
              rcases p with ⟨sv, bX⟩
              injection hp_eq with hsv _
              subst hsv
              dsimp [cornerSpokeRadial, cornerSpoke]
              exact ⟨hX', hZ'⟩
            · injection h
          · intro p1 hp1 p2 hp2 h_eq
            obtain ⟨_, q1, hX1, _, h_or1⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p1) hp1
            obtain ⟨_, q2, hX2, _, h_or2⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inl p2) hp2
            rcases h_or1 with h1 | h1 <;> [skip; injection h1]
            rcases h_or2 with h2 | h2 <;> [skip; injection h2]
            injection h1 with hp1_eq; injection h2 with hp2_eq
            rcases p1 with ⟨sv1, b1⟩; rcases p2 with ⟨sv2, b2⟩
            injection hp1_eq with hsv1 hb1; injection hp2_eq with hsv2 hb2
            subst hsv1 hb1 hsv2 hb2
            dsimp [cornerSpokeRadial, cornerSpoke] at h_eq
            subst h_eq
            rfl
        have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
            bdlDeltaX1 pcode M (Sum.inl (seg, b)) (Sum.inr (Sum.inl p)) ≠ 0)).card ≤ 2 := by
          refine (card_filter_le_of_injOn_filter _
            (fun q' : Q => pcode.checkX seg.val.1.val.1 q' ≠ 0 ∧ pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0)
            (fun p => p.1.val.1.val.2.val.1) ?_ ?_).trans (hov seg.val.1.val.1 seg.val.1.val.2.val.2)
          · intro p hp
            obtain ⟨_, q', hX', hZ', h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inr (Sum.inl p)) hp
            rcases h_or with h | h
            · injection h
            · injection h with h; injection h with hp_eq
              rcases p with ⟨seg', bX⟩
              injection hp_eq with hseg' _
              subst hseg'
              dsimp [cornerSeg]
              exact ⟨hX', hZ'⟩
          · intro p1 hp1 p2 hp2 h_eq
            obtain ⟨_, q1, hX1, hZ1, h_or1⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inr (Sum.inl p1)) hp1
            obtain ⟨_, q2, hX2, hZ2, h_or2⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 (Sum.inr (Sum.inl p2)) hp2
            rcases h_or1 with h1 | h1 <;> [injection h1; skip]
            rcases h_or2 with h2 | h2 <;> [injection h2; skip]
            injection h1 with h1; injection h1 with hp1_eq
            injection h2 with h2; injection h2 with hp2_eq
            rcases p1 with ⟨seg1, b1⟩; rcases p2 with ⟨seg2, b2⟩
            injection hp1_eq with hseg1 hb1; injection hp2_eq with hseg2 hb2
            subst hseg1 hb1 hseg2 hb2
            dsimp [cornerSeg] at h_eq
            subst h_eq
            rfl
        omega
  -- Step 3: For r > 0 or non-triangular segments, apply card_filter_three/four_indicators.
      · dsimp [bdlDeltaX1]
        simp only [dif_pos h_tri, dif_neg hr0]
        exact (card_filter_three_indicators_le_three _ _ _).trans (by omega)
    · dsimp [bdlDeltaX1]
      simp only [dif_neg h_tri]
      exact card_filter_four_indicators_le_four _ _ _ _
  · dsimp [bdlDeltaX1]
    exact card_filter_four_indicators_le_four _ _ _ _

/-! ## 3. Coupling Map Support Bounds & Total Z-Check Weight Bound (≤ 8) -/

lemma card_filter_bdlGXQ1_qX_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdQX : ∀ q : Q, (Finset.univ.filter (fun x : M_X => pcode.checkX x q ≠ 0)).card ≤ 4)
    (mZQ : BDLCQ2 pcode M) :
    (Finset.univ.filter (fun qX : BDLCX1 pcode M => bdlGXQ1 pcode M mZQ qX ≠ 0)).card ≤ 4 := by
  rw [card_filter_sum_eq', card_filter_sum_eq']
  have h_rad : (Finset.univ.filter (fun p : RadialVertex pcode M × Fin 3 =>
      bdlGXQ1 pcode M mZQ (Sum.inl p) ≠ 0)).card = 0 :=
    card_filter_eq_zero_of_imp_false _ (fun p hp => by rcases mZQ with _ | _ <;> exact hp rfl)
  -- Step 1: Case split on subdivided Z-arm checks vs. vertical boundary Z-checks.
  rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
  · have h_vert : (Finset.univ.filter (fun xv : BoundaryX0Link pcode M × Fin 2 =>
        bdlGXQ1 pcode M (Sum.inl (eZ, k, bZ)) (Sum.inr (Sum.inr xv)) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ hp => hp rfl)
    have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
        bdlGXQ1 pcode M (Sum.inl (eZ, k, bZ)) (Sum.inr (Sum.inl p)) ≠ 0)).card ≤ 4 := by
      refine (card_filter_le_of_injOn_filter _
        (fun x : M_X => pcode.checkX x eZ.val.1 ≠ 0)
        (fun p => p.1.val.1.val.1) ?_ ?_).trans (hdQX eZ.val.1)
      · intro p hp
        dsimp [bdlGXQ1] at hp
        split_ifs at hp with hc
        · exact hp
        · exact False.elim (hp rfl)
      · intro p1 hp1 p2 hp2 h_eq
        dsimp [bdlGXQ1] at hp1 hp2
        split_ifs at hp1 with hc1 <;> [skip; exact False.elim (hp1 rfl)]
        split_ifs at hp2 with hc2 <;> [skip; exact False.elim (hp2 rfl)]
        rcases hc1 with ⟨hr1, heZ1, hk1, hb1⟩
        rcases hc2 with ⟨hr2, heZ2, hk2, hb2⟩
        apply Prod.ext
        · exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h_eq (heZ1.trans heZ2.symm)))
            (Prod.ext (hr1.trans hr2.symm) (hk1.trans hk2.symm)))
        · exact hb1.trans hb2.symm
    omega
  -- Step 2: Bound the vertical boundary sector via injective projection to coarse X-checks.
  · have h_azim : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
        bdlGXQ1 pcode M (Sum.inr (eZ, v)) (Sum.inr (Sum.inl p)) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ hp => hp rfl)
    have h_vert : (Finset.univ.filter (fun p : BoundaryX0Link pcode M × Fin 2 =>
        bdlGXQ1 pcode M (Sum.inr (eZ, v)) (Sum.inr (Sum.inr p)) ≠ 0)).card ≤ 4 := by
      refine (card_filter_le_of_injOn_filter _
        (fun x : M_X => pcode.checkX x eZ.val.1 ≠ 0)
        (fun p => p.1.val.1) ?_ ?_).trans (hdQX eZ.val.1)
      · intro ⟨xv, vX⟩ hxv
        dsimp [bdlGXQ1] at hxv
        split_ifs at hxv with hc
        · exact hxv
        · exact False.elim (hxv rfl)
      · intro ⟨xv1, v1⟩ hxv1 ⟨xv2, v2⟩ hxv2 h_eq
        dsimp [bdlGXQ1] at hxv1 hxv2 h_eq
        split_ifs at hxv1 with hc1 <;> [skip; exact False.elim (hxv1 rfl)]
        split_ifs at hxv2 with hc2 <;> [skip; exact False.elim (hxv2 rfl)]
        exact Prod.ext (Subtype.ext (Prod.ext h_eq (hc1.1.trans hc2.1.symm))) (hc1.2.trans hc2.2.symm)
    omega

/-- Bounds the `BDLCQ1` support of any coarse $Z$-check $m_{ZZ} \in \mathrm{BDLCZ2}(M_Z)$ under
    `bdlGQZ1` by $8$ whenever $d_Z \le 8$. -/
lemma card_filter_bdlGQZ1_qQ_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdZ : ∀ z : M_Z, (Finset.univ.filter (fun q : Q => pcode.checkZ z q ≠ 0)).card ≤ 8)
    (mZZ : BDLCZ2 M_Z) :
    (Finset.univ.filter (fun qQ : BDLCQ1 pcode M => bdlGQZ1 pcode M mZZ qQ ≠ 0)).card ≤ 8 := by
  refine (card_filter_le_of_injOn_filter _
    (fun q : Q => pcode.checkZ mZZ.1 q ≠ 0)
    (fun qQ => xq0OwnerQ pcode M qQ.1) ?_ ?_).trans (hdZ mZZ.1)
  · intro qQ hqQ
    rcases qQ with ⟨v0, b0⟩
    rcases v0 with q | ⟨_ | eZ⟩
    · exact False.elim (hqQ rfl)
    · exact False.elim (hqQ rfl)
    · dsimp [bdlGQZ1, xq0OwnerQ] at hqQ ⊢
      split_ifs at hqQ with hc
      · rw [← hc.1]; exact eZ.property
      · exact False.elim (hqQ rfl)
  · intro qQ1 hqQ1 qQ2 hqQ2 h_eq
    rcases qQ1 with ⟨v1, b1⟩; rcases qQ2 with ⟨v2, b2⟩
    rcases v1 with _ | ⟨_ | eZ1⟩ <;> [exact False.elim (hqQ1 rfl); exact False.elim (hqQ1 rfl); skip]
    rcases v2 with _ | ⟨_ | eZ2⟩ <;> [exact False.elim (hqQ2 rfl); exact False.elim (hqQ2 rfl); skip]
    dsimp [bdlGQZ1, xq0OwnerQ] at hqQ1 hqQ2 h_eq
    split_ifs at hqQ1 with hc1 <;> [skip; exact False.elim (hqQ1 rfl)]
    split_ifs at hqQ2 with hc2 <;> [skip; exact False.elim (hqQ2 rfl)]
    apply Prod.ext
    · exact congr_arg (fun e => Sum.inr (Sum.inr e)) (Subtype.ext (Prod.ext h_eq (hc1.1.trans hc2.1.symm)))
    · exact hc1.2.trans hc2.2.symm

/-- **Cylinder $Z$-Check Weight Bound (Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.11)**:
    Every $Z$-check $m_Z \in \mathrm{BDLStepXMZ}(pcode, M)$ acts on at most $8$ qubits in `BDLStepXQ`. -/
lemma card_filter_bdlStepXCheckZ_q1_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdZ : ∀ z : M_Z, (Finset.univ.filter (fun q : Q => pcode.checkZ z q ≠ 0)).card ≤ 8)
    (hdQX : ∀ q : Q, (Finset.univ.filter (fun x : M_X => pcode.checkX x q ≠ 0)).card ≤ 4)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (mZ : BDLStepXMZ pcode M) :
    (Finset.univ.filter (fun q1 : BDLStepXQ pcode M => bdlStepXCheckZ pcode M mZ q1 ≠ 0)).card ≤ 8 := by
  rw [card_filter_sum_eq']
  -- Step 1: Dispatch across BDLCX2, BDLCQ2, and BDLCZ2 Z-check sectors and sum the bounds.
  rcases mZ with mZX | ⟨mZQ | mZZ⟩
  · have h1 := card_filter_bdlDeltaX1_qX_le_four pcode M hov mZX
    have h1_eq : (Finset.univ.filter (fun a : BDLCX1 pcode M =>
        bdlStepXCheckZ pcode M (Sum.inl mZX) (Sum.inl a) ≠ 0)).card =
        (Finset.univ.filter (fun qX : BDLCX1 pcode M => bdlDeltaX1 pcode M mZX qX ≠ 0)).card :=
      card_filter_iff _ _ (fun _ => Iff.rfl)
    have h2 : (Finset.univ.filter (fun b : BDLCQ1 pcode M =>
        bdlStepXCheckZ pcode M (Sum.inl mZX) (Sum.inr b) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
    omega
  · have h1 := card_filter_bdlGXQ1_qX_le pcode M hdQX mZQ
    have h1_eq : (Finset.univ.filter (fun a : BDLCX1 pcode M =>
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inl mZQ)) (Sum.inl a) ≠ 0)).card =
        (Finset.univ.filter (fun qX : BDLCX1 pcode M => bdlGXQ1 pcode M mZQ qX ≠ 0)).card :=
      card_filter_iff _ _ (fun _ => Iff.rfl)
    have h2 := card_filter_bdlDeltaQ1_qQ_le_two pcode M mZQ
    have h2_eq : (Finset.univ.filter (fun b : BDLCQ1 pcode M =>
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inl mZQ)) (Sum.inr b) ≠ 0)).card =
        (Finset.univ.filter (fun qQ : BDLCQ1 pcode M => bdlDeltaQ1 pcode M mZQ qQ ≠ 0)).card :=
      card_filter_iff _ _ (fun _ => Iff.rfl)
    omega
  · have h1 : (Finset.univ.filter (fun a : BDLCX1 pcode M =>
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inl a) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
    have h2 := card_filter_bdlGQZ1_qQ_le pcode M hdZ mZZ
    have h2_eq : (Finset.univ.filter (fun b : BDLCQ1 pcode M =>
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inr b) ≠ 0)).card =
        (Finset.univ.filter (fun qQ : BDLCQ1 pcode M => bdlGQZ1 pcode M mZZ qQ ≠ 0)).card :=
      card_filter_iff _ _ (fun _ => Iff.rfl)
    omega

end WeldedHierarchy
