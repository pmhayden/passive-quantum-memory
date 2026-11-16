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

import Proofs.Step2DegreeAndWeld.CylinderQubitZDegreeInterior

/-!
# Uniform Qubit Z-Check Degree Bound Across Cylinder and Star Sectors

Proves `card_filter_bdlStepXCheckZ_mZ_le`, establishing that every qubit in `BDLStepXQ` has `bdlStepXCheckZ` degree at most 4 whenever input qubits have $Z$-check degree at most 4. Combines the interior radial and azimuthal cylinder bounds with explicit degree analyses on outer-boundary vertical cylinder qubits and star-interface qubits.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Equation (6) (`eq:dq-coboundary`), Equation (9) (`eq:Psi-QZ-def`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Complete Cylinder Qubit Z-Degree Bound (Outer Boundary & BDLCQ1 Sectors) -/

set_option maxHeartbeats 800000 in
/-- **Cylinder Qubit $Z$-Degree Bound (Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.11)**:
    Every qubit $q_1 \in \mathrm{BDLStepXQ}(pcode, M)$ participates in at most $4$ $Z$-checks
    in `BDLStepXMZ pcode M` whenever $d_{QZ} \le 4$ and coarse check overlap is at most $2$. -/
lemma card_filter_bdlStepXCheckZ_mZ_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hdQZ : ∀ q : Q, (Finset.univ.filter (fun z : M_Z => pcode.checkZ z q ≠ 0)).card ≤ 4)
    (hov : ∀ (x : M_X) (z : M_Z),
      (Finset.univ.filter (fun q : Q => pcode.checkX x q ≠ 0 ∧ pcode.checkZ z q ≠ 0)).card ≤ 2)
    (q1 : BDLStepXQ pcode M) :
    (Finset.univ.filter (fun mZ : BDLStepXMZ pcode M => bdlStepXCheckZ pcode M mZ q1 ≠ 0)).card ≤ 4 := by
  -- Step 1: Dispatch radial vertex and azimuthal segment qubits to interior helper lemmas.
  rcases q1 with qX | ⟨v0, b0⟩
  · rcases qX with ⟨rv0, b0⟩ | ⟨⟨seg0, b0⟩ | ⟨xv0, v0⟩⟩
    · exact card_filter_bdlStepXCheckZ_mZ_rv_le pcode M hdQZ hov rv0 b0
    · exact card_filter_bdlStepXCheckZ_mZ_seg_le pcode M seg0 b0
    -- Step 2: Bound Z-check degree for outer boundary vertical qubits (xv0, v0).
    · have h_zz : (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inl (Sum.inr (Sum.inr (xv0, v0)))) ≠ 0)).card = 0 :=
        card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
      rw [card_filter_sum_eq', card_filter_sum_eq', card_filter_sum_eq', card_filter_sum_eq']
      have h_zx_inl : (Finset.univ.filter (fun p : ShellSegment pcode M × Fin 3 =>
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inr (Sum.inr (xv0, v0)))) ≠ 0)).card = 0 := by
        apply card_filter_eq_zero_of_imp_false
        intro ⟨seg, b⟩ hp
        by_cases hr0 : seg.val.2.1.val = 0
        · obtain ⟨_, _, _, _, h_or⟩ := bdlDeltaX1_r0_ne_zero_imp pcode M seg b hr0 _ hp
          rcases h_or with h | h
          · injection h
          · injection h with h; injection h
        · unfold bdlStepXCheckZ bdlDeltaX1 at hp; dsimp only at hp
          by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
          · rw [dif_pos h_tri, dif_neg hr0] at hp
            rcases add_ne_zero_imp hp with h12 | h3
            · rcases add_ne_zero_imp h12 with h1 | h2
              · have h := ite_one_ne_zero_imp h1; injection h
              · have h := ite_one_ne_zero_imp h2; injection h
            · have h := ite_one_ne_zero_imp h3; injection h with h; injection h
          · rw [dif_neg h_tri] at hp
            rcases add_ne_zero_imp hp with h123 | h4
            · rcases add_ne_zero_imp h123 with h12 | h3
              · rcases add_ne_zero_imp h12 with h1 | h2
                · have h := ite_one_ne_zero_imp h1; injection h
                · have h := ite_one_ne_zero_imp h2; injection h
              · have h := ite_one_ne_zero_imp h3; injection h with h; injection h
            · have h := ite_one_ne_zero_imp h4; injection h with h; injection h
      have h_zq_inl : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl p))) (Sum.inl (Sum.inr (Sum.inr (xv0, v0)))) ≠ 0)).card = 0 :=
        card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
      have h_split_zx : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
          bdlStepXCheckZ pcode M (Sum.inl (Sum.inr p)) (Sum.inl (Sum.inr (Sum.inr (xv0, v0)))) ≠ 0)).card ≤
          (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxStartLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card +
          (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxEndLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card := by
        apply card_filter_le_add_of_or
        intro ⟨s, k, v⟩ hp
        unfold bdlStepXCheckZ bdlDeltaX1 at hp; dsimp only at hp
        have hz1 : (if (Sum.inr (Sum.inr (xv0, v0)) : BDLCX1 pcode M) = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)) then (1 : ZMod 2) else 0) = 0 :=
          if_neg (by intro h; injection h with h; injection h)
        have hz2 : (if (Sum.inr (Sum.inr (xv0, v0)) : BDLCX1 pcode M) = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ)) then (1 : ZMod 2) else 0) = 0 :=
          if_neg (by intro h; injection h with h; injection h)
        rw [hz1, hz2, add_zero, zero_add] at hp
        rcases add_ite_one_ne_zero_imp hp with h | h
        · injection h with h; injection h with h; injection h with hxv hv; exact Or.inl ⟨hxv, hv⟩
        · injection h with h; injection h with h; injection h with hxv hv; exact Or.inr ⟨hxv, hv⟩
      -- Step 3: Case split on boundary link vertex xv0.val.2 (qubit, Z-arm, or Z-check).
      rcases h_v : xv0.val.2 with q0 | ⟨⟨eZ0, j0⟩ | z0⟩
      · have h_zq_inr0 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
            bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inl (Sum.inr (Sum.inr (xv0, v0)))) ≠ 0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨eZ, v⟩ hp
          dsimp [bdlStepXCheckZ, bdlGXQ1] at hp
          split_ifs at hp with hc
          · have hc1 := hc.1; rw [h_v] at hc1; nomatch hc1
          · exact hp rfl
        have h_end0 : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxEndLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨s, k, v⟩ ⟨he, _⟩
          have hv_eq : xv0.val.2 = bxEnd pcode M s.val.2 k := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) he
          rw [h_v] at hv_eq
          exact bxEnd_ne_inl pcode M s.val.2 k q0 hv_eq.symm
        have h_start4 : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxStartLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card ≤ 4 := by
          refine (card_filter_le_of_injOn_filter _
            (fun z : M_Z => pcode.checkZ z q0 ≠ 0)
            (fun p => p.1.val.2.val.2) ?_ ?_).trans (hdQZ q0)
          · intro ⟨s, k, v⟩ ⟨hs, _⟩
            have hv_eq : xv0.val.2 = bxStart pcode M s.val.2 k := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) hs
            rw [h_v] at hv_eq
            dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv_eq
            split_ifs at hv_eq with hk0
            injection hv_eq with hq_eq; rw [hq_eq]; exact s.val.2.property
          · intro ⟨s1, k1, v1⟩ ⟨hs1, hv1_eq⟩ ⟨s2, k2, v2⟩ ⟨hs2, hv2_eq⟩ h_eq
            have hv1 : xv0.val.2 = bxStart pcode M s1.val.2 k1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) hs1
            have hv2 : xv0.val.2 = bxStart pcode M s2.val.2 k2 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) hs2
            rw [h_v] at hv1 hv2
            dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv1 hv2
            split_ifs at hv1 with hk1
            split_ifs at hv2 with hk2
            injection hv1 with hq1; injection hv2 with hq2
            have hx1 : xv0.val.1 = s1.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) hs1
            have hx2 : xv0.val.1 = s2.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) hs2
            exact Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2)
              (Subtype.ext (Prod.ext (hq1.symm.trans hq2) h_eq))))
              (Prod.ext (Fin.ext (hk1.trans hk2.symm)) (hv1_eq.symm.trans hv2_eq))
        omega
      · have h_zq_inr0 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
            bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inl (Sum.inr (Sum.inr (xv0, v0)))) ≠ 0)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨eZ, v⟩ hp
          dsimp [bdlStepXCheckZ, bdlGXQ1] at hp
          rw [h_v] at hp
          split_ifs at hp with hc
          · nomatch hc.1
          · exact hp rfl
        have h_start1 : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxStartLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨s1, k1, v1⟩ ⟨hs1, hv1_eq⟩ ⟨s2, k2, v2⟩ ⟨hs2, hv2_eq⟩
          dsimp only at hs1 hs2 hv1_eq hv2_eq
          have hv1 : xv0.val.2 = bxStart pcode M s1.val.2 k1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) hs1
          have hv2 : xv0.val.2 = bxStart pcode M s2.val.2 k2 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) hs2
          rw [h_v] at hv1 hv2
          dsimp [bxStart, armStart, projXq0ToBoundaryX0] at hv1 hv2
          split_ifs at hv1 with hk1
          split_ifs at hv2 with hk2
          injection hv1 with hv1; injection hv1 with hv1; injection hv1 with heZ1 hj1
          injection hv2 with hv2; injection hv2 with hv2; injection hv2 with heZ2 hj2
          have hj1_val := congr_arg Fin.val hj1; (try dsimp at hj1_val)
          have hj2_val := congr_arg Fin.val hj2; (try dsimp at hj2_val)
          have hx1 : xv0.val.1 = s1.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) hs1
          have hx2 : xv0.val.1 = s2.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) hs2
          exact Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2) (heZ1.symm.trans heZ2)))
            (Prod.ext (Fin.ext (by dsimp only; omega)) (hv1_eq.symm.trans hv2_eq))
        have h_end1 : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxEndLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card ≤ 1 := by
          apply card_filter_le_one_of_unique
          intro ⟨s1, k1, v1⟩ ⟨he1, hv1_eq⟩ ⟨s2, k2, v2⟩ ⟨he2, hv2_eq⟩
          dsimp only at he1 he2 hv1_eq hv2_eq
          have hv1 : xv0.val.2 = bxEnd pcode M s1.val.2 k1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) he1
          have hv2 : xv0.val.2 = bxEnd pcode M s2.val.2 k2 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) he2
          rw [h_v] at hv1 hv2
          dsimp [bxEnd, armEnd, projXq0ToBoundaryX0] at hv1 hv2
          split_ifs at hv1 with hk1 <;> [skip; (injection hv1 with hv1; injection hv1)]
          split_ifs at hv2 with hk2 <;> [skip; (injection hv2 with hv2; injection hv2)]
          injection hv1 with hv1; injection hv1 with hv1; injection hv1 with heZ1 hj1
          injection hv2 with hv2; injection hv2 with hv2; injection hv2 with heZ2 hj2
          have hj1_val := congr_arg Fin.val hj1; (try dsimp at hj1_val)
          have hj2_val := congr_arg Fin.val hj2; (try dsimp at hj2_val)
          have hx1 : xv0.val.1 = s1.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) he1
          have hx2 : xv0.val.1 = s2.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) he2
          exact Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2) (heZ1.symm.trans heZ2)))
            (Prod.ext (Fin.ext (by dsimp only; omega)) (hv1_eq.symm.trans hv2_eq))
        omega
      · have h_start0 : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxStartLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card = 0 := by
          apply card_filter_eq_zero_of_imp_false
          intro ⟨s, k, v⟩ ⟨hs, _⟩
          have hv_eq : xv0.val.2 = bxStart pcode M s.val.2 k := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) hs
          rw [h_v] at hv_eq
          exact bxStart_ne_inr_inr pcode M s.val.2 k z0 hv_eq.symm
        have h_end2 : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) × Fin 2 => xv0 = bxEndLink pcode M p.1 p.2.1 ∧ v0 = p.2.2)).card ≤ 2 := by
          refine (card_filter_le_of_injOn_filter _
            (fun q : Q => pcode.checkX xv0.val.1 q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0)
            (fun p => p.1.val.2.val.1) ?_ ?_).trans (hov xv0.val.1 z0)
          · intro ⟨s, k, v⟩ ⟨he, _⟩
            have hx : xv0.val.1 = s.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) he
            have hv_eq : xv0.val.2 = bxEnd pcode M s.val.2 k := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) he
            rw [h_v] at hv_eq
            dsimp [bxEnd, armEnd, projXq0ToBoundaryX0] at hv_eq
            split_ifs at hv_eq with hk <;> [injection hv_eq with hv_eq; skip]; (try injection hv_eq)
            injection hv_eq with hv_eq; injection hv_eq with hz_eq
            rw [hx, hz_eq]
            exact ⟨s.property, s.val.2.property⟩
          · intro ⟨s1, k1, v1⟩ ⟨he1, hv1_eq⟩ ⟨s2, k2, v2⟩ ⟨he2, hv2_eq⟩ h_eq
            dsimp only at he1 he2 h_eq hv1_eq hv2_eq
            have hx1 : xv0.val.1 = s1.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) he1
            have hx2 : xv0.val.1 = s2.val.1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.1) he2
            have hv1 : xv0.val.2 = bxEnd pcode M s1.val.2 k1 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) he1
            have hv2 : xv0.val.2 = bxEnd pcode M s2.val.2 k2 := congr_arg (fun u : BoundaryX0Link pcode M => u.val.2) he2
            rw [h_v] at hv1 hv2
            dsimp [bxEnd, armEnd, projXq0ToBoundaryX0] at hv1 hv2
            split_ifs at hv1 with hk1 <;> [injection hv1 with hv1; skip]; (try injection hv1)
            split_ifs at hv2 with hk2 <;> [injection hv2 with hv2; skip]; (try injection hv2)
            injection hv1 with hv1; injection hv1 with hz1
            injection hv2 with hv2; injection hv2 with hz2
            exact Prod.ext (Subtype.ext (Prod.ext (hx1.symm.trans hx2)
              (Subtype.ext (Prod.ext h_eq (hz1.symm.trans hz2)))))
              (Prod.ext (Fin.ext (by dsimp only; omega)) (hv1_eq.symm.trans hv2_eq))
        have h_zq_inr2 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
            bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inl (Sum.inr (Sum.inr (xv0, v0)))) ≠ 0)).card ≤ 2 := by
          refine (card_filter_le_of_injOn_filter _
            (fun q : Q => pcode.checkX xv0.val.1 q ≠ 0 ∧ pcode.checkZ z0 q ≠ 0)
            (fun p => p.1.val.1) ?_ ?_).trans (hov xv0.val.1 z0)
          · intro ⟨eZ, v⟩ hp
            dsimp [bdlStepXCheckZ, bdlGXQ1] at hp
            rw [h_v] at hp
            split_ifs at hp with hc <;> [skip; exact False.elim (hp rfl)]
            injection hc.1 with hc1; injection hc1 with hz_eq
            rw [hz_eq]; exact ⟨hp, eZ.property⟩
          · intro ⟨eZ1, v1⟩ hp1 ⟨eZ2, v2⟩ hp2 h_eq
            dsimp [bdlStepXCheckZ, bdlGXQ1] at hp1 hp2 h_eq
            rw [h_v] at hp1 hp2
            split_ifs at hp1 with hc1 <;> [skip; exact False.elim (hp1 rfl)]
            split_ifs at hp2 with hc2 <;> [skip; exact False.elim (hp2 rfl)]
            injection hc1.1 with hc1_1; injection hc1_1 with hz1
            injection hc2.1 with hc2_1; injection hc2_1 with hz2
            exact Prod.ext (Subtype.ext (Prod.ext h_eq (hz1.symm.trans hz2))) (hc1.2.symm.trans hc2.2)
        omega
  -- Step 4: Bound Z-check degree for qubit-cylinder qubits (v0, b0) in BDLCQ1.
  · rw [card_filter_sum_eq', card_filter_sum_eq']
    have h_zx1 : (Finset.univ.filter (fun a : ShellSegment pcode M × Fin 3 =>
        bdlStepXCheckZ pcode M (Sum.inl (Sum.inl a)) (Sum.inr (v0, b0)) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
    have h_zx2 : (Finset.univ.filter (fun b : ActiveZLink pcode × Fin (M + 1) × Fin 2 =>
        bdlStepXCheckZ pcode M (Sum.inl (Sum.inr b)) (Sum.inr (v0, b0)) ≠ 0)).card = 0 :=
      card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
    rw [h_zx1, h_zx2, add_zero, zero_add, card_filter_sum_eq']
    rcases v0 with q0 | ⟨⟨eZ0, j0⟩ | eZ0⟩
    · have h_zz0 : (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inr (Sum.inl q0, b0)) ≠ 0)).card = 0 :=
        card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
      have h_zq_inr0 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inr (Sum.inl q0, b0)) ≠ 0)).card = 0 := by
        apply card_filter_eq_zero_of_imp_false
        intro ⟨eZ, v⟩ hp
        unfold bdlStepXCheckZ bdlDeltaQ1 at hp; dsimp only at hp
        rcases add_ite_one_ne_zero_imp hp with h | h <;> (injection h with h _; injection h)
      have h_zq_inl4 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl p))) (Sum.inr (Sum.inl q0, b0)) ≠ 0)).card ≤ 4 := by
        refine (card_filter_le_of_injOn_filter _
          (fun z : M_Z => pcode.checkZ z q0 ≠ 0)
          (fun p => p.1.val.2) ?_ ?_).trans (hdQZ q0)
        · intro ⟨eZ, k, bZ⟩ hp
          unfold bdlStepXCheckZ bdlDeltaQ1 at hp; dsimp only at hp
          rcases add_ite_one_ne_zero_imp hp with h | h
          · injection h with hv _
            dsimp [armStart] at hv
            split_ifs at hv with hk0
            injection hv with hq_eq; rw [hq_eq]; exact eZ.property
          · injection h with hv _
            exact False.elim (armEnd_ne_inl pcode M eZ k q0 hv.symm)
        · intro ⟨eZ1, k1, bZ1⟩ hp1 ⟨eZ2, k2, bZ2⟩ hp2 h_eq
          unfold bdlStepXCheckZ bdlDeltaQ1 at hp1 hp2; dsimp only at hp1 hp2
          rcases add_ite_one_ne_zero_imp hp1 with h1 | h1 <;>
            [skip; (injection h1 with hv1 _; exact False.elim (armEnd_ne_inl pcode M eZ1 k1 q0 hv1.symm))]
          rcases add_ite_one_ne_zero_imp hp2 with h2 | h2 <;>
            [skip; (injection h2 with hv2 _; exact False.elim (armEnd_ne_inl pcode M eZ2 k2 q0 hv2.symm))]
          injection h1 with hv1 hb1; injection h2 with hv2 hb2
          dsimp [armStart] at hv1 hv2
          split_ifs at hv1 with hk1
          split_ifs at hv2 with hk2
          injection hv1 with hq1; injection hv2 with hq2
          exact Prod.ext (Subtype.ext (Prod.ext (hq1.symm.trans hq2) h_eq))
            (Prod.ext (Fin.ext (hk1.trans hk2.symm)) (hb1.symm.trans hb2))
      rw [card_filter_sum_eq']; omega
    · have h_zz0 : (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inr (Sum.inr (Sum.inl (eZ0, j0)), b0)) ≠ 0)).card = 0 :=
        card_filter_eq_zero_of_imp_false _ (fun _ h => h rfl)
      have h_zq_inr0 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inr (Sum.inr (Sum.inl (eZ0, j0)), b0)) ≠ 0)).card = 0 := by
        apply card_filter_eq_zero_of_imp_false
        intro ⟨eZ, v⟩ hp
        unfold bdlStepXCheckZ bdlDeltaQ1 at hp; dsimp only at hp
        rcases add_ite_one_ne_zero_imp hp with h | h <;> (injection h with h _; injection h with h; injection h)
      have h_split := card_filter_le_add_of_or
        (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl p))) (Sum.inr (Sum.inr (Sum.inl (eZ0, j0)), b0)) ≠ 0)
        (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          (Sum.inr (Sum.inl (eZ0, j0)), b0) = (armStart pcode M p.1 p.2.1, p.2.2))
        (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          (Sum.inr (Sum.inl (eZ0, j0)), b0) = (armEnd pcode M p.1 p.2.1, p.2.2))
        (fun _ hp => by unfold bdlStepXCheckZ bdlDeltaQ1 at hp; exact add_ite_one_ne_zero_imp hp)
      have h_s1 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          (Sum.inr (Sum.inl (eZ0, j0)), b0) = (armStart pcode M p.1 p.2.1, p.2.2))).card ≤ 1 := by
        apply card_filter_le_one_of_unique
        intro ⟨eZ1, k1, bZ1⟩ h1 ⟨eZ2, k2, bZ2⟩ h2
        dsimp only at h1 h2
        injection h1 with hv1 hb1; injection h2 with hv2 hb2
        dsimp [armStart] at hv1 hv2
        split_ifs at hv1 with hk1
        split_ifs at hv2 with hk2
        injection hv1 with hv1; injection hv1 with hv1; injection hv1 with heZ1 hj1
        injection hv2 with hv2; injection hv2 with hv2; injection hv2 with heZ2 hj2
        have hj1_val := congr_arg Fin.val hj1; (try dsimp at hj1_val)
        have hj2_val := congr_arg Fin.val hj2; (try dsimp at hj2_val)
        exact Prod.ext (heZ1.symm.trans heZ2) (Prod.ext (Fin.ext (by dsimp only; omega)) (hb1.symm.trans hb2))
      have h_e1 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          (Sum.inr (Sum.inl (eZ0, j0)), b0) = (armEnd pcode M p.1 p.2.1, p.2.2))).card ≤ 1 := by
        apply card_filter_le_one_of_unique
        intro ⟨eZ1, k1, bZ1⟩ h1 ⟨eZ2, k2, bZ2⟩ h2
        dsimp only at h1 h2
        injection h1 with hv1 hb1; injection h2 with hv2 hb2
        dsimp [armEnd] at hv1 hv2
        split_ifs at hv1 with hk1 <;> [skip; (injection hv1 with hv1; injection hv1)]
        split_ifs at hv2 with hk2 <;> [skip; (injection hv2 with hv2; injection hv2)]
        injection hv1 with hv1; injection hv1 with hv1; injection hv1 with heZ1 hj1
        injection hv2 with hv2; injection hv2 with hv2; injection hv2 with heZ2 hj2
        have hj1_val := congr_arg Fin.val hj1; (try dsimp at hj1_val)
        have hj2_val := congr_arg Fin.val hj2; (try dsimp at hj2_val)
        exact Prod.ext (heZ1.symm.trans heZ2) (Prod.ext (Fin.ext (by dsimp only; omega)) (hb1.symm.trans hb2))
      rw [card_filter_sum_eq']; omega
    · have h_zz1 : (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inr (Sum.inr (Sum.inr eZ0), b0)) ≠ 0)).card ≤ 1 := by
        apply card_filter_le_one_of_unique
        intro mZZ1 hp1 mZZ2 hp2
        dsimp [bdlStepXCheckZ, bdlGQZ1] at hp1 hp2
        split_ifs at hp1 with hc1 <;> [skip; exact False.elim (hp1 rfl)]
        split_ifs at hp2 with hc2 <;> [skip; exact False.elim (hp2 rfl)]
        exact Prod.ext (hc1.1.symm.trans hc2.1) (hc1.2.symm.trans hc2.2)
      have h_zq_inr2 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inr (Sum.inr (Sum.inr eZ0), b0)) ≠ 0)).card ≤ 2 := by
        have h_sub : Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
            bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr p))) (Sum.inr (Sum.inr (Sum.inr eZ0), b0)) ≠ 0) ⊆
            {(eZ0, 0), (eZ0, 1)} := by
          intro ⟨eZ, v⟩ hp
          rw [Finset.mem_filter] at hp
          have hp1 := hp.2
          unfold bdlStepXCheckZ bdlDeltaQ1 at hp1; dsimp only at hp1
          have heZ_eq : eZ = eZ0 := by
            rcases add_ite_one_ne_zero_imp hp1 with h | h <;>
              (injection h with hv _; injection hv with hv; injection hv with hv; exact hv.symm)
          subst heZ_eq
          rw [Finset.mem_insert, Finset.mem_singleton]
          fin_cases v
          · exact Or.inl rfl
          · exact Or.inr rfl
        exact (Finset.card_le_card h_sub).trans Finset.card_le_two
      have h_zq_inl1 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl p))) (Sum.inr (Sum.inr (Sum.inr eZ0), b0)) ≠ 0)).card ≤ 1 := by
        apply card_filter_le_one_of_unique
        intro ⟨eZ1, k1, bZ1⟩ hp1 ⟨eZ2, k2, bZ2⟩ hp2
        unfold bdlStepXCheckZ bdlDeltaQ1 at hp1 hp2; dsimp only at hp1 hp2
        rcases add_ite_one_ne_zero_imp hp1 with h1 | h1 <;>
          [(injection h1 with hv1 _; exact False.elim (armStart_ne_inr_inr pcode M eZ1 k1 eZ0 hv1.symm)); skip]
        rcases add_ite_one_ne_zero_imp hp2 with h2 | h2 <;>
          [(injection h2 with hv2 _; exact False.elim (armStart_ne_inr_inr pcode M eZ2 k2 eZ0 hv2.symm)); skip]
        injection h1 with hv1 hb1; injection h2 with hv2 hb2
        dsimp [armEnd] at hv1 hv2
        split_ifs at hv1 with hk1 <;> [(injection hv1 with hv1; injection hv1); skip]
        split_ifs at hv2 with hk2 <;> [(injection hv2 with hv2; injection hv2); skip]
        injection hv1 with hv1; injection hv1 with heZ1
        injection hv2 with hv2; injection hv2 with heZ2
        exact Prod.ext (heZ1.symm.trans heZ2) (Prod.ext (Fin.ext (by dsimp only; omega)) (hb1.symm.trans hb2))
      rw [card_filter_sum_eq']; omega

end WeldedHierarchy
