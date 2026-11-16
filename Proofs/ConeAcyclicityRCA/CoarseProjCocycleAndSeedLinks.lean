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

import Proofs.ConeAcyclicityRCA.Layer1ConeCocycle

/-!
# Star-Interface Cocycle Constancy, Surface-Seed Link Connectivity, and Cylinder Differential Incidences

Proves constancy of cylinderResidualCocycle along star arms and vertical attachment edges, assembling the coarse projected cocycle coarseProjCocycle and total cylinder primitive fullCylinderCocycle. Defines the symmetric adjacency step XLinkStep (with symmetry lemma xLinkStep_symm), verifies primal and dual link connectivity on the [[5, 1, 2]] surface seed (hasConnectedXLinks_surfaceSeed), and establishes explicit incidence identities for the cylinder differentials bdlDeltaX0 and bdlDeltaX1.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.6 (`lem:block-sdr`), Proposition 3.7 (`prop:classical-hpl`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.1 (`lem:seed-code`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Subdivision Arm and Vertical Layer Constancy on BDLCQ1 -/

/-- Local arm step constancy on `Y_{q0}` assuming `cylinderResidualCocycle` vanishes on incident cylinders `Y_x`. -/
lemma cylinderResidualCocycle_arm_const_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) (b : Fin 3)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x eZ.val.1 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h (Sum.inl qX) = 0)
    (h_syn : syndrome (dualCode (bdlCylinderStepX pcode M)) h
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) = 0) :
    cylinderResidualCocycle pcode M h (Sum.inr (armStart pcode M eZ k, b)) =
    cylinderResidualCocycle pcode M h (Sum.inr (armEnd pcode M eZ k, b)) := by
  have h_syn2 : syndrome (dualCode (bdlCylinderStepX pcode M)) (cylinderResidualCocycle pcode M h)
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) = 0 := by
    dsimp [cylinderResidualCocycle, apexResidualCocycle]
    rw [syndrome_add_checkGen_dual, syndrome_add_checkGen_dual]
    exact h_syn
  dsimp [syndrome, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex] at h_syn2
  rw [Fintype.sum_sum_type] at h_syn2
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) (Sum.inl qX) *
        cylinderResidualCocycle pcode M h (Sum.inl qX)) = 0 := by
    apply Finset.sum_eq_zero
    intro qX _
    rcases qX with _ | ⟨⟨seg, bX⟩ | _⟩
    · exact zero_mul _
    · dsimp [bdlStepXCheckZ, bdlGXQ1]
      split_ifs with hc
      · by_cases hx : pcode.checkX seg.val.1.val.1 eZ.val.1 = 0
        · rw [hx, zero_mul]
        · rw [h_zero_X seg.val.1.val.1 hx (Sum.inr (Sum.inl (seg, bX))) rfl, mul_zero]
      · exact zero_mul _
    · exact zero_mul _
  rw [hX, zero_add] at h_syn2
  have hQ : (∑ qQ : BDLCQ1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) (Sum.inr qQ) *
        cylinderResidualCocycle pcode M h (Sum.inr qQ)) =
      cylinderResidualCocycle pcode M h (Sum.inr (armStart pcode M eZ k, b)) +
      cylinderResidualCocycle pcode M h (Sum.inr (armEnd pcode M eZ k, b)) := by
    dsimp [bdlStepXCheckZ, bdlDeltaQ1]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (armStart pcode M eZ k, b)]
    · rw [Finset.sum_eq_single (armEnd pcode M eZ k, b)]
      · simp
      · intro _ _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  rw [hQ] at h_syn2
  have h2 := zmod2_add_self (cylinderResidualCocycle pcode M h (Sum.inr (armEnd pcode M eZ k, b)))
  linear_combination h_syn2 - h2

/-- Induction along arm `eZ` in layer `b`: `cylinderResidualCocycle` at `armStart` and `armEnd` equals its value at `(Sum.inl eZ.val.1, b)`. -/
lemma cylinderResidualCocycle_arm_eq_center {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (eZ : ActiveZ pcode) (b : Fin 3)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x eZ.val.1 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h (Sum.inl qX) = 0)
    (h_syn_arm : ∀ k' : Fin (M + 1),
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inr (Sum.inl (Sum.inl (eZ, k', b)))) = 0)
    (k : Fin (M + 1)) :
    cylinderResidualCocycle pcode M h (Sum.inr (armStart pcode M eZ k, b)) =
      cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl eZ.val.1, b)) ∧
    cylinderResidualCocycle pcode M h (Sum.inr (armEnd pcode M eZ k, b)) =
      cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl eZ.val.1, b)) := by
  have h_step : ∀ k' : Fin (M + 1),
      cylinderResidualCocycle pcode M h (Sum.inr (armStart pcode M eZ k', b)) =
      cylinderResidualCocycle pcode M h (Sum.inr (armEnd pcode M eZ k', b)) :=
    fun k' => cylinderResidualCocycle_arm_const_step pcode M h eZ k' b h_zero_X (h_syn_arm k')
  suffices h_ind : ∀ (n : ℕ) (hn : n < M + 1),
      cylinderResidualCocycle pcode M h (Sum.inr (armStart pcode M eZ ⟨n, hn⟩, b)) =
        cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl eZ.val.1, b)) ∧
      cylinderResidualCocycle pcode M h (Sum.inr (armEnd pcode M eZ ⟨n, hn⟩, b)) =
        cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl eZ.val.1, b)) from
    h_ind k.val k.isLt
  intro n
  induction n with
  | zero =>
    intro hn
    have h0 : armStart pcode M eZ 0 = Sum.inl eZ.val.1 := rfl
    have he0 : (⟨0, hn⟩ : Fin (M + 1)) = 0 := rfl
    rw [he0]
    exact ⟨by rw [h0], (h_step 0).symm.trans (by rw [h0])⟩
  | succ m ih =>
    intro hm
    have hm' : m < M + 1 := Nat.lt_of_succ_lt hm
    have h_link : armStart pcode M eZ ⟨m + 1, hm⟩ = armEnd pcode M eZ ⟨m, hm'⟩ := by
      dsimp [armStart, armEnd]
      have h_lt : m < M := Nat.lt_of_succ_lt_succ hm
      rw [dif_pos h_lt]
    have h_start : cylinderResidualCocycle pcode M h (Sum.inr (armStart pcode M eZ ⟨m + 1, hm⟩, b)) =
        cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl eZ.val.1, b)) := by
      rw [h_link, (ih hm').2]
    exact ⟨h_start, (h_step ⟨m + 1, hm⟩).symm.trans h_start⟩

/-- Local vertical terminal constancy on `Y_{q0}` assuming `cylinderResidualCocycle` vanishes on incident cylinders `Y_x`. -/
lemma cylinderResidualCocycle_vertical_const {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (eZ : ActiveZ pcode) (b : Fin 2)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x eZ.val.1 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h (Sum.inl qX) = 0)
    (h_syn : syndrome (dualCode (bdlCylinderStepX pcode M)) h
      (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) = 0) :
    cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), 0)) =
    cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), b.succ)) := by
  have h_syn2 : syndrome (dualCode (bdlCylinderStepX pcode M)) (cylinderResidualCocycle pcode M h)
      (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) = 0 := by
    dsimp [cylinderResidualCocycle, apexResidualCocycle]
    rw [syndrome_add_checkGen_dual, syndrome_add_checkGen_dual]
    exact h_syn
  dsimp [syndrome, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex] at h_syn2
  rw [Fintype.sum_sum_type] at h_syn2
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) (Sum.inl qX) *
        cylinderResidualCocycle pcode M h (Sum.inl qX)) = 0 := by
    apply Finset.sum_eq_zero
    intro qX _
    rcases qX with _ | ⟨_ | ⟨xv, b'⟩⟩
    · exact zero_mul _
    · exact zero_mul _
    · dsimp [bdlStepXCheckZ, bdlGXQ1]
      split_ifs with hc
      · by_cases hx : pcode.checkX xv.val.1 eZ.val.1 = 0
        · rw [hx, zero_mul]
        · rw [h_zero_X xv.val.1 hx (Sum.inr (Sum.inr (xv, b'))) rfl, mul_zero]
      · exact zero_mul _
  rw [hX, zero_add] at h_syn2
  have hQ : (∑ qQ : BDLCQ1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) (Sum.inr qQ) *
        cylinderResidualCocycle pcode M h (Sum.inr qQ)) =
      cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), 0)) +
      cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), b.succ)) := by
    dsimp [bdlStepXCheckZ, bdlDeltaQ1]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), 0)]
    · rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), b.succ)]
      · simp
      · intro _ _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  rw [hQ] at h_syn2
  have h2 := zmod2_add_self (cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), b.succ)))
  linear_combination h_syn2 - h2

/-! ## 2. Coarse Projection Cocycle and Full Cylinder Coboundary Reconstruction -/

/-- Coarse 1-cochain `coarseProjCocycle pcode M h` extracted from the layer-0 center `(Sum.inl q0, 0)` of each double star `Y_{q0}`. -/
noncomputable def coarseProjCocycle {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (q0 : Q) : ZMod 2 :=
  cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl q0, 0))

/-- Proves that `cylinderResidualCocycle pcode M h` on `Sum.inr (v0, b)` equals the coarse value `coarseProjCocycle pcode M h (xq0OwnerQ pcode M v0)`. -/
lemma cylinderResidualCocycle_inr_eq_coarse {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hq_z : ∀ q, ∃ z, pcode.checkZ z q ≠ 0)
    (h : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x q0 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h (Sum.inl qX) = 0)
    (h_syn_arm : ∀ (eZ : ActiveZ pcode) (k : Fin (M + 1)) (b : Fin 3), eZ.val.1 = q0 →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) = 0)
    (h_syn_vert : ∀ (eZ : ActiveZ pcode) (b : Fin 2), eZ.val.1 = q0 →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inr (Sum.inl (Sum.inr (eZ, b)))) = 0)
    (v0 : Xq0 pcode M) (hv0 : xq0OwnerQ pcode M v0 = q0) (b : Fin 3) :
    cylinderResidualCocycle pcode M h (Sum.inr (v0, b)) = coarseProjCocycle pcode M h q0 := by
  have h_arm_end : ∀ (eZ : ActiveZ pcode) (heZ : eZ.val.1 = q0) (b' : Fin 3),
      cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), b')) =
      cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl q0, b')) := by
    intro eZ heZ b'
    have h_end := (cylinderResidualCocycle_arm_eq_center pcode M h eZ b'
      (heZ.symm ▸ h_zero_X) (fun k' => h_syn_arm eZ k' b' heZ) (Fin.last M)).2
    have h_last : armEnd pcode M eZ (Fin.last M) = Sum.inr (Sum.inr eZ) := by
      dsimp [armEnd, Fin.last]
      rw [dif_neg (Nat.lt_irrefl M)]
    rw [← h_last, h_end, heZ]
  have h_layer_eq : cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl q0, b)) =
      coarseProjCocycle pcode M h q0 := by
    obtain ⟨z0, hz0⟩ := hq_z q0
    let eZ0 : ActiveZ pcode := ⟨(q0, z0), hz0⟩
    have h_vert0 := cylinderResidualCocycle_vertical_const pcode M h eZ0 0
      h_zero_X (h_syn_vert eZ0 0 rfl)
    have h_vert1 := cylinderResidualCocycle_vertical_const pcode M h eZ0 1
      h_zero_X (h_syn_vert eZ0 1 rfl)
    have h0 := h_arm_end eZ0 rfl 0
    have h1 := h_arm_end eZ0 rfl 1
    have h2 := h_arm_end eZ0 rfl 2
    fin_cases b
    · rfl
    · exact (h1.symm.trans h_vert0.symm).trans h0
    · exact (h2.symm.trans h_vert1.symm).trans h0
  rcases v0 with q' | ⟨⟨eZ, j⟩ | eZ⟩
  · dsimp [xq0OwnerQ] at hv0
    subst hv0
    exact h_layer_eq
  · dsimp [xq0OwnerQ] at hv0
    have h_j := (cylinderResidualCocycle_arm_eq_center pcode M h eZ b
      (hv0.symm ▸ h_zero_X) (fun k' => h_syn_arm eZ k' b hv0)
      ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩).1
    have h_start : armStart pcode M eZ ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ =
        Sum.inr (Sum.inl (eZ, j)) := rfl
    rw [← h_start, h_j, hv0, h_layer_eq]
  · dsimp [xq0OwnerQ] at hv0
    rw [h_arm_end eZ hv0 b, h_layer_eq]

/-- Relates the coarse dual syndrome of `coarseProjCocycle pcode M h` at `z0` to the fine layer-0 Z-disk syndrome. -/
lemma syndrome_coarseProjCocycle_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2)
    (z0 : M_Z)
    (h_term : ∀ (eZ : ActiveZ pcode), eZ.val.2 = z0 →
      cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), 0)) =
        coarseProjCocycle pcode M h eZ.val.1)
    (h_syn_z0 : syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inr (Sum.inr (z0, 0))) = 0) :
    syndrome (dualCode pcode) (coarseProjCocycle pcode M h) z0 = 0 := by
  have h_syn2 : syndrome (dualCode (bdlCylinderStepX pcode M)) (cylinderResidualCocycle pcode M h)
      (Sum.inr (Sum.inr (z0, 0))) = 0 := by
    dsimp [cylinderResidualCocycle, apexResidualCocycle]
    rw [syndrome_add_checkGen_dual, syndrome_add_checkGen_dual]
    exact h_syn_z0
  dsimp [syndrome, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex] at h_syn2
  rw [Fintype.sum_sum_type] at h_syn2
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, 0))) (Sum.inl qX) *
        cylinderResidualCocycle pcode M h (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => zero_mul _)
  rw [hX, zero_add, Fintype.sum_prod_type, Finset.sum_comm] at h_syn2
  rw [Finset.sum_eq_single 0] at h_syn2
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h_syn2
    have h_inl : (∑ q : Q, bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, 0))) (Sum.inr (Sum.inl q, 0)) *
        cylinderResidualCocycle pcode M h (Sum.inr (Sum.inl q, 0))) = 0 :=
      Finset.sum_eq_zero (fun _ _ => zero_mul _)
    have h_mid : (∑ p : ActiveZ pcode × Fin M,
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, 0))) (Sum.inr (Sum.inr (Sum.inl p), 0)) *
          cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inl p), 0))) = 0 :=
      Finset.sum_eq_zero (fun _ _ => zero_mul _)
    rw [h_inl, zero_add, h_mid, zero_add] at h_syn2
    have h_active : ∀ eZ : ActiveZ pcode,
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, 0))) (Sum.inr (Sum.inr (Sum.inr eZ), 0)) *
          cylinderResidualCocycle pcode M h (Sum.inr (Sum.inr (Sum.inr eZ), 0)) =
        if eZ.val.2 = z0 then coarseProjCocycle pcode M h eZ.val.1 else 0 := by
      intro eZ
      dsimp [bdlStepXCheckZ, bdlGQZ1]
      by_cases heZ : eZ.val.2 = z0
      · rw [if_pos ⟨heZ, rfl⟩, one_mul, if_pos heZ, h_term eZ heZ]
      · rw [if_neg (fun hc => heZ hc.1), zero_mul, if_neg heZ]
    simp_rw [h_active] at h_syn2
    rw [sum_activeZ_eq pcode z0 (coarseProjCocycle pcode M h)] at h_syn2
    dsimp [syndrome, dualCode, f2CheckGen, f2Syndrome, dualF2ChainComplex]
    simp_rw [mul_comm (pcode.checkZ z0 _)]
    exact h_syn2
  · intro b _ hne
    apply Finset.sum_eq_zero
    intro v0 _
    rcases v0 with _ | ⟨_ | eZ⟩
    · exact zero_mul _
    · exact zero_mul _
    · dsimp [bdlStepXCheckZ, bdlGQZ1]
      rw [if_neg (fun hc => hne hc.2), zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Complete fine 0-cochain `fullCylinderCocycle` on `BDLStepXMX pcode M` solving `checkGen (dualCode (bdlCylinderStepX pcode M)) d2 = h`. -/
noncomputable def fullCylinderCocycle {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (c : M_X → ZMod 2) :
    BDLStepXMX pcode M → ZMod 2 :=
  apexRadialCocycle pcode M h +
    layer1ConeCochain pcode M (coneLinkVal pcode M h) +
    liftStepXMX pcode M c

/-- Reconstructs the fine 1-cochain `h` from `fullCylinderCocycle pcode M h c` and `cylinderResidualCocycle pcode M h`. -/
lemma fullCylinderCocycle_eq_of_residual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) (c : M_X → ZMod 2) (q : BDLStepXQ pcode M)
    (h_res : cylinderResidualCocycle pcode M h q =
      checkGen (dualCode (bdlCylinderStepX pcode M)) (liftStepXMX pcode M c) q) :
    h q = checkGen (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) q := by
  have h_lin : checkGen (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) q =
      checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) q +
      checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M (coneLinkVal pcode M h)) q +
      checkGen (dualCode (bdlCylinderStepX pcode M)) (liftStepXMX pcode M c) q := by
    dsimp [fullCylinderCocycle]
    rw [map_add, map_add]
    rfl
  rw [h_lin, ← h_res]
  change h q = _ + _ + (h q + checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) q +
    checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M (coneLinkVal pcode M h)) q)
  have ha := zmod2_add_self (checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) q)
  have hb := zmod2_add_self (checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M (coneLinkVal pcode M h)) q)
  linear_combination -ha - hb

/-! ## 3. Link-Graph Walk Combinatorics and Surface Seed Link-Connectedness -/

/-- Single step in the link graph of `x : M_X` in `code`. -/
def XLinkStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : M_X) (a b : Q) : Prop :=
  code.checkX x a ≠ 0 ∧ code.checkX x b ≠ 0 ∧
    ∃ z : M_Z, code.checkZ z a ≠ 0 ∧ code.checkZ z b ≠ 0

/-- Symmetry of the single-step link adjacency relation `XLinkStep code x`. -/
lemma xLinkStep_symm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : M_X) {a b : Q} (h : XLinkStep code x a b) :
    XLinkStep code x b a := by
  rcases h with ⟨ha, hb, z, hza, hzb⟩
  exact ⟨hb, ha, z, hzb, hza⟩

/-- Symmetry of the reflexive-transitive closure `Relation.ReflTransGen (XLinkStep code x)`. -/
lemma reflTransGen_XLinkStep_symm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : M_X) {a b : Q}
    (h : Relation.ReflTransGen (XLinkStep code x) a b) :
    Relation.ReflTransGen (XLinkStep code x) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (xLinkStep_symm code x hbc)).trans ih

/-- Connectedness criterion: if every active qubit in the link of `x` connects to a hub `q_hub`, then the link of `x` is connected. -/
lemma reflTransGen_XLinkStep_of_hub {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (x : M_X) (q_hub : Q)
    (h_to_hub : ∀ q : Q, code.checkX x q ≠ 0 → Relation.ReflTransGen (XLinkStep code x) q q_hub)
    {q q' : Q} (hq : code.checkX x q ≠ 0) (hq' : code.checkX x q' ≠ 0) :
    Relation.ReflTransGen (XLinkStep code x) q q' :=
  (h_to_hub q hq).trans (reflTransGen_XLinkStep_symm code x (h_to_hub q' hq'))

/-- Every qubit active in X-check `x` of `bdlSurfaceSeedCode` is one `XLinkStep` away from central qubit `2`. -/
lemma surfaceSeed_primal_step_to_two (x : Fin 2) (q : Fin 5)
    (hq : bdlSurfaceSeedCode.checkX x q ≠ 0) :
    XLinkStep bdlSurfaceSeedCode x q 2 := by
  fin_cases x <;> fin_cases q <;>
    first
    | exact False.elim (hq rfl)
    | (refine ⟨hq, by decide, ?_⟩; first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩)

/-- Every qubit active in dual X-check `x` of `dualCode bdlSurfaceSeedCode` is one `XLinkStep` away from central qubit `2`. -/
lemma surfaceSeed_dual_step_to_two (x : Fin 2) (q : Fin 5)
    (hq : (dualCode bdlSurfaceSeedCode).checkX x q ≠ 0) :
    XLinkStep (dualCode bdlSurfaceSeedCode) x q 2 := by
  fin_cases x <;> fin_cases q <;>
    first
    | exact False.elim (hq rfl)
    | (refine ⟨hq, by decide, ?_⟩; first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩)

/-- Establishes `HasConnectedXLinks` for both `bdlSurfaceSeedCode` and `dualCode bdlSurfaceSeedCode`. -/
theorem hasConnectedXLinks_surfaceSeed :
    HasConnectedXLinks bdlSurfaceSeedCode ∧
    HasConnectedXLinks (dualCode bdlSurfaceSeedCode) := by
  refine ⟨?_, ?_⟩
  · intro x q q' hq hq'
    exact reflTransGen_XLinkStep_of_hub bdlSurfaceSeedCode x 2
      (fun a ha => Relation.ReflTransGen.single (surfaceSeed_primal_step_to_two x a ha)) hq hq'
  · intro x q q' hq hq'
    exact reflTransGen_XLinkStep_of_hub (dualCode bdlSurfaceSeedCode) x 2
      (fun a ha => Relation.ReflTransGen.single (surfaceSeed_dual_step_to_two x a ha)) hq hq'

/-- Unfolds `(dualCode code).checkX` to `code.checkZ`. -/
@[simp] lemma dualCode_checkX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) :
    (dualCode code).checkX = code.checkZ := rfl

/-- Unfolds `(dualCode code).checkZ` to `code.checkX`. -/
@[simp] lemma dualCode_checkZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) :
    (dualCode code).checkZ = code.checkX := rfl

/-- Unfolds `(bdlCylinderStepX pcode M).checkX` to `bdlStepXCheckX pcode M`. -/
@[simp] lemma bdlCylinderStepX_checkX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    (bdlCylinderStepX pcode M).checkX = bdlStepXCheckX pcode M := rfl

/-- Unfolds `(bdlCylinderStepX pcode M).checkZ` to `bdlStepXCheckZ pcode M`. -/
@[simp] lemma bdlCylinderStepX_checkZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    (bdlCylinderStepX pcode M).checkZ = bdlStepXCheckZ pcode M := rfl

/-! ## 4. Explicit Coboundary Incidence Lemmas for bdlDeltaX0 and bdlDeltaX1 -/

/-- Evaluates `bdlDeltaX0` at an apex vertex `Sum.inl (x, b)` and an `r = 0` radial 1-cell to `1`. -/
lemma bdlDeltaX0_radial_apex_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (rv : RadialVertex pcode M) (b : Fin 3)
    (hr0 : rv.val.val.2.val = 0) :
    bdlStepXCheckX pcode M (Sum.inl (rv.val.val.1.val.1, b)) (Sum.inl (Sum.inl (rv, b))) = 1 := by
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  rw [if_pos hr0, if_pos rfl, add_zero]

/-- Evaluates `bdlDeltaX0` at a shell vertex `Sum.inr (rv.val, b)` and its own radial 1-cell `(rv, b)` to `1`. -/
lemma bdlDeltaX0_radial_self_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (rv : RadialVertex pcode M) (b : Fin 3) :
    bdlStepXCheckX pcode M (Sum.inr (rv.val, b)) (Sum.inl (Sum.inl (rv, b))) = 1 := by
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  by_cases hr0 : rv.val.val.2.val = 0
  · rw [if_pos hr0, if_pos rfl, zero_add]
  · have h_ne : (Sum.inr (rv.val, b) : BDLStepXMX pcode M) ≠
        Sum.inr (radialParentVertex pcode M rv.val, b) := by
      intro hc
      injection hc with hc1
      injection hc1 with hc2
      have hr := congr_arg (fun w : ShellVertex pcode M => w.val.2.val) hc2
      dsimp [radialParentVertex, finPred] at hr
      omega
    rw [if_neg hr0, if_neg h_ne, if_pos rfl, zero_add]

/-- Evaluates `bdlDeltaX0` at the radial parent shell vertex and radial 1-cell `(rv, b)` with `r ≠ 0` to `1`. -/
lemma bdlDeltaX0_radial_parent_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (rv : RadialVertex pcode M) (b : Fin 3)
    (hr0 : rv.val.val.2.val ≠ 0) :
    bdlStepXCheckX pcode M (Sum.inr (radialParentVertex pcode M rv.val, b)) (Sum.inl (Sum.inl (rv, b))) = 1 := by
  have h_ne : (Sum.inr (radialParentVertex pcode M rv.val, b) : BDLStepXMX pcode M) ≠
      Sum.inr (rv.val, b) := by
    intro hc
    injection hc with hc1
    injection hc1 with hc2
    have hr := congr_arg (fun w : ShellVertex pcode M => w.val.2.val) hc2
    dsimp [radialParentVertex, finPred] at hr
    omega
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  rw [if_neg hr0, if_pos rfl, if_neg h_ne, add_zero]

/-- Evaluates `bdlDeltaX0` at `shellSegStartVertex pcode M seg` and azimuthal segment `(seg, b)` to `1`. -/
lemma bdlDeltaX0_seg_start_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3) :
    bdlStepXCheckX pcode M (Sum.inr (shellSegStartVertex pcode M seg, b))
      (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 1 := by
  have h_ne : (Sum.inr (shellSegStartVertex pcode M seg, b) : BDLStepXMX pcode M) ≠
      Sum.inr (shellSegEndVertex pcode M seg, b) := by
    intro hc; injection hc with hc1; injection hc1 with hc2
    exact shellSegStartVertex_ne_end pcode M seg hc2
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  rw [if_pos rfl, if_neg h_ne, add_zero]

/-- Evaluates `bdlDeltaX0` at `shellSegEndVertex pcode M seg` and azimuthal segment `(seg, b)` to `1`. -/
lemma bdlDeltaX0_seg_end_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3) :
    bdlStepXCheckX pcode M (Sum.inr (shellSegEndVertex pcode M seg, b))
      (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 1 := by
  have h_ne : (Sum.inr (shellSegEndVertex pcode M seg, b) : BDLStepXMX pcode M) ≠
      Sum.inr (shellSegStartVertex pcode M seg, b) := by
    intro hc; injection hc with hc1; injection hc1 with hc2
    exact shellSegStartVertex_ne_end pcode M seg hc2.symm
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  rw [if_neg h_ne, if_pos rfl, zero_add]

/-- Evaluates `bdlDeltaX0` at outer shell vertex `(mkOuterShellVertex pcode M xv, 0)` and vertical 1-cell `(xv, b)` to `1`. -/
lemma bdlDeltaX0_vert_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (xv : BoundaryX0Link pcode M) (b : Fin 2) :
    bdlStepXCheckX pcode M
      (Sum.inr (mkOuterShellVertex pcode M xv, 0))
      (Sum.inl (Sum.inr (Sum.inr (xv, b)))) = 1 := by
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  fin_cases b <;> simp

/-- Evaluates `bdlDeltaX0` at outer shell vertex `(mkOuterShellVertex pcode M xv, b.succ)` and vertical 1-cell `(xv, b)` to `1`. -/
lemma bdlDeltaX0_vert_succ_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (xv : BoundaryX0Link pcode M) (b : Fin 2) :
    bdlStepXCheckX pcode M
      (Sum.inr (mkOuterShellVertex pcode M xv, b.succ))
      (Sum.inl (Sum.inr (Sum.inr (xv, b)))) = 1 := by
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  fin_cases b <;> simp

/-- Identifies the start radial spoke of `cornerSeg` with `cornerSpokeRadial`. -/
lemma cornerSeg_startVertex_eq_cornerSpoke {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (q : Q) (z : M_Z)
    (hX : pcode.checkX x q ≠ 0) (hZ : pcode.checkZ z q ≠ 0) :
    shellSegStartVertex pcode M (cornerSeg pcode M x q z hX hZ) = cornerSpoke pcode M x q hX := by
  apply Subtype.ext; apply Prod.ext
  · apply Subtype.ext; apply Prod.ext
    · rfl
    · rfl
  · rfl

/-- Evaluates `bdlDeltaX1` on a canonical `r = 0` square 2-cell and an incident `cornerSpokeRadial` 1-cell to `1`. -/
lemma bdlDeltaX1_canonical_spoke_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (h_tri : seg.val.2.2.val = seg.val.2.1.val) (hr0 : seg.val.2.1.val = 0)
    (h_can : seg.val.1.val.2.val.1 = canonicalSquareQ pcode seg.val.1.val.1 seg.val.1.val.2.val.2
      ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩)
    (q' : Q) (hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0) (hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0) :
    bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b)))
      (Sum.inl (Sum.inl (cornerSpokeRadial pcode M seg.val.1.val.1 q' hX', b))) = 1 := by
  dsimp [bdlStepXCheckZ, bdlDeltaX1]
  rw [dif_pos h_tri, dif_pos hr0, if_pos h_can]
  rw [Finset.sum_eq_single q']
  · rw [dif_pos hX', if_pos hZ']; simp
  · intro q'' _ hne
    by_cases hX'' : pcode.checkX seg.val.1.val.1 q'' ≠ 0
    · rw [dif_pos hX'']
      by_cases hZ'' : pcode.checkZ seg.val.1.val.2.val.2 q'' ≠ 0
      · rw [if_pos hZ'']
        have h_ne_sp : (Sum.inl (cornerSpokeRadial pcode M seg.val.1.val.1 q' hX', b) : BDLCX1 pcode M) ≠
            Sum.inl (cornerSpokeRadial pcode M seg.val.1.val.1 q'' hX'', b) := by
          intro h_eq
          apply hne
          injection h_eq with h1; injection h1 with h2 _
          have hv := congr_arg (fun w : RadialVertex pcode M => w.val.val.1.val.2) h2
          dsimp [cornerSpokeRadial, cornerSpoke] at hv
          injection hv with hq_eq
          exact hq_eq.symm
        rw [if_neg h_ne_sp]; rfl
      · rw [if_neg hZ'']
    · rw [dif_neg hX'']
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q'))

/-- Evaluates `bdlDeltaX1` on a canonical `r = 0` square 2-cell and an incident `cornerSeg` azimuthal 1-cell to `1`. -/
lemma bdlDeltaX1_canonical_seg_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (h_tri : seg.val.2.2.val = seg.val.2.1.val) (hr0 : seg.val.2.1.val = 0)
    (h_can : seg.val.1.val.2.val.1 = canonicalSquareQ pcode seg.val.1.val.1 seg.val.1.val.2.val.2
      ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩)
    (q' : Q) (hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0) (hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0) :
    bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b)))
      (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ', b)))) = 1 := by
  dsimp [bdlStepXCheckZ, bdlDeltaX1]
  rw [dif_pos h_tri, if_pos hr0, if_pos h_can]
  rw [Finset.sum_eq_single q']
  · rw [dif_pos hX', dif_pos hZ']; simp
  · intro q'' _ hne
    by_cases hX'' : pcode.checkX seg.val.1.val.1 q'' ≠ 0
    · rw [dif_pos hX'']
      by_cases hZ'' : pcode.checkZ seg.val.1.val.2.val.2 q'' ≠ 0
      · rw [dif_pos hZ'']
        have h_ne_cs : (Sum.inr (Sum.inl (cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ', b)) : BDLCX1 pcode M) ≠
            Sum.inr (Sum.inl (cornerSeg pcode M seg.val.1.val.1 q'' seg.val.1.val.2.val.2 hX'' hZ'', b)) := by
          intro h_eq
          apply hne
          injection h_eq with h1; injection h1 with h2; injection h2 with h3 _
          have hq_eq := congr_arg (fun s : ShellSegment pcode M => s.val.1.val.2.val.1) h3
          exact hq_eq.symm
        rw [if_neg h_ne_cs]; rfl
      · rw [dif_neg hZ'']
    · rw [dif_neg hX'']
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q'))

/-- Evaluates `bdlDeltaX1` on an `r > 0` grid 2-cell `(seg, b)` and `shellSegStartRadial` to `1`. -/
lemma bdlDeltaX1_pos_startRadial_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (hr0 : seg.val.2.1.val ≠ 0) :
    bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b)))
      (Sum.inl (Sum.inl (shellSegStartRadial pcode M seg, b))) = 1 := by
  have h_ne : (Sum.inl (shellSegStartRadial pcode M seg, b) : BDLCX1 pcode M) ≠
      Sum.inl (shellSegEndRadial pcode M seg hr0, b) := by
    intro hc; injection hc with hc1; injection hc1 with hc2 _
    exact shellSegStartVertex_ne_end pcode M seg (congr_arg Subtype.val hc2)
  dsimp [bdlStepXCheckZ, bdlDeltaX1]
  by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
  · rw [dif_pos h_tri, dif_neg hr0, if_pos rfl, if_neg h_ne]; rfl
  · rw [dif_neg h_tri, if_pos rfl, if_neg h_ne]; rfl

/-- Evaluates `bdlDeltaX1` on an `r > 0` grid 2-cell `(seg, b)` and `shellSegEndRadial` to `1`. -/
lemma bdlDeltaX1_pos_endRadial_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (hr0 : seg.val.2.1.val ≠ 0) :
    bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b)))
      (Sum.inl (Sum.inl (shellSegEndRadial pcode M seg hr0, b))) = 1 := by
  have h_ne : (Sum.inl (shellSegEndRadial pcode M seg hr0, b) : BDLCX1 pcode M) ≠
      Sum.inl (shellSegStartRadial pcode M seg, b) := by
    intro hc; injection hc with hc1; injection hc1 with hc2 _
    exact shellSegStartVertex_ne_end pcode M seg (congr_arg Subtype.val hc2).symm
  dsimp [bdlStepXCheckZ, bdlDeltaX1]
  by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
  · rw [dif_pos h_tri, dif_neg hr0, if_neg h_ne, if_pos rfl]; rfl
  · rw [dif_neg h_tri, if_neg h_ne, if_pos rfl]; rfl

/-- Evaluates `bdlDeltaX1` on an `r > 0` grid 2-cell `(seg, b)` and azimuthal 1-cell `(seg, b)` to `1`. -/
lemma bdlDeltaX1_pos_seg_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (hr0 : seg.val.2.1.val ≠ 0) :
    bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b)))
      (Sum.inl (Sum.inr (Sum.inl (seg, b)))) = 1 := by
  dsimp [bdlStepXCheckZ, bdlDeltaX1]
  by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
  · rw [dif_pos h_tri, if_neg hr0]; simp
  · have h_pred_ne : (Sum.inr (Sum.inl (seg, b)) : BDLCX1 pcode M) ≠
        Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)) := by
      intro hc; injection hc with hc1; injection hc1 with hc2; injection hc2 with hc3 _
      have hr := congr_arg (fun s : ShellSegment pcode M => s.val.2.1.val) hc3
      dsimp [shellSegPred, finPred] at hr
      have h_lt : seg.val.2.2.val < seg.val.2.1.val := Nat.lt_of_le_of_ne seg.property h_tri
      omega
    rw [dif_neg h_tri, if_neg h_pred_ne]; simp

/-- Evaluates `bdlDeltaX1` on a non-degenerate `r > 0` grid 2-cell `(seg, b)` and inner azimuthal 1-cell `(shellSegPred seg, b)` to `1`. -/
lemma bdlDeltaX1_pos_pred_eq_one {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (b : Fin 3)
    (h_tri : seg.val.2.2.val ≠ seg.val.2.1.val) :
    bdlStepXCheckZ pcode M (Sum.inl (Sum.inl (seg, b)))
      (Sum.inl (Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)))) = 1 := by
  have h_pred_ne : (Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b)) : BDLCX1 pcode M) ≠
      Sum.inr (Sum.inl (seg, b)) := by
    intro hc; injection hc with hc1; injection hc1 with hc2; injection hc2 with hc3 _
    have hr := congr_arg (fun s : ShellSegment pcode M => s.val.2.1.val) hc3
    dsimp [shellSegPred, finPred] at hr
    have h_lt : seg.val.2.2.val < seg.val.2.1.val := Nat.lt_of_le_of_ne seg.property h_tri
    omega
  dsimp [bdlStepXCheckZ, bdlDeltaX1]
  rw [dif_neg h_tri, if_pos rfl, if_neg h_pred_ne]; rfl

end WeldedHierarchy
