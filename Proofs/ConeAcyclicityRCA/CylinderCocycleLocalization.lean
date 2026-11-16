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

import Proofs.ConeAcyclicityRCA.LocalCocycleDualityAndBalls

/-!
# Cylinder Support Localization, Single-Step Stabilizer Transfer, and Welded Cone Invariants

Proves that radial-shell and residual cocycle primitives vanish on cylinders disjoint from the input cocycle support, yielding localized single-step stabilizer generation transfers across dual cylinder welding (bdlCylinderStepX_dual_globalStabilizers_step), primal cylinder welding via Fredholm duality (bdlCylinderStepX_primal_globalStabilizers_step), and LLL rescaling (bdlPerturbStep_globalStabilizers_step). Bundles the inductive geometric and topological invariants HasBDLConeInvariants and defines the alternating half-step hierarchy bdlHalfStep.

## References

* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
* Part I, Section 3.1 (`subsec:rca-trinity`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 3.2 (`subsec:nilpotent-hpl`), Lemma 3.6 (`lem:block-sdr`), Proposition 3.7 (`prop:classical-hpl`)
* Part I, Section 3.3 (`subsec:scale-matched-rca`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Cylinder Vanishing Lemmas for Radial Shell Homotopy and Cone Cocycles -/

/-- If `h` vanishes on all cylinder qubits owned by `x`, then `hRadialShell pcode M h sv b = 0` on cylinder `x`. -/
lemma hRadialShell_eq_zero_of_cylinder_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0)
    (sv : ShellVertex pcode M) (b : Fin 3) (hsv : sv.val.1.val.1 = x) :
    hRadialShell pcode M h sv b = 0 := by
  dsimp [hRadialShell]
  by_cases h_nd : ¬ IsDiagZeroVertex pcode M sv
  · rw [dif_pos h_nd]
    exact h_zero (Sum.inl (⟨sv, h_nd⟩, b)) hsv
  · rw [dif_neg h_nd]
    rcases h_v : sv.val.1.val.2 with q0 | ⟨⟨eZ, j⟩ | z⟩
    · rfl
    · rfl
    · (try dsimp only)
      split_ifs with h_ex
      · let q_can := canonicalSquareQ pcode sv.val.1.val.1 z h_ex
        let h_can := canonicalSquareQ_spec pcode sv.val.1.val.1 z h_ex
        have h1 : h (Sum.inl (Sum.inl (cornerSpokeRadial pcode M sv.val.1.val.1 q_can h_can.1, b))) = 0 :=
          h_zero (Sum.inl (cornerSpokeRadial pcode M sv.val.1.val.1 q_can h_can.1, b)) hsv
        have h2 : h (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode M sv.val.1.val.1 q_can z h_can.1 h_can.2, b)))) = 0 :=
          h_zero (Sum.inr (Sum.inl (cornerSeg pcode M sv.val.1.val.1 q_can z h_can.1 h_can.2, b))) hsv
        rw [h1, h2, add_zero]
      · rfl

/-- `radialParentVertex` preserves the coarse owner X-check `sv.val.1.val.1`. -/
lemma radialParentVertex_ownerX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv : ShellVertex pcode M) :
    (radialParentVertex pcode M sv).val.1.val.1 = sv.val.1.val.1 :=
  rfl

/-- Iterating `radialParentVertex` `k` times preserves the coarse owner X-check. -/
lemma iterate_radialParentVertex_ownerX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (i : ℕ) (sv : ShellVertex pcode M) :
    ((radialParentVertex pcode M)^[i] sv).val.1.val.1 = sv.val.1.val.1 := by
  induction i generalizing sv with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, radialParentVertex_ownerX]

/-- If `h` vanishes on cylinder `x`, then `radialRaySum pcode M h sv b = 0` on cylinder `x`. -/
lemma radialRaySum_eq_zero_of_cylinder_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0)
    (sv : ShellVertex pcode M) (b : Fin 3) (hsv : sv.val.1.val.1 = x) :
    radialRaySum pcode M h sv b = 0 := by
  dsimp [radialRaySum]
  apply Finset.sum_eq_zero
  intro i _
  exact hRadialShell_eq_zero_of_cylinder_zero pcode M h x h_zero
    ((radialParentVertex pcode M)^[i] sv) b
    ((iterate_radialParentVertex_ownerX pcode M i sv).trans hsv)

/-- If `h` vanishes on cylinder `x`, then `apexRadialCocycle pcode M h` vanishes on cylinder `x`. -/
lemma apexRadialCocycle_eq_zero_of_cylinder_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0)
    (mX : BDLStepXMX pcode M) (hmX : stepXMXOwnerX pcode M mX = x) :
    apexRadialCocycle pcode M h mX = 0 := by
  rcases mX with ⟨x', b⟩ | ⟨sv, b⟩
  · rfl
  · exact radialRaySum_eq_zero_of_cylinder_zero pcode M h x h_zero sv b hmX

/-- If `h` vanishes on cylinder `x`, the dual coboundary of `apexRadialCocycle` vanishes on cylinder qubits of `x`. -/
lemma checkGen_dual_apexRadialCocycle_inl_eq_zero_of_cylinder_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0)
    (qX : BDLCX1 pcode M) (hqX : qXOwnerX pcode M qX = x) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) (Sum.inl qX) = 0 := by
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  apply Finset.sum_eq_zero
  intro mX _
  by_cases h_chk : bdlStepXCheckX pcode M mX (Sum.inl qX) = 0
  · rw [h_chk, zero_mul]
  · have h_owner : stepXMXOwnerX pcode M mX = x := by
      rcases qX with ⟨rv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, b⟩⟩
      · dsimp [bdlStepXCheckX, bdlDeltaX0] at h_chk
        by_cases hr0 : rv.val.val.2.val = 0
        · rw [if_pos hr0] at h_chk
          by_cases h1 : mX = Sum.inl (rv.val.val.1.val.1, b)
          · subst h1; exact hqX
          · by_cases h2 : mX = Sum.inr (rv.val, b)
            · subst h2; exact hqX
            · rw [if_neg h1, if_neg h2] at h_chk; exact False.elim (h_chk rfl)
        · rw [if_neg hr0] at h_chk
          by_cases h1 : mX = Sum.inr (radialParentVertex pcode M rv.val, b)
          · subst h1; exact hqX
          · by_cases h2 : mX = Sum.inr (rv.val, b)
            · subst h2; exact hqX
            · rw [if_neg h1, if_neg h2] at h_chk; exact False.elim (h_chk rfl)
      · dsimp [bdlStepXCheckX, bdlDeltaX0] at h_chk
        by_cases h1 : mX = Sum.inr (shellSegStartVertex pcode M seg, b)
        · subst h1; exact hqX
        · by_cases h2 : mX = Sum.inr (shellSegEndVertex pcode M seg, b)
          · subst h2; exact hqX
          · rw [if_neg h1, if_neg h2] at h_chk; exact False.elim (h_chk rfl)
      · dsimp [bdlStepXCheckX, bdlDeltaX0] at h_chk
        by_cases h1 : mX = Sum.inr (mkOuterShellVertex pcode M xv, 0)
        · subst h1; exact hqX
        · by_cases h2 : mX = Sum.inr (mkOuterShellVertex pcode M xv, b.succ)
          · subst h2; exact hqX
          · rw [if_neg h1, if_neg h2] at h_chk; exact False.elim (h_chk rfl)
    rw [apexRadialCocycle_eq_zero_of_cylinder_zero pcode M h x h_zero mX h_owner, mul_zero]

/-! ## 2. Euclidean Ball Support Localization for `coarseProjCocycle` and `fullCylinderCocycle` -/

/-- If `h` vanishes on cylinder `x`, then `apexResidualCocycle pcode M h` vanishes on cylinder `x`. -/
lemma apexResidualCocycle_eq_zero_of_cylinder_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0)
    (qX : BDLCX1 pcode M) (hqX : qXOwnerX pcode M qX = x) :
    apexResidualCocycle pcode M h (Sum.inl qX) = 0 := by
  change h (Sum.inl qX) + checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) (Sum.inl qX) = 0
  rw [h_zero qX hqX,
      checkGen_dual_apexRadialCocycle_inl_eq_zero_of_cylinder_zero pcode M h x h_zero qX hqX,
      add_zero]

/-- If `h` vanishes on cylinder `x`, then `coneLinkVal pcode M h x q b = 0`. -/
lemma coneLinkVal_eq_zero_of_cylinder_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (h_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0)
    (b : Fin 2) :
    coneLinkVal pcode M h x b = 0 := by
  dsimp [coneLinkVal]
  split_ifs with hex
  · exact apexResidualCocycle_eq_zero_of_cylinder_zero pcode M h x h_zero
      (Sum.inr (Sum.inr (⟨(x, Sum.inl (Classical.choose hex)), Classical.choose_spec hex⟩, b))) rfl
  · rfl

/-- If `h` vanishes on cylinder `x` and `c x = 0`, then `fullCylinderCocycle pcode M h c` vanishes on cylinder `x`. -/
lemma fullCylinderCocycle_eq_zero_of_cylinder_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (c : M_X → ZMod 2) (x : M_X)
    (hc : c x = 0)
    (h_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0)
    (mX : BDLStepXMX pcode M) (hmX : stepXMXOwnerX pcode M mX = x) :
    fullCylinderCocycle pcode M h c mX = 0 := by
  change apexRadialCocycle pcode M h mX +
    layer1ConeCochain pcode M (coneLinkVal pcode M h) mX +
    liftStepXMX pcode M c mX = 0
  have h1 := apexRadialCocycle_eq_zero_of_cylinder_zero pcode M h x h_zero mX hmX
  have h2 : layer1ConeCochain pcode M (coneLinkVal pcode M h) mX = 0 := by
    rcases mX with ⟨x', b⟩ | ⟨sv, b⟩
    · dsimp [stepXMXOwnerX] at hmX; subst hmX
      dsimp [layer1ConeCochain]
      rw [coneLinkVal_eq_zero_of_cylinder_zero pcode M h x' h_zero 0,
          coneLinkVal_eq_zero_of_cylinder_zero pcode M h x' h_zero 1,
          ite_self, ite_self]
    · dsimp [stepXMXOwnerX] at hmX; subst hmX
      dsimp [layer1ConeCochain]
      rw [coneLinkVal_eq_zero_of_cylinder_zero pcode M h sv.val.1.val.1 h_zero 0,
          coneLinkVal_eq_zero_of_cylinder_zero pcode M h sv.val.1.val.1 h_zero 1,
          ite_self, ite_self]
  have h3 : liftStepXMX pcode M c mX = 0 := by
    dsimp [liftStepXMX]; rw [hmX, hc]
  rw [h1, h2, h3, add_zero, add_zero]

/-- The dual coboundary of `layer1ConeCochain` vanishes identically on all star qubits `Sum.inr qQ`. -/
lemma checkGen_dual_layer1ConeCochain_inr_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c_cone : M_X → Fin 2 → ZMod 2) (v0 : Xq0 pcode M) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M c_cone) (Sum.inr (v0, 0)) = 0 := by
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  apply Finset.sum_eq_zero
  intro mX _
  rcases mX with ⟨x, b⟩ | ⟨sv, b⟩
  · exact zero_mul _
  · dsimp [bdlStepXCheckX, bdlGXQ0]
    split_ifs with hc
    · rcases hc with ⟨_, _, rfl⟩
      dsimp [layer1ConeCochain]
      simp
    · exact zero_mul _

/-- If `h` vanishes on all fine qubits belonging to `q0` and its incident cylinders, `coarseProjCocycle pcode M h q0 = 0`. -/
lemma coarseProjCocycle_eq_zero_of_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (hq0_zero : h (Sum.inr (Sum.inl q0, 0)) = 0)
    (h_cyl_zero : ∀ (x : M_X), pcode.checkX x q0 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0) :
    coarseProjCocycle pcode M h q0 = 0 := by
  change h (Sum.inr (Sum.inl q0, 0)) +
    checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) (Sum.inr (Sum.inl q0, 0)) +
    checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M (coneLinkVal pcode M h))
      (Sum.inr (Sum.inl q0, 0)) = 0
  rw [hq0_zero, checkGen_dual_layer1ConeCochain_inr_zero, zero_add, add_zero]
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  apply Finset.sum_eq_zero
  intro mX _
  rcases mX with ⟨x, b⟩ | ⟨sv, b⟩
  · exact zero_mul _
  · dsimp [bdlStepXCheckX, bdlGXQ0]
    split_ifs with hc
    · by_cases hx : pcode.checkX sv.val.1.val.1 q0 = 0
      · dsimp [xq0OwnerQ]; rw [hx, zero_mul]
      · rw [apexRadialCocycle_eq_zero_of_cylinder_zero pcode M h sv.val.1.val.1
          (h_cyl_zero sv.val.1.val.1 hx) (Sum.inr (sv, b)) rfl, mul_zero]
    · exact zero_mul _

/-- Support localization of `coarseProjCocycle`: if `supp1 (dualCode (bdlCylinderStepX pcode M)) h ⊆ Ball3D x0 r`,
    then `supp1 (dualCode pcode) (coarseProjCocycle pcode M h) ⊆ Ball3D x0 (r + 3 * D_edge)`. -/
lemma coarseProjCocycle_supp1_subset {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (x0 : Point3D) {r : ℝ} (hr : 0 ≤ r)
    (h : BDLStepXQ pcode M → ZMod 2)
    (h_supp : supp1 (dualCode (bdlCylinderStepX pcode M)) h ⊆ ball3D x0 r) :
    supp1 (dualCode pcode) (coarseProjCocycle pcode M h) ⊆ ball3D x0 (r + 3 * D_edge) := by
  have hD0 := hD.1
  intro p ⟨q0, hq0_ne, hp⟩; subst hp
  by_contra h_not_in
  apply hq0_ne
  apply coarseProjCocycle_eq_zero_of_zero pcode M h q0
  · by_contra h_ne
    have h_in := h_supp ⟨Sum.inr (Sum.inl q0, 0), h_ne, rfl⟩
    have h_in' : pcode.posQ q0 ∈ ball3D x0 (r + 3 * D_edge) :=
      ball3D_mono x0 hr (by linarith) h_in
    exact h_not_in h_in'
  · intro x hx qX hqX
    by_contra h_ne
    have h_qX_in := h_supp ⟨Sum.inl qX, h_ne, rfl⟩
    have h_x_in := ownerX_mem_ball3D_of_bdlCylinderStepX_posQ_inl pcode M hD x0 hr qX h_qX_in
    rw [hqX] at h_x_in
    have h_q0_in := ball3D_step_of_distSq3D_le x0 (pcode.posX x) (pcode.posQ q0)
      (by linarith) hD0 h_x_in (hD.2.2 x q0 hx)
    have h_eq : r + 2 * D_edge + D_edge = r + 3 * D_edge := by ring
    rw [h_eq] at h_q0_in
    exact h_not_in h_q0_in

/-- Support localization of `fullCylinderCocycle`: if `supp1 (dualCode (bdlCylinderStepX pcode M)) h ⊆ Ball3D x0 r`
    and `supp2 (dualCode pcode) c ⊆ Ball3D x0 R_coarse` with `r + 2 * D_edge ≤ R_coarse`,
    then `supp2 (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) ⊆ Ball3D x0 (R_coarse + 2 * D_edge)`. -/
lemma fullCylinderCocycle_supp2_subset {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (x0 : Point3D) {r R_coarse : ℝ} (hr : 0 ≤ r) (hrR : r + 2 * D_edge ≤ R_coarse)
    (h : BDLStepXQ pcode M → ZMod 2) (c : M_X → ZMod 2)
    (h_supp : supp1 (dualCode (bdlCylinderStepX pcode M)) h ⊆ ball3D x0 r)
    (hc_supp : supp2 (dualCode pcode) c ⊆ ball3D x0 R_coarse) :
    supp2 (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) ⊆
      ball3D x0 (R_coarse + 2 * D_edge) := by
  have hD0 := hD.1
  have hR_nonneg : 0 ≤ R_coarse := by linarith
  intro p ⟨mX, hmX_ne, hp⟩; subst hp
  let x := stepXMXOwnerX pcode M mX
  by_cases hx_in : pcode.posX x ∈ ball3D x0 R_coarse
  · exact bdlCylinderStepX_posX_mem_ball3D_of_ownerX pcode M hD x0 hR_nonneg mX hx_in
  · exfalso
    apply hmX_ne
    have hc_x : c x = 0 := by
      by_contra hcx_ne
      exact hx_in (hc_supp ⟨x, hcx_ne, rfl⟩)
    have h_cyl_zero : ∀ qX : BDLCX1 pcode M, qXOwnerX pcode M qX = x → h (Sum.inl qX) = 0 := by
      intro qX hqX
      by_contra hqX_ne
      have h_qX_in := h_supp ⟨Sum.inl qX, hqX_ne, rfl⟩
      have h_x_in := ownerX_mem_ball3D_of_bdlCylinderStepX_posQ_inl pcode M hD x0 hr qX h_qX_in
      rw [hqX] at h_x_in
      exact hx_in (ball3D_mono x0 (by linarith) hrR h_x_in)
    exact fullCylinderCocycle_eq_zero_of_cylinder_zero pcode M h c x hc_x h_cyl_zero mX rfl

/-- Local syndrome preservation for `coarseProjCocycle` on `Ball3D x0 R_coarse`:
    if `syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0` for all `mZ ∈ Ball3D x0 R_fine`
    with `R_coarse + 6 * D_edge ≤ R_fine`, then `syndrome (dualCode pcode) (coarseProjCocycle pcode M h) z0 = 0`
    for all `z0 ∈ Ball3D x0 R_coarse`. -/
theorem syndrome_coarseProjCocycle_of_ball {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (x0 : Point3D) {R_coarse R_fine : ℝ}
    (hR0 : 0 ≤ R_coarse) (hRR : R_coarse + 6 * D_edge ≤ R_fine)
    (h : BDLStepXQ pcode M → ZMod 2)
    (h_syn : ∀ mZ : BDLStepXMZ pcode M,
      (bdlCylinderStepX pcode M).posZ mZ ∈ ball3D x0 R_fine →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0)
    (z0 : M_Z) (hz0 : pcode.posZ z0 ∈ ball3D x0 R_coarse) :
    syndrome (dualCode pcode) (coarseProjCocycle pcode M h) z0 = 0 := by
  have hD0 := hD.1
  apply syndrome_coarseProjCocycle_eq pcode M h z0
  · intro eZ heZ
    have hq_in : pcode.posQ eZ.val.1 ∈ ball3D x0 (R_coarse + D_edge) := by
      have hz_eZ : pcode.posZ eZ.val.2 ∈ ball3D x0 R_coarse := heZ ▸ hz0
      exact ball3D_step_of_distSq3D_le x0 (pcode.posZ eZ.val.2) (pcode.posQ eZ.val.1)
        hR0 hD0 hz_eZ (hD.2.1 eZ.val.2 eZ.val.1 eZ.property)
    apply cylinderResidualCocycle_term_eq_coarse pcode M h eZ
    · intro x hx qX hqX
      have hx_in : pcode.posX x ∈ ball3D x0 (R_coarse + 2 * D_edge) := by
        have h1 := ball3D_step_of_distSq3D_le x0 (pcode.posQ eZ.val.1) (pcode.posX x)
          (by linarith) hD0 hq_in (by rw [distSq3D_comm]; exact hD.2.2 x eZ.val.1 hx)
        have h_eq : R_coarse + D_edge + D_edge = R_coarse + 2 * D_edge := by ring
        rw [h_eq] at h1; exact h1
      apply cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h x
      · intro seg b hseg
        apply h_syn
        have h_grid := bdlCylinderStepX_posZ_grid_mem_ball3D_of_posX pcode M hD x0
          (by linarith) x hx_in seg b hseg
        exact ball3D_mono x0 (by linarith) (by linarith) h_grid
      · intro s' k' b' hs'
        apply h_syn
        have h_col := bdlCylinderStepX_posZ_collar_mem_ball3D_of_posX pcode M hD x0
          (by linarith) x hx_in s' k' b' hs'
        exact ball3D_mono x0 (by linarith) (by linarith) h_col
      · exact hqX
    · intro k'
      apply h_syn
      have h_arm := bdlCylinderStepX_posZ_arm_mem_ball3D_of_posQ pcode M hD x0
        (by linarith) eZ.val.1 hq_in eZ k' 0 rfl
      exact ball3D_mono x0 (by linarith) (by linarith) h_arm
  · apply h_syn
    change pcode.posZ z0 ∈ ball3D x0 R_fine
    exact ball3D_mono x0 hR0 (by linarith) hz0

/-! ## 3. Local Coboundary Exactness of `fullCylinderCocycle` on `ball3D` -/

/-- Local coboundary exactness for `fullCylinderCocycle` on `Ball3D x0 r`:
    if `syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0` on `Ball3D x0 R_fine`
    and `coarseProjCocycle pcode M h q0 = checkGen (dualCode pcode) c q0` on `Ball3D x0 r_coarse`
    with `r + D_edge ≤ r_coarse` and `r + 5 * D_edge ≤ R_fine`,
    then `h q = checkGen (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) q`
    for all `q ∈ Ball3D x0 r`. -/
theorem checkGen_fullCylinderCocycle_of_ball {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (hq_z : ∀ q : Q, ∃ z : M_Z, pcode.checkZ z q ≠ 0)
    (x0 : Point3D) {r r_coarse R_fine : ℝ}
    (hr0 : 0 ≤ r) (hrr : r + D_edge ≤ r_coarse) (hrR : r + 5 * D_edge ≤ R_fine)
    (h : BDLStepXQ pcode M → ZMod 2) (c : M_X → ZMod 2)
    (h_syn : ∀ mZ : BDLStepXMZ pcode M,
      (bdlCylinderStepX pcode M).posZ mZ ∈ ball3D x0 R_fine →
      syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0)
    (hc_eq : ∀ q0 : Q, pcode.posQ q0 ∈ ball3D x0 r_coarse →
      coarseProjCocycle pcode M h q0 = checkGen (dualCode pcode) c q0)
    (q : BDLStepXQ pcode M) (hq_in : (bdlCylinderStepX pcode M).posQ q ∈ ball3D x0 r) :
    h q = checkGen (dualCode (bdlCylinderStepX pcode M)) (fullCylinderCocycle pcode M h c) q := by
  have hD0 := hD.1
  apply fullCylinderCocycle_eq_of_residual pcode M h c q
  rw [checkGen_dual_liftStepXMX]
  rcases q with qX | ⟨v0, b⟩
  · let x := qXOwnerX pcode M qX
    have hx_in : pcode.posX x ∈ ball3D x0 (r + 2 * D_edge) :=
      ownerX_mem_ball3D_of_bdlCylinderStepX_posQ_inl pcode M hD x0 hr0 qX hq_in
    have h_zero : cylinderResidualCocycle pcode M h (Sum.inl qX) = 0 := by
      apply cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h x
      · intro seg b' hseg
        apply h_syn
        have h_grid := bdlCylinderStepX_posZ_grid_mem_ball3D_of_posX pcode M hD x0
          (by linarith) x hx_in seg b' hseg
        exact ball3D_mono x0 (by linarith) (by linarith) h_grid
      · intro s' k' b' hs'
        apply h_syn
        have h_col := bdlCylinderStepX_posZ_collar_mem_ball3D_of_posX pcode M hD x0
          (by linarith) x hx_in s' k' b' hs'
        exact ball3D_mono x0 (by linarith) (by linarith) h_col
      · rfl
    rw [h_zero]
    rfl
  · let q0 := xq0OwnerQ pcode M v0
    have hq0_in : pcode.posQ q0 ∈ ball3D x0 (r + D_edge) :=
      ownerQ_mem_ball3D_of_xq0Pos pcode M hD x0 hr0 v0 hq_in
    have h_inr : cylinderResidualCocycle pcode M h (Sum.inr (v0, b)) =
        coarseProjCocycle pcode M h q0 := by
      apply cylinderResidualCocycle_inr_eq_coarse pcode M hq_z h q0
      · intro x hx qX hqX
        have hx_in : pcode.posX x ∈ ball3D x0 (r + 2 * D_edge) := by
          have h1 := ball3D_step_of_distSq3D_le x0 (pcode.posQ q0) (pcode.posX x)
            (by linarith) hD0 hq0_in (by rw [distSq3D_comm]; exact hD.2.2 x q0 hx)
          have h_eq : r + D_edge + D_edge = r + 2 * D_edge := by ring
          rw [h_eq] at h1; exact h1
        apply cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h x
        · intro seg b' hseg
          apply h_syn
          have h_grid := bdlCylinderStepX_posZ_grid_mem_ball3D_of_posX pcode M hD x0
            (by linarith) x hx_in seg b' hseg
          exact ball3D_mono x0 (by linarith) (by linarith) h_grid
        · intro s' k' b' hs'
          apply h_syn
          have h_col := bdlCylinderStepX_posZ_collar_mem_ball3D_of_posX pcode M hD x0
            (by linarith) x hx_in s' k' b' hs'
          exact ball3D_mono x0 (by linarith) (by linarith) h_col
        · exact hqX
      · intro eZ k' b' heZ
        apply h_syn
        have h_arm := bdlCylinderStepX_posZ_arm_mem_ball3D_of_posQ pcode M hD x0
          (by linarith) q0 hq0_in eZ k' b' heZ
        exact ball3D_mono x0 (by linarith) (by linarith) h_arm
      · intro eZ b' heZ
        apply h_syn
        have h_vert := bdlCylinderStepX_posZ_vert_mem_ball3D_of_posQ pcode M hD x0
          (by linarith) q0 hq0_in eZ b' heZ
        exact ball3D_mono x0 (by linarith) (by linarith) h_vert
      · rfl
    rw [h_inr, hc_eq q0 (ball3D_mono x0 (by linarith) hrr hq0_in)]
    rfl

/-! ## 4. One-Step Primal & Dual Reductions and `HasBDLConeInvariants` -/

/-- **One-Step Dual Global Stabilizer Reduction Across `bdlCylinderStepX` (`bdlCylinderStepX_dual_globalStabilizers_step`):** -/
theorem bdlCylinderStepX_dual_globalStabilizers_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (hq_z : ∀ q : Q, ∃ z : M_Z, pcode.checkZ z q ≠ 0)
    (x0 : Point3D) {r R_coarse : ℝ} (hr0 : 0 ≤ r) (hrR : r + 2 * D_edge ≤ R_coarse)
    (h_coarse_gen : globalStabilizersInBall (dualCode pcode) x0 (r + 3 * D_edge) ⊆
      locallyGeneratedInBall (dualCode pcode) x0 R_coarse) :
    globalStabilizersInBall (dualCode (bdlCylinderStepX pcode M)) x0 r ⊆
      locallyGeneratedInBall (dualCode (bdlCylinderStepX pcode M)) x0 (R_coarse + 2 * D_edge) := by
  intro h ⟨hh_syn, hh_supp⟩
  have h_coarse_in : coarseProjCocycle pcode M h ∈
      globalStabilizersInBall (dualCode pcode) x0 (r + 3 * D_edge) :=
    ⟨syndrome_coarseProjCocycle_global pcode M hov h_conn h hh_syn,
     coarseProjCocycle_supp1_subset pcode M hD x0 hr0 h hh_supp⟩
  obtain ⟨c, hc_supp, hc_gen⟩ := h_coarse_gen h_coarse_in
  exact ⟨fullCylinderCocycle pcode M h c,
    fullCylinderCocycle_supp2_subset pcode M hD x0 hr0 hrR h c hh_supp hc_supp,
    checkGen_fullCylinderCocycle_global pcode M hov h_conn hq_z h c hh_syn hc_gen⟩

/-- **One-Step `LocalCocycleExtends` Reduction Across `bdlCylinderStepX` (`bdlCylinderStepX_localCocycleExtends_step`):** -/
theorem bdlCylinderStepX_localCocycleExtends_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (hq_z : ∀ q : Q, ∃ z : M_Z, pcode.checkZ z q ≠ 0)
    (x0 : Point3D) {r R_coarse R_fine : ℝ}
    (hr0 : 0 ≤ r) (hR0 : 0 ≤ R_coarse)
    (hrR : r + 5 * D_edge ≤ R_fine) (hRR : R_coarse + 6 * D_edge ≤ R_fine)
    (h_ext_coarse : LocalCocycleExtends pcode x0 (r + D_edge) R_coarse) :
    LocalCocycleExtends (bdlCylinderStepX pcode M) x0 r R_fine := by
  intro h hh_syn
  have h_coarse_syn : ∀ z0 : M_Z, pcode.posZ z0 ∈ ball3D x0 R_coarse →
      syndrome (dualCode pcode) (coarseProjCocycle pcode M h) z0 = 0 :=
    fun z0 hz0 => syndrome_coarseProjCocycle_of_ball pcode M hD hov h_conn x0 hR0 hRR h hh_syn z0 hz0
  obtain ⟨c, hc_eq⟩ := h_ext_coarse (coarseProjCocycle pcode M h) h_coarse_syn
  refine ⟨fullCylinderCocycle pcode M h c, fun q hq_in => ?_⟩
  exact checkGen_fullCylinderCocycle_of_ball pcode M hD hov h_conn hq_z x0 hr0 (le_refl _) hrR h c hh_syn hc_eq q hq_in

/-- **One-Step Primal Global Stabilizer Reduction Across `bdlCylinderStepX` (`bdlCylinderStepX_primal_globalStabilizers_step`):** -/
theorem bdlCylinderStepX_primal_globalStabilizers_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (hq_z : ∀ q : Q, ∃ z : M_Z, pcode.checkZ z q ≠ 0)
    (x0 : Point3D) {r R_coarse R_fine : ℝ}
    (hr0 : 0 ≤ r) (hR0 : 0 ≤ R_coarse)
    (hrR : r + 5 * D_edge ≤ R_fine) (hRR : R_coarse + 6 * D_edge ≤ R_fine)
    (h_primal_coarse : globalStabilizersInBall pcode x0 (r + D_edge) ⊆
      locallyGeneratedInBall pcode x0 R_coarse) :
    globalStabilizersInBall (bdlCylinderStepX pcode M) x0 r ⊆
      locallyGeneratedInBall (bdlCylinderStepX pcode M) x0 R_fine := by
  rw [local_gen_iff_localCocycleExtends] at h_primal_coarse ⊢
  exact bdlCylinderStepX_localCocycleExtends_step pcode M hD hov h_conn hq_z x0 hr0 hR0 hrR hRR h_primal_coarse

/-- **One-Step Global Stabilizer Reduction Across `bdlPerturbStep` (`bdlPerturbStep_globalStabilizers_step`):** -/
theorem bdlPerturbStep_globalStabilizers_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L : ℕ) (hL : 0 < L)
    (cQ : Q → Point3D) (cZ : M_Z → Point3D) (cX : M_X → Point3D)
    {C_shift : ℝ} (hC : 0 ≤ C_shift)
    (hcQ : ∀ q, distSq3D (cQ q) (fun _ => 0) ≤ (C_shift * (L : ℝ)) ^ 2)
    (hcZ : ∀ mZ, distSq3D (cZ mZ) (fun _ => 0) ≤ (C_shift * (L : ℝ)) ^ 2)
    (x0 : Point3D) {r R_coarse : ℝ} (hr0 : 0 ≤ r) (hR0 : 0 ≤ R_coarse)
    (h_coarse : globalStabilizersInBall code (fun axis => x0 axis / (L : ℝ)) (r / (L : ℝ) + C_shift) ⊆
      locallyGeneratedInBall code (fun axis => x0 axis / (L : ℝ)) R_coarse) :
    globalStabilizersInBall (bdlPerturbStep code L cQ cZ cX) x0 r ⊆
      locallyGeneratedInBall (bdlPerturbStep code L cQ cZ cX) x0 ((L : ℝ) * (R_coarse + C_shift)) := by
  intro g ⟨hg_syn, hg_supp⟩
  have hg_coarse : g ∈ globalStabilizersInBall code (fun axis => x0 axis / (L : ℝ)) (r / (L : ℝ) + C_shift) := by
    refine ⟨hg_syn, ?_⟩
    intro p ⟨q, hq_ne, hp⟩; subst hp
    have h_in_p := hg_supp ⟨q, hq_ne, rfl⟩
    exact perturb_point_mem_coarse_ball x0 (code.posQ q) (cQ q) L hL hr0 hC (hcQ q) h_in_p
  obtain ⟨c2, hc2_supp, hc2_gen⟩ := h_coarse hg_coarse
  refine ⟨c2, ?_, hc2_gen⟩
  intro p ⟨mZ, hmZ_ne, hp⟩; subst hp
  have h_in_c := hc2_supp ⟨mZ, hmZ_ne, rfl⟩
  exact coarse_ball_mem_perturb_point x0 (code.posZ mZ) (cZ mZ) L hL hR0 hC (hcZ mZ) h_in_c

/-- Combined structural and geometric invariants preserved across all half-steps of `bdlRandomCode`. -/
def HasBDLConeInvariants (B : BundledCSSCode3D) : Prop :=
  HasBoundedCheckDegreeOverlap B ∧
  HasInteractionRange8 B ∧
  HasUnitBallDensityT B ∧
  HasEveryQubitChecked B.code ∧
  HasConnectedXLinks B.code ∧
  HasConnectedXLinks (dualCode B.code)

/-- Symmetry of `HasBDLConeInvariants` under CSS code duality (`dualBundled`). -/
lemma hasBDLConeInvariants_dualBundled (B : BundledCSSCode3D)
    (h : HasBDLConeInvariants B) :
    HasBDLConeInvariants (dualBundled B) := by
  rcases h with ⟨h_ov, h8, h_dens, h_chk, h_conn_p, h_conn_d⟩
  exact ⟨dualBundled_preserves_bounded_check_degree_overlap B h_ov,
         dualBundled_preserves_interaction_range8 B h8,
         dualBundled_preserves_unit_ball_density B h_dens,
         hasEveryQubitChecked_dualCode B.code h_chk,
         h_conn_d,
         h_conn_p⟩

/-- The base surface seed code `bdlSurfaceSeedBundled` satisfies `HasBDLConeInvariants`. -/
lemma hasBDLConeInvariants_surfaceSeed :
    HasBDLConeInvariants bdlSurfaceSeedBundled :=
  ⟨hasBoundedCheckDegreeOverlap_surfaceSeed,
   hasInteractionRange8_surfaceSeed,
   hasUnitBallDensityT_surfaceSeed,
   hasEveryQubitChecked_surfaceSeed,
   hasConnectedXLinks_surfaceSeed.1,
   hasConnectedXLinks_surfaceSeed.2⟩

/-- `HasEveryQubitChecked` implies `HasNoIsolatedQ` (`∀ q, ∃ x, checkX x q ≠ 0`). -/
lemma hasNoIsolatedQ_of_hasEveryQubitChecked {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (h : HasEveryQubitChecked code) :
    HasNoIsolatedQ code :=
  ⟨fun q _ => h.2 q, fun q _ => h.1 q⟩

/-- `HasBDLConeInvariants B` guarantees that `bdlLLLPerturbation B` is a `ValidLLLSphericalCapPerturbation`. -/
lemma validLLLSphericalCapPerturbation_of_invariants (B : BundledCSSCode3D)
    (h : HasBDLConeInvariants B) :
    ValidLLLSphericalCapPerturbation B (bdlLLLPerturbation B) := by
  have h_deg : HasBoundedSimplexDegreeD B 32 :=
    hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap B h.1
  exact bdlLLLPerturbation_spec_of_exists B
    (bdl_step1_lll_perturbation_exists B h_deg h.2.1 h.2.2.1)

/-- Any code with `HasInteractionRange8` and perturbations in `[0, 1]` satisfies `HasCoarseEdgeBound pcode 15`. -/
lemma hasCoarseEdgeBound_of_validLLLPerturbation (B : BundledCSSCode3D)
    (h_valid : ValidLLLSphericalCapPerturbation B (bdlLLLPerturbation B)) :
    let c := bdlLLLPerturbation B
    HasCoarseEdgeBound (bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2)
      ((2 * bdlAlpha + 1) * (bdlLambda : ℝ)) := by
  refine ⟨by dsimp [bdlAlpha, bdlLambda]; positivity, ?_, ?_⟩
  · intro z q hzq
    exact (h_valid.2.2.2.1 z q hzq).2
  · intro x q hxq
    exact (h_valid.2.2.2.2.1 x q hxq).2

/-- `bdlRandomStepX` preserves `HasBDLConeInvariants`. -/
lemma hasBDLConeInvariants_bdlRandomStepX (B : BundledCSSCode3D)
    (h : HasBDLConeInvariants B) :
    HasBDLConeInvariants (bdlRandomStepX B) := by
  rcases h with ⟨h_ov, h8, h_dens, h_chk, h_conn_p, h_conn_d⟩
  have h_deg : HasBoundedSimplexDegreeD B 32 :=
    hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap B h_ov
  have hq : HasNoIsolatedQ B.code := hasNoIsolatedQ_of_hasEveryQubitChecked B.code h_chk
  have h_conn_step := hasConnectedXLinks_bdlRandomStepX B ⟨h_conn_p, h_conn_d⟩ hq
  exact ⟨bdlRandomStepX_preserves_bounded_check_degree_overlap B h_ov,
         bdlRandomStepX_preserves_interaction_range8 B h8,
         bdlRandomStepX_preserves_unit_ball_density B h_deg h8 hq h_dens,
         hasEveryQubitChecked_bdlCylinderStepX _ bdlSubdivPred h_chk,
         h_conn_step.1,
         h_conn_step.2⟩

/-- `bdlRandomStepZ` preserves `HasBDLConeInvariants`. -/
lemma hasBDLConeInvariants_bdlRandomStepZ (B : BundledCSSCode3D)
    (h : HasBDLConeInvariants B) :
    HasBDLConeInvariants (bdlRandomStepZ B) :=
  hasBDLConeInvariants_dualBundled (bdlRandomStepX (dualBundled B))
    (hasBDLConeInvariants_bdlRandomStepX (dualBundled B)
      (hasBDLConeInvariants_dualBundled B h))

/-- Half-step sequence `bdlHalfStep n` (`n = 0, 1, ...`) interpolating between `bdlSurfaceSeedBundled` (`n = 0`)
    and `bdlRandomBundled k = bdlHalfStep (2 * (k + 1))`. -/
noncomputable def bdlHalfStep : ℕ → BundledCSSCode3D
  | 0 => bdlSurfaceSeedBundled
  | n + 1 => if n % 2 = 0 then bdlRandomStepX (bdlHalfStep n) else bdlRandomStepZ (bdlHalfStep n)

/-- Even half-steps `bdlHalfStep (2 * m)` coincide with `bdlIteratedBundled m`. -/
lemma bdlHalfStep_even (m : ℕ) :
    bdlHalfStep (2 * m) = (bdlRandomStepZ ∘ bdlRandomStepX)^[m] bdlSurfaceSeedBundled := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h_step1 : bdlHalfStep (2 * (m + 1)) = bdlRandomStepZ (bdlHalfStep (2 * m + 1)) := by
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      have h_odd : (2 * m + 1) % 2 ≠ 0 := by omega
      rw [h1]; exact if_neg h_odd
    have h_step2 : bdlHalfStep (2 * m + 1) = bdlRandomStepX (bdlHalfStep (2 * m)) := by
      have h_even : (2 * m) % 2 = 0 := by omega
      exact if_pos h_even
    rw [h_step1, h_step2, ih, Function.iterate_succ_apply']
    rfl

/-- At top scale `2 * k + 2`, `bdlHalfStep (2 * k + 2)` coincides with `bdlRandomBundled k`. -/
lemma bdlHalfStep_eq_bdlRandomBundled (k : ℕ) :
    bdlHalfStep (2 * (k + 1)) = bdlRandomBundled k :=
  bdlHalfStep_even (k + 1)

/-- Every half-step complex `bdlHalfStep n` satisfies `HasBDLConeInvariants`. -/
lemma hasBDLConeInvariants_bdlHalfStep (n : ℕ) :
    HasBDLConeInvariants (bdlHalfStep n) := by
  induction n with
  | zero => exact hasBDLConeInvariants_surfaceSeed
  | succ n ih =>
    dsimp [bdlHalfStep]
    split_ifs
    · exact hasBDLConeInvariants_bdlRandomStepX (bdlHalfStep n) ih
    · exact hasBDLConeInvariants_bdlRandomStepZ (bdlHalfStep n) ih

end WeldedHierarchy
