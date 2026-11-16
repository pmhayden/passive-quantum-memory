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

import Proofs.HierarchicalClusterDecoder.ClusterDecoderSynthesis
import Proofs.HierarchicalClusterDecoder.ZeroSpilloverWitnessHelpers

/-!
# Zero-Spillover Realizable Cluster Steps and Multiscale Intact Witness Pools

Defines `HasZeroSpilloverBallParityWitnessFamily`, cleaner-closed Tanner components (`IsCleanerClosedTannerComponent`), multiscale connectivity relations (`MultiscaleClusterConnPrimal`, `MultiscaleClusterConnDual`), and intact percolating cluster pools (`multiscaleIntactWitnessPoolPrimal`, `multiscaleIntactWitnessPoolDual`). Proves exact zero-spillover error-chain realizability across primal cylinder fibers (`primal_cylinder_subsyndrome_zero_spillover_recovery`) and isolated dual cleaner components (`dual_cleaner_isolated_component_coboundary_eq`).

## References

* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`), Proposition 5.3 (`prop:cluster-decoder-witness`)
* Part II, Section 2 (`subsec:setup`), Definition 2.5 (`def:syndrome-safe`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.1 (`lem:seed-code`), Definition 4.2 (`def:multiscale-cluster-decoder`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
* Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

namespace WeldedHierarchy
namespace BDLDecoder

/-- **Zero-Spillover Ball Parity Witness Family (`HasZeroSpilloverBallParityWitnessFamily`,
    Part II, Definition 2.5(ii) (`def:syndrome-safe`) and
    Section 5.1 (`subsec:direct-worldline-synthesis`),
    Theorem 4.1(i)–(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    Refines `HasBallParityWitnessFamily` by requiring that:
    - every check-syndrome witness `c ∈ W` is the exact syndrome of a valid 1-chain `e_C : Q → ZMod 2`
      (`syndrome code e_C = c`) with zero spillover outside `c`
      ($\partial_{\mathrm{chk}} E_C^{\mathrm{full}} = \mathbf{1}_{C_m} \in \mathcal{V}_{\mathrm{valid}}$,
      Part II, Equation (77) (`eq:exact-intact-cluster-boundary`)),
    - every witness `c ∈ W` has weight at least `w` (`(w : ℝ) ≤ syndromeWeight c`), and
    - for every weight shell `m : ℕ`, the number of witnesses in `W` of weight `m` is bounded by
      `B ^ m` ($N_k(m) \le K_{\mathrm{cl}}^m$, Part II, Definition 2.5(ii) (`def:syndrome-safe`) and
      Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
def HasZeroSpilloverBallParityWitnessFamily {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (_L_Z L_X : Q → ZMod 2) (r : ℝ) (w B : ℕ) : Prop :=
  ∃ (ψ : (M_X → ZMod 2) → ZMod 2) (W : Finset (M_X → ZMod 2)),
    ψ 0 = 0 ∧
    (∀ m : ℕ, (W.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤ B ^ m) ∧
    (∀ c ∈ W, (w : ℝ) ≤ syndromeWeight c) ∧
    (∀ c ∈ W, ∃ e_C : Q → ZMod 2, syndrome code e_C = c) ∧
    (∀ (e e' : Q → ZMod 2) (x0 : Point3D),
      (∀ q : Q, e q ≠ e' q → code.posQ q ∈ ball3D x0 r) →
      ψ (syndrome code e') + dualPairing L_X e' ≠
        ψ (syndrome code e) + dualPairing L_X e →
      ∃ c ∈ W,
        (∀ m : M_X, c m ≠ 0 → syndrome code e m ≠ 0) ∨
        (∀ m : M_X, c m ≠ 0 → syndrome code e' m ≠ 0))

lemma hasZeroSpilloverBallParityWitnessFamily_dual_dual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {code : CSSCode3D Q M_Z M_X} {L_Z L_X : Q → ZMod 2} {r : ℝ} {w B : ℕ}
    (h : HasZeroSpilloverBallParityWitnessFamily code L_Z L_X r w B) :
    HasZeroSpilloverBallParityWitnessFamily (dualCode (dualCode code)) L_Z L_X r w B := h

lemma hasZeroSpilloverBallParityWitnessFamily_transportBundled {B1 B2 : BundledCSSCode3D} (hB : B1 = B2)
    {L_Z L_X : B1.Q → ZMod 2} {r : ℝ} {w B : ℕ}
    (h : HasZeroSpilloverBallParityWitnessFamily B1.code L_Z L_X r w B) :
    HasZeroSpilloverBallParityWitnessFamily B2.code
      (transportBundledChain hB L_Z) (transportBundledChain hB L_X) r w B := by
  subst hB; exact h

lemma hasZeroSpilloverBallParityWitnessFamily_dual_transportBundled {B1 B2 : BundledCSSCode3D} (hB : B1 = B2)
    {L_Z L_X : B1.Q → ZMod 2} {r : ℝ} {w B : ℕ}
    (h : HasZeroSpilloverBallParityWitnessFamily (dualCode B1.code) L_X L_Z r w B) :
    HasZeroSpilloverBallParityWitnessFamily (dualCode B2.code)
      (transportBundledChain hB L_X) (transportBundledChain hB L_Z) r w B := by
  subst hB; exact h

/-- **Exact HPL Dual Coboundary Commutation (`syndrome_dual_liftCylinderLX_eq_embedCoarse`,
    Part II, Proposition 4.3(i) (`prop:rca-hierarchy`) and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`))**:
    For every coarse 1-cochain `e0 : Q → ZMod 2`, lifting `e0` via the HPL chain map
    `liftCylinderLX pcode M e0` ($\widetilde{\iota}_i^1(e_0)$) commutes with the dual check
    coboundary operator via the 3-layer coarse syndrome embedding `embedCoarseStepXMZ`:
    $\partial_{\mathrm{chk}}^{(i)}(\widetilde{\iota}_i^1(e_0)) = \Delta_3(\partial_{\mathrm{chk}}^{(i-1)} e_0)$,
    with zero spillover onto cylinder (`BDLCX2`) or star (`BDLCQ2`) checks. -/
theorem syndrome_dual_liftCylinderLX_eq_embedCoarse {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (e0 : Q → ZMod 2) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) (liftCylinderLX pcode M e0) =
      embedCoarseStepXMZ pcode M (syndrome (dualCode pcode) e0) := by
  ext mZ
  simp only [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [Fintype.sum_sum_type]
  have h_qX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M mZ (Sum.inl qX) * liftCylinderLX pcode M e0 (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => by dsimp [liftCylinderLX]; simp)
  rw [h_qX, zero_add]
  rcases mZ with mZX | ⟨mZQ | mZZ⟩
  · dsimp [embedCoarseStepXMZ]
    exact Finset.sum_eq_zero (fun _ _ => zero_mul _)
  · dsimp [bdlStepXCheckZ, embedCoarseStepXMZ]
    rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
    · have h_exp : ∀ qQ : BDLCQ1 pcode M,
          bdlDeltaQ1 pcode M (Sum.inl (eZ, k, bZ)) qQ * liftCylinderLX pcode M e0 (Sum.inr qQ) =
          (if qQ = (armStart pcode M eZ k, bZ) then 1 else 0) * liftCylinderLX pcode M e0 (Sum.inr qQ) +
          (if qQ = (armEnd pcode M eZ k, bZ) then 1 else 0) * liftCylinderLX pcode M e0 (Sum.inr qQ) := by
        intro qQ; dsimp [bdlDeltaQ1]; ring
      simp_rw [h_exp, Finset.sum_add_distrib]
      have h1 : (∑ qQ : BDLCQ1 pcode M,
          (if qQ = (armStart pcode M eZ k, bZ) then (1 : ZMod 2) else 0) *
            liftCylinderLX pcode M e0 (Sum.inr qQ)) = e0 eZ.val.1 := by
        rw [Finset.sum_eq_single (armStart pcode M eZ k, bZ)]
        · dsimp [liftCylinderLX]; rw [if_pos rfl, one_mul, xq0OwnerQ_armStart]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      have h2 : (∑ qQ : BDLCQ1 pcode M,
          (if qQ = (armEnd pcode M eZ k, bZ) then (1 : ZMod 2) else 0) *
            liftCylinderLX pcode M e0 (Sum.inr qQ)) = e0 eZ.val.1 := by
        rw [Finset.sum_eq_single (armEnd pcode M eZ k, bZ)]
        · dsimp [liftCylinderLX]; rw [if_pos rfl, one_mul, xq0OwnerQ_armEnd]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      rw [h1, h2, zmod2_add_self]
    · have h_exp : ∀ qQ : BDLCQ1 pcode M,
          bdlDeltaQ1 pcode M (Sum.inr (eZ, v)) qQ * liftCylinderLX pcode M e0 (Sum.inr qQ) =
          (if qQ = (Sum.inr (Sum.inr eZ), 0) then 1 else 0) * liftCylinderLX pcode M e0 (Sum.inr qQ) +
          (if qQ = (Sum.inr (Sum.inr eZ), v.succ) then 1 else 0) * liftCylinderLX pcode M e0 (Sum.inr qQ) := by
        intro qQ; dsimp [bdlDeltaQ1]; ring
      simp_rw [h_exp, Finset.sum_add_distrib]
      have h1 : (∑ qQ : BDLCQ1 pcode M,
          (if qQ = (Sum.inr (Sum.inr eZ), 0) then (1 : ZMod 2) else 0) *
            liftCylinderLX pcode M e0 (Sum.inr qQ)) = e0 eZ.val.1 := by
        rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), 0)]
        · dsimp [liftCylinderLX, xq0OwnerQ]; rw [if_pos rfl, one_mul]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      have h2 : (∑ qQ : BDLCQ1 pcode M,
          (if qQ = (Sum.inr (Sum.inr eZ), v.succ) then (1 : ZMod 2) else 0) *
            liftCylinderLX pcode M e0 (Sum.inr qQ)) = e0 eZ.val.1 := by
        rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), v.succ)]
        · dsimp [liftCylinderLX, xq0OwnerQ]; rw [if_pos rfl, one_mul]
        · intro qQ _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      rw [h1, h2, zmod2_add_self]
  · dsimp [bdlStepXCheckZ, embedCoarseStepXMZ]
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single mZZ.2]
    · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have h_inl : (∑ q : Q, bdlGQZ1 pcode M mZZ (Sum.inl q, mZZ.2) *
          liftCylinderLX pcode M e0 (Sum.inr (Sum.inl q, mZZ.2))) = 0 :=
        Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGQZ1]; simp)
      have h_mid : (∑ p : ActiveZ pcode × Fin M,
          bdlGQZ1 pcode M mZZ (Sum.inr (Sum.inl p), mZZ.2) *
            liftCylinderLX pcode M e0 (Sum.inr (Sum.inr (Sum.inl p), mZZ.2))) = 0 :=
        Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGQZ1]; simp)
      rw [h_inl, zero_add, h_mid, zero_add]
      have h_term : ∀ eZ : ActiveZ pcode,
          bdlGQZ1 pcode M mZZ (Sum.inr (Sum.inr eZ), mZZ.2) *
            liftCylinderLX pcode M e0 (Sum.inr (Sum.inr (Sum.inr eZ), mZZ.2)) =
          if eZ.val.2 = mZZ.1 then e0 eZ.val.1 else 0 := by
        intro eZ; dsimp [bdlGQZ1, liftCylinderLX, xq0OwnerQ]
        by_cases heZ : eZ.val.2 = mZZ.1 <;> simp [heZ]
      simp_rw [h_term]; rw [sum_activeZ_eq pcode mZZ.1 e0]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    · intro b _ hne; apply Finset.sum_eq_zero; intro v0 _
      rcases v0 with _ | ⟨_ | eZ⟩ <;> dsimp [bdlGQZ1] <;> simp [hne]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- **Two-Stage Cleaner + HPL Dual Coboundary Zero-Spillover Recovery Identity
    (`syndrome_cleanTwoStageRX_add_liftCylinderLX_eq`,
    Part II, Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`),
    Equation (77) (`eq:exact-intact-cluster-boundary`))**:
    Whenever a fine Z-check syndrome `C1 : BDLStepXMZ pcode M → ZMod 2` satisfies the local
    cylinder, star, and 3-layer replication meta-checks so that two-stage cleaning `cleanTwoStageRX pcode M C1`
    leaves `embedCoarseStepXMZ pcode M c0`, and `e0 : Q → ZMod 2` is a coarse zero-spillover recovery
    chain for `c0` (`syndrome (dualCode pcode) e0 = c0`), the composite fine recovery chain
    `cleanTwoStageRX pcode M C1 + liftCylinderLX pcode M e0` ($E_i(C) \oplus \widetilde{\iota}_i^1(e_0)$)
    has exact check boundary `C1` with zero spillover. -/
theorem syndrome_cleanTwoStageRX_add_liftCylinderLX_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (C1 : BDLStepXMZ pcode M → ZMod 2) (c0 : M_Z → ZMod 2) (e0 : Q → ZMod 2)
    (h_clean : C1 + syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanTwoStageRX pcode M C1) =
      embedCoarseStepXMZ pcode M c0)
    (he0 : syndrome (dualCode pcode) e0 = c0) :
    syndrome (dualCode (bdlCylinderStepX pcode M))
      (cleanTwoStageRX pcode M C1 + liftCylinderLX pcode M e0) = C1 := by
  rw [map_add, syndrome_dual_liftCylinderLX_eq_embedCoarse, he0]
  ext mZ
  have hm := congr_fun h_clean mZ
  simp only [Pi.add_apply] at hm ⊢
  have h2 := zmod2_add_self (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanTwoStageRX pcode M C1) mZ)
  linear_combination -hm + h2

/-- **Intact Fine Cluster Zero-Spillover Recovery Identity
    (`syndrome_intactCluster_cleanTwoStageRX_add_liftCylinderLX_eq`,
    Part II, Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`),
    Equation (77) (`eq:exact-intact-cluster-boundary`))**:
    For any realizable fine syndrome `C1 = syndrome (dualCode (bdlCylinderStepX pcode M)) h`
    (such as an isolated intact cluster component $\mathbf{1}_{C_i} \in \ker(\partial_{\mathrm{meta},\mathrm{loc}}^{(i)})$)
    and any coarse zero-spillover recovery chain `e0` for `rxCleanedCoarseSyndrome pcode M C1`,
    the lifted fine recovery chain `cleanTwoStageRX pcode M C1 + liftCylinderLX pcode M e0`
    has exact syndrome `C1` with zero spillover. -/
theorem syndrome_intactCluster_cleanTwoStageRX_add_liftCylinderLX_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q, ∃ z, pcode.checkZ z q ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (e0 : Q → ZMod 2)
    (he0 : syndrome (dualCode pcode) e0 =
      rxCleanedCoarseSyndrome pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h)) :
    let C1 := syndrome (dualCode (bdlCylinderStepX pcode M)) h
    syndrome (dualCode (bdlCylinderStepX pcode M))
      (cleanTwoStageRX pcode M C1 + liftCylinderLX pcode M e0) = C1 := by
  intro C1
  exact syndrome_cleanTwoStageRX_add_liftCylinderLX_eq pcode M C1
    (rxCleanedCoarseSyndrome pcode M C1) e0
    (rxCleanedCoarseProj_syndrome_eq pcode M hov hq_z h_conn h).2 he0

/-- **Primal Cleaner + HPL Coboundary Zero-Spillover Recovery Identity
    (`syndrome_add_liftCylinderLZ_eq`,
    Part II, Proposition 4.3(i) (`prop:rca-hierarchy`) and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`))**:
    Whenever a fine X-check syndrome `C1 : BDLStepXMX pcode M → ZMod 2` and local cylinder/star
    recovery chain `e_clean : BDLStepXQ pcode M → ZMod 2` satisfy
    `C1 + syndrome (bdlCylinderStepX pcode M) e_clean = embedCoarseStepXMX pcode M c0`, and
    `e0 : Q → ZMod 2` is a coarse zero-spillover recovery chain for `c0` (`syndrome pcode e0 = c0`),
    the composite fine recovery chain `e_clean + liftCylinderLZ pcode M e0` has exact check boundary
    `C1` with zero spillover. -/
theorem syndrome_add_liftCylinderLZ_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (C1 : BDLStepXMX pcode M → ZMod 2) (e_clean : BDLStepXQ pcode M → ZMod 2)
    (c0 : M_X → ZMod 2) (e0 : Q → ZMod 2)
    (h_clean : C1 + syndrome (bdlCylinderStepX pcode M) e_clean = embedCoarseStepXMX pcode M c0)
    (he0 : syndrome pcode e0 = c0) :
    syndrome (bdlCylinderStepX pcode M) (e_clean + liftCylinderLZ pcode M e0) = C1 := by
  rw [map_add, syndrome_liftCylinderLZ_eq_embedCoarse, he0]
  ext mX
  have hm := congr_fun h_clean mX
  simp only [Pi.add_apply] at hm ⊢
  have h2 := zmod2_add_self (syndrome (bdlCylinderStepX pcode M) e_clean mX)
  linear_combination -hm + h2

/-- **General Base-Scale Zero-Spillover Ball Parity Witness Theorem from Ball Filling
    (`hasZeroSpilloverBallParityWitnessFamily_of_ball_filling`,
    Part II, Definition 2.5(ii) (`def:syndrome-safe`) and
    Theorem 4.1(i)–(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    On any CSS code `code` where `syndrome (dualCode code) L_X = 0` and every cycle in `ball3D x0 r`
    is locally generated (`globalStabilizersInBall code x0 r ⊆ locallyGeneratedInBall code x0 R_fill`),
    the zero parity rule `ψ ≡ 0` and the pool `W = (Finset.univ.image (syndrome code)).erase 0` of all
    non-zero realizable syndromes form a `HasZeroSpilloverBallParityWitnessFamily` with minimum weight `1`
    and shell base `B ≥ |M_X|`. -/
theorem hasZeroSpilloverBallParityWitnessFamily_of_ball_filling {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2) (r R_fill : ℝ) {B : ℕ}
    (hB : Fintype.card M_X ≤ B)
    (h_syn_X : syndrome (dualCode code) L_X = 0)
    (h_fill : ∀ x0 : Point3D,
      globalStabilizersInBall code x0 r ⊆ locallyGeneratedInBall code x0 R_fill) :
    HasZeroSpilloverBallParityWitnessFamily code L_Z L_X r 1 B := by
  let ψ : (M_X → ZMod 2) → ZMod 2 := fun _ => 0
  let W : Finset (M_X → ZMod 2) := (Finset.univ.image (syndrome code)).erase 0
  refine ⟨ψ, W, rfl,
    fun m => card_filter_syndrome_weight_le W hB m,
    ?_, ?_, ?_⟩
  · intro c hc
    have hc_ne : c ≠ 0 := (Finset.mem_erase.mp hc).1
    have h_ex : ∃ x : M_X, c x ≠ 0 := by
      by_contra h_all
      push_neg at h_all
      exact hc_ne (funext h_all)
    rcases h_ex with ⟨x, hx⟩
    have hx_mem : x ∈ Finset.univ.filter (fun y => c y ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    have h_pos : 1 ≤ (Finset.univ.filter (fun y => c y ≠ 0)).card :=
      Finset.card_pos.mpr ⟨x, hx_mem⟩
    dsimp [syndromeWeight]
    exact_mod_cast h_pos
  · intro c hc
    have hc_img : c ∈ Finset.univ.image (syndrome code) := (Finset.mem_erase.mp hc).2
    rcases Finset.mem_image.mp hc_img with ⟨e_C, _, h_eq⟩
    exact ⟨e_C, h_eq⟩
  · intro e e' x0 h_diff h_disc
    dsimp [ψ] at h_disc
    rw [zero_add, zero_add] at h_disc
    by_cases he_zero : syndrome code e = 0
    · by_cases he'_zero : syndrome code e' = 0
      · exfalso
        let g : Q → ZMod 2 := e' + e
        have hg_syn : syndrome code g = 0 := by
          dsimp [g]; rw [map_add, he'_zero, he_zero, add_zero]
        have hg_supp : supp1 code g ⊆ ball3D x0 r := by
          intro p ⟨q, hq_ne, hp⟩
          subst hp
          apply h_diff q
          intro h_eq
          apply hq_ne
          dsimp [g]
          rw [h_eq]
          exact zmod2_add_self (e' q)
        obtain ⟨c2, _, hc2_gen⟩ := h_fill x0 ⟨hg_syn, hg_supp⟩
        have h_pair_zero : dualPairing L_X g = 0 := by
          rw [← hc2_gen]
          exact dualPairing_checkGen_zero code c2 L_X h_syn_X
        have h_pair_add : dualPairing L_X g = dualPairing L_X e' + dualPairing L_X e :=
          dualPairing_add_right_zmod2 L_X e' e
        rw [h_pair_add] at h_pair_zero
        have h_eq_pair : dualPairing L_X e' = dualPairing L_X e := by
          have h_alg : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
          exact h_alg _ _ h_pair_zero
        exact h_disc h_eq_pair
      · refine ⟨syndrome code e', Finset.mem_erase.mpr ⟨he'_zero,
          Finset.mem_image.mpr ⟨e', Finset.mem_univ e', rfl⟩⟩, Or.inr (fun m hm => hm)⟩
    · refine ⟨syndrome code e, Finset.mem_erase.mpr ⟨he_zero,
        Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩⟩, Or.inl (fun m hm => hm)⟩

/-- **Base-Scale Primal Zero-Spillover Ball Parity Witness Family (`hasZeroSpilloverBallParityWitnessFamily_bdlIterated1_primal`,
    Part II, Proposition 4.3(ii) (`prop:rca-hierarchy`) and
    Theorem 4.1(i)–(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    Established from `hasZeroSpilloverBallParityWitnessFamily_of_ball_filling`,
    `card_iterated1_le_clusterStepBase`, and `bdlHalfStep_subcylinder_filling`. -/
theorem hasZeroSpilloverBallParityWitnessFamily_bdlIterated1_primal
    {r : ℝ} (hr0 : 0 ≤ r) (hr_hi : r ≤ 7015) :
    HasZeroSpilloverBallParityWitnessFamily (bdlIteratedBundled 1).code
      (bdlIteratedLZ 1) (bdlIteratedLX 1)
      r (clusterRawWeight 0) (bdlClusterStepBase ^ 8) := by
  have h_hom := hasUniqueLogicalHomology_bdlIterated 1
  have hB : Fintype.card (bdlIteratedBundled 1).M_X ≤ bdlClusterStepBase ^ 8 := by
    have h_card := card_iterated1_le_clusterStepBase.1
    dsimp [clusterRawWeight] at h_card
    rwa [pow_one] at h_card
  exact hasZeroSpilloverBallParityWitnessFamily_of_ball_filling
    (bdlIteratedBundled 1).code (bdlIteratedLZ 1) (bdlIteratedLX 1) r bdlBaseFillingRadius
    hB h_hom.h_syn_X (fun x0 => (bdlHalfStep_subcylinder_filling 0 x0 hr0 hr_hi).1)

/-- **Base-Scale Dual Zero-Spillover Ball Parity Witness Family (`hasZeroSpilloverBallParityWitnessFamily_bdlIterated1_dual`,
    Part II, Proposition 4.3(ii) (`prop:rca-hierarchy`) and
    Theorem 4.1(i)–(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    Established from `hasZeroSpilloverBallParityWitnessFamily_of_ball_filling`,
    `card_iterated1_le_clusterStepBase`, and `bdlHalfStep_subcylinder_filling`. -/
theorem hasZeroSpilloverBallParityWitnessFamily_bdlIterated1_dual
    {r : ℝ} (hr0 : 0 ≤ r) (hr_hi : r ≤ 7015) :
    HasZeroSpilloverBallParityWitnessFamily (dualCode (bdlIteratedBundled 1).code)
      (bdlIteratedLX 1) (bdlIteratedLZ 1)
      r (clusterRawWeight 0) (bdlClusterStepBase ^ 8) := by
  have h_hom := hasUniqueLogicalHomology_bdlIterated 1
  have hB : Fintype.card (bdlIteratedBundled 1).M_Z ≤ bdlClusterStepBase ^ 8 := by
    have h_card := card_iterated1_le_clusterStepBase.2
    dsimp [clusterRawWeight] at h_card
    rwa [pow_one] at h_card
  exact hasZeroSpilloverBallParityWitnessFamily_of_ball_filling
    (dualCode (bdlIteratedBundled 1).code) (bdlIteratedLX 1) (bdlIteratedLZ 1) r bdlBaseFillingRadius
    hB h_hom.h_syn_Z (fun x0 => (bdlHalfStep_subcylinder_filling 0 x0 hr0 hr_hi).2)

/-! ## 1. Multiscale Zero-Spillover Intact-Cluster Recovery Building Blocks
    (Part II, Lemma 4.1 (`lem:seed-code`), Definition 4.2 (`def:multiscale-cluster-decoder`),
    Proposition 4.3(i) (`prop:rca-hierarchy`), Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`),
    and Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)) -/

/-- **Seed-Code Primal Syndrome Surjectivity (`syndrome_bdlSurfaceSeedCode_surjective`,
    Part II, Lemma 4.1 (`lem:seed-code`), Equation (69) (`eq:seed-code-cohomology`))**:
    On the base $[\![5,1,2]\!]$ planar surface seed code `bdlSurfaceSeedCode` ($\mathcal{C}_0 = \mathrm{bdlIteratedBundled}\;0$),
    the primal check coboundary map is surjective ($H_0(\mathcal{C}_0) = H^2(\mathcal{C}_0^*) = 0$):
    every X-check syndrome `s : Fin 2 → ZMod 2` is the exact syndrome of a physical 1-chain
    `e : Fin 5 → ZMod 2` with zero spillover. -/
theorem syndrome_bdlSurfaceSeedCode_surjective (s : Fin 2 → ZMod 2) :
    ∃ e : Fin 5 → ZMod 2, syndrome bdlSurfaceSeedCode e = s := by
  simp only [funext_iff]
  revert s
  decide

/-- **Seed-Code Dual Syndrome Surjectivity (`syndrome_dual_bdlSurfaceSeedCode_surjective`,
    Part II, Lemma 4.1 (`lem:seed-code`), Equation (69) (`eq:seed-code-cohomology`))**:
    On the dual of the base $[\![5,1,2]\!]$ planar surface seed code `dualCode bdlSurfaceSeedCode`
    ($\mathcal{C}_0^*$), the Z-check coboundary map $\delta_0^1 : \mathbb{F}_2^5 \to \mathbb{F}_2^2$ is surjective
    ($H^2(\mathcal{C}_0) = C_0^2 / \mathrm{im}(\delta_0^1) = 0$): every Z-check syndrome `s : Fin 2 → ZMod 2`
    is the exact syndrome of a 1-cochain `h : Fin 5 → ZMod 2` with zero spillover. -/
theorem syndrome_dual_bdlSurfaceSeedCode_surjective (s : Fin 2 → ZMod 2) :
    ∃ h : Fin 5 → ZMod 2, syndrome (dualCode bdlSurfaceSeedCode) h = s := by
  simp only [funext_iff]
  revert s
  decide

private def IsCylinderX0Chain {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X)
    (u : BDLStepXQ pcode M → ZMod 2) : Prop :=
  ∀ q : BDLStepXQ pcode M, u q ≠ 0 →
    ∃ qX : BDLCX1 pcode M, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x0

private lemma isCylinderX0Chain_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    IsCylinderX0Chain pcode M x0 0 := by
  intro q hq
  exact False.elim (hq rfl)

private lemma isCylinderX0Chain_add {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X)
    {u v : BDLStepXQ pcode M → ZMod 2}
    (hu : IsCylinderX0Chain pcode M x0 u) (hv : IsCylinderX0Chain pcode M x0 v) :
    IsCylinderX0Chain pcode M x0 (u + v) := by
  intro q hq
  by_cases huq : u q ≠ 0
  · exact hu q huq
  · push_neg at huq
    have hvq : v q ≠ 0 := by
      intro hv0
      apply hq
      change u q + v q = 0
      rw [huq, hv0, add_zero]
    exact hv q hvq

private lemma isCylinderX0Chain_singleQubit_inl {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) (qX : BDLCX1 pcode M)
    (h_own : cX1OwnerX pcode M qX = x0) :
    IsCylinderX0Chain pcode M x0 (singleQubit (Sum.inl qX)) := by
  intro q hq
  dsimp [singleQubit] at hq
  by_cases h_eq : q = Sum.inl qX
  · exact ⟨qX, h_eq, h_own⟩
  · rw [if_neg h_eq] at hq
    exact False.elim (hq rfl)

private lemma syndrome_singleQubit_inl_cX1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (qX : BDLCX1 pcode M) :
    syndrome (bdlCylinderStepX pcode M) (singleQubit (Sum.inl qX)) =
      fun mX => bdlDeltaX0 pcode M mX qX := by
  ext mX
  dsimp [syndrome, f2Syndrome, bdlCylinderStepX, singleQubit]
  rw [Finset.sum_eq_single (Sum.inl qX)]
  · rw [if_pos rfl, mul_one]
    rfl
  · intro q _ hne
    rw [if_neg hne, mul_zero]
  · intro h_abs
    exact False.elim (h_abs (Finset.mem_univ _))

private lemma exists_shellVertex_shift_to_layer_apex {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) (b : Fin 3) :
    ∀ (n : ℕ) (sv : ShellVertex pcode M),
      sv.val.2.val = n → sv.val.1.val.1 = x0 →
      ∃ u : BDLStepXQ pcode M → ZMod 2,
        IsCylinderX0Chain pcode M x0 u ∧
        syndrome (bdlCylinderStepX pcode M) u =
          singleQubit (Sum.inr (sv, b)) + singleQubit (Sum.inl (x0, b)) := by
  intro n
  induction n with
  | zero =>
    intro sv hn hsv_x0
    by_cases h_diag : IsDiagZeroVertex pcode M sv
    · rcases h_diag with ⟨_, z, hz⟩
      have h_link : InLinkOfX pcode M x0 (Sum.inr (Sum.inr z)) := by
        have hp := sv.val.1.property
        rwa [hsv_x0, hz] at hp
      obtain ⟨q, hX, hZ⟩ := h_link
      have h_ex : ∃ q' : Q, pcode.checkX x0 q' ≠ 0 ∧ pcode.checkZ z q' ≠ 0 := ⟨q, hX, hZ⟩
      have hsv_eq : sv = cornerDiagVertex pcode M x0 z h_ex := by
        apply Subtype.ext
        apply Prod.ext
        · exact Subtype.ext (Prod.ext hsv_x0 hz)
        · exact Fin.ext hn
      let qX1 : BDLCX1 pcode M := Sum.inl (cornerSpokeRadial pcode M x0 q hX, b)
      let qX2 : BDLCX1 pcode M := Sum.inr (Sum.inl (cornerSeg pcode M x0 q z hX hZ, b))
      refine ⟨singleQubit (Sum.inl qX1) + singleQubit (Sum.inl qX2),
        isCylinderX0Chain_add pcode M x0
          (isCylinderX0Chain_singleQubit_inl pcode M x0 qX1 rfl)
          (isCylinderX0Chain_singleQubit_inl pcode M x0 qX2 rfl), ?_⟩
      rw [map_add, syndrome_singleQubit_inl_cX1, syndrome_singleQubit_inl_cX1, hsv_eq]
      ext mX
      simp only [Pi.add_apply, singleQubit]
      dsimp [qX1, qX2, bdlDeltaX0]
      have hr0_spoke : (cornerSpokeRadial pcode M x0 q hX).val.val.2.val = 0 := rfl
      rw [if_pos hr0_spoke, shellSegStartVertex_cornerSeg, shellSegEndVertex_cornerSeg]
      have h_spoke : (cornerSpokeRadial pcode M x0 q hX).val = cornerSpoke pcode M x0 q hX := rfl
      have hx_spoke : (cornerSpoke pcode M x0 q hX).val.1.val.1 = x0 := rfl
      rw [h_spoke, hx_spoke]
      have h_cancel := zmod2_add_self
        (if mX = Sum.inr (cornerSpoke pcode M x0 q hX, b) then (1 : ZMod 2) else 0)
      linear_combination h_cancel
    · let rv : RadialVertex pcode M := ⟨sv, h_diag⟩
      let qX : BDLCX1 pcode M := Sum.inl (rv, b)
      refine ⟨singleQubit (Sum.inl qX),
        isCylinderX0Chain_singleQubit_inl pcode M x0 qX hsv_x0, ?_⟩
      rw [syndrome_singleQubit_inl_cX1]
      ext mX
      simp only [Pi.add_apply, singleQubit]
      dsimp [qX, rv, bdlDeltaX0]
      rw [if_pos hn, hsv_x0]
      ring
  | succ m ih =>
    intro sv hn hsv_x0
    have hr_nz : sv.val.2.val ≠ 0 := by omega
    have h_nd : ¬ IsDiagZeroVertex pcode M sv := fun h => hr_nz h.1
    let rv : RadialVertex pcode M := ⟨sv, h_nd⟩
    let qX : BDLCX1 pcode M := Sum.inl (rv, b)
    let sv_par : ShellVertex pcode M := radialParentVertex pcode M sv
    have h_par_r : sv_par.val.2.val = m := by
      dsimp [sv_par, radialParentVertex, finPred]
      omega
    have h_par_x0 : sv_par.val.1.val.1 = x0 := hsv_x0
    obtain ⟨u_par, hu_par_supp, hu_par_syn⟩ := ih sv_par h_par_r h_par_x0
    refine ⟨singleQubit (Sum.inl qX) + u_par,
      isCylinderX0Chain_add pcode M x0
        (isCylinderX0Chain_singleQubit_inl pcode M x0 qX hsv_x0) hu_par_supp, ?_⟩
    rw [map_add, syndrome_singleQubit_inl_cX1, hu_par_syn]
    ext mX
    simp only [Pi.add_apply, singleQubit]
    dsimp [qX, rv, bdlDeltaX0]
    rw [if_neg hr_nz]
    change ((if mX = Sum.inr (sv_par, b) then (1 : ZMod 2) else 0) +
        (if mX = Sum.inr (sv, b) then 1 else 0)) +
      ((if mX = Sum.inr (sv_par, b) then 1 else 0) +
        (if mX = Sum.inl (x0, b) then 1 else 0)) =
      (if mX = Sum.inr (sv, b) then 1 else 0) + (if mX = Sum.inl (x0, b) then 1 else 0)
    have h_cancel := zmod2_add_self (if mX = Sum.inr (sv_par, b) then (1 : ZMod 2) else 0)
    linear_combination h_cancel

private lemma exists_layer_apex_shift_to_zero_of_link {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X)
    (xv : BoundaryX0Link pcode M) (hxv : xv.val.1 = x0) (b : Fin 3) :
    ∃ u : BDLStepXQ pcode M → ZMod 2,
      IsCylinderX0Chain pcode M x0 u ∧
      syndrome (bdlCylinderStepX pcode M) u =
        singleQubit (Sum.inl (x0, b)) + singleQubit (Sum.inl (x0, (0 : Fin 3))) := by
  have h_succ : ∀ v : Fin 2,
      ∃ u : BDLStepXQ pcode M → ZMod 2,
        IsCylinderX0Chain pcode M x0 u ∧
        syndrome (bdlCylinderStepX pcode M) u =
          singleQubit (Sum.inl (x0, v.succ)) + singleQubit (Sum.inl (x0, (0 : Fin 3))) := by
    intro v
    let sv_out : ShellVertex pcode M := mkOuterShellVertex pcode M xv
    obtain ⟨u1, hu1_supp, hu1_syn⟩ :=
      exists_shellVertex_shift_to_layer_apex pcode M x0 v.succ sv_out.val.2.val sv_out rfl hxv
    obtain ⟨u0, hu0_supp, hu0_syn⟩ :=
      exists_shellVertex_shift_to_layer_apex pcode M x0 0 sv_out.val.2.val sv_out rfl hxv
    let qX_v : BDLCX1 pcode M := Sum.inr (Sum.inr (xv, v))
    refine ⟨u1 + singleQubit (Sum.inl qX_v) + u0,
      isCylinderX0Chain_add pcode M x0
        (isCylinderX0Chain_add pcode M x0 hu1_supp
          (isCylinderX0Chain_singleQubit_inl pcode M x0 qX_v hxv))
        hu0_supp, ?_⟩
    rw [map_add, map_add, hu1_syn, syndrome_singleQubit_inl_cX1, hu0_syn]
    ext mX
    simp only [Pi.add_apply, singleQubit]
    dsimp [qX_v, bdlDeltaX0]
    change (((if mX = Sum.inr (sv_out, v.succ) then (1 : ZMod 2) else 0) +
          (if mX = Sum.inl (x0, v.succ) then 1 else 0)) +
        ((if mX = Sum.inr (sv_out, 0) then 1 else 0) +
          (if mX = Sum.inr (sv_out, v.succ) then 1 else 0))) +
      ((if mX = Sum.inr (sv_out, 0) then 1 else 0) +
        (if mX = Sum.inl (x0, 0) then 1 else 0)) =
      (if mX = Sum.inl (x0, v.succ) then 1 else 0) + (if mX = Sum.inl (x0, 0) then 1 else 0)
    have h1 := zmod2_add_self (if mX = Sum.inr (sv_out, v.succ) then (1 : ZMod 2) else 0)
    have h0 := zmod2_add_self (if mX = Sum.inr (sv_out, (0 : Fin 3)) then (1 : ZMod 2) else 0)
    linear_combination h1 + h0
  fin_cases b
  · refine ⟨0, isCylinderX0Chain_zero pcode M x0, ?_⟩
    rw [map_zero]
    ext mX
    simp only [Pi.zero_apply, Pi.add_apply]
    exact (zmod2_add_self _).symm
  · exact h_succ 0
  · exact h_succ 1

/-- **Intra-Cylinder Spanning-Tree Zero-Spillover Shift (`primal_cylinder_fiber_zero_spillover_shift`,
    Part II, Proposition 4.3(i) (`prop:rca-hierarchy`) and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`))**:
    On `bdlCylinderStepX pcode M`, for any coarse check `x0 : M_X` and any fine check
    `mX : BDLStepXMX pcode M` in cylinder `x0` (`stepXMXOwnerX pcode M mX = x0`) that is active in a
    realizable syndrome `S = syndrome (bdlCylinderStepX pcode M) e`, there exists a cylinder 1-chain
    `u : BDLStepXQ pcode M → ZMod 2` supported on `BDLCX1` inside cylinder `x0` such that
    `syndrome (bdlCylinderStepX pcode M) u = singleQubit mX + singleQubit (Sum.inl (x0, 0))`
    (shifting the active fine check `mX` along the radial/vertical spanning tree of cylinder $Y_{x_0}^{(3)}$
    to the cylinder apex `(x0, 0)` with zero spillover outside cylinder `x0`). -/
theorem primal_cylinder_fiber_zero_spillover_shift {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (_h_conn : HasConnectedXLinks pcode)
    (e : BDLStepXQ pcode M → ZMod 2) (x0 : M_X) (mX : BDLStepXMX pcode M)
    (hmX_own : stepXMXOwnerX pcode M mX = x0)
    (hmX_act : syndrome (bdlCylinderStepX pcode M) e mX ≠ 0) :
    ∃ u : BDLStepXQ pcode M → ZMod 2,
      (∀ q : BDLStepXQ pcode M, u q ≠ 0 → ∃ qX : BDLCX1 pcode M, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x0) ∧
      syndrome (bdlCylinderStepX pcode M) u =
        singleQubit mX + singleQubit (Sum.inl (x0, (0 : Fin 3))) := by
  rcases mX with ⟨x, b⟩ | ⟨sv, b⟩
  · dsimp [stepXMXOwnerX] at hmX_own
    subst hmX_own
    obtain ⟨q, _, hq_ne⟩ : ∃ q ∈ (Finset.univ : Finset (BDLStepXQ pcode M)),
        bdlStepXCheckX pcode M (Sum.inl (x, b)) q * e q ≠ 0 := by
      by_contra h_all
      push_neg at h_all
      exact hmX_act (Finset.sum_eq_zero h_all)
    have h_chk : bdlStepXCheckX pcode M (Sum.inl (x, b)) q ≠ 0 :=
      left_ne_zero_of_mul hq_ne
    have h_xv : ∃ xv : BoundaryX0Link pcode M, xv.val.1 = x := by
      rcases q with ⟨⟨rv, b'⟩ | ⟨_ | _⟩⟩ | _
      · dsimp [bdlStepXCheckX, bdlDeltaX0] at h_chk
        by_cases hr0 : rv.val.val.2.val = 0
        · rw [if_pos hr0] at h_chk
          by_cases h_eq : (Sum.inl (x, b) : BDLStepXMX pcode M) = Sum.inl (rv.val.val.1.val.1, b')
          · injection h_eq with h_pair
            injection h_pair with hx_eq _
            exact ⟨rv.val.val.1, hx_eq.symm⟩
          · rw [if_neg h_eq] at h_chk
            exact False.elim (h_chk rfl)
        · rw [if_neg hr0] at h_chk
          exact False.elim (h_chk rfl)
      · exact False.elim (h_chk rfl)
      · exact False.elim (h_chk rfl)
      · exact False.elim (h_chk rfl)
    obtain ⟨xv, hxv⟩ := h_xv
    exact exists_layer_apex_shift_to_zero_of_link pcode M x xv hxv b
  · dsimp [stepXMXOwnerX] at hmX_own
    obtain ⟨u_rad, hu_rad_supp, hu_rad_syn⟩ :=
      exists_shellVertex_shift_to_layer_apex pcode M x0 b sv.val.2.val sv rfl hmX_own
    obtain ⟨u_vert, hu_vert_supp, hu_vert_syn⟩ :=
      exists_layer_apex_shift_to_zero_of_link pcode M x0 sv.val.1 hmX_own b
    refine ⟨u_rad + u_vert,
      isCylinderX0Chain_add pcode M x0 hu_rad_supp hu_vert_supp, ?_⟩
    rw [map_add, hu_rad_syn, hu_vert_syn]
    ext mX'
    simp only [Pi.add_apply]
    have h_cancel := zmod2_add_self (singleQubit (Sum.inl (x0, b)) mX')
    linear_combination h_cancel

/-- **Primal Cylinder Lifted Zero-Spillover Recovery (`primal_cylinder_lifted_zero_spillover_recovery`,
    Part II, Proposition 4.3(i) (`prop:rca-hierarchy`) and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`))**:
    Given any coarse zero-spillover chain `e0 : Q → ZMod 2` (`syndrome pcode e0 = c0`) and any choice
    `mX_of : M_X → BDLStepXMX pcode M` of one active fine check `mX_of x0 ∈ supp(S)` in cylinder `x0`
    for each `x0 ∈ supp(c0)` (`stepXMXOwnerX pcode M (mX_of x0) = x0` and `S (mX_of x0) ≠ 0`),
    combining the intra-cylinder shifts `u_{x0}` of `primal_cylinder_fiber_zero_spillover_shift`
    with `liftCylinderLZ pcode M e0` via `syndrome_add_liftCylinderLZ_eq` produces a fine 1-chain
    `e1 : BDLStepXQ pcode M → ZMod 2` with exact syndrome
    `c1 = ∑ x0 ∈ Finset.univ.filter (fun x0 => c0 x0 ≠ 0), singleQubit (mX_of x0)`
    supported inside `supp(S)` (`∀ mX, c1 mX ≠ 0 → S mX ≠ 0`). -/
theorem primal_cylinder_lifted_zero_spillover_recovery {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h_conn : HasConnectedXLinks pcode)
    (e : BDLStepXQ pcode M → ZMod 2)
    (c0 : M_X → ZMod 2) (e0 : Q → ZMod 2) (he0 : syndrome pcode e0 = c0)
    (mX_of : M_X → BDLStepXMX pcode M)
    (hmX_own : ∀ x0 : M_X, c0 x0 ≠ 0 → stepXMXOwnerX pcode M (mX_of x0) = x0)
    (hmX_act : ∀ x0 : M_X, c0 x0 ≠ 0 → syndrome (bdlCylinderStepX pcode M) e (mX_of x0) ≠ 0) :
    let S := syndrome (bdlCylinderStepX pcode M) e
    let supp_c0 := Finset.univ.filter (fun x0 : M_X => c0 x0 ≠ 0)
    let c1 : BDLStepXMX pcode M → ZMod 2 := ∑ x0 ∈ supp_c0, singleQubit (mX_of x0)
    (∃ e1 : BDLStepXQ pcode M → ZMod 2, syndrome (bdlCylinderStepX pcode M) e1 = c1) ∧
    (∀ mX : BDLStepXMX pcode M, c1 mX ≠ 0 → S mX ≠ 0) := by
  intro S supp_c0 c1
  have h_shift : ∀ x0 : M_X, ∃ u : BDLStepXQ pcode M → ZMod 2,
      c0 x0 ≠ 0 →
        syndrome (bdlCylinderStepX pcode M) u =
          singleQubit (mX_of x0) + singleQubit (Sum.inl (x0, (0 : Fin 3))) := by
    intro x0
    by_cases hx0 : c0 x0 ≠ 0
    · obtain ⟨u, _, hu_syn⟩ :=
        primal_cylinder_fiber_zero_spillover_shift pcode M h_conn e x0 (mX_of x0)
          (hmX_own x0 hx0) (hmX_act x0 hx0)
      exact ⟨u, fun _ => hu_syn⟩
    · exact ⟨0, fun h_abs => False.elim (hx0 h_abs)⟩
  choose u_of hu_of using h_shift
  let e_clean : BDLStepXQ pcode M → ZMod 2 := ∑ x0 ∈ supp_c0, u_of x0
  have h_embed_eq : embedCoarseStepXMX pcode M c0 =
      ∑ x0 ∈ supp_c0, singleQubit (Sum.inl (x0, (0 : Fin 3))) := by
    ext mX
    rw [Finset.sum_apply]
    rcases mX with ⟨x0, b⟩ | mXR
    · rcases b with ⟨_ | _ | _ | _, hb⟩
      · change c0 x0 = ∑ x' ∈ supp_c0, singleQubit (Sum.inl (x', (0 : Fin 3))) (Sum.inl (x0, (0 : Fin 3)))
        by_cases hx0 : c0 x0 ≠ 0
        · rw [Finset.sum_eq_single x0]
          · dsimp [singleQubit]
            rw [if_pos rfl]
            have hc0_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
            exact hc0_one (c0 x0) hx0
          · intro x' _ hx'
            dsimp [singleQubit]
            rw [if_neg (by intro h_eq; injection h_eq with h_eq; injection h_eq with h1 _; exact hx' h1.symm)]
          · intro h_abs
            exact False.elim (h_abs (Finset.mem_filter.mpr ⟨Finset.mem_univ x0, hx0⟩))
        · push_neg at hx0
          rw [hx0, Finset.sum_eq_zero]
          intro x' hx'
          have hx'_ne : x' ≠ x0 := by
            intro h_eq; subst h_eq
            exact (Finset.mem_filter.mp hx').2 hx0
          dsimp [singleQubit]
          rw [if_neg (by intro h_eq; injection h_eq with h_eq; injection h_eq with h1 _; exact hx'_ne h1.symm)]
      · change (0 : ZMod 2) = ∑ x' ∈ supp_c0, singleQubit (Sum.inl (x', (0 : Fin 3))) (Sum.inl (x0, (1 : Fin 3)))
        symm
        apply Finset.sum_eq_zero
        intro x' _
        dsimp [singleQubit]
        rw [if_neg (by intro h_eq; nomatch h_eq)]
      · change (0 : ZMod 2) = ∑ x' ∈ supp_c0, singleQubit (Sum.inl (x', (0 : Fin 3))) (Sum.inl (x0, (2 : Fin 3)))
        symm
        apply Finset.sum_eq_zero
        intro x' _
        dsimp [singleQubit]
        rw [if_neg (by intro h_eq; nomatch h_eq)]
      · omega
    · dsimp [embedCoarseStepXMX]
      symm
      apply Finset.sum_eq_zero
      intro x' _
      dsimp [singleQubit]
  have h_clean : c1 + syndrome (bdlCylinderStepX pcode M) e_clean = embedCoarseStepXMX pcode M c0 := by
    dsimp [c1, e_clean]
    rw [map_sum, h_embed_eq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x0 hx0
    have hx0_ne : c0 x0 ≠ 0 := (Finset.mem_filter.mp hx0).2
    rw [hu_of x0 hx0_ne]
    ext mX
    simp only [Pi.add_apply]
    have h2 := zmod2_add_self (singleQubit (mX_of x0) mX)
    linear_combination h2
  refine ⟨⟨e_clean + liftCylinderLZ pcode M e0,
    syndrome_add_liftCylinderLZ_eq pcode M c1 e_clean c0 e0 h_clean he0⟩, ?_⟩
  intro mX hmX_ne
  dsimp [c1] at hmX_ne
  rw [Finset.sum_apply] at hmX_ne
  obtain ⟨x0, hx0_mem, hx0_sq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmX_ne
  have hx0_ne : c0 x0 ≠ 0 := (Finset.mem_filter.mp hx0_mem).2
  dsimp [singleQubit] at hx0_sq
  by_cases h_eq : mX = mX_of x0
  · subst h_eq
    exact hmX_act x0 hx0_ne
  · rw [if_neg h_eq] at hx0_sq
    exact False.elim (hx0_sq rfl)

private lemma restrictCX2_restrictStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X)) (S : BDLStepXMZ pcode M → ZMod 2) (x : M_X) :
    restrictCX2 pcode M x (restrictStepXMZ pcode M K S) =
      if inVX x ∈ K then restrictCX2 pcode M x S else 0 := by
  by_cases hx : inVX x ∈ K
  · rw [if_pos hx]
    ext mZ
    dsimp only [restrictCX2, restrictStepXMZ]
    by_cases hmZ : stepXMZOwnerTanner pcode M mZ ∈ ({inVX x} : Finset (TannerVertex Q M_Z M_X))
    · have h_eq : stepXMZOwnerTanner pcode M mZ = inVX x := Finset.mem_singleton.mp hmZ
      rw [if_pos hmZ, if_pos hmZ, h_eq, if_pos hx]
    · rw [if_neg hmZ, if_neg hmZ]
  · rw [if_neg hx]
    ext mZ
    dsimp only [restrictCX2, restrictStepXMZ, Pi.zero_apply]
    by_cases hmZ : stepXMZOwnerTanner pcode M mZ ∈ ({inVX x} : Finset (TannerVertex Q M_Z M_X))
    · have h_eq : stepXMZOwnerTanner pcode M mZ = inVX x := Finset.mem_singleton.mp hmZ
      rw [if_pos hmZ, h_eq, if_neg hx]
    · rw [if_neg hmZ]

private lemma cleanCylinderX_restrictStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X)) (S : BDLStepXMZ pcode M → ZMod 2) (x : M_X) :
    cleanCylinderX pcode M (restrictStepXMZ pcode M K S) x =
      if inVX x ∈ K then cleanCylinderX pcode M S x else 0 := by
  by_cases hx : inVX x ∈ K
  · rw [if_pos hx]
    apply cleanCylinderX_congr
    rw [restrictCX2_restrictStepXMZ, if_pos hx]
  · rw [if_neg hx]
    apply cleanCylinderX_eq_zero_of_restrictCX2_eq_zero
    rw [restrictCX2_restrictStepXMZ, if_neg hx]

private lemma restrictCQ2_restrictStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X)) (S : BDLStepXMZ pcode M → ZMod 2) (q0 : Q) :
    restrictCQ2 pcode M q0 (restrictStepXMZ pcode M K S) =
      if inVQ q0 ∈ K then restrictCQ2 pcode M q0 S else 0 := by
  by_cases hq : inVQ q0 ∈ K
  · rw [if_pos hq]
    ext mZ
    dsimp only [restrictCQ2, restrictStepXMZ]
    by_cases hmZ : stepXMZOwnerTanner pcode M mZ ∈ ({inVQ q0} : Finset (TannerVertex Q M_Z M_X))
    · have h_eq : stepXMZOwnerTanner pcode M mZ = inVQ q0 := Finset.mem_singleton.mp hmZ
      rw [if_pos hmZ, if_pos hmZ, h_eq, if_pos hq]
    · rw [if_neg hmZ, if_neg hmZ]
  · rw [if_neg hq]
    ext mZ
    dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply]
    by_cases hmZ : stepXMZOwnerTanner pcode M mZ ∈ ({inVQ q0} : Finset (TannerVertex Q M_Z M_X))
    · have h_eq : stepXMZOwnerTanner pcode M mZ = inVQ q0 := Finset.mem_singleton.mp hmZ
      rw [if_pos hmZ, h_eq, if_neg hq]
    · rw [if_neg hmZ]

private lemma restrictCQ2_stage1_restrictStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X)) (S : BDLStepXMZ pcode M → ZMod 2)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
      inVX x ∈ K)
    (hK_X_to_Q : ∀ x : M_X, ∀ q0 : Q,
      inVX x ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
      inVQ q0 ∈ K)
    (q0 : Q) :
    let D_1 := dualCode (bdlCylinderStepX pcode M)
    let S_K := restrictStepXMZ pcode M K S
    restrictCQ2 pcode M q0 (S_K + syndrome D_1 (cleanStage1X pcode M S_K)) =
      if inVQ q0 ∈ K then
        restrictCQ2 pcode M q0 (S + syndrome D_1 (cleanStage1X pcode M S))
      else 0 := by
  intro D_1 S_K
  have h_term : ∀ x : M_X,
      restrictCQ2 pcode M q0 (syndrome D_1 (cleanCylinderX pcode M S_K x)) =
        if inVQ q0 ∈ K then
          restrictCQ2 pcode M q0 (syndrome D_1 (cleanCylinderX pcode M S x))
        else 0 := by
    intro x
    dsimp only [S_K]
    rw [cleanCylinderX_restrictStepXMZ]
    by_cases hq : inVQ q0 ∈ K
    · rw [if_pos hq]
      by_cases hx : inVX x ∈ K
      · rw [if_pos hx]
      · rw [if_neg hx, map_zero]
        have h0 : restrictCQ2 pcode M q0 0 = 0 := by
          ext mZ; dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply]; exact ite_self _
        rw [h0]
        symm
        by_contra h_nz
        have h_chk : pcode.checkX x q0 ≠ 0 := by
          intro h_chk0
          exact h_nz (restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero pcode M x q0 h_chk0
            (cleanCylinderX pcode M S x) (cleanCylinderX_support pcode M S x))
        exact hx (hK_Q_to_X q0 x hq h_chk h_nz)
    · rw [if_neg hq]
      by_cases hx : inVX x ∈ K
      · rw [if_pos hx]
        by_contra h_nz
        have h_chk : pcode.checkX x q0 ≠ 0 := by
          intro h_chk0
          exact h_nz (restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero pcode M x q0 h_chk0
            (cleanCylinderX pcode M S x) (cleanCylinderX_support pcode M S x))
        exact hq (hK_X_to_Q x q0 hx h_chk h_nz)
      · rw [if_neg hx, map_zero]
        ext mZ; dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply]; exact ite_self _
  have h_sum : restrictCQ2 pcode M q0 (syndrome D_1 (cleanStage1X pcode M S_K)) =
      if inVQ q0 ∈ K then
        restrictCQ2 pcode M q0 (syndrome D_1 (cleanStage1X pcode M S))
      else 0 := by
    by_cases hq : inVQ q0 ∈ K
    · rw [if_pos hq]
      dsimp only [cleanStage1X]
      rw [map_sum (syndrome D_1), map_sum (syndrome D_1)]
      ext mZ
      dsimp only [restrictCQ2, restrictStepXMZ]
      split_ifs with hmZ
      · rw [Finset.sum_apply, Finset.sum_apply]
        apply Finset.sum_congr rfl; intro x _
        have ht := congr_fun (h_term x) mZ
        rw [if_pos hq] at ht
        dsimp only [restrictCQ2, restrictStepXMZ] at ht
        rw [if_pos hmZ, if_pos hmZ] at ht
        exact ht
      · rfl
    · rw [if_neg hq]
      dsimp only [cleanStage1X]
      rw [map_sum (syndrome D_1)]
      ext mZ
      dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply]
      split_ifs with hmZ
      · rw [Finset.sum_apply]
        apply Finset.sum_eq_zero; intro x _
        have ht := congr_fun (h_term x) mZ
        rw [if_neg hq] at ht
        dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply] at ht
        rw [if_pos hmZ] at ht
        exact ht
      · rfl
  rw [restrictCQ2_add, h_sum]
  dsimp only [S_K]
  rw [restrictCQ2_restrictStepXMZ]
  by_cases hq : inVQ q0 ∈ K
  · rw [if_pos hq, if_pos hq, if_pos hq, restrictCQ2_add]
  · rw [if_neg hq, if_neg hq, if_neg hq, add_zero]

private lemma cleanStarQ_stage1_restrictStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X)) (S : BDLStepXMZ pcode M → ZMod 2)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
      inVX x ∈ K)
    (hK_X_to_Q : ∀ x : M_X, ∀ q0 : Q,
      inVX x ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
      inVQ q0 ∈ K)
    (q0 : Q) :
    let D_1 := dualCode (bdlCylinderStepX pcode M)
    let S_K := restrictStepXMZ pcode M K S
    cleanStarQ pcode M (S_K + syndrome D_1 (cleanStage1X pcode M S_K)) q0 =
      if inVQ q0 ∈ K then
        cleanStarQ pcode M (S + syndrome D_1 (cleanStage1X pcode M S)) q0
      else 0 := by
  intro D_1 S_K
  have h_r := restrictCQ2_stage1_restrictStepXMZ pcode M K S hK_Q_to_X hK_X_to_Q q0
  by_cases hq : inVQ q0 ∈ K
  · rw [if_pos hq]
    apply cleanStarQ_congr
    dsimp only [D_1, S_K] at h_r ⊢
    rw [h_r, if_pos hq]
  · rw [if_neg hq]
    apply cleanStarQ_eq_zero_of_restrictCQ2_eq_zero
    dsimp only [D_1, S_K] at h_r ⊢
    rw [h_r, if_neg hq]

/-- **Dual Cleaner Isolated-Component Coboundary Identity (`dual_cleaner_isolated_component_coboundary_eq`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Lemma 4.4 (`lem:two-stage-cleaner-contraction`), and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`))**:
    On `D_1 = dualCode (bdlCylinderStepX pcode M)`, for any realizable fine syndrome `S = syndrome D_1 h`
    and any Tanner vertex component `K : Finset (TannerVertex Q M_Z M_X)` that is closed under
    backward and forward Stage-1/Stage-2 cleaner exports (so `K` is cleaner-isolated from
    `supp(S) \setminus K` in the two-hop block-pool overlap graph), the restricted component syndrome
    `S_K := restrictStepXMZ pcode M K S` satisfies:
    (i) `S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K) = embedCoarseStepXMZ pcode M (rxCleanedCoarseSyndrome pcode M S_K)`
        ($\mathbf{1}_{C_i} \in \ker(\partial_{\mathrm{meta},\mathrm{loc}}^{(i)})$ cleans to its 3-layer
        symmetric coarse projection with zero cylinder or star residue),
    (ii) `27 * (Finset.univ.filter (fun z0 : M_Z => rxCleanedCoarseSyndrome pcode M S_K z0 ≠ 0)).card ≤ 16 * syndromeWeightNat S_K`
         (the component-wise $\frac{16}{27}$ cleaner contraction of Part II, Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`), Equation (73) (`eq:two-step-16-27`)), and
    (iii) for any coarse zero-spillover recovery chain `e0 : Q → ZMod 2` with
          `syndrome (dualCode pcode) e0 = rxCleanedCoarseSyndrome pcode M S_K`,
          `syndrome D_1 (cleanTwoStageRX pcode M S_K + liftCylinderLX pcode M e0) = S_K`. -/
lemma cleanTwoStageRX_restrictStepXMZ_cz2_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K : Finset (TannerVertex Q M_Z M_X))
    (h : BDLStepXQ pcode M → ZMod 2)
    (hK_Z_to_Q : ∀ z0 : M_Z, ∀ q0 : Q,
      inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
        (z0, b) ≠ 0) →
      inVQ q0 ∈ K)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x)) ≠ 0 →
      inVX x ∈ K)
    (hK_X_to_Q : ∀ x : M_X, ∀ q0 : Q,
      inVX x ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x)) ≠ 0 →
      inVQ q0 ∈ K)
    (hK_Q_to_Z : ∀ q0 : Q, ∀ z0 : M_Z,
      inVQ q0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
        (z0, b) ≠ 0) →
      inVZ z0 ∈ K)
    (z0 : M_Z) (b : Fin 3) :
    let D_1 := dualCode (bdlCylinderStepX pcode M)
    let S := syndrome D_1 h
    let S_K := restrictStepXMZ pcode M K S
    (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K)) (Sum.inr (Sum.inr (z0, b))) =
      if inVZ z0 ∈ K then rxCleanedCoarseSyndrome pcode M S z0 else 0 := by
  intro D_1 S S_K
  let S1 := S + syndrome D_1 (cleanStage1X pcode M S)
  let S1_K := S_K + syndrome D_1 (cleanStage1X pcode M S_K)
  have h_exp_K : (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K)) (Sum.inr (Sum.inr (z0, b))) =
      S_K (Sum.inr (Sum.inr (z0, b))) +
        ∑ q0 : Q, exportQZ pcode M (cleanStarQ pcode M S1_K q0) (z0, b) := by
    change S_K (Sum.inr (Sum.inr (z0, b))) +
      syndrome D_1 (cleanStage1X pcode M S_K + cleanStage2Q pcode M S1_K) (Sum.inr (Sum.inr (z0, b))) = _
    rw [map_add, Pi.add_apply, syndrome_cleanStage1X_cz2_eq_zero, zero_add]
    congr 1
    dsimp [cleanStage2Q]
    rw [map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl; intro q0 _
    unfold exportQZ
    rw [splitStepXQ_Q_cleanStarQ]
  have h_exp_all : (S + syndrome D_1 (cleanTwoStageRX pcode M S)) (Sum.inr (Sum.inr (z0, b))) =
      S (Sum.inr (Sum.inr (z0, b))) +
        ∑ q0 : Q, exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) := by
    change S (Sum.inr (Sum.inr (z0, b))) +
      syndrome D_1 (cleanStage1X pcode M S + cleanStage2Q pcode M S1) (Sum.inr (Sum.inr (z0, b))) = _
    rw [map_add, Pi.add_apply, syndrome_cleanStage1X_cz2_eq_zero, zero_add]
    congr 1
    dsimp [cleanStage2Q]
    rw [map_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl; intro q0 _
    unfold exportQZ
    rw [splitStepXQ_Q_cleanStarQ]
  rw [h_exp_K]
  by_cases hz : inVZ z0 ∈ K
  · rw [if_pos hz]
    have h_sk : S_K (Sum.inr (Sum.inr (z0, b))) = S (Sum.inr (Sum.inr (z0, b))) := by
      have hz' : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inr (z0, b))) ∈ K := hz
      dsimp [S_K, restrictStepXMZ]
      rw [if_pos hz']
    have h_sum_eq : (∑ q0 : Q, exportQZ pcode M (cleanStarQ pcode M S1_K q0) (z0, b)) =
        ∑ q0 : Q, exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) := by
      apply Finset.sum_congr rfl; intro q0 _
      have h_star_q0 := cleanStarQ_stage1_restrictStepXMZ pcode M K S hK_Q_to_X hK_X_to_Q q0
      dsimp [D_1, S_K, S1, S1_K] at h_star_q0 ⊢
      rw [h_star_q0]
      by_cases hq : inVQ q0 ∈ K
      · rw [if_pos hq]
      · rw [if_neg hq]
        have h_exp0 : exportQZ pcode M 0 (z0, b) = 0 := by
          rw [exportQZ_apply]; exact Finset.sum_eq_zero (fun _ _ => mul_zero _)
        rw [h_exp0]
        symm
        by_contra h_nz
        have h_chk : pcode.checkZ z0 q0 ≠ 0 :=
          checkZ_ne_zero_of_exportQZ_cleanStarQ_ne_zero pcode M S1 q0 z0 b h_nz
        exact hq (hK_Z_to_Q z0 q0 hz h_chk ⟨b, h_nz⟩)
    rw [h_sk, h_sum_eq, ← h_exp_all]
    have h_s2 := congr_fun (rxCleanedCoarseProj_syndrome_eq pcode M hov hq_z h_conn h).2
      (Sum.inr (Sum.inr (z0, b)))
    dsimp [embedCoarseStepXMZ] at h_s2
    exact h_s2
  · rw [if_neg hz]
    have h_sk : S_K (Sum.inr (Sum.inr (z0, b))) = 0 := by
      have hz' : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inr (z0, b))) ∉ K := hz
      dsimp [S_K, restrictStepXMZ]
      rw [if_neg hz']
    rw [h_sk, zero_add]
    apply Finset.sum_eq_zero; intro q0 _
    have h_star_q0 := cleanStarQ_stage1_restrictStepXMZ pcode M K S hK_Q_to_X hK_X_to_Q q0
    dsimp [D_1, S_K, S1, S1_K] at h_star_q0 ⊢
    rw [h_star_q0]
    by_cases hq : inVQ q0 ∈ K
    · rw [if_pos hq]
      by_contra h_nz
      have h_chk : pcode.checkZ z0 q0 ≠ 0 :=
        checkZ_ne_zero_of_exportQZ_cleanStarQ_ne_zero pcode M S1 q0 z0 b h_nz
      exact hz (hK_Q_to_Z q0 z0 hq h_chk ⟨b, h_nz⟩)
    · rw [if_neg hq, exportQZ_apply]
      exact Finset.sum_eq_zero (fun _ _ => mul_zero _)

theorem dual_cleaner_isolated_component_coboundary_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K : Finset (TannerVertex Q M_Z M_X))
    (h : BDLStepXQ pcode M → ZMod 2)
    (hK_Z_to_Q : ∀ z0 : M_Z, ∀ q0 : Q,
      inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
        (z0, b) ≠ 0) →
      inVQ q0 ∈ K)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x)) ≠ 0 →
      inVX x ∈ K)
    (hK_X_to_Q : ∀ x : M_X, ∀ q0 : Q,
      inVX x ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x)) ≠ 0 →
      inVQ q0 ∈ K)
    (hK_Q_to_Z : ∀ q0 : Q, ∀ z0 : M_Z,
      inVQ q0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
        (z0, b) ≠ 0) →
      inVZ z0 ∈ K)
    (_hK_compl_X_to_Q : ∀ x : M_X, ∀ q0 : Q,
      inVX x ∉ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x)) ≠ 0 →
      inVQ q0 ∉ K)
    (_hK_compl_Q_to_Z : ∀ q0 : Q, ∀ z0 : M_Z,
      inVQ q0 ∉ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
        (z0, b) ≠ 0) →
      inVZ z0 ∉ K) :
    let D_1 := dualCode (bdlCylinderStepX pcode M)
    let S := syndrome D_1 h
    let S_K := restrictStepXMZ pcode M K S
    (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K) =
      embedCoarseStepXMZ pcode M (rxCleanedCoarseSyndrome pcode M S_K)) ∧
    (27 * (Finset.univ.filter (fun z0 : M_Z => rxCleanedCoarseSyndrome pcode M S_K z0 ≠ 0)).card ≤
      16 * syndromeWeightNat S_K) ∧
    (∀ e0 : Q → ZMod 2,
      syndrome (dualCode pcode) e0 = rxCleanedCoarseSyndrome pcode M S_K →
      syndrome D_1 (cleanTwoStageRX pcode M S_K + liftCylinderLX pcode M e0) = S_K) := by
  intro D_1 S S_K
  let S1 := S + syndrome D_1 (cleanStage1X pcode M S)
  let S1_K := S_K + syndrome D_1 (cleanStage1X pcode M S_K)
  have h_s2_cz : ∀ (z0 : M_Z) (b : Fin 3),
      (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K)) (Sum.inr (Sum.inr (z0, b))) =
        if inVZ z0 ∈ K then rxCleanedCoarseSyndrome pcode M S z0 else 0 :=
    cleanTwoStageRX_restrictStepXMZ_cz2_eq pcode M hov hq_z h_conn K h
      hK_Z_to_Q hK_Q_to_X hK_X_to_Q hK_Q_to_Z
  have h_part1 : S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K) =
      embedCoarseStepXMZ pcode M (rxCleanedCoarseSyndrome pcode M S_K) := by
    ext mZ
    rcases mZ with mZX | ⟨mZQ | ⟨z0, b⟩⟩
    · dsimp [embedCoarseStepXMZ]
      let x := cX2OwnerX pcode M mZX
      have h_x : restrictCX2 pcode M x (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K)) = 0 := by
        change restrictCX2 pcode M x (S_K + syndrome D_1 (cleanStage1X pcode M S_K + cleanStage2Q pcode M S1_K)) = 0
        rw [map_add, ← add_assoc, restrictCX2_add,
            restrictCX2_syndrome_eq_zero_of_support_Q pcode M x (cleanStage2Q pcode M S1_K)
              (cleanStage2Q_inl_eq_zero pcode M S1_K),
            add_zero, restrictCX2_add]
        have h_sum_syn : restrictCX2 pcode M x (syndrome D_1 (cleanStage1X pcode M S_K)) =
            restrictCX2 pcode M x (syndrome D_1 (cleanCylinderX pcode M S_K x)) := by
          ext mZ'
          dsimp [cleanStage1X, restrictCX2, restrictStepXMZ]
          split_ifs with hmZ'
          · rw [map_sum, Finset.sum_apply, Finset.sum_eq_single x]
            · intro x' _ hne
              have h_z := congr_fun (restrictCX2_syndrome_eq_zero_of_support_ne pcode M x x' hne
                (cleanCylinderX pcode M S_K x') (cleanCylinderX_support pcode M S_K x')) mZ'
              dsimp [restrictCX2, restrictStepXMZ] at h_z
              rw [if_pos hmZ'] at h_z
              exact h_z
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ x))
          · rfl
        rw [h_sum_syn, restrictCX2_restrictStepXMZ, cleanCylinderX_restrictStepXMZ]
        by_cases hx : inVX x ∈ K
        · rw [if_pos hx, if_pos hx, (cleanCylinderX_spec pcode M hov h_conn h x).1]
          ext mZ'; exact zmod2_add_self _
        · rw [if_neg hx, if_neg hx, map_zero, zero_add]
          ext mZ'; dsimp [restrictCX2, restrictStepXMZ]; exact ite_self _
      have h_at := congr_fun h_x (Sum.inl mZX)
      dsimp [restrictCX2, restrictStepXMZ] at h_at
      have hm : stepXMZOwnerTanner pcode M (Sum.inl mZX) ∈ ({inVX x} : Finset _) :=
        Finset.mem_singleton_self _
      rw [if_pos hm] at h_at
      exact h_at
    · dsimp [embedCoarseStepXMZ]
      let q0 := cQ2OwnerQ pcode M mZQ
      have h_q : restrictCQ2 pcode M q0 (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K)) = 0 := by
        change restrictCQ2 pcode M q0 (S_K + syndrome D_1 (cleanStage1X pcode M S_K + cleanStage2Q pcode M S1_K)) = 0
        rw [map_add, ← add_assoc, restrictCQ2_add]
        have h_sum_syn : restrictCQ2 pcode M q0 (syndrome D_1 (cleanStage2Q pcode M S1_K)) =
            restrictCQ2 pcode M q0 (syndrome D_1 (cleanStarQ pcode M S1_K q0)) := by
          ext mZ'
          dsimp [cleanStage2Q, restrictCQ2, restrictStepXMZ]
          split_ifs with hmZ'
          · rw [map_sum, Finset.sum_apply, Finset.sum_eq_single q0]
            · intro q0' _ hne
              have h_z := congr_fun (restrictCQ2_syndrome_eq_zero_of_support_ne pcode M q0 q0' hne
                (cleanStarQ pcode M S1_K q0') (cleanStarQ_support pcode M S1_K q0')) mZ'
              dsimp [restrictCQ2, restrictStepXMZ] at h_z
              rw [if_pos hmZ'] at h_z
              exact h_z
            · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0))
          · rfl
        have h_r := restrictCQ2_stage1_restrictStepXMZ pcode M K S hK_Q_to_X hK_X_to_Q q0
        have h_s := cleanStarQ_stage1_restrictStepXMZ pcode M K S hK_Q_to_X hK_X_to_Q q0
        dsimp [D_1, S_K, S1, S1_K] at h_r h_s ⊢
        rw [h_sum_syn, h_r, h_s]
        by_cases hq : inVQ q0 ∈ K
        · rw [if_pos hq, if_pos hq]
          have h1_cyl : ∀ x : M_X, restrictCX2 pcode M x (syndrome D_1 (h + cleanStage1X pcode M S)) = 0 :=
            restrictCX2_syndrome_add_cleanStage1X_eq_zero pcode M hov h_conn h
          have h_s1_eq : S + syndrome D_1 (cleanStage1X pcode M S) =
              syndrome D_1 (h + cleanStage1X pcode M S) :=
            (map_add (syndrome D_1) h (cleanStage1X pcode M S)).symm
          rw [h_s1_eq, (cleanStarQ_spec pcode M hov h_conn (h + cleanStage1X pcode M S) h1_cyl q0).1]
          ext mZ'; exact zmod2_add_self _
        · rw [if_neg hq, if_neg hq, map_zero, zero_add]
          ext mZ'; dsimp [restrictCQ2, restrictStepXMZ]; exact ite_self _
      have h_at := congr_fun h_q (Sum.inr (Sum.inl mZQ))
      dsimp [restrictCQ2, restrictStepXMZ] at h_at
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl mZQ)) ∈ ({inVQ q0} : Finset _) :=
        Finset.mem_singleton_self _
      rw [if_pos hm] at h_at
      exact h_at
    · dsimp only [embedCoarseStepXMZ, rxCleanedCoarseSyndrome]
      change (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K)) (Sum.inr (Sum.inr (z0, b))) =
        (S_K + syndrome D_1 (cleanTwoStageRX pcode M S_K)) (Sum.inr (Sum.inr (z0, 0)))
      rw [h_s2_cz z0 b, h_s2_cz z0 0]
  have h_filter_eq :
      Finset.univ.filter (fun z0 : M_Z => rxCleanedCoarseSyndrome pcode M S_K z0 ≠ 0) =
        activeCoarseZInK pcode M K S := by
    ext z0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, activeCoarseZInK]
    have h0 := h_s2_cz z0 0
    change rxCleanedCoarseSyndrome pcode M S_K z0 =
      (if inVZ z0 ∈ K then rxCleanedCoarseSyndrome pcode M S z0 else 0) at h0
    rw [h0]
    by_cases hz : inVZ z0 ∈ K <;> simp [hz]
  refine ⟨h_part1, ?_, ?_⟩
  · rw [h_filter_eq]
    exact rxCleanedCoarseSyndrome_component_contraction pcode M hov hq_z h_conn K S ⟨h, rfl⟩
      hK_Z_to_Q hK_Q_to_X
  · intro e0 he0
    exact syndrome_cleanTwoStageRX_add_liftCylinderLX_eq pcode M S_K
      (rxCleanedCoarseSyndrome pcode M S_K) e0 h_part1 he0

/-- Coarse primal syndrome map (`coarsePrimalSyndrome`,
    Part II, Proposition 4.3(i) (`prop:rca-hierarchy`) and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`)), projecting a fine X-check
    syndrome on `bdlCylinderStepX pcode M` to its coarse cylinder-sum syndrome on `pcode`. -/
abbrev coarsePrimalSyndrome {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMX pcode M → ZMod 2) : M_X → ZMod 2 :=
  coarseSyndromeStepXMX pcode M S

/-- **Primal Cylinder Sub-Syndrome Zero-Spillover Recovery (`primal_cylinder_subsyndrome_zero_spillover_recovery`,
    Part II, Proposition 4.3(i) (`prop:rca-hierarchy`) and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`))**:
    For any fine sub-syndrome `S_K : BDLStepXMX pcode M → ZMod 2` whose active checks belong to the
    support of a realizable syndrome `syndrome (bdlCylinderStepX pcode M) e`, summing the intra-cylinder
    radial/vertical shifts of `primal_cylinder_fiber_zero_spillover_shift` over
    `supp(S_K)` produces a cylinder 1-chain `u_clean : BDLStepXQ pcode M → ZMod 2` such that:
    (i) `S_K + syndrome (bdlCylinderStepX pcode M) u_clean = embedCoarseStepXMX pcode M (coarsePrimalSyndrome pcode M S_K)`, and
    (ii) for any coarse zero-spillover recovery chain `e0 : Q → ZMod 2` with
         `syndrome pcode e0 = coarsePrimalSyndrome pcode M S_K`,
         `syndrome (bdlCylinderStepX pcode M) (u_clean + liftCylinderLZ pcode M e0) = S_K`. -/
theorem primal_cylinder_subsyndrome_zero_spillover_recovery {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h_conn : HasConnectedXLinks pcode)
    (e : BDLStepXQ pcode M → ZMod 2)
    (S_K : BDLStepXMX pcode M → ZMod 2)
    (h_act : ∀ mX : BDLStepXMX pcode M, S_K mX ≠ 0 → syndrome (bdlCylinderStepX pcode M) e mX ≠ 0) :
    ∃ u_clean : BDLStepXQ pcode M → ZMod 2,
      (S_K + syndrome (bdlCylinderStepX pcode M) u_clean =
        embedCoarseStepXMX pcode M (coarsePrimalSyndrome pcode M S_K)) ∧
      (∀ e0 : Q → ZMod 2,
        syndrome pcode e0 = coarsePrimalSyndrome pcode M S_K →
        syndrome (bdlCylinderStepX pcode M) (u_clean + liftCylinderLZ pcode M e0) = S_K) := by
  let supp_SK := Finset.univ.filter (fun mX : BDLStepXMX pcode M => S_K mX ≠ 0)
  let apex0 : M_X → BDLStepXMX pcode M := fun x0 => Sum.inl (x0, (0 : Fin 3))
  have h_shift : ∀ mX : BDLStepXMX pcode M, ∃ u : BDLStepXQ pcode M → ZMod 2,
      S_K mX ≠ 0 →
        syndrome (bdlCylinderStepX pcode M) u =
          singleQubit mX + singleQubit (apex0 (stepXMXOwnerX pcode M mX)) := by
    intro mX
    by_cases hmX : S_K mX ≠ 0
    · obtain ⟨u, _, hu_syn⟩ :=
        primal_cylinder_fiber_zero_spillover_shift pcode M h_conn e
          (stepXMXOwnerX pcode M mX) mX rfl (h_act mX hmX)
      exact ⟨u, fun _ => hu_syn⟩
    · exact ⟨0, fun h_abs => False.elim (hmX h_abs)⟩
  choose u_of hu_of using h_shift
  let u_clean : BDLStepXQ pcode M → ZMod 2 := ∑ mX ∈ supp_SK, u_of mX
  have h_zmod2_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have h_SK_eq : S_K = ∑ mX ∈ supp_SK, singleQubit mX := by
    ext mX
    rw [Finset.sum_apply]
    by_cases hmX : S_K mX ≠ 0
    · rw [Finset.sum_eq_single mX]
      · dsimp [singleQubit]; rw [if_pos rfl, h_zmod2_one (S_K mX) hmX]
      · intro mX' _ hne; dsimp [singleQubit]; rw [if_neg hne.symm]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_filter.mpr ⟨Finset.mem_univ mX, hmX⟩))
    · push_neg at hmX
      rw [hmX]
      symm
      apply Finset.sum_eq_zero; intro mX' hmX'
      have hne : mX ≠ mX' := by
        intro h_eq; subst h_eq; exact (Finset.mem_filter.mp hmX').2 hmX
      dsimp [singleQubit]; rw [if_neg hne]
  have h_embed_eq : embedCoarseStepXMX pcode M (coarsePrimalSyndrome pcode M S_K) =
      ∑ mX ∈ supp_SK, singleQubit (apex0 (stepXMXOwnerX pcode M mX)) := by
    ext mX'
    rw [Finset.sum_apply]
    rcases mX' with ⟨x0, b⟩ | mXR
    · rcases b with ⟨_ | _ | _ | _, hb⟩
      · change coarseSyndromeStepXMX pcode M S_K x0 =
          ∑ mX ∈ supp_SK, singleQubit (apex0 (stepXMXOwnerX pcode M mX)) (apex0 x0)
        dsimp [coarseSyndromeStepXMX]
        have h_lhs : (∑ mX ∈ Finset.univ.filter (fun mX => stepXMXOwnerX pcode M mX = x0), S_K mX) =
            ∑ mX : BDLStepXMX pcode M, if stepXMXOwnerX pcode M mX = x0 then S_K mX else 0 := by
          rw [Finset.sum_filter]
        have h_rhs : (∑ mX ∈ supp_SK,
            singleQubit (apex0 (stepXMXOwnerX pcode M mX)) (apex0 x0)) =
            ∑ mX : BDLStepXMX pcode M,
              if S_K mX ≠ 0 then
                singleQubit (apex0 (stepXMXOwnerX pcode M mX)) (apex0 x0)
              else 0 := by
          rw [Finset.sum_filter]
        rw [h_lhs, h_rhs]
        apply Finset.sum_congr rfl; intro mX _
        by_cases hmX : S_K mX ≠ 0
        · rw [if_pos hmX, h_zmod2_one (S_K mX) hmX]
          dsimp [singleQubit, apex0]
          by_cases h_own : stepXMXOwnerX pcode M mX = x0
          · rw [if_pos h_own, if_pos (by rw [h_own])]
          · rw [if_neg h_own, if_neg (by intro h_eq; injection h_eq with hp; injection hp with h1 _; exact h_own h1.symm)]
        · push_neg at hmX
          rw [if_neg (not_not.mpr hmX), hmX, ite_self]
      · change (0 : ZMod 2) = ∑ mX ∈ supp_SK,
          singleQubit (apex0 (stepXMXOwnerX pcode M mX)) (Sum.inl (x0, (1 : Fin 3)))
        symm; apply Finset.sum_eq_zero; intro mX _
        dsimp [singleQubit, apex0]; rw [if_neg (by intro h_eq; nomatch h_eq)]
      · change (0 : ZMod 2) = ∑ mX ∈ supp_SK,
          singleQubit (apex0 (stepXMXOwnerX pcode M mX)) (Sum.inl (x0, (2 : Fin 3)))
        symm; apply Finset.sum_eq_zero; intro mX _
        dsimp [singleQubit, apex0]; rw [if_neg (by intro h_eq; nomatch h_eq)]
      · omega
    · dsimp [embedCoarseStepXMX]
      symm; apply Finset.sum_eq_zero; intro mX _; dsimp [singleQubit, apex0]
  have h_clean : S_K + syndrome (bdlCylinderStepX pcode M) u_clean =
      embedCoarseStepXMX pcode M (coarsePrimalSyndrome pcode M S_K) := by
    dsimp [u_clean]
    rw [map_sum, h_embed_eq]
    conv_lhs => rw [h_SK_eq]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro mX hmX
    have hmX_ne : S_K mX ≠ 0 := (Finset.mem_filter.mp hmX).2
    rw [hu_of mX hmX_ne]
    ext mX'
    simp only [Pi.add_apply]
    have h2 := zmod2_add_self (singleQubit mX mX')
    linear_combination h2
  refine ⟨u_clean, h_clean, fun e0 he0 =>
    syndrome_add_liftCylinderLZ_eq pcode M S_K u_clean
      (coarsePrimalSyndrome pcode M S_K) e0 h_clean he0⟩

/-- Cleaner-closed Tanner vertex component predicate (`IsCleanerClosedTannerComponent`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(i) (`thm:direct-worldline-intact-cluster-erasure`)):
    a Tanner vertex subset `K : Finset (TannerVertex Q M_Z M_X)` is closed under both backward and
    forward Stage-1 cylinder-to-star and Stage-2 star-to-Z-block cleaner exports for `S`. -/
def IsCleanerClosedTannerComponent {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X)) (S : BDLStepXMZ pcode M → ZMod 2) : Prop :=
  (∀ z0 : M_Z, ∀ q0 : Q,
    inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
    (∃ b : Fin 3, exportQZ pcode M
      (cleanStarQ pcode M (S + syndrome (dualCode (bdlCylinderStepX pcode M))
        (cleanStage1X pcode M S)) q0) (z0, b) ≠ 0) →
    inVQ q0 ∈ K) ∧
  (∀ q0 : Q, ∀ x : M_X,
    inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
    restrictCQ2 pcode M q0
      (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
    inVX x ∈ K) ∧
  (∀ x : M_X, ∀ q0 : Q,
    inVX x ∈ K → pcode.checkX x q0 ≠ 0 →
    restrictCQ2 pcode M q0
      (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
    inVQ q0 ∈ K) ∧
  (∀ q0 : Q, ∀ z0 : M_Z,
    inVQ q0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
    (∃ b : Fin 3, exportQZ pcode M
      (cleanStarQ pcode M (S + syndrome (dualCode (bdlCylinderStepX pcode M))
        (cleanStage1X pcode M S)) q0) (z0, b) ≠ 0) →
    inVZ z0 ∈ K)

/-- Single-step primal cylinder intact cluster relation (`IsPrimalCylinderClusterStep`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)):
    `c1` is a fine sub-syndrome of a realizable syndrome on `bdlCylinderStepX pcode M` whose
    coarse cylinder-sum projection is `coarsePrimalSyndrome pcode M c1 = c0` with
    `syndromeWeightNat c0 ≤ syndromeWeightNat c1`. -/
def IsPrimalCylinderClusterStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (c0 : M_X → ZMod 2) (c1 : BDLStepXMX pcode M → ZMod 2) : Prop :=
  (∃ e : BDLStepXQ pcode M → ZMod 2,
    ∀ mX : BDLStepXMX pcode M, c1 mX ≠ 0 → syndrome (bdlCylinderStepX pcode M) e mX ≠ 0) ∧
  coarsePrimalSyndrome pcode M c1 = c0 ∧
  syndromeWeightNat c0 ≤ syndromeWeightNat c1

/-- Single-step two-hop block-pool adjacency on active fine Z-checks (`TwoHopPoolAdj`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`)): `a, b ∈ supp(c1)` belong to a
    common single-check two-hop block pool `fineTwoHopPool pcode M {z0}`. -/
def TwoHopPoolAdj {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (c1 : BDLStepXMZ pcode M → ZMod 2) (a b : BDLStepXMZ pcode M) : Prop :=
  c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
  ∃ z0 : M_Z, a ∈ fineTwoHopPool pcode M {z0} ∧ b ∈ fineTwoHopPool pcode M {z0}

/-- Two-hop block-pool connectedness (`IsTwoHopPoolConnected`,
    Part II, Definition 3.2(i),(ii) (`def:multiscale-cluster-decoder`) and
    Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`)):
    every pair of active fine checks `u, v ∈ supp(c1)` is connected in `supp(c1)` by a chain of
    active fine checks in which consecutive vertices belong to a common single-check two-hop block
    pool `fineTwoHopPool pcode M {z0}`. -/
def IsTwoHopPoolConnected {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (c1 : BDLStepXMZ pcode M → ZMod 2) : Prop :=
  ∀ u v : BDLStepXMZ pcode M, c1 u ≠ 0 → c1 v ≠ 0 →
    Relation.ReflTransGen (TwoHopPoolAdj pcode M c1) u v

/-- Multiscale step adjacency across a primal cylinder step (`PrimalMultiscaleAdj`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)):
    two active fine checks `a, b ∈ supp(c1)` are linked through scales `≤ i + 1` if they lie in
    the same coarse cylinder or their owner cylinders are active in `c0` and connected via `Conn0`. -/
def PrimalMultiscaleAdj {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_X → M_X → Prop)
    (c0 : M_X → ZMod 2) (c1 : BDLStepXMX pcode M → ZMod 2)
    (a b : BDLStepXMX pcode M) : Prop :=
  c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
  (stepXMXOwnerX pcode M a = stepXMXOwnerX pcode M b ∨
    (c0 (stepXMXOwnerX pcode M a) ≠ 0 ∧
     c0 (stepXMXOwnerX pcode M b) ≠ 0 ∧
     Conn0 (stepXMXOwnerX pcode M a) (stepXMXOwnerX pcode M b)))

/-- Multiscale connectivity relation across a primal cylinder step (`PrimalMultiscaleConn`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
def PrimalMultiscaleConn {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_X → M_X → Prop)
    (c0 : M_X → ZMod 2) (c1 : BDLStepXMX pcode M → ZMod 2) :
    BDLStepXMX pcode M → BDLStepXMX pcode M → Prop :=
  Relation.ReflTransGen (PrimalMultiscaleAdj pcode M Conn0 c0 c1)

/-- Multiscale step adjacency across a dual two-hop pool step (`DualMultiscaleAdj`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)):
    two active fine checks `a, b ∈ supp(c1)` are linked through scales `≤ i + 1` if they are
    horizontally adjacent via `TwoHopPoolAdj` or belong to two-hop pools of active coarse checks
    `z_a, z_b ∈ supp(c0)` connected via `Conn0`. -/
def DualMultiscaleAdj {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_Z → M_Z → Prop)
    (c0 : M_Z → ZMod 2) (c1 : BDLStepXMZ pcode M → ZMod 2)
    (a b : BDLStepXMZ pcode M) : Prop :=
  c1 a ≠ 0 ∧ c1 b ≠ 0 ∧
  (TwoHopPoolAdj pcode M c1 a b ∨
    ∃ z_a z_b : M_Z,
      c0 z_a ≠ 0 ∧ c0 z_b ≠ 0 ∧ Conn0 z_a z_b ∧
      a ∈ fineTwoHopPool pcode M {z_a} ∧ b ∈ fineTwoHopPool pcode M {z_b})

/-- Multiscale connectivity relation across a dual two-hop pool step (`DualMultiscaleConn`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
def DualMultiscaleConn {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_Z → M_Z → Prop)
    (c0 : M_Z → ZMod 2) (c1 : BDLStepXMZ pcode M → ZMod 2) :
    BDLStepXMZ pcode M → BDLStepXMZ pcode M → Prop :=
  Relation.ReflTransGen (DualMultiscaleAdj pcode M Conn0 c0 c1)

/-- Single-step dual cylinder intact cluster relation (`IsDualCylinderClusterStep`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)):
    `c1` is the restriction `restrictStepXMZ pcode M K S` of a realizable syndrome
    `S = syndrome (dualCode (bdlCylinderStepX pcode M)) h` to a cleaner-closed Tanner component `K`
    such that its two-stage cleaned coarse syndrome is `rxCleanedCoarseSyndrome pcode M c1 = c0`
    and it satisfies `27 * |c0| ≤ 16 * |c1|`. -/
def IsDualCylinderClusterStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (c0 : M_Z → ZMod 2) (c1 : BDLStepXMZ pcode M → ZMod 2) : Prop :=
  ∃ (h : BDLStepXQ pcode M → ZMod 2) (K : Finset (TannerVertex Q M_Z M_X)),
    IsCleanerClosedTannerComponent pcode M K (syndrome (dualCode (bdlCylinderStepX pcode M)) h) ∧
    c1 = restrictStepXMZ pcode M K (syndrome (dualCode (bdlCylinderStepX pcode M)) h) ∧
    rxCleanedCoarseSyndrome pcode M c1 = c0 ∧
    27 * syndromeWeightNat c0 ≤ 16 * syndromeWeightNat c1

/-- Recursive multiscale cluster connectivity relation in the primal X-check sector
    (`MultiscaleClusterConnPrimal`, Part II, Definition 4.2 (`def:multiscale-cluster-decoder`)
    and Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)), propagating
    `PrimalMultiscaleConn` across `bdlRandomStepX` and `DualMultiscaleConn` across `bdlRandomStepZ`
    for `k + 1` full RG cycles. -/
def MultiscaleClusterConnPrimal :
    (k : ℕ) → ((bdlIteratedBundled (k + 1)).M_X → ZMod 2) →
    (bdlIteratedBundled (k + 1)).M_X → (bdlIteratedBundled (k + 1)).M_X → Prop
  | 0, c2 =>
      let B := bdlIteratedBundled 0
      let B1 := bdlRandomStepX B
      let c1 : B1.M_X → ZMod 2 :=
        rxCleanedCoarseSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred c2
      let c0 : B.M_X → ZMod 2 :=
        coarsePrimalSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred c1
      let Conn0 : B.M_X → B.M_X → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
      let Conn1 : B1.M_X → B1.M_X → Prop :=
        PrimalMultiscaleConn (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1
      DualMultiscaleConn (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred Conn1 c1 c2
  | k + 1, c2 =>
      let B := bdlIteratedBundled (k + 1)
      let B1 := bdlRandomStepX B
      let c1 : B1.M_X → ZMod 2 :=
        rxCleanedCoarseSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred c2
      let c0 : B.M_X → ZMod 2 :=
        coarsePrimalSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred c1
      let Conn0 : B.M_X → B.M_X → Prop := MultiscaleClusterConnPrimal k c0
      let Conn1 : B1.M_X → B1.M_X → Prop :=
        PrimalMultiscaleConn (bdlPerturbedOfBundled B) bdlSubdivPred Conn0 c0 c1
      DualMultiscaleConn (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred Conn1 c1 c2

/-- Recursive multiscale cluster connectivity relation at odd half-steps in the dual Z-check sector
    (`MultiscaleClusterConnDualHalf`, Part II, Definition 4.2 (`def:multiscale-cluster-decoder`)
    and Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
def MultiscaleClusterConnDualHalf :
    (k : ℕ) → ((bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2) →
    (bdlRandomStepX (bdlIteratedBundled k)).M_Z →
    (bdlRandomStepX (bdlIteratedBundled k)).M_Z → Prop
  | 0, c1 =>
      let B0 := bdlIteratedBundled 0
      let c0 : B0.M_Z → ZMod 2 :=
        rxCleanedCoarseSyndrome (bdlPerturbedOfBundled B0) bdlSubdivPred c1
      let Conn0 : B0.M_Z → B0.M_Z → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
      DualMultiscaleConn (bdlPerturbedOfBundled B0) bdlSubdivPred Conn0 c0 c1
  | k + 1, c_top =>
      let B_prev := bdlIteratedBundled k
      let B_half := bdlRandomStepX B_prev
      let B_mid := bdlIteratedBundled (k + 1)
      let c_mid : B_mid.M_Z → ZMod 2 :=
        rxCleanedCoarseSyndrome (bdlPerturbedOfBundled B_mid) bdlSubdivPred c_top
      let c_prev : B_half.M_Z → ZMod 2 :=
        coarsePrimalSyndrome (bdlPerturbedOfBundled (dualBundled B_half)) bdlSubdivPred c_mid
      let Conn_prev : B_half.M_Z → B_half.M_Z → Prop :=
        MultiscaleClusterConnDualHalf k c_prev
      let Conn_mid : B_mid.M_Z → B_mid.M_Z → Prop :=
        PrimalMultiscaleConn (bdlPerturbedOfBundled (dualBundled B_half)) bdlSubdivPred
          Conn_prev c_prev c_mid
      DualMultiscaleConn (bdlPerturbedOfBundled B_mid) bdlSubdivPred Conn_mid c_mid c_top

/-- Multiscale cluster connectivity relation in the dual Z-check sector
    (`MultiscaleClusterConnDual`, Part II, Definition 4.2 (`def:multiscale-cluster-decoder`) and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`)), propagating
    `MultiscaleClusterConnDualHalf k c1` across the top primal cylinder step
    $B_{2k+1} \to B_{2k+2}$. -/
def MultiscaleClusterConnDual (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2) :
    (bdlIteratedBundled (k + 1)).M_Z → (bdlIteratedBundled (k + 1)).M_Z → Prop :=
  let B := bdlIteratedBundled k
  let B1 := bdlRandomStepX B
  let c1 : B1.M_Z → ZMod 2 :=
    coarsePrimalSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred c2
  let Conn1 : B1.M_Z → B1.M_Z → Prop := MultiscaleClusterConnDualHalf k c1
  PrimalMultiscaleConn (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred Conn1 c1 c2

/-- Recursive multiscale intact percolating cluster predicate in the primal X-check sector
    (`IsMultiscaleIntactPercolatingClusterPrimal`, Part II, Lemma 4.1 (`lem:seed-code`),
    Definition 4.2 (`def:multiscale-cluster-decoder`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)), tracing a
    physical cluster `c` on `bdlIteratedBundled (k + 1)` across `k + 1` full RG cycles
    `(bdlRandomStepZ ∘ bdlRandomStepX)` down to the $[\![5,1,2]\!]$ planar surface seed code
    `bdlSurfaceSeedBundled = bdlIteratedBundled 0` (where every seed syndrome is realizable by
    `syndrome_bdlSurfaceSeedCode_surjective`). -/
def IsMultiscaleIntactPercolatingClusterPrimal :
    (k : ℕ) → ((bdlIteratedBundled (k + 1)).M_X → ZMod 2) → Prop
  | 0, c2 =>
      let B := bdlIteratedBundled 0
      let B1 := bdlRandomStepX B
      c2 ≠ 0 ∧
      ∃ (c0 : B.M_X → ZMod 2) (c1 : B1.M_X → ZMod 2),
        (∃ e0 : B.Q → ZMod 2, syndrome B.code e0 = c0) ∧
        IsPrimalCylinderClusterStep (bdlPerturbedOfBundled B) bdlSubdivPred c0 c1 ∧
        IsDualCylinderClusterStep (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred c1 c2
  | k + 1, c2 =>
      let B := bdlIteratedBundled (k + 1)
      let B1 := bdlRandomStepX B
      ∃ (c0 : B.M_X → ZMod 2) (c1 : B1.M_X → ZMod 2),
        IsMultiscaleIntactPercolatingClusterPrimal k c0 ∧
        IsPrimalCylinderClusterStep (bdlPerturbedOfBundled B) bdlSubdivPred c0 c1 ∧
        IsDualCylinderClusterStep (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred c1 c2

/-- Recursive multiscale intact percolating cluster predicate at odd half-steps in the dual Z-check
    sector (`IsMultiscaleIntactPercolatingClusterDualHalf`, Part II, Lemma 4.1 (`lem:seed-code`),
    Definition 4.2 (`def:multiscale-cluster-decoder`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)), tracing a cluster `c1`
    on `bdlRandomStepX (bdlIteratedBundled k)` ($B_{2k+1}$) down to
    `bdlSurfaceSeedBundled = bdlIteratedBundled 0` so that every interior primal step
    $B_{2j+1} \to B_{2j+2}$ sits directly beneath the dual step $B_{2j+2} \to B_{2j+3}$. -/
def IsMultiscaleIntactPercolatingClusterDualHalf :
    (k : ℕ) → ((bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2) → Prop
  | 0, c1 =>
      let B0 := bdlIteratedBundled 0
      ∃ (c0 : B0.M_Z → ZMod 2),
        (∃ h0 : B0.Q → ZMod 2, syndrome (dualCode B0.code) h0 = c0) ∧
        IsDualCylinderClusterStep (bdlPerturbedOfBundled B0) bdlSubdivPred c0 c1
  | k + 1, c_top =>
      let B_prev := bdlIteratedBundled k
      let B_half := bdlRandomStepX B_prev
      let B_mid := bdlIteratedBundled (k + 1)
      c_top ≠ 0 ∧
      ∃ (c_prev : B_half.M_Z → ZMod 2) (c_mid : B_mid.M_Z → ZMod 2),
        c_prev ≠ 0 ∧
        IsMultiscaleIntactPercolatingClusterDualHalf k c_prev ∧
        IsPrimalCylinderClusterStep (bdlPerturbedOfBundled (dualBundled B_half))
          bdlSubdivPred c_prev c_mid ∧
        IsDualCylinderClusterStep (bdlPerturbedOfBundled B_mid)
          bdlSubdivPred c_mid c_top

/-- Multiscale intact percolating cluster predicate in the dual Z-check sector
    (`IsMultiscaleIntactPercolatingClusterDual`, Part II, Lemma 4.1 (`lem:seed-code`),
    Definition 4.2 (`def:multiscale-cluster-decoder`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)), combining
    `IsMultiscaleIntactPercolatingClusterDualHalf k c1` at $B_{2k+1}$ with the top primal cylinder
    step $B_{2k+1} \to B_{2k+2}$ and multiscale graph connectedness `MultiscaleClusterConnDual k c2`. -/
def IsMultiscaleIntactPercolatingClusterDual (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2) : Prop :=
  let B := bdlIteratedBundled k
  let B1 := bdlRandomStepX B
  c2 ≠ 0 ∧
  ∃ (c1 : B1.M_Z → ZMod 2),
    IsMultiscaleIntactPercolatingClusterDualHalf k c1 ∧
    IsPrimalCylinderClusterStep (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred c1 c2 ∧
    (c1 ≠ 0 → ∀ mX : (bdlIteratedBundled (k + 1)).M_Z,
      c2 mX ≠ 0 →
      c1 (stepXMXOwnerX (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred mX) ≠ 0) ∧
    (∀ u v : (bdlIteratedBundled (k + 1)).M_Z,
      c2 u ≠ 0 → c2 v ≠ 0 → MultiscaleClusterConnDual k c2 u v)

/-- Code-level zero-spillover witness pool constructor (`codeZeroSpilloverPool`) using
    `Classical.propDecidable` and uniform `[Fintype]` / `[DecidableEq]` typeclass instances. -/
noncomputable def codeZeroSpilloverPool {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    (w : ℕ) (P : (M_X → ZMod 2) → Prop) : Finset (M_X → ZMod 2) :=
  @Finset.filter (M_X → ZMod 2)
    (fun c => c ≠ 0 ∧ w ≤ syndromeWeightNat c ∧
      (∃ e_C : Q → ZMod 2, syndrome code e_C = c) ∧ P c)
    (fun _ => Classical.propDecidable _)
    Finset.univ

lemma mem_codeZeroSpilloverPool_mpr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    (w : ℕ) (P : (M_X → ZMod 2) → Prop) (c : M_X → ZMod 2)
    (hc : c ≠ 0) (hw : w ≤ syndromeWeightNat c)
    (he : ∃ e_C : Q → ZMod 2, syndrome code e_C = c) (hP : P c) :
    c ∈ codeZeroSpilloverPool code w P := by
  exact (@Finset.mem_filter (M_X → ZMod 2)
    (fun c => c ≠ 0 ∧ w ≤ syndromeWeightNat c ∧
      (∃ e_C : Q → ZMod 2, syndrome code e_C = c) ∧ P c)
    (fun _ => Classical.propDecidable _) Finset.univ c).mpr
    ⟨Finset.mem_univ c, hc, hw, he, hP⟩

lemma zero_not_mem_codeZeroSpilloverPool {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    (w : ℕ) (P : (M_X → ZMod 2) → Prop) :
    (0 : M_X → ZMod 2) ∉ codeZeroSpilloverPool code w P := by
  intro h_mem
  have h := (@Finset.mem_filter (M_X → ZMod 2)
    (fun c => c ≠ 0 ∧ w ≤ syndromeWeightNat c ∧
      (∃ e_C : Q → ZMod 2, syndrome code e_C = c) ∧ P c)
    (fun _ => Classical.propDecidable _) Finset.univ 0).mp h_mem
  exact h.2.1 rfl

lemma weight_le_of_mem_codeZeroSpilloverPool {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    (w : ℕ) (P : (M_X → ZMod 2) → Prop) :
    ∀ c ∈ codeZeroSpilloverPool code w P, (w : ℝ) ≤ syndromeWeight c := by
  intro c hc
  have h := (@Finset.mem_filter (M_X → ZMod 2)
    (fun c => c ≠ 0 ∧ w ≤ syndromeWeightNat c ∧
      (∃ e_C : Q → ZMod 2, syndrome code e_C = c) ∧ P c)
    (fun _ => Classical.propDecidable _) Finset.univ c).mp hc
  rw [syndromeWeight_eq_natCast]
  exact_mod_cast h.2.2.1

lemma exists_syndrome_eq_of_mem_codeZeroSpilloverPool {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X)
    (w : ℕ) (P : (M_X → ZMod 2) → Prop) :
    ∀ c ∈ codeZeroSpilloverPool code w P, ∃ e_C : Q → ZMod 2, syndrome code e_C = c := by
  intro c hc
  have h := (@Finset.mem_filter (M_X → ZMod 2)
    (fun c => c ≠ 0 ∧ w ≤ syndromeWeightNat c ∧
      (∃ e_C : Q → ZMod 2, syndrome code e_C = c) ∧ P c)
    (fun _ => Classical.propDecidable _) Finset.univ c).mp hc
  exact h.2.2.2.1

/-- Multiscale intact connected cluster predicate in the primal X-check sector
    (`IsMultiscaleIntactConnectedClusterPrimal`, Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
def IsMultiscaleIntactConnectedClusterPrimal (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2) : Prop :=
  IsMultiscaleIntactPercolatingClusterPrimal k c2 ∧
    ∀ u v : (bdlIteratedBundled (k + 1)).M_X,
      c2 u ≠ 0 → c2 v ≠ 0 → MultiscaleClusterConnPrimal k c2 u v

/-- Multiscale intact percolating cluster witness pool in the primal sector
    (`multiscaleIntactWitnessPoolPrimal`, Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
noncomputable def multiscaleIntactWitnessPoolPrimal (k : ℕ) :
    Finset ((bdlIteratedBundled (k + 1)).M_X → ZMod 2) :=
  codeZeroSpilloverPool (bdlIteratedBundled (k + 1)).code (clusterRawWeight k)
    (IsMultiscaleIntactConnectedClusterPrimal k)

/-- Membership introduction for `multiscaleIntactWitnessPoolPrimal k`. -/
lemma mem_multiscaleIntactWitnessPoolPrimal_mpr (k : ℕ) :
    ∀ (c : (bdlIteratedBundled (k + 1)).M_X → ZMod 2),
      c ≠ 0 →
      clusterRawWeight k ≤ syndromeWeightNat c →
      (∃ e_C : (bdlIteratedBundled (k + 1)).Q → ZMod 2,
        syndrome (bdlIteratedBundled (k + 1)).code e_C = c) →
      IsMultiscaleIntactConnectedClusterPrimal k c →
      c ∈ multiscaleIntactWitnessPoolPrimal k :=
  mem_codeZeroSpilloverPool_mpr (bdlIteratedBundled (k + 1)).code (clusterRawWeight k) _

/-- Multiscale intact percolating cluster witness pool in the dual sector
    (`multiscaleIntactWitnessPoolDual`, Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`)). -/
noncomputable def multiscaleIntactWitnessPoolDual (k : ℕ) :
    Finset ((bdlIteratedBundled (k + 1)).M_Z → ZMod 2) :=
  codeZeroSpilloverPool (dualCode (bdlIteratedBundled (k + 1)).code) (clusterRawWeight k)
    (IsMultiscaleIntactPercolatingClusterDual k)

/-- Multiscale decoded logical parity rule in the primal sector (`multiscaleParityRulePrimal`,
    Part II, Definition 2.5 (`def:syndrome-safe`) and
    Definition 4.2 (`def:multiscale-cluster-decoder`)), propagating the base zero
    parity rule on `bdlIteratedBundled 1` across `k` full RG cycles via `rzCoarseParityRule` at
    `bdlRandomStepX` and `rxCleanedParityRule` at `bdlRandomStepZ` for safe-subspace logical immunity. -/
noncomputable def multiscaleParityRulePrimal :
    (k : ℕ) → ((bdlIteratedBundled (k + 1)).M_X → ZMod 2) → ZMod 2
  | 0 => fun _ => 0
  | k + 1 =>
      let B := bdlIteratedBundled (k + 1)
      let B1 := bdlRandomStepX B
      let ψ1 := rzCoarseParityRule (bdlPerturbedOfBundled B) bdlSubdivPred
        (multiscaleParityRulePrimal k)
      rxCleanedParityRule (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
        ψ1 (stepXLX B (bdlIteratedLX (k + 1)))

/-- Multiscale decoded logical parity rule in the dual sector (`multiscaleParityRuleDual`,
    Part II, Definition 2.5 (`def:syndrome-safe`) and
    Definition 4.2 (`def:multiscale-cluster-decoder`)), propagating the base zero
    parity rule on `bdlIteratedBundled 1` across `k` full RG cycles via `rxCleanedParityRule` at
    `bdlRandomStepX` and `rzCoarseParityRule` at `bdlRandomStepZ` for safe-subspace logical immunity. -/
noncomputable def multiscaleParityRuleDual :
    (k : ℕ) → ((bdlIteratedBundled (k + 1)).M_Z → ZMod 2) → ZMod 2
  | 0 => fun _ => 0
  | k + 1 =>
      let B := bdlIteratedBundled (k + 1)
      let B1 := bdlRandomStepX B
      let ψ1 := rxCleanedParityRule (bdlPerturbedOfBundled B) bdlSubdivPred
        (multiscaleParityRuleDual k) (bdlIteratedLZ (k + 1))
      rzCoarseParityRule (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred ψ1

/-- `multiscaleParityRulePrimal k` vanishes on the zero syndrome. -/
lemma multiscaleParityRulePrimal_zero (k : ℕ) :
    multiscaleParityRulePrimal k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    dsimp [multiscaleParityRulePrimal]
    exact rxCleanedParityRule_zero _ bdlSubdivPred _
      (rzCoarseParityRule_zero _ bdlSubdivPred _ ih) _

/-- `multiscaleParityRuleDual k` vanishes on the zero syndrome. -/
lemma multiscaleParityRuleDual_zero (k : ℕ) :
    multiscaleParityRuleDual k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ m ih =>
    dsimp [multiscaleParityRuleDual]
    exact rzCoarseParityRule_zero _ bdlSubdivPred _
      (rxCleanedParityRule_zero _ bdlSubdivPred _ ih _)

/-- The zero syndrome is never in `multiscaleIntactWitnessPoolPrimal k`. -/
lemma zero_not_mem_multiscaleIntactWitnessPoolPrimal (k : ℕ) :
    (0 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2) ∉ multiscaleIntactWitnessPoolPrimal k :=
  zero_not_mem_codeZeroSpilloverPool (bdlIteratedBundled (k + 1)).code (clusterRawWeight k) _

/-- The zero syndrome is never in `multiscaleIntactWitnessPoolDual k`. -/
lemma zero_not_mem_multiscaleIntactWitnessPoolDual (k : ℕ) :
    (0 : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2) ∉ multiscaleIntactWitnessPoolDual k :=
  zero_not_mem_codeZeroSpilloverPool (dualCode (bdlIteratedBundled (k + 1)).code) (clusterRawWeight k) _

/-- Every witness in `multiscaleIntactWitnessPoolPrimal k` has weight at least `clusterRawWeight k`. -/
lemma clusterRawWeight_le_of_mem_multiscaleIntactWitnessPoolPrimal (k : ℕ) :
    ∀ c ∈ multiscaleIntactWitnessPoolPrimal k, (clusterRawWeight k : ℝ) ≤ syndromeWeight c :=
  weight_le_of_mem_codeZeroSpilloverPool (bdlIteratedBundled (k + 1)).code (clusterRawWeight k) _

/-- Every witness in `multiscaleIntactWitnessPoolDual k` has weight at least `clusterRawWeight k`. -/
lemma clusterRawWeight_le_of_mem_multiscaleIntactWitnessPoolDual (k : ℕ) :
    ∀ c ∈ multiscaleIntactWitnessPoolDual k, (clusterRawWeight k : ℝ) ≤ syndromeWeight c :=
  weight_le_of_mem_codeZeroSpilloverPool (dualCode (bdlIteratedBundled (k + 1)).code) (clusterRawWeight k) _

/-- Every witness in `multiscaleIntactWitnessPoolPrimal k` is a zero-spillover realizable syndrome. -/
lemma exists_syndrome_eq_of_mem_multiscaleIntactWitnessPoolPrimal (k : ℕ) :
    ∀ c ∈ multiscaleIntactWitnessPoolPrimal k,
      ∃ e_C : (bdlIteratedBundled (k + 1)).Q → ZMod 2,
        syndrome (bdlIteratedBundled (k + 1)).code e_C = c :=
  exists_syndrome_eq_of_mem_codeZeroSpilloverPool (bdlIteratedBundled (k + 1)).code (clusterRawWeight k) _

/-- Every witness in `multiscaleIntactWitnessPoolDual k` is a zero-spillover realizable syndrome. -/
lemma exists_syndrome_eq_of_mem_multiscaleIntactWitnessPoolDual (k : ℕ) :
    ∀ c ∈ multiscaleIntactWitnessPoolDual k,
      ∃ h_C : (bdlIteratedBundled (k + 1)).Q → ZMod 2,
        syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h_C = c :=
  exists_syndrome_eq_of_mem_codeZeroSpilloverPool (dualCode (bdlIteratedBundled (k + 1)).code) (clusterRawWeight k) _

/-- Extracts the coarse syndrome equality and contraction bound from `IsDualCylinderClusterStep`. -/
lemma IsDualCylinderClusterStep.syn_wt {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {pcode : CSSCode3D Q M_Z M_X} {M : ℕ} {c0 : M_Z → ZMod 2} {c1 : BDLStepXMZ pcode M → ZMod 2}
    (h : IsDualCylinderClusterStep pcode M c0 c1) :
    rxCleanedCoarseSyndrome pcode M c1 = c0 ∧ 27 * syndromeWeightNat c0 ≤ 16 * syndromeWeightNat c1 := by
  rcases h with ⟨_, _, _, _, h1, h2⟩; exact ⟨h1, h2⟩

/-- Extracts `c ≠ 0 ∧ P c` from membership in `codeZeroSpilloverPool code w P`. -/
lemma prop_of_mem_codeZeroSpilloverPool {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (w : ℕ) (P : (M_X → ZMod 2) → Prop) :
    ∀ c ∈ codeZeroSpilloverPool code w P, c ≠ 0 ∧ P c := by
  intro c hc
  have h := (@Finset.mem_filter (M_X → ZMod 2)
    (fun c => c ≠ 0 ∧ w ≤ syndromeWeightNat c ∧ (∃ e_C : Q → ZMod 2, syndrome code e_C = c) ∧ P c)
    (fun _ => Classical.propDecidable _) Finset.univ c).mp hc
  exact ⟨h.2.1, h.2.2.2.2⟩

/-- Polymorphic Klarner shell cardinality bound for `codeZeroSpilloverPool code w P`. -/
lemma card_shell_codeZeroSpilloverPool_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (w : ℕ) (P : (M_X → ZMod 2) → Prop)
    (G : HierStepPkg M_X)
    (h_lift : ∀ c : M_X → ZMod 2, c ≠ 0 → P c →
      ∃ (Conn : M_X → M_X → Prop) (w_coeff : ℕ) (C_hat : Finset G.V),
        w_coeff ≤ 55 ∧
        IsHierClusterWitness G Conn w_coeff c C_hat ∧
        (C_hat ∩ G.R).Nonempty ∧
        (∀ x y : M_X, c x ≠ 0 → c y ≠ 0 → Conn x y))
    (m : ℕ) :
    ((codeZeroSpilloverPool code w P).filter
      (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
      (bdlClusterStepBase ^ 8) ^ m := by
  apply G.card_shell_le (codeZeroSpilloverPool code w P) _ m
  intro c hc
  obtain ⟨hc_ne, hP⟩ := prop_of_mem_codeZeroSpilloverPool code w P c hc
  exact ⟨hc_ne, h_lift c hc_ne hP⟩

/-- Primal multiscale cluster witness lift to `primalHierPkg k`. -/
lemma exists_hierClusterWitness_primal (k : ℕ) :
    ∀ c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2,
      IsMultiscaleIntactPercolatingClusterPrimal k c2 →
      ∃ C_hat : Finset (primalHierPkg k).V,
        IsHierClusterWitness (primalHierPkg k) (MultiscaleClusterConnPrimal k c2) 43 c2 C_hat ∧
        (C_hat ∩ (primalHierPkg k).R).Nonempty := by
  induction k with
  | zero =>
    intro c2 h_intact
    obtain ⟨hc2_ne, c0, c1, _, ⟨_, rfl, h_wt1⟩, h_step2⟩ := h_intact
    obtain ⟨rfl, h_wt2⟩ := h_step2.syn_wt
    exact primalHierPkg_base_lift hc2_ne rfl h_wt1 rfl h_wt2
  | succ m ih =>
    intro c2 h_intact
    obtain ⟨c0, c1, h_intact0, ⟨_, rfl, h_wt1⟩, h_step2⟩ := h_intact
    obtain ⟨rfl, h_wt2⟩ := h_step2.syn_wt
    obtain ⟨C_hat_0, hw0, hR0⟩ := ih _ h_intact0
    exact primalHierPkg_succ_lift m hw0 hR0 rfl h_wt1 rfl h_wt2

/-- Dual multiscale cluster witness lift at odd half-steps to `dualHalfHierPkg k`. -/
lemma exists_hierClusterWitness_dualHalf (k : ℕ) :
    ∀ c1 : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2,
      IsMultiscaleIntactPercolatingClusterDualHalf k c1 →
      ∃ C_hat : Finset (dualHalfHierPkg k).V,
        IsHierClusterWitness (dualHalfHierPkg k) (MultiscaleClusterConnDualHalf k c1) 43 c1 C_hat ∧
        (0 < k → (C_hat ∩ (dualHalfHierPkg k).R).Nonempty) := by
  induction k with
  | zero =>
    intro c1 h_half
    obtain ⟨c0, _, h_step⟩ := h_half
    obtain ⟨rfl, h_wt⟩ := h_step.syn_wt
    exact dualHalfHierPkg_base_lift rfl h_wt
  | succ m ih =>
    intro c_top h_half_top
    obtain ⟨_, c_prev, c_mid, hc_prev_ne, h_half, ⟨_, rfl, h_wt1⟩, h_step2⟩ := h_half_top
    obtain ⟨rfl, h_wt2⟩ := h_step2.syn_wt
    obtain ⟨C_hat_prev, hw_prev, hR_prev⟩ := ih _ h_half
    exact dualHalfHierPkg_succ_lift m hw_prev hR_prev hc_prev_ne rfl h_wt1 rfl h_wt2

end BDLDecoder
end WeldedHierarchy

end
