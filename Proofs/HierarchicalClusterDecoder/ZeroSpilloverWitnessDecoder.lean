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

import Proofs.HierarchicalClusterDecoder.ZeroSpilloverWitnessHelpers
import Proofs.HierarchicalClusterDecoder.ZeroSpilloverBallParityHelpers

/-!
# Intact Percolating Cluster Decomposition and Klarner Witness Shell Bounds

Proves that any ball-confined error discrepancy forces a realizable, multiscale-connected intact percolating cluster witness in `multiscaleIntactWitnessPoolPrimal` or `multiscaleIntactWitnessPoolDual` (`multiscaleIntactWitnessPool_ball_parity_witness_exists`). Combines the (3/2)^k cluster weight growth with rooted Klarner walk counting to establish `multiscale_intact_cluster_witness_decomposition_and_klarner_bound` and `hasZeroSpilloverBallParityWitnessFamily_bdlWelded_lambdaPow` on `bdlWeldedCode k`.

## References

* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Lemma 5.4 (`lem:percolating-cluster-bounds`)
* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.3 (`lem:klarner-bound`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Definition 4.2 (`def:multiscale-cluster-decoder`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
* Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

namespace WeldedHierarchy
namespace BDLDecoder

attribute [local irreducible] bdlSubdivPred

/-! ## 1. Helper Lemmas for Intact Percolating Cluster Realizability and Component Extraction -/

lemma syndromeWeightNat_pos_of_ne_zero {M : Type} [Fintype M] [DecidableEq M]
    {c : M → ZMod 2} (hc : c ≠ 0) : 1 ≤ syndromeWeightNat c := by
  have ⟨m, hm⟩ : ∃ m : M, c m ≠ 0 := by
    by_contra h_all; push_neg at h_all; exact hc (funext h_all)
  exact Finset.card_pos.mpr ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩

lemma clusterRawWeight_pos (k : ℕ) : 1 ≤ clusterRawWeight k := by
  have h1 := three_pow_le_two_pow_mul_clusterRawWeight k
  have h2 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have h3 : 1 ≤ 2 ^ k * clusterRawWeight k := le_trans h2 h1
  rcases Nat.eq_zero_or_pos (clusterRawWeight k) with h0 | hpos
  · rw [h0, mul_zero] at h3; omega
  · exact hpos

lemma clusterRawWeight_succ_le_of_step {m a b c : ℕ}
    (h0 : clusterRawWeight m ≤ a) (h1 : a ≤ b) (h2 : 27 * b ≤ 16 * c) :
    clusterRawWeight (m + 1) ≤ c := by
  dsimp [clusterRawWeight]; omega

lemma isPrimalCylinderClusterStep_realizable_and_weight {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h_conn : HasConnectedXLinks pcode)
    {c0 : M_X → ZMod 2} {c1 : BDLStepXMX pcode M → ZMod 2}
    (h_step : IsPrimalCylinderClusterStep pcode M c0 c1)
    (he0 : ∃ e0 : Q → ZMod 2, syndrome pcode e0 = c0) :
    (∃ e1 : BDLStepXQ pcode M → ZMod 2, syndrome (bdlCylinderStepX pcode M) e1 = c1) ∧
    syndromeWeightNat c0 ≤ syndromeWeightNat c1 := by
  rcases h_step with ⟨⟨e, he⟩, hc0, hwt⟩
  rcases he0 with ⟨e0, he0_eq⟩
  obtain ⟨u_clean, _, hu_rec⟩ := primal_cylinder_subsyndrome_zero_spillover_recovery pcode M h_conn e c1 he
  exact ⟨⟨u_clean + liftCylinderLZ pcode M e0, hu_rec e0 (he0_eq.trans hc0.symm)⟩, hwt⟩

lemma isDualCylinderClusterStep_realizable_and_weight {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    {c0 : M_Z → ZMod 2} {c1 : BDLStepXMZ pcode M → ZMod 2}
    (h_step : IsDualCylinderClusterStep pcode M c0 c1)
    (hh0 : ∃ h0 : Q → ZMod 2, syndrome (dualCode pcode) h0 = c0) :
    (∃ h1 : BDLStepXQ pcode M → ZMod 2,
      syndrome (dualCode (bdlCylinderStepX pcode M)) h1 = c1) ∧
    27 * syndromeWeightNat c0 ≤ 16 * syndromeWeightNat c1 := by
  rcases h_step with ⟨h, K, ⟨hZ_Q, hQ_X, hX_Q, hQ_Z⟩, rfl, hc0, hwt⟩
  rcases hh0 with ⟨h0, hh0_eq⟩
  have h_cob := (dual_cleaner_isolated_component_coboundary_eq pcode M hov hq_z h_conn K h
    hZ_Q hQ_X hX_Q hQ_Z
    (fun x q0 hx hchk h_nz hq0 => hx (hQ_X q0 x hq0 hchk h_nz))
    (fun q0 z0 hq0 hchk h_nz hz0 => hq0 (hZ_Q z0 q0 hz0 hchk h_nz))).2.2 h0 (hh0_eq.trans hc0.symm)
  exact ⟨⟨_, h_cob⟩, hwt⟩

lemma isMultiscaleIntactPercolatingClusterPrimal_props (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (h_cl : IsMultiscaleIntactPercolatingClusterPrimal k c2) :
    c2 ≠ 0 ∧
    clusterRawWeight k ≤ syndromeWeightNat c2 ∧
    (∃ e_C : (bdlIteratedBundled (k + 1)).Q → ZMod 2,
      syndrome (bdlIteratedBundled (k + 1)).code e_C = c2) := by
  induction k with
  | zero =>
    rcases h_cl with ⟨hc2_ne, c0, c1, he0, h_step1, h_step2⟩
    let B := bdlIteratedBundled 0
    let B1 := bdlRandomStepX B
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled 0
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    have ⟨he1, _⟩ := isPrimalCylinderClusterStep_realizable_and_weight
      (bdlPerturbedOfBundled B) bdlSubdivPred h_inv_B.2.2.2.2.1 h_step1 he0
    have ⟨hh2, _⟩ := isDualCylinderClusterStep_realizable_and_weight
      (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
      h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 h_step2 he1
    have he2' : ∃ e_C : (bdlIteratedBundled (0 + 1)).Q → ZMod 2,
        syndrome (bdlIteratedBundled (0 + 1)).code e_C = c2 := by
      rcases hh2 with ⟨e2, he2⟩
      exact ⟨e2, he2⟩
    exact ⟨hc2_ne, syndromeWeightNat_pos_of_ne_zero hc2_ne, he2'⟩
  | succ m ih =>
    rcases h_cl with ⟨c0, c1, h_cl0, h_step1, h_step2⟩
    rcases ih c0 h_cl0 with ⟨_, h_wt0, he0⟩
    let B := bdlIteratedBundled (m + 1)
    let B1 := bdlRandomStepX B
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    have ⟨he1, h_wt1⟩ := isPrimalCylinderClusterStep_realizable_and_weight
      (bdlPerturbedOfBundled B) bdlSubdivPred h_inv_B.2.2.2.2.1 h_step1 he0
    have ⟨hh2, h_wt2⟩ := isDualCylinderClusterStep_realizable_and_weight
      (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
      h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 h_step2 he1
    have he2' : ∃ e_C : (bdlIteratedBundled (m + 1 + 1)).Q → ZMod 2,
        syndrome (bdlIteratedBundled (m + 1 + 1)).code e_C = c2 := by
      rcases hh2 with ⟨e2, he2⟩
      exact ⟨e2, he2⟩
    have h_wt_c2 : clusterRawWeight (m + 1) ≤ syndromeWeightNat c2 :=
      clusterRawWeight_succ_le_of_step h_wt0 h_wt1 h_wt2
    have hc2_ne : c2 ≠ 0 := by
      intro h_z
      have h_w0 : syndromeWeightNat c2 = 0 := by
        subst h_z; dsimp [syndromeWeightNat]; simp
      have h_pos := clusterRawWeight_pos (m + 1)
      omega
    exact ⟨hc2_ne, h_wt_c2, he2'⟩

section
attribute [local irreducible] bdlIteratedBundled

lemma mem_multiscaleIntactWitnessPoolPrimal_of_isMultiscale (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (h_cl : IsMultiscaleIntactPercolatingClusterPrimal k c2)
    (h_conn : ∀ u v : (bdlIteratedBundled (k + 1)).M_X,
      c2 u ≠ 0 → c2 v ≠ 0 → MultiscaleClusterConnPrimal k c2 u v) :
    c2 ∈ multiscaleIntactWitnessPoolPrimal k :=
  let h_props := isMultiscaleIntactPercolatingClusterPrimal_props k c2 h_cl
  mem_multiscaleIntactWitnessPoolPrimal_mpr k c2 h_props.1 h_props.2.1 h_props.2.2
    (And.intro h_cl h_conn)

end

lemma isMultiscaleIntactPercolatingClusterDualHalf_props (k : ℕ)
    (c1 : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2)
    (h_cl : IsMultiscaleIntactPercolatingClusterDualHalf k c1) :
    (k = 0 ∨ clusterRawWeight k ≤ syndromeWeightNat c1) ∧
    (∃ h1 : (bdlRandomStepX (bdlIteratedBundled k)).Q → ZMod 2,
      syndrome (dualCode (bdlRandomStepX (bdlIteratedBundled k)).code) h1 = c1) := by
  induction k with
  | zero =>
    rcases h_cl with ⟨c0, hh0, h_step⟩
    let B0 := bdlIteratedBundled 0
    have h_inv_B0 : HasBDLConeInvariants B0 := hasBDLConeInvariants_bdlIteratedBundled 0
    have ⟨hh1, _⟩ := isDualCylinderClusterStep_realizable_and_weight
      (bdlPerturbedOfBundled B0) bdlSubdivPred
      h_inv_B0.1.2 h_inv_B0.2.2.2.1.2 h_inv_B0.2.2.2.2.1 h_step hh0
    exact ⟨Or.inl rfl, hh1⟩
  | succ m ih =>
    rcases h_cl with ⟨_, c_prev, c_mid, hc_prev_ne, h_cl_prev, h_step1, h_step2⟩
    rcases ih c_prev h_cl_prev with ⟨h_wt_prev_or, hh_prev⟩
    have h_wt_prev : clusterRawWeight m ≤ syndromeWeightNat c_prev := by
      rcases h_wt_prev_or with rfl | h_wt
      · exact syndromeWeightNat_pos_of_ne_zero hc_prev_ne
      · exact h_wt
    let B_prev := bdlIteratedBundled m
    let B_half := bdlRandomStepX B_prev
    let B_mid := bdlIteratedBundled (m + 1)
    have h_inv_prev : HasBDLConeInvariants B_prev := hasBDLConeInvariants_bdlIteratedBundled m
    have h_inv_half : HasBDLConeInvariants B_half :=
      hasBDLConeInvariants_bdlRandomStepX B_prev h_inv_prev
    have h_inv_dhalf : HasBDLConeInvariants (dualBundled B_half) :=
      hasBDLConeInvariants_dualBundled B_half h_inv_half
    have h_inv_mid : HasBDLConeInvariants B_mid := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    have ⟨hh_mid, h_wt1⟩ := isPrimalCylinderClusterStep_realizable_and_weight
      (bdlPerturbedOfBundled (dualBundled B_half)) bdlSubdivPred
      h_inv_dhalf.2.2.2.2.1 h_step1 hh_prev
    have hh_mid' : ∃ h0 : B_mid.Q → ZMod 2, syndrome (dualCode B_mid.code) h0 = c_mid := by
      rcases hh_mid with ⟨h0, hh0⟩
      exact ⟨h0, hh0⟩
    have ⟨hh_top, h_wt2⟩ := isDualCylinderClusterStep_realizable_and_weight
      (bdlPerturbedOfBundled B_mid) bdlSubdivPred
      h_inv_mid.1.2 h_inv_mid.2.2.2.1.2 h_inv_mid.2.2.2.2.1 h_step2 hh_mid'
    have h_wt_top : clusterRawWeight (m + 1) ≤ syndromeWeightNat c1 :=
      clusterRawWeight_succ_le_of_step h_wt_prev h_wt1 h_wt2
    exact ⟨Or.inr h_wt_top, hh_top⟩

lemma mem_multiscaleIntactWitnessPoolDual_of_isMultiscale (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2)
    (h_cl : IsMultiscaleIntactPercolatingClusterDual k c2) :
    c2 ∈ multiscaleIntactWitnessPoolDual k := by
  rcases h_cl with ⟨hc2_ne, c1, h_cl1, h_step2, h_own, h_conn⟩
  rcases isMultiscaleIntactPercolatingClusterDualHalf_props k c1 h_cl1 with ⟨h_wt1_or, hh1⟩
  let B := bdlIteratedBundled k
  let B1 := bdlRandomStepX B
  have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled k
  have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
  have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
    hasBDLConeInvariants_dualBundled B1 h_inv_B1
  have ⟨hh2, h_wt2⟩ := isPrimalCylinderClusterStep_realizable_and_weight
    (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
    h_inv_dB1.2.2.2.2.1 h_step2 hh1
  have hh2' : ∃ h_C : (bdlIteratedBundled (k + 1)).Q → ZMod 2,
      syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h_C = c2 := by
    rcases hh2 with ⟨h_C, hh_C⟩
    exact ⟨h_C, hh_C⟩
  have h_wt_c2 : clusterRawWeight k ≤ syndromeWeightNat c2 := by
    rcases h_wt1_or with rfl | h_wt1
    · exact syndromeWeightNat_pos_of_ne_zero hc2_ne
    · exact le_trans h_wt1 h_wt2
  exact mem_codeZeroSpilloverPool_mpr (dualCode (bdlIteratedBundled (k + 1)).code) (clusterRawWeight k)
    _ c2 hc2_ne h_wt_c2 hh2' ⟨hc2_ne, c1, h_cl1, h_step2, h_own, h_conn⟩

/-! ### Symmetry of Multiscale Connectivity Relations -/

lemma reflTransGen_symm {α : Type*} {R : α → α → Prop}
    (h_symm : ∀ a b, R a b → R b a) {u v : α}
    (h : Relation.ReflTransGen R u v) : Relation.ReflTransGen R v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (h_symm _ _ hbc)).trans ih

lemma primalMultiscaleAdj_symm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    {Conn0 : M_X → M_X → Prop}
    (h_symm : ∀ a b, Conn0 a b → Conn0 b a)
    (c0 : M_X → ZMod 2) (c1 : BDLStepXMX pcode M → ZMod 2)
    {u v : BDLStepXMX pcode M}
    (h : PrimalMultiscaleAdj pcode M Conn0 c0 c1 u v) :
    PrimalMultiscaleAdj pcode M Conn0 c0 c1 v u := by
  rcases h with ⟨hu, hv, h_eq | ⟨ha, hb, hconn⟩⟩
  · exact ⟨hv, hu, Or.inl h_eq.symm⟩
  · exact ⟨hv, hu, Or.inr ⟨hb, ha, h_symm _ _ hconn⟩⟩

lemma primalMultiscaleConn_symm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    {Conn0 : M_X → M_X → Prop}
    (h_symm : ∀ a b, Conn0 a b → Conn0 b a)
    (c0 : M_X → ZMod 2) (c1 : BDLStepXMX pcode M → ZMod 2)
    {u v : BDLStepXMX pcode M}
    (h : PrimalMultiscaleConn pcode M Conn0 c0 c1 u v) :
    PrimalMultiscaleConn pcode M Conn0 c0 c1 v u :=
  reflTransGen_symm (fun _ _ => primalMultiscaleAdj_symm pcode M h_symm c0 c1) h

lemma twoHopPoolAdj_symm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (c1 : BDLStepXMZ pcode M → ZMod 2)
    {u v : BDLStepXMZ pcode M}
    (h : TwoHopPoolAdj pcode M c1 u v) :
    TwoHopPoolAdj pcode M c1 v u := by
  rcases h with ⟨hu, hv, z0, hzu, hzv⟩
  exact ⟨hv, hu, z0, hzv, hzu⟩

lemma dualMultiscaleAdj_symm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    {Conn0 : M_Z → M_Z → Prop}
    (h_symm : ∀ a b, Conn0 a b → Conn0 b a)
    (c0 : M_Z → ZMod 2) (c1 : BDLStepXMZ pcode M → ZMod 2)
    {u v : BDLStepXMZ pcode M}
    (h : DualMultiscaleAdj pcode M Conn0 c0 c1 u v) :
    DualMultiscaleAdj pcode M Conn0 c0 c1 v u := by
  rcases h with ⟨hu, hv, h_th | ⟨za, zb, hza, hzb, hconn, ha, hb⟩⟩
  · exact ⟨hv, hu, Or.inl (twoHopPoolAdj_symm pcode M c1 h_th)⟩
  · exact ⟨hv, hu, Or.inr ⟨zb, za, hzb, hza, h_symm _ _ hconn, hb, ha⟩⟩

lemma dualMultiscaleConn_symm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    {Conn0 : M_Z → M_Z → Prop}
    (h_symm : ∀ a b, Conn0 a b → Conn0 b a)
    (c0 : M_Z → ZMod 2) (c1 : BDLStepXMZ pcode M → ZMod 2)
    {u v : BDLStepXMZ pcode M}
    (h : DualMultiscaleConn pcode M Conn0 c0 c1 u v) :
    DualMultiscaleConn pcode M Conn0 c0 c1 v u :=
  reflTransGen_symm (fun _ _ => dualMultiscaleAdj_symm pcode M h_symm c0 c1) h

lemma multiscaleClusterConnPrimal_refl (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (u : (bdlIteratedBundled (k + 1)).M_X) :
    MultiscaleClusterConnPrimal k c2 u u := by
  cases k <;> exact Relation.ReflTransGen.refl

lemma multiscaleClusterConnPrimal_trans (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    {u v w : (bdlIteratedBundled (k + 1)).M_X}
    (h1 : MultiscaleClusterConnPrimal k c2 u v)
    (h2 : MultiscaleClusterConnPrimal k c2 v w) :
    MultiscaleClusterConnPrimal k c2 u w := by
  cases k <;> exact Relation.ReflTransGen.trans h1 h2

lemma multiscaleClusterConnPrimal_symm (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2) :
    ∀ {u v}, MultiscaleClusterConnPrimal k c2 u v → MultiscaleClusterConnPrimal k c2 v u := by
  induction k with
  | zero =>
    intro u v h
    exact dualMultiscaleConn_symm _ bdlSubdivPred
      (fun _ _ => primalMultiscaleConn_symm _ bdlSubdivPred (fun _ _ h0 => ⟨h0.2, h0.1⟩) _ _)
      _ _ h
  | succ m ih =>
    intro u v h
    exact dualMultiscaleConn_symm _ bdlSubdivPred
      (fun _ _ => primalMultiscaleConn_symm _ bdlSubdivPred (@ih _) _ _)
      _ _ h

lemma multiscaleClusterConnDualHalf_symm (k : ℕ)
    (c1 : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2) :
    ∀ {u v}, MultiscaleClusterConnDualHalf k c1 u v → MultiscaleClusterConnDualHalf k c1 v u := by
  induction k with
  | zero =>
    intro u v h
    exact dualMultiscaleConn_symm _ bdlSubdivPred (fun _ _ h0 => ⟨h0.2, h0.1⟩) _ _ h
  | succ m ih =>
    intro u v h
    exact dualMultiscaleConn_symm _ bdlSubdivPred
      (fun _ _ => primalMultiscaleConn_symm _ bdlSubdivPred (@ih _) _ _)
      _ _ h

lemma multiscaleClusterConnDual_symm (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2) :
    ∀ {u v}, MultiscaleClusterConnDual k c2 u v → MultiscaleClusterConnDual k c2 v u := by
  intro u v h
  exact primalMultiscaleConn_symm _ bdlSubdivPred (fun _ _ => multiscaleClusterConnDualHalf_symm k _) _ _ h

/-! ### Single-Step Primal and Dual Subsyndrome Restriction Lemmas -/

lemma primal_subsyndrome_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (e : BDLStepXQ pcode M → ZMod 2)
    (S1 : BDLStepXMX pcode M → ZMod 2)
    (hS1 : syndrome (bdlCylinderStepX pcode M) e = S1)
    (Conn0_S : M_X → M_X → Prop)
    (c1 : BDLStepXMX pcode M → ZMod 2)
    (hc1_sub : ∀ u : BDLStepXMX pcode M, c1 u ≠ 0 → S1 u ≠ 0)
    (hc1_closed : ∀ u v : BDLStepXMX pcode M,
      c1 u ≠ 0 →
      PrimalMultiscaleConn pcode M Conn0_S (coarsePrimalSyndrome pcode M S1) S1 u v →
      c1 v ≠ 0) :
    (∀ x0 : M_X, coarsePrimalSyndrome pcode M c1 x0 ≠ 0 ↔
      (coarsePrimalSyndrome pcode M S1 x0 ≠ 0 ∧
        ∃ u : BDLStepXMX pcode M, c1 u ≠ 0 ∧ stepXMXOwnerX pcode M u = x0)) ∧
    IsPrimalCylinderClusterStep pcode M (coarsePrimalSyndrome pcode M c1) c1 ∧
    ((∀ x_a x_b : M_X, coarsePrimalSyndrome pcode M S1 x_a ≠ 0 →
        Conn0_S x_a x_b → coarsePrimalSyndrome pcode M S1 x_b ≠ 0) →
      ∀ x_a x_b : M_X, coarsePrimalSyndrome pcode M c1 x_a ≠ 0 →
        Conn0_S x_a x_b → coarsePrimalSyndrome pcode M c1 x_b ≠ 0) ∧
    (∀ (Conn0_c : M_X → M_X → Prop),
      (∀ x_a x_b : M_X, coarsePrimalSyndrome pcode M c1 x_a ≠ 0 →
        coarsePrimalSyndrome pcode M c1 x_b ≠ 0 → Conn0_S x_a x_b → Conn0_c x_a x_b) →
      ∀ u v : BDLStepXMX pcode M,
        c1 u ≠ 0 →
        PrimalMultiscaleConn pcode M Conn0_S (coarsePrimalSyndrome pcode M S1) S1 u v →
        PrimalMultiscaleConn pcode M Conn0_c (coarsePrimalSyndrome pcode M c1) c1 u v) ∧
    (∀ u0 v : BDLStepXMX pcode M,
      c1 u0 ≠ 0 → coarsePrimalSyndrome pcode M S1 (stepXMXOwnerX pcode M u0) ≠ 0 →
      PrimalMultiscaleConn pcode M Conn0_S (coarsePrimalSyndrome pcode M S1) S1 u0 v →
      coarsePrimalSyndrome pcode M c1 (stepXMXOwnerX pcode M v) ≠ 0) := by
  have h_zmod2_eq : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by decide
  have h_fib_full : ∀ u v : BDLStepXMX pcode M,
      c1 u ≠ 0 → S1 v ≠ 0 → stepXMXOwnerX pcode M u = stepXMXOwnerX pcode M v → c1 v ≠ 0 := by
    intro u v hu hv h_own
    exact hc1_closed u v hu (Relation.ReflTransGen.single ⟨hc1_sub u hu, hv, Or.inl h_own⟩)
  have hc0_eq : ∀ x0 : M_X,
      coarsePrimalSyndrome pcode M c1 x0 =
        if (∃ u : BDLStepXMX pcode M, c1 u ≠ 0 ∧ stepXMXOwnerX pcode M u = x0)
        then coarsePrimalSyndrome pcode M S1 x0 else 0 := by
    intro x0
    dsimp [coarsePrimalSyndrome, coarseSyndromeStepXMX]
    split_ifs with h_ex
    · rcases h_ex with ⟨u, hu, hu_own⟩
      apply Finset.sum_congr rfl
      intro v hv
      have hv_own : stepXMXOwnerX pcode M v = x0 := (Finset.mem_filter.mp hv).2
      apply h_zmod2_eq
      exact ⟨hc1_sub v, fun hv_S1 => h_fib_full u v hu hv_S1 (hu_own.trans hv_own.symm)⟩
    · apply Finset.sum_eq_zero
      intro v hv
      have hv_own : stepXMXOwnerX pcode M v = x0 := (Finset.mem_filter.mp hv).2
      by_contra hv_nz
      exact h_ex ⟨v, hv_nz, hv_own⟩
  have hc0_iff : ∀ x0 : M_X, coarsePrimalSyndrome pcode M c1 x0 ≠ 0 ↔
      (coarsePrimalSyndrome pcode M S1 x0 ≠ 0 ∧
        ∃ u : BDLStepXMX pcode M, c1 u ≠ 0 ∧ stepXMXOwnerX pcode M u = x0) := by
    intro x0
    rw [hc0_eq x0]
    by_cases h_ex : ∃ u : BDLStepXMX pcode M, c1 u ≠ 0 ∧ stepXMXOwnerX pcode M u = x0 <;> simp [h_ex]
  have h_wt : syndromeWeightNat (coarsePrimalSyndrome pcode M c1) ≤ syndromeWeightNat c1 := by
    dsimp [syndromeWeightNat]
    have h_sub : Finset.univ.filter (fun x0 : M_X => coarsePrimalSyndrome pcode M c1 x0 ≠ 0) ⊆
        (Finset.univ.filter (fun u : BDLStepXMX pcode M => c1 u ≠ 0)).image
          (stepXMXOwnerX pcode M) := by
      intro x0 hx0
      rcases (hc0_iff x0).mp (Finset.mem_filter.mp hx0).2 with ⟨_, u, hu, rfl⟩
      exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩, rfl⟩
    exact (Finset.card_le_card h_sub).trans Finset.card_image_le
  have hc1_sub_e : ∀ u : BDLStepXMX pcode M, c1 u ≠ 0 → syndrome (bdlCylinderStepX pcode M) e u ≠ 0 := by
    rw [hS1]; exact hc1_sub
  refine ⟨hc0_iff, ⟨⟨e, hc1_sub_e⟩, rfl, h_wt⟩, ?_, ?_, ?_⟩
  · intro hConn0_S x_a x_b hxa h_conn
    rcases (hc0_iff x_a).mp hxa with ⟨hS0_a, u, hu, hu_own⟩
    have hS0_b : coarsePrimalSyndrome pcode M S1 x_b ≠ 0 := hConn0_S x_a x_b hS0_a h_conn
    obtain ⟨v, hv_own, hv_S1⟩ :=
      exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero pcode M S1 x_b hS0_b
    have hv_c1 : c1 v ≠ 0 :=
      hc1_closed u v hu (Relation.ReflTransGen.single
        ⟨hc1_sub u hu, hv_S1, Or.inr ⟨hu_own ▸ hS0_a, hv_own ▸ hS0_b,
          hu_own.symm ▸ hv_own.symm ▸ h_conn⟩⟩)
    exact (hc0_iff x_b).mpr ⟨hS0_b, v, hv_c1, hv_own⟩
  · intro Conn0_c hConn0_c u v hu h_path
    induction h_path with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      rename_i b c
      have hb_c1 : c1 b ≠ 0 := hc1_closed u b hu hab
      have hc_c1 : c1 c ≠ 0 := hc1_closed u c hu (hab.tail hbc)
      rcases hbc with ⟨_, _, h_own_eq | ⟨hS0_b, hS0_c, h_conn_bc⟩⟩
      · exact ih.tail ⟨hb_c1, hc_c1, Or.inl h_own_eq⟩
      · have hc0_b : coarsePrimalSyndrome pcode M c1 (stepXMXOwnerX pcode M b) ≠ 0 :=
          (hc0_iff _).mpr ⟨hS0_b, b, hb_c1, rfl⟩
        have hc0_c : coarsePrimalSyndrome pcode M c1 (stepXMXOwnerX pcode M c) ≠ 0 :=
          (hc0_iff _).mpr ⟨hS0_c, c, hc_c1, rfl⟩
        exact ih.tail ⟨hb_c1, hc_c1,
          Or.inr ⟨hc0_b, hc0_c, hConn0_c _ _ hc0_b hc0_c h_conn_bc⟩⟩
  · intro u0 v hu0 hS0_u0 h_path
    have hS0_v : coarsePrimalSyndrome pcode M S1 (stepXMXOwnerX pcode M v) ≠ 0 := by
      induction h_path with
      | refl => exact hS0_u0
      | tail _ hbc ih =>
        rcases hbc with ⟨_, _, h_own_eq | ⟨_, hS0_c, _⟩⟩
        · rwa [← h_own_eq]
        · exact hS0_c
    have hv_c1 : c1 v ≠ 0 := hc1_closed u0 v hu0 h_path
    exact (hc0_iff _).mpr ⟨hS0_v, v, hv_c1, rfl⟩

lemma exists_mem_fineTwoHopPool_singleton {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (mZ : BDLStepXMZ pcode M) :
    ∃ z0 : M_Z, mZ ∈ fineTwoHopPool pcode M {z0} := by
  rcases mZ with (⟨⟨⟨⟨⟨x1, ⟨⟨q1, z1⟩, hZ1⟩⟩, hX1⟩, r1, k1⟩, hs1⟩, b1⟩ |
                  ⟨⟨⟨x1, ⟨⟨q1, z1⟩, hZ1⟩⟩, hX1⟩, k1, b1⟩) |
                 ((⟨⟨⟨q1, z1⟩, hZ1⟩, k1, b1⟩ | ⟨⟨⟨q1, z1⟩, hZ1⟩, b1⟩) | ⟨z1, b1⟩)
  · refine ⟨z1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change inVX x1 ∈ twoHopTannerOfZ pcode {z1}
    rw [inVX_mem_twoHopTannerOfZ_iff, twoHopX, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, q1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, z1, Finset.mem_singleton_self z1, hZ1⟩, hX1⟩
  · refine ⟨z1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change inVX x1 ∈ twoHopTannerOfZ pcode {z1}
    rw [inVX_mem_twoHopTannerOfZ_iff, twoHopX, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, q1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, z1, Finset.mem_singleton_self z1, hZ1⟩, hX1⟩
  · refine ⟨z1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change inVQ q1 ∈ twoHopTannerOfZ pcode {z1}
    rw [inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, z1, Finset.mem_singleton_self z1, hZ1⟩
  · refine ⟨z1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change inVQ q1 ∈ twoHopTannerOfZ pcode {z1}
    rw [inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, z1, Finset.mem_singleton_self z1, hZ1⟩
  · refine ⟨z1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change inVZ z1 ∈ twoHopTannerOfZ pcode {z1}
    rw [inVZ_mem_twoHopTannerOfZ_iff]
    exact Finset.mem_singleton_self z1

lemma mem_twoHopTannerOfZ_iff_exists_singleton {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (K_Z : Finset M_Z) (v : TannerVertex Q M_Z M_X) :
    v ∈ twoHopTannerOfZ pcode K_Z ↔ ∃ z0 ∈ K_Z, v ∈ twoHopTannerOfZ pcode {z0} := by
  rcases v with x | (q0 | z0)
  · change inVX x ∈ twoHopTannerOfZ pcode K_Z ↔ ∃ z0 ∈ K_Z, inVX x ∈ twoHopTannerOfZ pcode {z0}
    simp only [inVX_mem_twoHopTannerOfZ_iff, twoHopX, oneHopQ, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨q0, ⟨z0, hz0, hZ⟩, hX⟩
      exact ⟨z0, hz0, q0, hZ, hX⟩
    · rintro ⟨z0, hz0, q0, hZ, hX⟩
      exact ⟨q0, ⟨z0, hz0, hZ⟩, hX⟩
  · change inVQ q0 ∈ twoHopTannerOfZ pcode K_Z ↔ ∃ z0 ∈ K_Z, inVQ q0 ∈ twoHopTannerOfZ pcode {z0}
    simp only [inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton, exists_eq_left]
  · change inVZ z0 ∈ twoHopTannerOfZ pcode K_Z ↔ ∃ z' ∈ K_Z, inVZ z0 ∈ twoHopTannerOfZ pcode {z'}
    simp only [inVZ_mem_twoHopTannerOfZ_iff, Finset.mem_singleton]
    constructor
    · intro hz0; exact ⟨z0, hz0, rfl⟩
    · rintro ⟨z', hz', rfl⟩; exact hz'

lemma exists_inVX_ne_zero_of_cleanCylinderX_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (S_any : BDLStepXMZ pcode M → ZMod 2) (x : M_X)
    (h_clean_nz : cleanCylinderX pcode M S_any x ≠ 0) :
    ∃ b : BDLStepXMZ pcode M, stepXMZOwnerTanner pcode M b = inVX x ∧ S_any b ≠ 0 := by
  have h_rest_nz : restrictCX2 pcode M x S_any ≠ 0 := by
    intro h0
    exact h_clean_nz (cleanCylinderX_eq_zero_of_restrictCX2_eq_zero pcode M S_any x h0)
  have ⟨b, hb⟩ : ∃ b : BDLStepXMZ pcode M, restrictCX2 pcode M x S_any b ≠ 0 := by
    by_contra h_all; push_neg at h_all; exact h_rest_nz (funext h_all)
  dsimp only [restrictCX2, restrictStepXMZ] at hb
  split_ifs at hb with hb_own
  · exact ⟨b, Finset.mem_singleton.mp hb_own, hb⟩
  · exact False.elim (hb rfl)

lemma exists_cQ2_ne_zero_of_restrictCQ2_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (S_any : BDLStepXMZ pcode M → ZMod 2) (q0 : Q)
    (h_rest_nz : restrictCQ2 pcode M q0 S_any ≠ 0) :
    ∃ mZQ : BDLCQ2 pcode M,
      cQ2OwnerQ pcode M mZQ = q0 ∧ S_any (Sum.inr (Sum.inl mZQ)) ≠ 0 := by
  by_contra h_all; push_neg at h_all
  apply h_rest_nz; ext mZ
  dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply]
  split_ifs with hmZ
  · rcases mZ with mZX | (mZQ | mZZ)
    · dsimp [stepXMZOwnerTanner, inVX, inVQ] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
    · dsimp [stepXMZOwnerTanner, inVQ] at hmZ
      rw [Finset.mem_singleton, Sum.inr.injEq, Sum.inl.injEq] at hmZ
      exact h_all mZQ hmZ
    · dsimp [stepXMZOwnerTanner, inVZ, inVQ] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
  · rfl

noncomputable def activeTwoHopPoolZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c1 : BDLStepXMZ pcode M → ZMod 2) : Finset M_Z :=
  Finset.univ.filter (fun z0 : M_Z =>
    ∃ a : BDLStepXMZ pcode M, c1 a ≠ 0 ∧ a ∈ fineTwoHopPool pcode M {z0})

lemma mem_activeTwoHopPoolZ_iff {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (c1 : BDLStepXMZ pcode M → ZMod 2) (z0 : M_Z) :
    z0 ∈ activeTwoHopPoolZ pcode M c1 ↔
      ∃ a : BDLStepXMZ pcode M, c1 a ≠ 0 ∧ a ∈ fineTwoHopPool pcode M {z0} := by
  dsimp [activeTwoHopPoolZ]
  exact ⟨fun hz => (Finset.mem_filter.mp hz).2,
    fun h_ex => Finset.mem_filter.mpr ⟨Finset.mem_univ z0, h_ex⟩⟩

lemma dual_subsyndrome_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2)
    (S1 : BDLStepXMZ pcode M → ZMod 2)
    (hS1 : syndrome (dualCode (bdlCylinderStepX pcode M)) h = S1)
    (Conn0_S : M_Z → M_Z → Prop)
    (c1 : BDLStepXMZ pcode M → ZMod 2)
    (hc1_sub : ∀ u : BDLStepXMZ pcode M, c1 u ≠ 0 → S1 u ≠ 0)
    (hc1_closed : ∀ u v : BDLStepXMZ pcode M,
      c1 u ≠ 0 →
      DualMultiscaleConn pcode M Conn0_S (rxCleanedCoarseSyndrome pcode M S1) S1 u v →
      c1 v ≠ 0) :
    (∀ z0 : M_Z, rxCleanedCoarseSyndrome pcode M c1 z0 ≠ 0 ↔
      (rxCleanedCoarseSyndrome pcode M S1 z0 ≠ 0 ∧
        ∃ a : BDLStepXMZ pcode M, c1 a ≠ 0 ∧ a ∈ fineTwoHopPool pcode M {z0})) ∧
    IsDualCylinderClusterStep pcode M (rxCleanedCoarseSyndrome pcode M c1) c1 ∧
    ((∀ z_a z_b : M_Z, rxCleanedCoarseSyndrome pcode M S1 z_a ≠ 0 →
        Conn0_S z_a z_b → rxCleanedCoarseSyndrome pcode M S1 z_b ≠ 0) →
      ∀ z_a z_b : M_Z, rxCleanedCoarseSyndrome pcode M c1 z_a ≠ 0 →
        Conn0_S z_a z_b → rxCleanedCoarseSyndrome pcode M c1 z_b ≠ 0) ∧
    (∀ (Conn0_c : M_Z → M_Z → Prop),
      (∀ z_a z_b : M_Z, rxCleanedCoarseSyndrome pcode M c1 z_a ≠ 0 →
        rxCleanedCoarseSyndrome pcode M c1 z_b ≠ 0 → Conn0_S z_a z_b → Conn0_c z_a z_b) →
      ∀ u v : BDLStepXMZ pcode M,
        c1 u ≠ 0 →
        DualMultiscaleConn pcode M Conn0_S (rxCleanedCoarseSyndrome pcode M S1) S1 u v →
        DualMultiscaleConn pcode M Conn0_c (rxCleanedCoarseSyndrome pcode M c1) c1 u v) := by
  have h_zmod2_eq : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b := by decide
  let K_Z : Finset M_Z := activeTwoHopPoolZ pcode M c1
  let K : Finset (TannerVertex Q M_Z M_X) := twoHopTannerOfZ pcode K_Z
  have h_twohop_closed : ∀ (z0 : M_Z) (a b : BDLStepXMZ pcode M),
      c1 a ≠ 0 → S1 b ≠ 0 → a ∈ fineTwoHopPool pcode M {z0} → b ∈ fineTwoHopPool pcode M {z0} →
      c1 b ≠ 0 := by
    intro z0 a b ha hb ha_p hb_p
    exact hc1_closed a b ha (Relation.ReflTransGen.single
      ⟨hc1_sub a ha, hb, Or.inl ⟨hc1_sub a ha, hb, z0, ha_p, hb_p⟩⟩)
  have hc1_eq_restrict : c1 = restrictStepXMZ pcode M K S1 := by
    ext b
    dsimp only [restrictStepXMZ]
    split_ifs with hb_K
    · apply h_zmod2_eq
      refine ⟨hc1_sub b, fun hb_S1 => ?_⟩
      rcases (mem_twoHopTannerOfZ_iff_exists_singleton pcode K_Z _).mp hb_K with ⟨z0, hz0, hb_z0⟩
      rcases (mem_activeTwoHopPoolZ_iff pcode M c1 z0).mp hz0 with ⟨a, ha_c1, ha_p⟩
      exact h_twohop_closed z0 a b ha_c1 hb_S1 ha_p
        (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb_z0⟩)
    · by_contra hb_c1
      rcases exists_mem_fineTwoHopPool_singleton pcode M b with ⟨z0, hb_z0⟩
      have hz0 : z0 ∈ K_Z := (mem_activeTwoHopPoolZ_iff pcode M c1 z0).mpr ⟨b, hb_c1, hb_z0⟩
      exact hb_K ((mem_twoHopTannerOfZ_iff_exists_singleton pcode K_Z _).mpr
        ⟨z0, hz0, (Finset.mem_filter.mp hb_z0).2⟩)
  have hK_Z_to_Q : ∀ z0 : M_Z, ∀ q0 : Q,
      inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (S1 + syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanStage1X pcode M S1)) q0) (z0, b) ≠ 0) →
      inVQ q0 ∈ K := by
    intro z0 q0 hz0 h_chk _
    change inVZ z0 ∈ twoHopTannerOfZ pcode K_Z at hz0
    change inVQ q0 ∈ twoHopTannerOfZ pcode K_Z
    rw [inVZ_mem_twoHopTannerOfZ_iff] at hz0
    rw [inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, z0, hz0, h_chk⟩
  have hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S1 x)) ≠ 0 →
      inVX x ∈ K := by
    intro q0 x hq0 h_chk _
    change inVQ q0 ∈ twoHopTannerOfZ pcode K_Z at hq0
    change inVX x ∈ twoHopTannerOfZ pcode K_Z
    rw [inVQ_mem_twoHopTannerOfZ_iff] at hq0
    rw [inVX_mem_twoHopTannerOfZ_iff, twoHopX, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, q0, hq0, h_chk⟩
  have hK_X_to_Q : ∀ x : M_X, ∀ q0 : Q,
      inVX x ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S1 x)) ≠ 0 →
      inVQ q0 ∈ K := by
    intro x q0 hx_K h_chkX h_rest_nz
    have h_clean_nz : cleanCylinderX pcode M S1 x ≠ 0 := by
      intro h0; rw [h0, map_zero] at h_rest_nz
      exact h_rest_nz (by ext mZ; dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply]; exact ite_self _)
    obtain ⟨b, hb_own, hb_S1⟩ := exists_inVX_ne_zero_of_cleanCylinderX_ne_zero pcode M S1 x h_clean_nz
    have hb_c1 : c1 b ≠ 0 := by
      rw [hc1_eq_restrict]; dsimp only [restrictStepXMZ]; rw [hb_own, if_pos hx_K]; exact hb_S1
    obtain ⟨z0, h_chkZ⟩ := hq_z q0
    have hb_z0 : b ∈ fineTwoHopPool pcode M {z0} := by
      rw [fineTwoHopPool, Finset.mem_filter]
      refine ⟨Finset.mem_univ b, ?_⟩
      rw [hb_own, inVX_mem_twoHopTannerOfZ_iff, twoHopX, Finset.mem_filter]
      exact ⟨Finset.mem_univ x, q0,
        Finset.mem_filter.mpr ⟨Finset.mem_univ q0, z0, Finset.mem_singleton_self z0, h_chkZ⟩, h_chkX⟩
    have hz0_K : z0 ∈ K_Z := (mem_activeTwoHopPoolZ_iff pcode M c1 z0).mpr ⟨b, hb_c1, hb_z0⟩
    change inVQ q0 ∈ twoHopTannerOfZ pcode K_Z
    rw [inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter]
    exact ⟨Finset.mem_univ q0, z0, hz0_K, h_chkZ⟩
  have hK_Q_to_Z : ∀ q0 : Q, ∀ z0 : M_Z,
      inVQ q0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b_fin : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (S1 + syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanStage1X pcode M S1)) q0) (z0, b_fin) ≠ 0) →
      inVZ z0 ∈ K := by
    intro q0 z0 hq0_K h_chkZ ⟨b_fin, h_exp_nz⟩
    have h_star_nz : cleanStarQ pcode M
        (S1 + syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanStage1X pcode M S1)) q0 ≠ 0 := by
      intro h0; rw [h0, exportQZ_apply] at h_exp_nz
      exact h_exp_nz (Finset.sum_eq_zero (fun _ _ => mul_zero _))
    have h_rest_s1_nz : restrictCQ2 pcode M q0
        (S1 + syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanStage1X pcode M S1)) ≠ 0 := by
      intro h0
      exact h_star_nz (cleanStarQ_eq_zero_of_restrictCQ2_eq_zero pcode M _ q0 h0)
    obtain ⟨mZQ, hmZQ_own, hmZQ_nz⟩ :=
      exists_cQ2_ne_zero_of_restrictCQ2_ne_zero pcode M _ q0 h_rest_s1_nz
    rw [s1_cq2_eq_sum_KX pcode M K S1 hK_Q_to_X q0 hq0_K mZQ hmZQ_own] at hmZQ_nz
    by_cases h_S1_mZQ : S1 (Sum.inr (Sum.inl mZQ)) = 0
    · rw [h_S1_mZQ, zero_add] at hmZQ_nz
      obtain ⟨x, hx_mem, hx_exp_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hmZQ_nz
      have hx_K : inVX x ∈ K := (Finset.mem_filter.mp hx_mem).2
      have h_eq_exp : syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M S1 x) (Sum.inr (Sum.inl mZQ)) =
          exportXQ pcode M (cleanCylinderX pcode M S1 x) mZQ := by
        unfold exportXQ; rw [splitStepXQ_X_cleanCylinderX]
      have h_rest_x_nz : restrictCQ2 pcode M q0
          (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S1 x)) ≠ 0 := by
        intro h0
        have h_at := congr_fun h0 (Sum.inr (Sum.inl mZQ))
        dsimp [restrictCQ2, restrictStepXMZ] at h_at
        have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl mZQ)) ∈ ({inVQ q0} : Finset _) := by
          simp [stepXMZOwnerTanner, hmZQ_own]
        rw [if_pos hm, h_eq_exp] at h_at
        exact hx_exp_nz h_at
      have h_chkX : pcode.checkX x q0 ≠ 0 := by
        intro h_chk0
        exact h_rest_x_nz (restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero
          pcode M x q0 h_chk0 (cleanCylinderX pcode M S1 x) (cleanCylinderX_support pcode M S1 x))
      have h_clean_nz : cleanCylinderX pcode M S1 x ≠ 0 := by
        intro h0; rw [h0, map_zero] at h_rest_x_nz
        exact h_rest_x_nz (by ext mZ; dsimp only [restrictCQ2, restrictStepXMZ, Pi.zero_apply]; exact ite_self _)
      obtain ⟨b, hb_own, hb_S1⟩ := exists_inVX_ne_zero_of_cleanCylinderX_ne_zero pcode M S1 x h_clean_nz
      have hb_c1 : c1 b ≠ 0 := by
        rw [hc1_eq_restrict]; dsimp only [restrictStepXMZ]; rw [hb_own, if_pos hx_K]; exact hb_S1
      have hb_z0 : b ∈ fineTwoHopPool pcode M {z0} := by
        rw [fineTwoHopPool, Finset.mem_filter]
        refine ⟨Finset.mem_univ b, ?_⟩
        rw [hb_own, inVX_mem_twoHopTannerOfZ_iff, twoHopX, Finset.mem_filter]
        exact ⟨Finset.mem_univ x, q0,
          Finset.mem_filter.mpr ⟨Finset.mem_univ q0, z0, Finset.mem_singleton_self z0, h_chkZ⟩, h_chkX⟩
      change inVZ z0 ∈ twoHopTannerOfZ pcode K_Z
      rw [inVZ_mem_twoHopTannerOfZ_iff]
      exact (mem_activeTwoHopPoolZ_iff pcode M c1 z0).mpr ⟨b, hb_c1, hb_z0⟩
    · let b : BDLStepXMZ pcode M := Sum.inr (Sum.inl mZQ)
      have hb_own : stepXMZOwnerTanner pcode M b = inVQ q0 := congr_arg inVQ hmZQ_own
      have hb_c1 : c1 b ≠ 0 := by
        rw [hc1_eq_restrict]; dsimp only [restrictStepXMZ]; rw [hb_own, if_pos hq0_K]; exact h_S1_mZQ
      have hb_z0 : b ∈ fineTwoHopPool pcode M {z0} := by
        rw [fineTwoHopPool, Finset.mem_filter]
        refine ⟨Finset.mem_univ b, ?_⟩
        rw [hb_own, inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter]
        exact ⟨Finset.mem_univ q0, z0, Finset.mem_singleton_self z0, h_chkZ⟩
      change inVZ z0 ∈ twoHopTannerOfZ pcode K_Z
      rw [inVZ_mem_twoHopTannerOfZ_iff]
      exact (mem_activeTwoHopPoolZ_iff pcode M c1 z0).mpr ⟨b, hb_c1, hb_z0⟩
  have hK_Z_to_Q_h : ∀ z0 : M_Z, ∀ q0 : Q,
      inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
          (z0, b) ≠ 0) →
      inVQ q0 ∈ K := by
    rw [hS1]; exact hK_Z_to_Q
  have hK_Q_to_X_h : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x)) ≠ 0 →
      inVX x ∈ K := by
    rw [hS1]; exact hK_Q_to_X
  have hK_X_to_Q_h : ∀ x : M_X, ∀ q0 : Q,
      inVX x ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanCylinderX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) x)) ≠ 0 →
      inVQ q0 ∈ K := by
    rw [hS1]; exact hK_X_to_Q
  have hK_Q_to_Z_h : ∀ q0 : Q, ∀ z0 : M_Z,
      inVQ q0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b_fin : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
          (z0, b_fin) ≠ 0) →
      inVZ z0 ∈ K := by
    rw [hS1]; exact hK_Q_to_Z
  have h_cob := dual_cleaner_isolated_component_coboundary_eq pcode M hov hq_z h_conn K h
    hK_Z_to_Q_h hK_Q_to_X_h hK_X_to_Q_h hK_Q_to_Z_h
    (fun x q0 hx hchk h_nz hq0 => hx (hK_Q_to_X_h q0 x hq0 hchk h_nz))
    (fun q0 z0 hq0 hchk h_nz hz0 => hq0 (hK_Z_to_Q_h z0 q0 hz0 hchk h_nz))
  have hc0_eq : ∀ z0 : M_Z,
      rxCleanedCoarseSyndrome pcode M c1 z0 =
        if inVZ z0 ∈ K then rxCleanedCoarseSyndrome pcode M S1 z0 else 0 := by
    intro z0
    rw [hc1_eq_restrict, ← hS1]
    exact cleanTwoStageRX_restrictStepXMZ_cz2_eq pcode M hov hq_z h_conn K h
      hK_Z_to_Q_h hK_Q_to_X_h hK_X_to_Q_h hK_Q_to_Z_h z0 0
  have hc0_iff : ∀ z0 : M_Z, rxCleanedCoarseSyndrome pcode M c1 z0 ≠ 0 ↔
      (rxCleanedCoarseSyndrome pcode M S1 z0 ≠ 0 ∧
        ∃ a : BDLStepXMZ pcode M, c1 a ≠ 0 ∧ a ∈ fineTwoHopPool pcode M {z0}) := by
    intro z0
    rw [hc0_eq z0]
    have hz0_iff : inVZ z0 ∈ K ↔
        ∃ a : BDLStepXMZ pcode M, c1 a ≠ 0 ∧ a ∈ fineTwoHopPool pcode M {z0} := by
      change inVZ z0 ∈ twoHopTannerOfZ pcode K_Z ↔ _
      rw [inVZ_mem_twoHopTannerOfZ_iff]
      exact mem_activeTwoHopPoolZ_iff pcode M c1 z0
    by_cases hz : inVZ z0 ∈ K
    · rw [if_pos hz]
      exact ⟨fun hS0 => ⟨hS0, hz0_iff.mp hz⟩, fun h_pair => h_pair.1⟩
    · rw [if_neg hz]
      exact ⟨fun h0 => False.elim (h0 rfl), fun h_pair => False.elim (hz (hz0_iff.mpr h_pair.2))⟩
  have h_step : IsDualCylinderClusterStep pcode M (rxCleanedCoarseSyndrome pcode M c1) c1 := by
    have hc1_eq_h : c1 = restrictStepXMZ pcode M K (syndrome (dualCode (bdlCylinderStepX pcode M)) h) := by
      rw [hS1]; exact hc1_eq_restrict
    refine ⟨h, K, ⟨hK_Z_to_Q_h, hK_Q_to_X_h, hK_X_to_Q_h, hK_Q_to_Z_h⟩, hc1_eq_h, rfl, ?_⟩
    have h_wt := h_cob.2.1
    rw [← hc1_eq_h] at h_wt
    exact h_wt
  refine ⟨hc0_iff, h_step, ?_, ?_⟩
  · intro hConn0_S z_a z_b hza h_conn_ab
    rcases (hc0_iff z_a).mp hza with ⟨hS0_a, a, ha_c1, ha_p⟩
    have hS0_b : rxCleanedCoarseSyndrome pcode M S1 z_b ≠ 0 := hConn0_S z_a z_b hS0_a h_conn_ab
    have h_pos_b : 1 ≤ ((fineTwoHopPool pcode M {z_b}).filter (fun mZ => S1 mZ ≠ 0)).card := by
      have h_contr := two_hop_bipartite_pool_contraction pcode M hov hq_z h_conn {z_b} S1 ⟨h, hS1⟩
        (fun z' hz' => by rw [Finset.mem_singleton.mp hz']; exact hS0_b)
      rw [Finset.card_singleton] at h_contr
      omega
    rcases Finset.card_pos.mp h_pos_b with ⟨b, hb_mem⟩
    rcases Finset.mem_filter.mp hb_mem with ⟨hb_p, hb_S1⟩
    have hb_c1 : c1 b ≠ 0 :=
      hc1_closed a b ha_c1 (Relation.ReflTransGen.single
        ⟨hc1_sub a ha_c1, hb_S1, Or.inr ⟨z_a, z_b, hS0_a, hS0_b, h_conn_ab, ha_p, hb_p⟩⟩)
    exact (hc0_iff z_b).mpr ⟨hS0_b, b, hb_c1, hb_p⟩
  · intro Conn0_c hConn0_c u v hu h_path
    induction h_path with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      rename_i b c
      have hb_c1 : c1 b ≠ 0 := hc1_closed u b hu hab
      have hc_c1 : c1 c ≠ 0 := hc1_closed u c hu (hab.tail hbc)
      rcases hbc with ⟨_, _, ⟨_, _, z0, hb_p, hc_p⟩ | ⟨z_b, z_c, hS0_b, hS0_c, h_conn_bc, hb_p, hc_p⟩⟩
      · exact ih.tail ⟨hb_c1, hc_c1, Or.inl ⟨hb_c1, hc_c1, z0, hb_p, hc_p⟩⟩
      · have hc0_b : rxCleanedCoarseSyndrome pcode M c1 z_b ≠ 0 :=
          (hc0_iff z_b).mpr ⟨hS0_b, b, hb_c1, hb_p⟩
        have hc0_c : rxCleanedCoarseSyndrome pcode M c1 z_c ≠ 0 :=
          (hc0_iff z_c).mpr ⟨hS0_c, c, hc_c1, hc_p⟩
        exact ih.tail ⟨hb_c1, hc_c1,
          Or.inr ⟨z_b, z_c, hc0_b, hc0_c, hConn0_c z_b z_c hc0_b hc0_c h_conn_bc, hb_p, hc_p⟩⟩

/-! ### Multiscale Component Extraction and Ball-Parity Discrepancy Induction -/

lemma primalMultiscaleConn_active_right {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_X → M_X → Prop) (c0 : M_X → ZMod 2) (c1 : BDLStepXMX pcode M → ZMod 2)
    {u v : BDLStepXMX pcode M} (hu : c1 u ≠ 0)
    (h : PrimalMultiscaleConn pcode M Conn0 c0 c1 u v) : c1 v ≠ 0 := by
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hbc.2.1

lemma dualMultiscaleConn_active_right {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (Conn0 : M_Z → M_Z → Prop) (c0 : M_Z → ZMod 2) (c1 : BDLStepXMZ pcode M → ZMod 2)
    {u v : BDLStepXMZ pcode M} (hu : c1 u ≠ 0)
    (h : DualMultiscaleConn pcode M Conn0 c0 c1 u v) : c1 v ≠ 0 := by
  induction h with
  | refl => exact hu
  | tail _ hbc _ => exact hbc.2.1

lemma multiscaleClusterConnPrimal_active_right (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    {u v : (bdlIteratedBundled (k + 1)).M_X} (hu : c2 u ≠ 0)
    (h : MultiscaleClusterConnPrimal k c2 u v) : c2 v ≠ 0 := by
  cases k <;> exact dualMultiscaleConn_active_right _ _ _ _ _ hu h

lemma multiscaleClusterConnDualHalf_active_right (k : ℕ)
    (c1 : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2)
    {u v : (bdlRandomStepX (bdlIteratedBundled k)).M_Z} (hu : c1 u ≠ 0)
    (h : MultiscaleClusterConnDualHalf k c1 u v) : c1 v ≠ 0 := by
  cases k <;> exact dualMultiscaleConn_active_right _ _ _ _ _ hu h

lemma multiscaleClusterConnDual_active_right (k : ℕ)
    (c2 : (bdlIteratedBundled (k + 1)).M_Z → ZMod 2)
    {u v : (bdlIteratedBundled (k + 1)).M_Z} (hu : c2 u ≠ 0)
    (h : MultiscaleClusterConnDual k c2 u v) : c2 v ≠ 0 :=
  primalMultiscaleConn_active_right _ _ _ _ _ hu h

noncomputable def pushedSyndromePrimal :
    (k : ℕ) → ((bdlIteratedBundled (k + 1)).M_X → ZMod 2) →
    ((bdlIteratedBundled 1).M_X → ZMod 2)
  | 0, S => S
  | k + 1, S =>
      let B := bdlIteratedBundled (k + 1)
      let B1 := bdlRandomStepX B
      let S1 := rxCleanedCoarseSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred S
      let S0 := coarsePrimalSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred S1
      pushedSyndromePrimal k S0

noncomputable def pushedSyndromeDualHalf :
    (k : ℕ) → ((bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2) →
    ((bdlRandomStepX (bdlIteratedBundled 0)).M_Z → ZMod 2)
  | 0, S => S
  | k + 1, S =>
      let B_prev := bdlIteratedBundled k
      let B_half := bdlRandomStepX B_prev
      let B_mid := bdlIteratedBundled (k + 1)
      let S_mid := rxCleanedCoarseSyndrome (bdlPerturbedOfBundled B_mid) bdlSubdivPred S
      let S_prev := coarsePrimalSyndrome (bdlPerturbedOfBundled (dualBundled B_half)) bdlSubdivPred S_mid
      pushedSyndromeDualHalf k S_prev

lemma exists_active_in_fineTwoHopPool_singleton {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (u1 : M_Z)
    (h : BDLStepXQ pcode M → ZMod 2)
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hS : syndrome (dualCode (bdlCylinderStepX pcode M)) h = S)
    (hu1 : rxCleanedCoarseSyndrome pcode M S u1 ≠ 0) :
    ∃ u2 ∈ fineTwoHopPool pcode M {u1}, S u2 ≠ 0 := by
  have h_contr := two_hop_bipartite_pool_contraction pcode M
    hov hq_z h_conn {u1} S ⟨h, hS⟩
    (fun z' hz' => by rw [Finset.mem_singleton.mp hz']; exact hu1)
  rw [Finset.card_singleton] at h_contr
  by_contra h_none
  push_neg at h_none
  have h_empty : (fineTwoHopPool pcode M {u1}).filter (fun mZ => S mZ ≠ 0) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (fun x hx h_ne => h_ne (h_none x hx))
  rw [h_empty, Finset.card_empty] at h_contr
  omega

lemma rxCleanedCoarseSyndrome_ne_zero_of_witness {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    {S1 c1 : BDLStepXMZ pcode M → ZMod 2}
    (h_iff : ∀ z0 : M_Z, rxCleanedCoarseSyndrome pcode M c1 z0 ≠ 0 ↔
      (rxCleanedCoarseSyndrome pcode M S1 z0 ≠ 0 ∧
        ∃ a : BDLStepXMZ pcode M, c1 a ≠ 0 ∧ a ∈ fineTwoHopPool pcode M {z0}))
    (z0 : M_Z) (hz0 : rxCleanedCoarseSyndrome pcode M S1 z0 ≠ 0)
    (a : BDLStepXMZ pcode M) (ha : c1 a ≠ 0) (ha_pool : a ∈ fineTwoHopPool pcode M {z0}) :
    rxCleanedCoarseSyndrome pcode M c1 z0 ≠ 0 :=
  (h_iff z0).mpr ⟨hz0, a, ha, ha_pool⟩

lemma coarsePrimalSyndrome_ne_zero_of_witness {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    {S1 c1 : BDLStepXMX pcode M → ZMod 2}
    (h_iff : ∀ x0 : M_X, coarsePrimalSyndrome pcode M c1 x0 ≠ 0 ↔
      (coarsePrimalSyndrome pcode M S1 x0 ≠ 0 ∧
        ∃ u : BDLStepXMX pcode M, c1 u ≠ 0 ∧ stepXMXOwnerX pcode M u = x0))
    (x0 : M_X) (hx0 : coarsePrimalSyndrome pcode M S1 x0 ≠ 0)
    (u : BDLStepXMX pcode M) (hu : c1 u ≠ 0) (hu_own : stepXMXOwnerX pcode M u = x0) :
    coarsePrimalSyndrome pcode M c1 x0 ≠ 0 :=
  (h_iff x0).mpr ⟨hx0, u, hu, hu_own⟩

noncomputable def restrictToComponent {α : Type*} (R : α → α → Prop) (S : α → ZMod 2) (u0 : α) :
    α → ZMod 2 :=
  fun v => if R u0 v then S v else 0

lemma restrictToComponent_sub {α : Type*} (R : α → α → Prop) (S : α → ZMod 2) (u0 : α)
    (u : α) (hu : restrictToComponent R S u0 u ≠ 0) : S u ≠ 0 := by
  dsimp [restrictToComponent] at hu
  split_ifs at hu with h_conn
  · exact hu
  · exact False.elim (hu rfl)

lemma restrictToComponent_conn {α : Type*} (R : α → α → Prop) (S : α → ZMod 2) (u0 : α)
    (u : α) (hu : restrictToComponent R S u0 u ≠ 0) : R u0 u := by
  dsimp [restrictToComponent] at hu
  by_contra h_nc
  exact hu (if_neg h_nc)

lemma restrictToComponent_closed {α : Type*} (R : α → α → Prop) (S : α → ZMod 2) (u0 : α)
    (h_trans : ∀ {a b c : α}, R a b → R b c → R a c)
    (h_act : ∀ {a b : α}, S a ≠ 0 → R a b → S b ≠ 0)
    (u v : α) (hu : restrictToComponent R S u0 u ≠ 0) (h_uv : R u v) :
    restrictToComponent R S u0 v ≠ 0 := by
  have h_u0_v : R u0 v := h_trans (restrictToComponent_conn R S u0 u hu) h_uv
  have hS_v : S v ≠ 0 := h_act (restrictToComponent_sub R S u0 u hu) h_uv
  dsimp [restrictToComponent]
  rw [if_pos h_u0_v]
  exact hS_v

lemma restrictToComponent_self {α : Type*} (R : α → α → Prop) (S : α → ZMod 2) (u0 : α)
    (h_refl : R u0 u0) (hS : S u0 ≠ 0) : restrictToComponent R S u0 u0 ≠ 0 := by
  dsimp [restrictToComponent]
  rw [if_pos h_refl]
  exact hS

lemma exists_ne_zero_of_fun_ne_zero {α : Type*} {f : α → ZMod 2} (h : f ≠ 0) :
    ∃ x : α, f x ≠ 0 := by
  by_contra h_all; push_neg at h_all; exact h (funext h_all)
lemma primal_subsyndrome_multiscale (k : ℕ)
    (e : (bdlIteratedBundled (k + 1)).Q → ZMod 2)
    (S2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (hS2 : syndrome (bdlIteratedBundled (k + 1)).code e = S2)
    (c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (v_base : (bdlIteratedBundled 1).M_X)
    (hc2_base : pushedSyndromePrimal k c2 v_base ≠ 0)
    (hc2_sub : ∀ u : (bdlIteratedBundled (k + 1)).M_X, c2 u ≠ 0 → S2 u ≠ 0)
    (hc2_closed : ∀ u v : (bdlIteratedBundled (k + 1)).M_X,
      c2 u ≠ 0 → MultiscaleClusterConnPrimal k S2 u v → c2 v ≠ 0) :
    IsMultiscaleIntactPercolatingClusterPrimal k c2 ∧
    (∀ u v : (bdlIteratedBundled (k + 1)).M_X,
      c2 u ≠ 0 → MultiscaleClusterConnPrimal k S2 u v → MultiscaleClusterConnPrimal k c2 u v) := by
  induction k with
  | zero =>
    let B := bdlIteratedBundled 0
    let B1 := bdlRandomStepX B
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled 0
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    let pcode0 := bdlPerturbedOfBundled B
    let pcode1 := bdlPerturbedOfBundled (dualBundled B1)
    let S1 := rxCleanedCoarseSyndrome pcode1 bdlSubdivPred S2
    let S0 := coarsePrimalSyndrome pcode0 bdlSubdivPred S1
    let Conn0_S : B.M_X → B.M_X → Prop := fun a b => S0 a ≠ 0 ∧ S0 b ≠ 0
    let Conn1_S : B1.M_X → B1.M_X → Prop := PrimalMultiscaleConn pcode0 bdlSubdivPred Conn0_S S0 S1
    have h_dual := dual_subsyndrome_step pcode1 bdlSubdivPred
      h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 e S2 hS2 Conn1_S c2 hc2_sub hc2_closed
    rcases h_dual with ⟨hc1_iff, h_step2, hc1_closed_raw, h_trans2⟩
    let c1 := rxCleanedCoarseSyndrome pcode1 bdlSubdivPred c2
    have hc1_sub : ∀ u : B1.M_X, c1 u ≠ 0 → S1 u ≠ 0 := fun u hu => ((hc1_iff u).mp hu).1
    have hc1_closed : ∀ u v : B1.M_X, c1 u ≠ 0 → Conn1_S u v → c1 v ≠ 0 :=
      hc1_closed_raw (fun _ _ ha h_conn => primalMultiscaleConn_active_right pcode0 bdlSubdivPred Conn0_S S0 S1 ha h_conn)
    let e1 : B1.Q → ZMod 2 := rxCleanedCoarseProj pcode1 bdlSubdivPred e
    have hS1_eq : syndrome (bdlCylinderStepX pcode0 bdlSubdivPred) e1 = S1 := by
      have h_rx := (rxCleanedCoarseProj_syndrome_eq pcode1 bdlSubdivPred
        h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 e).1
      exact h_rx.trans (congr_arg _ hS2)
    have h_prim := primal_subsyndrome_step pcode0 bdlSubdivPred e1 S1 hS1_eq Conn0_S c1 hc1_sub hc1_closed
    rcases h_prim with ⟨_, h_step1, _, h_trans1, _⟩
    let c0 := coarsePrimalSyndrome pcode0 bdlSubdivPred c1
    have hc2_ne : c2 ≠ 0 := fun h0 => hc2_base (by rw [h0]; rfl)
    have he0 : ∃ e0 : B.Q → ZMod 2, syndrome B.code e0 = c0 :=
      syndrome_bdlSurfaceSeedCode_surjective c0
    let Conn0_c : B.M_X → B.M_X → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
    have h_conn1 := h_trans1 Conn0_c (fun _ _ ha hb _ => ⟨ha, hb⟩)
    exact ⟨⟨hc2_ne, c0, c1, he0, h_step1, h_step2⟩,
      h_trans2 (PrimalMultiscaleConn pcode0 bdlSubdivPred Conn0_c c0 c1)
        (fun u v hu _ h_uv => h_conn1 u v hu h_uv)⟩
  | succ m ih =>
    let B := bdlIteratedBundled (m + 1)
    let B1 := bdlRandomStepX B
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    let pcode0 := bdlPerturbedOfBundled B
    let pcode1 := bdlPerturbedOfBundled (dualBundled B1)
    let S1 := rxCleanedCoarseSyndrome pcode1 bdlSubdivPred S2
    let S0 := coarsePrimalSyndrome pcode0 bdlSubdivPred S1
    let Conn0_S : B.M_X → B.M_X → Prop := MultiscaleClusterConnPrimal m S0
    let Conn1_S : B1.M_X → B1.M_X → Prop := PrimalMultiscaleConn pcode0 bdlSubdivPred Conn0_S S0 S1
    have h_dual := dual_subsyndrome_step pcode1 bdlSubdivPred
      h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 e S2 hS2 Conn1_S c2 hc2_sub hc2_closed
    rcases h_dual with ⟨hc1_iff, h_step2, hc1_closed_raw, h_trans2⟩
    let c1 := rxCleanedCoarseSyndrome pcode1 bdlSubdivPred c2
    have hc1_sub : ∀ u : B1.M_X, c1 u ≠ 0 → S1 u ≠ 0 := fun u hu => ((hc1_iff u).mp hu).1
    have hc1_closed : ∀ u v : B1.M_X, c1 u ≠ 0 → Conn1_S u v → c1 v ≠ 0 :=
      hc1_closed_raw (fun _ _ ha h_conn => primalMultiscaleConn_active_right pcode0 bdlSubdivPred Conn0_S S0 S1 ha h_conn)
    let e1 : B1.Q → ZMod 2 := rxCleanedCoarseProj pcode1 bdlSubdivPred e
    have hS1_eq : syndrome (bdlCylinderStepX pcode0 bdlSubdivPred) e1 = S1 := by
      have h_rx := (rxCleanedCoarseProj_syndrome_eq pcode1 bdlSubdivPred
        h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 e).1
      exact h_rx.trans (congr_arg _ hS2)
    have h_prim := primal_subsyndrome_step pcode0 bdlSubdivPred e1 S1 hS1_eq Conn0_S c1 hc1_sub hc1_closed
    rcases h_prim with ⟨hc0_iff, h_step1, hc0_closed_raw, h_trans1, _⟩
    let c0 := coarsePrimalSyndrome pcode0 bdlSubdivPred c1
    have hc0_sub : ∀ x0 : B.M_X, c0 x0 ≠ 0 → S0 x0 ≠ 0 := fun x0 hx0 => ((hc0_iff x0).mp hx0).1
    have hc0_closed : ∀ x_a x_b : B.M_X, c0 x_a ≠ 0 → Conn0_S x_a x_b → c0 x_b ≠ 0 :=
      hc0_closed_raw (fun _ _ ha h_conn => multiscaleClusterConnPrimal_active_right m S0 ha h_conn)
    let e0 : B.Q → ZMod 2 := projCylinderLZ pcode0 bdlSubdivPred e1
    have hS0_eq : syndrome B.code e0 = S0 := by
      have h_rz := (coarseSyndromeStepXMX_syndrome_eq pcode0 bdlSubdivPred e1).symm
      rw [hS1_eq] at h_rz
      exact h_rz
    obtain ⟨h_cl0, h_conn0⟩ := ih e0 S0 hS0_eq c0 hc2_base hc0_sub hc0_closed
    let Conn0_c : B.M_X → B.M_X → Prop := MultiscaleClusterConnPrimal m c0
    have h_conn1 := h_trans1 Conn0_c (fun x_a x_b ha _ h_ab => h_conn0 x_a x_b ha h_ab)
    exact ⟨⟨c0, c1, h_cl0, h_step1, h_step2⟩,
      h_trans2 (PrimalMultiscaleConn pcode0 bdlSubdivPred Conn0_c c0 c1)
        (fun u v hu _ h_uv => h_conn1 u v hu h_uv)⟩

lemma exists_upward_active_primal_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (e : BDLStepXQ pcode M → ZMod 2)
    (S1 : BDLStepXMX pcode M → ZMod 2)
    (hS1 : syndrome (bdlCylinderStepX pcode M) e = S1)
    (Conn0_S : M_X → M_X → Prop)
    (hConn0_act : ∀ x_a x_b : M_X, coarsePrimalSyndrome pcode M S1 x_a ≠ 0 →
      Conn0_S x_a x_b → coarsePrimalSyndrome pcode M S1 x_b ≠ 0)
    (u0 : M_X) (hu0 : coarsePrimalSyndrome pcode M S1 u0 ≠ 0) :
    ∃ u1 : BDLStepXMX pcode M, S1 u1 ≠ 0 ∧
      ∀ c1 : BDLStepXMX pcode M → ZMod 2,
        (∀ u, c1 u ≠ 0 → S1 u ≠ 0) →
        (∀ u v, c1 u ≠ 0 → PrimalMultiscaleConn pcode M Conn0_S (coarsePrimalSyndrome pcode M S1) S1 u v → c1 v ≠ 0) →
        c1 u1 ≠ 0 →
        (∀ x0 : M_X, coarsePrimalSyndrome pcode M c1 x0 ≠ 0 → coarsePrimalSyndrome pcode M S1 x0 ≠ 0) ∧
        (∀ x_a x_b : M_X, coarsePrimalSyndrome pcode M c1 x_a ≠ 0 → Conn0_S x_a x_b → coarsePrimalSyndrome pcode M c1 x_b ≠ 0) ∧
        coarsePrimalSyndrome pcode M c1 u0 ≠ 0 := by
  obtain ⟨u1, hu1_own, hS1_u1⟩ :=
    exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero pcode M S1 u0 hu0
  refine ⟨u1, hS1_u1, fun c1 hc1_sub hc1_closed hc1_u1 => ?_⟩
  have h_prim := primal_subsyndrome_step pcode M e S1 hS1 Conn0_S c1 hc1_sub hc1_closed
  exact ⟨fun x0 hx0 => ((h_prim.1 x0).mp hx0).1,
    h_prim.2.2.1 hConn0_act,
    (h_prim.1 u0).mpr ⟨hu0, u1, hc1_u1, hu1_own⟩⟩

lemma exists_upward_active_dual_step {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2)
    (S1 : BDLStepXMZ pcode M → ZMod 2)
    (hS1 : syndrome (dualCode (bdlCylinderStepX pcode M)) h = S1)
    (Conn0_S : M_Z → M_Z → Prop)
    (hConn0_act : ∀ z_a z_b : M_Z, rxCleanedCoarseSyndrome pcode M S1 z_a ≠ 0 →
      Conn0_S z_a z_b → rxCleanedCoarseSyndrome pcode M S1 z_b ≠ 0)
    (u1 : M_Z) (hu1 : rxCleanedCoarseSyndrome pcode M S1 u1 ≠ 0) :
    ∃ u2 : BDLStepXMZ pcode M, S1 u2 ≠ 0 ∧
      ∀ c1 : BDLStepXMZ pcode M → ZMod 2,
        (∀ u, c1 u ≠ 0 → S1 u ≠ 0) →
        (∀ u v, c1 u ≠ 0 → DualMultiscaleConn pcode M Conn0_S (rxCleanedCoarseSyndrome pcode M S1) S1 u v → c1 v ≠ 0) →
        c1 u2 ≠ 0 →
        (∀ z0 : M_Z, rxCleanedCoarseSyndrome pcode M c1 z0 ≠ 0 → rxCleanedCoarseSyndrome pcode M S1 z0 ≠ 0) ∧
        (∀ z_a z_b : M_Z, rxCleanedCoarseSyndrome pcode M c1 z_a ≠ 0 → Conn0_S z_a z_b → rxCleanedCoarseSyndrome pcode M c1 z_b ≠ 0) ∧
        rxCleanedCoarseSyndrome pcode M c1 u1 ≠ 0 := by
  obtain ⟨u2, hu2_pool, hS1_u2⟩ :=
    exists_active_in_fineTwoHopPool_singleton pcode M hov hq_z h_conn u1 h S1 hS1 hu1
  refine ⟨u2, hS1_u2, fun c1 hc1_sub hc1_closed hc1_u2 => ?_⟩
  have h_dual := dual_subsyndrome_step pcode M hov hq_z h_conn h S1 hS1 Conn0_S c1 hc1_sub hc1_closed
  exact ⟨fun z0 hz0 => ((h_dual.1 z0).mp hz0).1,
    h_dual.2.2.1 hConn0_act,
    (h_dual.1 u1).mpr ⟨hu1, u2, hc1_u2, hu2_pool⟩⟩

lemma exists_upward_active_primal (k : ℕ)
    (e : (bdlIteratedBundled (k + 1)).Q → ZMod 2)
    (S2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (hS2 : syndrome (bdlIteratedBundled (k + 1)).code e = S2)
    (v_base : (bdlIteratedBundled 1).M_X)
    (hv_base : pushedSyndromePrimal k S2 v_base ≠ 0) :
    ∃ u_top : (bdlIteratedBundled (k + 1)).M_X,
      S2 u_top ≠ 0 ∧
      ∀ c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2,
        (∀ u, c2 u ≠ 0 → S2 u ≠ 0) →
        (∀ u v, c2 u ≠ 0 → MultiscaleClusterConnPrimal k S2 u v → c2 v ≠ 0) →
        c2 u_top ≠ 0 →
        pushedSyndromePrimal k c2 v_base ≠ 0 := by
  induction k with
  | zero =>
    exact ⟨v_base, hv_base, fun _ _ _ hc2_top => hc2_top⟩
  | succ m ih =>
    let B := bdlIteratedBundled (m + 1)
    let B1 := bdlRandomStepX B
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    let pcode0 := bdlPerturbedOfBundled B
    let pcode1 := bdlPerturbedOfBundled (dualBundled B1)
    let S1 := rxCleanedCoarseSyndrome pcode1 bdlSubdivPred S2
    let S0 := coarsePrimalSyndrome pcode0 bdlSubdivPred S1
    let e1 : B1.Q → ZMod 2 := rxCleanedCoarseProj pcode1 bdlSubdivPred e
    have hS1_eq : syndrome (bdlCylinderStepX pcode0 bdlSubdivPred) e1 = S1 := by
      have h_rx := (rxCleanedCoarseProj_syndrome_eq pcode1 bdlSubdivPred
        h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 e).1
      exact h_rx.trans (congr_arg _ hS2)
    let e0 : B.Q → ZMod 2 := projCylinderLZ pcode0 bdlSubdivPred e1
    have hS0_eq : syndrome B.code e0 = S0 := by
      have h_rz := (coarseSyndromeStepXMX_syndrome_eq pcode0 bdlSubdivPred e1).symm
      rw [hS1_eq] at h_rz
      exact h_rz
    have hu0_ex := ih e0 S0 hS0_eq hv_base
    rcases hu0_ex with ⟨u0, hS0_u0, hu0_prop⟩
    let Conn0_S : B.M_X → B.M_X → Prop := MultiscaleClusterConnPrimal m S0
    let Conn1_S : B1.M_X → B1.M_X → Prop := PrimalMultiscaleConn pcode0 bdlSubdivPred Conn0_S S0 S1
    have hu1_ex := exists_upward_active_primal_step pcode0 bdlSubdivPred e1 S1 hS1_eq Conn0_S
      (fun _ _ ha h_conn => multiscaleClusterConnPrimal_active_right m S0 ha h_conn) u0 hS0_u0
    rcases hu1_ex with ⟨u1, hS1_u1, hu1_prop⟩
    have hu2_ex := exists_upward_active_dual_step pcode1 bdlSubdivPred
      h_inv_dB1.1.2 h_inv_dB1.2.2.2.1.2 h_inv_dB1.2.2.2.2.1 e S2 hS2 Conn1_S
      (fun _ _ ha h_conn => primalMultiscaleConn_active_right pcode0 bdlSubdivPred Conn0_S S0 S1 ha h_conn)
      u1 hS1_u1
    rcases hu2_ex with ⟨u2, hS2_u2, hu2_prop⟩
    refine @Exists.intro ((bdlIteratedBundled (m + 2)).M_X)
      (fun u_top => S2 u_top ≠ 0 ∧
        ∀ c2 : (bdlIteratedBundled (m + 2)).M_X → ZMod 2,
          (∀ u, c2 u ≠ 0 → S2 u ≠ 0) →
          (∀ u v, c2 u ≠ 0 → MultiscaleClusterConnPrimal (m + 1) S2 u v → c2 v ≠ 0) →
          c2 u_top ≠ 0 →
          pushedSyndromePrimal (m + 1) c2 v_base ≠ 0)
      u2 ⟨hS2_u2, fun c2 hc2_sub hc2_closed hc2_u2 => ?_⟩
    rcases hu2_prop c2 hc2_sub hc2_closed hc2_u2 with ⟨hc1_sub, hc1_closed, hc1_u1⟩
    rcases hu1_prop (rxCleanedCoarseSyndrome pcode1 bdlSubdivPred c2) hc1_sub hc1_closed hc1_u1 with
      ⟨hc0_sub, hc0_closed, hc0_u0⟩
    exact hu0_prop (coarsePrimalSyndrome pcode0 bdlSubdivPred (rxCleanedCoarseSyndrome pcode1 bdlSubdivPred c2))
      hc0_sub hc0_closed hc0_u0

section
attribute [local irreducible] bdlIteratedBundled

lemma exists_multiscaleIntactWitnessPrimal_of_upward_active (k : ℕ)
    (e : (bdlIteratedBundled (k + 1)).Q → ZMod 2)
    (S2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (hS2 : syndrome (bdlIteratedBundled (k + 1)).code e = S2)
    (v_base : (bdlIteratedBundled 1).M_X)
    (u_top : (bdlIteratedBundled (k + 1)).M_X)
    (hS2_top : S2 u_top ≠ 0)
    (hu_top_prop : ∀ c2 : (bdlIteratedBundled (k + 1)).M_X → ZMod 2,
      (∀ u, c2 u ≠ 0 → S2 u ≠ 0) →
      (∀ u v, c2 u ≠ 0 → MultiscaleClusterConnPrimal k S2 u v → c2 v ≠ 0) →
      c2 u_top ≠ 0 →
      pushedSyndromePrimal k c2 v_base ≠ 0) :
    ∃ c ∈ multiscaleIntactWitnessPoolPrimal k,
      ∀ m : (bdlIteratedBundled (k + 1)).M_X,
        c m ≠ 0 → S2 m ≠ 0 :=
  let c2 := restrictToComponent (MultiscaleClusterConnPrimal k S2) S2 u_top
  let hc2_sub : ∀ u : (bdlIteratedBundled (k + 1)).M_X, c2 u ≠ 0 → S2 u ≠ 0 :=
    restrictToComponent_sub (MultiscaleClusterConnPrimal k S2) S2 u_top
  let hc2_conn_top : ∀ u : (bdlIteratedBundled (k + 1)).M_X,
      c2 u ≠ 0 → MultiscaleClusterConnPrimal k S2 u_top u :=
    restrictToComponent_conn (MultiscaleClusterConnPrimal k S2) S2 u_top
  let hc2_closed : ∀ u v : (bdlIteratedBundled (k + 1)).M_X,
      c2 u ≠ 0 → MultiscaleClusterConnPrimal k S2 u v → c2 v ≠ 0 :=
    restrictToComponent_closed (MultiscaleClusterConnPrimal k S2) S2 u_top
      (multiscaleClusterConnPrimal_trans k S2)
      (multiscaleClusterConnPrimal_active_right k S2)
  let hc2_top : c2 u_top ≠ 0 :=
    restrictToComponent_self (MultiscaleClusterConnPrimal k S2) S2 u_top
      (multiscaleClusterConnPrimal_refl k S2 u_top) hS2_top
  let hc2_base : pushedSyndromePrimal k c2 v_base ≠ 0 :=
    hu_top_prop c2 hc2_sub hc2_closed hc2_top
  let h_sub := primal_subsyndrome_multiscale k e S2 hS2 c2 v_base hc2_base hc2_sub hc2_closed
  let h_conn_c2 : ∀ u v : (bdlIteratedBundled (k + 1)).M_X,
      c2 u ≠ 0 → c2 v ≠ 0 → MultiscaleClusterConnPrimal k c2 u v :=
    fun u v hu hv =>
      h_sub.2 u v hu
        (multiscaleClusterConnPrimal_trans k S2
          (multiscaleClusterConnPrimal_symm k S2 (hc2_conn_top u hu))
          (hc2_conn_top v hv))
  @Exists.intro ((bdlIteratedBundled (k + 1)).M_X → ZMod 2)
    (fun c => c ∈ multiscaleIntactWitnessPoolPrimal k ∧
      ∀ m : (bdlIteratedBundled (k + 1)).M_X,
        c m ≠ 0 → S2 m ≠ 0)
    c2 (And.intro (mem_multiscaleIntactWitnessPoolPrimal_of_isMultiscale k c2 h_sub.1 h_conn_c2) hc2_sub)

end

lemma exists_multiscaleIntactWitnessPrimal_of_pushedSyndrome_ne_zero (k : ℕ)
    (e : (bdlIteratedBundled (k + 1)).Q → ZMod 2)
    (h_ne : pushedSyndromePrimal k (syndrome (bdlIteratedBundled (k + 1)).code e) ≠ 0) :
    ∃ c ∈ multiscaleIntactWitnessPoolPrimal k,
      ∀ m : (bdlIteratedBundled (k + 1)).M_X,
        c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e m ≠ 0 :=
  (exists_ne_zero_of_fun_ne_zero h_ne).elim fun v_base hv_base =>
    (exists_upward_active_primal k e (syndrome (bdlIteratedBundled (k + 1)).code e) rfl v_base hv_base).elim
      fun u_top hu_top =>
        exists_multiscaleIntactWitnessPrimal_of_upward_active k e
          (syndrome (bdlIteratedBundled (k + 1)).code e) rfl v_base u_top hu_top.1 hu_top.2

lemma dualHalf_subsyndrome_multiscale (k : ℕ)
    (h1 : (bdlRandomStepX (bdlIteratedBundled k)).Q → ZMod 2)
    (S_top : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2)
    (hS_top : syndrome (dualCode (bdlRandomStepX (bdlIteratedBundled k)).code) h1 = S_top)
    (c_top : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2)
    (v_half0 : (bdlRandomStepX (bdlIteratedBundled 0)).M_Z)
    (hc_base : pushedSyndromeDualHalf k c_top v_half0 ≠ 0)
    (hc_sub : ∀ u : (bdlRandomStepX (bdlIteratedBundled k)).M_Z, c_top u ≠ 0 → S_top u ≠ 0)
    (hc_closed : ∀ u v : (bdlRandomStepX (bdlIteratedBundled k)).M_Z,
      c_top u ≠ 0 → MultiscaleClusterConnDualHalf k S_top u v → c_top v ≠ 0) :
    c_top ≠ 0 ∧
    IsMultiscaleIntactPercolatingClusterDualHalf k c_top ∧
    (∀ u v : (bdlRandomStepX (bdlIteratedBundled k)).M_Z,
      c_top u ≠ 0 → MultiscaleClusterConnDualHalf k S_top u v →
      MultiscaleClusterConnDualHalf k c_top u v) := by
  induction k with
  | zero =>
    let B0 := bdlIteratedBundled 0
    have h_inv_B0 : HasBDLConeInvariants B0 := hasBDLConeInvariants_bdlIteratedBundled 0
    let pcode0 := bdlPerturbedOfBundled B0
    let S0 := rxCleanedCoarseSyndrome pcode0 bdlSubdivPred S_top
    let Conn0_S : B0.M_Z → B0.M_Z → Prop := fun a b => S0 a ≠ 0 ∧ S0 b ≠ 0
    have h_dual := dual_subsyndrome_step pcode0 bdlSubdivPred
      h_inv_B0.1.2 h_inv_B0.2.2.2.1.2 h_inv_B0.2.2.2.2.1 h1 S_top hS_top Conn0_S c_top hc_sub hc_closed
    rcases h_dual with ⟨_, h_step, _, h_trans⟩
    let c0 := rxCleanedCoarseSyndrome pcode0 bdlSubdivPred c_top
    have hc_top_ne : c_top ≠ 0 := fun h0 => hc_base (by rw [h0]; rfl)
    have hh0 : ∃ h0 : B0.Q → ZMod 2, syndrome (dualCode B0.code) h0 = c0 :=
      syndrome_dual_bdlSurfaceSeedCode_surjective c0
    let Conn0_c : B0.M_Z → B0.M_Z → Prop := fun a b => c0 a ≠ 0 ∧ c0 b ≠ 0
    exact ⟨hc_top_ne, ⟨c0, hh0, h_step⟩, h_trans Conn0_c (fun _ _ ha hb _ => ⟨ha, hb⟩)⟩
  | succ m ih =>
    let B_prev := bdlIteratedBundled m
    let B_half := bdlRandomStepX B_prev
    let B_mid := bdlIteratedBundled (m + 1)
    have h_inv_prev : HasBDLConeInvariants B_prev := hasBDLConeInvariants_bdlIteratedBundled m
    have h_inv_half : HasBDLConeInvariants B_half :=
      hasBDLConeInvariants_bdlRandomStepX B_prev h_inv_prev
    have h_inv_dhalf : HasBDLConeInvariants (dualBundled B_half) :=
      hasBDLConeInvariants_dualBundled B_half h_inv_half
    have h_inv_mid : HasBDLConeInvariants B_mid := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    let pcode_half := bdlPerturbedOfBundled (dualBundled B_half)
    let pcode_mid := bdlPerturbedOfBundled B_mid
    let S_mid := rxCleanedCoarseSyndrome pcode_mid bdlSubdivPred S_top
    let S_prev := coarsePrimalSyndrome pcode_half bdlSubdivPred S_mid
    let Conn_prev_S : B_half.M_Z → B_half.M_Z → Prop := MultiscaleClusterConnDualHalf m S_prev
    let Conn_mid_S : B_mid.M_Z → B_mid.M_Z → Prop :=
      PrimalMultiscaleConn pcode_half bdlSubdivPred Conn_prev_S S_prev S_mid
    have h_dual := dual_subsyndrome_step pcode_mid bdlSubdivPred
      h_inv_mid.1.2 h_inv_mid.2.2.2.1.2 h_inv_mid.2.2.2.2.1 h1 S_top hS_top Conn_mid_S c_top hc_sub hc_closed
    rcases h_dual with ⟨hc_mid_iff, h_step2, hc_mid_closed_raw, h_trans2⟩
    let c_mid := rxCleanedCoarseSyndrome pcode_mid bdlSubdivPred c_top
    have hc_mid_sub : ∀ u : B_mid.M_Z, c_mid u ≠ 0 → S_mid u ≠ 0 :=
      fun u hu => ((hc_mid_iff u).mp hu).1
    have hc_mid_closed : ∀ u v : B_mid.M_Z, c_mid u ≠ 0 → Conn_mid_S u v → c_mid v ≠ 0 :=
      hc_mid_closed_raw (fun _ _ ha h_conn =>
        primalMultiscaleConn_active_right pcode_half bdlSubdivPred Conn_prev_S S_prev S_mid ha h_conn)
    let h_mid : B_mid.Q → ZMod 2 := rxCleanedCoarseProj pcode_mid bdlSubdivPred h1
    have hS_mid_eq : syndrome (bdlCylinderStepX pcode_half bdlSubdivPred) h_mid = S_mid := by
      have h_rx := (rxCleanedCoarseProj_syndrome_eq pcode_mid bdlSubdivPred
        h_inv_mid.1.2 h_inv_mid.2.2.2.1.2 h_inv_mid.2.2.2.2.1 h1).1
      exact h_rx.trans (congr_arg _ hS_top)
    have h_prim := primal_subsyndrome_step pcode_half bdlSubdivPred h_mid S_mid hS_mid_eq
      Conn_prev_S c_mid hc_mid_sub hc_mid_closed
    rcases h_prim with ⟨hc_prev_iff, h_step1, hc_prev_closed_raw, h_trans1, _⟩
    let c_prev := coarsePrimalSyndrome pcode_half bdlSubdivPred c_mid
    have hc_prev_sub : ∀ x0 : B_half.M_Z, c_prev x0 ≠ 0 → S_prev x0 ≠ 0 :=
      fun x0 hx0 => ((hc_prev_iff x0).mp hx0).1
    have hc_prev_closed : ∀ x_a x_b : B_half.M_Z, c_prev x_a ≠ 0 → Conn_prev_S x_a x_b → c_prev x_b ≠ 0 :=
      hc_prev_closed_raw (fun _ _ ha h_conn => multiscaleClusterConnDualHalf_active_right m S_prev ha h_conn)
    let h_prev : B_half.Q → ZMod 2 := projCylinderLZ pcode_half bdlSubdivPred h_mid
    have hS_prev_eq : syndrome (dualCode B_half.code) h_prev = S_prev := by
      have h_rz := (coarseSyndromeStepXMX_syndrome_eq pcode_half bdlSubdivPred h_mid).symm
      rw [hS_mid_eq] at h_rz
      exact h_rz
    obtain ⟨hc_prev_ne, h_cl_prev, h_conn_prev⟩ :=
      ih h_prev S_prev hS_prev_eq c_prev hc_base hc_prev_sub hc_prev_closed
    have hc_top_ne : c_top ≠ 0 := by
      obtain ⟨x0, hx0⟩ : ∃ x0, c_prev x0 ≠ 0 := by
        by_contra h_all; push_neg at h_all; exact hc_prev_ne (funext h_all)
      rcases (hc_prev_iff x0).mp hx0 with ⟨_, u1, hu1_ne, _⟩
      rcases (hc_mid_iff u1).mp hu1_ne with ⟨_, u2, hu2_ne, _⟩
      exact fun h0 => hu2_ne (by rw [h0]; rfl)
    let Conn_prev_c : B_half.M_Z → B_half.M_Z → Prop := MultiscaleClusterConnDualHalf m c_prev
    have h_conn_mid := h_trans1 Conn_prev_c (fun x_a x_b ha _ h_ab => h_conn_prev x_a x_b ha h_ab)
    exact ⟨hc_top_ne,
      ⟨hc_top_ne, c_prev, c_mid, hc_prev_ne, h_cl_prev, h_step1, h_step2⟩,
      h_trans2 (PrimalMultiscaleConn pcode_half bdlSubdivPred Conn_prev_c c_prev c_mid)
        (fun u v hu _ h_uv => h_conn_mid u v hu h_uv)⟩

lemma exists_upward_active_dualHalf (k : ℕ)
    (h1 : (bdlRandomStepX (bdlIteratedBundled k)).Q → ZMod 2)
    (S_top : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2)
    (hS_top : syndrome (dualCode (bdlRandomStepX (bdlIteratedBundled k)).code) h1 = S_top)
    (v_half0 : (bdlRandomStepX (bdlIteratedBundled 0)).M_Z)
    (hv_base : pushedSyndromeDualHalf k S_top v_half0 ≠ 0) :
    ∃ u_top : (bdlRandomStepX (bdlIteratedBundled k)).M_Z,
      S_top u_top ≠ 0 ∧
      ∀ c_top : (bdlRandomStepX (bdlIteratedBundled k)).M_Z → ZMod 2,
        (∀ u, c_top u ≠ 0 → S_top u ≠ 0) →
        (∀ u v, c_top u ≠ 0 → MultiscaleClusterConnDualHalf k S_top u v → c_top v ≠ 0) →
        c_top u_top ≠ 0 →
        pushedSyndromeDualHalf k c_top v_half0 ≠ 0 := by
  induction k with
  | zero =>
    exact ⟨v_half0, hv_base, fun _ _ _ hc_top => hc_top⟩
  | succ m ih =>
    let B_prev := bdlIteratedBundled m
    let B_half := bdlRandomStepX B_prev
    let B_mid := bdlIteratedBundled (m + 1)
    have h_inv_prev : HasBDLConeInvariants B_prev := hasBDLConeInvariants_bdlIteratedBundled m
    have h_inv_half : HasBDLConeInvariants B_half :=
      hasBDLConeInvariants_bdlRandomStepX B_prev h_inv_prev
    have h_inv_dhalf : HasBDLConeInvariants (dualBundled B_half) :=
      hasBDLConeInvariants_dualBundled B_half h_inv_half
    have h_inv_mid : HasBDLConeInvariants B_mid := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    let pcode_half := bdlPerturbedOfBundled (dualBundled B_half)
    let pcode_mid := bdlPerturbedOfBundled B_mid
    let S_mid := rxCleanedCoarseSyndrome pcode_mid bdlSubdivPred S_top
    let S_prev := coarsePrimalSyndrome pcode_half bdlSubdivPred S_mid
    let h_mid : B_mid.Q → ZMod 2 := rxCleanedCoarseProj pcode_mid bdlSubdivPred h1
    have hS_mid_eq : syndrome (bdlCylinderStepX pcode_half bdlSubdivPred) h_mid = S_mid := by
      have h_rx := (rxCleanedCoarseProj_syndrome_eq pcode_mid bdlSubdivPred
        h_inv_mid.1.2 h_inv_mid.2.2.2.1.2 h_inv_mid.2.2.2.2.1 h1).1
      exact h_rx.trans (congr_arg _ hS_top)
    let h_prev : B_half.Q → ZMod 2 := projCylinderLZ pcode_half bdlSubdivPred h_mid
    have hS_prev_eq : syndrome (dualCode B_half.code) h_prev = S_prev := by
      have h_rz := (coarseSyndromeStepXMX_syndrome_eq pcode_half bdlSubdivPred h_mid).symm
      rw [hS_mid_eq] at h_rz
      exact h_rz
    have hu0_ex := ih h_prev S_prev hS_prev_eq hv_base
    rcases hu0_ex with ⟨u0, hS_prev_u0, hu0_prop⟩
    let Conn_prev_S : B_half.M_Z → B_half.M_Z → Prop := MultiscaleClusterConnDualHalf m S_prev
    let Conn_mid_S : B_mid.M_Z → B_mid.M_Z → Prop :=
      PrimalMultiscaleConn pcode_half bdlSubdivPred Conn_prev_S S_prev S_mid
    have hu1_ex := exists_upward_active_primal_step pcode_half bdlSubdivPred h_mid S_mid hS_mid_eq Conn_prev_S
      (fun _ _ ha h_conn => multiscaleClusterConnDualHalf_active_right m S_prev ha h_conn) u0 hS_prev_u0
    rcases hu1_ex with ⟨u1, hS_mid_u1, hu1_prop⟩
    have hu2_ex := exists_upward_active_dual_step pcode_mid bdlSubdivPred
      h_inv_mid.1.2 h_inv_mid.2.2.2.1.2 h_inv_mid.2.2.2.2.1 h1 S_top hS_top Conn_mid_S
      (fun _ _ ha h_conn => primalMultiscaleConn_active_right pcode_half bdlSubdivPred Conn_prev_S S_prev S_mid ha h_conn)
      u1 hS_mid_u1
    rcases hu2_ex with ⟨u2, hS_top_u2, hu2_prop⟩
    refine @Exists.intro ((bdlRandomStepX (bdlIteratedBundled (m + 1))).M_Z)
      (fun u_top => S_top u_top ≠ 0 ∧
        ∀ c_top : (bdlRandomStepX (bdlIteratedBundled (m + 1))).M_Z → ZMod 2,
          (∀ u, c_top u ≠ 0 → S_top u ≠ 0) →
          (∀ u v, c_top u ≠ 0 → MultiscaleClusterConnDualHalf (m + 1) S_top u v → c_top v ≠ 0) →
          c_top u_top ≠ 0 →
          pushedSyndromeDualHalf (m + 1) c_top v_half0 ≠ 0)
      u2 ⟨hS_top_u2, fun c_top hc_sub hc_closed hc_u2 => ?_⟩
    let c_mid : B_mid.M_Z → ZMod 2 := rxCleanedCoarseSyndrome pcode_mid bdlSubdivPred c_top
    let c_prev : B_half.M_Z → ZMod 2 := coarsePrimalSyndrome pcode_half bdlSubdivPred c_mid
    rcases hu2_prop c_top hc_sub hc_closed hc_u2 with ⟨hc_mid_sub, hc_mid_closed, hc_mid_u1⟩
    rcases hu1_prop c_mid hc_mid_sub hc_mid_closed hc_mid_u1 with
      ⟨hc_prev_sub, hc_prev_closed, hc_prev_u0⟩
    exact hu0_prop c_prev hc_prev_sub hc_prev_closed hc_prev_u0

lemma exists_multiscaleIntactWitnessDual_of_pushedSyndrome_ne_zero (k : ℕ)
    (h : (bdlIteratedBundled (k + 1)).Q → ZMod 2)
    (h_ne : pushedSyndromeDualHalf k
      (coarsePrimalSyndrome
        (bdlPerturbedOfBundled (dualBundled (bdlRandomStepX (bdlIteratedBundled k))))
        bdlSubdivPred
        (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h)) ≠ 0) :
    ∃ c ∈ multiscaleIntactWitnessPoolDual k,
      ∀ m : (bdlIteratedBundled (k + 1)).M_Z,
        c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h m ≠ 0 := by
  let B := bdlIteratedBundled k
  let B1 := bdlRandomStepX B
  let pcode1 := bdlPerturbedOfBundled (dualBundled B1)
  let S2 := syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h
  let S1 := coarsePrimalSyndrome pcode1 bdlSubdivPred S2
  let h1 : B1.Q → ZMod 2 := projCylinderLZ pcode1 bdlSubdivPred h
  have hS1_eq : syndrome (dualCode B1.code) h1 = S1 :=
    (coarseSyndromeStepXMX_syndrome_eq pcode1 bdlSubdivPred h).symm
  have hv_ex := exists_ne_zero_of_fun_ne_zero h_ne
  rcases hv_ex with ⟨v_half0, hv_base⟩
  have hu1_ex := exists_upward_active_dualHalf k h1 S1 hS1_eq v_half0 hv_base
  rcases hu1_ex with ⟨u1, hS1_u1, hu1_prop⟩
  have hu2_ex :=
    exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero pcode1 bdlSubdivPred S2 u1 hS1_u1
  rcases hu2_ex with ⟨u2, hu2_own, hS2_u2⟩
  let c2 := restrictToComponent (MultiscaleClusterConnDual k S2) S2 u2
  have hc2_sub : ∀ u : (bdlIteratedBundled (k + 1)).M_Z, c2 u ≠ 0 → S2 u ≠ 0 :=
    restrictToComponent_sub (MultiscaleClusterConnDual k S2) S2 u2
  have hc2_conn_u2 : ∀ u : (bdlIteratedBundled (k + 1)).M_Z,
      c2 u ≠ 0 → MultiscaleClusterConnDual k S2 u2 u :=
    restrictToComponent_conn (MultiscaleClusterConnDual k S2) S2 u2
  have hc2_closed : ∀ u v : (bdlIteratedBundled (k + 1)).M_Z,
      c2 u ≠ 0 → MultiscaleClusterConnDual k S2 u v → c2 v ≠ 0 :=
    restrictToComponent_closed (MultiscaleClusterConnDual k S2) S2 u2
      (fun h1 h2 => h1.trans h2)
      (multiscaleClusterConnDual_active_right k S2)
  have hc2_u2 : c2 u2 ≠ 0 :=
    restrictToComponent_self (MultiscaleClusterConnDual k S2) S2 u2
      Relation.ReflTransGen.refl hS2_u2
  have hc2_ne : c2 ≠ 0 := fun h0 => hc2_u2 (by rw [h0]; rfl)
  let Conn1_S : B1.M_Z → B1.M_Z → Prop := MultiscaleClusterConnDualHalf k S1
  have h_prim := primal_subsyndrome_step pcode1 bdlSubdivPred h S2 rfl Conn1_S c2 hc2_sub hc2_closed
  let c1 := coarsePrimalSyndrome pcode1 bdlSubdivPred c2
  have hc1_sub : ∀ x0 : B1.M_Z, c1 x0 ≠ 0 → S1 x0 ≠ 0 :=
    fun x0 hx0 => ((h_prim.1 x0).mp hx0).1
  have hc1_closed : ∀ x_a x_b : B1.M_Z, c1 x_a ≠ 0 → Conn1_S x_a x_b → c1 x_b ≠ 0 :=
    h_prim.2.2.1 (fun _ _ ha h_conn => multiscaleClusterConnDualHalf_active_right k S1 ha h_conn)
  have hc1_u1 : c1 u1 ≠ 0 :=
    coarsePrimalSyndrome_ne_zero_of_witness pcode1 bdlSubdivPred h_prim.1 u1 hS1_u1 u2 hc2_u2 hu2_own
  have hc1_base : pushedSyndromeDualHalf k c1 v_half0 ≠ 0 :=
    hu1_prop c1 hc1_sub hc1_closed hc1_u1
  have h_dh := dualHalf_subsyndrome_multiscale k h1 S1 hS1_eq c1 v_half0 hc1_base hc1_sub hc1_closed
  have h_own : c1 ≠ 0 → ∀ mX : (bdlIteratedBundled (k + 1)).M_Z,
      c2 mX ≠ 0 → c1 (stepXMXOwnerX pcode1 bdlSubdivPred mX) ≠ 0 := by
    intro _ mX hmX
    exact h_prim.2.2.2.2 u2 mX hc2_u2 (hu2_own.symm ▸ hS1_u1) (hc2_conn_u2 mX hmX)
  have h_conn_c2 : ∀ u v : (bdlIteratedBundled (k + 1)).M_Z,
      c2 u ≠ 0 → c2 v ≠ 0 → MultiscaleClusterConnDual k c2 u v :=
    fun u v hu hv =>
      h_prim.2.2.2.1 (MultiscaleClusterConnDualHalf k c1)
        (fun x_a x_b ha _ h_ab => h_dh.2.2 x_a x_b ha h_ab)
        u v hu ((multiscaleClusterConnDual_symm k S2 (hc2_conn_u2 u hu)).trans (hc2_conn_u2 v hv))
  exact @Exists.intro ((bdlIteratedBundled (k + 1)).M_Z → ZMod 2)
    (fun c => c ∈ multiscaleIntactWitnessPoolDual k ∧
      ∀ m : (bdlIteratedBundled (k + 1)).M_Z,
        c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h m ≠ 0)
    c2 ⟨mem_multiscaleIntactWitnessPoolDual_of_isMultiscale k c2
      ⟨hc2_ne, c1, h_dh.2.1, h_prim.2.1, h_own, h_conn_c2⟩, hc2_sub⟩

/-! ### Single-Step Ball and Parity Projection Lemmas and Base-Scale Filling -/

lemma stepX_primal_proj_ball_and_parity (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (L_X : B.Q → ZMod 2)
    (ψ_0 : (B.M_X → ZMod 2) → ZMod 2)
    (x0 : Point3D) {r : ℝ} (hr0 : 0 ≤ r)
    (e e' : (bdlRandomStepX B).Q → ZMod 2)
    (h_diff : ∀ q : (bdlRandomStepX B).Q,
      e q ≠ e' q → (bdlRandomStepX B).code.posQ q ∈ ball3D x0 r)
    (h_disc : rzCoarseParityRule (bdlPerturbedOfBundled B) bdlSubdivPred ψ_0
        (syndrome (bdlRandomStepX B).code e') + dualPairing (stepXLX B L_X) e' ≠
      rzCoarseParityRule (bdlPerturbedOfBundled B) bdlSubdivPred ψ_0
        (syndrome (bdlRandomStepX B).code e) + dualPairing (stepXLX B L_X) e) :
    let pcode := bdlPerturbedOfBundled B
    let e0 := projCylinderLZ pcode bdlSubdivPred e
    let e0' := projCylinderLZ pcode bdlSubdivPred e'
    syndrome B.code e0 = coarsePrimalSyndrome pcode bdlSubdivPred (syndrome (bdlRandomStepX B).code e) ∧
    syndrome B.code e0' = coarsePrimalSyndrome pcode bdlSubdivPred (syndrome (bdlRandomStepX B).code e') ∧
    (∀ q0 : B.Q, e0 q0 ≠ e0' q0 →
      B.code.posQ q0 ∈ ball3D (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003)) ∧
    (ψ_0 (syndrome B.code e0') + dualPairing L_X e0' ≠
      ψ_0 (syndrome B.code e0) + dualPairing L_X e0) := by
  let pcode := bdlPerturbedOfBundled B
  let M := bdlSubdivPred
  have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
  have hlam_ne : (bdlLambda : ℝ) ≠ 0 := ne_of_gt hlam_pos
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  let c := bdlLLLPerturbation B
  let D_edge : ℝ := 2001 * (bdlLambda : ℝ)
  have hD : HasCoarseEdgeBound pcode D_edge := by
    have hD_raw := hasCoarseEdgeBound_of_validLLLPerturbation B h_valid
    have h_eq : (2 * bdlAlpha + 1) * (bdlLambda : ℝ) = D_edge := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; ring
    rwa [h_eq] at hD_raw
  have h_alpha_nonneg : (0 : ℝ) ≤ bdlAlpha := by dsimp [bdlAlpha, bdlAlphaNat]; norm_num
  have h_rad_p : (r + D_edge) / (bdlLambda : ℝ) + bdlAlpha ≤ r / (bdlLambda : ℝ) + 7003 := by
    dsimp [D_edge, bdlAlpha, bdlAlphaNat]; field_simp [hlam_ne]; linarith
  have hr_div_nonneg : 0 ≤ (r + D_edge) / (bdlLambda : ℝ) + bdlAlpha :=
    add_nonneg (div_nonneg (by linarith [hD.1]) (le_of_lt hlam_pos)) h_alpha_nonneg
  refine ⟨(coarseSyndromeStepXMX_syndrome_eq pcode M e).symm,
    (coarseSyndromeStepXMX_syndrome_eq pcode M e').symm, ?_, ?_⟩
  · intro q0 hq0_ne
    have h_in_pert := projCylinderLZ_diff_in_ball pcode M hD x0 hr0 e e' h_diff q0 hq0_ne
    have h_in_coarse := perturb_point_mem_coarse_ball x0 (B.code.posQ q0) (c.1 q0)
      bdlLambda bdlLambda_pos (by linarith [hD.1]) h_alpha_nonneg (le_of_eq (h_valid.1 q0)) h_in_pert
    exact ball3D_mono _ hr_div_nonneg h_rad_p h_in_coarse
  · have h_disc_e := rzCoarseParityRule_discrepancy_eq pcode M ψ_0 L_X e
    have h_disc_e' := rzCoarseParityRule_discrepancy_eq pcode M ψ_0 L_X e'
    intro h_eq
    exact h_disc (h_disc_e'.trans (h_eq.trans h_disc_e.symm))

lemma stepX_dual_proj_ball_and_parity (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (L_Z : B.Q → ZMod 2)
    (ψ_0 : (B.M_Z → ZMod 2) → ZMod 2)
    (x0 : Point3D) {r : ℝ} (hr0 : 0 ≤ r)
    (h h' : (bdlRandomStepX B).Q → ZMod 2)
    (h_diff : ∀ q : (bdlRandomStepX B).Q,
      h q ≠ h' q → (bdlRandomStepX B).code.posQ q ∈ ball3D x0 r)
    (h_disc : rxCleanedParityRule (bdlPerturbedOfBundled B) bdlSubdivPred ψ_0 L_Z
        (syndrome (dualCode (bdlRandomStepX B).code) h') + dualPairing (stepXLZ B L_Z) h' ≠
      rxCleanedParityRule (bdlPerturbedOfBundled B) bdlSubdivPred ψ_0 L_Z
        (syndrome (dualCode (bdlRandomStepX B).code) h) + dualPairing (stepXLZ B L_Z) h) :
    let pcode := bdlPerturbedOfBundled B
    let h0 := rxCleanedCoarseProj pcode bdlSubdivPred h
    let h0' := rxCleanedCoarseProj pcode bdlSubdivPred h'
    syndrome (dualCode B.code) h0 =
      rxCleanedCoarseSyndrome pcode bdlSubdivPred (syndrome (dualCode (bdlRandomStepX B).code) h) ∧
    syndrome (dualCode B.code) h0' =
      rxCleanedCoarseSyndrome pcode bdlSubdivPred (syndrome (dualCode (bdlRandomStepX B).code) h') ∧
    (∀ q0 : B.Q, h0 q0 ≠ h0' q0 →
      B.code.posQ q0 ∈ ball3D (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003)) ∧
    (ψ_0 (syndrome (dualCode B.code) h0') + dualPairing L_Z h0' ≠
      ψ_0 (syndrome (dualCode B.code) h0) + dualPairing L_Z h0) := by
  let pcode := bdlPerturbedOfBundled B
  let M := bdlSubdivPred
  have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
  have hlam_ne : (bdlLambda : ℝ) ≠ 0 := ne_of_gt hlam_pos
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  let c := bdlLLLPerturbation B
  let D_edge : ℝ := 2001 * (bdlLambda : ℝ)
  have hD : HasCoarseEdgeBound pcode D_edge := by
    have hD_raw := hasCoarseEdgeBound_of_validLLLPerturbation B h_valid
    have h_eq : (2 * bdlAlpha + 1) * (bdlLambda : ℝ) = D_edge := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; ring
    rwa [h_eq] at hD_raw
  have h_alpha_nonneg : (0 : ℝ) ≤ bdlAlpha := by dsimp [bdlAlpha, bdlAlphaNat]; norm_num
  have h_rad_d : (r + 3 * D_edge) / (bdlLambda : ℝ) + bdlAlpha ≤ r / (bdlLambda : ℝ) + 7003 := by
    dsimp [D_edge, bdlAlpha, bdlAlphaNat]; field_simp [hlam_ne]; linarith
  have hr_div_nonneg : 0 ≤ (r + 3 * D_edge) / (bdlLambda : ℝ) + bdlAlpha :=
    add_nonneg (div_nonneg (by linarith [hD.1]) (le_of_lt hlam_pos)) h_alpha_nonneg
  refine ⟨(rxCleanedCoarseProj_syndrome_eq pcode M h_inv.1.2 h_inv.2.2.2.1.2 h_inv.2.2.2.2.1 h).1,
    (rxCleanedCoarseProj_syndrome_eq pcode M h_inv.1.2 h_inv.2.2.2.1.2 h_inv.2.2.2.2.1 h').1,
    ?_, ?_⟩
  · intro q0 hq0_ne
    have h_in_pert := rxCleanedCoarseProj_diff_in_ball pcode M hD x0 hr0 h h' h_diff q0 hq0_ne
    have h_in_coarse := perturb_point_mem_coarse_ball x0 (B.code.posQ q0) (c.1 q0)
      bdlLambda bdlLambda_pos (by linarith [hD.1]) h_alpha_nonneg (le_of_eq (h_valid.1 q0)) h_in_pert
    exact ball3D_mono _ hr_div_nonneg h_rad_d h_in_coarse
  · have h_disc_h := rxCleanedParityRule_discrepancy_eq pcode M h_inv.1.2 h_inv.2.2.2.1.2 h_inv.2.2.2.2.1 ψ_0 L_Z h
    have h_disc_h' := rxCleanedParityRule_discrepancy_eq pcode M h_inv.1.2 h_inv.2.2.2.1.2 h_inv.2.2.2.2.1 ψ_0 L_Z h'
    intro h_eq
    exact h_disc (h_disc_h'.trans (h_eq.trans h_disc_h.symm))

lemma syndrome_ne_zero_or_of_ball_filling {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_X : Q → ZMod 2) (x0 : Point3D) (r R_fill : ℝ)
    (h_syn_X : syndrome (dualCode code) L_X = 0)
    (h_fill : globalStabilizersInBall code x0 r ⊆ locallyGeneratedInBall code x0 R_fill)
    (e e' : Q → ZMod 2)
    (h_diff : ∀ q : Q, e q ≠ e' q → code.posQ q ∈ ball3D x0 r)
    (h_disc : dualPairing L_X e' ≠ dualPairing L_X e) :
    syndrome code e ≠ 0 ∨ syndrome code e' ≠ 0 := by
  by_contra h_none
  push_neg at h_none
  rcases h_none with ⟨he_zero, he'_zero⟩
  let g : Q → ZMod 2 := e' + e
  have hg_syn : syndrome code g = 0 := by
    dsimp [g]; rw [map_add, he'_zero, he_zero, add_zero]
  have hg_supp : supp1 code g ⊆ ball3D x0 r := by
    intro p ⟨q, hq_ne, hp⟩
    subst hp
    apply h_diff q
    intro h_eq
    apply hq_ne
    dsimp [g]; rw [h_eq]; exact zmod2_add_self (e' q)
  obtain ⟨c2, _, hc2_gen⟩ := h_fill ⟨hg_syn, hg_supp⟩
  have h_pair_zero : dualPairing L_X g = 0 := by
    rw [← hc2_gen]
    exact dualPairing_checkGen_zero code c2 L_X h_syn_X
  rw [dualPairing_add_right_zmod2 L_X e' e] at h_pair_zero
  have h_alg : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h_disc (h_alg _ _ h_pair_zero)

lemma primal_pushedSyndrome_ne_zero_of_ball_discrepancy (k : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr_hi : scaleDownRadius (2 * k) r ≤ 7015)
    (e e' : (bdlIteratedBundled (k + 1)).Q → ZMod 2) (x0 : Point3D)
    (h_diff : ∀ q : (bdlIteratedBundled (k + 1)).Q,
      e q ≠ e' q → (bdlIteratedBundled (k + 1)).code.posQ q ∈ ball3D x0 r)
    (h_disc : multiscaleParityRulePrimal k (syndrome (bdlIteratedBundled (k + 1)).code e') +
        dualPairing (bdlIteratedLX (k + 1)) e' ≠
      multiscaleParityRulePrimal k (syndrome (bdlIteratedBundled (k + 1)).code e) +
        dualPairing (bdlIteratedLX (k + 1)) e) :
    pushedSyndromePrimal k (syndrome (bdlIteratedBundled (k + 1)).code e) ≠ 0 ∨
    pushedSyndromePrimal k (syndrome (bdlIteratedBundled (k + 1)).code e') ≠ 0 := by
  induction k generalizing r x0 with
  | zero =>
    dsimp [scaleDownRadius] at hr_hi
    have h_disc' : dualPairing (bdlIteratedLX 1) e' ≠ dualPairing (bdlIteratedLX 1) e := by
      simpa [multiscaleParityRulePrimal] using h_disc
    exact syndrome_ne_zero_or_of_ball_filling
      (bdlIteratedBundled 1).code (bdlIteratedLX 1) x0 r bdlBaseFillingRadius
      (hasUniqueLogicalHomology_bdlIterated 1).h_syn_X
      (bdlHalfStep_subcylinder_filling 0 x0 hr0 hr_hi).1
      e e' h_diff h_disc'
  | succ m ih =>
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
    let r1 : ℝ := r / (bdlLambda : ℝ) + 7003
    let r2 : ℝ := r1 / (bdlLambda : ℝ) + 7003
    have hr1 : 0 ≤ r1 := add_nonneg (div_nonneg hr0 (le_of_lt hlam_pos)) (by norm_num)
    have hr2 : 0 ≤ r2 := add_nonneg (div_nonneg hr1 (le_of_lt hlam_pos)) (by norm_num)
    have h_sd_eq : scaleDownRadius (2 * (m + 1)) r = scaleDownRadius (2 * m) r2 := by
      have h_2m : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [h_2m]; rfl
    rw [h_sd_eq] at hr_hi
    let B := bdlIteratedBundled (m + 1)
    let B1 := bdlRandomStepX B
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    let ψ1 := rzCoarseParityRule (bdlPerturbedOfBundled B) bdlSubdivPred (multiscaleParityRulePrimal m)
    obtain ⟨he1_syn, he1'_syn, h_diff1, h_disc1⟩ :=
      stepX_dual_proj_ball_and_parity (dualBundled B1) h_inv_dB1
        (stepXLX B (bdlIteratedLX (m + 1))) ψ1 x0 hr0 e e' h_diff h_disc
    let e1 := rxCleanedCoarseProj (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred e
    let e1' := rxCleanedCoarseProj (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred e'
    obtain ⟨he0_syn, he0'_syn, h_diff0, h_disc0⟩ :=
      stepX_primal_proj_ball_and_parity B h_inv_B
        (bdlIteratedLX (m + 1)) (multiscaleParityRulePrimal m)
        (fun axis => x0 axis / (bdlLambda : ℝ)) hr1 e1 e1' h_diff1 h_disc1
    let e0 := projCylinderLZ (bdlPerturbedOfBundled B) bdlSubdivPred e1
    let e0' := projCylinderLZ (bdlPerturbedOfBundled B) bdlSubdivPred e1'
    have h_res := ih hr2 hr_hi e0 e0' _ h_diff0 h_disc0
    have h_eq_e : syndrome B.code e0 =
        coarsePrimalSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred
          (rxCleanedCoarseSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
            (syndrome (bdlIteratedBundled (m + 2)).code e)) :=
      he0_syn.trans (congr_arg _ he1_syn)
    have h_eq_e' : syndrome B.code e0' =
        coarsePrimalSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred
          (rxCleanedCoarseSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
            (syndrome (bdlIteratedBundled (m + 2)).code e')) :=
      he0'_syn.trans (congr_arg _ he1'_syn)
    rwa [h_eq_e, h_eq_e'] at h_res

lemma dual_pushedSyndrome_ne_zero_of_ball_discrepancy (k : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr_hi : scaleDownRadius (2 * k) r ≤ 7015)
    (h h' : (bdlIteratedBundled (k + 1)).Q → ZMod 2) (x0 : Point3D)
    (h_diff : ∀ q : (bdlIteratedBundled (k + 1)).Q,
      h q ≠ h' q → (dualCode (bdlIteratedBundled (k + 1)).code).posQ q ∈ ball3D x0 r)
    (h_disc : multiscaleParityRuleDual k (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h') +
        dualPairing (bdlIteratedLZ (k + 1)) h' ≠
      multiscaleParityRuleDual k (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h) +
        dualPairing (bdlIteratedLZ (k + 1)) h) :
    let B1 := bdlRandomStepX (bdlIteratedBundled k)
    let pcode1 := bdlPerturbedOfBundled (dualBundled B1)
    pushedSyndromeDualHalf k
      (coarsePrimalSyndrome pcode1 bdlSubdivPred
        (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h)) ≠ 0 ∨
    pushedSyndromeDualHalf k
      (coarsePrimalSyndrome pcode1 bdlSubdivPred
        (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h')) ≠ 0 := by
  induction k generalizing r x0 with
  | zero =>
    dsimp [scaleDownRadius] at hr_hi
    dsimp [multiscaleParityRuleDual] at h_disc
    let B0 := bdlIteratedBundled 0
    let B1 := bdlRandomStepX B0
    have h_inv_B0 : HasBDLConeInvariants B0 := hasBDLConeInvariants_bdlIteratedBundled 0
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B0 h_inv_B0
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    let pcode1 := bdlPerturbedOfBundled (dualBundled B1)
    have h_disc' : rzCoarseParityRule pcode1 bdlSubdivPred (fun _ => 0)
        (syndrome (dualCode (bdlIteratedBundled 1).code) h') + dualPairing (bdlIteratedLZ 1) h' ≠
      rzCoarseParityRule pcode1 bdlSubdivPred (fun _ => 0)
        (syndrome (dualCode (bdlIteratedBundled 1).code) h) + dualPairing (bdlIteratedLZ 1) h := h_disc
    obtain ⟨hh1_syn, hh1'_syn, h_diff1, h_disc1⟩ :=
      stepX_primal_proj_ball_and_parity (dualBundled B1) h_inv_dB1
        (stepXLZ B0 (bdlIteratedLZ 0)) (fun _ => 0) x0 hr0 h h' h_diff h_disc'
    rw [zero_add, zero_add] at h_disc1
    have hlam := bdlLambda_ge_10000
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := by linarith
    have hr1_0 : 0 ≤ r / (bdlLambda : ℝ) + 7003 :=
      add_nonneg (div_nonneg hr0 (le_of_lt hlam_pos)) (by norm_num)
    have hr1_hi : r / (bdlLambda : ℝ) + 7003 ≤ 7015 := by
      have : r / (bdlLambda : ℝ) ≤ 1 := (div_le_one hlam_pos).mpr (by linarith)
      linarith
    have h_syn_LZ1 : syndrome (dualCode (dualCode B1.code)) (stepXLZ B0 (bdlIteratedLZ 0)) = 0 :=
      cylinder_syndrome_primal_lift (bdlPerturbedOfBundled B0) bdlSubdivPred (bdlIteratedLZ 0)
        (hasUniqueLogicalHomology_bdlIterated 0).h_syn_Z
    have h_res := syndrome_ne_zero_or_of_ball_filling
      (dualCode B1.code) (stepXLZ B0 (bdlIteratedLZ 0))
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) (10005 * (bdlLambda : ℝ))
      h_syn_LZ1
      (bdlRandomStepX_dual_subcylinder_filling B0 h_inv_B0 _ hr1_0 hr1_hi)
      (projCylinderLZ pcode1 bdlSubdivPred h) (projCylinderLZ pcode1 bdlSubdivPred h')
      h_diff1 h_disc1
    have h_eq_h : syndrome (dualCode B1.code) (projCylinderLZ pcode1 bdlSubdivPred h) =
        coarsePrimalSyndrome pcode1 bdlSubdivPred (syndrome (dualCode (bdlIteratedBundled 1).code) h) :=
      hh1_syn
    have h_eq_h' : syndrome (dualCode B1.code) (projCylinderLZ pcode1 bdlSubdivPred h') =
        coarsePrimalSyndrome pcode1 bdlSubdivPred (syndrome (dualCode (bdlIteratedBundled 1).code) h') :=
      hh1'_syn
    rwa [h_eq_h, h_eq_h'] at h_res
  | succ m ih =>
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
    let r1 : ℝ := r / (bdlLambda : ℝ) + 7003
    let r2 : ℝ := r1 / (bdlLambda : ℝ) + 7003
    have hr1 : 0 ≤ r1 := add_nonneg (div_nonneg hr0 (le_of_lt hlam_pos)) (by norm_num)
    have hr2 : 0 ≤ r2 := add_nonneg (div_nonneg hr1 (le_of_lt hlam_pos)) (by norm_num)
    have h_sd_eq : scaleDownRadius (2 * (m + 1)) r = scaleDownRadius (2 * m) r2 := by
      have h_2m : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [h_2m]; rfl
    rw [h_sd_eq] at hr_hi
    let B := bdlIteratedBundled (m + 1)
    let B1 := bdlRandomStepX B
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    have h_inv_B1 : HasBDLConeInvariants B1 := hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    have h_inv_dB1 : HasBDLConeInvariants (dualBundled B1) :=
      hasBDLConeInvariants_dualBundled B1 h_inv_B1
    let ψ1 := rxCleanedParityRule (bdlPerturbedOfBundled B) bdlSubdivPred
      (multiscaleParityRuleDual m) (bdlIteratedLZ (m + 1))
    obtain ⟨hh1_syn, hh1'_syn, h_diff1, h_disc1⟩ :=
      stepX_primal_proj_ball_and_parity (dualBundled B1) h_inv_dB1
        (stepXLZ B (bdlIteratedLZ (m + 1))) ψ1 x0 hr0 h h' h_diff h_disc
    let h1 := projCylinderLZ (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred h
    let h1' := projCylinderLZ (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred h'
    obtain ⟨hh0_syn, hh0'_syn, h_diff0, h_disc0⟩ :=
      stepX_dual_proj_ball_and_parity B h_inv_B
        (bdlIteratedLZ (m + 1)) (multiscaleParityRuleDual m)
        (fun axis => x0 axis / (bdlLambda : ℝ)) hr1 h1 h1' h_diff1 h_disc1
    let h0 := rxCleanedCoarseProj (bdlPerturbedOfBundled B) bdlSubdivPred h1
    let h0' := rxCleanedCoarseProj (bdlPerturbedOfBundled B) bdlSubdivPred h1'
    have h_res := ih hr2 hr_hi h0 h0' _ h_diff0 h_disc0
    have h_eq_h : syndrome (dualCode B.code) h0 =
        rxCleanedCoarseSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred
          (coarsePrimalSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
            (syndrome (dualCode (bdlIteratedBundled (m + 2)).code) h)) :=
      hh0_syn.trans (congr_arg _ hh1_syn)
    have h_eq_h' : syndrome (dualCode B.code) h0' =
        rxCleanedCoarseSyndrome (bdlPerturbedOfBundled B) bdlSubdivPred
          (coarsePrimalSyndrome (bdlPerturbedOfBundled (dualBundled B1)) bdlSubdivPred
            (syndrome (dualCode (bdlIteratedBundled (m + 2)).code) h')) :=
      hh0'_syn.trans (congr_arg _ hh1'_syn)
    rwa [h_eq_h, h_eq_h'] at h_res

/-- **Multiscale Intact Witness Pool Shell Cardinality Bound (`multiscaleIntactWitnessPool_shell_card_le`,
    Part II, Lemma 3.3 (`lem:klarner-bound`), Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`),
    Equation (75) (`eq:total-multiscale-vertex-bound`), and
    Theorem 5.1(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    For every hierarchy level `k : ℕ` and every weight shell `m : ℕ`, the number of multiscale
    intact percolating cluster witnesses of weight `m` in `multiscaleIntactWitnessPoolPrimal k`
    and `multiscaleIntactWitnessPoolDual k` is bounded by `(bdlClusterStepBase ^ 8) ^ m` via the
    component-wise $\frac{16}{27}$ cleaner contraction (`27 * |C_{i-2}| ≤ 16 * |C_i|`), total
    multiscale vertex sum $|\widehat{C}| < 5|C_{2k+2}|$, and Klarner animal counting on the
    bounded-degree hierarchical check graph $\widehat{\mathbb{G}}_{\mathrm{hier}}$. -/
theorem multiscaleIntactWitnessPool_shell_card_le (k : ℕ) :
    (∀ m : ℕ, ((multiscaleIntactWitnessPoolPrimal k).filter
      (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
      (bdlClusterStepBase ^ 8) ^ m) ∧
    (∀ m : ℕ, ((multiscaleIntactWitnessPoolDual k).filter
      (fun c => (Finset.univ.filter (fun z => c z ≠ 0)).card = m)).card ≤
      (bdlClusterStepBase ^ 8) ^ m) := by
  refine ⟨fun m => card_shell_codeZeroSpilloverPool_le
    (bdlIteratedBundled (k + 1)).code (clusterRawWeight k) _ (primalHierPkg k) ?_ m,
    fun m => card_shell_codeZeroSpilloverPool_le
    (dualCode (bdlIteratedBundled (k + 1)).code) (clusterRawWeight k) _ (dualHierPkg k) ?_ m⟩
  · intro c _ ⟨h_intact, h_conn⟩
    obtain ⟨C_hat, hw, hR⟩ := exists_hierClusterWitness_primal k c h_intact
    exact ⟨MultiscaleClusterConnPrimal k c, 43, C_hat, by decide, hw, hR, h_conn⟩
  · intro c hc_ne ⟨_, c1, h_half, ⟨_, h_syn1, h_wt1⟩, _, h_conn⟩
    subst h_syn1
    obtain ⟨C_hat_1, hw1, hR1⟩ := exists_hierClusterWitness_dualHalf k _ h_half
    obtain ⟨C_hat_2, hw2, hR2⟩ := dualStepMidHierPkg_lift k
      (dualHalfHierPkg k) hw1 hR1 (fun _ => hc_ne) rfl h_wt1
    exact ⟨MultiscaleClusterConnDual k c, 54, C_hat_2, by decide, hw2, hR2, h_conn⟩

lemma exists_mem_or_left {α : Type*} (s : Finset α) (P Q : α → Prop)
    (h : ∃ c ∈ s, P c) : ∃ c ∈ s, P c ∨ Q c :=
  match h with
  | ⟨c, hc_mem, hc_P⟩ => @Exists.intro α (fun c => c ∈ s ∧ (P c ∨ Q c)) c ⟨hc_mem, Or.inl hc_P⟩

lemma exists_mem_or_right {α : Type*} (s : Finset α) (P Q : α → Prop)
    (h : ∃ c ∈ s, Q c) : ∃ c ∈ s, P c ∨ Q c :=
  match h with
  | ⟨c, hc_mem, hc_Q⟩ => @Exists.intro α (fun c => c ∈ s ∧ (P c ∨ Q c)) c ⟨hc_mem, Or.inr hc_Q⟩

/-- **Intact Percolating Cluster Witness Extraction on Euclidean Balls
    (`multiscaleIntactWitnessPool_ball_parity_witness_exists`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Proposition 4.3(ii) (`prop:rca-hierarchy`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    For any hierarchy level `k : ℕ`, any radius `0 ≤ r` with `scaleDownRadius (2 * k) r ≤ 7015`,
    and any two chains `e, e'` (or dual cochains `h, h'`) agreeing outside `ball3D x0 r` whose
    multiscale decoded logical parities differ, at least one of `syndrome e` or `syndrome e'`
    contains an intact percolating cluster witness `c ∈ multiscaleIntactWitnessPoolPrimal k`
    (respectively `c ∈ multiscaleIntactWitnessPoolDual k`). -/
theorem multiscaleIntactWitnessPool_ball_parity_witness_exists (k : ℕ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr_hi : scaleDownRadius (2 * k) r ≤ 7015) :
    (∀ (e e' : (bdlIteratedBundled (k + 1)).Q → ZMod 2) (x0 : Point3D),
      (∀ q : (bdlIteratedBundled (k + 1)).Q,
        e q ≠ e' q → (bdlIteratedBundled (k + 1)).code.posQ q ∈ ball3D x0 r) →
      multiscaleParityRulePrimal k (syndrome (bdlIteratedBundled (k + 1)).code e') +
          dualPairing (bdlIteratedLX (k + 1)) e' ≠
        multiscaleParityRulePrimal k (syndrome (bdlIteratedBundled (k + 1)).code e) +
          dualPairing (bdlIteratedLX (k + 1)) e →
      ∃ c ∈ multiscaleIntactWitnessPoolPrimal k,
        (∀ m : (bdlIteratedBundled (k + 1)).M_X,
          c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e m ≠ 0) ∨
        (∀ m : (bdlIteratedBundled (k + 1)).M_X,
          c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e' m ≠ 0)) ∧
    (∀ (h h' : (bdlIteratedBundled (k + 1)).Q → ZMod 2) (x0 : Point3D),
      (∀ q : (bdlIteratedBundled (k + 1)).Q,
        h q ≠ h' q → (dualCode (bdlIteratedBundled (k + 1)).code).posQ q ∈ ball3D x0 r) →
      multiscaleParityRuleDual k (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h') +
          dualPairing (bdlIteratedLZ (k + 1)) h' ≠
        multiscaleParityRuleDual k (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h) +
          dualPairing (bdlIteratedLZ (k + 1)) h →
      ∃ c ∈ multiscaleIntactWitnessPoolDual k,
        (∀ m : (bdlIteratedBundled (k + 1)).M_Z,
          c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h m ≠ 0) ∨
        (∀ m : (bdlIteratedBundled (k + 1)).M_Z,
          c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h' m ≠ 0)) := by
  refine ⟨fun e e' x0 h_diff h_disc => ?_, fun h h' x0 h_diff h_disc => ?_⟩
  · exact (primal_pushedSyndrome_ne_zero_of_ball_discrepancy k hr0 hr_hi e e' x0 h_diff h_disc).elim
      (fun h_e => exists_mem_or_left (multiscaleIntactWitnessPoolPrimal k)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_X,
          c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e m ≠ 0)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_X,
          c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e' m ≠ 0)
        (exists_multiscaleIntactWitnessPrimal_of_pushedSyndrome_ne_zero k e h_e))
      (fun h_e' => exists_mem_or_right (multiscaleIntactWitnessPoolPrimal k)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_X,
          c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e m ≠ 0)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_X,
          c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e' m ≠ 0)
        (exists_multiscaleIntactWitnessPrimal_of_pushedSyndrome_ne_zero k e' h_e'))
  · exact (dual_pushedSyndrome_ne_zero_of_ball_discrepancy k hr0 hr_hi h h' x0 h_diff h_disc).elim
      (fun h_h => exists_mem_or_left (multiscaleIntactWitnessPoolDual k)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_Z,
          c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h m ≠ 0)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_Z,
          c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h' m ≠ 0)
        (exists_multiscaleIntactWitnessDual_of_pushedSyndrome_ne_zero k h h_h))
      (fun h_h' => exists_mem_or_right (multiscaleIntactWitnessPoolDual k)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_Z,
          c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h m ≠ 0)
        (fun c => ∀ m : (bdlIteratedBundled (k + 1)).M_Z,
          c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h' m ≠ 0)
        (exists_multiscaleIntactWitnessDual_of_pushedSyndrome_ne_zero k h' h_h'))

/-- **Multiscale Intact Cluster Witness Decomposition and Klarner Bound
    (`multiscale_intact_cluster_witness_decomposition_and_klarner_bound`,
    Part II, Definition 4.2 (`def:multiscale-cluster-decoder`),
    Lemma 4.4(iii) (`lem:two-stage-cleaner-contraction`), and
    Theorem 4.1(i),(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    Across the welded hierarchy `bdlIteratedBundled (k + 1)` down to the $[\![5,1,2]\!]$ seed code
    `bdlSurfaceSeedBundled = bdlIteratedBundled 0` (Part II, Lemma 4.1 (`lem:seed-code`),
    Equation (69) (`eq:seed-code-cohomology`)):
    - Every intact percolating cluster $\widehat{C} \subset \widehat{\mathbb{G}}_{\mathrm{hier}}$ lifts
      across primal and dual steps (`primal_cylinder_subsyndrome_zero_spillover_recovery`,
      `dual_cleaner_isolated_component_coboundary_eq`) to a zero-spillover witness `c ∈ W` satisfying
      `∃ e_C, syndrome code e_C = c` (Part II, Equation (77) (`eq:exact-intact-cluster-boundary`)).
    - By the $\frac{16}{27}$ cleaner contraction (Equation (73) (`eq:two-step-16-27`)), every `c ∈ W` has
      weight `clusterRawWeight k ≤ syndromeWeight c` (Equation (74) (`eq:percolating-weight-lower-bound`))
      and $|\widehat{C}| < 5|C_{2k+2}|$ (Equation (75) (`eq:total-multiscale-vertex-bound`)), so Klarner
      counting (Lemma 3.3 (`lem:klarner-bound`), `multiscaleIntactWitnessPool_shell_card_le`) bounds
      each weight-$m$ shell of `W` by `(bdlClusterStepBase ^ 8) ^ m`.
    - Any two chains `e, e'` agreeing outside `ball3D x0 r` (`0 ≤ r`, `scaleDownRadius (2 * k) r ≤ 7015`)
      with distinct decoded logical parities contain a witness `c ∈ W` in `syndrome e` or `syndrome e'`
      (`multiscaleIntactWitnessPool_ball_parity_witness_exists`). -/
theorem multiscale_intact_cluster_witness_decomposition_and_klarner_bound (k : ℕ) :
    (∃ (ψ_P : ((bdlIteratedBundled (k + 1)).M_X → ZMod 2) → ZMod 2)
       (W_P : Finset ((bdlIteratedBundled (k + 1)).M_X → ZMod 2)),
      ψ_P 0 = 0 ∧
      (∀ m : ℕ, (W_P.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
        (bdlClusterStepBase ^ 8) ^ m) ∧
      (∀ c ∈ W_P, (clusterRawWeight k : ℝ) ≤ syndromeWeight c) ∧
      (∀ c ∈ W_P, ∃ e_C : (bdlIteratedBundled (k + 1)).Q → ZMod 2,
        syndrome (bdlIteratedBundled (k + 1)).code e_C = c) ∧
      (∀ {r : ℝ}, 0 ≤ r → scaleDownRadius (2 * k) r ≤ 7015 →
        ∀ (e e' : (bdlIteratedBundled (k + 1)).Q → ZMod 2) (x0 : Point3D),
          (∀ q : (bdlIteratedBundled (k + 1)).Q,
            e q ≠ e' q → (bdlIteratedBundled (k + 1)).code.posQ q ∈ ball3D x0 r) →
          ψ_P (syndrome (bdlIteratedBundled (k + 1)).code e') + dualPairing (bdlIteratedLX (k + 1)) e' ≠
            ψ_P (syndrome (bdlIteratedBundled (k + 1)).code e) + dualPairing (bdlIteratedLX (k + 1)) e →
          ∃ c ∈ W_P,
            (∀ m : (bdlIteratedBundled (k + 1)).M_X,
              c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e m ≠ 0) ∨
            (∀ m : (bdlIteratedBundled (k + 1)).M_X,
              c m ≠ 0 → syndrome (bdlIteratedBundled (k + 1)).code e' m ≠ 0))) ∧
    (∃ (ψ_D : ((bdlIteratedBundled (k + 1)).M_Z → ZMod 2) → ZMod 2)
       (W_D : Finset ((bdlIteratedBundled (k + 1)).M_Z → ZMod 2)),
      ψ_D 0 = 0 ∧
      (∀ m : ℕ, (W_D.filter (fun c => (Finset.univ.filter (fun z => c z ≠ 0)).card = m)).card ≤
        (bdlClusterStepBase ^ 8) ^ m) ∧
      (∀ c ∈ W_D, (clusterRawWeight k : ℝ) ≤ syndromeWeight c) ∧
      (∀ c ∈ W_D, ∃ h_C : (bdlIteratedBundled (k + 1)).Q → ZMod 2,
        syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h_C = c) ∧
      (∀ {r : ℝ}, 0 ≤ r → scaleDownRadius (2 * k) r ≤ 7015 →
        ∀ (h h' : (bdlIteratedBundled (k + 1)).Q → ZMod 2) (x0 : Point3D),
          (∀ q : (bdlIteratedBundled (k + 1)).Q,
            h q ≠ h' q → (dualCode (bdlIteratedBundled (k + 1)).code).posQ q ∈ ball3D x0 r) →
          ψ_D (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h') +
              dualPairing (bdlIteratedLZ (k + 1)) h' ≠
            ψ_D (syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h) +
              dualPairing (bdlIteratedLZ (k + 1)) h →
          ∃ c ∈ W_D,
            (∀ m : (bdlIteratedBundled (k + 1)).M_Z,
              c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h m ≠ 0) ∨
            (∀ m : (bdlIteratedBundled (k + 1)).M_Z,
              c m ≠ 0 → syndrome (dualCode (bdlIteratedBundled (k + 1)).code) h' m ≠ 0))) := by
  have h_card := multiscaleIntactWitnessPool_shell_card_le k
  refine ⟨⟨multiscaleParityRulePrimal k, multiscaleIntactWitnessPoolPrimal k,
    multiscaleParityRulePrimal_zero k, h_card.1,
    clusterRawWeight_le_of_mem_multiscaleIntactWitnessPoolPrimal k,
    exists_syndrome_eq_of_mem_multiscaleIntactWitnessPoolPrimal k,
    fun hr0 hr_hi => (multiscaleIntactWitnessPool_ball_parity_witness_exists k hr0 hr_hi).1⟩,
    ⟨multiscaleParityRuleDual k, multiscaleIntactWitnessPoolDual k,
    multiscaleParityRuleDual_zero k, h_card.2,
    clusterRawWeight_le_of_mem_multiscaleIntactWitnessPoolDual k,
    exists_syndrome_eq_of_mem_multiscaleIntactWitnessPoolDual k,
    fun hr0 hr_hi => (multiscaleIntactWitnessPool_ball_parity_witness_exists k hr0 hr_hi).2⟩⟩

/-- **Multiscale Zero-Spillover Ball Parity Witness Theorem (`hasZeroSpilloverBallParityWitnessFamily_bdlIterated_succ`,
    Part II, Section 5.1 (`subsec:direct-worldline-synthesis`),
    Theorem 4.1(i)–(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    Direct packaging of `multiscale_intact_cluster_witness_decomposition_and_klarner_bound` into
    `HasZeroSpilloverBallParityWitnessFamily` for both primal and dual sectors at level `k + 1`. -/
theorem hasZeroSpilloverBallParityWitnessFamily_bdlIterated_succ (k : ℕ) :
    ∀ {r : ℝ}, 0 ≤ r → scaleDownRadius (2 * k) r ≤ 7015 →
      HasZeroSpilloverBallParityWitnessFamily (bdlIteratedBundled (k + 1)).code
        (bdlIteratedLZ (k + 1)) (bdlIteratedLX (k + 1))
        r (clusterRawWeight k) (bdlClusterStepBase ^ 8) ∧
      HasZeroSpilloverBallParityWitnessFamily (dualCode (bdlIteratedBundled (k + 1)).code)
        (bdlIteratedLX (k + 1)) (bdlIteratedLZ (k + 1))
        r (clusterRawWeight k) (bdlClusterStepBase ^ 8) := by
  intro r hr0 hr_hi
  obtain ⟨⟨ψ_P, W_P, hψP0, hWP_card, hWP_wt, hWP_real, hWP_fail⟩,
          ⟨ψ_D, W_D, hψD0, hWD_card, hWD_wt, hWD_real, hWD_fail⟩⟩ :=
    multiscale_intact_cluster_witness_decomposition_and_klarner_bound k
  exact ⟨⟨ψ_P, W_P, hψP0, hWP_card, hWP_wt, hWP_real, hWP_fail hr0 hr_hi⟩,
         ⟨ψ_D, W_D, hψD0, hWD_card, hWD_wt, hWD_real, hWD_fail hr0 hr_hi⟩⟩

/-- **Macroscopic Radius-$74\Lambda_{\mathrm{BDL}}^k$ Zero-Spillover Ball Parity Witness Theorem
    for `bdlWeldedCode k` (`hasZeroSpilloverBallParityWitnessFamily_bdlWelded_lambdaPow`,
    Part I, Section 5.3, Lemma 5.4(ii) (`lem:percolating-cluster-bounds`);
    Part II, Section 5.1, Theorem 5.1(i)–(iii) (`thm:direct-worldline-intact-cluster-erasure`))**:
    At every level `k : ℕ`, both `bdlWeldedCode k` and `dualCode (bdlWeldedCode k)` admit a
    `HasZeroSpilloverBallParityWitnessFamily` at Euclidean radius
    `2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)` (`= 74 * Λ^k`)
    with minimum weight `clusterRawWeight k` and per-unit-weight Klarner animal base `bdlClusterStepBase ^ 8`. -/
theorem hasZeroSpilloverBallParityWitnessFamily_bdlWelded_lambdaPow (k : ℕ) :
    HasZeroSpilloverBallParityWitnessFamily (bdlWeldedCode k) (bdlWeldedLZ k) (bdlWeldedLX k)
      (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) (clusterRawWeight k)
      (bdlClusterStepBase ^ 8) ∧
    HasZeroSpilloverBallParityWitnessFamily (dualCode (bdlWeldedCode k)) (bdlWeldedLX k) (bdlWeldedLZ k)
      (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) (clusterRawWeight k)
      (bdlClusterStepBase ^ 8) := by
  have hr0 : (0 : ℝ) ≤ 2 * ((37 * bdlLambda ^ k : ℕ) : ℝ) := by positivity
  have h_sd : scaleDownRadius (2 * k) (2 * ((37 * bdlLambda ^ k : ℕ) : ℝ)) ≤ 7015 := by
    rcases k with _ | k'
    · simp only [pow_zero, mul_one, Nat.cast_ofNat, scaleDownRadius]; norm_num
    · have hlam : (10000 : ℝ) ≤ (bdlLambda : ℝ) := bdlLambda_ge_10000
      have h74 : (74 : ℝ) ≤ (bdlLambda : ℝ) ^ (k' + 1) := by
        rw [pow_succ]; nlinarith [one_le_pow₀ (by linarith : (1 : ℝ) ≤ (bdlLambda : ℝ)) (n := k')]
      have h_div : (2 * ((37 * bdlLambda ^ (k' + 1) : ℕ) : ℝ)) / ((bdlLambda : ℝ) ^ (2 * (k' + 1))) ≤ 1 := by
        rw [div_le_iff₀ (by positivity), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
          two_mul (k' + 1), pow_add (bdlLambda : ℝ) (k' + 1) (k' + 1)]
        nlinarith [(by positivity : (0 : ℝ) ≤ (bdlLambda : ℝ) ^ (k' + 1))]
      linarith [scaleDownRadius_bound (2 * (k' + 1)) hr0]
  obtain ⟨hP, hD⟩ := hasZeroSpilloverBallParityWitnessFamily_bdlIterated_succ k hr0 h_sd
  exact ⟨hasZeroSpilloverBallParityWitnessFamily_transportBundled (bdlIteratedBundled_eq (k + 1)) hP,
         hasZeroSpilloverBallParityWitnessFamily_dual_transportBundled (bdlIteratedBundled_eq (k + 1)) hD⟩

end BDLDecoder
end WeldedHierarchy

end
