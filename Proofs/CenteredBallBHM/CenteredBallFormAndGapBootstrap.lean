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

import Proofs.CenteredBallBHM.CenteredBallOverlapAndTQO1Diff

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# Centered Ball Telescoping Relative Form Bounds and Scale-Cutoff Calibration

Combines single-ball conditional-expectation telescoping with local-to-global norm transfer to establish coherent safe-subspace commutator bounds and full-space relative form bounds (`coherent_dressed_pinched_commutator_le_of_siteFamily_boxBall`, `relative_form_bound_of_siteFamily_boxBall`, `centeredSiteOp_diffD_and_rem_bounds_of_multiScale_boxBall_condExp_and_cor1_loc`), and calibrates `bdlScaleCutoffK` against the relative cone acyclicity expansion constant (`two_mul_bdlScaleCutoffK_add_three_le_L_star`, `linearExpansionRadius_collar_const_rca_bdl_two_mul_bdlScaleCutoffK_add_one_le_safe_radius`).

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

/-! ## 1. Centered-Ball Coherent Safe-Subspace Commutator & Relative Form Bound -/

theorem coherent_dressed_pinched_commutator_le_of_siteFamily_boxBall {D L R_fw : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (X_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_sum_X : (∑ u : BoxD D L, X_u u) = U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0)
    (Pi_safe O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe) (hO_norm : ‖O_dec‖ ≤ 1) (h_comm_H0 : Commute sys.H0 O_dec)
    (h_fw : ∀ (W : QuasiLocalPerturbation D L Site),
      ∀ r ∈ Finset.Icc 1 R_fw, ∀ A ∈ boxCubes D L r,
        Pi_safe * (W.term r A * O_dec - O_dec * W.term r A) * Pi_safe = 0)
    {C : ℝ} (hC : 1 ≤ C) (K : ℕ)
    (hK_fw : linearExpansionRadius C ((2 * K + 1) + bhmElementaryCubeSide) ≤ R_fw)
    (c_u : BoxD D L → ℝ) {ε_rem δ_split : ℝ}
    (h_rem_site : ∀ u : BoxD D L,
      let X_hat := centeredSiteOp (X_u u) (c_u u)
      ‖X_hat - indexedSingleBallApproxM sys C u K X_hat‖ ≤ ε_rem)
    (h_split : 2 * ((Fintype.card (BoxD D L) : ℝ) * ε_rem) ≤ δ_split) :
    let Pi_safe_dress := U.1 * Pi_safe * (U.1†)
    let O_dec_dress := U.1 * O_dec * (U.1†)
    ‖Pi_safe_dress * ((sys.H0 + V.totalPerturbation) * O_dec_dress -
        O_dec_dress * (sys.H0 + V.totalPerturbation)) * Pi_safe_dress‖ ≤ δ_split := by
  intro Pi_safe_dress O_dec_dress
  let X_hat := fun u : BoxD D L => centeredSiteOp (X_u u) (c_u u)
  let c_shift : ℝ := ∑ u : BoxD D L, c_u u
  let W_tel := ∑ u : BoxD D L, ∑ k ∈ Finset.Icc 1 K, indexedSingleBallDiffD sys C u k (X_hat u)
  let R_rem := ∑ u : BoxD D L, (X_hat u - indexedSingleBallApproxM sys C u K (X_hat u))
  let H_loc := sys.H0 + (c_shift : ℂ) • 1 + W_tel
  have h_decomp := conj_sub_H0_sub_shift_eq_centered_telescoping_of_siteFamily_boxBall
    sys V U X_u h_sum_X C K c_u
  have h_diff_eq : U.1† * (sys.H0 + V.totalPerturbation) * U.1 - H_loc = R_rem := by
    dsimp [H_loc, W_tel, R_rem]
    calc U.1† * (sys.H0 + V.totalPerturbation) * U.1 - (sys.H0 + (c_shift : ℂ) • 1 + W_tel)
      _ = (U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 - (c_shift : ℂ) • 1) - W_tel := by abel
      _ = (W_tel + R_rem) - W_tel := by rw [h_decomp]
      _ = R_rem := add_sub_cancel_left W_tel R_rem
  have h_W_fw : Pi_safe * (W_tel * O_dec - O_dec * W_tel) * Pi_safe = 0 := by
    apply pi_safe_commutator_finset_sum_eq_zero Pi_safe O_dec Finset.univ
    intro u _
    apply pi_safe_commutator_finset_sum_eq_zero Pi_safe O_dec (Finset.Icc 1 K)
    intro k hk
    have hk_le : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hk_fw : linearExpansionRadius C ((2 * k + 1) + bhmElementaryCubeSide) ≤ R_fw :=
      le_trans (linearExpansionRadius_mono (by linarith) (by omega)) hK_fw
    exact pi_safe_commutator_indexedSingleBallDiffD_eq_zero
      sys Pi_safe O_dec h_fw hC u k hk_fw (X_hat u)
  have h_shift_fw :
      Pi_safe * (((c_shift : ℂ) • 1) * O_dec - O_dec * ((c_shift : ℂ) • 1)) * Pi_safe = 0 :=
    pi_safe_commutator_smul_eq_zero Pi_safe O_dec 1 (c_shift : ℂ)
      (pi_safe_commutator_eq_zero_of_commute Pi_safe O_dec 1 (Commute.one_left O_dec))
  have h_H_loc_fw : Pi_safe * (H_loc * O_dec - O_dec * H_loc) * Pi_safe = 0 :=
    pi_safe_commutator_add_eq_zero Pi_safe O_dec (sys.H0 + (c_shift : ℂ) • 1) W_tel
      (pi_safe_commutator_add_eq_zero Pi_safe O_dec sys.H0 ((c_shift : ℂ) • 1)
        (pi_safe_commutator_eq_zero_of_commute Pi_safe O_dec sys.H0 h_comm_H0) h_shift_fw) h_W_fw
  have h_R_norm : ‖R_rem‖ ≤ (Fintype.card (BoxD D L) : ℝ) * ε_rem := by
    dsimp [R_rem]
    calc ‖∑ u : BoxD D L, (X_hat u - indexedSingleBallApproxM sys C u K (X_hat u))‖
      _ ≤ ∑ u : BoxD D L, ‖X_hat u - indexedSingleBallApproxM sys C u K (X_hat u)‖ := norm_sum_le _ _
      _ ≤ ∑ _u : BoxD D L, ε_rem := Finset.sum_le_sum (fun u _ => h_rem_site u)
      _ = (Fintype.card (BoxD D L) : ℝ) * ε_rem := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 := norm_dressed_pinched_commutator_le_two_mul_tail_bhm
    U Pi_safe O_dec (sys.H0 + V.totalPerturbation) H_loc hPi hO_norm h_H_loc_fw
  rw [h_diff_eq] at h1
  exact le_trans (le_trans h1 (mul_le_mul_of_nonneg_left h_R_norm (by norm_num))) h_split

theorem relative_form_bound_of_siteFamily_boxBall {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (X_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_sum_X : (∑ u : BoxD D L, X_u u) = U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0)
    {C : ℝ} (hC : 1 ≤ C) (K : ℕ) (c_u : BoxD D L → ℝ) (δ_shell : ℕ → ℝ) {ε_rem δ_split : ℝ}
    (hδ_nn : ∀ k ∈ Finset.Icc 1 K, 0 ≤ δ_shell k) (hX_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_u u))
    (hD_norm : ∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      let X_hat := centeredSiteOp (X_u u) (c_u u)
      ‖indexedSingleBallDiffD sys C u k X_hat‖ ≤ δ_shell k)
    (h_rem_site : ∀ u : BoxD D L,
      let X_hat := centeredSiteOp (X_u u) (c_u u)
      ‖X_hat - indexedSingleBallApproxM sys C u K X_hat‖ ≤ ε_rem)
    (h_slope :
      (∑ k ∈ Finset.Icc 1 K,
        δ_shell k * (((2 * (linearExpansionRadius (3 * C) (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)) ≤
        bhmSandwichDeviation)
    (h_rem_split : (Fintype.card (BoxD D L) : ℝ) * ε_rem ≤ δ_split / 2)
    (ψ : ManyBodyHilbertSpace Site) :
    let c_shift : ℝ := ∑ u : BoxD D L, c_u u
    |RCLike.re (inner ℂ ψ
        ((U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
      bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2 := by
  intro c_shift
  let X_hat := fun u : BoxD D L => centeredSiteOp (X_u u) (c_u u)
  let W_tel := ∑ k ∈ Finset.Icc 1 K, ∑ u : BoxD D L, indexedSingleBallDiffD sys C u k (X_hat u)
  let R_rem := ∑ u : BoxD D L, (X_hat u - indexedSingleBallApproxM sys C u K (X_hat u))
  have h_decomp : U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 - (c_shift : ℂ) • 1 = W_tel + R_rem := by
    rw [conj_sub_H0_sub_shift_eq_centered_telescoping_of_siteFamily_boxBall sys V U X_u h_sum_X C K c_u]
    dsimp [W_tel, R_rem]; rw [Finset.sum_comm]
  have hX_hat_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_hat u) :=
    fun u => isSelfAdjoint_sub_real_smul_one_bhm (hX_sa u) (c_u u)
  have hH0_nn : 0 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) :=
    le_trans (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (sys.sum_norm_checkProj_sq_le_re_inner_H0 h_weight ψ)
  have h_W_bound : |RCLike.re (inner ℂ ψ (W_tel ψ))| ≤
      bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
    change |RCLike.re (inner ℂ ψ
        ((∑ k ∈ Finset.Icc 1 K, ∑ u : BoxD D L, indexedSingleBallDiffD sys C u k (X_hat u)) ψ))| ≤
      bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ))
    rw [re_inner_sum_apply]
    calc |∑ k ∈ Finset.Icc 1 K,
            RCLike.re (inner ℂ ψ ((∑ u : BoxD D L, indexedSingleBallDiffD sys C u k (X_hat u)) ψ))|
      _ ≤ ∑ k ∈ Finset.Icc 1 K,
            |RCLike.re (inner ℂ ψ ((∑ u : BoxD D L, indexedSingleBallDiffD sys C u k (X_hat u)) ψ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 K,
            (δ_shell k * (((2 * (linearExpansionRadius (3 * C) (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)) *
              RCLike.re (inner ℂ ψ (sys.H0 ψ)) :=
        Finset.sum_le_sum (fun k hk =>
          abs_re_inner_sum_indexedSingleBallDiffD_le_re_inner_H0 sys h_weight hC
            (Finset.mem_Icc.mp hk).1 X_hat (hδ_nn k hk) hX_hat_sa (hD_norm k hk) ψ)
      _ = (∑ k ∈ Finset.Icc 1 K,
            δ_shell k * (((2 * (linearExpansionRadius (3 * C) (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)) *
            RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by rw [← Finset.sum_mul]
      _ ≤ bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) :=
        mul_le_mul_of_nonneg_right h_slope hH0_nn
  have h_R_norm : ‖R_rem‖ ≤ δ_split / 2 := by
    dsimp [R_rem]
    calc ‖∑ u : BoxD D L, (X_hat u - indexedSingleBallApproxM sys C u K (X_hat u))‖
      _ ≤ ∑ u : BoxD D L, ‖X_hat u - indexedSingleBallApproxM sys C u K (X_hat u)‖ := norm_sum_le _ _
      _ ≤ ∑ _u : BoxD D L, ε_rem := Finset.sum_le_sum (fun u _ => h_rem_site u)
      _ = (Fintype.card (BoxD D L) : ℝ) * ε_rem := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ δ_split / 2 := h_rem_split
  have h_R_bound : |RCLike.re (inner ℂ ψ (R_rem ψ))| ≤ (δ_split / 2) * ‖ψ‖ ^ 2 :=
    le_trans (abs_re_inner_le_opNorm_mul_norm_sq R_rem ψ)
      (mul_le_mul_of_nonneg_right h_R_norm (sq_nonneg _))
  rw [h_decomp, ContinuousLinearMap.add_apply, inner_add_right, map_add]
  exact le_trans (abs_add_le _ _) (add_le_add h_W_bound h_R_bound)

/-! ## 2. `h_cor1_loc` Multi-Scale Centered-Ball Bounds & Spectral Gap Bootstrap -/

theorem norm_centeredSiteOp_sub_indexedSingleBallApproxM_le_of_cor1_loc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {L_star k K : ℕ} {C : ℝ}
    (hTQO1 : SatisfiesTQO1 sys L_star)
    (h_cor1_loc : ∀ (u : BoxD D L) (j : ℕ), 1 ≤ j → j + 2 ≤ L_star →
      ∀ S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site (boxCube u j) S →
        ‖sys.localGroundProj (singleCubeSupportC C u j) * S‖ ≤ ‖sys.P0 * S‖)
    (u : BoxD D L) (hk1 : 1 ≤ k) (hkL : (2 * k + 1) + 2 ≤ L_star) (hKL : 2 * K + 1 ≤ L_star)
    {X_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {ε_k ε_K : ℝ}
    (hX_sa : IsSelfAdjoint X_u) (hX_comm : Commute X_u sys.P0)
    (h_tail_k : ‖X_u - condExp Site (boxBall u k) X_u‖ ≤ ε_k)
    (h_tail_K : ‖X_u - condExp Site (boxBall u K) X_u‖ ≤ ε_K) :
    let c_u := tqo1SiteBallCondExpScalar sys K u X_u
    let X_hat := centeredSiteOp X_u c_u
    ‖X_hat - indexedSingleBallApproxM sys C u k X_hat‖ ≤
      bhmTelescopingFactor * ε_k + 2 * ε_K := by
  intro c_u X_hat
  have hc_spec := (tqo1SiteBallCondExpScalar_spec sys hTQO1 hKL u hX_sa).1
  have hPX_hat : ‖sys.P0 * X_hat‖ ≤ ε_K :=
    norm_P0_mul_centeredSiteOp_boxBall_le sys K u hX_comm hc_spec h_tail_K
  have hX_hat_sa : IsSelfAdjoint X_hat := isSelfAdjoint_sub_real_smul_one_bhm hX_sa c_u
  let O_k := condExp Site (boxBall u k) X_hat
  have hO_k_sa : IsSelfAdjoint O_k := isSelfAdjoint_condExp_bhm (boxBall u k) hX_hat_sa
  have hO_k_supp : IsSupportedOn Site (boxCube (shiftCorner u k) (2 * k + 1)) O_k :=
    _root_.isSupportedOn_mono (boxBall_subset_boxCube u k)
      (isSupportedOn_condExp Site (boxBall u k) X_hat)
  have h_cor1 : ‖sys.localGroundProj (singleBallSupportC C u k) * O_k‖ ≤ ‖sys.P0 * O_k‖ :=
    h_cor1_loc (shiftCorner u k) (2 * k + 1) (by omega) hkL O_k hO_k_supp
  have h_tail_hat : ‖X_hat - O_k‖ ≤ ε_k := by
    rw [(centeredSiteOp_sub_condExp_eq (boxBall u k) X_u c_u).2.2]; exact h_tail_k
  rw [indexedSingleBallApproxM_of_pos sys C u hk1 X_hat]
  exact (telescoping_norm_bounds_of_approx_P0
    sys.P0 (sys.localGroundProj (singleBallSupportC C u k)) X_hat O_k
    sys.isStarProjection_P0 (sys.isStarProjection_P_loc_bhm (singleBallSupportC C u k))
    hX_hat_sa hO_k_sa hPX_hat h_cor1 h_tail_hat).2.2.2

theorem centeredSiteOp_diffD_and_rem_bounds_of_multiScale_boxBall_condExp_and_cor1_loc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {L_star K : ℕ} {C : ℝ}
    (hTQO1 : SatisfiesTQO1 sys L_star)
    (h_cor1_loc : ∀ (u : BoxD D L) (j : ℕ), 1 ≤ j → j + 2 ≤ L_star →
      ∀ S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site (boxCube u j) S →
        ‖sys.localGroundProj (singleCubeSupportC C u j) * S‖ ≤ ‖sys.P0 * S‖)
    (hK1 : 1 ≤ K) (hKL : (2 * K + 1) + 2 ≤ L_star)
    (X_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (ε_tail : ℕ → ℝ) (M0 : ℝ)
    (hX_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_u u))
    (hX_comm : ∀ u : BoxD D L, Commute (X_u u) sys.P0)
    (h_tail : ∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖X_u u - condExp Site (boxBall u k) (X_u u)‖ ≤ ε_tail k)
    (h_norm0 : ∀ u : BoxD D L,
      ‖centeredSiteOp (X_u u) (tqo1SiteBallCondExpScalar sys K u (X_u u))‖ ≤ M0) :
    let c_u := fun u : BoxD D L => tqo1SiteBallCondExpScalar sys K u (X_u u)
    let X_hat := fun u : BoxD D L => centeredSiteOp (X_u u) (c_u u)
    (∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u k (X_hat u)‖ ≤
        bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) ∧
    (∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u K (X_hat u)‖ ≤ 5 * ε_tail K) ∧
    (∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖indexedSingleBallDiffD sys C u k (X_hat u)‖ ≤
        (bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) +
          (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K)) := by
  intro c_u X_hat
  have hK_mem : K ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hK1, le_rfl⟩
  have hKL_le : 2 * K + 1 ≤ L_star := by omega
  have h_approx : ∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u k (X_hat u)‖ ≤
        bhmTelescopingFactor * ε_tail k + 2 * ε_tail K := by
    intro k hk u
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkK⟩
    exact norm_centeredSiteOp_sub_indexedSingleBallApproxM_le_of_cor1_loc
      sys hTQO1 h_cor1_loc u hk1 (by omega) hKL_le (hX_sa u) (hX_comm u)
      (h_tail k hk u) (h_tail K hK_mem u)
  have h_rem_K : ∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u K (X_hat u)‖ ≤ 5 * ε_tail K := by
    intro u; have hK := h_approx K hK_mem u; dsimp [bhmTelescopingFactor] at hK; linarith
  refine ⟨h_approx, h_rem_K, fun k hk u => ?_⟩
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hkK⟩
  have hprev_bound :
      ‖X_hat u - indexedSingleBallApproxM sys C u (k - 1) (X_hat u)‖ ≤
        (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K) := by
    by_cases hk_eq1 : k = 1
    · rw [if_pos hk_eq1, hk_eq1, Nat.sub_self, indexedSingleBallApproxM_zero, sub_zero]
      exact h_norm0 u
    · rw [if_neg hk_eq1]
      exact h_approx (k - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) u
  exact norm_indexedSingleBallDiffD_le_of_approx_bounds sys C u k (X_hat u)
    (h_approx k hk u) hprev_bound

theorem norm_centeredSiteOp_sub_indexedSingleBallApproxM_le_of_cor1_loc_of_offDiag {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {L_star k K : ℕ} {C : ℝ}
    (hTQO1 : SatisfiesTQO1 sys L_star)
    (h_cor1_loc : ∀ (u : BoxD D L) (j : ℕ), 1 ≤ j → j + 2 ≤ L_star →
      ∀ S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site (boxCube u j) S →
        ‖sys.localGroundProj (singleCubeSupportC C u j) * S‖ ≤ ‖sys.P0 * S‖)
    (u : BoxD D L) (hk1 : 1 ≤ k) (hkL : (2 * k + 1) + 2 ≤ L_star) (hKL : 2 * K + 1 ≤ L_star)
    {X_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {ε_k ε_K : ℝ}
    (hX_sa : IsSelfAdjoint X_u)
    (h_tail_k : ‖X_u - condExp Site (boxBall u k) X_u‖ ≤ ε_k)
    (h_tail_off_K : ‖X_u - condExp Site (boxBall u K) X_u‖ + ‖sys.P0 * X_u * (1 - sys.P0)‖ ≤ ε_K) :
    let c_u := tqo1SiteBallCondExpScalar sys K u X_u
    let X_hat := centeredSiteOp X_u c_u
    ‖X_hat - indexedSingleBallApproxM sys C u k X_hat‖ ≤
      bhmTelescopingFactor * ε_k + 2 * ε_K := by
  intro c_u X_hat
  have hc_spec := (tqo1SiteBallCondExpScalar_spec sys hTQO1 hKL u hX_sa).1
  have hPX_hat : ‖sys.P0 * X_hat‖ ≤ ε_K :=
    norm_P0_mul_centeredSiteOp_boxBall_le_of_offDiag sys K u hc_spec h_tail_off_K
  have hX_hat_sa : IsSelfAdjoint X_hat := isSelfAdjoint_sub_real_smul_one_bhm hX_sa c_u
  let O_k := condExp Site (boxBall u k) X_hat
  have hO_k_sa : IsSelfAdjoint O_k := isSelfAdjoint_condExp_bhm (boxBall u k) hX_hat_sa
  have hO_k_supp : IsSupportedOn Site (boxCube (shiftCorner u k) (2 * k + 1)) O_k :=
    _root_.isSupportedOn_mono (boxBall_subset_boxCube u k)
      (isSupportedOn_condExp Site (boxBall u k) X_hat)
  have h_cor1 : ‖sys.localGroundProj (singleBallSupportC C u k) * O_k‖ ≤ ‖sys.P0 * O_k‖ :=
    h_cor1_loc (shiftCorner u k) (2 * k + 1) (by omega) hkL O_k hO_k_supp
  have h_tail_hat : ‖X_hat - O_k‖ ≤ ε_k := by
    rw [(centeredSiteOp_sub_condExp_eq (boxBall u k) X_u c_u).2.2]; exact h_tail_k
  rw [indexedSingleBallApproxM_of_pos sys C u hk1 X_hat]
  exact (telescoping_norm_bounds_of_approx_P0
    sys.P0 (sys.localGroundProj (singleBallSupportC C u k)) X_hat O_k
    sys.isStarProjection_P0 (sys.isStarProjection_P_loc_bhm (singleBallSupportC C u k))
    hX_hat_sa hO_k_sa hPX_hat h_cor1 h_tail_hat).2.2.2

theorem centeredSiteOp_diffD_and_rem_bounds_of_multiScale_boxBall_condExp_and_cor1_loc_of_offDiag
    {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) {L_star K : ℕ} {C : ℝ}
    (hTQO1 : SatisfiesTQO1 sys L_star)
    (h_cor1_loc : ∀ (u : BoxD D L) (j : ℕ), 1 ≤ j → j + 2 ≤ L_star →
      ∀ S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site (boxCube u j) S →
        ‖sys.localGroundProj (singleCubeSupportC C u j) * S‖ ≤ ‖sys.P0 * S‖)
    (hK1 : 1 ≤ K) (hKL : (2 * K + 1) + 2 ≤ L_star)
    (X_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (ε_tail : ℕ → ℝ) (M0 : ℝ)
    (hX_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_u u))
    (h_tail : ∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖X_u u - condExp Site (boxBall u k) (X_u u)‖ ≤ ε_tail k)
    (h_tail_off_K : ∀ u : BoxD D L,
      ‖X_u u - condExp Site (boxBall u K) (X_u u)‖ + ‖sys.P0 * X_u u * (1 - sys.P0)‖ ≤ ε_tail K)
    (h_norm0 : ∀ u : BoxD D L,
      ‖centeredSiteOp (X_u u) (tqo1SiteBallCondExpScalar sys K u (X_u u))‖ ≤ M0) :
    let c_u := fun u : BoxD D L => tqo1SiteBallCondExpScalar sys K u (X_u u)
    let X_hat := fun u : BoxD D L => centeredSiteOp (X_u u) (c_u u)
    (∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u k (X_hat u)‖ ≤
        bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) ∧
    (∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u K (X_hat u)‖ ≤ 5 * ε_tail K) ∧
    (∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖indexedSingleBallDiffD sys C u k (X_hat u)‖ ≤
        (bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) +
          (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K)) := by
  intro c_u X_hat
  have hK_mem : K ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hK1, le_rfl⟩
  have hKL_le : 2 * K + 1 ≤ L_star := by omega
  have h_approx : ∀ k ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u k (X_hat u)‖ ≤
        bhmTelescopingFactor * ε_tail k + 2 * ε_tail K := by
    intro k hk u
    rcases Finset.mem_Icc.mp hk with ⟨hk1, hkK⟩
    exact norm_centeredSiteOp_sub_indexedSingleBallApproxM_le_of_cor1_loc_of_offDiag
      sys hTQO1 h_cor1_loc u hk1 (by omega) hKL_le (hX_sa u) (h_tail k hk u) (h_tail_off_K u)
  have h_rem_K : ∀ u : BoxD D L,
      ‖X_hat u - indexedSingleBallApproxM sys C u K (X_hat u)‖ ≤ 5 * ε_tail K := by
    intro u; have hK := h_approx K hK_mem u; dsimp [bhmTelescopingFactor] at hK; linarith
  refine ⟨h_approx, h_rem_K, fun k hk u => ?_⟩
  rcases Finset.mem_Icc.mp hk with ⟨hk1, hkK⟩
  have hprev_bound :
      ‖X_hat u - indexedSingleBallApproxM sys C u (k - 1) (X_hat u)‖ ≤
        (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K) := by
    by_cases hk_eq1 : k = 1
    · rw [if_pos hk_eq1, hk_eq1, Nat.sub_self, indexedSingleBallApproxM_zero, sub_zero]
      exact h_norm0 u
    · rw [if_neg hk_eq1]
      exact h_approx (k - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) u
  exact norm_indexedSingleBallDiffD_le_of_approx_bounds sys C u k (X_hat u)
    (h_approx k hk u) hprev_bound

/-! ## 3. Scale Calibration for `2 * bdlScaleCutoffK k + 1` -/

lemma two_mul_bdlScaleCutoffK_add_three_le_L_star {k : ℕ} (hk : 4 ≤ k) :
    (2 * bdlScaleCutoffK k + 1) + 2 ≤ Nat.floor (cStarBDL * (bdlBoxSide k : ℝ)) := by
  rw [floor_c_star_BDL_mul_bdlBoxSide_eq]
  dsimp [bdlScaleCutoffK]
  have h_pow : bdlLambda ^ (k - 4) * bdlLambda ≤ bdlLambda ^ (2 * k) := by
    rw [← pow_succ]; exact Nat.pow_le_pow_right bdlLambda_pos (by omega)
  have h1 : 1 ≤ bdlLambda ^ (k - 4) := Nat.one_le_pow (k - 4) bdlLambda bdlLambda_pos
  have h5 : 5 ≤ bdlLambda := by decide
  have h_mul : (2 * bdlLambda ^ (k - 4) + 1) + 2 ≤ bdlLambda ^ (k - 4) * bdlLambda := by
    calc (2 * bdlLambda ^ (k - 4) + 1) + 2
      _ ≤ 2 * bdlLambda ^ (k - 4) + 3 * bdlLambda ^ (k - 4) := by omega
      _ = bdlLambda ^ (k - 4) * 5 := by ring
      _ ≤ bdlLambda ^ (k - 4) * bdlLambda := Nat.mul_le_mul_left _ h5
  exact le_trans h_mul h_pow

lemma collar_const_rca_bdl_mul_five_le_bdlLambda_pow_four :
    collarConstRCABDL * 5 ≤ bdlLambda ^ 4 := by decide

lemma linearExpansionRadius_collar_const_rca_bdl_two_mul_bdlScaleCutoffK_add_one_le_safe_radius {k : ℕ} (hk : 4 ≤ k) :
    linearExpansionRadius (collarConstRCABDL : ℝ) ((2 * bdlScaleCutoffK k + 1) + bhmElementaryCubeSide) ≤
      bdlLambda ^ k := by
  dsimp [linearExpansionRadius, bhmElementaryCubeSide, bdlScaleCutoffK]
  have h_cast : (collarConstRCABDL : ℝ) * (((2 * bdlLambda ^ (k - 4) + 1) + 2 : ℕ) : ℝ) =
      ((collarConstRCABDL * ((2 * bdlLambda ^ (k - 4) + 1) + 2) : ℕ) : ℝ) := by push_cast; ring
  rw [h_cast, Nat.ceil_natCast]
  have hk_eq : k = (k - 4) + 4 := (Nat.sub_add_cancel hk).symm
  rw [hk_eq, pow_add]
  have h1 : 1 ≤ bdlLambda ^ (k - 4) := Nat.one_le_pow (k - 4) bdlLambda bdlLambda_pos
  have h_le5 : (2 * bdlLambda ^ (k - 4) + 1) + 2 ≤ 5 * bdlLambda ^ (k - 4) := by omega
  have h_C : collarConstRCABDL * 5 ≤ bdlLambda ^ 4 := collar_const_rca_bdl_mul_five_le_bdlLambda_pow_four
  calc collarConstRCABDL * ((2 * bdlLambda ^ (k - 4) + 1) + 2)
    _ ≤ collarConstRCABDL * (5 * bdlLambda ^ (k - 4)) := Nat.mul_le_mul_left collarConstRCABDL h_le5
    _ = bdlLambda ^ (k - 4) * (collarConstRCABDL * 5) := by ring
    _ ≤ bdlLambda ^ (k - 4) * bdlLambda ^ 4 := Nat.mul_le_mul_left _ h_C

end
