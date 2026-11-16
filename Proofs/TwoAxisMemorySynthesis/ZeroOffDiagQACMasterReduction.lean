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

import Proofs.HastingsKomaLightCone.SpectralLowPassFilterClosure

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory KMSPinchedGibbs
open PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

attribute [local irreducible] collarConstRCABDL bdlLambda qCodeBDL r0BDL mMaxBDL

/-!
# Zero-Temperature QAC Dressing Bundle Construction for the Welded 3D Memory

Constructs the zero-temperature QAC dressing unitary bundle `HasZeroTempDressingBundle` for the level-k welded 3D memory system, establishing ground-space commutation, dressed energy-band sandwich bounds, and superpolynomially small dressed single-site decoder commutators.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
-/

/-! ## 1. General Site-Family Continuous-$s$ Centered-`boxBall` Gap Bootstrap -/

/-- **General Site-Family Continuous-$s$ Centered-`boxBall` Gap Bootstrap
    (`indexedSpectralGap_bootstrap_on_Icc_of_siteFamily_boxBall_norm_of_cor1_loc`)**:
    Establishes `∀ s ∈ Set.Icc 0 1, bhmPerturbedGap ≤ indexedSpectralGap sys V s` from any unitary
    flow `U_QAC` and site-operator family `X_QAC` whose sum equals `H_dress(s) - sys.H0`, whose
    terms are self-adjoint and commute with `sys.P0`, and whose `boxBall u j` conditional
    expectation tails and norms are bounded by `J * g_tail j` and `J * m_0 / 2`. -/
theorem indexedSpectralGap_bootstrap_on_Icc_of_siteFamily_boxBall_norm_of_cor1_loc
    {D L L_star : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i) (V : QuasiLocalPerturbation D L Site)
    {C : ℝ} (hC : 1 ≤ C) (hTQO1 : SatisfiesTQO1 sys L_star)
    (h_cor1_loc : ∀ (u : BoxD D L) (j : ℕ), 1 ≤ j → j + 2 ≤ L_star →
      ∀ S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site (boxCube u j) S →
        ‖sys.localGroundProj (singleCubeSupportC C u j) * S‖ ≤ ‖sys.P0 * S‖)
    {K : ℕ} (hK1 : 1 ≤ K) (hKL : (2 * K + 1) + 2 ≤ L_star)
    (U_QAC : ℝ → unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (X_QAC : ℝ → BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {J J_0 m_0 δ_split : ℝ} {g_tail : ℕ → ℝ}
    (hg_tail : IsSuperpolynomialDecay g_tail)
    (hJ_nn : 0 ≤ J) (hJ_le_J0 : J ≤ J_0) (hm0_nn : 0 ≤ m_0)
    (hJ0_le : J_0 ≤ bhmUniformCouplingThreshold D (3 * C) m_0 g_tail)
    (h_rem_J0 : 2 * ((L : ℝ) ^ D * (5 * (J_0 * g_tail K))) ≤ δ_split)
    (hδ_lt : δ_split < 1 / 4)
    (hX_sum : ∀ s ∈ Set.Icc 0 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap sys V u) →
      (∑ u : BoxD D L, X_QAC s u) =
        (U_QAC s).1† * (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) * (U_QAC s).1 - sys.H0)
    (hX_sa : ∀ s ∈ Set.Icc 0 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap sys V u) →
      ∀ u : BoxD D L, IsSelfAdjoint (X_QAC s u))
    (h_off_K : ∀ s ∈ Set.Icc 0 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap sys V u) →
      ∀ u : BoxD D L,
        ‖X_QAC s u - condExp Site (boxBall u K) (X_QAC s u)‖ +
          ‖sys.P0 * (X_QAC s u) * (1 - sys.P0)‖ ≤ J * g_tail K)
    (h_tail : ∀ s ∈ Set.Icc 0 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap sys V u) →
      ∀ j ∈ Finset.Icc 1 K, ∀ u : BoxD D L,
        ‖X_QAC s u - condExp Site (boxBall u j) (X_QAC s u)‖ ≤ J * g_tail j)
    (hX_norm : ∀ s ∈ Set.Icc 0 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap sys V u) →
      ∀ u : BoxD D L, ‖X_QAC s u‖ ≤ J * m_0 / 2) :
    ∀ s ∈ Set.Icc 0 1, bhmPerturbedGap ≤ indexedSpectralGap sys V s := by
  have h3C : 1 ≤ 3 * C := by linarith
  have hJ0_nn : 0 ≤ J_0 := le_trans hJ_nn hJ_le_J0
  have hK_nn : 0 ≤ g_tail K := hg_tail.1 K
  have hδ_nn : 0 ≤ δ_split := le_trans (by positivity) h_rem_J0
  have h_boot := indexedSpectralGap_bootstrap_on_Icc_of_unitary_flow
    sys h_weight V hδ_nn hδ_lt (fun s hs h_ih => ?_)
  · exact fun s hs => (h_boot s hs).2.1
  · let V_s := scaleQuasiLocalPerturbation s V
    let X_u := X_QAC s
    let ε_tail : ℕ → ℝ := fun j => J * g_tail j
    let M0 : ℝ := J * m_0
    let c_u := fun u : BoxD D L => tqo1SiteBallCondExpScalar sys K u (X_u u)
    let δ_shell : ℕ → ℝ := fun j =>
      (bhmTelescopingFactor * ε_tail j + 2 * ε_tail K) +
        (if j = 1 then M0 else bhmTelescopingFactor * ε_tail (j - 1) + 2 * ε_tail K)
    have h_mom_pair := bhmShellNormalizedMomentSum_le_uniform D h3C hm0_nn hg_tail hK1
    have h_rem_split : 2 * ((Fintype.card (BoxD D L) : ℝ) * (5 * ε_tail K)) ≤ δ_split := by
      have h1 := lr_and_rem_split_le_of_J_proportional
        (ε_tail := ε_tail) (ε_LR := 0) (c_LR := 0)
        hJ_nn hJ_le_J0 le_rfl le_rfl (by ring_nf; exact le_rfl) hK_nn le_rfl
        (by rw [mul_zero, sq, mul_zero, mul_zero]; exact hδ_nn) h_rem_J0
      exact h1.2
    have h_norm0 : ∀ u : BoxD D L,
        ‖centeredSiteOp (X_u u) (tqo1SiteBallCondExpScalar sys K u (X_u u))‖ ≤ M0 := by
      intro u
      have h1 := norm_centeredSiteOp_tqo1SiteBallCondExpScalar_le_two_mul_norm
        sys hTQO1 (by omega : 2 * K + 1 ≤ L_star) u (hX_sa s hs h_ih u)
      have h2 := hX_norm s hs h_ih u
      dsimp only [X_u, M0] at h1 h2 ⊢; linarith
    have h_bounds :=
      centeredSiteOp_diffD_and_rem_bounds_of_multiScale_boxBall_condExp_and_cor1_loc_of_offDiag
        sys hTQO1 h_cor1_loc hK1 hKL X_u ε_tail M0
        (hX_sa s hs h_ih) (h_tail s hs h_ih) (h_off_K s hs h_ih) h_norm0
    have hδ_shell_nn : ∀ j ∈ Finset.Icc 1 K, 0 ≤ δ_shell j := by
      intro j _hj; dsimp [δ_shell, bhmTelescopingFactor, ε_tail, M0]
      have hj_nn := mul_nonneg hJ_nn (hg_tail.1 j)
      have hJK_nn := mul_nonneg hJ_nn (hg_tail.1 K)
      have hM0_nn := mul_nonneg hJ_nn hm0_nn
      by_cases hj_eq1 : j = 1
      · rw [if_pos hj_eq1]; linarith
      · rw [if_neg hj_eq1]; have hprev_nn := mul_nonneg hJ_nn (hg_tail.1 (j - 1)); linarith
    have h_slope := slope_bhmShell_le_bhmSandwichDeviation_of_J_le
      D (3 * C) hK1 hJ_nn h_mom_pair.1 le_rfl (fun _ _ => le_rfl) h_mom_pair.2
      (le_trans hJ_le_J0 hJ0_le)
    refine ⟨U_QAC s, ∑ u : BoxD D L, c_u u, fun ψ => ?_⟩
    exact relative_form_bound_of_siteFamily_boxBall
      sys h_weight V_s (U_QAC s) X_u (hX_sum s hs h_ih) hC K c_u δ_shell hδ_shell_nn
      (hX_sa s hs h_ih) h_bounds.2.2 h_bounds.2.1 h_slope (by linarith) ψ

/-- **Approximate Ground-Projector Commutation from Centered-Ball Telescoping Remainder
    (`dressed_P0_commutator_le_of_siteFamily_boxBall`)**:
    Because every centered-ball shell difference `indexedSingleBallDiffD sys C u k (X_hat u)`
    annihilates `sys.P_loc (singleBallSupportC C u k)` and hence commutes with `sys.P0`, the
    telescoped local Hamiltonian `H_loc = sys.H0 + c_shift • 1 + W_tel` commutes identically with
    `sys.P0`. Consequently, for `P0_dress = U.1 * sys.P0 * U.1†`,
    `‖(sys.H0 + V.V_tot) * P0_dress - P0_dress * (sys.H0 + V.V_tot)‖ ≤ 2 * ‖R_rem‖ ≤ δ_split`
    holds unconditionally without assuming `Commute H_dress sys.P0`. -/
theorem dressed_P0_commutator_le_of_siteFamily_boxBall {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (X_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_sum_X : (∑ u : BoxD D L, X_u u) = U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0)
    {C : ℝ} (hC : 1 ≤ C) (K : ℕ) (c_u : BoxD D L → ℝ)
    (hX_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_u u)) {ε_rem δ_split : ℝ}
    (h_rem_site : ∀ u : BoxD D L,
      let X_hat := centeredSiteOp (X_u u) (c_u u)
      ‖X_hat - indexedSingleBallApproxM sys C u K X_hat‖ ≤ ε_rem)
    (h_split : 2 * ((Fintype.card (BoxD D L) : ℝ) * ε_rem) ≤ δ_split) :
    let P0_dress := U.1 * sys.P0 * (U.1†)
    ‖(sys.H0 + V.totalPerturbation) * P0_dress - P0_dress * (sys.H0 + V.totalPerturbation)‖ ≤ δ_split := by
  intro P0_dress
  let X_hat := fun u : BoxD D L => centeredSiteOp (X_u u) (c_u u)
  have hX_hat_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_hat u) := fun u =>
    isSelfAdjoint_sub_real_smul_one_bhm (hX_sa u) (c_u u)
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
  have h_W_fw :
      (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) *
        (W_tel * sys.P0 - sys.P0 * W_tel) * 1 = 0 := by
    refine pi_safe_commutator_finset_sum_eq_zero 1 sys.P0 Finset.univ _ (fun u _ => ?_)
    refine pi_safe_commutator_finset_sum_eq_zero 1 sys.P0 (Finset.Icc 1 K) _ (fun k hk => ?_)
    rcases indexedSingleBallDiffD_isSelfAdjoint_and_mul_P_loc_eq_zero
      sys hC u (Finset.mem_Icc.mp hk).1 (hX_hat_sa u) with ⟨hD_sa, hD_Ploc⟩
    have hD_P0 : indexedSingleBallDiffD sys C u k (X_hat u) * sys.P0 = 0 := by
      rw [← (sys.localProj_mul_proj0_eq_proj0 (singleBallSupportC C u k)).1, ← mul_assoc, hD_Ploc, zero_mul]
    have hP0_D : sys.P0 * indexedSingleBallDiffD sys C u k (X_hat u) = 0 := by
      calc sys.P0 * indexedSingleBallDiffD sys C u k (X_hat u)
        _ = star (indexedSingleBallDiffD sys C u k (X_hat u) * sys.P0) := by
          rw [star_mul, hD_sa.star_eq, sys.isStarProjection_P0.isSelfAdjoint.star_eq]
        _ = 0 := by
          rw [hD_P0]
          exact (IsSelfAdjoint.zero (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)).star_eq
    apply pi_safe_commutator_eq_zero_of_commute
    rw [commute_iff_eq, hD_P0, hP0_D]
  have h_H_loc_fw :
      (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) *
        (H_loc * sys.P0 - sys.P0 * H_loc) * 1 = 0 := by
    refine pi_safe_commutator_add_eq_zero 1 sys.P0 _ _ ?_ h_W_fw
    refine pi_safe_commutator_add_eq_zero 1 sys.P0 _ _ ?_ ?_
    · exact pi_safe_commutator_eq_zero_of_commute 1 sys.P0 sys.H0 sys.commute_H0_P0
    · exact pi_safe_commutator_smul_eq_zero 1 sys.P0 1 (c_shift : ℂ)
        (pi_safe_commutator_eq_zero_of_commute 1 sys.P0 1 (Commute.one_left sys.P0))
  have h_R_norm : ‖R_rem‖ ≤ (Fintype.card (BoxD D L) : ℝ) * ε_rem := by
    dsimp [R_rem]
    calc ‖∑ u : BoxD D L, (X_hat u - indexedSingleBallApproxM sys C u K (X_hat u))‖
      _ ≤ ∑ u : BoxD D L, ‖X_hat u - indexedSingleBallApproxM sys C u K (X_hat u)‖ := norm_sum_le _ _
      _ ≤ ∑ _u : BoxD D L, ε_rem := Finset.sum_le_sum (fun u _ => h_rem_site u)
      _ = (Fintype.card (BoxD D L) : ℝ) * ε_rem := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 := norm_dressed_pinched_commutator_le_two_mul_tail_bhm
    U 1 sys.P0 (sys.H0 + V.totalPerturbation) H_loc ⟨mul_one 1, IsSelfAdjoint.one _⟩
    (isStarProjection_norm_le_one_bhm sys.isStarProjection_P0) h_H_loc_fw
  have hU1 : U.1 * (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) * U.1† = 1 := by
    change U.1 * 1 * star U.1 = 1
    rw [mul_one, (Unitary.mem_iff.mp U.2).2]
  rw [hU1, one_mul, mul_one, h_diff_eq] at h1
  exact le_trans (le_trans h1 (mul_le_mul_of_nonneg_left h_R_norm (by norm_num))) h_split

/-! ## 2. Zero-Temperature Perturbative Dressing Bundle (`HasZeroTempDressingBundle`) -/

attribute [local irreducible]
  bdlBoxSide bdlScaleCutoffK bBDL bdlHierarchySteps bdlWeldedCode bdlLocalDescriptor bdlPushChain

instance (priority := 10000) instNeZeroBDLBoxSideIrred (k : ℕ) : NeZero (bdlBoxSide k) :=
  instNeZeroBDLBoxSide k

/-- Zero-temperature dressing bundle predicate at scale `L` (`HasZeroTempDressingBundle`). -/
abbrev HasZeroTempDressingBundle {L : ℕ} [NeZero L]
    (m : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (δ_split_L : ℝ) (g_LR : ℕ → ℝ) : Prop :=
  ∃ (U_dress : unitary (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
    (E0 : ℝ),
    (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v →
      ∀ r : ℕ,
        ‖U_dress.1† * A_v * U_dress.1 -
          condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v r) (U_dress.1† * A_v * U_dress.1)‖ ≤
          ‖A_v‖ * g_LR r) ∧
    ‖(m.sys.H0 + V.totalPerturbation) * (U_dress.1 * m.sys.P0 * U_dress.1†) -
      (U_dress.1 * m.sys.P0 * U_dress.1†) * (m.sys.H0 + V.totalPerturbation)‖ ≤
      δ_split_L / 6 ∧
    (∀ ψ : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)),
      |RCLike.re (inner ℂ ψ
        ((U_dress.1† * (m.sys.H0 + V.totalPerturbation) * U_dress.1 -
          m.sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (m.sys.H0 ψ)) +
          (δ_split_L / 4) * ‖ψ‖ ^ 2) ∧
    let Pi_safe_dress := U_dress.1 * m.Pi_safe * U_dress.1†
    let O_Z_dress := U_dress.1 * m.O_dec_Z * U_dress.1†
    let O_X_dress := U_dress.1 * m.O_dec_X * U_dress.1†
    ‖Pi_safe_dress * ((m.sys.H0 + V.totalPerturbation) * O_Z_dress -
      O_Z_dress * (m.sys.H0 + V.totalPerturbation)) * Pi_safe_dress‖ ≤ δ_split_L ∧
    ‖Pi_safe_dress * ((m.sys.H0 + V.totalPerturbation) * O_X_dress -
      O_X_dress * (m.sys.H0 + V.totalPerturbation)) * Pi_safe_dress‖ ≤ δ_split_L ∧
    (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v →
      ‖Pi_safe_dress * (A_v * O_Z_dress - O_Z_dress * A_v) * Pi_safe_dress‖ ≤
        δ_split_L * ‖A_v‖ ∧
      ‖Pi_safe_dress * (A_v * O_X_dress - O_X_dress * A_v) * Pi_safe_dress‖ ≤
        δ_split_L * ‖A_v‖)

private lemma zero_temp_dressing_bundle_at_L {L K r_fw : ℕ} [NeZero L]
    (m : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
    (h_cor1_loc : ∀ (u : Box3D L) (j : ℕ), 1 ≤ j → j + 2 ≤ Nat.floor (cStarBDL * (L : ℝ)) →
      ∀ S : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)),
        IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxCube u j) S →
        ‖m.sys.localGroundProj (singleCubeSupportC (collarConstRCABDL : ℝ) u j) * S‖ ≤ ‖m.sys.P0 * S‖)
    (h_fw_spec : ∀ (W : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes 3 L r,
        m.Pi_safe * (W.term r A * m.O_dec_Z - m.O_dec_Z * W.term r A) * m.Pi_safe = 0 ∧
        m.Pi_safe * (W.term r A * m.O_dec_X - m.O_dec_X * W.term r A) * m.Pi_safe = 0)
    (hK1 : 1 ≤ K)
    (hKL : (2 * K + 1) + 2 ≤ Nat.floor (cStarBDL * (L : ℝ)))
    (hK_fw : linearExpansionRadius (collarConstRCABDL : ℝ) (2 * K + 1 + bhmElementaryCubeSide) ≤ r_fw)
    (hr_LR : 2 * K + 1 ≤ r_fw)
    {g_LR g_tail0 : ℕ → ℝ} (hg_LR : IsSuperpolynomialDecay g_LR) (hg_tail0 : IsSuperpolynomialDecay g_tail0)
    {J J_0 m_0 δ_0 : ℝ} (hm0_nn : 0 ≤ m_0) (hJ_nn : 0 ≤ J) (hJ_le : J ≤ J_0) (hJ_le_one : J ≤ 1)
    (hJ0_le : J_0 ≤ bhmUniformCouplingThreshold 3 (3 * (collarConstRCABDL : ℝ)) m_0 (fun r => g_tail0 r + g_LR r))
    (hδ_lt : δ_0 < 1 / 4)
    (h_LR_J0 : 4 * (J_0 * g_LR K) ^ 2 ≤ δ_0)
    (h_rem_J0 : 2 * (((L : ℝ) ^ 3) * (5 * (J_0 * (g_tail0 K + g_LR K)))) ≤ δ_0)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (h_qac_L :
      ∃ (U_QAC : ℝ → unitary (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
        (X_QAC : ℝ → Box3D L → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))),
        (∀ (v : Box3D L)
          (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
            ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
          IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v → ∀ r : ℕ,
            ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
              condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v r)
                ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤ (J * g_LR r) * ‖A_v‖) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) 1,
          (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap m.sys V u) →
          let V_s := scaleQuasiLocalPerturbation s V
          let H_dress := (U_QAC s).1† * (m.sys.H0 + V_s.totalPerturbation) * (U_QAC s).1
          (∑ u : Box3D L, X_QAC s u) = H_dress - m.sys.H0 ∧
          (∀ u : Box3D L, IsSelfAdjoint (X_QAC s u)) ∧
          (∀ u : Box3D L,
            ‖X_QAC s u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u K) (X_QAC s u)‖ +
              ‖m.sys.P0 * (X_QAC s u) * (1 - m.sys.P0)‖ ≤ J * g_tail0 K) ∧
          (∀ j ∈ Finset.Icc 1 K, ∀ u : Box3D L,
            ‖X_QAC s u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j) (X_QAC s u)‖ ≤
              J * g_tail0 j) ∧
          (∀ u : Box3D L, ‖X_QAC s u‖ ≤ J * m_0 / 2)) :
    HasZeroTempDressingBundle m V (6 * δ_0) g_LR := by
  let δ_split_L := 6 * δ_0
  rcases h_qac_L with ⟨U_QAC, X_QAC, h_1site_all, h_boot_props⟩
  let g_tail : ℕ → ℝ := fun r => g_tail0 r + g_LR r
  have hg_tail : IsSuperpolynomialDecay g_tail := isSuperpolynomialDecay_add hg_tail0 hg_LR
  have hC : (1 : ℝ) ≤ (collarConstRCABDL : ℝ) := one_le_collar_const_rca_bdl_twoBlock
  have h3C : (1 : ℝ) ≤ 3 * (collarConstRCABDL : ℝ) := by linarith
  haveI : NeZero 3 := ⟨by decide⟩
  have hδ0_nn : 0 ≤ δ_0 := le_trans (by positivity) h_LR_J0
  have hδ0_le_δ : δ_0 ≤ δ_split_L := by dsimp [δ_split_L]; linarith
  have hX_sum : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap m.sys V u) →
      (∑ u : Box3D L, X_QAC s u) =
        (U_QAC s).1† * (m.sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) * (U_QAC s).1 -
          m.sys.H0 :=
    fun s hs h_gap => (h_boot_props s hs h_gap).1
  have hX_sa : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap m.sys V u) →
      ∀ u : Box3D L, IsSelfAdjoint (X_QAC s u) :=
    fun s hs h_gap => (h_boot_props s hs h_gap).2.1
  have h_off_K : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap m.sys V u) →
      ∀ u : Box3D L,
        ‖X_QAC s u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u K) (X_QAC s u)‖ +
          ‖m.sys.P0 * (X_QAC s u) * (1 - m.sys.P0)‖ ≤ J * g_tail K := by
    intro s hs h_gap u
    have h0 := (h_boot_props s hs h_gap).2.2.1 u
    have hg_le : J * g_tail0 K ≤ J * g_tail K :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hg_LR.1 K)) hJ_nn
    exact le_trans h0 hg_le
  have h_tail : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap m.sys V u) →
      ∀ j ∈ Finset.Icc 1 K, ∀ u : Box3D L,
        ‖X_QAC s u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j) (X_QAC s u)‖ ≤ J * g_tail j := by
    intro s hs h_gap j hj u
    have h0 := (h_boot_props s hs h_gap).2.2.2.1 j hj u
    have hg_le : J * g_tail0 j ≤ J * g_tail j :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hg_LR.1 j)) hJ_nn
    exact le_trans h0 hg_le
  have hX_norm : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap m.sys V u) →
      ∀ u : Box3D L, ‖X_QAC s u‖ ≤ J * m_0 / 2 :=
    fun s hs h_gap => (h_boot_props s hs h_gap).2.2.2.2
  have hc_LR_nn : 0 ≤ g_LR K := hg_LR.1 K
  have hε_LR_nn : 0 ≤ J * g_LR K := mul_nonneg hJ_nn hc_LR_nn
  have h_gap_all := indexedSpectralGap_bootstrap_on_Icc_of_siteFamily_boxBall_norm_of_cor1_loc
    m.sys (fun idx => by rw [(m.h_sys_checks idx).2.2])
    V hC m.h_tqo.1 h_cor1_loc hK1 hKL U_QAC X_QAC hg_tail
    hJ_nn hJ_le hm0_nn hJ0_le h_rem_J0 hδ_lt hX_sum hX_sa h_off_K h_tail hX_norm
  have h1_mem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  let U_dress := U_QAC 1
  let X_u := X_QAC 1
  have h_sum_1 : (∑ u : Box3D L, X_u u) =
      U_dress.1† * (m.sys.H0 + V.totalPerturbation) * U_dress.1 - m.sys.H0 := by
    have hs := hX_sum 1 h1_mem h_gap_all; rwa [scaleQuasiLocalPerturbation_one] at hs
  have h_sa_1 : ∀ u : Box3D L, IsSelfAdjoint (X_u u) := hX_sa 1 h1_mem h_gap_all
  have h_off_K_1 : ∀ u : Box3D L,
      ‖X_u u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u K) (X_u u)‖ +
        ‖m.sys.P0 * (X_u u) * (1 - m.sys.P0)‖ ≤ J * g_tail K :=
    h_off_K 1 h1_mem h_gap_all
  have h_tail_1 : ∀ j ∈ Finset.Icc 1 K, ∀ u : Box3D L,
      ‖X_u u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j) (X_u u)‖ ≤ J * g_tail j :=
    h_tail 1 h1_mem h_gap_all
  have hX_norm_1 : ∀ u : Box3D L, ‖X_u u‖ ≤ J * m_0 / 2 := hX_norm 1 h1_mem h_gap_all
  let ε_tail : ℕ → ℝ := fun j => J * g_tail j
  let M0 : ℝ := J * m_0
  let c_u := fun u : Box3D L => tqo1SiteBallCondExpScalar m.sys K u (X_u u)
  let δ_shell : ℕ → ℝ := fun j =>
    (bhmTelescopingFactor * ε_tail j + 2 * ε_tail K) +
      (if j = 1 then M0 else bhmTelescopingFactor * ε_tail (j - 1) + 2 * ε_tail K)
  have h_mom_pair := bhmShellNormalizedMomentSum_le_uniform 3 h3C hm0_nn hg_tail hK1
  have h_splits := lr_and_rem_split_le_of_J_proportional (ε_tail := ε_tail)
    hJ_nn hJ_le hε_LR_nn hc_LR_nn le_rfl (hg_tail.1 K) le_rfl h_LR_J0 h_rem_J0
  have h_norm0 : ∀ u : Box3D L,
      ‖centeredSiteOp (X_u u) (tqo1SiteBallCondExpScalar m.sys K u (X_u u))‖ ≤ M0 := by
    intro u
    have h1 := norm_centeredSiteOp_tqo1SiteBallCondExpScalar_le_two_mul_norm
      m.sys m.h_tqo.1 (by omega : 2 * K + 1 ≤ Nat.floor (cStarBDL * (L : ℝ))) u (h_sa_1 u)
    have h2 := hX_norm_1 u
    dsimp only [X_u, M0] at h1 h2 ⊢; linarith
  have h_bounds :=
    centeredSiteOp_diffD_and_rem_bounds_of_multiScale_boxBall_condExp_and_cor1_loc_of_offDiag
      m.sys m.h_tqo.1 h_cor1_loc hK1 hKL X_u ε_tail M0
      h_sa_1 h_tail_1 h_off_K_1 h_norm0
  have hδ_nn : ∀ j ∈ Finset.Icc 1 K, 0 ≤ δ_shell j := by
    intro j _hj; dsimp [δ_shell, bhmTelescopingFactor, ε_tail, M0]
    have hj_nn := mul_nonneg hJ_nn (hg_tail.1 j)
    have hK_nn := mul_nonneg hJ_nn (hg_tail.1 K)
    have hM0_nn := mul_nonneg hJ_nn hm0_nn
    by_cases hj_eq1 : j = 1
    · rw [if_pos hj_eq1]; linarith
    · rw [if_neg hj_eq1]; have hprev_nn := mul_nonneg hJ_nn (hg_tail.1 (j - 1)); linarith
  have h_slope := slope_bhmShell_le_bhmSandwichDeviation_of_J_le
    3 (3 * (collarConstRCABDL : ℝ)) hK1 hJ_nn h_mom_pair.1 le_rfl (fun _ _ => le_rfl) h_mom_pair.2
    (le_trans hJ_le hJ0_le)
  have h_coh_Z := le_trans
    (coherent_dressed_pinched_commutator_le_of_siteFamily_boxBall
      m.sys V U_dress X_u h_sum_1 m.Pi_safe m.O_dec_Z
      m.h_decoder_props.1.1 m.h_decoder_props.2.1.2.2.1
      m.h_decoder_props.2.1.2.2.2.1 (fun W r hr A hA => (h_fw_spec W r hr A hA).1)
      hC K hK_fw c_u h_bounds.2.1 h_splits.2)
    hδ0_le_δ
  have h_coh_X := le_trans
    (coherent_dressed_pinched_commutator_le_of_siteFamily_boxBall
      m.sys V U_dress X_u h_sum_1 m.Pi_safe m.O_dec_X
      m.h_decoder_props.1.1 m.h_decoder_props.2.2.1.2.2.1
      m.h_decoder_props.2.2.1.2.2.2.1 (fun W r hr A hA => (h_fw_spec W r hr A hA).2)
      hC K hK_fw c_u h_bounds.2.1 h_splits.2)
    hδ0_le_δ
  refine ⟨U_dress, ∑ u : Box3D L, c_u u, ?_, ?_, ?_, h_coh_Z, h_coh_X, ?_⟩
  · intro v A_v hA_v r
    have h1 := h_1site_all v A_v hA_v r
    have hJ_g : J * g_LR r ≤ 1 * g_LR r := mul_le_mul_of_nonneg_right hJ_le_one (hg_LR.1 r)
    have h2 : (J * g_LR r) * ‖A_v‖ ≤ ‖A_v‖ * g_LR r := by
      calc (J * g_LR r) * ‖A_v‖ ≤ (1 * g_LR r) * ‖A_v‖ :=
            mul_le_mul_of_nonneg_right hJ_g (norm_nonneg A_v)
        _ = ‖A_v‖ * g_LR r := by ring
    exact le_trans h1 h2
  · have h_P0_comm := dressed_P0_commutator_le_of_siteFamily_boxBall
      m.sys V U_dress X_u h_sum_1 hC K c_u h_sa_1 h_bounds.2.1 h_splits.2
    exact le_trans h_P0_comm (by linarith)
  · intro ψ
    have hf_form := relative_form_bound_of_siteFamily_boxBall (δ_split := δ_0)
      m.sys (fun idx => by rw [(m.h_sys_checks idx).2.2]) V U_dress X_u h_sum_1
      hC K c_u δ_shell hδ_nn h_sa_1 h_bounds.2.2 h_bounds.2.1 h_slope (by linarith [h_splits.2]) ψ
    have h_div4 : δ_0 / 2 ≤ δ_split_L / 4 := by dsimp [δ_split_L]; linarith
    have h_mul := mul_le_mul_of_nonneg_right h_div4 (sq_nonneg ‖ψ‖)
    linarith [hf_form, h_mul]
  · intro v A_v hA_v
    have h_tail_K := h_1site_all v A_v hA_v K
    have h_card_pos : (1 : ℝ) ≤ (Fintype.card (BoxD 3 L) : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := BoxD 3 L)
    have h_2J_le_δ : 2 * (J * g_LR K) ≤ δ_split_L := by
      have hJ_g_le : J * g_LR K ≤ ε_tail K :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hg_tail0.1 K)) hJ_nn
      have h_eps_nn : 0 ≤ ε_tail K := mul_nonneg hJ_nn (hg_tail.1 K)
      have h_card_mul : 5 * ε_tail K ≤ (Fintype.card (BoxD 3 L) : ℝ) * (5 * ε_tail K) :=
        le_mul_of_one_le_left (by positivity) h_card_pos
      have h_splits_rem := le_trans h_splits.2 hδ0_le_δ
      linarith
    have hZ_fw := pi_safe_commutator_condExp_boxBall_eq_zero m.Pi_safe m.O_dec_Z
      (fun W r hr A hA => (h_fw_spec W r hr A hA).1) v hr_LR
      ((U_QAC 1).1† * A_v * (U_QAC 1).1)
    have hX_fw := pi_safe_commutator_condExp_boxBall_eq_zero m.Pi_safe m.O_dec_X
      (fun W r hr A hA => (h_fw_spec W r hr A hA).2) v hr_LR
      ((U_QAC 1).1† * A_v * (U_QAC 1).1)
    have hZ_le := norm_dressed_pinched_commutator_le_two_mul_qac_tail_clm
      (U_QAC 1) m.Pi_safe m.O_dec_Z A_v
      (condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v K) ((U_QAC 1).1† * A_v * (U_QAC 1).1))
      m.h_decoder_props.1.1 m.h_decoder_props.2.1.2.2.1 hZ_fw
    have hX_le := norm_dressed_pinched_commutator_le_two_mul_qac_tail_clm
      (U_QAC 1) m.Pi_safe m.O_dec_X A_v
      (condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v K) ((U_QAC 1).1† * A_v * (U_QAC 1).1))
      m.h_decoder_props.1.1 m.h_decoder_props.2.2.1.2.2.1 hX_fw
    have h_mid : 2 * ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
        condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v K) ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤ δ_split_L * ‖A_v‖ := by
      have h1 : 2 * ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
          condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v K) ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤
          (2 * (J * g_LR K)) * ‖A_v‖ := by linarith
      exact le_trans h1 (mul_le_mul_of_nonneg_right h_2J_le_δ (norm_nonneg A_v))
    exact ⟨le_trans hZ_le h_mid, le_trans hX_le h_mid⟩

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible] HasZeroTempDressingBundle

/-- **Zero-Temperature Perturbative Dressing Bundle (`bdl_inhomogeneous_zero_temp_dressing_bundle_exists`)
    (`bdl_inhomogeneous_zero_temp_dressing_bundle_exists`)**:
    Combines `kato_hastings_band_limited_qac_site_family_of_gap_bootstrap` (`SpectralLowPassFilterClosure`)
    with `indexedSpectralGap_bootstrap_on_Icc_of_siteFamily_boxBall_norm_of_cor1_loc` and
    `dressed_P0_commutator_le_of_siteFamily_boxBall` to produce the quasi-local dressing unitary
    `U_dress`, scalar shift `E0`, approximate ground-space commutation `≤ δ_split L / 6`,
    full-spectrum relative form stability, coherent safe-subspace drift bound, and linear 1-site
    safe-subspace immunity bound for all scales `k ≥ k_0` and couplings `0 ≤ J ≤ J_0`. -/
theorem bdl_inhomogeneous_zero_temp_dressing_bundle_exists
    (mem : ∀ k : ℕ, Inhomogeneous3DMemoryRealization (bdlBoxSide k)
        qCodeBDL r0BDL mMaxBDL cStarBDL (collarConstRCABDL : ℝ)
        betaCritBDL cFBDL etaBDL cMemBDL)
    (h_mem_spec : ∀ k : ℕ,
      (mem k).D_field = bdlLocalDescriptor k ∧
      (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k) (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
          (mem k).Pi_safe * (W.term r A * (mem k).O_dec_Z - (mem k).O_dec_Z * W.term r A) *
            (mem k).Pi_safe = 0 ∧
          (mem k).Pi_safe * (W.term r A * (mem k).O_dec_X - (mem k).O_dec_X * W.term r A) *
            (mem k).Pi_safe = 0))
    (f : ℕ → ℝ) (hf : IsSuperpolynomialDecay f) :
    ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
      0 < J_0 ∧
      IsSuperpolynomialDecay δ_split ∧
      IsSuperpolynomialDecay g_LR ∧
      ∀ (k : ℕ), k_0 ≤ k →
        ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
          ∀ (V : QuasiLocalPerturbation 3 (bdlBoxSide k) (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
            V.SatisfiesDecayBound J f →
            HasZeroTempDressingBundle (mem k) V (δ_split (bdlBoxSide k)) g_LR := by
  rcases kato_hastings_band_limited_qac_site_family_of_gap_bootstrap f hf with
    ⟨g_LR, g_tail0, m_0, hg_LR, hg_tail0, hm0_nn, h_qac_flow⟩
  let g_tail : ℕ → ℝ := fun r => g_tail0 r + g_LR r
  have hg_tail : IsSuperpolynomialDecay g_tail := isSuperpolynomialDecay_add hg_tail0 hg_LR
  have hC : (1 : ℝ) ≤ (collarConstRCABDL : ℝ) := one_le_collar_const_rca_bdl_twoBlock
  have h3C : (1 : ℝ) ≤ 3 * (collarConstRCABDL : ℝ) := by linarith
  let J_0 : ℝ := bhmUniformCouplingThreshold 3 (3 * (collarConstRCABDL : ℝ)) m_0 g_tail
  have hJ0_pos : 0 < J_0 := bhmUniformCouplingThreshold_pos 3 h3C hm0_nn hg_tail
  have hJ0_le_one : J_0 ≤ 1 := bhmUniformCouplingThreshold_le_one 3 h3C hm0_nn hg_tail
  let δ_split0 : ℕ → ℝ := bdlExactSplittingEnvelope J_0 g_tail g_LR
  have hδ0_super : IsSuperpolynomialDecay δ_split0 :=
    isSuperpolynomialDecay_bdlExactSplittingEnvelope (le_of_lt hJ0_pos) hg_tail hg_LR
  let δ_split : ℕ → ℝ := fun L => 6 * δ_split0 L
  have hδ_super : IsSuperpolynomialDecay δ_split :=
    isSuperpolynomialDecay_const_mul hδ0_super (by norm_num)
  rcases exists_k_eight_of_isSuperpolynomialDecay hδ0_super with ⟨k_8, hk_8⟩
  refine ⟨J_0, max 7 k_8, δ_split, g_LR, hJ0_pos, hδ_super, hg_LR,
    fun k hk J hJ_nn hJ_le V hV_dec => ?_⟩
  have hk7 : 7 ≤ k := le_trans (le_max_left 7 k_8) hk
  have hk4 : 4 ≤ k := by omega
  have hk8_le : k_8 ≤ k := le_trans (le_max_right 7 k_8) hk
  have hJ_le_one : J ≤ 1 := le_trans hJ_le hJ0_le_one
  exact zero_temp_dressing_bundle_at_L (mem k)
    (mem_cor1_loc_of_D_field_eq k (mem k) (h_mem_spec k).1)
    (h_mem_spec k).2
    (one_le_bdlScaleCutoffK k)
    (two_mul_bdlScaleCutoffK_add_three_le_L_star hk4)
    (linearExpansionRadius_collar_const_rca_bdl_two_mul_bdlScaleCutoffK_add_one_le_safe_radius hk4)
    (two_mul_bdlScaleCutoffK_add_one_le_bdlLambda_pow hk4)
    hg_LR hg_tail0 hm0_nn hJ_nn hJ_le hJ_le_one le_rfl
    ((hk_8 k hk8_le).2)
    (four_mul_sq_J0_g_LR_le_bdlExactSplittingEnvelope J_0 g_tail g_LR hk7)
    (two_mul_vol_five_J0_g_tail_le_bdlExactSplittingEnvelope J_0 g_tail g_LR hk7)
    V (h_qac_flow k hk4 rfl (mem k) J hJ_nn hJ_le_one V hV_dec)

end
