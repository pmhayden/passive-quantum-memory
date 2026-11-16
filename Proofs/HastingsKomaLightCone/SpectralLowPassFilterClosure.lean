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

import Proofs.HastingsKomaLightCone.KatoHastingsSubspaceIntertwining

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Block-Diagonal Dressed Site Family Closure under Gap Bootstrap

Combines `IsKatoHastingsFlowSystem` and `IsSmoothBandpassFilterWeight` to construct the block-diagonal dressed site operator family (`kato_hastings_band_limited_qac_site_family_of_gap_bootstrap`). Establishes exact commutation with the reference ground projector, telescoping sum identity, self-adjointness, operator norm bounds, and centered-ball superpolynomial tail decay.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (78) (`eq:Xu-norm-and-tail`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
-/

/-- **General Band-Limited Kato–Hastings Site-Family Bridge
    (`kato_flow_band_limited_site_family_properties`)**. -/
theorem kato_flow_band_limited_site_family_properties {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem sys.P0 D_gen U_flow P_flow)
    {w : ℝ → ℂ} (hw_int : Integrable w) (hw_one : (∫ t : ℝ, w t) = 1)
    (hw_real : ∀ t : ℝ, star (w t) = w t) (s : ℝ)
    (h_comm_bare : Commute (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) (P_flow s))
    (h_bare_offDiag : ∀ Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      twoBlockOffDiagProj (P_flow s)
        (bochnerFilteredOp (sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation) w Y) = 0) :
    let V_s := scaleQuasiLocalPerturbation s V
    let U_s := katoFlowUnitary hFlow s
    let H_dress := U_s.1† * (sys.H0 + V_s.totalPerturbation) * U_s.1
    let X_u := fun u : BoxD D L =>
      bochnerFilteredSiteOp H_dress U_s.1 w (sitePerturbationOp V_s u) (sys.siteCheckOp u)
    Commute H_dress sys.P0 ∧
    (∑ u : BoxD D L, X_u u) = H_dress - sys.H0 ∧
    (∀ u : BoxD D L, IsSelfAdjoint (X_u u)) ∧
    (∀ u : BoxD D L, Commute (X_u u) sys.P0) ∧
    (∀ u : BoxD D L, twoBlockOffDiagProj sys.P0 (X_u u) = 0) := by
  intro V_s U_s H_dress X_u
  have hHs_sa : IsSelfAdjoint (sys.H0 + V_s.totalPerturbation) :=
    isSelfAdjoint_add_clm sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have hH_dress_sa : IsSelfAdjoint H_dress :=
    isSelfAdjoint_conj_adjoint hHs_sa U_s.1
  have h_comm_dress : Commute H_dress sys.P0 := by
    have h_ode := (qac_ode_flow_properties sys V hFlow s).2.2.2.1
    dsimp [interpolatedHamiltonianOp, interpolatedHamiltonian] at h_ode
    rw [← scaleQuasiLocalPerturbation_V_tot s V] at h_ode
    exact h_ode h_comm_bare
  have h_sum : (∑ u : BoxD D L, X_u u) = H_dress - sys.H0 := by
    exact (sum_bochnerFilteredSiteOp_eq_H'_sub_H0
      sys.H0 V_s.totalPerturbation H_dress U_s.1 w
      (sitePerturbationOp V_s) sys.siteCheckOp
      (sum_sitePerturbationOp_eq_V_tot V_s)
      sys.sum_siteCheckOp_eq_H0 rfl hw_one
      (fun X => integrable_smul_heisenbergFlow_of_integrable hH_dress_sa hw_int X)).1
  have h_sa : ∀ u : BoxD D L, IsSelfAdjoint (X_u u) := fun u =>
    isSelfAdjoint_bochnerFilteredSiteOp hH_dress_sa
      (isSelfAdjoint_sitePerturbationOp V_s u)
      (sys.isSelfAdjoint_siteCheckOp u) hw_real
  have h_off_and_comm : ∀ u : BoxD D L,
      twoBlockOffDiagProj sys.P0 (X_u u) = 0 ∧ Commute (X_u u) sys.P0 := by
    intro u
    rcases siteCheckOp_mul_P0_and_P0_mul_eq_zero sys u with ⟨hQP0, hP0Q⟩
    have h1 := twoBlockOffDiagProj_dressed_bochnerFilteredSiteOp_eq_zero
      hFlow sys.isStarProjection_P0.isIdempotentElem.eq hHs_sa hw_int s
      (V_u := sitePerturbationOp V_s u) (Q_u := sys.siteCheckOp u) hQP0 hP0Q h_bare_offDiag
    exact ⟨h1.1, h1.2.2.2⟩
  exact ⟨h_comm_dress, h_sum, h_sa, fun u => (h_off_and_comm u).2, fun u => (h_off_and_comm u).1⟩

attribute [local irreducible] collarConstRCABDL bdlLambda qCodeBDL r0BDL mMaxBDL

/-- Unconditional telescoping sum and self-adjointness of `bochnerFilteredSiteOp` (`X_raw`)
    for any `IsSmoothBandpassFilterWeight w`. -/
theorem bochnerFilteredSiteOp_properties_of_smooth {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V_s : QuasiLocalPerturbation D L Site)
    (U_s : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw : IsSmoothBandpassFilterWeight w) :
    let H_dress := U_s.1† * (sys.H0 + V_s.totalPerturbation) * U_s.1
    let X_u := fun u : BoxD D L =>
      bochnerFilteredSiteOp H_dress U_s.1 w (sitePerturbationOp V_s u) (sys.siteCheckOp u)
    (∑ u : BoxD D L, X_u u) = H_dress - sys.H0 ∧
    (∀ u : BoxD D L, IsSelfAdjoint (X_u u)) := by
  intro H_dress X_u
  have hHs_sa : IsSelfAdjoint (sys.H0 + V_s.totalPerturbation) :=
    isSelfAdjoint_add_clm sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have hH_dress_sa : IsSelfAdjoint H_dress := isSelfAdjoint_conj_adjoint hHs_sa U_s.1
  refine ⟨(sum_bochnerFilteredSiteOp_eq_H'_sub_H0
      sys.H0 V_s.totalPerturbation H_dress U_s.1 w (sitePerturbationOp V_s) sys.siteCheckOp
      (sum_sitePerturbationOp_eq_V_tot V_s) sys.sum_siteCheckOp_eq_H0 rfl hw.integral_eq_one
      (fun X => integrable_smul_heisenbergFlow_of_integrable hH_dress_sa hw.integrable X)).1,
    fun u => isSelfAdjoint_bochnerFilteredSiteOp hH_dress_sa
      (isSelfAdjoint_sitePerturbationOp V_s u) (sys.isSelfAdjoint_siteCheckOp u) hw.star_eq_self⟩

/-- Bare-frame operator norm bound for
    `bochnerFilteredOp H_s w (mem.sys.siteCheckOp u) - mem.sys.siteCheckOp u`
    under any `IsSmoothBandpassFilterWeight w`. -/
theorem norm_bare_bochnerFilteredOp_siteCheckOp_sub_self_of_smooth_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem J s : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    {w : ℝ → ℂ} (hw : IsSmoothBandpassFilterWeight w)
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1)
    (hf : IsSuperpolynomialDecay f) (hV_dec : V.SatisfiesDecayBound J f) (u : Box3D L) :
    let V_s := scaleQuasiLocalPerturbation s V
    let H_s := mem.sys.H0 + V_s.totalPerturbation
    ‖bochnerFilteredOp H_s w (mem.sys.siteCheckOp u) - mem.sys.siteCheckOp u‖ ≤
      J * ((∫ t : ℝ, ‖w t‖ * |t|) *
        (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f)) := by
  intro V_s H_s
  have hHs_sa : IsSelfAdjoint H_s :=
    isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have h_comm_Q : Commute mem.sys.H0 (mem.sys.siteCheckOp u) := by
    rw [siteCheckOp_eq_anchoredSiteCheckOp]
    exact (isSelfAdjoint_and_commute_H0_anchoredSiteCheckOp anchorOfRegion mem.sys u).2
  have h1 := norm_bochnerFilteredOp_sub_self_le_of_commute_left
    hHs_sa h_comm_Q hw.integrable hw.integral_eq_one hw.integrable_norm_mul_abs
  have h2 := norm_opCommutator_V_tot_siteCheckOp_inhomogeneous_le mem V hJ_nn hs hf hV_dec u
  have hwt_nn : 0 ≤ ∫ t : ℝ, ‖w t‖ * |t| :=
    integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  calc ‖bochnerFilteredOp H_s w (mem.sys.siteCheckOp u) - mem.sys.siteCheckOp u‖
    _ ≤ (∫ t : ℝ, ‖w t‖ * |t|) * ‖opCommutator V_s.totalPerturbation (mem.sys.siteCheckOp u)‖ := h1
    _ ≤ (∫ t : ℝ, ‖w t‖ * |t|) *
          (J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f)) :=
      mul_le_mul_of_nonneg_left h2 hwt_nn
    _ = J * ((∫ t : ℝ, ‖w t‖ * |t|) *
          (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f)) := by ring

/-- Unconditional zero-mode operator norm bound for `bochnerFilteredSiteOp` under any
    `IsSmoothBandpassFilterWeight w`. -/
theorem norm_bochnerFilteredSiteOp_inhomogeneous_le_of_smooth {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem J s c_U_Q : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (U_s : unitary (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
    {w : ℝ → ℂ} (hw : IsSmoothBandpassFilterWeight w)
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1) (hf : IsSuperpolynomialDecay f)
    (hV_dec : V.SatisfiesDecayBound J f) (u : Box3D L)
    (h_UQ0 : ‖U_s.1† * mem.sys.siteCheckOp u * U_s.1 - mem.sys.siteCheckOp u‖ ≤ J * c_U_Q) :
    let V_s := scaleQuasiLocalPerturbation s V
    let H_dress := U_s.1† * (mem.sys.H0 + V_s.totalPerturbation) * U_s.1
    ‖bochnerFilteredSiteOp H_dress U_s.1 w (sitePerturbationOp V_s u) (mem.sys.siteCheckOp u)‖ ≤
      J * bdlBandLimitedBaseMoment w f c_U_Q / 2 := by
  intro V_s H_dress
  let H_s := mem.sys.H0 + V_s.totalPerturbation
  let V_u := sitePerturbationOp V_s u
  let Q_u := mem.sys.siteCheckOp u
  let B_V := bochnerFilteredOp H_s w V_u
  let B_Q := bochnerFilteredOp H_s w Q_u - Q_u
  let ΔQ_U := U_s.1† * Q_u * U_s.1 - Q_u
  have hHs_sa : IsSelfAdjoint H_s :=
    isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have hX_eq : bochnerFilteredSiteOp H_dress U_s.1 w V_u Q_u =
      U_s.1† * B_V * U_s.1 + U_s.1† * B_Q * U_s.1 + ΔQ_U :=
    bochnerFilteredSiteOp_eq_bare_three_term hHs_sa U_s hw.integrable V_u Q_u
  have hBV := le_trans (norm_unitary_adj_conj_le_clm U_s B_V)
    (norm_bare_bochnerFilteredOp_sitePerturbationOp_weight_inhomogeneous_le
      mem V w hJ_nn hs hf hV_dec u)
  have hBQ := le_trans (norm_unitary_adj_conj_le_clm U_s B_Q)
    (norm_bare_bochnerFilteredOp_siteCheckOp_sub_self_of_smooth_le
      mem V hw hJ_nn hs hf hV_dec u)
  have h_tri : ‖bochnerFilteredSiteOp H_dress U_s.1 w V_u Q_u‖ ≤
      ‖U_s.1† * B_V * U_s.1‖ + ‖U_s.1† * B_Q * U_s.1‖ + ‖ΔQ_U‖ := by
    rw [hX_eq]; exact norm_add_three_le _ _ _
  dsimp [bdlBandLimitedBaseMoment]
  linarith [h_tri, hBV, hBQ, h_UQ0]

/-- Multi-scale `boxBall u j` conditional expectation tail bound for `bochnerFilteredSiteOp`
    from bare-frame `boxBall u (j / 2)` bounds and unitary light-cone bounds. -/
theorem norm_bochnerFilteredSiteOp_boxBall_sub_condExp_inhomogeneous_le_of_smooth {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem J s : ℝ}
    {f g_bare_V g_bare_Q ε_LR_box g_LR_Q : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (U_s : unitary (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
    {w : ℝ → ℂ} (hw : IsSmoothBandpassFilterWeight w)
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1) (hf : IsSuperpolynomialDecay f)
    (hV_dec : V.SatisfiesDecayBound J f)
    (u : Box3D L) (j : ℕ) (hε_nn : 0 ≤ ε_LR_box j)
    (h_bare_V :
      let V_s := scaleQuasiLocalPerturbation s V
      let H_s := mem.sys.H0 + V_s.totalPerturbation
      let B_V := bochnerFilteredOp H_s w (sitePerturbationOp V_s u)
      ‖B_V - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u (j / 2)) B_V‖ ≤
        J * g_bare_V j)
    (h_bare_Q :
      let V_s := scaleQuasiLocalPerturbation s V
      let H_s := mem.sys.H0 + V_s.totalPerturbation
      let B_Q := bochnerFilteredOp H_s w (mem.sys.siteCheckOp u) - mem.sys.siteCheckOp u
      ‖B_Q - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u (j / 2)) B_Q‖ ≤
        J * g_bare_Q j)
    (h_U_box : ∀ B_loc : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)),
      IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u (j / 2)) B_loc →
      ‖U_s.1† * B_loc * U_s.1 -
        condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j)
          (U_s.1† * B_loc * U_s.1)‖ ≤
        ε_LR_box j * ‖B_loc‖)
    (h_U_Q :
      let Q_u := mem.sys.siteCheckOp u
      ‖(U_s.1† * Q_u * U_s.1 - Q_u) -
        condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j)
          (U_s.1† * Q_u * U_s.1 - Q_u)‖ ≤
        J * g_LR_Q j) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let V_s := scaleQuasiLocalPerturbation s V
    let H_dress := U_s.1† * (mem.sys.H0 + V_s.totalPerturbation) * U_s.1
    let X_u := bochnerFilteredSiteOp H_dress U_s.1 w (sitePerturbationOp V_s u) (mem.sys.siteCheckOp u)
    ‖X_u - condExp Site (boxBall u j) X_u‖ ≤
      J * bdlBandLimitedTailProfile w f g_bare_V g_bare_Q ε_LR_box g_LR_Q j := by
  intro Site V_s H_dress X_u
  let H_s := mem.sys.H0 + V_s.totalPerturbation
  let V_u := sitePerturbationOp V_s u
  let Q_u := mem.sys.siteCheckOp u
  let B_V := bochnerFilteredOp H_s w V_u
  let B_Q := bochnerFilteredOp H_s w Q_u - Q_u
  let ΔQ_U := U_s.1† * Q_u * U_s.1 - Q_u
  have hHs_sa : IsSelfAdjoint H_s :=
    isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have hX_eq : X_u = U_s.1† * B_V * U_s.1 + U_s.1† * B_Q * U_s.1 + ΔQ_U :=
    bochnerFilteredSiteOp_eq_bare_three_term hHs_sa U_s hw.integrable V_u Q_u
  have h_decomp : X_u - condExp Site (boxBall u j) X_u =
      (U_s.1† * B_V * U_s.1 - condExp Site (boxBall u j) (U_s.1† * B_V * U_s.1)) +
      (U_s.1† * B_Q * U_s.1 - condExp Site (boxBall u j) (U_s.1† * B_Q * U_s.1)) +
      (ΔQ_U - condExp Site (boxBall u j) ΔQ_U) := by
    rw [hX_eq, condExp_add, condExp_add]; abel
  have h_tri : ‖X_u - condExp Site (boxBall u j) X_u‖ ≤
      ‖U_s.1† * B_V * U_s.1 - condExp Site (boxBall u j) (U_s.1† * B_V * U_s.1)‖ +
      ‖U_s.1† * B_Q * U_s.1 - condExp Site (boxBall u j) (U_s.1† * B_Q * U_s.1)‖ +
      ‖ΔQ_U - condExp Site (boxBall u j) ΔQ_U‖ := by
    rw [h_decomp]; exact norm_add_three_le _ _ _
  have h_UV := norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail
    U_s (boxBall u (j / 2)) (boxBall u j) B_V hε_nn h_bare_V h_U_box
  have h_UQ := norm_unitary_conj_sub_condExp_le_of_bare_and_unitary_tail
    U_s (boxBall u (j / 2)) (boxBall u j) B_Q hε_nn h_bare_Q h_U_box
  have hBV_norm := mul_le_mul_of_nonneg_left
    (norm_bare_bochnerFilteredOp_sitePerturbationOp_weight_inhomogeneous_le
      mem V w hJ_nn hs hf hV_dec u) hε_nn
  have hBQ_norm := mul_le_mul_of_nonneg_left
    (norm_bare_bochnerFilteredOp_siteCheckOp_sub_self_of_smooth_le
      mem V hw hJ_nn hs hf hV_dec u) hε_nn
  dsimp [bdlBandLimitedTailProfile]
  linarith [h_tri, h_UV, h_UQ, h_U_Q, hBV_norm, hBQ_norm]

private lemma le_mul_add_of_le_mul_of_nonneg {a J c d : ℝ}
    (ha : a ≤ J * c) (hJ : 0 ≤ J) (hd : 0 ≤ d) : a ≤ J * (c + d) := by nlinarith

private lemma add_le_mul_add_of_le {a b J c d : ℝ}
    (ha : a ≤ J * c) (hb : b ≤ J * d) : a + b ≤ J * (c + d) := by linarith

/-- **Kato–Hastings Band-Limited QAC Flow & Site-Operator Decomposition
    (`kato_hastings_band_limited_qac_site_family_of_gap_bootstrap`)**. -/
theorem kato_hastings_band_limited_qac_site_family_of_gap_bootstrap
    (f : ℕ → ℝ) (hf : IsSuperpolynomialDecay f) :
    ∃ (g_LR g_tail0 : ℕ → ℝ) (m_0 : ℝ),
      IsSuperpolynomialDecay g_LR ∧ IsSuperpolynomialDecay g_tail0 ∧ 0 ≤ m_0 ∧
      ∀ (k : ℕ) (_hk4 : 4 ≤ k) {L : ℕ} [NeZero L] (_hL : L = bdlBoxSide k),
        ∀ (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
            cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
          (J : ℝ), 0 ≤ J → J ≤ 1 →
          ∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))), V.SatisfiesDecayBound J f →
            ∃ (U_QAC : ℝ → unitary (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))))
              (X_QAC : ℝ → Box3D L → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))),
              (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
                IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v → ∀ r : ℕ,
                  ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
                    condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall v r) ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤
                    (J * g_LR r) * ‖A_v‖) ∧
              ∀ s ∈ Set.Icc (0 : ℝ) 1,
                (∀ u ∈ Set.Icc 0 s, bhmPerturbedGap ≤ indexedSpectralGap mem.sys V u) →
                let V_s := scaleQuasiLocalPerturbation s V
                let H_dress := (U_QAC s).1† * (mem.sys.H0 + V_s.totalPerturbation) * (U_QAC s).1
                (∑ u : Box3D L, X_QAC s u) = H_dress - mem.sys.H0 ∧
                (∀ u : Box3D L, IsSelfAdjoint (X_QAC s u)) ∧
                (∀ u : Box3D L,
                  ‖X_QAC s u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u (bdlScaleCutoffK k)) (X_QAC s u)‖ +
                    ‖mem.sys.P0 * (X_QAC s u) * (1 - mem.sys.P0)‖ ≤ J * g_tail0 (bdlScaleCutoffK k)) ∧
                (∀ j ∈ Finset.Icc 1 (bdlScaleCutoffK k), ∀ u : Box3D L,
                  ‖X_QAC s u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j) (X_QAC s u)‖ ≤ J * g_tail0 j) ∧
                (∀ u : Box3D L, ‖X_QAC s u‖ ≤ J * m_0 / 2) := by
  let w_BL : ℝ → ℂ := bandpassFilterWeight
  have hw_BL : IsSmoothBandpassFilterWeight w_BL := isSmoothBandpassFilterWeight_w_BP
  let g_bare_V : ℕ → ℝ := bdlSchwartzPerturbationBoxBallTailProfile bandpassFilterWeight f
  let g_bare_Q : ℕ → ℝ := bdlSchwartzCheckBoxBallTailProfile f
  have hg_bare_V : IsSuperpolynomialDecay g_bare_V :=
    isSuperpolynomialDecay_bdlSchwartzPerturbationBoxBallTailProfile hf
      (fun hc => isSuperpolynomialDecay_tail_integral_norm_w_BP hc)
  have hg_bare_Q : IsSuperpolynomialDecay g_bare_Q :=
    isSuperpolynomialDecay_bdlSchwartzCheckBoxBallTailProfile hf
  rcases kato_hastings_subspace_intertwining_w_BP_of_gap_bootstrap f hf with
    ⟨f_D, g_offDiag, hf_D, hg_off, h_flow_all⟩
  let g_LR : ℕ → ℝ := hastingsKomaOneSiteTailProfile 3 f_D
  let ε_LR_box : ℕ → ℝ := hastingsKomaBoxBallHalfTailProfile f_D
  let g_LR_Q : ℕ → ℝ := hastingsKomaSiteCheckBoxBallTailProfile f_D
  let c_U_Q : ℝ := 2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D
  let g_raw_tail : ℕ → ℝ := bdlBandLimitedTailProfile w_BL f g_bare_V g_bare_Q ε_LR_box g_LR_Q
  let g_tail0 : ℕ → ℝ := fun j => g_raw_tail j + g_offDiag j
  let m_0 : ℝ := bdlBandLimitedBaseMoment w_BL f c_U_Q
  have hg_LR : IsSuperpolynomialDecay g_LR :=
    isSuperpolynomialDecay_hastingsKomaOneSiteTailProfile 3 hf_D
  have hε_box : IsSuperpolynomialDecay ε_LR_box :=
    isSuperpolynomialDecay_hastingsKomaBoxBallHalfTailProfile hf_D
  have hg_LR_Q : IsSuperpolynomialDecay g_LR_Q :=
    isSuperpolynomialDecay_hastingsKomaSiteCheckBoxBallTailProfile hf_D
  have hg_raw_tail : IsSuperpolynomialDecay g_raw_tail :=
    isSuperpolynomialDecay_bdlBandLimitedTailProfile w_BL hf hg_bare_V hg_bare_Q hε_box hg_LR_Q
  have hg_tail0 : IsSuperpolynomialDecay g_tail0 :=
    isSuperpolynomialDecay_add hg_raw_tail hg_off
  have hc_UQ_nn : 0 ≤ c_U_Q :=
    mul_nonneg (mul_nonneg zero_le_two bdlInhomogeneousSiteWeightBound_nonneg)
      (bdlInhomogeneousCommutatorBound_nonneg hf_D)
  have hm0_nn : 0 ≤ m_0 := bdlBandLimitedBaseMoment_nonneg w_BL hf hc_UQ_nn
  refine ⟨g_LR, g_tail0, m_0, hg_LR, hg_tail0, hm0_nn, ?_⟩
  intro k hk4 L _ hL mem J hJ_nn hJ1 V hV_dec
  have hKL : bdlScaleCutoffK k ≤ L := by
    rw [hL]
    exact le_trans (Finset.mem_Icc.mp (bdlScaleCutoffK_mem_Icc_safe_radius hk4)).2
      (bdlLambda_pow_k_le_bdlBoxSide k)
  rcases h_flow_all k hk4 hL mem J hJ_nn hJ1 V hV_dec with ⟨U_QAC, h_1site, h_bootstrap⟩
  let X_QAC : ℝ → Box3D L → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ] ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))) :=
    fun s u =>
      let V_s := scaleQuasiLocalPerturbation s V
      let H_dress := (U_QAC s).1† * (mem.sys.H0 + V_s.totalPerturbation) * (U_QAC s).1
      bochnerFilteredSiteOp H_dress (U_QAC s).1 w_BL
        (sitePerturbationOp V_s u) (mem.sys.siteCheckOp u)
  refine ⟨U_QAC, X_QAC, h_1site, ?_⟩
  intro s hs h_gap
  rcases h_bootstrap s hs h_gap with ⟨h_off_K, h_U_tails, h_UQ0⟩
  have h_props := bochnerFilteredSiteOp_properties_of_smooth
    mem.sys (scaleQuasiLocalPerturbation s V) (U_QAC s) hw_BL
  have h_raw_j : ∀ j ∈ Finset.Icc 1 (bdlScaleCutoffK k), ∀ u : Box3D L,
      ‖X_QAC s u - condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u j) (X_QAC s u)‖ ≤ J * g_raw_tail j := by
    intro j hj u
    have hj_cut : j / 4 ≤ L := by
      have hjK : j ≤ bdlScaleCutoffK k := (Finset.mem_Icc.mp hj).2
      omega
    have h_bare_V := norm_bare_bochnerFilteredOp_w_BP_sitePerturbationOp_boxBall_sub_condExp_le
      mem V hJ_nn hJ1 hs hf hV_dec u j hj_cut
    have h_bare_Q := norm_bare_bochnerFilteredOp_w_BP_siteCheckOp_boxBall_sub_condExp_le
      mem V hJ_nn hJ1 hs hf hV_dec u j hj_cut
    rcases h_U_tails j hj u with ⟨h_U_box, h_U_Q⟩
    exact norm_bochnerFilteredSiteOp_boxBall_sub_condExp_inhomogeneous_le_of_smooth
      mem V (U_QAC s) hw_BL hJ_nn hs hf hV_dec u j (hε_box.1 j)
      h_bare_V h_bare_Q h_U_box h_U_Q
  refine ⟨h_props.1, h_props.2, ?_, ?_, ?_⟩
  · intro u
    exact add_le_mul_add_of_le
      (h_raw_j (bdlScaleCutoffK k) (Finset.mem_Icc.mpr ⟨one_le_bdlScaleCutoffK k, le_rfl⟩) u)
      (h_off_K u)
  · intro j hj u
    exact le_mul_add_of_le_mul_of_nonneg (h_raw_j j hj u) hJ_nn (hg_off.1 j)
  · intro u
    exact norm_bochnerFilteredSiteOp_inhomogeneous_le_of_smooth
      mem V (U_QAC s) hw_BL hJ_nn hs hf hV_dec u (h_UQ0 u)
end
