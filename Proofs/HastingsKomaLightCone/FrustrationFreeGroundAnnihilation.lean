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

import Proofs.HastingsKomaLightCone.FlowBridgeAndCubeCommutatorFactor

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Frustration-Free Check Annihilation and Five-Term Tail Profile

Proves frustration-free ground-projector annihilation of `siteCheckOp` (`siteCheckOp_mul_P0_and_P0_mul_eq_zero`), defines the five-term superpolynomial conditional expectation tail profile (`bdlInhomogeneousTwoBlockTailProfile`), and provides Hermitian quadratic-form and Courant–Fischer eigenvalue comparison lemmas (`inner_offDiagSafeDefect_eq_proj_add`, `re_inner_offDiagSafeDefect_le_norm_mul_sq`, `opEigenvalues_le_of_affine_form_bound`, `abs_exp_neg_mul_sub_le_exp_sub_one_mul`).

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (79) (`eq:Xu-bare-three-term`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
-/

/-! ## 1. Unconditional Frustration-Free Annihilation Against `sys.P0` -/

/-- Every check projector `sys.checkProj i` of an `IndexedCommutingProjectorHamiltonian` is
    annihilated on both sides by the global ground projector `sys.P0`. -/
theorem checkProj_mul_P0_and_P0_mul_checkProj_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (i : ι) :
    sys.checkProj i * sys.P0 = 0 ∧ sys.P0 * sys.checkProj i = 0 := by
  have h_right : sys.checkProj i * sys.P0 = 0 := by
    rw [← sys.localProj_univ_eq_proj0]
    exact sys.checkProj_mul_P_loc_eq_zero i Finset.univ (Finset.subset_univ _)
  have h_left : sys.P0 * sys.checkProj i = 0 := by
    rw [← sys.localProj_univ_eq_proj0, (sys.commute_P_loc_checkProj Finset.univ i).eq,
      sys.localProj_univ_eq_proj0, h_right]
  exact ⟨h_right, h_left⟩

/-- Every site-anchored check operator `anchoredSiteCheckOp anchor_reg sys u` is annihilated on
    both sides by `sys.P0`. -/
theorem anchoredSiteCheckOp_mul_P0_and_P0_mul_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    anchoredSiteCheckOp anchor_reg sys u * sys.P0 = 0 ∧
    sys.P0 * anchoredSiteCheckOp anchor_reg sys u = 0 := by
  dsimp [anchoredSiteCheckOp]
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_mul_assoc, (checkProj_mul_P0_and_P0_mul_checkProj_eq_zero sys i).1]
    ext ψ σ; simp
  · rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_smul_comm, (checkProj_mul_P0_and_P0_mul_checkProj_eq_zero sys i).2]
    ext ψ σ; simp

/-- `sys.siteCheckOp u` is annihilated on both sides by `sys.P0`. -/
theorem siteCheckOp_mul_P0_and_P0_mul_eq_zero {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    sys.siteCheckOp u * sys.P0 = 0 ∧ sys.P0 * sys.siteCheckOp u = 0 :=
  anchoredSiteCheckOp_mul_P0_and_P0_mul_eq_zero anchorOfRegion sys u

/-! ## 2. $L$-Independent Bare-Frame Perturbation & Site-Check Bochner Filter Bounds -/

/-- **$L$-Independent Site Perturbation Norm Bound (`norm_sitePerturbationOp_inhomogeneous_le`)**:
    For any `V : QuasiLocalPerturbation 3 L Site` satisfying `V.SatisfiesDecayBound J f` with
    `0 ≤ J` and `IsSuperpolynomialDecay f`, and any `s ∈ Set.Icc 0 1`,
    `‖sitePerturbationOp (scaleQuasiLocalPerturbation s V) u‖ ≤ J * ∑' q : ℕ, (q : ℝ) ^ 3 * f q`. -/
theorem norm_sitePerturbationOp_inhomogeneous_le {L : ℕ} [NeZero L]
    {Site : Box3D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation 3 L Site)
    {J s : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1) (hf : IsSuperpolynomialDecay f)
    (hV_dec : V.SatisfiesDecayBound J f) (u : Box3D L) :
    ‖sitePerturbationOp (scaleQuasiLocalPerturbation s V) u‖ ≤
      J * ∑' q : ℕ, (q : ℝ) ^ 3 * f q := by
  have hVs_dec : (scaleQuasiLocalPerturbation s V).SatisfiesDecayBound J f :=
    satisfiesDecayBound_scaleQuasiLocalPerturbation_of_mem_Icc V hs hJ_nn hf.1 hV_dec
  have h1 : ‖sitePerturbationOp (scaleQuasiLocalPerturbation s V) u‖ ≤
      J * ∑ q ∈ Finset.Icc 1 L, f q := by
    rw [sitePerturbationOp_eq_anchoredSitePerturbationOp]
    exact norm_anchoredSitePerturbationOp_le (scaleQuasiLocalPerturbation s V) hVs_dec u
      (fun q _ A hA => boxCube_anchorOfCube hA)
  have h_sum_f : ∑ q ∈ Finset.Icc 1 L, f q ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q := by
    calc ∑ q ∈ Finset.Icc 1 L, f q
      _ ≤ ∑ q ∈ Finset.Icc 1 L, (q : ℝ) ^ 3 * f q := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).1
        have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq1
        calc f q = 1 * f q := (one_mul _).symm
          _ ≤ (q : ℝ) ^ 3 * f q := mul_le_mul_of_nonneg_right hq3 (hf.1 q)
      _ ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
        (summable_pow_mul_of_isSuperpolynomialDecay hf 3).sum_le_tsum (Finset.Icc 1 L)
          (fun q _ => mul_nonneg (by positivity) (hf.1 q))
  exact le_trans h1 (mul_le_mul_of_nonneg_left h_sum_f hJ_nn)

/-- **$L$-Independent Site-Check Commutator Bound for `Inhomogeneous3DMemoryRealization`
    (`norm_opCommutator_V_tot_siteCheckOp_inhomogeneous_le`)**:
    Without any `IsSupportedOn Site (boxCube u r_0) (mem.sys.siteCheckOp u)` hypothesis,
    `‖opCommutator (scaleQuasiLocalPerturbation s V).V_tot (mem.sys.siteCheckOp u)‖ ≤ J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f)`. -/
theorem norm_opCommutator_V_tot_siteCheckOp_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    {J s : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1) (hf : IsSuperpolynomialDecay f)
    (hV_dec : V.SatisfiesDecayBound J f) (u : Box3D L) :
    ‖opCommutator (scaleQuasiLocalPerturbation s V).totalPerturbation (mem.sys.siteCheckOp u)‖ ≤
      J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f) := by
  haveI : NeZero 3 := ⟨by decide⟩
  have hVs_dec : (scaleQuasiLocalPerturbation s V).SatisfiesDecayBound J f :=
    satisfiesDecayBound_scaleQuasiLocalPerturbation_of_mem_Icc V hs hJ_nn hf.1 hV_dec
  have h_ball_cov : ∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
      ∃ v0 : Box3D L, mem.sys.support idx ⊆ boxBall v0 r0BDL := fun idx =>
    ⟨staticCSSCheckSite idx,
      (mem.h_sys_checks idx).2.1 ▸ (staticCSSCheckSite_mem_and_subset_boxBall mem.D_field idx).2⟩
  have h1 : ‖opCommutator (scaleQuasiLocalPerturbation s V).totalPerturbation (mem.sys.siteCheckOp u)‖ ≤
      J * (2 * bdlInhomogeneousSiteWeightBound *
        uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f) := by
    rw [siteCheckOp_eq_anchoredSiteCheckOp]
    exact norm_opCommutator_V_tot_siteCheckOp_le_of_ball_cover anchorOfRegion mem.sys h_ball_cov
      (scaleQuasiLocalPerturbation s V) hJ_nn hf.1 hVs_dec u
      (sum_weight_anchorOfRegion_inhomogeneous_le mem u)
  have h_uc : uniformCubeCommutatorFactor 3 L (2 * r0BDL + 1) f ≤
      bdlInhomogeneousCommutatorBound f :=
    uniformCubeCommutatorFactor_le_tsum (D := 3) (L := L) (r_c := 2 * r0BDL + 1) hf
  have h_w_nn := bdlInhomogeneousSiteWeightBound_nonneg
  exact le_trans h1 (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h_uc (by positivity)) hJ_nn)

/-- **$L$-Independent Bare-Frame Site-Check Bochner Filter Drift Bound
    (`norm_bare_bochnerFilteredOp_siteCheckOp_sub_self_inhomogeneous_le`)**:
    Without any `IsSupportedOn Site (boxCube u r_0) (mem.sys.siteCheckOp u)` hypothesis,
    `‖bochnerFilteredOp (mem.sys.H0 + (scaleQuasiLocalPerturbation s V).V_tot) w_BH11 (mem.sys.siteCheckOp u) - mem.sys.siteCheckOp u‖ ≤ J * (2 * Real.pi * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f)`. -/
theorem norm_bare_bochnerFilteredOp_siteCheckOp_sub_self_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    {J s : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1) (hf : IsSuperpolynomialDecay f)
    (hV_dec : V.SatisfiesDecayBound J f) (u : Box3D L) :
    let V_s := scaleQuasiLocalPerturbation s V
    let H_s := mem.sys.H0 + V_s.totalPerturbation
    let Q_u := mem.sys.siteCheckOp u
    ‖bochnerFilteredOp H_s bhFilterWeight Q_u - Q_u‖ ≤
      J * (2 * Real.pi * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f) := by
  intro V_s H_s Q_u
  have hHs_sa : IsSelfAdjoint H_s :=
    isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
  have h_comm_Q : Commute mem.sys.H0 Q_u := by
    dsimp [Q_u]
    rw [siteCheckOp_eq_anchoredSiteCheckOp]
    exact (isSelfAdjoint_and_commute_H0_anchoredSiteCheckOp anchorOfRegion mem.sys u).2
  have h1 := (norm_bochnerFilteredOp_w_BH11_sub_self_le_of_commute_left hHs_sa h_comm_Q).2
  have h2 := norm_opCommutator_V_tot_siteCheckOp_inhomogeneous_le mem V hJ_nn hs hf hV_dec u
  have h3 := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  linarith

/-- $L$-independent bare perturbation tail profile at cutoff `r_cut`:
    replaces `∑ q ∈ Finset.Icc 1 r_cut, f q` by `∑' q : ℕ, f q` and
    `∑ q ∈ Finset.Icc (r_cut + 1) L, f q` by `∑' q : ℕ, if r_cut < q then f q else 0`. -/
def bdlInhomogeneousBarePerturbationTailProfile (r_cut : ℕ) (f : ℕ → ℝ) (ε_LR_bare : ℝ) : ℝ :=
  ε_LR_bare * (∑' q : ℕ, f q) +
    2 * ∑' q : ℕ, if r_cut < q then f q else 0

lemma barePerturbationTailProfile_le_bdlInhomogeneousBarePerturbationTailProfile
    (L r_cut : ℕ) {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {ε_LR_bare : ℝ} (hε : 0 ≤ ε_LR_bare) :
    barePerturbationTailProfile L r_cut f ε_LR_bare ≤
      bdlInhomogeneousBarePerturbationTailProfile r_cut f ε_LR_bare := by
  have hf_sum : Summable f := summable_of_isSuperpolynomialDecay hf
  have h_low : ∑ q ∈ Finset.Icc 1 r_cut, f q ≤ ∑' q : ℕ, f q :=
    hf_sum.sum_le_tsum (Finset.Icc 1 r_cut) (fun q _ => hf.1 q)
  let f_tail : ℕ → ℝ := fun q => if r_cut < q then f q else 0
  have hf_tail_nn : ∀ q : ℕ, 0 ≤ f_tail q := fun q => by
    dsimp [f_tail]; split_ifs <;> [exact hf.1 q; exact le_rfl]
  have hf_tail_sum : Summable f_tail :=
    Summable.of_nonneg_of_le hf_tail_nn
      (fun q => by dsimp [f_tail]; split_ifs <;> [exact le_rfl; exact hf.1 q]) hf_sum
  have h_high : ∑ q ∈ Finset.Icc (r_cut + 1) L, f q ≤ ∑' q : ℕ, f_tail q := by
    have h_eq : ∑ q ∈ Finset.Icc (r_cut + 1) L, f q =
        ∑ q ∈ Finset.Icc (r_cut + 1) L, f_tail q := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq_gt : r_cut < q := by have := (Finset.mem_Icc.mp hq).1; omega
      dsimp [f_tail]; rw [if_pos hq_gt]
    rw [h_eq]
    exact hf_tail_sum.sum_le_tsum (Finset.Icc (r_cut + 1) L) (fun q _ => hf_tail_nn q)
  dsimp [barePerturbationTailProfile, bdlInhomogeneousBarePerturbationTailProfile]
  linarith [mul_le_mul_of_nonneg_left h_low hε]

/-- **$L$-Independent Bare-Frame Perturbation `condExp` Tail Bound
    (`norm_bare_bochnerFilteredOp_sitePerturbationOp_sub_condExp_inhomogeneous_le`)**. -/
theorem norm_bare_bochnerFilteredOp_sitePerturbationOp_sub_condExp_inhomogeneous_le
    {L : ℕ} [NeZero L]
    {Site : Box3D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    (V : QuasiLocalPerturbation 3 L Site) {J s : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hs : s ∈ Set.Icc 0 1) (hf : IsSuperpolynomialDecay f)
    (hV_dec : V.SatisfiesDecayBound J f)
    (u : Box3D L) (r_cut r_bare : ℕ) (hr_cut_L : r_cut ≤ L)
    {ε_LR_bare : ℝ} (hε_LR_nn : 0 ≤ ε_LR_bare)
    (h_low_lr : ∀ q ∈ Finset.Icc 1 r_cut,
      ∀ O_q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      IsSupportedOn Site (boxCube u q) O_q →
      ‖bochnerFilteredOp H bhFilterWeight O_q -
        condExp Site (boxCube u r_bare) (bochnerFilteredOp H bhFilterWeight O_q)‖ ≤
        ε_LR_bare * ‖O_q‖) :
    let V_s := scaleQuasiLocalPerturbation s V
    let V_u := sitePerturbationOp V_s u
    ‖bochnerFilteredOp H bhFilterWeight V_u -
      condExp Site (boxCube u r_bare) (bochnerFilteredOp H bhFilterWeight V_u)‖ ≤
      J * bdlInhomogeneousBarePerturbationTailProfile r_cut f ε_LR_bare := by
  intro V_s V_u
  have hVs_dec : V_s.SatisfiesDecayBound J f :=
    satisfiesDecayBound_scaleQuasiLocalPerturbation_of_mem_Icc V hs hJ_nn hf.1 hV_dec
  have h1 := norm_bare_bochnerFilteredOp_anchoredSitePerturbationOp_sub_condExp_le_J_mul
    hH V_s hJ_nn hf.1 hVs_dec (fun q _ A hA => boxCube_anchorOfCube hA)
    u r_cut r_bare hr_cut_L hε_LR_nn h_low_lr
  have h2 := barePerturbationTailProfile_le_bdlInhomogeneousBarePerturbationTailProfile
    L r_cut hf hε_LR_nn
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hJ_nn)

/-! ## 3. $L$-Independent Five-Term Tail Profile `bdlInhomogeneousTwoBlockTailProfile` -/

/-- **$L$-Independent Five-Term Spatial Tail Profile (`bdlInhomogeneousTwoBlockTailProfile`)**:
    Replaces `∑ q ∈ Finset.Icc 1 L, f q` by `∑' q : ℕ, (q : ℝ) ^ 3 * f q` and
    `uniformCubeCommutatorFactor 3 L (2 * r_0_BDL + 1) f` by `bdlInhomogeneousCommutatorBound f`
    so the profile depends only on `f` and the five scale profiles, completely independent of `L`. -/
def bdlInhomogeneousTwoBlockTailProfile (f : ℕ → ℝ)
    (g_bare_V g_bare_Q ε_LR_box g_LR_Q g_offDiag : ℝ) : ℝ :=
  2 * g_bare_V + 2 * g_bare_Q +
    ε_LR_box * ((∑' q : ℕ, (q : ℝ) ^ 3 * f q) +
      2 * Real.pi * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f) +
    g_LR_Q + 2 * g_offDiag

lemma bdlInhomogeneousTwoBlockTailProfile_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {g_bare_V g_bare_Q ε_LR_box g_LR_Q g_offDiag : ℝ}
    (hg_V : 0 ≤ g_bare_V) (hg_Q : 0 ≤ g_bare_Q) (hε_LR : 0 ≤ ε_LR_box)
    (hg_LR_Q : 0 ≤ g_LR_Q) (hg_off : 0 ≤ g_offDiag) :
    0 ≤ bdlInhomogeneousTwoBlockTailProfile f g_bare_V g_bare_Q ε_LR_box g_LR_Q g_offDiag := by
  have h_tsum_f : 0 ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
    tsum_nonneg fun q => mul_nonneg (by positivity) (hf.1 q)
  have h_comm_f : 0 ≤ bdlInhomogeneousCommutatorBound f := mul_nonneg (by positivity) h_tsum_f
  have h_w_nn := bdlInhomogeneousSiteWeightBound_nonneg
  have h_pi_nn : 0 ≤ Real.pi := Real.pi_pos.le
  dsimp [bdlInhomogeneousTwoBlockTailProfile]
  positivity

/-- **Superpolynomial Decay of `bdlInhomogeneousTwoBlockTailProfile`
    (`isSuperpolynomialDecay_bdlInhomogeneousTwoBlockTailProfile`)**. -/
theorem isSuperpolynomialDecay_bdlInhomogeneousTwoBlockTailProfile {f : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f)
    {g_bare_V g_bare_Q ε_LR_box g_LR_Q g_offDiag : ℕ → ℝ}
    (hg_V : IsSuperpolynomialDecay g_bare_V)
    (hg_Q : IsSuperpolynomialDecay g_bare_Q)
    (hε_LR : IsSuperpolynomialDecay ε_LR_box)
    (hg_LR_Q : IsSuperpolynomialDecay g_LR_Q)
    (hg_off : IsSuperpolynomialDecay g_offDiag) :
    IsSuperpolynomialDecay (fun j =>
      bdlInhomogeneousTwoBlockTailProfile f
        (g_bare_V j) (g_bare_Q j) (ε_LR_box j) (g_LR_Q j) (g_offDiag j)) := by
  have h_tsum_f : 0 ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
    tsum_nonneg fun q => mul_nonneg (by positivity) (hf.1 q)
  have h_comm_f : 0 ≤ bdlInhomogeneousCommutatorBound f := mul_nonneg (by positivity) h_tsum_f
  have h_w_nn := bdlInhomogeneousSiteWeightBound_nonneg
  have h_pi_nn : 0 ≤ Real.pi := Real.pi_pos.le
  let C_mid := (∑' q : ℕ, (q : ℝ) ^ 3 * f q) +
    2 * Real.pi * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f
  have hC_mid_nn : 0 ≤ C_mid := by dsimp [C_mid]; positivity
  have h1 := isSuperpolynomialDecay_const_mul hg_V (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := isSuperpolynomialDecay_const_mul hg_Q (by norm_num : (0 : ℝ) ≤ 2)
  have h3 : IsSuperpolynomialDecay (fun j => ε_LR_box j * C_mid) := by
    have h_eq : (fun j => ε_LR_box j * C_mid) = (fun j => C_mid * ε_LR_box j) := by
      funext j; ring
    rw [h_eq]
    exact isSuperpolynomialDecay_const_mul hε_LR hC_mid_nn
  have h5 := isSuperpolynomialDecay_const_mul hg_off (by norm_num : (0 : ℝ) ≤ 2)
  exact isSuperpolynomialDecay_add
    (isSuperpolynomialDecay_add (isSuperpolynomialDecay_add (isSuperpolynomialDecay_add h1 h2) h3) hg_LR_Q)
    h5

/-! ## 4. Off-Diagonal Quadratic Form & Rescaled Courant–Fischer Eigenvalue Helpers -/

theorem inner_offDiagSafeDefect_eq_proj_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (ψ : ManyBodyHilbertSpace Site) :
    inner ℂ ψ ((offDiagSafeDefect Pi_safe A) ψ) =
      inner ℂ (Pi_safe ψ) (A ((1 - Pi_safe) ψ)) + inner ℂ ((1 - Pi_safe) ψ) (A (Pi_safe ψ)) := by
  unfold offDiagSafeDefect
  rw [ContinuousLinearMap.add_apply, inner_add_right]
  have hPi_adj : Pi_safe† = Pi_safe := hPi.isSelfAdjoint.star_eq
  have hPi_c_adj : (1 - Pi_safe)† = 1 - Pi_safe := hPi.one_sub.isSelfAdjoint.star_eq
  have h1 : inner ℂ ψ ((Pi_safe * A * (1 - Pi_safe)) ψ) =
      inner ℂ (Pi_safe ψ) (A ((1 - Pi_safe) ψ)) := by
    simp only [ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, hPi_adj]
  have h2 : inner ℂ ψ (((1 - Pi_safe) * A * Pi_safe) ψ) =
      inner ℂ ((1 - Pi_safe) ψ) (A (Pi_safe ψ)) := by
    simp only [ContinuousLinearMap.mul_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, hPi_c_adj]
  rw [h1, h2]

theorem re_inner_offDiagSafeDefect_le_norm_mul_sq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hPi : IsStarProjection Pi_safe)
    (R_rem : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ ψ ((offDiagSafeDefect Pi_safe R_rem) ψ))| ≤ ‖R_rem‖ * ‖ψ‖ ^ 2 := by
  let u := Pi_safe ψ; let v := (1 - Pi_safe) ψ
  rw [inner_offDiagSafeDefect_eq_proj_add hPi R_rem ψ, map_add]
  have h_tri := abs_add_le (RCLike.re (inner ℂ u (R_rem v))) (RCLike.re (inner ℂ v (R_rem u)))
  have h_uv : |RCLike.re (inner ℂ u (R_rem v))| ≤ ‖R_rem‖ * (‖u‖ * ‖v‖) := by
    calc |RCLike.re (inner ℂ u (R_rem v))| ≤ ‖inner ℂ u (R_rem v)‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖u‖ * ‖R_rem v‖ := norm_inner_le_norm u (R_rem v)
      _ ≤ ‖u‖ * (‖R_rem‖ * ‖v‖) := mul_le_mul_of_nonneg_left (R_rem.le_opNorm v) (norm_nonneg u)
      _ = ‖R_rem‖ * (‖u‖ * ‖v‖) := by ring
  have h_vu : |RCLike.re (inner ℂ v (R_rem u))| ≤ ‖R_rem‖ * (‖u‖ * ‖v‖) := by
    calc |RCLike.re (inner ℂ v (R_rem u))| ≤ ‖inner ℂ v (R_rem u)‖ := RCLike.abs_re_le_norm _
      _ ≤ ‖v‖ * ‖R_rem u‖ := norm_inner_le_norm v (R_rem u)
      _ ≤ ‖v‖ * (‖R_rem‖ * ‖u‖) := mul_le_mul_of_nonneg_left (R_rem.le_opNorm u) (norm_nonneg v)
      _ = ‖R_rem‖ * (‖u‖ * ‖v‖) := by ring
  have h_pyth : ‖ψ‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := isStarProjection_pythagorean_bhm hPi ψ
  have h_amgm : 2 * (‖u‖ * ‖v‖) ≤ ‖ψ‖ ^ 2 := by linarith [sq_nonneg (‖u‖ - ‖v‖)]
  have h_prod := mul_le_mul_of_nonneg_left h_amgm (norm_nonneg R_rem)
  linarith

theorem opEigenvalues_le_of_affine_form_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {d α : ℝ} (hα : 0 ≤ α)
    (h_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      d * ‖ϕ‖ ^ 2 + α * RCLike.re (inner ℂ ϕ (A ϕ)) ≤ RCLike.re (inner ℂ ϕ (B ϕ)))
    (ω : ManyBodyConfig Site) :
    d + α * opEigenvalues A hA ω ≤ opEigenvalues B hB ω := by
  let i := configFinEquiv Site ω
  let E0_low := eigenSpanBelow A hA i.1; let U_low := eigenSpanBelow B hB (i.1 + 1)
  have h_dim_E0 : Module.finrank ℂ E0_low = i.1 :=
    finrank_eigenSpanBelow A hA i.1 (le_of_lt i.2)
  have h_orth_E0 := E0_low.finrank_add_finrank_orthogonal
  have h_dim_U : Module.finrank ℂ U_low = i.1 + 1 :=
    finrank_eigenSpanBelow B hB (i.1 + 1) i.2
  have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
      Module.finrank ℂ (E0_lowᗮ) + Module.finrank ℂ U_low := by omega
  rcases exists_ne_zero_mem_inf_of_finrank_lt_add (E0_lowᗮ) U_low h_dim_lt with
    ⟨ϕ, hϕ_orth, hϕU, hϕ_ne⟩
  have h_A_ge : opEigenvalues A hA ω * ‖ϕ‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ (A ϕ)) := by
    apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow A hA i.1
      (sortedEigenvalues A hA i) _ hϕ_orth
    intro j hj; exact sortedEigenvalues_monotone_bhm A hA hj
  have h_B_le : RCLike.re (inner ℂ ϕ (B ϕ)) ≤ opEigenvalues B hB ω * ‖ϕ‖ ^ 2 := by
    apply re_inner_apply_H_le_of_mem_eigenSpanBelow B hB (i.1 + 1)
      (sortedEigenvalues B hB i) _ hϕU
    intro j hj; exact sortedEigenvalues_monotone_bhm B hB (Nat.lt_succ_iff.mp hj)
  have h_αA := mul_le_mul_of_nonneg_left h_A_ge hα
  have h_le : (d + α * opEigenvalues A hA ω) * ‖ϕ‖ ^ 2 ≤ opEigenvalues B hB ω * ‖ϕ‖ ^ 2 := by
    linarith [h_form ϕ]
  exact le_of_mul_le_mul_right h_le (sq_pos_of_pos (norm_pos_iff.mpr hϕ_ne))

theorem abs_exp_neg_mul_sub_le_exp_sub_one_mul {β a b ε : ℝ}
    (hβ : 0 ≤ β) (hε : 0 ≤ ε) (h_diff : |a - b| ≤ ε) :
    |Real.exp (-β * a) - Real.exp (-β * b)| ≤ (Real.exp (β * ε) - 1) * Real.exp (-β * a) := by
  rcases abs_le.mp h_diff with ⟨h_low, h_high⟩
  have h_exp_up : Real.exp (-β * b) ≤ Real.exp (β * ε) * Real.exp (-β * a) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have h_exp_low : Real.exp (-β * ε) * Real.exp (-β * a) ≤ Real.exp (-β * b) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
  have h_one_sub : 1 - Real.exp (-β * ε) ≤ Real.exp (β * ε) - 1 := by
    have h_prod : Real.exp (-β * ε) * Real.exp (β * ε) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    have h_le1 : Real.exp (-β * ε) ≤ 1 := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
    have h_ge1 : 1 ≤ Real.exp (β * ε) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by nlinarith)
    nlinarith
  rw [abs_sub_comm]; refine abs_le.mpr ⟨?_, by linarith⟩
  linarith [mul_le_mul_of_nonneg_right h_one_sub (le_of_lt (Real.exp_pos (-β * a)))]

end
