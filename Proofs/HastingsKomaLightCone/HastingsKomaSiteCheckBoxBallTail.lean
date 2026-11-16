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

import Proofs.CenteredBallBHM.CenteredBallFormAndGapBootstrap

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# Centered-Ball Unitary Light-Cone Tails for Local Observables and Checks

Establishes superpolynomial truncation helpers (`isSuperpolynomialDecay_ite_lt`), site check operator norm bounds (`norm_siteCheckOp_inhomogeneous_le`), and Hastings–Koma unitary light-cone tail bounds (`hastingsKomaBoxBallHalfTailProfile`, `hastingsKomaSiteCheckBoxBallTailProfile`) along quasi-adiabatic continuation flows.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (70) (`eq:hastings-koma-lr`), Equations (73)–(74) (`eq:unitary-one-site-lr`, `eq:check-duhamel-WBP`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
-/

/-! ## 1. Superpolynomial Decay Truncation Helper & Site-Check Operator Norm Bound -/

/-- Replacing the finitely many values $j < N_0$ of a superpolynomially decaying function `g`
    by a nonnegative constant `C_0` preserves `IsSuperpolynomialDecay`. -/
lemma isSuperpolynomialDecay_ite_lt {g : ℕ → ℝ} (hg : IsSuperpolynomialDecay g)
    (N_0 : ℕ) {C_0 : ℝ} (hC_0 : 0 ≤ C_0) :
    IsSuperpolynomialDecay (fun j => if j < N_0 then C_0 else g j) := by
  refine ⟨fun j => by (try dsimp only); split_ifs <;> [exact hC_0; exact hg.1 j], fun n => ?_⟩
  refine (hg.2 n).congr' ?_
  filter_upwards [eventually_ge_atTop N_0] with j hj
  have h_not : ¬ j < N_0 := not_lt.mpr hj
  simp [h_not]

lemma bdlInhomogeneousCommutatorBound_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    0 ≤ bdlInhomogeneousCommutatorBound f :=
  mul_nonneg (by positivity) (tsum_nonneg fun q => mul_nonneg (by positivity) (hf.1 q))

/-- Norm bound `‖mem.sys.siteCheckOp u‖ ≤ bdlInhomogeneousSiteWeightBound`. -/
theorem norm_siteCheckOp_inhomogeneous_le {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem : ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (u : Box3D L) :
    ‖mem.sys.siteCheckOp u‖ ≤ bdlInhomogeneousSiteWeightBound := by
  let S_u := Finset.univ.filter (fun idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL =>
    anchorOfRegion (mem.sys.support idx) = u)
  rw [siteCheckOp_eq_anchoredSiteCheckOp]
  dsimp [anchoredSiteCheckOp]
  calc ‖∑ idx ∈ S_u, (mem.sys.weight idx : ℂ) • mem.sys.checkProj idx‖
    _ ≤ ∑ idx ∈ S_u, ‖(mem.sys.weight idx : ℂ) • mem.sys.checkProj idx‖ := norm_sum_le _ _
    _ ≤ ∑ idx ∈ S_u, mem.sys.weight idx := by
      refine Finset.sum_le_sum fun idx _ => ?_
      have hw_nn : 0 ≤ mem.sys.weight idx := le_trans zero_le_one (mem.sys.weight_ge_one idx)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw_nn]
      have hP : ‖mem.sys.checkProj idx‖ ≤ 1 := by
        have hproj := mem.sys.is_projector idx
        by_cases h0 : ‖mem.sys.checkProj idx‖ = 0
        · linarith
        · have hp : 0 < ‖mem.sys.checkProj idx‖ :=
            lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
          have hsq : ‖mem.sys.checkProj idx‖ * ‖mem.sys.checkProj idx‖ ≤
              1 * ‖mem.sys.checkProj idx‖ := by
            rw [one_mul, ← CStarRing.norm_star_mul_self, hproj.isSelfAdjoint.star_eq,
              hproj.isIdempotentElem.eq]
          exact le_of_mul_le_mul_right hsq hp
      nlinarith
    _ ≤ bdlInhomogeneousSiteWeightBound := sum_weight_anchorOfRegion_inhomogeneous_le mem u

/-! ## 2. Centered-Ball `h_U_box` & `h_U_Q` Hastings–Koma Light-Cone Bounds -/

/-- Superpolynomially decaying `h_U_box` tail profile for operators supported on `boxBall u (j / 2)`
    conjugated into `boxBall u j`. -/
def hastingsKomaBoxBallHalfTailProfile (f_D : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 *
    hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D) (fun r => r + 1 - r / 2) j

theorem isSuperpolynomialDecay_hastingsKomaBoxBallHalfTailProfile {f_D : ℕ → ℝ}
    (hf_D : IsSuperpolynomialDecay f_D) :
    IsSuperpolynomialDecay (hastingsKomaBoxBallHalfTailProfile f_D) := by
  have h_env : IsSuperpolynomialDecay
      (hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D) (fun r => r + 1 - r / 2)) :=
    isSuperpolynomialDecay_hastingsKomaSuperpolyEnvelope
      (hastingsKomaOneSiteConst_nonneg 3 hf_D)
      ⟨2, by decide, Eventually.of_forall fun r => by omega⟩
  have h_dom : IsSuperpolynomialDecay
      (fun j => 27 * ((j : ℝ) ^ 3 *
        hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D) (fun r => r + 1 - r / 2) j)) :=
    isSuperpolynomialDecay_const_mul (isSuperpolynomialDecay_mul_pow h_env 3) (by norm_num)
  refine ⟨fun j => mul_nonneg (by positivity)
    (hastingsKomaSuperpolyEnvelope_nonneg (hastingsKomaOneSiteConst_nonneg 3 hf_D) _ j), fun n => ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h_dom.2 n)
    (Eventually.of_forall fun j => mul_nonneg (by positivity)
      (mul_nonneg (by positivity)
        (hastingsKomaSuperpolyEnvelope_nonneg (hastingsKomaOneSiteConst_nonneg 3 hf_D) _ j))) ?_
  filter_upwards [eventually_ge_atTop 1] with j hj1
  have h_card : ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 ≤ 27 * (j : ℝ) ^ 3 := by
    have h1 : ((2 * (j / 2) + 1 : ℕ) : ℝ) ≤ 3 * (j : ℝ) := by
      have h_nat : 2 * (j / 2) + 1 ≤ 3 * j := by omega
      exact_mod_cast h_nat
    calc ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3
      _ ≤ (3 * (j : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = 27 * (j : ℝ) ^ 3 := by ring
  have h_env_nn := hastingsKomaSuperpolyEnvelope_nonneg (hastingsKomaOneSiteConst_nonneg 3 hf_D)
    (fun r => r + 1 - r / 2) j
  unfold hastingsKomaBoxBallHalfTailProfile
  calc (j : ℝ) ^ n * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 *
          hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D) (fun r => r + 1 - r / 2) j)
    _ ≤ (j : ℝ) ^ n * ((27 * (j : ℝ) ^ 3) *
          hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D) (fun r => r + 1 - r / 2) j) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right h_card h_env_nn
    _ = (j : ℝ) ^ n * (27 * ((j : ℝ) ^ 3 *
          hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D) (fun r => r + 1 - r / 2) j)) := by
      ring

/-- **Centered-Ball `h_U_box` Hastings–Koma Light-Cone `condExp` Bound
    (`norm_unitaryOfTimeEvolutionOp_boxBall_half_sub_condExp_le_J_mul`)**. -/
theorem norm_unitaryOfTimeEvolutionOp_boxBall_half_sub_condExp_le_J_mul
    {L : ℕ} [NeZero L]
    {Site : Box3D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (D_loc : QuasiLocalPerturbation 3 L Site) {J s : ℝ} {f_D : ℕ → ℝ}
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (-1) 1)
    (hf_D : IsSuperpolynomialDecay f_D) (hD_dec : D_loc.SatisfiesDecayBound J f_D)
    (u : Box3D L) (j : ℕ)
    (B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hB_loc : IsSupportedOn Site (boxBall u (j / 2)) B_loc) :
    let U_s := unitaryOfTimeEvolutionOp D_loc.totalPerturbation D_loc.isSelfAdjoint_totalPerturbation s
    ‖U_s.1† * B_loc * U_s.1 - condExp Site (boxBall u j) (U_s.1† * B_loc * U_s.1)‖ ≤
      (J * hastingsKomaBoxBallHalfTailProfile f_D j) * ‖B_loc‖ := by
  intro U_s
  haveI : NeZero 3 := ⟨by decide⟩
  let H_D := perturbationLatticeHamiltonian D_loc 1
  have hU_eq : U_s.1 = (unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s).1 := by
    change timeEvolutionOp D_loc.totalPerturbation s = timeEvolutionOp H_D.totalHamiltonian s
    rw [perturbationLatticeHamiltonian_one_H_tot]
  rw [show (J * hastingsKomaBoxBallHalfTailProfile f_D j) * ‖B_loc‖ =
      (J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) *
        hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D)
          (fun r => r + 1 - r / 2) j by unfold hastingsKomaBoxBallHalfTailProfile; ring]
  apply le_mul_hastingsKomaSuperpolyEnvelope_of_forall
  intro m
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hX_ne : (boxBall u (j / 2)).Nonempty := ⟨u, mem_boxBall_self u (j / 2)⟩
  have hd_pos : 0 < j + 1 - j / 2 := by omega
  have h_hk := norm_unitaryOfTimeEvolutionOp_adj_conj_sub_condExp_le_hastings_koma
    H_D hm_nn zero_le_one hs hX_ne hd_pos
    (regionDist_boxBall_compl_boxBall_ge u (Nat.div_le_self j 2)) B_loc hB_loc
  (try dsimp only at h_hk)
  rw [← hU_eq, Real.rpow_natCast] at h_hk
  have hs1 : H_D.s1 (m : ℝ) ≤ J * quasiLocalS1Factor 3 f_D (m : ℝ) :=
    perturbationLatticeHamiltonian_s1_le_J_mul D_loc hJ0 (by norm_num) hf_D hD_dec hm_nn
  have h_exp : Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1 ≤
      J * ((2 * quasiLocalS1Factor 3 f_D (m : ℝ)) *
        Real.exp (2 * quasiLocalS1Factor 3 f_D (m : ℝ))) := by
    refine exp_sub_one_le_J_mul_of_le_J_mul hJ0 hJ1 ?_ (by linarith)
    have := quasiLocalS1Factor_nonneg 3 hf_D (m : ℝ); positivity
  have h_card : ((boxBall u (j / 2)).card : ℝ) ≤ ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast card_boxBall_le_pow u (j / 2)
  have h_denom_pos : (0 : ℝ) < (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m := by positivity
  have h_num : 2 * ((boxBall u (j / 2)).card : ℝ) *
        (Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) * ‖B_loc‖ ≤
      (J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) *
        hastingsKomaOneSiteConst 3 f_D m := by
    unfold hastingsKomaOneSiteConst
    have h_exp_nn : 0 ≤ Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1 := by
      have h_s1_nn : 0 ≤ H_D.s1 (m : ℝ) := by
        unfold LatticeHamiltonian.s1
        exact Finset.le_sup'_of_le _ (Finset.mem_univ u)
          (Finset.sum_nonneg fun Z _ => by positivity)
      linarith [Real.one_le_exp (by positivity : 0 ≤ 2 * H_D.s1 (m : ℝ) * 1)]
    have h1 : ((boxBall u (j / 2)).card : ℝ) * (Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) ≤
        ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 *
          (J * ((2 * quasiLocalS1Factor 3 f_D (m : ℝ)) *
            Real.exp (2 * quasiLocalS1Factor 3 f_D (m : ℝ)))) :=
      mul_le_mul h_card h_exp h_exp_nn (by positivity)
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 zero_le_two) (norm_nonneg B_loc)
    linarith
  have h_div : (2 * ((boxBall u (j / 2)).card : ℝ) *
        ((Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) /
          (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m)) * ‖B_loc‖ ≤
      (J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) *
        (hastingsKomaOneSiteConst 3 f_D m /
          (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m) := by
    calc (2 * ((boxBall u (j / 2)).card : ℝ) *
            ((Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) /
              (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m)) * ‖B_loc‖
      _ = (2 * ((boxBall u (j / 2)).card : ℝ) *
            (Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) * ‖B_loc‖) /
            (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m := by ring
      _ ≤ ((J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) *
            hastingsKomaOneSiteConst 3 f_D m) /
            (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m :=
        div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
      _ = (J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) *
            (hastingsKomaOneSiteConst 3 f_D m /
              (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m) := by ring
  exact le_trans h_hk h_div

/-- Superpolynomially decaying `h_U_Q` tail profile for `ΔQ_U = U_s.1† * Q_u * U_s.1 - Q_u`
    on `boxBall u j`. -/
def hastingsKomaSiteCheckBoxBallTailProfile (f_D : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < 2 * r0BDL then
    4 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D
  else
    (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound) *
      hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D)
        (fun r => r + 1 - 2 * r0BDL) j

theorem isSuperpolynomialDecay_hastingsKomaSiteCheckBoxBallTailProfile {f_D : ℕ → ℝ}
    (hf_D : IsSuperpolynomialDecay f_D) :
    IsSuperpolynomialDecay (hastingsKomaSiteCheckBoxBallTailProfile f_D) := by
  have h_env : IsSuperpolynomialDecay
      (hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D)
        (fun r => r + 1 - 2 * r0BDL)) :=
    isSuperpolynomialDecay_hastingsKomaSuperpolyEnvelope
      (hastingsKomaOneSiteConst_nonneg 3 hf_D)
      ⟨2, by decide, by
        filter_upwards [eventually_ge_atTop (4 * r0BDL)] with r hr
        omega⟩
  have h_high : IsSuperpolynomialDecay
      (fun j => (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound) *
        hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D)
          (fun r => r + 1 - 2 * r0BDL) j) :=
    isSuperpolynomialDecay_const_mul h_env
      (mul_nonneg (by positivity) bdlInhomogeneousSiteWeightBound_nonneg)
  have hC0 : 0 ≤ 4 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D :=
    mul_nonneg (mul_nonneg (by norm_num) bdlInhomogeneousSiteWeightBound_nonneg)
      (bdlInhomogeneousCommutatorBound_nonneg hf_D)
  exact isSuperpolynomialDecay_ite_lt h_high (2 * r0BDL) hC0

/-- **Centered-Ball `h_U_Q` Hastings–Koma Light-Cone `condExp` Bound
    (`norm_unitaryOfTimeEvolutionOp_siteCheckOp_boxBall_sub_condExp_le_J_mul`)**. -/
theorem norm_unitaryOfTimeEvolutionOp_siteCheckOp_boxBall_sub_condExp_le_J_mul
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {f_D : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (D_loc : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc 0 1)
    (hf_D : IsSuperpolynomialDecay f_D) (hD_dec : D_loc.SatisfiesDecayBound J f_D)
    (u : Box3D L) (j : ℕ) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let U_s := unitaryOfTimeEvolutionOp D_loc.totalPerturbation D_loc.isSelfAdjoint_totalPerturbation s
    let ΔQ_U := U_s.1† * mem.sys.siteCheckOp u * U_s.1 - mem.sys.siteCheckOp u
    ‖ΔQ_U - condExp Site (boxBall u j) ΔQ_U‖ ≤
      J * hastingsKomaSiteCheckBoxBallTailProfile f_D j := by
  intro Site U_s ΔQ_U
  haveI : NeZero 3 := ⟨by decide⟩
  let Q_u := mem.sys.siteCheckOp u
  unfold hastingsKomaSiteCheckBoxBallTailProfile
  split_ifs with hj_lt
  · have h_ce : ‖ΔQ_U - condExp Site (boxBall u j) ΔQ_U‖ ≤ 2 * ‖ΔQ_U‖ :=
      norm_sub_condExp_le_two_mul_norm (boxBall u j) ΔQ_U
    have h_conj : U_s.1† * Q_u * U_s.1 = heisenbergFlow (0 + D_loc.totalPerturbation) (-s) Q_u := by
      rw [zero_add]
      change star (timeEvolutionOp D_loc.totalPerturbation s) * Q_u * timeEvolutionOp D_loc.totalPerturbation s =
        timeEvolutionOp D_loc.totalPerturbation (-s) * Q_u * timeEvolutionOp D_loc.totalPerturbation (-(-s))
      rw [star_timeEvolutionOp D_loc.isSelfAdjoint_totalPerturbation s, neg_neg]
    have h0_sa : IsSelfAdjoint ((0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) +
        D_loc.totalPerturbation) := by
      rw [zero_add]; exact D_loc.isSelfAdjoint_totalPerturbation
    have h_mvt := norm_heisenbergFlow_sub_self_le_of_commute_left h0_sa (Commute.zero_left Q_u) (-s)
    rw [abs_neg, abs_of_nonneg hs.1] at h_mvt
    have h_comm : ‖opCommutator D_loc.totalPerturbation Q_u‖ ≤
        J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D) := by
      have h1 := norm_opCommutator_V_tot_siteCheckOp_inhomogeneous_le mem D_loc hJ0
        ⟨zero_le_one, le_rfl⟩ hf_D hD_dec u
      rwa [scaleQuasiLocalPerturbation_one] at h1
    have h_s_le : ‖opCommutator D_loc.totalPerturbation Q_u‖ * s ≤ ‖opCommutator D_loc.totalPerturbation Q_u‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hs.2
    have h_ΔQ : ‖ΔQ_U‖ ≤
        J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D) := by
      dsimp [ΔQ_U]; rw [h_conj]
      exact le_trans h_mvt (le_trans h_s_le h_comm)
    linarith
  · have hj_ge : 2 * r0BDL ≤ j := not_lt.mp hj_lt
    have hQ_supp_j : IsSupportedOn Site (boxBall u j) Q_u :=
      isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u hj_ge
    have hQ_ce : condExp Site (boxBall u j) Q_u = Q_u :=
      condExp_eq_self_of_isSupportedOn hQ_supp_j
    have h_id : ΔQ_U - condExp Site (boxBall u j) ΔQ_U =
        U_s.1† * Q_u * U_s.1 - condExp Site (boxBall u j) (U_s.1† * Q_u * U_s.1) := by
      dsimp [ΔQ_U]; rw [condExp_sub_clm, hQ_ce]; abel
    rw [h_id]
    let H_D := perturbationLatticeHamiltonian D_loc 1
    have hU_eq : U_s.1 = (unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s).1 := by
      change timeEvolutionOp D_loc.totalPerturbation s = timeEvolutionOp H_D.totalHamiltonian s
      rw [perturbationLatticeHamiltonian_one_H_tot]
    rw [show J * ((((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound) *
          hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D)
            (fun r => r + 1 - 2 * r0BDL) j) =
        (J * (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound)) *
          hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D)
            (fun r => r + 1 - 2 * r0BDL) j by ring]
    apply le_mul_hastingsKomaSuperpolyEnvelope_of_forall
    intro m
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hX_ne : (boxBall u (2 * r0BDL)).Nonempty := ⟨u, mem_boxBall_self u (2 * r0BDL)⟩
    have hd_pos : 0 < j + 1 - 2 * r0BDL := by omega
    have h_hk := norm_unitaryOfTimeEvolutionOp_adj_conj_sub_condExp_le_hastings_koma
      H_D hm_nn zero_le_one ⟨by linarith [hs.1], hs.2⟩ hX_ne hd_pos
      (regionDist_boxBall_compl_boxBall_ge u hj_ge)
      Q_u (isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u le_rfl)
    (try dsimp only at h_hk)
    rw [← hU_eq, Real.rpow_natCast] at h_hk
    have hs1 : H_D.s1 (m : ℝ) ≤ J * quasiLocalS1Factor 3 f_D (m : ℝ) :=
      perturbationLatticeHamiltonian_s1_le_J_mul D_loc hJ0 (by norm_num) hf_D hD_dec hm_nn
    have h_exp : Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1 ≤
        J * ((2 * quasiLocalS1Factor 3 f_D (m : ℝ)) *
          Real.exp (2 * quasiLocalS1Factor 3 f_D (m : ℝ))) := by
      refine exp_sub_one_le_J_mul_of_le_J_mul hJ0 hJ1 ?_ (by linarith)
      have := quasiLocalS1Factor_nonneg 3 hf_D (m : ℝ); positivity
    have h_card : ((boxBall u (2 * r0BDL)).card : ℝ) ≤ ((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 := by
      have hc := card_boxBall_le_pow u (2 * r0BDL)
      have h_eq : 2 * (2 * r0BDL) + 1 = 4 * r0BDL + 1 := by ring
      rw [h_eq] at hc; exact_mod_cast hc
    have hQ_le : ‖Q_u‖ ≤ bdlInhomogeneousSiteWeightBound :=
      norm_siteCheckOp_inhomogeneous_le mem u
    have h_denom_pos : (0 : ℝ) < (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m := by positivity
    have h_exp_nn : 0 ≤ Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1 := by
      have h_s1_nn : 0 ≤ H_D.s1 (m : ℝ) := by
        unfold LatticeHamiltonian.s1
        exact Finset.le_sup'_of_le _ (Finset.mem_univ u)
          (Finset.sum_nonneg fun Z _ => by positivity)
      linarith [Real.one_le_exp (by positivity : 0 ≤ 2 * H_D.s1 (m : ℝ) * 1)]
    have h_num : 2 * ((boxBall u (2 * r0BDL)).card : ℝ) *
          (Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) * ‖Q_u‖ ≤
        (J * (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound)) *
          hastingsKomaOneSiteConst 3 f_D m := by
      unfold hastingsKomaOneSiteConst
      have h1 : ((boxBall u (2 * r0BDL)).card : ℝ) * ‖Q_u‖ ≤
          ((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound :=
        mul_le_mul h_card hQ_le (norm_nonneg Q_u) (by positivity)
      have h2 := mul_le_mul h1 h_exp h_exp_nn
        (mul_nonneg (by positivity) bdlInhomogeneousSiteWeightBound_nonneg)
      linarith
    refine le_trans h_hk ?_
    calc (2 * ((boxBall u (2 * r0BDL)).card : ℝ) *
            ((Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) /
              (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m)) * ‖Q_u‖
      _ = (2 * ((boxBall u (2 * r0BDL)).card : ℝ) *
            (Real.exp (2 * H_D.s1 (m : ℝ) * 1) - 1) * ‖Q_u‖) /
            (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m := by ring
      _ ≤ ((J * (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound)) *
            hastingsKomaOneSiteConst 3 f_D m) /
            (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m :=
        div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
      _ = (J * (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound)) *
            (hastingsKomaOneSiteConst 3 f_D m /
              (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m) := by ring

end
