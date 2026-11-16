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

import Proofs.HastingsKomaLightCone.HastingsKomaSiteCheckBoxBallTail

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# Bare-Frame Check Light-Cone Tails and Two-Block Site Norm Bounds

Establishes bare-frame Bochner conditional expectation tail bounds (`bdlBareCheckBoxBallTailProfile`, `norm_bare_bochnerFilteredOp_siteCheckOp_boxBall_sub_condExp_inhomogeneous_le`) for filtered local check operators on centered lattice balls. Derives system-size-independent operator norm bounds (`bdlInhomogeneousTwoBlockBaseMoment`) for two-block projected dressed site terms.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`), Equation (72) (`eq:bochner-bare-Q-tail`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (78) (`eq:Xu-norm-and-tail`)
-/

/-! ## 1. Commutator-Flow Bochner MVT & Interpolated Heisenberg Flow Helpers -/

/-- If `[H0, Q_u] = 0`, `IsSupportedOn Site B Q_u`, and for all `τ ∈ Set.Icc (-Real.pi) Real.pi`
    the commutator flow satisfies `‖heisenbergFlow (H0 + V_tot) τ (opCommutator V_tot Q_u) - condExp Site B (...)‖ ≤ M`,
    then `B_Q := bochnerFilteredOp (H0 + V_tot) w_BH11 Q_u - Q_u` satisfies
    `‖B_Q - condExp Site B B_Q‖ ≤ Real.pi * M`. -/
theorem norm_bochnerFilteredOp_w_BH11_sub_self_sub_condExp_le_of_commute_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {H0 totalPerturbation Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {B : Finset (BoxD D L)} {M : ℝ}
    (h_comm : Commute H0 Q_u) (hQ_supp : IsSupportedOn Site B Q_u) (hM_nn : 0 ≤ M)
    (h_comm_flow : ∀ τ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖heisenbergFlow (H0 + totalPerturbation) τ (opCommutator totalPerturbation Q_u) -
        condExp Site B (heisenbergFlow (H0 + totalPerturbation) τ (opCommutator totalPerturbation Q_u))‖ ≤ M) :
    let B_Q := bochnerFilteredOp (H0 + totalPerturbation) bhFilterWeight Q_u - Q_u
    ‖B_Q - condExp Site B B_Q‖ ≤ Real.pi * M := by
  intro B_Q
  let Ψ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    ContinuousLinearMap.id ℂ _ - condExpCLM Site B
  have hQ_ce : condExp Site B Q_u = Q_u := condExp_eq_self_of_isSupportedOn hQ_supp
  have hΨ_Q : Ψ Q_u = 0 := by change Q_u - condExp Site B Q_u = 0; rw [hQ_ce, sub_self]
  have h_eq : B_Q - condExp Site B B_Q =
      bochnerFilteredOp (H0 + totalPerturbation) bhFilterWeight Q_u -
        condExp Site B (bochnerFilteredOp (H0 + totalPerturbation) bhFilterWeight Q_u) := by
    change Ψ B_Q = Ψ (bochnerFilteredOp (H0 + totalPerturbation) bhFilterWeight Q_u)
    dsimp [B_Q]; rw [map_sub, hΨ_Q, sub_zero]
  rw [h_eq]
  apply norm_bochnerFilteredOp_w_BH11_sub_condExp_le_of_Icc_pi (H0 + totalPerturbation) Q_u B
    (mul_nonneg Real.pi_pos.le hM_nn)
  intro t ht
  have h_deriv : ∀ τ ∈ Set.Icc (-Real.pi) Real.pi,
      HasDerivWithinAt (fun τ => Ψ (heisenbergFlow (H0 + totalPerturbation) τ Q_u))
        (Ψ ((Complex.I : ℂ) • heisenbergFlow (H0 + totalPerturbation) τ (opCommutator totalPerturbation Q_u)))
        (Set.Icc (-Real.pi) Real.pi) τ := by
    intro τ _
    have hd1 : HasDerivAt (fun τ => heisenbergFlow (H0 + totalPerturbation) τ Q_u)
        ((Complex.I : ℂ) • heisenbergFlow (H0 + totalPerturbation) τ (opCommutator totalPerturbation Q_u)) τ :=
      hasDerivAt_heisenbergFlow_of_commute_left (totalPerturbation := totalPerturbation) h_comm τ
    exact ((Ψ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt τ hd1).hasDerivWithinAt
  have h_deriv_norm : ∀ τ ∈ Set.Icc (-Real.pi) Real.pi,
      ‖Ψ ((Complex.I : ℂ) • heisenbergFlow (H0 + totalPerturbation) τ (opCommutator totalPerturbation Q_u))‖ ≤ M := by
    intro τ hτ
    rw [map_smul, norm_smul, Complex.norm_I, one_mul]
    exact h_comm_flow τ hτ
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-Real.pi) Real.pi :=
    ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
  have h_mvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    h_deriv h_deriv_norm (convex_Icc (-Real.pi) Real.pi) h0_mem ht
  have h_at_0 : Ψ (heisenbergFlow (H0 + totalPerturbation) 0 Q_u) = 0 := by
    have h0 : heisenbergFlow (H0 + totalPerturbation) 0 Q_u = Q_u := by
      unfold heisenbergFlow; rw [neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
    rw [h0, hΨ_Q]
  (try dsimp only at h_mvt)
  rw [h_at_0, sub_zero, sub_zero, Real.norm_eq_abs] at h_mvt
  have ht_abs : |t| ≤ Real.pi := abs_le.mpr ht
  calc ‖Ψ (heisenbergFlow (H0 + totalPerturbation) t Q_u)‖
    _ ≤ M * |t| := h_mvt
    _ ≤ M * Real.pi := mul_le_mul_of_nonneg_left ht_abs hM_nn
    _ = Real.pi * M := mul_comm _ _

/-- Pointwise Heisenberg flow `condExp` bound for `interpolatedLatticeHamiltonian` on `Set.Icc (-Real.pi) Real.pi`. -/
theorem norm_heisenbergFlow_interpolated_sub_condExp_inhomogeneous_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s τ : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (-1) 1) (hτ : τ ∈ Set.Icc (-Real.pi) Real.pi)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f)
    {X B : Finset (Box3D L)} (hX : X.Nonempty)
    (d : ℕ → ℕ) (r : ℕ) (hd_pos : 0 < d r)
    (h_dist : (Finset.univ \ B).Nonempty → d r ≤ regionDist X (Finset.univ \ B))
    (O_X : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hO_X : IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) X O_X) :
    let H_s := mem.sys.H0 + (scaleQuasiLocalPerturbation s V).totalPerturbation
    ‖heisenbergFlow H_s τ O_X -
      condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) B (heisenbergFlow H_s τ O_X)‖ ≤
      ((X.card : ℝ) * bdlBochnerHastingsKomaEnvelope f d r) * ‖O_X‖ := by
  intro H_s
  haveI : NeZero 3 := ⟨by decide⟩
  let H_lat := interpolatedLatticeHamiltonian mem.sys V s
  have hHs_eq : H_s = H_lat.totalHamiltonian := by
    dsimp [H_s, H_lat]
    rw [interpolatedLatticeHamiltonian_H_tot, interpolatedHamiltonianOp,
      scaleQuasiLocalPerturbation_V_tot]
  rw [hHs_eq, show ((X.card : ℝ) * bdlBochnerHastingsKomaEnvelope f d r) * ‖O_X‖ =
      ((X.card : ℝ) * ‖O_X‖) *
        hastingsKomaSuperpolyEnvelope (bdlBochnerHastingsKomaConst f) d r by
    unfold bdlBochnerHastingsKomaEnvelope; ring]
  apply le_mul_hastingsKomaSuperpolyEnvelope_of_forall
  intro m0
  have hm0_nn : (0 : ℝ) ≤ (m0 : ℝ) := Nat.cast_nonneg m0
  have h_hk := norm_heisenbergFlow_sub_condExp_le_hastings_koma
    H_lat hm0_nn Real.pi_pos.le hX hd_pos h_dist O_X hO_X hτ
  rw [Real.rpow_natCast] at h_hk
  have hs1 : H_lat.s1 (m0 : ℝ) ≤ bdlInhomogeneousInterpolatedS1Bound f (m0 : ℝ) :=
    (interpolatedLatticeHamiltonian_s1_inhomogeneous_le mem V hJ0 hJ1 (abs_le.mpr hs) hf hV hm0_nn).2
  have h_exp : Real.exp (2 * H_lat.s1 (m0 : ℝ) * Real.pi) - 1 ≤
      Real.exp (2 * bdlInhomogeneousInterpolatedS1Bound f (m0 : ℝ) * Real.pi) - 1 := by
    have h_mul : 2 * H_lat.s1 (m0 : ℝ) * Real.pi ≤
        2 * bdlInhomogeneousInterpolatedS1Bound f (m0 : ℝ) * Real.pi := by
      have := Real.pi_pos.le; nlinarith
    linarith [Real.exp_le_exp.mpr h_mul]
  have h_denom_pos : (0 : ℝ) < (1 + (d r : ℝ) / 2) ^ m0 := by positivity
  calc ‖heisenbergFlow H_lat.totalHamiltonian τ O_X -
        condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) B (heisenbergFlow H_lat.totalHamiltonian τ O_X)‖
    _ ≤ 2 * ‖O_X‖ * (X.card : ℝ) *
          ((Real.exp (2 * H_lat.s1 (m0 : ℝ) * Real.pi) - 1) / (1 + (d r : ℝ) / 2) ^ m0) := h_hk
    _ = ((X.card : ℝ) * ‖O_X‖) *
          ((2 * (Real.exp (2 * H_lat.s1 (m0 : ℝ) * Real.pi) - 1)) /
            (1 + (d r : ℝ) / 2) ^ m0) := by ring
    _ ≤ ((X.card : ℝ) * ‖O_X‖) *
          (bdlBochnerHastingsKomaConst f m0 / (1 + (d r : ℝ) / 2) ^ m0) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      unfold bdlBochnerHastingsKomaConst
      exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h_denom_pos)

/-! ## 2. Unconditional Bare-Frame `B_Q` Light-Cone `condExp` Bound on `boxBall u (j / 2)` -/

/-- Scale-$q$ commutator weight for `siteCheckOp u`:
    `2 * bdlInhomogeneousSiteWeightBound * (((q + (4 * r_0_BDL + 1) : ℕ) : ℝ) ^ 3 * f q)` for $q \ge 1$. -/
def bdlCheckCommutatorWeight (f : ℕ → ℝ) (q : ℕ) : ℝ :=
  if q = 0 then 0
  else 2 * bdlInhomogeneousSiteWeightBound * (((q + (4 * r0BDL + 1) : ℕ) : ℝ) ^ 3 * f q)

theorem isSuperpolynomialDecay_bdlCheckCommutatorWeight {f : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f) :
    IsSuperpolynomialDecay (bdlCheckCommutatorWeight f) := by
  let C_mult : ℝ := 2 * bdlInhomogeneousSiteWeightBound * ((4 * r0BDL + 2 : ℕ) : ℝ) ^ 3
  have hC_nn : 0 ≤ C_mult := by
    dsimp [C_mult]; have := bdlInhomogeneousSiteWeightBound_nonneg; positivity
  have h_dom : IsSuperpolynomialDecay (fun q => C_mult * ((q : ℝ) ^ 3 * f q)) :=
    isSuperpolynomialDecay_const_mul (isSuperpolynomialDecay_mul_pow hf 3) hC_nn
  refine ⟨fun q => by
    unfold bdlCheckCommutatorWeight
    split_ifs
    · exact le_rfl
    · have := bdlInhomogeneousSiteWeightBound_nonneg
      have := hf.1 q
      positivity, fun n => ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h_dom.2 n)
    (Eventually.of_forall fun q => by
      unfold bdlCheckCommutatorWeight
      split_ifs
      · simp
      · have := bdlInhomogeneousSiteWeightBound_nonneg
        have := hf.1 q
        positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with q hq1
  have hq0 : q ≠ 0 := by omega
  unfold bdlCheckCommutatorWeight
  rw [if_neg hq0]
  have h_pow : ((q + (4 * r0BDL + 1) : ℕ) : ℝ) ^ 3 ≤
      ((4 * r0BDL + 2 : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3 := by
    have h_le : ((q + (4 * r0BDL + 1) : ℕ) : ℝ) ≤ ((4 * r0BDL + 2 : ℕ) : ℝ) * (q : ℝ) := by
      have h_nat : q + (4 * r0BDL + 1) ≤ (4 * r0BDL + 2) * q := by nlinarith
      exact_mod_cast h_nat
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h_le 3
  have h_w_nn := bdlInhomogeneousSiteWeightBound_nonneg
  have hf_nn := hf.1 q
  calc (q : ℝ) ^ n * (2 * bdlInhomogeneousSiteWeightBound *
          (((q + (4 * r0BDL + 1) : ℕ) : ℝ) ^ 3 * f q))
    _ ≤ (q : ℝ) ^ n * (2 * bdlInhomogeneousSiteWeightBound *
          ((((4 * r0BDL + 2 : ℕ) : ℝ) ^ 3 * (q : ℝ) ^ 3) * f q)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h_pow hf_nn) (by positivity)
    _ = (q : ℝ) ^ n * (C_mult * ((q : ℝ) ^ 3 * f q)) := by dsimp [C_mult]; ring

/-- Concrete $L$-independent bare check tail profile on `boxBall u (j / 2)`. -/
def bdlBareCheckBoxBallTailProfile (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < 8 * r0BDL then
    4 * Real.pi * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f
  else
    Real.pi * bdlInhomogeneousBarePerturbationTailProfile (j / 4) (bdlCheckCommutatorWeight f)
      (((2 * (2 * r0BDL + j / 4) + 1 : ℕ) : ℝ) ^ 3 *
        bdlBochnerHastingsKomaEnvelope f (fun r => r / 2 + 1 - (2 * r0BDL + r / 4)) j)

theorem isSuperpolynomialDecay_bdlBareCheckBoxBallTailProfile {f : ℕ → ℝ}
    (hf : IsSuperpolynomialDecay f) :
    IsSuperpolynomialDecay (bdlBareCheckBoxBallTailProfile f) := by
  let f_Q := bdlCheckCommutatorWeight f
  have hf_Q : IsSuperpolynomialDecay f_Q := isSuperpolynomialDecay_bdlCheckCommutatorWeight hf
  let d_Q : ℕ → ℕ := fun r => r / 2 + 1 - (2 * r0BDL + r / 4)
  have h_env : IsSuperpolynomialDecay (bdlBochnerHastingsKomaEnvelope f d_Q) :=
    isSuperpolynomialDecay_hastingsKomaSuperpolyEnvelope
      (bdlBochnerHastingsKomaConst_nonneg hf)
      ⟨8, by decide, by
        filter_upwards [eventually_ge_atTop (16 * r0BDL)] with r hr
        dsimp [d_Q]; omega⟩
  have h_pow_env : IsSuperpolynomialDecay
      (fun j => (j : ℝ) ^ 3 * bdlBochnerHastingsKomaEnvelope f d_Q j) :=
    isSuperpolynomialDecay_mul_pow h_env 3
  have h_low : IsSuperpolynomialDecay
      (fun j => (((2 * (2 * r0BDL + j / 4) + 1 : ℕ) : ℝ) ^ 3 *
        bdlBochnerHastingsKomaEnvelope f d_Q j) * ∑' q : ℕ, f_Q q) := by
    have h_tsum_nn : 0 ≤ ∑' q : ℕ, f_Q q := tsum_nonneg hf_Q.1
    have h_dom : IsSuperpolynomialDecay
        (fun j => (27 * ∑' q : ℕ, f_Q q) *
          ((j : ℝ) ^ 3 * bdlBochnerHastingsKomaEnvelope f d_Q j)) :=
      isSuperpolynomialDecay_const_mul h_pow_env (by positivity)
    refine ⟨fun j => mul_nonneg (mul_nonneg (by positivity)
      (bdlBochnerHastingsKomaEnvelope_nonneg hf d_Q j)) h_tsum_nn, fun n => ?_⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h_dom.2 n)
      (Eventually.of_forall fun j => by
        have := bdlBochnerHastingsKomaEnvelope_nonneg hf d_Q j
        positivity) ?_
    filter_upwards [eventually_ge_atTop (8 * r0BDL + 1)] with j hj
    have h_card : ((2 * (2 * r0BDL + j / 4) + 1 : ℕ) : ℝ) ^ 3 ≤ 27 * (j : ℝ) ^ 3 := by
      have h1 : ((2 * (2 * r0BDL + j / 4) + 1 : ℕ) : ℝ) ≤ 3 * (j : ℝ) := by
        have h_nat : 2 * (2 * r0BDL + j / 4) + 1 ≤ 3 * j := by omega
        exact_mod_cast h_nat
      calc ((2 * (2 * r0BDL + j / 4) + 1 : ℕ) : ℝ) ^ 3
        _ ≤ (3 * (j : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
        _ = 27 * (j : ℝ) ^ 3 := by ring
    have h_env_nn := bdlBochnerHastingsKomaEnvelope_nonneg hf d_Q j
    calc (j : ℝ) ^ n * ((((2 * (2 * r0BDL + j / 4) + 1 : ℕ) : ℝ) ^ 3 *
            bdlBochnerHastingsKomaEnvelope f d_Q j) * ∑' q : ℕ, f_Q q)
      _ ≤ (j : ℝ) ^ n * (((27 * (j : ℝ) ^ 3) *
            bdlBochnerHastingsKomaEnvelope f d_Q j) * ∑' q : ℕ, f_Q q) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_card h_env_nn) h_tsum_nn
      _ = (j : ℝ) ^ n * ((27 * ∑' q : ℕ, f_Q q) *
            ((j : ℝ) ^ 3 * bdlBochnerHastingsKomaEnvelope f d_Q j)) := by ring
  have h_high : IsSuperpolynomialDecay
      (fun j => 2 * ∑' q : ℕ, if j / 4 < q then f_Q q else 0) :=
    isSuperpolynomialDecay_two_mul_tsum_tail hf_Q
      ⟨4, by decide, Eventually.of_forall fun j => by omega⟩
  have h_pi := isSuperpolynomialDecay_const_mul (isSuperpolynomialDecay_add h_low h_high)
    Real.pi_pos.le
  have hC0 : 0 ≤ 4 * Real.pi * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      bdlInhomogeneousSiteWeightBound_nonneg)
      (bdlInhomogeneousCommutatorBound_nonneg hf)
  exact isSuperpolynomialDecay_ite_lt h_pi (8 * r0BDL) hC0

/-- **Unconditional Bare-Frame `B_Q` `condExp` Tail Bound on `boxBall u (j / 2)`
    (`norm_bare_bochnerFilteredOp_siteCheckOp_boxBall_sub_condExp_inhomogeneous_le`)**. -/
theorem norm_bare_bochnerFilteredOp_siteCheckOp_boxBall_sub_condExp_inhomogeneous_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {f : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc 0 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f)
    (u : Box3D L) (j : ℕ) (hj_cut : j / 4 ≤ L) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let V_s := scaleQuasiLocalPerturbation s V
    let H_s := mem.sys.H0 + V_s.totalPerturbation
    let B_Q := bochnerFilteredOp H_s bhFilterWeight (mem.sys.siteCheckOp u) - mem.sys.siteCheckOp u
    ‖B_Q - condExp Site (boxBall u (j / 2)) B_Q‖ ≤
      J * bdlBareCheckBoxBallTailProfile f j := by
  intro Site V_s H_s B_Q
  haveI : NeZero 3 := ⟨by decide⟩
  let Q_u := mem.sys.siteCheckOp u
  unfold bdlBareCheckBoxBallTailProfile
  split_ifs with hj_lt
  · have h_ce : ‖B_Q - condExp Site (boxBall u (j / 2)) B_Q‖ ≤ 2 * ‖B_Q‖ :=
      norm_sub_condExp_le_two_mul_norm (boxBall u (j / 2)) B_Q
    have hBQ := norm_bare_bochnerFilteredOp_siteCheckOp_sub_self_inhomogeneous_le
      mem V hJ0 hs hf hV u
    linarith
  · have hj_ge : 8 * r0BDL ≤ j := not_lt.mp hj_lt
    let r_cut := j / 4
    let r_bare := j / 2
    let r_X := 2 * r0BDL + r_cut
    let d_Q : ℕ → ℕ := fun r => r / 2 + 1 - (2 * r0BDL + r / 4)
    let f_Q := bdlCheckCommutatorWeight f
    have hf_Q : IsSuperpolynomialDecay f_Q := isSuperpolynomialDecay_bdlCheckCommutatorWeight hf
    let ε_LR_Q : ℝ := (((2 * r_X + 1 : ℕ) : ℝ) ^ 3) * bdlBochnerHastingsKomaEnvelope f d_Q j
    have hε_nn : 0 ≤ ε_LR_Q :=
      mul_nonneg (by positivity) (bdlBochnerHastingsKomaEnvelope_nonneg hf d_Q j)
    have hVs_dec : V_s.SatisfiesDecayBound J f :=
      satisfiesDecayBound_scaleQuasiLocalPerturbation_of_mem_Icc V hs hJ0 hf.1 hV
    have h_comm_Q : Commute mem.sys.H0 Q_u := by
      dsimp [Q_u]; rw [siteCheckOp_eq_anchoredSiteCheckOp]
      exact (isSelfAdjoint_and_commute_H0_anchoredSiteCheckOp anchorOfRegion mem.sys u).2
    have hQ_supp_bare : IsSupportedOn Site (boxBall u r_bare) Q_u :=
      isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u (by omega : 2 * r0BDL ≤ r_bare)
    let S_0 := boxBall u (2 * r0BDL)
    let C_q : ℕ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      fun q => ∑ A ∈ (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0),
        opCommutator (V_s.term q A) Q_u
    have h_comm_sum : opCommutator V_s.totalPerturbation Q_u = ∑ q ∈ Finset.Icc 1 L, C_q q :=
      opCommutator_V_tot_eq_sum_filter_not_disjoint V_s
        (isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u le_rfl)
    have h_norm_q : ∀ q ∈ Finset.Icc 1 L, ‖C_q q‖ ≤ J * f_Q q := by
      intro q hq
      have hq0 : q ≠ 0 := by have := (Finset.mem_Icc.mp hq).1; omega
      have h_sub_filt : (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0) ⊆
          (boxCubes 3 L q).filter (fun A =>
            ¬ Disjoint A (boxCube (shiftCorner u (2 * r0BDL)) (4 * r0BDL + 1))) := by
        intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hA_mem, hnd⟩
        exact Finset.mem_filter.mpr ⟨hA_mem, fun hdisj =>
          hnd (Finset.disjoint_of_subset_right (boxBall_subset_boxCube u (2 * r0BDL)) hdisj)⟩
      have hcard : (((boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) ≤
          ((q + (4 * r0BDL + 1) : ℕ) : ℝ) ^ 3 := by
        have hc := le_trans (Finset.card_le_card h_sub_filt)
          (card_filter_not_disjoint_boxCube_le_pow (shiftCorner u (2 * r0BDL)) q (4 * r0BDL + 1))
        exact_mod_cast hc
      have hQ_le := norm_siteCheckOp_inhomogeneous_le mem u
      calc ‖C_q q‖
        _ ≤ ∑ A ∈ (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0),
              ‖opCommutator (V_s.term q A) Q_u‖ := norm_sum_le _ _
        _ ≤ ∑ _A ∈ (boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0),
              (2 * (J * f q) * bdlInhomogeneousSiteWeightBound) := by
          refine Finset.sum_le_sum fun A hA => ?_
          have h1 := norm_opCommutator_le (V_s.term q A) Q_u
          have h2 := hVs_dec q hq A (Finset.mem_filter.mp hA).1
          exact le_trans h1 (mul_le_mul
            (mul_le_mul_of_nonneg_left h2 zero_le_two) hQ_le (norm_nonneg Q_u)
            (mul_nonneg zero_le_two (mul_nonneg hJ0 (hf.1 q))))
        _ = (((boxCubes 3 L q).filter (fun A => ¬ Disjoint A S_0)).card : ℝ) *
              (2 * (J * f q) * bdlInhomogeneousSiteWeightBound) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((q + (4 * r0BDL + 1) : ℕ) : ℝ) ^ 3 *
              (2 * (J * f q) * bdlInhomogeneousSiteWeightBound) :=
          mul_le_mul_of_nonneg_right hcard
            (mul_nonneg (mul_nonneg zero_le_two (mul_nonneg hJ0 (hf.1 q)))
              bdlInhomogeneousSiteWeightBound_nonneg)
        _ = J * f_Q q := by dsimp [f_Q, bdlCheckCommutatorWeight]; rw [if_neg hq0]; ring
    have h_supp_q : ∀ q ∈ Finset.Icc 1 r_cut, IsSupportedOn Site (boxBall u r_X) (C_q q) := by
      intro q hq
      rcases Finset.mem_Icc.mp hq with ⟨hq1, hq_cut⟩
      have hq_L : q ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hq1, le_trans hq_cut hj_cut⟩
      have hQ_supp_X : IsSupportedOn Site (boxBall u r_X) Q_u :=
        isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u (by omega : 2 * r0BDL ≤ r_X)
      refine isSupportedOn_finset_sum (boxBall u r_X) _ _ fun A hA => ?_
      have hA_mem : A ∈ boxCubes 3 L q := (Finset.mem_filter.mp hA).1
      rcases Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hA).2 with ⟨z, hzA, hz_ball⟩
      have hA_sub : A ⊆ boxBall u r_X := by
        intro x hxA
        have hA_eq : boxCube (anchorOfCube q A) q = A := boxCube_anchorOfCube hA_mem
        have hz_cube : z ∈ boxCube (anchorOfCube q A) q := hA_eq.symm ▸ hzA
        have hx_cube : x ∈ boxCube (anchorOfCube q A) q := hA_eq.symm ▸ hxA
        dsimp only [S_0, r_X, r_cut] at hz_ball hq_cut ⊢
        simp only [boxCube, boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hz_cube hx_cube hz_ball ⊢
        have hzx : boxDist z x ≤ q := by
          dsimp [boxDist]
          refine Finset.sup_le fun i _ => ?_
          have hzi := hz_cube i; have hxi := hx_cube i
          dsimp [coordDist]; omega
        have h_tri := boxDist_triangle u z x
        omega
      have hV_supp_X : IsSupportedOn Site (boxBall u r_X) (V_s.term q A) :=
        _root_.isSupportedOn_mono hA_sub (V_s.is_supported q hq_L A hA_mem)
      exact _root_.isSupportedOn_sub (boxBall u r_X)
        (_root_.isSupportedOn_mul (boxBall u r_X) hV_supp_X hQ_supp_X)
        (_root_.isSupportedOn_mul (boxBall u r_X) hQ_supp_X hV_supp_X)
    let Ψ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
        (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      ContinuousLinearMap.id ℂ _ - condExpCLM Site (boxBall u r_bare)
    have hHs_sa : IsSelfAdjoint H_s :=
      isSelfAdjoint_add_clm mem.sys.isSelfAdjoint_H0 V_s.isSelfAdjoint_totalPerturbation
    have h_flow_bound : ∀ τ ∈ Set.Icc (-Real.pi) Real.pi,
        ‖Ψ (heisenbergFlow H_s τ (opCommutator V_s.totalPerturbation Q_u))‖ ≤
          J * bdlInhomogeneousBarePerturbationTailProfile r_cut f_Q ε_LR_Q := by
      intro τ hτ
      have h_sum_τ : Ψ (heisenbergFlow H_s τ (opCommutator V_s.totalPerturbation Q_u)) =
          ∑ q ∈ Finset.Icc 1 L, Ψ (heisenbergFlow H_s τ (C_q q)) := by
        rw [h_comm_sum]; unfold heisenbergFlow; rw [Finset.mul_sum, Finset.sum_mul, map_sum]
      have h_low_lr : ∀ q ∈ Finset.Icc 1 r_cut,
          ‖Ψ (heisenbergFlow H_s τ (C_q q))‖ ≤ ε_LR_Q * (J * f_Q q) := by
        intro q hq
        rcases Finset.mem_Icc.mp hq with ⟨hq1, hq_cut⟩
        have hq_L : q ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hq1, le_trans hq_cut hj_cut⟩
        have hX_ne : (boxBall u r_X).Nonempty := ⟨u, mem_boxBall_self u r_X⟩
        have hd_pos : 0 < d_Q j := by dsimp [d_Q]; omega
        have h_hk := norm_heisenbergFlow_interpolated_sub_condExp_inhomogeneous_le
          mem V hJ0 hJ1 ⟨by linarith [hs.1], hs.2⟩ hτ hf hV hX_ne d_Q j hd_pos
          (regionDist_boxBall_compl_boxBall_ge u (by omega : r_X ≤ r_bare))
          (C_q q) (h_supp_q q hq)
        have h_card : ((boxBall u r_X).card : ℝ) ≤ ((2 * r_X + 1 : ℕ) : ℝ) ^ 3 := by
          exact_mod_cast card_boxBall_le_pow u r_X
        have h_env_nn := bdlBochnerHastingsKomaEnvelope_nonneg hf d_Q j
        calc ‖Ψ (heisenbergFlow H_s τ (C_q q))‖
          _ ≤ ((boxBall u r_X).card : ℝ) * bdlBochnerHastingsKomaEnvelope f d_Q j * ‖C_q q‖ := h_hk
          _ ≤ ε_LR_Q * ‖C_q q‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h_card h_env_nn) (norm_nonneg _)
          _ ≤ ε_LR_Q * (J * f_Q q) :=
            mul_le_mul_of_nonneg_left (h_norm_q q hq_L) hε_nn
      have h_high_triv : ∀ q ∈ Finset.Icc (r_cut + 1) L,
          ‖Ψ (heisenbergFlow H_s τ (C_q q))‖ ≤ 2 * (J * f_Q q) := by
        intro q hq
        have hq_L : q ∈ Finset.Icc 1 L :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hq).1; omega, (Finset.mem_Icc.mp hq).2⟩
        have h_ce : ‖Ψ (heisenbergFlow H_s τ (C_q q))‖ ≤ 2 * ‖heisenbergFlow H_s τ (C_q q)‖ :=
          norm_sub_condExp_le_two_mul_norm (boxBall u r_bare) (heisenbergFlow H_s τ (C_q q))
        have h_hf : ‖heisenbergFlow H_s τ (C_q q)‖ ≤ ‖C_q q‖ :=
          norm_heisenbergFlow_le_self hHs_sa τ (C_q q)
        exact le_trans h_ce (mul_le_mul_of_nonneg_left
          (le_trans h_hf (h_norm_q q hq_L)) zero_le_two)
      have h_union : Finset.Icc 1 L = Finset.Icc 1 r_cut ∪ Finset.Icc (r_cut + 1) L := by
        ext q; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have h_disj : Disjoint (Finset.Icc 1 r_cut) (Finset.Icc (r_cut + 1) L) := by
        rw [Finset.disjoint_left]; intro q hq1 hq2; simp only [Finset.mem_Icc] at hq1 hq2; omega
      have h1 : ‖∑ q ∈ Finset.Icc 1 r_cut, Ψ (heisenbergFlow H_s τ (C_q q))‖ ≤
          J * (ε_LR_Q * ∑ q ∈ Finset.Icc 1 r_cut, f_Q q) := by
        calc ‖∑ q ∈ Finset.Icc 1 r_cut, Ψ (heisenbergFlow H_s τ (C_q q))‖
          _ ≤ ∑ q ∈ Finset.Icc 1 r_cut, ‖Ψ (heisenbergFlow H_s τ (C_q q))‖ := norm_sum_le _ _
          _ ≤ ∑ q ∈ Finset.Icc 1 r_cut, ε_LR_Q * (J * f_Q q) := Finset.sum_le_sum h_low_lr
          _ = J * (ε_LR_Q * ∑ q ∈ Finset.Icc 1 r_cut, f_Q q) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
      have h2 : ‖∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (heisenbergFlow H_s τ (C_q q))‖ ≤
          J * (2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f_Q q) := by
        calc ‖∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (heisenbergFlow H_s τ (C_q q))‖
          _ ≤ ∑ q ∈ Finset.Icc (r_cut + 1) L, ‖Ψ (heisenbergFlow H_s τ (C_q q))‖ := norm_sum_le _ _
          _ ≤ ∑ q ∈ Finset.Icc (r_cut + 1) L, 2 * (J * f_Q q) := Finset.sum_le_sum h_high_triv
          _ = J * (2 * ∑ q ∈ Finset.Icc (r_cut + 1) L, f_Q q) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
      have h_tri := norm_add_le
        (∑ q ∈ Finset.Icc 1 r_cut, Ψ (heisenbergFlow H_s τ (C_q q)))
        (∑ q ∈ Finset.Icc (r_cut + 1) L, Ψ (heisenbergFlow H_s τ (C_q q)))
      have h_fin : ‖Ψ (heisenbergFlow H_s τ (opCommutator V_s.totalPerturbation Q_u))‖ ≤
          J * barePerturbationTailProfile L r_cut f_Q ε_LR_Q := by
        rw [h_sum_τ, h_union, Finset.sum_union h_disj]
        dsimp [barePerturbationTailProfile]; linarith
      exact le_trans h_fin (mul_le_mul_of_nonneg_left
        (barePerturbationTailProfile_le_bdlInhomogeneousBarePerturbationTailProfile
          L r_cut hf_Q hε_nn) hJ0)
    have hM_nn : 0 ≤ J * bdlInhomogeneousBarePerturbationTailProfile r_cut f_Q ε_LR_Q := by
      refine mul_nonneg hJ0 ?_
      unfold bdlInhomogeneousBarePerturbationTailProfile
      refine add_nonneg (mul_nonneg hε_nn (tsum_nonneg hf_Q.1))
        (mul_nonneg zero_le_two (tsum_nonneg fun q => ?_))
      split_ifs <;> [exact hf_Q.1 q; exact le_rfl]
    have h_mvt := norm_bochnerFilteredOp_w_BH11_sub_self_sub_condExp_le_of_commute_left
      h_comm_Q hQ_supp_bare hM_nn h_flow_bound
    linarith

/-! ## 3. Zero-Mode Base Norm Bound for `twoBlockFilteredSiteOp` -/

/-- Explicit $L$-independent zero-mode base norm `m_0` for `twoBlockFilteredSiteOp`. -/
def bdlInhomogeneousTwoBlockBaseMoment (f : ℕ → ℝ) (c_U_Q c_offDiag : ℝ) : ℝ :=
  2 * ((∑' q : ℕ, (q : ℝ) ^ 3 * f q) +
    2 * Real.pi * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f +
    c_U_Q + c_offDiag)

lemma bdlInhomogeneousTwoBlockBaseMoment_nonneg {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {c_U_Q c_offDiag : ℝ} (hc_UQ : 0 ≤ c_U_Q) (hc_off : 0 ≤ c_offDiag) :
    0 ≤ bdlInhomogeneousTwoBlockBaseMoment f c_U_Q c_offDiag := by
  unfold bdlInhomogeneousTwoBlockBaseMoment
  have h1 : 0 ≤ ∑' q : ℕ, (q : ℝ) ^ 3 * f q :=
    tsum_nonneg fun q => mul_nonneg (by positivity) (hf.1 q)
  have h2 := bdlInhomogeneousSiteWeightBound_nonneg
  have h3 := bdlInhomogeneousCommutatorBound_nonneg hf
  have h4 := Real.pi_pos.le
  positivity

end
