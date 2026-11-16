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

import Proofs.HastingsKomaLightCone.PerturbedSpectralLowPassBridge
import Proofs.KatoHastingsFlow.DressedCheckDriftBounds
import Proofs.KatoODE.NonAutonomousLiebRobinsonSeries

/-!
# Centered-Ball Unitary Light-Cone Bounds for Non-Autonomous Quasi-Local Flows

Extracts coupling-uniform local interaction envelopes (`quasiLocalTermNormBound`) from continuous `QuasiLocalPerturbation` families and proves single-site, half-radius ball, and check-drift conditional expectation tail bounds (`kato_hastings_nonAutonomous_unitary_light_cone_of_quasiLocal_generator`) along non-autonomous Kato–Hastings flows.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equations (73)–(74) (`eq:unitary-one-site-lr`, `eq:check-duhamel-WBP`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Equation (94) (`eq:dressed-unitary-lr`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
-/

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory
open KMSPinchedGibbs PerturbedThermalBarrier WeldedHierarchy WeldedHierarchy.BDLDecoder
open InhomogeneousMemoryChallenge

noncomputable section

/-! ## 1. Uniform Term-Norm & `s1` Bounds for Time-Dependent Quasi-Local Generators -/

/-- Uniform time-independent term-norm envelope for any `QuasiLocalPerturbation` satisfying
    `SatisfiesDecayBound J f_D`. -/
def quasiLocalTermNormBound {D L : ℕ} (J : ℝ) (f_D : ℕ → ℝ) (Z : Finset (BoxD D L)) : ℝ :=
  ∑ r ∈ Finset.Icc 1 L, if Z ∈ boxCubes D L r then J * f_D r else 0

lemma quasi_local_term_norm_bound_nonneg {D L : ℕ} {J : ℝ} {f_D : ℕ → ℝ}
    (hJ0 : 0 ≤ J) (hf_D : IsSuperpolynomialDecay f_D) (Z : Finset (BoxD D L)) :
    0 ≤ quasiLocalTermNormBound J f_D Z := by
  unfold quasiLocalTermNormBound
  refine Finset.sum_nonneg (fun r _ => ?_)
  split_ifs <;> [exact mul_nonneg hJ0 (hf_D.1 r); exact le_rfl]

lemma norm_perturbation_lattice_term_one_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f_D : ℕ → ℝ}
    (hV : V.SatisfiesDecayBound J f_D) (Z : Finset (BoxD D L)) :
    ‖(perturbationLatticeHamiltonian V 1).h Z‖ ≤ quasiLocalTermNormBound J f_D Z := by
  change ‖perturbationLatticeTerm V 1 Z‖ ≤ quasiLocalTermNormBound J f_D Z
  unfold perturbationLatticeTerm quasiLocalTermNormBound
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun r hr => ?_))
  split_ifs with hZr
  · rw [Complex.ofReal_one, one_smul]; exact hV r hr Z hZr
  · rw [norm_zero]

theorem sum_quasi_local_term_norm_bound_s1_le_J_mul {D L : ℕ} [NeZero D] [NeZero L]
    {J η : ℝ} {f_D : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_D : IsSuperpolynomialDecay f_D) (hη : 0 ≤ η) (x : BoxD D L) :
    (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      quasiLocalTermNormBound J f_D Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤
      J * quasiLocalS1Factor D f_D η := by
  let w : Finset (BoxD D L) → ℝ := fun Z => (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η
  have h_term : ∀ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      quasiLocalTermNormBound J f_D Z * w Z ≤
        ∑ r ∈ Finset.Icc 1 L,
          if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
            J * f_D r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
          else 0 := by
    intro Z hZ
    have hxZ : x ∈ Z := (Finset.mem_filter.mp hZ).2
    have hx1 : x ∈ boxCube x 1 := singleton_subset_boxCube x le_rfl (Finset.mem_singleton_self x)
    have h_nd : ¬ Disjoint Z (boxCube x 1) := Finset.not_disjoint_iff.mpr ⟨x, hxZ, hx1⟩
    unfold quasiLocalTermNormBound; rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun r hr => ?_)
    by_cases hZr : Z ∈ boxCubes D L r
    · have hZ_mem : Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) :=
        Finset.mem_filter.mpr ⟨hZr, h_nd⟩
      rw [if_pos hZr, if_pos hZ_mem]
      have hZ_eq : boxCube (anchorOfCube r Z) r = Z := boxCube_anchorOfCube hZr
      have h_wZ : w Z ≤ (2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η) :=
        card_mul_one_add_regionDiam_rpow_le (Finset.mem_Icc.mp hr).1 hη
          (hZ_eq ▸ card_boxCube_le_pow (anchorOfCube r Z) r)
          (hZ_eq ▸ regionDiam_boxCube_le (anchorOfCube r Z) r)
      exact mul_le_mul_of_nonneg_left h_wZ (mul_nonneg hJ (hf_D.1 r))
    · have hZ_nmem : Z ∉ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) :=
        fun h => hZr (Finset.mem_filter.mp h).1
      rw [if_neg hZr, if_neg hZ_nmem, zero_mul]
  have h_scale : ∀ r ∈ Finset.Icc 1 L,
      (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
        if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
          J * f_D r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
        else 0) ≤
      J * (2 : ℝ) ^ (D + Nat.ceil η) * ((r : ℝ) ^ (2 * D + Nat.ceil η) * f_D r) := by
    intro r hr
    let S_r := (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1))
    let C_r := J * f_D r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
    have hCr_nn : 0 ≤ C_r := by dsimp [C_r]; have := hf_D.1 r; positivity
    have h_le_univ : (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
        if Z ∈ S_r then C_r else 0) ≤
        ∑ Z : Finset (BoxD D L), if Z ∈ S_r then C_r else 0 :=
      Finset.sum_le_univ_sum_of_nonneg fun Z => by split_ifs <;> [exact hCr_nn; exact le_rfl]
    have h_univ_eq : (∑ Z : Finset (BoxD D L), if Z ∈ S_r then C_r else 0) = (S_r.card : ℝ) * C_r := by
      rw [← Finset.sum_filter, Finset.filter_univ_mem, Finset.sum_const, nsmul_eq_mul]
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have h_card_nat : S_r.card ≤ (2 * r) ^ D :=
      le_trans (card_filter_not_disjoint_boxCube_le_pow x r 1) (Nat.pow_le_pow_left (by omega) D)
    have h_card_r : (S_r.card : ℝ) ≤ (2 : ℝ) ^ D * (r : ℝ) ^ D := by
      have h_c : (S_r.card : ℝ) ≤ ((2 * r : ℝ)) ^ D := by exact_mod_cast h_card_nat
      rwa [mul_pow] at h_c
    calc (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z), if Z ∈ S_r then C_r else 0)
      _ ≤ (S_r.card : ℝ) * C_r := h_univ_eq ▸ h_le_univ
      _ ≤ ((2 : ℝ) ^ D * (r : ℝ) ^ D) * C_r := mul_le_mul_of_nonneg_right h_card_r hCr_nn
      _ = J * (2 : ℝ) ^ (D + Nat.ceil η) * ((r : ℝ) ^ (2 * D + Nat.ceil η) * f_D r) := by
        dsimp [C_r]
        have h_pow2 : (2 : ℝ) ^ (D + Nat.ceil η) = (2 : ℝ) ^ D * (2 : ℝ) ^ (Nat.ceil η) :=
          pow_add 2 D (Nat.ceil η)
        have h_powr : (r : ℝ) ^ (2 * D + Nat.ceil η) =
            (r : ℝ) ^ D * ((r : ℝ) ^ D * (r : ℝ) ^ (Nat.ceil η)) := by
          have h_idx : 2 * D + Nat.ceil η = D + (D + Nat.ceil η) := by omega
          rw [h_idx, pow_add, pow_add]
        rw [h_pow2, h_powr]; ring
  calc (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
        quasiLocalTermNormBound J f_D Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η)
    _ = ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          quasiLocalTermNormBound J f_D Z * w Z := Finset.sum_congr rfl fun Z _ => by dsimp [w]; ring
    _ ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          ∑ r ∈ Finset.Icc 1 L,
            if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
              J * f_D r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
            else 0 := Finset.sum_le_sum h_term
    _ = ∑ r ∈ Finset.Icc 1 L,
          ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
            if Z ∈ (boxCubes D L r).filter (fun A => ¬ Disjoint A (boxCube x 1)) then
              J * f_D r * ((2 : ℝ) ^ (Nat.ceil η) * (r : ℝ) ^ (D + Nat.ceil η))
            else 0 := Finset.sum_comm
    _ ≤ ∑ r ∈ Finset.Icc 1 L,
          J * (2 : ℝ) ^ (D + Nat.ceil η) * ((r : ℝ) ^ (2 * D + Nat.ceil η) * f_D r) :=
      Finset.sum_le_sum h_scale
    _ = (J * (2 : ℝ) ^ (D + Nat.ceil η)) *
          ∑ r ∈ Finset.Icc 1 L, (r : ℝ) ^ (2 * D + Nat.ceil η) * f_D r := by rw [← Finset.mul_sum]
    _ ≤ (J * (2 : ℝ) ^ (D + Nat.ceil η)) *
          ∑' r : ℕ, (r : ℝ) ^ (2 * D + Nat.ceil η) * f_D r := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact (summable_pow_mul_of_isSuperpolynomialDecay hf_D (2 * D + Nat.ceil η)).sum_le_tsum
        (Finset.Icc 1 L) (fun r _ => mul_nonneg (by positivity) (hf_D.1 r))
    _ = J * quasiLocalS1Factor D f_D η := by unfold quasiLocalS1Factor; ring

/-! ## 2. Non-Autonomous Unitary Flow `condExp` Tail & Site-Check Drift Bounds -/

theorem norm_kato_flow_unitary_quasi_local_adj_conj_sub_cond_exp_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (D_loc : ℝ → QuasiLocalPerturbation D L Site)
    {U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    {J η s : ℝ} {f_D : ℕ → ℝ}
    (hJ0 : 0 ≤ J) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hη : 0 ≤ η)
    (hf_D : IsSuperpolynomialDecay f_D)
    (hD_dec : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (D_loc τ).SatisfiesDecayBound J f_D)
    {X B : Finset (BoxD D L)} (hX : X.Nonempty) {d : ℕ} (hd_pos : 0 < d)
    (h_dist : (Finset.univ \ B).Nonempty → d ≤ regionDist X (Finset.univ \ B))
    (O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_X : IsSupportedOn Site X O_X) :
    let U_s := katoFlowUnitary hFlow s
    let S1 := J * quasiLocalS1Factor D f_D η
    ‖U_s.1† * O_X * U_s.1 - condExp Site B (U_s.1† * O_X * U_s.1)‖ ≤
      (2 * (X.card : ℝ) * ((Real.exp (2 * S1 * 1) - 1) / (1 + (d : ℝ) / 2) ^ η)) * ‖O_X‖ :=
  norm_non_autonomous_flow_sub_cond_exp_le_hastings_koma
    hFlow (fun τ => perturbationLatticeHamiltonian (D_loc τ) 1)
    (quasi_local_term_norm_bound_nonneg hJ0 hf_D)
    hη (mul_nonneg hJ0 (quasiLocalS1Factor_nonneg D hf_D η)) zero_le_one
    (sum_quasi_local_term_norm_bound_s1_le_J_mul hJ0 hf_D hη)
    (fun τ _ => (perturbationLatticeHamiltonian_one_H_tot (D_loc τ)).symm)
    (fun τ hτ W => norm_perturbation_lattice_term_one_le (D_loc τ) (hD_dec τ hτ) W)
    hX hd_pos h_dist O_X hO_X hs

theorem norm_kato_flow_unitary_single_site_box_ball_sub_cond_exp_le_J_mul
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (D_loc : ℝ → QuasiLocalPerturbation D L Site)
    {U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    {J s : ℝ} {f_D : ℕ → ℝ}
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hf_D : IsSuperpolynomialDecay f_D)
    (hD_dec : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (D_loc τ).SatisfiesDecayBound J f_D)
    (v : BoxD D L) (r_LR : ℕ)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA_v : IsSupportedOn Site {v} A_v) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * A_v * U_s.1 - condExp Site (boxBall v r_LR) (U_s.1† * A_v * U_s.1)‖ ≤
      (J * hastingsKomaOneSiteTailProfile D f_D r_LR) * ‖A_v‖ := by
  intro U_s
  rw [show (J * hastingsKomaOneSiteTailProfile D f_D r_LR) * ‖A_v‖ =
      (J * ‖A_v‖) * hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst D f_D)
        (fun r => r + 1) r_LR by unfold hastingsKomaOneSiteTailProfile; ring]
  apply le_mul_hastingsKomaSuperpolyEnvelope_of_forall
  intro m
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set S1 := J * quasiLocalS1Factor D f_D (m : ℝ)
  have h_hk := norm_kato_flow_unitary_quasi_local_adj_conj_sub_cond_exp_le
    D_loc hFlow hJ0 hs hm_nn hf_D hD_dec (Finset.singleton_nonempty v) (Nat.succ_pos r_LR)
    (regionDist_singleton_compl_boxBall_ge v r_LR) A_v hA_v
  (try dsimp only at h_hk)
  rw [Finset.card_singleton, Nat.cast_one, mul_one, Real.rpow_natCast] at h_hk
  have h_exp : Real.exp (2 * S1 * 1) - 1 ≤
      J * ((2 * quasiLocalS1Factor D f_D (m : ℝ)) * Real.exp (2 * quasiLocalS1Factor D f_D (m : ℝ))) := by
    refine exp_sub_one_le_J_mul_of_le_J_mul hJ0 hJ1 ?_ (by dsimp [S1]; linarith)
    have := quasiLocalS1Factor_nonneg D hf_D (m : ℝ); positivity
  have h_denom_pos : (0 : ℝ) < (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m := by positivity
  have h_num : 2 * (Real.exp (2 * S1 * 1) - 1) * ‖A_v‖ ≤
      (J * ‖A_v‖) * hastingsKomaOneSiteConst D f_D m := by
    unfold hastingsKomaOneSiteConst
    linarith [mul_le_mul_of_nonneg_right h_exp (norm_nonneg A_v)]
  refine le_trans h_hk ?_
  calc 2 * ((Real.exp (2 * S1 * 1) - 1) / (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m) * ‖A_v‖
    _ = (2 * (Real.exp (2 * S1 * 1) - 1) * ‖A_v‖) / (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m := by ring
    _ ≤ ((J * ‖A_v‖) * hastingsKomaOneSiteConst D f_D m) / (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m :=
      div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
    _ = (J * ‖A_v‖) * (hastingsKomaOneSiteConst D f_D m / (1 + ((r_LR + 1 : ℕ) : ℝ) / 2) ^ m) := by ring

theorem norm_kato_flow_unitary_box_ball_half_sub_cond_exp_le_J_mul
    {L : ℕ} [NeZero L]
    {Site : Box3D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (D_loc : ℝ → QuasiLocalPerturbation 3 L Site)
    {U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    {J s : ℝ} {f_D : ℕ → ℝ}
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hf_D : IsSuperpolynomialDecay f_D)
    (hD_dec : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (D_loc τ).SatisfiesDecayBound J f_D)
    (u : Box3D L) (j : ℕ)
    (B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hB_loc : IsSupportedOn Site (boxBall u (j / 2)) B_loc) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * B_loc * U_s.1 - condExp Site (boxBall u j) (U_s.1† * B_loc * U_s.1)‖ ≤
      (J * hastingsKomaBoxBallHalfTailProfile f_D j) * ‖B_loc‖ := by
  intro U_s; haveI : NeZero 3 := ⟨by decide⟩
  rw [show (J * hastingsKomaBoxBallHalfTailProfile f_D j) * ‖B_loc‖ =
      (J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) *
        hastingsKomaSuperpolyEnvelope (hastingsKomaOneSiteConst 3 f_D)
          (fun r => r + 1 - r / 2) j by unfold hastingsKomaBoxBallHalfTailProfile; ring]
  apply le_mul_hastingsKomaSuperpolyEnvelope_of_forall
  intro m
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hX_ne : (boxBall u (j / 2)).Nonempty := ⟨u, mem_boxBall_self u (j / 2)⟩
  have hd_pos : 0 < j + 1 - j / 2 := by omega
  set S1 := J * quasiLocalS1Factor 3 f_D (m : ℝ)
  have h_hk := norm_kato_flow_unitary_quasi_local_adj_conj_sub_cond_exp_le
    D_loc hFlow hJ0 hs hm_nn hf_D hD_dec hX_ne hd_pos
    (regionDist_boxBall_compl_boxBall_ge u (Nat.div_le_self j 2)) B_loc hB_loc
  (try dsimp only at h_hk); rw [Real.rpow_natCast] at h_hk
  have h_exp : Real.exp (2 * S1 * 1) - 1 ≤
      J * ((2 * quasiLocalS1Factor 3 f_D (m : ℝ)) * Real.exp (2 * quasiLocalS1Factor 3 f_D (m : ℝ))) := by
    refine exp_sub_one_le_J_mul_of_le_J_mul hJ0 hJ1 ?_ (by dsimp [S1]; linarith)
    have := quasiLocalS1Factor_nonneg 3 hf_D (m : ℝ); positivity
  have h_card : ((boxBall u (j / 2)).card : ℝ) ≤ ((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast card_boxBall_le_pow u (j / 2)
  have h_denom_pos : (0 : ℝ) < (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m := by positivity
  have h_exp_nn : 0 ≤ Real.exp (2 * S1 * 1) - 1 := by
    have hS1_nn : 0 ≤ S1 := mul_nonneg hJ0 (quasiLocalS1Factor_nonneg 3 hf_D (m : ℝ))
    linarith [Real.one_le_exp (by positivity : 0 ≤ 2 * S1 * 1)]
  have h_num : 2 * ((boxBall u (j / 2)).card : ℝ) * (Real.exp (2 * S1 * 1) - 1) * ‖B_loc‖ ≤
      (J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) * hastingsKomaOneSiteConst 3 f_D m := by
    unfold hastingsKomaOneSiteConst
    have h1 := mul_le_mul h_card h_exp h_exp_nn (by positivity)
    linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 zero_le_two) (norm_nonneg B_loc)]
  refine le_trans h_hk ?_
  calc (2 * ((boxBall u (j / 2)).card : ℝ) *
          ((Real.exp (2 * S1 * 1) - 1) / (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m)) * ‖B_loc‖
    _ = (2 * ((boxBall u (j / 2)).card : ℝ) * (Real.exp (2 * S1 * 1) - 1) * ‖B_loc‖) /
          (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m := by ring
    _ ≤ ((J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) * hastingsKomaOneSiteConst 3 f_D m) /
          (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m :=
      div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
    _ = (J * (((2 * (j / 2) + 1 : ℕ) : ℝ) ^ 3 * ‖B_loc‖)) *
          (hastingsKomaOneSiteConst 3 f_D m / (1 + ((j + 1 - j / 2 : ℕ) : ℝ) / 2) ^ m) := by ring

theorem norm_kato_flow_unitary_site_check_op_drift_inhomogeneous_le
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {f_D : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (D_loc : ℝ → QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    {U_flow P_flow : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))}
    (hFlow : IsKatoHastingsFlowSystem mem.sys.P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    (hJ0 : 0 ≤ J) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hf_D : IsSuperpolynomialDecay f_D)
    (hD_dec : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (D_loc τ).SatisfiesDecayBound J f_D)
    (u : Box3D L) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * mem.sys.siteCheckOp u * U_s.1 - mem.sys.siteCheckOp u‖ ≤
      J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D) := by
  intro U_s
  let g_U := 2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D
  have hg_nn : 0 ≤ g_U := mul_nonneg (mul_nonneg zero_le_two bdlInhomogeneousSiteWeightBound_nonneg)
    (bdlInhomogeneousCommutatorBound_nonneg hf_D)
  have h_comm : ∀ τ ∈ Set.Icc 0 s,
      ‖mem.sys.siteCheckOp u * (D_loc τ).totalPerturbation - (D_loc τ).totalPerturbation * mem.sys.siteCheckOp u‖ ≤ J * g_U := by
    intro τ hτ
    have h1 := norm_opCommutator_V_tot_siteCheckOp_inhomogeneous_le mem (D_loc τ) hJ0
      ⟨zero_le_one, le_rfl⟩ hf_D (hD_dec τ ⟨hτ.1, le_trans hτ.2 hs.2⟩) u
    rw [scaleQuasiLocalPerturbation_one] at h1; unfold opCommutator at h1; rwa [norm_sub_rev]
  exact le_trans (norm_katoFlowUnitary_check_drift_le_J_mul hFlow hs.1 h_comm)
    (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hg_nn hs.2) hJ0)

theorem norm_kato_flow_unitary_site_check_op_box_ball_sub_cond_exp_le_J_mul
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η_mem c_mem J s : ℝ} {f_D : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η_mem c_mem)
    (D_loc : ℝ → QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    {U_flow P_flow : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))}
    (hFlow : IsKatoHastingsFlowSystem mem.sys.P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    (hJ0 : 0 ≤ J) (hJ1 : J ≤ 1) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hf_D : IsSuperpolynomialDecay f_D)
    (hD_dec : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (D_loc τ).SatisfiesDecayBound J f_D)
    (u : Box3D L) (j : ℕ) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let U_s := katoFlowUnitary hFlow s
    let ΔQ_U := U_s.1† * mem.sys.siteCheckOp u * U_s.1 - mem.sys.siteCheckOp u
    ‖ΔQ_U - condExp Site (boxBall u j) ΔQ_U‖ ≤
      J * hastingsKomaSiteCheckBoxBallTailProfile f_D j := by
  intro Site U_s ΔQ_U; haveI : NeZero 3 := ⟨by decide⟩
  let Q_u := mem.sys.siteCheckOp u
  unfold hastingsKomaSiteCheckBoxBallTailProfile
  split_ifs with hj_lt
  · linarith [norm_sub_condExp_le_two_mul_norm (boxBall u j) ΔQ_U,
      norm_kato_flow_unitary_site_check_op_drift_inhomogeneous_le mem D_loc hFlow hJ0 hs hf_D hD_dec u]
  · have hj_ge : 2 * r0BDL ≤ j := not_lt.mp hj_lt
    have hQ_ce : condExp Site (boxBall u j) Q_u = Q_u :=
      condExp_eq_self_of_isSupportedOn (isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u hj_ge)
    have h_id : ΔQ_U - condExp Site (boxBall u j) ΔQ_U =
        U_s.1† * Q_u * U_s.1 - condExp Site (boxBall u j) (U_s.1† * Q_u * U_s.1) := by
      dsimp [ΔQ_U]; rw [condExp_sub_clm, hQ_ce]; abel
    rw [h_id, show J * ((((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound) *
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
    set S1 := J * quasiLocalS1Factor 3 f_D (m : ℝ)
    have h_hk := norm_kato_flow_unitary_quasi_local_adj_conj_sub_cond_exp_le
      D_loc hFlow hJ0 hs hm_nn hf_D hD_dec hX_ne hd_pos
      (regionDist_boxBall_compl_boxBall_ge u hj_ge)
      Q_u (isSupportedOn_boxBall_siteCheckOp_inhomogeneous mem u le_rfl)
    (try dsimp only at h_hk); rw [Real.rpow_natCast] at h_hk
    have h_exp : Real.exp (2 * S1 * 1) - 1 ≤
        J * ((2 * quasiLocalS1Factor 3 f_D (m : ℝ)) * Real.exp (2 * quasiLocalS1Factor 3 f_D (m : ℝ))) := by
      refine exp_sub_one_le_J_mul_of_le_J_mul hJ0 hJ1 ?_ (by dsimp [S1]; linarith)
      have := quasiLocalS1Factor_nonneg 3 hf_D (m : ℝ); positivity
    have h_card : ((boxBall u (2 * r0BDL)).card : ℝ) ≤ ((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 := by
      have hc := card_boxBall_le_pow u (2 * r0BDL)
      have h_eq : 2 * (2 * r0BDL) + 1 = 4 * r0BDL + 1 := by ring
      rw [h_eq] at hc; exact_mod_cast hc
    have hQ_le : ‖Q_u‖ ≤ bdlInhomogeneousSiteWeightBound := norm_siteCheckOp_inhomogeneous_le mem u
    have h_denom_pos : (0 : ℝ) < (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m := by positivity
    have h_exp_nn : 0 ≤ Real.exp (2 * S1 * 1) - 1 := by
      have hS1_nn : 0 ≤ S1 := mul_nonneg hJ0 (quasiLocalS1Factor_nonneg 3 hf_D (m : ℝ))
      linarith [Real.one_le_exp (by positivity : 0 ≤ 2 * S1 * 1)]
    have h_num : 2 * ((boxBall u (2 * r0BDL)).card : ℝ) * (Real.exp (2 * S1 * 1) - 1) * ‖Q_u‖ ≤
        (J * (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound)) *
          hastingsKomaOneSiteConst 3 f_D m := by
      unfold hastingsKomaOneSiteConst
      have h1 := mul_le_mul h_card hQ_le (norm_nonneg Q_u) (by positivity)
      linarith [mul_le_mul h1 h_exp h_exp_nn (mul_nonneg (by positivity) bdlInhomogeneousSiteWeightBound_nonneg)]
    refine le_trans h_hk ?_
    calc (2 * ((boxBall u (2 * r0BDL)).card : ℝ) *
            ((Real.exp (2 * S1 * 1) - 1) / (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m)) * ‖Q_u‖
      _ = (2 * ((boxBall u (2 * r0BDL)).card : ℝ) * (Real.exp (2 * S1 * 1) - 1) * ‖Q_u‖) /
            (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m := by ring
      _ ≤ ((J * (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound)) *
            hastingsKomaOneSiteConst 3 f_D m) / (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m :=
        div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
      _ = (J * (((4 * r0BDL + 1 : ℕ) : ℝ) ^ 3 * bdlInhomogeneousSiteWeightBound)) *
            (hastingsKomaOneSiteConst 3 f_D m / (1 + ((j + 1 - 2 * r0BDL : ℕ) : ℝ) / 2) ^ m) := by ring

/-! ## 3. Master Non-Autonomous Unitary Light-Cone Package -/

/-- **Non-Autonomous Kato–Hastings Unitary Light-Cone & Site-Check Drift Package
    (`kato_hastings_nonAutonomous_unitary_light_cone_of_quasiLocal_generator`)**. -/
theorem kato_hastings_nonAutonomous_unitary_light_cone_of_quasiLocal_generator
    {L : ℕ} [NeZero L]
    {c_star C β_c c_F η c_mem J : ℝ} {f_D : ℕ → ℝ}
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL c_star C β_c c_F η c_mem)
    (D_loc : ℝ → QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    {U_flow P_flow : ℝ → (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)))}
    (hFlow : IsKatoHastingsFlowSystem mem.sys.P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    (_hD_cont : Continuous (fun τ : ℝ => (D_loc τ).totalPerturbation))
    (hJ_nn : 0 ≤ J) (hJ1 : J ≤ 1)
    (hf_D : IsSuperpolynomialDecay f_D)
    (hD_dec : ∀ τ ∈ Set.Icc (0 : ℝ) 1, (D_loc τ).SatisfiesDecayBound J f_D) :
    let Site := UniformSite3D L (CodeSlotConfig qCodeBDL)
    let U_QAC := fun s : ℝ => katoFlowUnitary hFlow s
    (∀ (v : Box3D L) (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      IsSupportedOn Site {v} A_v →
      ∀ r : ℕ,
        ‖(U_QAC 1).1† * A_v * (U_QAC 1).1 -
          condExp Site (boxBall v r) ((U_QAC 1).1† * A_v * (U_QAC 1).1)‖ ≤
          (J * hastingsKomaOneSiteTailProfile 3 f_D r) * ‖A_v‖) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ (j : ℕ) (u : Box3D L),
        (∀ B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
          IsSupportedOn Site (boxBall u (j / 2)) B_loc →
          ‖(U_QAC s).1† * B_loc * (U_QAC s).1 -
            condExp Site (boxBall u j) ((U_QAC s).1† * B_loc * (U_QAC s).1)‖ ≤
            hastingsKomaBoxBallHalfTailProfile f_D j * ‖B_loc‖) ∧
        ‖((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u) -
          condExp Site (boxBall u j)
            ((U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u)‖ ≤
          J * hastingsKomaSiteCheckBoxBallTailProfile f_D j) ∧
      (∀ u : Box3D L,
        ‖(U_QAC s).1† * mem.sys.siteCheckOp u * (U_QAC s).1 - mem.sys.siteCheckOp u‖ ≤
          J * (2 * bdlInhomogeneousSiteWeightBound * bdlInhomogeneousCommutatorBound f_D))) := by
  intro Site U_QAC; haveI : NeZero 3 := ⟨by decide⟩
  refine ⟨fun v A_v hA_v r => ?_, fun s hs => ⟨fun j u => ⟨?_, ?_⟩, fun u => ?_⟩⟩
  · exact norm_kato_flow_unitary_single_site_box_ball_sub_cond_exp_le_J_mul
      D_loc hFlow hJ_nn hJ1 ⟨zero_le_one, le_rfl⟩ hf_D hD_dec v r A_v hA_v
  · intro B_loc hB_loc
    have hε_nn : 0 ≤ hastingsKomaBoxBallHalfTailProfile f_D j :=
      isSuperpolynomialDecay_hastingsKomaBoxBallHalfTailProfile hf_D |>.1 j
    exact le_trans (norm_kato_flow_unitary_box_ball_half_sub_cond_exp_le_J_mul
      D_loc hFlow hJ_nn hJ1 hs hf_D hD_dec u j B_loc hB_loc)
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hε_nn hJ1) (norm_nonneg B_loc))
  · exact norm_kato_flow_unitary_site_check_op_box_ball_sub_cond_exp_le_J_mul
      mem D_loc hFlow hJ_nn hJ1 hs hf_D hD_dec u j
  · exact norm_kato_flow_unitary_site_check_op_drift_inhomogeneous_le
      mem D_loc hFlow hJ_nn hs hf_D hD_dec u

alias kato_hastings_non_autonomous_unitary_light_cone_of_quasi_local_generator :=
  kato_hastings_nonAutonomous_unitary_light_cone_of_quasiLocal_generator

end
