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

import Proofs.KatoHastingsFlow.InterpolatedHamiltonianBochnerTails

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Dressed Check Drift and Unitary Conjugation Conditional-Expectation Bounds

Bounds check operator drift (`norm_katoFlowUnitary_check_drift_le_J_mul`), check conditional-expectation tails (`norm_katoFlowUnitary_check_sub_condExp_le_J_mul`, `norm_qacUnitaryFlow_check_drift_and_condExp_le_J_mul`), box conjugation tails (`norm_katoFlowUnitary_box_sub_condExp_le_of_commutator`), and single-site observable spread (`norm_katoFlowUnitary_singleSite_sub_condExp_le`) along `IsKatoHastingsFlowSystem`.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equations (73)–(74) (`eq:unitary-one-site-lr`, `eq:check-duhamel-WBP`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equations (78)–(79) (`eq:Xu-norm-and-tail`, `eq:Xu-bare-three-term`)
-/

/-!
## 1. Unitary Flow Check Drift and Check `condExp` Tail Bounds
-/

/-- **Unitary Flow Check Drift Bound (`h_U`) along `IsKatoHastingsFlowSystem`
    (`norm_katoFlowUnitary_check_drift_le_J_mul`)**:
    Along any `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow`, if $\|[Q_u, D_{\mathrm{gen}}(\tau)]\| \le J \cdot g_U$
    for all $\tau \in [0, s]$ ($s \ge 0$), then $U_s := \mathrm{katoFlowUnitary}\ hFlow\ s$ satisfies:
    $$\|U_s.1^\dagger Q_u U_s.1 - Q_u\| \le J \cdot (s \cdot g_U).$$ -/
theorem norm_katoFlowUnitary_check_drift_le_J_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P0 Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow)
    {J g_U s : ℝ} (hs : 0 ≤ s)
    (h_comm : ∀ τ ∈ Set.Icc 0 s, ‖Q_u * D_gen τ - D_gen τ * Q_u‖ ≤ J * g_U) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * Q_u * U_s.1 - Q_u‖ ≤ J * (s * g_U) := by
  intro U_s
  have h_duh := (duhamel_conjugation_bound P0 D_gen U_flow P_flow hFlow Q_u).2
    s (J * g_U) hs h_comm
  have h_eq : s * (J * g_U) = J * (s * g_U) := by ring
  rwa [h_eq] at h_duh

/-- **Unitary Flow Check `condExp` Tail Bound (`h_U_Q_tail`) along `IsKatoHastingsFlowSystem`
    (`norm_katoFlowUnitary_check_sub_condExp_le_J_mul`)**:
    When `IsSupportedOn Site (boxCube u j) Q_u` and $\|[Q_u, D_{\mathrm{gen}}(\tau)]\| \le J \cdot g_U$
    on $[0, s]$ ($s \ge 0$), $U_s := \mathrm{katoFlowUnitary}\ hFlow\ s$ satisfies:
    $$\|U_s.1^\dagger Q_u U_s.1 - \mathbb{E}_{B(u, j)}(U_s.1^\dagger Q_u U_s.1)\|
      \le J \cdot (2 s g_U).$$ -/
theorem norm_katoFlowUnitary_check_sub_condExp_le_J_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow)
    (u : BoxD D L) (j : ℕ)
    (hQ_supp_j : IsSupportedOn Site (boxCube u j) Q_u)
    {J g_U s : ℝ} (hs : 0 ≤ s)
    (h_comm : ∀ τ ∈ Set.Icc 0 s, ‖Q_u * D_gen τ - D_gen τ * Q_u‖ ≤ J * g_U) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * Q_u * U_s.1 - condExp Site (boxCube u j) (U_s.1† * Q_u * U_s.1)‖ ≤
      J * (2 * s * g_U) := by
  intro U_s
  let ΔQ := U_s.1† * Q_u * U_s.1 - Q_u
  have hQ_ce : condExp Site (boxCube u j) Q_u = Q_u :=
    condExp_eq_self_of_isSupportedOn hQ_supp_j
  have h_id : U_s.1† * Q_u * U_s.1 - condExp Site (boxCube u j) (U_s.1† * Q_u * U_s.1) =
      ΔQ - condExp Site (boxCube u j) ΔQ := by
    dsimp [ΔQ]
    rw [condExp_sub_clm, hQ_ce]
    abel
  have h_drift : ‖ΔQ‖ ≤ J * (s * g_U) :=
    norm_katoFlowUnitary_check_drift_le_J_mul hFlow hs h_comm
  have h_ce : ‖ΔQ - condExp Site (boxCube u j) ΔQ‖ ≤ 2 * ‖ΔQ‖ :=
    norm_sub_condExp_le_two_mul_norm (boxCube u j) ΔQ
  rw [h_id]
  linarith

/-- **Explicit $O(J)$ Check Drift and `condExp` Tail for a Quasi-Local QAC Generator
    (`norm_qacUnitaryFlow_check_drift_and_condExp_le_J_mul`)**:
    If `D_gen τ = D_loc.totalPerturbation` for a `QuasiLocalPerturbation` satisfying `D_loc.SatisfiesDecayBound J f_D`,
    `IsSupportedOn Site (boxCube u r_0) Q_u`, `‖Q_u‖ ≤ C_Q`, and `r_0 ≤ j`, then for all $s \ge 0$:
    1. `‖U_s.1† * Q_u * U_s.1 - Q_u‖ ≤ J * (2 * s * C_Q * uniformCubeCommutatorFactor D L r_0 f_D)`,
    2. `‖U_s.1† * Q_u * U_s.1 - condExp Site (boxCube u j) (U_s.1† * Q_u * U_s.1)‖ ≤ J * (4 * s * C_Q * uniformCubeCommutatorFactor D L r_0 f_D)`. -/
theorem norm_qacUnitaryFlow_check_drift_and_condExp_le_J_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (D_loc : QuasiLocalPerturbation D L Site)
    {U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 (fun _ => D_loc.totalPerturbation) U_flow P_flow)
    {J C_Q s : ℝ} {f_D : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_D : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f_D q) (hs : 0 ≤ s)
    (hD_decay : D_loc.SatisfiesDecayBound J f_D)
    (u : BoxD D L) (r_0 j : ℕ) (hrj : r_0 ≤ j)
    (hQ_norm : ‖Q_u‖ ≤ C_Q)
    (hQ_supp_0 : IsSupportedOn Site (boxCube u r_0) Q_u) :
    let U_s := katoFlowUnitary hFlow s
    let g_U := 2 * C_Q * uniformCubeCommutatorFactor D L r_0 f_D
    ‖U_s.1† * Q_u * U_s.1 - Q_u‖ ≤ J * (s * g_U) ∧
    ‖U_s.1† * Q_u * U_s.1 - condExp Site (boxCube u j) (U_s.1† * Q_u * U_s.1)‖ ≤
      J * (2 * s * g_U) := by
  intro U_s g_U
  have h_uc_nn : 0 ≤ uniformCubeCommutatorFactor D L r_0 f_D :=
    uniformCubeCommutatorFactor_nonneg D L r_0 hf_D
  have h_comm : ∀ τ ∈ Set.Icc 0 s, ‖Q_u * D_loc.totalPerturbation - D_loc.totalPerturbation * Q_u‖ ≤ J * g_U := by
    intro _ _
    have h1 := (norm_opCommutator_localOp_katoGenerator_le_J_mul D_loc hJ hf_D hD_decay u r_0 hQ_supp_0).2
    calc ‖Q_u * D_loc.totalPerturbation - D_loc.totalPerturbation * Q_u‖
      _ ≤ (J * (2 * uniformCubeCommutatorFactor D L r_0 f_D)) * ‖Q_u‖ := h1
      _ ≤ (J * (2 * uniformCubeCommutatorFactor D L r_0 f_D)) * C_Q :=
        mul_le_mul_of_nonneg_left hQ_norm (by positivity)
      _ = J * g_U := by dsimp [g_U]; ring
  have hQ_supp_j : IsSupportedOn Site (boxCube u j) Q_u :=
    isSupportedOn_mono (boxCube_mono_local u hrj) hQ_supp_0
  exact ⟨norm_katoFlowUnitary_check_drift_le_J_mul hFlow hs h_comm,
    norm_katoFlowUnitary_check_sub_condExp_le_J_mul hFlow u j hQ_supp_j hs h_comm⟩

/-!
## 2. Unitary Flow Box-Conjugation Tail and Single-Site Observable Tail Bounds
-/

/-- **Unitary Flow Box-Conjugation `condExp` Tail Bound (`h_U_box_tail`) from Generator Commutator
    (`norm_katoFlowUnitary_box_sub_condExp_le_of_commutator`)**:
    Along `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow` ($s \ge 0$), if $r_{\mathrm{bare}} \le j$
    and $\|[B_{\mathrm{loc}}, D_{\mathrm{gen}}(\tau)]\| \le C_{\mathrm{comm}} \|B_{\mathrm{loc}}\|$
    for every $B_{\mathrm{loc}}$ supported on `boxCube u r_bare` and $\tau \in [0, s]$, then:
    $$\|U_s.1^\dagger B_{\mathrm{loc}} U_s.1 - \mathbb{E}_{B(u, j)}(U_s.1^\dagger B_{\mathrm{loc}} U_s.1)\|
      \le (2 s C_{\mathrm{comm}}) \|B_{\mathrm{loc}}\|.$$ -/
theorem norm_katoFlowUnitary_box_sub_condExp_le_of_commutator {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow)
    (u : BoxD D L) {r_bare j : ℕ} (hrj : r_bare ≤ j)
    {s C_comm : ℝ} (hs : 0 ≤ s)
    (h_comm : ∀ (B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      IsSupportedOn Site (boxCube u r_bare) B_loc →
      ∀ τ ∈ Set.Icc 0 s, ‖B_loc * D_gen τ - D_gen τ * B_loc‖ ≤ C_comm * ‖B_loc‖)
    (B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hB_supp : IsSupportedOn Site (boxCube u r_bare) B_loc) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * B_loc * U_s.1 - condExp Site (boxCube u j) (U_s.1† * B_loc * U_s.1)‖ ≤
      (2 * s * C_comm) * ‖B_loc‖ := by
  intro U_s
  let ΔB := U_s.1† * B_loc * U_s.1 - B_loc
  have hB_supp_j : IsSupportedOn Site (boxCube u j) B_loc :=
    isSupportedOn_mono (boxCube_mono_local u hrj) hB_supp
  have hB_ce : condExp Site (boxCube u j) B_loc = B_loc :=
    condExp_eq_self_of_isSupportedOn hB_supp_j
  have h_id : U_s.1† * B_loc * U_s.1 - condExp Site (boxCube u j) (U_s.1† * B_loc * U_s.1) =
      ΔB - condExp Site (boxCube u j) ΔB := by
    dsimp [ΔB]
    rw [condExp_sub_clm, hB_ce]
    abel
  have h_duh : ‖ΔB‖ ≤ s * (C_comm * ‖B_loc‖) :=
    (duhamel_conjugation_bound P0 D_gen U_flow P_flow hFlow B_loc).2
      s (C_comm * ‖B_loc‖) hs (h_comm B_loc hB_supp)
  have h_ce : ‖ΔB - condExp Site (boxCube u j) ΔB‖ ≤ 2 * ‖ΔB‖ :=
    norm_sub_condExp_le_two_mul_norm (boxCube u j) ΔB
  rw [h_id]
  linarith

/-- **Hastings–Koma Light-Cone `condExp` Bound for Unitary Adjoint Conjugation
    (`norm_unitaryOfTimeEvolutionOp_adj_conj_sub_condExp_le_hastings_koma`)**:
    For `U_s := unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s`,
    adjoint conjugation $U_s.1^\dagger O_X U_s.1$ equals $\tau_{-s}^{H_D.\mathrm{totalHamiltonian}}(O_X)$,
    so `norm_heisenbergFlow_sub_condExp_le_hastings_koma` yields the light-cone `condExp` tail bound. -/
theorem norm_unitaryOfTimeEvolutionOp_adj_conj_sub_condExp_le_hastings_koma
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H_D : LatticeHamiltonian D L Site) {η T s : ℝ}
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hs : s ∈ Set.Icc (-T) T)
    {X B : Finset (BoxD D L)} (hX : X.Nonempty)
    {d : ℕ} (hd_pos : 0 < d)
    (h_dist : (Finset.univ \ B).Nonempty → d ≤ regionDist X (Finset.univ \ B))
    (O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_X : IsSupportedOn Site X O_X) :
    let U_s := unitaryOfTimeEvolutionOp H_D.totalHamiltonian H_D.isSelfAdjoint_totalHamiltonian s
    ‖U_s.1† * O_X * U_s.1 - condExp Site B (U_s.1† * O_X * U_s.1)‖ ≤
      ((2 * (X.card : ℝ) * ((Real.exp (2 * H_D.s1 η * T) - 1) / (1 + (d : ℝ) / 2) ^ η)) * ‖O_X‖) := by
  intro U_s
  have h_conj : U_s.1† * O_X * U_s.1 = heisenbergFlow H_D.totalHamiltonian (-s) O_X := by
    change star (timeEvolutionOp H_D.totalHamiltonian s) * O_X * timeEvolutionOp H_D.totalHamiltonian s =
      timeEvolutionOp H_D.totalHamiltonian (-s) * O_X * timeEvolutionOp H_D.totalHamiltonian (-(-s))
    rw [star_timeEvolutionOp H_D.isSelfAdjoint_totalHamiltonian s, neg_neg]
  have hns : -s ∈ Set.Icc (-T) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 := norm_heisenbergFlow_sub_condExp_le_hastings_koma H_D hη hT hX hd_pos h_dist O_X hO_X hns
  rw [h_conj]
  calc ‖heisenbergFlow H_D.totalHamiltonian (-s) O_X - condExp Site B (heisenbergFlow H_D.totalHamiltonian (-s) O_X)‖
    _ ≤ 2 * ‖O_X‖ * (X.card : ℝ) *
          ((Real.exp (2 * H_D.s1 η * T) - 1) / (1 + (d : ℝ) / 2) ^ η) := h1
    _ = (2 * (X.card : ℝ) *
          ((Real.exp (2 * H_D.s1 η * T) - 1) / (1 + (d : ℝ) / 2) ^ η)) * ‖O_X‖ := by ring

/-- **1-Site Observable Unitary Conjugation `condExp` Tail Bound (`h_1site_condExp`, `h_1site_tail`)
    (`norm_katoFlowUnitary_singleSite_sub_condExp_le`)**:
    Along `IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow` ($s \ge 0$), if $1 \le r_{\mathrm{LR}}$ and
    every operator supported on `boxCube v 1` satisfies $\|[A_v, D_{\mathrm{gen}}(\tau)]\| \le C_1 \|A_v\|$
    for $\tau \in [0, s]$, then every 1-site observable $A_v$ supported on $\{v\}$ satisfies:
    $$\|U_s.1^\dagger A_v U_s.1 - \mathbb{E}_{B(v, r_{\mathrm{LR}})}(U_s.1^\dagger A_v U_s.1)\|
      \le (2 s C_1) \|A_v\|.$$ -/
theorem norm_katoFlowUnitary_singleSite_sub_condExp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U_flow P_flow)
    (v : BoxD D L) {r_LR : ℕ} (hr_LR : 1 ≤ r_LR)
    {s C_1 : ℝ} (hs : 0 ≤ s)
    (h_comm : ∀ (B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      IsSupportedOn Site (boxCube v 1) B_loc →
      ∀ τ ∈ Set.Icc 0 s, ‖B_loc * D_gen τ - D_gen τ * B_loc‖ ≤ C_1 * ‖B_loc‖)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA_v : IsSupportedOn Site {v} A_v) :
    let U_s := katoFlowUnitary hFlow s
    ‖U_s.1† * A_v * U_s.1 - condExp Site (boxCube v r_LR) (U_s.1† * A_v * U_s.1)‖ ≤
      (2 * s * C_1) * ‖A_v‖ := by
  have hA_cube1 : IsSupportedOn Site (boxCube v 1) A_v :=
    isSupportedOn_mono (singleton_subset_boxCube v le_rfl) hA_v
  exact norm_katoFlowUnitary_box_sub_condExp_le_of_commutator hFlow v hr_LR hs h_comm A_v hA_cube1

end
