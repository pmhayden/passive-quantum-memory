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

import Proofs.KatoHastingsFlow.DressedCheckDriftBounds

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Full-Scale Tail Profiles and Observable Pullbacks Along QAC Flows

Establishes open-box ball-cube inclusions, radius-cover commutator bounds for `anchoredSiteCheckOp`, and membership of `fullScaleTailProfile` in `IsSuperpolynomialDecay`. Proves single-site observable pullback decay and logical sector symmetry preservation along `qacUnitaryFlow`.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equations (73)–(74) (`eq:unitary-one-site-lr`, `eq:check-duhamel-WBP`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (78) (`eq:Xu-norm-and-tail`)
-/

/-!
## 1. Ball-Cube Inclusions & Radius-Cover Check Commutator / Drift Bounds (No `boxCubes D L 2`)
-/

private lemma isStarProjection_norm_le_one_qacFlow {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 := by
  by_cases h0 : ‖P‖ = 0
  · linarith
  · have h_pos : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg P) (Ne.symm h0)
    have h_sq : ‖P‖ * ‖P‖ ≤ 1 * ‖P‖ := by
      rw [one_mul, ← CStarRing.norm_star_mul_self, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
    exact le_of_mul_le_mul_right h_sq h_pos

/-- Every $\ell_\infty$-ball `boxBall v r` on `BoxD D L` is contained in the open-box cube of side
    length `2 * r + 1` anchored at `fun i => ⟨(v i).val - r, ...⟩`. -/
theorem boxBall_subset_boxCube {D L : ℕ} (v : BoxD D L) (r : ℕ) :
    boxBall v r ⊆
      boxCube (fun i => ⟨(v i).val - r, Nat.sub_lt_of_lt (v i).isLt⟩) (2 * r + 1) := by
  intro y hy
  simp only [boxBall, boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  intro i
  have hi : coordDist (v i) (y i) ≤ boxDist v y :=
    Finset.le_sup (f := fun j => coordDist (v j) (y j)) (Finset.mem_univ i)
  have hi_le : coordDist (v i) (y i) ≤ r := le_trans hi hy
  dsimp [coordDist] at hi_le
  omega

/-- Every open-box cube `boxCube x0 r` is contained in `boxBall x0 r`. -/
theorem boxCube_subset_boxBall {D L : ℕ} (x0 : BoxD D L) (r : ℕ) :
    boxCube x0 r ⊆ boxBall x0 r := by
  intro y hy
  simp only [boxCube, boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  dsimp [boxDist]
  refine Finset.sup_le fun i _ => ?_
  have hi := hy i
  dsimp [coordDist]
  omega

/-- Site-anchored check operator $\sum_{i : \mathrm{anchor}(\mathrm{supp}(Q_i)) = u} w_i Q_i$
    (definitionally `rfl`-equal to `sys.siteCheckOp u` when `anchor_reg = anchorOfRegion`). -/
def anchoredSiteCheckOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ i ∈ Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = u),
    (sys.weight i : ℂ) • sys.checkProj i

/-- Partition-of-unity sum identity $\sum_{u \in \mathrm{BoxD}\ D\ L} Q_{\mathrm{site}}(u) = H_0$. -/
theorem sum_anchoredSiteCheckOp_eq_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    (∑ u : BoxD D L, anchoredSiteCheckOp anchor_reg sys u) = sys.H0 := by
  dsimp [anchoredSiteCheckOp, IndexedCommutingProjectorHamiltonian.H0]
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

/-- `anchoredSiteCheckOp anchor_reg sys u` is self-adjoint and commutes with `sys.H0`. -/
theorem isSelfAdjoint_and_commute_H0_anchoredSiteCheckOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    IsSelfAdjoint (anchoredSiteCheckOp anchor_reg sys u) ∧
    Commute sys.H0 (anchoredSiteCheckOp anchor_reg sys u) := by
  dsimp [anchoredSiteCheckOp]
  refine ⟨?_, ?_⟩
  · exact isSelfAdjoint_finset_sum _ _ (fun i _ =>
      isSelfAdjoint_real_smul (sys.weight i) (sys.is_projector i).isSelfAdjoint)
  · dsimp [IndexedCommutingProjectorHamiltonian.H0]
    refine Commute.sum_right _ _ _ fun i _ => ?_
    refine Commute.sum_left _ _ _ fun j _ => ?_
    exact ((sys.pairwise_commute j i).smul_left _).smul_right _

/-- Under `sys.support i ⊆ boxCube x0 r_0` and `V.SatisfiesDecayBound J f`, check projector
    `sys.checkProj i` satisfies `‖opCommutator V.totalPerturbation (sys.checkProj i)‖ ≤ 2 * J * uniformCubeCommutatorFactor D L r_0 f`. -/
theorem norm_opCommutator_V_tot_checkProj_le_of_radius_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f)
    {i : ι} {x0 : BoxD D L} {r_0 : ℕ}
    (h_supp_i : sys.support i ⊆ boxCube x0 r_0) :
    ‖opCommutator V.totalPerturbation (sys.checkProj i)‖ ≤
      2 * J * uniformCubeCommutatorFactor D L r_0 f := by
  have h_supp : IsSupportedOn Site (boxCube x0 r_0) (sys.checkProj i) :=
    isSupportedOn_mono h_supp_i (sys.is_supported i)
  have h1 := norm_opCommutator_V_tot_boxCube_le_uniform V hV_dec x0 r_0 h_supp
  have hQ_le : ‖sys.checkProj i‖ ≤ 1 :=
    isStarProjection_norm_le_one_qacFlow (sys.is_projector i)
  have h_fac_nn : 0 ≤ uniformCubeCommutatorFactor D L r_0 f :=
    uniformCubeCommutatorFactor_nonneg D L r_0 (fun q _ => hf_nn q)
  calc ‖opCommutator V.totalPerturbation (sys.checkProj i)‖
    _ ≤ 2 * ‖sys.checkProj i‖ * J * uniformCubeCommutatorFactor D L r_0 f := h1
    _ = ‖sys.checkProj i‖ * (2 * J * uniformCubeCommutatorFactor D L r_0 f) := by ring
    _ ≤ 1 * (2 * J * uniformCubeCommutatorFactor D L r_0 f) :=
      mul_le_mul_of_nonneg_right hQ_le (by positivity)
    _ = 2 * J * uniformCubeCommutatorFactor D L r_0 f := one_mul _

/-- Ball-cover variant of `norm_opCommutator_V_tot_checkProj_le_of_radius_cover`: if
    `sys.support i ⊆ boxBall v0 r_0`, then `sys.support i ⊆ boxCube x0 (2 * r_0 + 1)`. -/
theorem norm_opCommutator_V_tot_checkProj_le_of_ball_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f)
    {i : ι} {v0 : BoxD D L} {r_0 : ℕ}
    (h_ball_i : sys.support i ⊆ boxBall v0 r_0) :
    ‖opCommutator V.totalPerturbation (sys.checkProj i)‖ ≤
      2 * J * uniformCubeCommutatorFactor D L (2 * r_0 + 1) f :=
  norm_opCommutator_V_tot_checkProj_le_of_radius_cover sys V hJ_nn hf_nn hV_dec
    (Finset.Subset.trans h_ball_i (boxBall_subset_boxCube v0 r_0))

/-- **Radius-Cover Site-Check Commutator Bound (`norm_opCommutator_V_tot_siteCheckOp_le_of_radius_cover`)**:
    Replaces `h_cube_cov : ∀ i, ∃ A ∈ BoxCubes D L 2, sys.support i ⊆ A` with the arbitrary-radius
    cube cover `∀ i : ι, ∃ x0 : BoxD D L, sys.support i ⊆ boxCube x0 r_0`. -/
theorem norm_opCommutator_V_tot_siteCheckOp_le_of_radius_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {r_0 : ℕ} (h_rad_cov : ∀ i : ι, ∃ x0 : BoxD D L, sys.support i ⊆ boxCube x0 r_0)
    (V : QuasiLocalPerturbation D L Site) {J W_site : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f) (u : BoxD D L)
    (hW_le : (∑ i ∈ Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = u),
      sys.weight i) ≤ W_site) :
    ‖opCommutator V.totalPerturbation (anchoredSiteCheckOp anchor_reg sys u)‖ ≤
      J * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) := by
  let S_u := Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = u)
  have h_lin : opCommutator V.totalPerturbation (anchoredSiteCheckOp anchor_reg sys u) =
      ∑ i ∈ S_u, (sys.weight i : ℂ) • opCommutator V.totalPerturbation (sys.checkProj i) := by
    dsimp [anchoredSiteCheckOp, S_u, opCommutator]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ext ψ σ; simp; ring
  have h_fac_nn : 0 ≤ 2 * J * uniformCubeCommutatorFactor D L r_0 f := by
    have := uniformCubeCommutatorFactor_nonneg D L r_0 (fun q _ => hf_nn q)
    positivity
  rw [h_lin]
  calc ‖∑ i ∈ S_u, (sys.weight i : ℂ) • opCommutator V.totalPerturbation (sys.checkProj i)‖
    _ ≤ ∑ i ∈ S_u, ‖(sys.weight i : ℂ) • opCommutator V.totalPerturbation (sys.checkProj i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S_u, sys.weight i * (2 * J * uniformCubeCommutatorFactor D L r_0 f) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rcases h_rad_cov i with ⟨x0, hx0⟩
      have hw_nn : 0 ≤ sys.weight i := le_trans zero_le_one (sys.weight_ge_one i)
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw_nn]
      exact mul_le_mul_of_nonneg_left
        (norm_opCommutator_V_tot_checkProj_le_of_radius_cover sys V hJ_nn hf_nn hV_dec hx0) hw_nn
    _ = (∑ i ∈ S_u, sys.weight i) * (2 * J * uniformCubeCommutatorFactor D L r_0 f) := by
      rw [← Finset.sum_mul]
    _ ≤ W_site * (2 * J * uniformCubeCommutatorFactor D L r_0 f) :=
      mul_le_mul_of_nonneg_right hW_le h_fac_nn
    _ = J * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) := by ring

/-- **Ball-Cover Site-Check Commutator Bound (`norm_opCommutator_V_tot_siteCheckOp_le_of_ball_cover`)**:
    Under `h_ball_cov : ∀ i : ι, ∃ v0 : BoxD D L, sys.support i ⊆ boxBall v0 r_0` (which is the first
    conjunct of `sys.IsGeometricallyLocal r_0 w_0`), bounds `‖opCommutator V.totalPerturbation (anchoredSiteCheckOp anchor_reg sys u)‖`
    with cube scale `2 * r_0 + 1` and zero `BoxCubes D L 2` assumption. -/
theorem norm_opCommutator_V_tot_siteCheckOp_le_of_ball_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {r_0 : ℕ} (h_ball_cov : ∀ i : ι, ∃ v0 : BoxD D L, sys.support i ⊆ boxBall v0 r_0)
    (V : QuasiLocalPerturbation D L Site) {J W_site : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f) (u : BoxD D L)
    (hW_le : (∑ i ∈ Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = u),
      sys.weight i) ≤ W_site) :
    ‖opCommutator V.totalPerturbation (anchoredSiteCheckOp anchor_reg sys u)‖ ≤
      J * (2 * W_site * uniformCubeCommutatorFactor D L (2 * r_0 + 1) f) := by
  refine norm_opCommutator_V_tot_siteCheckOp_le_of_radius_cover anchor_reg sys
    (fun i => ?_) V hJ_nn hf_nn hV_dec u hW_le
  rcases h_ball_cov i with ⟨v0, hv0⟩
  exact ⟨fun d => ⟨(v0 d).val - r_0, Nat.sub_lt_of_lt (v0 d).isLt⟩,
    Finset.Subset.trans hv0 (boxBall_subset_boxCube v0 r_0)⟩

/-- **Duhamel Check-Operator Drift Bound Under Radius Cover (`norm_qacUnitaryFlow_siteCheckOp_drift_le_of_radius_cover`)**:
    Along any `IsKatoHastingsFlowSystem sys.P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow`, if
    `∀ i : ι, ∃ x0 : BoxD D L, sys.support i ⊆ boxCube x0 r_0`, then for all `s ∈ Set.Icc 0 1`:
    `‖(U_flow s)† * Q_u * U_flow s - Q_u‖ ≤ J * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f_D)`. -/
theorem norm_qacUnitaryFlow_siteCheckOp_drift_le_of_radius_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {r_0 : ℕ} (h_rad_cov : ∀ i : ι, ∃ x0 : BoxD D L, sys.support i ⊆ boxCube x0 r_0)
    (D_loc : ℝ → QuasiLocalPerturbation D L Site)
    (U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hFlow : IsKatoHastingsFlowSystem sys.P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    {s J W_site : ℝ} {f_D : ℕ → ℝ} (hs : s ∈ Set.Icc 0 1)
    (hJ_nn : 0 ≤ J) (hf_D_nn : ∀ r : ℕ, 0 ≤ f_D r)
    (hD_dec : ∀ τ ∈ Set.Icc 0 s, (D_loc τ).SatisfiesDecayBound J f_D)
    (u : BoxD D L)
    (hW_le : (∑ i ∈ Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = u),
      sys.weight i) ≤ W_site) :
    let Q_u := anchoredSiteCheckOp anchor_reg sys u
    ‖(U_flow s)† * Q_u * U_flow s - Q_u‖ ≤
      s * (J * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f_D)) ∧
    ‖(U_flow s)† * Q_u * U_flow s - Q_u‖ ≤
      J * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f_D) := by
  intro Q_u
  let S_U := 2 * W_site * uniformCubeCommutatorFactor D L r_0 f_D
  have hW_nn : 0 ≤ W_site := le_trans
    (Finset.sum_nonneg (fun i _ => le_trans zero_le_one (sys.weight_ge_one i))) hW_le
  have h_uc_nn : 0 ≤ uniformCubeCommutatorFactor D L r_0 f_D :=
    uniformCubeCommutatorFactor_nonneg D L r_0 (fun q _ => hf_D_nn q)
  have hSU_nn : 0 ≤ J * S_U := by dsimp [S_U]; positivity
  have h_comm : ∀ τ ∈ Set.Icc 0 s,
      ‖Q_u * (D_loc τ).totalPerturbation - (D_loc τ).totalPerturbation * Q_u‖ ≤ J * S_U := by
    intro τ hτ
    rw [norm_sub_rev (Q_u * (D_loc τ).totalPerturbation) ((D_loc τ).totalPerturbation * Q_u)]
    exact norm_opCommutator_V_tot_siteCheckOp_le_of_radius_cover
      anchor_reg sys h_rad_cov (D_loc τ) hJ_nn hf_D_nn (hD_dec τ hτ) u hW_le
  have h_duh := (duhamel_conjugation_bound sys.P0 (fun τ => (D_loc τ).totalPerturbation)
    U_flow P_flow hFlow Q_u).2 s (J * S_U) hs.1 h_comm
  have h_le1 : s * (J * S_U) ≤ J * S_U := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 hSU_nn
  exact ⟨h_duh, le_trans h_duh h_le1⟩

/-- Ball-cover variant of `norm_qacUnitaryFlow_siteCheckOp_drift_le_of_radius_cover`. -/
theorem norm_qacUnitaryFlow_siteCheckOp_drift_le_of_ball_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {r_0 : ℕ} (h_ball_cov : ∀ i : ι, ∃ v0 : BoxD D L, sys.support i ⊆ boxBall v0 r_0)
    (D_loc : ℝ → QuasiLocalPerturbation D L Site)
    (U_flow P_flow : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hFlow : IsKatoHastingsFlowSystem sys.P0 (fun τ => (D_loc τ).totalPerturbation) U_flow P_flow)
    {s J W_site : ℝ} {f_D : ℕ → ℝ} (hs : s ∈ Set.Icc 0 1)
    (hJ_nn : 0 ≤ J) (hf_D_nn : ∀ r : ℕ, 0 ≤ f_D r)
    (hD_dec : ∀ τ ∈ Set.Icc 0 s, (D_loc τ).SatisfiesDecayBound J f_D)
    (u : BoxD D L)
    (hW_le : (∑ i ∈ Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = u),
      sys.weight i) ≤ W_site) :
    let Q_u := anchoredSiteCheckOp anchor_reg sys u
    ‖(U_flow s)† * Q_u * U_flow s - Q_u‖ ≤
      s * (J * (2 * W_site * uniformCubeCommutatorFactor D L (2 * r_0 + 1) f_D)) ∧
    ‖(U_flow s)† * Q_u * U_flow s - Q_u‖ ≤
      J * (2 * W_site * uniformCubeCommutatorFactor D L (2 * r_0 + 1) f_D) := by
  refine norm_qacUnitaryFlow_siteCheckOp_drift_le_of_radius_cover anchor_reg sys
    (fun i => ?_) D_loc U_flow P_flow hFlow hs hJ_nn hf_D_nn hD_dec u hW_le
  rcases h_ball_cov i with ⟨v0, hv0⟩
  exact ⟨fun d => ⟨(v0 d).val - r_0, Nat.sub_lt_of_lt (v0 d).isLt⟩,
    Finset.Subset.trans hv0 (boxBall_subset_boxCube v0 r_0)⟩

/-!
## 2. Full-Scale (`1 ≤ m ≤ K`) Two-Block Filtered Site Operator `condExp` Decay & Base Norm
-/

/-- Full-scale tail envelope extending a high-scale (`r_0 ≤ j`) tail profile `g_high` down to
    `1 ≤ j < r_0` using the zero-mode base norm `m_0`:
    `fullScaleTailProfile r_0 m_0 g_high j := if j < r_0 then m_0 else g_high j`. -/
def fullScaleTailProfile (r_0 : ℕ) (m_0 : ℝ) (g_high : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < r_0 then m_0 else g_high j

/-- `fullScaleTailProfile r_0 m_0 g_high` preserves `IsSuperpolynomialDecay` since it agrees with
    `g_high` for all `j ≥ r_0`. -/
theorem isSuperpolynomialDecay_fullScaleTailProfile (r_0 : ℕ) {m_0 : ℝ} {g_high : ℕ → ℝ}
    (hm0_nn : 0 ≤ m_0) (hg_high : IsSuperpolynomialDecay g_high) :
    IsSuperpolynomialDecay (fullScaleTailProfile r_0 m_0 g_high) := by
  refine ⟨fun j => ?_, fun N => ?_⟩
  · dsimp [fullScaleTailProfile]
    split_ifs
    · exact hm0_nn
    · exact hg_high.1 j
  · refine (hg_high.2 N).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop r_0] with j hj
    dsimp [fullScaleTailProfile]
    rw [if_neg (not_lt.mpr hj)]

/-- **Radius-Cover Base Norm Bound for `twoBlockBochnerFilteredSiteOp` (`norm_twoBlockBochnerFilteredSiteOp_le_of_radius_cover`)**:
    Without `BoxCubes D L 2`, proves `‖X_u‖ ≤ J * m_0 / 2` under `∀ i : ι, ∃ x0, sys.support i ⊆ boxCube x0 r_0`. -/
theorem norm_twoBlockBochnerFilteredSiteOp_le_of_radius_cover {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor : ℕ → Finset (BoxD D L) → BoxD D L)
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {r_0 : ℕ} (h_rad_cov : ∀ i : ι, ∃ x0 : BoxD D L, sys.support i ⊆ boxCube x0 r_0)
    (V : QuasiLocalPerturbation D L Site)
    (h_anchor : ∀ q ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A)
    (U_s : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (u : BoxD D L) {J W_site S_U m_0 : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f)
    (hW_le : (∑ i ∈ Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = u),
      sys.weight i) ≤ W_site)
    (h_U : ‖U_s.1† * anchoredSiteCheckOp anchor_reg sys u * U_s.1 -
      anchoredSiteCheckOp anchor_reg sys u‖ ≤ J * S_U)
    (hm0_ge : 4 * ((∑ q ∈ Finset.Icc 1 L, f q) +
      Real.pi * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) + S_U) ≤ m_0) :
    let H' := U_s.1† * (sys.H0 + V.totalPerturbation) * U_s.1
    let X_u := twoBlockBochnerFilteredSiteOp sys.P0 H' U_s.1 bhFilterWeight
      (anchoredSitePerturbationOp anchor V u) (anchoredSiteCheckOp anchor_reg sys u)
    ‖X_u‖ ≤ J * (2 * ((∑ q ∈ Finset.Icc 1 L, f q) +
      Real.pi * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) + S_U)) ∧
    ‖X_u‖ ≤ J * m_0 / 2 := by
  intro H' X_u
  have hH_sa : IsSelfAdjoint (sys.H0 + V.totalPerturbation) :=
    isSelfAdjoint_add_clm sys.isSelfAdjoint_H0 V.isSelfAdjoint_totalPerturbation
  have h_comm_Q : Commute sys.H0 (anchoredSiteCheckOp anchor_reg sys u) :=
    (isSelfAdjoint_and_commute_H0_anchoredSiteCheckOp anchor_reg sys u).2
  have h_bare := norm_twoBlockBochnerFilteredSiteOp_w_BH11_le_of_bare_commute
    (V_u := anchoredSitePerturbationOp anchor V u)
    sys.isStarProjection_P0 hH_sa h_comm_Q U_s
  have h_V_u : ‖anchoredSitePerturbationOp anchor V u‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f q :=
    norm_anchoredSitePerturbationOp_le V hV_dec u h_anchor
  have h_Q_u : ‖opCommutator V.totalPerturbation (anchoredSiteCheckOp anchor_reg sys u)‖ ≤
      J * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) :=
    norm_opCommutator_V_tot_siteCheckOp_le_of_radius_cover
      anchor_reg sys h_rad_cov V hJ_nn hf_nn hV_dec u hW_le
  have h_pi_nn : 0 ≤ Real.pi := Real.pi_pos.le
  have h_pi_Q : Real.pi * ‖opCommutator V.totalPerturbation (anchoredSiteCheckOp anchor_reg sys u)‖ ≤
      Real.pi * (J * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f)) :=
    mul_le_mul_of_nonneg_left h_Q_u h_pi_nn
  have h1 : ‖X_u‖ ≤ J * (2 * ((∑ q ∈ Finset.Icc 1 L, f q) +
      Real.pi * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) + S_U)) := by
    dsimp [X_u, H'] at h_bare ⊢
    linarith
  have h_half : 2 * ((∑ q ∈ Finset.Icc 1 L, f q) +
      Real.pi * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) + S_U) ≤ m_0 / 2 := by
    linarith
  have h2 : ‖X_u‖ ≤ J * m_0 / 2 := by
    calc ‖X_u‖
      _ ≤ J * (2 * ((∑ q ∈ Finset.Icc 1 L, f q) +
            Real.pi * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) + S_U)) := h1
      _ ≤ J * (m_0 / 2) := mul_le_mul_of_nonneg_left h_half hJ_nn
      _ = J * m_0 / 2 := by ring
  exact ⟨h1, h2⟩

/-- **Full-Scale (`1 ≤ m ≤ K`) Two-Block Filtered Site Operator `condExp` Decay & Base Norm Along QAC Flow
    (`twoBlockFilteredSiteOp_condExp_decay_of_qacUnitaryFlow`)**:
    Combines the zero-mode norm bound `‖X_u‖ ≤ J * m_0 / 2` (for `1 ≤ m < r_0` via
    `norm_sub_condExp_le_two_mul_norm`) with the high-scale (`r_0 ≤ m ≤ K`) tail bound `h_high_tail`
    (Part I, Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (78) (`eq:Xu-norm-and-tail`))
    to yield `∀ m ∈ Finset.Icc 1 K, ‖X_u - condExp (boxCube v m) X_u‖ ≤ J * fullScaleTailProfile r_0 m_0 g_high m`. -/
theorem twoBlockFilteredSiteOp_condExp_decay_of_qacUnitaryFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor : ℕ → Finset (BoxD D L) → BoxD D L)
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {r_0 K : ℕ} (h_rad_cov : ∀ i : ι, ∃ x0 : BoxD D L, sys.support i ⊆ boxCube x0 r_0)
    (V : QuasiLocalPerturbation D L Site)
    (h_anchor : ∀ q ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L q, boxCube (anchor q A) q = A)
    (U_s : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {J W_site S_U m_0 : ℝ} {f g_high : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f)
    (hW_le : ∀ v : BoxD D L,
      (∑ i ∈ Finset.univ.filter (fun i : ι => anchor_reg (sys.support i) = v),
        sys.weight i) ≤ W_site)
    (h_U : ∀ v : BoxD D L,
      ‖U_s.1† * anchoredSiteCheckOp anchor_reg sys v * U_s.1 -
        anchoredSiteCheckOp anchor_reg sys v‖ ≤ J * S_U)
    (hm0_ge : 4 * ((∑ q ∈ Finset.Icc 1 L, f q) +
      Real.pi * (2 * W_site * uniformCubeCommutatorFactor D L r_0 f) + S_U) ≤ m_0)
    (h_high_tail : ∀ v : BoxD D L, ∀ m ∈ Finset.Icc r_0 K,
      let H' := U_s.1† * (sys.H0 + V.totalPerturbation) * U_s.1
      let X_v := twoBlockBochnerFilteredSiteOp sys.P0 H' U_s.1 bhFilterWeight
        (anchoredSitePerturbationOp anchor V v) (anchoredSiteCheckOp anchor_reg sys v)
      ‖X_v - condExp Site (boxCube v m) X_v‖ ≤ J * g_high m)
    (v : BoxD D L) :
    let H' := U_s.1† * (sys.H0 + V.totalPerturbation) * U_s.1
    let X_v := twoBlockBochnerFilteredSiteOp sys.P0 H' U_s.1 bhFilterWeight
      (anchoredSitePerturbationOp anchor V v) (anchoredSiteCheckOp anchor_reg sys v)
    IsSelfAdjoint X_v ∧
    Commute X_v sys.P0 ∧
    ‖X_v‖ ≤ J * m_0 / 2 ∧
    (∀ m ∈ Finset.Icc 1 K,
      ‖X_v - condExp Site (boxCube v m) X_v‖ ≤
        J * fullScaleTailProfile r_0 m_0 g_high m) := by
  intro H' X_v
  have hH_sa : IsSelfAdjoint (sys.H0 + V.totalPerturbation) :=
    isSelfAdjoint_add_clm sys.isSelfAdjoint_H0 V.isSelfAdjoint_totalPerturbation
  have hH'_sa : IsSelfAdjoint H' := by
    change star (star U_s.1 * (sys.H0 + V.totalPerturbation) * U_s.1) =
      star U_s.1 * (sys.H0 + V.totalPerturbation) * U_s.1
    rw [star_mul, star_mul, star_star, hH_sa.star_eq, mul_assoc]
  have hQ_sa : IsSelfAdjoint (anchoredSiteCheckOp anchor_reg sys v) :=
    (isSelfAdjoint_and_commute_H0_anchoredSiteCheckOp anchor_reg sys v).1
  have hV_sa : IsSelfAdjoint (anchoredSitePerturbationOp anchor V v) :=
    isSelfAdjoint_anchoredSitePerturbationOp anchor V v
  have hX_sa : IsSelfAdjoint X_v :=
    isSelfAdjoint_twoBlockBochnerFilteredSiteOp_w_BH11
      sys.isStarProjection_P0.isSelfAdjoint hH'_sa hV_sa hQ_sa
  have hX_comm : Commute X_v sys.P0 :=
    commute_twoBlockBochnerFilteredSiteOp sys.isStarProjection_P0.isIdempotentElem.eq
      H' U_s.1 bhFilterWeight _ _
  have hX_norm : ‖X_v‖ ≤ J * m_0 / 2 :=
    (norm_twoBlockBochnerFilteredSiteOp_le_of_radius_cover
      anchor anchor_reg sys h_rad_cov V h_anchor U_s v hJ_nn hf_nn hV_dec
      (hW_le v) (h_U v) hm0_ge).2
  refine ⟨hX_sa, hX_comm, hX_norm, fun m hm => ?_⟩
  dsimp [fullScaleTailProfile]
  split_ifs with h_lt
  · have h_ce : ‖X_v - condExp Site (boxCube v m) X_v‖ ≤ 2 * ‖X_v‖ :=
      norm_sub_condExp_le_two_mul_norm (boxCube v m) X_v
    linarith
  · have hm_Icc : m ∈ Finset.Icc r_0 K :=
      Finset.mem_Icc.mpr ⟨not_lt.mp h_lt, (Finset.mem_Icc.mp hm).2⟩
    exact h_high_tail v m hm_Icc

/-!
## 3. Concrete 1-Site Observable Pull-Back `condExp` Bound Along `qacUnitaryFlow`
-/

/-- **Concrete 1-Site Observable Pull-Back `condExp` Bound Along `qacUnitaryFlow`
    (`dressedSiteObs_condExp_decay_of_qacUnitaryFlow`)**:
    For `U_QAC := qacUnitaryFlow sys V` and any 1-site observable `A_v` (`IsSupportedOn Site {v} A_v`),
    bounds both the `boxCube v r_LR` (`1 ≤ r_LR`) and `boxBall v r_LR` (`∀ r_LR`) conditional
    expectation tails by `(J * (4 * s * uniformCubeCommutatorFactor D L 1 (fun r => 2 * f r))) * ‖A_v‖`. -/
theorem dressedSiteObs_condExp_decay_of_qacUnitaryFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    {J s : ℝ} {f : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hs_nn : 0 ≤ s)
    (hV_dec : V.SatisfiesDecayBound J f)
    (hf_super : IsSuperpolynomialDecay f)
    (v : BoxD D L)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA_v : IsSupportedOn Site {v} A_v) :
    let U_s := qacUnitaryFlow sys V s
    let c_1 := 4 * s * uniformCubeCommutatorFactor D L 1 (fun r => 2 * f r)
    0 ≤ c_1 ∧
    ‖U_s.1† * A_v * U_s.1 - A_v‖ ≤ (J * (2 * s * uniformCubeCommutatorFactor D L 1 (fun r => 2 * f r))) * ‖A_v‖ ∧
    (∀ r_LR : ℕ, 1 ≤ r_LR →
      ‖U_s.1† * A_v * U_s.1 - condExp Site (boxCube v r_LR) (U_s.1† * A_v * U_s.1)‖ ≤
        (J * c_1) * ‖A_v‖) ∧
    (∀ r_LR : ℕ,
      ‖U_s.1† * A_v * U_s.1 - condExp Site (boxBall v r_LR) (U_s.1† * A_v * U_s.1)‖ ≤
        (J * c_1) * ‖A_v‖) := by
  intro U_s c_1
  let D_loc := qacGeneratorPerturbation sys V
  let f_D : ℕ → ℝ := fun r => 2 * f r
  have hFlow := isKatoHastingsFlowSystem_qacUnitaryFlow sys V
  have hD_dec : D_loc.SatisfiesDecayBound J f_D :=
    (constructive_quasiLocal_qac_generator_and_flow sys V hf_super hV_dec).2.1
  have hf_D_nn : ∀ q ∈ Finset.Icc 1 L, 0 ≤ f_D q := fun q _ => by
    dsimp [f_D]; exact mul_nonneg zero_le_two (hf_super.1 q)
  have h_uc_nn : 0 ≤ uniformCubeCommutatorFactor D L 1 f_D :=
    uniformCubeCommutatorFactor_nonneg D L 1 hf_D_nn
  have hc1_nn : 0 ≤ c_1 := by dsimp [c_1]; positivity
  have hA_cube1 : IsSupportedOn Site (boxCube v 1) A_v :=
    isSupportedOn_mono (singleton_subset_boxCube v le_rfl) hA_v
  have h_comm : ∀ τ ∈ Set.Icc 0 s,
      ‖A_v * D_loc.totalPerturbation - D_loc.totalPerturbation * A_v‖ ≤
        (J * (2 * uniformCubeCommutatorFactor D L 1 f_D)) * ‖A_v‖ := by
    intro _ _
    exact (norm_opCommutator_localOp_katoGenerator_le_J_mul
      D_loc hJ_nn hf_D_nn hD_dec v 1 hA_cube1).2
  have h_duh := (duhamel_conjugation_bound sys.P0 (fun _ => D_loc.totalPerturbation)
    (fun t => (qacUnitaryFlow sys V t).1) (qacProjectorFlow sys V) hFlow A_v).2
    s ((J * (2 * uniformCubeCommutatorFactor D L 1 f_D)) * ‖A_v‖) hs_nn h_comm
  have h_drift : ‖U_s.1† * A_v * U_s.1 - A_v‖ ≤
      (J * (2 * s * uniformCubeCommutatorFactor D L 1 f_D)) * ‖A_v‖ := by
    calc ‖U_s.1† * A_v * U_s.1 - A_v‖
      _ ≤ s * ((J * (2 * uniformCubeCommutatorFactor D L 1 f_D)) * ‖A_v‖) := h_duh
      _ = (J * (2 * s * uniformCubeCommutatorFactor D L 1 f_D)) * ‖A_v‖ := by ring
  refine ⟨hc1_nn, h_drift, fun r_LR hr_LR => ?_, fun r_LR => ?_⟩
  · have h_comm_box : ∀ (B_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
        IsSupportedOn Site (boxCube v 1) B_loc →
        ∀ τ ∈ Set.Icc 0 s,
          ‖B_loc * D_loc.totalPerturbation - D_loc.totalPerturbation * B_loc‖ ≤
            (J * (2 * uniformCubeCommutatorFactor D L 1 f_D)) * ‖B_loc‖ := by
      intro B_loc hB_loc _ _
      exact (norm_opCommutator_localOp_katoGenerator_le_J_mul
        D_loc hJ_nn hf_D_nn hD_dec v 1 hB_loc).2
    have h1 := norm_katoFlowUnitary_singleSite_sub_condExp_le
      hFlow v hr_LR hs_nn h_comm_box A_v hA_v
    have h_eq : 2 * s * (J * (2 * uniformCubeCommutatorFactor D L 1 f_D)) = J * c_1 := by
      dsimp [c_1, f_D]; ring
    change ‖(katoFlowUnitary hFlow s).1† * A_v * (katoFlowUnitary hFlow s).1 -
      condExp Site (boxCube v r_LR) ((katoFlowUnitary hFlow s).1† * A_v * (katoFlowUnitary hFlow s).1)‖ ≤
      (J * c_1) * ‖A_v‖
    rwa [← h_eq]
  · let ΔA := U_s.1† * A_v * U_s.1 - A_v
    have hA_ball : IsSupportedOn Site (boxBall v r_LR) A_v :=
      isSupportedOn_mono (Finset.singleton_subset_iff.mpr (mem_boxBall_self v r_LR)) hA_v
    have hA_ce : condExp Site (boxBall v r_LR) A_v = A_v :=
      condExp_eq_self_of_isSupportedOn hA_ball
    have h_id : U_s.1† * A_v * U_s.1 - condExp Site (boxBall v r_LR) (U_s.1† * A_v * U_s.1) =
        ΔA - condExp Site (boxBall v r_LR) ΔA := by
      dsimp [ΔA]; rw [condExp_sub_clm, hA_ce]; abel
    have h_ce : ‖ΔA - condExp Site (boxBall v r_LR) ΔA‖ ≤ 2 * ‖ΔA‖ :=
      norm_sub_condExp_le_two_mul_norm (boxBall v r_LR) ΔA
    rw [h_id]
    dsimp [c_1, f_D, ΔA] at h_ce h_drift ⊢
    linarith

/-!
## 4. Sector-Symmetry Preservation Along `qacUnitaryFlow`
-/

/-- Helper: a list product of operators each commuting with `Pi_sec` commutes with `Pi_sec`. -/
private lemma commute_list_prod_left_of_forall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (Pi_sec : E →L[ℂ] E) (L_ops : List (E →L[ℂ] E))
    (h : ∀ A ∈ L_ops, Commute A Pi_sec) :
    Commute L_ops.prod Pi_sec := by
  induction L_ops with
  | nil =>
    rw [List.prod_nil]
    exact Commute.one_left Pi_sec
  | cons hd tl ih =>
    rw [List.prod_cons]
    exact (h hd List.mem_cons_self).mul_left
      (ih (fun A hA => h A (List.mem_cons_of_mem hd hA)))

/-- If `Pi_sec` commutes with every check projector `sys.checkProj i`, then `Pi_sec` commutes with
    `sys.H0`, `sys.P0`, every local ground projector `sys.localGroundProj A`, and every `anchoredSiteCheckOp anchor_reg sys u`. -/
theorem commute_H0_P0_P_loc_of_commute_checkProj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (anchor_reg : Finset (BoxD D L) → BoxD D L)
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_check_sec : ∀ i : ι, Commute (sys.checkProj i) Pi_sec) :
    Commute sys.H0 Pi_sec ∧
    Commute sys.P0 Pi_sec ∧
    (∀ A : Finset (BoxD D L), Commute (sys.localGroundProj A) Pi_sec) ∧
    (∀ u : BoxD D L, Commute (anchoredSiteCheckOp anchor_reg sys u) Pi_sec) := by
  refine ⟨?_, ?_, fun A => ?_, fun u => ?_⟩
  · dsimp [IndexedCommutingProjectorHamiltonian.H0]
    exact Commute.sum_left _ _ _ fun i _ => (h_check_sec i).smul_left _
  · dsimp [IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj]
    refine commute_list_prod_left_of_forall Pi_sec _ fun X hX => ?_
    rcases List.mem_map.mp hX with ⟨i, _, rfl⟩
    exact (Commute.one_left Pi_sec).sub_left (h_check_sec i)
  · dsimp [IndexedCommutingProjectorHamiltonian.localGroundProj, IndexedCommutingProjectorHamiltonian.localGroundProj]
    refine commute_list_prod_left_of_forall Pi_sec _ fun X hX => ?_
    rcases List.mem_map.mp hX with ⟨i, _, rfl⟩
    exact (Commute.one_left Pi_sec).sub_left (h_check_sec i)
  · dsimp [anchoredSiteCheckOp]
    exact Commute.sum_left _ _ _ fun i _ => (h_check_sec i).smul_left _

end
