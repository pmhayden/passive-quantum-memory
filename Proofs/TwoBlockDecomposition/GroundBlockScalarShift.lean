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

import Proofs.TwoBlockDecomposition.CartesianCubeSafeImmunity

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Ground-Block Scalar Centering and Approximate-Projector Single-Cube Telescoping

Defines `centeredSiteOp` and the local TQO-1 ground scalar `tqo1SiteCondExpScalar` of `condExp (boxCube u K) (X u)`, proves indexed local-to-global norm transfer on `IndexedCommutingProjectorHamiltonian`, and generalizes single-cube telescoping to operators with approximate ground-block annihilation (`3 * eps_k + 2 * eps_gnd`).

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

/-! ## 1. Centered Site Operators $\widehat{X}_u := X_u - (c_u : \mathbb{C}) \cdot 1$ & `tqo1SiteCondExpScalar` -/

/-- Centered operator $\widehat{X} := X - (c : \mathbb{C}) \cdot 1$ (Part I, Section 7.1 (`subsec:single-cube-telescoping`), Equation (84) (`eq:centered-Xu-and-Mk`)). -/
def centeredSiteOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (c : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  X - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)

/-- Ground-space TQO-1 scalar $c_u \in \mathbb{R}$ extracted from the scale-$K$ local conditional
    expectation $\mathbb{E}_{\mathrm{boxCube}(u, K)}(X)$:
    $$\mathrm{sys.P0} \cdot \mathbb{E}_{\mathrm{boxCube}(u, K)}(X) \cdot \mathrm{sys.P0} = (c_u : \mathbb{C}) \cdot \mathrm{sys.P0}.$$ -/
def tqo1SiteCondExpScalar {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (K : ℕ) (u : BoxD D L)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  if h : ∃ c : ℂ, sys.P0 * condExp Site (boxCube u K) X * sys.P0 = c • sys.P0 then
    h.choose.re
  else 0

/-- Under `SatisfiesTQO1 sys L_star` ($1 \le K \le L^*$) and `IsSelfAdjoint X`, the scalar
    `c_u := tqo1SiteCondExpScalar sys K u X` satisfies
    $\mathrm{sys.P0} \cdot \mathbb{E}_{\mathrm{boxCube}(u, K)}(X) \cdot \mathrm{sys.P0} = (c_u : \mathbb{C}) \cdot \mathrm{sys.P0}$
    and $|c_u| \le \|\mathbb{E}_{\mathrm{boxCube}(u, K)}(X)\|$. -/
theorem tqo1SiteCondExpScalar_spec {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {L_star K : ℕ} (hTQO1 : SatisfiesTQO1 sys L_star)
    (hK1 : 1 ≤ K) (hKL : K ≤ L_star) (u : BoxD D L)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hX_sa : IsSelfAdjoint X) :
    let c_u := tqo1SiteCondExpScalar sys K u X
    sys.P0 * condExp Site (boxCube u K) X * sys.P0 = (c_u : ℂ) • sys.P0 ∧
    |c_u| ≤ ‖condExp Site (boxCube u K) X‖ := by
  intro c_u
  have h_supp : IsSupportedOn Site (boxCube u K) (condExp Site (boxCube u K) X) :=
    isSupportedOn_condExp Site (boxCube u K) X
  have h_ex : ∃ c : ℂ, sys.P0 * condExp Site (boxCube u K) X * sys.P0 = c • sys.P0 :=
    hTQO1 K hK1 hKL u (condExp Site (boxCube u K) X) h_supp
  have hc_def : c_u = h_ex.choose.re := by
    dsimp [c_u, tqo1SiteCondExpScalar]; rw [dif_pos h_ex]
  have hc_spec : sys.P0 * condExp Site (boxCube u K) X * sys.P0 = h_ex.choose • sys.P0 :=
    h_ex.choose_spec
  have hO_sa : IsSelfAdjoint (condExp Site (boxCube u K) X) :=
    isSelfAdjoint_condExp_bhm (boxCube u K) hX_sa
  rcases tqo1_scalar_abs_le_norm_bhm sys.isStarProjection_P0 sys.frustration_free hc_spec with
    ⟨hc_norm, hc_im_fn⟩
  have hc_im : h_ex.choose.im = 0 := hc_im_fn hO_sa
  have hc_eq : (c_u : ℂ) = h_ex.choose := Complex.ext hc_def hc_im.symm
  refine ⟨hc_spec.trans (by rw [← hc_eq]), ?_⟩
  have h_abs : ‖(c_u : ℂ)‖ = ‖h_ex.choose‖ := by rw [hc_eq]
  rw [Complex.norm_real, Real.norm_eq_abs] at h_abs
  linarith

/-- Centering $X$ by a scalar multiple of the identity preserves self-adjointness, commutation with
    any operator (in particular `sys.P0` and `Pi_sec`), and the exact conditional expectation tail
    `centeredSiteOp X c - condExp Site A (centeredSiteOp X c) = X - condExp Site A X`. -/
theorem centeredSiteOp_sub_condExp_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (A : Finset (BoxD D L))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (c : ℝ) :
    condExp Site A (centeredSiteOp X c) =
      condExp Site A X - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) ∧
    centeredSiteOp X c - condExp Site A (centeredSiteOp X c) = X - condExp Site A X ∧
    ‖centeredSiteOp X c - condExp Site A (centeredSiteOp X c)‖ = ‖X - condExp Site A X‖ := by
  have h_one_supp : IsSupportedOn Site A
      ((c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :=
    isSupportedOn_smul A (c : ℂ) (isSupportedOn_one A)
  have h_cond_one :
      condExp Site A ((c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) =
        (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    condExp_eq_self_of_isSupportedOn h_one_supp
  have h_cond_sub :
      condExp Site A (centeredSiteOp X c) =
        condExp Site A X - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := by
    have h_map := (condExpCLM Site A).map_sub X
      ((c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    change condExp Site A (centeredSiteOp X c) =
      condExp Site A X - condExp Site A ((c : ℂ) • 1) at h_map
    rw [h_map, h_cond_one]
  have h_diff :
      centeredSiteOp X c - condExp Site A (centeredSiteOp X c) = X - condExp Site A X := by
    rw [h_cond_sub]
    dsimp [centeredSiteOp]
    exact sub_sub_sub_cancel_right X (condExp Site A X) ((c : ℂ) • 1)
  exact ⟨h_cond_sub, h_diff, by rw [h_diff]⟩

/-- When `Commute X sys.P0` and `sys.P0 * condExp Site (boxCube u K) X * sys.P0 = (c : ℂ) • sys.P0`,
    the centered operator $\widehat{X} := X - (c : \mathbb{C}) \cdot 1$ satisfies
    $\mathrm{sys.P0} \cdot \widehat{X} = \mathrm{sys.P0} \cdot (X - \mathbb{E}_{\mathrm{boxCube}(u, K)}(X)) \cdot \mathrm{sys.P0}$
    and $\|\mathrm{sys.P0} \cdot \widehat{X}\| \le \|X - \mathbb{E}_{\mathrm{boxCube}(u, K)}(X)\|$. -/
theorem norm_P0_mul_centeredSiteOp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (K : ℕ) (u : BoxD D L)
    {X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} {c ε_K : ℝ}
    (hX_comm : Commute X sys.P0)
    (hc_P0 : sys.P0 * condExp Site (boxCube u K) X * sys.P0 = (c : ℂ) • sys.P0)
    (h_tail_K : ‖X - condExp Site (boxCube u K) X‖ ≤ ε_K) :
    Commute (centeredSiteOp X c) sys.P0 ∧
    sys.P0 * centeredSiteOp X c =
      sys.P0 * (X - condExp Site (boxCube u K) X) * sys.P0 ∧
    ‖sys.P0 * centeredSiteOp X c‖ ≤ ε_K := by
  have h_comm : Commute (centeredSiteOp X c) sys.P0 := by
    dsimp [centeredSiteOp]
    exact hX_comm.sub_left ((Commute.one_left sys.P0).smul_left (c : ℂ))
  have hP0_idem : sys.P0 * sys.P0 = sys.P0 := sys.isStarProjection_P0.isIdempotentElem.eq
  have hP0_norm : ‖sys.P0‖ ≤ 1 := isStarProjection_norm_le_one_bhm sys.isStarProjection_P0
  have hP0_X_P0 : (sys.P0 * sys.P0) * X = sys.P0 * X * sys.P0 := by
    calc (sys.P0 * sys.P0) * X
      _ = sys.P0 * (sys.P0 * X) := mul_assoc _ _ _
      _ = sys.P0 * (X * sys.P0) := by rw [hX_comm.eq]
      _ = sys.P0 * X * sys.P0 := (mul_assoc _ _ _).symm
  have h_eq : sys.P0 * centeredSiteOp X c =
      sys.P0 * (X - condExp Site (boxCube u K) X) * sys.P0 := by
    dsimp [centeredSiteOp]
    calc sys.P0 * (X - (c : ℂ) • 1)
      _ = sys.P0 * X - sys.P0 * ((c : ℂ) • 1) := mul_sub sys.P0 X _
      _ = (sys.P0 * sys.P0) * X - (c : ℂ) • sys.P0 := by
        rw [hP0_idem, mul_smul_comm, mul_one]
      _ = sys.P0 * X * sys.P0 - sys.P0 * condExp Site (boxCube u K) X * sys.P0 := by
        rw [hP0_X_P0, hc_P0]
      _ = sys.P0 * (X - condExp Site (boxCube u K) X) * sys.P0 := by
        rw [mul_sub, sub_mul]
  refine ⟨h_comm, h_eq, ?_⟩
  rw [h_eq]
  exact le_trans (norm_sandwich_le_of_norm_le_one hP0_norm hP0_norm) h_tail_K

/-! ## 2. Generalized Single-Cube Telescoping & Indexed Norm Transfer -/

/-- **Remainder-Tolerant Bravyi–Hastings (2011) Lemma 4 Single-Cube Telescoping Bound (`telescoping_norm_bounds_of_approx_P0`)**:
    Generalizes `telescoping_norm_bounds_abstract` from exact $P X = 0$
    to $\|P X\| \le \varepsilon_{\mathrm{gnd}}$: if $\|P_C O\| \le \|P O\|$ and $\|X - O\| \le \varepsilon_k$,
    then $M := (1 - P_C) O (1 - P_C)$ is self-adjoint and satisfies
    $$\|X - M\| \le 3\varepsilon_k + 2\varepsilon_{\mathrm{gnd}}.$$ -/
theorem telescoping_norm_bounds_of_approx_P0 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P P_C X O : E →L[ℂ] E) {ε_k ε_gnd : ℝ}
    (hP_proj : IsStarProjection P)
    (hPC_proj : IsStarProjection P_C)
    (_hX_sa : IsSelfAdjoint X)
    (hO_sa : IsSelfAdjoint O)
    (hPX : ‖P * X‖ ≤ ε_gnd)
    (h_cor1 : ‖P_C * O‖ ≤ ‖P * O‖)
    (h_tail : ‖X - O‖ ≤ ε_k) :
    let M := (1 - P_C) * O * (1 - P_C)
    IsSelfAdjoint M ∧
    ‖P_C * O‖ ≤ ε_k + ε_gnd ∧
    ‖O * P_C‖ ≤ ε_k + ε_gnd ∧
    ‖X - M‖ ≤ bhmTelescopingFactor * ε_k + 2 * ε_gnd := by
  intro M
  have hM_sa : IsSelfAdjoint M := by
    rw [isSelfAdjoint_iff]; dsimp [M]
    rw [star_mul, star_mul, (hPC_proj.one_sub).isSelfAdjoint.star_eq, hO_sa.star_eq, mul_assoc]
  have hP_norm : ‖P‖ ≤ 1 := isStarProjection_norm_le_one_bhm hP_proj
  have h1PC_norm : ‖1 - P_C‖ ≤ 1 := isStarProjection_norm_le_one_bhm hPC_proj.one_sub
  have h_PO_eq : P * O = P * X - P * (X - O) := by rw [mul_sub, sub_sub_cancel]
  have h_PO_norm : ‖P * O‖ ≤ ε_k + ε_gnd := by
    rw [h_PO_eq]
    have h1 : ‖P * (X - O)‖ ≤ ε_k := by
      calc ‖P * (X - O)‖
        _ ≤ ‖P‖ * ‖X - O‖ := norm_mul_le _ _
        _ ≤ 1 * ε_k := mul_le_mul hP_norm h_tail (norm_nonneg _) zero_le_one
        _ = ε_k := one_mul _
    calc ‖P * X - P * (X - O)‖
      _ ≤ ‖P * X‖ + ‖P * (X - O)‖ := norm_sub_le _ _
      _ ≤ ε_gnd + ε_k := add_le_add hPX h1
      _ = ε_k + ε_gnd := add_comm _ _
  have h_PCO_norm : ‖P_C * O‖ ≤ ε_k + ε_gnd := le_trans h_cor1 h_PO_norm
  have h_OPC_star : O * P_C = (P_C * O)† := by
    change O * P_C = star (P_C * O)
    rw [star_mul, hO_sa.star_eq, hPC_proj.isSelfAdjoint.star_eq]
  have h_OPC_norm : ‖O * P_C‖ ≤ ε_k + ε_gnd := by
    rw [h_OPC_star,
      (ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).norm_map]
    exact h_PCO_norm
  have h_1PC_OPC : ‖(1 - P_C) * (O * P_C)‖ ≤ ε_k + ε_gnd := by
    calc ‖(1 - P_C) * (O * P_C)‖
      _ ≤ ‖1 - P_C‖ * ‖O * P_C‖ := norm_mul_le _ _
      _ ≤ 1 * (ε_k + ε_gnd) := mul_le_mul h1PC_norm h_OPC_norm (norm_nonneg _) zero_le_one
      _ = ε_k + ε_gnd := one_mul _
  have h_XM_norm : ‖X - M‖ ≤ bhmTelescopingFactor * ε_k + 2 * ε_gnd := by
    dsimp [M, bhmTelescopingFactor]
    rw [ring_telescoping_diff_decomp P_C X O]
    have h_part1 : ‖(X - O) + P_C * O‖ ≤ 2 * ε_k + ε_gnd := by
      calc ‖(X - O) + P_C * O‖
        _ ≤ ‖X - O‖ + ‖P_C * O‖ := norm_add_le _ _
        _ ≤ ε_k + (ε_k + ε_gnd) := add_le_add h_tail h_PCO_norm
        _ = 2 * ε_k + ε_gnd := by ring
    calc ‖((X - O) + P_C * O) + (1 - P_C) * (O * P_C)‖
      _ ≤ ‖(X - O) + P_C * O‖ + ‖(1 - P_C) * (O * P_C)‖ := norm_add_le _ _
      _ ≤ (2 * ε_k + ε_gnd) + (ε_k + ε_gnd) := add_le_add h_part1 h_1PC_OPC
      _ = 3 * ε_k + 2 * ε_gnd := by ring
  exact ⟨hM_sa, h_PCO_norm, h_OPC_norm, h_XM_norm⟩

/-- For an `IndexedCommutingProjectorHamiltonian` whose checks are each supported inside a $2$-cube,
    if $M$ is supported on $A_0$ and $B_0$ is a $1$-collar around $A_0$ (`IsOneCollarOf A0 B0`),
    then `sys.P_loc B0 * M * sys.P_loc B0` commutes with `sys.P0`. -/
lemma IndexedCommutingProjectorHamiltonian.commute_collar_sandwich_P0_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_cube_cov : ∀ i : ι, ∃ A ∈ boxCubes D L 2, sys.support i ⊆ A)
    {A0 B0 : Finset (BoxD D L)}
    {M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hCollar : IsOneCollarOf A0 B0)
    (hM_supp : IsSupportedOn Site A0 M) :
    Commute (sys.localGroundProj B0 * M * sys.localGroundProj B0) sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.P0,
    IndexedCommutingProjectorHamiltonian.groundProj]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
  apply commute_one_sub_right_bhm
  rcases h_cube_cov i with ⟨K, hK_cube, hiK⟩
  by_cases hDisj : Disjoint K A0
  · have hDisj_i : Disjoint A0 (sys.support i) :=
      Disjoint.mono_right hiK hDisj.symm
    have h_comm_M : Commute M (sys.checkProj i) :=
      commute_of_isSupportedOn_disjoint hDisj_i hM_supp (sys.is_supported i)
    have h_comm_PB0 : Commute (sys.localGroundProj B0) (sys.checkProj i) :=
      sys.commute_P_loc_checkProj B0 i
    exact (h_comm_PB0.mul_left h_comm_M).mul_left h_comm_PB0
  · have hKB0 : K ⊆ B0 := hCollar.2 K hK_cube hDisj
    have hiB0 : sys.support i ⊆ B0 := Finset.Subset.trans hiK hKB0
    have h_QP : sys.checkProj i * sys.localGroundProj B0 = 0 :=
      sys.checkProj_mul_P_loc_eq_zero i B0 hiB0
    have h_PQ : sys.localGroundProj B0 * sys.checkProj i = 0 := by
      rw [(sys.commute_P_loc_checkProj B0 i).eq, h_QP]
    rw [commute_iff_eq]
    calc (sys.localGroundProj B0 * M * sys.localGroundProj B0) * sys.checkProj i
      _ = sys.localGroundProj B0 * M * (sys.localGroundProj B0 * sys.checkProj i) := by rw [mul_assoc]
      _ = 0 := by rw [h_PQ, mul_zero]
      _ = (sys.checkProj i * sys.localGroundProj B0) * M * sys.localGroundProj B0 := by
        rw [h_QP, zero_mul, zero_mul]
      _ = sys.checkProj i * (sys.localGroundProj B0 * M * sys.localGroundProj B0) := by simp only [mul_assoc]

/-- Triangle inequality bound for `indexedSingleCubeDiffD sys C u k X` from consecutive
    approximation bounds `‖X - M_k‖ ≤ δ_k` and `‖X - M_{k-1}‖ ≤ δ_{k-1}`. -/
lemma norm_indexedSingleCubeDiffD_le_of_approx_bounds {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (C : ℝ) (u : BoxD D L) (k : ℕ)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {δ_k δ_prev : ℝ}
    (hk : ‖X - indexedSingleCubeApproxM sys C u k X‖ ≤ δ_k)
    (hprev : ‖X - indexedSingleCubeApproxM sys C u (k - 1) X‖ ≤ δ_prev) :
    ‖indexedSingleCubeDiffD sys C u k X‖ ≤ δ_k + δ_prev := by
  have h_eq :
      indexedSingleCubeDiffD sys C u k X =
        (X - indexedSingleCubeApproxM sys C u (k - 1) X) -
        (X - indexedSingleCubeApproxM sys C u k X) := by
    dsimp [indexedSingleCubeDiffD]; abel
  rw [h_eq]
  calc ‖(X - indexedSingleCubeApproxM sys C u (k - 1) X) -
          (X - indexedSingleCubeApproxM sys C u k X)‖
    _ ≤ ‖X - indexedSingleCubeApproxM sys C u (k - 1) X‖ +
          ‖X - indexedSingleCubeApproxM sys C u k X‖ := norm_sub_le _ _
    _ ≤ δ_prev + δ_k := add_le_add hprev hk
    _ = δ_k + δ_prev := add_comm _ _

/-! ## 3. Enclosing-Cube Support Monotonicity & Annihilation for `indexedSingleCubeDiffD` -/

/-- For $1 \le C$, incrementing the input radius by $1$ increases `linearExpansionRadius C r` by at least $1$. -/
lemma linearExpansionRadius_add_one_le {C : ℝ} (hC : 1 ≤ C) (r : ℕ) :
    linearExpansionRadius C r + 1 ≤ linearExpansionRadius C (r + 1) := by
  dsimp [linearExpansionRadius]
  have h1 : C * (r : ℝ) + 1 ≤ C * ((r + 1 : ℕ) : ℝ) := by
    push_cast; nlinarith
  have h2 : C * ((r + 1 : ℕ) : ℝ) ≤ (⌈C * ((r + 1 : ℕ) : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h_pos : 1 ≤ ⌈C * ((r + 1 : ℕ) : ℝ)⌉₊ := by
    have : (1 : ℝ) ≤ (⌈C * ((r + 1 : ℕ) : ℝ)⌉₊ : ℝ) := by
      have hr : (0 : ℝ) ≤ C * (r : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg r)
      linarith
    exact_mod_cast this
  have h_ceil : ⌈C * (r : ℝ)⌉₊ ≤ ⌈C * ((r + 1 : ℕ) : ℝ)⌉₊ - 1 := by
    rw [Nat.ceil_le, Nat.cast_sub h_pos, Nat.cast_one]
    linarith
  omega

/-- Monotonicity of `singleCubeSupportC C u k` in $k$: for $1 \le C$ and $2 \le k$,
    `singleCubeSupportC C u (k - 1) ⊆ singleCubeSupportC C u k`. -/
theorem singleCubeSupportC_pred_subset {D L : ℕ}
    {C : ℝ} (hC : 1 ≤ C) (u : BoxD D L) {k : ℕ} (hk2 : 2 ≤ k) :
    singleCubeSupportC C u (k - 1) ⊆ singleCubeSupportC C u k := by
  intro y hy
  simp only [singleCubeSupportC, enclosingBoxCube, mem_boxCube] at hy ⊢
  intro i
  let r1 := (k - 1) + bhmElementaryCubeSide
  let r2 := k + bhmElementaryCubeSide
  have hr : r2 = r1 + 1 := by dsimp [r1, r2, bhmElementaryCubeSide]; omega
  let R1 := linearExpansionRadius C r1
  let R2 := linearExpansionRadius C r2
  have hR : R1 + 1 ≤ R2 := by
    dsimp [R1, R2]; rw [hr]; exact linearExpansionRadius_add_one_le hC r1
  have hi : ((shiftDownOne u i).val - (R1 - r1) / 2 ≤ (y i).val) ∧
      ((y i).val < (shiftDownOne u i).val - (R1 - r1) / 2 + R1) := hy i
  change ((shiftDownOne u i).val - (R2 - r2) / 2 ≤ (y i).val) ∧
    ((y i).val < (shiftDownOne u i).val - (R2 - r2) / 2 + R2)
  omega

end
