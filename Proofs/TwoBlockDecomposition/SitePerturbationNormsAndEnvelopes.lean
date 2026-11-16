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

import Proofs.QuasiLocalDressing.KatoFlowUnitaryCondExpTails
import Proofs.TwoBlockDecomposition.GroundBlockScalarShift

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Site-Anchored Perturbation Norm Bounds, Shell Moment Sums, and Super-Polynomial Splitting Envelopes

Proves `O(J)` operator-norm bounds on `sitePerturbationOp` and `indexedFilteredSiteOp`, shows that super-polynomial tail decay makes the shell moment series `bhmShellUniformMomentBound` summable uniformly in system size `L` and cutoff `K`, and constructs the super-polynomial ground-space splitting envelope `bhmMultiScaleSplittingEnvelope`.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Lemma 6.2 (`lem:dsuper-closure`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part II, Section 2 (`subsec:setup`), Definition 2.3 (`def:perturbation-class`), Lemma 2.4 (`lem:D-super-closure`)
-/

/-! ## 1. Site Perturbation $O(J)$ Bounds & Unconditional `Commute sys.H0 (sys.siteCheckOp u)` -/

/-- For any scale $q$ and site $u \in \mathrm{BoxD}\ D\ L$, at most one cube $A \in \mathrm{BoxCubes}\ D\ L\ q$
    has `anchorOfCube q A = u`. -/
lemma card_filter_anchorOfCube_le_one {D L : ℕ} [NeZero L] (q : ℕ) (u : BoxD D L) :
    ((boxCubes D L q).filter (fun A => anchorOfCube q A = u)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun A₁ hA₁ A₂ hA₂ => ?_
  rcases Finset.mem_filter.mp hA₁ with ⟨hA₁_mem, hA₁_u⟩
  rcases Finset.mem_filter.mp hA₂ with ⟨hA₂_mem, hA₂_u⟩
  calc A₁
    _ = boxCube (anchorOfCube q A₁) q := (boxCube_anchorOfCube hA₁_mem).symm
    _ = boxCube u q := by rw [hA₁_u]
    _ = boxCube (anchorOfCube q A₂) q := by rw [← hA₂_u]
    _ = A₂ := boxCube_anchorOfCube hA₂_mem

/-- For any `V : QuasiLocalPerturbation D L Site` satisfying `V.SatisfiesDecayBound J f` with $J \ge 0$
    and $f \ge 0$, the site-anchored perturbation at $u$ satisfies
    `‖sitePerturbationOp V u‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f q`. -/
theorem norm_sitePerturbationOp_le_mul_sum_Icc {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f) (u : BoxD D L) :
    ‖sitePerturbationOp V u‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f q := by
  unfold sitePerturbationOp
  rw [Finset.mul_sum]
  calc ‖∑ q ∈ Finset.Icc 1 L,
          ∑ A ∈ (boxCubes D L q).filter (fun A => anchorOfCube q A = u), V.term q A‖
    _ ≤ ∑ q ∈ Finset.Icc 1 L,
          ‖∑ A ∈ (boxCubes D L q).filter (fun A => anchorOfCube q A = u), V.term q A‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Icc 1 L, J * f q := by
      refine Finset.sum_le_sum fun q hq => ?_
      let S_q := (boxCubes D L q).filter (fun A => anchorOfCube q A = u)
      have h_card : (S_q.card : ℝ) ≤ 1 := by
        exact_mod_cast card_filter_anchorOfCube_le_one q u
      calc ‖∑ A ∈ S_q, V.term q A‖
        _ ≤ ∑ A ∈ S_q, ‖V.term q A‖ := norm_sum_le _ _
        _ ≤ ∑ _A ∈ S_q, J * f q :=
          Finset.sum_le_sum fun A hA => hV_dec q hq A (Finset.mem_filter.mp hA).1
        _ = (S_q.card : ℝ) * (J * f q) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * (J * f q) := mul_le_mul_of_nonneg_right h_card (mul_nonneg hJ (hf_nn q))
        _ = J * f q := one_mul _

/-- Range-sum version of `norm_sitePerturbationOp_le_mul_sum_Icc`:
    `‖sitePerturbationOp V u‖ ≤ J * ∑ q ∈ Finset.range (L + 1), f q`. -/
theorem norm_sitePerturbationOp_le_mul_sum_range {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q)
    (hV_dec : V.SatisfiesDecayBound J f) (u : BoxD D L) :
    ‖sitePerturbationOp V u‖ ≤ J * ∑ q ∈ Finset.range (L + 1), f q := by
  have h_sub : Finset.Icc 1 L ⊆ Finset.range (L + 1) := fun q hq =>
    Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hq).2; omega)
  have h_sum_le : ∑ q ∈ Finset.Icc 1 L, f q ≤ ∑ q ∈ Finset.range (L + 1), f q :=
    Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun q _ _ => hf_nn q)
  exact le_trans (norm_sitePerturbationOp_le_mul_sum_Icc V hJ hf_nn hV_dec u)
    (mul_le_mul_of_nonneg_left h_sum_le hJ)

/-- Infinite-sum version of `norm_sitePerturbationOp_le_mul_sum_Icc`: if `Summable f`, then
    `‖sitePerturbationOp V u‖ ≤ J * (∑' q : ℕ, f q)`. -/
theorem norm_sitePerturbationOp_le_mul_tsum {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q) (hf_sum : Summable f)
    (hV_dec : V.SatisfiesDecayBound J f) (u : BoxD D L) :
    ‖sitePerturbationOp V u‖ ≤ J * (∑' q : ℕ, f q) := by
  have h_le : ∑ q ∈ Finset.Icc 1 L, f q ≤ ∑' q : ℕ, f q :=
    hf_sum.sum_le_tsum (Finset.Icc 1 L) (fun q _ => hf_nn q)
  exact le_trans (norm_sitePerturbationOp_le_mul_sum_Icc V hJ hf_nn hV_dec u)
    (mul_le_mul_of_nonneg_left h_le hJ)

/-- Every `sys.siteCheckOp u` of an `IndexedCommutingProjectorHamiltonian` commutes with `sys.H0`. -/
theorem IndexedCommutingProjectorHamiltonian.commute_H0_siteCheckOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    Commute sys.H0 (sys.siteCheckOp u) := by
  unfold IndexedCommutingProjectorHamiltonian.H0 IndexedCommutingProjectorHamiltonian.siteCheckOp
  refine Commute.sum_left Finset.univ _ _ fun i _ => ?_
  refine Commute.sum_right _ _ _ fun j _ => ?_
  exact ((sys.pairwise_commute i j).smul_left (sys.weight i : ℂ)).smul_right (sys.weight j : ℂ)

/-! ## 2. Bare-Frame Operator-Norm Bounds for `indexedFilteredSiteOp` -/

/-- Unitary invariance + filter bound for the site perturbation part:
    if `‖bochnerFilteredOp H w_BH11 (sitePerturbationOp V u)‖ ≤ C_w * ‖sitePerturbationOp V u‖`
    and `‖sitePerturbationOp V u‖ ≤ J * S_V` ($C_w \ge 0$), then
    `‖U_dress.1† * bochnerFilteredOp H w_BH11 (sitePerturbationOp V u) * U_dress.1‖ ≤ C_w * J * S_V`. -/
theorem norm_unitary_conj_bochnerFilteredOp_sitePerturbationOp_le {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (u : BoxD D L) {C_w J S_V : ℝ} (hCw : 0 ≤ C_w)
    (h_filt : ‖bochnerFilteredOp H bhFilterWeight (sitePerturbationOp V u)‖ ≤
      C_w * ‖sitePerturbationOp V u‖)
    (h_site : ‖sitePerturbationOp V u‖ ≤ J * S_V) :
    ‖U_dress.1† * bochnerFilteredOp H bhFilterWeight (sitePerturbationOp V u) * U_dress.1‖ ≤
      C_w * J * S_V := by
  calc ‖U_dress.1† * bochnerFilteredOp H bhFilterWeight (sitePerturbationOp V u) * U_dress.1‖
    _ ≤ ‖bochnerFilteredOp H bhFilterWeight (sitePerturbationOp V u)‖ :=
      norm_unitary_adj_conj_le_clm U_dress _
    _ ≤ C_w * ‖sitePerturbationOp V u‖ := h_filt
    _ ≤ C_w * (J * S_V) := mul_le_mul_of_nonneg_left h_site hCw
    _ = C_w * J * S_V := by ring

/-- Bare-frame 3-term $O(J)$ bound for `indexedFilteredSiteOp sys V U_dress w_BH11 u`:
    using `norm_bochnerFilteredSiteOp_le_of_bare_commute` and
    `sys.commute_H0_siteCheckOp u`, if `‖sitePerturbationOp V u‖ ≤ J * S_V`,
    `‖opCommutator V.V_tot (sys.siteCheckOp u)‖ ≤ J * S_Q`, and
    `‖U_dress.1† * sys.siteCheckOp u * U_dress.1 - sys.siteCheckOp u‖ ≤ J * S_U`, then
    `‖indexedFilteredSiteOp sys V U_dress w_BH11 u‖ ≤ J * (S_V + Real.pi * S_Q + S_U)`. -/
theorem norm_indexedFilteredSiteOp_w_BH11_le_of_bare_O_J {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (u : BoxD D L) {J S_V S_Q S_U : ℝ}
    (h_V : ‖sitePerturbationOp V u‖ ≤ J * S_V)
    (h_Q : ‖opCommutator V.totalPerturbation (sys.siteCheckOp u)‖ ≤ J * S_Q)
    (h_U : ‖U_dress.1† * sys.siteCheckOp u * U_dress.1 - sys.siteCheckOp u‖ ≤ J * S_U) :
    ‖indexedFilteredSiteOp sys V U_dress bhFilterWeight u‖ ≤ J * (S_V + Real.pi * S_Q + S_U) := by
  have hH_sa : IsSelfAdjoint (sys.H0 + V.totalPerturbation) :=
    isSelfAdjoint_add_clm sys.isSelfAdjoint_H0 V.isSelfAdjoint_totalPerturbation
  rcases integrable_and_integral_norm_w_BH11_mul_abs_le with ⟨hw_t_int, hw_t_le⟩
  have h1 := norm_bochnerFilteredSiteOp_le_of_bare_commute
    hH_sa (sys.commute_H0_siteCheckOp u) U_dress integrable_w_BH11
    integral_w_BH11_eq_one hw_t_int (V_u := sitePerturbationOp V u)
  rw [ ← indexedFilteredSiteOp_eq_bochnerFilteredSiteOp,
       integral_norm_w_BH11_eq_one, one_mul ] at h1
  have h_pi : (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) * ‖opCommutator V.totalPerturbation (sys.siteCheckOp u)‖ ≤
      Real.pi * (J * S_Q) := by
    calc (∫ t : ℝ, ‖bhFilterWeight t‖ * |t|) * ‖opCommutator V.totalPerturbation (sys.siteCheckOp u)‖
      _ ≤ Real.pi * ‖opCommutator V.totalPerturbation (sys.siteCheckOp u)‖ :=
        mul_le_mul_of_nonneg_right hw_t_le (norm_nonneg _)
      _ ≤ Real.pi * (J * S_Q) :=
        mul_le_mul_of_nonneg_left h_Q Real.pi_pos.le
  linarith

/-! ## 3. Explicit Small-$J$ Slope and Splitting Calibration -/

/-- **Small-$J$ Slope Calibration (`slope_le_bhmSandwichDeviation_of_J_le_moments`)**:
    When `M0 ≤ J * m_0`, `ε_tail k ≤ J * g_tail k` for $k \in \mathrm{Finset.Ico}\ 1\ K$, and
    `m_0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * g_tail k * ((k + 1 : ℝ) ^ D) ≤ C_mom`,
    for any `0 ≤ J ≤ bhmSandwichDeviation / (8 * (5 : ℝ) ^ D * (C_mom + 1))` we have
    `8 * (5 : ℝ) ^ D * (M0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * ε_tail k * ((k + 1 : ℝ) ^ D)) ≤ bhmSandwichDeviation`. -/
theorem slope_le_bhmSandwichDeviation_of_J_le_moments
    (D K : ℕ) {J m_0 C_mom M0 : ℝ} {ε_tail g_tail : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hC_mom_nn : 0 ≤ C_mom)
    (hM0 : M0 ≤ J * m_0)
    (hε_tail : ∀ k ∈ Finset.Ico 1 K, ε_tail k ≤ J * g_tail k)
    (h_mom : m_0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * g_tail k * ((k + 1 : ℝ) ^ D) ≤ C_mom)
    (hJ_le : J ≤ bhmSandwichDeviation / (8 * (5 : ℝ) ^ D * (C_mom + 1))) :
    8 * (5 : ℝ) ^ D *
      (M0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * ε_tail k * ((k + 1 : ℝ) ^ D)) ≤
      bhmSandwichDeviation := by
  have h1 : M0 * (1 : ℝ) ^ D ≤ J * (m_0 * (1 : ℝ) ^ D) := by
    rw [one_pow, mul_one, mul_one]; exact hM0
  have h2 : ∑ k ∈ Finset.Ico 1 K, 2 * ε_tail k * ((k + 1 : ℝ) ^ D) ≤
      J * ∑ k ∈ Finset.Ico 1 K, 2 * g_tail k * ((k + 1 : ℝ) ^ D) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_le := hε_tail k hk
    have hpow_nn : 0 ≤ ((k + 1 : ℝ) ^ D) := by positivity
    calc 2 * ε_tail k * ((k + 1 : ℝ) ^ D)
      _ ≤ 2 * (J * g_tail k) * ((k + 1 : ℝ) ^ D) := by
        apply mul_le_mul_of_nonneg_right _ hpow_nn
        linarith
      _ = J * (2 * g_tail k * ((k + 1 : ℝ) ^ D)) := by ring
  have h_sum_le : M0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * ε_tail k * ((k + 1 : ℝ) ^ D) ≤
      J * (C_mom + 1) := by
    calc M0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * ε_tail k * ((k + 1 : ℝ) ^ D)
      _ ≤ J * (m_0 * (1 : ℝ) ^ D) + J * ∑ k ∈ Finset.Ico 1 K, 2 * g_tail k * ((k + 1 : ℝ) ^ D) :=
        add_le_add h1 h2
      _ = J * (m_0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * g_tail k * ((k + 1 : ℝ) ^ D)) := by ring
      _ ≤ J * C_mom := mul_le_mul_of_nonneg_left h_mom hJ_nn
      _ ≤ J * (C_mom + 1) := mul_le_mul_of_nonneg_left (by linarith) hJ_nn
  have h_denom_pos : 0 < 8 * (5 : ℝ) ^ D * (C_mom + 1) := by positivity
  have hJ_mul : J * (8 * (5 : ℝ) ^ D * (C_mom + 1)) ≤ bhmSandwichDeviation :=
    (le_div_iff₀ h_denom_pos).mp hJ_le
  have h8_nn : 0 ≤ 8 * (5 : ℝ) ^ D := by positivity
  calc 8 * (5 : ℝ) ^ D *
        (M0 * (1 : ℝ) ^ D + ∑ k ∈ Finset.Ico 1 K, 2 * ε_tail k * ((k + 1 : ℝ) ^ D))
    _ ≤ 8 * (5 : ℝ) ^ D * (J * (C_mom + 1)) := mul_le_mul_of_nonneg_left h_sum_le h8_nn
    _ = J * (8 * (5 : ℝ) ^ D * (C_mom + 1)) := by ring
    _ ≤ bhmSandwichDeviation := hJ_mul

/-- Normalized ($J = 1$) shell moment sum matching the exact `h_slope` sum of
    `mkBH11DressingMasterBundleOfMultiScaleCondExp`. -/
def bhmShellNormalizedMomentSum (D : ℕ) (C : ℝ) (K : ℕ) (m_0 : ℝ) (g_tail : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 K,
    ((bhmTelescopingFactor * g_tail k + 2 * g_tail K) +
      (if k = 1 then m_0 else bhmTelescopingFactor * g_tail (k - 1) + 2 * g_tail K)) *
    (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)

/-- **Exact Multi-Scale Shell Slope Calibration (`slope_bhmShell_le_bhmSandwichDeviation_of_J_le`)**:
    When `M0 ≤ J * m_0`, `∀ k ∈ Finset.Icc 1 K, ε_tail k ≤ J * g_tail k`, and
    `bhmShellNormalizedMomentSum D C K m_0 g_tail ≤ C_mom` ($C_{\mathrm{mom}} \ge 0$), for any
    `0 ≤ J ≤ bhmSandwichDeviation / (C_mom + 1)` the exact `h_slope` condition of
    `mkBH11DressingMasterBundleOfMultiScaleCondExp` and
    `mkBH11SectorDressingMasterBundleOfMultiScaleCondExp` holds automatically. -/
theorem slope_bhmShell_le_bhmSandwichDeviation_of_J_le
    (D : ℕ) (C : ℝ) {K : ℕ} (hK1 : 1 ≤ K)
    {J m_0 C_mom M0 : ℝ} {ε_tail g_tail : ℕ → ℝ}
    (hJ_nn : 0 ≤ J) (hC_mom_nn : 0 ≤ C_mom)
    (hM0 : M0 ≤ J * m_0)
    (hε_tail : ∀ k ∈ Finset.Icc 1 K, ε_tail k ≤ J * g_tail k)
    (h_mom : bhmShellNormalizedMomentSum D C K m_0 g_tail ≤ C_mom)
    (hJ_le : J ≤ bhmSandwichDeviation / (C_mom + 1)) :
    (∑ k ∈ Finset.Icc 1 K,
      ((bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) +
        (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K)) *
      (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)) ≤
      bhmSandwichDeviation := by
  have hK_mem : K ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hK1, le_rfl⟩
  have hK_le : ε_tail K ≤ J * g_tail K := hε_tail K hK_mem
  have h_sum_le :
      (∑ k ∈ Finset.Icc 1 K,
        ((bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) +
          (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K)) *
        (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)) ≤
      J * bhmShellNormalizedMomentSum D C K m_0 g_tail := by
    unfold bhmShellNormalizedMomentSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk_le : ε_tail k ≤ J * g_tail k := hε_tail k hk
    have hV_nn :
        0 ≤ (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D) := by
      positivity
    have h_coeff :
        (bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) +
          (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K) ≤
        J * ((bhmTelescopingFactor * g_tail k + 2 * g_tail K) +
          (if k = 1 then m_0 else bhmTelescopingFactor * g_tail (k - 1) + 2 * g_tail K)) := by
      dsimp [bhmTelescopingFactor]
      by_cases hk_eq1 : k = 1
      · rw [if_pos hk_eq1, if_pos hk_eq1]
        linarith
      · rw [if_neg hk_eq1, if_neg hk_eq1]
        rcases Finset.mem_Icc.mp hk with ⟨hk1, hkK⟩
        have hprev_le : ε_tail (k - 1) ≤ J * g_tail (k - 1) :=
          hε_tail (k - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        linarith
    calc ((bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) +
            (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K)) *
          (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)
      _ ≤ (J * ((bhmTelescopingFactor * g_tail k + 2 * g_tail K) +
            (if k = 1 then m_0 else bhmTelescopingFactor * g_tail (k - 1) + 2 * g_tail K))) *
          (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D) :=
        mul_le_mul_of_nonneg_right h_coeff hV_nn
      _ = J * (((bhmTelescopingFactor * g_tail k + 2 * g_tail K) +
            (if k = 1 then m_0 else bhmTelescopingFactor * g_tail (k - 1) + 2 * g_tail K)) *
          (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)) := by
        ring
  have h_denom_pos : 0 < C_mom + 1 := by linarith
  have hJ_mul : J * (C_mom + 1) ≤ bhmSandwichDeviation :=
    (le_div_iff₀ h_denom_pos).mp hJ_le
  calc (∑ k ∈ Finset.Icc 1 K,
        ((bhmTelescopingFactor * ε_tail k + 2 * ε_tail K) +
          (if k = 1 then M0 else bhmTelescopingFactor * ε_tail (k - 1) + 2 * ε_tail K)) *
        (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D))
    _ ≤ J * bhmShellNormalizedMomentSum D C K m_0 g_tail := h_sum_le
    _ ≤ J * C_mom := mul_le_mul_of_nonneg_left h_mom hJ_nn
    _ ≤ J * (C_mom + 1) := mul_le_mul_of_nonneg_left (by linarith) hJ_nn
    _ ≤ bhmSandwichDeviation := hJ_mul

/-! ## 4. Uniform-in-$K$ Summability of `bhmShellNormalizedMomentSum` under `IsSuperpolynomialDecay` -/

/-- `IsSuperpolynomialDecay` is closed under right shift by $1$: `k ↦ g (k - 1)`. -/
lemma isSuperpolynomialDecay_pred {g : ℕ → ℝ} (hg : IsSuperpolynomialDecay g) :
    IsSuperpolynomialDecay (fun k : ℕ => g (k - 1)) := by
  refine ⟨fun k => hg.1 (k - 1), fun n => ?_⟩
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have h_tendsto_pred : Tendsto (fun k : ℕ => k - 1) atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    rw [Filter.eventually_atTop]
    exact ⟨b + 1, fun k hk => by omega⟩
  have h_comp : Tendsto (fun k : ℕ => ((k - 1 : ℕ) : ℝ) ^ n * g (k - 1)) atTop (𝓝 0) :=
    (hg.2 n).comp h_tendsto_pred
  have h_upper : Tendsto (fun k : ℕ => (2 : ℝ) ^ n * (((k - 1 : ℕ) : ℝ) ^ n * g (k - 1)))
      atTop (𝓝 0) := by
    simpa [mul_zero] using h_comp.const_mul ((2 : ℝ) ^ n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_upper
    (Eventually.of_forall fun k => mul_nonneg (pow_nonneg (Nat.cast_nonneg k) n) (hg.1 (k - 1))) ?_
  rw [Filter.eventually_atTop]
  refine ⟨2, fun k hk => ?_⟩
  have hk_le : (k : ℝ) ≤ 2 * ((k - 1 : ℕ) : ℝ) := by
    have : k ≤ 2 * (k - 1) := by omega
    exact_mod_cast this
  have h_pow : (k : ℝ) ^ n ≤ (2 * ((k - 1 : ℕ) : ℝ)) ^ n :=
    pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le n
  calc (k : ℝ) ^ n * g (k - 1)
    _ ≤ (2 * ((k - 1 : ℕ) : ℝ)) ^ n * g (k - 1) :=
      mul_le_mul_of_nonneg_right h_pow (hg.1 (k - 1))
    _ = (2 : ℝ) ^ n * (((k - 1 : ℕ) : ℝ) ^ n * g (k - 1)) := by rw [mul_pow, mul_assoc]

/-- Summability of `k ↦ (((2 * (linearExpansionRadius C (k + 2) + 1) : ℕ) : ℝ) ^ D) * f k`
    for any `IsSuperpolynomialDecay f` and `1 ≤ C`. -/
lemma summable_shell_volume_mul_of_isSuperpolynomialDecay (D : ℕ) (C : ℝ) (hC : 1 ≤ C)
    {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f) :
    Summable (fun k : ℕ =>
      f k * (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)) := by
  let B : ℝ := 2 * (3 * (C + 1) + 1)
  have h_base := (summable_pow_mul_of_isSuperpolynomialDecay hf D).mul_left (B ^ D)
  refine Summable.of_norm_bounded_eventually_nat h_base ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have h_nn :
      0 ≤ f k * (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D) :=
    mul_nonneg (hf.1 k) (pow_nonneg (Nat.cast_nonneg _) D)
  rw [Real.norm_of_nonneg h_nn]
  have hk2_ge1 : 1 ≤ k + bhmElementaryCubeSide := by dsimp [bhmElementaryCubeSide]; omega
  have h_rad := linearExpansionRadius_le_mul_bhm C hC hk2_ge1
  have hk2_le : ((k + bhmElementaryCubeSide : ℕ) : ℝ) ≤ 3 * (k : ℝ) := by
    dsimp [bhmElementaryCubeSide]
    have : k + 2 ≤ 3 * k := by omega
    exact_mod_cast this
  have h_le : ((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ≤
      B * (k : ℝ) := by
    dsimp [B]
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
    have hC_pos : 0 ≤ C + 1 := by linarith
    have h_rad' : (linearExpansionRadius C (k + bhmElementaryCubeSide) : ℝ) ≤
        (C + 1) * (3 * (k : ℝ)) :=
      le_trans h_rad (mul_le_mul_of_nonneg_left hk2_le hC_pos)
    push_cast
    nlinarith
  calc f k * (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)
    _ ≤ f k * ((B * (k : ℝ)) ^ D) := by
      apply mul_le_mul_of_nonneg_left _ (hf.1 k)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) h_le D
    _ = B ^ D * ((k : ℝ) ^ D * f k) := by rw [mul_pow]; ring

/-- Combined $k$-indexed shell decay profile
    `g_comb k = 3 * g_tail k + 3 * g_tail (k - 1) + 4 * k * g_tail k`. -/
def bhmShellCombinedDecay (g_tail : ℕ → ℝ) (k : ℕ) : ℝ :=
  bhmTelescopingFactor * g_tail k +
    bhmTelescopingFactor * g_tail (k - 1) +
    4 * ((k : ℝ) * g_tail k)

lemma isSuperpolynomialDecay_bhmShellCombinedDecay {g_tail : ℕ → ℝ}
    (hg : IsSuperpolynomialDecay g_tail) :
    IsSuperpolynomialDecay (bhmShellCombinedDecay g_tail) := by
  have h1 : IsSuperpolynomialDecay (fun k => bhmTelescopingFactor * g_tail k) :=
    isSuperpolynomialDecay_const_mul hg (by dsimp [bhmTelescopingFactor]; norm_num)
  have h2 : IsSuperpolynomialDecay (fun k => bhmTelescopingFactor * g_tail (k - 1)) :=
    isSuperpolynomialDecay_const_mul (isSuperpolynomialDecay_pred hg)
      (by dsimp [bhmTelescopingFactor]; norm_num)
  have h3 : IsSuperpolynomialDecay (fun k => 4 * ((k : ℝ) * g_tail k)) := by
    have h_pow1 := isSuperpolynomialDecay_mul_pow hg 1
    simpa [pow_one] using isSuperpolynomialDecay_const_mul h_pow1 (by norm_num : (0 : ℝ) ≤ 4)
  exact isSuperpolynomialDecay_add (isSuperpolynomialDecay_add h1 h2) h3

/-- $K$-independent upper bound for `bhmShellNormalizedMomentSum D C K m_0 g_tail`. -/
def bhmShellUniformMomentBound (D : ℕ) (C : ℝ) (m_0 : ℝ) (g_tail : ℕ → ℝ) : ℝ :=
  m_0 * (((2 * (linearExpansionRadius C (1 + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D) +
    ∑' k : ℕ,
      bhmShellCombinedDecay g_tail k *
        (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)

/-- For any `IsSuperpolynomialDecay g_tail`, $1 \le C$, and $m_0 \ge 0$,
    `bhmShellUniformMomentBound D C m_0 g_tail` is non-negative and bounds
    `bhmShellNormalizedMomentSum D C K m_0 g_tail` uniformly for all $K \ge 1$. -/
theorem bhmShellNormalizedMomentSum_le_uniform (D : ℕ) {C : ℝ} (hC : 1 ≤ C)
    {m_0 : ℝ} (hm0 : 0 ≤ m_0) {g_tail : ℕ → ℝ} (hg : IsSuperpolynomialDecay g_tail)
    {K : ℕ} (hK1 : 1 ≤ K) :
    0 ≤ bhmShellUniformMomentBound D C m_0 g_tail ∧
    bhmShellNormalizedMomentSum D C K m_0 g_tail ≤
      bhmShellUniformMomentBound D C m_0 g_tail := by
  let V_rad : ℕ → ℝ := fun k =>
    (((2 * (linearExpansionRadius C (k + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ^ D)
  have hV_nn : ∀ k : ℕ, 0 ≤ V_rad k := fun _ => by dsimp [V_rad]; positivity
  have hV_mono : ∀ {k₁ k₂ : ℕ}, k₁ ≤ k₂ → V_rad k₁ ≤ V_rad k₂ := by
    intro k₁ k₂ hk
    dsimp [V_rad]
    have h_rad : linearExpansionRadius C (k₁ + bhmElementaryCubeSide) ≤
        linearExpansionRadius C (k₂ + bhmElementaryCubeSide) :=
      linearExpansionRadius_mono (by linarith) (by omega)
    have h_le : ((2 * (linearExpansionRadius C (k₁ + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) ≤
        ((2 * (linearExpansionRadius C (k₂ + bhmElementaryCubeSide) + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega :
        2 * (linearExpansionRadius C (k₁ + bhmElementaryCubeSide) + 1) ≤
          2 * (linearExpansionRadius C (k₂ + bhmElementaryCubeSide) + 1))
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) h_le D
  have hg_comb := isSuperpolynomialDecay_bhmShellCombinedDecay hg
  have h_sum := summable_shell_volume_mul_of_isSuperpolynomialDecay D C hC hg_comb
  have h_term_nn : ∀ k : ℕ, 0 ≤ bhmShellCombinedDecay g_tail k * V_rad k :=
    fun k => mul_nonneg (hg_comb.1 k) (hV_nn k)
  have h_unif_nn : 0 ≤ bhmShellUniformMomentBound D C m_0 g_tail :=
    add_nonneg (mul_nonneg hm0 (hV_nn 1)) (tsum_nonneg h_term_nn)
  refine ⟨h_unif_nn, ?_⟩
  have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK1⟩
  have hK_mem : K ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hK1, le_rfl⟩
  have h_split_sum :
      bhmShellNormalizedMomentSum D C K m_0 g_tail ≤
      (∑ k ∈ Finset.Icc 1 K, (if k = 1 then m_0 * V_rad 1 else 0)) +
      (∑ k ∈ Finset.Icc 1 K,
        (bhmTelescopingFactor * g_tail k + bhmTelescopingFactor * g_tail (k - 1)) * V_rad k) +
      (∑ k ∈ Finset.Icc 1 K, 4 * g_tail K * V_rad K) := by
    unfold bhmShellNormalizedMomentSum
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    change ((bhmTelescopingFactor * g_tail k + 2 * g_tail K) +
        (if k = 1 then m_0 else bhmTelescopingFactor * g_tail (k - 1) + 2 * g_tail K)) * V_rad k ≤
      (if k = 1 then m_0 * V_rad 1 else 0) +
      (bhmTelescopingFactor * g_tail k + bhmTelescopingFactor * g_tail (k - 1)) * V_rad k +
      4 * g_tail K * V_rad K
    have hk_le_K : k ≤ K := (Finset.mem_Icc.mp hk).2
    have hVk_le : V_rad k ≤ V_rad K := hV_mono hk_le_K
    have hVk_nn : 0 ≤ V_rad k := hV_nn k
    have hgK_nn : 0 ≤ g_tail K := hg.1 K
    have hg_prev_nn : 0 ≤ bhmTelescopingFactor * g_tail (k - 1) :=
      mul_nonneg (by dsimp [bhmTelescopingFactor]; norm_num) (hg.1 (k - 1))
    have h_gK_V : g_tail K * V_rad k ≤ g_tail K * V_rad K :=
      mul_le_mul_of_nonneg_left hVk_le hgK_nn
    by_cases hk_eq1 : k = 1
    · subst hk_eq1
      simp only [ ↓reduceIte ]
      nlinarith
    · rw [if_neg hk_eq1, if_neg hk_eq1]
      nlinarith
  have h_part1 : (∑ k ∈ Finset.Icc 1 K, (if k = 1 then m_0 * V_rad 1 else 0)) = m_0 * V_rad 1 := by
    rw [Finset.sum_ite_eq' (Finset.Icc 1 K) 1 (fun _ => m_0 * V_rad 1), if_pos h1_mem]
  have h_part3 :
      (∑ _k ∈ Finset.Icc 1 K, 4 * g_tail K * V_rad K) ≤
      ∑ k ∈ Finset.Icc 1 K, (4 * ((k : ℝ) * g_tail k)) * V_rad k := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have h_card_eq : ((K + 1 - 1 : ℕ) : ℝ) = (K : ℝ) := by simp
    rw [h_card_eq]
    have h_single :
        (4 * ((K : ℝ) * g_tail K)) * V_rad K ≤
        ∑ k ∈ Finset.Icc 1 K, (4 * ((k : ℝ) * g_tail k)) * V_rad k :=
      Finset.single_le_sum
        (fun k _ => mul_nonneg (mul_nonneg (by norm_num)
          (mul_nonneg (Nat.cast_nonneg k) (hg.1 k))) (hV_nn k))
        hK_mem
    linarith
  have h_part23 :
      (∑ k ∈ Finset.Icc 1 K,
        (bhmTelescopingFactor * g_tail k + bhmTelescopingFactor * g_tail (k - 1)) * V_rad k) +
      (∑ k ∈ Finset.Icc 1 K, (4 * ((k : ℝ) * g_tail k)) * V_rad k) =
      ∑ k ∈ Finset.Icc 1 K, bhmShellCombinedDecay g_tail k * V_rad k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp [bhmShellCombinedDecay]
    ring
  have h_fin_le_tsum :
      (∑ k ∈ Finset.Icc 1 K, bhmShellCombinedDecay g_tail k * V_rad k) ≤
      ∑' k : ℕ, bhmShellCombinedDecay g_tail k * V_rad k :=
    h_sum.sum_le_tsum (Finset.Icc 1 K) (fun k _ => h_term_nn k)
  unfold bhmShellUniformMomentBound
  change bhmShellNormalizedMomentSum D C K m_0 g_tail ≤
    m_0 * V_rad 1 + ∑' k : ℕ, bhmShellCombinedDecay g_tail k * V_rad k
  linarith

/-! ## 5. $J$-Proportional LR and Remainder Splitting Calibration & Superpolynomial Envelope -/

/-- If `0 ≤ ε_LR ≤ J * c_LR`, `ε_tail K ≤ J * g_tail K`, and `0 ≤ J ≤ J_0` ($c_{\mathrm{LR}} \ge 0$,
    $g_{\mathrm{tail}}(K) \ge 0$), then `4 * (J_0 * c_LR) ^ 2 ≤ δ_split` and
    `2 * ((L : ℝ) ^ D * (5 * (J_0 * g_tail K))) ≤ δ_split` imply both
    `4 * ε_LR ^ 2 ≤ δ_split` and `2 * ((Fintype.card (BoxD D L) : ℝ) * (5 * ε_tail K)) ≤ δ_split`. -/
theorem lr_and_rem_split_le_of_J_proportional {D L K : ℕ}
    {J J_0 ε_LR c_LR δ_split : ℝ} {ε_tail g_tail : ℕ → ℝ}
    (_hJ_nn : 0 ≤ J) (hJ_le : J ≤ J_0)
    (hε_LR_nn : 0 ≤ ε_LR) (hc_LR_nn : 0 ≤ c_LR) (hε_LR : ε_LR ≤ J * c_LR)
    (hgK_nn : 0 ≤ g_tail K) (hε_K : ε_tail K ≤ J * g_tail K)
    (h_LR_J0 : 4 * (J_0 * c_LR) ^ 2 ≤ δ_split)
    (h_rem_J0 : 2 * ((L : ℝ) ^ D * (5 * (J_0 * g_tail K))) ≤ δ_split) :
    4 * ε_LR ^ 2 ≤ δ_split ∧
    2 * ((Fintype.card (BoxD D L) : ℝ) * (5 * ε_tail K)) ≤ δ_split := by
  have hε_LR_J0 : ε_LR ≤ J_0 * c_LR :=
    le_trans hε_LR (mul_le_mul_of_nonneg_right hJ_le hc_LR_nn)
  have h_sq : ε_LR ^ 2 ≤ (J_0 * c_LR) ^ 2 :=
    pow_le_pow_left₀ hε_LR_nn hε_LR_J0 2
  have h1 : 4 * ε_LR ^ 2 ≤ δ_split := by linarith
  have hε_K_J0 : ε_tail K ≤ J_0 * g_tail K :=
    le_trans hε_K (mul_le_mul_of_nonneg_right hJ_le hgK_nn)
  have h_card : (Fintype.card (BoxD D L) : ℝ) = (L : ℝ) ^ D := by
    have hc : Fintype.card (BoxD D L) = L ^ D := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    exact_mod_cast hc
  have h_L_nn : 0 ≤ (L : ℝ) ^ D := by positivity
  have h2 : 2 * ((Fintype.card (BoxD D L) : ℝ) * (5 * ε_tail K)) ≤ δ_split := by
    rw [h_card]
    have h_mul : (L : ℝ) ^ D * (5 * ε_tail K) ≤ (L : ℝ) ^ D * (5 * (J_0 * g_tail K)) :=
      mul_le_mul_of_nonneg_left (by linarith) h_L_nn
    linarith
  exact ⟨h1, h2⟩

/-- Pointwise multiplication closure of `IsSuperpolynomialDecay`: if $f_1, f_2 \in \mathcal{D}_{\mathrm{super}}$,
    then $r \mapsto f_1(r) f_2(r)$ belongs to $\mathcal{D}_{\mathrm{super}}$. -/
lemma isSuperpolynomialDecay_mul {f₁ f₂ : ℕ → ℝ}
    (hf₁ : IsSuperpolynomialDecay f₁) (hf₂ : IsSuperpolynomialDecay f₂) :
    IsSuperpolynomialDecay (fun r => f₁ r * f₂ r) := by
  refine ⟨fun r => mul_nonneg (hf₁.1 r) (hf₂.1 r), fun n => ?_⟩
  have h_eq : (fun r : ℕ => (r : ℝ) ^ n * (f₁ r * f₂ r)) =
      (fun r : ℕ => ((r : ℝ) ^ n * f₁ r) * ((r : ℝ) ^ 0 * f₂ r)) := by
    ext r; simp [pow_zero]; ring
  rw [h_eq]
  simpa using (hf₁.2 n).mul (hf₂.2 0)

/--Canonical superpolynomial splitting envelope for $K(L) = \lfloor c_K L \rfloor_+$ and
    $r_{\mathrm{LR}}(L) = \lfloor c_{\mathrm{LR}} L \rfloor_+$. -/
def bhmMultiScaleSplittingEnvelope (D : ℕ) (J_0 c_K c_LR : ℝ)
    (g_tail g_LR : ℕ → ℝ) (L : ℕ) : ℝ :=
  max (4 * (J_0 * g_LR ⌊c_LR * (L : ℝ)⌋₊) ^ 2)
      (2 * ((L : ℝ) ^ D * (5 * (J_0 * g_tail ⌊c_K * (L : ℝ)⌋₊))))

/-- `bhmMultiScaleSplittingEnvelope` belongs to `IsSuperpolynomialDecay` whenever $J_0 \ge 0$,
    $c_K > 0$, $c_{\mathrm{LR}} > 0$, and $g_{\mathrm{tail}}, g_{\mathrm{LR}} \in \mathcal{D}_{\mathrm{super}}$. -/
theorem isSuperpolynomialDecay_bhmMultiScaleSplittingEnvelope
    (D : ℕ) {J_0 c_K c_LR : ℝ} (hJ0 : 0 ≤ J_0) (hc_K : 0 < c_K) (hc_LR : 0 < c_LR)
    {g_tail g_LR : ℕ → ℝ} (hg_tail : IsSuperpolynomialDecay g_tail)
    (hg_LR : IsSuperpolynomialDecay g_LR) :
    IsSuperpolynomialDecay (bhmMultiScaleSplittingEnvelope D J_0 c_K c_LR g_tail g_LR) := by
  have h_lr_scaled : IsSuperpolynomialDecay (fun L => J_0 * g_LR ⌊c_LR * (L : ℝ)⌋₊) :=
    isSuperpolynomialDecay_const_mul (isSuperpolynomialDecay_floor_mul hg_LR hc_LR) hJ0
  have h_lr_sq : IsSuperpolynomialDecay (fun L => 4 * (J_0 * g_LR ⌊c_LR * (L : ℝ)⌋₊) ^ 2) := by
    have h_mul := isSuperpolynomialDecay_mul h_lr_scaled h_lr_scaled
    have h_eq : (fun L : ℕ => 4 * (J_0 * g_LR ⌊c_LR * (L : ℝ)⌋₊) ^ 2) =
        (fun L : ℕ => 4 * ((J_0 * g_LR ⌊c_LR * (L : ℝ)⌋₊) * (J_0 * g_LR ⌊c_LR * (L : ℝ)⌋₊))) := by
      ext L; ring
    rw [h_eq]
    exact isSuperpolynomialDecay_const_mul h_mul (by norm_num)
  have h_rem_scaled :
      IsSuperpolynomialDecay (fun L => 2 * ((L : ℝ) ^ D * (5 * (J_0 * g_tail ⌊c_K * (L : ℝ)⌋₊)))) := by
    have h_fl := isSuperpolynomialDecay_floor_mul hg_tail hc_K
    have h_pow := isSuperpolynomialDecay_mul_pow h_fl D
    have h_c := isSuperpolynomialDecay_const_mul h_pow (by positivity : 0 ≤ 10 * J_0)
    have h_eq : (fun L : ℕ => 2 * ((L : ℝ) ^ D * (5 * (J_0 * g_tail ⌊c_K * (L : ℝ)⌋₊)))) =
        (fun L : ℕ => (10 * J_0) * ((L : ℝ) ^ D * g_tail ⌊c_K * (L : ℝ)⌋₊)) := by
      ext L; ring
    rwa [h_eq]
  exact isSuperpolynomialDecay_max h_lr_sq h_rem_scaled

end
