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

import Proofs.SpacetimeWorldlineKP.PauliDiagRCACoercivity

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SpacetimeWorldlineKP

/-!
# Periodic Euclidean Worldline Expansion, Penrose Tree Inequality, and Simplex Volumes

Discretizes the periodic thermal circle (`thermalTimeSliceCount`) and bounds Euclidean worldline slice products (`norm_worldline_slice_product_le_exp_integral`) and ordered Dyson simplex volumes (`KPOrderedDysonSimplex`, `volume_kpOrderedDysonSimplex_le`). Formalizes connected-subgraph walk bounds (`KPIsConnectedSubgraph`) and Penrose's tree-partition identity (`PenroseAdj`, `abs_sum_connGraphs_le_arborescenceForests`) for repulsive Mayer graphs.

## References

* Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.3 (`lem:klarner-bound`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
* Kotecký–Preiss (1986), Cluster expansion for abstract polymer models
-/

/-! ## 1. Time-Slice Step Calibration, Semigroup Factorization & Propagator Sector Norm Bound -/

/-- **Thermal Imaginary-Time Slice Count (`thermalTimeSliceCount`)**:
    Slices $[0, \beta]$ into $M = \max(1, \lceil \beta \rceil)$ equal intervals so that each
    slice has duration $\tau_0 = \beta / M \in (0, 1]$ uniformly for all $\beta > 0$. -/
def thermalTimeSliceCount (β : ℝ) : ℕ :=
  max 1 ⌈β⌉₊

/-- **Thermal Imaginary-Time Slice Step (`thermalTimeSliceStep`)**:
    The single-slice Euclidean step $\tau_0 = \beta / (\mathrm{thermalTimeSliceCount}\;\beta : \mathbb{R})$. -/
def thermalTimeSliceStep (β : ℝ) : ℝ :=
  β / (thermalTimeSliceCount β : ℝ)

/-- **Uniform Time-Slice Step Bounds (`thermalTimeSliceCount_pos_and_step_bounds`)**:
    For every $\beta > 0$, $M = \mathrm{thermalTimeSliceCount}\;\beta \ge 1$,
    $M \cdot \mathrm{thermalTimeSliceStep}\;\beta = \beta$, and
    $0 < \mathrm{thermalTimeSliceStep}\;\beta \le 1$. -/
theorem thermalTimeSliceCount_pos_and_step_bounds {β : ℝ} (hβ_pos : 0 < β) :
    1 ≤ thermalTimeSliceCount β ∧
    0 < (thermalTimeSliceCount β : ℝ) ∧
    (thermalTimeSliceCount β : ℝ) * thermalTimeSliceStep β = β ∧
    0 < thermalTimeSliceStep β ∧
    thermalTimeSliceStep β ≤ 1 := by
  have hM_ge : 1 ≤ thermalTimeSliceCount β := le_max_left 1 ⌈β⌉₊
  have hM_pos : (0 : ℝ) < (thermalTimeSliceCount β : ℝ) := by
    have h1 : (1 : ℝ) ≤ (thermalTimeSliceCount β : ℝ) := by exact_mod_cast hM_ge
    linarith
  have h_mul : (thermalTimeSliceCount β : ℝ) * thermalTimeSliceStep β = β := by
    unfold thermalTimeSliceStep
    exact mul_div_cancel₀ β (ne_of_gt hM_pos)
  have h_step_pos : 0 < thermalTimeSliceStep β := by
    unfold thermalTimeSliceStep
    exact div_pos hβ_pos hM_pos
  have h_beta_le_M : β ≤ (thermalTimeSliceCount β : ℝ) := by
    have h_ceil : β ≤ (⌈β⌉₊ : ℝ) := Nat.le_ceil β
    have h_max : (⌈β⌉₊ : ℝ) ≤ (thermalTimeSliceCount β : ℝ) := by
      unfold thermalTimeSliceCount
      exact_mod_cast le_max_right 1 ⌈β⌉₊
    exact le_trans h_ceil h_max
  have h_step_le_one : thermalTimeSliceStep β ≤ 1 := by
    unfold thermalTimeSliceStep
    rw [div_le_iff₀ hM_pos, one_mul]
    exact h_beta_le_M
  exact ⟨hM_ge, hM_pos, h_mul, h_step_pos, h_step_le_one⟩

/-- **Zero-Time Identity of `gibbsBoltzmannOp` (`gibbsBoltzmannOp_zero_eq_one`)**:
    On the complete orthonormal eigenbasis of any self-adjoint operator $H$,
    $B_H(0) = 1$. -/
theorem gibbsBoltzmannOp_zero_eq_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) :
    gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) 0 = 1 := by
  unfold gibbsBoltzmannOp
  have h_exp : ∀ ω : ManyBodyConfig Site, Real.exp (-0 * opEigenvalues H hH ω) = 1 := fun ω => by
    rw [neg_zero, zero_mul, Real.exp_zero]
  simp_rw [h_exp, Complex.ofReal_one, one_smul]
  exact onb_sum_ketBra_eq_one (opEigenbasis H hH)
    (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)

/-- **Euclidean Semigroup Factorization of `gibbsBoltzmannOp`
    (`gibbsBoltzmannOp_add_eq_mul`)**:
    For any self-adjoint operator $H$ and imaginary times $t_1, t_2 \in \mathbb{R}$,
    $B_H(t_1 + t_2) = B_H(t_1) * B_H(t_2)$. -/
theorem gibbsBoltzmannOp_add_eq_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (t₁ t₂ : ℝ) :
    gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) (t₁ + t₂) =
      gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) t₁ *
        gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) t₂ := by
  symm
  unfold gibbsBoltzmannOp
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω₁ _ => ?_
  rw [Finset.mul_sum, Finset.sum_eq_single ω₁]
  · rw [clm_smul_mul, clm_mul_smul, clm_smul_smul,
      onb_ketBra_mul_ketBra (opEigenbasis H hH) (opEigenbasis_orthonormal H hH) ω₁ ω₁,
      if_pos rfl, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  · intro ω₂ _ hne
    rw [clm_smul_mul, clm_mul_smul, clm_smul_smul,
      onb_ketBra_mul_ketBra (opEigenbasis H hH) (opEigenbasis_orthonormal H hH) ω₁ ω₂,
      if_neg (Ne.symm hne), smul_zero]
  · intro h_not
    exact False.elim (h_not (Finset.mem_univ ω₁))

/-- **Integer-Multiple Power Factorization of `gibbsBoltzmannOp`
    (`gibbsBoltzmannOp_nat_mul_eq_pow`)**:
    For every $n \in \mathbb{N}$ and step $\tau \in \mathbb{R}$,
    $B_H(n \cdot \tau) = (B_H(\tau))^n$. -/
theorem gibbsBoltzmannOp_nat_mul_eq_pow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (n : ℕ) (τ : ℝ) :
    gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) ((n : ℝ) * τ) =
      (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) τ) ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul, pow_zero, gibbsBoltzmannOp_zero_eq_one H hH]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, gibbsBoltzmannOp_add_eq_mul H hH ((n : ℝ) * τ) τ,
      ih, pow_succ]

/-- **Thermal Time-Slice Power Factorization of `gibbsBoltzmannOp`
    (`gibbsBoltzmannOp_eq_pow_thermalTimeSliceStep`)**:
    For every $\beta > 0$, with $M = \mathrm{thermalTimeSliceCount}\;\beta$ and
    $\tau_0 = \mathrm{thermalTimeSliceStep}\;\beta$,
    $B_H(\beta) = (B_H(\tau_0))^M$. -/
theorem gibbsBoltzmannOp_eq_pow_thermalTimeSliceStep {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) {β : ℝ} (hβ_pos : 0 < β) :
    gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β =
      (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH)
        (thermalTimeSliceStep β)) ^ (thermalTimeSliceCount β) := by
  have h_mul := (thermalTimeSliceCount_pos_and_step_bounds hβ_pos).2.2.1
  conv_lhs => rw [← h_mul]
  exact gibbsBoltzmannOp_nat_mul_eq_pow H hH (thermalTimeSliceCount β) (thermalTimeSliceStep β)

/-- **Syndrome-Sector Euclidean Propagator Damping Bound
    (`norm_gibbsBoltzmannOp_mul_syndromeProjector_le_of_coercivity`)**:
    If $H_{\mathrm{diag}}$ is self-adjoint, commutes with $\Pi_\sigma = \mathrm{sys.syndromeProjector}\;\sigma$,
    and satisfies the lower form bound
    $\frac{3}{4} E_0(\sigma) \|\Pi_\sigma \psi\|^2 \le \operatorname{Re}\langle \Pi_\sigma \psi, H_{\mathrm{diag}}(\Pi_\sigma \psi)\rangle$
    for all $\psi$, then for every Euclidean time slice $s \ge 0$,
    $$\|\mathrm{gibbsBoltzmannOp}\;(\mathrm{opEigenbasis}\;H_{\mathrm{diag}}\;hH_{\mathrm{diag}})\;(\mathrm{opEigenvalues}\;H_{\mathrm{diag}}\;hH_{\mathrm{diag}})\;s * \Pi_\sigma\|
      \le \exp\bigl(-\tfrac{3}{4} s \, \mathrm{sys.syndromeEnergy}\;\sigma\bigr).$$ -/
theorem norm_gibbsBoltzmannOp_mul_syndromeProjector_le_of_coercivity {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag)
    (σ : ι → Bool)
    (h_comm : Commute H_diag (sys.syndromeProjector σ))
    (h_lower : ∀ ψ : ManyBodyHilbertSpace Site,
      (3 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2 ≤
        RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))))
    {s : ℝ} (hs : 0 ≤ s) :
    ‖gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) s *
        sys.syndromeProjector σ‖ ≤
      Real.exp (-(3 / 4 : ℝ) * s * sys.syndromeEnergy σ) := by
  let ψ_eig := opEigenbasis H_diag hH_diag
  let E_eig := opEigenvalues H_diag hH_diag
  let P := sys.syndromeProjector σ
  let C := Real.exp (-(3 / 4 : ℝ) * s * sys.syndromeEnergy σ)
  have hC_nonneg : 0 ≤ C := le_of_lt (Real.exp_pos _)
  have hP : IsStarProjection P := (syndrome_resolution_indexed sys).2.1 σ
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  have h_inner_boltz : ∀ (ω : ManyBodyConfig Site) (ψ : ManyBodyHilbertSpace Site),
      inner ℂ (ψ_eig ω) (gibbsBoltzmannOp ψ_eig E_eig s ψ) =
        (Real.exp (-s * E_eig ω) : ℂ) * inner ℂ (ψ_eig ω) ψ := by
    intro ω ψ
    unfold gibbsBoltzmannOp
    rw [ContinuousLinearMap.sum_apply, inner_sum, Finset.sum_eq_single ω]
    · rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
        inner_smul_right, opEigenbasis_orthonormal H_diag hH_diag ω ω, if_pos rfl, mul_one]
    · intro ω' _ hne
      rw [ContinuousLinearMap.smul_apply, rankOneKetBra_apply, inner_smul_right,
        inner_smul_right, opEigenbasis_orthonormal H_diag hH_diag ω ω',
        if_neg (Ne.symm hne), mul_zero, mul_zero]
    · intro h_not
      exact False.elim (h_not (Finset.mem_univ ω))
  apply ContinuousLinearMap.opNorm_le_bound _ hC_nonneg
  intro φ
  have h_term_le : ∀ ω : ManyBodyConfig Site,
      ‖inner ℂ (ψ_eig ω) ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)‖ ^ 2 ≤
        C ^ 2 * ‖inner ℂ (ψ_eig ω) (P φ)‖ ^ 2 := by
    intro ω
    have h_norm_eq :
        ‖inner ℂ (ψ_eig ω) ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)‖ =
          Real.exp (-s * E_eig ω) * ‖inner ℂ (ψ_eig ω) (P φ)‖ := by
      change ‖inner ℂ (ψ_eig ω) (gibbsBoltzmannOp ψ_eig E_eig s (P φ))‖ = _
      rw [h_inner_boltz ω (P φ), norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
    have h_lin_le :
        Real.exp (-s * E_eig ω) * ‖inner ℂ (ψ_eig ω) (P φ)‖ ≤
          C * ‖inner ℂ (ψ_eig ω) (P φ)‖ := by
      by_cases h_zero : ‖P (ψ_eig ω)‖ = 0
      · have hP_zero : P (ψ_eig ω) = 0 := norm_eq_zero.mp h_zero
        have h_in_zero : inner ℂ (ψ_eig ω) (P φ) = 0 := by
          rw [← ContinuousLinearMap.adjoint_inner_left, hP_adj, hP_zero, inner_zero_left]
        rw [h_in_zero, norm_zero, mul_zero, mul_zero]
      · have h_sq_pos : 0 < ‖P (ψ_eig ω)‖ ^ 2 := sq_pos_of_ne_zero h_zero
        have h_quad := (commute_opEigenbasis_quadForm_eq H_diag P hH_diag hP h_comm ω).2.1
        have h_low := h_lower (ψ_eig ω)
        change (3 / 4 : ℝ) * sys.syndromeEnergy σ * ‖P (ψ_eig ω)‖ ^ 2 ≤
          RCLike.re (inner ℂ (P (ψ_eig ω)) (H_diag (P (ψ_eig ω)))) at h_low
        rw [h_quad] at h_low
        have hE_ge : (3 / 4 : ℝ) * sys.syndromeEnergy σ ≤ E_eig ω :=
          le_of_mul_le_mul_right h_low h_sq_pos
        have h_exp_le : Real.exp (-s * E_eig ω) ≤ C := by
          apply Real.exp_le_exp.mpr
          nlinarith
        exact mul_le_mul_of_nonneg_right h_exp_le (norm_nonneg _)
    rw [h_norm_eq]
    have h_lhs_nn : 0 ≤ Real.exp (-s * E_eig ω) * ‖inner ℂ (ψ_eig ω) (P φ)‖ :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (norm_nonneg _)
    nlinarith
  have h_sq_le :
      ‖(gibbsBoltzmannOp ψ_eig E_eig s * P) φ‖ ^ 2 ≤ (C * ‖φ‖) ^ 2 := by
    calc ‖(gibbsBoltzmannOp ψ_eig E_eig s * P) φ‖ ^ 2
      _ = ∑ ω : ManyBodyConfig Site,
            ‖inner ℂ (ψ_eig ω) ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)‖ ^ 2 :=
        (opEigenbasis_parseval H_diag hH_diag _).symm
      _ ≤ ∑ ω : ManyBodyConfig Site, C ^ 2 * ‖inner ℂ (ψ_eig ω) (P φ)‖ ^ 2 :=
        Finset.sum_le_sum fun ω _ => h_term_le ω
      _ = C ^ 2 * ∑ ω : ManyBodyConfig Site, ‖inner ℂ (ψ_eig ω) (P φ)‖ ^ 2 := by
        rw [← Finset.mul_sum]
      _ = C ^ 2 * ‖P φ‖ ^ 2 := by
        rw [opEigenbasis_parseval H_diag hH_diag (P φ)]
      _ ≤ C ^ 2 * ‖φ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (isStarProjection_norm_sq_apply_le hP φ) (sq_nonneg C)
      _ = (C * ‖φ‖) ^ 2 := by ring
  have h_rhs_nn : 0 ≤ C * ‖φ‖ := mul_nonneg hC_nonneg (norm_nonneg φ)
  nlinarith [norm_nonneg ((gibbsBoltzmannOp ψ_eig E_eig s * P) φ)]

/-- **Multi-Slice Euclidean Worldline Propagator Product (`worldlineSliceProduct`)**:
    Given slice durations $s_0, \dots, s_m$, syndrome sequence $\sigma_0, \dots, \sigma_m$,
    and jump operators $K_0, \dots, K_{m-1}$, recursively forms the time-ordered product
    $$(e^{-s_0 H_{\mathrm{diag}}} \Pi_{\sigma_0}) K_0 (e^{-s_1 H_{\mathrm{diag}}} \Pi_{\sigma_1}) \cdots K_{m-1} (e^{-s_m H_{\mathrm{diag}}} \Pi_{\sigma_m}).$$ -/
def worldlineSliceProduct {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) :
    {m : ℕ} → (Fin (m + 1) → ℝ) → (Fin (m + 1) → (ι → Bool)) →
      (Fin m → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) →
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  | 0, s, σ, _ =>
      gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) (s 0) *
        sys.syndromeProjector (σ 0)
  | _ + 1, s, σ, K =>
      (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) (s 0) *
        sys.syndromeProjector (σ 0)) * K 0 *
        worldlineSliceProduct sys H_diag hH_diag
          (fun r => s r.succ) (fun r => σ r.succ) (fun r => K r.succ)

/-- **Multi-Slice Euclidean Worldline Propagator Product Bound
    (`norm_worldline_slice_product_le_exp_integral`)**:
    Along any $m$-step imaginary-time jump sequence with slice durations $s_0, \dots, s_m \ge 0$,
    syndrome sequence $\sigma_0, \dots, \sigma_m$, and jump operators $K_1, \dots, K_m$,
    the operator norm of the time-ordered worldline product
    `worldlineSliceProduct sys H_diag hH_diag s σ K` is bounded by
    $$\Bigl(\prod_{r=1}^m \|K_r\|\Bigr)
      \exp\Bigl(-\tfrac{3}{4} \sum_{r=0}^m s_r \, \mathrm{sys.syndromeEnergy}(\sigma_r)\Bigr).$$ -/
theorem norm_worldline_slice_product_le_exp_integral {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag)
    (h_comm : ∀ σ : ι → Bool, Commute H_diag (sys.syndromeProjector σ))
    (h_lower : ∀ (σ : ι → Bool) (ψ : ManyBodyHilbertSpace Site),
      (3 / 4 : ℝ) * sys.syndromeEnergy σ * ‖sys.syndromeProjector σ ψ‖ ^ 2 ≤
        RCLike.re (inner ℂ (sys.syndromeProjector σ ψ) (H_diag (sys.syndromeProjector σ ψ))))
    {m : ℕ}
    (s : Fin (m + 1) → ℝ) (hs : ∀ r, 0 ≤ s r)
    (σ : Fin (m + 1) → (ι → Bool))
    (K : Fin m → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    ‖worldlineSliceProduct sys H_diag hH_diag s σ K‖ ≤
      (∏ r : Fin m, ‖K r‖) *
        Real.exp (-(3 / 4 : ℝ) * ∑ r : Fin (m + 1), s r * sys.syndromeEnergy (σ r)) := by
  induction m with
  | zero =>
    dsimp [worldlineSliceProduct]
    rw [Fin.prod_univ_zero, one_mul, Fin.sum_univ_one]
    have h0 := norm_gibbsBoltzmannOp_mul_syndromeProjector_le_of_coercivity
      sys H_diag hH_diag (σ 0) (h_comm (σ 0)) (h_lower (σ 0)) (hs 0)
    have h_arg : -(3 / 4 : ℝ) * s 0 * sys.syndromeEnergy (σ 0) =
        -(3 / 4 : ℝ) * (s 0 * sys.syndromeEnergy (σ 0)) := by ring
    rwa [h_arg] at h0
  | succ m ih =>
    dsimp [worldlineSliceProduct]
    let A0 := gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) (s 0) *
      sys.syndromeProjector (σ 0)
    let Rest := worldlineSliceProduct sys H_diag hH_diag
      (fun r => s r.succ) (fun r => σ r.succ) (fun r => K r.succ)
    have hA0 : ‖A0‖ ≤ Real.exp (-(3 / 4 : ℝ) * s 0 * sys.syndromeEnergy (σ 0)) :=
      norm_gibbsBoltzmannOp_mul_syndromeProjector_le_of_coercivity
        sys H_diag hH_diag (σ 0) (h_comm (σ 0)) (h_lower (σ 0)) (hs 0)
    have hRest : ‖Rest‖ ≤
        (∏ r : Fin m, ‖K r.succ‖) *
          Real.exp (-(3 / 4 : ℝ) * ∑ r : Fin (m + 1), s r.succ * sys.syndromeEnergy (σ r.succ)) :=
      ih (fun r => s r.succ) (fun r => hs r.succ) (fun r => σ r.succ) (fun r => K r.succ)
    have h_step1 : ‖A0 * K 0 * Rest‖ ≤ ‖A0‖ * ‖K 0‖ * ‖Rest‖ :=
      le_trans (norm_mul_le (A0 * K 0) Rest)
        (mul_le_mul_of_nonneg_right (norm_mul_le A0 (K 0)) (norm_nonneg Rest))
    have h_step2 :
        ‖A0‖ * ‖K 0‖ * ‖Rest‖ ≤
          (Real.exp (-(3 / 4 : ℝ) * s 0 * sys.syndromeEnergy (σ 0)) * ‖K 0‖) *
            ((∏ r : Fin m, ‖K r.succ‖) *
              Real.exp (-(3 / 4 : ℝ) * ∑ r : Fin (m + 1), s r.succ * sys.syndromeEnergy (σ r.succ))) := by
      refine mul_le_mul
        (mul_le_mul_of_nonneg_right hA0 (norm_nonneg (K 0)))
        hRest
        (norm_nonneg Rest)
        (mul_nonneg (le_of_lt (Real.exp_pos _)) (norm_nonneg (K 0)))
    have h_rhs_eq :
        (Real.exp (-(3 / 4 : ℝ) * s 0 * sys.syndromeEnergy (σ 0)) * ‖K 0‖) *
          ((∏ r : Fin m, ‖K r.succ‖) *
            Real.exp (-(3 / 4 : ℝ) * ∑ r : Fin (m + 1), s r.succ * sys.syndromeEnergy (σ r.succ))) =
        (∏ r : Fin (m + 1), ‖K r‖) *
          Real.exp (-(3 / 4 : ℝ) * ∑ r : Fin (m + 1 + 1), s r * sys.syndromeEnergy (σ r)) := by
      have h_prod : (∏ r : Fin (m + 1), ‖K r‖) = ‖K 0‖ * ∏ r : Fin m, ‖K r.succ‖ :=
        Fin.prod_univ_succ _
      have h_sum :
          (∑ r : Fin (m + 1 + 1), s r * sys.syndromeEnergy (σ r)) =
          s 0 * sys.syndromeEnergy (σ 0) +
            ∑ x : Fin (m + 1), s x.succ * sys.syndromeEnergy (σ x.succ) :=
        Fin.sum_univ_succ _
      rw [h_prod, h_sum]
      have h_exp :
          Real.exp (-(3 / 4 : ℝ) * (s 0 * sys.syndromeEnergy (σ 0) +
            ∑ x : Fin (m + 1), s x.succ * sys.syndromeEnergy (σ x.succ))) =
          Real.exp (-(3 / 4 : ℝ) * s 0 * sys.syndromeEnergy (σ 0)) *
            Real.exp (-(3 / 4 : ℝ) * ∑ x : Fin (m + 1), s x.succ * sys.syndromeEnergy (σ x.succ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h_exp]
      ring
    exact le_trans h_step1 (h_rhs_eq ▸ h_step2)

/-! ## 2. Space-Time Polymer Representation of Witness Gibbs Ratio -/

/-- **Space-Time Polymer Majorant Representation for Witness Gibbs Probability
    (`HasPolymerWitnessMajorant`, Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`))**:
    Captures that for a given witness $W \subseteq \iota$, the witness Gibbs probability
    $\mathrm{gibbsFailureProb}(H, hH, \beta, \Pi_W)$ is bounded above by the pinned polymer ratio
    $\sum_{\gamma \in \mathcal{P}_W} |\widetilde{w}(\gamma)| \exp(\sum_{\gamma' \not\sim \gamma} a(\gamma'))$,
    controlled via `polymerPinnedSum` and `polymerPartitionZ` on a finite space-time polymer type
    `Polymer`. -/
def HasPolymerWitnessMajorant {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    {Polymer : Type} [Fintype Polymer] [DecidableEq Polymer]
    (compat : Polymer → Polymer → Prop)
    (w a d : Polymer → ℝ)
    (W : Finset ι) (PinnedW : Finset Polymer) : Prop :=
  SatisfiesKoteckyPreissCondition compat w a d ∧
  gibbsFailureProb H hH β (positiveCheckWitnessProj sys W) ≤
    ∑ γ ∈ PinnedW, w γ * Real.exp (∑ γ' ∈ Finset.univ.filter (fun γ' => ¬compat γ γ'), a γ')

/-! ## 3. Collar-Block Canonical Witness Anchor Cubes & 1-Step Worldline Helpers -/

/-- **Nonempty Spatial Support of Every Static CSS Check (`staticCSSCheckSupport_nonempty`)** -/
theorem staticCSSCheckSupport_nonempty {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (idx : StaticCSSCheckIdx L q_code m_max) : (sys.support idx).Nonempty := by
  rw [(h_sys_checks idx).2.1]
  rcases idx with ⟨v, _⟩ | ⟨v, _⟩ | ⟨v, _⟩
  · exact ⟨v, Finset.mem_singleton_self v⟩
  · exact ⟨v, mem_boxBall_self v r_0⟩
  · exact ⟨v, mem_boxBall_self v r_0⟩

/-- **Collar Block Site Capacity (`collarBlockSiteCapacity`)**:
    Number of check-support anchor sites $(2(R_{\mathrm{pert}} + 2 r_{\mathrm{rca}} + r_0) + 1)^3$
    grouped into each step $j : \mathrm{Fin}\;m$ of `canonicalWitnessAnchorCubes`. -/
def collarBlockSiteCapacity (R_pert r_0 : ℕ) (C_rca : ℝ) : ℕ :=
  (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3

/-- **Canonical Witness Anchor Cubes (`canonicalWitnessAnchorCubes`)**:
    For each order $m \in \mathbb{N}$ and step index $j : \mathrm{Fin}\;m$, selects one site from the
    spatial support of each check in the $j$-th block of size `collarBlockSiteCapacity R_pert r_0 C_rca` of `W.toList`. -/
def canonicalWitnessAnchorCubes {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (R_pert r_0 : ℕ) (C_rca : ℝ) (W : Finset ι) (m : ℕ) (j : Fin m) : Finset (BoxD D L) :=
  let K_collar := collarBlockSiteCapacity R_pert r_0 C_rca
  (Finset.range K_collar).biUnion fun t =>
    if h : j.val * K_collar + t < W.toList.length then
      let c := W.toList.get ⟨j.val * K_collar + t, h⟩
      if h_supp : (sys.support c).Nonempty then {h_supp.choose} else ∅
    else ∅

/-- **Block Site-Cardinality Bound of `canonicalWitnessAnchorCubes` (`card_canonicalWitnessAnchorCubes_le`)** -/
theorem card_canonicalWitnessAnchorCubes_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (R_pert r_0 : ℕ) (C_rca : ℝ) (W : Finset ι) (m : ℕ) (j : Fin m) :
    (canonicalWitnessAnchorCubes sys R_pert r_0 C_rca W m j).card ≤
      collarBlockSiteCapacity R_pert r_0 C_rca := by
  unfold canonicalWitnessAnchorCubes
  refine le_trans Finset.card_biUnion_le ?_
  have h_le_one : ∀ t ∈ Finset.range (collarBlockSiteCapacity R_pert r_0 C_rca),
      ((if h : j.val * collarBlockSiteCapacity R_pert r_0 C_rca + t < W.toList.length then
        let c := W.toList.get ⟨j.val * collarBlockSiteCapacity R_pert r_0 C_rca + t, h⟩
        if h_supp : (sys.support c).Nonempty then {h_supp.choose} else ∅
      else ∅) : Finset (BoxD D L)).card ≤ 1 := by
    intro t _
    split_ifs with h₁
    · (try dsimp only); split_ifs <;> simp
    · simp
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 h_le_one) ?_
  simp

/-- **Additivity of 1-Step `worldlineSliceProduct` in the Jump Operator
    (`worldlineSliceProduct_one_step_add`)** -/
theorem worldlineSliceProduct_one_step_add {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D_dim L Site ι)
    (H_diag K_a K_b : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag)
    (t₀ t₁ : ℝ) (σ₀ σ₁ : ι → Bool) :
    worldlineSliceProduct sys H_diag hH_diag ![t₀, t₁] ![σ₀, σ₁] ![K_a + K_b] =
      worldlineSliceProduct sys H_diag hH_diag ![t₀, t₁] ![σ₀, σ₁] ![K_a] +
        worldlineSliceProduct sys H_diag hH_diag ![t₀, t₁] ![σ₀, σ₁] ![K_b] := by
  change (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) t₀ *
      sys.syndromeProjector σ₀) * (K_a + K_b) *
      (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) t₁ *
        sys.syndromeProjector σ₁) = _
  rw [mul_add, add_mul]
  rfl

/-- **Syndrome-Sector Projection of `positiveCheckWitnessProj`
    (`positiveCheckWitnessProj_mul_syndromeProjector`)** -/
theorem positiveCheckWitnessProj_mul_syndromeProjector {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D_dim L Site ι)
    (W : Finset ι) (σ₀ : ι → Bool) :
    positiveCheckWitnessProj sys W * sys.syndromeProjector σ₀ =
      (((if ∀ c ∈ W, σ₀ c = true then (1 : ℝ) else 0 : ℝ) : ℂ) • sys.syndromeProjector σ₀) := by
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_idemp : sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀ = sys.syndromeProjector σ₀ :=
    (h_res.2.1 σ₀).isIdempotentElem.eq
  have h_orth : ∀ τ : ι → Bool, τ ≠ σ₀ → sys.syndromeProjector τ * sys.syndromeProjector σ₀ = 0 :=
    fun τ hne => h_res.2.2.1 τ σ₀ hne
  unfold positiveCheckWitnessProj
  rw [Finset.sum_mul]
  split_ifs with hW
  · rw [Complex.ofReal_one, one_smul,
      Finset.sum_eq_single σ₀ (fun τ _ hne => h_orth τ hne)
        (fun h_not => False.elim (h_not (Finset.mem_filter.mpr ⟨Finset.mem_univ σ₀, hW⟩))),
      h_idemp]
  · have h_zero : (((0 : ℝ) : ℂ) • sys.syndromeProjector σ₀) = 0 := by ext ψ; simp
    rw [h_zero]
    refine Finset.sum_eq_zero fun τ hτ => h_orth τ ?_
    intro h_eq
    subst h_eq
    exact hW (Finset.mem_filter.mp hτ).2

/-- **Centered Witness Sector Scalar Weight (`centeredWitnessSectorWeight`)**:
    The eigenvalue $\mathbf{1}_{\forall c \in W, \sigma_0 c = \mathrm{true}} - p_{\mathrm{diag}}(W)$
    of `centeredWitnessObservable` on syndrome sector $\sigma_0$. -/
noncomputable def centeredWitnessSectorWeight {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (β : ℝ)
    (P_W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (W : Finset ι) (σ₀ : ι → Bool) : ℝ :=
  (if ∀ c ∈ W, σ₀ c = true then (1 : ℝ) else 0) - gibbsFailureProb H_diag hH_diag β P_W

/-- **Witness-Sector vs. Full-Partition Split of `centeredWitnessSectorWeight` Sums
    (`sum_centeredWitnessSectorWeight_mul_eq`)** -/
theorem sum_centeredWitnessSectorWeight_mul_eq {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (β : ℝ)
    (P_W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (W : Finset ι) (F : (ι → Bool) → ℝ) :
    (∑ σ₀ : ι → Bool, centeredWitnessSectorWeight H_diag hH_diag β P_W W σ₀ * F σ₀) =
      (∑ σ₀ ∈ Finset.univ.filter (fun σ₀ : ι → Bool => ∀ c ∈ W, σ₀ c = true), F σ₀) -
        gibbsFailureProb H_diag hH_diag β P_W * (∑ σ₀ : ι → Bool, F σ₀) := by
  have h_pt : ∀ σ₀ : ι → Bool,
      centeredWitnessSectorWeight H_diag hH_diag β P_W W σ₀ * F σ₀ =
        (if ∀ c ∈ W, σ₀ c = true then F σ₀ else 0) -
          gibbsFailureProb H_diag hH_diag β P_W * F σ₀ := by
    intro σ₀
    unfold centeredWitnessSectorWeight
    split_ifs <;> ring
  simp only [h_pt, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.mul_sum]

/-- **Elimination of Vacuum / Non-Witness Sectors $\sigma_0 \notin \mathcal{E}(W)$ Under Non-Negative Partition Sum
    (`sum_centeredWitnessSectorWeight_mul_le_sum_filter_of_sum_nonneg`)** -/
theorem sum_centeredWitnessSectorWeight_mul_le_sum_filter_of_sum_nonneg {D_dim L : ℕ}
    {Site : BoxD D_dim L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D_dim L Site ι)
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (β : ℝ)
    (W : Finset ι) (F : (ι → Bool) → ℝ)
    (hF_sum : 0 ≤ ∑ σ₀ : ι → Bool, F σ₀) :
    let P_W := positiveCheckWitnessProj sys W
    (∑ σ₀ : ι → Bool, centeredWitnessSectorWeight H_diag hH_diag β P_W W σ₀ * F σ₀) ≤
      ∑ σ₀ ∈ Finset.univ.filter (fun σ₀ : ι → Bool => ∀ c ∈ W, σ₀ c = true), F σ₀ := by
  intro P_W
  rw [sum_centeredWitnessSectorWeight_mul_eq H_diag hH_diag β P_W W F]
  have hZ_pos : 0 < gibbsPartitionZ (opEigenvalues H_diag hH_diag) β :=
    gibbsPartitionZ_pos (opEigenvalues H_diag hH_diag) β
  have h_tr_nn : 0 ≤ hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag)
      (opEigenvalues H_diag hH_diag) β * P_W) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    exact Finset.sum_nonneg fun ω _ => mul_nonneg (le_of_lt (Real.exp_pos _))
      ((isStarProjection_positiveCheckWitnessProj sys W).1.re_inner_nonneg _)
  have h_prob_nn : 0 ≤ gibbsFailureProb H_diag hH_diag β P_W := by
    rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H_diag hH_diag β P_W]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hZ_pos)) h_tr_nn
  linarith [mul_nonneg h_prob_nn hF_sum]

/-- **Cube-Intersecting Check Set (`cubeIntersectingChecks`)** -/
def cubeIntersectingChecks {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (A : Finset (Box3D L)) :
    Finset (StaticCSSCheckIdx L q_code m_max) :=
  Finset.univ.filter (fun c => ¬Disjoint (sys.support c) A)

/-- **Centered Witness Observable (`centeredWitnessObservable`)**:
    $A_W := P_W - p_{\mathrm{diag}}(W) \cdot 1$, whose thermal trace under $B_{H_{\mathrm{diag}}}(\beta)$
    vanishes identically. -/
noncomputable def centeredWitnessObservable {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H_diag : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_diag : IsSelfAdjoint H_diag) (β : ℝ)
    (P_W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  P_W - ((gibbsFailureProb H_diag hH_diag β P_W : ℝ) : ℂ) • 1

/-- **Local Check-Flip Conservation Outside `cubeIntersectingChecks`
    (`pauliOffDiagonalCubeTerm_check_support_conservation`)** -/
theorem pauliOffDiagonalCubeTerm_check_support_conservation
    {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    {A : Finset (Box3D L)}
    {K : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hK_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A K)
    (σ₀ σ₁ : StaticCSSCheckIdx L q_code m_max → Bool)
    {c : StaticCSSCheckIdx L q_code m_max}
    (hc_not_in : c ∉ cubeIntersectingChecks sys A)
    (h_ne : σ₁ c ≠ σ₀ c) :
    sys.syndromeProjector σ₀ * K * sys.syndromeProjector σ₁ = 0 := by
  have h_supp_disj : Disjoint A (sys.support c) := by
    simp only [cubeIntersectingChecks, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hc_not_in
    exact hc_not_in.symm
  have h_comm_K : K * sys.checkProj c = sys.checkProj c * K :=
    KMSPinchedGibbs.commute_of_isSupportedOn_disjoint h_supp_disj hK_supp (sys.is_supported c)
  have h_abs := (PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.2.2.2.2.1
  have h_comm_proj : ∀ σ, sys.syndromeProjector σ * sys.checkProj c =
      sys.checkProj c * sys.syndromeProjector σ := fun σ =>
    ((indexed_check_commuting_perturbation_commutes_with_syndromeProjector
      sys (sys.checkProj c) (fun i => sys.pairwise_commute c i)).1 σ).symm
  cases h0 : σ₀ c <;> cases h1 : σ₁ c
  · exfalso; exact h_ne (h1.trans h0.symm)
  · have h_left : sys.syndromeProjector σ₀ * sys.checkProj c = 0 := by
      rw [h_comm_proj σ₀, h_abs σ₀ c, if_neg (by simp [h0])]
    have h_right : sys.checkProj c * sys.syndromeProjector σ₁ = sys.syndromeProjector σ₁ := by
      rw [h_abs σ₁ c, if_pos h1]
    calc sys.syndromeProjector σ₀ * K * sys.syndromeProjector σ₁
      _ = sys.syndromeProjector σ₀ * K * (sys.checkProj c * sys.syndromeProjector σ₁) := by
          rw [h_right]
      _ = sys.syndromeProjector σ₀ * (K * sys.checkProj c) * sys.syndromeProjector σ₁ := by
          simp only [mul_assoc]
      _ = (sys.syndromeProjector σ₀ * sys.checkProj c) * K * sys.syndromeProjector σ₁ := by
          rw [h_comm_K]; simp only [mul_assoc]
      _ = 0 := by rw [h_left, zero_mul, zero_mul]
  · have h_left : sys.syndromeProjector σ₀ * sys.checkProj c = sys.syndromeProjector σ₀ := by
      rw [h_comm_proj σ₀, h_abs σ₀ c, if_pos h0]
    have h_right : sys.checkProj c * sys.syndromeProjector σ₁ = 0 := by
      rw [h_abs σ₁ c, if_neg (by simp [h1])]
    calc sys.syndromeProjector σ₀ * K * sys.syndromeProjector σ₁
      _ = (sys.syndromeProjector σ₀ * sys.checkProj c) * K * sys.syndromeProjector σ₁ := by
          rw [h_left]
      _ = sys.syndromeProjector σ₀ * (sys.checkProj c * K) * sys.syndromeProjector σ₁ := by
          simp only [mul_assoc]
      _ = sys.syndromeProjector σ₀ * K * (sys.checkProj c * sys.syndromeProjector σ₁) := by
          rw [← h_comm_K]; simp only [mul_assoc]
      _ = 0 := by rw [h_right, mul_zero]
  · exfalso; exact h_ne (h1.trans h0.symm)

/-! ## 4. Klarner Connected Subgraph Counting & Penrose Arborescence Combinatorics -/

/-- **Connected Subgraph Predicate (`KPIsConnectedSubgraph`, Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.3 (`lem:klarner-bound`))** -/
def KPIsConnectedSubgraph {V : Type*} (adj : V → V → Prop) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ adj x y) u v

/-- Enumeration of all `k`-step `adj`-walks starting at `v`. -/
private def kpValidWalks {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] : ℕ → V → Finset (List V)
  | 0, v => {[v]}
  | k + 1, v => (Finset.univ.filter (adj v)).biUnion (fun u => (kpValidWalks adj k u).image (v :: ·))

private lemma head_mem_of_mem_validWalks {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] :
    ∀ (k : ℕ) (v : V) {L : List V}, L ∈ kpValidWalks adj k v → v ∈ L
  | 0, v, L, hL => by rw [kpValidWalks, Finset.mem_singleton] at hL; subst hL; exact List.mem_singleton_self v
  | k + 1, v, L, hL => by
      rcases Finset.mem_biUnion.mp hL with ⟨u, _, hL_img⟩
      rcases Finset.mem_image.mp hL_img with ⟨L₁, _, rfl⟩
      exact List.mem_cons_self

private lemma card_validWalks_le {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] {Δ : ℕ}
    (h_deg : ∀ v : V, (Finset.univ.filter (adj v)).card ≤ Δ) :
    ∀ (k : ℕ) (v : V), (kpValidWalks adj k v).card ≤ Δ ^ k
  | 0, v => by simp [kpValidWalks]
  | k + 1, v => by
      rw [kpValidWalks]
      calc ((Finset.univ.filter (adj v)).biUnion (fun u => (kpValidWalks adj k u).image (v :: ·))).card
        _ ≤ ∑ u ∈ Finset.univ.filter (adj v), (kpValidWalks adj k u).card :=
              le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun u _ => Finset.card_image_le)
        _ ≤ (Finset.univ.filter (adj v)).card • (Δ ^ k) :=
              Finset.sum_le_card_nsmul _ _ (Δ ^ k) fun u _ => card_validWalks_le adj h_deg k u
        _ ≤ Δ * Δ ^ k := by simpa using Nat.mul_le_mul_right (Δ ^ k) (h_deg v)
        _ = Δ ^ (k + 1) := by ring

private lemma exists_splice_validWalks {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] (h_symm : ∀ u v : V, adj u v → adj v u) :
    ∀ (k : ℕ) (v : V) {L : List V}, L ∈ kpValidWalks adj k v →
      ∀ {u w : V}, u ∈ L.toFinset → adj u w →
        ∃ L' ∈ kpValidWalks adj (k + 2) v, L'.toFinset = insert w L.toFinset
  | 0, v, L, hL, u, w, hu, huw => by
      rw [kpValidWalks, Finset.mem_singleton] at hL; subst hL
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, Finset.mem_singleton] at hu; subst hu
      refine ⟨[u, w, u], Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, huw⟩,
        Finset.mem_image.mpr ⟨[w, u], Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, h_symm u w huw⟩,
            Finset.mem_image.mpr ⟨[u], by simp [kpValidWalks], rfl⟩⟩, rfl⟩⟩, ?_⟩
      ext x; simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]; tauto
  | k + 1, v, L, hL, u, w, hu, huw => by
      by_cases huv : u = v
      · subst huv
        have hv_mem : u ∈ L.toFinset := List.mem_toFinset.mpr (head_mem_of_mem_validWalks adj (k + 1) u hL)
        refine ⟨u :: w :: L, Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, huw⟩,
          Finset.mem_image.mpr ⟨w :: L, Finset.mem_biUnion.mpr
            ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, h_symm u w huw⟩,
              Finset.mem_image.mpr ⟨L, hL, rfl⟩⟩, rfl⟩⟩, ?_⟩
        ext x; simp only [List.toFinset_cons, Finset.mem_insert]
        have : x = u → x ∈ L.toFinset := fun h => h ▸ hv_mem
        tauto
      · rcases Finset.mem_biUnion.mp hL with ⟨v₁, hv₁_adj, hL_img⟩
        rcases Finset.mem_image.mp hL_img with ⟨L₁, hL₁_mem, rfl⟩
        simp only [List.toFinset_cons, Finset.mem_insert] at hu
        rcases exists_splice_validWalks adj h_symm k v₁ hL₁_mem (hu.resolve_left huv) huw with
          ⟨L₁', hL₁'_mem, hL₁'_set⟩
        exact ⟨v :: L₁', Finset.mem_biUnion.mpr ⟨v₁, hv₁_adj, Finset.mem_image.mpr ⟨L₁', hL₁'_mem, rfl⟩⟩,
          by simp only [List.toFinset_cons, hL₁'_set]; ext x; simp only [Finset.mem_insert]; tauto⟩

private lemma exists_boundary_edge_of_reflTransGen {V : Type*} [DecidableEq V]
    {adj : V → V → Prop} {S T : Finset V} {a b : V}
    (h_path : Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ adj x y) a b)
    (ha : a ∈ T) (hb : b ∉ T) : ∃ u ∈ T, ∃ w ∈ S \ T, adj u w := by
  induction h_path with
  | refl => exact False.elim (hb ha)
  | @tail c d _ hcd ih =>
      by_cases hc : c ∈ T
      · exact ⟨c, hc, d, Finset.mem_sdiff.mpr ⟨hcd.2.1, hb⟩, hcd.2.2⟩
      · exact ih hc

private lemma exists_validWalk_covering_connectedSubgraph {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] (h_symm : ∀ u v : V, adj u v → adj v u)
    {S : Finset V} {v_0 : V} (hv₀ : v_0 ∈ S) (h_conn : KPIsConnectedSubgraph adj S) :
    ∀ j : ℕ, j < S.card → ∃ L ∈ kpValidWalks adj (2 * j) v_0, L.toFinset ⊆ S ∧ L.toFinset.card = j + 1
  | 0, _ => ⟨[v_0], by simp [kpValidWalks], fun x hx => by
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hx
      exact hx ▸ hv₀, by simp⟩
  | j + 1, hj => by
      rcases exists_validWalk_covering_connectedSubgraph adj h_symm hv₀ h_conn j
        (Nat.lt_of_succ_lt hj) with ⟨L, hL_mem, hL_sub, hL_card⟩
      have h_sdiff_ne : (S \ L.toFinset).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h_empty
        have := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp h_empty); omega
      rcases h_sdiff_ne with ⟨y, hy⟩
      rcases Finset.mem_sdiff.mp hy with ⟨hy_S, hy_not_L⟩
      have hv₀_L : v_0 ∈ L.toFinset :=
        List.mem_toFinset.mpr (head_mem_of_mem_validWalks adj (2 * j) v_0 hL_mem)
      rcases exists_boundary_edge_of_reflTransGen (h_conn.2 v_0 hv₀ y hy_S) hv₀_L hy_not_L with
        ⟨u, hu_L, w, hw_sdiff, huw⟩
      rcases Finset.mem_sdiff.mp hw_sdiff with ⟨hw_S, hw_not_L⟩
      rcases exists_splice_validWalks adj h_symm (2 * j) v_0 hL_mem hu_L huw with ⟨L', hL'_mem, hL'_set⟩
      have h_mul : 2 * j + 2 = 2 * (j + 1) := by ring
      rw [h_mul] at hL'_mem
      exact ⟨L', hL'_mem, hL'_set ▸ Finset.insert_subset hw_S hL_sub,
        by rw [hL'_set, Finset.card_insert_of_notMem hw_not_L, hL_card]⟩

/-- **Klarner Depth-First Spanning-Walk Bound on Connected Subgraphs (`kp_klarner_connected_polymer_count_le`)** -/
theorem kp_klarner_connected_polymer_count_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] (h_symm : ∀ u v : V, adj u v → adj v u)
    {Δ : ℕ} (hΔ : 4 ≤ Δ) (h_deg : ∀ v : V, (Finset.univ.filter (adj v)).card ≤ Δ)
    (v_0 : V) {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 ≤ ε) :
    let Conn_m := Finset.univ.filter (fun S : Finset V =>
      v_0 ∈ S ∧ S.card = m ∧ KPIsConnectedSubgraph adj S)
    (Conn_m.card : ℝ) ≤ ((Δ : ℝ) ^ 2) ^ m ∧
    (∑ S ∈ Conn_m, ε ^ S.card) ≤ ((Δ : ℝ) ^ 2 * ε) ^ m := by
  intro Conn_m
  have h_sub : Conn_m ⊆ (kpValidWalks adj (2 * (m - 1)) v_0).image List.toFinset := fun S hS => by
    rcases (Finset.mem_filter.mp hS).2 with ⟨hv₀, hS_card, h_conn⟩
    rcases exists_validWalk_covering_connectedSubgraph adj h_symm hv₀ h_conn (m - 1) (by omega) with
      ⟨L, hL_mem, hL_sub, hL_card⟩
    exact Finset.mem_image.mpr ⟨L, hL_mem, Finset.eq_of_subset_of_card_le hL_sub (by omega)⟩
  have h_card_nat : Conn_m.card ≤ (Δ ^ 2) ^ m := by
    calc Conn_m.card
      _ ≤ (kpValidWalks adj (2 * (m - 1)) v_0).card := le_trans (Finset.card_le_card h_sub) Finset.card_image_le
      _ ≤ Δ ^ (2 * (m - 1)) := card_validWalks_le adj h_deg (2 * (m - 1)) v_0
      _ ≤ Δ ^ (2 * m) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = (Δ ^ 2) ^ m := by rw [pow_mul]
  have h_card_real : (Conn_m.card : ℝ) ≤ ((Δ : ℝ) ^ 2) ^ m := by exact_mod_cast h_card_nat
  refine ⟨h_card_real, ?_⟩
  have h_sum_eq : (∑ S ∈ Conn_m, ε ^ S.card) = (Conn_m.card : ℝ) * (ε ^ m) := by
    rw [Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_filter.mp hS).2.2.1],
      Finset.sum_const, nsmul_eq_mul]
  rw [h_sum_eq, mul_pow]
  exact mul_le_mul_of_nonneg_right h_card_real (pow_nonneg hε m)

private def kpValidWalksOn {V : Type*} [DecidableEq V] (U : Finset V)
    (adj : V → V → Prop) [DecidableRel adj] : ℕ → V → Finset (List V)
  | 0, v => {[v]}
  | k + 1, v => (U.filter (adj v)).biUnion (fun u => (kpValidWalksOn U adj k u).image (v :: ·))

private lemma head_mem_of_mem_validWalksOn {V : Type*} [DecidableEq V] (U : Finset V)
    (adj : V → V → Prop) [DecidableRel adj] :
    ∀ (k : ℕ) (v : V) {L : List V}, L ∈ kpValidWalksOn U adj k v → v ∈ L
  | 0, v, L, hL => by rw [kpValidWalksOn, Finset.mem_singleton] at hL; subst hL; exact List.mem_singleton_self v
  | k + 1, v, L, hL => by
      rcases Finset.mem_biUnion.mp hL with ⟨u, _, hL_img⟩
      rcases Finset.mem_image.mp hL_img with ⟨L₁, _, rfl⟩
      exact List.mem_cons_self

private lemma card_validWalksOn_le {V : Type*} [DecidableEq V] (U : Finset V)
    (adj : V → V → Prop) [DecidableRel adj] {Δ : ℕ}
    (h_deg : ∀ v ∈ U, (U.filter (adj v)).card ≤ Δ) :
    ∀ (k : ℕ) {v : V}, v ∈ U → (kpValidWalksOn U adj k v).card ≤ Δ ^ k
  | 0, _, _ => by simp [kpValidWalksOn]
  | k + 1, v, hv => by
      rw [kpValidWalksOn]
      calc ((U.filter (adj v)).biUnion (fun u => (kpValidWalksOn U adj k u).image (v :: ·))).card
        _ ≤ ∑ u ∈ U.filter (adj v), (kpValidWalksOn U adj k u).card :=
              le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun u _ => Finset.card_image_le)
        _ ≤ (U.filter (adj v)).card • (Δ ^ k) :=
              Finset.sum_le_card_nsmul _ _ (Δ ^ k) fun u hu =>
                card_validWalksOn_le U adj h_deg k (Finset.mem_filter.mp hu).1
        _ ≤ Δ * Δ ^ k := by simpa using Nat.mul_le_mul_right (Δ ^ k) (h_deg v hv)
        _ = Δ ^ (k + 1) := by ring

private lemma exists_splice_validWalksOn {V : Type*} [DecidableEq V] (U : Finset V)
    (adj : V → V → Prop) [DecidableRel adj] (h_symm : ∀ u v : V, adj u v → adj v u) :
    ∀ (k : ℕ) (v : V) {L : List V}, L ∈ kpValidWalksOn U adj k v →
      ∀ {u w : V}, u ∈ L.toFinset → u ∈ U → w ∈ U → adj u w →
        ∃ L' ∈ kpValidWalksOn U adj (k + 2) v, L'.toFinset = insert w L.toFinset
  | 0, v, L, hL, u, w, hu, huU, hwU, huw => by
      rw [kpValidWalksOn, Finset.mem_singleton] at hL; subst hL
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty, Finset.mem_singleton] at hu; subst hu
      refine ⟨[u, w, u], Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hwU, huw⟩,
        Finset.mem_image.mpr ⟨[w, u], Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_filter.mpr ⟨huU, h_symm u w huw⟩,
            Finset.mem_image.mpr ⟨[u], by simp [kpValidWalksOn], rfl⟩⟩, rfl⟩⟩, ?_⟩
      ext x; simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false]; tauto
  | k + 1, v, L, hL, u, w, hu, huU, hwU, huw => by
      by_cases huv : u = v
      · subst huv
        have hv_mem : u ∈ L.toFinset := List.mem_toFinset.mpr (head_mem_of_mem_validWalksOn U adj (k + 1) u hL)
        refine ⟨u :: w :: L, Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hwU, huw⟩,
          Finset.mem_image.mpr ⟨w :: L, Finset.mem_biUnion.mpr
            ⟨u, Finset.mem_filter.mpr ⟨huU, h_symm u w huw⟩,
              Finset.mem_image.mpr ⟨L, hL, rfl⟩⟩, rfl⟩⟩, ?_⟩
        ext x; simp only [List.toFinset_cons, Finset.mem_insert]
        have : x = u → x ∈ L.toFinset := fun h => h ▸ hv_mem
        tauto
      · rcases Finset.mem_biUnion.mp hL with ⟨v₁, hv₁_adj, hL_img⟩
        rcases Finset.mem_image.mp hL_img with ⟨L₁, hL₁_mem, rfl⟩
        simp only [List.toFinset_cons, Finset.mem_insert] at hu
        rcases exists_splice_validWalksOn U adj h_symm k v₁ hL₁_mem (hu.resolve_left huv) huU hwU huw with
          ⟨L₁', hL₁'_mem, hL₁'_set⟩
        exact ⟨v :: L₁', Finset.mem_biUnion.mpr ⟨v₁, hv₁_adj, Finset.mem_image.mpr ⟨L₁', hL₁'_mem, rfl⟩⟩,
          by simp only [List.toFinset_cons, hL₁'_set]; ext x; simp only [Finset.mem_insert]; tauto⟩

private lemma exists_validWalkOn_covering_connectedSubgraph {V : Type*} [DecidableEq V] (U : Finset V)
    (adj : V → V → Prop) [DecidableRel adj] (h_symm : ∀ u v : V, adj u v → adj v u)
    {S : Finset V} (hSU : S ⊆ U) {v_0 : V} (hv₀ : v_0 ∈ S) (h_conn : KPIsConnectedSubgraph adj S) :
    ∀ j : ℕ, j < S.card → ∃ L ∈ kpValidWalksOn U adj (2 * j) v_0, L.toFinset ⊆ S ∧ L.toFinset.card = j + 1
  | 0, _ => ⟨[v_0], by simp [kpValidWalksOn], fun x hx => by
      simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hx
      exact hx ▸ hv₀, by simp⟩
  | j + 1, hj => by
      rcases exists_validWalkOn_covering_connectedSubgraph U adj h_symm hSU hv₀ h_conn j
        (Nat.lt_of_succ_lt hj) with ⟨L, hL_mem, hL_sub, hL_card⟩
      have h_sdiff_ne : (S \ L.toFinset).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]; intro h_empty
        have := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp h_empty); omega
      rcases h_sdiff_ne with ⟨y, hy⟩
      rcases Finset.mem_sdiff.mp hy with ⟨hy_S, hy_not_L⟩
      have hv₀_L : v_0 ∈ L.toFinset :=
        List.mem_toFinset.mpr (head_mem_of_mem_validWalksOn U adj (2 * j) v_0 hL_mem)
      rcases exists_boundary_edge_of_reflTransGen (h_conn.2 v_0 hv₀ y hy_S) hv₀_L hy_not_L with
        ⟨u, hu_L, w, hw_sdiff, huw⟩
      rcases Finset.mem_sdiff.mp hw_sdiff with ⟨hw_S, hw_not_L⟩
      rcases exists_splice_validWalksOn U adj h_symm (2 * j) v_0 hL_mem hu_L
        (hSU (hL_sub hu_L)) (hSU hw_S) huw with ⟨L', hL'_mem, hL'_set⟩
      have h_mul : 2 * j + 2 = 2 * (j + 1) := by ring
      rw [h_mul] at hL'_mem
      exact ⟨L', hL'_mem, hL'_set ▸ Finset.insert_subset hw_S hL_sub,
        by rw [hL'_set, Finset.card_insert_of_notMem hw_not_L, hL_card]⟩

theorem kp_klarner_connected_subgraph_on_count_le
    {V : Type*} [DecidableEq V] (U : Finset V)
    (adj : V → V → Prop) [DecidableRel adj] (h_symm : ∀ u v : V, adj u v → adj v u)
    {Δ : ℕ} (hΔ : 1 ≤ Δ) (h_deg : ∀ v ∈ U, (U.filter (adj v)).card ≤ Δ)
    {v_0 : V} (hv₀U : v_0 ∈ U) {m : ℕ} (hm : 1 ≤ m) :
    let Conn_m := U.powerset.filter (fun S : Finset V =>
      v_0 ∈ S ∧ S.card = m ∧ KPIsConnectedSubgraph adj S)
    Conn_m.card ≤ (Δ ^ 2) ^ m := by
  intro Conn_m
  have h_sub : Conn_m ⊆ (kpValidWalksOn U adj (2 * (m - 1)) v_0).image List.toFinset := fun S hS => by
    rcases Finset.mem_filter.mp hS with ⟨hS_pow, hv₀, hS_card, h_conn⟩
    rcases exists_validWalkOn_covering_connectedSubgraph U adj h_symm
      (Finset.mem_powerset.mp hS_pow) hv₀ h_conn (m - 1) (by omega) with
      ⟨L, hL_mem, hL_sub, hL_card⟩
    exact Finset.mem_image.mpr ⟨L, hL_mem, Finset.eq_of_subset_of_card_le hL_sub (by omega)⟩
  calc Conn_m.card
    _ ≤ (kpValidWalksOn U adj (2 * (m - 1)) v_0).card :=
        le_trans (Finset.card_le_card h_sub) Finset.card_image_le
    _ ≤ Δ ^ (2 * (m - 1)) := card_validWalksOn_le U adj h_deg (2 * (m - 1)) hv₀U
    _ ≤ Δ ^ (2 * m) := Nat.pow_le_pow_right hΔ (by omega)
    _ = (Δ ^ 2) ^ m := by rw [pow_mul]

lemma connectedSubgraph_bound_of_step_le
    {V : Type*} [DecidableEq V] {adj : V → V → Prop} {S : Finset V}
    (h_conn : KPIsConnectedSubgraph adj S) {v_0 : V} (hv₀ : v_0 ∈ S)
    (d : V → ℕ) (d_0 : ℕ) (hd₀ : d v_0 = 0)
    (h_step : ∀ u ∈ S, ∀ w ∈ S, adj u w → d w ≤ d u + d_0) :
    ∀ x ∈ S, d x ≤ (S.card - 1) * d_0 := by
  have h_ind : ∀ j : ℕ, j < S.card →
      ∃ T ⊆ S, v_0 ∈ T ∧ T.card = j + 1 ∧ ∀ x ∈ T, d x ≤ j * d_0 := by
    intro j; induction j with
    | zero =>
        intro _
        refine ⟨{v_0}, Finset.singleton_subset_iff.mpr hv₀, Finset.mem_singleton_self v_0,
          Finset.card_singleton v_0, fun x hx => ?_⟩
        rw [Finset.mem_singleton.mp hx, hd₀, Nat.zero_mul]
    | succ j ih =>
        intro hj
        rcases ih (Nat.lt_of_succ_lt hj) with ⟨T, hT_sub, hv₀_T, hT_card, hT_bound⟩
        have h_sdiff_ne : (S \ T).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]; intro h_empty
          have := Finset.card_le_card (Finset.sdiff_eq_empty_iff_subset.mp h_empty); omega
        rcases h_sdiff_ne with ⟨y, hy⟩
        rcases Finset.mem_sdiff.mp hy with ⟨hy_S, hy_not_T⟩
        rcases exists_boundary_edge_of_reflTransGen (h_conn.2 v_0 hv₀ y hy_S) hv₀_T hy_not_T with
          ⟨u, hu_T, w, hw_sdiff, huw⟩
        rcases Finset.mem_sdiff.mp hw_sdiff with ⟨hw_S, hw_not_T⟩
        refine ⟨insert w T, Finset.insert_subset hw_S hT_sub, Finset.mem_insert_of_mem hv₀_T,
          by rw [Finset.card_insert_of_notMem hw_not_T, hT_card], fun x hx => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx_T
        · calc d x ≤ d u + d_0 := h_step u (hT_sub hu_T) x hw_S huw
            _ ≤ j * d_0 + d_0 := Nat.add_le_add_right (hT_bound u hu_T) d_0
            _ = (j + 1) * d_0 := by ring
        · exact le_trans (hT_bound x hx_T) (Nat.mul_le_mul_right d_0 (Nat.le_succ j))
  have hS_pos : 0 < S.card := Finset.card_pos.mpr ⟨v_0, hv₀⟩
  rcases h_ind (S.card - 1) (Nat.sub_lt hS_pos zero_lt_one) with ⟨T, hT_sub, _, hT_card, hT_bound⟩
  have hT_eq : T = S := Finset.eq_of_subset_of_card_le hT_sub (by omega)
  rwa [hT_eq] at hT_bound

def PenroseAdj {p : ℕ} (G : Finset (Fin p × Fin p)) (u v : Fin p) : Prop :=
  (u, v) ∈ G ∨ (v, u) ∈ G

private lemma penroseAdj_symm {p : ℕ} {G : Finset (Fin p × Fin p)} {u v : Fin p}
    (h : PenroseAdj G u v) : PenroseAdj G v u := h.symm

private def penroseBall {p : ℕ} (G : Finset (Fin p × Fin p)) (r : Fin p) : ℕ → Finset (Fin p)
  | 0 => {r}
  | k + 1 => penroseBall G r k ∪
      Finset.univ.filter (fun v => ∃ u ∈ penroseBall G r k, PenroseAdj G u v)

private lemma root_mem_penroseBall {p : ℕ} (G : Finset (Fin p × Fin p)) (r : Fin p) :
    ∀ k : ℕ, r ∈ penroseBall G r k
  | 0 => Finset.mem_singleton_self r
  | k + 1 => Finset.mem_union_left _ (root_mem_penroseBall G r k)

private lemma penroseBall_subset_succ {p : ℕ} (G : Finset (Fin p × Fin p)) (r : Fin p) (k : ℕ) :
    penroseBall G r k ⊆ penroseBall G r (k + 1) := Finset.subset_union_left

private lemma penroseBall_mono {p : ℕ} (G : Finset (Fin p × Fin p)) (r : Fin p)
    {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : penroseBall G r k₁ ⊆ penroseBall G r k₂ := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact Finset.Subset.trans ih (penroseBall_subset_succ G r _)

private lemma mem_penroseBall_succ_of_adj {p : ℕ} {G : Finset (Fin p × Fin p)} {r u v : Fin p} {k : ℕ}
    (hu : u ∈ penroseBall G r k) (h_adj : PenroseAdj G u v) :
    v ∈ penroseBall G r (k + 1) :=
  Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, u, hu, h_adj⟩)

private lemma penroseBall_eq_univ_iff_connected {p : ℕ} (hp : 0 < p)
    (G : Finset (Fin p × Fin p)) (r : Fin p) :
    KPIsConnectedSubgraph (PenroseAdj G) Finset.univ ↔ penroseBall G r p = Finset.univ := by
  constructor
  · intro h_conn
    by_contra h_ne
    have h_strict : ∀ k < p, penroseBall G r k ⊂ penroseBall G r (k + 1) := fun k hk => by
      refine ssubset_iff_subset_ne.mpr ⟨penroseBall_subset_succ G r k, fun h_eq => h_ne ?_⟩
      refine Finset.eq_univ_of_forall fun v => penroseBall_mono G r (Nat.le_of_lt hk) ?_
      have h_path := h_conn.2 r (Finset.mem_univ r) v (Finset.mem_univ v)
      induction h_path with
      | refl => exact root_mem_penroseBall G r k
      | @tail x y _ hxy ih => exact h_eq ▸ mem_penroseBall_succ_of_adj ih hxy.2.2
    have h_card : ∀ k ≤ p, k + 1 ≤ (penroseBall G r k).card := fun k => by
      induction k with
      | zero => intro _; simp [penroseBall]
      | succ k ih =>
          intro hk
          have := Finset.card_lt_card (h_strict k (Nat.lt_of_succ_le hk))
          have := ih (Nat.le_of_lt hk); omega
    have h_le : (penroseBall G r p).card ≤ p := by simpa using Finset.card_le_univ (penroseBall G r p)
    have := h_card p (le_refl p); omega
  · intro h_univ
    have h_reach : ∀ k : ℕ, ∀ v ∈ penroseBall G r k,
        Relation.ReflTransGen (fun x y => x ∈ (Finset.univ : Finset (Fin p)) ∧
          y ∈ (Finset.univ : Finset (Fin p)) ∧ PenroseAdj G x y) r v := fun k => by
      induction k with
      | zero => intro v hv; rw [penroseBall, Finset.mem_singleton] at hv; subst hv; exact .refl
      | succ k ih =>
          intro v hv
          rcases Finset.mem_union.mp hv with hv_k | hv_step
          · exact ih v hv_k
          · rcases (Finset.mem_filter.mp hv_step).2 with ⟨u, hu_k, huv⟩
            exact .tail (ih u hu_k) ⟨Finset.mem_univ u, Finset.mem_univ v, huv⟩
    have h_symm_path : ∀ u v : Fin p,
        Relation.ReflTransGen (fun x y => x ∈ (Finset.univ : Finset (Fin p)) ∧
          y ∈ (Finset.univ : Finset (Fin p)) ∧ PenroseAdj G x y) u v →
        Relation.ReflTransGen (fun x y => x ∈ (Finset.univ : Finset (Fin p)) ∧
          y ∈ (Finset.univ : Finset (Fin p)) ∧ PenroseAdj G x y) v u := by
      intro u v h_path
      induction h_path with
      | refl => exact .refl
      | @tail x y _ hxy ih => exact .head ⟨hxy.2.1, hxy.1, penroseAdj_symm hxy.2.2⟩ ih
    refine ⟨⟨r, Finset.mem_univ r⟩, fun u _ v _ => ?_⟩
    exact .trans (h_symm_path r u (h_reach p u (h_univ.symm ▸ Finset.mem_univ u)))
      (h_reach p v (h_univ.symm ▸ Finset.mem_univ v))

private def penroseDist {p : ℕ} (G : Finset (Fin p × Fin p)) (r v : Fin p) : ℕ :=
  if h : ∃ k, v ∈ penroseBall G r k then Nat.find h else p + 1

private lemma mem_penroseBall_iff_penroseDist_le {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} (h_conn : penroseBall G r p = Finset.univ)
    (v : Fin p) (k : ℕ) :
    v ∈ penroseBall G r k ↔ penroseDist G r v ≤ k := by
  have h_ex : ∃ m, v ∈ penroseBall G r m := ⟨p, h_conn.symm ▸ Finset.mem_univ v⟩
  have hd : penroseDist G r v = Nat.find h_ex := dif_pos h_ex
  rw [hd]
  exact ⟨fun hv => Nat.find_min' h_ex hv, fun h_le => penroseBall_mono G r h_le (Nat.find_spec h_ex)⟩

private lemma penroseDist_eq_zero_iff {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} (h_conn : penroseBall G r p = Finset.univ) (v : Fin p) :
    penroseDist G r v = 0 ↔ v = r := by
  have h_iff := mem_penroseBall_iff_penroseDist_le h_conn v 0
  simp only [penroseBall, Finset.mem_singleton, Nat.le_zero] at h_iff
  exact h_iff.symm

private lemma penroseDist_adj_le {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r u v : Fin p} (h_conn : penroseBall G r p = Finset.univ)
    (h_adj : PenroseAdj G u v) : penroseDist G r v ≤ penroseDist G r u + 1 := by
  rw [← mem_penroseBall_iff_penroseDist_le h_conn]
  exact mem_penroseBall_succ_of_adj
    ((mem_penroseBall_iff_penroseDist_le h_conn u (penroseDist G r u)).mpr (le_refl _)) h_adj

private def penrosePreds {p : ℕ} (G : Finset (Fin p × Fin p)) (r v : Fin p) : Finset (Fin p) :=
  (penroseBall G r (penroseDist G r v - 1)).filter (fun u => PenroseAdj G u v)

private lemma penrosePreds_nonempty {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r v : Fin p} (h_conn : penroseBall G r p = Finset.univ) (hv : v ≠ r) :
    (penrosePreds G r v).Nonempty := by
  have hd_pos : 1 ≤ penroseDist G r v := by
    have := (penroseDist_eq_zero_iff h_conn v).not.mpr hv; omega
  have hv_in : v ∈ penroseBall G r ((penroseDist G r v - 1) + 1) := by
    rw [Nat.sub_add_cancel hd_pos, mem_penroseBall_iff_penroseDist_le h_conn]
  have hv_not : v ∉ penroseBall G r (penroseDist G r v - 1) := by
    rw [mem_penroseBall_iff_penroseDist_le h_conn]; omega
  rcases Finset.mem_union.mp hv_in with hv_prev | hv_filt
  · exact False.elim (hv_not hv_prev)
  · rcases (Finset.mem_filter.mp hv_filt).2 with ⟨u, hu_ball, huv⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨hu_ball, huv⟩⟩

private def penroseParent {p : ℕ} (G : Finset (Fin p × Fin p)) (r v : Fin p) : Fin p :=
  if h : v ≠ r ∧ (penrosePreds G r v).Nonempty then (penrosePreds G r v).min' h.2 else r

private lemma penroseParent_mem_preds {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r v : Fin p} (h_conn : penroseBall G r p = Finset.univ) (hv : v ≠ r) :
    penroseParent G r v ∈ penrosePreds G r v := by
  have h_cond : v ≠ r ∧ (penrosePreds G r v).Nonempty := ⟨hv, penrosePreds_nonempty h_conn hv⟩
  unfold penroseParent; rw [dif_pos h_cond]; exact Finset.min'_mem _ h_cond.2

private lemma penroseParent_adj {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r v : Fin p} (h_conn : penroseBall G r p = Finset.univ) (hv : v ≠ r) :
    PenroseAdj G (penroseParent G r v) v :=
  (Finset.mem_filter.mp (penroseParent_mem_preds h_conn hv)).2

private lemma penroseDist_penroseParent {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r v : Fin p} (h_conn : penroseBall G r p = Finset.univ) (hv : v ≠ r) :
    penroseDist G r (penroseParent G r v) + 1 = penroseDist G r v := by
  have h_mem := (Finset.mem_filter.mp (penroseParent_mem_preds h_conn hv)).1
  rw [mem_penroseBall_iff_penroseDist_le h_conn] at h_mem
  have h_le := penroseDist_adj_le h_conn (penroseParent_adj h_conn hv)
  have := (penroseDist_eq_zero_iff h_conn v).not.mpr hv; omega

private lemma penroseParent_le_of_mem_preds {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r v u : Fin p} (h_conn : penroseBall G r p = Finset.univ)
    (hv : v ≠ r) (hu : u ∈ penrosePreds G r v) : penroseParent G r v ≤ u := by
  have h_cond : v ≠ r ∧ (penrosePreds G r v).Nonempty := ⟨hv, ⟨u, hu⟩⟩
  unfold penroseParent; rw [dif_pos h_cond]; exact Finset.min'_le _ u hu

private def IsPenroseTreeEdge {p : ℕ} (G : Finset (Fin p × Fin p)) (r : Fin p) (e : Fin p × Fin p) : Prop :=
  (e.2 ≠ r ∧ e.1 = penroseParent G r e.2) ∨ (e.1 ≠ r ∧ e.2 = penroseParent G r e.1)

private def IsPenroseCompatibleEdge {p : ℕ} (G : Finset (Fin p × Fin p)) (r : Fin p) (e : Fin p × Fin p) : Prop :=
  penroseDist G r e.2 ≤ penroseDist G r e.1 + 1 ∧
  penroseDist G r e.1 ≤ penroseDist G r e.2 + 1 ∧
  (penroseDist G r e.1 < penroseDist G r e.2 → penroseParent G r e.2 ≤ e.1) ∧
  (penroseDist G r e.2 < penroseDist G r e.1 → penroseParent G r e.1 ≤ e.2)

private def IsPenroseFreeEdge {p : ℕ} (G : Finset (Fin p × Fin p)) (r : Fin p) (e : Fin p × Fin p) : Prop :=
  IsPenroseCompatibleEdge G r e ∧ ¬IsPenroseTreeEdge G r e

private lemma isPenroseCompatibleEdge_of_mem {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} (h_conn : penroseBall G r p = Finset.univ)
    {e : Fin p × Fin p} (he : e ∈ G) : IsPenroseCompatibleEdge G r e := by
  have h12 : PenroseAdj G e.1 e.2 := Or.inl he
  have h21 : PenroseAdj G e.2 e.1 := Or.inr he
  refine ⟨penroseDist_adj_le h_conn h12, penroseDist_adj_le h_conn h21, fun h_lt => ?_, fun h_lt => ?_⟩
  · have he2_ne : e.2 ≠ r := fun h_eq => by have := (penroseDist_eq_zero_iff h_conn e.2).mpr h_eq; omega
    refine penroseParent_le_of_mem_preds h_conn he2_ne (Finset.mem_filter.mpr ⟨?_, h12⟩)
    rw [mem_penroseBall_iff_penroseDist_le h_conn]; omega
  · have he1_ne : e.1 ≠ r := fun h_eq => by have := (penroseDist_eq_zero_iff h_conn e.1).mpr h_eq; omega
    refine penroseParent_le_of_mem_preds h_conn he1_ne (Finset.mem_filter.mpr ⟨?_, h21⟩)
    rw [mem_penroseBall_iff_penroseDist_le h_conn]; omega

private def toggleEdge {p : ℕ} (e : Fin p × Fin p) (G : Finset (Fin p × Fin p)) : Finset (Fin p × Fin p) :=
  if e ∈ G then G.erase e else insert e G

private lemma toggleEdge_involutive {p : ℕ} (e : Fin p × Fin p) (G : Finset (Fin p × Fin p)) :
    toggleEdge e (toggleEdge e G) = G := by
  unfold toggleEdge; by_cases he : e ∈ G <;> simp [he, Finset.insert_erase]

private lemma neg_one_pow_toggleEdge {p : ℕ} (e : Fin p × Fin p) (G : Finset (Fin p × Fin p)) :
    ((-1 : ℝ) ^ G.card) + ((-1 : ℝ) ^ (toggleEdge e G).card) = 0 := by
  unfold toggleEdge
  by_cases he : e ∈ G
  · rw [if_pos he, Finset.card_erase_of_mem he]
    have h_pos : 1 ≤ G.card := Finset.card_pos.mpr ⟨e, he⟩
    have h_pow : ((-1 : ℝ) ^ (G.card - 1 + 1)) = ((-1 : ℝ) ^ (G.card - 1)) * (-1 : ℝ) := pow_succ (-1 : ℝ) (G.card - 1)
    rw [Nat.sub_add_cancel h_pos] at h_pow; linarith
  · rw [if_neg he, Finset.card_insert_of_notMem he, pow_succ]; ring

private lemma penroseParent_adj_toggleEdge {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r v : Fin p} {e : Fin p × Fin p}
    (h_conn : penroseBall G r p = Finset.univ) (he : IsPenroseFreeEdge G r e) (hv : v ≠ r) :
    PenroseAdj (toggleEdge e G) (penroseParent G r v) v := by
  have h_adj := penroseParent_adj h_conn hv
  have h_not_tree := he.2
  unfold toggleEdge PenroseAdj at *
  rcases h_adj with h_in | h_in
  · have h_ne : (penroseParent G r v, v) ≠ e := fun h_eq => by subst h_eq; exact h_not_tree (Or.inl ⟨hv, rfl⟩)
    split_ifs <;> [exact Or.inl (Finset.mem_erase.mpr ⟨h_ne, h_in⟩); exact Or.inl (Finset.mem_insert_of_mem h_in)]
  · have h_ne : (v, penroseParent G r v) ≠ e := fun h_eq => by subst h_eq; exact h_not_tree (Or.inr ⟨hv, rfl⟩)
    split_ifs <;> [exact Or.inr (Finset.mem_erase.mpr ⟨h_ne, h_in⟩); exact Or.inr (Finset.mem_insert_of_mem h_in)]

private lemma isPenroseCompatibleEdge_of_mem_toggleEdge {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} {e d : Fin p × Fin p}
    (h_conn : penroseBall G r p = Finset.univ) (he : IsPenroseFreeEdge G r e) (hd : d ∈ toggleEdge e G) :
    IsPenroseCompatibleEdge G r d := by
  unfold toggleEdge at hd; split_ifs at hd with h_in
  · exact isPenroseCompatibleEdge_of_mem h_conn (Finset.mem_of_mem_erase hd)
  · rcases Finset.mem_insert.mp hd with rfl | hd_G
    · exact he.1
    · exact isPenroseCompatibleEdge_of_mem h_conn hd_G

private lemma penroseBall_toggleEdge_eq {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} {e : Fin p × Fin p}
    (h_conn : penroseBall G r p = Finset.univ) (he : IsPenroseFreeEdge G r e) :
    penroseBall (toggleEdge e G) r = penroseBall G r := by
  funext k; induction k with
  | zero => rfl
  | succ k ih =>
      ext v; simp only [penroseBall, ih, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (hv_k | ⟨u, hu_k, huv⟩)
        · exact Or.inl hv_k
        · rw [mem_penroseBall_iff_penroseDist_le h_conn] at hu_k
          rcases huv with huv_in | hvu_in
          · have h_comp := isPenroseCompatibleEdge_of_mem_toggleEdge h_conn he huv_in
            have hv_ball := (mem_penroseBall_iff_penroseDist_le h_conn v (k + 1)).mpr
              (le_trans h_comp.1 (Nat.add_le_add_right hu_k 1))
            simpa only [penroseBall, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hv_ball
          · have h_comp := isPenroseCompatibleEdge_of_mem_toggleEdge h_conn he hvu_in
            have hv_ball := (mem_penroseBall_iff_penroseDist_le h_conn v (k + 1)).mpr
              (le_trans h_comp.2.1 (Nat.add_le_add_right hu_k 1))
            simpa only [penroseBall, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] using hv_ball
      · rintro (hv_k | ⟨u, hu_k, huv⟩)
        · exact Or.inl hv_k
        · by_cases hv_k : v ∈ penroseBall G r k
          · exact Or.inl hv_k
          · right
            have hv_ne : v ≠ r := fun h_eq => hv_k (h_eq ▸ root_mem_penroseBall G r k)
            have hv_le : penroseDist G r v ≤ k + 1 :=
              (mem_penroseBall_iff_penroseDist_le h_conn v (k + 1)).mp (mem_penroseBall_succ_of_adj hu_k huv)
            have hv_gt : k < penroseDist G r v := by
              by_contra h_not
              exact hv_k ((mem_penroseBall_iff_penroseDist_le h_conn v k).mpr (Nat.le_of_not_lt h_not))
            have h_par_dist := penroseDist_penroseParent h_conn hv_ne
            have h_par_in : penroseParent G r v ∈ penroseBall G r k := by
              rw [mem_penroseBall_iff_penroseDist_le h_conn]; omega
            exact ⟨penroseParent G r v, h_par_in, penroseParent_adj_toggleEdge h_conn he hv_ne⟩

private lemma penroseDist_toggleEdge_eq {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} {e : Fin p × Fin p}
    (h_conn : penroseBall G r p = Finset.univ) (he : IsPenroseFreeEdge G r e) :
    penroseDist (toggleEdge e G) r = penroseDist G r := by
  funext v; unfold penroseDist; rw [penroseBall_toggleEdge_eq h_conn he]

private lemma penroseParent_toggleEdge_eq {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} {e : Fin p × Fin p}
    (h_conn : penroseBall G r p = Finset.univ) (he : IsPenroseFreeEdge G r e) :
    penroseParent (toggleEdge e G) r = penroseParent G r := by
  have h_ball := penroseBall_toggleEdge_eq h_conn he
  have h_dist := penroseDist_toggleEdge_eq h_conn he
  have h_conn' : penroseBall (toggleEdge e G) r p = Finset.univ := by rw [h_ball, h_conn]
  funext v
  rcases eq_or_ne v r with rfl | hv
  · simp [penroseParent]
  · have hu₀_in : penroseParent G r v ∈ penrosePreds (toggleEdge e G) r v := by
      unfold penrosePreds; rw [h_ball, h_dist]
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (penroseParent_mem_preds h_conn hv)).1,
        penroseParent_adj_toggleEdge h_conn he hv⟩
    have h_le₁ : penroseParent (toggleEdge e G) r v ≤ penroseParent G r v :=
      penroseParent_le_of_mem_preds h_conn' hv hu₀_in
    have h_par'_mem := penroseParent_mem_preds h_conn' hv
    unfold penrosePreds at h_par'_mem; rw [h_ball, h_dist] at h_par'_mem
    rcases Finset.mem_filter.mp h_par'_mem with ⟨h_in_ball, h_adj'⟩
    rw [mem_penroseBall_iff_penroseDist_le h_conn] at h_in_ball
    have hd_pos : 1 ≤ penroseDist G r v := by have := (penroseDist_eq_zero_iff h_conn v).not.mpr hv; omega
    have h_lt : penroseDist G r (penroseParent (toggleEdge e G) r v) < penroseDist G r v := by omega
    have h_le₂ : penroseParent G r v ≤ penroseParent (toggleEdge e G) r v := by
      rcases h_adj' with h_in | h_in
      · exact (isPenroseCompatibleEdge_of_mem_toggleEdge h_conn he h_in).2.2.1 h_lt
      · exact (isPenroseCompatibleEdge_of_mem_toggleEdge h_conn he h_in).2.2.2 h_lt
    exact le_antisymm h_le₁ h_le₂

private lemma isPenroseFreeEdge_toggleEdge_eq {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} {e : Fin p × Fin p}
    (h_conn : penroseBall G r p = Finset.univ) (he : IsPenroseFreeEdge G r e) :
    IsPenroseFreeEdge (toggleEdge e G) r = IsPenroseFreeEdge G r := by
  funext d; unfold IsPenroseFreeEdge IsPenroseCompatibleEdge IsPenroseTreeEdge
  rw [penroseDist_toggleEdge_eq h_conn he, penroseParent_toggleEdge_eq h_conn he]

def arborescenceForests {p : ℕ} (S R : Finset (Fin p)) : Finset (Fin p → Fin p) :=
  Finset.univ.filter (fun f : Fin p → Fin p =>
    (∀ v, v ∉ S \ R → f v = v) ∧ (∀ v ∈ S \ R, f v ∈ S ∧ f^[p] v ∈ R))

private lemma penroseParent_iterate_eq_root {p : ℕ}
    {G : Finset (Fin p × Fin p)} {r : Fin p} (h_conn : penroseBall G r p = Finset.univ) :
    ∀ (k : ℕ) (v : Fin p), penroseDist G r v ≤ k → (penroseParent G r)^[k] v = r := by
  intro k; induction k with
  | zero => intro v hk; simp [(penroseDist_eq_zero_iff h_conn v).mp (Nat.le_zero.mp hk)]
  | succ k ih =>
      intro v hk
      by_cases hv : v = r
      · have hr_fix : penroseParent G r r = r := by simp [penroseParent]
        have hr_dist : penroseDist G r r ≤ k := by
          rw [(penroseDist_eq_zero_iff h_conn r).mpr rfl]; exact Nat.zero_le k
        rw [hv, Function.iterate_succ_apply, hr_fix]; exact ih r hr_dist
      · rw [Function.iterate_succ_apply]
        have := penroseDist_penroseParent h_conn hv
        exact ih (penroseParent G r v) (by omega)

lemma abs_sum_connGraphs_le_arborescenceForests {p : ℕ} (hp : 0 < p)
    (adj : Fin p → Fin p → Prop) (h_symm : ∀ u v, adj u v → adj v u) (r : Fin p) :
    let E_adj : Finset (Fin p × Fin p) := Finset.univ.filter (fun e => e.1 < e.2 ∧ adj e.1 e.2)
    let ConnGraphs := E_adj.powerset.filter (fun G =>
      KPIsConnectedSubgraph (PenroseAdj G) Finset.univ)
    |∑ G ∈ ConnGraphs, ((-1 : ℝ) ^ G.card)| ≤
      (((arborescenceForests Finset.univ {r}).filter
        (fun f => ∀ v : Fin p, v ≠ r → adj (f v) v)).card : ℝ) := by
  intro E_adj ConnGraphs
  let FreeSet (G : Finset (Fin p × Fin p)) : Finset (Fin p × Fin p) := E_adj.filter (IsPenroseFreeEdge G r)
  let ConnFree := ConnGraphs.filter (fun G => (FreeSet G).Nonempty)
  let ConnTree := ConnGraphs.filter (fun G => ¬(FreeSet G).Nonempty)
  have h_split : (∑ G ∈ ConnGraphs, ((-1 : ℝ) ^ G.card)) =
      (∑ G ∈ ConnFree, ((-1 : ℝ) ^ G.card)) + (∑ G ∈ ConnTree, ((-1 : ℝ) ^ G.card)) :=
    (Finset.sum_filter_add_sum_filter_not ConnGraphs (fun G => (FreeSet G).Nonempty) _).symm
  have h_free_zero : (∑ G ∈ ConnFree, ((-1 : ℝ) ^ G.card)) = 0 := by
    let pickEdge (F : Finset (Fin p × Fin p)) : Fin p × Fin p :=
      if h : F.Nonempty then Classical.choose h else (r, r)
    have h_pick_mem : ∀ {F : Finset (Fin p × Fin p)} (h : F.Nonempty), pickEdge F ∈ F := by
      intro F h; dsimp [pickEdge]; rw [dif_pos h]; exact Classical.choose_spec h
    let inv (G : Finset (Fin p × Fin p)) : Finset (Fin p × Fin p) := toggleEdge (pickEdge (FreeSet G)) G
    refine Finset.sum_involution (fun G _ => inv G)
      (fun G _ => neg_one_pow_toggleEdge (pickEdge (FreeSet G)) G) ?_ ?_ ?_
    · intro G _ _ h_eq
      dsimp [inv, toggleEdge] at h_eq
      by_cases h_in : pickEdge (FreeSet G) ∈ G
      · rw [if_pos h_in] at h_eq
        have h_not : pickEdge (FreeSet G) ∉ G.erase (pickEdge (FreeSet G)) := Finset.notMem_erase _ _
        rw [h_eq] at h_not; exact h_not h_in
      · rw [if_neg h_in] at h_eq
        have h_mem : pickEdge (FreeSet G) ∈ insert (pickEdge (FreeSet G)) G := Finset.mem_insert_self _ _
        rw [h_eq] at h_mem; exact h_in h_mem
    · intro G hG
      rcases Finset.mem_filter.mp hG with ⟨hG_conn, hG_free⟩
      rcases Finset.mem_filter.mp hG_conn with ⟨hG_sub, hG_kp⟩
      rw [Finset.mem_powerset] at hG_sub
      have h_ball : penroseBall G r p = Finset.univ := (penroseBall_eq_univ_iff_connected hp G r).mp hG_kp
      rcases Finset.mem_filter.mp (h_pick_mem hG_free) with ⟨he_E, he_free⟩
      have h_free_eq : FreeSet (inv G) = FreeSet G := by
        dsimp [FreeSet, inv]; rw [isPenroseFreeEdge_toggleEdge_eq h_ball he_free]
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun d hd => ?_, ?_⟩,
        h_free_eq.symm ▸ hG_free⟩
      · dsimp [inv, toggleEdge] at hd; split_ifs at hd with h_in
        · exact hG_sub (Finset.mem_of_mem_erase hd)
        · rcases Finset.mem_insert.mp hd with rfl | hd_G <;> [exact he_E; exact hG_sub hd_G]
      · rw [penroseBall_eq_univ_iff_connected hp _ r]; dsimp [inv]
        rw [penroseBall_toggleEdge_eq h_ball he_free, h_ball]
    · intro G hG
      rcases Finset.mem_filter.mp hG with ⟨hG_conn, hG_free⟩
      have h_ball : penroseBall G r p = Finset.univ :=
        (penroseBall_eq_univ_iff_connected hp G r).mp (Finset.mem_filter.mp hG_conn).2
      have he_free := (Finset.mem_filter.mp (h_pick_mem hG_free)).2
      have h_free_eq : FreeSet (inv G) = FreeSet G := by
        dsimp [FreeSet, inv]; rw [isPenroseFreeEdge_toggleEdge_eq h_ball he_free]
      dsimp [inv]; rw [h_free_eq, toggleEdge_involutive]
  let TargetArb := (arborescenceForests Finset.univ {r}).filter (fun f => ∀ v : Fin p, v ≠ r → adj (f v) v)
  have h_tree_card : ConnTree.card ≤ TargetArb.card := by
    refine Finset.card_le_card_of_injOn (fun G => penroseParent G r) ?_ ?_
    · intro G hG
      rcases Finset.mem_filter.mp (Finset.mem_filter.mp hG).1 with ⟨hG_sub, hG_kp⟩
      rw [Finset.mem_powerset] at hG_sub
      have h_ball : penroseBall G r p = Finset.univ := (penroseBall_eq_univ_iff_connected hp G r).mp hG_kp
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · intro v hv
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and, not_not] at hv
        subst hv; simp [penroseParent]
      · intro v _
        exact ⟨Finset.mem_univ _, Finset.mem_singleton.mpr (penroseParent_iterate_eq_root h_ball p v
          ((mem_penroseBall_iff_penroseDist_le h_ball v p).mp (h_ball.symm ▸ Finset.mem_univ v)))⟩
      · intro v hv
        rcases penroseParent_adj h_ball hv with h_in | h_in
        · exact (Finset.mem_filter.mp (hG_sub h_in)).2.2
        · exact h_symm _ _ (Finset.mem_filter.mp (hG_sub h_in)).2.2
    · intro G₁ hG₁ G₂ hG₂ h_par_eq
      rcases Finset.mem_filter.mp hG₁ with ⟨hG₁_conn, hG₁_nf⟩
      rcases Finset.mem_filter.mp hG₁_conn with ⟨hG₁_sub, hG₁_kp⟩
      rcases Finset.mem_filter.mp hG₂ with ⟨hG₂_conn, hG₂_nf⟩
      rcases Finset.mem_filter.mp hG₂_conn with ⟨hG₂_sub, hG₂_kp⟩
      rw [Finset.mem_powerset] at hG₁_sub hG₂_sub
      have h_ball₁ := (penroseBall_eq_univ_iff_connected hp G₁ r).mp hG₁_kp
      have h_ball₂ := (penroseBall_eq_univ_iff_connected hp G₂ r).mp hG₂_kp
      have h_sub_aux : ∀ {A B : Finset (Fin p × Fin p)}, A ⊆ E_adj → B ⊆ E_adj →
          penroseBall A r p = Finset.univ → penroseBall B r p = Finset.univ →
          ¬(FreeSet A).Nonempty → penroseParent A r = penroseParent B r → A ⊆ B := by
        intro A B hA_sub hB_sub hA_ball hB_ball hA_nf hAB e he
        have he_E := hA_sub he
        have he_lt := (Finset.mem_filter.mp he_E).2.1
        have he_tree : IsPenroseTreeEdge A r e := by
          by_contra h_nt
          exact hA_nf ⟨e, Finset.mem_filter.mpr ⟨he_E, isPenroseCompatibleEdge_of_mem hA_ball he, h_nt⟩⟩
        rcases he_tree with ⟨he2_ne, he1_eq⟩ | ⟨he1_ne, he2_eq⟩
        · have h_adj := (he1_eq.trans (congrFun hAB e.2)).symm ▸ penroseParent_adj hB_ball he2_ne
          rcases h_adj with h_in | h_in
          · exact h_in
          · exact False.elim (lt_asymm he_lt (Finset.mem_filter.mp (hB_sub h_in)).2.1)
        · have h_adj := (he2_eq.trans (congrFun hAB e.1)).symm ▸ penroseParent_adj hB_ball he1_ne
          rcases h_adj with h_in | h_in
          · exact False.elim (lt_asymm he_lt (Finset.mem_filter.mp (hB_sub h_in)).2.1)
          · exact h_in
      exact Finset.Subset.antisymm
        (h_sub_aux hG₁_sub hG₂_sub h_ball₁ h_ball₂ hG₁_nf h_par_eq)
        (h_sub_aux hG₂_sub hG₁_sub h_ball₂ h_ball₁ hG₂_nf h_par_eq.symm)
  rw [h_split, h_free_zero, zero_add]
  calc |∑ G ∈ ConnTree, ((-1 : ℝ) ^ G.card)|
    _ ≤ ∑ G ∈ ConnTree, |((-1 : ℝ) ^ G.card)| := Finset.abs_sum_le_sum_abs _ _
    _ = (ConnTree.card : ℝ) := by simp
    _ ≤ (TargetArb.card : ℝ) := by exact_mod_cast h_tree_card

lemma ofFn_get_eq_self {α : Type*} (l : List α) (d : α) (m : ℕ) (hm : l.length = m) :
    List.ofFn (fun j : Fin m => if h : j.val < l.length then l.get ⟨j.val, h⟩ else d) = l := by
  refine List.ext_get (by simp [hm]) (fun i h₁ h₂ => ?_)
  simp [h₂]

lemma list_prod_opNorm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [Nontrivial E] (l : List (E →L[ℂ] E)) :
    ‖l.prod‖ ≤ (l.map norm).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact le_trans (norm_mul_le hd tl.prod)
      (mul_le_mul_of_nonneg_left ih (norm_nonneg hd))

lemma list_prod_reverse_map_opNorm_le {α E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Nontrivial E] (f : α → (E →L[ℂ] E)) (l : List α) :
    ‖(l.reverse.map f).prod‖ ≤ (l.map (fun x => ‖f x‖)).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.prod_cons,
      mul_comm ‖f hd‖]
    exact le_trans (norm_mul_le _ _)
      (mul_le_mul_of_nonneg_right ih (norm_nonneg (f hd)))

lemma list_prod_le_prod_map {α : Type*} (l : List α) (f g : α → ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x) (hfg : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
    have h_hd_nn : 0 ≤ f hd := hf hd List.mem_cons_self
    have h_hd_le : f hd ≤ g hd := hfg hd List.mem_cons_self
    have h_tl_nn : 0 ≤ (tl.map f).prod :=
      List.prod_nonneg (by intro y hy; rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩; exact hf x (List.mem_cons_of_mem hd hx))
    have h_tl_le : (tl.map f).prod ≤ (tl.map g).prod :=
      ih (fun x hx => hf x (List.mem_cons_of_mem hd hx)) (fun x hx => hfg x (List.mem_cons_of_mem hd hx))
    exact mul_le_mul h_hd_le h_tl_le h_tl_nn (le_trans h_hd_nn h_hd_le)

lemma list_prod_le_finset_prod_of_le_one {α : Type*} [DecidableEq α]
    (l : List α) (w : α → ℝ)
    (hw₀ : ∀ x ∈ l, 0 ≤ w x) (hw₁ : ∀ x ∈ l, w x ≤ 1) :
    (l.map w).prod ≤ ∏ x ∈ l.toFinset, w x := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, List.toFinset_cons]
    have h_hd₀ := hw₀ hd List.mem_cons_self
    have h_hd₁ := hw₁ hd List.mem_cons_self
    have h_tl₀ : ∀ x ∈ tl, 0 ≤ w x := fun x hx => hw₀ x (List.mem_cons_of_mem hd hx)
    have h_tl₁ : ∀ x ∈ tl, w x ≤ 1 := fun x hx => hw₁ x (List.mem_cons_of_mem hd hx)
    have h_tl_ih := ih h_tl₀ h_tl₁
    have h_tl_nn : 0 ≤ (tl.map w).prod :=
      List.prod_nonneg (by intro y hy; rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩; exact h_tl₀ x hx)
    by_cases h_mem : hd ∈ tl.toFinset
    · rw [Finset.insert_eq_of_mem h_mem]
      calc w hd * (tl.map w).prod
        _ ≤ 1 * (tl.map w).prod := mul_le_mul_of_nonneg_right h_hd₁ h_tl_nn
        _ = (tl.map w).prod := one_mul _
        _ ≤ ∏ x ∈ tl.toFinset, w x := h_tl_ih
    · rw [Finset.prod_insert h_mem]
      exact mul_le_mul_of_nonneg_left h_tl_ih h_hd₀

lemma finset_prod_mul_prod_le_prod_union_of_le_one {α : Type*} [DecidableEq α]
    (A B : Finset α) (w : α → ℝ)
    (hw₀ : ∀ x ∈ A ∪ B, 0 ≤ w x) (hw₁ : ∀ x ∈ A ∪ B, w x ≤ 1) :
    (∏ x ∈ A, w x) * (∏ x ∈ B, w x) ≤ ∏ x ∈ A ∪ B, w x := by
  have h_union : A ∪ B = A ∪ (B \ A) := (Finset.union_sdiff_self_eq_union).symm
  rw [h_union, Finset.prod_union Finset.disjoint_sdiff]
  have hA_nn : 0 ≤ ∏ x ∈ A, w x :=
    Finset.prod_nonneg fun x hx => hw₀ x (Finset.mem_union_left B hx)
  refine mul_le_mul_of_nonneg_left ?_ hA_nn
  have hB_split : B = (B \ A) ∪ (B ∩ A) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  have h_disj : Disjoint (B \ A) (B ∩ A) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_inter.mp hx₂).2
  have h_sdiff_nn : 0 ≤ ∏ x ∈ B \ A, w x :=
    Finset.prod_nonneg fun x hx => hw₀ x (Finset.mem_union_right A (Finset.mem_sdiff.mp hx).1)
  have h_inter_le : (∏ x ∈ B ∩ A, w x) ≤ 1 :=
    Finset.prod_le_one₀ (fun x hx => hw₀ x (Finset.mem_union_right A (Finset.mem_inter.mp hx).1))
      (fun x hx => hw₁ x (Finset.mem_union_right A (Finset.mem_inter.mp hx).1))
  calc ∏ x ∈ B, w x
    _ = ∏ x ∈ (B \ A) ∪ (B ∩ A), w x := by rw [← hB_split]
    _ = (∏ x ∈ B \ A, w x) * (∏ x ∈ B ∩ A, w x) := Finset.prod_union h_disj
    _ ≤ (∏ x ∈ B \ A, w x) * 1 := mul_le_mul_of_nonneg_left h_inter_le h_sdiff_nn
    _ = ∏ x ∈ B \ A, w x := mul_one _

lemma list_sum_map_filter_le {α : Type*} (l : List α) (p : α → Bool) (f : α → ℝ)
    (hf : ∀ x ∈ l, 0 ≤ f x) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.filter_cons, List.map_cons, List.sum_cons]
    have h_tl := ih (fun x hx => hf x (List.mem_cons_of_mem hd hx))
    have h_hd := hf hd List.mem_cons_self
    split_ifs
    · rw [List.map_cons, List.sum_cons]; linarith
    · linarith

lemma list_map_finRange_get_eq_map {α β : Type*} (l : List α) (f : α → β) :
    (List.finRange l.length).map (fun j => f (l.get j)) = l.map f := by
  change (List.finRange l.length).map (f ∘ l.get) = l.map f
  rw [← List.map_map, List.map_get_finRange]

lemma exp_list_map_sum {α : Type*} (l : List α) (f : α → ℝ) :
    Real.exp (l.map f).sum = (l.map (fun x => Real.exp (f x))).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.sum_cons, Real.exp_add, ih, List.map_cons, List.prod_cons]

lemma list_prod_const_mul {α : Type*} (l : List α) (c : ℝ) (f : α → ℝ) :
    (l.map (fun x => c * f x)).prod = (c ^ l.length) * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ', ih, List.map_cons, List.prod_cons]
    ring

lemma list_prod_mul_distrib {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map f).prod * (l.map g).prod = (l.map (fun x => f x * g x)).prod := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    ring

lemma abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) :
    |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · have h_abs : |x| = x := abs_of_nonneg hx
    have h_exp_ge : 1 ≤ Real.exp x := Real.one_le_exp hx
    rw [abs_of_nonneg (sub_nonneg.mpr h_exp_ge), h_abs]
    have h_le : 1 - x ≤ Real.exp (-x) := by
      have := Real.add_one_le_exp (-x)
      linarith
    have h_mul := mul_le_mul_of_nonneg_right h_le (le_of_lt (Real.exp_pos x))
    rw [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h_mul
    linarith
  · have h_abs : |x| = -x := abs_of_nonpos hx
    have h_exp_le : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    rw [abs_of_nonpos (sub_nonpos.mpr h_exp_le), h_abs]
    have h_le : 1 + x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    have h_exp_ge_one : 1 ≤ Real.exp (-x) := Real.one_le_exp (neg_nonneg.mpr hx)
    have h_neg_nn : 0 ≤ -x := neg_nonneg.mpr hx
    nlinarith

lemma abs_setIntegral_Icc_le_of_abs_le {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : ℝ → ℝ) (hg : ∀ t ∈ Set.Icc 0 β, |g t| ≤ C) :
    |∫ t in Set.Icc 0 β, g t| ≤ β * C := by
  have h_vol : (MeasureTheory.volume (Set.Icc 0 β)).toReal = β := by
    rw [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hβ]
  have h_lt : MeasureTheory.volume (Set.Icc 0 β) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have h_bound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (s := Set.Icc 0 β) (C := C) h_lt (fun t ht => by rw [Real.norm_eq_abs]; exact hg t ht)
  rw [Real.norm_eq_abs, MeasureTheory.measureReal_def, h_vol, mul_comm C β] at h_bound
  exact h_bound

lemma fin_strictMono_id_le_aux {m : ℕ} {f : Fin m → Fin m} (hf : StrictMono f) :
    ∀ (k : ℕ) (a : Fin m), a.val = k → k ≤ (f a).val
  | 0, _, _ => Nat.zero_le _
  | k + 1, a, ha => by
    let a_prev : Fin m := ⟨k, by omega⟩
    have h_prev := fin_strictMono_id_le_aux hf k a_prev rfl
    have h_lt : (f a_prev).val < (f a).val := hf (by change k < a.val; omega)
    omega

lemma fin_strictMono_id_le {m : ℕ} {f : Fin m → Fin m} (hf : StrictMono f) (a : Fin m) :
    a ≤ f a :=
  fin_strictMono_id_le_aux hf a.val a rfl

def KPOrderedDysonSimplex {m : ℕ} (β : ℝ) (τ : Fin m → ℝ) : Prop :=
  (∀ j : Fin m, 0 ≤ τ j ∧ τ j ≤ β) ∧ StrictMono τ

lemma measurableSet_kpOrderedDysonSimplex {m : ℕ} (β : ℝ) :
    MeasurableSet {τ : Fin m → ℝ | KPOrderedDysonSimplex β τ} := by
  have h_eq : {τ : Fin m → ℝ | KPOrderedDysonSimplex β τ} =
      (⋂ j : Fin m, {τ : Fin m → ℝ | 0 ≤ τ j} ∩ {τ : Fin m → ℝ | τ j ≤ β}) ∩
        ⋂ i : Fin m, ⋂ j : Fin m, ⋂ (_ : i < j), {τ : Fin m → ℝ | τ i < τ j} := by
    ext τ
    simp only [Set.mem_setOf_eq, KPOrderedDysonSimplex, StrictMono, Set.mem_inter_iff, Set.mem_iInter]
  rw [h_eq]
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.iInter fun j => MeasurableSet.inter ?_ ?_
    · exact isClosed_le continuous_const (continuous_apply j) |>.measurableSet
    · exact isClosed_le (continuous_apply j) continuous_const |>.measurableSet
  · refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => ?_
    exact isOpen_lt (continuous_apply i) (continuous_apply j) |>.measurableSet

lemma volume_kpOrderedDysonSimplex_le {m : ℕ} {β : ℝ} (hβ : 0 ≤ β) :
    (MeasureTheory.volume {τ : Fin m → ℝ | KPOrderedDysonSimplex β τ}).toReal ≤
      (β ^ m) / (m.factorial : ℝ) := by
  let S₁ : Set (Fin m → ℝ) := {τ : Fin m → ℝ | KPOrderedDysonSimplex β τ}
  have hS₁_meas : MeasurableSet S₁ := measurableSet_kpOrderedDysonSimplex β
  let B_cube : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Icc 0 β)
  let e_perm (π : Equiv.Perm (Fin m)) : (Fin m → ℝ) ≃ᵐ (Fin m → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) π
  have h_pre_meas : ∀ π : Equiv.Perm (Fin m), MeasurableSet (e_perm π ⁻¹' S₁) :=
    fun π => hS₁_meas.preimage (e_perm π).measurable
  have h_pre_vol : ∀ π : Equiv.Perm (Fin m),
      MeasureTheory.volume (e_perm π ⁻¹' S₁) = MeasureTheory.volume S₁ :=
    fun π => (MeasureTheory.measurePreserving_piCongrLeft (fun _ : Fin m => MeasureTheory.volume) π).measure_preimage
      hS₁_meas.nullMeasurableSet
  have h_disj : ((Finset.univ : Finset (Equiv.Perm (Fin m))) : Set (Equiv.Perm (Fin m))).PairwiseDisjoint
      (fun π => e_perm π ⁻¹' S₁) := by
    intro π₁ _ π₂ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro τ h₁ h₂
    have h_sm₁ : StrictMono (e_perm π₁ τ) := h₁.2
    have h_sm₂ : StrictMono (e_perm π₂ τ) := h₂.2
    let σ₁ : Fin m → Fin m := fun a => π₂ (π₁.symm a)
    let σ₂ : Fin m → Fin m := fun a => π₁ (π₂.symm a)
    have h_comp₁ : ∀ a : Fin m, e_perm π₂ τ (σ₁ a) = e_perm π₁ τ a := fun a => by
      dsimp [e_perm, σ₁]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      have h_symm := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Fin m => ℝ) π₁ τ (π₁.symm a)
      rw [π₁.apply_symm_apply] at h_symm
      exact h_symm.symm
    have h_comp₂ : ∀ a : Fin m, e_perm π₁ τ (σ₂ a) = e_perm π₂ τ a := fun a => by
      dsimp [e_perm, σ₂]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
      have h_symm := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Fin m => ℝ) π₂ τ (π₂.symm a)
      rw [π₂.apply_symm_apply] at h_symm
      exact h_symm.symm
    have hσ₁_sm : StrictMono σ₁ := fun a b hab => by
      rw [← h_sm₂.lt_iff_lt, h_comp₁ a, h_comp₁ b]
      exact h_sm₁ hab
    have hσ₂_sm : StrictMono σ₂ := fun a b hab => by
      rw [← h_sm₁.lt_iff_lt, h_comp₂ a, h_comp₂ b]
      exact h_sm₂ hab
    apply hne
    refine Equiv.ext fun j => ?_
    let a := π₁ j
    have ha₁ : a ≤ σ₁ a := fin_strictMono_id_le hσ₁_sm a
    have ha₂ : a ≤ σ₂ a := fin_strictMono_id_le hσ₂_sm a
    have h_inv : σ₂ (σ₁ a) = a := by dsimp [σ₁, σ₂]; simp
    have h_eq : σ₁ a = a := by
      rcases lt_or_eq_of_le ha₁ with h_lt | h_eq
      · have h_lt₂ : σ₂ a < σ₂ (σ₁ a) := hσ₂_sm h_lt
        rw [h_inv] at h_lt₂
        exact False.elim (lt_irrefl a (lt_of_le_of_lt ha₂ h_lt₂))
      · exact h_eq.symm
    dsimp [σ₁, a] at h_eq
    rw [π₁.symm_apply_apply] at h_eq
    exact h_eq.symm
  have h_sub_cube : (⋃ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))), e_perm π ⁻¹' S₁) ⊆ B_cube := by
    intro τ hτ
    rcases Set.mem_iUnion₂.mp hτ with ⟨π, _, hτ_π⟩
    intro j _
    have hj := hτ_π.1 (π j)
    dsimp [e_perm] at hj
    rwa [MeasurableEquiv.piCongrLeft_apply_apply] at hj
  have h_cube_vol : MeasureTheory.volume B_cube = ENNReal.ofReal (β ^ m) := by
    dsimp [B_cube]
    rw [MeasureTheory.volume_pi_pi]
    simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow hβ m).symm
  have h_sum_vol :
      (m.factorial : ENNReal) * MeasureTheory.volume S₁ ≤ ENNReal.ofReal (β ^ m) := by
    calc (m.factorial : ENNReal) * MeasureTheory.volume S₁
      _ = ∑ π : Equiv.Perm (Fin m), MeasureTheory.volume (e_perm π ⁻¹' S₁) := by
          simp_rw [h_pre_vol, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ = MeasureTheory.volume (⋃ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))), e_perm π ⁻¹' S₁) :=
          (MeasureTheory.measure_biUnion_finset h_disj (fun π _ => h_pre_meas π)).symm
      _ ≤ MeasureTheory.volume B_cube := MeasureTheory.measure_mono h_sub_cube
      _ = ENNReal.ofReal (β ^ m) := h_cube_vol
  have h_real := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_sum_vol
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hβ m)] at h_real
  have h_fac_pos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  rw [le_div_iff₀ h_fac_pos]
  linarith

lemma abs_integral_kpOrderedDysonSimplex_le {m : ℕ} {β B : ℝ}
    (hβ : 0 ≤ β) (hB : 0 ≤ B) (g : (Fin m → ℝ) → ℝ)
    (hg : ∀ τ : Fin m → ℝ, KPOrderedDysonSimplex β τ → |g τ| ≤ B) :
    |∫ τ : Fin m → ℝ, if KPOrderedDysonSimplex β τ then g τ else 0| ≤
      ((β ^ m) / (m.factorial : ℝ)) * B := by
  let S₁ : Set (Fin m → ℝ) := {τ : Fin m → ℝ | KPOrderedDysonSimplex β τ}
  have hS₁_meas : MeasurableSet S₁ := measurableSet_kpOrderedDysonSimplex β
  have h_ind : (fun τ : Fin m → ℝ => if KPOrderedDysonSimplex β τ then g τ else 0) =
      S₁.indicator g := by
    ext τ; by_cases h : KPOrderedDysonSimplex β τ <;> simp [S₁, h]
  rw [h_ind, MeasureTheory.integral_indicator hS₁_meas]
  have h_vol_le := volume_kpOrderedDysonSimplex_le (m := m) hβ
  have h_lt_top : MeasureTheory.volume S₁ < ⊤ := by
    let B_cube : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Icc 0 β)
    have h_sub : S₁ ⊆ B_cube := fun τ hτ j _ => hτ.1 j
    have h_cube_vol : MeasureTheory.volume B_cube = ENNReal.ofReal (β ^ m) := by
      dsimp [B_cube]
      rw [MeasureTheory.volume_pi_pi]
      simp only [Real.volume_Icc, sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (ENNReal.ofReal_pow hβ m).symm
    exact lt_of_le_of_lt (MeasureTheory.measure_mono h_sub) (h_cube_vol ▸ ENNReal.ofReal_lt_top)
  have h_bound := MeasureTheory.norm_setIntegral_le_of_norm_le_const (s := S₁) (C := B) h_lt_top
    (fun τ hτ => by rw [Real.norm_eq_abs]; exact hg τ hτ)
  rw [Real.norm_eq_abs, MeasureTheory.measureReal_def] at h_bound
  calc |∫ τ in S₁, g τ|
    _ ≤ B * (MeasureTheory.volume S₁).toReal := h_bound
    _ = (MeasureTheory.volume S₁).toReal * B := mul_comm _ _
    _ ≤ ((β ^ m) / (m.factorial : ℝ)) * B := mul_le_mul_of_nonneg_right h_vol_le hB

lemma abs_syndromeEnergy_syndromeXor_sub_le
    {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_wt : ∀ idx, sys.weight idx = 1)
    (δ η : StaticCSSCheckIdx L q_code m_max → Bool)
    (S : Finset (StaticCSSCheckIdx L q_code m_max))
    (h_supp : ∀ c, δ c = true → c ∈ S) :
    |sys.syndromeEnergy (fun c => xor (δ c) (η c)) - sys.syndromeEnergy η| ≤ (S.card : ℝ) := by
  have h_en : ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
      sys.syndromeEnergy σ = ∑ c : StaticCSSCheckIdx L q_code m_max, if σ c = true then (1 : ℝ) else 0 := by
    intro σ
    unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => by rw [h_wt c]
  rw [h_en (fun c => xor (δ c) (η c)), h_en η, ← Finset.sum_sub_distrib]
  have h_sub_S : (∑ c : StaticCSSCheckIdx L q_code m_max,
      ((if xor (δ c) (η c) = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0))) =
      ∑ c ∈ S, ((if xor (δ c) (η c) = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0)) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ S) fun c _ hc_not => ?_
    have hδ_false : δ c = false := by
      cases hδ : δ c
      · rfl
      · exact False.elim (hc_not (h_supp c hδ))
    have h_xor : xor (δ c) (η c) = η c := by
      rw [hδ_false]
      cases η c <;> rfl
    rw [h_xor, sub_self]
  rw [h_sub_S]
  calc |∑ c ∈ S, ((if xor (δ c) (η c) = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0))|
    _ ≤ ∑ c ∈ S, |(if xor (δ c) (η c) = true then (1 : ℝ) else 0) - (if η c = true then (1 : ℝ) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ S, (1 : ℝ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        cases xor (δ c) (η c) <;> cases η c <;> norm_num
    _ = (S.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

lemma shiftOpenBox_neighborhoodOffset_mem_boxBall {L r_0 : ℕ}
    (v : Box3D L) (nb : LocalNeighborhoodIdx r_0)
    (h_in : InOpenBox v (neighborhoodOffset r_0 nb)) :
    shiftOpenBox v (neighborhoodOffset r_0 nb) ∈ boxBall v r_0 := by
  let w := shiftOpenBox v (neighborhoodOffset r_0 nb)
  change w ∈ boxBall v r_0
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩
  dsimp [boxDist]
  refine Finset.sup_le fun μ _ => ?_
  have h_nb := (nb μ).isLt
  have h_in_μ := h_in μ
  have h_sh_μ : (w μ).val = ((shiftOpenBox v (neighborhoodOffset r_0 nb)) μ).val := rfl
  dsimp [shiftOpenBox, shiftOpenBoxD] at h_sh_μ
  rw [dif_pos h_in_μ] at h_sh_μ
  dsimp [neighborhoodOffset, coordDist] at h_in_μ h_sh_μ ⊢
  omega

lemma abs_syndromeEnergy_foldr_syndromeXor_sub_le_sum
    {α : Type*} {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_wt : ∀ idx, sys.weight idx = 1)
    (δ_fn : α → StaticCSSCheckIdx L q_code m_max → Bool)
    (S_fn : α → Finset (StaticCSSCheckIdx L q_code m_max))
    (w_fn : α → ℝ)
    (l : List α)
    (h_supp : ∀ x ∈ l, (∀ c, δ_fn x c = true → c ∈ S_fn x) ∧ ((S_fn x).card : ℝ) ≤ w_fn x)
    (σ₀ : StaticCSSCheckIdx L q_code m_max → Bool) :
    |sys.syndromeEnergy (l.foldr (fun x acc c => xor (δ_fn x c) (acc c)) σ₀) -
      sys.syndromeEnergy σ₀| ≤ (l.map w_fn).sum := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    let σ_tl := tl.foldr (fun x acc c => xor (δ_fn x c) (acc c)) σ₀
    have h_hd := h_supp hd List.mem_cons_self
    have h_step1 : |sys.syndromeEnergy (fun c => xor (δ_fn hd c) (σ_tl c)) - sys.syndromeEnergy σ_tl| ≤ w_fn hd :=
      le_trans (abs_syndromeEnergy_syndromeXor_sub_le sys h_wt (δ_fn hd) σ_tl (S_fn hd) h_hd.1) h_hd.2
    have h_step2 : |sys.syndromeEnergy σ_tl - sys.syndromeEnergy σ₀| ≤ (tl.map w_fn).sum :=
      ih (fun x hx => h_supp x (List.mem_cons_of_mem hd hx))
    have h_tri := abs_add_le
      (sys.syndromeEnergy (fun c => xor (δ_fn hd c) (σ_tl c)) - sys.syndromeEnergy σ_tl)
      (sys.syndromeEnergy σ_tl - sys.syndromeEnergy σ₀)
    rw [sub_add_sub_cancel] at h_tri
    linarith

lemma norm_sq_eq_sum_syndromeProjector_norm_sq_local {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (φ : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))) :
    ‖φ‖ ^ 2 = ∑ σ : StaticCSSCheckIdx L q_code m_max → Bool, ‖sys.syndromeProjector σ φ‖ ^ 2 := by
  have h_one : perturbedSyndromeDiagOp sys 1 = 1 :=
    perturbed_syndromeDiagOp_eq_self_of_commute sys (fun σ => Commute.one_left _)
  have h_re := perturbed_re_inner_syndromeDiagOp_eq_sum sys 1 φ
  rw [h_one] at h_re
  simp only [ContinuousLinearMap.one_apply, inner_self_eq_norm_sq] at h_re
  exact h_re

lemma syndromePinchOp_norm_le_local {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (M : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))) :
    ‖syndromePinchOp sys M‖ ≤ ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg M) fun ψ => ?_
  have h_res := PerturbedThermalBarrier.syndrome_resolution_indexed sys
  have h_sq : ‖syndromePinchOp sys M ψ‖ ^ 2 ≤ (‖M‖ * ‖ψ‖) ^ 2 := by
    rw [norm_sq_eq_sum_syndromeProjector_norm_sq_local sys (syndromePinchOp sys M ψ),
      mul_pow, norm_sq_eq_sum_syndromeProjector_norm_sq_local sys ψ, Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    have h_act : sys.syndromeProjector σ (syndromePinchOp sys M ψ) =
        sys.syndromeProjector σ (M (sys.syndromeProjector σ ψ)) := by
      change (sys.syndromeProjector σ * perturbedSyndromeDiagOp sys M) ψ = _
      rw [(perturbed_syndromeDiagOp_mul_syndromeProjector sys M σ).2.1]
      rfl
    rw [h_act]
    have h_proj := isStarProjection_norm_sq_apply_le_bhm (h_res.2.1 σ) (M (sys.syndromeProjector σ ψ))
    have h_op := pow_le_pow_left₀ (norm_nonneg _) (M.le_opNorm (sys.syndromeProjector σ ψ)) 2
    linarith [mul_pow ‖M‖ ‖sys.syndromeProjector σ ψ‖ 2]
  exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg M) (norm_nonneg ψ)) (by linarith)

lemma sub_syndromePinchOp_norm_le_two_mul_norm {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (M : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))) :
    ‖M - syndromePinchOp sys M‖ ≤ 2 * ‖M‖ :=
  le_trans (norm_sub_le M (syndromePinchOp sys M)) (by linarith [syndromePinchOp_norm_le_local sys M])

end SpacetimeWorldlineKP

end
