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

import Defs.FlowAndFilter

/-!
# Bochner Integral Norm Contraction and Conditional Expectation Interchange

Proves norm integrability and operator-norm contraction for `bochnerFilteredOp`, wraps `condExp` as a continuous linear map `condExpCLM` to commute conditional expectations with Bochner time integrals, and establishes off-diagonal conditional expectation tail bounds.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (69) (`eq:two-bochner-transforms`), Proposition 6.3 (`prop:bochner-time-convolution`)
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Bochner Integral Norm Contraction and Superoperator Interchange
-/

/-- High-priority `IsScalarTower` instance for continuous linear endomorphisms over `ℂ`. -/
instance (priority := 10000) instIsScalarTowerCLM {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : IsScalarTower ℂ (E →L[ℂ] E) (E →L[ℂ] E) where
  smul_assoc _ _ _ := by ext; rfl

/-- High-priority `SMulCommClass` instance for continuous linear endomorphisms over `ℂ`. -/
instance (priority := 10000) instSMulCommClassCLM {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] : SMulCommClass ℂ (E →L[ℂ] E) (E →L[ℂ] E) where
  smul_comm c A B := by
    ext x
    change c • A (B x) = A (c • B x)
    exact (A.map_smul c (B x)).symm

/-- Exponential addition law $\exp(x + y) = \exp(x) \exp(y)$ for commuting continuous linear maps. -/
lemma clm_exp_add_of_commute {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {x y : E →L[ℂ] E} (hxy : Commute x y) :
    NormedSpace.exp (x + y) = NormedSpace.exp x * NormedSpace.exp y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hxy
    ((NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _)

/-- Submultiplicativity of the operator norm under contraction sandwiches $\|B X A\| \le \|X\|$ when $\|B\|, \|A\| \le 1$. -/
private lemma norm_sandwich_le_of_norm_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {B X A : E →L[ℂ] E} (hB : ‖B‖ ≤ 1) (hA : ‖A‖ ≤ 1) :
    ‖B * X * A‖ ≤ ‖X‖ := by
  calc ‖B * X * A‖
    _ ≤ ‖B * X‖ * ‖A‖ := norm_mul_le (B * X) A
    _ ≤ (‖B‖ * ‖X‖) * ‖A‖ := mul_le_mul_of_nonneg_right (norm_mul_le B X) (norm_nonneg A)
    _ ≤ (1 * ‖X‖) * 1 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hB (norm_nonneg X)) hA
        (norm_nonneg A) (mul_nonneg zero_le_one (norm_nonneg X))
    _ = ‖X‖ := by ring

/-- Negative-time evolution operator rewrite `timeEvolutionOp H' (-t) = exp(-(i t) • H')`. -/
lemma timeEvolutionOp_neg_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    timeEvolutionOp H' (-t) = NormedSpace.exp ((-(Complex.I * (t : ℂ))) • H') := by
  dsimp [timeEvolutionOp]
  rw [Complex.ofReal_neg, mul_neg]

/-- Inversion law `timeEvolutionOp H' t * timeEvolutionOp H' (-t) = 1` and `timeEvolutionOp H' (-t) * timeEvolutionOp H' t = 1`. -/
lemma timeEvolutionOp_mul_neg_self {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    timeEvolutionOp H' t * timeEvolutionOp H' (-t) = 1 ∧
    timeEvolutionOp H' (-t) * timeEvolutionOp H' t = 1 := by
  let x := (Complex.I * (t : ℂ)) • H'
  have h_neg : timeEvolutionOp H' (-t) = NormedSpace.exp (-x) := by
    dsimp [x]
    rw [timeEvolutionOp_neg_eq, neg_smul (Complex.I * (t : ℂ)) H']
  constructor
  · change NormedSpace.exp x * timeEvolutionOp H' (-t) = 1
    rw [h_neg, ← clm_exp_add_of_commute (Commute.refl x).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  · change timeEvolutionOp H' (-t) * NormedSpace.exp x = 1
    rw [h_neg, ← clm_exp_add_of_commute (Commute.refl x).neg_left, neg_add_cancel, NormedSpace.exp_zero]

/-- When $H'$ is self-adjoint, $\|U_{H'}(t)\| \le 1$. -/
private lemma norm_timeEvolutionOp_le_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (t : ℝ) :
    ‖timeEvolutionOp H' t‖ ≤ 1 := by
  let x := (Complex.I * (t : ℂ)) • H'
  have h_star_x : star x = -x := by
    dsimp [x]
    rw [star_smul, hH'.star_eq, star_mul', RCLike.star_def,
      Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_smul (Complex.I * (t : ℂ)) H']
  have h_exp_adj : (NormedSpace.exp x)† * NormedSpace.exp x = 1 := by
    change star (NormedSpace.exp x) * NormedSpace.exp x = 1
    rw [NormedSpace.star_exp, h_star_x,
      ← clm_exp_add_of_commute (Commute.refl x).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have h1 : ‖(1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  have h_sq : ‖timeEvolutionOp H' t‖ ^ 2 ≤ 1 := by
    change ‖NormedSpace.exp x‖ ^ 2 ≤ 1
    rw [sq, ← CStarRing.norm_star_mul_self,
      show star (NormedSpace.exp x) = (NormedSpace.exp x)† from rfl, h_exp_adj]
    exact h1
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp h_sq

/-- Exact unitary norm preservation of `heisenbergFlow` under a self-adjoint Hamiltonian $H'$. -/
private lemma norm_heisenbergFlow_eq_of_isSelfAdjoint {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (t : ℝ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖heisenbergFlow H' t O‖ = ‖O‖ := by
  have hle : ∀ (u : ℝ) (Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      ‖heisenbergFlow H' u Y‖ ≤ ‖Y‖ := by
    intro u Y
    dsimp [heisenbergFlow]
    exact norm_sandwich_le_of_norm_le_one
      (norm_timeEvolutionOp_le_one hH' u) (norm_timeEvolutionOp_le_one hH' (-u))
  apply le_antisymm (hle t O)
  have h_inv : heisenbergFlow H' (-t) (heisenbergFlow H' t O) = O := by
    dsimp [heisenbergFlow]
    rw [neg_neg]
    calc timeEvolutionOp H' (-t) * (timeEvolutionOp H' t * O * timeEvolutionOp H' (-t)) *
          timeEvolutionOp H' t
      _ = (timeEvolutionOp H' (-t) * timeEvolutionOp H' t) * O *
          (timeEvolutionOp H' (-t) * timeEvolutionOp H' t) := by
        simp only [mul_assoc]
      _ = 1 * O * 1 := by rw [(timeEvolutionOp_mul_neg_self H' t).2]
      _ = O := by rw [one_mul, mul_one]
  calc ‖O‖
    _ = ‖heisenbergFlow H' (-t) (heisenbergFlow H' t O)‖ := by rw [h_inv]
    _ ≤ ‖heisenbergFlow H' t O‖ := hle (-t) (heisenbergFlow H' t O)

/-- **Bochner Filter $L^1$ Norm Bound (`norm_bochnerFilteredOp_le`)**:
    When $H'$ is self-adjoint, the operator norm of the Bochner time-filtered observable
    $\mathcal{F}_w^{H'}(O) = \int_{-\infty}^\infty w(t) \tau_t^{H'}(O) \, dt$ is bounded by
    $(\int_{-\infty}^\infty \|w(t)\| \, dt) \cdot \|O\|$. -/
theorem norm_bochnerFilteredOp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H')
    (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖bochnerFilteredOp H' w O‖ ≤ (∫ t : ℝ, ‖w t‖) * ‖O‖ := by
  unfold bochnerFilteredOp
  calc ‖∫ t : ℝ, w t • heisenbergFlow H' t O‖
    _ ≤ ∫ t : ℝ, ‖w t • heisenbergFlow H' t O‖ := norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖w t‖ * ‖O‖ := by
      congr 1
      funext t
      rw [norm_smul, norm_heisenbergFlow_eq_of_isSelfAdjoint hH' t O]
    _ = (∫ t : ℝ, ‖w t‖) * ‖O‖ := integral_mul_const ‖O‖ (fun t => ‖w t‖)

/-- **Continuous Linear Superoperator Interchange (`clm_apply_bochnerFilteredOp`)**:
    Every continuous linear superoperator $\Phi : \mathcal{B}(\mathcal{H}) \to_L[\mathbb{C}] \mathcal{B}(\mathcal{H})$
    (such as `condExp Site A`, `id - condExp Site A`, or left/right multiplication by $1 - P$)
    commutes with the Bochner time integral on integrable filtered flows. -/
theorem clm_apply_bochnerFilteredOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (Φ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
         (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_int : Integrable (fun t : ℝ => w t • heisenbergFlow H' t O)) :
    Φ (bochnerFilteredOp H' w O) = ∫ t : ℝ, w t • Φ (heisenbergFlow H' t O) := by
  unfold bochnerFilteredOp
  rw [← Φ.integral_comp_comm h_int]
  congr 1
  funext t
  exact map_smul Φ (w t) (heisenbergFlow H' t O)

/-!
## 2. Two-Regime Master Bochner Light-Cone Tail Bound
-/

/-- Partial trace `partialTrace Site B` is additive in the global operator. -/
lemma partialTrace_add {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    (O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    partialTrace Site B (O₁ + O₂) = partialTrace Site B O₁ + partialTrace Site B O₂ := by
  ext ψ α
  change (∑ γ : LocalConfig Site (Finset.univ \ B), ∑ β : LocalConfig Site B,
      (partialTraceEntry Site B O₁ γ α β + partialTraceEntry Site B O₂ γ α β) * ψ.ofLp β) =
    (∑ γ : LocalConfig Site (Finset.univ \ B), ∑ β : LocalConfig Site B,
      partialTraceEntry Site B O₁ γ α β * ψ.ofLp β) +
    (∑ γ : LocalConfig Site (Finset.univ \ B), ∑ β : LocalConfig Site B,
      partialTraceEntry Site B O₂ γ α β * ψ.ofLp β)
  simp only [add_mul, Finset.sum_add_distrib]

/-- Partial trace `partialTrace Site B` is homogeneous with respect to complex scalar multiplication. -/
lemma partialTrace_smul {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L)) (c : ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    partialTrace Site B (c • O) = c • partialTrace Site B O := by
  ext ψ α
  change (∑ γ : LocalConfig Site (Finset.univ \ B), ∑ β : LocalConfig Site B,
      (c * partialTraceEntry Site B O γ α β) * ψ.ofLp β) =
    c * (∑ γ : LocalConfig Site (Finset.univ \ B), ∑ β : LocalConfig Site B,
      partialTraceEntry Site B O γ α β * ψ.ofLp β)
  simp only [mul_assoc, Finset.mul_sum]

/-- Partial-trace conditional expectation `condExp Site B` is additive. -/
lemma condExp_add {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L))
    (O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    condExp Site B (O₁ + O₂) = condExp Site B O₁ + condExp Site B O₂ := by
  dsimp [condExp]
  rw [partialTrace_add, smul_add]
  ext ψ σ; rfl

/-- Partial-trace conditional expectation `condExp Site B` is complex-linear. -/
lemma condExp_smul {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L)) (c : ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    condExp Site B (c • O) = c • condExp Site B O := by
  dsimp [condExp]
  rw [partialTrace_smul, smul_comm]
  ext ψ σ; rfl

/-- The partial-trace conditional expectation `condExp Site B` bundled as a continuous linear
    superoperator on `ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site`. -/
def condExpCLM {D L : ℕ}
    (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L)) :
    (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  LinearMap.toContinuousLinearMap
    { toFun := condExp Site B
      map_add' := condExp_add Site B
      map_smul' := condExp_smul Site B }

/-- **Bochner Filtered Conditional-Expectation Tail Transfer (`norm_offDiag_bochnerFilteredOp_sub_condExp_le`)**:
    If $\|(1 - P) \tau_t^{H'}(O) (1 - P) - \mathbb{E}_{A_0}((1 - P) \tau_t^{H'}(O) (1 - P))\| \le b(t)$
    for all $t \in \mathbb{R}$ and $\|w(t)\| \cdot b(t)$ is integrable with integral $\le \varepsilon_{\mathrm{tail}}$,
    then the off-diagonal Bochner-filtered operator $O_{\mathrm{off}} = (1 - P) \mathcal{F}_w^{H'}(O) (1 - P)$
    satisfies $\|O_{\mathrm{off}} - \mathbb{E}_{A_0}(O_{\mathrm{off}})\| \le \varepsilon_{\mathrm{tail}}$. -/
theorem norm_offDiag_bochnerFilteredOp_sub_condExp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (A0 : Finset (BoxD D L))
    (b : ℝ → ℝ) (ε_tail : ℝ)
    (h_int : Integrable (fun t : ℝ => w t • heisenbergFlow H' t O))
    (h_int_b : Integrable (fun t : ℝ => ‖w t‖ * b t))
    (h_pt : ∀ t : ℝ,
      let F_t := (1 - P) * heisenbergFlow H' t O * (1 - P)
      ‖F_t - condExp Site A0 F_t‖ ≤ b t)
    (h_int_le : (∫ t : ℝ, ‖w t‖ * b t) ≤ ε_tail) :
    let O_off := (1 - P) * bochnerFilteredOp H' w O * (1 - P)
    ‖O_off - condExp Site A0 O_off‖ ≤ ε_tail := by
  intro O_off
  let S_off : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    ((ContinuousLinearMap.mul ℂ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)).flip (1 - P)).comp
      (ContinuousLinearMap.mul ℂ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (1 - P))
  let Ψ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    (ContinuousLinearMap.id ℂ _ - condExpCLM Site A0).comp S_off
  have hΨ_apply : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Ψ X = (1 - P) * X * (1 - P) - condExp Site A0 ((1 - P) * X * (1 - P)) := fun _ => rfl
  have hΨ_bochner : O_off - condExp Site A0 O_off =
      ∫ t : ℝ, w t • Ψ (heisenbergFlow H' t O) := by
    rw [← hΨ_apply (bochnerFilteredOp H' w O)]
    exact clm_apply_bochnerFilteredOp H' w O Ψ h_int
  have hΨ_integrable : Integrable (fun t : ℝ => w t • Ψ (heisenbergFlow H' t O)) := by
    have h1 := Ψ.integrable_comp h_int
    have h2 : (fun t : ℝ => Ψ (w t • heisenbergFlow H' t O)) =
        (fun t : ℝ => w t • Ψ (heisenbergFlow H' t O)) := by
      funext t
      exact map_smul Ψ (w t) (heisenbergFlow H' t O)
    rwa [h2] at h1
  rw [hΨ_bochner]
  calc ‖∫ t : ℝ, w t • Ψ (heisenbergFlow H' t O)‖
    _ ≤ ∫ t : ℝ, ‖w t • Ψ (heisenbergFlow H' t O)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖w t‖ * b t := by
      apply integral_mono hΨ_integrable.norm h_int_b
      intro t
      dsimp only
      rw [norm_smul, hΨ_apply]
      exact mul_le_mul_of_nonneg_left (h_pt t) (norm_nonneg (w t))
    _ ≤ ε_tail := h_int_le

/-- Scalar multiplication on the left preserves commutativity of continuous linear operators. -/
lemma commute_smul_left_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {A B : E →L[ℂ] E} (h : Commute A B) (c : ℂ) : Commute (c • A) B := by
  rw [commute_iff_eq]
  ext v
  have h_eq : (A * B) v = (B * A) v := congrArg (fun T : E →L[ℂ] E => T v) h.eq
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul] at h_eq ⊢
  rw [h_eq]

/-- **Sector Preservation of Bochner Time Filter (`commute_bochnerFilteredOp_of_commute`)**:
    If $\Pi_{\mathrm{sec}}$ commutes with both the Hamiltonian $H'$ and the operator $O$, then
    $\Pi_{\mathrm{sec}}$ commutes with the Bochner time-filtered operator `bochnerFilteredOp H' w O`. -/
theorem commute_bochnerFilteredOp_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH_comm : Commute H' Pi_sec) (hO_comm : Commute O Pi_sec)
    (h_int : Integrable (fun t : ℝ => w t • heisenbergFlow H' t O)) :
    Commute (bochnerFilteredOp H' w O) Pi_sec := by
  let C_Pi : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    (ContinuousLinearMap.mul ℂ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)).flip Pi_sec -
      ContinuousLinearMap.mul ℂ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) Pi_sec
  have h_comm_pt : ∀ t : ℝ, C_Pi (heisenbergFlow H' t O) = 0 := by
    intro t
    have hU_pos : Commute (timeEvolutionOp H' t) Pi_sec :=
      (commute_smul_left_clm hH_comm (Complex.I * (t : ℂ))).exp_left
    have hU_neg : Commute (timeEvolutionOp H' (-t)) Pi_sec :=
      (commute_smul_left_clm hH_comm (Complex.I * ((-t : ℝ) : ℂ))).exp_left
    have h_flow : Commute (heisenbergFlow H' t O) Pi_sec :=
      (hU_pos.mul_left hO_comm).mul_left hU_neg
    change heisenbergFlow H' t O * Pi_sec - Pi_sec * heisenbergFlow H' t O = 0
    rw [h_flow.eq, sub_self]
  have h_int_zero : C_Pi (bochnerFilteredOp H' w O) = 0 := by
    rw [clm_apply_bochnerFilteredOp H' w O C_Pi h_int]
    have h_fn : (fun t : ℝ => w t • C_Pi (heisenbergFlow H' t O)) =
        (fun _ : ℝ => (0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) := by
      funext t
      rw [h_comm_pt t]
      ext ψ i
      exact mul_zero (w t)
    rw [h_fn, integral_zero]
  rw [commute_iff_eq]
  exact sub_eq_zero.mp h_int_zero
