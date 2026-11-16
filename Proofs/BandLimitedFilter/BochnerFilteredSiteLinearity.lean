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
import Proofs.BandLimitedFilter.BandLimitedWeightIntegrals
import Proofs.BandLimitedFilter.BandLimitedFourierMoments
import Proofs.LiebRobinson.BochnerQuasiLocality
import Proofs.LiebRobinson.DuhamelAndGronwall
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.BandLimitedFilter.EigenprojEvolutionAndBlockDecomp
import Proofs.LiebRobinson.SuperpolyDecayClosure
import Proofs.BandLimitedFilter.BochnerFilterSelfAdjointness
import Proofs.LiebRobinson.LiebRobinsonSeries

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Linearity and Telescoping Sums of Bochner-Filtered Site Operators

Proves linearity of `heisenbergFlow` and `bochnerFilteredOp`, defines the site-filtered operator `bochnerFilteredSiteOp`, and establishes exact telescoping summation of filtered site terms back to the total dressed Hamiltonian difference. Derives unitary conjugation identities relating dressed and bare Bochner-filtered operators.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (69) (`eq:two-bochner-transforms`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
-/

/-! ## 1. Linearity and Fixed-Point Invariance of `bochnerFilteredOp` -/

/-- `heisenbergFlow H' t` is additive in the observable. -/
lemma heisenbergFlow_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    heisenbergFlow H' t (A + B) = heisenbergFlow H' t A + heisenbergFlow H' t B := by
  unfold heisenbergFlow; rw [mul_add, add_mul]

/-- `heisenbergFlow H' t` preserves subtraction. -/
lemma heisenbergFlow_sub {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    heisenbergFlow H' t (A - B) = heisenbergFlow H' t A - heisenbergFlow H' t B := by
  unfold heisenbergFlow; rw [mul_sub, sub_mul]

/-- `heisenbergFlow H' t` commutes with finite sums. -/
lemma heisenbergFlow_finset_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {α : Type*} (s : Finset α)
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ)
    (f : α → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    heisenbergFlow H' t (∑ a ∈ s, f a) = ∑ a ∈ s, heisenbergFlow H' t (f a) := by
  unfold heisenbergFlow; rw [Finset.mul_sum, Finset.sum_mul]

/-- Additivity of `bochnerFilteredOp H' w` on integrable flows. -/
theorem bochnerFilteredOp_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (w : ℝ → ℂ)
    {A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hA : Integrable (fun t : ℝ => w t • heisenbergFlow H' t A))
    (hB : Integrable (fun t : ℝ => w t • heisenbergFlow H' t B)) :
    bochnerFilteredOp H' w (A + B) = bochnerFilteredOp H' w A + bochnerFilteredOp H' w B := by
  unfold bochnerFilteredOp
  have h_pt : (fun t : ℝ => w t • heisenbergFlow H' t (A + B)) =
      (fun t : ℝ => w t • heisenbergFlow H' t A + w t • heisenbergFlow H' t B) := by
    funext t; rw [heisenbergFlow_add, smul_add]
  rw [h_pt, integral_add hA hB]

/-- Finite-sum linearity of `bochnerFilteredOp H' w` on integrable flows. -/
theorem bochnerFilteredOp_finset_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {α : Type*} (s : Finset α)
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (w : ℝ → ℂ)
    (f : α → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hf : ∀ a ∈ s, Integrable (fun t : ℝ => w t • heisenbergFlow H' t (f a))) :
    bochnerFilteredOp H' w (∑ a ∈ s, f a) = ∑ a ∈ s, bochnerFilteredOp H' w (f a) := by
  unfold bochnerFilteredOp
  have h_pt : (fun t : ℝ => w t • heisenbergFlow H' t (∑ a ∈ s, f a)) =
      (fun t : ℝ => ∑ a ∈ s, w t • heisenbergFlow H' t (f a)) := by
    funext t; rw [heisenbergFlow_finset_sum, Finset.smul_sum]
  rw [h_pt, integral_finset_sum s hf]

/-- Any operator $Z$ commuting with $H'$ is a fixed point of `bochnerFilteredOp H' w` whenever $\int w = 1$. -/
theorem bochnerFilteredOp_eq_self_of_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' Z : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {w : ℝ → ℂ} (hw_one : (∫ t : ℝ, w t) = 1) (hHZ : Commute H' Z) :
    bochnerFilteredOp H' w Z = Z := by
  unfold bochnerFilteredOp
  have h_flow : (fun t : ℝ => w t • heisenbergFlow H' t Z) = (fun t : ℝ => w t • Z) := by
    funext t
    have hU : Commute (timeEvolutionOp H' t) Z :=
      (commute_smul_left_clm hHZ (Complex.I * (t : ℂ))).exp_left
    have h_heis : heisenbergFlow H' t Z = Z := by
      dsimp [heisenbergFlow]; rw [hU.eq, mul_assoc, (timeEvolutionOp_mul_neg_self H' t).1, mul_one]
    rw [h_heis]
  rw [h_flow, integral_smul_const, hw_one, one_smul]

/-- In particular, `bochnerFilteredOp H' w H' = H'` whenever $\int_{-\infty}^\infty w(t)\, dt = 1$. -/
theorem bochnerFilteredOp_self_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {w : ℝ → ℂ} (hw_one : (∫ t : ℝ, w t) = 1) :
    bochnerFilteredOp H' w H' = H' :=
  bochnerFilteredOp_eq_self_of_commute H' H' hw_one (Commute.refl H')

/-! ## 2. Bochner-Filtered Site Operator `bochnerFilteredSiteOp` -/

/-- **BH11 Section 7 Lemma 7 (`rewrite1`) Bochner-Filtered Site Operator (`bochnerFilteredSiteOp`)**:
    $X_u := \mathrm{bochnerFilteredOp}\ H'\ w\ (U^\dagger V_u U) + (\mathrm{bochnerFilteredOp}\ H'\ w\ (U^\dagger Q_u U) - Q_u)$. -/
def bochnerFilteredSiteOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  bochnerFilteredOp H' w (U† * V_u * U) +
    (bochnerFilteredOp H' w (U† * Q_u * U) - Q_u)

/-- The difference of two self-adjoint continuous linear operators on a complex Hilbert space is self-adjoint. -/
lemma isSelfAdjoint_sub_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A - B) :=
  hA.sub hB

/-- **Self-Adjointness of `bochnerFilteredSiteOp`**:
    Whenever $H'$, $V_u$, and $Q_u$ are self-adjoint and $\forall t,\, \mathrm{star}(w(t)) = w(t)$,
    `bochnerFilteredSiteOp H' U w V_u Q_u` is self-adjoint. -/
theorem isSelfAdjoint_bochnerFilteredSiteOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' U V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (hV_u : IsSelfAdjoint V_u) (hQ_u : IsSelfAdjoint Q_u)
    {w : ℝ → ℂ} (hw : ∀ t : ℝ, star (w t) = w t) :
    IsSelfAdjoint (bochnerFilteredSiteOp H' U w V_u Q_u) := by
  unfold bochnerFilteredSiteOp
  have h1 : IsSelfAdjoint (bochnerFilteredOp H' w (U† * V_u * U)) :=
    isSelfAdjoint_bochnerFilteredOp hH' (isSelfAdjoint_conj_adjoint hV_u U) hw
  have h2 : IsSelfAdjoint (bochnerFilteredOp H' w (U† * Q_u * U)) :=
    isSelfAdjoint_bochnerFilteredOp hH' (isSelfAdjoint_conj_adjoint hQ_u U) hw
  exact isSelfAdjoint_add_clm h1 (isSelfAdjoint_sub_clm h2 hQ_u)

/-- Specialization of `isSelfAdjoint_bochnerFilteredSiteOp` to `bhFilterWeight`. -/
theorem isSelfAdjoint_bochnerFilteredSiteOp_w_BH11 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' U V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (hV_u : IsSelfAdjoint V_u) (hQ_u : IsSelfAdjoint Q_u) :
    IsSelfAdjoint (bochnerFilteredSiteOp H' U bhFilterWeight V_u Q_u) :=
  isSelfAdjoint_bochnerFilteredSiteOp hH' hV_u hQ_u star_w_BH11

/-- **Exact Global Energy Decomposition (`sum_bochnerFilteredSiteOp_eq_H'_sub_H0`)**:
    When $\sum_{u} V_u(u) = V_{\mathrm{tot}}$, $\sum_{u} Q_u(u) = H_0$, $H' = U^\dagger (H_0 + V_{\mathrm{tot}}) U$,
    $\int_{-\infty}^\infty w(t)\, dt = 1$, and `w t • heisenbergFlow H' t X` is integrable for all $X$,
    the site-filtered operators $X_u := \mathrm{bochnerFilteredSiteOp}\ H'\ U\ w\ (V_u(u))\ (Q_u(u))$
    sum globally to $H' - H_0$:
    $$\sum_{u \in \mathrm{BoxD}\ D\ L} X_u = H' - H_0 \qquad\text{and}\qquad
      H_0 + \sum_{u \in \mathrm{BoxD}\ D\ L} X_u = H'.$$ -/
theorem sum_bochnerFilteredSiteOp_eq_H'_sub_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H0 totalPerturbation H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hV_sum : (∑ u : BoxD D L, V_u u) = totalPerturbation)
    (hQ_sum : (∑ u : BoxD D L, Q_u u) = H0)
    (hH'_eq : H' = U† * (H0 + totalPerturbation) * U)
    (hw_one : (∫ t : ℝ, w t) = 1)
    (hint : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Integrable (fun t : ℝ => w t • heisenbergFlow H' t X)) :
    (∑ u : BoxD D L, bochnerFilteredSiteOp H' U w (V_u u) (Q_u u)) = H' - H0 ∧
    H0 + (∑ u : BoxD D L, bochnerFilteredSiteOp H' U w (V_u u) (Q_u u)) = H' := by
  have h_sum_V :
      (∑ u : BoxD D L, bochnerFilteredOp H' w (U† * V_u u * U)) =
        bochnerFilteredOp H' w (U† * totalPerturbation * U) := by
    rw [← bochnerFilteredOp_finset_sum Finset.univ H' w (fun u => U† * V_u u * U)
      (fun u _ => hint _)]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hV_sum]
  have h_sum_Q :
      (∑ u : BoxD D L, bochnerFilteredOp H' w (U† * Q_u u * U)) =
        bochnerFilteredOp H' w (U† * H0 * U) := by
    rw [← bochnerFilteredOp_finset_sum Finset.univ H' w (fun u => U† * Q_u u * U)
      (fun u _ => hint _)]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hQ_sum]
  have h_tot :
      (∑ u : BoxD D L, bochnerFilteredSiteOp H' U w (V_u u) (Q_u u)) = H' - H0 := by
    unfold bochnerFilteredSiteOp
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h_sum_V, h_sum_Q, hQ_sum]
    have h_add_boch :
        bochnerFilteredOp H' w (U† * totalPerturbation * U) + bochnerFilteredOp H' w (U† * H0 * U) =
          bochnerFilteredOp H' w H' := by
      rw [← bochnerFilteredOp_add H' w (hint _) (hint _)]
      have h_alg : U† * totalPerturbation * U + U† * H0 * U = H' := by
        rw [hH'_eq, mul_add (U†) H0 totalPerturbation, add_mul, add_comm]
      rw [h_alg]
    rw [← add_sub_assoc, h_add_boch, bochnerFilteredOp_self_eq H' hw_one]
  refine ⟨h_tot, ?_⟩
  rw [h_tot, add_sub_cancel]

/-!
## 3. Bochner Conditional-Expectation Tail Bounds for `bochnerFilteredOp` & `bochnerFilteredSiteOp`
-/

/-- **Unprojected Bochner Conditional-Expectation Tail Transfer (`norm_bochnerFilteredOp_sub_condExp_le`)**:
    If $\|\tau_t^{H'}(O) - \mathbb{E}_{A_0}(\tau_t^{H'}(O))\| \le b(t)$ for all $t \in \mathbb{R}$ and
    $\int_{-\infty}^\infty \|w(t)\| b(t)\, dt \le \varepsilon_{\mathrm{tail}}$, then
    $\|\mathcal{F}_w^{H'}(O) - \mathbb{E}_{A_0}(\mathcal{F}_w^{H'}(O))\| \le \varepsilon_{\mathrm{tail}}$. -/
theorem norm_bochnerFilteredOp_sub_condExp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (A0 : Finset (BoxD D L))
    (b : ℝ → ℝ) (ε_tail : ℝ)
    (h_int : Integrable (fun t : ℝ => w t • heisenbergFlow H' t O))
    (h_int_b : Integrable (fun t : ℝ => ‖w t‖ * b t))
    (h_pt : ∀ t : ℝ,
      ‖heisenbergFlow H' t O - condExp Site A0 (heisenbergFlow H' t O)‖ ≤ b t)
    (h_int_le : (∫ t : ℝ, ‖w t‖ * b t) ≤ ε_tail) :
    ‖bochnerFilteredOp H' w O - condExp Site A0 (bochnerFilteredOp H' w O)‖ ≤ ε_tail := by
  let Ψ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →L[ℂ]
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    ContinuousLinearMap.id ℂ _ - condExpCLM Site A0
  have hΨ_apply : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Ψ X = X - condExp Site A0 X := fun _ => rfl
  have hΨ_bochner : bochnerFilteredOp H' w O - condExp Site A0 (bochnerFilteredOp H' w O) =
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

/-- Triangle-inequality conditional-expectation tail bound for `bochnerFilteredSiteOp` when $Q_u$
    is already supported on $A_0$ (`condExp Site A0 Q_u = Q_u`). -/
theorem norm_bochnerFilteredSiteOp_sub_condExp_le_of_isSupportedOn {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (A0 : Finset (BoxD D L))
    {ε_V ε_Q : ℝ}
    (hQ_supp : IsSupportedOn Site A0 Q_u)
    (hV_tail : ‖bochnerFilteredOp H' w (U† * V_u * U) -
      condExp Site A0 (bochnerFilteredOp H' w (U† * V_u * U))‖ ≤ ε_V)
    (hQ_tail : ‖bochnerFilteredOp H' w (U† * Q_u * U) -
      condExp Site A0 (bochnerFilteredOp H' w (U† * Q_u * U))‖ ≤ ε_Q) :
    let X_u := bochnerFilteredSiteOp H' U w V_u Q_u
    ‖X_u - condExp Site A0 X_u‖ ≤ ε_V + ε_Q := by
  intro X_u
  let FV := bochnerFilteredOp H' w (U† * V_u * U)
  let FQ := bochnerFilteredOp H' w (U† * Q_u * U)
  have hQ_ce : condExp Site A0 Q_u = Q_u := condExp_eq_self_of_isSupportedOn hQ_supp
  have h_sub_ce : condExp Site A0 (FQ - Q_u) = condExp Site A0 FQ - Q_u := by
    have h1 := (condExpCLM Site A0).map_sub FQ Q_u
    change condExp Site A0 (FQ - Q_u) = condExp Site A0 FQ - condExp Site A0 Q_u at h1
    rw [h1, hQ_ce]
  have h_ce_X : condExp Site A0 X_u = condExp Site A0 FV + (condExp Site A0 FQ - Q_u) := by
    change condExp Site A0 (FV + (FQ - Q_u)) = _
    rw [condExp_add, h_sub_ce]
  have h_diff : X_u - condExp Site A0 X_u =
      (FV - condExp Site A0 FV) + (FQ - condExp Site A0 FQ) := by
    change (FV + (FQ - Q_u)) - condExp Site A0 X_u = _
    rw [h_ce_X]
    abel
  rw [h_diff]
  exact le_trans (norm_add_le _ _) (add_le_add hV_tail hQ_tail)

/-- Off-diagonal conditional-expectation tail bound for `(1 - P) * bochnerFilteredSiteOp H' U w V_u Q_u * (1 - P)`
    when $(1 - P) Q_u (1 - P) = Q_u$ and $Q_u$ is supported on $A_0$. -/
theorem norm_offDiag_bochnerFilteredSiteOp_sub_condExp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (P H' U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (A0 : Finset (BoxD D L))
    {ε_V ε_Q : ℝ}
    (hQ_exc : (1 - P) * Q_u * (1 - P) = Q_u)
    (hQ_supp : IsSupportedOn Site A0 Q_u)
    (hV_tail :
      let FV_off := (1 - P) * bochnerFilteredOp H' w (U† * V_u * U) * (1 - P)
      ‖FV_off - condExp Site A0 FV_off‖ ≤ ε_V)
    (hQ_tail :
      let FQ_off := (1 - P) * bochnerFilteredOp H' w (U† * Q_u * U) * (1 - P)
      ‖FQ_off - condExp Site A0 FQ_off‖ ≤ ε_Q) :
    let X_u := bochnerFilteredSiteOp H' U w V_u Q_u
    let O_off := (1 - P) * X_u * (1 - P)
    ‖O_off - condExp Site A0 O_off‖ ≤ ε_V + ε_Q := by
  intro X_u O_off
  let FV_off := (1 - P) * bochnerFilteredOp H' w (U† * V_u * U) * (1 - P)
  let FQ_off := (1 - P) * bochnerFilteredOp H' w (U† * Q_u * U) * (1 - P)
  have hQ_ce : condExp Site A0 Q_u = Q_u := condExp_eq_self_of_isSupportedOn hQ_supp
  have hO_eq : O_off = FV_off + (FQ_off - Q_u) := by
    dsimp [O_off, X_u, bochnerFilteredSiteOp, FV_off, FQ_off]
    rw [mul_add (1 - P), add_mul _ _ (1 - P),
      mul_sub (1 - P) _ Q_u, sub_mul _ ((1 - P) * Q_u) (1 - P), hQ_exc]
  have h_sub_ce : condExp Site A0 (FQ_off - Q_u) = condExp Site A0 FQ_off - Q_u := by
    have h1 := (condExpCLM Site A0).map_sub FQ_off Q_u
    change condExp Site A0 (FQ_off - Q_u) = condExp Site A0 FQ_off - condExp Site A0 Q_u at h1
    rw [h1, hQ_ce]
  have h_diff : O_off - condExp Site A0 O_off =
      (FV_off - condExp Site A0 FV_off) + (FQ_off - condExp Site A0 FQ_off) := by
    rw [hO_eq, condExp_add, h_sub_ce]
    abel
  rw [h_diff]
  exact le_trans (norm_add_le _ _) (add_le_add hV_tail hQ_tail)

/-!
## 4. Unitary-Conjugation Covariance of `bochnerFilteredOp` & `bochnerFilteredSiteOp`
-/

/-- Power-conjugation identity $(V A U)^n = V A^n U$ whenever $U V = 1$ and $V U = 1$. -/
lemma ring_conj_pow_of_mul_eq_one {R : Type*} [Ring R] {V U : R}
    (hUV : U * V = 1) (hVU : V * U = 1) (A : R) (n : ℕ) :
    (V * A * U) ^ n = V * A ^ n * U := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, mul_one, hVU]
  | succ n ih =>
    rw [pow_succ, ih]
    calc (V * A ^ n * U) * (V * A * U)
      _ = V * A ^ n * (U * V) * A * U := by simp only [mul_assoc]
      _ = V * (A ^ n * A) * U := by rw [hUV, mul_one]; simp only [mul_assoc]
      _ = V * A ^ (n + 1) * U := by rw [← pow_succ]

/-- Exponential conjugation identity $\exp(V A U) = V \exp(A) U$ whenever $U V = 1$ and $V U = 1$. -/
theorem clm_exp_conj_of_mul_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {V U : E →L[ℂ] E} (hUV : U * V = 1) (hVU : V * U = 1) (A : E →L[ℂ] E) :
    NormedSpace.exp (V * A * U) = V * NormedSpace.exp A * U := by
  let S_VU : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip U).comp
      (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) V)
  have hS_apply : ∀ X : E →L[ℂ] E, S_VU X = V * X * U := fun _ => rfl
  have h_term : ∀ n : ℕ,
      ((Nat.factorial n : ℂ)⁻¹) • (V * A * U) ^ n =
      S_VU (((Nat.factorial n : ℂ)⁻¹) • A ^ n) := by
    intro n
    rw [S_VU.map_smul, hS_apply, ring_conj_pow_of_mul_eq_one hUV hVU A n]
  calc NormedSpace.exp (V * A * U)
    _ = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • (V * A * U) ^ n := clm_exp_eq_tsum (V * A * U)
    _ = ∑' n : ℕ, S_VU (((Nat.factorial n : ℂ)⁻¹) • A ^ n) := tsum_congr h_term
    _ = S_VU (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • A ^ n) :=
      (S_VU.map_tsum (clm_expSeries_summable A)).symm
    _ = S_VU (NormedSpace.exp A) := by rw [← clm_exp_eq_tsum A]
    _ = V * NormedSpace.exp A * U := rfl

/-- Unitary conjugation covariance of `timeEvolutionOp`:
    `timeEvolutionOp (U† * H * U) t = U† * timeEvolutionOp H t * U`. -/
theorem timeEvolutionOp_conj_unitary {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hUU_adj : U * U† = 1) (hU_adj_U : U† * U = 1)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    timeEvolutionOp (U† * H * U) t = U† * timeEvolutionOp H t * U := by
  unfold timeEvolutionOp
  have h_smul : (Complex.I * (t : ℂ)) • (U† * H * U) =
      U† * ((Complex.I * (t : ℂ)) • H) * U := by
    rw [← clm_smul_mul, ← clm_mul_smul]
  rw [h_smul, clm_exp_conj_of_mul_eq_one hUU_adj hU_adj_U]

/-- Unitary conjugation covariance of `heisenbergFlow`:
    `heisenbergFlow (U† * H * U) t (U† * O * U) = U† * heisenbergFlow H t O * U`. -/
theorem heisenbergFlow_conj_unitary {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hUU_adj : U * U† = 1) (hU_adj_U : U† * U = 1)
    (H O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    heisenbergFlow (U† * H * U) t (U† * O * U) = U† * heisenbergFlow H t O * U := by
  unfold heisenbergFlow
  rw [timeEvolutionOp_conj_unitary hUU_adj hU_adj_U H t,
    timeEvolutionOp_conj_unitary hUU_adj hU_adj_U H (-t)]
  calc (U† * timeEvolutionOp H t * U) * (U† * O * U) * (U† * timeEvolutionOp H (-t) * U)
    _ = U† * timeEvolutionOp H t * (U * U†) * O * (U * U†) * timeEvolutionOp H (-t) * U := by
      simp only [mul_assoc]
    _ = U† * (timeEvolutionOp H t * O * timeEvolutionOp H (-t)) * U := by
      rw [hUU_adj, mul_one, mul_one]; simp only [mul_assoc]

/-- Unitary conjugation covariance of `bochnerFilteredOp`:
    `bochnerFilteredOp (U† * H * U) w (U† * O * U) = U† * bochnerFilteredOp H w O * U`. -/
theorem bochnerFilteredOp_conj_unitary {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hUU_adj : U * U† = 1) (hU_adj_U : U† * U = 1)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (w : ℝ → ℂ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (h_int : Integrable (fun t : ℝ => w t • heisenbergFlow H t O)) :
    bochnerFilteredOp (U† * H * U) w (U† * O * U) = U† * bochnerFilteredOp H w O * U := by
  unfold bochnerFilteredOp
  rw [clm_sandwich_integral_smul (U†) U w _ h_int]
  congr 1; funext t
  rw [heisenbergFlow_conj_unitary hUU_adj hU_adj_U H O t]

/-- **Dressed-to-Undressed Decomposition of `bochnerFilteredSiteOp` (`bochnerFilteredSiteOp_eq_conj_unitary`)**:
    When $H' = U^\dagger H U$ with $U$ unitary ($U U^\dagger = 1$ and $U^\dagger U = 1$) and
    $\int_{-\infty}^\infty w(t)\, dt = 1$, the BH11 site operator decomposes as:
    $$X_u = U^\dagger \mathcal{F}_w^H(V_u) U + U^\dagger \big(\mathcal{F}_w^H(Q_u) - Q_u\big) U + \big(U^\dagger Q_u U - Q_u\big).$$ -/
theorem bochnerFilteredSiteOp_eq_conj_unitary {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H H' U V_u Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {w : ℝ → ℂ}
    (hH' : H' = U† * H * U)
    (hUU_adj : U * U† = 1) (hU_adj_U : U† * U = 1)
    (h_int_V : Integrable (fun t : ℝ => w t • heisenbergFlow H t V_u))
    (h_int_Q : Integrable (fun t : ℝ => w t • heisenbergFlow H t Q_u)) :
    bochnerFilteredSiteOp H' U w V_u Q_u =
      U† * bochnerFilteredOp H w V_u * U +
      U† * (bochnerFilteredOp H w Q_u - Q_u) * U +
      (U† * Q_u * U - Q_u) := by
  unfold bochnerFilteredSiteOp
  rw [hH', bochnerFilteredOp_conj_unitary hUU_adj hU_adj_U H w V_u h_int_V,
    bochnerFilteredOp_conj_unitary hUU_adj hU_adj_U H w Q_u h_int_Q,
    mul_sub (U†) (bochnerFilteredOp H w Q_u) Q_u, sub_mul _ (U† * Q_u) U]
  abel

/-- **Commuting-Check Heisenberg Derivative Reduction (`hasDerivAt_heisenbergFlow_of_commute_left`)**:
    When $Q_u$ commutes with the unperturbed Hamiltonian $H_0$, its Heisenberg flow under
    $H = H_0 + V_{\mathrm{tot}}$ has derivative driven solely by $[V_{\mathrm{tot}}, Q_u]$:
    $$\frac{d}{dt} \tau_t^{H_0 + V_{\mathrm{tot}}}(Q_u)
      = i \, \tau_t^{H_0 + V_{\mathrm{tot}}}\big([V_{\mathrm{tot}}, Q_u]\big).$$ -/
theorem hasDerivAt_heisenbergFlow_of_commute_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation Q_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : Commute H0 Q_u) (t : ℝ) :
    HasDerivAt (fun τ => heisenbergFlow (H0 + totalPerturbation) τ Q_u)
      ((Complex.I : ℂ) • heisenbergFlow (H0 + totalPerturbation) t (opCommutator totalPerturbation Q_u)) t := by
  let H := H0 + totalPerturbation
  have hd := hasDerivAt_heisenbergFlow H Q_u t
  have hU_pos : H * timeEvolutionOp H t = timeEvolutionOp H t * H :=
    (commute_smul_left_clm (Commute.refl H) (Complex.I * (t : ℂ))).exp_left.symm.eq
  have hU_neg : timeEvolutionOp H (-t) * H = H * timeEvolutionOp H (-t) :=
    (commute_smul_left_clm (Commute.refl H) (Complex.I * ((-t : ℝ) : ℂ))).exp_left.eq
  have h_comm_flow : opCommutator H (heisenbergFlow H t Q_u) =
      heisenbergFlow H t (opCommutator H Q_u) := by
    unfold opCommutator heisenbergFlow
    rw [mul_sub (timeEvolutionOp H t) (H * Q_u) (Q_u * H),
      sub_mul _ (timeEvolutionOp H t * (Q_u * H)) (timeEvolutionOp H (-t))]
    have hL : H * (timeEvolutionOp H t * Q_u * timeEvolutionOp H (-t)) =
        timeEvolutionOp H t * (H * Q_u) * timeEvolutionOp H (-t) := by
      calc H * (timeEvolutionOp H t * Q_u * timeEvolutionOp H (-t))
        _ = (H * timeEvolutionOp H t) * Q_u * timeEvolutionOp H (-t) := by simp only [mul_assoc]
        _ = timeEvolutionOp H t * (H * Q_u) * timeEvolutionOp H (-t) := by
          rw [hU_pos]; simp only [mul_assoc]
    have hR : (timeEvolutionOp H t * Q_u * timeEvolutionOp H (-t)) * H =
        timeEvolutionOp H t * (Q_u * H) * timeEvolutionOp H (-t) := by
      calc (timeEvolutionOp H t * Q_u * timeEvolutionOp H (-t)) * H
        _ = timeEvolutionOp H t * Q_u * (timeEvolutionOp H (-t) * H) := by simp only [mul_assoc]
        _ = timeEvolutionOp H t * (Q_u * H) * timeEvolutionOp H (-t) := by
          rw [hU_neg]; simp only [mul_assoc]
    rw [hL, hR]
  have h_opComm : opCommutator H Q_u = opCommutator totalPerturbation Q_u := by
    dsimp [H]; unfold opCommutator
    have h0 : H0 * Q_u - Q_u * H0 = 0 := sub_eq_zero.mpr h_comm.eq
    calc (H0 + totalPerturbation) * Q_u - Q_u * (H0 + totalPerturbation)
      _ = (H0 * Q_u - Q_u * H0) + (totalPerturbation * Q_u - Q_u * totalPerturbation) := by
        rw [add_mul, mul_add]; abel
      _ = totalPerturbation * Q_u - Q_u * totalPerturbation := by rw [h0, zero_add]
  have h_eq : (Complex.I : ℂ) • opCommutator H (heisenbergFlow H t Q_u) =
      (Complex.I : ℂ) • heisenbergFlow H t (opCommutator totalPerturbation Q_u) := by
    rw [h_comm_flow, h_opComm]
  exact hd.congr_deriv h_eq

end
