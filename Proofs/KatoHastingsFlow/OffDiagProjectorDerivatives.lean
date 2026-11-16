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

import Proofs.BandLimitedFilter.BandLimitedFilterSynthesis
import Proofs.QuasiLocalDressing.UnfilteredMultiScaleFlowWitnesses

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Off-Diagonal Two-Block Projections and Projector Derivative Identities

Establishes linearity, symmetry-sector commutation, and diagonal-block annihilation for `twoBlockOffDiagProj` (`twoBlockOffDiagProj_add`, `commute_twoBlockOffDiagProj`, `diag_blocks_twoBlockOffDiagProj_eq_zero`, `twoBlockOffDiagProj_commutator_eq_of_commute`), and proves the off-diagonal projector derivative identity (`proj_hasDerivAt_offDiag_id`) for differentiable idempotent projector families.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (75) (`eq:qac-generator-def`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Kato (1950), Journal of the Physical Society of Japan 5, 435–439
-/

/-!
## 1. Exact Spectral Block Off-Diagonal Identity for the BH11 Kato–Hastings Generator
-/

/-- Additivity of `twoBlockOffDiagProj P`. -/
theorem twoBlockOffDiagProj_add {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P X Y : E →L[ℂ] E) :
    twoBlockOffDiagProj P (X + Y) = twoBlockOffDiagProj P X + twoBlockOffDiagProj P Y := by
  dsimp [twoBlockOffDiagProj]
  rw [mul_add, add_mul, mul_add, add_mul]
  abel

/-- Subtraction linearity of `twoBlockOffDiagProj P`. -/
theorem twoBlockOffDiagProj_sub {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P X Y : E →L[ℂ] E) :
    twoBlockOffDiagProj P (X - Y) = twoBlockOffDiagProj P X - twoBlockOffDiagProj P Y := by
  have h_neg : twoBlockOffDiagProj P (-Y) = -twoBlockOffDiagProj P Y := by
    dsimp [twoBlockOffDiagProj]
    rw [mul_neg, neg_mul, mul_neg, neg_mul, neg_add]
  rw [sub_eq_add_neg, twoBlockOffDiagProj_add, h_neg, ← sub_eq_add_neg]

/-- Scalar-multiplication linearity of `twoBlockOffDiagProj P`. -/
theorem twoBlockOffDiagProj_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (P : E →L[ℂ] E) (c : ℂ) (X : E →L[ℂ] E) :
    twoBlockOffDiagProj P (c • X) = c • twoBlockOffDiagProj P X := by
  dsimp [twoBlockOffDiagProj]
  rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_add]

/-- Sector-symmetry preservation for `twoBlockOffDiagProj P X`: if both $P$ and $X$ commute with
    $\Pi_{\mathrm{sec}}$, then `twoBlockOffDiagProj P X` commutes with $\Pi_{\mathrm{sec}}$. -/
theorem commute_twoBlockOffDiagProj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P X Pi_sec : E →L[ℂ] E} (hP_sec : Commute P Pi_sec) (hX_sec : Commute X Pi_sec) :
    Commute (twoBlockOffDiagProj P X) Pi_sec := by
  have h1P_sec : Commute (1 - P) Pi_sec := (Commute.one_left Pi_sec).sub_left hP_sec
  exact ((hP_sec.mul_left hX_sec).mul_left h1P_sec).add_left
    ((h1P_sec.mul_left hX_sec).mul_left hP_sec)

/-- For an idempotent $P$ ($P^2 = P$), both diagonal blocks of `twoBlockOffDiagProj P X` vanish:
    $P (\mathrm{twoBlockOffDiagProj}\ P\ X) P = 0$ and $(1 - P)(\mathrm{twoBlockOffDiagProj}\ P\ X)(1 - P) = 0$. -/
theorem diag_blocks_twoBlockOffDiagProj_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP_idem : P * P = P) (X : E →L[ℂ] E) :
    P * twoBlockOffDiagProj P X * P = 0 ∧
    (1 - P) * twoBlockOffDiagProj P X * (1 - P) = 0 := by
  have h1P_P : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP_idem, sub_self]
  have hP_1P : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP_idem, sub_self]
  have h1 : P * (P * X * (1 - P)) * P = 0 := by
    calc P * (P * X * (1 - P)) * P
      _ = P * (P * X) * ((1 - P) * P) := by simp only [mul_assoc]
      _ = 0 := by rw [h1P_P, mul_zero]
  have h2 : P * ((1 - P) * X * P) * P = 0 := by
    calc P * ((1 - P) * X * P) * P
      _ = (P * (1 - P)) * X * P * P := by simp only [mul_assoc]
      _ = 0 := by rw [hP_1P, zero_mul, zero_mul, zero_mul]
  have h3 : (1 - P) * (P * X * (1 - P)) * (1 - P) = 0 := by
    calc (1 - P) * (P * X * (1 - P)) * (1 - P)
      _ = ((1 - P) * P) * X * (1 - P) * (1 - P) := by simp only [mul_assoc]
      _ = 0 := by rw [h1P_P, zero_mul, zero_mul, zero_mul]
  have h4 : (1 - P) * ((1 - P) * X * P) * (1 - P) = 0 := by
    calc (1 - P) * ((1 - P) * X * P) * (1 - P)
      _ = (1 - P) * ((1 - P) * X) * (P * (1 - P)) := by simp only [mul_assoc]
      _ = 0 := by rw [hP_1P, mul_zero]
  unfold twoBlockOffDiagProj
  refine ⟨?_, ?_⟩
  · rw [mul_add, add_mul, h1, h2, add_zero]
  · rw [mul_add, add_mul, h3, h4, add_zero]

/-- When `Commute H' P`, `twoBlockOffDiagProj P` commutes with the commutator `[ · , H']`:
    `twoBlockOffDiagProj P (D * H' - H' * D) = (twoBlockOffDiagProj P D) * H' - H' * (twoBlockOffDiagProj P D)`. -/
theorem twoBlockOffDiagProj_commutator_eq_of_commute {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P H' : E →L[ℂ] E} (hHP : Commute H' P) (D : E →L[ℂ] E) :
    twoBlockOffDiagProj P (D * H' - H' * D) =
      twoBlockOffDiagProj P D * H' - H' * twoBlockOffDiagProj P D := by
  have hH1P : Commute H' (1 - P) := (Commute.one_right H').sub_right hHP
  unfold twoBlockOffDiagProj
  have hR : P * (D * H' - H' * D) * (1 - P) =
      (P * D * (1 - P)) * H' - H' * (P * D * (1 - P)) := by
    rw [mul_sub P (D * H') (H' * D), sub_mul]
    have h1 : P * (D * H') * (1 - P) = (P * D * (1 - P)) * H' := by
      calc P * (D * H') * (1 - P)
        _ = P * D * (H' * (1 - P)) := by simp only [mul_assoc]
        _ = P * D * ((1 - P) * H') := by rw [hH1P.eq]
        _ = (P * D * (1 - P)) * H' := by simp only [mul_assoc]
    have h2 : P * (H' * D) * (1 - P) = H' * (P * D * (1 - P)) := by
      calc P * (H' * D) * (1 - P)
        _ = (P * H') * D * (1 - P) := by simp only [mul_assoc]
        _ = (H' * P) * D * (1 - P) := by rw [hHP.symm.eq]
        _ = H' * (P * D * (1 - P)) := by simp only [mul_assoc]
    rw [h1, h2]
  have hL : (1 - P) * (D * H' - H' * D) * P =
      ((1 - P) * D * P) * H' - H' * ((1 - P) * D * P) := by
    rw [mul_sub (1 - P) (D * H') (H' * D), sub_mul]
    have h1 : (1 - P) * (D * H') * P = ((1 - P) * D * P) * H' := by
      calc (1 - P) * (D * H') * P
        _ = (1 - P) * D * (H' * P) := by simp only [mul_assoc]
        _ = (1 - P) * D * (P * H') := by rw [hHP.eq]
        _ = ((1 - P) * D * P) * H' := by simp only [mul_assoc]
    have h2 : (1 - P) * (H' * D) * P = H' * ((1 - P) * D * P) := by
      calc (1 - P) * (H' * D) * P
        _ = ((1 - P) * H') * D * P := by simp only [mul_assoc]
        _ = (H' * (1 - P)) * D * P := by rw [hH1P.symm.eq]
        _ = H' * ((1 - P) * D * P) := by simp only [mul_assoc]
    rw [h1, h2]
  rw [hR, hL, add_mul, mul_add]
  abel

/-!
## 2. Kato Projector Derivative Identity & Sector Preservation along $H(s) = H_0 + s V_{\mathrm{tot}}$
-/

/-- **Differentiable Projection Off-Diagonal Derivative Identity (`proj_hasDerivAt_offDiag_id`)**:
    If $P : \mathbb{R} \to (E \to_L[\mathbb{C}] E)$ is a family of idempotents ($P(\tau)^2 = P(\tau)$)
    with derivative `HasDerivAt P dP_s s`, then $dP_s = dP_s P(s) + P(s) dP_s$, so both diagonal blocks
    vanish ($P(s) dP_s P(s) = 0$ and $(1 - P(s)) dP_s (1 - P(s)) = 0$), and the canonical Kato generator
    $\mathcal{D}_{\mathrm{Kato}}(s) := \mathrm{localKatoGeneratorTerm}\ (P(s))\ dP_s = i (P(s) dP_s - dP_s P(s))$
    satisfies the exact Kato ODE:
    $$\mathrm{HasDerivAt}\ P\ \big((i : \mathbb{C}) \bullet (\mathcal{D}_{\mathrm{Kato}}(s) P(s) - P(s) \mathcal{D}_{\mathrm{Kato}}(s))\big)\ s.$$ -/
theorem proj_hasDerivAt_offDiag_id {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : ℝ → (E →L[ℂ] E)) {dP_s : E →L[ℂ] E} {s : ℝ}
    (hP_idem : ∀ τ : ℝ, P τ * P τ = P τ)
    (hP_deriv : HasDerivAt P dP_s s) :
    let D_Kato := localKatoGeneratorTerm (P s) dP_s
    dP_s = dP_s * P s + P s * dP_s ∧
    P s * dP_s * P s = 0 ∧
    (1 - P s) * dP_s * (1 - P s) = 0 ∧
    dP_s = (1 - P s) * dP_s * P s + P s * dP_s * (1 - P s) ∧
    (Complex.I : ℂ) • (D_Kato * P s - P s * D_Kato) = dP_s ∧
    HasDerivAt P ((Complex.I : ℂ) • (D_Kato * P s - P s * D_Kato)) s := by
  intro D_Kato
  have h_prod : HasDerivAt (fun τ => P τ * P τ) (dP_s * P s + P s * dP_s) s :=
    hP_deriv.mul hP_deriv
  have h_eq_fn : (fun τ => P τ * P τ) = P := funext hP_idem
  rw [h_eq_fn] at h_prod
  have h_leib : dP_s = dP_s * P s + P s * dP_s := hP_deriv.unique h_prod
  have h_PDP : P s * dP_s * P s = 0 := by
    have h2 : P s * dP_s * P s + P s * dP_s * P s = P s * dP_s * P s + 0 := by
      calc P s * dP_s * P s + P s * dP_s * P s
        _ = P s * dP_s * (P s * P s) + (P s * P s) * dP_s * P s := by rw [hP_idem s]
        _ = P s * (dP_s * P s + P s * dP_s) * P s := by
          rw [mul_add, add_mul]
          simp only [mul_assoc]
        _ = P s * dP_s * P s + 0 := by rw [← h_leib, add_zero]
    exact add_left_cancel h2
  have h_1PD1P : (1 - P s) * dP_s * (1 - P s) = 0 := by
    have h1 : (1 - P s) * dP_s * (1 - P s) =
        dP_s - (dP_s * P s + P s * dP_s) + P s * dP_s * P s := by
      rw [sub_mul, one_mul, sub_mul, mul_sub, mul_one, mul_sub, mul_one]; abel
    rw [h1, ← h_leib, sub_self, zero_add, h_PDP]
  have h_off : dP_s = (1 - P s) * dP_s * P s + P s * dP_s * (1 - P s) := by
    calc dP_s
      _ = dP_s * P s + P s * dP_s := h_leib
      _ = (dP_s * P s - P s * dP_s * P s) + (P s * dP_s - P s * dP_s * P s) := by
        rw [h_PDP, sub_zero, sub_zero]
      _ = (1 - P s) * dP_s * P s + P s * dP_s * (1 - P s) := by
        rw [sub_mul, one_mul, sub_mul, mul_sub, mul_one]
  have h_kato_comm : (Complex.I : ℂ) • (D_Kato * P s - P s * D_Kato) = dP_s := by
    dsimp [D_Kato]
    rw [commutator_localKatoGeneratorTerm_eq_offDiag (hP_idem s), ← h_off]
  refine ⟨h_leib, h_PDP, h_1PD1P, h_off, h_kato_comm, ?_⟩
  rw [h_kato_comm]
  exact hP_deriv

end
