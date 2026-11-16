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
import Proofs.LiebRobinson.BochnerQuasiLocality

/-!
# Operator Exponential Eigenprojector Identities and Two-Block Spectral Decomposition

Establishes power-series identities for continuous linear operator exponentials (`clm_exp_eq_tsum`, `clm_exp_smul_mul_proj`, `clm_proj_mul_exp_smul`) and proves eigenprojector phase evolution under `timeEvolutionOp` (`timeEvolutionOp_mul_proj_of_eigenvalue`). Derives two-block spectral decomposition from off-diagonal block annihilation (`ring_spectral_decomp_of_offDiag_zero`, `clm_sandwich_integral_smul`).

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Bravyi–Hastings (2011), Communications in Mathematical Physics 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Ground-Space Exponential Eigenvalue Reduction
-/

/-- Right-eigenprojection power identity: if $A P = a \bullet P$, then $A^n P = a^n \bullet P$. -/
lemma ring_pow_mul_of_mul_eq_smul {R : Type*} [Ring R] [Module ℂ R]
    [SMulCommClass ℂ R R] [IsScalarTower ℂ R R]
    {A P : R} {a : ℂ} (hAP : A * P = a • P) (n : ℕ) :
    A ^ n * P = (a ^ n) • P := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, one_smul]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, hAP, smul_smul, ← pow_succ]

/-- Left-eigenprojection power identity: if $P A = a \bullet P$, then $P A^n = a^n \bullet P$. -/
lemma ring_mul_pow_of_mul_eq_smul {R : Type*} [Ring R] [Module ℂ R]
    [SMulCommClass ℂ R R] [IsScalarTower ℂ R R]
    {A P : R} {a : ℂ} (hPA : P * A = a • P) (n : ℕ) :
    P * A ^ n = (a ^ n) • P := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, mul_one, one_smul]
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, hPA, smul_smul, ← pow_succ]

/-- Power-series expansion of the Banach-algebra exponential $\exp(A) = \sum_{n=0}^\infty (n!)^{-1} A^n$. -/
lemma clm_exp_eq_tsum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) :
    NormedSpace.exp A = ∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • A ^ n :=
  congrFun (NormedSpace.exp_eq_tsum ℂ) A

/-- Summability of the exponential power series $\sum_{n=0}^\infty (n!)^{-1} A^n$ on $E \to_L[\mathbb{C}] E$. -/
lemma clm_expSeries_summable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) :
    Summable (fun n : ℕ => ((Nat.factorial n : ℂ)⁻¹) • A ^ n) :=
  NormedSpace.expSeries_summable_of_mem_ball' (𝕂 := ℂ) A
    ((NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _)

/-- If $A^n P = B^n P$ for all $n \in \mathbb{N}$, then $\exp(A) P = \exp(B) P$. -/
lemma clm_exp_mul_eq_of_pow_mul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A B P : E →L[ℂ] E} (h_pow : ∀ n : ℕ, A ^ n * P = B ^ n * P) :
    NormedSpace.exp A * P = NormedSpace.exp B * P := by
  let R_P : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    (ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip P
  have h_term : ∀ n : ℕ,
      R_P (((Nat.factorial n : ℂ)⁻¹) • A ^ n) =
      R_P (((Nat.factorial n : ℂ)⁻¹) • B ^ n) := by
    intro n
    rw [R_P.map_smul, R_P.map_smul]
    exact congrArg (((Nat.factorial n : ℂ)⁻¹) • ·) (h_pow n)
  calc NormedSpace.exp A * P
    _ = R_P (NormedSpace.exp A) := rfl
    _ = R_P (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • A ^ n) := by
      rw [clm_exp_eq_tsum A]
    _ = ∑' n : ℕ, R_P (((Nat.factorial n : ℂ)⁻¹) • A ^ n) :=
      R_P.map_tsum (clm_expSeries_summable A)
    _ = ∑' n : ℕ, R_P (((Nat.factorial n : ℂ)⁻¹) • B ^ n) :=
      tsum_congr h_term
    _ = R_P (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • B ^ n) :=
      (R_P.map_tsum (clm_expSeries_summable B)).symm
    _ = R_P (NormedSpace.exp B) := by
      rw [← clm_exp_eq_tsum B]
    _ = NormedSpace.exp B * P := rfl

/-- If $P A^n = P B^n$ for all $n \in \mathbb{N}$, then $P \exp(A) = P \exp(B)$. -/
lemma clm_mul_exp_eq_of_mul_pow_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A B P : E →L[ℂ] E} (h_pow : ∀ n : ℕ, P * A ^ n = P * B ^ n) :
    P * NormedSpace.exp A = P * NormedSpace.exp B := by
  let L_P : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    ContinuousLinearMap.mul ℂ (E →L[ℂ] E) P
  have h_term : ∀ n : ℕ,
      L_P (((Nat.factorial n : ℂ)⁻¹) • A ^ n) =
      L_P (((Nat.factorial n : ℂ)⁻¹) • B ^ n) := by
    intro n
    rw [L_P.map_smul, L_P.map_smul]
    exact congrArg (((Nat.factorial n : ℂ)⁻¹) • ·) (h_pow n)
  calc P * NormedSpace.exp A
    _ = L_P (NormedSpace.exp A) := rfl
    _ = L_P (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • A ^ n) := by
      rw [clm_exp_eq_tsum A]
    _ = ∑' n : ℕ, L_P (((Nat.factorial n : ℂ)⁻¹) • A ^ n) :=
      L_P.map_tsum (clm_expSeries_summable A)
    _ = ∑' n : ℕ, L_P (((Nat.factorial n : ℂ)⁻¹) • B ^ n) :=
      tsum_congr h_term
    _ = L_P (∑' n : ℕ, ((Nat.factorial n : ℂ)⁻¹) • B ^ n) :=
      (L_P.map_tsum (clm_expSeries_summable B)).symm
    _ = L_P (NormedSpace.exp B) := by
      rw [← clm_exp_eq_tsum B]
    _ = P * NormedSpace.exp B := rfl

/-- If $H' P = e_0 \bullet P$, then $\exp(c \bullet H') P = \exp((c e_0) \bullet 1) P$. -/
lemma clm_exp_smul_mul_proj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H' P : E →L[ℂ] E} {e0 : ℂ} (hHP : H' * P = e0 • P) (c : ℂ) :
    NormedSpace.exp (c • H') * P = NormedSpace.exp ((c * e0) • (1 : E →L[ℂ] E)) * P := by
  have hA : (c • H') * P = (c * e0) • P := by
    rw [smul_mul_assoc, hHP, smul_smul]
  have hB : ((c * e0) • (1 : E →L[ℂ] E)) * P = (c * e0) • P := by
    rw [smul_mul_assoc, one_mul]
  apply clm_exp_mul_eq_of_pow_mul_eq
  intro n
  rw [ring_pow_mul_of_mul_eq_smul hA n, ring_pow_mul_of_mul_eq_smul hB n]

/-- If $P H' = e_0 \bullet P$, then $P \exp(c \bullet H') = P \exp((c e_0) \bullet 1)$. -/
lemma clm_proj_mul_exp_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H' P : E →L[ℂ] E} {e0 : ℂ} (hPH : P * H' = e0 • P) (c : ℂ) :
    P * NormedSpace.exp (c • H') = P * NormedSpace.exp ((c * e0) • (1 : E →L[ℂ] E)) := by
  have hA : P * (c • H') = (c * e0) • P := by
    rw [mul_smul_comm, hPH, smul_smul]
  have hB : P * ((c * e0) • (1 : E →L[ℂ] E)) = (c * e0) • P := by
    rw [mul_smul_comm, mul_one]
  apply clm_mul_exp_eq_of_mul_pow_eq
  intro n
  rw [ring_mul_pow_of_mul_eq_smul hA n, ring_mul_pow_of_mul_eq_smul hB n]

/-- The scalar exponential $\exp(z \bullet 1)$ commutes with every operator $Z$. -/
lemma commute_exp_smul_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (z : ℂ) (Z : E →L[ℂ] E) :
    Commute (NormedSpace.exp (z • (1 : E →L[ℂ] E))) Z :=
  (commute_smul_left_clm (Commute.one_left Z) z).exp_left

/-- Scalar exponential inversion $\exp(z \bullet 1) \exp((-z) \bullet 1) = 1$. -/
lemma exp_smul_one_mul_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (z : ℂ) :
    NormedSpace.exp (z • (1 : E →L[ℂ] E)) * NormedSpace.exp ((-z) • (1 : E →L[ℂ] E)) = 1 := by
  have h_comm : Commute (z • (1 : E →L[ℂ] E)) ((-z) • (1 : E →L[ℂ] E)) :=
    commute_smul_left_clm (Commute.one_left ((-z) • (1 : E →L[ℂ] E))) z
  rw [← clm_exp_add_of_commute h_comm, ← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]

/-- If $H' P = E_0 P$ and $P^2 = P$, then $\exp(i H' t) P = \exp(i E_0 t) P$ and
    $P \exp(-i H' t) = \exp(-i E_0 t) P$. -/
lemma timeEvolutionOp_mul_proj_of_eigenvalue {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {E0 : ℝ} (_hP : IsStarProjection P)
    (hHP : H' * P = (E0 : ℂ) • P) (hPH : P * H' = (E0 : ℂ) • P) (t : ℝ) :
    timeEvolutionOp H' t * P =
      NormedSpace.exp ((Complex.I * (t : ℂ) * (E0 : ℂ)) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) * P ∧
    P * timeEvolutionOp H' (-t) =
      P * NormedSpace.exp ((-(Complex.I * (t : ℂ) * (E0 : ℂ))) •
        (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) := by
  constructor
  · exact clm_exp_smul_mul_proj hHP (Complex.I * (t : ℂ))
  · rw [timeEvolutionOp_neg_eq, clm_proj_mul_exp_smul hPH (-(Complex.I * (t : ℂ))), neg_mul]

/-!
## 2. Off-Diagonal Annihilation and Two-Block Spectral Decomposition
-/

/-- Diagonal block invariance under Heisenberg evolution when $P$ is an eigenprojection of $H'$. -/
lemma monoid_diag_flow_id {R : Type*} [Monoid R] {P U_pos U_neg e_pos e_neg X : R}
    (hPU : P * U_pos = e_pos * P) (hUP : U_neg * P = P * e_neg)
    (hComm : Commute e_neg (P * X * P)) (he : e_pos * e_neg = 1) :
    P * (U_pos * X * U_neg) * P = P * X * P := by
  calc P * (U_pos * X * U_neg) * P
    _ = (P * U_pos) * X * (U_neg * P) := by simp only [mul_assoc]
    _ = (e_pos * P) * X * (P * e_neg) := by rw [hPU, hUP]
    _ = e_pos * ((P * X * P) * e_neg) := by simp only [mul_assoc]
    _ = e_pos * (e_neg * (P * X * P)) := by rw [hComm.symm.eq]
    _ = (e_pos * e_neg) * (P * X * P) := by rw [← mul_assoc]
    _ = P * X * P := by rw [he, one_mul]

/-- Off-diagonal block factorization $A (U_+ X U_-) B = e_+ (A X B) e_-$ under intertwining relations. -/
lemma monoid_sandwich_rew {R : Type*} [Monoid R] {A B U_pos U_neg e_pos e_neg X : R}
    (hAU : A * U_pos = e_pos * A) (hUB : U_neg * B = B * e_neg) :
    A * (U_pos * X * U_neg) * B = e_pos * (A * X * B) * e_neg := by
  calc A * (U_pos * X * U_neg) * B
    _ = (A * U_pos) * X * (U_neg * B) := by simp only [mul_assoc]
    _ = (e_pos * A) * X * (B * e_neg) := by rw [hAU, hUB]
    _ = e_pos * (A * X * B) * e_neg := by simp only [mul_assoc]

/-- Any operator $Y$ whose off-diagonal blocks $P Y (1 - P)$ and $(1 - P) Y P$ vanish equals
    $P Y P + (1 - P) Y (1 - P)$ and commutes with the idempotent $P$. -/
lemma ring_spectral_decomp_of_offDiag_zero {R : Type*} [Ring R] {P Y : R}
    (hP_idem : P * P = P)
    (h_off_R : P * Y * (1 - P) = 0)
    (h_off_L : (1 - P) * Y * P = 0) :
    (P * Y * P + (1 - P) * Y * (1 - P) = Y) ∧ Commute Y P := by
  have h_1P_mul_P : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP_idem, sub_self]
  have h_P_mul_1P : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP_idem, sub_self]
  have h_eq : P * Y * P + (1 - P) * Y * (1 - P) = Y := by
    calc P * Y * P + (1 - P) * Y * (1 - P)
      _ = (P * Y * P + P * Y * (1 - P)) + ((1 - P) * Y * P + (1 - P) * Y * (1 - P)) := by
        rw [h_off_R, h_off_L, add_zero, zero_add]
      _ = P * Y * (P + (1 - P)) + (1 - P) * Y * (P + (1 - P)) := by
        rw [← mul_add, ← mul_add]
      _ = P * Y * 1 + (1 - P) * Y * 1 := by rw [add_sub_cancel]
      _ = (P + (1 - P)) * Y := by rw [mul_one, mul_one, ← add_mul]
      _ = 1 * Y := by rw [add_sub_cancel]
      _ = Y := one_mul Y
  have h_comm : Commute (P * Y * P + (1 - P) * Y * (1 - P)) P := by
    rw [commute_iff_eq, add_mul, mul_add,
      mul_assoc (P * Y) P P, hP_idem,
      mul_assoc ((1 - P) * Y) (1 - P) P, h_1P_mul_P, mul_zero, add_zero,
      ← mul_assoc P (P * Y) P, ← mul_assoc P P Y, hP_idem,
      ← mul_assoc P ((1 - P) * Y) (1 - P),
      ← mul_assoc P (1 - P) Y, h_P_mul_1P, zero_mul, zero_mul, add_zero]
  rw [h_eq] at h_comm
  exact ⟨h_eq, h_comm⟩

/-- Continuous linear sandwich multiplication commutes with Bochner integration:
    $A \big(\int w(t) g(t)\,dt\big) B = \int w(t) (A g(t) B)\,dt$. -/
lemma clm_sandwich_integral_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A B : E →L[ℂ] E) (w : ℝ → ℂ) (g : ℝ → (E →L[ℂ] E))
    (hf : Integrable (fun t : ℝ => w t • g t)) :
    A * (∫ t : ℝ, w t • g t) * B = ∫ t : ℝ, w t • (A * g t * B) := by
  let L : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
    ((ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip B).comp
      (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) A)
  have h1 : L (∫ t : ℝ, w t • g t) = ∫ t : ℝ, L (w t • g t) :=
    (L.integral_comp_comm hf).symm
  have h2 : (fun t : ℝ => L (w t • g t)) = (fun t : ℝ => w t • (A * g t * B)) := by
    funext t
    exact L.map_smul (w t) (g t)
  rw [← h2]
  exact h1
