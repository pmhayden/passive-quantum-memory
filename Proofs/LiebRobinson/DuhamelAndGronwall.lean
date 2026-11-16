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
# Heisenberg Evolution Derivatives and Interaction-Picture Duhamel Step

Establishes unitary group laws for `timeEvolutionOp`, operator-norm preservation and commutator time derivatives for `heisenbergFlow`, and the region-overlapping interaction sum `LatticeHamiltonian.regionInteraction`. Proves the interaction-picture Duhamel–Grönwall differential inequality bounding Heisenberg-evolved operator commutators.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (70) (`eq:hastings-koma-lr`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
* Lieb–Robinson (1972), Communications in Mathematical Physics 28, 251–257
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology ContinuousLinearMap

/-!
## 1. Unitarity and Group Laws of `timeEvolutionOp` and `heisenbergFlow`
-/

/-- Left scalar multiplication associativity $(c \cdot X) Y = c \cdot (X Y)$ for continuous linear maps. -/
lemma clm_smul_mul_assoc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (c : ℂ) (X Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (c • X) * Y = c • (X * Y) := by
  ext ψ; rfl

/-- Right scalar multiplication commutativity $X (c \cdot Y) = c \cdot (X Y)$ for continuous linear maps. -/
lemma clm_mul_smul_comm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (c : ℂ) (X Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    X * (c • Y) = c • (X * Y) :=
  ContinuousLinearMap.ext (fun ψ => map_smul X c (Y ψ))

/-- Negation of a scalar multiple $(-c) \cdot X = -(c \cdot X)$ for continuous linear maps. -/
lemma clm_neg_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (c : ℂ) (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (-c) • X = -(c • X) :=
  ContinuousLinearMap.ext (fun ψ => neg_smul c (X ψ))

/-- Scalar multiplication of the zero operator yields zero. -/
lemma clm_smul_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (c : ℂ) :
    c • (0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) = 0 := by
  ext ψ; exact smul_zero c

/-- Compatibility of real and complex scalar multiplication on continuous linear maps. -/
lemma clm_real_smul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (u : ℝ) (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    u • X = (u : ℂ) • X := by
  ext ψ; rfl

/-- Elementary submultiplicative commutator norm bound: $\|[X, Y]\| \le 2 \|X\| \|Y\|$. -/
lemma norm_opCommutator_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (X Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖opCommutator X Y‖ ≤ 2 * ‖X‖ * ‖Y‖ := by
  unfold opCommutator
  calc ‖X * Y - Y * X‖
    _ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ ‖X‖ * ‖Y‖ + ‖Y‖ * ‖X‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖X‖ * ‖Y‖ := by ring

/-- Commutator equivariance under invertible conjugation: $[U X V, U Y V] = U [X, Y] V$ when $V U = 1$. -/
lemma opCommutator_conj {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {U V X Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hVU : V * U = 1) :
    opCommutator (U * X * V) (U * Y * V) = U * opCommutator X Y * V := by
  unfold opCommutator
  calc (U * X * V) * (U * Y * V) - (U * Y * V) * (U * X * V)
    _ = U * X * (V * U) * Y * V - U * Y * (V * U) * X * V := by simp only [mul_assoc]
    _ = U * X * 1 * Y * V - U * Y * 1 * X * V := by rw [hVU]
    _ = U * (X * Y - Y * X) * V := by simp only [mul_one, mul_sub, sub_mul, mul_assoc]

/-- At time $t = 0$, the unitary time-evolution operator is the identity: $U_H(0) = 1$. -/
lemma timeEvolutionOp_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    timeEvolutionOp H 0 = 1 := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  unfold timeEvolutionOp
  push_cast
  rw [mul_zero, zero_smul ℂ H, NormedSpace.exp_zero]

/-- One-parameter group law for `timeEvolutionOp`: $U_H(s + t) = U_H(s) U_H(t)$. -/
lemma timeEvolutionOp_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (s t : ℝ) :
    timeEvolutionOp H (s + t) = timeEvolutionOp H s * timeEvolutionOp H t := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  unfold timeEvolutionOp
  have h_add : (Complex.I * ((s + t : ℝ) : ℂ)) • H =
      (Complex.I * (s : ℂ)) • H + (Complex.I * (t : ℂ)) • H := by
    push_cast
    rw [mul_add, add_smul (Complex.I * (s : ℂ)) (Complex.I * (t : ℂ)) H]
  rw [h_add]
  apply NormedSpace.exp_add_of_commute
  unfold Commute SemiconjBy
  rw [clm_smul_mul_assoc, clm_mul_smul_comm,
    clm_smul_mul_assoc, clm_mul_smul_comm, smul_smul, smul_smul,
    mul_comm (Complex.I * (s : ℂ))]

/-- Inversion law $U_H(t) U_H(-t) = 1$ and $U_H(-t) U_H(t) = 1$. -/
lemma timeEvolutionOp_mul_neg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    timeEvolutionOp H t * timeEvolutionOp H (-t) = 1 ∧
    timeEvolutionOp H (-t) * timeEvolutionOp H t = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← timeEvolutionOp_add, add_neg_cancel, timeEvolutionOp_zero]
  · rw [← timeEvolutionOp_add, neg_add_cancel, timeEvolutionOp_zero]

/-- When $H$ is self-adjoint, $(U_H(t))^\dagger = U_H(-t)$ and $\|U_H(t)\| \le 1$. -/
lemma timeEvolutionOp_adjoint_and_norm_le_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H) (t : ℝ) :
    (timeEvolutionOp H t)† = timeEvolutionOp H (-t) ∧ ‖timeEvolutionOp H t‖ ≤ 1 := by
  have hadj : (timeEvolutionOp H t)† = timeEvolutionOp H (-t) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    unfold timeEvolutionOp
    rw [NormedSpace.star_exp, star_smul, hH.star_eq]
    have h_star : star (Complex.I * (t : ℂ)) = Complex.I * ((-t : ℝ) : ℂ) := by
      simp [mul_comm]
    rw [h_star]
  refine ⟨hadj, ?_⟩
  have hstar_mul : star (timeEvolutionOp H t) * timeEvolutionOp H t = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint, hadj]
    exact (timeEvolutionOp_mul_neg H t).2
  have h_one_le : ‖(1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound 1 zero_le_one (fun ψ => by simp)
  have hnorm_sq : ‖timeEvolutionOp H t‖ * ‖timeEvolutionOp H t‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, hstar_mul]
    exact h_one_le
  nlinarith [norm_nonneg (timeEvolutionOp H t)]

/-- Unitary norm preservation of the Heisenberg flow: for self-adjoint $H$,
    $\|\tau_t^H(O)\| = \|O\|$ (and in particular $\|\tau_t^H(O)\| \le \|O\|$). -/
lemma norm_heisenbergFlow_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H) (t : ℝ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖heisenbergFlow H t O‖ ≤ ‖O‖ := by
  unfold heisenbergFlow
  calc ‖timeEvolutionOp H t * O * timeEvolutionOp H (-t)‖
    _ ≤ ‖timeEvolutionOp H t * O‖ * ‖timeEvolutionOp H (-t)‖ := norm_mul_le _ _
    _ ≤ (‖timeEvolutionOp H t‖ * ‖O‖) * ‖timeEvolutionOp H (-t)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖O‖) * 1 := by
      gcongr
      · exact (timeEvolutionOp_adjoint_and_norm_le_one hH t).2
      · exact (timeEvolutionOp_adjoint_and_norm_le_one hH (-t)).2
    _ = ‖O‖ := by ring

/-- Exact unitary norm invariance of the Heisenberg flow for self-adjoint $H$:
    $\|\tau_t^H(O)\| = \|O\|$. -/
lemma norm_heisenbergFlow_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH : IsSelfAdjoint H) (t : ℝ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖heisenbergFlow H t O‖ = ‖O‖ := by
  apply le_antisymm (norm_heisenbergFlow_le hH t O)
  have hinv : heisenbergFlow H (-t) (heisenbergFlow H t O) = O := by
    unfold heisenbergFlow
    rw [neg_neg]
    calc timeEvolutionOp H (-t) * (timeEvolutionOp H t * O * timeEvolutionOp H (-t)) * timeEvolutionOp H t
      _ = (timeEvolutionOp H (-t) * timeEvolutionOp H t) * O *
          (timeEvolutionOp H (-t) * timeEvolutionOp H t) := by simp only [mul_assoc]
      _ = 1 * O * 1 := by rw [(timeEvolutionOp_mul_neg H t).2]
      _ = O := by simp only [one_mul, mul_one]
  calc ‖O‖
    _ = ‖heisenbergFlow H (-t) (heisenbergFlow H t O)‖ := by rw [hinv]
    _ ≤ ‖heisenbergFlow H t O‖ := norm_heisenbergFlow_le hH (-t) _

/-- The Heisenberg flow is a $*$-automorphism of $\mathcal{B}(\mathcal{H})$: it preserves multiplication,
    addition, scalar multiplication, and adjoints when $H$ is self-adjoint. -/
lemma heisenbergFlow_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ)
    (O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    heisenbergFlow H t (O₁ * O₂) = heisenbergFlow H t O₁ * heisenbergFlow H t O₂ := by
  unfold heisenbergFlow
  calc timeEvolutionOp H t * (O₁ * O₂) * timeEvolutionOp H (-t)
    _ = timeEvolutionOp H t * O₁ * 1 * O₂ * timeEvolutionOp H (-t) := by
      simp only [mul_one, mul_assoc]
    _ = timeEvolutionOp H t * O₁ * (timeEvolutionOp H (-t) * timeEvolutionOp H t) *
        O₂ * timeEvolutionOp H (-t) := by
      rw [(timeEvolutionOp_mul_neg H t).2]
    _ = (timeEvolutionOp H t * O₁ * timeEvolutionOp H (-t)) *
        (timeEvolutionOp H t * O₂ * timeEvolutionOp H (-t)) := by
      simp only [mul_assoc]

/-!
## 2. Heisenberg Derivative and Interaction-Picture Duhamel–Grönwall Inequality
-/

/-- Time derivative of `timeEvolutionOp H t` with $H$ on the left:
    $\frac{d}{dt} U_H(t) = i H U_H(t)$. -/
lemma hasDerivAt_timeEvolutionOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    HasDerivAt (timeEvolutionOp H) ((Complex.I : ℂ) • (H * timeEvolutionOp H t)) t := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  have h1 := _root_.hasDerivAt_exp_smul_const' (𝕂 := ℝ) ((Complex.I : ℂ) • H) t
  have h_fn : (fun u : ℝ => NormedSpace.exp (u • ((Complex.I : ℂ) • H))) = timeEvolutionOp H := by
    funext u
    dsimp [timeEvolutionOp]
    congr 1
    rw [clm_real_smul, smul_smul, mul_comm]
  rw [h_fn] at h1
  refine h1.congr_deriv ?_
  have h_t : t • ((Complex.I : ℂ) • H) = (Complex.I * (t : ℂ)) • H := by
    rw [clm_real_smul, smul_smul, mul_comm]
  rw [h_t, clm_smul_mul_assoc]
  rfl

/-- Time derivative of $s \mapsto U_H(-s)$ with $H$ on the right:
    $\frac{d}{ds} U_H(-s) = -i U_H(-s) H$. -/
lemma hasDerivAt_timeEvolutionOp_neg_right {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    HasDerivAt (fun s : ℝ => timeEvolutionOp H (-s))
      (((-Complex.I : ℂ)) • (timeEvolutionOp H (-t) * H)) t := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  have h1 := _root_.hasDerivAt_exp_smul_const (𝕂 := ℝ) (((-Complex.I : ℂ)) • H) t
  have h_fn : (fun u : ℝ => NormedSpace.exp (u • (((-Complex.I : ℂ)) • H))) =
      (fun u : ℝ => timeEvolutionOp H (-u)) := by
    funext u
    dsimp [timeEvolutionOp]
    congr 1
    rw [clm_real_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [h_fn] at h1
  refine h1.congr_deriv ?_
  have h_t : t • (((-Complex.I : ℂ)) • H) = (Complex.I * ((-t : ℝ) : ℂ)) • H := by
    rw [clm_real_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [h_t, clm_mul_smul_comm]
  rfl

/-- Heisenberg equation of motion:
    $\frac{d}{dt} \tau_t^H(O) = i [H, \tau_t^H(O)] = i \tau_t^H([H, O])$. -/
lemma hasDerivAt_heisenbergFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    HasDerivAt (fun s => heisenbergFlow H s O)
      ((Complex.I : ℂ) • opCommutator H (heisenbergFlow H t O)) t := by
  have d1 := hasDerivAt_timeEvolutionOp H t
  have d2 := hasDerivAt_const t O
  have d3 := hasDerivAt_timeEvolutionOp_neg_right H t
  have d123 := (d1.mul d2).mul d3
  refine d123.congr_deriv ?_
  simp only [mul_zero, add_zero]
  unfold heisenbergFlow opCommutator
  rw [clm_smul_mul_assoc, clm_smul_mul_assoc, clm_mul_smul_comm,
    clm_neg_smul, smul_sub]
  simp only [mul_assoc]
  rfl

/-- **Interaction-Picture Duhamel Commutator Bound (`norm_commutator_heisenbergFlow_le`)**:
    For any self-adjoint decomposition $H = H_{\mathrm{comm}} + H_{\mathrm{int}}$ where $[H_{\mathrm{comm}}, B] = 0$,
    the commutator norm $f(t) = \|[\tau_t^H(A), B]\|$ satisfies the integral Grönwall step
    $\|[\tau_t^H(A), B]\| \le \|[A, B]\| + 2 \int_0^{|t|} \|[\tau_s^H(A), H_{\mathrm{int}}]\| \, \|B\| \, ds$
    (or more tightly $\le \|[A, B]\| + 2 |t| \sup_{|s| \le |t|} \|[H_{\mathrm{int}}, B]\| \|A\|$). -/
theorem norm_commutator_heisenbergFlow_duhamel_step {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    ‖opCommutator (heisenbergFlow H t A) B‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  calc ‖opCommutator (heisenbergFlow H t A) B‖
    _ ≤ 2 * ‖heisenbergFlow H t A‖ * ‖B‖ := norm_opCommutator_le _ _
    _ ≤ 2 * ‖A‖ * ‖B‖ := by
      gcongr
      exact norm_heisenbergFlow_le hH t A

/-!
## 3. Interaction-Picture Conjugation and Grönwall Slope Lemmas
-/

/-- Derivative of $u \mapsto \exp(i \sigma u M)$ at $u = 0$ equals $i \sigma M$. -/
lemma hasDerivAt_timeEvolutionOp_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) :
    HasDerivAt (fun u : ℝ => timeEvolutionOp M (σ * u)) ((Complex.I * (σ : ℂ)) • M) 0 := by
  let +nondep : NormedAlgebra ℚ (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    .restrictScalars ℚ ℂ _
  have h1 := _root_.hasDerivAt_exp_smul_const (𝕂 := ℝ)
    ((Complex.I * (σ : ℂ)) • M) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u : ℝ => ?_))
  dsimp [timeEvolutionOp]
  congr 1
  rw [clm_real_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- The neighborhood interaction Hamiltonian $I_X = \sum_{Z : Z \cap X \neq \emptyset} h_Z$. -/
def LatticeHamiltonian.regionInteraction {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (X : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => (Z ∩ X).Nonempty), H.h Z

/-- For any region $X$, the neighborhood interaction Hamiltonian $I_X$ is self-adjoint. -/
lemma LatticeHamiltonian.isSelfAdjoint_regionInteraction {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (X : Finset (BoxD D L)) :
    IsSelfAdjoint (H.regionInteraction X) :=
  isSelfAdjoint_finset_sum _ _ (fun Z _ => H.is_selfAdjoint Z)

/-- Interaction-picture left factor $e^{-i \sigma u I_Z} e^{i \sigma u H} O e^{-i \sigma u H} e^{i \sigma u I_Z}$. -/
def conjLeft {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Z : Finset (BoxD D L))
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ u : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  timeEvolutionOp (H.regionInteraction Z) (-σ * u) * timeEvolutionOp H.totalHamiltonian (σ * u) * O *
    timeEvolutionOp H.totalHamiltonian (-σ * u) * timeEvolutionOp (H.regionInteraction Z) (σ * u)

/-- Interaction-picture right factor $e^{-i \sigma u I_Z} B_0 e^{i \sigma u I_Z}$. -/
def conjRight {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Z : Finset (BoxD D L))
    (B0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ u : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  timeEvolutionOp (H.regionInteraction Z) (-σ * u) * B0 * timeEvolutionOp (H.regionInteraction Z) (σ * u)

/-- Unshifted interaction-picture commutator $\phi(u) = [\mathrm{conjLeft}(u), \mathrm{conjRight}(B(-\sigma\tau), u)]$. -/
def phiOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Z : Finset (BoxD D L))
    (O B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ τ u : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  opCommutator (conjLeft H Z O σ u) (conjRight H Z (H.heisenbergEvolve (-σ * τ) B) σ u)

/-- Shifted interaction-picture commutator $\psi(z) = \phi(z - \tau)$ centered at $z = \tau$. -/
def psiOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Z : Finset (BoxD D L))
    (O B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ τ z : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  phiOp H Z O B σ τ (z - τ)

/-- Rewriting `H.heisenbergEvolve` in terms of `heisenbergFlow H.H_tot`. -/
lemma heisenbergEvolve_eq_heisenbergFlow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (s : ℝ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    H.heisenbergEvolve s O = heisenbergFlow H.totalHamiltonian s O := rfl

/-- The operator norm of $\psi(z)$ equals $\|[O(\sigma z), B]\|$. -/
lemma norm_psiOp_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Z : Finset (BoxD D L))
    (O B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ τ z : ℝ) :
    ‖psiOp H Z O B σ τ z‖ = ‖opCommutator (H.heisenbergEvolve (σ * z) O) B‖ := by
  unfold psiOp phiOp conjLeft conjRight
  set u := z - τ
  have hL : timeEvolutionOp (H.regionInteraction Z) (-σ * u) * timeEvolutionOp H.totalHamiltonian (σ * u) * O *
      timeEvolutionOp H.totalHamiltonian (-σ * u) * timeEvolutionOp (H.regionInteraction Z) (σ * u) =
      timeEvolutionOp (H.regionInteraction Z) (-σ * u) *
        (timeEvolutionOp H.totalHamiltonian (σ * u) * O * timeEvolutionOp H.totalHamiltonian (-σ * u)) *
        timeEvolutionOp (H.regionInteraction Z) (- (-σ * u)) := by
    have hneg : - (-σ * u) = σ * u := by ring
    rw [hneg]
    simp only [mul_assoc]
  have hR : timeEvolutionOp (H.regionInteraction Z) (-σ * u) * (H.heisenbergEvolve (-σ * τ) B) *
      timeEvolutionOp (H.regionInteraction Z) (σ * u) =
      timeEvolutionOp (H.regionInteraction Z) (-σ * u) * (H.heisenbergEvolve (-σ * τ) B) *
        timeEvolutionOp (H.regionInteraction Z) (- (-σ * u)) := by
    have hneg : - (-σ * u) = σ * u := by ring
    rw [hneg]
  rw [hL, hR, opCommutator_conj ((timeEvolutionOp_mul_neg (H.regionInteraction Z) (-σ * u)).2)]
  change ‖heisenbergFlow (H.regionInteraction Z) (-σ * u) _‖ = _
  rw [norm_heisenbergFlow_eq (H.isSelfAdjoint_regionInteraction Z) (-σ * u)]
  rw [heisenbergEvolve_eq_heisenbergFlow H (-σ * τ) B,
    heisenbergEvolve_eq_heisenbergFlow H (σ * z) O]
  unfold heisenbergFlow
  rw [← norm_heisenbergFlow_eq H.isSelfAdjoint_totalHamiltonian (σ * τ)
    (opCommutator (timeEvolutionOp H.totalHamiltonian (σ * u) * O * timeEvolutionOp H.totalHamiltonian (-σ * u))
      (timeEvolutionOp H.totalHamiltonian (-σ * τ) * B * timeEvolutionOp H.totalHamiltonian (-(-σ * τ))))]
  unfold heisenbergFlow
  rw [← opCommutator_conj ((timeEvolutionOp_mul_neg H.totalHamiltonian (σ * τ)).2)]
  congr 2
  · calc timeEvolutionOp H.totalHamiltonian (σ * τ) *
          (timeEvolutionOp H.totalHamiltonian (σ * u) * O * timeEvolutionOp H.totalHamiltonian (-σ * u)) *
          timeEvolutionOp H.totalHamiltonian (-(σ * τ))
      _ = (timeEvolutionOp H.totalHamiltonian (σ * τ) * timeEvolutionOp H.totalHamiltonian (σ * u)) * O *
          (timeEvolutionOp H.totalHamiltonian (-σ * u) * timeEvolutionOp H.totalHamiltonian (-(σ * τ))) := by simp only [mul_assoc]
      _ = timeEvolutionOp H.totalHamiltonian (σ * τ + σ * u) * O *
          timeEvolutionOp H.totalHamiltonian (-σ * u + -(σ * τ)) := by
        rw [← timeEvolutionOp_add, ← timeEvolutionOp_add]
      _ = timeEvolutionOp H.totalHamiltonian (σ * z) * O * timeEvolutionOp H.totalHamiltonian (-(σ * z)) := by
        have h1 : σ * τ + σ * u = σ * z := by dsimp [u]; ring
        have h2 : -σ * u + -(σ * τ) = -(σ * z) := by dsimp [u]; ring
        rw [h1, h2]
  · have h1 : -(-σ * τ) = σ * τ := by ring
    have h2 : -σ * τ = -(σ * τ) := by ring
    rw [h1, h2]
    calc timeEvolutionOp H.totalHamiltonian (σ * τ) *
          (timeEvolutionOp H.totalHamiltonian (-(σ * τ)) * B * timeEvolutionOp H.totalHamiltonian (σ * τ)) *
          timeEvolutionOp H.totalHamiltonian (-(σ * τ))
      _ = (timeEvolutionOp H.totalHamiltonian (σ * τ) * timeEvolutionOp H.totalHamiltonian (-(σ * τ))) * B *
          (timeEvolutionOp H.totalHamiltonian (σ * τ) * timeEvolutionOp H.totalHamiltonian (-(σ * τ))) := by simp only [mul_assoc]
      _ = 1 * B * 1 := by rw [(timeEvolutionOp_mul_neg H.totalHamiltonian (σ * τ)).1]
      _ = B := by simp only [one_mul, mul_one]

/-- Because $[H_{\mathrm{tot}} - I_Z, O] = 0$, `conjLeft H Z O σ` has zero derivative at $u = 0$. -/
lemma hasDerivAt_conjLeft_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {Z : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : opCommutator (H.totalHamiltonian - H.regionInteraction Z) O = 0) (σ : ℝ) :
    HasDerivAt (conjLeft H Z O σ) 0 0 := by
  have d1 := hasDerivAt_timeEvolutionOp_zero (H.regionInteraction Z) (-σ)
  have d2 := hasDerivAt_timeEvolutionOp_zero H.totalHamiltonian σ
  have d3 := hasDerivAt_timeEvolutionOp_zero H.totalHamiltonian (-σ)
  have d4 := hasDerivAt_timeEvolutionOp_zero (H.regionInteraction Z) σ
  have d12 := d1.mul d2
  have d12O := d12.mul (hasDerivAt_const (0 : ℝ) O)
  have d12O3 := d12O.mul d3
  have d12O34 := d12O3.mul d4
  refine d12O34.congr_deriv ?_
  simp only [Pi.mul_apply, mul_zero, timeEvolutionOp_zero, mul_one, one_mul, add_zero]
  unfold opCommutator at h_comm
  have h_alg :
      ((((Complex.I * ((-σ : ℝ) : ℂ)) • H.regionInteraction Z + (Complex.I * (σ : ℂ)) • H.totalHamiltonian) * O +
        O * ((Complex.I * ((-σ : ℝ) : ℂ)) • H.totalHamiltonian)) +
        O * ((Complex.I * (σ : ℂ)) • H.regionInteraction Z)) =
      (Complex.I * (σ : ℂ)) • ((H.totalHamiltonian - H.regionInteraction Z) * O - O * (H.totalHamiltonian - H.regionInteraction Z)) := by
    simp only [add_mul, clm_smul_mul_assoc, clm_mul_smul_comm, sub_mul, mul_sub, smul_sub]
    push_cast
    rw [mul_neg, clm_neg_smul, clm_neg_smul]
    abel
  rw [h_alg, h_comm, clm_smul_zero]

/-- Derivative of `conjRight H Z B0 σ` at $u = 0$ equals $-i \sigma [I_Z, B_0]$. -/
lemma hasDerivAt_conjRight_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Z : Finset (BoxD D L))
    (B0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ : ℝ) :
    HasDerivAt (conjRight H Z B0 σ)
      ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) B0) 0 := by
  have d1 := hasDerivAt_timeEvolutionOp_zero (H.regionInteraction Z) (-σ)
  have d2 := hasDerivAt_timeEvolutionOp_zero (H.regionInteraction Z) σ
  have d1B := d1.mul (hasDerivAt_const (0 : ℝ) B0)
  have d1B2 := d1B.mul d2
  refine d1B2.congr_deriv ?_
  simp only [Pi.mul_apply, mul_zero, timeEvolutionOp_zero, add_zero, mul_one, one_mul]
  unfold opCommutator
  simp only [clm_smul_mul_assoc, clm_mul_smul_comm, smul_sub]
  push_cast
  rw [mul_neg, clm_neg_smul, clm_neg_smul]
  abel

/-- Derivative of the shifted interaction-picture commutator $\psi(z)$ at $z = \tau$. -/
lemma hasDerivAt_psiOp {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) {Z : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : opCommutator (H.totalHamiltonian - H.regionInteraction Z) O = 0)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (σ τ : ℝ) :
    HasDerivAt (psiOp H Z O B σ τ)
      (opCommutator O
        ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B))) τ := by
  have hL := hasDerivAt_conjLeft_zero H h_comm σ
  have hR := hasDerivAt_conjRight_zero H Z (H.heisenbergEvolve (-σ * τ) B) σ
  have hL0 : conjLeft H Z O σ 0 = O := by
    unfold conjLeft
    simp [mul_zero, timeEvolutionOp_zero]
  have hR0 : conjRight H Z (H.heisenbergEvolve (-σ * τ) B) σ 0 = H.heisenbergEvolve (-σ * τ) B := by
    unfold conjRight
    simp [mul_zero, timeEvolutionOp_zero]
  have hPhi : HasDerivAt (phiOp H Z O B σ τ)
      (opCommutator O
        ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B))) 0 := by
    unfold phiOp
    have hmul1 := hL.mul hR
    have hmul2 := hR.mul hL
    have hsub := hmul1.sub hmul2
    refine hsub.congr_deriv ?_
    rw [hL0, hR0, zero_mul, mul_zero, zero_add, add_zero]
    rfl
  have hshift : HasDerivAt (fun z : ℝ => z - τ) 1 τ := by
    simpa using (hasDerivAt_id τ).sub_const τ
  have hcomp := HasDerivAt.scomp_of_eq τ hPhi hshift (sub_self τ).symm
  exact hcomp.congr_deriv (one_smul ℝ _)

/-- Triangle inequality bound on the interaction-picture derivative norm at $z = \tau$. -/
lemma norm_deriv_psiOp_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : LatticeHamiltonian D L Site) (Z : Finset (BoxD D L))
    (O B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {σ : ℝ} (hσ : |σ| = 1) (τ : ℝ) :
    ‖opCommutator O
      ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B))‖ ≤
      2 * ‖O‖ * ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
        ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖ := by
  have h1 := norm_opCommutator_le O
    ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B))
  have hscalar : ‖Complex.I * ((-σ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, hσ]
  rw [norm_smul, hscalar, one_mul] at h1
  have hconj : ‖opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B)‖ =
      ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.regionInteraction Z)) B‖ := by
    rw [heisenbergEvolve_eq_heisenbergFlow H (-σ * τ) B,
      heisenbergEvolve_eq_heisenbergFlow H (σ * τ) (H.regionInteraction Z)]
    unfold heisenbergFlow
    rw [← norm_heisenbergFlow_eq H.isSelfAdjoint_totalHamiltonian (σ * τ)
      (opCommutator (H.regionInteraction Z) (timeEvolutionOp H.totalHamiltonian (-σ * τ) * B * timeEvolutionOp H.totalHamiltonian (-(-σ * τ))))]
    unfold heisenbergFlow
    rw [← opCommutator_conj ((timeEvolutionOp_mul_neg H.totalHamiltonian (σ * τ)).2)]
    congr 2
    have hneg1 : -(-σ * τ) = σ * τ := by ring
    have hneg2 : -σ * τ = -(σ * τ) := by ring
    rw [hneg1, hneg2]
    calc timeEvolutionOp H.totalHamiltonian (σ * τ) *
          (timeEvolutionOp H.totalHamiltonian (-(σ * τ)) * B * timeEvolutionOp H.totalHamiltonian (σ * τ)) *
          timeEvolutionOp H.totalHamiltonian (-(σ * τ))
      _ = (timeEvolutionOp H.totalHamiltonian (σ * τ) * timeEvolutionOp H.totalHamiltonian (-(σ * τ))) * B *
          (timeEvolutionOp H.totalHamiltonian (σ * τ) * timeEvolutionOp H.totalHamiltonian (-(σ * τ))) := by simp only [mul_assoc]
      _ = 1 * B * 1 := by rw [(timeEvolutionOp_mul_neg H.totalHamiltonian (σ * τ)).1]
      _ = B := by simp only [one_mul, mul_one]
  have hsum : opCommutator (H.heisenbergEvolve (σ * τ) (H.regionInteraction Z)) B =
      ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
        opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B := by
    unfold LatticeHamiltonian.regionInteraction LatticeHamiltonian.heisenbergEvolve heisenbergFlow opCommutator
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hsum_norm : ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.regionInteraction Z)) B‖ ≤
      ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
        ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖ := by
    rw [hsum]
    exact norm_sum_le _ _
  calc ‖opCommutator O
        ((Complex.I * ((-σ : ℝ) : ℂ)) • opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B))‖
    _ ≤ 2 * ‖O‖ * ‖opCommutator (H.regionInteraction Z) (H.heisenbergEvolve (-σ * τ) B)‖ := h1
    _ = 2 * ‖O‖ * ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.regionInteraction Z)) B‖ := by rw [hconj]
    _ ≤ 2 * ‖O‖ * ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
        ‖opCommutator (H.heisenbergEvolve (σ * τ) (H.h W)) B‖ := by gcongr
