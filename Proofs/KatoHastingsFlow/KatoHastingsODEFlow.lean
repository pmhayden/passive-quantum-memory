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
# Unitarity, Subspace Tracking, and Duhamel Drift for Kato–Hastings Flows

Proves unitarity, exact ground-subspace tracking, and dressed Hamiltonian block-diagonalization (`kato_hastings_ode_flow`) for any `IsKatoHastingsFlowSystem`. Establishes the Duhamel commutator integral bound (`duhamel_conjugation_bound`) controlling operator drift along the unitary continuation flow.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`), Equation (77) (`eq:rotated-H-block-decomp`)
* Kato (1950), Journal of the Physical Society of Japan 5, 435–439
* Hastings–Wen (2005), Physical Review B 72, 045141
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Non-Autonomous Kato–Hastings ODE Unitarity and Subspace Tracking
-/

/-- Real scalar multiplication commutes with the continuous linear map adjoint (`StarModule ℝ`). -/
instance instStarModuleRealCLM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : StarModule ℝ (E →L[ℂ] E) where
  star_smul r A := by
    change star ((r : ℂ) • A) = (r : ℂ) • star A
    rw [star_smul, RCLike.star_def, Complex.conj_ofReal]

/-- Left scalar multiplication associativity `(c • A) * B = c • (A * B)` for continuous linear maps. -/
lemma clm_smul_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) (A B : E →L[ℂ] E) : (c • A) * B = c • (A * B) := by
  ext x; rfl

/-- Right scalar multiplication commutativity `A * (c • B) = c • (A * B)` for continuous linear maps. -/
lemma clm_mul_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) (A B : E →L[ℂ] E) : A * (c • B) = c • (A * B) := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul]

/-- Any differentiable curve in a normed space with identically zero derivative is constant. -/
lemma eq_of_hasDerivAt_zero {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → G} (hf : ∀ u : ℝ, HasDerivAt f 0 u) (s : ℝ) : f s = f 0 :=
  is_const_of_deriv_eq_zero (fun u => (hf u).differentiableAt) (fun u => (hf u).deriv) s 0

/-- On a finite-dimensional Hilbert space, a left-isometric operator $A^\dagger A = 1$ is unitary ($A A^\dagger = 1$). -/
lemma mul_adjoint_eq_one_of_adjoint_mul_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    {A : E →L[ℂ] E} (h : A† * A = 1) : A * A† = 1 := by
  have h_inj : Function.Injective A.toLinearMap := by
    intro x y hxy
    have hxy' : A x = A y := hxy
    have h1 : (A† * A) x = (A† * A) y := by
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
      exact congrArg (A†) hxy'
    rw [h, ContinuousLinearMap.one_apply, ContinuousLinearMap.one_apply] at h1
    exact h1
  have h_surj : Function.Surjective A.toLinearMap :=
    LinearMap.injective_iff_surjective.mp h_inj
  ext z
  rcases h_surj z with ⟨x, rfl⟩
  change (A * A†) (A x) = A x
  rw [← ContinuousLinearMap.mul_apply, mul_assoc, h, mul_one]

/-- Any isometric operator satisfying $A^\dagger A = 1$ has operator norm $\|A\| \le 1$ and $\|A^\dagger\| \le 1$. -/
lemma norm_le_one_of_adjoint_mul_self_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {A : E →L[ℂ] E} (h : A† * A = 1) :
    ‖A‖ ≤ 1 ∧ ‖A†‖ ≤ 1 := by
  have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h_sq : ‖A‖ ^ 2 ≤ 1 := by
    rw [sq, ← CStarRing.norm_star_mul_self, show star A = A† from rfl, h]
    exact h1
  have h_norm : ‖A‖ ≤ 1 := (sq_le_one_iff₀ (norm_nonneg A)).mp h_sq
  have h_adj_norm : ‖A†‖ = ‖A‖ :=
    (ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).norm_map A
  exact ⟨h_norm, h_adj_norm.le.trans h_norm⟩

/-- Submultiplicativity of the operator norm under contraction sandwiches $\|B X A\| \le \|X\|$ when $\|B\|, \|A\| \le 1$. -/
lemma norm_sandwich_le_of_norm_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {B X A : E →L[ℂ] E} (hB : ‖B‖ ≤ 1) (hA : ‖A‖ ≤ 1) :
    ‖B * X * A‖ ≤ ‖X‖ := by
  calc ‖B * X * A‖
    _ ≤ ‖B * X‖ * ‖A‖ := norm_mul_le (B * X) A
    _ ≤ (‖B‖ * ‖X‖) * ‖A‖ := mul_le_mul_of_nonneg_right (norm_mul_le B X) (norm_nonneg A)
    _ ≤ (1 * ‖X‖) * 1 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hB (norm_nonneg X)) hA
        (norm_nonneg A) (mul_nonneg zero_le_one (norm_nonneg X))
    _ = ‖X‖ := by ring

/-- Algebraic cancellation identity for $\frac{d}{ds}(U(s)^\dagger U(s)) = 0$. -/
lemma alg_unitary_deriv_cancel {R : Type*} [Ring R] [Module ℂ R]
    [SMulCommClass ℂ R R] [IsScalarTower ℂ R R] (B D A : R) :
    (-(Complex.I : ℂ) • (B * D)) * A + B * ((Complex.I : ℂ) • (D * A)) = 0 := by
  rw [smul_mul_assoc, mul_smul_comm, mul_assoc, neg_smul, neg_add_cancel]

/-- Algebraic simplification of $\frac{d}{ds}(U(s)^\dagger P(s))$. -/
lemma alg_up_deriv_simp {R : Type*} [Ring R] [Module ℂ R]
    [SMulCommClass ℂ R R] [IsScalarTower ℂ R R] (B D Q : R) :
    (-(Complex.I : ℂ) • (B * D)) * Q + B * ((Complex.I : ℂ) • (D * Q - Q * D)) =
    -(Complex.I : ℂ) • (B * Q * D) := by
  rw [smul_mul_assoc, mul_smul_comm, mul_sub, ← mul_assoc, ← mul_assoc,
    smul_sub, neg_smul, neg_smul]
  abel

/-- Algebraic cancellation identity for $\frac{d}{ds}(U(s)^\dagger P(s) U(s)) = 0$. -/
lemma alg_upu_deriv_cancel {R : Type*} [Ring R] [Module ℂ R]
    [SMulCommClass ℂ R R] [IsScalarTower ℂ R R] (B Q D A : R) :
    (-(Complex.I : ℂ) • (B * Q * D)) * A + (B * Q) * ((Complex.I : ℂ) • (D * A)) = 0 := by
  rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc (B * Q) D A, neg_smul, neg_add_cancel]

/-- Monoid conjugation inversion: if $A B = 1$ and $B Q A = Q_0$, then $A Q_0 B = Q$. -/
lemma monoid_align2 {R : Type*} [Monoid R] {A B Q Q0 : R}
    (hAB : A * B = 1) (halign1 : B * Q * A = Q0) :
    A * Q0 * B = Q := by
  have hAQ0 : A * Q0 = Q * A := by
    calc A * Q0
      _ = A * (B * Q * A) := by rw [halign1]
      _ = (A * B) * (Q * A) := by simp only [mul_assoc]
      _ = Q * A := by rw [hAB, one_mul]
  calc A * Q0 * B
    _ = (Q * A) * B := by rw [hAQ0]
    _ = Q * (A * B) := by rw [mul_assoc]
    _ = Q := by rw [hAB, mul_one]

/-- Monoid commutation transport: if $A B = 1$, $B Q A = Q_0$, and $[H, Q] = 0$, then $[B H A, Q_0] = 0$. -/
lemma monoid_commute_conj {R : Type*} [Monoid R] {A B Q Q0 H : R}
    (hAB : A * B = 1) (halign1 : B * Q * A = Q0) (hcomm : Commute H Q) :
    Commute (B * H * A) Q0 := by
  rw [commute_iff_eq]
  have hAQ0 : A * Q0 = Q * A := by
    calc A * Q0
      _ = A * (B * Q * A) := by rw [halign1]
      _ = (A * B) * (Q * A) := by simp only [mul_assoc]
      _ = Q * A := by rw [hAB, one_mul]
  have hQ0B : Q0 * B = B * Q := by
    calc Q0 * B
      _ = (B * Q * A) * B := by rw [halign1]
      _ = (B * Q) * (A * B) := by simp only [mul_assoc]
      _ = B * Q := by rw [hAB, mul_one]
  calc (B * H * A) * Q0
    _ = (B * H) * (A * Q0) := by rw [mul_assoc]
    _ = (B * H) * (Q * A) := by rw [hAQ0]
    _ = B * (H * Q) * A := by simp only [mul_assoc]
    _ = B * (Q * H) * A := by rw [hcomm.eq]
    _ = (B * Q) * (H * A) := by simp only [mul_assoc]
    _ = (Q0 * B) * (H * A) := by rw [← hQ0B]
    _ = Q0 * (B * H * A) := by simp only [mul_assoc]

/-- Abstract Kato–Hastings ODE unitarity and subspace tracking on any finite-dimensional Hilbert space. -/
lemma kato_hastings_ode_abstract {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (P0 : E →L[ℂ] E) (D_gen U P : ℝ → (E →L[ℂ] E))
    (hD_sa : ∀ s : ℝ, IsSelfAdjoint (D_gen s))
    (hU0 : U 0 = 1)
    (hP0 : P 0 = P0)
    (hU_deriv : ∀ s : ℝ, HasDerivAt U ((Complex.I : ℂ) • (D_gen s * U s)) s)
    (hP_deriv : ∀ s : ℝ, HasDerivAt P ((Complex.I : ℂ) • (D_gen s * P s - P s * D_gen s)) s)
    (s : ℝ) :
    HasDerivAt (fun u => (U u)†) (-(Complex.I : ℂ) • ((U s)† * D_gen s)) s ∧
    (U s)† * U s = 1 ∧
    U s * (U s)† = 1 ∧
    (U s)† * P s * U s = P0 ∧
    U s * P0 * (U s)† = P s ∧
    (∀ H_s : E →L[ℂ] E, Commute H_s (P s) → Commute ((U s)† * H_s * U s) P0) := by
  have hU_adj_deriv : ∀ u : ℝ,
      HasDerivAt (fun t => (U t)†) (-(Complex.I : ℂ) • ((U u)† * D_gen u)) u := by
    intro u
    have h1 : HasDerivAt (fun t => star (U t)) (star ((Complex.I : ℂ) • (D_gen u * U u))) u :=
      (hU_deriv u).star
    have h2 : star ((Complex.I : ℂ) • (D_gen u * U u)) =
        -(Complex.I : ℂ) • ((U u)† * D_gen u) := by
      rw [star_smul, star_mul, (hD_sa u).star_eq, RCLike.star_def, Complex.conj_I]
      rfl
    rw [h2] at h1
    exact h1
  have h_unitary_deriv : ∀ u : ℝ, HasDerivAt (fun t => (U t)† * U t) 0 u := by
    intro u
    have h_prod := (hU_adj_deriv u).mul (hU_deriv u)
    rw [alg_unitary_deriv_cancel ((U u)†) (D_gen u) (U u)] at h_prod
    exact h_prod
  have hU_adj_mul_all : ∀ u : ℝ, (U u)† * U u = 1 := by
    intro u
    rw [eq_of_hasDerivAt_zero h_unitary_deriv u, hU0]
    change star (1 : E →L[ℂ] E) * 1 = 1
    rw [star_one, mul_one]
  have hU_adj_mul : (U s)† * U s = 1 := hU_adj_mul_all s
  have hU_mul_adj : U s * (U s)† = 1 := mul_adjoint_eq_one_of_adjoint_mul_eq_one hU_adj_mul
  have h_UP_deriv : ∀ u : ℝ,
      HasDerivAt (fun t => (U t)† * P t) (-(Complex.I : ℂ) • ((U u)† * P u * D_gen u)) u := by
    intro u
    have h_prod := (hU_adj_deriv u).mul (hP_deriv u)
    rw [alg_up_deriv_simp ((U u)†) (D_gen u) (P u)] at h_prod
    exact h_prod
  have h_UPU_deriv : ∀ u : ℝ, HasDerivAt (fun t => (U t)† * P t * U t) 0 u := by
    intro u
    have h_prod := (h_UP_deriv u).mul (hU_deriv u)
    rw [alg_upu_deriv_cancel ((U u)†) (P u) (D_gen u) (U u)] at h_prod
    exact h_prod
  have h_align1 : (U s)† * P s * U s = P0 := by
    rw [eq_of_hasDerivAt_zero h_UPU_deriv s, hU0, hP0]
    change star (1 : E →L[ℂ] E) * P0 * 1 = P0
    rw [star_one, one_mul, mul_one]
  have h_align2 : U s * P0 * (U s)† = P s :=
    monoid_align2 hU_mul_adj h_align1
  have h_comm_rot : ∀ H_s : E →L[ℂ] E,
      Commute H_s (P s) → Commute ((U s)† * H_s * U s) P0 :=
    fun _ h_comm => monoid_commute_conj hU_mul_adj h_align1 h_comm
  exact ⟨hU_adj_deriv s, hU_adj_mul, hU_mul_adj, h_align1, h_align2, h_comm_rot⟩

/-- **Kato–Hastings Differential Flow Unitarity & Subspace Intertwining (`kato_hastings_ode_flow`)**:
    For any `IsKatoHastingsFlowSystem P0 D_gen U P` on `BoxD D L`:
    1. $U(s)^\dagger U(s) = 1$ and $U(s) U(s)^\dagger = 1$ for all $s \in \mathbb{R}$;
    2. $U(s)^\dagger P(s) U(s) = P_0$ for all $s \in \mathbb{R}$;
    3. For every $H_s$ commuting with $P(s)$, the dressed operator $U(s)^\dagger H_s U(s)$ commutes with $P_0$. -/
theorem kato_hastings_ode_flow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P) :
    (∀ s : ℝ, (U s)† * U s = 1 ∧ U s * (U s)† = 1) ∧
    (∀ s : ℝ, (U s)† * P s * U s = P0) ∧
    (∀ (s : ℝ) (H_s : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      Commute H_s (P s) → Commute ((U s)† * H_s * U s) P0) := by
  have h_abs := fun s => kato_hastings_ode_abstract P0 D_gen U P
    hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P s
  exact ⟨fun s => ⟨(h_abs s).2.1, (h_abs s).2.2.1⟩,
    fun s => (h_abs s).2.2.2.1,
    fun s H_s h_comm => (h_abs s).2.2.2.2.2 H_s h_comm⟩

/-!
## 2. Duhamel Conjugation Derivative and Banach Mean-Value Commutator Bound
-/

/-- **Duhamel Conjugation Derivative & Mean-Value Bound (`duhamel_conjugation_bound`)**:
    Along a Kato–Hastings flow `IsKatoHastingsFlowSystem P0 D_gen U P`, the conjugated observable
    $f(s) = U(s)^\dagger O U(s)$ satisfies
    $$\frac{d}{ds}\big(U(s)^\dagger O U(s)\big) = i \, U(s)^\dagger [O, \mathcal{D}(s)] U(s),$$
    and if $\|[O, \mathcal{D}(\tau)]\| \le \varepsilon_{\mathrm{comm}}$ for all $\tau \in [0, s]$ ($s \ge 0$),
    then $\|U(s)^\dagger O U(s) - O\| \le s \, \varepsilon_{\mathrm{comm}}$. -/
theorem duhamel_conjugation_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (∀ s : ℝ,
      HasDerivAt (fun τ => (U τ)† * O * U τ)
        ((Complex.I : ℂ) • ((U s)† * (O * D_gen s - D_gen s * O) * U s)) s) ∧
    (∀ (s : ℝ) (ε_comm : ℝ), 0 ≤ s →
      (∀ τ ∈ Set.Icc 0 s, ‖O * D_gen τ - D_gen τ * O‖ ≤ ε_comm) →
        ‖(U s)† * O * U s - O‖ ≤ s * ε_comm) := by
  have h_ode := fun u =>
    kato_hastings_ode_abstract P0 D_gen U P
      hFlow.isSelfAdjoint_D hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P u
  have h_deriv : ∀ u : ℝ,
      HasDerivAt (fun t => (U t)† * O * U t)
        ((Complex.I : ℂ) • ((U u)† * (O * D_gen u - D_gen u * O) * U u)) u := by
    intro u
    have h_UO : HasDerivAt (fun t => (U t)† * O)
        ((-(Complex.I : ℂ) • ((U u)† * D_gen u)) * O) u :=
      ((h_ode u).1).mul_const O
    have h_UOU := h_UO.mul (hFlow.hasDerivAt_U u)
    have h_alg :
        ((-(Complex.I : ℂ) • ((U u)† * D_gen u)) * O) * U u +
          ((U u)† * O) * ((Complex.I : ℂ) • (D_gen u * U u)) =
        (Complex.I : ℂ) • ((U u)† * (O * D_gen u - D_gen u * O) * U u) := by
      rw [clm_smul_mul, clm_smul_mul, clm_mul_smul, neg_smul,
        mul_sub ((U u)†) (O * D_gen u) (D_gen u * O), sub_mul,
        smul_sub]
      simp only [mul_assoc]
      abel
    rw [h_alg] at h_UOU
    exact h_UOU
  refine ⟨h_deriv, ?_⟩
  intro s ε_comm hs h_comm_bound
  have h_bound_deriv : ∀ u ∈ Set.Icc 0 s,
      ‖(Complex.I : ℂ) • ((U u)† * (O * D_gen u - D_gen u * O) * U u)‖ ≤ ε_comm := by
    intro u hu
    rcases norm_le_one_of_adjoint_mul_self_eq_one (h_ode u).2.1 with ⟨hU_norm, hU_adj_norm⟩
    rw [norm_smul, Complex.norm_I, one_mul]
    exact le_trans (norm_sandwich_le_of_norm_le_one hU_adj_norm hU_norm) (h_comm_bound u hu)
  have h_mvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => (U t)† * O * U t)
    (f' := fun u => (Complex.I : ℂ) • ((U u)† * (O * D_gen u - D_gen u * O) * U u))
    (s := Set.Icc 0 s)
    (fun u _ => (h_deriv u).hasDerivWithinAt)
    h_bound_deriv
    (convex_Icc 0 s)
    ⟨le_refl 0, hs⟩
    ⟨hs, le_refl s⟩
  have h_at_0 : (U 0)† * O * U 0 = O := by
    rw [hFlow.U_zero]
    change star (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) * O * 1 = O
    rw [star_one, one_mul, mul_one]
  have h_norm_s : ‖s - (0 : ℝ)‖ = s := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs]
  rw [h_at_0, h_norm_s, mul_comm ε_comm s] at h_mvt
  exact h_mvt
