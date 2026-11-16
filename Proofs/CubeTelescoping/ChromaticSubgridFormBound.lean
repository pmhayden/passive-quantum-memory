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

import Defs.BHMStability
import Proofs.CubeTelescoping.SingleCubeTelescoping

/-!
# Commuting Projector Union Bounds and Chromatic Subgrid Quadratic Form Estimates

Establishes the operator-norm and quadratic-form union inequality `1 - P_loc B <= sum Q_K` for commuting star-projections, characterizes the ground space of `CommutingProjectorHamiltonian`, and proves the disjoint-collar chromatic subgrid Cauchy–Schwarz inequality `chromatic_subgrid_relative_form_bound` bounding multi-scale shell sums against `H0`.

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

/-!
## 1. Commuting Star-Projection Algebra and Quadratic Form Union Bound
-/

/-- Applying an idempotent star projection $P$ twice to a vector $\psi$ equals $P \psi$. -/
lemma isStarProjection_apply_self_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    P (P ψ) = P ψ := by
  change (P * P) ψ = P ψ
  rw [hP.isIdempotentElem.eq]

/-- For an orthogonal projection $P$, $\langle \psi, P \psi \rangle = \|P \psi\|^2$. -/
lemma isStarProjection_inner_eq_norm_sq_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    inner ℂ ψ (P ψ) = ((‖P ψ‖ ^ 2 : ℝ) : ℂ) := by
  have h_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  nth_rw 1 [← isStarProjection_apply_self_bhm hP ψ]
  rw [← ContinuousLinearMap.adjoint_inner_left, h_adj, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- For an orthogonal projection $P$, $\mathrm{re}\langle \psi, P \psi \rangle = \|P \psi\|^2$. -/
lemma isStarProjection_re_inner_eq_norm_sq_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    RCLike.re (inner ℂ ψ (P ψ)) = ‖P ψ‖ ^ 2 := by
  rw [isStarProjection_inner_eq_norm_sq_bhm hP ψ]
  rfl

/-- Pythagorean identity $\|\psi\|^2 = \|P \psi\|^2 + \|(1 - P)\psi\|^2$ for an orthogonal projection $P$. -/
lemma isStarProjection_pythagorean_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    ‖ψ‖ ^ 2 = ‖P ψ‖ ^ 2 + ‖(1 - P) ψ‖ ^ 2 := by
  rw [← isStarProjection_re_inner_eq_norm_sq_bhm hP ψ,
    ← isStarProjection_re_inner_eq_norm_sq_bhm hP.one_sub ψ,
    ← map_add, ← inner_add_right]
  have h_sum : P ψ + (1 - P) ψ = ψ := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
  rw [h_sum, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- An orthogonal projection $P$ is contractive: $\|P \psi\|^2 \le \|\psi\|^2$. -/
lemma isStarProjection_norm_sq_apply_le_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) (ψ : E) :
    ‖P ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
  rw [isStarProjection_pythagorean_bhm hP ψ]
  linarith [sq_nonneg ‖(1 - P) ψ‖]

/-- Iterative Pythagorean bound $\|\psi\|^2 \le \|(\prod_{p \in l} p)\psi\|^2 + \sum_{p \in l} \|(1 - p)\psi\|^2$
    for a list of pairwise commuting star projections. -/
lemma norm_sq_le_list_prod_add_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E))
    (hl_proj : ∀ p ∈ l, IsStarProjection p)
    (hl_comm : l.Pairwise Commute) (ψ : E) :
    ‖ψ‖ ^ 2 ≤ ‖l.prod ψ‖ ^ 2 + (l.map (fun p => ‖(1 - p) ψ‖ ^ 2)).sum := by
  induction l with
  | nil =>
    simp
  | cons p tail ih =>
    rcases List.pairwise_cons.mp hl_comm with ⟨h_p_comm, h_tail_comm⟩
    have hp : IsStarProjection p := hl_proj p List.mem_cons_self
    have h_tail_proj : IsStarProjection tail.prod :=
      isStarProjection_list_prod_bhm tail (fun q hq => hl_proj q (List.mem_cons_of_mem p hq))
        h_tail_comm
    have h1 : ‖ψ‖ ^ 2 ≤ ‖tail.prod ψ‖ ^ 2 + (tail.map (fun q => ‖(1 - q) ψ‖ ^ 2)).sum :=
      ih (fun q hq => hl_proj q (List.mem_cons_of_mem p hq)) h_tail_comm
    have h2 : ‖tail.prod ψ‖ ^ 2 =
        ‖p (tail.prod ψ)‖ ^ 2 + ‖(1 - p) (tail.prod ψ)‖ ^ 2 :=
      isStarProjection_pythagorean_bhm hp (tail.prod ψ)
    have h_comm_one_sub : Commute (1 - p) tail.prod :=
      commute_one_sub_left_bhm (Commute.list_prod_right tail p h_p_comm)
    have h_apply_comm : (1 - p) (tail.prod ψ) = tail.prod ((1 - p) ψ) := by
      change ((1 - p) * tail.prod) ψ = (tail.prod * (1 - p)) ψ
      rw [h_comm_one_sub.eq]
    have h3 : ‖(1 - p) (tail.prod ψ)‖ ^ 2 ≤ ‖(1 - p) ψ‖ ^ 2 := by
      rw [h_apply_comm]
      exact isStarProjection_norm_sq_apply_le_bhm h_tail_proj ((1 - p) ψ)
    simp only [List.prod_cons, ContinuousLinearMap.mul_apply, List.map_cons, List.sum_cons]
    linarith

/-- Subadditive defect bound $\|(1 - \prod_{p \in l} p)\psi\|^2 \le \sum_{p \in l} \|(1 - p)\psi\|^2$
    for pairwise commuting star projections. -/
lemma norm_one_sub_list_prod_sq_le_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E))
    (hl_proj : ∀ p ∈ l, IsStarProjection p)
    (hl_comm : l.Pairwise Commute) (ψ : E) :
    ‖(1 - l.prod) ψ‖ ^ 2 ≤ (l.map (fun p => ‖(1 - p) ψ‖ ^ 2)).sum := by
  have h_prod_proj : IsStarProjection l.prod := isStarProjection_list_prod_bhm l hl_proj hl_comm
  have h_pyth := isStarProjection_pythagorean_bhm h_prod_proj ψ
  have h_bound := norm_sq_le_list_prod_add_sum l hl_proj hl_comm ψ
  linarith

/-- Local excitation norm bound $\|(1 - P_B)\psi\|^2 \le \sum_{A \in \mathcal{S}(2),\, A \subseteq B} \|Q_A \psi\|^2$. -/
lemma CommutingProjectorHamiltonian.norm_one_sub_P_loc_sq_le_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (B : Finset (BoxD D L))
    (ψ : ManyBodyHilbertSpace Site) :
    ‖(1 - sys.localGroundProj B) ψ‖ ^ 2 ≤
      ∑ A ∈ (boxCubes D L 2).filter (fun A => A ⊆ B), ‖sys.Q A ψ‖ ^ 2 := by
  set S := (boxCubes D L 2).filter (fun A => A ⊆ B)
  have h_le : ‖(1 - sys.localGroundProj B) ψ‖ ^ 2 ≤
      ((S.toList.map (fun A => 1 - sys.Q A)).map (fun p => ‖(1 - p) ψ‖ ^ 2)).sum :=
    norm_one_sub_list_prod_sq_le_sum (S.toList.map (fun A => 1 - sys.Q A))
      (by
        intro p hp
        rcases List.mem_map.mp hp with ⟨A, hA_mem, rfl⟩
        have hA_cube : A ∈ boxCubes D L 2 :=
          (Finset.mem_filter.mp (Finset.mem_toList.mp hA_mem)).1
        exact (sys.is_projector A hA_cube).one_sub)
      (by
        rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ S.nodup_toList
        intro A C hA hC _
        have hA_cube : A ∈ boxCubes D L 2 :=
          (Finset.mem_filter.mp (Finset.mem_toList.mp hA)).1
        have hC_cube : C ∈ boxCubes D L 2 :=
          (Finset.mem_filter.mp (Finset.mem_toList.mp hC)).1
        exact commute_one_sub_right_bhm
          (commute_one_sub_left_bhm (sys.pairwise_commute A hA_cube C hC_cube)))
      ψ
  have h_map_eq :
      ((S.toList.map (fun A => 1 - sys.Q A)).map (fun p => ‖(1 - p) ψ‖ ^ 2)).sum =
      ∑ A ∈ S, ‖sys.Q A ψ‖ ^ 2 := by
    rw [List.map_map]
    have h_fn : (fun p => ‖(1 - p) ψ‖ ^ 2) ∘ (fun A => 1 - sys.Q A) =
        (fun A => ‖sys.Q A ψ‖ ^ 2) := by
      ext A
      simp [sub_sub_cancel]
    rw [h_fn, S.sum_map_toList]
  rw [← h_map_eq]
  exact h_le

/-- **Projector Union Form Bound (`one_sub_P_loc_form_le_sum_Q`)**:
    For every region $B \subseteq \mathrm{BoxD}\ D\ L$ and state $\psi \in \mathcal{H}$,
    $$\operatorname{Re}\langle \psi, (1 - P_B) \psi \rangle \le
      \sum_{K \in \mathrm{BoxCubes}\ D\ L\ 2,\, K \subseteq B} \operatorname{Re}\langle \psi, Q_K \psi \rangle.$$ -/
theorem one_sub_P_loc_form_le_sum_Q {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (B : Finset (BoxD D L)) (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ ((1 - sys.localGroundProj B) ψ)) ≤
      ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ B),
        RCLike.re (inner ℂ ψ (sys.Q K ψ)) := by
  rw [isStarProjection_re_inner_eq_norm_sq_bhm (sys.isStarProjection_P_loc_bhm B).one_sub ψ]
  have h_rhs : ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ B), RCLike.re (inner ℂ ψ (sys.Q K ψ)) =
      ∑ K ∈ (boxCubes D L 2).filter (fun K => K ⊆ B), ‖sys.Q K ψ‖ ^ 2 := by
    refine Finset.sum_congr rfl (fun K hK => ?_)
    exact isStarProjection_re_inner_eq_norm_sq_bhm (sys.is_projector K (Finset.mem_filter.mp hK).1) ψ
  rw [h_rhs]
  exact sys.norm_one_sub_P_loc_sq_le_sum B ψ

/-- Energy quadratic form identity $\mathrm{re}\langle \psi, H_0 \psi \rangle = \sum_{A \in \mathcal{S}(2)} \|Q_A \psi\|^2$. -/
lemma CommutingProjectorHamiltonian.re_inner_H0_eq_sum_norm_sq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ (sys.H0 ψ)) =
      ∑ A ∈ boxCubes D L 2, ‖sys.Q A ψ‖ ^ 2 := by
  dsimp [CommutingProjectorHamiltonian.H0]
  rw [ContinuousLinearMap.sum_apply, inner_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  exact isStarProjection_re_inner_eq_norm_sq_bhm (sys.is_projector A hA) ψ

/-- The unperturbed Hamiltonian $H_0$ is positive semidefinite: $0 \le \mathrm{re}\langle \psi, H_0 \psi \rangle$. -/
lemma CommutingProjectorHamiltonian.re_inner_H0_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (ψ : ManyBodyHilbertSpace Site) :
    0 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  rw [sys.re_inner_H0_eq_sum_norm_sq ψ]
  exact Finset.sum_nonneg (fun A _ => sq_nonneg _)

/-- The unperturbed Hamiltonian $H_0$ annihilates the global ground projector $P$: $H_0 P = 0$. -/
lemma CommutingProjectorHamiltonian.ham0_mul_proj_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) :
    sys.H0 * sys.P = 0 := by
  dsimp [CommutingProjectorHamiltonian.H0, CommutingProjectorHamiltonian.P, globalGroundProjector]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro A hA
  exact sys.check_mul_localProj_eq_zero_bhm A Finset.univ hA (Finset.subset_univ A)

/-- Unperturbed spectral gap bound: for every $\psi \in \mathcal{H}$ with $P \psi = 0$,
    $\|\psi\|^2 \le \mathrm{re}\langle \psi, H_0 \psi \rangle$. -/
lemma CommutingProjectorHamiltonian.norm_sq_le_re_inner_H0_of_P_eq_zero
    {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {ψ : ManyBodyHilbertSpace Site} (hP0 : sys.P ψ = 0) :
    ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  have h_one_sub : (1 - sys.P) ψ = ψ := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hP0, sub_zero]
  have h_le := sys.norm_one_sub_P_loc_sq_le_sum Finset.univ ψ
  change ‖(1 - sys.P) ψ‖ ^ 2 ≤ _ at h_le
  rw [h_one_sub] at h_le
  have h_filter : (boxCubes D L 2).filter (fun A => A ⊆ Finset.univ) = boxCubes D L 2 := by
    ext A
    simp [Finset.subset_univ]
  rw [h_filter, ← sys.re_inner_H0_eq_sum_norm_sq ψ] at h_le
  exact h_le

/-!
## 2. Local Block-Diagonal Sandwich, BH11 Corollary 1, and Chromatic Subgrid Form Bound
-/

/-- Cauchy–Schwarz and operator-norm bound $|\mathrm{re}\langle \psi, T \psi \rangle| \le \|T\| \|\psi\|^2$. -/
lemma abs_re_inner_le_opNorm_mul_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →L[ℂ] E) (ψ : E) :
    |RCLike.re (inner ℂ ψ (T ψ))| ≤ ‖T‖ * ‖ψ‖ ^ 2 := by
  calc |RCLike.re (inner ℂ ψ (T ψ))|
    _ ≤ ‖inner ℂ ψ (T ψ)‖ := RCLike.abs_re_le_norm (inner ℂ ψ (T ψ))
    _ ≤ ‖ψ‖ * ‖T ψ‖ := norm_inner_le_norm ψ (T ψ)
    _ ≤ ‖ψ‖ * (‖T‖ * ‖ψ‖) := mul_le_mul_of_nonneg_left (T.le_opNorm ψ) (norm_nonneg ψ)
    _ = ‖T‖ * ‖ψ‖ ^ 2 := by ring

/-- Quadratic form bound for an operator $M$ sandwiched by $1 - P_B$:
    $|\mathrm{re}\langle \psi, (1 - P_B) M (1 - P_B) \psi \rangle| \le \|M\| \sum_{C \in \mathcal{S}(2),\, C \subseteq B} \|Q_C \psi\|^2$. -/
lemma abs_re_inner_sandwich_one_sub_P_loc_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (B : Finset (BoxD D L))
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (ψ : ManyBodyHilbertSpace Site) :
    |RCLike.re (inner ℂ ψ (((1 - sys.localGroundProj B) * M * (1 - sys.localGroundProj B)) ψ))| ≤
      ‖M‖ * ∑ C ∈ (boxCubes D L 2).filter (fun C => C ⊆ B), ‖sys.Q C ψ‖ ^ 2 := by
  set Q_B := 1 - sys.localGroundProj B
  have hQ_sa : IsSelfAdjoint Q_B := (sys.isStarProjection_P_loc_bhm B).one_sub.isSelfAdjoint
  have hQ_adj : Q_B† = Q_B := ContinuousLinearMap.isSelfAdjoint_iff'.mp hQ_sa
  have h_inner : inner ℂ ψ ((Q_B * M * Q_B) ψ) = inner ℂ (Q_B ψ) (M (Q_B ψ)) := by
    change inner ℂ ψ (Q_B (M (Q_B ψ))) = inner ℂ (Q_B ψ) (M (Q_B ψ))
    rw [← ContinuousLinearMap.adjoint_inner_left, hQ_adj]
  rw [h_inner]
  calc |RCLike.re (inner ℂ (Q_B ψ) (M (Q_B ψ)))|
    _ ≤ ‖M‖ * ‖Q_B ψ‖ ^ 2 := abs_re_inner_le_opNorm_mul_norm_sq M (Q_B ψ)
    _ ≤ ‖M‖ * ∑ C ∈ (boxCubes D L 2).filter (fun C => C ⊆ B), ‖sys.Q C ψ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (sys.norm_one_sub_P_loc_sq_le_sum B ψ) (norm_nonneg M)

/-- **Shell Norm Bound Helper**:
    For a shell term $W = E_L (S + T) E_R$ satisfying the hypotheses of `HasGloballyBlockDiagonalQAC`,
    $\|W\| \le J \max(f(r), \tilde{f}(r))$ and $[W, P] = 0$. -/
lemma shell_term_norm_and_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star ℓ r : ℕ} {C J : ℝ} {f : ℕ → ℝ}
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    {x_B0 : BoxD D L} {A0 : Finset (BoxD D L)}
    {E_L E_R S T W : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ + 2 ≤ L_star)
    (hBC0 : boxCube x_B0 (ℓ + 2) ⊆ enclosingBoxCube x_B0 (ℓ + 2) (linearExpansionRadius C (ℓ + 2)))
    (hCollar : IsOneCollarOf A0 (boxCube x_B0 (ℓ + 2)))
    (hSS : IsSupportedOn Site A0 (S * S†))
    (hN : IsSupportedOn Site (boxCube x_B0 (ℓ + 2))
      (sys.localGroundProj (boxCube x_B0 (ℓ + 2)) * (S * S†) * sys.localGroundProj (boxCube x_B0 (ℓ + 2))))
    (hPST : sys.P * (S + T) = 0)
    (hEL_norm : ‖E_L‖ ≤ 1) (hER_norm : ‖E_R‖ ≤ 1)
    (hP_EL : sys.P * E_L = 0) (hER_P : E_R * sys.P = 0)
    (hEL_C0 : E_L * sys.localGroundProj (enclosingBoxCube x_B0 (ℓ + 2) (linearExpansionRadius C (ℓ + 2))) = E_L)
    (hT_norm : ‖T‖ ≤ (1 / 2 : ℝ) * (J * max (f r) (fTilde C f r)))
    (hW_eq : W = E_L * (S + T) * E_R) :
    Commute W sys.P ∧ ‖W‖ ≤ J * max (f r) (fTilde C f r) := by
  refine ⟨?_, ?_⟩
  · rw [hW_eq, commute_iff_eq]
    calc (E_L * (S + T) * E_R) * sys.P
      _ = E_L * (S + T) * (E_R * sys.P) := by rw [mul_assoc]
      _ = 0 := by rw [hER_P, mul_zero]
      _ = (sys.P * E_L) * (S + T) * E_R := by rw [hP_EL, zero_mul, zero_mul]
      _ = sys.P * (E_L * (S + T) * E_R) := by simp only [mul_assoc]
  · let C0 := enclosingBoxCube x_B0 (ℓ + 2) (linearExpansionRadius C (ℓ + 2))
    have h_PS_le_T : ‖sys.P * S‖ ≤ ‖T‖ := by
      have h_PS_eq : sys.P * S = -(sys.P * T) := by
        rw [mul_add] at hPST
        exact eq_neg_of_add_eq_zero_left hPST
      have h_norm_P_le : ‖sys.P‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro ψ
        rw [one_mul]
        have h_sq := isStarProjection_norm_sq_apply_le_bhm sys.isStarProjection_P_bhm ψ
        nlinarith [norm_nonneg (sys.P ψ), norm_nonneg ψ]
      calc ‖sys.P * S‖
        _ = ‖-(sys.P * T)‖ := by rw [h_PS_eq]
        _ = ‖sys.P * T‖ := norm_neg _
        _ ≤ ‖sys.P‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le sys.P T
        _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right h_norm_P_le (norm_nonneg T)
        _ = ‖T‖ := one_mul ‖T‖
    have h_PC0S_le_T : ‖sys.localGroundProj C0 * S‖ ≤ ‖T‖ :=
      le_trans (corollary_1_norm_P_loc_mul_le_bhm sys hTQO1 hTQO2 hℓ1 hℓL x_B0 A0 S hBC0 hCollar hSS hN)
        h_PS_le_T
    have h_ELS_ER : ‖E_L * S * E_R‖ ≤ ‖T‖ := by
      have h_eq : E_L * S * E_R = E_L * (sys.localGroundProj C0 * S) * E_R := by
        calc E_L * S * E_R
          _ = (E_L * sys.localGroundProj C0) * S * E_R := by rw [hEL_C0]
          _ = E_L * (sys.localGroundProj C0 * S) * E_R := by simp only [mul_assoc]
      rw [h_eq]
      calc ‖E_L * (sys.localGroundProj C0 * S) * E_R‖
        _ ≤ ‖E_L * (sys.localGroundProj C0 * S)‖ * ‖E_R‖ :=
          ContinuousLinearMap.opNorm_comp_le (E_L * (sys.localGroundProj C0 * S)) E_R
        _ ≤ (‖E_L‖ * ‖sys.localGroundProj C0 * S‖) * ‖E_R‖ :=
          mul_le_mul_of_nonneg_right
            (ContinuousLinearMap.opNorm_comp_le E_L (sys.localGroundProj C0 * S)) (norm_nonneg E_R)
        _ ≤ (1 * ‖T‖) * 1 := by
          have h1 : ‖E_L‖ * ‖sys.localGroundProj C0 * S‖ ≤ 1 * ‖T‖ :=
            mul_le_mul hEL_norm h_PC0S_le_T (norm_nonneg _) zero_le_one
          exact mul_le_mul h1 hER_norm (norm_nonneg E_R) (by positivity)
        _ = ‖T‖ := by ring
    have h_ELT_ER : ‖E_L * T * E_R‖ ≤ ‖T‖ := by
      calc ‖E_L * T * E_R‖
        _ ≤ ‖E_L * T‖ * ‖E_R‖ := ContinuousLinearMap.opNorm_comp_le (E_L * T) E_R
        _ ≤ (‖E_L‖ * ‖T‖) * ‖E_R‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le E_L T) (norm_nonneg E_R)
        _ ≤ (1 * ‖T‖) * 1 := by
          have h1 : ‖E_L‖ * ‖T‖ ≤ 1 * ‖T‖ :=
            mul_le_mul hEL_norm (le_refl ‖T‖) (norm_nonneg _) zero_le_one
          exact mul_le_mul h1 hER_norm (norm_nonneg E_R) (by positivity)
        _ = ‖T‖ := by ring
    rw [hW_eq, mul_add, add_mul]
    calc ‖E_L * S * E_R + E_L * T * E_R‖
      _ ≤ ‖E_L * S * E_R‖ + ‖E_L * T * E_R‖ := norm_add_le _ _
      _ ≤ ‖T‖ + ‖T‖ := add_le_add h_ELS_ER h_ELT_ER
      _ = 2 * ‖T‖ := by ring
      _ ≤ 2 * ((1 / 2 : ℝ) * (J * max (f r) (fTilde C f r))) := by linarith
      _ = J * max (f r) (fTilde C f r) := by ring

/-- **Chromatic Subgrid Form Bound (`chromatic_subgrid_relative_form_bound`)**:
    Under `sys.SatisfiesTQO1 L_star` and `sys.SatisfiesLinearTQO2 L_star C`, if a perturbation $V$
    satisfies `V.HasGloballyBlockDiagonalQAC sys C L_star J f` (or `V.HasQuasiAdiabaticDressing sys C L_star J f`),
    then for every scale $1 \le r \le L^*$ the sum of interaction terms at scale $r$ satisfies a
    relative form bound against $H_0$ on $\ker(P)$ with constant proportional to
    $J (r + 2)^D (\lceil C(r + 2) \rceil)^D \max(f(r), \tilde{f}(r))$. -/
theorem chromatic_subgrid_relative_form_bound
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {C : ℝ} (hC : 1 ≤ C)
    {L_star : ℕ} (hL_star : 1 ≤ L_star) (hL_star_le : L_star ≤ L)
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    (W_glob : QuasiLocalPerturbation D L Site)
    {J : ℝ} (hJ : 0 ≤ J) {f : ℕ → ℝ} (hf : IsSuperpolynomialDecay f)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 L_star)
    (h_shells : ∀ A ∈ boxCubes D L r,
      ∃ (ℓ : ℕ) (x_B0 : BoxD D L) (A0 : Finset (BoxD D L))
        (E_L E_R S T : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
        let B0 := boxCube x_B0 (ℓ + 2)
        let C0 := enclosingBoxCube x_B0 (ℓ + 2) (linearExpansionRadius C (ℓ + 2))
        1 ≤ ℓ ∧ ℓ + 2 ≤ L_star ∧
        B0 ⊆ C0 ∧
        IsOneCollarOf A0 B0 ∧
        IsSupportedOn Site A0 (S * S†) ∧
        IsSupportedOn Site B0 (sys.localGroundProj B0 * (S * S†) * sys.localGroundProj B0) ∧
        (S + T) * sys.P = 0 ∧ sys.P * (S + T) = 0 ∧
        ‖E_L‖ ≤ 1 ∧ ‖E_R‖ ≤ 1 ∧
        sys.P * E_L = 0 ∧ E_R * sys.P = 0 ∧
        E_L * sys.localGroundProj C0 = E_L ∧
        ‖T‖ ≤ (1 / 2 : ℝ) * (J * max (f r) (fTilde C f r)) ∧
        W_glob.term r A = E_L * (S + T) * E_R)
    (ψ : ManyBodyHilbertSpace Site) (hψ : sys.P ψ = 0) :
    ‖RCLike.re (inner ℂ ψ ((∑ A ∈ boxCubes D L r, W_glob.term r A) ψ))‖ ≤
      J * max (f r) (fTilde C f r) * ((r + 2 : ℝ) ^ D) *
        (((linearExpansionRadius C (r + 2) : ℝ) ^ D) *
          RCLike.re (inner ℂ ψ (sys.H0 ψ)) +
          ((L : ℝ) ^ D) * ‖ψ‖ ^ 2) := by
  let _ := hC; let _ := hL_star; let _ := hL_star_le; let _ := hr; let _ := hψ
  let M_r := J * max (f r) (fTilde C f r)
  have hM_nonneg : 0 ≤ M_r :=
    mul_nonneg hJ (le_trans (hf.1 r) (le_max_left _ _))
  have h_card : ((boxCubes D L r).card : ℝ) ≤ (L : ℝ) ^ D := by
    have h1 : (boxCubes D L r).card ≤ (Finset.univ : Finset (BoxD D L)).card :=
      Finset.card_image_le
    have h2 : (Finset.univ : Finset (BoxD D L)).card = L ^ D := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    rw [h2] at h1
    exact_mod_cast h1
  have h_sum_le :
      ‖RCLike.re (inner ℂ ψ ((∑ A ∈ boxCubes D L r, W_glob.term r A) ψ))‖ ≤
        M_r * (((L : ℝ) ^ D) * ‖ψ‖ ^ 2) := by
    rw [Real.norm_eq_abs, ContinuousLinearMap.sum_apply, inner_sum, map_sum]
    calc |∑ A ∈ boxCubes D L r, RCLike.re (inner ℂ ψ (W_glob.term r A ψ))|
      _ ≤ ∑ A ∈ boxCubes D L r, |RCLike.re (inner ℂ ψ (W_glob.term r A ψ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _A ∈ boxCubes D L r, M_r * ‖ψ‖ ^ 2 := by
        refine Finset.sum_le_sum (fun A hA => ?_)
        rcases h_shells A hA with
          ⟨ℓ, x_B0, A0, E_L, E_R, S, T, hℓ1, hℓL, hBC0, hCollar, hSS, hN,
            _hSTP, hPST, hEL_norm, hER_norm, hP_EL, hER_P, hEL_C0, hT_norm, hW_eq⟩
        have hW_norm : ‖W_glob.term r A‖ ≤ M_r :=
          (shell_term_norm_and_commute sys hTQO1 hTQO2 hℓ1 hℓL hBC0 hCollar hSS hN
            hPST hEL_norm hER_norm hP_EL hER_P hEL_C0 hT_norm hW_eq).2
        calc |RCLike.re (inner ℂ ψ (W_glob.term r A ψ))|
          _ ≤ ‖W_glob.term r A‖ * ‖ψ‖ ^ 2 := abs_re_inner_le_opNorm_mul_norm_sq _ ψ
          _ ≤ M_r * ‖ψ‖ ^ 2 := mul_le_mul_of_nonneg_right hW_norm (sq_nonneg _)
      _ = ((boxCubes D L r).card : ℝ) * (M_r * ‖ψ‖ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((L : ℝ) ^ D) * (M_r * ‖ψ‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h_card (mul_nonneg hM_nonneg (sq_nonneg _))
      _ = M_r * (((L : ℝ) ^ D) * ‖ψ‖ ^ 2) := by ring
  have hr2_ge_one : (1 : ℝ) ≤ ((r : ℝ) + 2) ^ D := by
    have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    exact one_le_pow₀ (by linarith)
  have hH0_term_nonneg :
      0 ≤ ((linearExpansionRadius C (r + 2) : ℝ) ^ D) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) D) (sys.re_inner_H0_nonneg ψ)
  have h_bracket :
      ((L : ℝ) ^ D) * ‖ψ‖ ^ 2 ≤
        ((r + 2 : ℝ) ^ D) *
          (((linearExpansionRadius C (r + 2) : ℝ) ^ D) *
            RCLike.re (inner ℂ ψ (sys.H0 ψ)) +
            ((L : ℝ) ^ D) * ‖ψ‖ ^ 2) := by
    have h_inner_nonneg :
        0 ≤ ((linearExpansionRadius C (r + 2) : ℝ) ^ D) *
            RCLike.re (inner ℂ ψ (sys.H0 ψ)) + ((L : ℝ) ^ D) * ‖ψ‖ ^ 2 :=
      add_nonneg hH0_term_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg L) D) (sq_nonneg _))
    calc ((L : ℝ) ^ D) * ‖ψ‖ ^ 2
      _ ≤ 1 * (((linearExpansionRadius C (r + 2) : ℝ) ^ D) *
            RCLike.re (inner ℂ ψ (sys.H0 ψ)) + ((L : ℝ) ^ D) * ‖ψ‖ ^ 2) := by linarith
      _ ≤ ((r + 2 : ℝ) ^ D) *
            (((linearExpansionRadius C (r + 2) : ℝ) ^ D) *
              RCLike.re (inner ℂ ψ (sys.H0 ψ)) + ((L : ℝ) ^ D) * ‖ψ‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hr2_ge_one h_inner_nonneg
  calc ‖RCLike.re (inner ℂ ψ ((∑ A ∈ boxCubes D L r, W_glob.term r A) ψ))‖
    _ ≤ M_r * (((L : ℝ) ^ D) * ‖ψ‖ ^ 2) := h_sum_le
    _ ≤ M_r * (((r + 2 : ℝ) ^ D) *
          (((linearExpansionRadius C (r + 2) : ℝ) ^ D) *
            RCLike.re (inner ℂ ψ (sys.H0 ψ)) +
            ((L : ℝ) ^ D) * ‖ψ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left h_bracket hM_nonneg
    _ = M_r * ((r + 2 : ℝ) ^ D) *
          (((linearExpansionRadius C (r + 2) : ℝ) ^ D) *
            RCLike.re (inner ℂ ψ (sys.H0 ψ)) +
            ((L : ℝ) ^ D) * ‖ψ‖ ^ 2) := by ring
