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
import Proofs.BoxMetricAndCollarLemmas
import Proofs.SupportAndCondExpLemmas

/-!
# C*-Algebraic Local-to-Global Norm Transfer under TQO-1 and Linear TQO-2

Proves the C*-algebraic local-to-global norm transfer identities `||O_A P_loc B|| = ||O_A P||` and sector-filtered `||O_A Pi_sec P_loc B|| = ||O_A P0||` for operators supported in a region `A` with Linear TQO-2 collar `B`, together with the TQO-1 ground-state scalar bound `|c| <= ||O_A||`.

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Local Ground-State Projector Absorption $P_B P = P$ and Orthogonality
-/

/-- If $a$ and $b$ commute in a ring, then $1 - a$ and $b$ commute. -/
lemma commute_one_sub_left_bhm {R : Type*} [Ring R] {a b : R} (h : Commute a b) :
    Commute (1 - a) b := by
  rw [commute_iff_eq, sub_mul, mul_sub, one_mul, mul_one, h.eq]

/-- If $a$ and $b$ commute in a ring, then $a$ and $1 - b$ commute. -/
lemma commute_one_sub_right_bhm {R : Type*} [Ring R] {a b : R} (h : Commute a b) :
    Commute a (1 - b) := by
  rw [commute_iff_eq, mul_sub, sub_mul, mul_one, one_mul, h.eq]

/-- The product of a list of pairwise-commuting star projections is again a star projection. -/
lemma isStarProjection_list_prod_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E))
    (hl_proj : ∀ p ∈ l, IsStarProjection p)
    (hl_comm : l.Pairwise Commute) :
    IsStarProjection l.prod := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact ⟨IsIdempotentElem.one, IsSelfAdjoint.one (E →L[ℂ] E)⟩
  | cons p tail ih =>
    rw [List.prod_cons]
    rcases List.pairwise_cons.mp hl_comm with ⟨h_p_comm, h_tail_comm⟩
    have hp : IsStarProjection p := hl_proj p List.mem_cons_self
    have htail : IsStarProjection tail.prod :=
      ih (fun q hq => hl_proj q (List.mem_cons_of_mem p hq)) h_tail_comm
    have h_comm_prod : Commute p tail.prod := Commute.list_prod_right tail p h_p_comm
    exact hp.mul htail h_comm_prod

/-- If $p \in l$ is idempotent and commutes with every element of $l$, then $(1 - p) \cdot \prod l = 0$. -/
lemma one_sub_mul_list_prod_eq_zero_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (l : List (E →L[ℂ] E)) (p : E →L[ℂ] E)
    (hp_mem : p ∈ l) (hp_idem : IsIdempotentElem p)
    (hp_comm : ∀ q ∈ l, Commute p q) :
    (1 - p) * l.prod = 0 := by
  induction l with
  | nil =>
    cases hp_mem
  | cons q tail ih =>
    rw [List.prod_cons, ← mul_assoc]
    rcases List.mem_cons.mp hp_mem with rfl | hp_tail
    · have h_zero : (1 - p) * p = 0 := by
        rw [sub_mul, one_mul, hp_idem.eq, sub_self]
      rw [h_zero, zero_mul]
    · have h_comm : Commute (1 - p) q :=
        commute_one_sub_left_bhm (hp_comm q List.mem_cons_self)
      rw [h_comm.eq, mul_assoc, ih hp_tail (fun r hr => hp_comm r (List.mem_cons_of_mem q hr)),
        mul_zero]

/-- If every element $a \in l$ acts as a left identity on $x$ ($a \cdot x = x$), so does the list product $\prod l$. -/
lemma list_prod_mul_eq_right_bhm {R : Type*} [Monoid R] (l : List R) (x : R)
    (h : ∀ a ∈ l, a * x = x) : l.prod * x = x := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    rw [List.prod_cons, mul_assoc, ih (fun b hb => h b (List.mem_cons_of_mem a hb)),
      h a List.mem_cons_self]

/-- Every local ground projector `sys.P_loc B` of a `CommutingProjectorHamiltonian` is an orthogonal
    projection (`IsStarProjection (sys.P_loc B)`), hence $\|P_B\| \le 1$ and $\|1 - P_B\| \le 1$. -/
lemma CommutingProjectorHamiltonian.isStarProjection_P_loc_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (B : Finset (BoxD D L)) :
    IsStarProjection (sys.localGroundProj B) := by
  dsimp [CommutingProjectorHamiltonian.localGroundProj, localGroundProjector]
  set S := (boxCubes D L 2).filter (fun A => A ⊆ B)
  apply isStarProjection_list_prod_bhm
  · intro p hp
    rcases List.mem_map.mp hp with ⟨A, hA_mem, rfl⟩
    have hA_cube : A ∈ boxCubes D L 2 :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hA_mem)).1
    exact (sys.is_projector A hA_cube).one_sub
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ S.nodup_toList
    intro A C hA hC _
    have hA_cube : A ∈ boxCubes D L 2 :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hA)).1
    have hC_cube : C ∈ boxCubes D L 2 :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hC)).1
    exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.pairwise_commute A hA_cube C hC_cube))

/-- The global ground projector $P = P_\Lambda$ of a `CommutingProjectorHamiltonian` is a star projection. -/
lemma CommutingProjectorHamiltonian.isStarProjection_P_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) :
    IsStarProjection sys.P :=
  sys.isStarProjection_P_loc_bhm Finset.univ

/-- Any local term $Q_A$ ($A \in \mathcal{S}(2)$) contained in $B$ is annihilated on the right by $P_B$: $Q_A P_B = 0$. -/
lemma CommutingProjectorHamiltonian.check_mul_localProj_eq_zero_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (A B : Finset (BoxD D L)) (hA : A ∈ boxCubes D L 2) (hAB : A ⊆ B) :
    sys.Q A * sys.localGroundProj B = 0 := by
  dsimp [CommutingProjectorHamiltonian.localGroundProj, localGroundProjector]
  set S := (boxCubes D L 2).filter (fun C => C ⊆ B)
  have h_mem : 1 - sys.Q A ∈ S.toList.map (fun C => 1 - sys.Q C) := by
    apply List.mem_map_of_mem
    rw [Finset.mem_toList, Finset.mem_filter]
    exact ⟨hA, hAB⟩
  have h_sub : sys.Q A = 1 - (1 - sys.Q A) := (sub_sub_cancel 1 (sys.Q A)).symm
  rw [h_sub]
  apply one_sub_mul_list_prod_eq_zero_bhm _ (1 - sys.Q A) h_mem
    (sys.is_projector A hA).one_sub.isIdempotentElem
  intro q hq
  rcases List.mem_map.mp hq with ⟨C, hC_mem, rfl⟩
  have hC : C ∈ boxCubes D L 2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hC_mem)).1
  exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.pairwise_commute A hA C hC))

/-- For nested regions $B_1 \subseteq B_2 \subseteq \mathrm{BoxD}\ D\ L$, `sys.P_loc B₁` absorbs `sys.P_loc B₂`:
    $P_{B_1} P_{B_2} = P_{B_2}$ and $P_{B_2} P_{B_1} = P_{B_2}$. -/
lemma CommutingProjectorHamiltonian.localProj_mul_localProj_of_subset_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {B₁ B₂ : Finset (BoxD D L)} (hSub : B₁ ⊆ B₂) :
    sys.localGroundProj B₁ * sys.localGroundProj B₂ = sys.localGroundProj B₂ ∧
    sys.localGroundProj B₂ * sys.localGroundProj B₁ = sys.localGroundProj B₂ := by
  have h_left : sys.localGroundProj B₁ * sys.localGroundProj B₂ = sys.localGroundProj B₂ := by
    dsimp [CommutingProjectorHamiltonian.localGroundProj, localGroundProjector]
    apply list_prod_mul_eq_right_bhm
    intro p hp
    rcases List.mem_map.mp hp with ⟨K, hK_mem, rfl⟩
    rcases Finset.mem_filter.mp (Finset.mem_toList.mp hK_mem) with ⟨hK_cube, hKB1⟩
    have hKB2 : K ⊆ B₂ := Finset.Subset.trans hKB1 hSub
    have h_zero : sys.Q K * sys.localGroundProj B₂ = 0 := sys.check_mul_localProj_eq_zero_bhm K B₂ hK_cube hKB2
    change (1 - sys.Q K) * sys.localGroundProj B₂ = sys.localGroundProj B₂
    rw [sub_mul, one_mul, h_zero, sub_zero]
  refine ⟨h_left, ?_⟩
  have hB1_sa : star (sys.localGroundProj B₁) = sys.localGroundProj B₁ :=
    (sys.isStarProjection_P_loc_bhm B₁).isSelfAdjoint.star_eq
  have hB2_sa : star (sys.localGroundProj B₂) = sys.localGroundProj B₂ :=
    (sys.isStarProjection_P_loc_bhm B₂).isSelfAdjoint.star_eq
  calc sys.localGroundProj B₂ * sys.localGroundProj B₁
    _ = star (sys.localGroundProj B₂) * star (sys.localGroundProj B₁) := by rw [hB2_sa, hB1_sa]
    _ = star (sys.localGroundProj B₁ * sys.localGroundProj B₂) := (star_mul _ _).symm
    _ = star (sys.localGroundProj B₂) := by rw [h_left]
    _ = sys.localGroundProj B₂ := hB2_sa

/-- For any region $B \subseteq \mathrm{BoxD}\ D\ L$, the local ground projector `sys.P_loc B` of a
    `CommutingProjectorHamiltonian` absorbs the global ground projector `sys.P`:
    $P_B P = P$ and $P P_B = P$. -/
lemma CommutingProjectorHamiltonian.localProj_mul_proj_eq_proj_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site) (B : Finset (BoxD D L)) :
    sys.localGroundProj B * sys.P = sys.P ∧ sys.P * sys.localGroundProj B = sys.P := by
  have h_eq : sys.P = sys.localGroundProj Finset.univ := rfl
  rw [h_eq]
  exact sys.localProj_mul_localProj_of_subset_bhm (Finset.subset_univ B)

/-- Every local ground projector $P_B$ commutes with every elementary projector $Q_K$ ($K \in \mathcal{S}(2)$). -/
lemma CommutingProjectorHamiltonian.commute_P_loc_Q_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (B K : Finset (BoxD D L)) (hK : K ∈ boxCubes D L 2) :
    Commute (sys.localGroundProj B) (sys.Q K) := by
  dsimp [CommutingProjectorHamiltonian.localGroundProj, localGroundProjector]
  apply Commute.list_prod_left
  intro p hp
  rcases List.mem_map.mp hp with ⟨C, hC_mem, rfl⟩
  have hC_cube : C ∈ boxCubes D L 2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hC_mem)).1
  exact commute_one_sub_left_bhm (sys.pairwise_commute C hC_cube K hK)

/-- If $A \in \mathcal{S}(2)$ is contained in $B$, then $P_B Q_A = 0$. -/
lemma CommutingProjectorHamiltonian.localProj_mul_check_eq_zero_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (A B : Finset (BoxD D L)) (hA : A ∈ boxCubes D L 2) (hAB : A ⊆ B) :
    sys.localGroundProj B * sys.Q A = 0 := by
  rw [(sys.commute_P_loc_Q_bhm B A hA).eq, sys.check_mul_localProj_eq_zero_bhm A B hA hAB]

/-- Local ground projectors $P_A$ and $P_B$ of a `CommutingProjectorHamiltonian` commute for all regions $A, B$. -/
lemma CommutingProjectorHamiltonian.commute_P_loc {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (A B : Finset (BoxD D L)) :
    Commute (sys.localGroundProj A) (sys.localGroundProj B) := by
  dsimp [CommutingProjectorHamiltonian.localGroundProj, localGroundProjector]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨K, hK_mem, rfl⟩
  have hK_cube : K ∈ boxCubes D L 2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hK_mem)).1
  exact commute_one_sub_right_bhm (sys.commute_P_loc_Q_bhm A K hK_cube)

/-!
## 2. Bravyi–Hastings Corollary 1: Local-to-Global Operator Norm Transfer
-/

/-- **TQO-1 Ground-Space Scalar Bound (`tqo1_scalar_abs_le_norm_bhm`)**:
    If $P \ne 0$ is an orthogonal projection and $P O P = c \, P$, then $\|c\| \le \|O\|$,
    and if $O$ is self-adjoint then $\operatorname{Im}(c) = 0$. -/
lemma tqo1_scalar_abs_le_norm_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {c : ℂ} (hP_proj : IsStarProjection P) (hP_ne : P ≠ 0)
    (hc : P * O * P = c • P) :
    ‖c‖ ≤ ‖O‖ ∧ (IsSelfAdjoint O → c.im = 0) := by
  have h_exists_vec : ∃ ψ : ManyBodyHilbertSpace Site, P ψ ≠ 0 := by
    by_contra h_all
    push_neg at h_all
    exact hP_ne (ContinuousLinearMap.ext h_all)
  rcases h_exists_vec with ⟨ψ₀, hψ₀⟩
  let ϕ := P ψ₀
  have hϕ_ne : ϕ ≠ 0 := hψ₀
  have hϕ_pos : 0 < ‖ϕ‖ := norm_pos_iff.mpr hϕ_ne
  have hP_idem : P * P = P := hP_proj.isIdempotentElem.eq
  have hPϕ : P ϕ = ϕ := by
    change (P * P) ψ₀ = P ψ₀
    rw [hP_idem]
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP_proj.isSelfAdjoint
  have h_inner_eq : inner ℂ ϕ (O ϕ) = c * ((‖ϕ‖ ^ 2 : ℝ) : ℂ) := by
    calc inner ℂ ϕ (O ϕ)
      _ = inner ℂ (P ϕ) (O (P ϕ)) := by rw [hPϕ]
      _ = inner ℂ ϕ ((P * O * P) ϕ) := by
        change inner ℂ (P ϕ) (O (P ϕ)) = inner ℂ ϕ (P (O (P ϕ)))
        rw [← ContinuousLinearMap.adjoint_inner_left P, hP_adj]
      _ = inner ℂ ϕ ((c • P) ϕ) := by rw [hc]
      _ = c * ((‖ϕ‖ ^ 2 : ℝ) : ℂ) := by
        rw [ContinuousLinearMap.smul_apply, hPϕ, inner_smul_right, inner_self_eq_norm_sq_to_K]
        norm_cast
  constructor
  · have h_norm_inner : ‖inner ℂ ϕ (O ϕ)‖ ≤ ‖O‖ * ‖ϕ‖ ^ 2 := by
      calc ‖inner ℂ ϕ (O ϕ)‖
        _ ≤ ‖ϕ‖ * ‖O ϕ‖ := norm_inner_le_norm ϕ (O ϕ)
        _ ≤ ‖ϕ‖ * (‖O‖ * ‖ϕ‖) := mul_le_mul_of_nonneg_left (O.le_opNorm ϕ) (norm_nonneg ϕ)
        _ = ‖O‖ * ‖ϕ‖ ^ 2 := by ring
    rw [h_inner_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg ‖ϕ‖)] at h_norm_inner
    exact le_of_mul_le_mul_right h_norm_inner (sq_pos_of_pos hϕ_pos)
  · intro hO_sa
    have hO_adj : O† = O := ContinuousLinearMap.isSelfAdjoint_iff'.mp hO_sa
    have h_inner_real : (inner ℂ ϕ (O ϕ)).im = 0 := by
      have h_symm : inner ℂ (O ϕ) ϕ = inner ℂ ϕ (O ϕ) := by
        calc inner ℂ (O ϕ) ϕ
          _ = inner ℂ ϕ ((O†) ϕ) := (ContinuousLinearMap.adjoint_inner_right O ϕ ϕ).symm
          _ = inner ℂ ϕ (O ϕ) := by rw [hO_adj]
      have h_conj : starRingEnd ℂ (inner ℂ ϕ (O ϕ)) = inner ℂ ϕ (O ϕ) := by
        rw [inner_conj_symm, h_symm]
      exact Complex.conj_eq_iff_im.mp h_conj
    rw [h_inner_eq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_add] at h_inner_real
    exact (mul_eq_zero.mp h_inner_real).resolve_right (ne_of_gt (sq_pos_of_pos hϕ_pos))

/-- Every star projection $P$ on a Hilbert space has operator norm $\|P\| \le 1$. -/
lemma isStarProjection_norm_le_one_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {P : E →L[ℂ] E} (hP : IsStarProjection P) :
    ‖P‖ ≤ 1 := by
  have h_eq : ‖P‖ ^ 2 = ‖P‖ := by
    rw [sq, ← CStarRing.norm_star_mul_self, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
  nlinarith [norm_nonneg P]

/-- Adjoint symmetry: if $P$ and $O$ are self-adjoint, $c \in \mathbb{R}$, and $(O - c I) P = 0$,
    then $P (O - c I) = 0$. -/
lemma eq_zero_of_mul_eq_zero_of_isSelfAdjoint_bhm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    {P O : E →L[ℂ] E} (hP : IsSelfAdjoint P) (hO : IsSelfAdjoint O) (c : ℝ)
    (h : (O - (c : ℂ) • (1 : E →L[ℂ] E)) * P = 0) :
    P * (O - (c : ℂ) • (1 : E →L[ℂ] E)) = 0 := by
  have h1 : IsSelfAdjoint ((c : ℂ) • (1 : E →L[ℂ] E)) := by
    rw [IsSelfAdjoint, star_smul, star_one, RCLike.star_def, Complex.conj_ofReal]
  have hM : IsSelfAdjoint (O - (c : ℂ) • (1 : E →L[ℂ] E)) := hO.sub h1
  calc P * (O - (c : ℂ) • (1 : E →L[ℂ] E))
    _ = star P * star (O - (c : ℂ) • (1 : E →L[ℂ] E)) := by rw [hP.star_eq, hM.star_eq]
    _ = star ((O - (c : ℂ) • (1 : E →L[ℂ] E)) * P) := (star_mul _ P).symm
    _ = star (0 : E →L[ℂ] E) := by rw [h]
    _ = 0 := star_zero _

/-- Scalar sandwich identity $P (c \cdot I) P = c \cdot (P P)$. -/
lemma mul_smul_one_mul_bhm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : E →L[ℂ] E) (c : ℂ) :
    P * (c • (1 : E →L[ℂ] E)) * P = c • (P * P) := by
  ext ψ
  simp

/-- **Local Block-Diagonal Sandwich Decomposition from TQO-1 and Linear TQO-2**:
    If $O$ is a self-adjoint operator supported on $A = \mathrm{boxCube}(x_0, r)$ ($1 \le r \le L^*$)
    that commutes with the global ground projector $P$ ($[O, P] = 0$), then by TQO-1 and Linear TQO-2
    there exists a real scalar $c \in \mathbb{R}$ with $|c| \le \|O\|$ such that
    $$O = c \cdot I + (I - P_B)(O - c \cdot I)(I - P_B), \qquad \|O - c \cdot I\| \le 2 \|O\|,$$
    where $B = \mathrm{enclosingBoxCube}(x_0, r, \mathrm{linearExpansionRadius}\ C\ r)$. -/
lemma exists_local_sandwich_of_tqo_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star : ℕ} {C : ℝ}
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star)
    (x0 : BoxD D L)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O)
    (hO_supp : IsSupportedOn Site (boxCube x0 r) O)
    (hO_comm : Commute O sys.P) :
    ∃ c : ℝ,
      |c| ≤ ‖O‖ ∧
      ‖O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ ≤ 2 * ‖O‖ ∧
      O = (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) +
        (1 - sys.localGroundProj (enclosingBoxCube x0 r (linearExpansionRadius C r))) *
          (O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) *
          (1 - sys.localGroundProj (enclosingBoxCube x0 r (linearExpansionRadius C r))) := by
  rcases hTQO1 r hr1 hrL x0 O hO_supp with ⟨c_C, hc_C⟩
  have hP_idem : sys.P * sys.P = sys.P := sys.isStarProjection_P_bhm.isIdempotentElem.eq
  have hOP : O * sys.P = c_C • sys.P := by
    calc O * sys.P
      _ = O * (sys.P * sys.P) := by rw [hP_idem]
      _ = (O * sys.P) * sys.P := by rw [mul_assoc]
      _ = (sys.P * O) * sys.P := by rw [hO_comm.eq]
      _ = sys.P * O * sys.P := rfl
      _ = c_C • sys.P := hc_C
  rcases tqo1_scalar_abs_le_norm_bhm sys.isStarProjection_P_bhm sys.frustration_free hc_C with
    ⟨hc_C_norm, hc_C_im⟩
  have hc_im : c_C.im = 0 := hc_C_im hO_sa
  let c : ℝ := c_C.re
  have hc_eq : (c : ℂ) = c_C := Complex.ext rfl hc_im.symm
  have hc_norm : |c| ≤ ‖O‖ := by
    have h1 : ‖(c : ℂ)‖ = ‖c_C‖ := by rw [hc_eq]
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    linarith
  let M := O - (c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  have hM_norm : ‖M‖ ≤ 2 * ‖O‖ := by
    calc ‖M‖
      _ ≤ ‖O‖ + ‖(c : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ :=
        norm_sub_le O _
      _ = ‖O‖ + |c| * ‖(1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖O‖ + |c| * 1 := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ ≤ ‖O‖ + ‖O‖ * 1 := by gcongr
      _ = 2 * ‖O‖ := by ring
  have hMP : M * sys.P = 0 := by
    apply ContinuousLinearMap.ext
    intro ψ
    change (O - (c : ℂ) • 1) (sys.P ψ) = 0
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ← ContinuousLinearMap.mul_apply, hOP,
      ContinuousLinearMap.smul_apply, hc_eq, sub_self]
  have hM_supp : IsSupportedOn Site (boxCube x0 r) M :=
    isSupportedOn_sub_smul_one hO_supp (c : ℂ)
  let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
  have hMP_loc : M * sys.localGroundProj B = 0 :=
    ((hTQO2 r hr1 hrL x0).2 M hM_supp).mp hMP
  have hP_locM : sys.localGroundProj B * M = 0 :=
    eq_zero_of_mul_eq_zero_of_isSelfAdjoint_bhm (sys.isStarProjection_P_loc_bhm B).isSelfAdjoint hO_sa c hMP_loc
  have h_sandwich : (1 - sys.localGroundProj B) * M * (1 - sys.localGroundProj B) = M := by
    calc (1 - sys.localGroundProj B) * M * (1 - sys.localGroundProj B)
      _ = (M - sys.localGroundProj B * M) * (1 - sys.localGroundProj B) := by rw [sub_mul, one_mul]
      _ = M * (1 - sys.localGroundProj B) := by rw [hP_locM, sub_zero]
      _ = M - M * sys.localGroundProj B := by rw [mul_sub, mul_one]
      _ = M := by rw [hMP_loc, sub_zero]
  refine ⟨c, hc_norm, hM_norm, ?_⟩
  rw [h_sandwich]
  dsimp [M]
  abel

/-- For any operator $M$ supported on $A_0$ and any $1$-collar $B_0$ around $A_0$
    (`IsOneCollarOf A0 B0`), the locally projected operator $P_{B_0} M P_{B_0}$ commutes with the
    global ground-space projector $P$. -/
lemma CommutingProjectorHamiltonian.commute_collar_sandwich_P_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {A0 B0 : Finset (BoxD D L)}
    {M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hCollar : IsOneCollarOf A0 B0)
    (hM_supp : IsSupportedOn Site A0 M) :
    Commute (sys.localGroundProj B0 * M * sys.localGroundProj B0) sys.P := by
  dsimp [CommutingProjectorHamiltonian.P, globalGroundProjector, localGroundProjector]
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨K, hK_mem, rfl⟩
  have hK_cube : K ∈ boxCubes D L 2 := (Finset.mem_filter.mp (Finset.mem_toList.mp hK_mem)).1
  apply commute_one_sub_right_bhm
  by_cases hDisj : Disjoint K A0
  · have h_comm_M : Commute M (sys.Q K) :=
      commute_of_isSupportedOn_disjoint hDisj.symm hM_supp (sys.is_supported K hK_cube)
    have h_comm_PB0 : Commute (sys.localGroundProj B0) (sys.Q K) := sys.commute_P_loc_Q_bhm B0 K hK_cube
    exact (h_comm_PB0.mul_left h_comm_M).mul_left h_comm_PB0
  · have hKB0 : K ⊆ B0 := hCollar.2 K hK_cube hDisj
    rw [commute_iff_eq]
    calc (sys.localGroundProj B0 * M * sys.localGroundProj B0) * sys.Q K
      _ = sys.localGroundProj B0 * M * (sys.localGroundProj B0 * sys.Q K) := by rw [mul_assoc]
      _ = 0 := by rw [sys.localProj_mul_check_eq_zero_bhm K B0 hK_cube hKB0, mul_zero]
      _ = (sys.Q K * sys.localGroundProj B0) * M * sys.localGroundProj B0 := by
        rw [sys.check_mul_localProj_eq_zero_bhm K B0 hK_cube hKB0, zero_mul, zero_mul]
      _ = sys.Q K * (sys.localGroundProj B0 * M * sys.localGroundProj B0) := by simp only [mul_assoc]

/-- For any operator $S$ and region $B_0$, the operator $P_{B_0} S S^\dagger P_{B_0}$ is self-adjoint. -/
lemma isSelfAdjoint_collar_mul_adjoint_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (B0 : Finset (BoxD D L))
    (S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    IsSelfAdjoint (sys.localGroundProj B0 * (S * S†) * sys.localGroundProj B0) := by
  rw [IsSelfAdjoint]
  have hB0_sa : star (sys.localGroundProj B0) = sys.localGroundProj B0 :=
    (sys.isStarProjection_P_loc_bhm B0).isSelfAdjoint.star_eq
  change star (sys.localGroundProj B0 * (S * star S) * sys.localGroundProj B0) =
    sys.localGroundProj B0 * (S * star S) * sys.localGroundProj B0
  rw [star_mul, star_mul, star_mul, star_star, hB0_sa]
  simp only [mul_assoc]

set_option maxHeartbeats 800000 in
/-- **Bravyi–Hastings Section 4 Corollary 1 (`corollary_1_norm_P_loc_mul_le_bhm`)**:
    Under TQO-1 and Linear TQO-2 up to cutoff $L^*$, for any local shell $S$ with $S S^\dagger$
    supported on $A_0$ and $1$-collar $B_0 = \mathrm{boxCube}(x_{B_0}, \ell + 2) \subseteq C_0 =
    \mathrm{enclosingBoxCube}(x_{B_0}, \ell + 2, R(\ell + 2))$,
    $$\|P_{C_0} S\| \le \|P S\|.$$ -/
lemma corollary_1_norm_P_loc_mul_le_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star ℓ : ℕ} {C : ℝ}
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ + 2 ≤ L_star)
    (x_B0 : BoxD D L) (A0 : Finset (BoxD D L))
    (S : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hBC0 : boxCube x_B0 (ℓ + 2) ⊆
      enclosingBoxCube x_B0 (ℓ + 2) (linearExpansionRadius C (ℓ + 2)))
    (hCollar : IsOneCollarOf A0 (boxCube x_B0 (ℓ + 2)))
    (hSS_supp : IsSupportedOn Site A0 (S * S†))
    (hN_supp : IsSupportedOn Site (boxCube x_B0 (ℓ + 2))
      (sys.localGroundProj (boxCube x_B0 (ℓ + 2)) * (S * S†) * sys.localGroundProj (boxCube x_B0 (ℓ + 2)))) :
    ‖sys.localGroundProj (enclosingBoxCube x_B0 (ℓ + 2) (linearExpansionRadius C (ℓ + 2))) * S‖ ≤
      ‖sys.P * S‖ := by
  let B0 := boxCube x_B0 (ℓ + 2)
  let C0 := enclosingBoxCube x_B0 (ℓ + 2) (linearExpansionRadius C (ℓ + 2))
  let N := sys.localGroundProj B0 * (S * S†) * sys.localGroundProj B0
  have hN_sa : IsSelfAdjoint N := isSelfAdjoint_collar_mul_adjoint_bhm sys B0 S
  have hN_comm : Commute N sys.P := sys.commute_collar_sandwich_P_bhm hCollar hSS_supp
  rcases exists_local_sandwich_of_tqo_bhm sys hTQO1 hTQO2 (by omega : 1 ≤ ℓ + 2) hℓL
    x_B0 N hN_sa hN_supp hN_comm with ⟨c, _hc_norm, _hM_norm, hN_eq⟩
  have h_PNP : sys.P * N * sys.P = (c : ℂ) • sys.P := by
    have hP_C0 : sys.P * (1 - sys.localGroundProj C0) = 0 := by
      rw [mul_sub, mul_one, (sys.localProj_mul_proj_eq_proj_bhm C0).2, sub_self]
    have hP_idem : sys.P * sys.P = sys.P := sys.isStarProjection_P_bhm.isIdempotentElem.eq
    calc sys.P * N * sys.P
      _ = sys.P * ((c : ℂ) • 1 + (1 - sys.localGroundProj C0) * (N - (c : ℂ) • 1) * (1 - sys.localGroundProj C0)) *
          sys.P := by rw [← hN_eq]
      _ = sys.P * ((c : ℂ) • 1) * sys.P +
          (sys.P * (1 - sys.localGroundProj C0)) * (N - (c : ℂ) • 1) * (1 - sys.localGroundProj C0) * sys.P := by
        rw [mul_add, add_mul]
        simp only [mul_assoc]
      _ = (c : ℂ) • sys.P := by
        rw [mul_smul_one_mul_bhm, hP_idem, hP_C0, zero_mul, zero_mul, zero_mul, add_zero]
  have h_PNP_eq_PS : sys.P * N * sys.P = (sys.P * S) * (sys.P * S)† := by
    have hP_sa : star sys.P = sys.P := sys.isStarProjection_P_bhm.isSelfAdjoint.star_eq
    dsimp [N]
    calc sys.P * (sys.localGroundProj B0 * (S * S†) * sys.localGroundProj B0) * sys.P
      _ = (sys.P * sys.localGroundProj B0) * S * S† * (sys.localGroundProj B0 * sys.P) := by simp only [mul_assoc]
      _ = sys.P * S * S† * sys.P := by
        rw [(sys.localProj_mul_proj_eq_proj_bhm B0).2, (sys.localProj_mul_proj_eq_proj_bhm B0).1]
      _ = (sys.P * S) * (star S * star sys.P) := by
        rw [hP_sa]
        change (sys.P * S * star S) * sys.P = (sys.P * S) * (star S * sys.P)
        simp only [mul_assoc]
      _ = (sys.P * S) * (sys.P * S)† := by
        rw [← star_mul]
        rfl
  have hc_le_norm_PS_sq : |c| ≤ ‖sys.P * S‖ ^ 2 := by
    have h_exists_vec : ∃ ψ : ManyBodyHilbertSpace Site, sys.P ψ ≠ 0 := by
      by_contra h_all
      push_neg at h_all
      exact sys.frustration_free (ContinuousLinearMap.ext h_all)
    rcases h_exists_vec with ⟨ψ₀, hψ₀⟩
    let ϕ := sys.P ψ₀
    have hϕ_pos : 0 < ‖ϕ‖ := norm_pos_iff.mpr hψ₀
    have hPϕ : sys.P ϕ = ϕ := by
      change (sys.P * sys.P) ψ₀ = sys.P ψ₀
      rw [sys.isStarProjection_P_bhm.isIdempotentElem.eq]
    have h_app : ((sys.P * S) * (sys.P * S)†) ϕ = (c : ℂ) • ϕ := by
      rw [← h_PNP_eq_PS, h_PNP, ContinuousLinearMap.smul_apply, hPϕ]
    have h_norm_app : |c| * ‖ϕ‖ ≤ ‖(sys.P * S) * (sys.P * S)†‖ * ‖ϕ‖ := by
      have h1 : ‖(c : ℂ) • ϕ‖ = ‖((sys.P * S) * (sys.P * S)†) ϕ‖ := by rw [h_app]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h1
      rw [h1]
      exact ((sys.P * S) * (sys.P * S)†).le_opNorm ϕ
    have hc_le_op : |c| ≤ ‖(sys.P * S) * (sys.P * S)†‖ :=
      le_of_mul_le_mul_right h_norm_app hϕ_pos
    have h_cstar : ‖(sys.P * S) * (sys.P * S)†‖ = ‖sys.P * S‖ ^ 2 := by
      rw [sq, ← CStarRing.norm_self_mul_star]
      rfl
    rwa [h_cstar] at hc_le_op

  have h_PC0_N_PC0 : sys.localGroundProj C0 * N * sys.localGroundProj C0 = (c : ℂ) • sys.localGroundProj C0 := by
    have hC0_idem : sys.localGroundProj C0 * sys.localGroundProj C0 = sys.localGroundProj C0 :=
      (sys.isStarProjection_P_loc_bhm C0).isIdempotentElem.eq
    have hC0_one_sub : sys.localGroundProj C0 * (1 - sys.localGroundProj C0) = 0 := by
      rw [mul_sub, mul_one, hC0_idem, sub_self]
    calc sys.localGroundProj C0 * N * sys.localGroundProj C0
      _ = sys.localGroundProj C0 * ((c : ℂ) • 1 + (1 - sys.localGroundProj C0) * (N - (c : ℂ) • 1) * (1 - sys.localGroundProj C0)) *
          sys.localGroundProj C0 := by rw [← hN_eq]
      _ = sys.localGroundProj C0 * ((c : ℂ) • 1) * sys.localGroundProj C0 +
          (sys.localGroundProj C0 * (1 - sys.localGroundProj C0)) * (N - (c : ℂ) • 1) * (1 - sys.localGroundProj C0) * sys.localGroundProj C0 := by
        rw [mul_add, add_mul]
        simp only [mul_assoc]
      _ = (c : ℂ) • sys.localGroundProj C0 := by
        rw [mul_smul_one_mul_bhm, hC0_idem, hC0_one_sub, zero_mul, zero_mul, zero_mul, add_zero]
  have h_PC0_eq_PC0S : sys.localGroundProj C0 * N * sys.localGroundProj C0 = (sys.localGroundProj C0 * S) * (sys.localGroundProj C0 * S)† := by
    have hC0_sa : star (sys.localGroundProj C0) = sys.localGroundProj C0 :=
      (sys.isStarProjection_P_loc_bhm C0).isSelfAdjoint.star_eq
    dsimp [N]
    calc sys.localGroundProj C0 * (sys.localGroundProj B0 * (S * S†) * sys.localGroundProj B0) * sys.localGroundProj C0
      _ = (sys.localGroundProj C0 * sys.localGroundProj B0) * S * S† * (sys.localGroundProj B0 * sys.localGroundProj C0) := by simp only [mul_assoc]
      _ = sys.localGroundProj C0 * S * S† * sys.localGroundProj C0 := by
        rw [(sys.localProj_mul_localProj_of_subset_bhm hBC0).2, (sys.localProj_mul_localProj_of_subset_bhm hBC0).1]
      _ = (sys.localGroundProj C0 * S) * (star S * star (sys.localGroundProj C0)) := by
        rw [hC0_sa]
        change (sys.localGroundProj C0 * S * star S) * sys.localGroundProj C0 = (sys.localGroundProj C0 * S) * (star S * sys.localGroundProj C0)
        simp only [mul_assoc]
      _ = (sys.localGroundProj C0 * S) * (sys.localGroundProj C0 * S)† := by
        rw [← star_mul]
        rfl
  have h_norm_PC0_le : ‖sys.localGroundProj C0‖ ≤ 1 :=
    isStarProjection_norm_le_one_bhm (sys.isStarProjection_P_loc_bhm C0)
  have h_sq_le : ‖sys.localGroundProj C0 * S‖ ^ 2 ≤ ‖sys.P * S‖ ^ 2 := by
    calc ‖sys.localGroundProj C0 * S‖ ^ 2
      _ = ‖(sys.localGroundProj C0 * S) * (sys.localGroundProj C0 * S)†‖ := by
        rw [sq, ← CStarRing.norm_self_mul_star]
        rfl
      _ = ‖(c : ℂ) • sys.localGroundProj C0‖ := by rw [← h_PC0_eq_PC0S, h_PC0_N_PC0]
      _ = |c| * ‖sys.localGroundProj C0‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left h_norm_PC0_le (abs_nonneg c)
      _ = |c| := mul_one |c|
      _ ≤ ‖sys.P * S‖ ^ 2 := hc_le_norm_PS_sq
  nlinarith [norm_nonneg (sys.localGroundProj C0 * S), norm_nonneg (sys.P * S)]

/-- Reverse inclusion norm bound: since $P = P P_{C_k}$ and $\|P\| \le 1$, $\|P O_k\| \le \|P_{C_k} O_k\|$. -/
lemma norm_P_mul_le_norm_P_loc_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    (C_k : Finset (BoxD D L))
    (O_k : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖sys.P * O_k‖ ≤ ‖sys.localGroundProj C_k * O_k‖ := by
  have h_norm_P_le : ‖sys.P‖ ≤ 1 := isStarProjection_norm_le_one_bhm sys.isStarProjection_P_bhm
  calc ‖sys.P * O_k‖
    _ = ‖(sys.P * sys.localGroundProj C_k) * O_k‖ := by rw [(sys.localProj_mul_proj_eq_proj_bhm C_k).2]
    _ = ‖sys.P * (sys.localGroundProj C_k * O_k)‖ := by rw [mul_assoc]
    _ ≤ ‖sys.P‖ * ‖sys.localGroundProj C_k * O_k‖ :=
      ContinuousLinearMap.opNorm_comp_le sys.P (sys.localGroundProj C_k * O_k)
    _ ≤ 1 * ‖sys.localGroundProj C_k * O_k‖ :=
      mul_le_mul_of_nonneg_right h_norm_P_le (norm_nonneg (sys.localGroundProj C_k * O_k))
    _ = ‖sys.localGroundProj C_k * O_k‖ := one_mul _

/-- **Local-to-Global $C^*$-Norm Equality (`local_to_global_cstar_norm_eq`)**:
    Under `sys.SatisfiesTQO1 L_star` and `sys.SatisfiesLinearTQO2 L_star C`, for any operator $O_k$
    with $O_k O_k^\dagger$ supported on $A_k$ and 1-collar $B_k = \mathrm{boxCube}\;x_B\;(k+2) \subseteq C_k$,
    $$\|P_{C_k} O_k\| = \|P O_k\|.$$ -/
theorem local_to_global_cstar_norm_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star k : ℕ} {C : ℝ}
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    (hk1 : 1 ≤ k) (hkL : k + 2 ≤ L_star)
    (x_B : BoxD D L) (A_k : Finset (BoxD D L))
    (O_k : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hBC_k : boxCube x_B (k + 2) ⊆
      enclosingBoxCube x_B (k + 2) (linearExpansionRadius C (k + 2)))
    (hCollar : IsOneCollarOf A_k (boxCube x_B (k + 2)))
    (hOO_supp : IsSupportedOn Site A_k (O_k * O_k†))
    (hN_supp : IsSupportedOn Site (boxCube x_B (k + 2))
      (sys.localGroundProj (boxCube x_B (k + 2)) * (O_k * O_k†) * sys.localGroundProj (boxCube x_B (k + 2)))) :
    ‖sys.localGroundProj (enclosingBoxCube x_B (k + 2) (linearExpansionRadius C (k + 2))) * O_k‖ =
      ‖sys.P * O_k‖ := by
  exact le_antisymm
    (corollary_1_norm_P_loc_mul_le_bhm sys hTQO1 hTQO2 hk1 hkL x_B A_k O_k hBC_k hCollar hOO_supp hN_supp)
    (norm_P_mul_le_norm_P_loc_mul sys
      (enclosingBoxCube x_B (k + 2) (linearExpansionRadius C (k + 2))) O_k)

/-- **Bravyi–Hastings Section 4 Corollary 1 (`tqo2_norm_mul_P_loc_eq_norm_mul_P`)**:
    Under TQO-1 and Linear TQO-2 up to cutoff $L^*$, for any local operator $O_k$ with $O_k O_k^\dagger$
    supported on $A_k$ and $1$-collar $B_k = \mathrm{boxCube}(x_B, k + 2) \subseteq C_k$,
    $$\|P_{C_k} O_k\| = \|P O_k\|.$$ -/
theorem tqo2_norm_mul_P_loc_eq_norm_mul_P {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star : ℕ} {C : ℝ}
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    {k : ℕ} (hk1 : 1 ≤ k) (hkL : k + 2 ≤ L_star)
    (x_B : BoxD D L) (A_k : Finset (BoxD D L))
    (O_k : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hBC_k : boxCube x_B (k + 2) ⊆
      enclosingBoxCube x_B (k + 2) (linearExpansionRadius C (k + 2)))
    (hCollar : IsOneCollarOf A_k (boxCube x_B (k + 2)))
    (hOO_supp : IsSupportedOn Site A_k (O_k * O_k†))
    (hN_supp : IsSupportedOn Site (boxCube x_B (k + 2))
      (sys.localGroundProj (boxCube x_B (k + 2)) * (O_k * O_k†) * sys.localGroundProj (boxCube x_B (k + 2)))) :
    ‖sys.localGroundProj (enclosingBoxCube x_B (k + 2) (linearExpansionRadius C (k + 2))) * O_k‖ =
      ‖sys.P * O_k‖ :=
  local_to_global_cstar_norm_eq sys hTQO1 hTQO2 hk1 hkL x_B A_k O_k hBC_k hCollar hOO_supp hN_supp

/-- **Sector-Filtered Local-to-Global Kernel & $C^*$-Norm Transfer (`sector_tqo2_norm_mul_P_loc_eq_norm_mul_P0`)**:
    Under `SatisfiesSectorFilteredLinearTQO2 sys Pi_sec L_star C`, for every scale $1 \le r \le L^*$,
    site $x_0 \in \mathrm{BoxD}\ D\ L$, and operator $O_A$ supported on $A = \mathrm{boxCube}(x_0, r)$
    with enclosing cube $B = \mathrm{enclosingBoxCube}(x_0, r, \mathrm{linearExpansionRadius}\ C\ r)$,
    $$O_A P_0 = 0 \iff O_A \Pi_{\mathrm{sec}} P_B = 0.$$ -/
theorem sector_tqo2_norm_mul_P_loc_eq_norm_mul_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {L_star : ℕ} {C : ℝ}
    (hTQO2 : SatisfiesSectorFilteredLinearTQO2 sys Pi_sec L_star C)
    {r : ℕ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star) (x0 : BoxD D L)
    {O_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO_A : IsSupportedOn Site (boxCube x0 r) O_A) :
    let B := enclosingBoxCube x0 r (linearExpansionRadius C r)
    (O_A * sys.P0 = 0 ↔ O_A * Pi_sec * sys.localGroundProj B = 0) :=
  hTQO2.2.2.2.2 r hr1 hrL x0 O_A hO_A
