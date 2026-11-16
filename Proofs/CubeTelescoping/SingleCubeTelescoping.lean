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
import Proofs.CubeTelescoping.LocalToGlobalNormTransfer
import Proofs.BandLimitedFilter.EigenprojEvolutionAndBlockDecomp

/-!
# Self-Adjoint Conditional Expectations and Single-Cube 3-Epsilon Telescoping

Proves Hilbert-space self-adjointness of `partialTrace` (`partialTrace_adjoint_bhm`) and the normalized conditional expectation `condExp` (`isSelfAdjoint_condExp_bhm`). Establishes the abstract $3\varepsilon_k$ single-cube approximation bound (`telescoping_norm_bounds_abstract`, `norm_sub_localTelescopingApprox_le`, `single_cube_telescoping_bound`) for block-diagonal operators under TQO-1 and Linear TQO-2.

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Lemma 7.1 (`lem:norm-transfer`)
* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

/-!
## 1. Adjoint of `partialTrace` and `condExp`, and BH11 Lemma 4 Single-Cube Telescoping
-/

/-- Inner product with a global computational basis state `basisVecGlobal Site σ` extracts the `σ`-coordinate. -/
lemma inner_basisVecGlobal_left_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (σ : ManyBodyConfig Site) (v : ManyBodyHilbertSpace Site) :
    inner ℂ (basisVecGlobal Site σ) v = v.ofLp σ := by
  simp [basisVecGlobal, PiLp.inner_apply, apply_ite conj, mul_comm]

/-- Each partial trace matrix element `partialTraceEntry Site A ρ γ α β` is a basis inner product. -/
lemma partialTraceEntry_eq_inner_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (γ : LocalConfig Site (Finset.univ \ A))
    (α β : LocalConfig Site A) :
    partialTraceEntry Site A ρ γ α β =
      inner ℂ (basisVecGlobal Site (combineConfig A α γ))
        (ρ (basisVecGlobal Site (combineConfig A β γ))) := by
  rw [inner_basisVecGlobal_left_bhm]
  rfl

/-- Complex conjugation of `partialTraceEntry` transposes indices and takes the operator adjoint `ρ†`. -/
lemma star_partialTraceEntry_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (γ : LocalConfig Site (Finset.univ \ A))
    (α β : LocalConfig Site A) :
    star (partialTraceEntry Site A ρ γ β α) = partialTraceEntry Site A (ρ†) γ α β := by
  rw [partialTraceEntry_eq_inner_bhm, partialTraceEntry_eq_inner_bhm,
    RCLike.star_def, inner_conj_symm, ContinuousLinearMap.adjoint_inner_right]

/-- Algebraic summation identity for the sesquilinear form of `partialTrace` and its adjoint. -/
lemma star_sum_partialTrace_helper_bhm {α_t γ_t : Type*} [Fintype α_t] [Fintype γ_t]
    (E E_adj : γ_t → α_t → α_t → ℂ) (φ ψ F_lhs F_rhs : α_t → ℂ)
    (h_lhs : ∀ α, F_lhs α = ∑ γ : γ_t, ∑ β : α_t, E γ α β * φ β)
    (h_rhs : ∀ β, F_rhs β = ∑ γ : γ_t, ∑ α : α_t, E_adj γ β α * ψ α)
    (hE : ∀ γ α β, star (E γ β α) = E_adj γ α β) :
    (∑ α : α_t, ψ α * star (F_lhs α)) =
    ∑ β : α_t, F_rhs β * star (φ β) := by
  simp only [h_lhs, h_rhs, star_sum, star_mul, hE, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- Explicit coordinate expansion of the `EuclideanSpace ℂ ι` inner product. -/
lemma inner_euclideanSpace_eq_bhm {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    inner ℂ x y = ∑ i : ι, y.ofLp i * star (x.ofLp i) := by
  rw [PiLp.inner_apply]
  rfl

/-- Characterization of the Hilbert-space adjoint on `EuclideanSpace ℂ ι` via coordinate sums. -/
lemma euclideanSpace_adjoint_eq_of_matrix_bhm {ι : Type*} [Fintype ι]
    (T S : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (h : ∀ φ ψ : EuclideanSpace ℂ ι,
      (∑ α : ι, ψ.ofLp α * star ((T φ).ofLp α)) =
        ∑ β : ι, (S ψ).ofLp β * star (φ.ofLp β)) :
    T† = S := by
  ext ψ : 1
  apply ext_inner_left ℂ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_right, inner_euclideanSpace_eq_bhm, inner_euclideanSpace_eq_bhm]
  exact h φ ψ

/-- Coordinate formula for `partialTrace Site A ρ φ` at local configuration `α`. -/
lemma partialTrace_apply_ofLp_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (φ : LocalHilbertSpace Site A) (α : LocalConfig Site A) :
    (partialTrace Site A ρ φ).ofLp α =
      ∑ γ : LocalConfig Site (Finset.univ \ A), ∑ β : LocalConfig Site A,
        partialTraceEntry Site A ρ γ α β * φ.ofLp β := rfl

/-- The partial trace commutes with the Hilbert-space adjoint: `(partialTrace Site A ρ)† = partialTrace Site A (ρ†)`. -/
lemma partialTrace_adjoint_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (partialTrace Site A ρ)† = partialTrace Site A (ρ†) :=
  euclideanSpace_adjoint_eq_of_matrix_bhm (partialTrace Site A ρ) (partialTrace Site A (ρ†))
    (fun φ ψ => star_sum_partialTrace_helper_bhm
      (partialTraceEntry Site A ρ) (partialTraceEntry Site A (ρ†))
      φ.ofLp ψ.ofLp
      (partialTrace Site A ρ φ).ofLp (partialTrace Site A (ρ†) ψ).ofLp
      (partialTrace_apply_ofLp_bhm A ρ φ) (partialTrace_apply_ofLp_bhm A (ρ†) ψ)
      (star_partialTraceEntry_bhm A ρ))

/-- The partial-trace conditional expectation `condExp Site A` commutes with the Hilbert-space adjoint. -/
lemma condExp_adjoint_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    (ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (condExp Site A ρ)† = condExp Site A (ρ†) := by
  dsimp [condExp]
  rw [cylinderOp_adjoint]
  congr 1
  change star (((Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ)⁻¹) • partialTrace Site A ρ) =
    ((Fintype.card (LocalConfig Site (Finset.univ \ A)) : ℂ)⁻¹) • partialTrace Site A (ρ†)
  rw [star_smul, star_inv₀, star_natCast, ← partialTrace_adjoint_bhm]
  rfl

/-- Applying `condExp Site A` to a self-adjoint operator `ρ` yields a self-adjoint operator. -/
lemma isSelfAdjoint_condExp_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A : Finset (BoxD D L))
    {ρ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hρ : IsSelfAdjoint ρ) :
    IsSelfAdjoint (condExp Site A ρ) := by
  rw [isSelfAdjoint_iff]
  change (condExp Site A ρ)† = condExp Site A ρ
  rw [condExp_adjoint_bhm, show ρ† = star ρ from rfl, hρ.star_eq]

/-- When $1 \le C$, $r \le \lceil C r \rceil = \mathrm{linearExpansionRadius}\ C\ r$. -/
lemma self_le_linearExpansionRadius_bhm {C : ℝ} (hC : 1 ≤ C) (r : ℕ) :
    r ≤ linearExpansionRadius C r := by
  dsimp [linearExpansionRadius]
  have hr : (r : ℝ) ≤ C * (r : ℝ) := by
    calc (r : ℝ)
      _ = 1 * (r : ℝ) := (one_mul _).symm
      _ ≤ C * (r : ℝ) := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg r)
  exact_mod_cast le_trans hr (Nat.le_ceil _)

/-- Noncommutative ring decomposition of $X - (1 - P_C) O (1 - P_C)$ into tail error $(X - O)$ and
    projected $O$-boundary terms $P_C O + (1 - P_C)(O P_C)$. -/
lemma ring_telescoping_diff_decomp {R : Type*} [Ring R] (P_C X O : R) :
    X - (1 - P_C) * O * (1 - P_C) =
      ((X - O) + P_C * O) + (1 - P_C) * (O * P_C) := by
  noncomm_ring

/-- **Abstract BH11 Lemma 4 Sharpened $3\varepsilon$ Telescoping Norm Bound (`telescoping_norm_bounds_abstract`)**:
    Given $P X = 0$, the Corollary 1 bound $\|P_C O\| \le \|P O\|$, and the tail bound $\|X - O\| \le \varepsilon$,
    proves $\|P_C X\| \le 2\varepsilon$, $\|X P_C\| \le 2\varepsilon$, and
    $\|X - (1 - P_C) O (1 - P_C)\| \le 3\varepsilon$. -/
lemma telescoping_norm_bounds_abstract {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (P P_C X O : E →L[ℂ] E) (ε : ℝ)
    (hP_proj : IsStarProjection P)
    (hPC_proj : IsStarProjection P_C)
    (hX_sa : IsSelfAdjoint X)
    (hO_sa : IsSelfAdjoint O)
    (hPX : P * X = 0)
    (h_cor1 : ‖P_C * O‖ ≤ ‖P * O‖)
    (h_tail : ‖X - O‖ ≤ ε) :
    let M := (1 - P_C) * O * (1 - P_C)
    IsSelfAdjoint M ∧
    ‖P_C * X‖ ≤ 2 * ε ∧
    ‖X * P_C‖ ≤ 2 * ε ∧
    ‖X - M‖ ≤ bhmTelescopingFactor * ε := by
  intro M
  have hM_sa : IsSelfAdjoint M := by
    rw [isSelfAdjoint_iff]
    dsimp [M]
    rw [star_mul, star_mul, (hPC_proj.one_sub).isSelfAdjoint.star_eq, hO_sa.star_eq, mul_assoc]
  have hP_norm : ‖P‖ ≤ 1 := isStarProjection_norm_le_one_bhm hP_proj
  have hPC_norm : ‖P_C‖ ≤ 1 := isStarProjection_norm_le_one_bhm hPC_proj
  have h1PC_norm : ‖1 - P_C‖ ≤ 1 := isStarProjection_norm_le_one_bhm hPC_proj.one_sub
  have h_PO_eq : P * O = -(P * (X - O)) := by
    rw [mul_sub P X O, hPX, zero_sub, neg_neg]
  have h_PO_norm : ‖P * O‖ ≤ ε := by
    rw [h_PO_eq, norm_neg]
    calc ‖P * (X - O)‖
      _ ≤ ‖P‖ * ‖X - O‖ := norm_mul_le _ _
      _ ≤ 1 * ε := mul_le_mul hP_norm h_tail (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε
  have h_PCO_norm : ‖P_C * O‖ ≤ ε := le_trans h_cor1 h_PO_norm
  have h_PCX_eq : P_C * X = P_C * (X - O) + P_C * O := by
    rw [mul_sub, sub_add_cancel]
  have h_PCX_norm : ‖P_C * X‖ ≤ 2 * ε := by
    rw [h_PCX_eq]
    have h1 : ‖P_C * (X - O)‖ ≤ ε := by
      calc ‖P_C * (X - O)‖
        _ ≤ ‖P_C‖ * ‖X - O‖ := norm_mul_le _ _
        _ ≤ 1 * ε := mul_le_mul hPC_norm h_tail (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
    calc ‖P_C * (X - O) + P_C * O‖
      _ ≤ ‖P_C * (X - O)‖ + ‖P_C * O‖ := norm_add_le _ _
      _ ≤ ε + ε := add_le_add h1 h_PCO_norm
      _ = 2 * ε := by ring
  have h_XPC_star : X * P_C = (P_C * X)† := by
    change X * P_C = star (P_C * X)
    rw [star_mul, hX_sa.star_eq, hPC_proj.isSelfAdjoint.star_eq]
  have h_XPC_norm : ‖X * P_C‖ ≤ 2 * ε := by
    rw [h_XPC_star,
      (ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).norm_map]
    exact h_PCX_norm
  have h_OPC_star : O * P_C = (P_C * O)† := by
    change O * P_C = star (P_C * O)
    rw [star_mul, hO_sa.star_eq, hPC_proj.isSelfAdjoint.star_eq]
  have h_OPC_norm : ‖O * P_C‖ ≤ ε := by
    rw [h_OPC_star,
      (ContinuousLinearMap.adjoint : (E →L[ℂ] E) ≃ₗᵢ⋆[ℂ] (E →L[ℂ] E)).norm_map]
    exact h_PCO_norm
  have h_1PC_OPC : ‖(1 - P_C) * (O * P_C)‖ ≤ ε := by
    calc ‖(1 - P_C) * (O * P_C)‖
      _ ≤ ‖1 - P_C‖ * ‖O * P_C‖ := norm_mul_le _ _
      _ ≤ 1 * ε := mul_le_mul h1PC_norm h_OPC_norm (norm_nonneg _) zero_le_one
      _ = ε := one_mul _
  have h_XM_norm : ‖X - M‖ ≤ bhmTelescopingFactor * ε := by
    dsimp [M, bhmTelescopingFactor]
    rw [ring_telescoping_diff_decomp P_C X O]
    have h_part1 : ‖(X - O) + P_C * O‖ ≤ 2 * ε := by
      calc ‖(X - O) + P_C * O‖
        _ ≤ ‖X - O‖ + ‖P_C * O‖ := norm_add_le _ _
        _ ≤ ε + ε := add_le_add h_tail h_PCO_norm
        _ = 2 * ε := by ring
    calc ‖((X - O) + P_C * O) + (1 - P_C) * (O * P_C)‖
      _ ≤ ‖(X - O) + P_C * O‖ + ‖(1 - P_C) * (O * P_C)‖ := norm_add_le _ _
      _ ≤ 2 * ε + ε := add_le_add h_part1 h_1PC_OPC
      _ = 3 * ε := by ring
  exact ⟨hM_sa, h_PCX_norm, h_XPC_norm, h_XM_norm⟩

/-- **BH11 Lemma 4 (`lemma:shell`) Local Telescoping Approximation Bound (`norm_sub_localTelescopingApprox_le`)**:
    Under `sys.SatisfiesTQO1 L_star` and `sys.SatisfiesLinearTQO2 L_star C` with $1 \le C$, for any site $u \in \Lambda$,
    scale $1 \le k$ with $k + 2 \le L^*$, and self-adjoint off-diagonal operator $X_u'$ annihilated by
    `sys.P` with $\|X_u' - \mathbb{E}_{A_k}(X_u')\| \le \varepsilon_k$, the local approximation
    $M_k(u) = \mathrm{singleCubeApproxM}\;\mathrm{sys}\;C\;u\;k\;X_u'$ is self-adjoint, supported on
    $C_k(u)$, annihilated by `sys.P`, and satisfies $\|X_u' - M_k(u)\| \le 3 \varepsilon_k$. -/
lemma norm_sub_localTelescopingApprox_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    (u : BoxD D L) {k : ℕ} (hk1 : 1 ≤ k) (hkL : k + 2 ≤ L_star)
    {X_u' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {ε_k : ℝ}
    (hX_sa : IsSelfAdjoint X_u')
    (hPX : sys.P * X_u' = 0)
    (h_tail : ‖X_u' - condExp Site (boxCube u k) X_u'‖ ≤ ε_k) :
    let C_k := singleCubeSupportC C u k
    let M_k := singleCubeApproxM sys C u k X_u'
    IsSelfAdjoint M_k ∧
    IsSupportedOn Site C_k M_k ∧
    M_k * sys.P = 0 ∧
    sys.P * M_k = 0 ∧
    Commute M_k sys.P ∧
    ‖sys.localGroundProj C_k * X_u'‖ ≤ 2 * ε_k ∧
    ‖X_u' * sys.localGroundProj C_k‖ ≤ 2 * ε_k ∧
    ‖X_u' - M_k‖ ≤ bhmTelescopingFactor * ε_k := by
  let A_k := boxCube u k
  let x_B := shiftDownOne u
  let B_k := boxCube x_B (k + 2)
  let C_k := singleCubeSupportC C u k
  let O_k := condExp Site A_k X_u'
  let M_k := singleCubeApproxM sys C u k X_u'
  have hk_ne : k ≠ 0 := by omega
  have hM_eq : M_k = localTelescopingApprox sys C u k X_u' := by
    dsimp [M_k, singleCubeApproxM]
    rw [if_neg hk_ne]
  have hO_sa : IsSelfAdjoint O_k := isSelfAdjoint_condExp_bhm A_k hX_sa
  have hO_supp : IsSupportedOn Site A_k O_k := ⟨_, rfl⟩
  have hCollar : IsOneCollarOf A_k B_k := isOneCollarOf_boxCube_shiftDownOne u k
  have hBC_k : B_k ⊆ C_k :=
    boxCube_subset_enclosingBoxCube x_B (self_le_linearExpansionRadius_bhm hC (k + 2))
  have hA_C : A_k ⊆ C_k := Finset.Subset.trans hCollar.1 hBC_k
  have hOO_supp : IsSupportedOn Site A_k (O_k * O_k†) :=
    isSupportedOn_mul A_k hO_supp (isSupportedOn_adjoint A_k hO_supp)
  have hN_supp : IsSupportedOn Site B_k (sys.localGroundProj B_k * (O_k * O_k†) * sys.localGroundProj B_k) :=
    isSupportedOn_mul B_k
      (isSupportedOn_mul B_k (sys.isSupportedOn_P_loc B_k)
        (isSupportedOn_mono hCollar.1 hOO_supp))
      (sys.isSupportedOn_P_loc B_k)
  have h1PC_supp : IsSupportedOn Site C_k (1 - sys.localGroundProj C_k) :=
    isSupportedOn_sub C_k (isSupportedOn_one C_k) (sys.isSupportedOn_P_loc C_k)
  have hM_supp : IsSupportedOn Site C_k M_k := by
    rw [hM_eq]
    exact isSupportedOn_mul C_k
      (isSupportedOn_mul C_k h1PC_supp (isSupportedOn_mono hA_C hO_supp))
      h1PC_supp
  have h1PC_P : (1 - sys.localGroundProj C_k) * sys.P = 0 := by
    rw [sub_mul, one_mul, (sys.localProj_mul_proj_eq_proj_bhm C_k).1, sub_self]
  have hP_1PC : sys.P * (1 - sys.localGroundProj C_k) = 0 := by
    rw [mul_sub, mul_one, (sys.localProj_mul_proj_eq_proj_bhm C_k).2, sub_self]
  have hMP : M_k * sys.P = 0 := by
    rw [hM_eq]
    dsimp [localTelescopingApprox]
    rw [mul_assoc, h1PC_P, mul_zero]
  have hPM : sys.P * M_k = 0 := by
    rw [hM_eq]
    dsimp [localTelescopingApprox]
    rw [← mul_assoc, ← mul_assoc, hP_1PC, zero_mul, zero_mul]
  have hM_comm : Commute M_k sys.P := by
    rw [commute_iff_eq, hMP, hPM]
  have h_cor1 : ‖sys.localGroundProj C_k * O_k‖ ≤ ‖sys.P * O_k‖ :=
    corollary_1_norm_P_loc_mul_le_bhm sys hTQO1 hTQO2 hk1 hkL x_B A_k O_k hBC_k hCollar hOO_supp hN_supp
  rcases telescoping_norm_bounds_abstract sys.P (sys.localGroundProj C_k) X_u' O_k ε_k
    sys.isStarProjection_P_bhm (sys.isStarProjection_P_loc_bhm C_k) hX_sa hO_sa hPX h_cor1 h_tail with
    ⟨hM_sa, h_PCX, h_XPC, h_XM⟩
  change IsSelfAdjoint (localTelescopingApprox sys C u k X_u') at hM_sa
  change ‖X_u' - localTelescopingApprox sys C u k X_u'‖ ≤ bhmTelescopingFactor * ε_k at h_XM
  rw [← hM_eq] at hM_sa h_XM
  exact ⟨hM_sa, hM_supp, hMP, hPM, hM_comm, h_PCX, h_XPC, h_XM⟩

/-- **Bravyi–Hastings Section 4 Lemma 3 (`single_cube_telescoping_bound`)**:
    Let $X'$ be a self-adjoint operator with $P X' = 0$ and
    $\|X' - \mathbb{E}_{\mathrm{boxCube}(u, k)}(X')\| \le \varepsilon_k$ for $1 \le k$ and $k + 2 \le L^*$.
    Under `1 ≤ C`, `sys.SatisfiesTQO1 L_star`, and `sys.SatisfiesLinearTQO2 L_star C`, the local
    telescoping approximation $M_k(u) = \mathrm{singleCubeApproxM}\;\mathrm{sys}\;C\;u\;k\;X'$ is
    supported on $C_k(u) = \mathrm{singleCubeSupportC}\;C\;u\;k$, annihilates $P$ from both sides,
    and satisfies $\|X' - M_k(u)\| \le 3 \varepsilon_k$. -/
theorem single_cube_telescoping_bound {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (sys : CommutingProjectorHamiltonian D L Site)
    {L_star : ℕ} {C : ℝ} (hC : 1 ≤ C)
    (hTQO1 : sys.SatisfiesTQO1 L_star)
    (hTQO2 : sys.SatisfiesLinearTQO2 L_star C)
    (u : BoxD D L) {k : ℕ} (hk1 : 1 ≤ k) (hkL : k + 2 ≤ L_star)
    {X' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {ε_k : ℝ}
    (hX_sa : IsSelfAdjoint X')
    (hPX : sys.P * X' = 0)
    (h_approx : ‖X' - condExp Site (boxCube u k) X'‖ ≤ ε_k) :
    let M_k := singleCubeApproxM sys C u k X'
    IsSupportedOn Site (singleCubeSupportC C u k) M_k ∧
    M_k * sys.P = 0 ∧ sys.P * M_k = 0 ∧
    ‖X' - M_k‖ ≤ bhmTelescopingFactor * ε_k := by
  rcases norm_sub_localTelescopingApprox_le sys hC hTQO1 hTQO2 u hk1 hkL hX_sa hPX h_approx with
    ⟨_hM_sa, hM_supp, hMP, hPM, _hM_comm, _h_PCX, _h_XPC, h_XM⟩
  exact ⟨hM_supp, hMP, hPM, h_XM⟩

