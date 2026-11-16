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

import Proofs.GapBootstrap.CheckCommutingTwoBlockStability

/-!
# Eigenbasis Spectral Alignment Unitaries and Conjugated-Hamiltonian Commutation

Constructs the ordered eigenbasis intertwiner `spectralAlignmentUnitary` mapping sorted eigenstates of `sys.H0` to sorted eigenstates of `sys.H0 + V.totalPerturbation`, proves exact commutation of the conjugated Hamiltonian with `sys.P0` and `sys.H0`, and uses Courant–Fischer eigenvalue comparison (`sortedEigenvalues_sub_le_of_isometry_form_bound`) to transfer relative form bounds to sorted eigenvalue differences.

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Promotion of `LinearIsometryEquiv` to `unitary` & Orthonormal Basis Intertwiner
-/

/-- Canonical promotion of a `LinearIsometryEquiv` $U : E \simeq_{\ell i} E$ to `unitary (E →L[ℂ] E)`. -/
def linearIsometryEquivToUnitary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) : unitary (E →L[ℂ] E) :=
  let u : E →L[ℂ] E := U.toLinearIsometry.toContinuousLinearMap
  let v : E →L[ℂ] E := U.symm.toLinearIsometry.toContinuousLinearMap
  have huv : u * v = 1 := by
    ext x; exact U.apply_symm_apply x
  have hu_star_u : star u * u = 1 := by
    ext x
    apply ext_inner_right ℂ
    intro y
    change inner ℂ ((u† * u) x) y = inner ℂ x y
    rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_left]
    exact U.inner_map_map x y
  have h_star_eq : star u = v := by
    calc star u
      _ = star u * 1 := (mul_one _).symm
      _ = star u * (u * v) := by rw [huv]
      _ = (star u * u) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [hu_star_u, one_mul]
  ⟨u, Unitary.mem_iff.mpr ⟨hu_star_u, by rw [h_star_eq, huv]⟩⟩

@[simp]
lemma linearIsometryEquivToUnitary_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (x : E) :
    (linearIsometryEquivToUnitary U).1 x = U x :=
  rfl

@[simp]
lemma linearIsometryEquivToUnitary_adj_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (x : E) :
    ((linearIsometryEquivToUnitary U).1†) x = U.symm x := by
  let u : E →L[ℂ] E := U.toLinearIsometry.toContinuousLinearMap
  let v : E →L[ℂ] E := U.symm.toLinearIsometry.toContinuousLinearMap
  have huv : u * v = 1 := by ext y; exact U.apply_symm_apply y
  have hu_star_u : (u†) * u = 1 := Unitary.coe_star_mul_self (linearIsometryEquivToUnitary U)
  have h_adj : u† = v := by
    calc u†
      _ = (u†) * (u * v) := by rw [huv, mul_one]
      _ = ((u†) * u) * v := (mul_assoc _ _ _).symm
      _ = v := by rw [hu_star_u, one_mul]
  exact congrFun (congrArg DFunLike.coe h_adj) x

/-- Unitary operator intertwining two orthonormal bases $b_1, b_2$ ($U (b_1 i) = b_2 i$). -/
def orthonormalBasisIntertwiner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι_b : Type*} [Fintype ι_b] [DecidableEq ι_b]
    (b₁ b₂ : OrthonormalBasis ι_b ℂ E) : unitary (E →L[ℂ] E) :=
  linearIsometryEquivToUnitary (b₁.repr.trans b₂.repr.symm)

lemma orthonormalBasisIntertwiner_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι_b : Type*} [Fintype ι_b] [DecidableEq ι_b]
    (b₁ b₂ : OrthonormalBasis ι_b ℂ E) (i : ι_b) :
    (orthonormalBasisIntertwiner b₁ b₂).1 (b₁ i) = b₂ i := by
  change b₂.repr.symm (b₁.repr (b₁ i)) = b₂ i
  have h_repr : b₁.repr (b₁ i) = b₂.repr (b₂ i) := by
    ext j
    rw [b₁.repr_apply_apply, b₂.repr_apply_apply]
    by_cases hji : j = i
    · subst hji; rw [b₁.inner_eq_one, b₂.inner_eq_one]
    · rw [b₁.inner_eq_zero hji, b₂.inner_eq_zero hji]
  rw [h_repr, b₂.repr.symm_apply_apply]

lemma orthonormalBasisIntertwiner_adj_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {ι_b : Type*} [Fintype ι_b] [DecidableEq ι_b]
    (b₁ b₂ : OrthonormalBasis ι_b ℂ E) (i : ι_b) :
    ((orthonormalBasisIntertwiner b₁ b₂).1†) (b₂ i) = b₁ i := by
  have h_star_self :
      ((orthonormalBasisIntertwiner b₁ b₂).1†) * (orthonormalBasisIntertwiner b₁ b₂).1 = 1 :=
    Unitary.coe_star_mul_self (orthonormalBasisIntertwiner b₁ b₂)
  have h1 := congrArg ((orthonormalBasisIntertwiner b₁ b₂).1†)
    (orthonormalBasisIntertwiner_apply b₁ b₂ i)
  rw [← ContinuousLinearMap.mul_apply, h_star_self, ContinuousLinearMap.one_apply] at h1
  exact h1.symm

/-!
## 2. Spectral Properties of `sys.H0` and `spectralAlignmentUnitary`
-/

/-- Eigenvalue and `sys.P0` action characterization on `sortedEigenbasis sys.H0`. -/
lemma IndexedCommutingProjectorHamiltonian.sortedEigenbasis_H0_properties {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i) :
    let b0 := sortedEigenbasis sys.H0 sys.isSelfAdjoint_H0
    let μ0 := sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0
    (∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)), 0 ≤ μ0 i) ∧
    (∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < sys.groundDegeneracy → μ0 i = 0 ∧ sys.P0 (b0 i) = b0 i) ∧
    (∀ j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      sys.groundDegeneracy ≤ j.1 → 1 ≤ μ0 j ∧ sys.P0 (b0 j) = 0) := by
  intro b0 μ0
  have h_bounds := eigenvalue_bounds_of_trialSubspace sys.H0 sys.isSelfAdjoint_H0
    sys.groundSpace sys.groundDegeneracy rfl 0 0 1
    (fun ψ => by rw [zero_mul]; exact sys.re_inner_H0_nonneg ψ)
    (fun ψ hψ => by
      have h0 : sys.H0 ψ = 0 := hψ
      rw [h0, inner_zero_right, map_zero, zero_mul])
    (fun ψ hψ => by
      rw [one_mul]
      exact sys.norm_sq_le_re_inner_H0_of_mem_orthogonal_groundSpace h_weight hψ)
  rcases h_bounds with ⟨h_nonneg, h_low, h_high⟩
  refine ⟨h_nonneg, fun i hi => ?_, fun j hj => ?_⟩
  · have hμ0 : sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 i = 0 :=
      le_antisymm (h_low i hi) (h_nonneg i)
    have hH0_i : sys.H0 (b0 i) = 0 := by
      rw [sortedEigenbasis_apply_H_bhm sys.H0 sys.isSelfAdjoint_H0 i, hμ0,
        Complex.ofReal_zero, zero_smul]
    exact ⟨hμ0, (sys.mem_groundSpace_iff h_weight (b0 i)).mp hH0_i⟩
  · have hμ1 : 1 ≤ sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 j := h_high j hj
    have hP0_H0 : sys.P0 * sys.H0 = 0 :=
      sys.commute_H0_P0.symm.eq.trans sys.ham0_mul_proj0_eq_zero
    have h_app : (sys.P0 * sys.H0) (b0 j) = 0 := by rw [hP0_H0, ContinuousLinearMap.zero_apply]
    rw [ContinuousLinearMap.mul_apply,
      sortedEigenbasis_apply_H_bhm sys.H0 sys.isSelfAdjoint_H0 j, map_smul] at h_app
    have hμ_ne : ((sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 j : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (by linarith)
    exact ⟨hμ1, (smul_eq_zero.mp h_app).resolve_left hμ_ne⟩

/-- **Canonical Spectral Alignment Unitary (`spectralAlignmentUnitary`)**:
    Maps the ordered eigenbasis of `sys.H0` to the ordered eigenbasis of `sys.H0 + V.V_tot`. -/
def spectralAlignmentUnitary {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
  orthonormalBasisIntertwiner
    (sortedEigenbasis sys.H0 sys.isSelfAdjoint_H0)
    (sortedEigenbasis (sys.H0 + V.totalPerturbation) (isSelfAdjoint_indexedH0_add_V_tot_bhm sys V))

/-- Action of `U_spec.1† * (sys.H0 + V.V_tot) * U_spec.1` on the unperturbed eigenbasis `sortedEigenbasis sys.H0`. -/
lemma spectralAlignmentUnitary_conj_apply_eigenbasis {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    let U_spec := spectralAlignmentUnitary sys V
    let b0 := sortedEigenbasis sys.H0 sys.isSelfAdjoint_H0
    let hH := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V
    (U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) (b0 i) =
      (sortedEigenvalues (sys.H0 + V.totalPerturbation) hH i : ℂ) • b0 i := by
  intro U_spec b0 hH
  let bH := sortedEigenbasis (sys.H0 + V.totalPerturbation) hH
  change ((orthonormalBasisIntertwiner b0 bH).1†)
    ((sys.H0 + V.totalPerturbation) ((orthonormalBasisIntertwiner b0 bH).1 (b0 i))) = _
  rw [orthonormalBasisIntertwiner_apply b0 bH i,
    sortedEigenbasis_apply_H_bhm (sys.H0 + V.totalPerturbation) hH i,
    map_smul, orthonormalBasisIntertwiner_adj_apply b0 bH i]

/-- Two continuous linear maps that agree on all elements of an `OrthonormalBasis` are equal. -/
lemma ext_of_orthonormalBasis_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι_b : Type*} [Fintype ι_b] [DecidableEq ι_b]
    (b : OrthonormalBasis ι_b ℂ E) {T₁ T₂ : E →L[ℂ] E}
    (h : ∀ i : ι_b, T₁ (b i) = T₂ (b i)) :
    T₁ = T₂ := by
  ext ψ
  rw [← b.sum_repr ψ, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, map_smul, h i]

/-- **Unconditional Exact Block-Diagonality of `spectralAlignmentUnitary`
    (`commute_spectralAlignmentUnitary_conj_P0_and_H0`)**:
    For every perturbation $V$, $U_{\mathrm{spec}}^\dagger (H_0 + V_{\mathrm{tot}}) U_{\mathrm{spec}}$
    commutes identically with both `sys.P0` and `sys.H0`. -/
theorem commute_spectralAlignmentUnitary_conj_P0_and_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i) :
    let U_spec := spectralAlignmentUnitary sys V
    Commute (U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) sys.P0 ∧
    Commute (U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) sys.H0 := by
  intro U_spec
  let b0 := sortedEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let hH := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V
  rcases sys.sortedEigenbasis_H0_properties h_weight with ⟨_, h_low, h_high⟩
  refine ⟨?_, ?_⟩
  · rw [commute_iff_eq]
    apply ext_of_orthonormalBasis_eq b0
    intro i
    change (U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) (sys.P0 (b0 i)) =
      sys.P0 ((U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) (b0 i))
    rw [spectralAlignmentUnitary_conj_apply_eigenbasis sys V i, map_smul]
    by_cases hi : i.1 < sys.groundDegeneracy
    · rw [(h_low i hi).2, spectralAlignmentUnitary_conj_apply_eigenbasis sys V i]
    · rw [(h_high i (Nat.le_of_not_lt hi)).2, map_zero, smul_zero]
  · rw [commute_iff_eq]
    apply ext_of_orthonormalBasis_eq b0
    intro i
    change (U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) (sys.H0 (b0 i)) =
      sys.H0 ((U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) (b0 i))
    rw [sortedEigenbasis_apply_H_bhm sys.H0 sys.isSelfAdjoint_H0 i,
      spectralAlignmentUnitary_conj_apply_eigenbasis sys V i,
      map_smul, map_smul,
      spectralAlignmentUnitary_conj_apply_eigenbasis sys V i,
      sortedEigenbasis_apply_H_bhm sys.H0 sys.isSelfAdjoint_H0 i,
      smul_smul, smul_smul, mul_comm]

/-!
## 3. Two-Sided Courant–Fischer Eigenvalue Comparison & Approximate-to-Exact Unitary Dressing Upgrade
-/

/-- **Two-Sided Courant–Fischer Eigenvalue Sandwich (`sortedEigenvalues_sub_le_of_isometry_form_bound`)**:
    If a linear isometry equivalence $U$ satisfies the relative form bound
    $|\mathrm{re}\langle U\phi, (H_0 + V_{\mathrm{tot}})(U\phi)\rangle - \mathrm{re}\langle \phi, H_0 \phi\rangle - E_0 \|\phi\|^2|
      \le \gamma \, \mathrm{re}\langle \phi, H_0 \phi\rangle + \varepsilon \|\phi\|^2$
    with $0 \le \gamma \le 1$, then every ordered eigenvalue $\lambda_i$ of $H_0 + V_{\mathrm{tot}}$ and $\mu_i$ of $H_0$
    satisfies $|\lambda_i - \mu_i - E_0| \le \gamma \mu_i + \varepsilon$. -/
theorem sortedEigenvalues_sub_le_of_isometry_form_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : ManyBodyHilbertSpace Site ≃ₗᵢ[ℂ] ManyBodyHilbertSpace Site)
    {E0 γ ε : ℝ} (hγ_nonneg : 0 ≤ γ) (hγ_le_one : γ ≤ 1)
    (h_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ (U ϕ) ((sys.H0 + V.totalPerturbation) (U ϕ))) -
        RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) - E0 * ‖ϕ‖ ^ 2| ≤
        γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) + ε * ‖ϕ‖ ^ 2)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    let hH := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V
    let lam_i := sortedEigenvalues (sys.H0 + V.totalPerturbation) hH i
    let μ_i := sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 i
    |lam_i - μ_i - E0| ≤ γ * μ_i + ε := by
  intro hH lam_i μ_i
  let H := sys.H0 + V.totalPerturbation
  let E0_span := eigenSpanBelow sys.H0 sys.isSelfAdjoint_H0 (i.1 + 1)
  let W := E0_span.map U.toLinearEquiv.toLinearMap
  have hW_dim : Module.finrank ℂ W = i.1 + 1 := by
    rw [LinearEquiv.finrank_map_eq,
      finrank_eigenSpanBelow sys.H0 sys.isSelfAdjoint_H0 (i.1 + 1) i.2]
  have h_upper : lam_i ≤ E0 + (1 + γ) * μ_i + ε := by
    let U_orth := (eigenSpanBelow H hH i.1)ᗮ
    have h_dim_E : Module.finrank ℂ (eigenSpanBelow H hH i.1) = i.1 :=
      finrank_eigenSpanBelow H hH i.1 (le_of_lt i.2)
    have h_orth := (eigenSpanBelow H hH i.1).finrank_add_finrank_orthogonal
    have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
        Module.finrank ℂ W + Module.finrank ℂ U_orth := by
      dsimp [U_orth]; omega
    rcases exists_ne_zero_mem_inf_of_finrank_lt_add W U_orth h_dim_lt with ⟨ψ, hψW, hψU, hψ_ne⟩
    rcases Submodule.mem_map.mp hψW with ⟨ϕ, hϕ_mem, hUϕ⟩
    have hUϕ_eq : U ϕ = ψ := hUϕ
    have h_norm : ‖ϕ‖ = ‖ψ‖ := by rw [← hUϕ_eq, U.norm_map]
    have h_H0_le : RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) ≤ μ_i * ‖ϕ‖ ^ 2 := by
      apply re_inner_apply_H_le_of_mem_eigenSpanBelow sys.H0 sys.isSelfAdjoint_H0 (i.1 + 1) μ_i _ hϕ_mem
      intro j hj
      exact sortedEigenvalues_monotone_bhm sys.H0 sys.isSelfAdjoint_H0 (Nat.lt_succ_iff.mp hj)
    have h_H_low : lam_i * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ)) := by
      apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow H hH i.1 lam_i _ hψU
      intro j hj
      exact sortedEigenvalues_monotone_bhm H hH hj
    have hb := (abs_le.mp (h_form ϕ)).2
    rw [hUϕ_eq, h_norm] at hb
    rw [h_norm] at h_H0_le
    have h_mul : (1 + γ) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) ≤ (1 + γ) * (μ_i * ‖ψ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h_H0_le (by linarith)
    have h_le : lam_i * ‖ψ‖ ^ 2 ≤ (E0 + (1 + γ) * μ_i + ε) * ‖ψ‖ ^ 2 := by linarith
    exact le_of_mul_le_mul_right h_le (sq_pos_of_pos (norm_pos_iff.mpr hψ_ne))
  have h_lower : E0 + (1 - γ) * μ_i - ε ≤ lam_i := by
    let E0_low := eigenSpanBelow sys.H0 sys.isSelfAdjoint_H0 i.1
    let V_sub := (E0_lowᗮ).map U.toLinearEquiv.toLinearMap
    let U_low := eigenSpanBelow H hH (i.1 + 1)
    have h_dim_E0 : Module.finrank ℂ E0_low = i.1 :=
      finrank_eigenSpanBelow sys.H0 sys.isSelfAdjoint_H0 i.1 (le_of_lt i.2)
    have h_orth_E0 := E0_low.finrank_add_finrank_orthogonal
    have h_dim_V : Module.finrank ℂ V_sub = Module.finrank ℂ (E0_lowᗮ) :=
      LinearEquiv.finrank_map_eq U.toLinearEquiv (E0_lowᗮ)
    have h_dim_U : Module.finrank ℂ U_low = i.1 + 1 :=
      finrank_eigenSpanBelow H hH (i.1 + 1) i.2
    have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
        Module.finrank ℂ V_sub + Module.finrank ℂ U_low := by
      omega
    rcases exists_ne_zero_mem_inf_of_finrank_lt_add V_sub U_low h_dim_lt with ⟨ψ, hψV, hψU, hψ_ne⟩
    rcases Submodule.mem_map.mp hψV with ⟨ϕ, hϕ_orth, hUϕ⟩
    have hUϕ_eq : U ϕ = ψ := hUϕ
    have h_norm : ‖ϕ‖ = ‖ψ‖ := by rw [← hUϕ_eq, U.norm_map]
    have h_H0_ge : μ_i * ‖ϕ‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
      apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow sys.H0 sys.isSelfAdjoint_H0 i.1 μ_i _ hϕ_orth
      intro j hj
      exact sortedEigenvalues_monotone_bhm sys.H0 sys.isSelfAdjoint_H0 hj
    have h_H_high : RCLike.re (inner ℂ ψ (H ψ)) ≤ lam_i * ‖ψ‖ ^ 2 := by
      apply re_inner_apply_H_le_of_mem_eigenSpanBelow H hH (i.1 + 1) lam_i _ hψU
      intro j hj
      exact sortedEigenvalues_monotone_bhm H hH (Nat.lt_succ_iff.mp hj)
    have hb := (abs_le.mp (h_form ϕ)).1
    rw [hUϕ_eq, h_norm] at hb
    rw [h_norm] at h_H0_ge
    have h_mul : (1 - γ) * (μ_i * ‖ψ‖ ^ 2) ≤ (1 - γ) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) :=
      mul_le_mul_of_nonneg_left h_H0_ge (by linarith)
    have h_le : (E0 + (1 - γ) * μ_i - ε) * ‖ψ‖ ^ 2 ≤ lam_i * ‖ψ‖ ^ 2 := by linarith
    exact le_of_mul_le_mul_right h_le (sq_pos_of_pos (norm_pos_iff.mpr hψ_ne))
  rw [abs_le]
  constructor <;> linarith

/-- Quadratic form identity for `spectralAlignmentUnitary sys V` in the eigenbasis of `sys.H0`. -/
lemma re_inner_spectralAlignmentUnitary_conj_sub_eq_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (E0 : ℝ) (ψ : ManyBodyHilbertSpace Site) :
    let U_spec := spectralAlignmentUnitary sys V
    let b0 := sortedEigenbasis sys.H0 sys.isSelfAdjoint_H0
    let hH := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V
    RCLike.re (inner ℂ ψ ((U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1 - sys.H0 - (E0 : ℂ) • 1) ψ)) =
      ∑ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
        (sortedEigenvalues (sys.H0 + V.totalPerturbation) hH i -
          sortedEigenvalues sys.H0 sys.isSelfAdjoint_H0 i - E0) *
          ‖inner ℂ (b0 i) ψ‖ ^ 2 := by
  intro U_spec b0 hH
  let bH := sortedEigenbasis (sys.H0 + V.totalPerturbation) hH
  have h_U_norm : ∀ i, ‖inner ℂ (bH i) (U_spec.1 ψ)‖ = ‖inner ℂ (b0 i) ψ‖ := by
    intro i
    have h_in : inner ℂ (bH i) (U_spec.1 ψ) = inner ℂ (b0 i) ψ := by
      rw [← orthonormalBasisIntertwiner_apply b0 bH i]
      exact (b0.repr.trans bH.repr.symm).inner_map_map (b0 i) ψ
    rw [h_in]
  have h_term1 : RCLike.re (inner ℂ ψ ((U_spec.1† * (sys.H0 + V.totalPerturbation) * U_spec.1) ψ)) =
      ∑ i, sortedEigenvalues (sys.H0 + V.totalPerturbation) hH i * ‖inner ℂ (b0 i) ψ‖ ^ 2 := by
    rw [← inner_unitary_conj U_spec (sys.H0 + V.totalPerturbation) ψ,
      re_inner_apply_H_eq_sum (sys.H0 + V.totalPerturbation) hH (U_spec.1 ψ)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_U_norm i]
  have h_term2 := re_inner_apply_H_eq_sum sys.H0 sys.isSelfAdjoint_H0 ψ
  have h_term3 : E0 * ‖ψ‖ ^ 2 = ∑ i, E0 * ‖inner ℂ (b0 i) ψ‖ ^ 2 := by
    rw [← b0.sum_sq_norm_inner_right ψ, Finset.mul_sum]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
    inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one,
    h_term1, h_term2, h_term3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

end
