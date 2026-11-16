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
import Proofs.CubeTelescoping.ChromaticSubgridFormBound

/-!
# Ordered Spectral Subspaces and Courant–Fischer Trial-Subspace Min-Max Bounds

Develops the spectral subspace `eigenSpanBelow` spanned by the lowest `k` eigenvectors of `sortedEigenbasis` and proves the finite-dimensional Courant–Fischer min-max comparison theorem `eigenvalue_bounds_of_trialSubspace` converting quadratic-form bounds on a trial subspace and its orthogonal complement into `IndexedHasStableLowEnergyBand`.

## References

* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap

/-!
## 1. Self-Adjointness of $H_0 + V_{\mathrm{tot}}$ and Ordered Spectral Basis `sortedEigenbasis`
-/

/-- The full perturbed indexed Hamiltonian $H = H_0 + V_{\mathrm{tot}}$ is self-adjoint. -/
lemma isSelfAdjoint_indexedH0_add_V_tot_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) :
    IsSelfAdjoint (sys.H0 + V.totalPerturbation) :=
  isSelfAdjoint_add_clm sys.isSelfAdjoint_H0 V.isSelfAdjoint_totalPerturbation

/-- The sequence `sortedEigenvalues H hH` is monotone increasing: $i \le j \implies \mu_i \le \mu_j$. -/
lemma sortedEigenvalues_monotone_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) :
    Monotone (sortedEigenvalues H hH) := by
  intro i j hij
  dsimp [sortedEigenvalues]
  let hSymm : H.toLinearMap.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.toLinearMap).mpr
      ((ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff H).mpr hH)
  exact hSymm.eigenvalues_antitone rfl (Fin.rev_le_rev.mpr hij)

/-- The $i$-th basis vector of `sortedEigenbasis H hH` is an eigenvector of $H$ with eigenvalue `sortedEigenvalues H hH i`. -/
lemma sortedEigenbasis_apply_H_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :
    H (sortedEigenbasis H hH i) =
      (sortedEigenvalues H hH i : ℂ) • sortedEigenbasis H hH i := by
  let hSymm : H.toLinearMap.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.toLinearMap).mpr
      ((ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff H).mpr hH)
  dsimp [sortedEigenbasis, sortedEigenvalues, finRevEquiv]
  rw [OrthonormalBasis.reindex_apply]
  exact hSymm.apply_eigenvectorBasis rfl i.rev

/-- Spectral coordinate identity $\langle e_i, H \psi \rangle = \mu_i \langle e_i, \psi \rangle$ for $e_i = \mathrm{sortedEigenbasis}\ H\ hH\ i$. -/
lemma sortedEigenbasis_inner_apply_H {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)))
    (ψ : ManyBodyHilbertSpace Site) :
    inner ℂ (sortedEigenbasis H hH i) (H ψ) =
      (sortedEigenvalues H hH i : ℂ) * inner ℂ (sortedEigenbasis H hH i) ψ := by
  let hSymm : H.toLinearMap.IsSymmetric :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint H.toLinearMap).mpr
      ((ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff H).mpr hH)
  have h1 : inner ℂ (H (sortedEigenbasis H hH i)) ψ =
      inner ℂ (sortedEigenbasis H hH i) (H ψ) := hSymm (sortedEigenbasis H hH i) ψ
  rw [← h1, sortedEigenbasis_apply_H_bhm, inner_smul_left]
  simp

/-- Spectral expansion of the quadratic form $\mathrm{re}\langle \psi, H \psi \rangle = \sum_i \mu_i |\langle e_i, \psi \rangle|^2$. -/
lemma re_inner_apply_H_eq_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ (H ψ)) =
      ∑ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
        sortedEigenvalues H hH i * ‖inner ℂ (sortedEigenbasis H hH i) ψ‖ ^ 2 := by
  let b := sortedEigenbasis H hH
  rw [← b.sum_inner_mul_inner ψ (H ψ), map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sortedEigenbasis_inner_apply_H H hH i ψ]
  have h_conj : inner ℂ ψ (b i) = starRingEnd ℂ (inner ℂ (b i) ψ) := by
    rw [inner_conj_symm]
  rw [h_conj]
  set z : ℂ := inner ℂ (b i) ψ
  set μ : ℝ := sortedEigenvalues H hH i
  have h_prod : starRingEnd ℂ z * ((μ : ℂ) * z) = (μ : ℂ) * (starRingEnd ℂ z * z) := by ring
  rw [h_prod]
  have h_norm : starRingEnd ℂ z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h_norm, ← Complex.ofReal_mul]
  rfl

/-!
## 2. Low-Energy Spectral Subspaces `eigenSpanBelow` and Quadratic Form Estimates
-/

/-- The subspace spanned by the lowest `k` eigenvectors of `H`. -/
def eigenSpanBelow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ) :
    Submodule ℂ (ManyBodyHilbertSpace Site) :=
  let b := sortedEigenbasis H hH
  let S : Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :=
    Finset.univ.filter (fun i => i.1 < k)
  Submodule.span ℂ ((S.image b) : Set (ManyBodyHilbertSpace Site))

/-- Cardinality of `{i : Fin N | i.1 < k}` is $k$ whenever $k \le N$. -/
lemma card_filter_lt_fin (N k : ℕ) (hk : k ≤ N) :
    (Finset.univ.filter (fun i : Fin N => i.1 < k)).card = k := by
  have h_eq : Finset.univ.filter (fun i : Fin N => i.1 < k) =
      Finset.univ.map (Fin.castLEEmb hk) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fin.castLEEmb_apply, Fin.ext_iff, Fin.val_castLE]
    constructor
    · intro hi
      exact ⟨⟨i.1, hi⟩, rfl⟩
    · rintro ⟨j, hj⟩
      have hj_lt := j.2
      omega
  rw [h_eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The dimension of `eigenSpanBelow H hH k` is $k$ whenever $k \le \dim \mathcal{H}$. -/
lemma finrank_eigenSpanBelow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ)
    (hk : k ≤ Module.finrank ℂ (ManyBodyHilbertSpace Site)) :
    Module.finrank ℂ (eigenSpanBelow H hH k) = k := by
  unfold eigenSpanBelow
  let b := sortedEigenbasis H hH
  let S : Finset (Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) :=
    Finset.univ.filter (fun i => i.1 < k)
  have h_li : LinearIndependent ℂ b := b.toBasis.linearIndependent
  have h_ind : LinearIndepOn ℂ id ((S.image b) : Set (ManyBodyHilbertSpace Site)) := by
    rw [Finset.coe_image]
    exact h_li.linearIndepOn_id.mono (Set.image_subset_range _ _)
  rw [finrank_span_finset_eq_card h_ind, Finset.card_image_of_injective _ h_li.injective]
  exact card_filter_lt_fin _ k hk

/-- The subspace `eigenSpanBelow H hH k` is invariant under $H$. -/
lemma eigenSpanBelow_invariant {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ) :
    ∀ ψ ∈ eigenSpanBelow H hH k, H ψ ∈ eigenSpanBelow H hH k := by
  intro ψ hψ
  have h_le : eigenSpanBelow H hH k ≤ (eigenSpanBelow H hH k).comap H.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rcases hx with ⟨i, hi, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    rw [sortedEigenbasis_apply_H_bhm H hH i]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨i, hi, rfl⟩
  exact h_le hψ

/-- Any vector $\psi \in \mathrm{eigenSpanBelow}\ H\ hH\ k$ is orthogonal to all eigenvectors $e_i$ with $i \ge k$. -/
lemma inner_eq_zero_of_mem_eigenSpanBelow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) (hi : k ≤ i.1)
    {ψ : ManyBodyHilbertSpace Site} (hψ : ψ ∈ eigenSpanBelow H hH k) :
    inner ℂ (sortedEigenbasis H hH i) ψ = 0 := by
  let b := sortedEigenbasis H hH
  have h_sub : eigenSpanBelow H hH k ≤ LinearMap.ker (innerSL ℂ (b i)).toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rcases hx with ⟨j, hj, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    have hij : i ≠ j := by
      intro h_eq
      subst h_eq
      omega
    exact b.inner_eq_zero hij
  exact h_sub hψ

/-- Any vector $\psi \in (\mathrm{eigenSpanBelow}\ H\ hH\ k)^\perp$ is orthogonal to all eigenvectors $e_i$ with $i < k$. -/
lemma inner_eq_zero_of_mem_orthogonal_eigenSpanBelow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ)
    (i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site))) (hi : i.1 < k)
    {ψ : ManyBodyHilbertSpace Site} (hψ : ψ ∈ (eigenSpanBelow H hH k)ᗮ) :
    inner ℂ (sortedEigenbasis H hH i) ψ = 0 := by
  have h_mem : sortedEigenbasis H hH i ∈ eigenSpanBelow H hH k := by
    apply Submodule.subset_span
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨i, hi, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal h_mem hψ

/-- Upper quadratic form bound $\mathrm{re}\langle \psi, H \psi \rangle \le B \|\psi\|^2$ on `eigenSpanBelow H hH k`
    when $\mu_i \le B$ for all $i < k$. -/
lemma re_inner_apply_H_le_of_mem_eigenSpanBelow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ) (B : ℝ)
    (hB : ∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < k → sortedEigenvalues H hH i ≤ B)
    {ψ : ManyBodyHilbertSpace Site} (hψ : ψ ∈ eigenSpanBelow H hH k) :
    RCLike.re (inner ℂ ψ (H ψ)) ≤ B * ‖ψ‖ ^ 2 := by
  rw [re_inner_apply_H_eq_sum H hH ψ, ← (sortedEigenbasis H hH).sum_sq_norm_inner_right ψ,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hi : i.1 < k
  · exact mul_le_mul_of_nonneg_right (hB i hi) (sq_nonneg _)
  · have hz : inner ℂ (sortedEigenbasis H hH i) ψ = 0 :=
      inner_eq_zero_of_mem_eigenSpanBelow H hH k i (Nat.le_of_not_lt hi) hψ
    simp [hz]

/-- Lower quadratic form bound $A \|\psi\|^2 \le \mathrm{re}\langle \psi, H \psi \rangle$ on `eigenSpanBelow H hH k`
    when $A \le \mu_i$ for all $i < k$. -/
lemma le_re_inner_apply_H_of_mem_eigenSpanBelow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ) (A : ℝ)
    (hA : ∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < k → A ≤ sortedEigenvalues H hH i)
    {ψ : ManyBodyHilbertSpace Site} (hψ : ψ ∈ eigenSpanBelow H hH k) :
    A * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ)) := by
  rw [re_inner_apply_H_eq_sum H hH ψ, ← (sortedEigenbasis H hH).sum_sq_norm_inner_right ψ,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hi : i.1 < k
  · exact mul_le_mul_of_nonneg_right (hA i hi) (sq_nonneg _)
  · have hz : inner ℂ (sortedEigenbasis H hH i) ψ = 0 :=
      inner_eq_zero_of_mem_eigenSpanBelow H hH k i (Nat.le_of_not_lt hi) hψ
    simp [hz]

/-- Lower quadratic form bound $C_{\mathrm{bound}} \|\psi\|^2 \le \mathrm{re}\langle \psi, H \psi \rangle$
    on $(\mathrm{eigenSpanBelow}\ H\ hH\ k)^\perp$ when $C_{\mathrm{bound}} \le \mu_i$ for all $i \ge k$. -/
lemma le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (k : ℕ) (C_bound : ℝ)
    (hC : ∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      k ≤ i.1 → C_bound ≤ sortedEigenvalues H hH i)
    {ψ : ManyBodyHilbertSpace Site} (hψ : ψ ∈ (eigenSpanBelow H hH k)ᗮ) :
    C_bound * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ)) := by
  rw [re_inner_apply_H_eq_sum H hH ψ, ← (sortedEigenbasis H hH).sum_sq_norm_inner_right ψ,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hi : i.1 < k
  · have hz : inner ℂ (sortedEigenbasis H hH i) ψ = 0 :=
      inner_eq_zero_of_mem_orthogonal_eigenSpanBelow H hH k i hi hψ
    simp [hz]
  · exact mul_le_mul_of_nonneg_right (hC i (Nat.le_of_not_lt hi)) (sq_nonneg _)

/-!
## 3. Courant–Fischer Subspace Intersection and Trial Subspace Min-Max Theorems
-/

/-- Grassmannian dimension inequality: two subspaces $U, V \le \mathcal{H}$ with
    $\dim U + \dim V > \dim \mathcal{H}$ have a non-zero vector $\psi \in U \cap V$. -/
lemma exists_ne_zero_mem_inf_of_finrank_lt_add {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (U V : Submodule ℂ (ManyBodyHilbertSpace Site))
    (h_dim : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
      Module.finrank ℂ U + Module.finrank ℂ V) :
    ∃ ψ : ManyBodyHilbertSpace Site, ψ ∈ U ∧ ψ ∈ V ∧ ψ ≠ 0 := by
  have h_sup_inf := Submodule.finrank_sup_add_finrank_inf_eq U V
  have h_sup_le : Module.finrank ℂ (U ⊔ V : Submodule ℂ (ManyBodyHilbertSpace Site)) ≤
      Module.finrank ℂ (ManyBodyHilbertSpace Site) :=
    Submodule.finrank_le (U ⊔ V)
  have h_inf_pos : 0 < Module.finrank ℂ (U ⊓ V : Submodule ℂ (ManyBodyHilbertSpace Site)) := by
    omega
  have h_ne_bot : (U ⊓ V : Submodule ℂ (ManyBodyHilbertSpace Site)) ≠ ⊥ := by
    intro h_bot
    rw [h_bot, finrank_bot] at h_inf_pos
    omega
  rcases (Submodule.ne_bot_iff (U ⊓ V)).mp h_ne_bot with ⟨ψ, hψ_mem, hψ_ne⟩
  exact ⟨ψ, hψ_mem.1, hψ_mem.2, hψ_ne⟩

/-- **Courant–Fischer Trial Subspace Theorem**:
    Given a $k$-dimensional trial subspace $W \le \mathcal{H}$ on which $\langle \psi, H \psi \rangle \le b \|\psi\|^2$
    and on whose orthogonal complement $W^\perp$ we have $\langle \psi, H \psi \rangle \ge c \|\psi\|^2$,
    together with a global lower bound $\langle \psi, H \psi \rangle \ge a \|\psi\|^2$,
    the ordered eigenvalues $\mu_0 \le \dots \le \mu_{N-1}$ of $H$ satisfy:
    - $a \le \mu_i$ for all $i$,
    - $\mu_i \le b$ for all $i < k$,
    - $c \le \mu_j$ for all $j \ge k$. -/
theorem eigenvalue_bounds_of_trialSubspace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H)
    (W : Submodule ℂ (ManyBodyHilbertSpace Site))
    (k : ℕ) (hk : Module.finrank ℂ W = k)
    (a b c : ℝ)
    (h_global : ∀ ψ : ManyBodyHilbertSpace Site,
      a * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ)))
    (h_W : ∀ ψ ∈ W, RCLike.re (inner ℂ ψ (H ψ)) ≤ b * ‖ψ‖ ^ 2)
    (h_W_orth : ∀ ψ ∈ Wᗮ, c * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ))) :
    (∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      a ≤ sortedEigenvalues H hH i) ∧
    (∀ i : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      i.1 < k → sortedEigenvalues H hH i ≤ b) ∧
    (∀ j : Fin (Module.finrank ℂ (ManyBodyHilbertSpace Site)),
      k ≤ j.1 → c ≤ sortedEigenvalues H hH j) := by
  let b_vec := sortedEigenbasis H hH
  have hk_le_N : k ≤ Module.finrank ℂ (ManyBodyHilbertSpace Site) := by
    rw [← hk]
    exact Submodule.finrank_le W
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h1 := h_global (b_vec i)
    rw [b_vec.norm_eq_one i, one_pow, mul_one, sortedEigenbasis_apply_H_bhm H hH i,
      inner_smul_right, b_vec.inner_eq_one i, mul_one] at h1
    exact h1
  · intro i hi
    let U := (eigenSpanBelow H hH i.1)ᗮ
    have h_dim_E : Module.finrank ℂ (eigenSpanBelow H hH i.1) = i.1 :=
      finrank_eigenSpanBelow H hH i.1 (le_of_lt i.2)
    have h_orth := (eigenSpanBelow H hH i.1).finrank_add_finrank_orthogonal
    have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
        Module.finrank ℂ W + Module.finrank ℂ U := by
      dsimp [U]
      omega
    rcases exists_ne_zero_mem_inf_of_finrank_lt_add W U h_dim_lt with ⟨ψ, hψW, hψU, hψ_ne⟩
    have h_low : sortedEigenvalues H hH i * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ)) := by
      apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow H hH i.1
        (sortedEigenvalues H hH i) _ hψU
      intro j hj
      exact sortedEigenvalues_monotone_bhm H hH hj
    have h_high : RCLike.re (inner ℂ ψ (H ψ)) ≤ b * ‖ψ‖ ^ 2 := h_W ψ hψW
    have h_le : sortedEigenvalues H hH i * ‖ψ‖ ^ 2 ≤ b * ‖ψ‖ ^ 2 := le_trans h_low h_high
    have h_norm_pos : 0 < ‖ψ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hψ_ne)
    exact le_of_mul_le_mul_right h_le h_norm_pos
  · intro j hj
    let U := eigenSpanBelow H hH (j.1 + 1)
    have hj_le_N : j.1 + 1 ≤ Module.finrank ℂ (ManyBodyHilbertSpace Site) := j.2
    have h_dim_U : Module.finrank ℂ U = j.1 + 1 :=
      finrank_eigenSpanBelow H hH (j.1 + 1) hj_le_N
    have h_orth := W.finrank_add_finrank_orthogonal
    have h_dim_lt : Module.finrank ℂ (ManyBodyHilbertSpace Site) <
        Module.finrank ℂ Wᗮ + Module.finrank ℂ U := by
      omega
    rcases exists_ne_zero_mem_inf_of_finrank_lt_add Wᗮ U h_dim_lt with ⟨ψ, hψW_orth, hψU, hψ_ne⟩
    have h_low : c * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H ψ)) := h_W_orth ψ hψW_orth
    have h_high : RCLike.re (inner ℂ ψ (H ψ)) ≤ sortedEigenvalues H hH j * ‖ψ‖ ^ 2 := by
      apply re_inner_apply_H_le_of_mem_eigenSpanBelow H hH (j.1 + 1)
        (sortedEigenvalues H hH j) _ hψU
      intro i hi
      have hij : i ≤ j := Nat.lt_succ_iff.mp hi
      exact sortedEigenvalues_monotone_bhm H hH hij
    have h_le : c * ‖ψ‖ ^ 2 ≤ sortedEigenvalues H hH j * ‖ψ‖ ^ 2 := le_trans h_low h_high
    have h_norm_pos : 0 < ‖ψ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hψ_ne)
    exact le_of_mul_le_mul_right h_le h_norm_pos

/-- **Reduction of `IndexedHasStableLowEnergyBand` to Trial Subspace Form Bounds**: -/
theorem indexedHasStableLowEnergyBand_of_trialSubspace {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (Δ_gap δ_split : ℝ)
    (W : Submodule ℂ (ManyBodyHilbertSpace Site))
    (hW_dim : Module.finrank ℂ W = sys.groundDegeneracy)
    (a b c : ℝ)
    (h_ab : b - a ≤ δ_split)
    (h_bc : c - b ≥ Δ_gap)
    (h_global : ∀ ψ : ManyBodyHilbertSpace Site,
      a * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ ((sys.H0 + V.totalPerturbation) ψ)))
    (h_W : ∀ ψ ∈ W, RCLike.re (inner ℂ ψ ((sys.H0 + V.totalPerturbation) ψ)) ≤ b * ‖ψ‖ ^ 2)
    (h_W_orth : ∀ ψ ∈ Wᗮ, c * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ ((sys.H0 + V.totalPerturbation) ψ))) :
    IndexedHasStableLowEnergyBand sys V Δ_gap δ_split := by
  let H := sys.H0 + V.totalPerturbation
  let d_gs := sys.groundDegeneracy
  have hH : IsSelfAdjoint H := isSelfAdjoint_indexedH0_add_V_tot_bhm sys V
  have hd_le_N : d_gs ≤ Module.finrank ℂ (ManyBodyHilbertSpace Site) :=
    Submodule.finrank_le sys.groundSpace
  rcases eigenvalue_bounds_of_trialSubspace H hH W d_gs hW_dim a b c h_global h_W h_W_orth with
    ⟨h_eig_a, h_eig_b, h_eig_c⟩
  refine ⟨hH, eigenSpanBelow H hH d_gs, b - δ_split, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact finrank_eigenSpanBelow H hH d_gs hd_le_N
  · exact eigenSpanBelow_invariant H hH d_gs
  · intro ψ hψ
    constructor
    · apply le_re_inner_apply_H_of_mem_eigenSpanBelow H hH d_gs (b - δ_split) _ hψ
      intro i _
      linarith [h_eig_a i]
    · have h_eq : b - δ_split + δ_split = b := by ring
      rw [h_eq]
      exact re_inner_apply_H_le_of_mem_eigenSpanBelow H hH d_gs b h_eig_b hψ
  · intro ψ hψ
    apply le_re_inner_apply_H_of_mem_orthogonal_eigenSpanBelow H hH d_gs
      (b - δ_split + δ_split + Δ_gap) _ hψ
    intro j hj
    linarith [h_eig_c j hj]
  · intro i j hi hj
    rw [abs_le]
    constructor <;> linarith [h_eig_a i, h_eig_b i hi, h_eig_a j, h_eig_b j hj]
  · intro i j hi hj
    linarith [h_eig_b i hi, h_eig_c j hj]

/-- Construct a `LinearIsometryEquiv` from an element of the `unitary` group of continuous linear maps. -/
def unitaryToLinearIsometryEquiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) : E ≃ₗᵢ[ℂ] E :=
  have h_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  have h_self_star : U.1 * U.1† = 1 := Unitary.coe_mul_star_self U
  { U.1.toLinearMap with
    invFun := fun y => (U.1†) y
    left_inv := fun y => by
      change (U.1† * U.1) y = y
      rw [h_star_self, ContinuousLinearMap.one_apply]
    right_inv := fun y => by
      change (U.1 * U.1†) y = y
      rw [h_self_star, ContinuousLinearMap.one_apply]
    norm_map' := fun y => by
      change ‖U.1 y‖ = ‖y‖
      have h_sq : ‖U.1 y‖ ^ 2 = ‖y‖ ^ 2 := by
        have h1 : inner ℂ (U.1 y) (U.1 y) = inner ℂ y y := by
          calc inner ℂ (U.1 y) (U.1 y)
            _ = inner ℂ y ((U.1† * U.1) y) := (ContinuousLinearMap.adjoint_inner_right U.1 y (U.1 y)).symm
            _ = inner ℂ y y := by rw [h_star_self, ContinuousLinearMap.one_apply]
        have h2 := congrArg RCLike.re h1
        rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h2
        exact h2
      nlinarith [norm_nonneg (U.1 y), norm_nonneg y] }

/-- Adjoint conjugation identity $\langle U \phi, T (U \phi) \rangle = \langle \phi, (U^\dagger T U) \phi \rangle$. -/
lemma inner_unitary_conj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) (T : E →L[ℂ] E) (ϕ : E) :
    inner ℂ (U.1 ϕ) (T (U.1 ϕ)) = inner ℂ ϕ ((U.1† * T * U.1) ϕ) := by
  calc inner ℂ (U.1 ϕ) (T (U.1 ϕ))
    _ = inner ℂ ϕ ((U.1†) (T (U.1 ϕ))) := (ContinuousLinearMap.adjoint_inner_right U.1 ϕ (T (U.1 ϕ))).symm
    _ = inner ℂ ϕ ((U.1† * T * U.1) ϕ) := rfl

/-- Orthogonal block-diagonal lower form bound: if `IsStarProjection P` and `Commute H' P`,
    and $H'$ is bounded below by $a$ on $\mathrm{range}(P)$ and by $c \ge a$ on $\ker(P)$,
    then $\mathrm{re}\langle \phi, H' \phi \rangle \ge a \|\phi\|^2$ for all $\phi \in \mathcal{H}$. -/
lemma re_inner_block_diagonal_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H' P : E →L[ℂ] E} (hP : IsStarProjection P) (h_comm : Commute H' P)
    {a c : ℝ} (hac : a ≤ c)
    (h_low : ∀ ψ : E, P ψ = ψ → a * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H' ψ)))
    (h_high : ∀ ψ : E, P ψ = 0 → c * ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (H' ψ)))
    (ϕ : E) :
    a * ‖ϕ‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ (H' ϕ)) := by
  let ϕ₁ := P ϕ
  let ϕ₂ := (1 - P) ϕ
  have hP_idem : P * P = P := hP.isIdempotentElem.eq
  have hP_adj : P† = P := ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.isSelfAdjoint
  have hQ_adj : (1 - P)† = 1 - P :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hP.one_sub.isSelfAdjoint
  have hϕ₁ : P ϕ₁ = ϕ₁ := isStarProjection_apply_self_bhm hP ϕ
  have hϕ₂ : P ϕ₂ = 0 := by
    change (P * (1 - P)) ϕ = 0
    rw [mul_sub, mul_one, hP_idem, sub_self, ContinuousLinearMap.zero_apply]
  have h_sum : ϕ₁ + ϕ₂ = ϕ := by
    change P ϕ + (1 - P) ϕ = ϕ
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
  have h_cross1 : inner ℂ ϕ₁ (H' ϕ₂) = 0 := by
    change inner ℂ (P ϕ) (H' ((1 - P) ϕ)) = 0
    rw [← ContinuousLinearMap.adjoint_inner_right P ϕ (H' ((1 - P) ϕ)), hP_adj]
    have h_zero : P * H' * (1 - P) = 0 := by
      rw [← h_comm.eq, mul_assoc, mul_sub, mul_one, hP_idem, sub_self, mul_zero]
    change inner ℂ ϕ ((P * H' * (1 - P)) ϕ) = 0
    rw [h_zero, ContinuousLinearMap.zero_apply, inner_zero_right]
  have h_cross2 : inner ℂ ϕ₂ (H' ϕ₁) = 0 := by
    change inner ℂ ((1 - P) ϕ) (H' (P ϕ)) = 0
    rw [← ContinuousLinearMap.adjoint_inner_right (1 - P) ϕ (H' (P ϕ)), hQ_adj]
    have h_comm_Q : Commute H' (1 - P) := commute_one_sub_right_bhm h_comm
    have h_zero : (1 - P) * H' * P = 0 := by
      rw [← h_comm_Q.eq, mul_assoc, sub_mul, one_mul, hP_idem, sub_self, mul_zero]
    change inner ℂ ϕ (((1 - P) * H' * P) ϕ) = 0
    rw [h_zero, ContinuousLinearMap.zero_apply, inner_zero_right]
  have h_decomp : RCLike.re (inner ℂ (ϕ₁ + ϕ₂) (H' (ϕ₁ + ϕ₂))) =
      RCLike.re (inner ℂ ϕ₁ (H' ϕ₁)) + RCLike.re (inner ℂ ϕ₂ (H' ϕ₂)) := by
    rw [map_add H', inner_add_left, inner_add_right, inner_add_right,
      h_cross1, h_cross2, add_zero, zero_add, map_add]
  rw [h_sum] at h_decomp
  have h1 : a * ‖ϕ₁‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ₁ (H' ϕ₁)) := h_low ϕ₁ hϕ₁
  have h2 : a * ‖ϕ₂‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ₂ (H' ϕ₂)) :=
    le_trans (mul_le_mul_of_nonneg_right hac (sq_nonneg _)) (h_high ϕ₂ hϕ₂)
  have h_pyth : ‖ϕ‖ ^ 2 = ‖ϕ₁‖ ^ 2 + ‖ϕ₂‖ ^ 2 := isStarProjection_pythagorean_bhm hP ϕ
  calc a * ‖ϕ‖ ^ 2
    _ = a * ‖ϕ₁‖ ^ 2 + a * ‖ϕ₂‖ ^ 2 := by rw [h_pyth, mul_add]
    _ ≤ RCLike.re (inner ℂ ϕ₁ (H' ϕ₁)) + RCLike.re (inner ℂ ϕ₂ (H' ϕ₂)) := add_le_add h1 h2
    _ = RCLike.re (inner ℂ ϕ (H' ϕ)) := h_decomp.symm
