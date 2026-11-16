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
import Proofs.CubeTelescoping.CoarseCubeFunctor
import Proofs.GapBootstrap.CourantFischerAndBootstrap
import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.DressedSafeSubspace.SectorFilteredFormBounds

/-!
# Dressed Energy Sandwiches and Sector-Filtered BHM Spectral Stability

Proves star-projection properties of dressed ground projectors (`indexedDressedGroundProj_isStarProjection`), converts unitary relative form bounds with slope at most $1/4$ into `SatisfiesDressedEnergySandwich` (`dressed_energy_sandwich_of_relative_form_bound`) and `IndexedHasStableLowEnergyBand` (`indexedHasStableLowEnergyBand_of_singleDressedBound`), and establishes sector-filtered BHM spectral stability (`hasSectorFilteredQACStability_of_commute_and_form_bound`, `theorem_unconditional_sector_filtered_bhm_stability_of_commute_P0`).

## References

* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Part I, Section 7.2 (`subsec:gap-bootstrap`), Theorem 7.3 (`thm:gap-bootstrap`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Bravyi, Hastings, and Michalakis (2010), J. Math. Phys. 51, 093512
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
## 1. Dressed Check Algebra and Indexed Unperturbed Ground Space Spectral Gap
-/

/-- `indexedDressedGroundProj sys U` is a star projection. -/
lemma indexedDressedGroundProj_isStarProjection {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    IsStarProjection (indexedDressedGroundProj sys U) := by
  have hU_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  have hP := sys.isStarProjection_P0
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, indexedDressedGroundProj]
    calc (U.1 * sys.P0 * U.1†) * (U.1 * sys.P0 * U.1†)
      _ = U.1 * sys.P0 * (U.1† * U.1) * sys.P0 * U.1† := by simp only [mul_assoc]
      _ = U.1 * (sys.P0 * sys.P0) * U.1† := by rw [hU_star_self, mul_one]; simp only [mul_assoc]
      _ = U.1 * sys.P0 * U.1† := by rw [hP.isIdempotentElem.eq]
  · rw [isSelfAdjoint_iff, indexedDressedGroundProj]
    change star (U.1 * sys.P0 * star U.1) = U.1 * sys.P0 * star U.1
    rw [star_mul, star_mul, star_star, hP.isSelfAdjoint.star_eq, mul_assoc]

/-- The unperturbed Hamiltonian `sys.H0` of an `IndexedCommutingProjectorHamiltonian` annihilates `sys.P0`. -/
lemma IndexedCommutingProjectorHamiltonian.ham0_mul_proj0_eq_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    sys.H0 * sys.P0 = 0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0]; rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [smul_mul_assoc, sys.checkProj_mul_P0_eq_zero i]; ext x; simp

/-- For any `IndexedCommutingProjectorHamiltonian sys` and any state $\psi$,
    $\mathrm{re}\langle \psi, \mathrm{sys.H0}\ \psi \rangle \ge 0$. -/
lemma IndexedCommutingProjectorHamiltonian.re_inner_H0_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (ψ : ManyBodyHilbertSpace Site) :
    0 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0]
  rw [ContinuousLinearMap.sum_apply, inner_sum, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
  exact mul_nonneg (le_trans zero_le_one (sys.weight_ge_one i))
    (by
      change 0 ≤ RCLike.re (inner ℂ ψ (sys.checkProj i ψ))
      rw [isStarProjection_re_inner_eq_norm_sq_bhm (sys.is_projector i) ψ]
      exact sq_nonneg _)

/-- When `∀ i : ι, 1 ≤ sys.weight i`, the excited projection $1 - P_0$ is form-bounded by $H_0$:
    $\mathrm{re}\langle \psi, (1 - P_0) \psi \rangle \le \mathrm{re}\langle \psi, H_0 \psi \rangle$. -/
lemma IndexedCommutingProjectorHamiltonian.one_sub_P0_form_le_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ ((1 - sys.P0) ψ)) ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  have h1P0 : IsStarProjection (1 - sys.P0) := sys.isStarProjection_P0.one_sub
  rw [isStarProjection_re_inner_eq_norm_sq_bhm h1P0 ψ]
  dsimp [IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj]
  set l := (Finset.univ : Finset ι).toList
  have h_proj : ∀ p ∈ l.map (fun i : ι => 1 - sys.checkProj i), IsStarProjection p := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    exact (sys.is_projector i).one_sub
  have h_comm : (l.map (fun i : ι => 1 - sys.checkProj i)).Pairwise Commute := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (Finset.univ : Finset ι).nodup_toList
    intro i j _ _ _
    exact commute_one_sub_right_bhm (commute_one_sub_left_bhm (sys.pairwise_commute i j))
  have h_sum_le := norm_one_sub_list_prod_sq_le_sum (l.map (fun i : ι => 1 - sys.checkProj i))
    h_proj h_comm ψ
  rw [List.map_map] at h_sum_le
  have h_comp : ((fun p => ‖(1 - p) ψ‖ ^ 2) ∘ fun i : ι => 1 - sys.checkProj i) =
      (fun i : ι => RCLike.re (inner ℂ ψ (sys.checkProj i ψ))) := by
    funext i
    change ‖(1 - (1 - sys.checkProj i)) ψ‖ ^ 2 = RCLike.re (inner ℂ ψ (sys.checkProj i ψ))
    rw [sub_sub_cancel, isStarProjection_re_inner_eq_norm_sq_bhm (sys.is_projector i) ψ]
  rw [h_comp, Finset.sum_map_toList] at h_sum_le
  refine le_trans h_sum_le ?_
  dsimp [IndexedCommutingProjectorHamiltonian.H0]
  rw [ContinuousLinearMap.sum_apply, inner_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, Complex.re_ofReal_mul]
  change RCLike.re (inner ℂ ψ (sys.checkProj i ψ)) ≤
    sys.weight i * RCLike.re (inner ℂ ψ (sys.checkProj i ψ))
  have hQ_nn : 0 ≤ RCLike.re (inner ℂ ψ (sys.checkProj i ψ)) := by
    rw [isStarProjection_re_inner_eq_norm_sq_bhm (sys.is_projector i) ψ]
    exact sq_nonneg _
  calc RCLike.re (inner ℂ ψ (sys.checkProj i ψ))
    _ = 1 * RCLike.re (inner ℂ ψ (sys.checkProj i ψ)) := (one_mul _).symm
    _ ≤ sys.weight i * RCLike.re (inner ℂ ψ (sys.checkProj i ψ)) :=
      mul_le_mul_of_nonneg_right (h_weight i) hQ_nn

/-- When `∀ i : ι, 1 ≤ sys.weight i`, $\psi \in \ker H_0 \iff P_0 \psi = \psi$. -/
lemma IndexedCommutingProjectorHamiltonian.mem_groundSpace_iff {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (ψ : ManyBodyHilbertSpace Site) :
    ψ ∈ sys.groundSpace ↔ sys.P0 ψ = ψ := by
  constructor
  · intro hψ
    have hH0_ψ : sys.H0 ψ = 0 := hψ
    have h1P0 : IsStarProjection (1 - sys.P0) := sys.isStarProjection_P0.one_sub
    have h_le := sys.one_sub_P0_form_le_H0 h_weight ψ
    rw [hH0_ψ, inner_zero_right, map_zero, isStarProjection_re_inner_eq_norm_sq_bhm h1P0 ψ] at h_le
    have h_norm_zero : ‖(1 - sys.P0) ψ‖ = 0 :=
      sq_eq_zero_iff.mp (le_antisymm h_le (sq_nonneg _))
    have h_sub : ψ - sys.P0 ψ = 0 := by
      simpa [ContinuousLinearMap.sub_apply] using norm_eq_zero.mp h_norm_zero
    exact (sub_eq_zero.mp h_sub).symm
  · intro hPψ
    change sys.H0 ψ = 0
    rw [← hPψ, ← ContinuousLinearMap.mul_apply, sys.ham0_mul_proj0_eq_zero,
      ContinuousLinearMap.zero_apply]

/-- Spectral gap of `sys.H0` on `(sys.groundSpace)ᗮ`: when `∀ i : ι, 1 ≤ sys.weight i`,
    every $\psi \in (\ker H_0)^\perp$ satisfies $\|\psi\|^2 \le \mathrm{re}\langle \psi, H_0 \psi \rangle$. -/
lemma IndexedCommutingProjectorHamiltonian.norm_sq_le_re_inner_H0_of_mem_orthogonal_groundSpace
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    {ψ : ManyBodyHilbertSpace Site} (hψ : ψ ∈ (sys.groundSpace)ᗮ) :
    ‖ψ‖ ^ 2 ≤ RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
  have hPψ_mem : sys.P0 ψ ∈ sys.groundSpace := by
    rw [sys.mem_groundSpace_iff h_weight]
    change (sys.P0 * sys.P0) ψ = sys.P0 ψ
    rw [sys.isStarProjection_P0.isIdempotentElem.eq]
  have h_orth : inner ℂ (sys.P0 ψ) ψ = 0 := Submodule.inner_right_of_mem_orthogonal hPψ_mem hψ
  have hPψ_zero : sys.P0 ψ = 0 := by
    have h_norm_sq : ‖sys.P0 ψ‖ ^ 2 = 0 := by
      rw [← isStarProjection_re_inner_eq_norm_sq_bhm sys.isStarProjection_P0 ψ,
        ← ContinuousLinearMap.adjoint_inner_left,
        show sys.P0† = star sys.P0 from rfl, sys.isStarProjection_P0.isSelfAdjoint.star_eq,
        h_orth, map_zero]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h_norm_sq)
  have h1P_ψ : (1 - sys.P0) ψ = ψ := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hPψ_zero, sub_zero]
  have h_form := sys.one_sub_P0_form_le_H0 h_weight ψ
  rw [h1P_ψ, inner_self_eq_norm_sq] at h_form
  exact h_form

/-!
## 2. Dressed Energy Form Sandwich $\frac{3}{4} H_0 \le U^\dagger H U - E_0 I \le \frac{5}{4} H_0 + \delta_{\mathrm{split}} I$
-/

/-- **Dressed Energy Form Sandwich (`dressed_energy_sandwich_of_relative_form_bound`)**:
    If a unitary $U$ satisfies $[U^\dagger H U, P_0] = 0$, $P_0 (U^\dagger H U - E_0 I) P_0$ has norm
    at most $\delta_{\mathrm{split}}$, and $(1 - P_0)(U^\dagger H U - H_0 - E_0 I)(1 - P_0)$ is
    bounded in quadratic form by $\frac{1}{4} \langle \psi, H_0 \psi \rangle + \delta_{\mathrm{split}} \|\psi\|^2$,
    then `SatisfiesDressedEnergySandwich sys V U E0 δ_split` holds. -/
theorem dressed_energy_sandwich_of_relative_form_bound
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {E0 δ_split : ℝ}
    (_h_comm : Commute (U.1† * (sys.H0 + V.totalPerturbation) * U.1) sys.P0)
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ ((U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    SatisfiesDressedEnergySandwich sys V U E0 δ_split := by
  intro ϕ _hϕ
  let U_iso := unitaryToLinearIsometryEquiv U
  let ψ : ManyBodyHilbertSpace Site := U_iso.symm ϕ
  have hU_ψ : U.1 ψ = ϕ := U_iso.apply_symm_apply ϕ
  have h_norm : ‖ψ‖ = ‖ϕ‖ := U_iso.symm.norm_map ϕ
  have h_star_self : U.1† * U.1 = 1 := Unitary.coe_star_mul_self U
  have h_H0_tilde : inner ℂ ϕ (indexedDressedH0Op sys U ϕ) = inner ℂ ψ (sys.H0 ψ) := by
    rw [← hU_ψ, inner_unitary_conj U (indexedDressedH0Op sys U) ψ]
    have h_eq : U.1† * indexedDressedH0Op sys U * U.1 = sys.H0 := by
      unfold indexedDressedH0Op
      calc U.1† * (U.1 * sys.H0 * U.1†) * U.1
        _ = (U.1† * U.1) * sys.H0 * (U.1† * U.1) := by simp only [mul_assoc]
        _ = 1 * sys.H0 * 1 := by rw [h_star_self]
        _ = sys.H0 := by rw [one_mul, mul_one]
    rw [h_eq]
  have h_H_conj :
      inner ℂ ϕ ((sys.H0 + V.totalPerturbation) ϕ) = inner ℂ ψ ((U.1† * (sys.H0 + V.totalPerturbation) * U.1) ψ) := by
    rw [← hU_ψ]
    exact inner_unitary_conj U (sys.H0 + V.totalPerturbation) ψ
  have h_shift_ϕ :
      RCLike.re (inner ℂ ϕ (((sys.H0 + V.totalPerturbation) - (E0 : ℂ) • 1) ϕ)) =
        RCLike.re (inner ℂ ψ ((U.1† * (sys.H0 + V.totalPerturbation) * U.1) ψ)) - E0 * ‖ϕ‖ ^ 2 := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub, h_H_conj, re_inner_smul_one]
  have h_diff_ψ :
      RCLike.re (inner ℂ ψ ((U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 - (E0 : ℂ) • 1) ψ)) =
        RCLike.re (inner ℂ ψ ((U.1† * (sys.H0 + V.totalPerturbation) * U.1) ψ)) -
          RCLike.re (inner ℂ ψ (sys.H0 ψ)) - E0 * ‖ψ‖ ^ 2 := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      inner_sub_right, inner_sub_right, map_sub, map_sub, re_inner_smul_one]
  have h_abs := abs_le.mp (h_form ψ)
  rw [h_diff_ψ, ← h_H0_tilde, h_norm] at h_abs
  rw [h_shift_ϕ]
  dsimp [bhmSandwichLower, bhmSandwichUpper, bhmSandwichDeviation, bhmPerturbedGap] at h_abs ⊢
  constructor <;> linarith

/-- **Indexed Unitary-Dressed Form Bound to `IndexedHasStableLowEnergyBand`**:
    Under `∀ i : ι, 1 ≤ sys.weight i`, if a unitary $U$ satisfies the relative form bound
    $|\mathrm{re}\langle \psi, (U^\dagger H U - H_0 - E_0 I)\psi \rangle| \le \gamma \mathrm{re}\langle \psi, H_0 \psi \rangle + \varepsilon \|\psi\|^2$
    with $\gamma \le 1/4$, $\gamma + 2\varepsilon \le 1/2$, and $2\varepsilon \le \delta_{\mathrm{split}}$,
    then `IndexedHasStableLowEnergyBand sys V bhmPerturbedGap δ_split` holds. -/
theorem indexedHasStableLowEnergyBand_of_singleDressedBound
    {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    (δ_split : ℝ)
    (U : ManyBodyHilbertSpace Site ≃ₗᵢ[ℂ] ManyBodyHilbertSpace Site)
    (c0 γ ε : ℝ)
    (hγ : γ ≤ 1 / 4)
    (h_gap : γ + 2 * ε ≤ 1 / 2)
    (h_split : 2 * ε ≤ δ_split)
    (h_bound : ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ (U ϕ) ((sys.H0 + V.totalPerturbation) (U ϕ))) -
        RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) - c0 * ‖ϕ‖ ^ 2| ≤
        γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) + ε * ‖ϕ‖ ^ 2) :
    IndexedHasStableLowEnergyBand sys V bhmPerturbedGap δ_split := by
  let W : Submodule ℂ (ManyBodyHilbertSpace Site) :=
    sys.groundSpace.map U.toLinearEquiv.toLinearMap
  have hW_dim : Module.finrank ℂ W = sys.groundDegeneracy :=
    LinearEquiv.finrank_map_eq U.toLinearEquiv sys.groundSpace
  apply indexedHasStableLowEnergyBand_of_trialSubspace sys V bhmPerturbedGap δ_split W hW_dim
    (c0 - ε) (c0 + ε) (c0 + (1 - γ) - ε)
  · linarith
  · dsimp [bhmPerturbedGap]; linarith
  · intro ψ
    let ϕ := U.symm ψ
    have hUϕ : U ϕ = ψ := U.apply_symm_apply ψ
    have h_norm : ‖ϕ‖ = ‖ψ‖ := U.symm.norm_map ψ
    have hb := (abs_le.mp (h_bound ϕ)).1
    rw [hUϕ, h_norm] at hb
    have hH0_nn : 0 ≤ RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := sys.re_inner_H0_nonneg ϕ
    have h1_sub_γ : 0 ≤ 1 - γ := by linarith
    have h_prod_nn : 0 ≤ (1 - γ) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) :=
      mul_nonneg h1_sub_γ hH0_nn
    linarith
  · intro ψ hψ
    rcases Submodule.mem_map.mp hψ with ⟨ϕ, hϕ_mem, rfl⟩
    change RCLike.re (inner ℂ (U ϕ) ((sys.H0 + V.totalPerturbation) (U ϕ))) ≤ (c0 + ε) * ‖U ϕ‖ ^ 2
    rw [U.norm_map ϕ]
    have hH0_zero : sys.H0 ϕ = 0 := hϕ_mem
    have hb := (abs_le.mp (h_bound ϕ)).2
    rw [hH0_zero, inner_zero_right, map_zero, mul_zero, sub_zero, zero_add] at hb
    linarith
  · intro ψ hψ
    let ϕ := U.symm ψ
    have hUϕ : U ϕ = ψ := U.apply_symm_apply ψ
    have h_norm : ‖ϕ‖ = ‖ψ‖ := U.symm.norm_map ψ
    have hϕ_orth : ϕ ∈ (sys.groundSpace)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro χ hχ
      have hUχ_mem : U χ ∈ W := Submodule.mem_map_of_mem hχ
      have h_orth := Submodule.inner_right_of_mem_orthogonal hUχ_mem hψ
      rw [← U.inner_map_map χ ϕ, hUϕ]
      exact h_orth
    have hH0_gap : ‖ϕ‖ ^ 2 ≤ RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) :=
      sys.norm_sq_le_re_inner_H0_of_mem_orthogonal_groundSpace h_weight hϕ_orth
    have hb := (abs_le.mp (h_bound ϕ)).1
    rw [hUϕ, h_norm] at hb
    rw [h_norm] at hH0_gap
    have h1_sub_γ : 0 ≤ 1 - γ := by linarith
    have h_mul : (1 - γ) * ‖ψ‖ ^ 2 ≤ (1 - γ) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) :=
      mul_le_mul_of_nonneg_left hH0_gap h1_sub_γ
    linarith

/-!
## 3. Sector-Filtered Bravyi–Hastings–Michalakis Spectral Stability
-/

/-- Unconditional `HasSectorFilteredQACStability` from `[H0 + V_tot, P0] = 0` and relative form bound. -/
lemma hasSectorFilteredQACStability_of_commute_and_form_bound
    {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (h_weight : ∀ i : ι, 1 ≤ sys.weight i)
    {δ_split E0 γ ε : ℝ} (hγ : γ ≤ 1 / 4) (h_gap : γ + 2 * ε ≤ 1 / 2) (h_split : 2 * ε ≤ δ_split)
    (h_comm : Commute (sys.H0 + V.totalPerturbation) sys.P0)
    (h_form : ∀ ϕ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ϕ ((V.totalPerturbation - (E0 : ℂ) • 1) ϕ))| ≤
        γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) + ε * ‖ϕ‖ ^ 2) :
    HasSectorFilteredQACStability sys V δ_split := by
  let U1 : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) := 1
  have hU1_coe : U1.1 = 1 := rfl
  have hU1_adj : U1.1† = 1 := star_one (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  have h_conj_eq : U1.1† * (sys.H0 + V.totalPerturbation) * U1.1 = sys.H0 + V.totalPerturbation := by
    rw [hU1_adj, hU1_coe, one_mul, mul_one]
  have h_comm_U1 : Commute (U1.1† * (sys.H0 + V.totalPerturbation) * U1.1) sys.P0 := by
    rw [h_conj_eq]; exact h_comm
  have h_diff_eq : ∀ ϕ : ManyBodyHilbertSpace Site,
      RCLike.re (inner ℂ ϕ ((U1.1† * (sys.H0 + V.totalPerturbation) * U1.1 - sys.H0 - (E0 : ℂ) • 1) ϕ)) =
      RCLike.re (inner ℂ ϕ ((V.totalPerturbation - (E0 : ℂ) • 1) ϕ)) := fun ϕ => by
    rw [h_conj_eq, add_sub_cancel_left]
  have h_band : IndexedHasStableLowEnergyBand sys V bhmPerturbedGap δ_split := by
    let U_iso := unitaryToLinearIsometryEquiv U1
    apply indexedHasStableLowEnergyBand_of_singleDressedBound sys V h_weight δ_split U_iso E0 γ ε
      hγ h_gap h_split (fun ϕ => ?_)
    have hU_ϕ : U_iso ϕ = ϕ := rfl
    have h_lhs :
        RCLike.re (inner ℂ (U_iso ϕ) ((sys.H0 + V.totalPerturbation) (U_iso ϕ))) -
          RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) - E0 * ‖ϕ‖ ^ 2 =
        RCLike.re (inner ℂ ϕ ((V.totalPerturbation - (E0 : ℂ) • 1) ϕ)) := by
      rw [hU_ϕ, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
        inner_add_right, inner_sub_right, map_add, map_sub, re_inner_smul_one]; ring
    rw [h_lhs]; exact h_form ϕ
  refine ⟨h_band, U1, E0, h_comm_U1, ?_⟩
  apply dressed_energy_sandwich_of_relative_form_bound sys V U1 h_comm_U1 (fun ψ => ?_)
  rw [h_diff_eq ψ]
  have h1 : γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) ≤
      bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) := by
    rw [show bhmSandwichDeviation = 1 / 4 from rfl]
    exact mul_le_mul_of_nonneg_right hγ (sys.re_inner_H0_nonneg ψ)
  have h2 : ε * ‖ψ‖ ^ 2 ≤ (δ_split / 2) * ‖ψ‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖ψ‖)
  exact le_trans (h_form ψ) (add_le_add h1 h2)

/-- **Master Unconditional Sector-Filtered BHM Stability Theorem
    (`theorem_unconditional_sector_filtered_bhm_stability_of_commute_P0`)**. -/
theorem theorem_unconditional_sector_filtered_bhm_stability_of_commute_P0
    (D : ℕ) [NeZero D] (C : ℝ) (hC : 1 ≤ C)
    (c_star : ℝ) (hc_pos : 0 < c_star) (hc_bound : 2 * C * c_star < 1)
    (f : ℕ → ℝ) (hf : IsSuperpolynomialDecay f) :
    ∃ (J0 : ℝ) (L0 : ℕ) (δ_split : ℕ → ℝ),
      0 < J0 ∧ 1 ≤ L0 ∧ IsSuperpolynomialDecay δ_split ∧
      ∀ (L : ℕ) [NeZero L], L0 ≤ L →
        ∀ (Site : BoxD D L → Type) [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
          [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
          (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
          (Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
          let L_star := Nat.floor (c_star * (L : ℝ))
          (∀ i : ι, 1 ≤ sys.weight i) →
          SatisfiesSectorFilteredLinearTQO2 sys Pi_sec L_star C →
          ∀ (J : ℝ) (V : QuasiLocalPerturbation D L Site),
            0 ≤ J → J ≤ J0 → V.SatisfiesDecayBound J f →
            (HasSectorFilteredQACStability sys (indexedLocalBlockDiagonalProjection sys V) (δ_split L) ∧
              ∃ V_loc : QuasiLocalPerturbation D L Site,
                (∀ r : ℕ, ∀ A : Finset (BoxD D L),
                  V_loc.term r A = (1 - sys.localGroundProj A) * V.term r A * (1 - sys.localGroundProj A)) ∧
                V_loc.SatisfiesDecayBound J f ∧
                (∀ r : ℕ, ∀ A : Finset (BoxD D L), Commute (V_loc.term r A) sys.P0) ∧
                HasSectorFilteredQACStability sys V_loc (δ_split L)) ∧
            ((∀ r ∈ Finset.Icc 1 L_star, ∀ A ∈ boxCubes D L r, Commute (V.term r A) sys.P0) →
              ∃ E0 : ℝ, ∀ ϕ : ManyBodyHilbertSpace Site, Pi_sec ϕ = ϕ →
                |RCLike.re (inner ℂ ϕ ((V.totalPerturbation - (E0 : ℂ) • 1) ϕ))| ≤
                  bhmSandwichDeviation * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) +
                    (δ_split L / 2) * ‖ϕ‖ ^ 2) ∧
            ((∀ ϕ : ManyBodyHilbertSpace Site, Pi_sec ϕ = ϕ) →
              (∀ r ∈ Finset.Icc 1 L, ∀ A ∈ boxCubes D L r, Commute (V.term r A) sys.P0) →
              HasSectorFilteredQACStability sys V (δ_split L)) := by
  have hC_pos : 0 < C := by linarith
  let δ_tail : ℕ → ℝ := fTilde C f
  have hδ_tail : IsSuperpolynomialDecay δ_tail := isSuperpolynomialDecay_fTilde hC_pos hf
  let g_series : ℕ → ℝ := fun r => (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r
  have hg_nonneg : ∀ r : ℕ, 0 ≤ g_series r := fun r =>
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) D) (hf.1 r)
  have hg_sum : Summable g_series := summable_two_mul_linearExpansionRadius_pow_mul D C hC hf
  let S : ℝ := ∑' r : ℕ, g_series r
  have hS_nonneg : 0 ≤ S := tsum_nonneg hg_nonneg
  let J0 : ℝ := 1 / (8 * (S + 1))
  have hJ0_pos : 0 < J0 := by dsimp [J0]; positivity
  let δ_split : ℕ → ℝ := fun L => (2 * J0) * ((L : ℝ) ^ D * δ_tail ⌊c_star * (L : ℝ)⌋₊)
  have hδ_split : IsSuperpolynomialDecay δ_split :=
    isSuperpolynomialDecay_const_mul
      (isSuperpolynomialDecay_mul_pow (isSuperpolynomialDecay_floor_mul hδ_tail hc_pos) D)
      (by positivity)
  have h_tendsto_zero : Tendsto δ_split atTop (𝓝 0) := by simpa using hδ_split.2 0
  rcases Filter.eventually_atTop.mp (h_tendsto_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)))
    with ⟨N0, hN0⟩
  let L0 : ℕ := max (max 1 N0) ⌈1 / c_star⌉₊
  refine ⟨J0, L0, δ_split, hJ0_pos, le_trans (le_max_left 1 N0) (le_max_left _ _), hδ_split, ?_⟩
  intro L _ hL_ge Site _ _ _ ι _ _ sys Pi_sec L_star h_weight h_tqo J V hJ_nonneg hJ_le hV_decay
  have hL_ge_ceil : ⌈1 / c_star⌉₊ ≤ L := le_trans (le_max_right _ _) hL_ge
  have hL_ge_N0 : N0 ≤ L := le_trans (le_trans (le_max_right 1 N0) (le_max_left _ _)) hL_ge
  have hL_star1 : 1 ≤ L_star := by
    apply Nat.le_floor
    have h1 : 1 / c_star ≤ (L : ℝ) := le_trans (Nat.le_ceil (1 / c_star)) (Nat.cast_le.mpr hL_ge_ceil)
    have h2 := (div_le_iff₀ hc_pos).mp h1; rw [Nat.cast_one]; linarith
  have hL_star_le_L : L_star ≤ L := by
    apply Nat.floor_le_of_le
    have hc_le_one : c_star ≤ 1 := by nlinarith
    have hL_nonneg : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    nlinarith
  let γ : ℝ := ∑ r ∈ Finset.Icc 1 L_star, 2 * J * g_series r
  let ε : ℝ := ∑ r ∈ Finset.Icc (L_star + 1) L, J * ((L : ℝ) ^ D) * f r
  have hγ_bound : γ ≤ 1 / 4 := by
    have h_sum_g_le : ∑ r ∈ Finset.Icc 1 L_star, g_series r ≤ S :=
      hg_sum.sum_le_tsum (Finset.Icc 1 L_star) (fun r _ => hg_nonneg r)
    have h_eq : γ = 2 * J * ∑ r ∈ Finset.Icc 1 L_star, g_series r := by
      dsimp [γ]; rw [← Finset.mul_sum]
    have hJ_S : J * (8 * (S + 1)) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 8 * (S + 1))).mp hJ_le
    rw [h_eq]
    have h1 : 2 * J * ∑ r ∈ Finset.Icc 1 L_star, g_series r ≤ 2 * J * (S + 1) := by nlinarith
    linarith
  have h_split_bound : 2 * ε ≤ δ_split L := by
    have h_eps_eq : ε = (J * ((L : ℝ) ^ D)) * ∑ r ∈ Finset.Icc (L_star + 1) L, f r := by
      dsimp [ε]; rw [← Finset.mul_sum]
    have h_tail : ∑ r ∈ Finset.Icc (L_star + 1) L, f r ≤ δ_tail L_star :=
      sum_tail_le_fTilde C hC hf L L_star hL_star1
    rw [h_eps_eq]; dsimp [δ_split]
    have h1 : (J * ((L : ℝ) ^ D)) * ∑ r ∈ Finset.Icc (L_star + 1) L, f r ≤
        (J * ((L : ℝ) ^ D)) * δ_tail L_star :=
      mul_le_mul_of_nonneg_left h_tail (mul_nonneg hJ_nonneg (pow_nonneg (Nat.cast_nonneg L) D))
    have h2 : (J * ((L : ℝ) ^ D)) * δ_tail L_star ≤ (J0 * ((L : ℝ) ^ D)) * δ_tail L_star :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hJ_le (pow_nonneg (Nat.cast_nonneg L) D))
        (hδ_tail.1 L_star)
    linarith
  have h_gap_bound : γ + 2 * ε ≤ 1 / 2 := by
    have hδ_lt : δ_split L < 1 / 4 := hN0 L hL_ge_N0; linarith
  have h_high_form : ∀ (W : QuasiLocalPerturbation D L Site), W.SatisfiesDecayBound J f →
      ∀ ϕ : ManyBodyHilbertSpace Site,
        |RCLike.re (inner ℂ ϕ ((∑ r ∈ Finset.Icc (L_star + 1) L, ∑ A ∈ boxCubes D L r, W.term r A) ϕ))| ≤
          ε * ‖ϕ‖ ^ 2 := by
    intro W hW_dec ϕ
    rw [re_inner_sum_apply]
    change |∑ r ∈ Finset.Icc (L_star + 1) L, RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, W.term r A) ϕ))| ≤
      (∑ r ∈ Finset.Icc (L_star + 1) L, J * ((L : ℝ) ^ D) * f r) * ‖ϕ‖ ^ 2
    rw [Finset.sum_mul]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun r hr => ?_))
    have hr_mem : r ∈ Finset.Icc 1 L :=
      Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hr).1; omega, (Finset.mem_Icc.mp hr).2⟩
    exact tail_scale_r_form_bound W hJ_nonneg hf.1 hW_dec hr_mem ϕ
  have h_part1 : HasSectorFilteredQACStability sys (indexedLocalBlockDiagonalProjection sys V) (δ_split L) := by
    let V_loc := indexedLocalBlockDiagonalProjection sys V
    rcases indexedLocalBlockDiagonalProjection_properties sys V hV_decay with ⟨hV_loc_decay, hV_loc_comm⟩
    have h_comm_tot : Commute (sys.H0 + V_loc.totalPerturbation) sys.P0 :=
      commute_H0_add_V_tot_P0_of_commute_terms sys V_loc (fun r _ A _ => hV_loc_comm r A)
    apply hasSectorFilteredQACStability_of_commute_and_form_bound sys V_loc h_weight
      hγ_bound h_gap_bound h_split_bound h_comm_tot (E0 := 0) (fun ϕ => ?_)
    have h_zero_shift : (V_loc.totalPerturbation - ((0 : ℝ) : ℂ) • 1) ϕ = V_loc.totalPerturbation ϕ := by simp
    have h_V_split : V_loc.totalPerturbation =
        (∑ r ∈ Finset.Icc 1 L_star, ∑ A ∈ boxCubes D L r, V_loc.term r A) +
        (∑ r ∈ Finset.Icc (L_star + 1) L, ∑ A ∈ boxCubes D L r, V_loc.term r A) :=
      sum_Icc_split hL_star1 hL_star_le_L (fun r => ∑ A ∈ boxCubes D L r, V_loc.term r A)
    rw [h_zero_shift, h_V_split, ContinuousLinearMap.add_apply, inner_add_right, map_add]
    have h_low_bound :
        |RCLike.re (inner ℂ ϕ ((∑ r ∈ Finset.Icc 1 L_star, ∑ A ∈ boxCubes D L r, V_loc.term r A) ϕ))| ≤
          γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
      rw [re_inner_sum_apply]
      change |∑ r ∈ Finset.Icc 1 L_star, RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, V_loc.term r A) ϕ))| ≤
        (∑ r ∈ Finset.Icc 1 L_star, 2 * J * g_series r) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ))
      rw [Finset.sum_mul]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun r hr => ?_))
      have h_sc := localBlockDiagonal_scale_r_form_bound sys h_weight V hC hJ_nonneg hf.1 hV_decay
        (Finset.mem_Icc.mp hr).1 (le_trans (Finset.mem_Icc.mp hr).2 hL_star_le_L) ϕ
      have h_eq : 2 * J * g_series r = 2 * J * (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r := by
        dsimp [g_series]; ring
      rw [h_eq]; exact h_sc
    exact le_trans (abs_add_le _ _) (add_le_add h_low_bound (h_high_form V_loc hV_loc_decay ϕ))
  have h_part2 :
      (∀ r ∈ Finset.Icc 1 L_star, ∀ A ∈ boxCubes D L r, Commute (V.term r A) sys.P0) →
      ∃ E0 : ℝ, ∀ ϕ : ManyBodyHilbertSpace Site, Pi_sec ϕ = ϕ →
        |RCLike.re (inner ℂ ϕ ((V.totalPerturbation - (E0 : ℂ) • 1) ϕ))| ≤
          γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) + ε * ‖ϕ‖ ^ 2 := by
    intro hV_comm_low
    have h_scale_exists : ∀ r : ℕ, r ∈ Finset.Icc 1 L_star →
        ∃ c_r : ℝ, ∀ ϕ : ManyBodyHilbertSpace Site, Pi_sec ϕ = ϕ →
          |RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, V.term r A) ϕ)) - c_r * ‖ϕ‖ ^ 2| ≤
            (2 * J * g_series r) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
      intro r hr
      rcases indexed_sector_scale_r_form_bound sys h_weight hJ_nonneg hf.1 h_tqo V hV_decay
        (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2
        (le_trans (Finset.mem_Icc.mp hr).2 hL_star_le_L) (hV_comm_low r hr) with ⟨c_r, hc_r⟩
      refine ⟨c_r, fun ϕ hϕ => ?_⟩
      have h_eq : 2 * J * g_series r = 2 * J * (((2 * linearExpansionRadius C r : ℕ) : ℝ) ^ D) * f r := by
        dsimp [g_series]; ring
      rw [h_eq]; exact hc_r ϕ hϕ
    let c_scale : ℕ → ℝ := fun r =>
      if hr : r ∈ Finset.Icc 1 L_star then (h_scale_exists r hr).choose else 0
    have hc_scale : ∀ r ∈ Finset.Icc 1 L_star, ∀ ϕ : ManyBodyHilbertSpace Site, Pi_sec ϕ = ϕ →
        |RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, V.term r A) ϕ)) - c_scale r * ‖ϕ‖ ^ 2| ≤
          (2 * J * g_series r) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
      intro r hr ϕ hϕ; dsimp [c_scale]; rw [dif_pos hr]; exact (h_scale_exists r hr).choose_spec ϕ hϕ
    let E0 : ℝ := ∑ r ∈ Finset.Icc 1 L_star, c_scale r
    refine ⟨E0, fun ϕ hϕ_sec => ?_⟩
    have h_V_split : V.totalPerturbation =
        (∑ r ∈ Finset.Icc 1 L_star, ∑ A ∈ boxCubes D L r, V.term r A) +
        (∑ r ∈ Finset.Icc (L_star + 1) L, ∑ A ∈ boxCubes D L r, V.term r A) :=
      sum_Icc_split hL_star1 hL_star_le_L (fun r => ∑ A ∈ boxCubes D L r, V.term r A)
    have h_lhs :
        RCLike.re (inner ℂ ϕ ((V.totalPerturbation - (E0 : ℂ) • 1) ϕ)) =
        (RCLike.re (inner ℂ ϕ ((∑ r ∈ Finset.Icc 1 L_star, ∑ A ∈ boxCubes D L r, V.term r A) ϕ)) -
          E0 * ‖ϕ‖ ^ 2) +
        RCLike.re (inner ℂ ϕ ((∑ r ∈ Finset.Icc (L_star + 1) L, ∑ A ∈ boxCubes D L r, V.term r A) ϕ)) := by
      rw [ContinuousLinearMap.sub_apply, h_V_split, ContinuousLinearMap.add_apply,
        inner_sub_right, inner_add_right, map_sub, map_add, re_inner_smul_one]; ring
    rw [h_lhs]
    have h_low_bound :
        |RCLike.re (inner ℂ ϕ ((∑ r ∈ Finset.Icc 1 L_star, ∑ A ∈ boxCubes D L r, V.term r A) ϕ)) -
          E0 * ‖ϕ‖ ^ 2| ≤ γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
      rw [re_inner_sum_apply]
      change |∑ r ∈ Finset.Icc 1 L_star, RCLike.re (inner ℂ ϕ ((∑ A ∈ boxCubes D L r, V.term r A) ϕ)) -
          (∑ r ∈ Finset.Icc 1 L_star, c_scale r) * ‖ϕ‖ ^ 2| ≤
        (∑ r ∈ Finset.Icc 1 L_star, 2 * J * g_series r) * RCLike.re (inner ℂ ϕ (sys.H0 ϕ))
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.sum_mul]
      exact le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum (fun r hr => hc_scale r hr ϕ hϕ_sec))
    exact le_trans (abs_add_le _ _) (add_le_add h_low_bound (h_high_form V hV_decay ϕ))
  rcases indexedLocalBlockDiagonalProjection_properties sys V hV_decay with ⟨hV_loc_decay, hV_loc_comm⟩
  refine ⟨⟨h_part1, indexedLocalBlockDiagonalProjection sys V, fun _ _ => rfl,
      hV_loc_decay, hV_loc_comm, h_part1⟩, ?_, ?_⟩
  · intro hV_comm_low
    rcases h_part2 hV_comm_low with ⟨E0, hE0⟩
    refine ⟨E0, fun ϕ hϕ => ?_⟩
    have h1 : γ * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ϕ (sys.H0 ϕ)) := by
      rw [show bhmSandwichDeviation = 1 / 4 from rfl]
      exact mul_le_mul_of_nonneg_right hγ_bound (sys.re_inner_H0_nonneg ϕ)
    have h2 : ε * ‖ϕ‖ ^ 2 ≤ (δ_split L / 2) * ‖ϕ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ‖ϕ‖)
    exact le_trans (hE0 ϕ hϕ) (add_le_add h1 h2)
  · intro hPi_all hV_comm_all
    have hV_comm_low : ∀ r ∈ Finset.Icc 1 L_star, ∀ A ∈ boxCubes D L r, Commute (V.term r A) sys.P0 :=
      fun r hr A hA => hV_comm_all r
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, le_trans (Finset.mem_Icc.mp hr).2 hL_star_le_L⟩)
        A hA
    rcases h_part2 hV_comm_low with ⟨E0, hE0⟩
    exact hasSectorFilteredQACStability_of_commute_and_form_bound sys V h_weight
      hγ_bound h_gap_bound h_split_bound
      (commute_H0_add_V_tot_P0_of_commute_terms sys V hV_comm_all)
      (fun ϕ => hE0 ϕ (hPi_all ϕ))

end
