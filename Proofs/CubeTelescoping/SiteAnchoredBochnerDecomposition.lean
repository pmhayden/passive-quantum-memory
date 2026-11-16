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

import Proofs.BandLimitedFilter.BochnerFilteredSiteLinearity
import Proofs.CubeTelescoping.SpectralAlignmentUnitary
import Proofs.QuasiLocalDressing.DressedObservableExpansion

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Bochner Filter Norm Contractivity and Site-Anchored Rotated Energy Decomposition

Proves `L^1` operator-norm contractivity of Bochner time convolutions `bochnerFilteredOp`, establishes the exact site-anchored partitions of unity `∑ u, siteCheckOp u = sys.H0` and `∑ u, sitePerturbationOp u = V.totalPerturbation`, and derives self-adjointness, norm bounds, and the global rotated Hamiltonian decomposition `∑ u, indexedFilteredSiteOp u = U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0`.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

/-!
## 1. Pointwise Unitary Norm Bounds and Filter Contractivity for `bhFilterWeight`
-/

/-- For a self-adjoint Hamiltonian $H'$, `timeEvolutionOp H' t` has operator norm $\le 1$. -/
theorem norm_timeEvolutionOp_le_one_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (t : ℝ) :
    ‖timeEvolutionOp H' t‖ ≤ 1 := by
  have h_unit : (timeEvolutionOp H' t)† * timeEvolutionOp H' t = 1 :=
    Unitary.coe_star_mul_self (unitaryOfTimeEvolutionOp H' hH' t)
  exact (norm_le_one_of_adjoint_mul_self_eq_one h_unit).1

/-- For a self-adjoint Hamiltonian $H'$, `heisenbergFlow H' t O` has operator norm $\le \|O\|$. -/
theorem norm_heisenbergFlow_le_bhm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') (t : ℝ)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖heisenbergFlow H' t O‖ ≤ ‖O‖ := by
  unfold heisenbergFlow
  exact norm_sandwich_le_of_norm_le_one
    (norm_timeEvolutionOp_le_one_bhm hH' t)
    (norm_timeEvolutionOp_le_one_bhm hH' (-t))

/-- General $L^1$ norm bound for `bochnerFilteredOp H' w O` when $H'$ is self-adjoint:
    $\|\mathrm{bochnerFilteredOp}\ H'\ w\ O\| \le \left(\int \|w(t)\|\,dt\right) \|O\|$. -/
theorem norm_bochnerFilteredOp_le_integral_norm_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H') {w : ℝ → ℂ}
    (hw_int : Integrable (fun t : ℝ => ‖w t‖) MeasureTheory.volume)
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖bochnerFilteredOp H' w O‖ ≤ (∫ t : ℝ, ‖w t‖) * ‖O‖ := by
  unfold bochnerFilteredOp
  calc ‖∫ t : ℝ, w t • heisenbergFlow H' t O‖
    _ ≤ ∫ t : ℝ, ‖w t • heisenbergFlow H' t O‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖w t‖ * ‖O‖ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (hw_int.mul_const ‖O‖) (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_heisenbergFlow_le_bhm hH' t O) (norm_nonneg (w t))
    _ = (∫ t : ℝ, ‖w t‖) * ‖O‖ := integral_mul_const ‖O‖ (fun t : ℝ => ‖w t‖)

/-- Operator-norm contractivity of `bochnerFilteredOp H' w_BH11`. -/
theorem norm_bochnerFilteredOp_w_BH11_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH' : IsSelfAdjoint H')
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖bochnerFilteredOp H' bhFilterWeight O‖ ≤ ‖O‖ := by
  have h := norm_bochnerFilteredOp_le_integral_norm_mul hH' integrable_norm_w_BH11 O
  rwa [integral_norm_w_BH11_eq_one, one_mul] at h

/-!
## 2. Site-Anchored Partition of Unity Identities on `BoxD D L`
-/

/-- Fiberwise partition of unity over `Finset.univ : Finset β`: summing a filtered finset sum over
    all fibers `g a = u` recovers the sum over `S`. -/
lemma sum_fiberwise_univ_eq {α β M : Type*} [Fintype β] [DecidableEq β] [AddCommMonoid M]
    (S : Finset α) (g : α → β) (f : α → M) :
    (∑ u : β, ∑ a ∈ S.filter (fun a => g a = u), f a) = ∑ a ∈ S, f a :=
  Finset.sum_fiberwise_of_maps_to (g := g) (fun _ _ => Finset.mem_univ _) f

/-- **Indexed Site-Anchored Check Partition of Unity
    (`IndexedCommutingProjectorHamiltonian.sum_siteCheckOp_eq_H0`)**:
    For any `IndexedCommutingProjectorHamiltonian`, summing `sys.siteCheckOp u` over all
    sites $u \in \mathrm{BoxD}\ D\ L$ equals `sys.H0`. -/
theorem IndexedCommutingProjectorHamiltonian.sum_siteCheckOp_eq_H0 {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    (∑ u : BoxD D L, sys.siteCheckOp u) = sys.H0 := by
  unfold IndexedCommutingProjectorHamiltonian.siteCheckOp IndexedCommutingProjectorHamiltonian.H0
  exact sum_fiberwise_univ_eq Finset.univ (fun i : ι => anchorOfRegion (sys.support i))
    (fun i : ι => (sys.weight i : ℂ) • sys.checkProj i)

/-- **Site-Anchored Perturbation Partition of Unity (`sum_sitePerturbationOp_eq_V_tot`)**:
    For any `QuasiLocalPerturbation D L Site`, summing `sitePerturbationOp V u` over all sites
    $u \in \mathrm{BoxD}\ D\ L$ equals `V.totalPerturbation`. -/
theorem sum_sitePerturbationOp_eq_V_tot {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) :
    (∑ u : BoxD D L, sitePerturbationOp V u) = V.totalPerturbation := by
  unfold sitePerturbationOp QuasiLocalPerturbation.totalPerturbation
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact sum_fiberwise_univ_eq (boxCubes D L q) (anchorOfCube q) (V.term q)

/-- Every `sys.siteCheckOp u` of an `IndexedCommutingProjectorHamiltonian` is self-adjoint. -/
theorem IndexedCommutingProjectorHamiltonian.isSelfAdjoint_siteCheckOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    IsSelfAdjoint (sys.siteCheckOp u) := by
  unfold IndexedCommutingProjectorHamiltonian.siteCheckOp
  refine isSelfAdjoint_finset_sum _ _ fun i _ => ?_
  exact isSelfAdjoint_real_smul (sys.weight i) (sys.is_projector i).isSelfAdjoint

/-- Every `sitePerturbationOp V u` is self-adjoint. -/
theorem isSelfAdjoint_sitePerturbationOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (u : BoxD D L) :
    IsSelfAdjoint (sitePerturbationOp V u) := by
  unfold sitePerturbationOp
  refine isSelfAdjoint_finset_sum _ _ fun q _ =>
    isSelfAdjoint_finset_sum _ _ fun A _ => V.is_selfAdjoint q A

/-- Every `sys.siteCheckOp u` is annihilated on both sides by `sys.P0`, and lies purely in the
    excited block: $(1 - P_0) \, \mathrm{sys.siteCheckOp}(u) \, (1 - P_0) = \mathrm{sys.siteCheckOp}(u)$. -/
theorem IndexedCommutingProjectorHamiltonian.siteCheckOp_mul_P0_and_exc {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (u : BoxD D L) :
    sys.siteCheckOp u * sys.P0 = 0 ∧
    sys.P0 * sys.siteCheckOp u = 0 ∧
    (1 - sys.P0) * sys.siteCheckOp u * (1 - sys.P0) = sys.siteCheckOp u := by
  have hR : sys.siteCheckOp u * sys.P0 = 0 := by
    unfold IndexedCommutingProjectorHamiltonian.siteCheckOp
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_mul_assoc, sys.checkProj_mul_P0_eq_zero i]
    ext x; simp
  have hL : sys.P0 * sys.siteCheckOp u = 0 := by
    simpa using eq_zero_of_mul_eq_zero_of_isSelfAdjoint_bhm
      sys.isStarProjection_P0.isSelfAdjoint (sys.isSelfAdjoint_siteCheckOp u) 0 (by simpa using hR)
  refine ⟨hR, hL, ?_⟩
  calc (1 - sys.P0) * sys.siteCheckOp u * (1 - sys.P0)
    _ = (sys.siteCheckOp u - sys.P0 * sys.siteCheckOp u) * (1 - sys.P0) := by rw [sub_mul, one_mul]
    _ = sys.siteCheckOp u * (1 - sys.P0) := by rw [hL, sub_zero]
    _ = sys.siteCheckOp u - sys.siteCheckOp u * sys.P0 := by rw [mul_sub, mul_one]
    _ = sys.siteCheckOp u := by rw [hR, sub_zero]

/-!
## 3. Bridge Between `indexedFilteredSiteOp` and `bochnerFilteredSiteOp`
-/

/-- If `H` is self-adjoint, then `U.1† * H * U.1` is self-adjoint. -/
lemma isSelfAdjoint_unitary_adj_conj {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (U : unitary (E →L[ℂ] E)) {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) :
    IsSelfAdjoint ((U.1†) * H * U.1) := by
  rw [isSelfAdjoint_iff]
  change star (star U.1 * H * U.1) = star U.1 * H * U.1
  rw [star_mul, star_mul, star_star, hH.star_eq, mul_assoc]

/-- Definitional bridge: `indexedFilteredSiteOp sys V U w u` is `bochnerFilteredSiteOp` applied to
    `sitePerturbationOp V u` and `sys.siteCheckOp u`. -/
lemma indexedFilteredSiteOp_eq_bochnerFilteredSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (w : ℝ → ℂ) (u : BoxD D L) :
    indexedFilteredSiteOp sys V U w u =
      bochnerFilteredSiteOp (U.1† * (sys.H0 + V.totalPerturbation) * U.1) U.1 w
        (sitePerturbationOp V u) (sys.siteCheckOp u) := rfl

/-- **Self-Adjointness of `indexedFilteredSiteOp` (`isSelfAdjoint_indexedFilteredSiteOp`)**:
    For any real-valued filter kernel $w$ (`∀ t, star (w t) = w t`), `indexedFilteredSiteOp sys V U w u`
    is self-adjoint. -/
theorem isSelfAdjoint_indexedFilteredSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw : ∀ t : ℝ, star (w t) = w t) (u : BoxD D L) :
    IsSelfAdjoint (indexedFilteredSiteOp sys V U w u) := by
  rw [indexedFilteredSiteOp_eq_bochnerFilteredSiteOp]
  have hH' : IsSelfAdjoint (U.1† * (sys.H0 + V.totalPerturbation) * U.1) :=
    isSelfAdjoint_unitary_adj_conj U (sys.isSelfAdjoint_H0.add V.isSelfAdjoint_totalPerturbation)
  exact isSelfAdjoint_bochnerFilteredSiteOp hH'
    (isSelfAdjoint_sitePerturbationOp V u) (sys.isSelfAdjoint_siteCheckOp u) hw

/-- Specialization of `isSelfAdjoint_indexedFilteredSiteOp` to `bhFilterWeight`. -/
theorem isSelfAdjoint_indexedFilteredSiteOp_w_BH11 {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (u : BoxD D L) :
    IsSelfAdjoint (indexedFilteredSiteOp sys V U bhFilterWeight u) :=
  isSelfAdjoint_indexedFilteredSiteOp sys V U star_w_BH11 u

/-- Operator-norm bound for `indexedFilteredSiteOp sys V U w_BH11 u`:
    $\|\mathrm{indexedFilteredSiteOp}\ \mathrm{sys}\ V\ U\ w_{\mathrm{BH11}}\ u\|
      \le \|\mathrm{sitePerturbationOp}\ V\ u\| + 2 \|\mathrm{sys.siteCheckOp}\ u\|$. -/
theorem norm_indexedFilteredSiteOp_w_BH11_le {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (u : BoxD D L) :
    ‖indexedFilteredSiteOp sys V U bhFilterWeight u‖ ≤
      ‖sitePerturbationOp V u‖ + 2 * ‖sys.siteCheckOp u‖ := by
  let H' := U.1† * (sys.H0 + V.totalPerturbation) * U.1
  have hH' : IsSelfAdjoint H' :=
    isSelfAdjoint_unitary_adj_conj U (sys.isSelfAdjoint_H0.add V.isSelfAdjoint_totalPerturbation)
  have hU_norm : ‖U.1‖ ≤ 1 := (unitary_opNorm_le_one U).1
  have hU_adj_norm : ‖U.1†‖ ≤ 1 := (unitary_opNorm_le_one U).2
  have h1 : ‖bochnerFilteredOp H' bhFilterWeight (U.1† * sitePerturbationOp V u * U.1)‖ ≤
      ‖sitePerturbationOp V u‖ :=
    le_trans (norm_bochnerFilteredOp_w_BH11_le hH' _)
      (norm_sandwich_le_of_norm_le_one hU_adj_norm hU_norm)
  have h2 : ‖bochnerFilteredOp H' bhFilterWeight (U.1† * sys.siteCheckOp u * U.1) - sys.siteCheckOp u‖ ≤
      2 * ‖sys.siteCheckOp u‖ := by
    have h2a : ‖bochnerFilteredOp H' bhFilterWeight (U.1† * sys.siteCheckOp u * U.1)‖ ≤
        ‖sys.siteCheckOp u‖ :=
      le_trans (norm_bochnerFilteredOp_w_BH11_le hH' _)
        (norm_sandwich_le_of_norm_le_one hU_adj_norm hU_norm)
    calc ‖bochnerFilteredOp H' bhFilterWeight (U.1† * sys.siteCheckOp u * U.1) - sys.siteCheckOp u‖
      _ ≤ ‖bochnerFilteredOp H' bhFilterWeight (U.1† * sys.siteCheckOp u * U.1)‖ + ‖sys.siteCheckOp u‖ :=
        norm_sub_le _ _
      _ ≤ ‖sys.siteCheckOp u‖ + ‖sys.siteCheckOp u‖ := add_le_add h2a le_rfl
      _ = 2 * ‖sys.siteCheckOp u‖ := by ring
  unfold indexedFilteredSiteOp
  exact le_trans (norm_add_le _ _) (add_le_add h1 h2)

/-- **BH11 Lemma 7 (`rewrite1`) Global Energy Decomposition for `indexedFilteredSiteOp`
    (`sum_indexedFilteredSiteOp_eq_conj_sub_H0`)**:
    For any unitary $U$ and any filter kernel $w$ with $\int_{-\infty}^\infty w(t)\, dt = 1$
    such that `w t • heisenbergFlow H' t X` is integrable for all $X$,
    $$\sum_{u \in \mathrm{BoxD}\ D\ L} \mathrm{indexedFilteredSiteOp}\ \mathrm{sys}\ V\ U\ w\ u
      = U^\dagger (H_0 + V_{\mathrm{tot}}) U - H_0.$$ -/
theorem sum_indexedFilteredSiteOp_eq_conj_sub_H0 {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {w : ℝ → ℂ} (hw_one : (∫ t : ℝ, w t) = 1)
    (hint : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Integrable (fun t : ℝ => w t • heisenbergFlow (U.1† * (sys.H0 + V.totalPerturbation) * U.1) t X)) :
    (∑ u : BoxD D L, indexedFilteredSiteOp sys V U w u) =
      U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 ∧
    sys.H0 + (∑ u : BoxD D L, indexedFilteredSiteOp sys V U w u) =
      U.1† * (sys.H0 + V.totalPerturbation) * U.1 := by
  simp_rw [indexedFilteredSiteOp_eq_bochnerFilteredSiteOp]
  exact sum_bochnerFilteredSiteOp_eq_H'_sub_H0
    sys.H0 V.totalPerturbation (U.1† * (sys.H0 + V.totalPerturbation) * U.1) U.1 w
    (sitePerturbationOp V) sys.siteCheckOp
    (sum_sitePerturbationOp_eq_V_tot V)
    sys.sum_siteCheckOp_eq_H0 rfl hw_one hint

/-- Specialization of `sum_indexedFilteredSiteOp_eq_conj_sub_H0` to `bhFilterWeight`. -/
theorem sum_indexedFilteredSiteOp_w_BH11_eq_conj_sub_H0 {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    (∑ u : BoxD D L, indexedFilteredSiteOp sys V U bhFilterWeight u) =
      U.1† * (sys.H0 + V.totalPerturbation) * U.1 - sys.H0 ∧
    sys.H0 + (∑ u : BoxD D L, indexedFilteredSiteOp sys V U bhFilterWeight u) =
      U.1† * (sys.H0 + V.totalPerturbation) * U.1 :=
  sum_indexedFilteredSiteOp_eq_conj_sub_H0 sys V U integral_w_BH11_eq_one
    (integrable_w_BH11_smul_heisenbergFlow _)

/-- Off-diagonal conditional-expectation tail bound for `indexedFilteredSiteOp sys V U w u` when
    $\mathrm{sys.siteCheckOp}\ u$ is supported on $A_0$. -/
theorem norm_offDiag_indexedFilteredSiteOp_sub_condExp_le {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (U : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (w : ℝ → ℂ) (u : BoxD D L) (A0 : Finset (BoxD D L))
    {ε_V ε_Q : ℝ}
    (hQ_supp : IsSupportedOn Site A0 (sys.siteCheckOp u))
    (hV_tail :
      let FV_off := (1 - sys.P0) *
        bochnerFilteredOp (U.1† * (sys.H0 + V.totalPerturbation) * U.1) w
          (U.1† * sitePerturbationOp V u * U.1) * (1 - sys.P0)
      ‖FV_off - condExp Site A0 FV_off‖ ≤ ε_V)
    (hQ_tail :
      let FQ_off := (1 - sys.P0) *
        bochnerFilteredOp (U.1† * (sys.H0 + V.totalPerturbation) * U.1) w
          (U.1† * sys.siteCheckOp u * U.1) * (1 - sys.P0)
      ‖FQ_off - condExp Site A0 FQ_off‖ ≤ ε_Q) :
    let X_u := indexedFilteredSiteOp sys V U w u
    let O_off := (1 - sys.P0) * X_u * (1 - sys.P0)
    ‖O_off - condExp Site A0 O_off‖ ≤ ε_V + ε_Q := by
  rw [indexedFilteredSiteOp_eq_bochnerFilteredSiteOp]
  exact norm_offDiag_bochnerFilteredSiteOp_sub_condExp_le
    sys.P0 (U.1† * (sys.H0 + V.totalPerturbation) * U.1) U.1 w
    (sitePerturbationOp V u) (sys.siteCheckOp u) A0
    (sys.siteCheckOp_mul_P0_and_exc u).2.2 hQ_supp hV_tail hQ_tail

end
