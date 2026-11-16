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

import Proofs.BandLimitedFilter.BandLimitedFilterSynthesis
import Proofs.QuasiLocalDressing.KatoFlowUnitaryCondExpTails

noncomputable section

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap MeasureTheory

/-!
# Unfiltered Multi-Scale Quasi-Local Flow Witnesses and Two-Block Projections

Defines the quasi-local flow witness structures `BH11UnfilteredQuasiLocalFlowWitness`, `BH11UnfilteredMultiScaleFlowWitness`, `BH11SectorUnfilteredMultiScaleFlowWitness`, and the two-block projected `BH11TwoBlockMultiScaleFlowWitness` (`BH11UnfilteredMultiScaleFlowWitness.toTwoBlock`), proving exact ground-space commutation (`BH11TwoBlockMultiScaleFlowWitness.commute_siteOp_P0`) and global energy decomposition (`BH11TwoBlockMultiScaleFlowWitness.sum_siteOp_eq_conj_sub_H0`).

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 6.2 (`subsec:bochner-lr`), Proposition 6.3 (`prop:bochner-time-convolution`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Bravyi and Hastings (2011), Commun. Math. Phys. 307, 609–627
-/

/-!
## 1. Single-Scale and Multi-Scale Quasi-Local Flow Witnesses
-/

/-- The product of a list of pairwise-commuting star projections is a star projection. -/
private lemma isStarProjection_list_prod_dressing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (l : List (E →L[ℂ] E))
    (hl_proj : ∀ p ∈ l, IsStarProjection p) (hl_comm : l.Pairwise Commute) :
    IsStarProjection l.prod := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact ⟨IsIdempotentElem.one, IsSelfAdjoint.one (E →L[ℂ] E)⟩
  | cons p tail ih =>
    rw [List.prod_cons]
    rcases List.pairwise_cons.mp hl_comm with ⟨h_p_comm, h_tail_comm⟩
    exact (hl_proj p List.mem_cons_self).mul
      (ih (fun q hq => hl_proj q (List.mem_cons_of_mem p hq)) h_tail_comm)
      (Commute.list_prod_right tail p h_p_comm)

/-- Global ground projector `sys.P0` is a star projection for any
    `IndexedCommutingProjectorHamiltonian`. -/
lemma IndexedCommutingProjectorHamiltonian.isStarProjection_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    IsStarProjection sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj]
  apply isStarProjection_list_prod_dressing
  · intro p hp
    rcases List.mem_map.mp hp with ⟨i, _, rfl⟩
    exact (sys.is_projector i).one_sub
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (Finset.univ : Finset ι).nodup_toList
    intro i j _ _ _
    exact (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (sys.pairwise_commute i j))

/-- Unperturbed Hamiltonian `sys.H0` commutes with `sys.P0` for any
    `IndexedCommutingProjectorHamiltonian`. -/
lemma IndexedCommutingProjectorHamiltonian.commute_H0_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    Commute sys.H0 sys.P0 := by
  dsimp [IndexedCommutingProjectorHamiltonian.H0,
    IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj]
  apply Commute.sum_left
  intro i _
  apply commute_smul_left_clm _ (sys.weight i : ℂ)
  apply Commute.list_prod_right
  intro p hp
  rcases List.mem_map.mp hp with ⟨j, _, rfl⟩
  exact (Commute.one_right _).sub_right (sys.pairwise_commute i j)

/-- **Single-Scale Unfiltered Quasi-Local Flow Witness (`BH11UnfilteredQuasiLocalFlowWitness`)**:
    Packages a dressing unitary `U_dress`, single-scale cube conditional-expectation bounds, and
    direct site ground-projector commutation `h_X_comm_P0`. -/
structure BH11UnfilteredQuasiLocalFlowWitness {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (K r_LR : ℕ) (ε_K_val ε_LR : ℝ) where
  U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  h_comm_P0 : Commute (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) sys.P0
  h_X_comm_P0 : ∀ u : BoxD D L,
    Commute (bochnerFilteredSiteOp (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1)
      U_dress.1 bhFilterWeight (V_u u) (Q_u u)) sys.P0
  h_site_condExp : ∀ u : BoxD D L,
    let X_u := bochnerFilteredSiteOp (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1)
      U_dress.1 bhFilterWeight (V_u u) (Q_u u)
    ‖X_u - condExp Site (boxCube u K) X_u‖ ≤ ε_K_val
  h_1site_condExp : ∀ (v : BoxD D L)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
    IsSupportedOn Site {v} A_v →
    ‖U_dress.1† * A_v * U_dress.1 -
      condExp Site (boxCube v r_LR) (U_dress.1† * A_v * U_dress.1)‖ ≤ ε_LR * ‖A_v‖

/-- **Multi-Scale Unfiltered Quasi-Local Flow Witness (`BH11UnfilteredMultiScaleFlowWitness`)**:
    Packages multi-scale `condExp` tails `‖X_u - condExp Site (boxCube u j) X_u‖ ≤ J * g_tail j`
    together with direct ground-space commutation `h_X_comm_P0`. -/
structure BH11UnfilteredMultiScaleFlowWitness {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (r_0 K r_LR : ℕ) (J ε_LR : ℝ) (g_tail : ℕ → ℝ) where
  U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  h_comm_P0 : Commute (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) sys.P0
  h_X_comm_P0 : ∀ u : BoxD D L,
    Commute (bochnerFilteredSiteOp (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1)
      U_dress.1 bhFilterWeight (V_u u) (Q_u u)) sys.P0
  hg_tail_nonneg : ∀ j ∈ Finset.Icc r_0 K, 0 ≤ g_tail j
  h_site_multiscale_condExp : ∀ (u : BoxD D L), ∀ j ∈ Finset.Icc r_0 K,
    let X_u := bochnerFilteredSiteOp (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1)
      U_dress.1 bhFilterWeight (V_u u) (Q_u u)
    ‖X_u - condExp Site (boxCube u j) X_u‖ ≤ J * g_tail j
  h_1site_condExp : ∀ (v : BoxD D L)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
    IsSupportedOn Site {v} A_v →
    ‖U_dress.1† * A_v * U_dress.1 -
      condExp Site (boxCube v r_LR) (U_dress.1† * A_v * U_dress.1)‖ ≤ ε_LR * ‖A_v‖

/-- Extracts the single-scale `BH11UnfilteredQuasiLocalFlowWitness` at scale `K` from a
    `BH11UnfilteredMultiScaleFlowWitness` whenever `r_0 ≤ K`. -/
def BH11UnfilteredMultiScaleFlowWitness.toUnfilteredQuasiLocalFlowWitness {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {sys : IndexedCommutingProjectorHamiltonian D L Site ι}
    {V : QuasiLocalPerturbation D L Site}
    {V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    {r_0 K r_LR : ℕ} {J ε_LR : ℝ} {g_tail : ℕ → ℝ}
    (W : BH11UnfilteredMultiScaleFlowWitness sys V V_u Q_u r_0 K r_LR J ε_LR g_tail)
    (hrK : r_0 ≤ K) :
    BH11UnfilteredQuasiLocalFlowWitness sys V V_u Q_u K r_LR (J * g_tail K) ε_LR where
  U_dress := W.U_dress
  h_comm_P0 := W.h_comm_P0
  h_X_comm_P0 := W.h_X_comm_P0
  h_site_condExp u := W.h_site_multiscale_condExp u K (Finset.mem_Icc.mpr ⟨hrK, le_refl K⟩)
  h_1site_condExp := W.h_1site_condExp

/-- **Sector-Preserving Multi-Scale Unfiltered Flow Witness
    (`BH11SectorUnfilteredMultiScaleFlowWitness`)**:
    Combines `BH11UnfilteredMultiScaleFlowWitness` with exact sector-symmetry commutation
    `Commute X_u Pi_sec`. -/
structure BH11SectorUnfilteredMultiScaleFlowWitness {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_sec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (r_0 K r_LR : ℕ) (J ε_LR : ℝ) (g_tail : ℕ → ℝ)
    extends BH11UnfilteredMultiScaleFlowWitness sys V V_u Q_u r_0 K r_LR J ε_LR g_tail where
  h_comm_sec : ∀ u : BoxD D L,
    Commute (bochnerFilteredSiteOp (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1)
      U_dress.1 bhFilterWeight (V_u u) (Q_u u)) Pi_sec

/-!
## 2. Two-Block Projected Multi-Scale Flow Witnesses (`BH11TwoBlockMultiScaleFlowWitness`)
-/

/-- **Two-Block Multi-Scale Quasi-Local Flow Witness (`BH11TwoBlockMultiScaleFlowWitness`)**:
    Packages the two-block projected site operators
    `Y_u := twoBlockBochnerFilteredSiteOp sys.P0 H' U_dress.1 w_BH11 (V_u u) (Q_u u)`,
    which satisfy `Commute Y_u sys.P0` unconditionally for all $u$. -/
structure BH11TwoBlockMultiScaleFlowWitness {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (r_0 K r_LR : ℕ) (J ε_LR : ℝ) (g_tail : ℕ → ℝ) where
  U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
  h_comm_P0 : Commute (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1) sys.P0
  hg_tail_nonneg : ∀ j ∈ Finset.Icc r_0 K, 0 ≤ g_tail j
  h_site_multiscale_condExp : ∀ (u : BoxD D L), ∀ j ∈ Finset.Icc r_0 K,
    let Y_u := twoBlockBochnerFilteredSiteOp sys.P0 (U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1)
      U_dress.1 bhFilterWeight (V_u u) (Q_u u)
    ‖Y_u - condExp Site (boxCube u j) Y_u‖ ≤ J * g_tail j
  h_1site_condExp : ∀ (v : BoxD D L)
    (A_v : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
    IsSupportedOn Site {v} A_v →
    ‖U_dress.1† * A_v * U_dress.1 -
      condExp Site (boxCube v r_LR) (U_dress.1† * A_v * U_dress.1)‖ ≤ ε_LR * ‖A_v‖

/-- Automatic ground-space commutation `Commute Y_u sys.P0` for any
    `BH11TwoBlockMultiScaleFlowWitness`. -/
theorem BH11TwoBlockMultiScaleFlowWitness.commute_siteOp_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {sys : IndexedCommutingProjectorHamiltonian D L Site ι}
    {V : QuasiLocalPerturbation D L Site}
    {V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    {r_0 K r_LR : ℕ} {J ε_LR : ℝ} {g_tail : ℕ → ℝ}
    (W : BH11TwoBlockMultiScaleFlowWitness sys V V_u Q_u r_0 K r_LR J ε_LR g_tail)
    (u : BoxD D L) :
    Commute (twoBlockBochnerFilteredSiteOp sys.P0 (W.U_dress.1† * (sys.H0 + V.totalPerturbation) * W.U_dress.1)
      W.U_dress.1 bhFilterWeight (V_u u) (Q_u u)) sys.P0 :=
  commute_twoBlockBochnerFilteredSiteOp sys.isStarProjection_P0.isIdempotentElem.eq _ _ _ _ _

/-- Automatic global sum identity $\sum_u Y_u = U_{\mathrm{dress}}^\dagger (H_0 + V_{\mathrm{tot}}) U_{\mathrm{dress}} - H_0$
    for any `BH11TwoBlockMultiScaleFlowWitness` whenever $\sum_u V_u(u) = V_{\mathrm{tot}}$ and
    $\sum_u Q_u(u) = H_0$. -/
theorem BH11TwoBlockMultiScaleFlowWitness.sum_siteOp_eq_conj_sub_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {sys : IndexedCommutingProjectorHamiltonian D L Site ι}
    {V : QuasiLocalPerturbation D L Site}
    {V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    {r_0 K r_LR : ℕ} {J ε_LR : ℝ} {g_tail : ℕ → ℝ}
    (W : BH11TwoBlockMultiScaleFlowWitness sys V V_u Q_u r_0 K r_LR J ε_LR g_tail)
    (hV_sum : (∑ u : BoxD D L, V_u u) = V.totalPerturbation)
    (hQ_sum : (∑ u : BoxD D L, Q_u u) = sys.H0) :
    (∑ u : BoxD D L,
      twoBlockBochnerFilteredSiteOp sys.P0 (W.U_dress.1† * (sys.H0 + V.totalPerturbation) * W.U_dress.1)
        W.U_dress.1 bhFilterWeight (V_u u) (Q_u u)) =
      W.U_dress.1† * (sys.H0 + V.totalPerturbation) * W.U_dress.1 - sys.H0 :=
  (sum_twoBlockBochnerFilteredSiteOp_w_BH11_eq_H'_sub_H0 V_u Q_u
    sys.isStarProjection_P0.isIdempotentElem.eq W.h_comm_P0 sys.commute_H0_P0
    hV_sum hQ_sum rfl).1

/-- Every `BH11UnfilteredMultiScaleFlowWitness` converts directly into a
    `BH11TwoBlockMultiScaleFlowWitness` with the exact same `g_tail` because
    `twoBlockDiagProj sys.P0 X_u = X_u` when `Commute X_u sys.P0`. -/
def BH11UnfilteredMultiScaleFlowWitness.toTwoBlock {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {sys : IndexedCommutingProjectorHamiltonian D L Site ι}
    {V : QuasiLocalPerturbation D L Site}
    {V_u Q_u : BoxD D L → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    {r_0 K r_LR : ℕ} {J ε_LR : ℝ} {g_tail : ℕ → ℝ}
    (W : BH11UnfilteredMultiScaleFlowWitness sys V V_u Q_u r_0 K r_LR J ε_LR g_tail) :
    BH11TwoBlockMultiScaleFlowWitness sys V V_u Q_u r_0 K r_LR J ε_LR g_tail where
  U_dress := W.U_dress
  h_comm_P0 := W.h_comm_P0
  hg_tail_nonneg := W.hg_tail_nonneg
  h_site_multiscale_condExp u j hj := by
    dsimp [twoBlockBochnerFilteredSiteOp]
    rw [twoBlockDiagProj_eq_self_of_isStarProjection_commute sys.isStarProjection_P0 (W.h_X_comm_P0 u)]
    exact W.h_site_multiscale_condExp u j hj
  h_1site_condExp := W.h_1site_condExp

end
