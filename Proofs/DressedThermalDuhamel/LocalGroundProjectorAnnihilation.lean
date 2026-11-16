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

import Proofs.DressedThermalDuhamel.SyndromePinchedPeierlsBogoliubov

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

noncomputable section

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

/-!
# Local Ground-Projector Annihilation and Ground-Pinched BHM Form Preservation

Proves clean-region local ground projector (`P_loc`) syndrome annihilation and global ground-space (`P0`) commutation for local telescoping differences. Establishes exact unitary-pullback sector Boltzmann identities and two-block `P0`-pinched preservation of the BHM relative form bound.

## References

* Part I, Section 7.1 (`subsec:single-cube-telescoping`), Proposition 7.2 (`prop:single-cube-telescoping`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
-/

/-! ## 1. Clean-Region `localGroundProj` & Syndrome Projector Annihilation and Commutation -/

/-- Every factor `1 - sys.checkProj i` commutes with every bare syndrome projector `sys.syndromeProjector σ`,
so any list product `(l.map (fun i => 1 - sys.checkProj i)).prod` commutes with `sys.syndromeProjector σ`. -/
theorem perturbed_commute_list_prod_one_sub_checkProj_syndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (σ : ι → Bool) (l : List ι) :
    Commute ((l.map (fun i => 1 - sys.checkProj i)).prod) (sys.syndromeProjector σ) := by
  refine Commute.list_prod_left _ _ fun x hx => ?_
  rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
  exact Commute.sub_left (Commute.one_left _)
    ((syndrome_resolution_indexed sys).2.2.2.2.2.2.1 σ i)

/-- Every local ground projector `sys.P_loc B` commutes with every bare syndrome projector
`sys.syndromeProjector σ`. -/
theorem perturbed_commute_P_loc_syndromeProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (B : Finset (BoxD D L)) (σ : ι → Bool) :
    Commute (sys.localGroundProj B) (sys.syndromeProjector σ) := by
  unfold IndexedCommutingProjectorHamiltonian.localGroundProj
  exact perturbed_commute_list_prod_one_sub_checkProj_syndromeProjector sys σ _

/-- If syndrome `σ` has no violated checks supported inside `B`
(`∀ i : ι, sys.support i ⊆ B → σ i = false`), then `sys.P_loc B` acts as the identity on
`sys.syndromeProjector σ` from both left and right. -/
theorem perturbed_P_loc_mul_syndromeProjector_of_clean_region {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {B : Finset (BoxD D L)} {σ : ι → Bool}
    (h_clean : ∀ i : ι, sys.support i ⊆ B → σ i = false) :
    sys.localGroundProj B * sys.syndromeProjector σ = sys.syndromeProjector σ ∧
    sys.syndromeProjector σ * sys.localGroundProj B = sys.syndromeProjector σ := by
  have h_left : sys.localGroundProj B * sys.syndromeProjector σ = sys.syndromeProjector σ := by
    unfold IndexedCommutingProjectorHamiltonian.localGroundProj
    refine perturbed_list_prod_one_sub_checkProj_mul_syndromeProjector sys σ _ fun i hi => ?_
    have hi_f : i ∈ Finset.univ.filter (fun j : ι => sys.support j ⊆ B) :=
      Finset.mem_toList.mp hi
    exact h_clean i (Finset.mem_filter.mp hi_f).2
  refine ⟨h_left, ?_⟩
  rw [← (perturbed_commute_P_loc_syndromeProjector sys B σ).eq, h_left]

/-- If `D_loc` is self-adjoint, annihilated on the right by `sys.P_loc B` (`D_loc * sys.P_loc B = 0`),
and syndrome `σ` has no violated checks supported inside `B`
(`∀ i : ι, sys.support i ⊆ B → σ i = false`), then `D_loc` annihilates `sys.syndromeProjector σ`
on both sides, commutes with `sys.syndromeProjector σ`, and has zero syndrome-diagonal block on `σ`. -/
theorem perturbed_local_diff_annihilates_and_commutes_syndromeProjector_of_clean_region {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {D_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {B : Finset (BoxD D L)} (hD_sa : IsSelfAdjoint D_loc)
    (hDP : D_loc * sys.localGroundProj B = 0)
    {σ : ι → Bool} (h_clean : ∀ i : ι, sys.support i ⊆ B → σ i = false) :
    D_loc * sys.syndromeProjector σ = 0 ∧
    sys.syndromeProjector σ * D_loc = 0 ∧
    Commute D_loc (sys.syndromeProjector σ) ∧
    sys.syndromeProjector σ * D_loc * sys.syndromeProjector σ = 0 :=
  perturbed_local_diff_mul_syndromeProjector_eq_zero sys hD_sa hDP
    (perturbed_P_loc_mul_syndromeProjector_of_clean_region sys h_clean).1

/-- Any self-adjoint local telescoping difference `D_loc` with `D_loc * sys.P_loc B = 0`
annihilates the bare ground-space projector `sys.P0` on both sides and commutes with `sys.P0`. -/
theorem perturbed_local_diff_annihilates_and_commutes_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {D_loc : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {B : Finset (BoxD D L)} (hD_sa : IsSelfAdjoint D_loc)
    (hDP : D_loc * sys.localGroundProj B = 0) :
    D_loc * sys.P0 = 0 ∧
    sys.P0 * D_loc = 0 ∧
    Commute D_loc sys.P0 ∧
    sys.P0 * D_loc * sys.P0 = 0 := by
  have h_σ0 := perturbed_local_diff_annihilates_and_commutes_syndromeProjector_of_clean_region
    sys hD_sa hDP (σ := fun _ => false) (fun _ _ => rfl)
  rw [(syndrome_resolution_indexed sys).1] at h_σ0
  exact h_σ0

/-- Any finite sum `W_tel = ∑ a ∈ s_idx, D_fam a` of self-adjoint local telescoping differences
satisfying `D_fam a * sys.P_loc (B a) = 0` annihilates `sys.P0` on both sides and commutes with
`sys.P0`. -/
theorem perturbed_sum_local_diff_annihilates_and_commutes_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {α_idx : Type*} (s_idx : Finset α_idx)
    (D_fam : α_idx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : α_idx → Finset (BoxD D L))
    (hD_sa : ∀ a ∈ s_idx, IsSelfAdjoint (D_fam a))
    (hDP : ∀ a ∈ s_idx, D_fam a * sys.localGroundProj (B a) = 0) :
    (∑ a ∈ s_idx, D_fam a) * sys.P0 = 0 ∧
    sys.P0 * (∑ a ∈ s_idx, D_fam a) = 0 ∧
    Commute (∑ a ∈ s_idx, D_fam a) sys.P0 ∧
    sys.P0 * (∑ a ∈ s_idx, D_fam a) * sys.P0 = 0 := by
  have h_right : (∑ a ∈ s_idx, D_fam a) * sys.P0 = 0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun a ha =>
      (perturbed_local_diff_annihilates_and_commutes_P0 sys (hD_sa a ha) (hDP a ha)).1
  have h_left : sys.P0 * (∑ a ∈ s_idx, D_fam a) = 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun a ha =>
      (perturbed_local_diff_annihilates_and_commutes_P0 sys (hD_sa a ha) (hDP a ha)).2.1
  have h_comm : Commute (∑ a ∈ s_idx, D_fam a) sys.P0 := by
    rw [commute_iff_eq, h_right, h_left]
  have h_pinch : sys.P0 * (∑ a ∈ s_idx, D_fam a) * sys.P0 = 0 := by
    rw [h_left, zero_mul]
  exact ⟨h_right, h_left, h_comm, h_pinch⟩

/-- If every term `D_fam a` in a finite sum either acts on a clean region for `σ`
(`D_fam a * sys.P_loc (B a) = 0` and `∀ i : ι, sys.support i ⊆ B a → σ i = false`) or commutes
with `sys.syndromeProjector σ`, then the sum commutes with `sys.syndromeProjector σ`. -/
theorem perturbed_sum_local_diff_commutes_syndromeProjector_of_clean_or_commute {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    {α_idx : Type*} (s_idx : Finset α_idx)
    (D_fam : α_idx → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : α_idx → Finset (BoxD D L)) {σ : ι → Bool}
    (hD_sa : ∀ a ∈ s_idx, IsSelfAdjoint (D_fam a))
    (h_term : ∀ a ∈ s_idx,
      (D_fam a * sys.localGroundProj (B a) = 0 ∧ (∀ i : ι, sys.support i ⊆ B a → σ i = false)) ∨
      Commute (D_fam a) (sys.syndromeProjector σ)) :
    Commute (∑ a ∈ s_idx, D_fam a) (sys.syndromeProjector σ) := by
  refine Commute.sum_left s_idx _ _ fun a ha => ?_
  rcases h_term a ha with ⟨hDP, h_clean⟩ | h_comm
  · exact (perturbed_local_diff_annihilates_and_commutes_syndromeProjector_of_clean_region
      sys (hD_sa a ha) hDP h_clean).2.2.1
  · exact h_comm

/-! ## 2. Unconditional Unitary-Conjugated Sector Boltzmann Identity & Telescoping Form Bounds -/

/-- If `E_w.1† * P * E_w.1 = P'`, then `E_w.1 * P' * E_w.1† = P`. -/
theorem perturbed_unitary_conj_symm_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (E_w : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    {P P' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hEw_conj : E_w.1† * P * E_w.1 = P') :
    E_w.1 * P' * E_w.1† = P := by
  have hU_mul : E_w.1 * E_w.1† = 1 := Unitary.coe_mul_star_self E_w
  calc E_w.1 * P' * E_w.1†
    _ = E_w.1 * (E_w.1† * P * E_w.1) * E_w.1† := by rw [hEw_conj]
    _ = (E_w.1 * E_w.1†) * P * (E_w.1 * E_w.1†) := by noncomm_ring
    _ = 1 * P * 1 := by rw [hU_mul]
    _ = P := by simp

/-- **Exact Unitary-Conjugated Sector Boltzmann Identity
(`perturbed_boltzmann_trace_syndromeProjector_eq_unitary_pullback`)**:
For any self-adjoint Hamiltonian `H` (including `H_pull` or `H_tel`, with **no commutation
assumption between `H` and `Π_σ` or `Π_{σ'}`**) and any unitary `E_w` satisfying
`E_w.1† * sys.syndromeProjector σ * E_w.1 = sys.syndromeProjector σ'`, we have the exact identity:
$$\operatorname{Tr}\!\left(e^{-\beta H} \Pi_\sigma\right) =
  \operatorname{Tr}\!\left(e^{-\beta (E_w^\dagger H E_w)} \Pi_{\sigma'}\right).$$ -/
theorem perturbed_boltzmann_trace_syndromeProjector_eq_unitary_pullback {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H)
    {σ σ' : ι → Bool}
    (E_w : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hEw_conj : E_w.1† * sys.syndromeProjector σ * E_w.1 = sys.syndromeProjector σ')
    (β : ℝ) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
      sys.syndromeProjector σ) =
    hilbertTrace (gibbsBoltzmannOp
      (opEigenbasis (E_w.1† * H * E_w.1) (perturbed_isSelfAdjoint_unitary_pullback E_w hH))
      (opEigenvalues (E_w.1† * H * E_w.1) (perturbed_isSelfAdjoint_unitary_pullback E_w hH)) β *
      sys.syndromeProjector σ') := by
  have h_symm := perturbed_unitary_conj_symm_eq E_w hEw_conj
  rw [← h_symm]
  exact (perturbed_hilbertTrace_gibbsBoltzmannOp_unitary_pullback_eq E_w H hH
    (perturbed_isSelfAdjoint_unitary_pullback E_w hH) β (sys.syndromeProjector σ')).symm

/-- **Unconditional Telescoping Unitary Pullback Difference Decomposition
(`perturbed_unitary_conj_telescoping_sub_eq`)**:
If `H_pull = sys.H0 + (c_shift : ℂ) • 1 + W_tel + R_rem`, `W_tel = W_out + W_in`, and
`Commute E_w.1 W_out`, then `W_out` and `(c_shift : ℂ) • 1` cancel identically in
`E_w.1† * H_pull * E_w.1 - H_pull`. -/
theorem perturbed_unitary_conj_telescoping_sub_eq {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (c_shift : ℝ)
    {H_pull W_tel W_out W_in R_rem : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (E_w : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (h_decomp : H_pull = sys.H0 + (c_shift : ℂ) • 1 + W_tel + R_rem)
    (hW_split : W_tel = W_out + W_in)
    (h_comm_Ew : Commute E_w.1 W_out) :
    E_w.1† * H_pull * E_w.1 - H_pull =
      (E_w.1† * sys.H0 * E_w.1 - sys.H0) +
        ((E_w.1† * W_in * E_w.1 - W_in) + (E_w.1† * R_rem * E_w.1 - R_rem)) := by
  have hU_star : E_w.1† * E_w.1 = 1 := Unitary.coe_star_mul_self E_w
  have h_Wout_conj : E_w.1† * W_out * E_w.1 = W_out := by
    rw [mul_assoc, h_comm_Ew.symm.eq, ← mul_assoc, hU_star, one_mul]
  have h_one_conj :
      E_w.1† * ((c_shift : ℂ) • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) *
        E_w.1 = (c_shift : ℂ) • 1 := by
    rw [mul_smul_comm, smul_mul_assoc, mul_one, hU_star]
  rw [h_decomp, hW_split]
  calc E_w.1† * (sys.H0 + (c_shift : ℂ) • 1 + (W_out + W_in) + R_rem) * E_w.1 -
        (sys.H0 + (c_shift : ℂ) • 1 + (W_out + W_in) + R_rem)
    _ = (E_w.1† * sys.H0 * E_w.1 - sys.H0) +
        (E_w.1† * ((c_shift : ℂ) • 1) * E_w.1 - (c_shift : ℂ) • 1) +
        (E_w.1† * W_out * E_w.1 - W_out) +
        ((E_w.1† * W_in * E_w.1 - W_in) + (E_w.1† * R_rem * E_w.1 - R_rem)) := by
      noncomm_ring
    _ = (E_w.1† * sys.H0 * E_w.1 - sys.H0) +
        ((E_w.1† * W_in * E_w.1 - W_in) + (E_w.1† * R_rem * E_w.1 - R_rem)) := by
      rw [h_one_conj, h_Wout_conj, sub_self, sub_self, add_zero, add_zero]

/-! ## 3. Two-Block Ground-Space Diagonal Projection Bridges & Turnkey Unpinched Discharger -/

/-- `perturbed_safePinchedOp sys.P0 sys.H0 = sys.H0` since `Commute sys.H0 sys.P0`. -/
theorem perturbed_safePinchedOp_P0_H0_eq_H0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    perturbedSafePinchedOp sys.P0 sys.H0 = sys.H0 := by
  have hP0 : IsStarProjection sys.P0 := by
    rw [← (syndrome_resolution_indexed sys).1]
    exact (syndrome_resolution_indexed sys).2.1 (fun _ => false)
  have h_comm0 : Commute sys.H0 sys.P0 := by
    rw [← (syndrome_resolution_indexed sys).1]
    exact (syndrome_resolution_indexed sys).2.2.2.2.2.2.2 (fun _ => false)
  exact perturbed_safePinchedOp_eq_self_of_commute hP0 h_comm0

/-- Projecting any self-adjoint operator `H'` onto its two-block ground-space diagonal part
`perturbed_safePinchedOp sys.P0 H'` produces a self-adjoint operator that **commutes with `sys.P0`**
and satisfies the **exact same BHM relative form bound against `sys.H0`** with the exact same
constants `γ` and `δ_split / 2`. -/
theorem perturbed_bhm_form_bound_safePinchedOp_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH' : IsSelfAdjoint H')
    {c_shift γ δ_split : ℝ}
    (h_form : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ ((H' - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
        γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) :
    IsSelfAdjoint (perturbedSafePinchedOp sys.P0 H') ∧
    Commute (perturbedSafePinchedOp sys.P0 H') sys.P0 ∧
    (∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((perturbedSafePinchedOp sys.P0 H' - sys.H0 - (c_shift : ℂ) • 1) ψ))| ≤
        γ * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) := by
  have hP0 : IsStarProjection sys.P0 := by
    rw [← (syndrome_resolution_indexed sys).1]
    exact (syndrome_resolution_indexed sys).2.1 (fun _ => false)
  have h_comm0 : Commute sys.H0 sys.P0 := by
    rw [← (syndrome_resolution_indexed sys).1]
    exact (syndrome_resolution_indexed sys).2.2.2.2.2.2.2 (fun _ => false)
  refine ⟨perturbed_isSelfAdjoint_safePinchedOp hP0 hH',
    perturbed_commute_safePinchedOp_proj hP0 H', fun ψ => ?_⟩
  exact perturbed_bhm_form_bound_safePinchedOp sys H' sys.P0 hP0 h_comm0 h_form ψ

/-- If `sys.P0 * H' * sys.P0 = (E0 : ℂ) • sys.P0`, then the two-block diagonalized operator
`perturbed_safePinchedOp sys.P0 H'` has exact ground-space eigenvalue `E0`:
`perturbed_safePinchedOp sys.P0 H' * sys.P0 = (E0 : ℂ) • sys.P0` and
`sys.P0 * perturbed_safePinchedOp sys.P0 H' = (E0 : ℂ) • sys.P0`. -/
theorem perturbed_safePinchedOp_P0_ground_eigenvalue {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H' : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {E0 : ℝ} (h_P0_H'_P0 : sys.P0 * H' * sys.P0 = (E0 : ℂ) • sys.P0) :
    perturbedSafePinchedOp sys.P0 H' * sys.P0 = (E0 : ℂ) • sys.P0 ∧
    sys.P0 * perturbedSafePinchedOp sys.P0 H' = (E0 : ℂ) • sys.P0 := by
  have hP0 : IsStarProjection sys.P0 := by
    rw [← (syndrome_resolution_indexed sys).1]
    exact (syndrome_resolution_indexed sys).2.1 (fun _ => false)
  have hP0_idem : sys.P0 * sys.P0 = sys.P0 := hP0.isIdempotentElem.eq
  have h_right : perturbedSafePinchedOp sys.P0 H' * sys.P0 = (E0 : ℂ) • sys.P0 := by
    calc perturbedSafePinchedOp sys.P0 H' * sys.P0
      _ = (sys.P0 * H' * sys.P0) * sys.P0 +
          (1 - sys.P0) * H' * (sys.P0 - sys.P0 * sys.P0) := by
        unfold perturbedSafePinchedOp
        noncomm_ring
      _ = (E0 : ℂ) • (sys.P0 * sys.P0) +
          (1 - sys.P0) * H' * (sys.P0 - sys.P0 * sys.P0) := by
        rw [h_P0_H'_P0, smul_mul_assoc]
      _ = (E0 : ℂ) • sys.P0 := by
        rw [hP0_idem, sub_self, mul_zero, add_zero]
  refine ⟨h_right, ?_⟩
  rw [← (perturbed_commute_safePinchedOp_proj hP0 H').eq, h_right]

end
