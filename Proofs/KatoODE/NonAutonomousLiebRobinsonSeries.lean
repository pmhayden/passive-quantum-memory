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

import Proofs.KatoHastingsFlow.KatoHastingsODEFlow
import Proofs.KatoHastingsFlow.InterpolatedHamiltonianBochnerTails
import Proofs.LiebRobinson.BochnerQuasiLocality
import Proofs.LiebRobinson.LiebRobinsonSeries

/-!
# Non-Autonomous Hastings–Koma Lieb–Robinson Series

Establishes the non-autonomous Duhamel–Grönwall induction step and proves the Hastings–Koma Lieb–Robinson commutator bound `non_autonomous_hastings_koma_lieb_robinson_box` and conditional expectation bound `norm_non_autonomous_flow_sub_cond_exp_le_hastings_koma` along time-dependent `IsKatoHastingsFlowSystem` evolutions.

## References

* Part I, Section 6.2 (`subsec:bochner-lr`), Equation (70) (`eq:hastings-koma-lr`), Equation (73) (`eq:unitary-one-site-lr`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Proposition 6.4 (`prop:qac-block-diagonalization`)
* Hastings–Koma (2006), Communications in Mathematical Physics 265, 781–804
-/

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology

noncomputable section
set_option linter.unusedSectionVars false

variable {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]

/-! ## 1. Unitary Conjugation Norm & Commutator Invariance Along `IsKatoHastingsFlowSystem` -/

lemma is_self_adjoint_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (A - B) := hA.sub hB

lemma adjoint_one_eq_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : (1 : E →L[ℂ] E)† = 1 := star_one (E →L[ℂ] E)

lemma norm_mul_mul_adjoint_eq {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hU1 : U† * U = 1) (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖U * X * U†‖ = ‖X‖ := by
  rcases norm_le_one_of_adjoint_mul_self_eq_one hU1 with ⟨hU_le, hU_adj_le⟩
  apply le_antisymm (norm_sandwich_le_of_norm_le_one hU_le hU_adj_le)
  have h_inv : U† * (U * X * U†) * U = X := by
    calc U† * (U * X * U†) * U = (U† * U) * X * (U† * U) := by simp only [mul_assoc]
      _ = X := by rw [hU1, one_mul, mul_one]
  calc ‖X‖ = ‖U† * (U * X * U†) * U‖ := by rw [h_inv]
    _ ≤ ‖U * X * U†‖ := norm_sandwich_le_of_norm_le_one hU_adj_le hU_le

lemma norm_op_commutator_adj_conj_eq {U : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hU1 : U† * U = 1) (hU2 : U * U† = 1)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖opCommutator (U† * A * U) B‖ = ‖opCommutator A (U * B * U†)‖ := by
  rw [← norm_mul_mul_adjoint_eq hU1 (opCommutator (U† * A * U) B), ← opCommutator_conj hU1]
  have hA : U * (U† * A * U) * U† = A := by
    calc U * (U† * A * U) * U† = (U * U†) * A * (U * U†) := by simp only [mul_assoc]
      _ = A := by rw [hU2, one_mul, mul_one]
  rw [hA]

lemma has_deriv_at_forward_conj {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (τ : ℝ) :
    HasDerivAt (fun z => U z * B * (U z)†)
      ((Complex.I : ℂ) • opCommutator (D_gen τ) (U τ * B * (U τ)†)) τ := by
  have hU_adj_deriv := (kato_hastings_ode_abstract P0 D_gen U P hFlow.isSelfAdjoint_D
    hFlow.U_zero hFlow.P_zero hFlow.hasDerivAt_U hFlow.hasDerivAt_P τ).1
  refine (((hFlow.hasDerivAt_U τ).mul (hasDerivAt_const τ B)).mul hU_adj_deriv).congr_deriv ?_
  simp only [Pi.mul_apply, mul_zero, add_zero]; unfold opCommutator
  rw [clm_smul_mul_assoc, clm_smul_mul_assoc, clm_mul_smul_comm, clm_neg_smul, smul_sub]
  simp only [mul_assoc, sub_eq_add_neg]

/-! ## 2. Support-Ball Commutator Supremum `regionCommSup` & Commuting Heisenberg Invariance -/

lemma heisenberg_flow_eq_self_of_op_commutator_eq_zero
    {R O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h_comm : opCommutator R O = 0) (t : ℝ) : heisenbergFlow R t O = O := by
  have hRO : Commute R O := sub_eq_zero.mp h_comm
  have h_exp : timeEvolutionOp R t * O = O * timeEvolutionOp R t :=
    (hRO.smul_left (Complex.I * (t : ℂ))).exp_left.eq
  unfold heisenbergFlow
  rw [h_exp, mul_assoc, (timeEvolutionOp_mul_neg R t).1, mul_one]

lemma norm_op_commutator_heisenberg_flow_right_eq
    {R O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hR_sa : IsSelfAdjoint R) (h_comm : opCommutator R O = 0)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (t : ℝ) :
    ‖opCommutator O (heisenbergFlow R t X)‖ = ‖opCommutator O X‖ := by
  have h_id : heisenbergFlow R t (opCommutator O X) = opCommutator O (heisenbergFlow R t X) := by
    calc heisenbergFlow R t (opCommutator O X)
      _ = heisenbergFlow R t (O * X) - heisenbergFlow R t (X * O) := by
        unfold heisenbergFlow opCommutator; rw [mul_sub, sub_mul]
      _ = opCommutator O (heisenbergFlow R t X) := by
        rw [heisenbergFlow_mul, heisenbergFlow_mul,
          heisenberg_flow_eq_self_of_op_commutator_eq_zero h_comm t]; rfl
  rw [← h_id, norm_heisenbergFlow_eq hR_sa t]

def regionCommSup (Z : Finset (BoxD D L))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : ℝ :=
  sSup ((fun O => ‖opCommutator O X‖) '' {O | IsSupportedOn Site Z O ∧ ‖O‖ ≤ 1})

lemma bdd_above_region_comm_set (Z : Finset (BoxD D L))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    BddAbove ((fun O => ‖opCommutator O X‖) '' {O | IsSupportedOn Site Z O ∧ ‖O‖ ≤ 1}) := by
  refine ⟨2 * ‖X‖, ?_⟩; rintro _ ⟨O, ⟨_, hO1⟩, rfl⟩
  calc ‖opCommutator O X‖ ≤ 2 * ‖O‖ * ‖X‖ := norm_opCommutator_le O X
    _ ≤ 2 * 1 * ‖X‖ := by gcongr
    _ = 2 * ‖X‖ := by ring

lemma nonempty_region_comm_set (Z : Finset (BoxD D L))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ((fun O => ‖opCommutator O X‖) '' {O | IsSupportedOn Site Z O ∧ ‖O‖ ≤ 1}).Nonempty :=
  ⟨0, 0, ⟨_root_.isSupportedOn_zero Z, by simp⟩, by simp [opCommutator]⟩

lemma region_comm_sup_nonneg (Z : Finset (BoxD D L))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) : 0 ≤ regionCommSup Z X :=
  le_csSup (bdd_above_region_comm_set Z X) ⟨0, ⟨_root_.isSupportedOn_zero Z, by simp⟩, by simp [opCommutator]⟩

lemma le_region_comm_sup {Z : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site Z O) (h1 : ‖O‖ ≤ 1)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖opCommutator O X‖ ≤ regionCommSup Z X :=
  le_csSup (bdd_above_region_comm_set Z X) ⟨O, ⟨hO, h1⟩, rfl⟩

lemma region_comm_sup_le (Z : Finset (BoxD D L))
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {C : ℝ} (h : ∀ O, IsSupportedOn Site Z O → ‖O‖ ≤ 1 → ‖opCommutator O X‖ ≤ C) :
    regionCommSup Z X ≤ C := by
  refine csSup_le (nonempty_region_comm_set Z X) ?_; rintro _ ⟨O, ⟨hO, h1⟩, rfl⟩; exact h O hO h1

lemma norm_op_commutator_le_mul_region_comm_sup {Z : Finset (BoxD D L)}
    {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site Z O) {M : ℝ} (hM_nn : 0 ≤ M) (hM : ‖O‖ ≤ M)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖opCommutator O X‖ ≤ M * regionCommSup Z X := by
  by_cases hO0 : ‖O‖ = 0
  · have h_comm0 : ‖opCommutator O X‖ = 0 := le_antisymm
      (by calc ‖opCommutator O X‖ ≤ 2 * ‖O‖ * ‖X‖ := norm_opCommutator_le O X
            _ = 0 := by rw [hO0]; ring) (norm_nonneg _)
    rw [h_comm0]; exact mul_nonneg hM_nn (region_comm_sup_nonneg Z X)
  · have hO_pos : 0 < ‖O‖ := lt_of_le_of_ne (norm_nonneg O) (Ne.symm hO0)
    set O_unit := (‖O‖⁻¹ : ℝ) • O
    have h_supp : IsSupportedOn Site Z O_unit := by
      dsimp [O_unit]; rw [clm_real_smul]; exact isSupportedOn_smul Z _ hO
    have h_norm : ‖O_unit‖ ≤ 1 := by
      dsimp [O_unit]; rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg O)), inv_mul_cancel₀ hO0]
    have h_comm : opCommutator O_unit X = (‖O‖⁻¹ : ℝ) • opCommutator O X := by
      dsimp [O_unit]; unfold opCommutator
      rw [clm_real_smul, clm_real_smul, clm_smul_mul_assoc, clm_mul_smul_comm, ← smul_sub]
    have h_le := le_region_comm_sup h_supp h_norm X
    rw [h_comm, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg O))] at h_le
    have h_mul := mul_le_mul_of_nonneg_left h_le (le_of_lt hO_pos)
    rw [← mul_assoc, mul_inv_cancel₀ hO0, one_mul] at h_mul
    exact le_trans h_mul (mul_le_mul_of_nonneg_right hM (region_comm_sup_nonneg Z X))

lemma region_comm_sup_sub_le (Z : Finset (BoxD D L))
    (X Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    regionCommSup Z X - regionCommSup Z Y ≤ 2 * ‖X - Y‖ := by
  rw [sub_le_iff_le_add']
  refine region_comm_sup_le Z X (fun O hO h1 => ?_)
  have h_split : opCommutator O X = opCommutator O Y + opCommutator O (X - Y) := by
    unfold opCommutator; rw [mul_sub, sub_mul]; abel
  calc ‖opCommutator O X‖ = ‖opCommutator O Y + opCommutator O (X - Y)‖ := by rw [h_split]
    _ ≤ ‖opCommutator O Y‖ + ‖opCommutator O (X - Y)‖ := norm_add_le _ _
    _ ≤ regionCommSup Z Y + 2 * ‖O‖ * ‖X - Y‖ :=
      add_le_add (le_region_comm_sup hO h1 Y) (norm_opCommutator_le O (X - Y))
    _ ≤ regionCommSup Z Y + 2 * 1 * ‖X - Y‖ := by gcongr
    _ = regionCommSup Z Y + 2 * ‖X - Y‖ := by ring

lemma continuous_region_comm_sup (Z : Finset (BoxD D L)) :
    Continuous (regionCommSup (Site := Site) Z) := by
  refine Metric.continuous_iff.mpr (fun X ε hε => ⟨ε / 2, half_pos hε, fun Y hYX => ?_⟩)
  rw [Real.dist_eq, abs_lt]; rw [dist_eq_norm] at hYX
  have h1 := region_comm_sup_sub_le Z Y X; have h2 := region_comm_sup_sub_le Z X Y
  have hYX' : ‖X - Y‖ < ε / 2 := by rwa [norm_sub_rev]
  constructor <;> linarith

/-! ## 3. Non-Autonomous Interaction-Picture Observable `nonAutonomousInteractionOp` -/

def nonAutonomousInteractionOp (H : ℝ → LatticeHamiltonian D L Site)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (Z : Finset (BoxD D L)) (τ z : ℝ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  heisenbergFlow ((H τ).totalHamiltonian - (H τ).regionInteraction Z) (-(z - τ)) (U z * B * (U z)†)

lemma norm_op_commutator_non_autonomous_interaction_op_eq (H : ℝ → LatticeHamiltonian D L Site)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {Z : Finset (BoxD D L)} {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site Z O) (τ z : ℝ) :
    ‖opCommutator O (nonAutonomousInteractionOp H U B Z τ z)‖ =
      ‖opCommutator O (U z * B * (U z)†)‖ :=
  norm_op_commutator_heisenberg_flow_right_eq
    (is_self_adjoint_sub (H τ).isSelfAdjoint_totalHamiltonian ((H τ).isSelfAdjoint_regionInteraction Z))
    ((H τ).opCommutator_H_tot_sub_regionInteraction_eq_zero hO) (U z * B * (U z)†) (-(z - τ))

lemma norm_op_commutator_sub_le_interaction_op (H : ℝ → LatticeHamiltonian D L Site)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {Z : Finset (BoxD D L)} {O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hO : IsSupportedOn Site Z O) (τ z : ℝ) :
    ‖opCommutator O (U z * B * (U z)†)‖ - ‖opCommutator O (U τ * B * (U τ)†)‖ ≤
      2 * ‖O‖ * ‖nonAutonomousInteractionOp H U B Z τ z - nonAutonomousInteractionOp H U B Z τ τ‖ := by
  rw [← norm_op_commutator_non_autonomous_interaction_op_eq H U B hO τ z,
    ← norm_op_commutator_non_autonomous_interaction_op_eq H U B hO τ τ]
  set Xz := nonAutonomousInteractionOp H U B Z τ z
  set Xτ := nonAutonomousInteractionOp H U B Z τ τ
  have h_split : opCommutator O Xz = opCommutator O Xτ + opCommutator O (Xz - Xτ) := by
    unfold opCommutator; rw [mul_sub, sub_mul]; abel
  calc ‖opCommutator O Xz‖ - ‖opCommutator O Xτ‖
    _ ≤ (‖opCommutator O Xτ‖ + ‖opCommutator O (Xz - Xτ)‖) - ‖opCommutator O Xτ‖ := by
      rw [h_split]; exact sub_le_sub_right (norm_add_le _ _) _
    _ = ‖opCommutator O (Xz - Xτ)‖ := add_sub_cancel_left _ _
    _ ≤ 2 * ‖O‖ * ‖Xz - Xτ‖ := norm_opCommutator_le O (Xz - Xτ)

lemma region_comm_sup_sub_le_interaction_op (H : ℝ → LatticeHamiltonian D L Site)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (Z : Finset (BoxD D L)) (τ z : ℝ) :
    regionCommSup Z (U z * B * (U z)†) - regionCommSup Z (U τ * B * (U τ)†) ≤
      2 * ‖nonAutonomousInteractionOp H U B Z τ z - nonAutonomousInteractionOp H U B Z τ τ‖ := by
  have h_eq : ∀ u : ℝ,
      regionCommSup Z (U u * B * (U u)†) = regionCommSup Z (nonAutonomousInteractionOp H U B Z τ u) := by
    intro u; unfold regionCommSup; congr 1; ext y; simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨O, ⟨hO, h1⟩, hy⟩ => ⟨O, ⟨hO, h1⟩,
        (norm_op_commutator_non_autonomous_interaction_op_eq H U B hO τ u).trans hy⟩,
      fun ⟨O, ⟨hO, h1⟩, hy⟩ => ⟨O, ⟨hO, h1⟩,
        (norm_op_commutator_non_autonomous_interaction_op_eq H U B hO τ u).symm.trans hy⟩⟩
  rw [h_eq z, h_eq τ]; exact region_comm_sup_sub_le Z _ _

lemma has_deriv_at_non_autonomous_interaction_op
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P) (H : ℝ → LatticeHamiltonian D L Site)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (Z : Finset (BoxD D L)) {τ : ℝ} (hD_τ : D_gen τ = (H τ).totalHamiltonian) :
    HasDerivAt (nonAutonomousInteractionOp H U B Z τ)
      ((Complex.I : ℂ) • opCommutator ((H τ).regionInteraction Z) (U τ * B * (U τ)†)) τ := by
  set R := (H τ).totalHamiltonian - (H τ).regionInteraction Z; set Bτ := U τ * B * (U τ)†
  have hshift : HasDerivAt (fun z : ℝ => z - τ) 1 τ := by simpa using (hasDerivAt_id τ).sub_const τ
  have d1 : HasDerivAt (fun z : ℝ => timeEvolutionOp R (-(z - τ)))
      ((Complex.I * ((-1 : ℝ) : ℂ)) • R) τ := by
    have hcomp := HasDerivAt.scomp_of_eq τ (hasDerivAt_timeEvolutionOp_zero R (-1)) hshift (sub_self τ).symm
    refine (hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))).congr_deriv (one_smul _ _)
    simp only [Function.comp_apply, neg_one_mul]
  have d3 : HasDerivAt (fun z : ℝ => timeEvolutionOp R (- -(z - τ)))
      ((Complex.I * ((1 : ℝ) : ℂ)) • R) τ := by
    have hcomp := HasDerivAt.scomp_of_eq τ (hasDerivAt_timeEvolutionOp_zero R 1) hshift (sub_self τ).symm
    refine (hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))).congr_deriv (one_smul _ _)
    simp only [Function.comp_apply, neg_neg, one_mul]
  have d123 : HasDerivAt (nonAutonomousInteractionOp H U B Z τ) _ τ :=
    (d1.mul (has_deriv_at_forward_conj hFlow B τ)).mul d3
  refine d123.congr_deriv ?_
  simp only [Pi.mul_apply, sub_self, neg_zero, timeEvolutionOp_zero, one_mul, mul_one]
  rw [hD_τ]; unfold opCommutator; dsimp only [R, Bτ]
  simp only [clm_smul_mul_assoc, clm_mul_smul_comm, sub_mul, mul_sub, smul_sub]
  push_cast; rw [mul_neg, mul_one, clm_neg_smul, clm_neg_smul]; abel

lemma norm_deriv_non_autonomous_interaction_op_le (H : ℝ → LatticeHamiltonian D L Site)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (Z : Finset (BoxD D L)) {M : Finset (BoxD D L) → ℝ}
    (hM_nn : ∀ W, 0 ≤ M W) {τ : ℝ} (h_norm : ∀ W, ‖(H τ).h W‖ ≤ M W) :
    ‖(Complex.I : ℂ) • opCommutator ((H τ).regionInteraction Z) (U τ * B * (U τ)†)‖ ≤
      ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
        M W * regionCommSup W (U τ * B * (U τ)†) := by
  rw [norm_smul, Complex.norm_I, one_mul]
  have hsum : opCommutator ((H τ).regionInteraction Z) (U τ * B * (U τ)†) =
      ∑ W ∈ Finset.univ.filter (fun W : Finset (BoxD D L) => (W ∩ Z).Nonempty),
        opCommutator ((H τ).h W) (U τ * B * (U τ)†) := by
    unfold LatticeHamiltonian.regionInteraction opCommutator
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsum]; refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun W _ => ?_))
  exact norm_op_commutator_le_mul_region_comm_sup ((H τ).is_supported W) (hM_nn W) (h_norm W) _

/-! ## 4. Non-Autonomous Hastings–Koma Grönwall Recurrence & Lieb–Robinson Series Bound -/

def nonAutonomousSiteCommSum (M : Finset (BoxD D L) → ℝ)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (x : BoxD D L) (τ : ℝ) : ℝ :=
  ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
    M Z * regionCommSup Z (U τ * B * (U τ)†)

def nonAutonomousSiteQuotient (M : Finset (BoxD D L) → ℝ) (Y : Finset (BoxD D L)) (η : ℝ)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (x : BoxD D L) (τ : ℝ) : ℝ :=
  (weightY Y η x)⁻¹ * nonAutonomousSiteCommSum M U B x τ

def nonAutonomousMaxQuotient [NeZero D] [NeZero L]
    (M : Finset (BoxD D L) → ℝ) (Y : Finset (BoxD D L)) (η : ℝ)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (τ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun x => nonAutonomousSiteQuotient M Y η U B x τ)

lemma non_autonomous_site_comm_sum_nonneg {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (x : BoxD D L) (τ : ℝ) :
    0 ≤ nonAutonomousSiteCommSum M U B x τ :=
  Finset.sum_nonneg (fun Z _ => mul_nonneg (hM_nn Z) (region_comm_sup_nonneg Z _))

lemma non_autonomous_max_quotient_nonneg [NeZero D] [NeZero L]
    {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z) (Y : Finset (BoxD D L)) (η : ℝ)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (τ : ℝ) :
    0 ≤ nonAutonomousMaxQuotient M Y η U B τ := by
  have x0 : BoxD D L := fun _ => ⟨0, NeZero.pos L⟩
  exact le_trans (mul_nonneg (inv_nonneg.mpr (le_of_lt (weightY_pos Y η x0)))
    (non_autonomous_site_comm_sum_nonneg hM_nn U B x0 τ))
    (Finset.le_sup' (fun x => nonAutonomousSiteQuotient M Y η U B x τ) (Finset.mem_univ x0))

lemma non_autonomous_site_comm_sum_le_mul_max_quotient [NeZero D] [NeZero L]
    (M : Finset (BoxD D L) → ℝ) (Y : Finset (BoxD D L)) (η : ℝ)
    (U : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (x : BoxD D L) (τ : ℝ) :
    nonAutonomousSiteCommSum M U B x τ ≤ weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ := by
  have hw : 0 < weightY Y η x := weightY_pos Y η x
  have hmul := mul_le_mul_of_nonneg_left
    (Finset.le_sup' (fun z => nonAutonomousSiteQuotient M Y η U B z τ) (Finset.mem_univ x)) (le_of_lt hw)
  unfold nonAutonomousSiteQuotient at hmul
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hw), one_mul] at hmul

lemma non_autonomous_site_comm_sum_zero_le [NeZero D] [NeZero L]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z) {Y : Finset (BoxD D L)}
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) {η S1 : ℝ} (hη : 0 ≤ η)
    (h_s1 : ∀ z : BoxD D L, (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => z ∈ Z),
      M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤ S1) (x : BoxD D L) :
    nonAutonomousSiteCommSum M U B x 0 ≤ 2 * ‖B‖ * S1 * weightY Y η x := by
  unfold nonAutonomousSiteCommSum
  have hU0 : U 0 * B * (U 0)† = B := by rw [hFlow.U_zero, adjoint_one_eq_one, one_mul, mul_one]
  rw [hU0]
  have hterm : ∀ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
      M Z * regionCommSup Z B ≤ 2 * ‖B‖ * weightY Y η x *
        (M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by
    intro Z hZ; rw [Finset.mem_filter] at hZ; have hMZ := hM_nn Z
    by_cases hdisj : Disjoint Z Y
    · have h_sup0 : regionCommSup Z B ≤ 0 := region_comm_sup_le Z B (fun O hO _ => by
        rw [opCommutator_eq_zero_of_disjoint hdisj hO hB, norm_zero])
      have hw : 0 ≤ weightY Y η x := le_of_lt (weightY_pos Y η x)
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos hMZ h_sup0) (by positivity)
    · rw [Finset.not_disjoint_iff] at hdisj; rcases hdisj with ⟨y, hyZ, hyY⟩
      have h_sup_le : regionCommSup Z B ≤ 2 * ‖B‖ := region_comm_sup_le Z B (fun O _ h1 => by
        calc ‖opCommutator O B‖ ≤ 2 * ‖O‖ * ‖B‖ := norm_opCommutator_le O B
          _ ≤ 2 * 1 * ‖B‖ := by gcongr
          _ = 2 * ‖B‖ := by ring)
      have hd : (boxRegionDist x Y : ℝ) ≤ (regionDiam Z : ℝ) :=
        Nat.cast_le.mpr (le_trans (regionDist_le_boxDist (Finset.mem_singleton_self x) hyY)
          (boxDist_le_regionDiam hZ.2 hyZ))
      have hcard : (1 : ℝ) ≤ (Z.card : ℝ) := Nat.one_le_cast.mpr (Finset.card_pos.mpr ⟨x, hZ.2⟩)
      have hpos : 0 < (1 + (boxRegionDist x Y : ℝ) / 2) ^ η := Real.rpow_pos_of_pos (by positivity) η
      have hrpow : (1 + (boxRegionDist x Y : ℝ) / 2) ^ η ≤ (1 + (regionDiam Z : ℝ)) ^ η :=
        Real.rpow_le_rpow (by positivity) (by linarith) hη
      have h1 : 1 ≤ weightY Y η x * ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by
        unfold weightY; rw [one_div, le_inv_mul_iff₀ hpos]
        nlinarith [Real.rpow_pos_of_pos (by positivity : 0 < 1 + (regionDiam Z : ℝ)) η]
      calc M Z * regionCommSup Z B ≤ M Z * (2 * ‖B‖) * 1 := by nlinarith
        _ ≤ M Z * (2 * ‖B‖) * (weightY Y η x * ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η)) := by gcongr
        _ = 2 * ‖B‖ * weightY Y η x * (M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) := by ring
  calc ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z), M Z * regionCommSup Z B
    _ ≤ ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          2 * ‖B‖ * weightY Y η x * (M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) :=
      Finset.sum_le_sum hterm
    _ = 2 * ‖B‖ * weightY Y η x * ∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z),
          M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η := by rw [← Finset.mul_sum]
    _ ≤ 2 * ‖B‖ * weightY Y η x * S1 :=
      mul_le_mul_of_nonneg_left (h_s1 x) (mul_nonneg (by positivity) (le_of_lt (weightY_pos Y η x)))
    _ = 2 * ‖B‖ * S1 * weightY Y η x := by ring

lemma non_autonomous_max_quotient_zero_le [NeZero D] [NeZero L]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z) {Y : Finset (BoxD D L)}
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) {η S1 : ℝ} (hη : 0 ≤ η)
    (h_s1 : ∀ z : BoxD D L, (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => z ∈ Z),
      M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤ S1) :
    nonAutonomousMaxQuotient M Y η U B 0 ≤ 2 * ‖B‖ * S1 := by
  unfold nonAutonomousMaxQuotient; rw [Finset.sup'_le_iff]; intro x _; unfold nonAutonomousSiteQuotient
  have hw : 0 < weightY Y η x := weightY_pos Y η x
  calc (weightY Y η x)⁻¹ * nonAutonomousSiteCommSum M U B x 0
    _ ≤ (weightY Y η x)⁻¹ * (2 * ‖B‖ * S1 * weightY Y η x) :=
      mul_le_mul_of_nonneg_left (non_autonomous_site_comm_sum_zero_le hFlow hM_nn hB hη h_s1 x)
        (inv_nonneg.mpr (le_of_lt hw))
    _ = 2 * ‖B‖ * S1 * ((weightY Y η x)⁻¹ * weightY Y η x) := by ring
    _ = 2 * ‖B‖ * S1 := by rw [inv_mul_cancel₀ (ne_of_gt hw), mul_one]

lemma continuous_non_autonomous_max_quotient [NeZero D] [NeZero L]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P)
    (M : Finset (BoxD D L) → ℝ) (Y : Finset (BoxD D L)) (η : ℝ)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Continuous (nonAutonomousMaxQuotient M Y η U B) := by
  have hB_cont : Continuous (fun z : ℝ => U z * B * (U z)†) :=
    continuous_iff_continuousAt.mpr (fun z => (has_deriv_at_forward_conj hFlow B z).continuousAt)
  apply continuous_finset_sup' Finset.univ Finset.univ_nonempty
  intro x _; unfold nonAutonomousSiteQuotient nonAutonomousSiteCommSum
  exact continuous_const.mul (continuous_finset_sum _ (fun Z _ =>
    continuous_const.mul ((continuous_region_comm_sup Z).comp hB_cont)))

lemma eventually_slope_non_autonomous_max_quotient_lt [NeZero D] [NeZero L]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P) (H : ℝ → LatticeHamiltonian D L Site)
    {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z) {Y : Finset (BoxD D L)} (hY : Y.Nonempty)
    {η S1 : ℝ} (hη : 0 ≤ η)
    (h_s1 : ∀ z : BoxD D L, (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => z ∈ Z),
      M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤ S1)
    (B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {τ : ℝ} (hD_τ : D_gen τ = (H τ).totalHamiltonian) (h_norm_τ : ∀ W, ‖(H τ).h W‖ ≤ M W)
    (r : ℝ) (hr : 2 * S1 * nonAutonomousMaxQuotient M Y η U B τ < r) :
    ∀ᶠ z in 𝓝[>] τ,
      (z - τ)⁻¹ * (nonAutonomousMaxQuotient M Y η U B z - nonAutonomousMaxQuotient M Y η U B τ) < r := by
  apply eventually_slope_sup'_lt (fun x z => nonAutonomousSiteQuotient M Y η U B x z) τ r
  intro x; have hw : 0 < weightY Y η x := weightY_pos Y η x
  set Sx := Finset.univ.filter (fun Z : Finset (BoxD D L) => x ∈ Z)
  set f : Finset (BoxD D L) → ℝ → ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
    fun Z z => (2 * M Z) • (nonAutonomousInteractionOp H U B Z τ z - nonAutonomousInteractionOp H U B Z τ τ)
  set f' : Finset (BoxD D L) → ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
    fun Z => (2 * M Z) • ((Complex.I : ℂ) • opCommutator ((H τ).regionInteraction Z) (U τ * B * (U τ)†))
  have hf_deriv : ∀ Z ∈ Sx, HasDerivAt (f Z) (f' Z) τ := fun Z _ =>
    ((has_deriv_at_non_autonomous_interaction_op hFlow H B Z hD_τ).sub_const
      (nonAutonomousInteractionOp H U B Z τ τ)).const_smul (2 * M Z)
  have hZ_bound : ∀ Z ∈ Sx, ‖f' Z‖ ≤
      2 * (M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
        weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ := by
    intro Z hZ; rw [Finset.mem_filter] at hZ; have hMZ := hM_nn Z
    have hd := norm_deriv_non_autonomous_interaction_op_le H U B Z hM_nn h_norm_τ
    have hinter := sum_filter_inter_nonempty_le Z
      (fun W => M W * regionCommSup W (U τ * B * (U τ)†))
      (fun W => mul_nonneg (hM_nn W) (region_comm_sup_nonneg W _))
    have hsum_z : ∑ z ∈ Z, nonAutonomousSiteCommSum M U B z τ ≤
        (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x *
          nonAutonomousMaxQuotient M Y η U B τ := by
      calc ∑ z ∈ Z, nonAutonomousSiteCommSum M U B z τ
        _ ≤ ∑ z ∈ Z, weightY Y η z * nonAutonomousMaxQuotient M Y η U B τ :=
          Finset.sum_le_sum (fun z _ => non_autonomous_site_comm_sum_le_mul_max_quotient M Y η U B z τ)
        _ = (∑ z ∈ Z, weightY Y η z) * nonAutonomousMaxQuotient M Y η U B τ := by rw [← Finset.sum_mul]
        _ ≤ ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x) *
              nonAutonomousMaxQuotient M Y η U B τ :=
          mul_le_mul_of_nonneg_right (sum_weightY_le hY x hη hZ.2)
            (non_autonomous_max_quotient_nonneg hM_nn Y η U B τ)
        _ = (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x *
              nonAutonomousMaxQuotient M Y η U B τ := by ring
    have h_f'_norm : ‖f' Z‖ = 2 * M Z * ‖(Complex.I : ℂ) • opCommutator ((H τ).regionInteraction Z) (U τ * B * (U τ)†)‖ := by
      dsimp [f']; rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖f' Z‖ = 2 * M Z * ‖(Complex.I : ℂ) • opCommutator ((H τ).regionInteraction Z) (U τ * B * (U τ)†)‖ := h_f'_norm
      _ ≤ 2 * M Z * ∑ W ∈ Finset.univ.filter (fun W => (W ∩ Z).Nonempty),
            M W * regionCommSup W (U τ * B * (U τ)†) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ 2 * M Z * ∑ z ∈ Z, nonAutonomousSiteCommSum M U B z τ :=
        mul_le_mul_of_nonneg_left hinter (by positivity)
      _ ≤ 2 * M Z * ((Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η * weightY Y η x *
            nonAutonomousMaxQuotient M Y η U B τ) := mul_le_mul_of_nonneg_left hsum_z (by positivity)
      _ = 2 * (M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
          weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ := by ring
  have hsum_f' : ∑ Z ∈ Sx, ‖f' Z‖ ≤
      2 * S1 * nonAutonomousMaxQuotient M Y η U B τ * weightY Y η x := by
    calc ∑ Z ∈ Sx, ‖f' Z‖
      _ ≤ ∑ Z ∈ Sx, 2 * (M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
            weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ := Finset.sum_le_sum hZ_bound
      _ = 2 * (∑ Z ∈ Sx, M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) *
            weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      _ ≤ 2 * S1 * weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ := by
        have hs1 := h_s1 x
        have hpos : 0 ≤ weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ :=
          mul_nonneg (le_of_lt hw) (non_autonomous_max_quotient_nonneg hM_nn Y η U B τ)
        nlinarith
      _ = 2 * S1 * nonAutonomousMaxQuotient M Y η U B τ * weightY Y η x := by ring
  have ev := eventually_slope_sum_norm_lt Sx f f' τ hf_deriv
    (lt_of_le_of_lt hsum_f' (mul_lt_mul_of_pos_right hr hw))
  refine (ev.and self_mem_nhdsWithin).mono (fun z ⟨hz, hz_gt⟩ => ?_)
  have hz_pos : 0 < z - τ := sub_pos.mpr hz_gt
  have h_f_tau : (∑ Z ∈ Sx, ‖f Z τ‖) = 0 :=
    Finset.sum_eq_zero (fun Z _ => by dsimp [f]; rw [sub_self, smul_zero, norm_zero])
  have h_sub_le : nonAutonomousSiteCommSum M U B x z - nonAutonomousSiteCommSum M U B x τ ≤
      (∑ Z ∈ Sx, ‖f Z z‖) - (∑ Z ∈ Sx, ‖f Z τ‖) := by
    rw [h_f_tau, sub_zero]; unfold nonAutonomousSiteCommSum; rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum (fun Z _ => ?_)
    have hMZ := hM_nn Z
    have h_mul := mul_le_mul_of_nonneg_left (region_comm_sup_sub_le_interaction_op H U B Z τ z) hMZ
    have h_norm : ‖f Z z‖ = 2 * M Z *
        ‖nonAutonomousInteractionOp H U B Z τ z - nonAutonomousInteractionOp H U B Z τ τ‖ := by
      dsimp [f]; rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    linarith
  have hz_comm := lt_of_le_of_lt (mul_le_mul_of_nonneg_left h_sub_le (inv_nonneg.mpr (le_of_lt hz_pos))) hz
  have hz' := mul_lt_mul_of_pos_left hz_comm (inv_pos.mpr hw)
  unfold nonAutonomousSiteQuotient
  calc (z - τ)⁻¹ * ((weightY Y η x)⁻¹ * nonAutonomousSiteCommSum M U B x z -
          (weightY Y η x)⁻¹ * nonAutonomousSiteCommSum M U B x τ)
    _ = (weightY Y η x)⁻¹ * ((z - τ)⁻¹ *
          (nonAutonomousSiteCommSum M U B x z - nonAutonomousSiteCommSum M U B x τ)) := by ring
    _ < (weightY Y η x)⁻¹ * (r * weightY Y η x) := hz'
    _ = r := by rw [← mul_assoc, mul_comm (weightY Y η x)⁻¹, mul_assoc, inv_mul_cancel₀ (ne_of_gt hw), mul_one]

lemma non_autonomous_max_quotient_le_exp [NeZero D] [NeZero L]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P) (H : ℝ → LatticeHamiltonian D L Site)
    {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z) {Y : Finset (BoxD D L)} (hY : Y.Nonempty)
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : IsSupportedOn Site Y B) {η S1 T : ℝ} (hη : 0 ≤ η)
    (h_s1 : ∀ z : BoxD D L, (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => z ∈ Z),
      M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤ S1)
    (hD_eq : ∀ τ ∈ Set.Icc 0 T, D_gen τ = (H τ).totalHamiltonian)
    (h_norm : ∀ τ ∈ Set.Icc 0 T, ∀ W, ‖(H τ).h W‖ ≤ M W) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) :
    nonAutonomousMaxQuotient M Y η U B τ ≤ 2 * ‖B‖ * S1 * Real.exp (2 * S1 * τ) :=
  le_exp_of_eventually_slope_lt
    (continuous_non_autonomous_max_quotient hFlow M Y η B).continuousOn
    (non_autonomous_max_quotient_zero_le hFlow hM_nn hB hη h_s1)
    (fun u hu r hr => eventually_slope_non_autonomous_max_quotient_lt hFlow H hM_nn hY hη h_s1 B
      (hD_eq u (Set.Ico_subset_Icc_self hu)) (h_norm u (Set.Ico_subset_Icc_self hu)) r hr) hτ

set_option maxHeartbeats 800000 in
/-- **Non-Autonomous Hastings–Koma Lieb–Robinson Commutator Bound
    (`non_autonomous_hastings_koma_lieb_robinson_box`)**. -/
theorem non_autonomous_hastings_koma_lieb_robinson_box [NeZero D] [NeZero L]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P) (H : ℝ → LatticeHamiltonian D L Site)
    {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z)
    {η S1 T : ℝ} (hη : 0 ≤ η) (hS1_nn : 0 ≤ S1)
    (h_s1 : ∀ z : BoxD D L, (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => z ∈ Z),
      M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤ S1)
    (hD_eq : ∀ τ ∈ Set.Icc 0 T, D_gen τ = (H τ).totalHamiltonian)
    (h_norm : ∀ τ ∈ Set.Icc 0 T, ∀ W, ‖(H τ).h W‖ ≤ M W)
    (X Y : Finset (BoxD D L)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hA : IsSupportedOn Site X A) (hB : IsSupportedOn Site Y B) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    ‖opCommutator ((U s)† * A * U s) B‖ ≤
      2 * ‖A‖ * ‖B‖ * (X.card : ℝ) *
        ((Real.exp (2 * S1 * s) - 1) / (1 + (regionDist X Y : ℝ) / 2) ^ η +
          Real.exp (2 * S1 * s) * (if regionDist X Y = 0 then (1 : ℝ) else 0)) := by
  have hU_unit := (kato_hastings_ode_flow P0 D_gen U P hFlow).1
  rw [norm_op_commutator_adj_conj_eq (hU_unit s).1 (hU_unit s).2 A B]
  by_cases h_dist0 : regionDist X Y = 0
  · rw [if_pos h_dist0, mul_one]
    have hcard : (1 : ℝ) ≤ (X.card : ℝ) := Nat.one_le_cast.mpr (Finset.card_pos.mpr hX)
    have hs_nn : 0 ≤ s := hs.1
    have hexp_ge : 1 ≤ Real.exp (2 * S1 * s) := Real.one_le_exp (by positivity)
    have hdiv_nonneg : 0 ≤ (Real.exp (2 * S1 * s) - 1) / (1 + (regionDist X Y : ℝ) / 2) ^ η :=
      div_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos (by positivity) η))
    have h_step : ‖opCommutator A (U s * B * (U s)†)‖ ≤ 2 * ‖A‖ * ‖B‖ := by
      calc ‖opCommutator A (U s * B * (U s)†)‖ ≤ 2 * ‖A‖ * ‖U s * B * (U s)†‖ := norm_opCommutator_le A _
        _ = 2 * ‖A‖ * ‖B‖ := by rw [norm_mul_mul_adjoint_eq (hU_unit s).1 B]
    calc ‖opCommutator A (U s * B * (U s)†)‖ ≤ 2 * ‖A‖ * ‖B‖ * 1 * 1 := by rw [mul_one, mul_one]; exact h_step
      _ ≤ 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) * ((Real.exp (2 * S1 * s) - 1) /
          (1 + (regionDist X Y : ℝ) / 2) ^ η + Real.exp (2 * S1 * s)) := by gcongr; linarith
  · rw [if_neg h_dist0, mul_zero, add_zero]
    have h_dist_pos : 0 < regionDist X Y := Nat.pos_of_ne_zero h_dist0
    set f : ℝ → ℝ := fun τ => ‖opCommutator A (U τ * B * (U τ)†)‖
    set C_LR : ℝ := 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η
    set B_LR : ℝ → ℝ := fun τ => C_LR * (Real.exp (2 * S1 * τ) - 1)
    set B'_LR : ℝ → ℝ := fun τ => C_LR * (2 * S1 * Real.exp (2 * S1 * τ))
    have hB_cont_op : Continuous (fun τ : ℝ => U τ * B * (U τ)†) :=
      continuous_iff_continuousAt.mpr (fun τ => (has_deriv_at_forward_conj hFlow B τ).continuousAt)
    have hf_cont : ContinuousOn f (Set.Icc 0 s) :=
      ((continuous_const.mul hB_cont_op).sub (hB_cont_op.mul continuous_const)).norm.continuousOn
    have hf0 : f 0 ≤ B_LR 0 := by
      dsimp [f, B_LR]
      rw [hFlow.U_zero, adjoint_one_eq_one, one_mul, mul_one,
        opCommutator_eq_zero_of_disjoint (disjoint_of_regionDist_pos h_dist_pos) hA hB,
        norm_zero, mul_zero, Real.exp_zero, sub_self, mul_zero]
    have hB_deriv : ∀ τ : ℝ, HasDerivAt B_LR (B'_LR τ) τ := fun τ =>
      (((hasDerivAt_real_exp_const_mul (2 * S1) τ).sub_const 1).const_mul C_LR)
    have hB_cont : ContinuousOn B_LR (Set.Icc 0 s) := fun τ _ => (hB_deriv τ).continuousAt.continuousWithinAt
    have hB_within : ∀ τ ∈ Set.Ico 0 s, HasDerivWithinAt B_LR (B'_LR τ) (Set.Ici τ) τ :=
      fun τ _ => (hB_deriv τ).hasDerivWithinAt
    have h_slope : ∀ τ ∈ Set.Ico 0 s, ∀ r, B'_LR τ < r → ∃ᶠ z in 𝓝[>] τ, slope f τ z < r := by
      intro τ hτ r hr
      have hτ_T : τ ∈ Set.Icc 0 T := ⟨hτ.1, le_trans (le_of_lt hτ.2) hs.2⟩
      have hQ_le := non_autonomous_max_quotient_le_exp hFlow H hM_nn hY hB hη h_s1 hD_eq h_norm hτ_T
      set gA : ℝ → ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
        fun z => (2 * ‖A‖) • (nonAutonomousInteractionOp H U B X τ z - nonAutonomousInteractionOp H U B X τ τ)
      set dA : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
        (2 * ‖A‖) • ((Complex.I : ℂ) • opCommutator ((H τ).regionInteraction X) (U τ * B * (U τ)†))
      have hd_gA : HasDerivAt gA dA τ :=
        ((has_deriv_at_non_autonomous_interaction_op hFlow H B X (hD_eq τ hτ_T)).sub_const
          (nonAutonomousInteractionOp H U B X τ τ)).const_smul (2 * ‖A‖)
      have hd_norm_le : ‖dA‖ ≤ B'_LR τ := by
        have hd1 := norm_deriv_non_autonomous_interaction_op_le H U B X hM_nn (h_norm τ hτ_T)
        have hinter := sum_filter_inter_nonempty_le X
          (fun W => M W * regionCommSup W (U τ * B * (U τ)†))
          (fun W => mul_nonneg (hM_nn W) (region_comm_sup_nonneg W _))
        have h2A_nonneg : 0 ≤ 2 * ‖A‖ := mul_nonneg zero_le_two (norm_nonneg A)
        have hsum_X : ∑ x ∈ X, nonAutonomousSiteCommSum M U B x τ ≤
            ((X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η) *
              (2 * ‖B‖ * S1 * Real.exp (2 * S1 * τ)) := by
          calc ∑ x ∈ X, nonAutonomousSiteCommSum M U B x τ
            _ ≤ ∑ x ∈ X, weightY Y η x * nonAutonomousMaxQuotient M Y η U B τ :=
              Finset.sum_le_sum (fun x _ => non_autonomous_site_comm_sum_le_mul_max_quotient M Y η U B x τ)
            _ = (∑ x ∈ X, weightY Y η x) * nonAutonomousMaxQuotient M Y η U B τ := by rw [← Finset.sum_mul]
            _ ≤ ((X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η) *
                  (2 * ‖B‖ * S1 * Real.exp (2 * S1 * τ)) :=
              mul_le_mul (sum_weightY_regionDist_le X Y hY hη) hQ_le
                (non_autonomous_max_quotient_nonneg hM_nn Y η U B τ)
                (div_nonneg (Nat.cast_nonneg _) (le_of_lt (Real.rpow_pos_of_pos (by positivity) η)))
        have hdA_eq : ‖dA‖ = 2 * ‖A‖ * ‖(Complex.I : ℂ) • opCommutator ((H τ).regionInteraction X) (U τ * B * (U τ)†)‖ := by
          dsimp [dA]; rw [norm_smul, Real.norm_of_nonneg h2A_nonneg]
        calc ‖dA‖ = 2 * ‖A‖ * ‖(Complex.I : ℂ) • opCommutator ((H τ).regionInteraction X) (U τ * B * (U τ)†)‖ := hdA_eq
          _ ≤ 2 * ‖A‖ * ∑ W ∈ Finset.univ.filter (fun W => (W ∩ X).Nonempty),
                M W * regionCommSup W (U τ * B * (U τ)†) := mul_le_mul_of_nonneg_left hd1 h2A_nonneg
          _ ≤ 2 * ‖A‖ * ∑ x ∈ X, nonAutonomousSiteCommSum M U B x τ :=
            mul_le_mul_of_nonneg_left hinter h2A_nonneg
          _ ≤ 2 * ‖A‖ * (((X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η) *
                (2 * ‖B‖ * S1 * Real.exp (2 * S1 * τ))) := mul_le_mul_of_nonneg_left hsum_X h2A_nonneg
          _ = B'_LR τ := by dsimp [B'_LR, C_LR]; ring
      have hd_lt : (∑ _u ∈ ({()} : Finset Unit), ‖dA‖) < r := by
        rw [Finset.sum_singleton]; exact lt_of_le_of_lt hd_norm_le hr
      have ev := eventually_slope_sum_norm_lt ({()} : Finset Unit)
        (fun _ z => gA z) (fun _ => dA) τ (fun _ _ => hd_gA) hd_lt
      refine ((ev.and self_mem_nhdsWithin).mono (fun z ⟨hz, hz_gt⟩ => ?_)).frequently
      rw [Finset.sum_singleton, Finset.sum_singleton] at hz
      have hgA_tau : ‖gA τ‖ = 0 := by dsimp [gA]; rw [sub_self, smul_zero, norm_zero]
      have h_step : f z - f τ ≤ ‖gA z‖ - ‖gA τ‖ := by
        rw [hgA_tau, sub_zero]
        have h1 := norm_op_commutator_sub_le_interaction_op H U B hA τ z
        have h2 : ‖gA z‖ = 2 * ‖A‖ *
            ‖nonAutonomousInteractionOp H U B X τ z - nonAutonomousInteractionOp H U B X τ τ‖ := by
          dsimp [gA]; rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        dsimp [f]; linarith
      rw [slope_def_field, div_eq_inv_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h_step (inv_nonneg.mpr (le_of_lt (sub_pos.mpr hz_gt)))) hz
    have h_final := image_le_of_liminf_slope_right_le_deriv_boundary
      hf_cont hf0 hB_cont hB_within h_slope (Set.right_mem_Icc.mpr hs.1)
    dsimp [f, B_LR, C_LR] at h_final
    calc ‖opCommutator A (U s * B * (U s)†)‖
      _ ≤ 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) / (1 + (regionDist X Y : ℝ) / 2) ^ η *
            (Real.exp (2 * S1 * s) - 1) := h_final
      _ = 2 * ‖A‖ * ‖B‖ * (X.card : ℝ) *
            ((Real.exp (2 * S1 * s) - 1) / (1 + (regionDist X Y : ℝ) / 2) ^ η) := by ring

/-- **Non-Autonomous Hastings–Koma `condExp` Spatial Tail Bound
    (`norm_non_autonomous_flow_sub_cond_exp_le_hastings_koma`)**. -/
theorem norm_non_autonomous_flow_sub_cond_exp_le_hastings_koma [NeZero D] [NeZero L]
    [∀ x, Nonempty (Site x)]
    {P0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    {D_gen U P : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)}
    (hFlow : IsKatoHastingsFlowSystem P0 D_gen U P) (H : ℝ → LatticeHamiltonian D L Site)
    {M : Finset (BoxD D L) → ℝ} (hM_nn : ∀ Z, 0 ≤ M Z)
    {η S1 T : ℝ} (hη : 0 ≤ η) (hS1_nn : 0 ≤ S1) (hT : 0 ≤ T)
    (h_s1 : ∀ z : BoxD D L, (∑ Z ∈ Finset.univ.filter (fun Z : Finset (BoxD D L) => z ∈ Z),
      M Z * (Z.card : ℝ) * (1 + (regionDiam Z : ℝ)) ^ η) ≤ S1)
    (hD_eq : ∀ τ ∈ Set.Icc 0 T, D_gen τ = (H τ).totalHamiltonian)
    (h_norm : ∀ τ ∈ Set.Icc 0 T, ∀ W, ‖(H τ).h W‖ ≤ M W)
    {X B : Finset (BoxD D L)} (hX : X.Nonempty) {d : ℕ} (hd_pos : 0 < d)
    (h_dist : (Finset.univ \ B).Nonempty → d ≤ regionDist X (Finset.univ \ B))
    (O_X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_X : IsSupportedOn Site X O_X) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    ‖(U s)† * O_X * U s - condExp Site B ((U s)† * O_X * U s)‖ ≤
      (2 * (X.card : ℝ) * ((Real.exp (2 * S1 * T) - 1) / (1 + (d : ℝ) / 2) ^ η)) * ‖O_X‖ := by
  set ε : ℝ := (2 * (X.card : ℝ) * ((Real.exp (2 * S1 * T) - 1) / (1 + (d : ℝ) / 2) ^ η)) * ‖O_X‖
  have hexp_ge : 1 ≤ Real.exp (2 * S1 * T) := Real.one_le_exp (by positivity)
  have hε_nn : 0 ≤ ε := mul_nonneg (mul_nonneg (by positivity)
    (div_nonneg (by linarith) (le_of_lt (Real.rpow_pos_of_pos (by positivity) η)))) (norm_nonneg O_X)
  by_cases hBc : (Finset.univ \ B).Nonempty
  · apply norm_sub_condExp_le_of_commutator_bound B ((U s)† * O_X * U s) hε_nn
    intro Y hY
    have hd_le : d ≤ regionDist X (Finset.univ \ B) := h_dist hBc
    have h_dist_ne : regionDist X (Finset.univ \ B) ≠ 0 := by omega
    have h_lr := non_autonomous_hastings_koma_lieb_robinson_box
      hFlow H hM_nn hη hS1_nn h_s1 hD_eq h_norm X (Finset.univ \ B) hX hBc O_X Y hO_X hY hs
    rw [if_neg h_dist_ne, mul_zero, add_zero] at h_lr
    have hs_nn : 0 ≤ s := hs.1
    have hexp_s_ge : 1 ≤ Real.exp (2 * S1 * s) := Real.one_le_exp (by positivity)
    have hexp_le : Real.exp (2 * S1 * s) - 1 ≤ Real.exp (2 * S1 * T) - 1 := by
      have h_mul : 2 * S1 * s ≤ 2 * S1 * T := mul_le_mul_of_nonneg_left hs.2 (by positivity)
      linarith [Real.exp_le_exp.mpr h_mul]
    have hd_cast : (1 + (d : ℝ) / 2) ^ η ≤ (1 + (regionDist X (Finset.univ \ B) : ℝ) / 2) ^ η := by
      apply Real.rpow_le_rpow (by positivity) _ hη
      have : (d : ℝ) ≤ (regionDist X (Finset.univ \ B) : ℝ) := Nat.cast_le.mpr hd_le
      linarith
    have h_div : (Real.exp (2 * S1 * s) - 1) / (1 + (regionDist X (Finset.univ \ B) : ℝ) / 2) ^ η ≤
        (Real.exp (2 * S1 * T) - 1) / (1 + (d : ℝ) / 2) ^ η :=
      div_le_div₀ (by linarith) hexp_le (Real.rpow_pos_of_pos (by positivity) η) hd_cast
    calc ‖opCommutator ((U s)† * O_X * U s) Y‖
      _ ≤ 2 * ‖O_X‖ * ‖Y‖ * (X.card : ℝ) *
            ((Real.exp (2 * S1 * s) - 1) / (1 + (regionDist X (Finset.univ \ B) : ℝ) / 2) ^ η) := h_lr
      _ ≤ 2 * ‖O_X‖ * ‖Y‖ * (X.card : ℝ) *
            ((Real.exp (2 * S1 * T) - 1) / (1 + (d : ℝ) / 2) ^ η) :=
        mul_le_mul_of_nonneg_left h_div (by positivity)
      _ = ε * ‖Y‖ := by dsimp [ε]; ring
  · rw [Finset.not_nonempty_iff_eq_empty] at hBc
    apply norm_sub_condExp_le_of_commutator_bound B ((U s)† * O_X * U s) hε_nn
    intro Y hY; rw [hBc] at hY
    rcases isSupportedOn_empty_eq_smul_one hY with ⟨c, rfl⟩
    have h_comm : opCommutator ((U s)† * O_X * U s) (c • 1) = 0 := by
      unfold opCommutator; rw [clm_mul_smul_comm, clm_smul_mul_assoc, mul_one, one_mul, sub_self]
    rw [h_comm, norm_zero]; positivity

end
