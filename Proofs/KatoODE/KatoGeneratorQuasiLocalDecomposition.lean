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

import Proofs.KatoODE.ContinuationWeightKernel
import Proofs.HastingsKomaLightCone.InterpolatedS1AndSuperpolyEnvelope

/-!
# Concentric Cube-Shell Telescoping Decomposition of the Kato Generator

Constructs the concentric cube-shell telescoping decomposition `katoGeneratorQuasiLocal` (`shellCube`, `approxGenSiteOp`, `shellGenSiteOp`, `katoGeneratorShellDecayProfile`) realizing `katoHastingsGeneratorOp` as a parameter-continuous `QuasiLocalPerturbation` whose interaction norms inherit superpolynomial conditional expectation decay.

## References

* Part I, Section 6.1 (`subsec:dsuper-banach`), Definition 6.1 (`def:banach-quasilocal`)
* Part I, Section 6.3 (`subsec:qac-block-diag`), Equation (75) (`eq:qac-generator-def`), Proposition 6.4 (`prop:qac-block-diagonalization`)
-/

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics MeasureTheory ContinuousLinearMap
open WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## 1. Concentric Cube Shells `shellCube` on `BoxD D L` -/

def shellCube {D L : ℕ} [NeZero L] (u : BoxD D L) (r : ℕ) : Finset (BoxD D L) :=
  if r < L then enclosingBoxCube u 1 r else Finset.univ

lemma shellCube_of_lt {D L : ℕ} [NeZero L] (u : BoxD D L) {r : ℕ} (hr : r < L) :
    shellCube u r = enclosingBoxCube u 1 r := if_pos hr
lemma shellCube_of_ge {D L : ℕ} [NeZero L] (u : BoxD D L) {r : ℕ} (hr : L ≤ r) :
    shellCube u r = Finset.univ := if_neg (not_lt.mpr hr)
lemma shellCube_L {D L : ℕ} [NeZero L] (u : BoxD D L) :
    shellCube u L = Finset.univ := shellCube_of_ge u (le_refl L)

lemma boxCube_zero_L_eq_univ (D L : ℕ) [NeZero L] :
    boxCube (fun _ : Fin D => (⟨0, NeZero.pos L⟩ : Fin L)) L = Finset.univ := by
  ext x; simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and, zero_le, zero_add]
  exact ⟨fun _ => trivial, fun _ i => (x i).isLt⟩

lemma shellCube_mem_BoxCubes {D L : ℕ} [NeZero L] (u : BoxD D L) {r : ℕ} (hr : r ≤ L) :
    shellCube u r ∈ boxCubes D L r := by
  by_cases hlt : r < L
  · rw [shellCube_of_lt u hlt]; exact enclosingBoxCube_mem_BoxCubes u 1 r
  · have hrL : r = L := le_antisymm hr (not_lt.mp hlt)
    subst hrL; rw [shellCube_L]; simp only [boxCubes, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun _ : Fin D => (⟨0, NeZero.pos r⟩ : Fin r), boxCube_zero_L_eq_univ D r⟩

lemma mem_shellCube_self {D L : ℕ} [NeZero L] (u : BoxD D L) {r : ℕ} (hr1 : 1 ≤ r) :
    u ∈ shellCube u r := by
  by_cases hlt : r < L
  · rw [shellCube_of_lt u hlt]
    simp only [enclosingBoxCube, boxCube, Finset.mem_filter, Finset.mem_univ, true_and]; intro i; omega
  · rw [shellCube_of_ge u (not_lt.mp hlt)]; exact Finset.mem_univ u

lemma shellCube_sub_one_subset {D L : ℕ} [NeZero L] (u : BoxD D L) {r : ℕ} (hr2 : 2 ≤ r) :
    shellCube u (r - 1) ⊆ shellCube u r := by
  by_cases hlt : r < L
  · have hlt' : r - 1 < L := by omega
    rw [shellCube_of_lt u hlt, shellCube_of_lt u hlt']; intro x hx
    simp only [enclosingBoxCube, boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro i; have hxi := hx i
    have hdiv1 : (r - 1 - 1) / 2 ≤ (r - 1) / 2 := Nat.div_le_div_right (by omega)
    have hdiv2 : (r - 1) / 2 ≤ (r - 1 - 1) / 2 + 1 := by omega
    omega
  · rw [shellCube_of_ge u (not_lt.mp hlt)]; exact Finset.subset_univ _

lemma boxBall_half_sub_one_subset_shellCube {D L : ℕ} [NeZero L] (u : BoxD D L)
    {r : ℕ} (hr1 : 1 ≤ r) : boxBall u ((r - 1) / 2) ⊆ shellCube u r := by
  by_cases hlt : r < L
  · rw [shellCube_of_lt u hlt]; intro x hx
    simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [enclosingBoxCube, boxCube, Finset.mem_filter, Finset.mem_univ, true_and]; intro i
    have hi : coordDist (u i) (x i) ≤ boxDist u x :=
      Finset.le_sup (f := fun j : Fin D => coordDist (u j) (x j)) (Finset.mem_univ i)
    have hcoord : (((u i).val : ℤ) - ((x i).val : ℤ)).natAbs ≤ (r - 1) / 2 := le_trans hi hx
    omega
  · rw [shellCube_of_ge u (not_lt.mp hlt)]; exact Finset.subset_univ _

lemma card_filter_shellCube_eq_le_pow {D L : ℕ} [NeZero D] [NeZero L]
    {r : ℕ} (hr1 : 1 ≤ r) {A : Finset (BoxD D L)} (hA : A ∈ boxCubes D L r) :
    (Finset.univ.filter (fun u : BoxD D L => shellCube u r = A)).card ≤ r ^ D := by
  have hsub : Finset.univ.filter (fun u : BoxD D L => shellCube u r = A) ⊆ A := by
    intro u hu; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [← hu]; exact mem_shellCube_self u hr1
  rcases Finset.mem_image.mp hA with ⟨x0, _, rfl⟩
  exact le_trans (Finset.card_le_card hsub) (card_boxCube_le_pow x0 r)

/-! ## 2. Conditional Expectation Monotonicity & Telescoping Shell Operators -/

lemma condExp_univ_eq_self {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (O : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    condExp Site Finset.univ O = O := by
  have h_norm : ‖O - condExp Site Finset.univ O‖ ≤ 0 := by
    refine norm_sub_condExp_le_of_commutator_bound Finset.univ O (le_refl 0) (fun Y hY => ?_)
    rw [Finset.sdiff_self] at hY
    rcases isSupportedOn_empty_eq_smul_one_main hY with ⟨c, rfl⟩
    have h_comm : opCommutator O (c • (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) = 0 := by
      unfold opCommutator; rw [clm_mul_smul_comm, clm_smul_mul_assoc, mul_one, one_mul, sub_self]
    rw [h_comm, norm_zero, zero_mul]
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp h_norm)).symm

lemma norm_sub_condExp_le_two_mul_of_subset {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {A B : Finset (BoxD D L)} (hAB : A ⊆ B)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖X - condExp Site B X‖ ≤ 2 * ‖X - condExp Site A X‖ := by
  have hsupp : IsSupportedOn Site B (condExp Site A X) :=
    isSupportedOn_mono hAB (isSupportedOn_condExp Site A X)
  have hce : condExp Site B (condExp Site A X) = condExp Site A X :=
    condExp_eq_self_of_isSupportedOn hsupp
  have hsub : condExp Site B (X - condExp Site A X) =
      condExp Site B X - condExp Site B (condExp Site A X) :=
    map_sub (condExpCLM Site B) X (condExp Site A X)
  have hid : X - condExp Site B X =
      (X - condExp Site A X) - condExp Site B (X - condExp Site A X) := by rw [hsub, hce]; abel
  rw [hid]; exact norm_sub_condExp_le_two_mul_norm B (X - condExp Site A X)

def approxGenSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (u : BoxD D L) (r : ℕ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  if r = 0 then 0 else condExp Site (shellCube u r) D_u

def shellGenSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (u : BoxD D L) (r : ℕ) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  approxGenSiteOp D_u u r - approxGenSiteOp D_u u (r - 1)

private lemma isSelfAdjoint_zero_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] : IsSelfAdjoint (0 : E →L[ℂ] E) := IsSelfAdjoint.zero _

lemma isSelfAdjoint_approxGenSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hD : IsSelfAdjoint D_u) (u : BoxD D L) (r : ℕ) :
    IsSelfAdjoint (approxGenSiteOp D_u u r) := by
  dsimp [approxGenSiteOp]; split_ifs
  · exact isSelfAdjoint_zero_clm
  · exact isSelfAdjoint_condExp_bhm (shellCube u r) hD

lemma isSelfAdjoint_shellGenSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hD : IsSelfAdjoint D_u) (u : BoxD D L) (r : ℕ) :
    IsSelfAdjoint (shellGenSiteOp D_u u r) :=
  isSelfAdjoint_sub_clm (isSelfAdjoint_approxGenSiteOp hD u r)
    (isSelfAdjoint_approxGenSiteOp hD u (r - 1))

lemma isSupportedOn_shellGenSiteOp {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (u : BoxD D L) {r : ℕ} (hr1 : 1 ≤ r) :
    IsSupportedOn Site (shellCube u r) (shellGenSiteOp D_u u r) := by
  have hr0 : r ≠ 0 := by omega
  have h1 : IsSupportedOn Site (shellCube u r) (approxGenSiteOp D_u u r) := by
    simp only [approxGenSiteOp, if_neg hr0]; exact isSupportedOn_condExp Site (shellCube u r) D_u
  have h2 : IsSupportedOn Site (shellCube u r) (approxGenSiteOp D_u u (r - 1)) := by
    by_cases hr2 : r - 1 = 0
    · simp only [approxGenSiteOp, if_pos hr2]; exact isSupportedOn_zero (shellCube u r)
    · simp only [approxGenSiteOp, if_neg hr2]
      have hge2 : 2 ≤ r := by omega
      exact isSupportedOn_mono (shellCube_sub_one_subset u hge2)
        (isSupportedOn_condExp Site (shellCube u (r - 1)) D_u)
  exact isSupportedOn_sub (shellCube u r) h1 h2

lemma norm_approxGenSiteOp_le {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (u : BoxD D L) (r : ℕ) :
    ‖approxGenSiteOp D_u u r‖ ≤ ‖D_u‖ := by
  dsimp [approxGenSiteOp]; split_ifs
  · rw [norm_zero]; exact norm_nonneg D_u
  · exact norm_condExp_le (shellCube u r) D_u

lemma norm_shellGenSiteOp_le_two_mul_norm {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (u : BoxD D L) (r : ℕ) :
    ‖shellGenSiteOp D_u u r‖ ≤ 2 * ‖D_u‖ := by
  calc ‖shellGenSiteOp D_u u r‖
      ≤ ‖approxGenSiteOp D_u u r‖ + ‖approxGenSiteOp D_u u (r - 1)‖ := norm_sub_le _ _
    _ ≤ ‖D_u‖ + ‖D_u‖ :=
        add_le_add (norm_approxGenSiteOp_le D_u u r) (norm_approxGenSiteOp_le D_u u (r - 1))
    _ = 2 * ‖D_u‖ := by ring

lemma norm_shellGenSiteOp_le_four_mul_sub_condExp_boxBall {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (u : BoxD D L) {r : ℕ} (hr2 : 2 ≤ r) :
    ‖shellGenSiteOp D_u u r‖ ≤ 4 * ‖D_u - condExp Site (boxBall u ((r - 2) / 2)) D_u‖ := by
  have hr0 : r ≠ 0 := by omega
  have hr1 : r - 1 ≠ 0 := by omega
  have hr1_ge : 1 ≤ r - 1 := by omega
  have hsub1 : boxBall u ((r - 2) / 2) ⊆ shellCube u (r - 1) := by
    have heq : (r - 1 - 1) / 2 = (r - 2) / 2 := by omega
    rw [← heq]; exact boxBall_half_sub_one_subset_shellCube u hr1_ge
  have hsub2 : boxBall u ((r - 2) / 2) ⊆ shellCube u r :=
    Finset.Subset.trans hsub1 (shellCube_sub_one_subset u hr2)
  have h_id : shellGenSiteOp D_u u r =
      (D_u - condExp Site (shellCube u (r - 1)) D_u) -
        (D_u - condExp Site (shellCube u r) D_u) := by
    dsimp [shellGenSiteOp, approxGenSiteOp]; rw [if_neg hr0, if_neg hr1]; abel
  rw [h_id]
  calc ‖(D_u - condExp Site (shellCube u (r - 1)) D_u) -
          (D_u - condExp Site (shellCube u r) D_u)‖
      ≤ ‖D_u - condExp Site (shellCube u (r - 1)) D_u‖ +
          ‖D_u - condExp Site (shellCube u r) D_u‖ := norm_sub_le _ _
    _ ≤ 2 * ‖D_u - condExp Site (boxBall u ((r - 2) / 2)) D_u‖ +
          2 * ‖D_u - condExp Site (boxBall u ((r - 2) / 2)) D_u‖ :=
        add_le_add (norm_sub_condExp_le_two_mul_of_subset hsub1 D_u)
          (norm_sub_condExp_le_two_mul_of_subset hsub2 D_u)
    _ = 4 * ‖D_u - condExp Site (boxBall u ((r - 2) / 2)) D_u‖ := by ring

lemma sum_shellGenSiteOp_Icc {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (u : BoxD D L) (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, shellGenSiteOp D_u u r) = approxGenSiteOp D_u u n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 m), ih]; dsimp [shellGenSiteOp]; abel

lemma sum_shellGenSiteOp_Icc_L {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (D_u : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (u : BoxD D L) :
    (∑ r ∈ Finset.Icc 1 L, shellGenSiteOp D_u u r) = D_u := by
  rw [sum_shellGenSiteOp_Icc D_u u L]; dsimp [approxGenSiteOp]
  rw [if_neg (NeZero.ne L), shellCube_L u, condExp_univ_eq_self]

/-! ## 3. Continuity in the Hamiltonian & Linearity of `katoHastingsGeneratorOp` -/

private lemma continuous_exp_smul_clm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (c : ℂ) :
    Continuous (fun H : E →L[ℂ] E => NormedSpace.exp (c • H)) := by
  let +nondep : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous.comp (continuous_const_smul c)

lemma continuous_timeEvolutionOp_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] (t : ℝ) :
    Continuous (fun H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site =>
      timeEvolutionOp H t) := continuous_exp_smul_clm (Complex.I * (t : ℂ))

private lemma continuous_heisenbergFlow_left_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (t : ℝ) (X : E →L[ℂ] E) :
    Continuous (fun H : E →L[ℂ] E =>
      NormedSpace.exp ((Complex.I * (t : ℂ)) • H) * X *
        NormedSpace.exp ((Complex.I * ((-t : ℝ) : ℂ)) • H)) :=
  ((continuous_exp_smul_clm (Complex.I * (t : ℂ))).mul continuous_const).mul
    (continuous_exp_smul_clm (Complex.I * ((-t : ℝ) : ℂ)))

lemma continuous_heisenbergFlow_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (t : ℝ) (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Continuous (fun H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site =>
      heisenbergFlow H t X) := continuous_heisenbergFlow_left_clm t X

/-- Norm bound `‖katoHastingsGeneratorOp H W X‖ ≤ (∫ t, ‖W t‖) * ‖X‖` for self-adjoint `H`
    and integrable `W`. -/
lemma norm_katoHastingsGeneratorOp_le_integral_norm_mul {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    {W : ℝ → ℂ} (hW : Integrable W)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    ‖katoHastingsGeneratorOp H W X‖ ≤ (∫ t : ℝ, ‖W t‖) * ‖X‖ := by
  unfold katoHastingsGeneratorOp
  calc ‖∫ t : ℝ, W t • heisenbergFlow H t X‖
      ≤ ∫ t : ℝ, ‖W t • heisenbergFlow H t X‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, ‖W t‖ * ‖X‖ := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (hW.norm.mul_const ‖X‖) (Filter.Eventually.of_forall (fun t => ?_))
        dsimp; rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_heisenbergFlow_le_self hH t X) (norm_nonneg (W t))
    _ = (∫ t : ℝ, ‖W t‖) * ‖X‖ := MeasureTheory.integral_mul_const ‖X‖ (fun t => ‖W t‖)

/-- Finite-sum linearity of `katoHastingsGeneratorOp H W` in the operator argument. -/
lemma katoHastingsGeneratorOp_finset_sum {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site} (hH : IsSelfAdjoint H)
    {W : ℝ → ℂ} (hW : Integrable W) {ι : Type*} (s : Finset ι)
    (X : ι → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) :
    (∑ i ∈ s, katoHastingsGeneratorOp H W (X i)) =
      katoHastingsGeneratorOp H W (∑ i ∈ s, X i) := by
  unfold katoHastingsGeneratorOp
  rw [← MeasureTheory.integral_finset_sum s
    (fun i _ => integrable_smul_heisenbergFlow_of_integrable hH hW (X i))]
  congr 1; ext t
  simp only [heisenbergFlow, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]

private lemma isSelfAdjoint_add_real_smul_kato {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH0 : IsSelfAdjoint H0) (hV : IsSelfAdjoint totalPerturbation) (s : ℝ) :
    IsSelfAdjoint (H0 + s • totalPerturbation) := by
  rw [clm_real_smul]; exact isSelfAdjoint_interpolatedHamiltonian hH0 hV s

/-- Continuity of `s ↦ katoHastingsGeneratorOp (H0 + s • V_tot) W X` for self-adjoint `H0, V_tot`
    and integrable `W : ℝ → ℂ`, proved via dominated convergence. -/
theorem continuous_katoHastingsGeneratorOp_interpolated {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {H0 totalPerturbation : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hH0 : IsSelfAdjoint H0) (hV : IsSelfAdjoint totalPerturbation) {W : ℝ → ℂ} (hW : Integrable W)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    Continuous (fun s : ℝ => katoHastingsGeneratorOp (H0 + s • totalPerturbation) W X) := by
  unfold katoHastingsGeneratorOp
  have hH_sa : ∀ s : ℝ, IsSelfAdjoint (H0 + s • totalPerturbation) := isSelfAdjoint_add_real_smul_kato hH0 hV
  refine MeasureTheory.continuous_of_dominated (bound := fun t : ℝ => ‖W t‖ * ‖X‖) ?_ ?_ ?_ ?_
  · intro s
    exact (integrable_smul_heisenbergFlow_of_integrable (hH_sa s) hW X).aestronglyMeasurable
  · intro s; refine Filter.Eventually.of_forall (fun t => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_heisenbergFlow_le_self (hH_sa s) t X) (norm_nonneg (W t))
  · exact hW.norm.mul_const ‖X‖
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have hH_cont : Continuous (fun s : ℝ => H0 + s • totalPerturbation) :=
      continuous_const.add (continuous_id.smul continuous_const)
    exact ((continuous_heisenbergFlow_left t X).comp hH_cont).const_smul (W t)

/-! ## 4. Quasi-Local Cube-Shell Decomposition `katoGeneratorQuasiLocal` & Main Existence Theorem -/

/-- The concentric cube-shell `QuasiLocalPerturbation` decomposition of the Kato–Hastings
    continuation generator $\mathcal{D}_{H_0 + s V_{\mathrm{tot}}, W}(V_{\mathrm{tot}})$. -/
def katoGeneratorQuasiLocal {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH0 : IsSelfAdjoint H0)
    (W : ℝ → ℂ) (hW_int : Integrable W)
    (hW_real : ∀ t : ℝ, star (W t) = W t) (hW_odd : ∀ t : ℝ, W (-t) = - W t)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    QuasiLocalPerturbation D L Site where
  term r A :=
    if r ∈ Finset.Icc 1 L ∧ A ∈ boxCubes D L r then
      ∑ u ∈ Finset.univ.filter (fun u : BoxD D L => shellCube u r = A),
        shellGenSiteOp
          (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r
    else 0
  is_selfAdjoint r A := by
    split_ifs with h
    · refine isSelfAdjoint_finset_sum _ _ (fun u _ => ?_)
      have hHs : IsSelfAdjoint (H0 + s • V.totalPerturbation) :=
        isSelfAdjoint_add_real_smul_kato hH0 V.isSelfAdjoint_totalPerturbation s
      exact isSelfAdjoint_shellGenSiteOp
        (isSelfAdjoint_bochnerFilteredOp hHs (isSelfAdjoint_sitePerturbationOp V u) hW_real) u r
    · exact isSelfAdjoint_zero_clm
  is_supported r hr A hA := by
    rw [if_pos ⟨hr, hA⟩]
    refine isSupportedOn_finset_sum A _ _ (fun u hu => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    rw [← hu]; exact isSupportedOn_shellGenSiteOp _ u (Finset.mem_Icc.mp hr).1

/-- Exact telescoping identity: `(katoGeneratorQuasiLocal ... s).V_tot` equals
    `katoHastingsGeneratorOp (H0 + s • V.V_tot) W V.V_tot` for every `s : ℝ`. -/
theorem katoGeneratorQuasiLocal_V_tot_eq {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH0 : IsSelfAdjoint H0)
    (W : ℝ → ℂ) (hW_int : Integrable W)
    (hW_real : ∀ t : ℝ, star (W t) = W t) (hW_odd : ∀ t : ℝ, W (-t) = - W t)
    (V : QuasiLocalPerturbation D L Site) (s : ℝ) :
    (katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).totalPerturbation =
      katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W V.totalPerturbation := by
  let H_s := H0 + s • V.totalPerturbation
  have hHs : IsSelfAdjoint H_s := isSelfAdjoint_add_real_smul_kato hH0 V.isSelfAdjoint_totalPerturbation s
  let D_u := fun u : BoxD D L => katoHastingsGeneratorOp H_s W (sitePerturbationOp V u)
  change (∑ r ∈ Finset.Icc 1 L, ∑ A ∈ boxCubes D L r,
    (katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).term r A) =
    katoHastingsGeneratorOp H_s W V.totalPerturbation
  have h_inner : ∀ r ∈ Finset.Icc 1 L,
      (∑ A ∈ boxCubes D L r,
        (katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).term r A) =
      ∑ u : BoxD D L, shellGenSiteOp (D_u u) u r := by
    intro r hr
    have h_congr : ∀ A ∈ boxCubes D L r,
        (katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).term r A =
        ∑ u ∈ Finset.univ.filter (fun u : BoxD D L => shellCube u r = A),
          shellGenSiteOp (D_u u) u r := by
      intro A hA; dsimp [katoGeneratorQuasiLocal]; rw [if_pos ⟨hr, hA⟩]
    rw [Finset.sum_congr rfl h_congr]
    exact Finset.sum_fiberwise_of_maps_to
      (fun u _ => shellCube_mem_BoxCubes u (Finset.mem_Icc.mp hr).2) _
  rw [Finset.sum_congr rfl h_inner, Finset.sum_comm]
  simp_rw [sum_shellGenSiteOp_Icc_L]; dsimp [D_u]
  rw [katoHastingsGeneratorOp_finset_sum hHs hW_int Finset.univ (fun u => sitePerturbationOp V u),
    sum_sitePerturbationOp_eq_V_tot V]

/-- Continuity of `s ↦ (katoGeneratorQuasiLocal ... s).V_tot` on `ℝ`. -/
theorem continuous_katoGeneratorQuasiLocal_V_tot {D L : ℕ} [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH0 : IsSelfAdjoint H0)
    (W : ℝ → ℂ) (hW_int : Integrable W)
    (hW_real : ∀ t : ℝ, star (W t) = W t) (hW_odd : ∀ t : ℝ, W (-t) = - W t)
    (V : QuasiLocalPerturbation D L Site) :
    Continuous (fun s : ℝ =>
      (katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).totalPerturbation) := by
  have h_eq : (fun s : ℝ => (katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).totalPerturbation) =
      fun s : ℝ => katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W V.totalPerturbation := by
    funext s; exact katoGeneratorQuasiLocal_V_tot_eq H0 hH0 W hW_int hW_real hW_odd V s
  rw [h_eq]
  exact continuous_katoHastingsGeneratorOp_interpolated hH0 V.isSelfAdjoint_totalPerturbation hW_int V.totalPerturbation

/-- Norm bound on each cube term of `katoGeneratorQuasiLocal` in terms of the perturbation decay
    profile `f` and `∫ t, ‖W t‖`. -/
theorem norm_katoGeneratorQuasiLocal_term_le {D L : ℕ} [NeZero D] [NeZero L]
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH0 : IsSelfAdjoint H0)
    (W : ℝ → ℂ) (hW_int : Integrable W)
    (hW_real : ∀ t : ℝ, star (W t) = W t) (hW_odd : ∀ t : ℝ, W (-t) = - W t)
    (V : QuasiLocalPerturbation D L Site) {J : ℝ} {f : ℕ → ℝ}
    (hJ : 0 ≤ J) (hf_nn : ∀ q : ℕ, 0 ≤ f q) (hV : V.SatisfiesDecayBound J f) (s : ℝ)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 L) {A : Finset (BoxD D L)} (hA : A ∈ boxCubes D L r) :
    ‖(katoGeneratorQuasiLocal H0 hH0 W hW_int hW_real hW_odd V s).term r A‖ ≤
      J * (2 * ((r : ℝ) ^ D) * (∫ t : ℝ, ‖W t‖) * (∑ q ∈ Finset.Icc 1 L, f q)) := by
  have hHs : IsSelfAdjoint (H0 + s • V.totalPerturbation) :=
    isSelfAdjoint_add_real_smul_kato hH0 V.isSelfAdjoint_totalPerturbation s
  dsimp [katoGeneratorQuasiLocal]; rw [if_pos ⟨hr, hA⟩]
  let S := Finset.univ.filter (fun u : BoxD D L => shellCube u r = A)
  have hW_nn : 0 ≤ ∫ t : ℝ, ‖W t‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
  have hf_sum_nn : 0 ≤ ∑ q ∈ Finset.Icc 1 L, f q := Finset.sum_nonneg (fun q _ => hf_nn q)
  have h_site : ∀ u ∈ S,
      ‖shellGenSiteOp
        (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r‖ ≤
      2 * ((∫ t : ℝ, ‖W t‖) * (J * ∑ q ∈ Finset.Icc 1 L, f q)) := by
    intro u _
    have h1 := norm_shellGenSiteOp_le_two_mul_norm
      (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r
    have h2 := norm_katoHastingsGeneratorOp_le_integral_norm_mul hHs hW_int (sitePerturbationOp V u)
    have h3 : ‖sitePerturbationOp V u‖ ≤ J * ∑ q ∈ Finset.Icc 1 L, f q := by
      rw [sitePerturbationOp_eq_anchoredSitePerturbationOp, anchorOfCube_eq_qacAnchorOfCube]
      exact norm_qacSitePerturbationOp_le V hV u
    exact le_trans h1 (mul_le_mul_of_nonneg_left
      (le_trans h2 (mul_le_mul_of_nonneg_left h3 hW_nn)) zero_le_two)
  have h_card : (S.card : ℝ) ≤ (r : ℝ) ^ D := by
    exact_mod_cast card_filter_shellCube_eq_le_pow (Finset.mem_Icc.mp hr).1 hA
  calc ‖∑ u ∈ S, shellGenSiteOp
          (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r‖
      ≤ ∑ u ∈ S, ‖shellGenSiteOp
          (katoHastingsGeneratorOp (H0 + s • V.totalPerturbation) W (sitePerturbationOp V u)) u r‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _u ∈ S, 2 * ((∫ t : ℝ, ‖W t‖) * (J * ∑ q ∈ Finset.Icc 1 L, f q)) :=
        Finset.sum_le_sum h_site
    _ = (S.card : ℝ) * (2 * ((∫ t : ℝ, ‖W t‖) * (J * ∑ q ∈ Finset.Icc 1 L, f q))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((r : ℝ) ^ D) * (2 * ((∫ t : ℝ, ‖W t‖) * (J * ∑ q ∈ Finset.Icc 1 L, f q))) :=
        mul_le_mul_of_nonneg_right h_card (by positivity)
    _ = J * (2 * ((r : ℝ) ^ D) * (∫ t : ℝ, ‖W t‖) * (∑ q ∈ Finset.Icc 1 L, f q)) := by ring

/-- Decay profile for `katoGeneratorQuasiLocal` on a lattice of side `L`. -/
def katoGeneratorShellDecayProfile (D L : ℕ) (W : ℝ → ℂ) (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  if r ≤ L then 2 * ((r : ℝ) ^ D) * (∫ t : ℝ, ‖W t‖) * (∑ q ∈ Finset.Icc 1 L, f q) else 0

lemma isSuperpolynomialDecay_katoGeneratorShellDecayProfile (D L : ℕ) (W : ℝ → ℂ)
    {f : ℕ → ℝ} (hf : ∀ q : ℕ, 0 ≤ f q) :
    IsSuperpolynomialDecay (katoGeneratorShellDecayProfile D L W f) := by
  refine ⟨fun r => ?_, fun n => ?_⟩
  · dsimp [katoGeneratorShellDecayProfile]; split_ifs
    · have hW_nn : 0 ≤ ∫ t : ℝ, ‖W t‖ := MeasureTheory.integral_nonneg (fun _ => norm_nonneg _)
      have hf_nn : 0 ≤ ∑ q ∈ Finset.Icc 1 L, f q := Finset.sum_nonneg (fun q _ => hf q)
      positivity
    · exact le_refl 0
  · refine tendsto_atTop_of_eventually_const (i₀ := L + 1) (fun r hr => ?_)
    have hnot : ¬ (r ≤ L) := by omega
    simp [katoGeneratorShellDecayProfile, if_neg hnot]

/-- Main existence theorem for the quasi-local decomposition of the Kato–Hastings generator
    with continuation weight `bandpassContinuationWeight`. -/
theorem katoGeneratorQuasiLocal_exists {k L : ℕ} [NeZero L] (hL : L = bdlBoxSide k)
    (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    {J : ℝ} {f : ℕ → ℝ} (hJ : 0 ≤ J) (hJ1 : J ≤ 1)
    (hf : IsSuperpolynomialDecay f) (hV : V.SatisfiesDecayBound J f) :
    ∃ (f_D : ℕ → ℝ)
      (D_loc : ℝ → QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      IsSuperpolynomialDecay f_D ∧
      Continuous (fun s : ℝ => (D_loc s).totalPerturbation) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        (D_loc s).SatisfiesDecayBound J f_D ∧
        (D_loc s).totalPerturbation =
          katoHastingsGeneratorOp (mem.sys.H0 + s • V.totalPerturbation) bandpassContinuationWeight V.totalPerturbation) := by
  refine ⟨katoGeneratorShellDecayProfile 3 L bandpassContinuationWeight f,
    katoGeneratorQuasiLocal mem.sys.H0 mem.sys.isSelfAdjoint_H0
      bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V,
    isSuperpolynomialDecay_katoGeneratorShellDecayProfile 3 L bandpassContinuationWeight hf.1,
    continuous_katoGeneratorQuasiLocal_V_tot mem.sys.H0 mem.sys.isSelfAdjoint_H0
      bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V,
    fun s _ => ⟨fun r hr A hA => ?_, katoGeneratorQuasiLocal_V_tot_eq mem.sys.H0 mem.sys.isSelfAdjoint_H0
      bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V s⟩⟩
  dsimp [katoGeneratorShellDecayProfile]; rw [if_pos (Finset.mem_Icc.mp hr).2]
  exact norm_katoGeneratorQuasiLocal_term_le mem.sys.H0 mem.sys.isSelfAdjoint_H0
    bandpassContinuationWeight integrable_W_BP star_W_BP bandpassContinuationWeight_odd V hJ hf.1 hV s hr hA

end
