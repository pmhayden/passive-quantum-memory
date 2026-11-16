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

import Proofs.KMSSafeSubspaceODE.KMSDissipativeGeneratorAndGronwall
import Proofs.KMSSafeSubspaceODE.KMSFourthRootAndPinchedGibbs
import Proofs.TwoAxisMemorySynthesis.DaviesGKLSCompletePositivity

open scoped Classical InnerProduct ComplexConjugate BigOperators
open ContinuousLinearMap

noncomputable section

/-!
# GKLS Davies Thermal Generator Bridge, Cube Locality of Bohr Eigenoperators, and CPTP Unperturbed Lifetime

Formalizes Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(i)–(ii)
(`thm:unperturbed-kms-lifetime`) and Part II, Theorem 6.5(1) (`thm:main-D`):
1. Under `sys.IsGeometricallyLocal r_0 w_0` and unit check weights `∀ i, sys.weight i = 1`,
   every single-site Hermitian coupling `c : SingleSiteThermalCoupling D L_box Site β` has Bohr
   eigenoperators `bohrEigenop sys c.S ω` vanishing for `|ω| > w_0`, obeying `‖bohrEigenop sys c.S ω‖ ≤ ‖c.S‖`,
   satisfying `[H_0, A_ω] = -ω A_ω` and `(A_ω)† = A_{-ω}`, and supported inside an open-box cube
   `daviesEnclosingCube r_0 c.v` of side `min (4 * r_0 + 1) L_box` (`37` at `r_0 = 9`);
2. Grouping `(c, ω) ∈ couplings ×ˢ Icc (-w_0) w_0` by `(support, L)` yields a finite channel family
   `daviesBathChannels` satisfying `IsCubeRangeBath D L_box (4 * r_0 + 1)` and `IsAdjointSymmetricBath`,
   on which `opDaviesThermalGenerator` coincides identically with `opKMSLindbladGenerator`;
3. `opDaviesThermalSemigroup` is unital, $\dagger$-preserving, completely positive (`IsCPUnitalStarMap`),
   leaves `gibbsDensityOp` stationary, solves `SatisfiesDaviesThermalODE`, and obeys both
   stretched-exponential KMS lifetime bounds at $V = 0$.

## References

* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8(i)–(ii) (`thm:unperturbed-kms-lifetime`)
* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.5(1) (`thm:main-D`)
-/

/-- Open-box cube of side `min (4 * r_0 + 1) L_box` enclosing `boxBall v (2 * r_0)` on `BoxD D L_box`. -/
def daviesEnclosingCube {D L_box : ℕ} [NeZero L_box] (r_0 : ℕ) (v : BoxD D L_box) :
    Finset (BoxD D L_box) :=
  if 4 * r_0 + 1 ≤ L_box then
    boxCube (fun μ : Fin D => ⟨(v μ).val - 2 * r_0, Nat.sub_lt_of_lt (v μ).isLt⟩) (4 * r_0 + 1)
  else
    boxCube (fun _ : Fin D => ⟨0, NeZero.pos L_box⟩) L_box

/-- Fiberwise-summed `BathChannel` family $\mathcal{B}_{\mathrm{Davies}}$ associated to a finite set of
    single-site KMS thermal couplings `couplings` (summing KMS rates $\gamma_{c}(\omega) = e^{-\beta\omega/2} h_c(\omega)$
    over any pairs `(c, ω)` sharing the same enclosing cube and Bohr jump operator). -/
def daviesBathChannels {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (r_0 w_0 : ℕ) (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β)) :
    Finset (BathChannel D L_box Site) :=
  let idx := couplings ×ˢ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ)
  let pairs := idx.image (fun p => (daviesEnclosingCube r_0 p.1.v, bohrEigenop sys p.1.S p.2))
  pairs.image (fun wl =>
    { L := wl.2
      support := wl.1
      γ := ∑ p ∈ idx.filter (fun p =>
            daviesEnclosingCube r_0 p.1.v = wl.1 ∧ bohrEigenop sys p.1.S p.2 = wl.2),
            Real.exp (-β * (p.2 : ℝ) / 2) * p.1.h_spec p.2 })

private lemma min_four_mul_add_one_mem_Icc {L_box : ℕ} [NeZero L_box] (r_0 : ℕ) :
    min (4 * r_0 + 1) L_box ∈ Finset.Icc 1 (min (4 * r_0 + 1) L_box) := by
  rw [Finset.mem_Icc]
  exact ⟨Nat.le_min.mpr ⟨by omega, Nat.succ_le_of_lt (NeZero.pos L_box)⟩, le_rfl⟩

/-! ### Helper Section 1: Spectral Eigenspace Projections and Local/External Check Sums -/

private lemma rankOneKetBra_adjoint_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (φ : E) : (rankOneKetBra φ)† = rankOneKetBra φ := by
  apply ContinuousLinearMap.ext; intro ψ; apply ext_inner_left ℂ; intro χ
  rw [ContinuousLinearMap.adjoint_inner_right, rankOneKetBra_apply, rankOneKetBra_apply,
    inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

private lemma clm_smul_mul_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a : ℂ) (A B : E →L[ℂ] E) : (a • A) * B = a • (A * B) := by ext φ; simp

private lemma clm_mul_smul_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A B : E →L[ℂ] E) (a : ℂ) : A * (a • B) = a • (A * B) := by ext φ; simp

private lemma clm_zero_smul_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) : (0 : ℂ) • A = 0 := by ext φ; simp

private lemma clm_smul_zero_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) : c • (0 : E →L[ℂ] E) = 0 := by ext φ; simp

private lemma clm_add_smul_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : ℂ) (A : E →L[ℂ] E) : (a + b) • A = a • A + b • A := by ext φ; exact add_smul a b (A φ)

private lemma clm_sum_smul_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {α : Type*} (s : Finset α) (f : α → ℂ) (A : E →L[ℂ] E) :
    (∑ a ∈ s, f a) • A = ∑ a ∈ s, f a • A := by
  ext φ; simp [Finset.sum_smul]

private lemma clm_neg_smul_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c : ℂ) (A : E →L[ℂ] E) : (-c) • A = -(c • A) := by ext φ; exact neg_smul c (A φ)

private lemma clm_smul_sum_davies {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {α : Type*} (c : ℂ) (s : Finset α) (f : α → (E →L[ℂ] E)) :
    c • ∑ a ∈ s, f a = ∑ a ∈ s, c • f a := by
  ext φ; simp [Finset.smul_sum]

private lemma gkls_kms_single_channel_algebra {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (r e1 e2 h1 h2 : ℂ) (hr1 : r * e1 = h1) (hr2 : r * e2 = h2)
    (A X : E →L[ℂ] E) :
    (-(1 / 2 : ℂ)) • (r • (e1 • (A† * A * X - A† * X * A) - e2 • (A * X * A† - X * A * A†))) =
      (1 / 2 : ℂ) • (h1 • (A† * X * A - A† * A * X)) +
      (1 / 2 : ℂ) • (h2 • ((A†)† * X * A† - X * ((A†)† * A†))) := by
  rw [ContinuousLinearMap.adjoint_adjoint, ← mul_assoc X A (A†)]
  ext φ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply]
  rw [smul_sub, smul_smul, smul_smul, hr1, hr2, neg_smul, smul_sub, neg_sub,
    sub_eq_add_neg, ← smul_neg, ← smul_neg, neg_sub, add_comm]

private lemma gkls_anticommutator_combine {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (h : ℂ) (U V₁ V₂ : E →L[ℂ] E) :
    (1 / 2 : ℂ) • (h • (U - V₁)) + (1 / 2 : ℂ) • (h • (U - V₂)) =
      h • (U - (1 / 2 : ℂ) • (V₁ + V₂)) := by
  ext φ
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply]
  rw [← smul_add, ← smul_add, smul_comm (1 / 2 : ℂ) h]
  congr 1
  have h_ab : (U φ - V₁ φ) + (U φ - V₂ φ) = (U φ + U φ) - (V₁ φ + V₂ φ) := by abel
  rw [h_ab, smul_sub, ← two_smul ℂ (U φ), smul_smul]
  norm_num

private lemma isSupportedOn_add_local {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (B : Finset (BoxD D L_box))
    {O₁ O₂ : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (h₁ : IsSupportedOn Site B O₁) (h₂ : IsSupportedOn Site B O₂) :
    IsSupportedOn Site B (O₁ + O₂) := by
  rcases h₁ with ⟨L₁, rfl⟩; rcases h₂ with ⟨L₂, rfl⟩
  exact ⟨L₁ + L₂, by ext ψ σ; rfl⟩

private lemma isSupportedOn_finset_sum_local {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {α : Type*} (B : Finset (BoxD D L_box)) (s : Finset α)
    (f : α → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (hf : ∀ a ∈ s, IsSupportedOn Site B (f a)) :
    IsSupportedOn Site B (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [KMSPinchedGibbs.isSupportedOn_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isSupportedOn_add_local B (hf a (Finset.mem_insert_self a s))
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))

private lemma spectralEigenspaceProj_isStarProjection {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (E : ℝ) :
    IsStarProjection (spectralEigenspaceProj H hH E) := by
  have h_onb := opEigenbasis_orthonormal H hH
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem]
    unfold spectralEigenspaceProj
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ₁ hτ₁ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single τ₁]
    · simp [onb_ketBra_mul_ketBra _ h_onb]
    · intro τ₂ _ hne; simp [onb_ketBra_mul_ketBra _ h_onb, hne.symm]
    · intro h_not; exact False.elim (h_not hτ₁)
  · rw [ContinuousLinearMap.isSelfAdjoint_iff']
    unfold spectralEigenspaceProj
    rw [map_sum]
    exact Finset.sum_congr rfl fun τ _ => rankOneKetBra_adjoint_self _

private lemma spectralEigenspaceProj_mul_spectralEigenspaceProj {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (E₁ E₂ : ℝ) :
    spectralEigenspaceProj H hH E₁ * spectralEigenspaceProj H hH E₂ =
      if E₁ = E₂ then spectralEigenspaceProj H hH E₁ else 0 := by
  split_ifs with h_eq
  · subst h_eq; exact (spectralEigenspaceProj_isStarProjection H hH E₁).isIdempotentElem.eq
  · unfold spectralEigenspaceProj
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun τ₁ hτ₁ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun τ₂ hτ₂ => ?_
    have hne : τ₁ ≠ τ₂ := by
      intro h_same; subst h_same
      exact h_eq ((Finset.mem_filter.mp hτ₁).2.symm.trans (Finset.mem_filter.mp hτ₂).2)
    simp [onb_ketBra_mul_ketBra _ (opEigenbasis_orthonormal H hH), hne]

private lemma H_mul_spectralEigenspaceProj {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (E : ℝ) :
    H * spectralEigenspaceProj H hH E = (E : ℂ) • spectralEigenspaceProj H hH E ∧
    spectralEigenspaceProj H hH E * H = (E : ℂ) • spectralEigenspaceProj H hH E := by
  unfold spectralEigenspaceProj
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [(opEigenbasis_ketBra_props H hH τ).1, (Finset.mem_filter.mp hτ).2]
  · rw [Finset.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ hτ => ?_
    rw [(opEigenbasis_ketBra_props H hH τ).2.1, (Finset.mem_filter.mp hτ).2]

private lemma spectralEigenspaceProj_mul_of_eig {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (E ev : ℝ)
    (M : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hM : H * M = (ev : ℂ) • M) :
    spectralEigenspaceProj H hH E * M = if ev = E then M else 0 := by
  have hH_adj : H† = H := ContinuousLinearMap.isSelfAdjoint_iff'.mp hH
  have h_orth : ∀ (τ : ManyBodyConfig Site) (φ : ManyBodyHilbertSpace Site),
      opEigenvalues H hH τ ≠ ev →
      rankOneKetBra (opEigenbasis H hH τ) (M φ) = 0 := by
    intro τ φ hne
    have h1 : inner ℂ (opEigenbasis H hH τ) (H (M φ)) =
        (ev : ℂ) * inner ℂ (opEigenbasis H hH τ) (M φ) := by
      change inner ℂ _ ((H * M) φ) = _
      rw [hM, ContinuousLinearMap.smul_apply, inner_smul_right]
    have h2 : inner ℂ (opEigenbasis H hH τ) (H (M φ)) =
        (opEigenvalues H hH τ : ℂ) * inner ℂ (opEigenbasis H hH τ) (M φ) := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hH_adj, opEigenbasis_apply_H H hH τ,
        inner_smul_left, Complex.conj_ofReal]
    have h_sub : ((opEigenvalues H hH τ - ev : ℝ) : ℂ) *
        inner ℂ (opEigenbasis H hH τ) (M φ) = 0 := by
      push_cast; linear_combination h2.symm.trans h1
    have h_ne_c : ((opEigenvalues H hH τ - ev : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr hne
    have h_in : inner ℂ (opEigenbasis H hH τ) (M φ) = 0 :=
      (mul_eq_zero.mp h_sub).resolve_left h_ne_c
    rw [rankOneKetBra_apply, h_in, zero_smul]
  apply ContinuousLinearMap.ext; intro φ
  change (spectralEigenspaceProj H hH E) (M φ) = (if ev = E then M else 0) φ
  unfold spectralEigenspaceProj
  rw [ContinuousLinearMap.sum_apply]
  split_ifs with h_eq
  · subst h_eq
    have h_full := onb_sum_ketBra_eq_one (opEigenbasis H hH)
      (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
    have h_compl : (∑ τ ∈ Finset.univ.filter (fun τ => opEigenvalues H hH τ = ev),
        rankOneKetBra (opEigenbasis H hH τ) (M φ)) =
        ∑ τ : ManyBodyConfig Site, rankOneKetBra (opEigenbasis H hH τ) (M φ) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro τ _ h_not
      rw [Finset.mem_filter] at h_not
      exact h_orth τ φ (fun h_e => h_not ⟨Finset.mem_univ τ, h_e⟩)
    rw [h_compl, ← ContinuousLinearMap.sum_apply, h_full, ContinuousLinearMap.one_apply]
  · refine Finset.sum_eq_zero fun τ hτ => ?_
    exact h_orth τ φ (by rw [(Finset.mem_filter.mp hτ).2]; exact Ne.symm h_eq)

private lemma commute_spectralEigenspaceProj_of_commute {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (E : ℝ)
    {B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hB : Commute B H) :
    Commute B (spectralEigenspaceProj H hH E) := by
  let P := spectralEigenspaceProj H hH E
  have hHP := (H_mul_spectralEigenspaceProj H hH E).1
  have hP_sa : star P = P := (spectralEigenspaceProj_isStarProjection H hH E).isSelfAdjoint.star_eq
  have hH_sa : star H = H := hH.star_eq
  have h_left : ∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      Commute X H → P * (X * P) = X * P := by
    intro X hX
    have h_eig : H * (X * P) = (E : ℂ) • (X * P) := by
      rw [← mul_assoc, hX.symm.eq, mul_assoc, hHP, clm_mul_smul_davies]
    simpa [P] using spectralEigenspaceProj_mul_of_eig H hH E E (X * P) h_eig
  have hB_adj_comm : Commute (star B) H := by
    rw [commute_iff_eq]
    calc star B * H = star B * star H := by rw [hH_sa]
      _ = star (H * B) := (star_mul H B).symm
      _ = star (B * H) := by rw [hB.eq]
      _ = star H * star B := star_mul B H
      _ = H * star B := by rw [hH_sa]
  have h1 : P * (B * P) = B * P := h_left B hB
  have h2 : P * (star B * P) = star B * P := h_left (star B) hB_adj_comm
  have h2_adj : P * B = P * (B * P) := by
    have h_st := congrArg star h2
    simp only [star_mul, star_star, hP_sa, mul_assoc] at h_st
    exact h_st.symm
  rw [commute_iff_eq]
  exact h1.symm.trans h2_adj.symm

private lemma checkSum_spectralEigenspaceProj_props {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (I : Finset ι) (W : Finset (BoxD D L_box))
    (hW : ∀ i ∈ I, IsSupportedOn Site W (sys.checkProj i)) :
    let H_I := ∑ i ∈ I, sys.checkProj i
    let hH_I : IsSelfAdjoint H_I :=
      isSelfAdjoint_finset_sum I _ fun i _ => (sys.is_projector i).isSelfAdjoint
    (∀ m : ℤ, ¬(0 ≤ m ∧ m ≤ (I.card : ℤ)) →
      spectralEigenspaceProj H_I hH_I (m : ℝ) = 0) ∧
    (∀ m : ℤ, IsSupportedOn Site W (spectralEigenspaceProj H_I hH_I (m : ℝ))) ∧
    (∑ m ∈ Finset.Icc (0 : ℤ) (I.card : ℤ),
      spectralEigenspaceProj H_I hH_I (m : ℝ)) = 1 := by
  have h_res : ∃ P : ℕ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      (∀ k, I.card < k → P k = 0) ∧
      (∀ k, IsSupportedOn Site W (P k)) ∧
      (∑ k ∈ Finset.range (I.card + 1), P k) = 1 ∧
      (∀ k, (∑ i ∈ I, sys.checkProj i) * P k = (k : ℂ) • P k) := by
    revert hW
    induction I using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨fun k => if k = 0 then 1 else 0, fun k hk => ite_eq_right_iff.mpr fun h => by omega,
        fun k => by dsimp only; split_ifs; exacts [KMSPinchedGibbs.isSupportedOn_one W,
          KMSPinchedGibbs.isSupportedOn_zero W],
        by simp, fun k => by
          dsimp only
          split_ifs with hk
          · subst hk
            simp only [Finset.sum_empty, zero_mul, Nat.cast_zero, clm_zero_smul_davies]
          · simp only [Finset.sum_empty, zero_mul, clm_smul_zero_davies]⟩
    | @insert i₀ I hi₀ ih =>
      intro hW
      rcases ih (fun i hi => hW i (Finset.mem_insert_of_mem hi)) with
        ⟨P, hP_van, hP_supp, hP_sum, hP_eig⟩
      let Q₀ := sys.checkProj i₀
      have hQ₀_proj := sys.is_projector i₀
      have hQ₀_supp := hW i₀ (Finset.mem_insert_self i₀ I)
      have hH_comm : Commute (∑ i ∈ I, sys.checkProj i) Q₀ :=
        Commute.sum_left _ _ _ fun i _ => sys.pairwise_commute i i₀
      let P' : ℕ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
        fun k => (1 - Q₀) * P k + (if k = 0 then 0 else Q₀ * P (k - 1))
      refine ⟨P', ?_, ?_, ?_, ?_⟩
      · intro k hk
        rw [Finset.card_insert_of_notMem hi₀] at hk
        dsimp [P']
        rw [hP_van k (by omega), mul_zero, zero_add]
        split_ifs with hk0
        · rfl
        · rw [hP_van (k - 1) (by omega), mul_zero]
      · intro k
        dsimp [P']
        refine isSupportedOn_add_local W
          (KMSPinchedGibbs.isSupportedOn_mul W
            (KMSPinchedGibbs.isSupportedOn_sub W (KMSPinchedGibbs.isSupportedOn_one W) hQ₀_supp)
            (hP_supp k)) ?_
        split_ifs
        · exact KMSPinchedGibbs.isSupportedOn_zero W
        · exact KMSPinchedGibbs.isSupportedOn_mul W hQ₀_supp (hP_supp (k - 1))
      · rw [Finset.card_insert_of_notMem hi₀]
        dsimp [P']
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_succ,
          hP_van (I.card + 1) (by omega), add_zero, hP_sum, mul_one,
          Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, add_zero]
        rw [← Finset.mul_sum, hP_sum, mul_one, sub_add_cancel]
      · intro k
        rw [Finset.sum_insert hi₀]
        change (Q₀ + ∑ i ∈ I, sys.checkProj i) * P' k = (k : ℂ) • P' k
        have hQ_sub : Q₀ * (1 - Q₀) = 0 := by
          rw [mul_sub, mul_one, hQ₀_proj.isIdempotentElem.eq, sub_self]
        have h1 : (Q₀ + ∑ i ∈ I, sys.checkProj i) * ((1 - Q₀) * P k) =
            (k : ℂ) • ((1 - Q₀) * P k) := by
          rw [add_mul, ← mul_assoc, hQ_sub, zero_mul, zero_add, ← mul_assoc,
            (Commute.sub_right (Commute.one_right _) hH_comm).eq, mul_assoc,
            hP_eig k, clm_mul_smul_davies]
        dsimp only [P']
        rw [mul_add, h1]
        split_ifs with hk0
        · subst hk0; simp
        · rw [add_mul, ← mul_assoc, hQ₀_proj.isIdempotentElem.eq, ← mul_assoc,
            hH_comm.eq, mul_assoc, hP_eig (k - 1), clm_mul_smul_davies, smul_add]
          congr 1
          have hk_cast : (1 : ℂ) + ((k - 1 : ℕ) : ℂ) = (k : ℂ) := by
            norm_cast; omega
          rw [← hk_cast, add_smul, one_smul]
  rcases h_res with ⟨P, hP_van, hP_supp, hP_sum, hP_eig⟩
  intro H_I hH_I
  have h_eq_P : ∀ m : ℤ,
      spectralEigenspaceProj H_I hH_I (m : ℝ) =
        if 0 ≤ m ∧ m ≤ (I.card : ℤ) then P m.toNat else 0 := by
    intro m
    calc spectralEigenspaceProj H_I hH_I (m : ℝ)
      _ = spectralEigenspaceProj H_I hH_I (m : ℝ) * ∑ k ∈ Finset.range (I.card + 1), P k := by
        rw [hP_sum, mul_one]
      _ = ∑ k ∈ Finset.range (I.card + 1),
          (if (k : ℝ) = (m : ℝ) then P k else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact spectralEigenspaceProj_mul_of_eig H_I hH_I (m : ℝ) (k : ℝ) (P k) (hP_eig k)
      _ = if 0 ≤ m ∧ m ≤ (I.card : ℤ) then P m.toNat else 0 := by
        split_ifs with hm
        · rw [Finset.sum_eq_single m.toNat]
          · have hm_eq : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
              exact_mod_cast Int.toNat_of_nonneg hm.1
            rw [if_pos hm_eq]
          · intro k _ hk_ne
            rw [if_neg]
            intro hk_eq
            have hk_int : (k : ℤ) = m := by exact_mod_cast hk_eq
            exact hk_ne (by omega)
          · intro h_not
            exact False.elim (h_not (Finset.mem_range.mpr (by omega)))
        · refine Finset.sum_eq_zero fun k hk => ?_
          rw [if_neg]
          intro hk_eq
          have hk_int : (k : ℤ) = m := by exact_mod_cast hk_eq
          rw [Finset.mem_range] at hk
          omega
  refine ⟨fun m hm => by rw [h_eq_P m, if_neg hm],
    fun m => by
      rw [h_eq_P m]; split_ifs; exacts [hP_supp _, KMSPinchedGibbs.isSupportedOn_zero W],
    ?_⟩
  rw [← hP_sum]
  apply Finset.sum_bij (fun (m : ℤ) _ => m.toNat)
  · intro m hm; rw [Finset.mem_Icc] at hm; rw [Finset.mem_range]; omega
  · intro m₁ hm₁ m₂ hm₂ h_eq; rw [Finset.mem_Icc] at hm₁ hm₂; omega
  · intro k hk; rw [Finset.mem_range] at hk
    exact ⟨(k : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Int.toNat_natCast k⟩
  · intro m hm; rw [Finset.mem_Icc] at hm; rw [h_eq_P m, if_pos hm]

private lemma daviesEnclosingCube_mem_and_superset {D L_box : ℕ} [NeZero L_box]
    (r_0 : ℕ) (v : BoxD D L_box) :
    daviesEnclosingCube r_0 v ∈ boxCubes D L_box (min (4 * r_0 + 1) L_box) ∧
    boxBall v (2 * r_0) ⊆ daviesEnclosingCube r_0 v ∧
    ({v} : Finset (BoxD D L_box)) ⊆ daviesEnclosingCube r_0 v := by
  have hv_ball : v ∈ boxBall v (2 * r_0) := by
    simp [boxBall, boxDist, coordDist_self]
  suffices h_main :
      daviesEnclosingCube r_0 v ∈ boxCubes D L_box (min (4 * r_0 + 1) L_box) ∧
      boxBall v (2 * r_0) ⊆ daviesEnclosingCube r_0 v by
    exact ⟨h_main.1, h_main.2, Finset.singleton_subset_iff.mpr (h_main.2 hv_ball)⟩
  unfold daviesEnclosingCube
  split_ifs with h_le
  · rw [Nat.min_eq_left h_le]
    refine ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    intro y hy
    simp only [boxBall, boxCube, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro μ
    have hμ : coordDist (v μ) (y μ) ≤ boxDist v y :=
      Finset.le_sup (f := fun j => coordDist (v j) (y j)) (Finset.mem_univ μ)
    have hμ2 : coordDist (v μ) (y μ) ≤ 2 * r_0 := le_trans hμ hy
    dsimp [coordDist] at hμ2
    omega
  · rw [Nat.min_eq_right (le_of_not_ge h_le)]
    refine ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    intro y _
    simp only [boxCube, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun μ => ⟨Nat.zero_le _, by omega⟩

private lemma norm_sq_sum_of_pairwise_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {α : Type*} (s : Finset α) (f : α → E)
    (h_orth : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → inner ℂ (f a) (f b) = 0) :
    ‖∑ a ∈ s, f a‖ ^ 2 = ∑ a ∈ s, ‖f a‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_inner_zero : inner ℂ (f a) (∑ b ∈ s, f b) = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun b hb =>
        h_orth a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
          (fun h_eq => ha (h_eq ▸ hb))
    rw [norm_add_sq (𝕜 := ℂ), h_inner_zero, map_zero, mul_zero, add_zero,
      ih (fun x hx y hy hne =>
        h_orth x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hne)]

private lemma bohrEigenop_eq_local_check_sum {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    (h_unit : ∀ i : ι, sys.weight i = 1)
    {β : ℝ} (c : SingleSiteThermalCoupling D L_box Site β) (ω : ℤ) :
    let I_loc := Finset.univ.filter (fun i : ι => c.v ∈ sys.support i)
    let H_loc := ∑ i ∈ I_loc, sys.checkProj i
    let hH_loc : IsSelfAdjoint H_loc :=
      isSelfAdjoint_finset_sum I_loc _ fun i _ => (sys.is_projector i).isSelfAdjoint
    bohrEigenop sys c.S ω =
      ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
        if 0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ) then
          spectralEigenspaceProj H_loc hH_loc ((m - ω : ℤ) : ℝ) * c.S *
            spectralEigenspaceProj H_loc hH_loc (m : ℝ)
        else 0 := by
  intro I_loc H_loc hH_loc
  let I_ext := Finset.univ.filter (fun i : ι => c.v ∉ sys.support i)
  let H_ext := ∑ i ∈ I_ext, sys.checkProj i
  have hH_ext : IsSelfAdjoint H_ext :=
    isSelfAdjoint_finset_sum I_ext _ fun i _ => (sys.is_projector i).isSelfAdjoint
  have h_card : I_loc.card + I_ext.card = Fintype.card ι := by
    have h1 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι)
      (fun i => c.v ∈ sys.support i) (fun _ => (1 : ℕ))
    simpa [I_loc, I_ext] using h1
  have hH0_split : sys.H0 = H_loc + H_ext := by
    unfold IndexedCommutingProjectorHamiltonian.H0
    simp_rw [h_unit, Complex.ofReal_one, one_smul]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i => c.v ∈ sys.support i) sys.checkProj).symm
  have h_comm_loc_ext : Commute H_loc H_ext :=
    Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => sys.pairwise_commute i j
  have hS_comm_ext : Commute c.S H_ext := by
    refine Commute.sum_right _ _ _ fun i hi => ?_
    have h_disj : Disjoint ({c.v} : Finset (BoxD D L_box)) (sys.support i) :=
      Finset.disjoint_singleton_left.mpr (Finset.mem_filter.mp hi).2
    exact KMSPinchedGibbs.commute_of_isSupportedOn_disjoint h_disj c.isSupported_S (sys.is_supported i)
  have h_loc_props := checkSum_spectralEigenspaceProj_props sys I_loc Finset.univ
    (fun i _ => KMSPinchedGibbs.isSupportedOn_mono (Finset.subset_univ _) (sys.is_supported i))
  have h_ext_props := checkSum_spectralEigenspaceProj_props sys I_ext Finset.univ
    (fun i _ => KMSPinchedGibbs.isSupportedOn_mono (Finset.subset_univ _) (sys.is_supported i))
  let P_loc : ℤ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun m => spectralEigenspaceProj H_loc hH_loc (m : ℝ)
  let P_ext : ℤ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun n => spectralEigenspaceProj H_ext hH_ext (n : ℝ)
  have hP_tot : ∀ E : ℤ,
      spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ) =
        ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), P_loc m * P_ext (E - m) := by
    intro E
    calc spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ)
      _ = spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ) *
            ((∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), P_loc m) *
              (∑ n ∈ Finset.Icc (0 : ℤ) (I_ext.card : ℤ), P_ext n)) := by
        rw [h_loc_props.2.2, h_ext_props.2.2, mul_one, mul_one]
      _ = ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
            ∑ n ∈ Finset.Icc (0 : ℤ) (I_ext.card : ℤ),
              spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ) * (P_loc m * P_ext n) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), P_loc m * P_ext (E - m) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        have h_term : ∀ n ∈ Finset.Icc (0 : ℤ) (I_ext.card : ℤ),
            spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ) * (P_loc m * P_ext n) =
              if ((m + n : ℤ) : ℝ) = (E : ℝ) then P_loc m * P_ext n else 0 := by
          intro n _
          have h_eig : sys.H0 * (P_loc m * P_ext n) = ((m + n : ℤ) : ℂ) • (P_loc m * P_ext n) := by
            have hc : Commute H_ext (P_loc m) :=
              commute_spectralEigenspaceProj_of_commute H_loc hH_loc (m : ℝ) h_comm_loc_ext.symm
            rw [hH0_split, add_mul, ← mul_assoc, (H_mul_spectralEigenspaceProj H_loc hH_loc (m : ℝ)).1,
              clm_smul_mul_davies, ← mul_assoc, hc.eq, mul_assoc,
              (H_mul_spectralEigenspaceProj H_ext hH_ext (n : ℝ)).1, clm_mul_smul_davies]
            have hmnc : ((m + n : ℤ) : ℂ) = ((m : ℝ) : ℂ) + ((n : ℝ) : ℂ) := by push_cast; rfl
            rw [hmnc, clm_add_smul_davies]
          simpa using spectralEigenspaceProj_mul_of_eig sys.H0 sys.isSelfAdjoint_H0
            (E : ℝ) ((m + n : ℤ) : ℝ) (P_loc m * P_ext n) h_eig
        rw [Finset.sum_congr rfl h_term]
        by_cases hn_mem : 0 ≤ E - m ∧ E - m ≤ (I_ext.card : ℤ)
        · rw [Finset.sum_eq_single (E - m)]
          · have h_add : ((m + (E - m) : ℤ) : ℝ) = (E : ℝ) := by exact_mod_cast (by omega : m + (E - m) = E)
            rw [ite_eq_left_iff.mpr fun h => absurd h_add h]
          · intro n _ hne
            rw [ite_eq_right_iff.mpr]
            intro h_eq; have : m + n = E := by exact_mod_cast h_eq
            exact False.elim (hne (by omega))
          · intro h_not; exact False.elim (h_not (Finset.mem_Icc.mpr hn_mem))
        · have hP_ext_zero : P_ext (E - m) = 0 := h_ext_props.1 (E - m) hn_mem
          rw [Finset.sum_eq_zero, hP_ext_zero, mul_zero]
          intro n hn
          rw [Finset.mem_Icc] at hn
          rw [ite_eq_right_iff.mpr]
          intro h_eq; have : m + n = E := by exact_mod_cast h_eq
          exact False.elim (hn_mem ⟨by omega, by omega⟩)
  unfold bohrEigenop
  have h_each_E : ∀ E ∈ Finset.Icc (0 : ℤ) (Fintype.card ι : ℤ),
      (if 0 ≤ E - ω ∧ E - ω ≤ (Fintype.card ι : ℤ) then
        spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 ((E - ω : ℤ) : ℝ) * c.S *
          spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ)
      else 0) =
      ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
        if (0 ≤ E - ω ∧ E - ω ≤ (Fintype.card ι : ℤ)) ∧
           (0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ)) then
          (P_loc (m - ω) * c.S * P_loc m) * P_ext (E - m)
        else 0 := by
    intro E _
    split_ifs with hEω
    · rw [hP_tot (E - ω), hP_tot E, Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m hm => ?_
      have h_inner_m' : ∀ m' ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
          P_loc m' * P_ext (E - ω - m') * c.S * (P_loc m * P_ext (E - m)) =
            if m' = m - ω then (P_loc m' * c.S * P_loc m) * P_ext (E - m) else 0 := by
        intro m' _
        have hcS : Commute (P_ext (E - ω - m')) c.S :=
          (commute_spectralEigenspaceProj_of_commute H_ext hH_ext _ hS_comm_ext).symm
        have hcP : Commute (P_ext (E - ω - m')) (P_loc m) :=
          commute_spectralEigenspaceProj_of_commute H_loc hH_loc _
            (commute_spectralEigenspaceProj_of_commute H_ext hH_ext _ h_comm_loc_ext).symm
        calc P_loc m' * P_ext (E - ω - m') * c.S * (P_loc m * P_ext (E - m))
          _ = P_loc m' * (P_ext (E - ω - m') * c.S) * P_loc m * P_ext (E - m) := by simp only [mul_assoc]
          _ = P_loc m' * c.S * (P_ext (E - ω - m') * P_loc m) * P_ext (E - m) := by
            rw [hcS.eq]; simp only [mul_assoc]
          _ = (P_loc m' * c.S * P_loc m) * (P_ext (E - ω - m') * P_ext (E - m)) := by
            rw [hcP.eq]; simp only [mul_assoc]
          _ = if m' = m - ω then (P_loc m' * c.S * P_loc m) * P_ext (E - m) else 0 := by
            dsimp [P_ext]
            rw [spectralEigenspaceProj_mul_spectralEigenspaceProj]
            split_ifs with h1 h2
            · rw [h1]
            · exfalso; have : E - ω - m' = E - m := by exact_mod_cast h1
              exact h2 (by omega)
            · exfalso; exact h1 (by exact_mod_cast (by omega : E - ω - m' = E - m))
            · rw [mul_zero]
      rw [Finset.sum_congr rfl h_inner_m']
      by_cases hmω : 0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ)
      · rw [if_pos ⟨hEω, hmω⟩, Finset.sum_eq_single (m - ω)]
        · simp
        · intro m' _ hne; simp [hne]
        · intro h_not; exact False.elim (h_not (Finset.mem_Icc.mpr hmω))
      · rw [if_neg (fun h => hmω h.2)]
        refine Finset.sum_eq_zero fun m' hm' => ?_
        rw [Finset.mem_Icc] at hm'
        simp [show m' ≠ m - ω by omega]
    · symm; refine Finset.sum_eq_zero fun m _ => if_neg (fun h => hEω h.1)
  rw [Finset.sum_congr rfl h_each_E, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  by_cases hmω : 0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ)
  · rw [if_pos hmω]
    have h_sum_E : (∑ E ∈ Finset.Icc (0 : ℤ) (Fintype.card ι : ℤ),
        if (0 ≤ E - ω ∧ E - ω ≤ (Fintype.card ι : ℤ)) ∧
           (0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ)) then
          (P_loc (m - ω) * c.S * P_loc m) * P_ext (E - m)
        else 0) =
        (P_loc (m - ω) * c.S * P_loc m) *
          ∑ n ∈ Finset.Icc (0 : ℤ) (I_ext.card : ℤ), P_ext n := by
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_bij_ne_zero (fun (n : ℤ) _ _ => m + n) ?_ ?_ ?_ ?_
      · intro n hn _; rw [Finset.mem_Icc] at hn ⊢; omega
      · intro n₁ _ _ n₂ _ _ h_eq; omega
      · intro E hE h_ne
        by_cases hn_range : 0 ≤ E - m ∧ E - m ≤ (I_ext.card : ℤ)
        · refine ⟨E - m, Finset.mem_Icc.mpr hn_range, ?_, by omega⟩
          intro h_zero
          apply h_ne
          split_ifs
          · rw [show E - m = E - m from rfl, h_zero]
          · rfl
        · exfalso; apply h_ne
          split_ifs
          · dsimp [P_ext]; rw [h_ext_props.1 (E - m) hn_range, mul_zero]
          · rfl
      · intro n hn _
        rw [Finset.mem_Icc] at hn
        have h_cond : (0 ≤ m + n - ω ∧ m + n - ω ≤ (Fintype.card ι : ℤ)) ∧
            (0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ)) := ⟨⟨by omega, by omega⟩, hmω⟩
        rw [if_pos h_cond, show m + n - m = n by omega]
    have hP_ext_sum : ∑ n ∈ Finset.Icc (0 : ℤ) (I_ext.card : ℤ), P_ext n = 1 := h_ext_props.2.2
    rw [h_sum_E, hP_ext_sum, mul_one]
  · rw [if_neg hmω]
    exact Finset.sum_eq_zero fun E _ => if_neg (fun h => hmω h.2)

/-- **Local Check Decomposition, Norm Contraction, and `(4 * r_0 + 1)`-Cube Support of Bohr Eigenoperators
    (Part I, Theorem 5.8(ii) (`thm:unperturbed-kms-lifetime`))**:
    Under `sys.IsGeometricallyLocal r_0 w_0` (`1 ≤ r_0`) and unit check weights `∀ i, sys.weight i = 1`,
    every single-site Hermitian coupling `c` satisfies:
    1. `[sys.H0, bohrEigenop sys c.S ω] = -ω • bohrEigenop sys c.S ω` and `(bohrEigenop sys c.S ω)† = bohrEigenop sys c.S (-ω)`;
    2. `bohrEigenop sys c.S ω = 0` for `|ω| > w_0`;
    3. `‖bohrEigenop sys c.S ω‖ ≤ ‖c.S‖`;
    4. `daviesEnclosingCube r_0 c.v ∈ boxCubes D L_box (min (4 * r_0 + 1) L_box)` and
       `IsSupportedOn Site (daviesEnclosingCube r_0 c.v) (bohrEigenop sys c.S ω)`. -/
theorem bohrEigenop_locality_and_norm_bound {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    {r_0 w_0 : ℕ} (h_loc : sys.IsGeometricallyLocal r_0 w_0)
    (h_unit : ∀ i : ι, sys.weight i = 1)
    {β : ℝ} (c : SingleSiteThermalCoupling D L_box Site β) :
    (∀ ω : ℤ,
      opCommutator sys.H0 (bohrEigenop sys c.S ω) = (-(ω : ℂ)) • bohrEigenop sys c.S ω ∧
      (bohrEigenop sys c.S ω)† = bohrEigenop sys c.S (-ω)) ∧
    (∀ ω : ℤ, ω ∉ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ) → bohrEigenop sys c.S ω = 0) ∧
    (∀ ω : ℤ, ‖bohrEigenop sys c.S ω‖ ≤ ‖c.S‖) ∧
    (min (4 * r_0 + 1) L_box ∈ Finset.Icc 1 (min (4 * r_0 + 1) L_box) ∧
      daviesEnclosingCube r_0 c.v ∈ boxCubes D L_box (min (4 * r_0 + 1) L_box) ∧
      ∀ ω : ℤ, IsSupportedOn Site (daviesEnclosingCube r_0 c.v) (bohrEigenop sys c.S ω)) := by
  let W := daviesEnclosingCube r_0 c.v
  have hW_cube := daviesEnclosingCube_mem_and_superset r_0 c.v
  let I_loc := Finset.univ.filter (fun i : ι => c.v ∈ sys.support i)
  have hI_card : I_loc.card ≤ w_0 := h_loc.2 c.v
  have hI_supp : ∀ i ∈ I_loc, IsSupportedOn Site W (sys.checkProj i) := by
    intro i hi
    have hv_in : c.v ∈ sys.support i := (Finset.mem_filter.mp hi).2
    rcases h_loc.1 i with ⟨u, hu_sub⟩
    have hv_ball : boxDist u c.v ≤ r_0 := by
      simpa [boxBall] using hu_sub hv_in
    have h_sub_2r0 : sys.support i ⊆ boxBall c.v (2 * r_0) := by
      intro y hy
      have hy_ball : boxDist u y ≤ r_0 := by simpa [boxBall] using hu_sub hy
      simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and]
      refine Finset.sup_le fun μ _ => ?_
      have h1 : coordDist (u μ) (c.v μ) ≤ r_0 :=
        le_trans (Finset.le_sup (f := fun j => coordDist (u j) (c.v j)) (Finset.mem_univ μ)) hv_ball
      have h2 : coordDist (u μ) (y μ) ≤ r_0 :=
        le_trans (Finset.le_sup (f := fun j => coordDist (u j) (y j)) (Finset.mem_univ μ)) hy_ball
      have h_tri := coordDist_triangle (c.v μ) (u μ) (y μ)
      rw [coordDist_comm (c.v μ) (u μ)] at h_tri
      omega
    exact KMSPinchedGibbs.isSupportedOn_mono (h_sub_2r0.trans hW_cube.2.1) (sys.is_supported i)
  let H_loc := ∑ i ∈ I_loc, sys.checkProj i
  have hH_loc : IsSelfAdjoint H_loc :=
    isSelfAdjoint_finset_sum I_loc _ fun i _ => (sys.is_projector i).isSelfAdjoint
  have h_loc_spec := checkSum_spectralEigenspaceProj_props sys I_loc W hI_supp
  refine ⟨?_, ?_, ?_, min_four_mul_add_one_mem_Icc r_0, hW_cube.1, ?_⟩
  · intro ω
    refine ⟨?_, ?_⟩
    · unfold bohrEigenop opCommutator
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      split_ifs with hEω
      · have hL := (H_mul_spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 ((E - ω : ℤ) : ℝ)).1
        have hR := (H_mul_spectralEigenspaceProj sys.H0 sys.isSelfAdjoint_H0 (E : ℝ)).2
        have hc_diff : -(ω : ℂ) = (((E - ω : ℤ) : ℝ) : ℂ) - ((E : ℝ) : ℂ) := by push_cast; ring
        rw [← mul_assoc, ← mul_assoc, hL, clm_smul_mul_davies, clm_smul_mul_davies,
          mul_assoc (_ * c.S), hR, clm_mul_smul_davies, hc_diff, sub_smul]
      · simp
    · unfold bohrEigenop
      have hS_adj : star c.S = c.S := c.isSelfAdjoint_S.star_eq
      change star _ = _
      rw [star_sum]
      symm
      refine Finset.sum_bij_ne_zero (fun (E' : ℤ) _ _ => E' + ω) ?_ ?_ ?_ ?_
      · intro E' hE' h_ne
        rw [Finset.mem_Icc] at hE' ⊢
        by_cases h_cond : 0 ≤ E' - -ω ∧ E' - -ω ≤ (Fintype.card ι : ℤ)
        · omega
        · exact False.elim (h_ne (if_neg h_cond))
      · intro E₁ _ _ E₂ _ _ h_eq; omega
      · intro E hE h_ne
        rw [Finset.mem_Icc] at hE
        by_cases h_cond : 0 ≤ E - ω ∧ E - ω ≤ (Fintype.card ι : ℤ)
        · refine ⟨E - ω, Finset.mem_Icc.mpr h_cond, ?_, by omega⟩
          intro h_zero; apply h_ne
          have h_cond' : 0 ≤ E - ω - -ω ∧ E - ω - -ω ≤ (Fintype.card ι : ℤ) := by omega
          rw [if_pos h_cond]
          rw [if_pos h_cond', show E - ω - -ω = E by omega] at h_zero
          have hP1 := (spectralEigenspaceProj_isStarProjection sys.H0 sys.isSelfAdjoint_H0 ((E - ω : ℤ) : ℝ)).isSelfAdjoint.star_eq
          have hP2 := (spectralEigenspaceProj_isStarProjection sys.H0 sys.isSelfAdjoint_H0 (E : ℝ)).isSelfAdjoint.star_eq
          simp only [star_mul, hP1, hP2, hS_adj, mul_assoc]
          simpa only [mul_assoc] using h_zero
        · exact False.elim (h_ne (by rw [if_neg h_cond, star_zero]))
      · intro E' hE' h_ne
        rw [Finset.mem_Icc] at hE'
        have h_cond' : 0 ≤ E' - -ω ∧ E' - -ω ≤ (Fintype.card ι : ℤ) := by
          by_contra h_not; exact h_ne (if_neg h_not)
        have h_cond : 0 ≤ E' + ω - ω ∧ E' + ω - ω ≤ (Fintype.card ι : ℤ) := by omega
        rw [if_pos h_cond', if_pos h_cond, show E' + ω - ω = E' by omega,
          show E' - -ω = E' + ω by omega]
        have hP1 := (spectralEigenspaceProj_isStarProjection sys.H0 sys.isSelfAdjoint_H0 (E' : ℝ)).isSelfAdjoint.star_eq
        have hP2 := (spectralEigenspaceProj_isStarProjection sys.H0 sys.isSelfAdjoint_H0 ((E' + ω : ℤ) : ℝ)).isSelfAdjoint.star_eq
        simp only [star_mul, hP1, hP2, hS_adj, mul_assoc]
  · intro ω hω
    rw [bohrEigenop_eq_local_check_sum sys h_unit c ω]
    rw [Finset.mem_Icc] at hω
    dsimp [I_loc] at hI_card
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    exact if_neg (by omega)
  · intro ω
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c.S)
    intro ψ
    rw [bohrEigenop_eq_local_check_sum sys h_unit c ω]
    let P_loc : ℤ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
      fun m => spectralEigenspaceProj H_loc hH_loc (m : ℝ)
    let Y : ℤ → ManyBodyHilbertSpace Site := fun m =>
      (if 0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ) then P_loc (m - ω) * c.S * P_loc m else 0) ψ
    change ‖(∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
      if 0 ≤ m - ω ∧ m - ω ≤ (I_loc.card : ℤ) then P_loc (m - ω) * c.S * P_loc m else 0) ψ‖ ≤ _
    rw [ContinuousLinearMap.sum_apply]
    have hY_orth : ∀ m₁ ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
        ∀ m₂ ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), m₁ ≠ m₂ → inner ℂ (Y m₁) (Y m₂) = 0 := by
      intro m₁ _ m₂ _ hne
      dsimp [Y]
      split_ifs with h1 h2
      · have h_proj1 : P_loc (m₁ - ω) (P_loc (m₁ - ω) (c.S (P_loc m₁ ψ))) =
            P_loc (m₁ - ω) (c.S (P_loc m₁ ψ)) := by
          change (P_loc (m₁ - ω) * P_loc (m₁ - ω)) _ = _
          rw [(spectralEigenspaceProj_isStarProjection H_loc hH_loc _).isIdempotentElem.eq]
        have h_adj1 : (P_loc (m₁ - ω))† = P_loc (m₁ - ω) :=
          ContinuousLinearMap.isSelfAdjoint_iff'.mp
            (spectralEigenspaceProj_isStarProjection H_loc hH_loc _).isSelfAdjoint
        have h_prod0 : P_loc (m₁ - ω) * P_loc (m₂ - ω) = 0 := by
          dsimp [P_loc]
          rw [spectralEigenspaceProj_mul_spectralEigenspaceProj, if_neg]
          intro h_eq; have : m₁ - ω = m₂ - ω := by exact_mod_cast h_eq
          exact hne (by omega)
        change inner ℂ (P_loc (m₁ - ω) (c.S (P_loc m₁ ψ))) (P_loc (m₂ - ω) (c.S (P_loc m₂ ψ))) = 0
        rw [← h_proj1, ← ContinuousLinearMap.adjoint_inner_right, h_adj1]
        change inner ℂ _ ((P_loc (m₁ - ω) * P_loc (m₂ - ω)) (c.S (P_loc m₂ ψ))) = 0
        rw [h_prod0, ContinuousLinearMap.zero_apply, inner_zero_right]
      · simp
      · simp
      · simp
    have hP_orth : ∀ m₁ ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
        ∀ m₂ ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), m₁ ≠ m₂ →
          inner ℂ (P_loc m₁ ψ) (P_loc m₂ ψ) = 0 := by
      intro m₁ _ m₂ _ hne
      have h_adj1 : (P_loc m₁)† = P_loc m₁ :=
        ContinuousLinearMap.isSelfAdjoint_iff'.mp
          (spectralEigenspaceProj_isStarProjection H_loc hH_loc _).isSelfAdjoint
      have h_prod0 : P_loc m₁ * P_loc m₂ = 0 := by
        dsimp [P_loc]
        rw [spectralEigenspaceProj_mul_spectralEigenspaceProj, if_neg]
        intro h_eq; exact hne (by exact_mod_cast h_eq)
      rw [← ContinuousLinearMap.adjoint_inner_right, h_adj1]
      change inner ℂ ψ ((P_loc m₁ * P_loc m₂) ψ) = 0
      rw [h_prod0, ContinuousLinearMap.zero_apply, inner_zero_right]
    have h_each_Y : ∀ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ),
        ‖Y m‖ ^ 2 ≤ ‖c.S‖ ^ 2 * ‖P_loc m ψ‖ ^ 2 := by
      intro m _
      dsimp [Y]
      split_ifs
      · have hP_le1 : ‖P_loc (m - ω)‖ ≤ 1 :=
          isStarProjection_norm_le_one (spectralEigenspaceProj_isStarProjection H_loc hH_loc _)
        have h_n : ‖(P_loc (m - ω) * c.S * P_loc m) ψ‖ ≤ ‖c.S‖ * ‖P_loc m ψ‖ := by
          calc ‖P_loc (m - ω) (c.S (P_loc m ψ))‖
            _ ≤ ‖P_loc (m - ω)‖ * ‖c.S (P_loc m ψ)‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ 1 * (‖c.S‖ * ‖P_loc m ψ‖) :=
              mul_le_mul hP_le1 (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
            _ = ‖c.S‖ * ‖P_loc m ψ‖ := one_mul _
        calc ‖(P_loc (m - ω) * c.S * P_loc m) ψ‖ ^ 2
          _ ≤ (‖c.S‖ * ‖P_loc m ψ‖) ^ 2 := sq_le_sq' (by linarith [norm_nonneg ((P_loc (m - ω) * c.S * P_loc m) ψ)]) h_n
          _ = ‖c.S‖ ^ 2 * ‖P_loc m ψ‖ ^ 2 := mul_pow _ _ 2
      · simp; positivity
    have h_sq : ‖∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), Y m‖ ^ 2 ≤ (‖c.S‖ * ‖ψ‖) ^ 2 := by
      calc ‖∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), Y m‖ ^ 2
        _ = ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), ‖Y m‖ ^ 2 :=
          norm_sq_sum_of_pairwise_orthogonal _ Y hY_orth
        _ ≤ ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), ‖c.S‖ ^ 2 * ‖P_loc m ψ‖ ^ 2 :=
          Finset.sum_le_sum h_each_Y
        _ = ‖c.S‖ ^ 2 * ∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), ‖P_loc m ψ‖ ^ 2 :=
          (Finset.mul_sum _ _ _).symm
        _ = ‖c.S‖ ^ 2 * ‖∑ m ∈ Finset.Icc (0 : ℤ) (I_loc.card : ℤ), P_loc m ψ‖ ^ 2 := by
          rw [← norm_sq_sum_of_pairwise_orthogonal _ (fun m => P_loc m ψ) hP_orth]
        _ = (‖c.S‖ * ‖ψ‖) ^ 2 := by
          rw [← ContinuousLinearMap.sum_apply, h_loc_spec.2.2, ContinuousLinearMap.one_apply, mul_pow]
    exact ( abs_le_of_sq_le_sq' h_sq (by positivity) ).2
  · intro ω
    rw [bohrEigenop_eq_local_check_sum sys h_unit c ω]
    refine isSupportedOn_finset_sum_local W _ _ fun m _ => ?_
    split_ifs
    · exact KMSPinchedGibbs.isSupportedOn_mul W
        (KMSPinchedGibbs.isSupportedOn_mul W (h_loc_spec.2.1 (m - ω))
          (KMSPinchedGibbs.isSupportedOn_mono hW_cube.2.2 c.isSupported_S))
        (h_loc_spec.2.1 m)
    · exact KMSPinchedGibbs.isSupportedOn_zero W

/-! ### Helper Section 2: Modular Sandwich of Bohr Eigenoperators and `daviesBathChannels` Algebra -/

private lemma gibbsSqrtOp_mul_inv_and_eigenop_conj {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    let ψ_eig := opEigenbasis H hH
    let E_eig := opEigenvalues H hH
    gibbsInvSqrtOp ψ_eig E_eig β * gibbsSqrtOp ψ_eig E_eig β = 1 ∧
    gibbsSqrtOp ψ_eig E_eig β * gibbsInvSqrtOp ψ_eig E_eig β = 1 ∧
    ∀ (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (ev : ℝ),
      opCommutator H A = (ev : ℂ) • A →
      gibbsInvSqrtOp ψ_eig E_eig β * A * gibbsSqrtOp ψ_eig E_eig β =
        (Real.exp (β * ev / 2) : ℂ) • A ∧
      gibbsSqrtOp ψ_eig E_eig β * A * gibbsInvSqrtOp ψ_eig E_eig β =
        (Real.exp (-β * ev / 2) : ℂ) • A := by
  intro ψ_eig E_eig
  have hZ_pos : 0 < Real.sqrt (gibbsPartitionZ E_eig β) :=
    Real.sqrt_pos.mpr (gibbsPartitionZ_pos E_eig β)
  have hZ_ne : (Real.sqrt (gibbsPartitionZ E_eig β) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hZ_pos
  have h_onb := opEigenbasis_orthonormal H hH
  have h_id := onb_sum_ketBra_eq_one ψ_eig h_onb (opEigenbasis_parseval H hH)
  have h_inv_mul : gibbsInvSqrtOp ψ_eig E_eig β * gibbsSqrtOp ψ_eig E_eig β = 1 := by
    unfold gibbsInvSqrtOp gibbsSqrtOp
    rw [clm_smul_mul_davies, clm_mul_smul_davies, smul_smul, mul_inv_cancel₀ hZ_ne, one_smul, Finset.sum_mul]
    rw [← h_id]
    refine Finset.sum_congr rfl fun τ₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single τ₁]
    · rw [clm_smul_mul_davies, clm_mul_smul_davies, onb_ketBra_mul_ketBra _ h_onb, if_pos rfl, smul_smul]
      have hexp : Real.exp (β * E_eig τ₁ / 2) * Real.exp (-β * E_eig τ₁ / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hexp_c : (Real.exp (β * E_eig τ₁ / 2) : ℂ) * (Real.exp (-β * E_eig τ₁ / 2) : ℂ) = 1 := by
        exact_mod_cast hexp
      rw [hexp_c, one_smul]
    · intro τ₂ _ hne
      rw [clm_smul_mul_davies, clm_mul_smul_davies, onb_ketBra_mul_ketBra _ h_onb, if_neg hne.symm,
        smul_zero, smul_zero]
    · intro h_not; exact False.elim (h_not (Finset.mem_univ τ₁))
  have h_mul_inv : gibbsSqrtOp ψ_eig E_eig β * gibbsInvSqrtOp ψ_eig E_eig β = 1 := by
    unfold gibbsInvSqrtOp gibbsSqrtOp
    rw [clm_smul_mul_davies, clm_mul_smul_davies, smul_smul, inv_mul_cancel₀ hZ_ne, one_smul, Finset.sum_mul]
    rw [← h_id]
    refine Finset.sum_congr rfl fun τ₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single τ₁]
    · rw [clm_smul_mul_davies, clm_mul_smul_davies, onb_ketBra_mul_ketBra _ h_onb, if_pos rfl, smul_smul]
      have hexp : Real.exp (-β * E_eig τ₁ / 2) * Real.exp (β * E_eig τ₁ / 2) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have hexp_c : (Real.exp (-β * E_eig τ₁ / 2) : ℂ) * (Real.exp (β * E_eig τ₁ / 2) : ℂ) = 1 := by
        exact_mod_cast hexp
      rw [hexp_c, one_smul]
    · intro τ₂ _ hne
      rw [clm_smul_mul_davies, clm_mul_smul_davies, onb_ketBra_mul_ketBra _ h_onb, if_neg hne.symm,
        smul_zero, smul_zero]
    · intro h_not; exact False.elim (h_not (Finset.mem_univ τ₁))
  refine ⟨h_inv_mul, h_mul_inv, fun A ev hA => ?_⟩
  have h_block : ∀ τ₁ τ₂ : ManyBodyConfig Site,
      E_eig τ₂ - E_eig τ₁ = ev ∨
        rankOneKetBra (ψ_eig τ₂) * A * rankOneKetBra (ψ_eig τ₁) = 0 := by
    intro τ₁ τ₂
    by_cases h_diff : E_eig τ₂ - E_eig τ₁ = ev
    · exact Or.inl h_diff
    · right
      have hL := (opEigenbasis_ketBra_props H hH τ₂).2.1
      have hR := (opEigenbasis_ketBra_props H hH τ₁).1
      have h1 : rankOneKetBra (ψ_eig τ₂) * opCommutator H A * rankOneKetBra (ψ_eig τ₁) =
          ((E_eig τ₂ - E_eig τ₁ : ℝ) : ℂ) •
            (rankOneKetBra (ψ_eig τ₂) * A * rankOneKetBra (ψ_eig τ₁)) := by
        unfold opCommutator
        have hc_diff : ((E_eig τ₂ - E_eig τ₁ : ℝ) : ℂ) = (E_eig τ₂ : ℂ) - (E_eig τ₁ : ℂ) := by
          push_cast; rfl
        rw [mul_sub, sub_mul, ← mul_assoc (rankOneKetBra (ψ_eig τ₂)) H, hL,
          clm_smul_mul_davies, clm_smul_mul_davies,
          ← mul_assoc (rankOneKetBra (ψ_eig τ₂)) A H,
          mul_assoc (rankOneKetBra (ψ_eig τ₂) * A) H, hR, clm_mul_smul_davies,
          hc_diff, sub_smul]
      have h2 : rankOneKetBra (ψ_eig τ₂) * opCommutator H A * rankOneKetBra (ψ_eig τ₁) =
          (ev : ℂ) • (rankOneKetBra (ψ_eig τ₂) * A * rankOneKetBra (ψ_eig τ₁)) := by
        rw [hA, clm_mul_smul_davies, clm_smul_mul_davies]
      have h_sub : ((E_eig τ₂ - E_eig τ₁ - ev : ℝ) : ℂ) •
          (rankOneKetBra (ψ_eig τ₂) * A * rankOneKetBra (ψ_eig τ₁)) = 0 := by
        have hc : ((E_eig τ₂ - E_eig τ₁ - ev : ℝ) : ℂ) =
            ((E_eig τ₂ - E_eig τ₁ : ℝ) : ℂ) - (ev : ℂ) := by push_cast; ring
        rw [hc, sub_smul, ← h1, ← h2, sub_self]
      have h_ne_c : ((E_eig τ₂ - E_eig τ₁ - ev : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr h_diff
      exact (smul_eq_zero.mp h_sub).resolve_left h_ne_c
  have hA_expand : A = ∑ τ₂ : ManyBodyConfig Site, ∑ τ₁ : ManyBodyConfig Site,
      rankOneKetBra (ψ_eig τ₂) * A * rankOneKetBra (ψ_eig τ₁) := by
    calc A = (∑ τ₂, rankOneKetBra (ψ_eig τ₂)) * A * (∑ τ₁, rankOneKetBra (ψ_eig τ₁)) := by
          rw [h_id, one_mul, mul_one]
      _ = ∑ τ₂, ∑ τ₁, rankOneKetBra (ψ_eig τ₂) * A * rankOneKetBra (ψ_eig τ₁) := by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _
  refine ⟨?_, ?_⟩
  · unfold gibbsInvSqrtOp gibbsSqrtOp
    rw [clm_smul_mul_davies, clm_smul_mul_davies, clm_mul_smul_davies,
      smul_smul, mul_inv_cancel₀ hZ_ne, one_smul, Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [hA_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ₂ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ₁ _ => ?_
    rw [clm_smul_mul_davies, clm_smul_mul_davies, clm_mul_smul_davies, smul_smul]
    rcases h_block τ₁ τ₂ with h_eq | h_zero
    · congr 1
      have hexp : Real.exp (β * E_eig τ₂ / 2) * Real.exp (-β * E_eig τ₁ / 2) =
          Real.exp (β * ev / 2) := by
        rw [← Real.exp_add]; congr 1; rw [← h_eq]; ring
      exact_mod_cast hexp
    · rw [h_zero, smul_zero, smul_zero]
  · unfold gibbsInvSqrtOp gibbsSqrtOp
    rw [clm_smul_mul_davies, clm_smul_mul_davies, clm_mul_smul_davies,
      smul_smul, inv_mul_cancel₀ hZ_ne, one_smul, Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    conv_rhs => rw [hA_expand, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ₂ _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ₁ _ => ?_
    rw [clm_smul_mul_davies, clm_smul_mul_davies, clm_mul_smul_davies, smul_smul]
    rcases h_block τ₁ τ₂ with h_eq | h_zero
    · congr 1
      have hexp : Real.exp (-β * E_eig τ₂ / 2) * Real.exp (β * E_eig τ₁ / 2) =
          Real.exp (-β * ev / 2) := by
        rw [← Real.exp_add]; congr 1; rw [← h_eq]; ring
      exact_mod_cast hexp
    · rw [h_zero, smul_zero, smul_zero]

private lemma daviesBathChannels_fiber_and_symm {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    {r_0 w_0 : ℕ} (h_loc : sys.IsGeometricallyLocal r_0 w_0)
    (h_unit : ∀ i : ι, sys.weight i = 1)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β)) :
    let bath := daviesBathChannels sys r_0 w_0 β couplings
    IsCubeRangeBath D L_box (4 * r_0 + 1) bath ∧
    IsAdjointSymmetricBath bath ∧
    (∀ f : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) → ℝ,
      (∑ ch ∈ bath, ch.γ * f ch.L) =
        ∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
          Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * f (bohrEigenop sys c.S ω)) ∧
    (∀ F : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →
        (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      (∑ ch ∈ bath, (ch.γ : ℂ) • F ch.L) =
        ∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
          ((Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω : ℝ) : ℂ) • F (bohrEigenop sys c.S ω)) := by
  intro bath
  let idx := couplings ×ˢ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ)
  let pairFn : SingleSiteThermalCoupling D L_box Site β × ℤ →
      Finset (BoxD D L_box) × (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :=
    fun p => (daviesEnclosingCube r_0 p.1.v, bohrEigenop sys p.1.S p.2)
  let pairs := idx.image pairFn
  let rateFn : SingleSiteThermalCoupling D L_box Site β × ℤ → ℝ :=
    fun p => Real.exp (-β * (p.2 : ℝ) / 2) * p.1.h_spec p.2
  let mkCh : Finset (BoxD D L_box) ×
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →
      BathChannel D L_box Site := fun wl =>
    { L := wl.2
      support := wl.1
      γ := ∑ p ∈ idx.filter (fun p =>
            daviesEnclosingCube r_0 p.1.v = wl.1 ∧ bohrEigenop sys p.1.S p.2 = wl.2),
            rateFn p }
  have h_bath_eq : bath = pairs.image mkCh := rfl
  have h_mkCh_inj : Set.InjOn mkCh pairs := by
    intro wl₁ _ wl₂ _ h_eq
    exact Prod.ext (congrArg BathChannel.support h_eq) (congrArg BathChannel.L h_eq)
  have h_bohr := fun c : SingleSiteThermalCoupling D L_box Site β =>
    bohrEigenop_locality_and_norm_bound sys h_loc h_unit c
  have h_fiber_real : ∀ f : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) → ℝ,
      (∑ ch ∈ bath, ch.γ * f ch.L) =
        ∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
          rateFn (c, ω) * f (bohrEigenop sys c.S ω) := by
    intro f
    rw [h_bath_eq, Finset.sum_image h_mkCh_inj]
    have h_step : ∀ wl ∈ pairs, (mkCh wl).γ * f (mkCh wl).L =
        ∑ p ∈ idx.filter (fun p => pairFn p = wl), rateFn p * f (pairFn p).2 := by
      intro wl _
      dsimp only [mkCh, pairFn]
      rw [Finset.sum_mul]
      refine Finset.sum_congr ?_ fun p hp => by
        have hpL : bohrEigenop sys p.1.S p.2 = wl.2 := (Prod.ext_iff.mp (Finset.mem_filter.mp hp).2).2
        rw [hpL]
      ext p; simp [Prod.ext_iff]
    rw [Finset.sum_congr rfl h_step, Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
    exact Finset.sum_product couplings (Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ)) _
  have h_fiber_clm : ∀ F : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →
      (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site),
      (∑ ch ∈ bath, (ch.γ : ℂ) • F ch.L) =
        ∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
          (rateFn (c, ω) : ℂ) • F (bohrEigenop sys c.S ω) := by
    intro F
    rw [h_bath_eq, Finset.sum_image h_mkCh_inj]
    have h_step : ∀ wl ∈ pairs, ((mkCh wl).γ : ℂ) • F (mkCh wl).L =
        ∑ p ∈ idx.filter (fun p => pairFn p = wl), (rateFn p : ℂ) • F (pairFn p).2 := by
      intro wl _
      dsimp only [mkCh, pairFn]
      rw [Complex.ofReal_sum, clm_sum_smul_davies]
      refine Finset.sum_congr ?_ fun p hp => by
        have hpL : bohrEigenop sys p.1.S p.2 = wl.2 := (Prod.ext_iff.mp (Finset.mem_filter.mp hp).2).2
        rw [hpL]
      ext p; simp [Prod.ext_iff]
    rw [Finset.sum_congr rfl h_step, Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
    exact Finset.sum_product couplings (Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ)) _
  refine ⟨?_, ?_, h_fiber_real, h_fiber_clm⟩
  · intro ch hch
    rw [h_bath_eq] at hch
    rcases Finset.mem_image.mp hch with ⟨wl, hwl, rfl⟩
    rcases Finset.mem_image.mp hwl with ⟨⟨c, ω⟩, _, rfl⟩
    refine ⟨Finset.sum_nonneg fun p _ => mul_nonneg (le_of_lt (Real.exp_pos _))
      (p.1.kms_detailed_balance p.2).1, ?_⟩
    exact ⟨min (4 * r_0 + 1) L_box, (h_bohr c).2.2.2.1, daviesEnclosingCube r_0 c.v,
      (h_bohr c).2.2.2.2.1, rfl, (h_bohr c).2.2.2.2.2 ω⟩
  · have h_adj_mem : ∀ ch ∈ bath, mkCh (ch.support, (ch.L)†) ∈ bath := by
      intro ch hch
      rw [h_bath_eq] at hch ⊢
      rcases Finset.mem_image.mp hch with ⟨wl, hwl, rfl⟩
      rcases Finset.mem_image.mp hwl with ⟨⟨c, ω⟩, hp_mem, rfl⟩
      refine Finset.mem_image.mpr ⟨(daviesEnclosingCube r_0 c.v, (bohrEigenop sys c.S ω)†), ?_, rfl⟩
      refine Finset.mem_image.mpr ⟨(c, -ω), ?_, ?_⟩
      · rcases Finset.mem_product.mp hp_mem with ⟨hc, hω⟩
        rw [Finset.mem_Icc] at hω
        exact Finset.mem_product.mpr ⟨hc, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
      · dsimp only [pairFn]; rw [((h_bohr c).1 ω).2]
    refine ⟨fun ch => ⟨mkCh (ch.1.support, (ch.1.L)†), h_adj_mem ch.1 ch.2⟩, ?_, ?_⟩
    · rintro ⟨ch, hch⟩
      apply Subtype.ext
      rw [h_bath_eq] at hch
      rcases Finset.mem_image.mp hch with ⟨wl, _, rfl⟩
      dsimp only [mkCh]
      have h_adj_inv : ((wl.2)†)† = wl.2 := star_star wl.2
      simp [h_adj_inv]
    · rintro ⟨ch, hch⟩
      refine ⟨?_, rfl⟩
      rw [h_bath_eq] at hch
      rcases Finset.mem_image.mp hch with ⟨wl, _, rfl⟩
      dsimp only [mkCh, rateFn]
      refine Finset.sum_bij (fun p _ => (p.1, -p.2)) ?_ ?_ ?_ ?_
      · intro ⟨c, ω⟩ hp
        rcases Finset.mem_filter.mp hp with ⟨hp_idx, hW, hL⟩
        rcases Finset.mem_product.mp hp_idx with ⟨hc, hω⟩
        rw [Finset.mem_Icc] at hω
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, hW, ?_⟩
        have h_st : (bohrEigenop sys c.S ω)† = wl.2 := by rw [hL]; exact star_star wl.2
        exact ((h_bohr c).1 ω).2.symm.trans h_st
      · rintro ⟨c₁, ω₁⟩ _ ⟨c₂, ω₂⟩ _ h_eq
        injection h_eq with hc hω; exact Prod.ext hc (neg_inj.mp hω)
      · intro ⟨c, ω⟩ hp
        rcases Finset.mem_filter.mp hp with ⟨hp_idx, hW, hL⟩
        rcases Finset.mem_product.mp hp_idx with ⟨hc, hω⟩
        rw [Finset.mem_Icc] at hω
        refine ⟨(c, -ω), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, hW, ?_⟩,
          by simp⟩
        rw [← ((h_bohr c).1 ω).2, hL]
      · intro ⟨c, ω⟩ _
        dsimp only
        rw [(c.kms_detailed_balance ω).2, ← mul_assoc, ← Real.exp_add]
        congr 1; congr 1; push_cast; ring

private lemma davies_single_freq_kms_eq {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    {r_0 w_0 : ℕ} (h_loc : sys.IsGeometricallyLocal r_0 w_0)
    (h_unit : ∀ i : ι, sys.weight i = 1)
    (β : ℝ) (c : SingleSiteThermalCoupling D L_box Site β) (ω : ℤ)
    (X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    (-(1 / 2 : ℂ)) • (((Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω : ℝ) : ℂ) •
      kmsInvSandwich (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β
        (opCommutator ((bohrEigenop sys c.S ω)†)
          (kmsSandwich (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β
            (opCommutator (bohrEigenop sys c.S ω) X)))) =
    (1 / 2 : ℂ) • ((c.h_spec ω : ℂ) •
      ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω -
        (bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω * X)) +
    (1 / 2 : ℂ) • ((c.h_spec (-ω) : ℂ) •
      ((bohrEigenop sys c.S (-ω))† * X * bohrEigenop sys c.S (-ω) -
        X * ((bohrEigenop sys c.S (-ω))† * bohrEigenop sys c.S (-ω)))) := by
  let ψ_eig := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let E_eig := opEigenvalues sys.H0 sys.isSelfAdjoint_H0
  rcases gibbsSqrtOp_mul_inv_and_eigenop_conj sys.H0 sys.isSelfAdjoint_H0 β with
    ⟨h_inv_mul, h_mul_inv, h_conj⟩
  have h_bohr := bohrEigenop_locality_and_norm_bound sys h_loc h_unit c
  let A_ω := bohrEigenop sys c.S ω
  have hA_adj_eq : A_ω† = bohrEigenop sys c.S (-ω) := (h_bohr.1 ω).2
  have hA_comm : opCommutator sys.H0 (A_ω†) = ((ω : ℝ) : ℂ) • (A_ω†) := by
    rw [hA_adj_eq, (h_bohr.1 (-ω)).1]
    congr 1; push_cast; ring
  rcases h_conj (A_ω†) (ω : ℝ) hA_comm with ⟨h_c1, h_c2⟩
  have h_sand : kmsInvSandwich ψ_eig E_eig β
      (opCommutator (A_ω†) (kmsSandwich ψ_eig E_eig β (opCommutator A_ω X))) =
      (Real.exp (β * (ω : ℝ) / 2) : ℂ) • (A_ω† * A_ω * X - A_ω† * X * A_ω) -
      (Real.exp (-β * (ω : ℝ) / 2) : ℂ) • (A_ω * X * A_ω† - X * A_ω * A_ω†) := by
    dsimp only [kmsInvSandwich, kmsSandwich, opCommutator]
    rw [mul_sub, sub_mul,
      show gibbsInvSqrtOp ψ_eig E_eig β * (A_ω† * (gibbsSqrtOp ψ_eig E_eig β * (A_ω * X - X * A_ω) * gibbsSqrtOp ψ_eig E_eig β)) * gibbsInvSqrtOp ψ_eig E_eig β =
        (gibbsInvSqrtOp ψ_eig E_eig β * A_ω† * gibbsSqrtOp ψ_eig E_eig β) * (A_ω * X - X * A_ω) * (gibbsSqrtOp ψ_eig E_eig β * gibbsInvSqrtOp ψ_eig E_eig β) by simp only [mul_assoc],
      show gibbsInvSqrtOp ψ_eig E_eig β * ((gibbsSqrtOp ψ_eig E_eig β * (A_ω * X - X * A_ω) * gibbsSqrtOp ψ_eig E_eig β) * A_ω†) * gibbsInvSqrtOp ψ_eig E_eig β =
        (gibbsInvSqrtOp ψ_eig E_eig β * gibbsSqrtOp ψ_eig E_eig β) * (A_ω * X - X * A_ω) * (gibbsSqrtOp ψ_eig E_eig β * A_ω† * gibbsInvSqrtOp ψ_eig E_eig β) by simp only [mul_assoc],
      h_c1, h_mul_inv, mul_one, h_inv_mul, one_mul, h_c2,
      clm_smul_mul_davies, clm_mul_smul_davies, mul_sub, sub_mul,
      ← mul_assoc (A_ω†) A_ω X, ← mul_assoc (A_ω†) X A_ω]
  change (-(1 / 2 : ℂ)) • (((Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω : ℝ) : ℂ) •
    kmsInvSandwich ψ_eig E_eig β (opCommutator (A_ω†) (kmsSandwich ψ_eig E_eig β (opCommutator A_ω X)))) = _
  rw [h_sand, ← hA_adj_eq]
  have hr1 : (Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω) * Real.exp (β * (ω : ℝ) / 2) = c.h_spec ω := by
    calc Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * Real.exp (β * (ω : ℝ) / 2)
      _ = (Real.exp (-β * (ω : ℝ) / 2) * Real.exp (β * (ω : ℝ) / 2)) * c.h_spec ω := by ring
      _ = Real.exp 0 * c.h_spec ω := by rw [← Real.exp_add]; ring_nf
      _ = c.h_spec ω := by rw [Real.exp_zero, one_mul]
  have hr2 : (Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω) * Real.exp (-β * (ω : ℝ) / 2) = c.h_spec (-ω) := by
    rw [(c.kms_detailed_balance ω).2]
    calc Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * Real.exp (-β * (ω : ℝ) / 2)
      _ = (Real.exp (-β * (ω : ℝ) / 2) * Real.exp (-β * (ω : ℝ) / 2)) * c.h_spec ω := by ring
      _ = Real.exp (-β * (ω : ℝ)) * c.h_spec ω := by rw [← Real.exp_add]; congr 2; ring
  have hr1_c : ((Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω : ℝ) : ℂ) *
      (Real.exp (β * (ω : ℝ) / 2) : ℂ) = (c.h_spec ω : ℂ) := by exact_mod_cast hr1
  have hr2_c : ((Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω : ℝ) : ℂ) *
      (Real.exp (-β * (ω : ℝ) / 2) : ℂ) = (c.h_spec (-ω) : ℂ) := by exact_mod_cast hr2
  exact gkls_kms_single_channel_algebra _ _ _ _ _ hr1_c hr2_c A_ω X

/-- **Exact Algebraic Equivalence `opDaviesThermalGenerator = opKMSLindbladGenerator` on `daviesBathChannels`
    (Part I, Section 5.5, Theorem 5.8(ii) (`thm:unperturbed-kms-lifetime`))**:
    Under `sys.IsGeometricallyLocal r_0 w_0` and `∀ i, sys.weight i = 1`, `daviesBathChannels` satisfies
    `IsCubeRangeBath D L_box (4 * r_0 + 1)` and `IsAdjointSymmetricBath`, preserves the exact weighted
    squared-norm sum, and satisfies `opDaviesThermalGenerator = opKMSLindbladGenerator` on all `X`. -/
theorem opDaviesThermalGenerator_eq_opKMSLindbladGenerator {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    {r_0 w_0 : ℕ} (h_loc : sys.IsGeometricallyLocal r_0 w_0)
    (h_unit : ∀ i : ι, sys.weight i = 1)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β)) :
    let bath := daviesBathChannels sys r_0 w_0 β couplings
    IsCubeRangeBath D L_box (4 * r_0 + 1) bath ∧
    IsAdjointSymmetricBath bath ∧
    (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2 =
      ∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
        Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖bohrEigenop sys c.S ω‖ ^ 2) ∧
    (∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      opDaviesThermalGenerator sys β couplings X =
        opKMSLindbladGenerator sys.H0 sys.isSelfAdjoint_H0 β bath X) := by
  intro bath
  rcases daviesBathChannels_fiber_and_symm sys h_loc h_unit β couplings with
    ⟨h_cube, h_adj, h_fiber_real, h_fiber_clm⟩
  have h_bohr := fun c : SingleSiteThermalCoupling D L_box Site β =>
    bohrEigenop_locality_and_norm_bound sys h_loc h_unit c
  refine ⟨h_cube, h_adj, h_fiber_real (fun L => ‖L‖ ^ 2), ?_⟩
  · intro X
    dsimp only [opKMSLindbladGenerator, opDaviesThermalGenerator]
    rw [h_fiber_clm (fun L => kmsInvSandwich (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
      (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β
      (opCommutator (L†) (kmsSandwich (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β (opCommutator L X)))),
      sub_eq_add_neg, ← clm_neg_smul_davies, clm_smul_sum_davies]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    have h_tsum : (∑' ω : ℤ,
        (c.h_spec ω : ℂ) • ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω -
          (1 / 2 : ℂ) • ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω * X +
            X * ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω)))) =
        ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
          (c.h_spec ω : ℂ) • ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω -
            (1 / 2 : ℂ) • ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω * X +
              X * ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω))) := by
      refine tsum_eq_sum fun ω hω => ?_
      rw [(h_bohr c).2.1 ω hω]
      simp only [map_zero, zero_mul, mul_zero, add_zero, sub_zero, clm_smul_zero_davies]
    rw [h_tsum, clm_smul_sum_davies]
    rw [Finset.sum_congr rfl (fun ω _ => davies_single_freq_kms_eq sys h_loc h_unit β c ω X),
      Finset.sum_add_distrib]
    have h_reindex : (∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
        (1 / 2 : ℂ) • ((c.h_spec (-ω) : ℂ) •
          ((bohrEigenop sys c.S (-ω))† * X * bohrEigenop sys c.S (-ω) -
            X * ((bohrEigenop sys c.S (-ω))† * bohrEigenop sys c.S (-ω))))) =
        ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
          (1 / 2 : ℂ) • ((c.h_spec ω : ℂ) •
            ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω -
              X * ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω))) := by
      refine Finset.sum_bij (fun ω _ => -ω) ?_ ?_ ?_ (fun _ _ => rfl)
      · intro ω hω; rw [Finset.mem_Icc] at hω ⊢; omega
      · intro ω₁ _ ω₂ _ h_eq; exact neg_inj.mp h_eq
      · intro ω hω; rw [Finset.mem_Icc] at hω
        exact ⟨-ω, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, neg_neg ω⟩
    rw [h_reindex]
    have h_each_ω : ∀ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
        (c.h_spec ω : ℂ) • ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω -
          (1 / 2 : ℂ) • ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω * X +
            X * ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω))) =
        (1 / 2 : ℂ) • ((c.h_spec ω : ℂ) •
          ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω -
            (bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω * X)) +
        (1 / 2 : ℂ) • ((c.h_spec ω : ℂ) •
          ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω -
            X * ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω))) := fun ω _ =>
      (gkls_anticommutator_combine (c.h_spec ω : ℂ)
        ((bohrEigenop sys c.S ω)† * X * bohrEigenop sys c.S ω)
        ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω * X)
        (X * ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω))).symm
    rw [Finset.sum_congr rfl h_each_ω, Finset.sum_add_distrib]

/-! ### Helper Section 3: Gibbs Trace Stationarity Helpers -/

private lemma hilbertTrace_sub_local {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (A B : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace (A - B) = hilbertTrace A - hilbertTrace B := by
  unfold hilbertTrace
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  change RCLike.re (inner ℂ _ (A _ - B _)) = _
  rw [inner_sub_right, map_sub]

private lemma hilbertTrace_real_smul_local {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (r : ℝ) (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    hilbertTrace ((r : ℂ) • A) = r * hilbertTrace A := by
  unfold hilbertTrace
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  change RCLike.re (inner ℂ _ ((r : ℂ) • A _)) = _
  rw [inner_smul_right, re_ofReal_mul]

private lemma continuous_hilbertTrace_local {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] :
    Continuous (hilbertTrace (Site := Site)) := by
  unfold hilbertTrace
  refine continuous_finset_sum _ fun ψ _ => ?_
  exact RCLike.continuous_re.comp
    (continuous_const.inner ((ContinuousLinearMap.apply ℂ _ (basisVecGlobal Site ψ)).continuous))

private lemma gibbsSqrtOp_sq_and_commute_H {D L_box : ℕ}
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    let ψ_eig := opEigenbasis H hH
    let E_eig := opEigenvalues H hH
    gibbsSqrtOp ψ_eig E_eig β * gibbsSqrtOp ψ_eig E_eig β = gibbsDensityOp ψ_eig E_eig β ∧
    Commute (gibbsDensityOp ψ_eig E_eig β) H := by
  intro ψ_eig E_eig
  have h_onb := opEigenbasis_orthonormal H hH
  have hZ_pos := gibbsPartitionZ_pos E_eig β
  refine ⟨?_, ?_⟩
  · unfold gibbsSqrtOp gibbsDensityOp gibbsBoltzmannOp
    rw [clm_smul_mul_davies, clm_mul_smul_davies, smul_smul, Finset.sum_mul]
    have hZ_sq : ((Real.sqrt (gibbsPartitionZ E_eig β) : ℂ))⁻¹ *
        ((Real.sqrt (gibbsPartitionZ E_eig β) : ℂ))⁻¹ =
        (gibbsPartitionZ E_eig β : ℂ)⁻¹ := by
      have h_r : (Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ *
          (Real.sqrt (gibbsPartitionZ E_eig β))⁻¹ = (gibbsPartitionZ E_eig β)⁻¹ := by
        rw [← mul_inv, ← sq, Real.sq_sqrt (le_of_lt hZ_pos)]
      exact_mod_cast h_r
    rw [hZ_sq]
    congr 1
    refine Finset.sum_congr rfl fun τ₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single τ₁]
    · rw [clm_smul_mul_davies, clm_mul_smul_davies, onb_ketBra_mul_ketBra _ h_onb, if_pos rfl, smul_smul]
      congr 1
      have hexp : Real.exp (-β * E_eig τ₁ / 2) * Real.exp (-β * E_eig τ₁ / 2) =
          Real.exp (-β * E_eig τ₁) := by rw [← Real.exp_add]; congr 1; ring
      exact_mod_cast hexp
    · intro τ₂ _ hne
      rw [clm_smul_mul_davies, clm_mul_smul_davies, onb_ketBra_mul_ketBra _ h_onb, if_neg hne.symm,
        smul_zero, smul_zero]
    · intro h_not; exact False.elim (h_not (Finset.mem_univ τ₁))
  · unfold gibbsDensityOp gibbsBoltzmannOp
    rw [commute_iff_eq, clm_smul_mul_davies, clm_mul_smul_davies]
    congr 1
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [clm_smul_mul_davies, clm_mul_smul_davies, (opEigenbasis_ketBra_props H hH τ).2.1,
      (opEigenbasis_ketBra_props H hH τ).1]

/-- **GKLS Complete Positivity, Unitality, $\dagger$-Preservation, Gibbs Stationarity, and ODE Solution
    for `opDaviesThermalSemigroup` (Part I, Theorem 5.8(ii) (`thm:unperturbed-kms-lifetime`))**. -/
theorem opDaviesThermalSemigroup_cptp_and_ode {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    {r_0 w_0 : ℕ} (h_loc : sys.IsGeometricallyLocal r_0 w_0)
    (h_unit : ∀ i : ι, sys.weight i = 1)
    (β : ℝ)
    (couplings : Finset (SingleSiteThermalCoupling D L_box Site β))
    (O_0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_0)
    {t : ℝ} (ht : 0 ≤ t) :
    IsCPUnitalStarMap (opDaviesThermalSemigroup sys β couplings t) ∧
    (∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β *
          opDaviesThermalSemigroup sys β couplings t X) =
      hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β * X)) ∧
    SatisfiesDaviesThermalODE sys β couplings O_0
      (fun s => opDaviesThermalSemigroup sys β couplings s O_0) t := by
  let bath := daviesBathChannels sys r_0 w_0 β couplings
  rcases opDaviesThermalGenerator_eq_opKMSLindbladGenerator sys h_loc h_unit β couplings with
    ⟨_, h_adj, _, h_gen_eq⟩
  have h_clm_eq : opDaviesThermalGeneratorCLM sys β couplings =
      opKMSLindbladGeneratorCLM sys.H0 sys.isSelfAdjoint_H0 β bath := by
    apply ContinuousLinearMap.ext; intro X
    rw [opDaviesThermalGeneratorCLM_apply, opKMSLindbladGeneratorCLM_apply, h_gen_eq X]
  have h_semi_eq : ∀ s : ℝ, opDaviesThermalSemigroup sys β couplings s =
      opKMSLindbladSemigroup sys.H0 sys.isSelfAdjoint_H0 β bath s := by
    intro s; dsimp [opDaviesThermalSemigroup, opKMSLindbladSemigroup]; rw [h_clm_eq]
  let L := opDaviesThermalGeneratorCLM sys β couplings
  have hL_one : L 1 = 0 := by
    dsimp [L]; rw [opDaviesThermalGeneratorCLM_apply]
    unfold opDaviesThermalGenerator opCommutator
    rw [mul_one, one_mul, sub_self, smul_zero, zero_add]
    refine Finset.sum_eq_zero fun c _ => ?_
    have h_z : ∀ ω : ℤ,
        (c.h_spec ω : ℂ) • ((bohrEigenop sys c.S ω)† * 1 * bohrEigenop sys c.S ω -
          (1 / 2 : ℂ) • ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω * 1 +
            1 * ((bohrEigenop sys c.S ω)† * bohrEigenop sys c.S ω))) = 0 := by
      intro ω
      rw [mul_one, mul_one, one_mul, ← two_smul ℂ, smul_smul]
      norm_num
    simp_rw [h_z, tsum_zero]
  have h_unital : opDaviesThermalSemigroup sys β couplings t 1 = 1 :=
    superop_exp_unital_of_zero L hL_one t
  have hL_star : IsStarPreservingMap L := by
    have h_diss_star := (satisfiesKMSLindbladODE_opKMSLindbladSemigroup
      sys.H0 sys.isSelfAdjoint_H0 β bath h_adj O_0 hO_sa ht).1
    intro Y
    have h_gen_split : ∀ Z : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        opKMSLindbladGeneratorCLM sys.H0 sys.isSelfAdjoint_H0 β bath Z =
          Complex.I • (sys.H0 * Z - Z * sys.H0) +
            opKMSLindbladDissipator sys.H0 sys.isSelfAdjoint_H0 β bath Z := by
      intro Z
      dsimp only [opKMSLindbladGeneratorCLM]
      rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, opCommutatorCLM_apply]
      rfl
    dsimp only [L]; rw [h_clm_eq, h_gen_split Y, h_gen_split (Y†)]
    have h1 : (sys.H0 * Y)† = (Y†) * sys.H0 := by
      change star (sys.H0 * Y) = star Y * sys.H0
      rw [star_mul, sys.isSelfAdjoint_H0.star_eq]
    have h2 : (Y * sys.H0)† = sys.H0 * (Y†) := by
      change star (Y * sys.H0) = sys.H0 * star Y
      rw [star_mul, sys.isSelfAdjoint_H0.star_eq]
    rw [ContinuousLinearMap.adjoint.map_add, h_diss_star Y,
      ContinuousLinearMap.adjoint.map_smulₛₗ, Complex.conj_I,
      ContinuousLinearMap.adjoint.map_sub, h1, h2, neg_smul, ← smul_neg, neg_sub]
  have h_semi_star : IsStarPreservingMap (opDaviesThermalSemigroup sys β couplings t) :=
    superop_exp_isStarPreserving L hL_star t
  have h_ode_kms := (satisfiesKMSLindbladODE_opKMSLindbladSemigroup
    sys.H0 sys.isSelfAdjoint_H0 β bath h_adj O_0 hO_sa ht).2
  have h_ode : SatisfiesDaviesThermalODE sys β couplings O_0
      (fun s => opDaviesThermalSemigroup sys β couplings s O_0) t := by
    simp only [h_semi_eq]
    rcases h_ode_kms with ⟨h0, hsa, f', hf1, hf2⟩
    exact ⟨h0, hsa, f', hf1, fun s hs => by rw [h_gen_eq]; exact hf2 s hs⟩
  refine ⟨⟨h_unital, h_semi_star, isCompletelyPositiveMap_opDaviesThermalSemigroup sys β couplings ht⟩,
    ?_, h_ode⟩
  intro X
  let ψ_eig := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let E_eig := opEigenvalues sys.H0 sys.isSelfAdjoint_H0
  let ρ_β := gibbsDensityOp ψ_eig E_eig β
  rcases gibbsSqrtOp_sq_and_commute_H sys.H0 sys.isSelfAdjoint_H0 β with ⟨h_sq, h_ρ_comm⟩
  rcases gibbsSqrtOp_mul_inv_and_eigenop_conj sys.H0 sys.isSelfAdjoint_H0 β with
    ⟨h_inv_mul, h_mul_inv, _⟩
  have hL_tr : ∀ Y : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
      hilbertTrace (ρ_β * L Y) = 0 := by
    intro Y
    dsimp only [L]; rw [opDaviesThermalGeneratorCLM_apply, h_gen_eq Y]
    dsimp only [opKMSLindbladGenerator]
    rw [mul_sub, hilbertTrace_sub_local]
    have h_coh : hilbertTrace (ρ_β * (Complex.I • opCommutator sys.H0 Y)) = 0 := by
      dsimp only [opCommutator]
      rw [clm_mul_smul_davies, mul_sub, smul_sub, hilbertTrace_sub_local, ← mul_assoc ρ_β sys.H0 Y,
        ← mul_assoc ρ_β Y sys.H0, h_ρ_comm.eq]
      have h_cyc : hilbertTrace (Complex.I • (sys.H0 * ρ_β * Y)) =
          hilbertTrace (Complex.I • (ρ_β * Y * sys.H0)) := by
        rw [← clm_smul_mul_davies, ← clm_smul_mul_davies Complex.I (ρ_β * Y) sys.H0,
          show (Complex.I • (sys.H0 * ρ_β)) * Y = sys.H0 * (Complex.I • (ρ_β * Y)) by
            rw [clm_smul_mul_davies, clm_mul_smul_davies, mul_assoc],
          hilbertTrace_mul_comm_aux]
      dsimp only [ρ_β] at h_cyc ⊢
      linarith
    have h_diss : hilbertTrace (ρ_β * ((1 / 2 : ℂ) • ∑ ch ∈ bath,
        (ch.γ : ℂ) • kmsInvSandwich ψ_eig E_eig β
          (opCommutator (ch.L†) (kmsSandwich ψ_eig E_eig β (opCommutator ch.L Y))))) = 0 := by
      have hc : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [hc, clm_mul_smul_davies, hilbertTrace_real_smul_local, Finset.mul_sum, hilbertTrace_sum]
      suffices h_each : ∑ ch ∈ bath, hilbertTrace (ρ_β * ((ch.γ : ℂ) •
          kmsInvSandwich ψ_eig E_eig β (opCommutator (ch.L†)
            (kmsSandwich ψ_eig E_eig β (opCommutator ch.L Y))))) = 0 by
        rw [h_each, mul_zero]
      refine Finset.sum_eq_zero fun ch _ => ?_
      rw [clm_mul_smul_davies, hilbertTrace_real_smul_local]
      set Z := kmsSandwich ψ_eig E_eig β (opCommutator ch.L Y)
      set S_half := gibbsSqrtOp ψ_eig E_eig β
      set S_inv := gibbsInvSqrtOp ψ_eig E_eig β
      have h_ch0 : hilbertTrace (ρ_β * kmsInvSandwich ψ_eig E_eig β (opCommutator (ch.L†) Z)) = 0 := by
        dsimp only [ρ_β, kmsInvSandwich]
        rw [← h_sq]
        have h_assoc : S_half * S_half * (S_inv * opCommutator (ch.L†) Z * S_inv) =
            (S_half * (S_half * S_inv) * opCommutator (ch.L†) Z) * S_inv := by
          simp only [mul_assoc]
        rw [h_assoc, h_mul_inv, mul_one, hilbertTrace_mul_comm_aux, ← mul_assoc,
          h_inv_mul, one_mul]
        dsimp only [opCommutator]
        rw [hilbertTrace_sub_local, hilbertTrace_mul_comm_aux, sub_self]
      rw [h_ch0, mul_zero]
    linarith
  let trρ : (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) →+ ℝ :=
    { toFun := fun M => hilbertTrace (ρ_β * M)
      map_zero' := by
        rw [mul_zero]; unfold hilbertTrace; simp
      map_add' := fun M₁ M₂ => by
        rw [mul_add]; unfold hilbertTrace
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        change RCLike.re (inner ℂ _ ((ρ_β * M₁) _ + (ρ_β * M₂) _)) = _
        rw [inner_add_right, map_add] }
  have h_cont_trρ : Continuous trρ := by
    have h_eq : (fun M => hilbertTrace (ρ_β * M)) =
        hilbertTrace ∘ (clmSandwichOp ρ_β 1) := by
      ext M; simp [Function.comp_apply, clmSandwichOp_apply]
    change Continuous (fun M => hilbertTrace (ρ_β * M))
    rw [h_eq]
    exact continuous_hilbertTrace_local.comp (clmSandwichOp ρ_β 1).continuous
  exact superop_exp_real_functional_invariant trρ h_cont_trρ
    (fun r M => by
      change hilbertTrace (ρ_β * ((r : ℂ) • M)) = r * hilbertTrace (ρ_β * M)
      rw [clm_mul_smul_davies, hilbertTrace_real_smul_local])
    L hL_tr t X

/-- **Unperturbed Cube-Range KMS and CPTP GKLS Davies Memory Lifetime Bounds
    (Part I, Theorem 5.8(i)–(ii) (`thm:unperturbed-kms-lifetime`); Part II, Theorem 6.5(1))**:
    Given bare cube safe-subspace immunity up to `R_imm` (with `4 * r_0 + 1 ≤ R_imm`) and
    `gibbsFailureProb sys.H0 ... (1 - Pi_safe) ≤ p_fail`, establishes both (iv.a) the cube-range
    `opKMSLindbladGenerator` bound and (iv.b) the exact CPTP GKLS Davies thermal bath bounds. -/
theorem unperturbed_cube_kms_and_davies_lifetime_bounds {D L_box : ℕ} [NeZero L_box]
    {Site : BoxD D L_box → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L_box Site ι)
    {r_0 w_0 R_imm : ℕ}
    (h_loc : sys.IsGeometricallyLocal r_0 w_0)
    (h_unit : ∀ i : ι, sys.weight i = 1)
    (hR_le : 4 * r_0 + 1 ≤ R_imm)
    (Pi_safe O_0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe)
    (hO_sa : IsSelfAdjoint O_0) (hO_norm : ‖O_0‖ ≤ 1)
    (hO_comm : Commute sys.H0 O_0)
    (h_imm : ∀ r ∈ Finset.Icc 1 (min R_imm L_box), ∀ A ∈ boxCubes D L_box r,
      ∀ M_A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
        IsSupportedOn Site A M_A →
        Pi_safe * (M_A * O_0 - O_0 * M_A) * Pi_safe = 0)
    {β p_fail : ℝ} (hp_nonneg : 0 ≤ p_fail)
    (hp_le : gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤ p_fail) :
    (∀ (bath : Finset (BathChannel D L_box Site)),
      IsCubeRangeBath D L_box R_imm bath →
      (IsAdjointSymmetricBath bath →
        ∀ t : ℝ, 0 ≤ t →
          SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0
            (fun s => opKMSLindbladSemigroup sys.H0 sys.isSelfAdjoint_H0 β bath s O_0) t) ∧
      (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
        0 ≤ t →
        SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0 O_t t →
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) * t)) ∧
    (∀ (couplings : Finset (SingleSiteThermalCoupling D L_box Site β)),
      (∀ t : ℝ, 0 ≤ t →
        IsCPUnitalStarMap (opDaviesThermalSemigroup sys β couplings t) ∧
        (∀ X : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site,
          hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β *
              opDaviesThermalSemigroup sys β couplings t X) =
          hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β * X)) ∧
        SatisfiesDaviesThermalODE sys β couplings O_0
          (fun s => opDaviesThermalSemigroup sys β couplings s O_0) t) ∧
      (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
        0 ≤ t →
        SatisfiesDaviesThermalODE sys β couplings O_0 O_t t →
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
            Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖bohrEigenop sys c.S ω‖ ^ 2) *
            (p_fail ^ (1 / 2 : ℝ)) * t ∧
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
            Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖c.S‖ ^ 2) *
            (p_fail ^ (1 / 2 : ℝ)) * t)) := by
  have h_part_a : ∀ (bath : Finset (BathChannel D L_box Site)),
      IsCubeRangeBath D L_box R_imm bath →
      (IsAdjointSymmetricBath bath →
        ∀ t : ℝ, 0 ≤ t →
          SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0
            (fun s => opKMSLindbladSemigroup sys.H0 sys.isSelfAdjoint_H0 β bath s O_0) t) ∧
      (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
        0 ≤ t →
        SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0 O_t t →
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) * t) := by
    intro bath h_cube
    refine ⟨fun h_adj t ht =>
      (satisfiesKMSLindbladODE_opKMSLindbladSemigroup
        sys.H0 sys.isSelfAdjoint_H0 β bath h_adj O_0 hO_sa ht).2, ?_⟩
    intro O_t t ht h_ode
    let ψ_eig := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
    let E_eig := opEigenvalues sys.H0 sys.isSelfAdjoint_H0
    have h_onb := opEigenbasis_orthonormal sys.H0 sys.isSelfAdjoint_H0
    have h_tr := hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0
    have h_pars := opEigenbasis_parseval sys.H0 sys.isSelfAdjoint_H0
    let P_fail := 1 - Pi_safe
    have hP_fail : IsStarProjection P_fail := hPi.one_sub
    have hPi_norm : ‖Pi_safe‖ ≤ 1 := isStarProjection_norm_le_one hPi
    have h_ch_bound : ∀ ch ∈ bath,
        kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_0) ≤
          16 * (‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by
      intro ch hch
      rcases h_cube ch hch with ⟨_, r, hr, W, hW, _, hL_supp⟩
      have h_fw : Pi_safe * (ch.L * O_0 - O_0 * ch.L) * Pi_safe = 0 :=
        h_imm r hr W hW ch.L hL_supp
      let C := opCommutator ch.L O_0
      have h_fw' : Pi_safe * C * Pi_safe = 0 := h_fw
      have hC_split : C = P_fail * C + Pi_safe * C * P_fail := by
        dsimp only [P_fail]
        rw [sub_mul, one_mul, mul_sub, mul_one, h_fw', sub_zero, sub_add_cancel]
      have hC_norm : ‖C‖ ≤ 2 * ‖ch.L‖ := by
        dsimp only [C, opCommutator]
        calc ‖ch.L * O_0 - O_0 * ch.L‖
          _ ≤ ‖ch.L * O_0‖ + ‖O_0 * ch.L‖ := norm_sub_le _ _
          _ ≤ ‖ch.L‖ * ‖O_0‖ + ‖O_0‖ * ‖ch.L‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ ≤ ‖ch.L‖ * 1 + 1 * ‖ch.L‖ :=
            add_le_add (mul_le_mul_of_nonneg_left hO_norm (norm_nonneg _))
              (mul_le_mul_of_nonneg_right hO_norm (norm_nonneg _))
          _ = 2 * ‖ch.L‖ := by ring
      have hPiC_norm : ‖Pi_safe * C‖ ≤ 2 * ‖ch.L‖ :=
        (norm_mul_le _ _).trans
          ((mul_le_mul_of_nonneg_right hPi_norm (norm_nonneg C)).trans (by linarith))
      have hb1 := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr h_pars
        hP_fail C hp_le).2.2.1
      have hb2 := (kms_fourth_root_projector_bound ψ_eig E_eig β h_onb h_tr h_pars
        hP_fail (Pi_safe * C) hp_le).2.2.2
      have h_norm_C : kmsNorm ψ_eig E_eig β C ≤ 4 * ‖ch.L‖ * (p_fail ^ (1 / 4 : ℝ)) := by
        calc kmsNorm ψ_eig E_eig β C
          _ = kmsNorm ψ_eig E_eig β (P_fail * C + Pi_safe * C * P_fail) := by rw [← hC_split]
          _ ≤ kmsNorm ψ_eig E_eig β (P_fail * C) + kmsNorm ψ_eig E_eig β (Pi_safe * C * P_fail) :=
            kmsNorm_add_le ψ_eig E_eig β h_onb h_tr _ _
          _ ≤ ‖C‖ * (p_fail ^ (1 / 4 : ℝ)) + ‖Pi_safe * C‖ * (p_fail ^ (1 / 4 : ℝ)) :=
            add_le_add hb1 hb2
          _ ≤ (2 * ‖ch.L‖) * (p_fail ^ (1 / 4 : ℝ)) + (2 * ‖ch.L‖) * (p_fail ^ (1 / 4 : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_right hC_norm (by positivity))
              (mul_le_mul_of_nonneg_right hPiC_norm (by positivity))
          _ = 4 * ‖ch.L‖ * (p_fail ^ (1 / 4 : ℝ)) := by ring
      have h_sq_eq : kmsNormSq ψ_eig E_eig β C = (kmsNorm ψ_eig E_eig β C) ^ 2 :=
        (Real.sq_sqrt (kmsNormSq_nonneg ψ_eig E_eig β h_onb h_tr C)).symm
      have h_rpow : (p_fail ^ (1 / 4 : ℝ)) ^ 2 = p_fail ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp_nonneg]; norm_num
      have h_kms_nn : 0 ≤ kmsNorm ψ_eig E_eig β C := Real.sqrt_nonneg _
      rw [h_sq_eq]
      calc (kmsNorm ψ_eig E_eig β C) ^ 2
        _ ≤ (4 * ‖ch.L‖ * (p_fail ^ (1 / 4 : ℝ))) ^ 2 :=
          sq_le_sq' (by linarith [h_kms_nn]) h_norm_C
        _ = 16 * (‖ch.L‖ ^ 2) * ((p_fail ^ (1 / 4 : ℝ)) ^ 2) := by ring
        _ = 16 * (‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)) := by rw [h_rpow]
    let Γ_diss : ℝ := 16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))
    have hΓ_nonneg : 0 ≤ Γ_diss :=
      mul_nonneg (mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun ch hch => mul_nonneg (h_cube ch hch).1 (sq_nonneg _)))
        (Real.rpow_nonneg hp_nonneg _)
    have h_diss_le : 2 * kmsDissipativeForm sys.H0 sys.isSelfAdjoint_H0 β
        (opKMSLindbladDissipator sys.H0 sys.isSelfAdjoint_H0 β bath) O_0 O_0 ≤ Γ_diss := by
      rw [kmsDissipativeForm_opKMSLindbladDissipator_eq]
      calc (∑ ch ∈ bath, ch.γ * kmsNormSq ψ_eig E_eig β (opCommutator ch.L O_0))
        _ ≤ ∑ ch ∈ bath, ch.γ * (16 * (‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ))) :=
          Finset.sum_le_sum fun ch hch =>
            mul_le_mul_of_nonneg_left (h_ch_bound ch hch) (h_cube ch hch).1
        _ = Γ_diss := by
          dsimp only [Γ_diss]; rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun ch _ => by ring
    have hL_gen := isKMSSymmetricDissipativeGenerator_opKMSLindbladDissipator
      sys.H0 sys.isSelfAdjoint_H0 β bath (fun ch hch => (h_cube ch hch).1)
    have h_ode_diss := (satisfiesKMSLindbladODE_iff_satisfiesKMSDissipativeODE
      sys.H0 sys.isSelfAdjoint_H0 β bath O_0 O_t t).mp h_ode
    have h_gron := opKMSNormSq_sub_le_of_dissipativeODE_commute
      sys.H0 sys.isSelfAdjoint_H0 β _ hL_gen O_0 hO_sa hO_comm hΓ_nonneg ht h_diss_le h_ode_diss
    exact h_gron.trans_eq (by dsimp only [Γ_diss]; ring)
  refine ⟨h_part_a, fun couplings => ?_⟩
  refine ⟨fun t ht => opDaviesThermalSemigroup_cptp_and_ode sys h_loc h_unit β couplings O_0 hO_sa ht, ?_⟩
  intro O_t t ht h_ode_dav
  let bath := daviesBathChannels sys r_0 w_0 β couplings
  rcases opDaviesThermalGenerator_eq_opKMSLindbladGenerator sys h_loc h_unit β couplings with
    ⟨h_cube_4r0, _, h_sum_eq, h_gen_eq⟩
  have h_cube_R : IsCubeRangeBath D L_box R_imm bath := by
    intro ch hch
    rcases h_cube_4r0 ch hch with ⟨hγ, r, hr, W, hW, hsupp_eq, hL_supp⟩
    rw [Finset.mem_Icc] at hr
    exact ⟨hγ, r, Finset.mem_Icc.mpr ⟨hr.1, by omega⟩,
      W, hW, hsupp_eq, hL_supp⟩
  have h_ode_kms : SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0 O_t t := by
    rcases h_ode_dav with ⟨h0, hsa, f', hf1, hf2⟩
    exact ⟨h0, hsa, f', hf1, fun s hs => by rw [← h_gen_eq]; exact hf2 s hs⟩
  have h_b1 : opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
      8 * (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
        Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖bohrEigenop sys c.S ω‖ ^ 2) *
        (p_fail ^ (1 / 2 : ℝ)) * t := by
    rw [← h_sum_eq]
    exact (h_part_a bath h_cube_R).2 O_t t ht h_ode_kms
  refine ⟨h_b1, h_b1.trans ?_⟩
  have h_sum_le : (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
      Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖bohrEigenop sys c.S ω‖ ^ 2) ≤
      ∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
        Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖c.S‖ ^ 2 := by
    refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun ω _ => ?_
    have h_n := (bohrEigenop_locality_and_norm_bound sys h_loc h_unit c).2.2.1 ω
    have h_sq : ‖bohrEigenop sys c.S ω‖ ^ 2 ≤ ‖c.S‖ ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg (bohrEigenop sys c.S ω)]) h_n
    exact mul_le_mul_of_nonneg_left h_sq
      (mul_nonneg (le_of_lt (Real.exp_pos _)) (c.kms_detailed_balance ω).1)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_sum_le (by norm_num))
      (Real.rpow_nonneg hp_nonneg _)) ht

end
