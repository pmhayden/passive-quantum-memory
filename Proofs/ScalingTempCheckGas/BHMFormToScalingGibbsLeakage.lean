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

import Proofs.CenteredBallBHM.ExcitedBandGapFromRelativeForm
import Proofs.DressedThermalDuhamel.SafeComplementProjectorBounds
import Proofs.DressedSyndromeGibbs.DressedKMSGronwallTrajectory

/-!
# Check-Gas Binomial Trace Bounds and Logarithmic-Cooling Gibbs Leakage

Proves the commuting-projector check-gas binomial excited-trace bound and uniform-in-temperature eigenvector leakage bounds from the `BHM` relative form sandwich. Synthesizes `gibbsFailureProb_and_kms_bound_of_scaling_temp_bhm_form` in the logarithmic-cooling regime where inverse temperature scales logarithmically with system size.

## References

* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`)
* Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`)
-/
open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
noncomputable section
set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
namespace ScalingTempCheckGas

/-- Binomial sum of `Real.exp (-β' * sys.syndromeEnergy σ)` over all `σ : ι → Bool`
    when every check has unit weight `sys.weight i = 1`. -/
private lemma sum_exp_neg_mul_syndromeEnergy_eq_one_add_exp_pow {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ i : ι, sys.weight i = 1) (β' : ℝ) :
    (∑ σ : ι → Bool, Real.exp (-β' * sys.syndromeEnergy σ)) =
      (1 + Real.exp (-β')) ^ Fintype.card ι := by
  let f : ι → Bool → ℝ := fun _ b => if b = true then Real.exp (-β') else 1
  have h_prod_sum : (∏ i : ι, ∑ b : Bool, f i b) = ∑ σ : ι → Bool, ∏ i : ι, f i (σ i) :=
    Fintype.prod_sum f
  have h_lhs : (∏ i : ι, ∑ b : Bool, f i b) = (1 + Real.exp (-β')) ^ Fintype.card ι := by
    have h_bool : ∀ i : ι, (∑ b : Bool, f i b) = 1 + Real.exp (-β') := fun i => by
      rw [Fintype.sum_bool]; dsimp [f]; ring
    simp_rw [h_bool, Finset.prod_const, Finset.card_univ]
  have h_rhs : (∑ σ : ι → Bool, ∏ i : ι, f i (σ i)) =
      ∑ σ : ι → Bool, Real.exp (-β' * sys.syndromeEnergy σ) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h_syn : -β' * sys.syndromeEnergy σ = ∑ i : ι, (if σ i = true then -β' else 0) := by
      unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h_wt i]; split_ifs <;> ring
    rw [h_syn, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp [f]; split_ifs <;> simp
  linarith

/-- **Commuting-Projector Check-Gas Binomial Trace Bound (Part II, Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`))**. -/
theorem check_gas_binomial_excited_trace_bound {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ i : ι, sys.weight i = 1)
    (h_tr_le : ∀ σ : ι → Bool, hilbertTrace (sys.syndromeProjector σ) ≤ hilbertTrace sys.P0)
    {β' : ℝ} (hβ' : 0 ≤ β') :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) ≤
      ((1 + Real.exp (-β')) ^ Fintype.card ι - 1) * hilbertTrace sys.P0 := by
  let σ₀ : ι → Bool := fun _ => false
  have hP0_eq : sys.P0 = indexedBareFailureProjector sys {σ₀} := by
    rw [indexedBareFailureProjector, Finset.sum_singleton]
    exact (syndrome_resolution_indexed sys).1.symm
  have h_peel :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) ≤
      (∑ σ ∈ Finset.univ \ {σ₀}, Real.exp (-β' * sys.syndromeEnergy σ)) * hilbertTrace sys.P0 := by
    have h_eq : hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
        (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β' * (1 - sys.P0)) =
        ∑ σ ∈ Finset.univ \ {σ₀},
          Real.exp (-β' * sys.syndromeEnergy σ) * hilbertTrace (sys.syndromeProjector σ) := by
      rw [hP0_eq, (indexedBareFailureProjector_props sys {σ₀}).2, Finset.mul_sum, hilbertTrace_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hilbertTrace_gibbsBoltzmannOp_mul_eq,
        hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 (sys.syndromeProjector σ),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      let ψ := opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω
      let E_ω := opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω
      let P_σ := sys.syndromeProjector σ
      let t := RCLike.re (inner ℂ ψ (P_σ ψ))
      have h_res := syndrome_resolution_indexed sys
      have h1 : (P_σ * sys.H0) ψ = (E_ω : ℂ) • (P_σ ψ) := by
        change P_σ (sys.H0 ψ) = _
        rw [opEigenbasis_apply_H sys.H0 sys.isSelfAdjoint_H0 ω, map_smul]
      have h2 : (P_σ * sys.H0) ψ = (sys.syndromeEnergy σ : ℂ) • (P_σ ψ) := by
        have h_comm : P_σ * sys.H0 = sys.H0 * P_σ := (h_res.2.2.2.2.2.2.2 σ).symm.eq
        rw [h_comm, h_res.2.2.2.2.1 σ, ContinuousLinearMap.smul_apply]
      have h_in := congr_arg (fun v => RCLike.re (inner ℂ ψ v)) (h1.symm.trans h2)
      have h_eq_re : E_ω * t = sys.syndromeEnergy σ * t := by
        simpa only [t, inner_smul_right, re_ofReal_mul] using h_in
      have h_zero : (E_ω - sys.syndromeEnergy σ) * t = 0 := by linarith
      rcases mul_eq_zero.mp h_zero with hE | ht
      · have hE_eq : E_ω = sys.syndromeEnergy σ := sub_eq_zero.mp hE
        change Real.exp (-β' * E_ω) * t = Real.exp (-β' * sys.syndromeEnergy σ) * t
        rw [hE_eq]
      · change Real.exp (-β' * E_ω) * t = Real.exp (-β' * sys.syndromeEnergy σ) * t
        rw [ht, mul_zero, mul_zero]
    rw [h_eq, Finset.sum_mul]
    exact Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_left (h_tr_le σ) (le_of_lt (Real.exp_pos _))
  have h_syn_zero : sys.syndromeEnergy σ₀ = 0 := by
    unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy; simp [σ₀]
  have h_sdiff :
      (∑ σ ∈ Finset.univ \ {σ₀}, Real.exp (-β' * sys.syndromeEnergy σ)) + 1 =
        ∑ σ : ι → Bool, Real.exp (-β' * sys.syndromeEnergy σ) := by
    have h1 := Finset.sum_sdiff (Finset.subset_univ ({σ₀} : Finset (ι → Bool)))
      (f := fun σ => Real.exp (-β' * sys.syndromeEnergy σ))
    rw [Finset.sum_singleton, h_syn_zero, mul_zero, Real.exp_zero] at h1
    exact h1
  have h_sum_eq :
      (∑ σ ∈ Finset.univ \ {σ₀}, Real.exp (-β' * sys.syndromeEnergy σ)) =
        (1 + Real.exp (-β')) ^ Fintype.card ι - 1 := by
    have h_all := sum_exp_neg_mul_syndromeEnergy_eq_one_add_exp_pow sys h_wt β'
    linarith
  rwa [h_sum_eq] at h_peel

/-- If `P * Q = P` for two star projections `P` and `Q`, then `1 - Q ≤ 1 - P` in quadratic form. -/
private lemma re_inner_one_sub_le_of_mul_eq_left {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {P Q : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hPQ : P * Q = P)
    (ψ : ManyBodyHilbertSpace Site) :
    RCLike.re (inner ℂ ψ ((1 - Q) ψ)) ≤ RCLike.re (inner ℂ ψ ((1 - P) ψ)) := by
  have hQP : Q * P = P := by
    calc Q * P = star Q * star P := by rw [hQ.isSelfAdjoint.star_eq, hP.isSelfAdjoint.star_eq]
      _ = star (P * Q) := (star_mul P Q).symm
      _ = star P := by rw [hPQ]
      _ = P := hP.isSelfAdjoint.star_eq
  have h_one_sub_Q_mul_P : (1 - Q) * P = 0 := by rw [sub_mul, one_mul, hQP, sub_self]
  have h_apply : (1 - Q) ψ = (1 - Q) ((1 - P) ψ) := by
    have h_split : ψ = P ψ + (1 - P) ψ := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, add_sub_cancel]
    conv_lhs => rw [h_split]
    rw [map_add, ← ContinuousLinearMap.mul_apply, h_one_sub_Q_mul_P,
      ContinuousLinearMap.zero_apply, zero_add]
  rw [isStarProjection_re_inner_eq_norm_sq_bhm hQ.one_sub ψ,
    isStarProjection_re_inner_eq_norm_sq_bhm hP.one_sub ψ, h_apply]
  exact isStarProjection_norm_sq_apply_le_bhm hQ.one_sub ((1 - P) ψ)

/-- Bare eigenbasis dichotomy for `sys.H0`: at each `ω`, either `E_0 ω = 0` and
    `Re ⟨ψ_0 ω, (1 - sys.P0) (ψ_0 ω)⟩ = 0`, or `1 ≤ E_0 ω` and
    `Re ⟨ψ_0 ω, (1 - sys.P0) (ψ_0 ω)⟩ = 1`. -/
private lemma bare_eigenbasis_ground_or_excited_dichotomy {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ i : ι, 1 ≤ sys.weight i) (ω : ManyBodyConfig Site) :
    let ψ_0 := opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω
    let E_0 := opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω
    (E_0 = 0 ∧ RCLike.re (inner ℂ ψ_0 ((1 - sys.P0) ψ_0)) = 0) ∨
    (1 ≤ E_0 ∧ RCLike.re (inner ℂ ψ_0 ((1 - sys.P0) ψ_0)) = 1) := by
  intro ψ_0 E_0
  have hP0 : IsStarProjection sys.P0 := sys.isStarProjection_P0
  have h_re_norm : RCLike.re (inner ℂ ψ_0 ψ_0) = 1 :=
    (perturbed_norm_opEigenbasis_le_one sys.H0 sys.isSelfAdjoint_H0 ω).1
  have h_H0_re : RCLike.re (inner ℂ ψ_0 (sys.H0 ψ_0)) = E_0 := by
    change RCLike.re (inner ℂ ψ_0 (sys.H0 (opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω))) = E_0
    rw [opEigenbasis_apply_H sys.H0 sys.isSelfAdjoint_H0 ω, inner_smul_right,
      re_ofReal_mul, h_re_norm, mul_one]
  have h_gap_form : RCLike.re (inner ℂ ψ_0 ((1 - sys.P0) ψ_0)) ≤ E_0 := by
    have h1 := sys.one_sub_P0_form_le_H0_main h_wt ψ_0
    rwa [h_H0_re] at h1
  have h_nn : 0 ≤ RCLike.re (inner ℂ ψ_0 ((1 - sys.P0) ψ_0)) := hP0.one_sub.re_inner_nonneg ψ_0
  by_cases hE0 : E_0 = 0
  · exact Or.inl ⟨hE0, le_antisymm (by linarith) h_nn⟩
  · have h_zero : (E_0 : ℂ) • sys.P0 ψ_0 = 0 := by
      calc (E_0 : ℂ) • sys.P0 ψ_0
        _ = sys.P0 ((E_0 : ℂ) • ψ_0) := (map_smul sys.P0 (E_0 : ℂ) ψ_0).symm
        _ = sys.P0 (sys.H0 ψ_0) := by rw [← opEigenbasis_apply_H sys.H0 sys.isSelfAdjoint_H0 ω]
        _ = (sys.P0 * sys.H0) ψ_0 := rfl
        _ = (sys.H0 * sys.P0) ψ_0 := by rw [(sys.commute_H0_P0).symm.eq]
        _ = 0 := by rw [sys.ham0_mul_proj0_eq_zero, ContinuousLinearMap.zero_apply]
    have hP0_ψ : sys.P0 ψ_0 = 0 := (smul_eq_zero.mp h_zero).resolve_left (Complex.ofReal_ne_zero.mpr hE0)
    have h_re_one : RCLike.re (inner ℂ ψ_0 ((1 - sys.P0) ψ_0)) = 1 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hP0_ψ, sub_zero, h_re_norm]
    exact Or.inr ⟨by linarith, h_re_one⟩

/-- Positivity of `hilbertTrace sys.P0` when `sys.P0 ≠ 0`. -/
private lemma hilbertTrace_P0_pos {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι) (hP0_ne : sys.P0 ≠ 0) :
    0 < hilbertTrace sys.P0 := by
  let ψ_0 := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
  have hP0 : IsStarProjection sys.P0 := sys.isStarProjection_P0
  have h_nn : ∀ ω : ManyBodyConfig Site, 0 ≤ RCLike.re (inner ℂ (ψ_0 ω) (sys.P0 (ψ_0 ω))) :=
    fun ω => hP0.re_inner_nonneg (ψ_0 ω)
  have h_ge : 0 ≤ hilbertTrace sys.P0 := by
    rw [hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 sys.P0]
    exact Finset.sum_nonneg fun ω _ => h_nn ω
  refine lt_of_le_of_ne h_ge fun h_eq => hP0_ne ?_
  rw [hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 sys.P0] at h_eq
  have h_all := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => h_nn ω)).mp h_eq.symm
  apply ContinuousLinearMap.ext; intro v
  have h_id := onb_sum_ketBra_eq_one ψ_0
    (opEigenbasis_orthonormal sys.H0 sys.isSelfAdjoint_H0)
    (opEigenbasis_parseval sys.H0 sys.isSelfAdjoint_H0)
  have hv : v = ∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_0 ω) v := by
    calc v = (1 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) v := rfl
      _ = (∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_0 ω)) v := by rw [h_id]
      _ = ∑ ω : ManyBodyConfig Site, rankOneKetBra (ψ_0 ω) v := ContinuousLinearMap.sum_apply _ _ _
  rw [hv, map_sum, ContinuousLinearMap.zero_apply]
  refine Finset.sum_eq_zero fun ω _ => ?_
  have h_sq : ‖sys.P0 (ψ_0 ω)‖ ^ 2 = 0 := by
    rw [← isStarProjection_re_inner_eq_norm_sq_bhm hP0 (ψ_0 ω)]
    exact h_all ω (Finset.mem_univ ω)
  have h_zero : sys.P0 (ψ_0 ω) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp h_sq)
  rw [rankOneKetBra_apply, map_smul, h_zero, smul_zero]

/-- **Uniform-in-$\beta$ Ground- and Excited-Band Eigenvector Leakage Bound**. -/
theorem ground_and_excited_band_eigenvector_leakage_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ i : ι, 1 ≤ sys.weight i)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe)
    (hP0_safe : sys.P0 * Pi_safe = sys.P0)
    {E0 δ_0 : ℝ}
    (h_comm_P0 :
      let H := sys.H0 + V.totalPerturbation
      let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
      ‖H * P0_dress - P0_dress * H‖ ≤ δ_0 / 6)
    (h_form_q : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_0 / 4) * ‖ψ‖ ^ 2)
    (ω : ManyBodyConfig Site) :
    let H := sys.H0 + V.totalPerturbation
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    RCLike.re (inner ℂ (opEigenbasis H hH_pert ω)
        ((1 - Pi_safe_dress) (opEigenbasis H hH_pert ω))) ≤
      RCLike.re (inner ℂ (opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω)
        ((1 - sys.P0) (opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω))) + δ_0 := by
  intro H Pi_safe_dress
  let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
  let ψ_pert := opEigenbasis H hH_pert ω
  let ψ_0 := opEigenbasis sys.H0 sys.isSelfAdjoint_H0 ω
  let E_pert := opEigenvalues H hH_pert ω
  let E_0 := opEigenvalues sys.H0 sys.isSelfAdjoint_H0 ω
  have hδ_nn : 0 ≤ δ_0 := by
    have h_n := norm_nonneg (H * P0_dress - P0_dress * H); linarith [h_comm_P0]
  have hP0_dress : IsStarProjection P0_dress := isStarProjection_unitary_conj U_dress sys.isStarProjection_P0
  have hPi_dress : IsStarProjection Pi_safe_dress := isStarProjection_unitary_conj U_dress hPi
  have h_pert_norm : RCLike.re (inner ℂ ψ_pert ψ_pert) = 1 ∧ ‖ψ_pert‖ ≤ 1 :=
    perturbed_norm_opEigenbasis_le_one H hH_pert ω
  have h_lhs_le_one : RCLike.re (inner ℂ ψ_pert ((1 - Pi_safe_dress) ψ_pert)) ≤ 1 := by
    have h_add : RCLike.re (inner ℂ ψ_pert ((1 - Pi_safe_dress) ψ_pert)) +
        RCLike.re (inner ℂ ψ_pert (Pi_safe_dress ψ_pert)) = 1 := by
      rw [← map_add, ← inner_add_right, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, sub_add_cancel, h_pert_norm.1]
    linarith [hPi_dress.re_inner_nonneg ψ_pert]
  rcases bare_eigenbasis_ground_or_excited_dichotomy sys h_wt ω with ⟨hE0_eq, h_re0⟩ | ⟨_hE0_ge1, h_re1⟩
  · rw [h_re0, zero_add]
    by_cases hδ_ge1 : 1 ≤ δ_0
    · exact le_trans h_lhs_le_one hδ_ge1
    · push_neg at hδ_ge1
      have hP0_Pi_dress : P0_dress * Pi_safe_dress = P0_dress := by
        have hU_star : U_dress.1† * U_dress.1 = 1 := Unitary.coe_star_mul_self U_dress
        calc (U_dress.1 * sys.P0 * U_dress.1†) * (U_dress.1 * Pi_safe * U_dress.1†)
          _ = U_dress.1 * (sys.P0 * (U_dress.1† * U_dress.1) * Pi_safe) * U_dress.1† := by
              simp only [mul_assoc]
          _ = U_dress.1 * (sys.P0 * Pi_safe) * U_dress.1† := by rw [hU_star, mul_one]
          _ = P0_dress := by rw [hP0_safe]
      have h_le_P0 : RCLike.re (inner ℂ ψ_pert ((1 - Pi_safe_dress) ψ_pert)) ≤
          RCLike.re (inner ℂ ψ_pert ((1 - P0_dress) ψ_pert)) :=
        re_inner_one_sub_le_of_mul_eq_left hP0_dress hPi_dress hP0_Pi_dress ψ_pert
      let ψ_perp := (1 - P0_dress) ψ_pert
      rw [isStarProjection_re_inner_eq_norm_sq_bhm hP0_dress.one_sub ψ_pert] at h_le_P0
      have hP0_perp : P0_dress ψ_perp = 0 := by
        change (P0_dress * (1 - P0_dress)) ψ_pert = 0
        rw [mul_sub, mul_one, hP0_dress.isIdempotentElem.eq, sub_self, ContinuousLinearMap.zero_apply]
      have h_form_half : ∀ ψ : ManyBodyHilbertSpace Site,
          |RCLike.re (inner ℂ ψ
              ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
            bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + ((δ_0 / 2) / 2) * ‖ψ‖ ^ 2 := by
        intro ψ; have h1 := h_form_q ψ; rwa [show (δ_0 / 2) / 2 = δ_0 / 4 by ring]
      have h_qform_low := (dressed_ground_and_excited_band_quadratic_form_bounds
        sys h_wt V U_dress h_form_half).2 ψ_perp hP0_perp
      have h_ev_up : E_pert ≤ E0 + δ_0 / 4 := by
        have h_up := (perturbed_opEigenvalues_sandwich_of_unitary_form sys V hH_pert U_dress
          (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) h_form_q ω).2.2
        change E_pert ≤ E0 + (1 + 1 / 4) * E_0 + δ_0 / 4 at h_up
        linarith
      have hP0_adj : P0_dress† = P0_dress :=
        ContinuousLinearMap.isSelfAdjoint_iff'.mp hP0_dress.isSelfAdjoint
      have h_inner_P0_zero : ∀ v : ManyBodyHilbertSpace Site, inner ℂ ψ_perp (P0_dress v) = 0 := by
        intro v; rw [← ContinuousLinearMap.adjoint_inner_left, hP0_adj, hP0_perp, inner_zero_left]
      have h_eig_H : H ψ_pert = (E_pert : ℂ) • ψ_pert := opEigenbasis_apply_H H hH_pert ω
      have h_inner_H_pert :
          RCLike.re (inner ℂ ψ_perp ((H - (E0 : ℂ) • 1) ψ_pert)) =
            (E_pert - E0) * ‖ψ_perp‖ ^ 2 := by
        have h_apply : (H - (E0 : ℂ) • 1) ψ_pert = ((E_pert - E0 : ℝ) : ℂ) • ψ_pert := by
          rw [ContinuousLinearMap.sub_apply, h_eig_H, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply, ← sub_smul, Complex.ofReal_sub]
        have h_split : ψ_pert = P0_dress ψ_pert + ψ_perp := by
          dsimp [ψ_perp]; exact (add_sub_cancel _ _).symm
        rw [h_apply, inner_smul_right, re_ofReal_mul]
        conv_lhs => rw [h_split]
        rw [inner_add_right, h_inner_P0_zero ψ_pert, zero_add, inner_self_eq_norm_sq]
      have h_inner_H_P0 :
          inner ℂ ψ_perp ((H - (E0 : ℂ) • 1) (P0_dress ψ_pert)) =
            inner ℂ ψ_perp ((H * P0_dress - P0_dress * H) ψ_pert) := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, inner_sub_right, ← map_smul,
          h_inner_P0_zero ((E0 : ℂ) • ψ_pert), sub_zero,
          ContinuousLinearMap.sub_apply, inner_sub_right,
          show (P0_dress * H) ψ_pert = P0_dress (H ψ_pert) from rfl,
          h_inner_P0_zero (H ψ_pert), sub_zero]
        rfl
      have h_decomp_re :
          RCLike.re (inner ℂ ψ_perp ((H - (E0 : ℂ) • 1) ψ_perp)) =
            (E_pert - E0) * ‖ψ_perp‖ ^ 2 -
              RCLike.re (inner ℂ ψ_perp ((H * P0_dress - P0_dress * H) ψ_pert)) := by
        have h_sub : ψ_perp = ψ_pert - P0_dress ψ_pert := rfl
        conv_lhs => rw [
          show (H - (E0 : ℂ) • 1) ψ_perp =
            (H - (E0 : ℂ) • 1) ψ_pert - (H - (E0 : ℂ) • 1) (P0_dress ψ_pert) by
            rw [← map_sub, ← h_sub]]
        rw [inner_sub_right, map_sub, h_inner_H_pert, h_inner_H_P0]
      have h_perp_norm_le_one : ‖ψ_perp‖ ≤ 1 := by
        have h_sq : ‖ψ_perp‖ ^ 2 ≤ 1 ^ 2 := by
          calc ‖ψ_perp‖ ^ 2 ≤ ‖ψ_pert‖ ^ 2 :=
              isStarProjection_norm_sq_apply_le_bhm hP0_dress.one_sub ψ_pert
            _ ≤ 1 ^ 2 := by nlinarith [h_pert_norm.2, norm_nonneg ψ_pert]
        have h_abs := sq_le_sq.mp h_sq
        rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg zero_le_one] at h_abs
      have h_comm_re :
          -RCLike.re (inner ℂ ψ_perp ((H * P0_dress - P0_dress * H) ψ_pert)) ≤ δ_0 / 6 := by
        have h0 : -RCLike.re (inner ℂ ψ_perp ((H * P0_dress - P0_dress * H) ψ_pert)) ≤
            ‖inner ℂ ψ_perp ((H * P0_dress - P0_dress * H) ψ_pert)‖ := by
          have h_re := RCLike.re_le_norm (-inner ℂ ψ_perp ((H * P0_dress - P0_dress * H) ψ_pert))
          rwa [map_neg, norm_neg] at h_re
        have h1 : -RCLike.re (inner ℂ ψ_perp ((H * P0_dress - P0_dress * H) ψ_pert)) ≤
            ‖ψ_perp‖ * (‖H * P0_dress - P0_dress * H‖ * ‖ψ_pert‖) :=
          le_trans h0 (le_trans (norm_inner_le_norm _ _)
            (mul_le_mul_of_nonneg_left ((H * P0_dress - P0_dress * H).le_opNorm ψ_pert)
              (norm_nonneg _)))
        have h2 : ‖ψ_perp‖ * (‖H * P0_dress - P0_dress * H‖ * ‖ψ_pert‖) ≤ 1 * ((δ_0 / 6) * 1) :=
          mul_le_mul h_perp_norm_le_one
            (mul_le_mul h_comm_P0 h_pert_norm.2 (norm_nonneg _) (by linarith))
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
        linarith
      have h_pert_term : (E_pert - E0) * ‖ψ_perp‖ ^ 2 ≤ (δ_0 / 4) * ‖ψ_perp‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      have h_sq_nn : 0 ≤ ‖ψ_perp‖ ^ 2 := sq_nonneg _
      nlinarith
  · rw [h_re1]; linarith

/-- **Uniform-in-$\beta$ Unpinched Dressed Gibbs Failure Bound via Excited-Gap Absorption
    (Part II, Section 5.2 (`subsec:low-temp-crossover`), Proposition 5.2 (`prop:bhm-relative-form-bound`) and Theorem 5.3 (`thm:low-temperature-window-and-crossover`))**. -/
theorem gibbsFailureProb_dressed_le_unperturbed_half_beta_excited_add_split {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)] {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (h_wt : ∀ i : ι, 1 ≤ sys.weight i)
    (hP0_ne : sys.P0 ≠ 0)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (U_dress : unitary (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site))
    (Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hPi : IsStarProjection Pi_safe)
    (hP0_safe : sys.P0 * Pi_safe = sys.P0)
    {E0 δ_0 β : ℝ} (hβ : 0 ≤ β) (hδ_half : δ_0 ≤ 1 / 2)
    (h_comm_P0 :
      let H := sys.H0 + V.totalPerturbation
      let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
      ‖H * P0_dress - P0_dress * H‖ ≤ δ_0 / 6)
    (h_form_q : ∀ ψ : ManyBodyHilbertSpace Site,
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_0 / 4) * ‖ψ‖ ^ 2) :
    let H := sys.H0 + V.totalPerturbation
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    gibbsFailureProb H hH_pert β (1 - Pi_safe_dress) ≤
      (hilbertTrace sys.P0)⁻¹ *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
          (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((1 / 2 : ℝ) * β) * (1 - sys.P0)) + δ_0 := by
  intro H Pi_safe_dress
  let ψ_pert := opEigenbasis H hH_pert
  let E_pert := opEigenvalues H hH_pert
  let ψ_0 := opEigenbasis sys.H0 sys.isSelfAdjoint_H0
  let E_0 := opEigenvalues sys.H0 sys.isSelfAdjoint_H0
  have h_term_le : ∀ ω : ManyBodyConfig Site,
      Real.exp (-β * E_pert ω) *
        RCLike.re (inner ℂ (ψ_pert ω) ((1 - Pi_safe_dress) (ψ_pert ω))) ≤
      Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) *
        (Real.exp (-((1 / 2 : ℝ) * β) * E_0 ω) *
          RCLike.re (inner ℂ (ψ_0 ω) ((1 - sys.P0) (ψ_0 ω)))) +
      δ_0 * Real.exp (-β * E_pert ω) := by
    intro ω
    have h_leak := ground_and_excited_band_eigenvector_leakage_le
      sys h_wt V hH_pert U_dress Pi_safe hPi hP0_safe h_comm_P0 h_form_q ω
    have h_mul1 := mul_le_mul_of_nonneg_left h_leak (le_of_lt (Real.exp_pos (-β * E_pert ω)))
    have h_boltz_le :
        Real.exp (-β * E_pert ω) *
          RCLike.re (inner ℂ (ψ_0 ω) ((1 - sys.P0) (ψ_0 ω))) ≤
        Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) *
          (Real.exp (-((1 / 2 : ℝ) * β) * E_0 ω) *
            RCLike.re (inner ℂ (ψ_0 ω) ((1 - sys.P0) (ψ_0 ω)))) := by
      rcases bare_eigenbasis_ground_or_excited_dichotomy sys h_wt ω with ⟨_hE0, h_re0⟩ | ⟨hE0_ge1, h_re1⟩
      · rw [h_re0, mul_zero, mul_zero, mul_zero]
      · rw [h_re1, mul_one, mul_one, ← Real.exp_add]
        have h_ev_low := (perturbed_opEigenvalues_sandwich_of_unitary_form sys V hH_pert U_dress
          (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) h_form_q ω).2.1
        change E0 + (1 - 1 / 4) * E_0 ω - δ_0 / 4 ≤ E_pert ω at h_ev_low
        have h_absorb : E0 + (1 / 2 : ℝ) * (δ_0 / 2) + (1 / 2 : ℝ) * E_0 ω ≤ E_pert ω := by
          linarith
        exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have h_sum_le :
      hilbertTrace (gibbsBoltzmannOp ψ_pert E_pert β * (1 - Pi_safe_dress)) ≤
      Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) *
        hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0)) +
      δ_0 * gibbsPartitionZ E_pert β := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq, hilbertTrace_gibbsBoltzmannOp_mul_eq,
      gibbsPartitionZ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun ω _ => h_term_le ω
  have h_Z_low :
      Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) * hilbertTrace sys.P0 ≤
        gibbsPartitionZ E_pert β := by
    rw [hilbertTrace_eq_sum_opEigenbasis sys.H0 sys.isSelfAdjoint_H0 sys.P0,
      gibbsPartitionZ, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    have h_add_one : RCLike.re (inner ℂ (ψ_0 ω) ((1 - sys.P0) (ψ_0 ω))) +
        RCLike.re (inner ℂ (ψ_0 ω) (sys.P0 (ψ_0 ω))) = 1 := by
      rw [← map_add, ← inner_add_right, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, sub_add_cancel,
        (perturbed_norm_opEigenbasis_le_one sys.H0 sys.isSelfAdjoint_H0 ω).1]
    rcases bare_eigenbasis_ground_or_excited_dichotomy sys h_wt ω with ⟨hE0_eq, h_re0⟩ | ⟨_hE0_ge1, h_re1⟩
    · have hP0_one : RCLike.re (inner ℂ (ψ_0 ω) (sys.P0 (ψ_0 ω))) = 1 := by linarith
      rw [hP0_one, mul_one]
      have h_up := (perturbed_opEigenvalues_sandwich_of_unitary_form sys V hH_pert U_dress
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) h_form_q ω).2.2
      change E_pert ω ≤ E0 + (1 + 1 / 4) * E_0 ω + δ_0 / 4 at h_up
      exact Real.exp_le_exp.mpr (by nlinarith)
    · have hP0_zero : RCLike.re (inner ℂ (ψ_0 ω) (sys.P0 (ψ_0 ω))) = 0 := by linarith
      rw [hP0_zero, mul_zero]; exact le_of_lt (Real.exp_pos _)
  have hP0_pos : 0 < hilbertTrace sys.P0 := hilbertTrace_P0_pos sys hP0_ne
  have hP0_ne_r : hilbertTrace sys.P0 ≠ 0 := ne_of_gt hP0_pos
  have h_exc_nn : 0 ≤ hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0)) := by
    rw [hilbertTrace_gibbsBoltzmannOp_mul_eq]
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) (sys.isStarProjection_P0.one_sub.re_inner_nonneg _)
  have h_main_Z :
      Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) *
        hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0)) ≤
      ((hilbertTrace sys.P0)⁻¹ *
        hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0))) *
        gibbsPartitionZ E_pert β := by
    have h_id :
        Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) *
          hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0)) =
        ((hilbertTrace sys.P0)⁻¹ *
          hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0))) *
          (Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) * hilbertTrace sys.P0) := by
      calc Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) *
            hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0))
        _ = ((hilbertTrace sys.P0)⁻¹ * hilbertTrace sys.P0) *
              (Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) *
                hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0))) := by
            rw [inv_mul_cancel₀ hP0_ne_r, one_mul]
        _ = ((hilbertTrace sys.P0)⁻¹ *
              hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0))) *
              (Real.exp (-β * E0 - (1 / 2 : ℝ) * β * (δ_0 / 2)) * hilbertTrace sys.P0) := by ring
    rw [h_id]
    exact mul_le_mul_of_nonneg_left h_Z_low
      (mul_nonneg (inv_nonneg.mpr (le_of_lt hP0_pos)) h_exc_nn)
  have h_prod_le :
      gibbsFailureProb H hH_pert β (1 - Pi_safe_dress) * gibbsPartitionZ E_pert β ≤
      ((hilbertTrace sys.P0)⁻¹ *
        hilbertTrace (gibbsBoltzmannOp ψ_0 E_0 ((1 / 2 : ℝ) * β) * (1 - sys.P0)) + δ_0) *
        gibbsPartitionZ E_pert β := by
    rw [← perturbed_hilbertTrace_gibbsBoltzmannOp_eq_gibbsFailureProb_mul_partitionZ
      H hH_pert β (1 - Pi_safe_dress), add_mul]
    linarith
  exact le_of_mul_le_mul_right h_prod_le (gibbsPartitionZ_pos E_pert β)

private lemma nat_pow_eq_exp_mul_log {L : ℕ} (hL2 : 2 ≤ L) (m : ℕ) :
    ((L ^ m : ℕ) : ℝ) = Real.exp ((m : ℝ) * Real.log (L : ℝ)) := by
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  rw [Nat.cast_pow, Real.exp_nat_mul, Real.exp_log hL_pos]

private lemma binomial_exp_sub_one_le_vol_exp_quarter_beta {L N C_chk : ℕ}
    (hC_chk : 1 ≤ C_chk) (h_card : N ≤ C_chk * L ^ 3) (hL2 : 2 ≤ L)
    {β : ℝ} (hβ_scale : (4 * (C_chk : ℝ) + 4) * Real.log (L : ℝ) ≤ β) :
    (1 + Real.exp (-((1 / 2 : ℝ) * β))) ^ N - 1 ≤
      ((L ^ 3 : ℕ) : ℝ) * Real.exp (-(1 / 4 : ℝ) * β) := by
  have h_two_mul_le_pow : 2 * C_chk ≤ L ^ C_chk := by
    have hk : C_chk - 1 < 2 ^ (C_chk - 1) := (C_chk - 1).lt_two_pow_self
    have h_pow_eq : 2 * 2 ^ (C_chk - 1) = 2 ^ C_chk := by
      conv_rhs => rw [show C_chk = (C_chk - 1) + 1 by omega, pow_succ']
    exact le_trans (by omega : 2 * C_chk ≤ 2 ^ C_chk) (Nat.pow_le_pow_left hL2 C_chk)
  have h_log_nn : 0 ≤ Real.log (L : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
  have h_exp_Cchk : 2 * (C_chk : ℝ) * Real.exp (-(1 / 4 : ℝ) * β) ≤ 1 := by
    have h_cast : 2 * (C_chk : ℝ) ≤ ((L ^ C_chk : ℕ) : ℝ) := by exact_mod_cast h_two_mul_le_pow
    rw [nat_pow_eq_exp_mul_log hL2 C_chk] at h_cast
    have h_le_exp : Real.exp ((C_chk : ℝ) * Real.log (L : ℝ)) ≤ Real.exp ((1 / 4 : ℝ) * β) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h_prod := mul_le_mul_of_nonneg_right (le_trans h_cast h_le_exp)
      (le_of_lt (Real.exp_pos (-(1 / 4 : ℝ) * β)))
    rwa [← Real.exp_add, show (1 / 4 : ℝ) * β + -(1 / 4 : ℝ) * β = 0 by ring, Real.exp_zero] at h_prod
  have h_two_N_nat : 2 * N ≤ L ^ (2 * C_chk + 2) := by
    calc 2 * N ≤ 2 * (C_chk * L ^ 3) := Nat.mul_le_mul_left 2 h_card
      _ = (2 * C_chk) * L ^ 3 := by ring
      _ ≤ L ^ C_chk * L ^ 3 := Nat.mul_le_mul_right (L ^ 3) h_two_mul_le_pow
      _ = L ^ (C_chk + 3) := (pow_add L C_chk 3).symm
      _ ≤ L ^ (2 * C_chk + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  let y : ℝ := (N : ℝ) * Real.exp (-((1 / 2 : ℝ) * β))
  have hy_nn : 0 ≤ y := mul_nonneg (Nat.cast_nonneg N) (le_of_lt (Real.exp_pos _))
  have hy_half : 2 * y ≤ 1 := by
    have h_cast : 2 * (N : ℝ) ≤ ((L ^ (2 * C_chk + 2) : ℕ) : ℝ) := by exact_mod_cast h_two_N_nat
    rw [nat_pow_eq_exp_mul_log hL2 (2 * C_chk + 2), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h_cast
    have h_le_exp : Real.exp ((2 * (C_chk : ℝ) + 2) * Real.log (L : ℝ)) ≤
        Real.exp ((1 / 2 : ℝ) * β) := Real.exp_le_exp.mpr (by linarith)
    have h_prod := mul_le_mul_of_nonneg_right (le_trans h_cast h_le_exp)
      (le_of_lt (Real.exp_pos (-((1 / 2 : ℝ) * β))))
    rw [← Real.exp_add, show (1 / 2 : ℝ) * β + -((1 / 2 : ℝ) * β) = 0 by ring, Real.exp_zero] at h_prod
    dsimp [y]; linarith
  have h_pow_le_exp : (1 + Real.exp (-((1 / 2 : ℝ) * β))) ^ N ≤ Real.exp y := by
    have h1 : 1 + Real.exp (-((1 / 2 : ℝ) * β)) ≤ Real.exp (Real.exp (-((1 / 2 : ℝ) * β))) := by
      linarith [Real.add_one_le_exp (Real.exp (-((1 / 2 : ℝ) * β)))]
    have h2 : (1 + Real.exp (-((1 / 2 : ℝ) * β))) ^ N ≤
        (Real.exp (Real.exp (-((1 / 2 : ℝ) * β)))) ^ N :=
      pow_le_pow_left₀ (by positivity) h1 N
    rwa [← Real.exp_nat_mul] at h2
  have h_exp_y_sub_one : Real.exp y - 1 ≤ 2 * y := by
    have h_neg : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have h_mul : Real.exp y * (1 - y) ≤ 1 := by
      calc Real.exp y * (1 - y) ≤ Real.exp y * Real.exp (-y) :=
          mul_le_mul_of_nonneg_left h_neg (le_of_lt (Real.exp_pos y))
        _ = Real.exp (y + -y) := (Real.exp_add y (-y)).symm
        _ = 1 := by simp
    have h_quad : 1 ≤ (1 + 2 * y) * (1 - y) := by nlinarith
    nlinarith
  have h_two_y_le_vol : 2 * y ≤ ((L ^ 3 : ℕ) : ℝ) * Real.exp (-(1 / 4 : ℝ) * β) := by
    have h_N_le : (N : ℝ) ≤ (C_chk : ℝ) * ((L ^ 3 : ℕ) : ℝ) := by exact_mod_cast h_card
    have h_exp_split : Real.exp (-((1 / 2 : ℝ) * β)) =
        Real.exp (-(1 / 4 : ℝ) * β) * Real.exp (-(1 / 4 : ℝ) * β) := by
      rw [← Real.exp_add]; congr 1; ring
    have h_y_le : 2 * y ≤
        (2 * (C_chk : ℝ) * Real.exp (-(1 / 4 : ℝ) * β)) *
          (((L ^ 3 : ℕ) : ℝ) * Real.exp (-(1 / 4 : ℝ) * β)) := by
      dsimp [y]; rw [h_exp_split]
      have h_pos : 0 ≤ Real.exp (-(1 / 4 : ℝ) * β) * Real.exp (-(1 / 4 : ℝ) * β) := by positivity
      nlinarith
    have h_vol_nn : 0 ≤ ((L ^ 3 : ℕ) : ℝ) * Real.exp (-(1 / 4 : ℝ) * β) := by positivity
    nlinarith
  linarith

/-- **Logarithmic-Cooling Check-Gas & KMS Lindblad Trajectory Synthesis (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.4 (`thm:main-B`) and Section 5.2 (`subsec:low-temp-crossover`), Theorem 5.3 (`thm:low-temperature-window-and-crossover`))**. -/
theorem gibbsFailureProb_and_kms_bound_of_scaling_temp_bhm_form
    {L : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0] [Nonempty Site0]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) ι)
    (h_wt : ∀ i : ι, sys.weight i = 1)
    (hP0_ne : sys.P0 ≠ 0)
    (h_tr_le : ∀ σ : ι → Bool, hilbertTrace (sys.syndromeProjector σ) ≤ hilbertTrace sys.P0)
    {C_chk : ℕ} (hC_chk : 1 ≤ C_chk)
    (h_card_chk : Fintype.card ι ≤ C_chk * L ^ 3)
    (hL2 : 2 ≤ L)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L Site0))
    (U_dress : unitary (ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0)))
    (Pi_safe O_dec_Z O_dec_X : ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L Site0))
    (hPi : IsStarProjection Pi_safe) (hP0_safe : sys.P0 * Pi_safe = sys.P0)
    (hOZ_sa : IsSelfAdjoint O_dec_Z) (hOZ_norm : ‖O_dec_Z‖ ≤ 1)
    (hOX_sa : IsSelfAdjoint O_dec_X) (hOX_norm : ‖O_dec_X‖ ≤ 1)
    {E0 δ_0 : ℝ} (hδ_half : δ_0 ≤ 1 / 2)
    (h_comm_P0 :
      let H := sys.H0 + V.totalPerturbation
      let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
      ‖H * P0_dress - P0_dress * H‖ ≤ δ_0 / 6)
    (h_form_q : ∀ ψ : ManyBodyHilbertSpace (UniformSite3D L Site0),
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (sys.H0 + V.totalPerturbation) * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_0 / 4) * ‖ψ‖ ^ 2)
    (h_coh_Z :
      let H := sys.H0 + V.totalPerturbation; let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
      let O_Z_dress := U_dress.1 * O_dec_Z * U_dress.1†
      ‖Pi_safe_dress * (H * O_Z_dress - O_Z_dress * H) * Pi_safe_dress‖ ≤ δ_0)
    (h_coh_X :
      let H := sys.H0 + V.totalPerturbation; let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
      let O_X_dress := U_dress.1 * O_dec_X * U_dress.1†
      ‖Pi_safe_dress * (H * O_X_dress - O_X_dress * H) * Pi_safe_dress‖ ≤ δ_0)
    (h_1site : ∀ (v : Box3D L)
        (A_v : ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L Site0)),
      IsSupportedOn (UniformSite3D L Site0) {v} A_v →
      let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
      let O_Z_dress := U_dress.1 * O_dec_Z * U_dress.1†; let O_X_dress := U_dress.1 * O_dec_X * U_dress.1†
      ‖Pi_safe_dress * (A_v * O_Z_dress - O_Z_dress * A_v) * Pi_safe_dress‖ ≤ δ_0 * ‖A_v‖ ∧
      ‖Pi_safe_dress * (A_v * O_X_dress - O_X_dress * A_v) * Pi_safe_dress‖ ≤ δ_0 * ‖A_v‖) :
    let H := sys.H0 + V.totalPerturbation; let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    let C_scale : ℝ := 4 * (C_chk : ℝ) + 4; let c_F_pert : ℝ := 1 / 4
    ∀ (β : ℝ) (hH : IsSelfAdjoint H),
      C_scale * Real.log (L : ℝ) ≤ β →
      let p_log := ((L ^ 3 : ℕ) : ℝ) * Real.exp (-c_F_pert * β) + δ_0
      gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log ∧
      ∀ (bath : Finset (BathChannel 3 L (UniformSite3D L Site0)))
        (O_0 : ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L Site0)),
        (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
        (∀ ch ∈ bath, 0 ≤ ch.γ ∧
          ∃ v : Box3D L, ch.support = {v} ∧ IsSupportedOn (UniformSite3D L Site0) {v} ch.L) →
        let O_dress := U_dress.1 * O_0 * U_dress.1†
        ∀ (O_t : ℝ → (ManyBodyHilbertSpace (UniformSite3D L Site0) →L[ℂ]
            ManyBodyHilbertSpace (UniformSite3D L Site0))) (t : ℝ),
          0 ≤ t → SatisfiesKMSLindbladODE H hH β bath O_dress O_t t →
          opKMSNorm H hH β (O_t t - O_dress) ≤
            kmsDriftDirichletBound
              (2 * ‖H * O_dress - O_dress * H‖ * (p_log ^ (1 / 4 : ℝ)) + δ_0)
              ((∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (16 * (p_log ^ (1 / 2 : ℝ)) + δ_0)) t := by
  intro H Pi_safe_dress C_scale c_F_pert β hH hβ_scale p_log
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L Site0 x) := fun _ => inferInstance
  have h_log_nn : 0 ≤ Real.log (L : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ L))
  have hC_scale_pos : 0 < C_scale := by dsimp [C_scale]; positivity
  have hβ_nn : 0 ≤ β := le_trans (mul_nonneg (le_of_lt hC_scale_pos) h_log_nn) hβ_scale
  have h_wt_ge : ∀ i : ι, 1 ≤ sys.weight i := fun i => by rw [h_wt i]
  have h_step1 := gibbsFailureProb_dressed_le_unperturbed_half_beta_excited_add_split
    sys h_wt_ge hP0_ne V hH U_dress Pi_safe hPi hP0_safe hβ_nn hδ_half h_comm_P0 h_form_q
  have hβ_half_nn : 0 ≤ (1 / 2 : ℝ) * β := by linarith
  have h_binom := check_gas_binomial_excited_trace_bound sys h_wt h_tr_le hβ_half_nn
  have hP0_pos : 0 < hilbertTrace sys.P0 := hilbertTrace_P0_pos sys hP0_ne
  have hP0_ne_r : hilbertTrace sys.P0 ≠ 0 := ne_of_gt hP0_pos
  have h_inv_binom :
      (hilbertTrace sys.P0)⁻¹ *
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
          (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((1 / 2 : ℝ) * β) * (1 - sys.P0)) ≤
      (1 + Real.exp (-((1 / 2 : ℝ) * β))) ^ Fintype.card ι - 1 := by
    calc (hilbertTrace sys.P0)⁻¹ *
          hilbertTrace (gibbsBoltzmannOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) ((1 / 2 : ℝ) * β) * (1 - sys.P0))
      _ ≤ (hilbertTrace sys.P0)⁻¹ *
            (((1 + Real.exp (-((1 / 2 : ℝ) * β))) ^ Fintype.card ι - 1) * hilbertTrace sys.P0) :=
          mul_le_mul_of_nonneg_left h_binom (inv_nonneg.mpr (le_of_lt hP0_pos))
      _ = ((1 + Real.exp (-((1 / 2 : ℝ) * β))) ^ Fintype.card ι - 1) *
            ((hilbertTrace sys.P0)⁻¹ * hilbertTrace sys.P0) := by ring
      _ = (1 + Real.exp (-((1 / 2 : ℝ) * β))) ^ Fintype.card ι - 1 := by
          rw [inv_mul_cancel₀ hP0_ne_r, mul_one]
  have h_vol_bound := binomial_exp_sub_one_le_vol_exp_quarter_beta hC_chk h_card_chk hL2 hβ_scale
  have hp_log : gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log := by
    dsimp [p_log, c_F_pert]; linarith
  refine ⟨hp_log, ?_⟩
  intro bath O_0 hO_0 h_bath O_dress O_t t ht h_ode
  have hδ_nn : 0 ≤ δ_0 := by
    have h_n := norm_nonneg (H * (U_dress.1 * sys.P0 * U_dress.1†) -
      (U_dress.1 * sys.P0 * U_dress.1†) * H)
    linarith [h_comm_P0]
  have hPi_dress : IsStarProjection Pi_safe_dress := isStarProjection_unitary_conj U_dress hPi
  rcases hO_0 with rfl | rfl
  · have hO_dress_sa : IsSelfAdjoint O_dress := isSelfAdjoint_unitary_conj U_dress hOZ_sa
    have hO_dress_norm : ‖O_dress‖ ≤ 1 := le_trans (norm_unitary_conj_le U_dress O_0) hOZ_norm
    have h_bath_sq : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
        ‖Pi_safe_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_safe_dress‖ ^ 2 ≤
          ‖ch.L‖ ^ 2 * δ_0 := by
      intro ch hch
      refine ⟨(h_bath ch hch).1, ?_⟩
      have h1 := (h_1site (h_bath ch hch).2.choose ch.L (h_bath ch hch).2.choose_spec.2).1
      have h2 : ‖Pi_safe_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_safe_dress‖ ^ 2 ≤
          (δ_0 * ‖ch.L‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg ‖ch.L‖]
    exact opKMSNorm_le_kmsDriftDirichletBound_of_pinched_commutator_bounds
      H hH β bath O_dress Pi_safe_dress hO_dress_sa hO_dress_norm hPi_dress
      hp_log h_coh_Z h_bath_sq O_t t ht h_ode
  · have hO_dress_sa : IsSelfAdjoint O_dress := isSelfAdjoint_unitary_conj U_dress hOX_sa
    have hO_dress_norm : ‖O_dress‖ ≤ 1 := le_trans (norm_unitary_conj_le U_dress O_0) hOX_norm
    have h_bath_sq : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
        ‖Pi_safe_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_safe_dress‖ ^ 2 ≤
          ‖ch.L‖ ^ 2 * δ_0 := by
      intro ch hch
      refine ⟨(h_bath ch hch).1, ?_⟩
      have h1 := (h_1site (h_bath ch hch).2.choose ch.L (h_bath ch hch).2.choose_spec.2).2
      have h2 : ‖Pi_safe_dress * (ch.L * O_dress - O_dress * ch.L) * Pi_safe_dress‖ ^ 2 ≤
          (δ_0 * ‖ch.L‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg ‖ch.L‖]
    exact opKMSNorm_le_kmsDriftDirichletBound_of_pinched_commutator_bounds
      H hH β bath O_dress Pi_safe_dress hO_dress_sa hO_dress_norm hPi_dress
      hp_log h_coh_X h_bath_sq O_t t ht h_ode

end ScalingTempCheckGas
end
