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

import Proofs.TwoAxisMemorySynthesis.MacroscopicLambdaPowImmunity

open scoped Classical InnerProduct ComplexConjugate BigOperators
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open WeldedHierarchy WeldedHierarchy.BDLDecoder

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-!
# Finite-Range Perturbation Truncation, Zero Tail Leakage, and Cluster-Peeling Barrier Calibration

Formalizes the finite-interaction-range predicate `HasFiniteInteractionRange`, proves exact vanishing of safe-subspace commutators once the macroscopic protection scale exceeds the interaction range, and instantiates the dressed cluster-peeling free-energy barrier with welded-code parameters.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 2 (`subsec:setup`), Definition 2.3 (`def:perturbation-class`)
* Part II, Section 6 (`sec:lindblad`), Lemma 6.1 (`lem:kms-fourth-root`)
-/

/-! ## 1. Finite-Range Perturbation Predicate & Macroscopic Scale Absorption -/

/-- A quasi-local perturbation `V` on `BoxD D L` has finite interaction range `r_pert : ℕ` if all
    terms `V.term r A` at interaction scales `r > r_pert` vanish identically. -/
def HasFiniteInteractionRange {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (r_pert : ℕ) (V : QuasiLocalPerturbation D L Site) : Prop :=
  ∀ r > r_pert, ∀ A : Finset (BoxD D L), V.term r A = 0

/-- Dot-notation alias `V.HasFiniteInteractionRange r_pert`. -/
abbrev QuasiLocalPerturbation.HasFiniteInteractionRange {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site) (r_pert : ℕ) : Prop :=
  _root_.HasFiniteInteractionRange r_pert V

lemma hasFiniteInteractionRange_mono {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {r₁ r₂ : ℕ} {V : QuasiLocalPerturbation D L Site}
    (h_le : r₁ ≤ r₂) (hV : HasFiniteInteractionRange r₁ V) :
    HasFiniteInteractionRange r₂ V :=
  fun r hr A => hV r (lt_of_le_of_lt h_le hr) A

/-- For every finite interaction range `r_pert : ℕ`, any hierarchy level `k ≥ r_pert` satisfies
    `r_pert ≤ bdlLambda ^ k`. -/
lemma r_pert_le_bdlLambda_pow_of_le {r_pert k : ℕ} (hk : r_pert ≤ k) :
    r_pert ≤ bdlLambda ^ k := by
  have h1 : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
  have h2_real : (2 : ℝ) ≤ (bdlLambda : ℝ) := by
    have := bdlLambda_ge_10000
    linarith
  have h2 : 2 ≤ bdlLambda := by exact_mod_cast h2_real
  have h3 : 2 ^ k ≤ bdlLambda ^ k := Nat.pow_le_pow_left h2 k
  exact le_trans hk (le_trans h1 h3)

/-- Existence of a threshold level `k_0 := r_pert` above which `r_pert ≤ bdlLambda ^ k`. -/
lemma exists_k0_r_pert_le_bdlLambda_pow (r_pert : ℕ) :
    ∃ k_0 : ℕ, ∀ k : ℕ, k_0 ≤ k → r_pert ≤ bdlLambda ^ k :=
  ⟨r_pert, fun _ hk => r_pert_le_bdlLambda_pow_of_le hk⟩

/-- Under `HasFiniteInteractionRange r_pert V`, the total perturbation `V.totalPerturbation` truncates to
    scales `r ∈ Finset.Icc 1 (min r_pert L)`. -/
lemma v_tot_eq_sum_min_of_hasFiniteInteractionRange {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {r_pert : ℕ} {V : QuasiLocalPerturbation D L Site}
    (hV : HasFiniteInteractionRange r_pert V) :
    V.totalPerturbation = ∑ r ∈ Finset.Icc 1 (min r_pert L), ∑ A ∈ boxCubes D L r, V.term r A := by
  unfold QuasiLocalPerturbation.totalPerturbation
  refine (Finset.sum_subset (fun r hr => ?_) (fun r hr h_not => ?_)).symm
  · rw [Finset.mem_Icc] at hr ⊢
    exact ⟨hr.1, le_trans hr.2 (min_le_right r_pert L)⟩
  · rw [Finset.mem_Icc] at hr h_not
    have hr_gt : r > r_pert := by omega
    exact Finset.sum_eq_zero fun A _ => hV r hr_gt A

/-- Under `HasFiniteInteractionRange r_pert V`, the commutator `[V.V_tot, O_dec]` truncates to
    scales `r ∈ Finset.Icc 1 (min r_pert L)`. -/
lemma commutator_V_tot_eq_sum_min_of_hasFiniteInteractionRange {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {r_pert : ℕ} {V : QuasiLocalPerturbation D L Site}
    (hV : HasFiniteInteractionRange r_pert V)
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    V.totalPerturbation * O_dec - O_dec * V.totalPerturbation =
      ∑ r ∈ Finset.Icc 1 (min r_pert L), ∑ A ∈ boxCubes D L r,
        (V.term r A * O_dec - O_dec * V.term r A) := by
  rw [commutator_V_tot_eq_sum]
  refine (Finset.sum_subset (fun r hr => ?_) (fun r hr h_not => ?_)).symm
  · rw [Finset.mem_Icc] at hr ⊢
    exact ⟨hr.1, le_trans hr.2 (min_le_right r_pert L)⟩
  · rw [Finset.mem_Icc] at hr h_not
    have hr_gt : r > r_pert := by omega
    refine Finset.sum_eq_zero fun A _ => ?_
    simp [hV r hr_gt A]

/-- For a finite-range perturbation `HasFiniteInteractionRange r_pert V` satisfying
    `V.SatisfiesDecayBound J f` with `0 ≤ J` and `∀ r, 0 ≤ f r`, and `‖O_dec‖ ≤ 1`,
    $$\lVert [V_{\mathrm{tot}}, O_{\mathrm{dec}}] \rVert
      \le 2 J L^D \sum_{r=1}^{r_{\mathrm{pert}}} f(r)
      \le 2 J L^D \sum_{r=1}^L f(r).$$ -/
lemma norm_commutator_V_tot_le_of_hasFiniteInteractionRange {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {r_pert : ℕ} {V : QuasiLocalPerturbation D L Site}
    (hV_range : HasFiniteInteractionRange r_pert V)
    (O_dec : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_norm : ‖O_dec‖ ≤ 1)
    {J : ℝ} {f : ℕ → ℝ} (hJ_nn : 0 ≤ J) (hf_nn : ∀ r : ℕ, 0 ≤ f r)
    (hV_decay : V.SatisfiesDecayBound J f) :
    ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤
      2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 r_pert, f r := by
  rw [commutator_V_tot_eq_sum_min_of_hasFiniteInteractionRange hV_range O_dec]
  have h_sub_sum :
      (∑ r ∈ Finset.Icc 1 (min r_pert L), f r) ≤ ∑ r ∈ Finset.Icc 1 r_pert, f r := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) (fun r _ _ => hf_nn r)
    rw [Finset.mem_Icc] at hr ⊢
    exact ⟨hr.1, le_trans hr.2 (min_le_left r_pert L)⟩
  calc ‖∑ r ∈ Finset.Icc 1 (min r_pert L), ∑ A ∈ boxCubes D L r,
          (V.term r A * O_dec - O_dec * V.term r A)‖
    _ ≤ ∑ r ∈ Finset.Icc 1 (min r_pert L),
          ‖∑ A ∈ boxCubes D L r, (V.term r A * O_dec - O_dec * V.term r A)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 (min r_pert L), (2 * J * ((L : ℝ) ^ D) * f r) := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hrL : r ∈ Finset.Icc 1 L :=
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
          le_trans (Finset.mem_Icc.mp hr).2 (min_le_right r_pert L)⟩
      have h_inner : ‖∑ A ∈ boxCubes D L r, (V.term r A * O_dec - O_dec * V.term r A)‖ ≤
          ∑ A ∈ boxCubes D L r, (2 * (J * f r)) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun A hA => ?_)
        have h1 : ‖V.term r A * O_dec - O_dec * V.term r A‖ ≤ 2 * ‖V.term r A‖ :=
          norm_opCommutator_le_two_mul (V.term r A) hO_norm
        have h2 : ‖V.term r A‖ ≤ J * f r := hV_decay r hrL A hA
        linarith
      rw [Finset.sum_const, nsmul_eq_mul] at h_inner
      have h_card : ((boxCubes D L r).card : ℝ) ≤ (L : ℝ) ^ D := card_boxCubes_le D L r
      have h_jf_nn : 0 ≤ 2 * (J * f r) := by have := hf_nn r; positivity
      have h_mul : ((boxCubes D L r).card : ℝ) * (2 * (J * f r)) ≤
          ((L : ℝ) ^ D) * (2 * (J * f r)) :=
        mul_le_mul_of_nonneg_right h_card h_jf_nn
      linarith
    _ = 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 (min r_pert L), f r := by
      rw [← Finset.mul_sum]
    _ ≤ 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 r_pert, f r :=
      mul_le_mul_of_nonneg_left h_sub_sum (by positivity)

/-! ## 2. Exact Zero Tail Leakage ($\Gamma_{\mathrm{tail}} = 0$) & Finite-Range KMS Memory Lifetime -/

lemma opKMSNorm_le_opNorm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ)
    (A : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) :
    opKMSNorm H hH β A ≤ ‖A‖ :=
  kmsNorm_le_opNorm (opEigenbasis H hH) (opEigenvalues H hH) β
    (opEigenbasis_orthonormal H hH) (opEigenbasis_parseval H hH)
    (hilbertTrace_eq_sum_opEigenbasis H hH) A

lemma opKMSNorm_zero {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) :
    opKMSNorm H hH β 0 = 0 := by
  refine le_antisymm ?_ (Real.sqrt_nonneg _)
  have h := opKMSNorm_le_opNorm H hH β 0
  rwa [norm_zero] at h

/-- **Unconditional Zero Safe-Subspace Commutator for Finite-Range Perturbations
    (`pi_safe_commutator_V_tot_eq_zero_of_r_pert_le`)**:
    Whenever `r_pert ≤ r_fw`, `HasFiniteInteractionRange r_pert V`, and `Pi_safe` satisfies
    cube safe-subspace immunity on `Finset.Icc 1 r_fw`, the full safe-subspace commutator
    `Pi_safe * (V.V_tot * O_dec - O_dec * V.V_tot) * Pi_safe = 0` vanishes identically ($\Gamma_{\mathrm{tail}} = 0$). -/
theorem pi_safe_commutator_V_tot_eq_zero_of_r_pert_le {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    (V : QuasiLocalPerturbation D L Site)
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    {r_pert r_fw : ℕ} (h_range_le : r_pert ≤ r_fw)
    (hV_range : HasFiniteInteractionRange r_pert V)
    (h_fw : ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes D L r,
      Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0) :
    Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe = 0 := by
  have hV_fw : HasFiniteInteractionRange r_fw V :=
    hasFiniteInteractionRange_mono h_range_le hV_range
  rw [commutator_V_tot_eq_sum_min_of_hasFiniteInteractionRange hV_fw O_dec,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  have hr_fw : r ∈ Finset.Icc 1 r_fw :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      le_trans (Finset.mem_Icc.mp hr).2 (min_le_left r_fw L)⟩
  exact Finset.sum_eq_zero fun A hA => h_fw r hr_fw A hA

/-- **Level-$k$ Macroscopic Cube & Finite-Range Safe-Subspace Immunity for `bdlInhomogeneousSystem k`
    (`bdl_inhomogeneous_safe_projector_ball_safe_immunity_lambdaPow`)**:
    Lifts `bdl_inhomogeneous_safe_projector_and_macroscopic_immunity_exists k` to arbitrary
    finite-range perturbations with `r_pert ≤ bdlLambda ^ k`. -/
theorem bdl_inhomogeneous_safe_projector_ball_safe_immunity_lambdaPow (k : ℕ) :
    let L := bdlBoxSide k
    ∃ (Pi_safe O_dec_Z O_dec_X :
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      (∀ (v : Box3D L)
         (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
           ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
         IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v →
         Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
         Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0) ∧
      (∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 L r,
          Pi_safe * (V.term r A * O_dec_Z - O_dec_Z * V.term r A) * Pi_safe = 0 ∧
          Pi_safe * (V.term r A * O_dec_X - O_dec_X * V.term r A) * Pi_safe = 0) ∧
      (∀ (r_pert : ℕ), r_pert ≤ bdlLambda ^ k →
        ∀ (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
          HasFiniteInteractionRange r_pert V →
          Pi_safe * (V.totalPerturbation * O_dec_Z - O_dec_Z * V.totalPerturbation) * Pi_safe = 0 ∧
          Pi_safe * (V.totalPerturbation * O_dec_X - O_dec_X * V.totalPerturbation) * Pi_safe = 0) := by
  intro L
  rcases bdl_inhomogeneous_safe_projector_and_macroscopic_immunity_exists k with
    ⟨_sys, _Z_log, _X_log, Pi_safe, O_dec_Z, O_dec_X,
      _, _, _, _, _, _, _, _, _, _, _, _, h_fw_1site, h_fw_macro, _⟩
  refine ⟨Pi_safe, O_dec_Z, O_dec_X, h_fw_1site, h_fw_macro,
    fun r_pert hr_le V hV_range => ⟨?_, ?_⟩⟩
  · exact pi_safe_commutator_V_tot_eq_zero_of_r_pert_le V O_dec_Z Pi_safe hr_le hV_range
      (fun r hr A hA => (h_fw_macro V r hr A hA).1)
  · exact pi_safe_commutator_V_tot_eq_zero_of_r_pert_le V O_dec_X Pi_safe hr_le hV_range
      (fun r hr A hA => (h_fw_macro V r hr A hA).2)

/-- **Finite-Range Exact Zero Tail Leakage & KMS Memory Lifetime
    (`indexed_finite_range_kms_lifetime_of_cube_safe_immunity`)**:
    If `Pi_safe` and `O_dec` satisfy cube safe-subspace immunity up to scale `r_fw`, and `V` has finite
    interaction range `r_pert ≤ r_fw` (`HasFiniteInteractionRange r_pert V`), then:
    1. `Pi_safe * (V.V_tot * O_dec - O_dec * V.V_tot) * Pi_safe = 0` identically ($\Gamma_{\mathrm{tail}} = 0$);
    2. Both the operator norm and KMS norm of `Pi_safe * [V.V_tot, O_dec] * Pi_safe` vanish;
    3. `opKMSNorm (sys.H0 + V.V_tot) hH_pert β [V.V_tot, O_dec]` is bounded purely by the
       fourth-root Gibbs failure probability `2 * Γ_tot_range * (p_fail ^ (1 / 4 : ℝ))` with zero tail;
    4. Any KMS Lindblad trajectory `O_t` satisfies the zero-tail `kmsDriftDirichletBound` bound. -/
theorem indexed_finite_range_kms_lifetime_of_cube_safe_immunity {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site)
    (hH_pert : IsSelfAdjoint (sys.H0 + V.totalPerturbation))
    (β : ℝ)
    (bath : Finset (BathChannel D L Site))
    (O_dec Pi_safe : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hO_sa : IsSelfAdjoint O_dec) (hO_norm : ‖O_dec‖ ≤ 1)
    (h_comm_H0 : Commute sys.H0 O_dec)
    (hPi : IsStarProjection Pi_safe)
    {r_pert r_fw : ℕ} (h_range_le : r_pert ≤ r_fw)
    (hV_range : HasFiniteInteractionRange r_pert V)
    (h_fw : ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes D L r,
      Pi_safe * (V.term r A * O_dec - O_dec * V.term r A) * Pi_safe = 0)
    {J : ℝ} {f : ℕ → ℝ} (hJ_nn : 0 ≤ J) (hf_nn : ∀ r : ℕ, 0 ≤ f r)
    (hV_decay : V.SatisfiesDecayBound J f)
    (h_bath : ∀ ch ∈ bath, 0 ≤ ch.γ ∧
      Pi_safe * (ch.L * O_dec - O_dec * ch.L) * Pi_safe = 0)
    {p_fail : ℝ}
    (hp_le : gibbsFailureProb (sys.H0 + V.totalPerturbation) hH_pert β (1 - Pi_safe) ≤ p_fail) :
    let Γ_tot_range := 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 r_pert, f r
    let Γ_tot := 2 * J * ((L : ℝ) ^ D) * ∑ r ∈ Finset.Icc 1 L, f r
    Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe = 0 ∧
    ‖Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe‖ = 0 ∧
    opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β
      (Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe) = 0 ∧
    ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤ Γ_tot_range ∧
    ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤ Γ_tot ∧
    opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) ≤
      2 * ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)) ∧
    opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) ≤
      2 * Γ_tot_range * (p_fail ^ (1 / 4 : ℝ)) ∧
    (∀ (O_t : ℝ → (ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)) (t : ℝ),
      0 ≤ t →
      SatisfiesKMSLindbladODE (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec O_t t →
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (O_t t - O_dec) ≤
        kmsDriftDirichletBound
          (2 * ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)))
          (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
          t ∧
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (O_t t - O_dec) ≤
        kmsDriftDirichletBound
          (2 * Γ_tot_range * (p_fail ^ (1 / 4 : ℝ)))
          (16 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (p_fail ^ (1 / 2 : ℝ)))
          t) := by
  intro Γ_tot_range Γ_tot
  have hV_fw : HasFiniteInteractionRange r_fw V :=
    hasFiniteInteractionRange_mono h_range_le hV_range
  rcases pi_safe_commutator_V_tot_eq_zero_of_finite_range
      sys V hH_pert β O_dec Pi_safe hPi r_fw h_fw hV_fw hp_le with
    ⟨h_sand_zero, h_kms_exact⟩
  have h_norm_sand : ‖Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe‖ = 0 := by
    rw [h_sand_zero, norm_zero]
  have h_kms_sand :
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β
        (Pi_safe * (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) * Pi_safe) = 0 := by
    rw [h_sand_zero, opKMSNorm_zero]
  have h_tot_range : ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤ Γ_tot_range :=
    norm_commutator_V_tot_le_of_hasFiniteInteractionRange
      hV_range O_dec hO_norm hJ_nn hf_nn hV_decay
  have h_tot_L : ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ ≤ Γ_tot :=
    norm_commutator_V_tot_le V O_dec hO_norm hJ_nn hf_nn hV_decay
  have hp_nonneg : 0 ≤ p_fail :=
    le_trans (hilbertTrace_gibbsDensityOp_mul_proj_nonneg
      (opEigenbasis (sys.H0 + V.totalPerturbation) hH_pert) (opEigenvalues (sys.H0 + V.totalPerturbation) hH_pert) β
      (opEigenbasis_orthonormal (sys.H0 + V.totalPerturbation) hH_pert)
      (hilbertTrace_eq_sum_opEigenbasis (sys.H0 + V.totalPerturbation) hH_pert) hPi.one_sub) hp_le
  have h_rpow_nn : 0 ≤ p_fail ^ (1 / 4 : ℝ) := Real.rpow_nonneg hp_nonneg _
  have h_kms_range :
      opKMSNorm (sys.H0 + V.totalPerturbation) hH_pert β (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation) ≤
        2 * Γ_tot_range * (p_fail ^ (1 / 4 : ℝ)) := by
    have h_mul : 2 * ‖V.totalPerturbation * O_dec - O_dec * V.totalPerturbation‖ * (p_fail ^ (1 / 4 : ℝ)) ≤
        2 * Γ_tot_range * (p_fail ^ (1 / 4 : ℝ)) := by nlinarith
    linarith
  have hΓ_range_nn : 0 ≤ Γ_tot_range := le_trans (norm_nonneg _) h_tot_range
  have h_comm_H : opCommutator (sys.H0 + V.totalPerturbation) O_dec = V.totalPerturbation * O_dec - O_dec * V.totalPerturbation := by
    unfold opCommutator; rw [add_mul, mul_add, h_comm_H0.eq]; abel
  refine ⟨h_sand_zero, h_norm_sand, h_kms_sand, h_tot_range, h_tot_L, h_kms_exact, h_kms_range,
    fun O_t t ht h_ode => ⟨?_, ?_⟩⟩
  · exact opKMSNorm_le_kmsDriftDirichletBound_of_satisfiesKMSLindbladODE
      hH_pert β bath O_dec Pi_safe hO_sa hO_norm h_comm_H0 h_sand_zero hPi h_bath hp_le O_t t ht h_ode
  · exact opKMSNorm_le_kmsDriftDirichletBound_of_commutator_bound
      (sys.H0 + V.totalPerturbation) hH_pert β bath O_dec Pi_safe (V.totalPerturbation * O_dec - O_dec * V.totalPerturbation)
      hO_sa hO_norm h_comm_H (by positivity) h_kms_range hPi h_bath hp_le O_t t ht h_ode

/-! ## 3. Calibrated BDL Parameters & Instantiation of Dressed Thermal Barrier -/

lemma bdlClusterStepBase_pow_eight_gt_one :
    ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) > 1 := by
  have h2 : 2 ≤ bdlClusterStepBase := bdlClusterStepBase_ge_two
  have h_pow : 2 ≤ bdlClusterStepBase ^ 8 :=
    le_trans h2 (Nat.le_self_pow (by decide : 8 ≠ 0) bdlClusterStepBase)
  have h_cast : (2 : ℝ) ≤ ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) := by exact_mod_cast h_pow
  linarith

lemma log_nine_mul_bdlClusterStepBase_pow_eight_le_beta_c_BDL :
    Real.log (9 * ((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) ≤ betaCritBDL := by
  have hB8_pos : (0 : ℝ) < ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) := by
    linarith [bdlClusterStepBase_pow_eight_gt_one]
  have h9_exp : (9 : ℝ) ≤ Real.exp 100 := by
    have h := Real.add_one_le_exp 100
    linarith
  have h_log9 : Real.log 9 ≤ 100 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9) h9_exp
    rwa [Real.log_exp] at h
  rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (ne_of_gt hB8_pos)]
  linarith [log_bdlClusterStepBase_pow_eight_le_beta_c_BDL]

lemma one_le_clusterRawWeight_nat (k : ℕ) : 1 ≤ clusterRawWeight k := by
  have hw_ge1 : (1 : ℝ) ≤ ((clusterRawWeight k : ℕ) : ℝ) :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans (three_div_two_pow_le_clusterRawWeight k)
  exact_mod_cast hw_ge1

lemma c_F_BDL_mul_vol_pow_eta_le_clusterRawWeight (k : ℕ) :
    cFBDL * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL) ≤ (clusterRawWeight k : ℝ) := by
  have h_bar := bdlFreeEnergyBarrier_le_clusterRawWeight k
    (by linarith : betaCritBDL + 1 > betaCritBDL)
  dsimp [bdlFreeEnergyBarrier] at h_bar
  linarith

lemma syndromeSubsetProj_eq_indexedBareFailureProjector {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (S : Finset (ι → Bool)) :
    syndromeSubsetProj sys S = indexedBareFailureProjector sys S := rfl

end
