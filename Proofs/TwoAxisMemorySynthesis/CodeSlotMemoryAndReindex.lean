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

import Proofs.TwoAxisMemorySynthesis.SiteAlphabetTransport
import Proofs.TwoAxisMemorySynthesis.DaviesGeneratorBridge
import Proofs.KMSSafeSubspaceODE.CubeDressedCommutatorTelescoping

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Part1TwoAxisMemorySynthesis

/-!
# Abstract Memory Stability Predicates and Site-Alphabet Reindexing Invariance

Defines abstract predicates for safe decoded logical observables, unperturbed thermal and KMS Lindblad stability, and zero-temperature perturbative memory stability, and proves their invariance under sitewise Hilbert-space and check-index equivalences.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`)
-/

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]

/-! ## 1. Algebraic Simp Wrappers for `conjSiteOp` -/

section ConjSiteOpSimp

variable {D L : ℕ}
variable {Site0 Site1 : BoxD D L → Type}
variable [∀ x, Fintype (Site0 x)] [∀ x, DecidableEq (Site0 x)]
variable [∀ x, Fintype (Site1 x)] [∀ x, DecidableEq (Site1 x)]

@[simp] lemma conjSiteOp_one (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x) :
    conjSiteOp e 1 = 1 := conjEuclidean_one (cfgEquiv e)
@[simp] lemma conjSiteOp_zero (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x) :
    conjSiteOp e 0 = 0 := conjEuclidean_zero (cfgEquiv e)
@[simp] lemma conjSiteOp_add (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A B : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOp e (A + B) = conjSiteOp e A + conjSiteOp e B := rfl
@[simp] lemma conjSiteOp_sub (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A B : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOp e (A - B) = conjSiteOp e A - conjSiteOp e B := rfl
@[simp] lemma conjSiteOp_neg (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOp e (-A) = -conjSiteOp e A := rfl
@[simp] lemma conjSiteOp_smul (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x) (c : ℂ)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOp e (c • A) = c • conjSiteOp e A := rfl
@[simp] lemma conjSiteOp_mul (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A B : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOp e (A * B) = conjSiteOp e A * conjSiteOp e B := conjEuclidean_mul (cfgEquiv e) A B
@[simp] lemma conjSiteOp_adjoint (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    (conjSiteOp e A)† = conjSiteOp e (A†) := conjEuclidean_adjoint (cfgEquiv e) A
@[simp] lemma norm_conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    ‖conjSiteOp e A‖ = ‖A‖ := norm_conjEuclidean (cfgEquiv e) A

lemma conjSiteOp_commute_iff (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A B : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    Commute (conjSiteOp e A) (conjSiteOp e B) ↔ Commute A B :=
  conjEuclidean_commute_iff (cfgEquiv e) A B

lemma conjSiteOp_eq_zero_iff (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOp e A = 0 ↔ A = 0 := conjEuclidean_eq_zero_iff (cfgEquiv e) A

lemma conjSiteOp_eq_one_iff (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOp e A = 1 ↔ A = 1 := conjEuclidean_eq_one_iff (cfgEquiv e) A

lemma conjSiteOp_isSelfAdjoint (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    {A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (conjSiteOp e A) := conjEuclidean_isSelfAdjoint (cfgEquiv e) hA

lemma conjSiteOp_isStarProjection (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    {P : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0} (hP : IsStarProjection P) :
    IsStarProjection (conjSiteOp e P) := conjEuclidean_isStarProjection (cfgEquiv e) hP

/-- Continuous ℝ-linear map wrapper for `conjSiteOp e`. -/
def conjSiteOpCLM (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x) :
    (ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) →L[ℝ]
    (ManyBodyHilbertSpace Site1 →L[ℂ] ManyBodyHilbertSpace Site1) :=
  LinearMap.mkContinuous
    { toFun := conjSiteOp e, map_add' := conjSiteOp_add e, map_smul' := fun _ _ => rfl }
    1 (fun A => by rw [one_mul]; exact (norm_conjSiteOp e A).le)

@[simp]
lemma conjSiteOpCLM_apply (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    conjSiteOpCLM e A = conjSiteOp e A := rfl

lemma conjSiteOp_timeEvolutionOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (H₀ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) (t : ℝ) :
    conjSiteOp e (timeEvolutionOp H₀ t) = timeEvolutionOp (conjSiteOp e H₀) t := by
  let H₁ := conjSiteOp e H₀
  let F : ℝ → ManyBodyHilbertSpace Site1 →L[ℂ] ManyBodyHilbertSpace Site1 :=
    fun s => timeEvolutionOp H₁ (-s) * conjSiteOp e (timeEvolutionOp H₀ s)
  have hF_deriv : ∀ s : ℝ, HasDerivAt F 0 s := by
    intro s
    have hd1 := hasDerivAt_timeEvolutionOp_neg_right H₁ s
    have hd2 : HasDerivAt (fun u => conjSiteOp e (timeEvolutionOp H₀ u))
        ((Complex.I : ℂ) • (H₁ * conjSiteOp e (timeEvolutionOp H₀ s))) s := by
      have h0 := (conjSiteOpCLM e).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_timeEvolutionOp H₀ s)
      simpa only [Function.comp_def, conjSiteOpCLM_apply, conjSiteOp_smul, conjSiteOp_mul, H₁] using h0
    have hd := hd1.mul hd2
    rw [alg_unitary_deriv_cancel (timeEvolutionOp H₁ (-s)) H₁
      (conjSiteOp e (timeEvolutionOp H₀ s))] at hd
    exact hd
  have hFt : timeEvolutionOp H₁ (-t) * conjSiteOp e (timeEvolutionOp H₀ t) = 1 := by
    refine (eq_of_hasDerivAt_zero hF_deriv t).trans ?_
    dsimp [F]; rw [neg_zero, timeEvolutionOp_zero H₁, timeEvolutionOp_zero H₀, conjSiteOp_one, mul_one]
  calc conjSiteOp e (timeEvolutionOp H₀ t)
    _ = (timeEvolutionOp H₁ t * timeEvolutionOp H₁ (-t)) * conjSiteOp e (timeEvolutionOp H₀ t) := by
      rw [(timeEvolutionOp_mul_neg_self H₁ t).1, one_mul]
    _ = timeEvolutionOp H₁ t * (timeEvolutionOp H₁ (-t) * conjSiteOp e (timeEvolutionOp H₀ t)) := by
      rw [mul_assoc]
    _ = timeEvolutionOp H₁ t := by rw [hFt, mul_one]

lemma conjSiteOp_heisenbergFlow (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (H₀ A₀ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) (t : ℝ) :
    conjSiteOp e (heisenbergFlow H₀ t A₀) =
      heisenbergFlow (conjSiteOp e H₀) t (conjSiteOp e A₀) := by
  dsimp [heisenbergFlow]
  rw [conjSiteOp_mul, conjSiteOp_mul, conjSiteOp_timeEvolutionOp, conjSiteOp_timeEvolutionOp]

lemma inner_conjSiteOp (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (T₀ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0)
    (ψ₁ : ManyBodyHilbertSpace Site1) :
    inner ℂ ψ₁ (conjSiteOp e T₀ ψ₁) =
      inner ℂ (uReindex (cfgEquiv e).symm ψ₁) (T₀ (uReindex (cfgEquiv e).symm ψ₁)) := by
  have h := inner_uReindex (cfgEquiv e) (uReindex (cfgEquiv e).symm ψ₁)
    (T₀ (uReindex (cfgEquiv e).symm ψ₁))
  rw [uReindex_apply_symm (cfgEquiv e) ψ₁] at h
  exact h

lemma gibbsFailureProb_congr_H0
    {H₁ H₂ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0}
    (h : H₁ = H₂) (h₁ : IsSelfAdjoint H₁) (h₂ : IsSelfAdjoint H₂)
    (β : ℝ) (E : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0) :
    gibbsFailureProb H₁ h₁ β E = gibbsFailureProb H₂ h₂ β E := by
  subst h; rfl

lemma commute_syndromeSubsetProj_of_commute_checkProj
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι)
    {A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0}
    (hA : ∀ i : ι, Commute (sys.checkProj i) A)
    (S : Finset (ι → Bool)) :
    Commute (syndromeSubsetProj sys S) A := by
  dsimp [syndromeSubsetProj]
  exact Commute.sum_left _ _ _ fun σ _ =>
    (commute_syndromeProjector_of_commute_checkProj sys (fun i => (hA i).symm) σ).symm

lemma commute_syndromeSubsetProj_syndromeSignOp
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι)
    (S : Finset (ι → Bool)) (sgn : (ι → Bool) → ZMod 2) :
    Commute (syndromeSubsetProj sys S) (syndromeSignOp sys sgn) := by
  dsimp [syndromeSubsetProj]
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  rw [commute_iff_eq, syndromeProjector_mul_syndromeSignOp, syndromeSignOp_mul_syndromeProjector]

lemma commute_of_commute_checkProj_syndromeSignOp
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι)
    {A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0}
    (hA : ∀ i : ι, Commute (sys.checkProj i) A)
    (sgn : (ι → Bool) → ZMod 2) :
    Commute A (syndromeSignOp sys sgn) := by
  dsimp [syndromeSignOp]
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  rw [commute_iff_eq, clm_mul_smul, clm_smul_mul,
    (commute_syndromeProjector_of_commute_checkProj sys (fun i => (hA i).symm) σ).eq]

lemma commute_syndromeSignOp_syndromeSignOp
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site0 ι)
    (sgn₁ sgn₂ : (ι → Bool) → ZMod 2) :
    Commute (syndromeSignOp sys sgn₁) (syndromeSignOp sys sgn₂) := by
  have h1 : ∀ (A : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0),
      (∀ σ : ι → Bool, Commute (sys.syndromeProjector σ) A) →
      Commute (syndromeSignOp sys sgn₁) A := by
    intro A hA
    dsimp [syndromeSignOp]
    refine Commute.sum_left _ _ _ fun σ _ => ?_
    rw [commute_iff_eq, clm_smul_mul, clm_mul_smul, (hA σ).eq]
  refine h1 (syndromeSignOp sys sgn₂) fun σ => ?_
  rw [commute_iff_eq, syndromeProjector_mul_syndromeSignOp, syndromeSignOp_mul_syndromeProjector]

end ConjSiteOpSimp

/-! ## 2. Theorem 2 Helper Predicates -/

/-- **Strictly Increasing Open-Box Scale Sequence (`IsStrictlyIncreasingBoxSequence`)**:
    $L_k \ge k + 2$ and $L_k < L_{k+1}$ for all $k \in \mathbb{N}$. -/
abbrev IsStrictlyIncreasingBoxSequence (L : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, k + 2 ≤ L k ∧ L k < L (k + 1)

/-- **Decoded Logical Observables and Macroscopic Safe-Subspace Logical Immunity
    (`HasSafeDecodedLogicalObservables`)**. -/
def HasSafeDecodedLogicalObservables
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks))
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (R_imm : ℕ) : Prop :=
  sys.P0 ≠ 0 ∧ sys.P0 ≠ 1 ∧ 2 ≤ sys.groundDegeneracy ∧
  IsStarProjection Pi_safe ∧ Pi_safe ≠ 0 ∧ Pi_safe ≠ 1 ∧
  Commute sys.H0 Pi_safe ∧ sys.P0 * Pi_safe = sys.P0 ∧
  IsSelfAdjoint O_dec_Z ∧ O_dec_Z * O_dec_Z = 1 ∧ ‖O_dec_Z‖ ≤ 1 ∧
  Commute sys.H0 O_dec_Z ∧ Commute sys.P0 O_dec_Z ∧ Commute Pi_safe O_dec_Z ∧
  IsSelfAdjoint O_dec_X ∧ O_dec_X * O_dec_X = 1 ∧ ‖O_dec_X‖ ≤ 1 ∧
  Commute sys.H0 O_dec_X ∧ Commute sys.P0 O_dec_X ∧ Commute Pi_safe O_dec_X ∧
  (∀ i : Fin N_checks,
    Commute (sys.checkProj i) Pi_safe ∧
    Commute (sys.checkProj i) O_dec_Z ∧
    Commute (sys.checkProj i) O_dec_X) ∧
  Pi_safe * O_dec_Z * O_dec_X * Pi_safe = -(Pi_safe * O_dec_X * O_dec_Z * Pi_safe) ∧
  O_dec_Z * sys.P0 ≠ 0 ∧ O_dec_X * sys.P0 ≠ 0 ∧
  (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
    IsSupportedOn (UniformSite3D L Site0) {v} A_v →
    Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
    Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0) ∧
  (∀ r ∈ Finset.Icc 1 (min R_imm L), ∀ A ∈ boxCubes 3 L r, ∀ M_A : ℬ[L, Site0],
    IsSupportedOn (UniformSite3D L Site0) A M_A →
    Pi_safe * (M_A * O_dec_Z - O_dec_Z * M_A) * Pi_safe = 0 ∧
    Pi_safe * (M_A * O_dec_X - O_dec_X * M_A) * Pi_safe = 0)

/-- **Quasi-Local Dressing Unitary (`IsQuasiLocalUnitary`)**. -/
abbrev IsQuasiLocalUnitary {L : ℕ}
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (U_dress : unitary ℬ[L, Site0]) (g_dress : ℕ → ℝ) : Prop :=
  ∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
    IsSupportedOn (UniformSite3D L Site0) {v} A_v →
    ∀ r : ℕ,
      ‖U_dress.1† * A_v * U_dress.1 -
        condExp (UniformSite3D L Site0) (boxBall v r) (U_dress.1† * A_v * U_dress.1)‖ ≤
        ‖A_v‖ * g_dress r

/-- **Macroscopic Equilibrium Peierls Free-Energy Barrier and Stretched-Exponential KMS / GKLS
    Davies Memory Lifetime (`SatisfiesUnperturbedThermalAndKMSStability`)**. -/
def SatisfiesUnperturbedThermalAndKMSStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks))
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (R_imm w_0 : ℕ)
    (β_c c_F η : ℝ) : Prop :=
  ∀ β : ℝ, β > β_c →
    let ΔF := c_F * (β - β_c) * (((L ^ 3 : ℕ) : ℝ) ^ η)
    gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤ Real.exp (-ΔF) ∧
    (∀ (bath : Finset (BathChannel 3 L (UniformSite3D L Site0))) (O_0 : ℬ[L, Site0]),
      (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      IsCubeRangeBath 3 L R_imm bath →
      (IsAdjointSymmetricBath bath →
        ∀ t : ℝ, 0 ≤ t →
          SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0
            (fun s => opKMSLindbladSemigroup sys.H0 sys.isSelfAdjoint_H0 β bath s O_0) t) ∧
      (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
        0 ≤ t →
        SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_0 O_t t →
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t)) ∧
    (∀ (couplings : Finset (SingleSiteThermalCoupling 3 L (UniformSite3D L Site0) β))
      (O_0 : ℬ[L, Site0]),
      (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      (∀ t : ℝ, 0 ≤ t →
        IsCPUnitalStarMap (opDaviesThermalSemigroup sys β couplings t) ∧
        (∀ X : ℬ[L, Site0],
          hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β *
              opDaviesThermalSemigroup sys β couplings t X) =
          hilbertTrace (gibbsDensityOp (opEigenbasis sys.H0 sys.isSelfAdjoint_H0)
            (opEigenvalues sys.H0 sys.isSelfAdjoint_H0) β * X)) ∧
        SatisfiesDaviesThermalODE sys β couplings O_0
          (fun s => opDaviesThermalSemigroup sys β couplings s O_0) t) ∧
      (∀ (O_t : ℝ → ℬ[L, Site0]) (t : ℝ),
        0 ≤ t →
        SatisfiesDaviesThermalODE sys β couplings O_0 O_t t →
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
            Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖bohrEigenop sys c.S ω‖ ^ 2) *
            (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t ∧
        opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_0) ≤
          8 * (∑ c ∈ couplings, ∑ ω ∈ Finset.Icc (-(w_0 : ℤ)) (w_0 : ℤ),
            Real.exp (-β * (ω : ℝ) / 2) * c.h_spec ω * ‖c.S‖ ^ 2) *
            (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t))

/-- **Zero-Temperature Perturbative Full-Spectrum, Safe-Subspace, and Dynamical Memory Stability
    (`SatisfiesZeroTempPerturbativeMemoryStability`)**. -/
def SatisfiesZeroTempPerturbativeMemoryStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks))
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L Site0))
    (R_bath : ℕ)
    (δ_split : ℝ)
    (g_LR : ℕ → ℝ) : Prop :=
  let H := sys.H0 + V.totalPerturbation
  ∃ (U_dress : unitary ℬ[L, Site0]) (E0 : ℝ),
    let P0_dress := U_dress.1 * sys.P0 * U_dress.1†
    let Pi_safe_dress := U_dress.1 * Pi_safe * U_dress.1†
    IsQuasiLocalUnitary U_dress g_LR ∧
    ‖H * P0_dress - P0_dress * H‖ ≤ δ_split ∧
    ‖P0_dress * (H - (E0 : ℂ) • 1) * P0_dress‖ ≤ δ_split ∧
    (∀ ψ : ℋ[L, Site0],
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * H * U_dress.1 - sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2) ∧
    ∀ O_0 : ℬ[L, Site0], (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      let O_dress := U_dress.1 * O_0 * U_dress.1†
      ‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split ∧
      (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
        IsSupportedOn (UniformSite3D L Site0) {v} A_v →
        ‖Pi_safe_dress * (A_v * O_dress - O_dress * A_v) * Pi_safe_dress‖ ≤ δ_split * ‖A_v‖) ∧
      (∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, Site0],
        IsSupportedOn (UniformSite3D L Site0) W M_W →
        ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_split * ‖M_W‖) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split)

/-! ## 3. Abstract Check-Reindexing and Site-Alphabet Transport Lemmas -/

/-- Assembles `HasSafeDecodedLogicalObservables (sys.reindex e_chk)` for an abstract check
    index equivalence `e_chk : Idx ≃ Fin N_c`. -/
lemma hasSafeDecodedLogicalObservables_of_commute_reindex
    {L N_c R_imm : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (e_chk : Idx ≃ Fin N_c)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) Idx)
    (Z_log X_log Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (hZ_sq : Z_log * Z_log = 1) (hH0_Z : Commute sys.H0 Z_log) (hP0_Z : Commute sys.P0 Z_log)
    (hX_sq : X_log * X_log = 1) (hH0_X : Commute sys.H0 X_log)
    (h_ZX_anti_P0 : (Z_log * X_log + X_log * Z_log) * sys.P0 = 0)
    (hP0_ne0 : sys.P0 ≠ 0) (hP0_ne1 : sys.P0 ≠ 1)
    (hPi_proj : IsStarProjection Pi_safe) (hPi_ne0 : Pi_safe ≠ 0) (hPi_ne1 : Pi_safe ≠ 1)
    (hH0_Pi : Commute sys.H0 Pi_safe) (hP0_Pi : sys.P0 * Pi_safe = sys.P0)
    (hOZ_sa : IsSelfAdjoint O_dec_Z) (hOZ_sq : O_dec_Z * O_dec_Z = 1) (hOZ_norm : ‖O_dec_Z‖ ≤ 1)
    (hH0_OZ : Commute sys.H0 O_dec_Z) (hP0_OZ : Commute sys.P0 O_dec_Z) (hPi_OZ : Commute Pi_safe O_dec_Z)
    (hOX_sa : IsSelfAdjoint O_dec_X) (hOX_sq : O_dec_X * O_dec_X = 1) (hOX_norm : ‖O_dec_X‖ ≤ 1)
    (hH0_OX : Commute sys.H0 O_dec_X) (hP0_OX : Commute sys.P0 O_dec_X) (hPi_OX : Commute Pi_safe O_dec_X)
    (h_chk : ∀ idx : Idx,
      Commute (sys.checkProj idx) Pi_safe ∧
      Commute (sys.checkProj idx) O_dec_Z ∧
      Commute (sys.checkProj idx) O_dec_X)
    (h_anti : Pi_safe * O_dec_Z * O_dec_X * Pi_safe = -(Pi_safe * O_dec_X * O_dec_Z * Pi_safe))
    (hOZ_P0_ne : O_dec_Z * sys.P0 ≠ 0) (hOX_P0_ne : O_dec_X * sys.P0 ≠ 0)
    (h_1s : ∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
      IsSupportedOn (UniformSite3D L Site0) {v} A_v →
      Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
      Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0)
    (h_cube : ∀ r ∈ Finset.Icc 1 (min R_imm L), ∀ A ∈ boxCubes 3 L r, ∀ M_A : ℬ[L, Site0],
      IsSupportedOn (UniformSite3D L Site0) A M_A →
      Pi_safe * (M_A * O_dec_Z - O_dec_Z * M_A) * Pi_safe = 0 ∧
      Pi_safe * (M_A * O_dec_X - O_dec_X * M_A) * Pi_safe = 0) :
    HasSafeDecodedLogicalObservables (sys.reindex e_chk) Pi_safe O_dec_Z O_dec_X R_imm := by
  have hH0 : (sys.reindex e_chk).H0 = sys.H0 := sys.reindex_H0 e_chk
  have hP0 : (sys.reindex e_chk).P0 = sys.P0 := sys.reindex_P0 e_chk
  have h_deg : 2 ≤ (sys.reindex e_chk).groundDegeneracy :=
    two_le_groundDegeneracy_of_anticommuting_logicals (sys.reindex e_chk) Z_log X_log
      hZ_sq (by rwa [hH0]) (by rwa [hP0]) hX_sq (by rwa [hH0]) (by rwa [hP0])
  refine ⟨by rwa [hP0], by rwa [hP0], h_deg,
    hPi_proj, hPi_ne0, hPi_ne1, by rwa [hH0], by rwa [hP0],
    hOZ_sa, hOZ_sq, hOZ_norm, by rwa [hH0], by rwa [hP0], hPi_OZ,
    hOX_sa, hOX_sq, hOX_norm, by rwa [hH0], by rwa [hP0], hPi_OX,
    fun i => h_chk (e_chk.symm i), h_anti,
    by rwa [hP0], by rwa [hP0], h_1s, h_cube⟩

/-- Transports `HasSafeDecodedLogicalObservables` along a uniform site equivalence `e0 : SiteA ≃ SiteB`. -/
lemma hasSafeDecodedLogicalObservables_reindexHamiltonian
    {L N_checks R_imm : ℕ} [NeZero L]
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Fintype SiteB] [DecidableEq SiteB]
    (e0 : SiteA ≃ SiteB)
    (sys₀ : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteA) (Fin N_checks))
    (Pi_safe₀ O_dec_Z₀ O_dec_X₀ : ℬ[L, SiteA])
    (h₀ : HasSafeDecodedLogicalObservables sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀ R_imm) :
    let e : ∀ _ : Box3D L, SiteA ≃ SiteB := fun _ => e0
    HasSafeDecodedLogicalObservables (reindexHamiltonian e sys₀)
      (conjSiteOp e Pi_safe₀) (conjSiteOp e O_dec_Z₀) (conjSiteOp e O_dec_X₀) R_imm := by
  intro e
  let sys₁ := reindexHamiltonian e sys₀
  let Pi_safe₁ := conjSiteOp e Pi_safe₀
  let O_dec_Z₁ := conjSiteOp e O_dec_Z₀
  let O_dec_X₁ := conjSiteOp e O_dec_X₀
  have hH0₁ : sys₁.H0 = conjSiteOp e sys₀.H0 := reindexHamiltonian_H0 e sys₀
  have hP0₁ : sys₁.P0 = conjSiteOp e sys₀.P0 := reindexHamiltonian_P0 e sys₀
  rcases h₀ with ⟨hP0_ne0, hP0_ne1, _h_deg0,
    hPi_proj, hPi_ne0, hPi_ne1, hH0_Pi, hP0_Pi,
    hOZ_sa, hOZ_sq, hOZ_norm, hH0_OZ, hP0_OZ, hPi_OZ,
    hOX_sa, hOX_sq, hOX_norm, hH0_OX, hP0_OX, hPi_OX,
    h_chk0, h_anti0, hOZ_P0_ne, hOX_P0_ne, h_1s0, h_cube0⟩
  have h_Z_inv : O_dec_Z₁ * O_dec_Z₁ = 1 := by
    dsimp [O_dec_Z₁]; rw [← conjSiteOp_mul, hOZ_sq, conjSiteOp_one]
  have h_X_inv : O_dec_X₁ * O_dec_X₁ = 1 := by
    dsimp [O_dec_X₁]; rw [← conjSiteOp_mul, hOX_sq, conjSiteOp_one]
  have h_H0_OZ₁ : Commute sys₁.H0 O_dec_Z₁ := by
    rw [hH0₁]; exact (conjSiteOp_commute_iff e _ _).mpr hH0_OZ
  have h_P0_OZ₁ : Commute sys₁.P0 O_dec_Z₁ := by
    rw [hP0₁]; exact (conjSiteOp_commute_iff e _ _).mpr hP0_OZ
  have h_H0_OX₁ : Commute sys₁.H0 O_dec_X₁ := by
    rw [hH0₁]; exact (conjSiteOp_commute_iff e _ _).mpr hH0_OX
  have h_P0_OX₁ : Commute sys₁.P0 O_dec_X₁ := by
    rw [hP0₁]; exact (conjSiteOp_commute_iff e _ _).mpr hP0_OX
  have h_P0_Pi₁ : sys₁.P0 * Pi_safe₁ = sys₁.P0 := by
    rw [hP0₁]; dsimp [Pi_safe₁]; rw [← conjSiteOp_mul, hP0_Pi]
  have h_anti₁ : Pi_safe₁ * O_dec_Z₁ * O_dec_X₁ * Pi_safe₁ =
      -(Pi_safe₁ * O_dec_X₁ * O_dec_Z₁ * Pi_safe₁) := by
    dsimp [Pi_safe₁, O_dec_Z₁, O_dec_X₁]
    rw [← conjSiteOp_mul, ← conjSiteOp_mul, ← conjSiteOp_mul, h_anti0,
      conjSiteOp_neg, conjSiteOp_mul, conjSiteOp_mul, conjSiteOp_mul]
  have h_anti_P0₁ : (O_dec_Z₁ * O_dec_X₁ + O_dec_X₁ * O_dec_Z₁) * sys₁.P0 = 0 := by
    have hPi_P0₀ : Pi_safe₀ * sys₀.P0 = sys₀.P0 := by
      have h := congrArg star hP0_Pi
      rwa [star_mul, hPi_proj.isSelfAdjoint.star_eq,
        sys₀.isStarProjection_P0.isSelfAdjoint.star_eq] at h
    have h1 : sys₀.P0 * (Pi_safe₀ * O_dec_Z₀ * O_dec_X₀ * Pi_safe₀) * sys₀.P0 =
        O_dec_Z₀ * O_dec_X₀ * sys₀.P0 := by
      calc sys₀.P0 * (Pi_safe₀ * O_dec_Z₀ * O_dec_X₀ * Pi_safe₀) * sys₀.P0
        _ = (sys₀.P0 * Pi_safe₀) * O_dec_Z₀ * O_dec_X₀ * (Pi_safe₀ * sys₀.P0) := by
          simp only [mul_assoc]
        _ = sys₀.P0 * O_dec_Z₀ * O_dec_X₀ * sys₀.P0 := by rw [hP0_Pi, hPi_P0₀]
        _ = O_dec_Z₀ * (sys₀.P0 * O_dec_X₀) * sys₀.P0 := by
          rw [hP0_OZ.eq]; simp only [mul_assoc]
        _ = O_dec_Z₀ * O_dec_X₀ * (sys₀.P0 * sys₀.P0) := by
          rw [hP0_OX.eq]; simp only [mul_assoc]
        _ = O_dec_Z₀ * O_dec_X₀ * sys₀.P0 := by
          rw [sys₀.isStarProjection_P0.isIdempotentElem.eq]
    have h2 : sys₀.P0 * (Pi_safe₀ * O_dec_X₀ * O_dec_Z₀ * Pi_safe₀) * sys₀.P0 =
        O_dec_X₀ * O_dec_Z₀ * sys₀.P0 := by
      calc sys₀.P0 * (Pi_safe₀ * O_dec_X₀ * O_dec_Z₀ * Pi_safe₀) * sys₀.P0
        _ = (sys₀.P0 * Pi_safe₀) * O_dec_X₀ * O_dec_Z₀ * (Pi_safe₀ * sys₀.P0) := by
          simp only [mul_assoc]
        _ = sys₀.P0 * O_dec_X₀ * O_dec_Z₀ * sys₀.P0 := by rw [hP0_Pi, hPi_P0₀]
        _ = O_dec_X₀ * (sys₀.P0 * O_dec_Z₀) * sys₀.P0 := by
          rw [hP0_OX.eq]; simp only [mul_assoc]
        _ = O_dec_X₀ * O_dec_Z₀ * (sys₀.P0 * sys₀.P0) := by
          rw [hP0_OZ.eq]; simp only [mul_assoc]
        _ = O_dec_X₀ * O_dec_Z₀ * sys₀.P0 := by
          rw [sys₀.isStarProjection_P0.isIdempotentElem.eq]
    have h_anti_P0₀ : (O_dec_Z₀ * O_dec_X₀ + O_dec_X₀ * O_dec_Z₀) * sys₀.P0 = 0 := by
      rw [add_mul, ← h1, ← h2, h_anti0]
      ext ψ; simp
    rw [hP0₁]; dsimp [O_dec_Z₁, O_dec_X₁]
    rw [← conjSiteOp_mul, ← conjSiteOp_mul, ← conjSiteOp_add, ← conjSiteOp_mul,
      h_anti_P0₀, conjSiteOp_zero]
  have h_deg₁ : 2 ≤ sys₁.groundDegeneracy :=
    two_le_groundDegeneracy_of_anticommuting_logicals sys₁ O_dec_Z₁ O_dec_X₁
      h_Z_inv h_H0_OZ₁ h_P0_OZ₁ h_X_inv h_H0_OX₁ h_anti_P0₁
  refine ⟨sys₁.frustration_free,
    by rw [hP0₁]; exact mt (conjSiteOp_eq_one_iff e _).mp hP0_ne1,
    h_deg₁,
    conjSiteOp_isStarProjection e hPi_proj,
    mt (conjSiteOp_eq_zero_iff e _).mp hPi_ne0,
    mt (conjSiteOp_eq_one_iff e _).mp hPi_ne1,
    by rw [hH0₁]; exact (conjSiteOp_commute_iff e _ _).mpr hH0_Pi,
    h_P0_Pi₁,
    conjSiteOp_isSelfAdjoint e hOZ_sa, h_Z_inv,
    by rwa [norm_conjSiteOp],
    h_H0_OZ₁, h_P0_OZ₁,
    (conjSiteOp_commute_iff e _ _).mpr hPi_OZ,
    conjSiteOp_isSelfAdjoint e hOX_sa, h_X_inv,
    by rwa [norm_conjSiteOp],
    h_H0_OX₁, h_P0_OX₁,
    (conjSiteOp_commute_iff e _ _).mpr hPi_OX,
    fun i => ⟨(conjSiteOp_commute_iff e _ _).mpr (h_chk0 i).1,
      (conjSiteOp_commute_iff e _ _).mpr (h_chk0 i).2.1,
      (conjSiteOp_commute_iff e _ _).mpr (h_chk0 i).2.2⟩,
    h_anti₁,
    by rw [hP0₁]; dsimp [O_dec_Z₁]; rw [← conjSiteOp_mul]
       exact mt (conjSiteOp_eq_zero_iff e _).mp hOZ_P0_ne,
    by rw [hP0₁]; dsimp [O_dec_X₁]; rw [← conjSiteOp_mul]
       exact mt (conjSiteOp_eq_zero_iff e _).mp hOX_P0_ne,
    fun v A_v hA_v => ?_,
    fun r hr A hA M_A hM_A => ?_⟩
  · let e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA := fun _ => e0.symm
    let A_v₀ := conjSiteOp e_inv A_v
    have hA_v₀ : IsSupportedOn (UniformSite3D L SiteA) {v} A_v₀ :=
      isSupportedOn_conjSiteOp e_inv hA_v
    have hA_eq : A_v = conjSiteOp e A_v₀ :=
      (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) A_v).symm
    rcases h_1s0 v A_v₀ hA_v₀ with ⟨hZ0, hX0⟩
    refine ⟨?_, ?_⟩
    · rw [hA_eq]
      rw [← conjSiteOp_mul, ← conjSiteOp_mul, ← conjSiteOp_sub,
        ← conjSiteOp_mul, ← conjSiteOp_mul, hZ0, conjSiteOp_zero]
    · rw [hA_eq]
      rw [← conjSiteOp_mul, ← conjSiteOp_mul, ← conjSiteOp_sub,
        ← conjSiteOp_mul, ← conjSiteOp_mul, hX0, conjSiteOp_zero]
  · let e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA := fun _ => e0.symm
    let M_A₀ := conjSiteOp e_inv M_A
    have hM_A₀ : IsSupportedOn (UniformSite3D L SiteA) A M_A₀ :=
      isSupportedOn_conjSiteOp e_inv hM_A
    have hM_eq : M_A = conjSiteOp e M_A₀ :=
      (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) M_A).symm
    rcases h_cube0 r hr A hA M_A₀ hM_A₀ with ⟨hZ0, hX0⟩
    refine ⟨?_, ?_⟩
    · rw [hM_eq]
      rw [← conjSiteOp_mul, ← conjSiteOp_mul, ← conjSiteOp_sub,
        ← conjSiteOp_mul, ← conjSiteOp_mul, hZ0, conjSiteOp_zero]
    · rw [hM_eq]
      rw [← conjSiteOp_mul, ← conjSiteOp_mul, ← conjSiteOp_sub,
        ← conjSiteOp_mul, ← conjSiteOp_mul, hX0, conjSiteOp_zero]

/-- Transports `SatisfiesUnperturbedThermalAndKMSStability` along `e0 : SiteA ≃ SiteB` and
    `e_chk : Idx ≃ Fin N_checks`. -/
lemma satisfiesUnperturbedThermalAndKMSStability_reindexHamiltonian
    {L N_checks r_0 w_0 R_imm : ℕ} [NeZero L]
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Nonempty SiteA]
    [Fintype SiteB] [DecidableEq SiteB] [Nonempty SiteB]
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (e0 : SiteA ≃ SiteB) (e_chk : Idx ≃ Fin N_checks)
    (sys₀ : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteA) Idx)
    (S_safe : Finset (Idx → Bool))
    (Pi_safe₀ O_dec_Z₀ O_dec_X₀ : ℬ[L, SiteA])
    (h_Pi_eq : Pi_safe₀ = syndromeSubsetProj sys₀ S_safe)
    (h_loc₁ : (reindexHamiltonian (fun _ : Box3D L => e0) (sys₀.reindex e_chk)).IsGeometricallyLocal r_0 w_0)
    (h_unit₁ : ∀ i : Fin N_checks,
      (reindexHamiltonian (fun _ : Box3D L => e0) (sys₀.reindex e_chk)).weight i = 1)
    (hR_le : 4 * r_0 + 1 ≤ R_imm)
    {β_c c_F η : ℝ}
    (h_pfail₀ : ∀ β : ℝ, β > β_c →
      gibbsFailureProb sys₀.H0 sys₀.isSelfAdjoint_H0 β (1 - Pi_safe₀) ≤
        Real.exp (- (c_F * (β - β_c) * (((L ^ 3 : ℕ) : ℝ) ^ η))))
    (h_obs₁ :
      let e : ∀ _ : Box3D L, SiteA ≃ SiteB := fun _ => e0
      HasSafeDecodedLogicalObservables (reindexHamiltonian e (sys₀.reindex e_chk))
        (conjSiteOp e Pi_safe₀) (conjSiteOp e O_dec_Z₀) (conjSiteOp e O_dec_X₀) R_imm) :
    let e : ∀ _ : Box3D L, SiteA ≃ SiteB := fun _ => e0
    SatisfiesUnperturbedThermalAndKMSStability
      (reindexHamiltonian e (sys₀.reindex e_chk))
      (conjSiteOp e Pi_safe₀) (conjSiteOp e O_dec_Z₀) (conjSiteOp e O_dec_X₀)
      R_imm w_0 β_c c_F η := by
  intro e β hβ
  let sys₁ := reindexHamiltonian e (sys₀.reindex e_chk)
  let Pi_safe₁ := conjSiteOp e Pi_safe₀
  let O_dec_Z₁ := conjSiteOp e O_dec_Z₀
  let O_dec_X₁ := conjSiteOp e O_dec_X₀
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteA x) := fun _ => inferInstance
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteB x) := fun _ => inferInstance
  have h_H0_eq_base : sys₁.H0 = (reindexHamiltonian e sys₀).H0 := by
    rw [reindexHamiltonian_H0, reindexHamiltonian_H0, sys₀.reindex_H0 e_chk]
  have h_Pi_eq_sub : Pi_safe₁ = syndromeSubsetProj (reindexHamiltonian e sys₀) S_safe := by
    dsimp [Pi_safe₁]
    rw [h_Pi_eq, syndromeSubsetProj_reindexHamiltonian]
  have h_pfail_eq :
      gibbsFailureProb sys₁.H0 sys₁.isSelfAdjoint_H0 β (1 - Pi_safe₁) =
      gibbsFailureProb sys₀.H0 sys₀.isSelfAdjoint_H0 β (1 - Pi_safe₀) := by
    rw [gibbsFailureProb_congr_H0 h_H0_eq_base sys₁.isSelfAdjoint_H0
      (reindexHamiltonian e sys₀).isSelfAdjoint_H0 β (1 - Pi_safe₁),
      h_Pi_eq_sub, gibbsFailureProb_reindexHamiltonian_syndromeSubsetProj, ← h_Pi_eq]
  have h_pfail_le : gibbsFailureProb sys₁.H0 sys₁.isSelfAdjoint_H0 β (1 - Pi_safe₁) ≤
      Real.exp (- (c_F * (β - β_c) * (((L ^ 3 : ℕ) : ℝ) ^ η))) := by
    rw [h_pfail_eq]; exact h_pfail₀ β hβ
  rcases h_obs₁ with ⟨_hP0_ne0, _hP0_ne1, _h_deg,
    hPi_proj, _hPi_ne0, _hPi_ne1, _hH0_Pi, _hP0_Pi,
    hOZ_sa, _hOZ_sq, hOZ_norm, hH0_OZ, _hP0_OZ, _hPi_OZ,
    hOX_sa, _hOX_sq, hOX_norm, hH0_OX, _hP0_OX, _hPi_OX,
    _h_chk, _h_anti, _hOZ_P0_ne, _hOX_P0_ne, _h_1s₁, h_cube₁⟩
  have hZ_bounds := unperturbed_cube_kms_and_davies_lifetime_bounds
    sys₁ h_loc₁ h_unit₁ hR_le Pi_safe₁ O_dec_Z₁ hPi_proj hOZ_sa hOZ_norm hH0_OZ
    (fun r hr A hA M_A hM_A => (h_cube₁ r hr A hA M_A hM_A).1)
    (Real.exp_nonneg _) h_pfail_le
  have hX_bounds := unperturbed_cube_kms_and_davies_lifetime_bounds
    sys₁ h_loc₁ h_unit₁ hR_le Pi_safe₁ O_dec_X₁ hPi_proj hOX_sa hOX_norm hH0_OX
    (fun r hr A hA M_A hM_A => (h_cube₁ r hr A hA M_A hM_A).2)
    (Real.exp_nonneg _) h_pfail_le
  refine ⟨h_pfail_le, ?_, ?_⟩
  · intro bath O_0 hO_0 h_bath
    rcases hO_0 with rfl | rfl
    · exact hZ_bounds.1 bath h_bath
    · exact hX_bounds.1 bath h_bath
  · intro couplings O_0 hO_0
    rcases hO_0 with rfl | rfl
    · exact hZ_bounds.2 couplings
    · exact hX_bounds.2 couplings

/-- Transport of `SatisfiesZeroTempPerturbativeMemoryStability` along a uniform site bijection
    `e0 : SiteA ≃ SiteB`. -/
lemma satisfiesZeroTempPerturbativeMemoryStability_reindexHamiltonian
    {L N_checks R_bath : ℕ} [NeZero L]
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Fintype SiteB] [DecidableEq SiteB]
    (e0 : SiteA ≃ SiteB)
    (sys₀ : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteA) (Fin N_checks))
    (Pi_safe₀ O_dec_Z₀ O_dec_X₀ : ℬ[L, SiteA])
    (_hOZ_norm : ‖O_dec_Z₀‖ ≤ 1) (_hP0_OZ : Commute sys₀.P0 O_dec_Z₀)
    (_hOX_norm : ‖O_dec_X₀‖ ≤ 1) (_hP0_OX : Commute sys₀.P0 O_dec_X₀)
    (V₁ : QuasiLocalPerturbation 3 L (UniformSite3D L SiteB))
    {δ_split : ℝ} {g_LR : ℕ → ℝ}
    (h_stab₀ :
      let e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA := fun _ => e0.symm
      SatisfiesZeroTempPerturbativeMemoryStability sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀
        (reindexPerturbation e_inv V₁) R_bath δ_split g_LR) :
    let e : ∀ _ : Box3D L, SiteA ≃ SiteB := fun _ => e0
    SatisfiesZeroTempPerturbativeMemoryStability
      (reindexHamiltonian e sys₀)
      (conjSiteOp e Pi_safe₀) (conjSiteOp e O_dec_Z₀) (conjSiteOp e O_dec_X₀)
      V₁ R_bath δ_split g_LR := by
  intro e
  let e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA := fun _ => e0.symm
  let V₀ := reindexPerturbation e_inv V₁
  let sys₁ := reindexHamiltonian e sys₀
  let Pi_safe₁ := conjSiteOp e Pi_safe₀
  let O_dec_Z₁ := conjSiteOp e O_dec_Z₀
  let O_dec_X₁ := conjSiteOp e O_dec_X₀
  have h_V_tot : V₁.totalPerturbation = conjSiteOp e V₀.totalPerturbation := by
    have h1 := reindexPerturbation_V_tot e V₀
    have h2 : reindexPerturbation e V₀ = V₁ := by
      cases V₁; simp only [V₀, reindexPerturbation, conjSiteOp]; congr; funext r A
      exact conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) _
    rwa [h2] at h1
  have h_H0 : sys₁.H0 = conjSiteOp e sys₀.H0 := reindexHamiltonian_H0 e sys₀
  have h_P0 : sys₁.P0 = conjSiteOp e sys₀.P0 := reindexHamiltonian_P0 e sys₀
  rcases h_stab₀ with ⟨U₀, E0, h_ql₀, h_comm₀, h_split₀, h_form₀, h_obs₀⟩
  let U₁ : unitary ℬ[L, SiteB] := conjEuclideanUnitary (cfgEquiv e) U₀
  have h_U₁ : U₁.1 = conjSiteOp e U₀.1 := rfl
  have h_H₁ : sys₁.H0 + V₁.totalPerturbation = conjSiteOp e (sys₀.H0 + V₀.totalPerturbation) := by rw [h_H0, h_V_tot]; rfl
  have h_P0_dress : U₁.1 * sys₁.P0 * U₁.1† = conjSiteOp e (U₀.1 * sys₀.P0 * U₀.1†) := by
    rw [h_U₁, h_P0]; simp only [conjSiteOp_adjoint, conjSiteOp_mul]
  have h_Pi_dress : U₁.1 * Pi_safe₁ * U₁.1† = conjSiteOp e (U₀.1 * Pi_safe₀ * U₀.1†) := by
    rw [h_U₁]; simp only [Pi_safe₁, conjSiteOp_adjoint, conjSiteOp_mul]
  have h_form₁ : ∀ ψ₁ : ℋ[L, SiteB],
      |RCLike.re (inner ℂ ψ₁ ((U₁.1† * (sys₁.H0 + V₁.totalPerturbation) * U₁.1 - sys₁.H0 - (E0 : ℂ) • 1) ψ₁))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ₁ (sys₁.H0 ψ₁)) + (δ_split / 2) * ‖ψ₁‖ ^ 2 := by
    intro ψ₁
    let ψ₀ := uReindex (cfgEquiv e).symm ψ₁
    have h_op : U₁.1† * (sys₁.H0 + V₁.totalPerturbation) * U₁.1 - sys₁.H0 - (E0 : ℂ) • 1 =
        conjSiteOp e (U₀.1† * (sys₀.H0 + V₀.totalPerturbation) * U₀.1 - sys₀.H0 - (E0 : ℂ) • 1) := by
      rw [h_U₁, h_H₁, h_H0]
      simp only [conjSiteOp_adjoint, conjSiteOp_mul, conjSiteOp_sub, conjSiteOp_smul, conjSiteOp_one]
    rw [h_op, inner_conjSiteOp e, h_H0, inner_conjSiteOp e, ← norm_uReindex (cfgEquiv e).symm ψ₁]
    exact h_form₀ ψ₀
  refine ⟨U₁, E0, ?_, ?_, ?_, h_form₁, ?_⟩
  · intro v A_v hA_v r
    let A_v₀ := conjSiteOp e_inv A_v
    have hA_v₀_supp : IsSupportedOn (UniformSite3D L SiteA) {v} A_v₀ :=
      isSupportedOn_conjSiteOp e_inv hA_v
    have hA_v_eq : A_v = conjSiteOp e A_v₀ :=
      (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) A_v).symm
    have h_conj : U₁.1† * A_v * U₁.1 = conjSiteOp e (U₀.1† * A_v₀ * U₀.1) := by
      rw [h_U₁, hA_v_eq]
      simp only [conjSiteOp_adjoint, conjSiteOp_mul]
    rw [h_conj, condExp_conjSiteOp, ← conjSiteOp_sub e,
      norm_conjSiteOp, hA_v_eq, norm_conjSiteOp]
    exact h_ql₀ v A_v₀ hA_v₀_supp r
  · have h_comm_eq :
        (sys₁.H0 + V₁.totalPerturbation) * (U₁.1 * sys₁.P0 * U₁.1†) -
          (U₁.1 * sys₁.P0 * U₁.1†) * (sys₁.H0 + V₁.totalPerturbation) =
        conjSiteOp e ((sys₀.H0 + V₀.totalPerturbation) * (U₀.1 * sys₀.P0 * U₀.1†) -
          (U₀.1 * sys₀.P0 * U₀.1†) * (sys₀.H0 + V₀.totalPerturbation)) := by
      rw [h_H₁, h_P0_dress]; simp only [conjSiteOp_mul, conjSiteOp_sub]
    rw [h_comm_eq, norm_conjSiteOp]; exact h_comm₀
  · have h_inside :
        (U₁.1 * sys₁.P0 * U₁.1†) * (sys₁.H0 + V₁.totalPerturbation - (E0 : ℂ) • 1) * (U₁.1 * sys₁.P0 * U₁.1†) =
        conjSiteOp e ((U₀.1 * sys₀.P0 * U₀.1†) * (sys₀.H0 + V₀.totalPerturbation - (E0 : ℂ) • 1) *
          (U₀.1 * sys₀.P0 * U₀.1†)) := by
      rw [h_P0_dress, h_H₁]
      simp only [conjSiteOp_mul, conjSiteOp_sub, conjSiteOp_smul, conjSiteOp_one]
    rw [h_inside, norm_conjSiteOp]
    exact h_split₀
  · intro O_1 hO_1
    rcases hO_1 with rfl | rfl
    · rcases h_obs₀ O_dec_Z₀ (Or.inl rfl) with ⟨h_coh, h_1s, h_cube, h_drift⟩
      have h_OZ_dress : U₁.1 * O_dec_Z₁ * U₁.1† = conjSiteOp e (U₀.1 * O_dec_Z₀ * U₀.1†) := by
        rw [h_U₁]; simp only [O_dec_Z₁, conjSiteOp_adjoint, conjSiteOp_mul]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
            ((sys₁.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_Z₁ * U₁.1†) -
              (U₁.1 * O_dec_Z₁ * U₁.1†) * (sys₁.H0 + V₁.totalPerturbation)) *
            (U₁.1 * Pi_safe₁ * U₁.1†) =
            conjSiteOp e ((U₀.1 * Pi_safe₀ * U₀.1†) *
              ((sys₀.H0 + V₀.totalPerturbation) * (U₀.1 * O_dec_Z₀ * U₀.1†) -
                (U₀.1 * O_dec_Z₀ * U₀.1†) * (sys₀.H0 + V₀.totalPerturbation)) *
              (U₀.1 * Pi_safe₀ * U₀.1†)) := by
          rw [h_Pi_dress, h_H₁, h_OZ_dress]; simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp]; exact h_coh
      · intro v A_v hA_v
        let A_v₀ := conjSiteOp e_inv A_v
        have hA_v₀_supp : IsSupportedOn (UniformSite3D L SiteA) {v} A_v₀ :=
          isSupportedOn_conjSiteOp e_inv hA_v
        have hA_v_eq : A_v = conjSiteOp e A_v₀ :=
          (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) A_v).symm
        have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
            (A_v * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * A_v) *
            (U₁.1 * Pi_safe₁ * U₁.1†) =
            conjSiteOp e ((U₀.1 * Pi_safe₀ * U₀.1†) *
              (A_v₀ * (U₀.1 * O_dec_Z₀ * U₀.1†) - (U₀.1 * O_dec_Z₀ * U₀.1†) * A_v₀) *
              (U₀.1 * Pi_safe₀ * U₀.1†)) := by
          rw [h_Pi_dress, h_OZ_dress, hA_v_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp, hA_v_eq, norm_conjSiteOp]; exact h_1s v A_v₀ hA_v₀_supp
      · intro r hr W hW M_W hM_W
        let M_W₀ := conjSiteOp e_inv M_W
        have hM_W₀_supp : IsSupportedOn (UniformSite3D L SiteA) W M_W₀ :=
          isSupportedOn_conjSiteOp e_inv hM_W
        have hM_W_eq : M_W = conjSiteOp e M_W₀ :=
          (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) M_W).symm
        have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
            (M_W * (U₁.1 * O_dec_Z₁ * U₁.1†) - (U₁.1 * O_dec_Z₁ * U₁.1†) * M_W) *
            (U₁.1 * Pi_safe₁ * U₁.1†) =
            conjSiteOp e ((U₀.1 * Pi_safe₀ * U₀.1†) *
              (M_W₀ * (U₀.1 * O_dec_Z₀ * U₀.1†) - (U₀.1 * O_dec_Z₀ * U₀.1†) * M_W₀) *
              (U₀.1 * Pi_safe₀ * U₀.1†)) := by
          rw [h_Pi_dress, h_OZ_dress, hM_W_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp, hM_W_eq, norm_conjSiteOp]; exact h_cube r hr W hW M_W₀ hM_W₀_supp
      · intro t ht
        have h_eq : (heisenbergFlow (sys₁.H0 + V₁.totalPerturbation) t (U₁.1 * O_dec_Z₁ * U₁.1†) -
              U₁.1 * O_dec_Z₁ * U₁.1†) * (U₁.1 * sys₁.P0 * U₁.1†) =
            conjSiteOp e ((heisenbergFlow (sys₀.H0 + V₀.totalPerturbation) t (U₀.1 * O_dec_Z₀ * U₀.1†) -
              U₀.1 * O_dec_Z₀ * U₀.1†) * (U₀.1 * sys₀.P0 * U₀.1†)) := by
          rw [h_H₁, h_OZ_dress, h_P0_dress, ← conjSiteOp_heisenbergFlow]
          simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp]; exact h_drift t ht
    · rcases h_obs₀ O_dec_X₀ (Or.inr rfl) with ⟨h_coh, h_1s, h_cube, h_drift⟩
      have h_OX_dress : U₁.1 * O_dec_X₁ * U₁.1† = conjSiteOp e (U₀.1 * O_dec_X₀ * U₀.1†) := by
        rw [h_U₁]; simp only [O_dec_X₁, conjSiteOp_adjoint, conjSiteOp_mul]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
            ((sys₁.H0 + V₁.totalPerturbation) * (U₁.1 * O_dec_X₁ * U₁.1†) -
              (U₁.1 * O_dec_X₁ * U₁.1†) * (sys₁.H0 + V₁.totalPerturbation)) *
            (U₁.1 * Pi_safe₁ * U₁.1†) =
            conjSiteOp e ((U₀.1 * Pi_safe₀ * U₀.1†) *
              ((sys₀.H0 + V₀.totalPerturbation) * (U₀.1 * O_dec_X₀ * U₀.1†) -
                (U₀.1 * O_dec_X₀ * U₀.1†) * (sys₀.H0 + V₀.totalPerturbation)) *
              (U₀.1 * Pi_safe₀ * U₀.1†)) := by
          rw [h_Pi_dress, h_H₁, h_OX_dress]; simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp]; exact h_coh
      · intro v A_v hA_v
        let A_v₀ := conjSiteOp e_inv A_v
        have hA_v₀_supp : IsSupportedOn (UniformSite3D L SiteA) {v} A_v₀ :=
          isSupportedOn_conjSiteOp e_inv hA_v
        have hA_v_eq : A_v = conjSiteOp e A_v₀ :=
          (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) A_v).symm
        have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
            (A_v * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * A_v) *
            (U₁.1 * Pi_safe₁ * U₁.1†) =
            conjSiteOp e ((U₀.1 * Pi_safe₀ * U₀.1†) *
              (A_v₀ * (U₀.1 * O_dec_X₀ * U₀.1†) - (U₀.1 * O_dec_X₀ * U₀.1†) * A_v₀) *
              (U₀.1 * Pi_safe₀ * U₀.1†)) := by
          rw [h_Pi_dress, h_OX_dress, hA_v_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp, hA_v_eq, norm_conjSiteOp]; exact h_1s v A_v₀ hA_v₀_supp
      · intro r hr W hW M_W hM_W
        let M_W₀ := conjSiteOp e_inv M_W
        have hM_W₀_supp : IsSupportedOn (UniformSite3D L SiteA) W M_W₀ :=
          isSupportedOn_conjSiteOp e_inv hM_W
        have hM_W_eq : M_W = conjSiteOp e M_W₀ :=
          (conjEuclidean_symm_conjEuclidean (cfgEquiv e_inv) M_W).symm
        have h_eq : (U₁.1 * Pi_safe₁ * U₁.1†) *
            (M_W * (U₁.1 * O_dec_X₁ * U₁.1†) - (U₁.1 * O_dec_X₁ * U₁.1†) * M_W) *
            (U₁.1 * Pi_safe₁ * U₁.1†) =
            conjSiteOp e ((U₀.1 * Pi_safe₀ * U₀.1†) *
              (M_W₀ * (U₀.1 * O_dec_X₀ * U₀.1†) - (U₀.1 * O_dec_X₀ * U₀.1†) * M_W₀) *
              (U₀.1 * Pi_safe₀ * U₀.1†)) := by
          rw [h_Pi_dress, h_OX_dress, hM_W_eq]; simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp, hM_W_eq, norm_conjSiteOp]; exact h_cube r hr W hW M_W₀ hM_W₀_supp
      · intro t ht
        have h_eq : (heisenbergFlow (sys₁.H0 + V₁.totalPerturbation) t (U₁.1 * O_dec_X₁ * U₁.1†) -
              U₁.1 * O_dec_X₁ * U₁.1†) * (U₁.1 * sys₁.P0 * U₁.1†) =
            conjSiteOp e ((heisenbergFlow (sys₀.H0 + V₀.totalPerturbation) t (U₀.1 * O_dec_X₀ * U₀.1†) -
              U₀.1 * O_dec_X₀ * U₀.1†) * (U₀.1 * sys₀.P0 * U₀.1†)) := by
          rw [h_H₁, h_OX_dress, h_P0_dress, ← conjSiteOp_heisenbergFlow]
          simp only [conjSiteOp_mul, conjSiteOp_sub]
        rw [h_eq, norm_conjSiteOp]; exact h_drift t ht

end Part1TwoAxisMemorySynthesis

end
