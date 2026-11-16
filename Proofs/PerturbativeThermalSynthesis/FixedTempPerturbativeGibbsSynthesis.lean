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

import Proofs.DirectWorldlineCluster.WorldlineUrsellAndLowTempWindow
import Proofs.TwoAxisMemorySynthesis.Part1TwoAxisMemorySynthesis
import Proofs.PerturbativeThermalSynthesis.FixedTempWitnessCoverAndMajorant
import Proofs.PerturbativeThermalSynthesis.LogCoolingPerturbativeSynthesis

/-!
# Uniform Fixed-Temperature Perturbative Gibbs Self-Correction Synthesis

Defines `SatisfiesFixedTempWindowGibbsStability` and `SatisfiesFixedTempPerturbativeGibbsStability` in namespace `FixedTempPerturbativeGibbsSynthesis` and proves `fixed_temp_perturbative_gibbs_stability_main`. Splices the direct worldline Ursell cluster expansion in the intermediate-temperature window with the quasi-adiabatic continuation dressed low-temperature crossover uniformly for all inverse temperatures above the critical threshold.

## References

* Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.8 (`prop:diagonal-peeling`)
* Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge
open PerturbedThermalBarrier
open Part1TwoAxisMemorySynthesis SpacetimeWorldlineKP DirectWorldlineCluster

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace FixedTempPerturbativeGibbsSynthesis

private lemma q_code_BDL_ge_one : 1 ≤ qCodeBDL := by decide
private lemma r_0_BDL_ge_one : 1 ≤ r0BDL := by decide
private lemma w_0_BDL_ge_one : 1 ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by decide
private lemma r_0_BDL_le_C_rca_BDL : 1 + 4 * (r0BDL : ℝ) ≤ (collarConstRCABDL : ℝ) := by
  exact_mod_cast (by decide : 1 + 4 * r0BDL ≤ collarConstRCABDL)

private lemma sixteen_le_beta_c_BDL : (16 : ℝ) ≤ betaCritBDL := by
  have h_def : betaCritBDL =
      1200 * (_root_.bdlSingleStepFactor : ℝ) +
        2 * ((mMaxBDL + qCodeBDL : ℕ) : ℝ) * ((4 * r0BDL + 1 : ℕ) ^ 3 : ℝ) + 100 := rfl
  have h1 : (0 : ℝ) ≤ 1200 * (_root_.bdlSingleStepFactor : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤
      2 * ((mMaxBDL + qCodeBDL : ℕ) : ℝ) * ((4 * r0BDL + 1 : ℕ) ^ 3 : ℝ) := by positivity
  rw [h_def]
  linarith

private lemma isGeometricallyLocal_of_reindex {D L N_checks r_0 w_0 : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {Idx : Type} [Fintype Idx] [DecidableEq Idx]
    (e_chk : Idx ≃ Fin N_checks)
    (sys : IndexedCommutingProjectorHamiltonian D L Site Idx)
    (h : (sys.reindex e_chk).IsGeometricallyLocal r_0 w_0) :
    sys.IsGeometricallyLocal r_0 w_0 := by
  refine ⟨fun idx => ?_, fun v => ?_⟩
  · rcases h.1 (e_chk idx) with ⟨x, hx⟩
    dsimp [IndexedCommutingProjectorHamiltonian.reindex] at hx
    rw [Equiv.symm_apply_apply] at hx
    exact ⟨x, hx⟩
  · have hv := h.2 v
    have h_card :
        (Finset.univ.filter (fun idx : Idx => v ∈ sys.support idx)).card =
          (Finset.univ.filter (fun i : Fin N_checks => v ∈ (sys.reindex e_chk).support i)).card := by
      refine Finset.card_bij (fun idx _ => e_chk idx) ?_ ?_ ?_
      · intro idx hidx
        rw [Finset.mem_filter] at hidx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        dsimp [IndexedCommutingProjectorHamiltonian.reindex]
        rw [Equiv.symm_apply_apply]
        exact hidx.2
      · intro idx₁ _ idx₂ _ h_eq
        exact e_chk.injective h_eq
      · intro i hi
        rw [Finset.mem_filter] at hi
        refine ⟨e_chk.symm i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.2⟩,
          e_chk.apply_symm_apply i⟩
    rw [h_card]
    exact hv

private lemma le_floor_c_star_BDL_mul_bdlBoxSide_of_le_bdlLambda_pow {R_pert k_0 k : ℕ}
    (hR : R_pert ≤ bdlLambda ^ k_0) (hk : k_0 ≤ k) :
    R_pert ≤ Nat.floor (cStarBDL * (bdlBoxSide k : ℝ)) := by
  rw [floor_c_star_BDL_mul_bdlBoxSide_eq k]
  have hk2 : k_0 ≤ 2 * k := by omega
  exact le_trans hR (Nat.pow_le_pow_right bdlLambda_pos hk2)

private lemma card_box3D_bdlBoxSide_le_exp_floor_c_star_BDL {k : ℕ} (hk : 1 ≤ k) :
    (Fintype.card (Box3D (bdlBoxSide k)) : ℝ) ≤
      Real.exp (Nat.floor (cStarBDL * (bdlBoxSide k : ℝ)) : ℝ) := by
  rw [floor_c_star_BDL_mul_bdlBoxSide_eq k]
  have h_card : Fintype.card (Box3D (bdlBoxSide k)) = (bdlBoxSide k) ^ 3 := by
    simp [Box3D, BoxD]
  rw [h_card]
  let N := bdlLambda ^ (2 * k)
  have h_pow_le : (bdlBoxSide k) ^ 3 * Nat.factorial 10 ≤ N ^ 10 := by
    have h_side : (bdlBoxSide k) ^ 3 ≤ N ^ 9 := by
      dsimp [bdlBoxSide, bBDL, bdlHierarchySteps, N]
      rw [← pow_mul, ← pow_mul]
      exact Nat.pow_le_pow_right bdlLambda_pos (by omega)
    have h_fact : Nat.factorial 10 ≤ N := by
      have h1 : Nat.factorial 10 ≤ bdlLambda ^ 1 := by decide
      exact h1.trans (Nat.pow_le_pow_right bdlLambda_pos (by omega))
    calc (bdlBoxSide k) ^ 3 * Nat.factorial 10
      _ ≤ N ^ 9 * N := Nat.mul_le_mul h_side h_fact
      _ = N ^ 10 := by ring
  have h_real_le : (((bdlBoxSide k) ^ 3 : ℕ) : ℝ) * (Nat.factorial 10 : ℝ) ≤ (N : ℝ) ^ 10 := by
    exact_mod_cast h_pow_le
  have h_f10_pos : (0 : ℝ) < (Nat.factorial 10 : ℝ) := by positivity
  have h_div : (((bdlBoxSide k) ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) ^ 10 / (Nat.factorial 10 : ℝ) :=
    (le_div_iff₀ h_f10_pos).mpr h_real_le
  have h_term : (N : ℝ) ^ 10 / (Nat.factorial 10 : ℝ) ≤
      ∑ i ∈ Finset.range 11, (N : ℝ) ^ i / (Nat.factorial i : ℝ) :=
    Finset.single_le_sum (f := fun i => (N : ℝ) ^ i / (Nat.factorial i : ℝ))
      (fun i _ => div_nonneg (pow_nonneg (Nat.cast_nonneg N) i) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (by decide : 10 < 11))
  exact h_div.trans (h_term.trans (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg N) 11))

/-! ## 1. Site-Alphabet Reindexing Helpers -/

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  betaCritBDL _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor bdlClusterStepBase
  collarConstRCABDL bdlLambda bBDL bdlHierarchySteps qCodeBDL r0BDL mMaxBDL
  IndexedCommutingProjectorHamiltonian.H0 IndexedCommutingProjectorHamiltonian.groundProj
  IndexedCommutingProjectorHamiltonian.localGroundProj
  IndexedCommutingProjectorHamiltonian.groundSpace IndexedCommutingProjectorHamiltonian.groundDegeneracy
  IndexedCommutingProjectorHamiltonian.syndromeProjector QuasiLocalPerturbation.totalPerturbation
  opKMSNorm opKMSNormSq SatisfiesKMSLindbladODE heisenbergFlow condExp IsSupportedOn
  syndromeSignOp syndromeSubsetProj bdlSafeSyndromeSet bdlWeldedCode bdlLocalDescriptor
  weylPauliZ weylPauliX bdlPushChain

private lemma reindexHamiltonian_isGeometricallyLocal {L N_checks r_0 w_0 : ℕ}
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Fintype SiteB] [DecidableEq SiteB]
    (e0 : SiteA ≃ SiteB)
    (sys₀ : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteA) (Fin N_checks))
    (h : sys₀.IsGeometricallyLocal r_0 w_0) :
    (reindexHamiltonian (fun _ : Box3D L => e0) sys₀).IsGeometricallyLocal r_0 w_0 := h

private lemma reindexHamiltonian_reindex_weight {L N_checks : ℕ}
    {SiteA SiteB Idx : Type} [Fintype SiteA] [DecidableEq SiteA]
    [Fintype SiteB] [DecidableEq SiteB] [Fintype Idx] [DecidableEq Idx]
    (e0 : SiteA ≃ SiteB) (e_chk : Idx ≃ Fin N_checks)
    (sys : IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L SiteA) Idx) (i : Fin N_checks) :
    (reindexHamiltonian (fun _ : Box3D L => e0) (sys.reindex e_chk)).weight i =
      sys.weight (e_chk.symm i) := rfl

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]
local notation "ℋ_CP[" L ", " Site0 ", " N_checks "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (UniformSite3D L Site0) (Fin N_checks)
local notation "𝒱_pert[" L ", " Site0 "]" =>
  QuasiLocalPerturbation 3 L (UniformSite3D L Site0)

/-! ## 2. Finite-Range Perturbation & Fixed-Temperature Gibbs Stability Predicates -/

/-- Internal 4-conjunct fixed-temperature window Gibbs stability predicate (`β ∈ (β_c, β_max]`). -/
def SatisfiesFixedTempWindowGibbsStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    (R_bath : ℕ)
    (β_c β_max c_F_pert η δ_split : ℝ)
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
    (∀ O_0 : ℬ[L, Site0], (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      let O_dress := U_dress.1 * O_0 * U_dress.1†
      ‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split ∧
      (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
        IsSupportedOn (UniformSite3D L Site0) {v} A_v →
        ‖Pi_safe_dress * (A_v * O_dress - O_dress * A_v) * Pi_safe_dress‖ ≤ δ_split * ‖A_v‖) ∧
      (∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, Site0],
        IsSupportedOn (UniformSite3D L Site0) W M_W →
        ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_split * ‖M_W‖) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split)) ∧
    (∀ (β : ℝ) (hH : IsSelfAdjoint H),
      β > β_c → β ≤ β_max →
      let ΔF_pert := c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η)
      gibbsFailureProb H hH β (1 - Pi_safe) ≤ Real.exp (-ΔF_pert))

/-- **Fixed-Temperature and Logarithmic-Cooling Perturbative Full-Spectrum
    and Unpinched Gibbs Failure Probability Stability (`SatisfiesFixedTempPerturbativeGibbsStability`)**
    (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`) and Theorem 6.4 (`thm:main-B`)). -/
def SatisfiesFixedTempPerturbativeGibbsStability
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    (R_bath : ℕ)
    (β_c β_max c_F_pert C_scale c_F_dress η δ_split : ℝ)
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
    (∀ O_0 : ℬ[L, Site0], (O_0 = O_dec_Z ∨ O_0 = O_dec_X) →
      let O_dress := U_dress.1 * O_0 * U_dress.1†
      ‖Pi_safe_dress * (H * O_dress - O_dress * H) * Pi_safe_dress‖ ≤ δ_split ∧
      (∀ (v : Box3D L) (A_v : ℬ[L, Site0]),
        IsSupportedOn (UniformSite3D L Site0) {v} A_v →
        ‖Pi_safe_dress * (A_v * O_dress - O_dress * A_v) * Pi_safe_dress‖ ≤ δ_split * ‖A_v‖) ∧
      (∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r, ∀ M_W : ℬ[L, Site0],
        IsSupportedOn (UniformSite3D L Site0) W M_W →
        ‖Pi_safe_dress * (M_W * O_dress - O_dress * M_W) * Pi_safe_dress‖ ≤ δ_split * ‖M_W‖) ∧
      (∀ t : ℝ, 0 ≤ t →
        ‖(heisenbergFlow H t O_dress - O_dress) * P0_dress‖ ≤ t * δ_split)) ∧
    (∀ (β : ℝ) (hH : IsSelfAdjoint H),
      β > β_c → β ≤ β_max →
      let ΔF_pert := c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η)
      gibbsFailureProb H hH β (1 - Pi_safe) ≤ Real.exp (-ΔF_pert)) ∧
    (∀ (β : ℝ) (hH : IsSelfAdjoint H),
      C_scale * Real.log (L : ℝ) ≤ β →
      let p_log := ((L ^ 3 : ℕ) : ℝ) * Real.exp (-c_F_dress * β) + δ_split
      gibbsFailureProb H hH β (1 - Pi_safe_dress) ≤ p_log)

/-! ## 3. Finite-Range Decay Profile & Site-Alphabet Transport Helpers -/

/-- Step decay profile `if r ≤ R_pert then 1 else 0` associated with a finite interaction range
    `R_pert`. -/
def finiteRangeDecayProfile (R_pert r : ℕ) : ℝ :=
  if r ≤ R_pert then 1 else 0

/-- `finiteRangeDecayProfile R_pert` has superpolynomial decay for every `R_pert : ℕ`. -/
lemma isSuperpolynomialDecay_finiteRangeDecayProfile (R_pert : ℕ) :
    IsSuperpolynomialDecay (finiteRangeDecayProfile R_pert) := by
  refine ⟨fun r => by dsimp [finiteRangeDecayProfile]; split_ifs <;> norm_num, fun p => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop R_pert] with r hr
  dsimp [finiteRangeDecayProfile]
  rw [if_neg (not_le_of_gt hr), mul_zero]

/-- Every perturbation satisfying `HasFiniteRangeBound V R_pert J` with `0 ≤ J` also satisfies
    `V.SatisfiesDecayBound J (finiteRangeDecayProfile R_pert)`. -/
lemma satisfiesDecayBound_of_hasFiniteRangeBound
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {V : QuasiLocalPerturbation D L Site} {R_pert : ℕ} {J : ℝ}
    (_hJ_nn : 0 ≤ J) (hV : HasFiniteRangeBound V R_pert J) :
    V.SatisfiesDecayBound J (finiteRangeDecayProfile R_pert) := by
  intro r hr A hA
  dsimp [finiteRangeDecayProfile]
  split_ifs with hr_le
  · rw [mul_one]
    exact (hV r hr A hA).1 hr_le
  · rw [(hV r hr A hA).2 (lt_of_not_ge hr_le), norm_zero, mul_zero]

/-- Site-alphabet reindexing invariance of `gibbsFailureProb` for any self-adjoint Hamiltonian
    `H₀` and operator `P₀`. -/
private lemma gibbsFailureProb_conjSiteOp
    {D L : ℕ} {Site0 Site1 : BoxD D L → Type}
    [∀ x, Fintype (Site0 x)] [∀ x, DecidableEq (Site0 x)] [∀ x, Nonempty (Site0 x)]
    [∀ x, Fintype (Site1 x)] [∀ x, DecidableEq (Site1 x)] [∀ x, Nonempty (Site1 x)]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    (H₀ P₀ : ManyBodyHilbertSpace Site0 →L[ℂ] ManyBodyHilbertSpace Site0)
    (hH₀ : IsSelfAdjoint H₀)
    (hH₁ : IsSelfAdjoint (conjSiteOp e H₀))
    (β : ℝ) :
    gibbsFailureProb (conjSiteOp e H₀) hH₁ β (conjSiteOp e P₀) =
      gibbsFailureProb H₀ hH₀ β P₀ := by
  let ψ_alt : ManyBodyConfig Site1 → ManyBodyHilbertSpace Site1 :=
    fun ω => uReindex (cfgEquiv e) (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))
  let E_alt : ManyBodyConfig Site1 → ℝ :=
    fun ω => opEigenvalues H₀ hH₀ ((cfgEquiv e).symm ω)
  have h_onb : ∀ ω₁ ω₂, inner ℂ (ψ_alt ω₁) (ψ_alt ω₂) = if ω₁ = ω₂ then (1 : ℂ) else 0 := by
    intro ω₁ ω₂
    dsimp [ψ_alt]
    rw [inner_uReindex, opEigenbasis_orthonormal H₀ hH₀]
    by_cases hω : ω₁ = ω₂
    · subst hω; simp
    · have hne : (cfgEquiv e).symm ω₁ ≠ (cfgEquiv e).symm ω₂ :=
        fun h => hω ((cfgEquiv e).symm.injective h)
      rw [if_neg hne, if_neg hω]
  have h_eig : ∀ ω, conjSiteOp e H₀ (ψ_alt ω) = (E_alt ω : ℂ) • ψ_alt ω := by
    intro ω
    change uReindex (cfgEquiv e) (H₀ (uReindex (cfgEquiv e).symm
      (uReindex (cfgEquiv e) (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))))) = _
    rw [uReindex_symm_apply, opEigenbasis_apply_H H₀ hH₀, map_smul]
  have hZ_eq : gibbsPartitionZ (opEigenvalues (conjSiteOp e H₀) hH₁) β =
      gibbsPartitionZ (opEigenvalues H₀ hH₀) β := by
    rw [perturbed_gibbsPartitionZ_eq_of_any_orthonormal_eigenbasis
      (conjSiteOp e H₀) hH₁ ψ_alt E_alt h_onb h_eig β]
    exact (cfgEquiv e).symm.sum_comp (fun σ => Real.exp (-β * opEigenvalues H₀ hH₀ σ))
  have hTr_eq :
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis (conjSiteOp e H₀) hH₁)
        (opEigenvalues (conjSiteOp e H₀) hH₁) β * conjSiteOp e P₀) =
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H₀ hH₀) (opEigenvalues H₀ hH₀) β * P₀) := by
    rw [perturbed_hilbertTrace_gibbsBoltzmannOp_eq_sum_any_orthonormal_eigenbasis
      (conjSiteOp e H₀) hH₁ ψ_alt E_alt h_onb h_eig β (conjSiteOp e P₀),
      hilbertTrace_gibbsBoltzmannOp_mul_eq]
    have h_term : ∀ ω : ManyBodyConfig Site1,
        Real.exp (-β * E_alt ω) * RCLike.re (inner ℂ (ψ_alt ω) (conjSiteOp e P₀ (ψ_alt ω))) =
        Real.exp (-β * opEigenvalues H₀ hH₀ ((cfgEquiv e).symm ω)) *
          RCLike.re (inner ℂ (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))
            (P₀ (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω)))) := by
      intro ω
      have h_apply : conjSiteOp e P₀ (ψ_alt ω) =
          uReindex (cfgEquiv e) (P₀ (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))) := by
        change uReindex (cfgEquiv e) (P₀ (uReindex (cfgEquiv e).symm
          (uReindex (cfgEquiv e) (opEigenbasis H₀ hH₀ ((cfgEquiv e).symm ω))))) = _
        rw [uReindex_symm_apply]
      rw [h_apply]
      dsimp [ψ_alt, E_alt]
      rw [inner_uReindex]
    refine (Finset.sum_congr rfl fun ω _ => h_term ω).trans ?_
    exact (cfgEquiv e).symm.sum_comp (fun σ =>
      Real.exp (-β * opEigenvalues H₀ hH₀ σ) *
        RCLike.re (inner ℂ (opEigenbasis H₀ hH₀ σ) (P₀ (opEigenbasis H₀ hH₀ σ))))
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace,
    perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace, hZ_eq, hTr_eq]

/-- `HasFiniteRangeBound` is preserved under site-alphabet reindexing `reindexPerturbation`. -/
private lemma hasFiniteRangeBound_reindexPerturbation
    {D L : ℕ} {Site0 Site1 : BoxD D L → Type}
    [∀ x, Fintype (Site0 x)] [∀ x, DecidableEq (Site0 x)] [∀ x, Nonempty (Site0 x)]
    [∀ x, Fintype (Site1 x)] [∀ x, DecidableEq (Site1 x)] [∀ x, Nonempty (Site1 x)]
    (e : ∀ x : BoxD D L, Site0 x ≃ Site1 x)
    {V : QuasiLocalPerturbation D L Site0} {R_pert : ℕ} {J : ℝ}
    (hV : HasFiniteRangeBound V R_pert J) :
    HasFiniteRangeBound (reindexPerturbation e V) R_pert J := by
  intro r hr A hA
  refine ⟨fun hr_le => ?_, fun hr_gt => ?_⟩
  · change ‖conjEuclidean (cfgEquiv e) (V.term r A)‖ ≤ J
    rw [norm_conjEuclidean]
    exact (hV r hr A hA).1 hr_le
  · change conjEuclidean (cfgEquiv e) (V.term r A) = 0
    rw [(hV r hr A hA).2 hr_gt, conjEuclidean_zero]

/-- Transport of `SatisfiesFixedTempWindowGibbsStability` along a uniform site bijection
    `e0 : SiteA ≃ SiteB`. -/
private lemma satisfiesFixedTempPerturbativeGibbsStability_reindexHamiltonian
    {L N_checks R_bath : ℕ} [NeZero L]
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Nonempty SiteA]
    [Fintype SiteB] [DecidableEq SiteB] [Nonempty SiteB]
    (e0 : SiteA ≃ SiteB)
    (sys₀ : ℋ_CP[L, SiteA, N_checks])
    (Pi_safe₀ O_dec_Z₀ O_dec_X₀ : ℬ[L, SiteA])
    (hOZ_norm : ‖O_dec_Z₀‖ ≤ 1) (hOZ_P0 : Commute sys₀.P0 O_dec_Z₀)
    (hOX_norm : ‖O_dec_X₀‖ ≤ 1) (hOX_P0 : Commute sys₀.P0 O_dec_X₀)
    (V₁ : 𝒱_pert[L, SiteB])
    {β_c β_max c_F_pert η δ_split : ℝ} {g_LR : ℕ → ℝ}
    (h_gibbs₀ : SatisfiesFixedTempWindowGibbsStability
      sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀
      (reindexPerturbation (fun _ => e0.symm) V₁) R_bath β_c β_max c_F_pert η δ_split g_LR) :
    SatisfiesFixedTempWindowGibbsStability
      (reindexHamiltonian (fun _ => e0) sys₀)
      (conjSiteOp (fun _ => e0) Pi_safe₀)
      (conjSiteOp (fun _ => e0) O_dec_Z₀)
      (conjSiteOp (fun _ => e0) O_dec_X₀)
      V₁ R_bath β_c β_max c_F_pert η δ_split g_LR := by
  let e : ∀ _ : Box3D L, SiteA ≃ SiteB := fun _ => e0
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteA x) := fun _ => inferInstance
  haveI : ∀ x : Box3D L, Nonempty (UniformSite3D L SiteB x) := fun _ => inferInstance
  let e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA := fun _ => e0.symm
  have h_zero₀ : SatisfiesZeroTempPerturbativeMemoryStability
      sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀ (reindexPerturbation e_inv V₁) R_bath δ_split g_LR := by
    rcases h_gibbs₀ with ⟨U₀, E0, h1, h2, h3, h4, h5, _⟩
    exact ⟨U₀, E0, h1, h2, h3, h4, h5⟩
  have h_zero₁ := satisfiesZeroTempPerturbativeMemoryStability_reindexHamiltonian
    e0 sys₀ Pi_safe₀ O_dec_Z₀ O_dec_X₀ hOZ_norm hOZ_P0 hOX_norm hOX_P0 V₁ h_zero₀
  rcases h_zero₁ with ⟨U₁, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress⟩
  rcases h_gibbs₀ with ⟨_, _, _, _, _, _, _, h_gibbs_prob₀⟩
  refine ⟨U₁, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress, fun β hH₁ hβ hβ_le => ?_⟩
  let H₀ := sys₀.H0 + (reindexPerturbation e_inv V₁).totalPerturbation
  let H₁ := (reindexHamiltonian e sys₀).H0 + V₁.totalPerturbation
  have h_cfg_inv : cfgEquiv e_inv = (cfgEquiv e).symm := by ext σ x; rfl
  have hV_conj : conjSiteOp e (reindexPerturbation e_inv V₁).totalPerturbation = V₁.totalPerturbation := by
    rw [reindexPerturbation_V_tot]; dsimp [conjSiteOp]
    rw [h_cfg_inv, conjEuclidean_conjEuclidean_symm]
  have hH₁_eq : H₁ = conjSiteOp e H₀ := by
    dsimp [H₁, H₀]; rw [reindexHamiltonian_H0, ← hV_conj]
  have hH₀_eq : H₀ = conjSiteOp e_inv H₁ := by
    rw [hH₁_eq]; dsimp [conjSiteOp]; rw [h_cfg_inv, conjEuclidean_symm_conjEuclidean]
  have hH₀ : IsSelfAdjoint H₀ := by
    rw [hH₀_eq]; exact conjEuclidean_isSelfAdjoint (cfgEquiv e_inv) hH₁
  have h_fail_conj : (1 : ℬ[L, SiteB]) - conjSiteOp e Pi_safe₀ = conjSiteOp e (1 - Pi_safe₀) := by
    dsimp [conjSiteOp]
    rw [← conjEuclidean_one (cfgEquiv e), ← conjEuclidean_sub]
  have h_pfail_eq :
      gibbsFailureProb ((reindexHamiltonian e sys₀).H0 + V₁.totalPerturbation) hH₁ β (1 - conjSiteOp e Pi_safe₀) =
      gibbsFailureProb H₀ hH₀ β (1 - Pi_safe₀) := by
    have hH₁' : IsSelfAdjoint (conjSiteOp e H₀) := hH₁_eq ▸ hH₁
    have h_congr :
        gibbsFailureProb ((reindexHamiltonian e sys₀).H0 + V₁.totalPerturbation) hH₁ β (1 - conjSiteOp e Pi_safe₀) =
        gibbsFailureProb (conjSiteOp e H₀) hH₁' β (conjSiteOp e (1 - Pi_safe₀)) := by
      rw [h_fail_conj]
      congr 1
    rw [h_congr, gibbsFailureProb_conjSiteOp e H₀ (1 - Pi_safe₀) hH₀ hH₁' β]
  rw [h_pfail_eq]
  exact h_gibbs_prob₀ β hH₀ hβ hβ_le

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  gibbsFailureProb betaCritBDL _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor
  bdlClusterStepBase

/-! ## 4. Native `CodeSlotConfig` Synthesis & Main Theorem Synthesis -/

/-- **Bridge Theorem (`bdl_codeSlot_directWorldline_intact_cluster_bridge`)**:
    Connects the `DirectWorldlineCluster` intact-cluster expansion machinery
    (`worldline_character_projection_and_prufer_tree_bound`,
    `directWorldlineIntactCluster_witness_gibbs_bound`,
    `tubeLocal_koteckyPreiss_partition_erasure_ratio_le`, and
    `positiveWitness_gibbs_defect_sum_le`) to the concrete welded hierarchy `mem_k` on
    `CodeSlotConfig q_code_BDL` and its check witness family `W_family_k`. -/
theorem bdl_codeSlot_directWorldline_intact_cluster_bridge {k N_chk R_pert : ℕ}
    (e_chk : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin N_chk)
    (mem_k : Inhomogeneous3DMemoryRealization (bdlBoxSide k)
      qCodeBDL r0BDL mMaxBDL cStarBDL (collarConstRCABDL : ℝ)
      betaCritBDL cFBDL etaBDL cMemBDL)
    (S_safe_k : Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool))
    (W_family_k : Finset (Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL)))
    (V : 𝒱_pert[bdlBoxSide k, CodeSlotConfig qCodeBDL])
    (β_max β J : ℝ)
    (hH_orig : IsSelfAdjoint (mem_k.sys.H0 + V.totalPerturbation))
    (hR_pos : 1 ≤ R_pert)
    (hR_le_Lstar : R_pert ≤ Nat.floor (cStarBDL * (bdlBoxSide k : ℝ)))
    (h_scale_cal : SatisfiesWorldlineScaleCalibration (bdlBoxSide k) (Nat.floor (cStarBDL * (bdlBoxSide k : ℝ))) R_pert r0BDL (collarConstRCABDL : ℝ))
    (hβ : betaCritBDL < β)
    (hβ_le : β ≤ β_max)
    (hJ_nn : 0 ≤ J)
    (hJ_le_kp : J ≤ directWorldlineThreshold R_pert r0BDL
      ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) (collarConstRCABDL : ℝ) betaCritBDL β_max)
    (hV_range : HasFiniteRangeBound V R_pert J)
    (h_sys_eq : mem_k.sys = bdlInhomogeneousSystem k)
    (h_cover : IsPositiveCheckWitnessCover S_safe_k W_family_k)
    (hW_valid : ∀ W ∈ W_family_k, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes mem_k.D_field)
    (h_card_floor : ∀ W ∈ W_family_k, clusterRawWeight k ≤ W.card)
    (hW_ent : (∑ W ∈ W_family_k, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1) :
    (∀ W ∈ W_family_k,
       gibbsFailureProb (mem_k.sys.H0 + V.totalPerturbation) hH_orig β (positiveCheckWitnessProj mem_k.sys W) ≤
         Real.exp (-((betaCritBDL / 2 + min (β - betaCritBDL) 1) * (W.card : ℝ)))) ∧
    gibbsFailureProb (mem_k.sys.H0 + V.totalPerturbation) hH_orig β
      (1 - indexedBareFailureProjector mem_k.sys S_safe_k) ≤
      Real.exp (-(cFBDL * min (β - betaCritBDL) 1 * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL))) := by
  haveI : Nonempty (CodeSlotConfig qCodeBDL) := ⟨fun _ => false⟩
  haveI : ∀ x : Box3D (bdlBoxSide k),
      Nonempty (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL) x) :=
    fun _ => inferInstance
  have hβ_pos : 0 < β := lt_trans beta_crit_bdl_pos hβ
  let w_0_BDL : ℕ := (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)
  have h_geom_sys : mem_k.sys.IsGeometricallyLocal r0BDL w_0_BDL := by
    rw [h_sys_eq]
    exact isGeometricallyLocal_of_reindex e_chk (bdlInhomogeneousSystem k)
      (isGeometricallyLocal_bdlInhomogeneousSystem_reindex k e_chk)
  have h_witness_kp : ∀ W ∈ W_family_k,
      gibbsFailureProb (mem_k.sys.H0 + V.totalPerturbation) hH_orig β (positiveCheckWitnessProj mem_k.sys W) ≤
        Real.exp (-((betaCritBDL / 2 + min (β - betaCritBDL) 1) * (W.card : ℝ))) :=
    fun W hW =>
      exists_directWorldline_fixed_temp_witness_bound
        mem_k.D_field mem_k.h_D_field_valid mem_k.sys mem_k.h_sys_checks h_geom_sys
        hR_pos hR_le_Lstar h_scale_cal (Nat.cast_nonneg collarConstRCABDL) sixteen_le_beta_c_BDL hβ hβ_le hJ_nn hJ_le_kp
        mem_k.h_tqo.1 mem_k.h_tqo.2.2 V hV_range hH_orig W (hW_valid W hW)
  let α_KP : ℝ := betaCritBDL / 2 + min (β - betaCritBDL) 1
  have h_min_pos : 0 ≤ min (β - betaCritBDL) 1 := le_min (by linarith) zero_le_one
  have h_vol : cFBDL * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL) ≤ (clusterRawWeight k : ℝ) :=
    c_F_BDL_mul_vol_pow_eta_le_clusterRawWeight k
  have h_sum_le :
      (∑ W ∈ W_family_k, Real.exp (-α_KP * (W.card : ℝ))) ≤
        Real.exp (-(cFBDL * min (β - betaCritBDL) 1 * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL))) := by
    have h_term : ∀ W ∈ W_family_k,
        Real.exp (-α_KP * (W.card : ℝ)) ≤
          Real.exp (-(betaCritBDL / 2) * (W.card : ℝ)) *
            Real.exp (-(min (β - betaCritBDL) 1 * (clusterRawWeight k : ℝ))) := by
      intro W hW
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [α_KP]
      have hW_card : (clusterRawWeight k : ℝ) ≤ (W.card : ℝ) := Nat.cast_le.mpr (h_card_floor W hW)
      have h_mul := mul_le_mul_of_nonneg_left hW_card h_min_pos
      linarith
    calc (∑ W ∈ W_family_k, Real.exp (-α_KP * (W.card : ℝ)))
      _ ≤ ∑ W ∈ W_family_k,
            Real.exp (-(betaCritBDL / 2) * (W.card : ℝ)) *
              Real.exp (-(min (β - betaCritBDL) 1 * (clusterRawWeight k : ℝ))) :=
          Finset.sum_le_sum h_term
      _ = (∑ W ∈ W_family_k, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) *
            Real.exp (-(min (β - betaCritBDL) 1 * (clusterRawWeight k : ℝ))) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * Real.exp (-(min (β - betaCritBDL) 1 * (clusterRawWeight k : ℝ))) :=
          mul_le_mul_of_nonneg_right hW_ent (Real.exp_pos _).le
      _ = Real.exp (-(min (β - betaCritBDL) 1 * (clusterRawWeight k : ℝ))) := one_mul _
      _ ≤ Real.exp (-(cFBDL * min (β - betaCritBDL) 1 * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL))) := by
          apply Real.exp_le_exp.mpr
          have h_mul := mul_le_mul_of_nonneg_left h_vol h_min_pos
          linarith
  have h_defect_sum := DirectWorldlineCluster.positiveWitness_gibbs_defect_sum_le
    mem_k.sys (mem_k.sys.H0 + V.totalPerturbation) hH_orig β S_safe_k W_family_k
    (fun W => Real.exp (-α_KP * (W.card : ℝ))) h_cover
    (fun W hW => by
      (try dsimp only)
      have h_neg_α : -α_KP * (W.card : ℝ) = -((betaCritBDL / 2 + min (β - betaCritBDL) 1) * (W.card : ℝ)) := by
        dsimp [α_KP]; ring
      rw [h_neg_α]
      exact h_witness_kp W hW)
  exact ⟨h_witness_kp, le_trans h_defect_sum h_sum_le⟩

private def FixedTempWindowGibbsBound
    {L N_checks : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    (β_c β_max c_F_pert η : ℝ) : Prop :=
  ∀ (β : ℝ) (hH : IsSelfAdjoint (sys.H0 + V.totalPerturbation)),
    β > β_c → β ≤ β_max →
    gibbsFailureProb (sys.H0 + V.totalPerturbation) hH β (1 - Pi_safe) ≤
      Real.exp (-(c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η)))

/-- Combines `SatisfiesZeroTempPerturbativeMemoryStability` with the fixed-temperature window
    Gibbs failure bound to establish `SatisfiesFixedTempWindowGibbsStability`. -/
lemma satisfiesFixedTempWindowGibbsStability_of_zeroTemp
    {L N_checks R_bath : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    {β_c β_max c_F_pert η δ_split : ℝ} {g_LR : ℕ → ℝ}
    (h_zero : SatisfiesZeroTempPerturbativeMemoryStability sys Pi_safe O_dec_Z O_dec_X V R_bath δ_split g_LR)
    (h_gibbs : FixedTempWindowGibbsBound sys Pi_safe V β_c β_max c_F_pert η) :
    SatisfiesFixedTempWindowGibbsStability
      sys Pi_safe O_dec_Z O_dec_X V R_bath β_c β_max c_F_pert η δ_split g_LR := by
  rcases h_zero with ⟨U_dress, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress⟩
  exact ⟨U_dress, E0, h_ql, h_comm_P0, h_split_P0, h_form, h_obs_dress, h_gibbs⟩

/-- Combines the fixed-temperature window bound (`SatisfiesFixedTempWindowGibbsStability`) with the
    logarithmic-cooling QAC-dressed bound (`SatisfiesScalingTempPerturbativeThermalAndKMSStability`)
    to establish `SatisfiesFixedTempPerturbativeGibbsStability`. -/
lemma satisfiesFixedTempPerturbativeGibbsStability_of_window_and_scaling
    {L N_checks R_bath_win R_bath : ℕ} [NeZero L]
    {Site0 : Type} [Fintype Site0] [DecidableEq Site0]
    (sys : ℋ_CP[L, Site0, N_checks])
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, Site0])
    (V : 𝒱_pert[L, Site0])
    {β_c β_max c_F_pert C_scale c_F_dress η δ_split_win δ_split : ℝ}
    {g_LR_win g_LR : ℕ → ℝ}
    (h_win : SatisfiesFixedTempWindowGibbsStability
      sys Pi_safe O_dec_Z O_dec_X V R_bath_win β_c β_max c_F_pert η δ_split_win g_LR_win)
    (h_log : LogCoolingPerturbativeSynthesis.SatisfiesScalingTempPerturbativeThermalAndKMSStability
      sys Pi_safe O_dec_Z O_dec_X V R_bath C_scale c_F_dress δ_split g_LR) :
    SatisfiesFixedTempPerturbativeGibbsStability
      sys Pi_safe O_dec_Z O_dec_X V R_bath β_c β_max c_F_pert C_scale c_F_dress η δ_split g_LR := by
  rcases h_win with ⟨_, _, _, _, _, _, _, h4⟩
  rcases h_log with ⟨U_dress, E0, h1, h2_1, h2_2, h2_3, h3, h5⟩
  exact ⟨U_dress, E0, h1, h2_1, h2_2, h2_3, h3, h4, fun β hH hβ => (h5 β hH hβ).1⟩

private lemma isSelfAdjoint_H0_add_of_reindex {L N_c : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig qCodeBDL))
      (StaticCSSCheckIdx L qCodeBDL mMaxBDL))
    (e_chk : StaticCSSCheckIdx L qCodeBDL mMaxBDL ≃ Fin N_c)
    (V : 𝒱_pert[L, CodeSlotConfig qCodeBDL])
    (hH : IsSelfAdjoint ((sys.reindex e_chk).H0 + V.totalPerturbation)) :
    IsSelfAdjoint (sys.H0 + V.totalPerturbation) := by
  rwa [← sys.reindex_H0 e_chk]

private lemma fixedTempWindowGibbsBound_reindex_of_orig {L N_c : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig qCodeBDL))
      (StaticCSSCheckIdx L qCodeBDL mMaxBDL))
    (e_chk : StaticCSSCheckIdx L qCodeBDL mMaxBDL ≃ Fin N_c)
    (Pi_safe : ℬ[L, CodeSlotConfig qCodeBDL])
    (S_safe : Finset (StaticCSSCheckIdx L qCodeBDL mMaxBDL → Bool))
    (hPi : Pi_safe = syndromeSubsetProj sys S_safe)
    (V : 𝒱_pert[L, CodeSlotConfig qCodeBDL])
    (β_c β_max c_F_pert η : ℝ)
    (h_le : ∀ (β : ℝ) (hH : IsSelfAdjoint ((sys.reindex e_chk).H0 + V.totalPerturbation)),
      betaCritBDL < β → β ≤ β_max →
      gibbsFailureProb (sys.H0 + V.totalPerturbation)
        (isSelfAdjoint_H0_add_of_reindex sys e_chk V hH) β
        (1 - indexedBareFailureProjector sys S_safe) ≤
        Real.exp (-(c_F_pert * min (β - β_c) 1 * (((L ^ 3 : ℕ) : ℝ) ^ η))))
    (hβc : β_c = betaCritBDL) :
    FixedTempWindowGibbsBound (sys.reindex e_chk) Pi_safe V β_c β_max c_F_pert η := by
  intro β hH hβ hβ_le
  have hβ' : betaCritBDL < β := hβc ▸ hβ
  have h_bound := h_le β hH hβ' hβ_le
  have h_eq :
      gibbsFailureProb ((sys.reindex e_chk).H0 + V.totalPerturbation) hH β (1 - Pi_safe) =
      gibbsFailureProb (sys.H0 + V.totalPerturbation)
        (isSelfAdjoint_H0_add_of_reindex sys e_chk V hH) β
        (1 - indexedBareFailureProjector sys S_safe) := by
    rw [hPi, syndromeSubsetProj_eq_indexedBareFailureProjector]
    congr 1
    rw [sys.reindex_H0 e_chk]
  exact h_eq.le.trans h_bound

private lemma satisfiesWorldlineScaleCalibration_bdlBoxSide {R_pert k_0 k : ℕ}
    (hM_le_k0 : 4 * (Nat.ceil (collarConstRCABDL : ℝ) + 1) * (r0BDL + 1) * R_pert ≤ bdlLambda ^ k_0)
    (hk : k_0 ≤ k) (hk_ge_one : 1 ≤ k) :
    SatisfiesWorldlineScaleCalibration (bdlBoxSide k)
      (Nat.floor (cStarBDL * (bdlBoxSide k : ℝ))) R_pert r0BDL (collarConstRCABDL : ℝ) :=
  ⟨le_floor_c_star_BDL_mul_bdlBoxSide_of_le_bdlLambda_pow hM_le_k0 hk,
    r_0_BDL_le_C_rca_BDL,
    card_box3D_bdlBoxSide_le_exp_floor_c_star_BDL hk_ge_one⟩

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  bdlBoxSide HasSafeDecodedLogicalObservables SatisfiesUnperturbedThermalAndKMSStability
  SatisfiesZeroTempPerturbativeMemoryStability SatisfiesFixedTempWindowGibbsStability
  SatisfiesFixedTempPerturbativeGibbsStability
  LogCoolingPerturbativeSynthesis.SatisfiesScalingTempPerturbativeThermalAndKMSStability
  HasFiniteRangeBound
  IndexedCommutingProjectorHamiltonian.IsGeometricallyLocal
  IndexedCommutingProjectorHamiltonian.reindex bdlInhomogeneousSystem
  reindexHamiltonian reindexPerturbation conjSiteOp clusterRawWeight bdlClusterStepBase
  directWorldlineThreshold gibbsFailureProb betaCritBDL _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor
  FixedTempWindowGibbsBound SatisfiesWorldlineScaleCalibration

private lemma satisfiesFixedTempWindowGibbsStability_bdl_window {k N_chk R_pert R_bath k_0 : ℕ} {δ_split : ℝ} {g_LR : ℕ → ℝ}
    (e_chk : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin N_chk)
    (mem_k : Inhomogeneous3DMemoryRealization (bdlBoxSide k)
      qCodeBDL r0BDL mMaxBDL cStarBDL (collarConstRCABDL : ℝ)
      betaCritBDL cFBDL etaBDL cMemBDL)
    (S_safe_k : Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool))
    (W_family_k : Finset (Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL)))
    (V : 𝒱_pert[bdlBoxSide k, CodeSlotConfig qCodeBDL])
    (β_max J : ℝ)
    (h_zero_k : SatisfiesZeroTempPerturbativeMemoryStability
      (N_checks := N_chk) (mem_k.sys.reindex e_chk)
      mem_k.Pi_safe mem_k.O_dec_Z mem_k.O_dec_X V R_bath δ_split g_LR)
    (hR_pos : 1 ≤ R_pert)
    (hR_le_k0 : R_pert ≤ bdlLambda ^ k_0)
    (hM_le_k0 : 4 * (Nat.ceil (collarConstRCABDL : ℝ) + 1) * (r0BDL + 1) * R_pert ≤ bdlLambda ^ k_0)
    (hk : k_0 ≤ k) (hk_ge_one : 1 ≤ k) (hJ_nn : 0 ≤ J)
    (hJ_le_kp : J ≤ directWorldlineThreshold R_pert r0BDL
      ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) (collarConstRCABDL : ℝ) betaCritBDL β_max)
    (hV_range : HasFiniteRangeBound V R_pert J)
    (h_wk :
      mem_k.sys = bdlInhomogeneousSystem k ∧
      mem_k.Pi_safe = syndromeSubsetProj mem_k.sys S_safe_k ∧
      IsPositiveCheckWitnessCover S_safe_k W_family_k ∧
      (∀ W ∈ W_family_k, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes mem_k.D_field) ∧
      (∀ W ∈ W_family_k, clusterRawWeight k ≤ W.card) ∧
      (∑ W ∈ W_family_k, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1) :
    SatisfiesFixedTempWindowGibbsStability
      (N_checks := N_chk) (mem_k.sys.reindex e_chk)
      mem_k.Pi_safe mem_k.O_dec_Z mem_k.O_dec_X
      V R_bath betaCritBDL β_max cFBDL etaBDL δ_split g_LR :=
  satisfiesFixedTempWindowGibbsStability_of_zeroTemp
    (mem_k.sys.reindex e_chk) mem_k.Pi_safe mem_k.O_dec_Z mem_k.O_dec_X V h_zero_k
    (fixedTempWindowGibbsBound_reindex_of_orig mem_k.sys e_chk mem_k.Pi_safe S_safe_k
      h_wk.2.1 V betaCritBDL β_max cFBDL etaBDL
      (fun β hH hβ hβ_le =>
        (bdl_codeSlot_directWorldline_intact_cluster_bridge
          e_chk mem_k S_safe_k W_family_k V β_max β J
          (isSelfAdjoint_H0_add_of_reindex mem_k.sys e_chk V hH)
          hR_pos
          (le_floor_c_star_BDL_mul_bdlBoxSide_of_le_bdlLambda_pow hR_le_k0 hk)
          (satisfiesWorldlineScaleCalibration_bdlBoxSide hM_le_k0 hk hk_ge_one)
          hβ hβ_le hJ_nn hJ_le_kp hV_range
          h_wk.1 h_wk.2.2.1 h_wk.2.2.2.1 h_wk.2.2.2.2.1 h_wk.2.2.2.2.2).2)
      rfl)

/-- **Fixed-Temperature Perturbative Gibbs Stability on `CodeSlotConfig qCodeBDL`
    (`bdl_inhomogeneous_fixed_temp_gibbs_stability_codeSlot_of_equiv`)**. -/
theorem bdl_inhomogeneous_fixed_temp_gibbs_stability_codeSlot_of_equiv {N_c : ℕ → ℕ}
    (e_chk : ∀ k : ℕ, StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin (N_c k))
    (mem : ∀ k : ℕ, Inhomogeneous3DMemoryRealization (bdlBoxSide k)
        qCodeBDL r0BDL mMaxBDL cStarBDL (collarConstRCABDL : ℝ)
        betaCritBDL cFBDL etaBDL cMemBDL)
    (h_mem_spec : ∀ k : ℕ,
      (mem k).D_field = bdlLocalDescriptor k ∧
      (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k)
          (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
          (mem k).Pi_safe * (W.term r A * (mem k).O_dec_Z - (mem k).O_dec_Z * W.term r A) *
            (mem k).Pi_safe = 0 ∧
          (mem k).Pi_safe * (W.term r A * (mem k).O_dec_X - (mem k).O_dec_X * W.term r A) *
            (mem k).Pi_safe = 0))
    (h_obs_spec : ∀ k : ℕ,
      HasSafeDecodedLogicalObservables (N_checks := N_c k)
        ((mem k).sys.reindex (e_chk k)) (mem k).Pi_safe (mem k).O_dec_Z (mem k).O_dec_X
        (37 * bdlLambda ^ k))
    (S_safe : ∀ k : ℕ, Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool))
    (W_family : ∀ k : ℕ, Finset (Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL)))
    (h_witness_pkg : ∀ k : ℕ,
      (mem k).sys = bdlInhomogeneousSystem k ∧
      (mem k).Pi_safe = syndromeSubsetProj (mem k).sys (S_safe k) ∧
      IsPositiveCheckWitnessCover (S_safe k) (W_family k) ∧
      (∀ W ∈ W_family k, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes (mem k).D_field) ∧
      (∀ W ∈ W_family k, clusterRawWeight k ≤ W.card) ∧
      (∑ W ∈ W_family k, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1) :
    ∃ (c_F_pert : ℝ), 0 < c_F_pert ∧
      ∀ (R_pert : ℕ) (β_max : ℝ), 1 ≤ R_pert → betaCritBDL < β_max →
        ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
          0 < J_0 ∧
          R_pert ≤ bdlLambda ^ k_0 ∧
          IsSuperpolynomialDecay δ_split ∧
          IsSuperpolynomialDecay g_LR ∧
          ∀ (k : ℕ), k_0 ≤ k →
            ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
              ∀ (V : 𝒱_pert[bdlBoxSide k, CodeSlotConfig qCodeBDL]),
                HasFiniteRangeBound V R_pert J →
                SatisfiesFixedTempWindowGibbsStability
                  (N_checks := N_c k) ((mem k).sys.reindex (e_chk k))
                  (mem k).Pi_safe (mem k).O_dec_Z (mem k).O_dec_X
                  V 1 betaCritBDL β_max c_F_pert etaBDL (δ_split (bdlBoxSide k)) g_LR := by
  refine ⟨cFBDL, c_f_bdl_pos, fun R_pert β_max hR_pos _hβ_max => ?_⟩
  have h_ex := bdl_inhomogeneous_zero_temp_stability_codeSlot_of_equiv e_chk mem h_mem_spec h_obs_spec
      (finiteRangeDecayProfile R_pert) 1 (isSuperpolynomialDecay_finiteRangeDecayProfile R_pert) le_rfl
  have h1 := h_ex.choose_spec
  have h2 := h1.choose_spec
  have h3 := h2.choose_spec
  have h4 := h3.choose_spec
  have hJ0_kp : 0 < directWorldlineThreshold R_pert r0BDL
      ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) (collarConstRCABDL : ℝ) betaCritBDL β_max :=
    directWorldlineThreshold_pos R_pert r0BDL
      ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) (collarConstRCABDL : ℝ) betaCritBDL β_max
      hR_pos (Nat.cast_nonneg collarConstRCABDL) sixteen_le_beta_c_BDL
  have hR_le_k0 : R_pert ≤ bdlLambda ^
      (max h1.choose (max R_pert (4 * (Nat.ceil (collarConstRCABDL : ℝ) + 1) * (r0BDL + 1) * R_pert))) :=
    r_pert_le_bdlLambda_pow_of_le ((le_max_left R_pert _).trans (le_max_right h1.choose _))
  have hM_le_k0 : 4 * (Nat.ceil (collarConstRCABDL : ℝ) + 1) * (r0BDL + 1) * R_pert ≤ bdlLambda ^
      (max h1.choose (max R_pert (4 * (Nat.ceil (collarConstRCABDL : ℝ) + 1) * (r0BDL + 1) * R_pert))) :=
    r_pert_le_bdlLambda_pow_of_le ((le_max_right R_pert _).trans (le_max_right h1.choose _))
  refine ⟨min h_ex.choose (directWorldlineThreshold R_pert r0BDL
      ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) (collarConstRCABDL : ℝ) betaCritBDL β_max),
    max h1.choose (max R_pert (4 * (Nat.ceil (collarConstRCABDL : ℝ) + 1) * (r0BDL + 1) * R_pert)),
    h2.choose, h3.choose, lt_min h4.1 hJ0_kp, hR_le_k0, h4.2.1, h4.2.2.1,
    fun k hk J hJ_nn hJ_le V hV_range => ?_⟩
  have hk_z : h1.choose ≤ k := (le_max_left h1.choose _).trans hk
  have hJ_le_z : J ≤ h_ex.choose := hJ_le.trans (min_le_left _ _)
  have hJ_le_kp : J ≤ directWorldlineThreshold R_pert r0BDL
      ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) (collarConstRCABDL : ℝ) betaCritBDL β_max :=
    hJ_le.trans (min_le_right _ _)
  have hV_dec : V.SatisfiesDecayBound J (finiteRangeDecayProfile R_pert) :=
    satisfiesDecayBound_of_hasFiniteRangeBound hJ_nn hV_range
  have hk_ge_one : 1 ≤ k :=
    hR_pos.trans ((le_max_left R_pert _).trans ((le_max_right h1.choose _).trans hk))
  exact satisfiesFixedTempWindowGibbsStability_bdl_window
    (e_chk k) (mem k) (S_safe k) (W_family k) V β_max J
    (h4.2.2.2 k hk_z J hJ_nn hJ_le_z V hV_dec)
    hR_pos hR_le_k0 hM_le_k0 hk hk_ge_one hJ_nn hJ_le_kp hV_range (h_witness_pkg k)

def memWitnessBDL (k : ℕ) :
    Inhomogeneous3DMemoryRealization (bdlBoxSide k) qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL :=
  (bdl_inhomogeneous_codeSlot_memory_package_with_witness_cover k (equivStaticCSSCheckBDL k)).choose

def safeSyndromeWitnessBDL (k : ℕ) :
    Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :=
  (bdl_inhomogeneous_codeSlot_memory_package_with_witness_cover k (equivStaticCSSCheckBDL k)).choose_spec.choose

def witnessFamilyBDL (k : ℕ) :
    Finset (Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL)) :=
  (bdl_inhomogeneous_codeSlot_memory_package_with_witness_cover k (equivStaticCSSCheckBDL k)).choose_spec.choose_spec.choose

lemma memWitnessBDL_spec (k : ℕ) :
    (memWitnessBDL k).sys = bdlInhomogeneousSystem k ∧
    (memWitnessBDL k).Pi_safe = syndromeSubsetProj (memWitnessBDL k).sys (safeSyndromeWitnessBDL k) ∧
    (memWitnessBDL k).D_field = bdlLocalDescriptor k ∧
    (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k)
        (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
      ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
        (memWitnessBDL k).Pi_safe * (W.term r A * (memWitnessBDL k).O_dec_Z - (memWitnessBDL k).O_dec_Z * W.term r A) *
          (memWitnessBDL k).Pi_safe = 0 ∧
        (memWitnessBDL k).Pi_safe * (W.term r A * (memWitnessBDL k).O_dec_X - (memWitnessBDL k).O_dec_X * W.term r A) *
          (memWitnessBDL k).Pi_safe = 0) ∧
    HasSafeDecodedLogicalObservables (N_checks := nChecksBDL k)
      ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))
      (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
      (37 * bdlLambda ^ k) ∧
    IsPositiveCheckWitnessCover (safeSyndromeWitnessBDL k) (witnessFamilyBDL k) ∧
    (∀ W ∈ witnessFamilyBDL k, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes (memWitnessBDL k).D_field) ∧
    (∀ W ∈ witnessFamilyBDL k, clusterRawWeight k ≤ W.card) ∧
    (∑ W ∈ witnessFamilyBDL k, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1 :=
  (bdl_inhomogeneous_codeSlot_memory_package_with_witness_cover k (equivStaticCSSCheckBDL k)).choose_spec.choose_spec.choose_spec

lemma memWitnessBDL_mem_spec (k : ℕ) :
    (memWitnessBDL k).D_field = bdlLocalDescriptor k ∧
    (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k) (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
      ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
        (memWitnessBDL k).Pi_safe * (W.term r A * (memWitnessBDL k).O_dec_Z - (memWitnessBDL k).O_dec_Z * W.term r A) *
          (memWitnessBDL k).Pi_safe = 0 ∧
        (memWitnessBDL k).Pi_safe * (W.term r A * (memWitnessBDL k).O_dec_X - (memWitnessBDL k).O_dec_X * W.term r A) *
          (memWitnessBDL k).Pi_safe = 0) :=
  ⟨(memWitnessBDL_spec k).2.2.1, (memWitnessBDL_spec k).2.2.2.1⟩

lemma memWitnessBDL_obs_spec (k : ℕ) :
    HasSafeDecodedLogicalObservables (N_checks := nChecksBDL k)
      ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))
      (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
      (37 * bdlLambda ^ k) :=
  (memWitnessBDL_spec k).2.2.2.2.1

lemma memWitnessBDL_witness_pkg (k : ℕ) :
    (memWitnessBDL k).sys = bdlInhomogeneousSystem k ∧
    (memWitnessBDL k).Pi_safe = syndromeSubsetProj (memWitnessBDL k).sys (safeSyndromeWitnessBDL k) ∧
    IsPositiveCheckWitnessCover (safeSyndromeWitnessBDL k) (witnessFamilyBDL k) ∧
    (∀ W ∈ witnessFamilyBDL k, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes (memWitnessBDL k).D_field) ∧
    (∀ W ∈ witnessFamilyBDL k, clusterRawWeight k ≤ W.card) ∧
    (∑ W ∈ witnessFamilyBDL k, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1 :=
  ⟨(memWitnessBDL_spec k).1, (memWitnessBDL_spec k).2.1, (memWitnessBDL_spec k).2.2.2.2.2⟩

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  betaCritBDL _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor
  dLocBDL equivCodeSlotBDL nChecksBDL equivStaticCSSCheckBDL
  memWitnessBDL safeSyndromeWitnessBDL witnessFamilyBDL

/-- **Fixed-Temperature Perturbative Gibbs Self-Correction Synthesis
    (`fixed_temp_perturbative_gibbs_stability_main`)**
    (Part II, Section 6.3 (`subsec:main-theorems`), Theorem 6.3 (`thm:main-A`) and Theorem 6.4 (`thm:main-B`)). -/
theorem fixed_temp_perturbative_gibbs_stability_main :
    ∃ (d_loc r_0 w_0 Λ_scale : ℕ)
      (β_c c_F c_F_pert C_scale c_F_dress η : ℝ)
      (L N_checks : ℕ → ℕ)
      (_ : ∀ k : ℕ, NeZero (L k))
      (_ : NeZero d_loc)
      (sys : ∀ k : ℕ, ℋ_CP[L k, Fin d_loc, N_checks k])
      (Pi_safe O_dec_Z O_dec_X : ∀ k : ℕ, ℬ[L k, Fin d_loc]),
      2 ≤ d_loc ∧ 1 ≤ r_0 ∧ 1 ≤ w_0 ∧ 2 ≤ Λ_scale ∧
      0 < β_c ∧ 0 < c_F ∧ 0 < c_F_pert ∧ 0 < C_scale ∧ 0 < c_F_dress ∧ 0 < η ∧
      (∀ k : ℕ, L k = Λ_scale ^ (2 * k + 4)) ∧
      IsStrictlyIncreasingBoxSequence L ∧
      (∀ k : ℕ,
        (sys k).IsGeometricallyLocal r_0 w_0 ∧
        (∀ i : Fin (N_checks k), (sys k).weight i = 1) ∧
        HasSafeDecodedLogicalObservables (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
          (37 * Λ_scale ^ k) ∧
        SatisfiesUnperturbedThermalAndKMSStability (sys k)
          (Pi_safe k) (O_dec_Z k) (O_dec_X k) (37 * Λ_scale ^ k) w_0 β_c c_F η) ∧
      (∀ (R_pert R_bath : ℕ) (β_max : ℝ),
        1 ≤ R_pert →
        1 ≤ R_bath →
        β_c < β_max →
        ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
          0 < J_0 ∧
          IsSuperpolynomialDecay δ_split ∧
          IsSuperpolynomialDecay g_LR ∧
          ∀ (k : ℕ), k_0 ≤ k →
            ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
              ∀ (V : 𝒱_pert[L k, Fin d_loc]),
                HasFiniteRangeBound V R_pert J →
                SatisfiesFixedTempPerturbativeGibbsStability
                  (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
                  V R_bath β_c β_max c_F_pert C_scale c_F_dress η (δ_split (L k)) g_LR) := by
  have h_ft_ex := bdl_inhomogeneous_fixed_temp_gibbs_stability_codeSlot_of_equiv
    equivStaticCSSCheckBDL memWitnessBDL memWitnessBDL_mem_spec memWitnessBDL_obs_spec
    safeSyndromeWitnessBDL witnessFamilyBDL memWitnessBDL_witness_pkg
  have h_ft_spec := h_ft_ex.choose_spec
  have h_obs₁ : ∀ k : ℕ,
      HasSafeDecodedLogicalObservables
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X)
        (37 * bdlLambda ^ k) :=
    fun k => hasSafeDecodedLogicalObservables_reindexHamiltonian equivCodeSlotBDL
      ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))
      (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
      (memWitnessBDL_obs_spec k)
  refine ⟨dLocBDL, r0BDL, (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL), bdlLambda,
    betaCritBDL, cFBDL, h_ft_ex.choose, 4 * ((qCodeBDL + 2 * mMaxBDL : ℕ) : ℝ) + 4, (1 / 4 : ℝ),
    etaBDL, bdlBoxSide, nChecksBDL, inferInstance, inferInstance,
    fun k => reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)),
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X,
    two_le_d_loc_bdl, r_0_BDL_ge_one, w_0_BDL_ge_one, two_le_bdlLambda,
    beta_crit_bdl_pos, c_f_bdl_pos, h_ft_spec.1, LogCoolingPerturbativeSynthesis.c_scale_BDL_pos,
    LogCoolingPerturbativeSynthesis.c_F_pert_BDL_pos, eta_bdl_pos,
    bdlBoxSide_eq_bdlLambda_pow,
    fun k => (bdlBoxSide_scaling_and_strictMono k).2, ?_, ?_⟩
  · intro k
    rcases memWitnessBDL_spec k with ⟨h_sys_eq, h_Pi_eq, _hD, _h_fw_macro, _h_obs₀⟩
    have h_geom : (reindexHamiltonian (fun _ => equivCodeSlotBDL)
        ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))).IsGeometricallyLocal
        r0BDL ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) := by
      refine reindexHamiltonian_isGeometricallyLocal equivCodeSlotBDL
        ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)) ?_
      rw [h_sys_eq]; exact isGeometricallyLocal_bdlInhomogeneousSystem_reindex k (equivStaticCSSCheckBDL k)
    have h_unit : ∀ i : Fin (nChecksBDL k),
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))).weight i = 1 := by
      intro i
      rw [reindexHamiltonian_reindex_weight equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memWitnessBDL k).sys i,
        ((memWitnessBDL k).h_sys_checks ((equivStaticCSSCheckBDL k).symm i)).2.2]
    have h_therm_k : SatisfiesUnperturbedThermalAndKMSStability
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X)
        (37 * bdlLambda ^ k) ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL))
        betaCritBDL cFBDL etaBDL :=
      satisfiesUnperturbedThermalAndKMSStability_reindexHamiltonian
        equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memWitnessBDL k).sys (safeSyndromeWitnessBDL k)
        (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
        h_Pi_eq h_geom h_unit (four_mul_r0BDL_add_one_le_37_mul_pow k)
        (fun β hβ => ((memWitnessBDL k).h_unperturbed_thermal_and_kms_lifetime β hβ).1) (h_obs₁ k)
    exact ⟨h_geom, h_unit, h_obs₁ k, h_therm_k⟩
  · intro R_pert R_bath β_max hR_pert hR_bath hβ_max
    have h_fix_ex := h_ft_spec.2 R_pert β_max hR_pert hβ_max
    have h_fix1 := h_fix_ex.choose_spec
    have h_fix2 := h_fix1.choose_spec
    have h_fix3 := h_fix2.choose_spec
    have h_fix4 := h_fix3.choose_spec
    have h_log_ex := LogCoolingPerturbativeSynthesis.bdl_inhomogeneous_scaling_temp_stability_of_equiv
      equivCodeSlotBDL equivStaticCSSCheckBDL memWitnessBDL (fun k => (memWitnessBDL_spec k).1)
      memWitnessBDL_mem_spec memWitnessBDL_obs_spec
      (finiteRangeDecayProfile R_pert) R_bath
      (isSuperpolynomialDecay_finiteRangeDecayProfile R_pert) hR_bath
    have h_log1 := h_log_ex.choose_spec
    have h_log2 := h_log1.choose_spec
    have h_log3 := h_log2.choose_spec
    have h_log4 := h_log3.choose_spec
    refine ⟨min h_fix_ex.choose h_log_ex.choose, max h_fix1.choose h_log1.choose,
      h_log2.choose, h_log3.choose,
      lt_min h_fix4.1 h_log4.1, h_log4.2.1, h_log4.2.2.1,
      fun k hk J hJ_nn hJ_le V₁ hV₁_range => ?_⟩
    have hk_fix : h_fix1.choose ≤ k := (le_max_left h_fix1.choose h_log1.choose).trans hk
    have hk_log : h_log1.choose ≤ k := (le_max_right h_fix1.choose h_log1.choose).trans hk
    have hJ_fix : J ≤ h_fix_ex.choose := hJ_le.trans (min_le_left h_fix_ex.choose h_log_ex.choose)
    have hJ_log : J ≤ h_log_ex.choose := hJ_le.trans (min_le_right h_fix_ex.choose h_log_ex.choose)
    have hV₀_range : HasFiniteRangeBound
        (reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => equivCodeSlotBDL.symm) V₁) R_pert J :=
      hasFiniteRangeBound_reindexPerturbation (fun _ => equivCodeSlotBDL.symm) hV₁_range
    have h_gibbs₀ := h_fix4.2.2.2.2 k hk_fix J hJ_nn hJ_fix
      (reindexPerturbation (fun _ => equivCodeSlotBDL.symm) V₁) hV₀_range
    have hP0_sa : IsSelfAdjoint (memWitnessBDL k).sys.P0 := (memWitnessBDL k).sys.isStarProjection_P0.isSelfAdjoint
    have hOZ := (memWitnessBDL k).h_decoder_props.2.1; have hOX := (memWitnessBDL k).h_decoder_props.2.2.1
    have hZ := (memWitnessBDL k).h_logical_pair.2.1; have hX := (memWitnessBDL k).h_logical_pair.2.2.1
    have hP0_OZ : Commute ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)).P0 (memWitnessBDL k).O_dec_Z := by
      rw [(memWitnessBDL k).sys.reindex_P0 (equivStaticCSSCheckBDL k)]; exact commute_P0_of_mul_P0_eq hP0_sa hOZ.1 hZ.1 hZ.2.2.2 hOZ.2.2.2.2.1
    have hP0_OX : Commute ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)).P0 (memWitnessBDL k).O_dec_X := by
      rw [(memWitnessBDL k).sys.reindex_P0 (equivStaticCSSCheckBDL k)]; exact commute_P0_of_mul_P0_eq hP0_sa hOX.1 hX.1 hX.2.2.2 hOX.2.2.2.2.1
    have h_win₁ := satisfiesFixedTempPerturbativeGibbsStability_reindexHamiltonian
      equivCodeSlotBDL ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k))
      (memWitnessBDL k).Pi_safe (memWitnessBDL k).O_dec_Z (memWitnessBDL k).O_dec_X
      hOZ.2.2.1 hP0_OZ hOX.2.2.1 hP0_OX V₁ h_gibbs₀
    have hV₁_dec : V₁.SatisfiesDecayBound J (finiteRangeDecayProfile R_pert) :=
      satisfiesDecayBound_of_hasFiniteRangeBound hJ_nn hV₁_range
    have h_log₁ := h_log4.2.2.2 k hk_log J hJ_nn hJ_log V₁ hV₁_dec
    exact satisfiesFixedTempPerturbativeGibbsStability_of_window_and_scaling
      (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memWitnessBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
      (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).Pi_safe)
      (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_Z)
      (conjSiteOp (fun _ => equivCodeSlotBDL) (memWitnessBDL k).O_dec_X)
      V₁ h_win₁ h_log₁

end FixedTempPerturbativeGibbsSynthesis

end
