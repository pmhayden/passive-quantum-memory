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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellSpanning
import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellShuffleSeries

/-!
# Realizable-Syndrome Trace Reduction and Exact Dyson–Mayer Polymer-Gas Partition Identity

Reduces Boltzmann witness traces to sums over realizable static CSS syndromes (`hilbertTrace_gibbsBoltzmannOp_witness_eq_sum_realizableSyndromes`) and proves absolute summability of character-averaged Mayer polymer cluster weights (`summable_worldlineMayerPolymerClusterWeight`). Establishes the exact worldline Dyson–Mayer polymer-gas partition identity (`worldline_dyson_mayer_polymer_gas_partition_identity`) in each syndrome sector.

## References

* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier
open SpacetimeWorldlineKP

set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace DirectWorldlineCluster

local notation "SiteCSS[" L ", " q_code "]" => UniformSite3D L (CodeSlotConfig q_code)
local notation "ℋ_CSS[" L ", " q_code "]" => ManyBodyHilbertSpace (SiteCSS[L, q_code])
local notation "ℬ_CSS[" L ", " q_code "]" => ℋ_CSS[L, q_code] →L[ℂ] ℋ_CSS[L, q_code]
local notation "IdxCSS[" L ", " q_code ", " m_max "]" => StaticCSSCheckIdx L q_code m_max
local notation "SysCSS[" L ", " q_code ", " m_max "]" =>
  IndexedCommutingProjectorHamiltonian 3 L (SiteCSS[L, q_code]) (IdxCSS[L, q_code, m_max])

/-- **Per-sector reduction for the witness-projected Gibbs trace**:
Since `positiveCheckWitnessProj sys W` is the sum of `sys.syndromeProjector σ` over all `σ`
satisfying the witness `W`, and `sys.syndromeProjector σ = 0` for `σ ∉ realizableSyndromes D_field`,
the witness-projected trace equals the sum over `σ ∈ (realizableSyndromes D_field).filter ...`
of the per-sector traces `hilbertTrace (gibbsBoltzmannOp ... * sys.syndromeProjector σ)`. -/
lemma hilbertTrace_gibbsBoltzmannOp_witness_eq_sum_realizableSyndromes
    {L q_code r_0 m_max : ℕ} [NeZero L]
    {β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (H : ℬ_CSS[L, q_code]) (hH : IsSelfAdjoint H)
    (W : Finset (IdxCSS[L, q_code, m_max])) :
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
      positiveCheckWitnessProj sys W) =
      ∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
        hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
          sys.syndromeProjector σ) := by
  have h_sec_trace : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
        sys.syndromeProjector σ) =
        if σ ∈ realizableSyndromes D_field then
          hilbertTrace (gibbsBoltzmannOp (opEigenbasis H hH) (opEigenvalues H hH) β *
            sys.syndromeProjector σ)
        else 0 := by
    intro σ
    by_cases hσ : σ ∈ realizableSyndromes D_field
    · rw [if_pos hσ]
    · rw [if_neg hσ]
      have h_zero : sys.syndromeProjector σ = 0 := by
        by_contra h_ne
        obtain ⟨⟨a, b, hab⟩, _⟩ :=
          hilbertTrace_syndromeProjector_eq_P0_of_ne_zero D_field h_valid sys h_sys_checks σ h_ne
        exact hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, a, b, hab⟩)
      rw [h_zero, mul_zero]; unfold hilbertTrace; simp
  unfold positiveCheckWitnessProj
  rw [Finset.mul_sum, hilbertTrace_sum]
  refine (Finset.sum_congr rfl fun x _ => h_sec_trace x).trans ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]

/-- **Character-Averaged Multi-Polymer Cluster Weight on a Realizable Syndrome Sector**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)):
Averaging `worldlineMayerPolymerClusterWeight` over all logical characters
`ν ∈ syndromeClosedPauliFinset D_field` projects onto multi-polymer configurations whose net loop
operator commutes with all syndrome-closed Pauli operators and replaces the character-twisted
polymer weights by the product of local untwisted simplex weights. -/
lemma character_average_worldlineMayerPolymerClusterWeight_eq_of_realizable
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA J β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field)
    (K : WorldlineUrsellCluster L q_code) :
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K) =
    if (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
        K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) ∧
        (∀ ν ∈ syndromeClosedPauliFinset D_field,
          symplecticPauliSign ν
            (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1) then
      (Nat.factorial K.length : ℝ)⁻¹ *
        (K.map (fun γ =>
          ((-1 : ℝ) ^ γ.1.length) *
            (hilbertTrace (sys.syndromeProjector σ *
              ((hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
                (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)† *
                worldlinePolymerWeightedLoopOp D_field sys V γ)) /
              hilbertTrace (sys.syndromeProjector σ)) *
            ∫ τ : Fin γ.1.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys γ.1 σ β τ) *
                  ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ
              else 0)).prod
    else 0 := by
  rw [multiPolymer_logical_character_average_clusterWeight_eq D_field h_valid sys h_sys_checks]
  split_ifs with hK
  · rw [list_prod_spanningSurfaceSign_mul_worldlinePolymerMicroWeight_eq_of_valid
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le V e_loc d_loc h_scalar
      K hK.1 hσ]
  · rfl

/-- Multi-polymer character average of `worldlineMayerPolymerClusterWeight` over
$\nu \in \mathcal{G}_{\mathrm{closed}}$ on a realizable syndrome $\sigma \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$,
expressed via the net loop bitstring condition
`∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
lemma character_average_worldlineMayerPolymerClusterWeight_eq_loop_of_realizable
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA J β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (K : WorldlineUrsellCluster L q_code)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K) =
    if (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
        K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) then
      if ∀ ν ∈ syndromeClosedPauliFinset D_field,
          symplecticPauliSign ν
            (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1 then
        ((Nat.factorial K.length : ℝ)⁻¹) *
          (K.map (fun γ =>
            ((-1 : ℝ) ^ γ.1.length) *
              (hilbertTrace (sys.syndromeProjector σ *
                ((hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
                  (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)† *
                  worldlinePolymerWeightedLoopOp D_field sys V γ)) /
                hilbertTrace (sys.syndromeProjector σ)) *
              ∫ τ : Fin γ.1.length → ℝ,
                if InOrderedDysonSimplex β τ then
                  Real.exp (-worldlineBareAction D_field sys γ.1 σ β τ) *
                    ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ
                else 0)).prod
      else 0
    else 0 := by
  rw [character_average_worldlineMayerPolymerClusterWeight_eq_of_realizable
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le V e_loc d_loc h_scalar hσ K]
  by_cases hK : (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
  · by_cases h_loop : ∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν
          (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1
    · rw [if_pos ⟨hK.1, hK.2, h_loop⟩, if_pos hK, if_pos h_loop]
    · rw [if_neg (fun h => h_loop h.2.2), if_pos hK, if_neg h_loop]
  · rw [if_neg (fun h => hK ⟨h.1, h.2.1⟩), if_neg hK]

/-- Exact right-multiplication action of a single coset-reduced time-reversal symmetrized polymer
operator `worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V γ` on `sys.syndromeProjector σ₀`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma worldlinePolymerSymmetrizedWeightedLoopOp_mul_syndromeProjector_eq
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V γ * sys.syndromeProjector σ₀ =
      (((worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
          (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀) *
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀ : ℝ) : ℂ) •
        sys.syndromeProjector σ₀) := by
  let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
  rcases hermitianPauliZX_isSelfAdjoint_and_sq_eq_one μ.1 μ.2 with ⟨hM_sa, hM_sq⟩
  have hM_adj : (hermitianPauliZX μ.1 μ.2)† = hermitianPauliZX μ.1 μ.2 :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hM_sa
  have h_act := (worldlinePolymerWeightedLoopOp_and_loopAmplitude_reverse_eq
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V γ hγ hσ₀).2.1
  calc worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V γ * sys.syndromeProjector σ₀
    _ = (hermitianPauliZX μ.1 μ.2)† *
          (((1 / 2 : ℂ) • (worldlinePolymerWeightedLoopOp D_field sys V γ +
            worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2))) *
            sys.syndromeProjector σ₀) := by
        unfold worldlinePolymerSymmetrizedWeightedLoopOp
        dsimp only [μ]
        rw [clm_smul_mul, clm_smul_mul, clm_mul_smul, mul_assoc]
    _ = (hermitianPauliZX μ.1 μ.2)† *
          (((worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
              (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀) *
            spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀ : ℝ) : ℂ) •
            (hermitianPauliZX μ.1 μ.2 * sys.syndromeProjector σ₀)) := by
        rw [h_act]
    _ = (((worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀) *
          spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀ : ℝ) : ℂ) •
          sys.syndromeProjector σ₀) := by
        rw [clm_mul_smul, ← mul_assoc, hM_adj, hM_sq, one_mul]

/-- Exact right-multiplication action of the product of coset-reduced time-reversal symmetrized
polymer operators `(K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod` on
`sys.syndromeProjector σ₀` (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma list_prod_worldlinePolymerSymmetrizedWeightedLoopOp_mul_syndromeProjector_eq
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod *
      sys.syndromeProjector σ₀ =
    (((K.map (fun γ =>
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀)).prod *
      (K.map (fun γ =>
        worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
          (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀))).prod : ℝ) : ℂ) •
      sys.syndromeProjector σ₀ := by
  induction K with
  | nil =>
    simp
  | cons hd tl ih =>
    have h_hd_valid : IsValidWorldlinePolymer D_field sys C_RCA R_cut hd :=
      hK_valid hd List.mem_cons_self
    have h_tl_valid : ∀ γ ∈ tl, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ :=
      fun γ hγ => hK_valid γ (List.mem_cons_of_mem hd hγ)
    have h_hd_act := worldlinePolymerSymmetrizedWeightedLoopOp_mul_syndromeProjector_eq
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V h_hd_valid hσ₀
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, ih h_tl_valid, clm_mul_smul, h_hd_act, smul_smul, ← Complex.ofReal_mul]
    congr 2
    ring

/-- Any list `K` of logical coset bitstring pairs has its product of `hermitianPauliZX` operators
equal to a scalar multiple `z • (weylPauliZ a_sum * weylPauliX b_sum)` where `(a_sum, b_sum) = (K.map ...).sum`. -/
lemma list_prod_hermitianPauliZX_eq_smul_weylPauliZX
    {L q_code : ℕ} (l : List (PauliBitstringPair L q_code)) :
    ∃ z : ℂ,
      (l.map (fun μ => hermitianPauliZX μ.1 μ.2)).prod =
        z • (weylPauliZ l.sum.1 * weylPauliX l.sum.2) := by
  induction l with
  | nil =>
    refine ⟨1, ?_⟩
    simp [weylPauliZ_zero, weylPauliX_zero]
  | cons hd tl ih =>
    rcases ih with ⟨z_tl, hz_tl⟩
    have h_hd : ∃ z_hd : ℂ, hermitianPauliZX hd.1 hd.2 = z_hd • (weylPauliZ hd.1 * weylPauliX hd.2) := by
      unfold hermitianPauliZX
      split_ifs <;> [exact ⟨1, (one_smul ℂ _).symm⟩; exact ⟨Complex.I, rfl⟩]
    rcases h_hd with ⟨z_hd, hz_hd⟩
    refine ⟨z_hd * z_tl * signScalar (∑ p : BoxSlot3D L q_code, tl.sum.1 p * hd.2 p), ?_⟩
    simp only [List.map_cons, List.prod_cons, List.sum_cons, Prod.fst_add, Prod.snd_add]
    rw [hz_hd, hz_tl, clm_smul_mul, clm_mul_smul, weylPauliZX_mul_weylPauliZX,
      smul_smul, smul_smul]

/-- Simultaneous vanishing of the multi-polymer Duhamel–Dyson sector trace and the character average
of `worldlineMayerPolymerClusterWeight` whenever the net loop Pauli bitstring anticommutes with some
$\nu_0 \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$ (Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`) and Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)). -/
lemma multiPolymer_trace_and_clusterWeight_character_average_eq_zero_of_anticomm
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field)
    (h_not_all : ¬(∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1)) :
    hilbertTrace (sys.syndromeProjector σ₀ *
      (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) = 0 ∧
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ₀ K) = 0 := by
  rcases multiPolymer_trace_and_character_average_eq_zero_of_anticomm
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V d_loc K hK_valid hσ₀ h_not_all with
    ⟨h_tr_zero, h_prod_zero⟩
  refine ⟨h_tr_zero, ?_⟩
  unfold worldlineMayerPolymerClusterWeight
  by_cases h_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
  · have h_congr :
        (∑ ν ∈ syndromeClosedPauliFinset D_field,
          (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
            (if (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
                K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) then
              ((Nat.factorial K.length : ℝ)⁻¹) *
                (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ₀)).prod
            else 0)) =
        ((Nat.factorial K.length : ℝ)⁻¹) *
          (∑ ν ∈ syndromeClosedPauliFinset D_field,
            (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
              (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ₀)).prod) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ν _ => ?_
      rw [if_pos ⟨hK_valid, h_pw⟩]
      ring
    rw [h_congr, h_prod_zero, mul_zero]
  · refine Finset.sum_eq_zero fun ν _ => ?_
    rw [if_neg (fun h => h_pw h.2), mul_zero]

/-- Multi-polymer operator trace factorization on a realizable syndrome
$\sigma_0 \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$ when the net loop Pauli bitstring
commutes with all syndrome-closed Pauli operators $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma multiPolymer_prod_single_trace_eq_multiPolymer_trace_of_commute
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    (K.map (fun γ =>
      hilbertTrace (sys.syndromeProjector σ₀ *
        ((hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
          (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)† *
          worldlinePolymerWeightedLoopOp D_field sys V γ)) /
        hilbertTrace (sys.syndromeProjector σ₀))).prod =
    hilbertTrace (sys.syndromeProjector σ₀ *
      (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) /
      hilbertTrace (sys.syndromeProjector σ₀) := by
  have hV_supp : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      IsSupportedOn (SiteCSS[L, q_code]) A (V.term r A) :=
    fun r hr A hA => V.is_supported r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩) A hA
  have h_lhs_eq :
      (K.map (fun γ =>
        hilbertTrace (sys.syndromeProjector σ₀ *
          ((hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
            (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)† *
            worldlinePolymerWeightedLoopOp D_field sys V γ)) /
          hilbertTrace (sys.syndromeProjector σ₀))).prod =
      (K.map (fun γ =>
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀)).prod *
      (K.map (fun γ =>
        worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
          (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀))).prod := by
    rw [list_prod_mul_distrib]
    exact congrArg List.prod (List.map_congr_left fun γ hγ =>
      (spanningSurfaceSign_mul_worldlinePolymerLoopAmplitude_eq_of_valid
        D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V hV_supp γ (hK_valid γ hγ) hσ₀).symm)
  have h_act := list_prod_worldlinePolymerSymmetrizedWeightedLoopOp_mul_syndromeProjector_eq
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V K hK_valid hσ₀
  have h_idem := ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
  rcases hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes
      D_field h_valid sys h_sys_checks hσ₀ with ⟨_, h_tr_pos⟩
  have h_tr_ne : hilbertTrace (sys.syndromeProjector σ₀) ≠ 0 := ne_of_gt h_tr_pos
  let c_real : ℝ :=
    (K.map (fun γ =>
      spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ₀)).prod *
    (K.map (fun γ =>
      worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
        (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀))).prod
  have h_tr_rhs :
      hilbertTrace (sys.syndromeProjector σ₀ *
        (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) =
      c_real * hilbertTrace (sys.syndromeProjector σ₀) := by
    calc hilbertTrace (sys.syndromeProjector σ₀ *
          (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod)
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) *
            (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) := by rw [h_idem]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            ((K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod *
              sys.syndromeProjector σ₀)) := by
          rw [mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ₀) _, mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * (((c_real : ℝ) : ℂ) • sys.syndromeProjector σ₀)) := by
          rw [h_act]
      _ = c_real * hilbertTrace (sys.syndromeProjector σ₀) := by
          rw [clm_mul_smul, h_idem,
            (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 c_real 0).2.1]
  rw [h_lhs_eq, h_tr_rhs, mul_div_cancel_right₀ _ h_tr_ne]

/-- Multi-polymer Duhamel–Dyson cluster weight identity on a realizable syndrome
$\sigma_0 \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$ (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equations `eq:P-gamma-spanning-surface` and `eq:ursell-partition-sigma`):
for any pairwise collar-compatible tuple `K` of valid worldline polymers, the character average
over $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$ of `worldlineMayerPolymerClusterWeight`
equals the multi-polymer Duhamel–Dyson cluster amplitude on `sys.syndromeProjector σ₀`. -/
lemma multiPolymer_character_average_clusterWeight_eq_multiPolymer_trace
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA J β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ₀ K) =
    if ∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν
          (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1 then
      ((Nat.factorial K.length : ℝ)⁻¹) *
        (hilbertTrace (sys.syndromeProjector σ₀ *
          (K.map (worldlinePolymerSymmetrizedWeightedLoopOp D_field sys C_RCA V)).prod) /
          hilbertTrace (sys.syndromeProjector σ₀)) *
        (K.map (fun γ =>
          ((-1 : ℝ) ^ γ.1.length) *
            ∫ τ : Fin γ.1.length → ℝ,
              if InOrderedDysonSimplex β τ then
                Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
                  ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
              else 0)).prod
    else 0 := by
  by_cases h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1
  · rw [if_pos h_comm, character_average_worldlineMayerPolymerClusterWeight_eq_loop_of_realizable
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le V e_loc d_loc h_scalar K hσ₀,
      if_pos ⟨hK_valid, hK_pw⟩, if_pos h_comm,
      ← multiPolymer_prod_single_trace_eq_multiPolymer_trace_of_commute
        D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le V K hK_valid hK_pw h_comm hσ₀,
      mul_assoc]
    refine congrArg ((Nat.factorial K.length : ℝ)⁻¹ * ·) ?_
    refine Eq.trans ?_ (list_prod_mul_distrib K
      (fun γ =>
        hilbertTrace (sys.syndromeProjector σ₀ *
          ((hermitianPauliZX (worldlinePolymerLogicalCoset D_field sys C_RCA γ).1
            (worldlinePolymerLogicalCoset D_field sys C_RCA γ).2)† *
            worldlinePolymerWeightedLoopOp D_field sys V γ)) /
          hilbertTrace (sys.syndromeProjector σ₀))
      (fun γ =>
        ((-1 : ℝ) ^ γ.1.length) *
          ∫ τ : Fin γ.1.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys γ.1 σ₀ β τ) *
                ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ
            else 0)).symm
    exact congrArg List.prod (List.map_congr_left fun γ _ => by ring)
  · rw [if_neg h_comm]
    exact (multiPolymer_trace_and_clusterWeight_character_average_eq_zero_of_anticomm
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V d_loc K hK_valid hσ₀ h_comm).2

/-- For every polymer tuple $K : \mathrm{WorldlineUrsellCluster}\;L\;q_{\mathrm{code}}$ and every
realizable syndrome $\sigma_0 \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$, the discrete
character average over $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$ of
`worldlineMayerPolymerClusterWeight` equals `worldlineDysonMultiPolymerClusterWeight`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
lemma character_average_worldlineMayerPolymerClusterWeight_eq_dysonMultiPolymerClusterWeight
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA J β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (K : WorldlineUrsellCluster L q_code)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ₀ K) =
    worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K := by
  unfold worldlineDysonMultiPolymerClusterWeight
  by_cases hK : (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
  · rw [if_pos hK]
    exact multiPolymer_character_average_clusterWeight_eq_multiPolymer_trace
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le V e_loc d_loc h_scalar
      K hK.1 hK.2 hσ₀
  · rw [if_neg hK]
    unfold worldlineMayerPolymerClusterWeight
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [if_neg hK, mul_zero]

/-- Interchanging the finite character average over $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$
with the polymer-gas partition sum `worldlineMayerPolymerPartition` (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
lemma character_average_worldlineMayerPolymerPartition_eq_tsum_dysonMultiPolymerClusterWeight
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA J β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field)
    (h_summable : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      Summable (worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ₀)) :
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ₀) *
          worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ₀) =
    Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ₀) *
      ∑' K : WorldlineUrsellCluster L q_code,
        worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ₀ K := by
  let N_closed := ((syndromeClosedPauliFinset D_field).card : ℝ)
  have h_factor :
      (∑ ν ∈ syndromeClosedPauliFinset D_field,
        N_closed⁻¹ * Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ₀) *
          worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ₀) =
      Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ₀) *
        ∑ ν ∈ syndromeClosedPauliFinset D_field,
          ∑' K : WorldlineUrsellCluster L q_code,
            N_closed⁻¹ * worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ₀ K := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    unfold worldlineMayerPolymerPartition
    rw [tsum_mul_left]
    ring
  rw [h_factor]
  congr 1
  rw [← Summable.tsum_finsetSum (fun ν hν => (h_summable ν hν).mul_left N_closed⁻¹)]
  exact tsum_congr fun K =>
    character_average_worldlineMayerPolymerClusterWeight_eq_dysonMultiPolymerClusterWeight
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le V e_loc d_loc h_scalar K hσ₀

/-- Pointwise absolute-value bound on `worldlineMayerPolymerClusterWeight` (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
lemma abs_worldlineMayerPolymerClusterWeight_le
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (K : WorldlineUrsellCluster L q_code) :
    |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K| ≤
      ((Nat.factorial K.length : ℝ)⁻¹) *
        (K.map (fun γ =>
          if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|
          else 0)).prod := by
  have h_prod_nn : 0 ≤ (K.map (fun γ =>
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|
      else 0)).prod := by
    refine List.prod_nonneg ?_
    intro x hx
    rcases List.mem_map.mp hx with ⟨γ, _, rfl⟩
    split_ifs <;> positivity
  unfold worldlineMayerPolymerClusterWeight
  split_ifs with hK
  · rw [abs_mul, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h_abs_prod : ∀ l : List (WorldlineDysonPolymer L q_code),
        (∀ γ ∈ l, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) →
        |(l.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod| =
          (l.map (fun γ =>
            if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
              |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|
            else 0)).prod := by
      intro l hl
      induction l with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.map_cons, List.prod_cons, abs_mul]
        rw [if_pos (hl hd List.mem_cons_self),
          ih (fun γ hγ => hl γ (List.mem_cons_of_mem hd hγ))]
    exact le_of_eq (h_abs_prod K hK.1)
  · rw [abs_zero]
    exact mul_nonneg (by positivity) h_prod_nn

/-- For any finite set `ℱ` of polymer clusters and any nonnegative bound `B` on the finite sums
of `|worldlinePolymerWeight|` over valid polymers, the sum of `|worldlineMayerPolymerClusterWeight|`
over `ℱ` is bounded by `Real.exp B`, and hence `worldlineMayerPolymerClusterWeight` is `Summable`
(Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`). -/
lemma summable_worldlineMayerPolymerClusterWeight_of_bdd
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β B : ℝ} (hB_nn : 0 ≤ B)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_bdd : ∀ P₀ : Finset (WorldlineDysonPolymer L q_code),
      (∑ γ ∈ P₀.filter (IsValidWorldlinePolymer D_field sys C_RCA R_cut),
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|) ≤ B) :
    Summable (fun K : WorldlineUrsellCluster L q_code =>
      |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|) ∧
    Summable (worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ) := by
  have h_sum_abs : Summable (fun K : WorldlineUrsellCluster L q_code =>
      |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|) := by
    refine summable_of_sum_le (c := Real.exp B) (fun _ => abs_nonneg _) fun ℱ => ?_
    let P₀ : Finset (WorldlineDysonPolymer L q_code) :=
      (ℱ.biUnion List.toFinset).filter (IsValidWorldlinePolymer D_field sys C_RCA R_cut)
    let w_abs (γ : WorldlineDysonPolymer L q_code) : ℝ :=
      if IsValidWorldlinePolymer D_field sys C_RCA R_cut γ then
        |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|
      else 0
    have hw_nn : ∀ γ, 0 ≤ w_abs γ := fun γ => by dsimp [w_abs]; split_ifs <;> positivity
    have hP₀_sum_le : (∑ γ ∈ P₀, w_abs γ) ≤ B := by
      have h_eq : (∑ γ ∈ P₀, w_abs γ) =
          ∑ γ ∈ (ℱ.biUnion List.toFinset).filter (IsValidWorldlinePolymer D_field sys C_RCA R_cut),
            |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| := by
        refine Finset.sum_congr rfl fun γ hγ => ?_
        dsimp [w_abs]
        rw [if_pos (Finset.mem_filter.mp hγ).2]
      rw [h_eq]
      exact h_bdd (ℱ.biUnion List.toFinset)
    let K_max : ℕ := ℱ.sup List.length
    have h_len_mem : ∀ K ∈ ℱ, K.length ∈ Finset.range (K_max + 1) := fun K hK =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hK))
    have h_k_le : ∀ k ∈ Finset.range (K_max + 1),
        (∑ K ∈ ℱ.filter (fun K => K.length = k),
          |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|) ≤
        (B ^ k) / (k.factorial : ℝ) := by
      intro k _
      let ℱ_k := (ℱ.filter (fun K => K.length = k)).filter
        (fun K => ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
      have h_filt_eq :
          (∑ K ∈ ℱ.filter (fun K => K.length = k),
            |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|) =
          ∑ K ∈ ℱ_k,
            |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K| := by
        rw [← Finset.sum_filter_add_sum_filter_not (ℱ.filter (fun K => K.length = k))
          (fun K => ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)]
        have h_zero : (∑ K ∈ (ℱ.filter (fun K => K.length = k)).filter
            (fun K => ¬∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ),
            |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|) = 0 := by
          refine Finset.sum_eq_zero fun K hK => ?_
          have h_not := (Finset.mem_filter.mp hK).2
          unfold worldlineMayerPolymerClusterWeight
          rw [if_neg (fun h => h_not h.1), abs_zero]
        rw [h_zero, add_zero]
      rw [h_filt_eq]
      let tupleOf (K : WorldlineUrsellCluster L q_code) (j : Fin k) : WorldlineDysonPolymer L q_code :=
        if h : j.val < K.length then K.get ⟨j.val, h⟩ else ([], ∅)
      let T_k := Fintype.piFinset (fun _ : Fin k => P₀)
      have h_maps : ∀ K ∈ ℱ_k, tupleOf K ∈ T_k := by
        intro K hK
        rcases Finset.mem_filter.mp hK with ⟨hK_len, hK_val⟩
        rcases Finset.mem_filter.mp hK_len with ⟨hK_ℱ, h_len⟩
        refine Fintype.mem_piFinset.mpr fun j => ?_
        have hj : j.val < K.length := h_len ▸ j.isLt
        dsimp [tupleOf]
        rw [dif_pos hj]
        exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr
          ⟨K, hK_ℱ, List.mem_toFinset.mpr (List.get_mem K ⟨j.val, hj⟩)⟩,
          hK_val _ (List.get_mem K ⟨j.val, hj⟩)⟩
      have h_inj : Set.InjOn tupleOf (↑ℱ_k : Set (WorldlineUrsellCluster L q_code)) := by
        intro K₁ hK₁ K₂ hK₂ h_eq
        have h_len₁ : K₁.length = k := (Finset.mem_filter.mp (Finset.mem_filter.mp hK₁).1).2
        have h_len₂ : K₂.length = k := (Finset.mem_filter.mp (Finset.mem_filter.mp hK₂).1).2
        rw [← ofFn_get_eq_self K₁ ([], ∅) k h_len₁, ← ofFn_get_eq_self K₂ ([], ∅) k h_len₂]
        exact congrArg List.ofFn h_eq
      have h_prod_eq : ∀ K ∈ ℱ_k, (K.map w_abs).prod = ∏ j : Fin k, w_abs (tupleOf K j) := by
        intro K hK
        have h_len : K.length = k := (Finset.mem_filter.mp (Finset.mem_filter.mp hK).1).2
        have h_ofFn := ofFn_get_eq_self K ([], ∅) k h_len
        conv_lhs => rw [← h_ofFn, List.map_ofFn, List.prod_ofFn]
        rfl
      calc (∑ K ∈ ℱ_k, |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|)
        _ ≤ ∑ K ∈ ℱ_k, ((k.factorial : ℝ)⁻¹ * (∏ j : Fin k, w_abs (tupleOf K j))) := by
            refine Finset.sum_le_sum fun K hK => ?_
            have h_len : K.length = k := (Finset.mem_filter.mp (Finset.mem_filter.mp hK).1).2
            have h_le := abs_worldlineMayerPolymerClusterWeight_le
              (R_cut := R_cut) (C_RCA := C_RCA) (β := β) D_field sys V d_loc ν σ K
            rwa [h_len, h_prod_eq K hK] at h_le
        _ = (k.factorial : ℝ)⁻¹ * ∑ K ∈ ℱ_k, ∏ j : Fin k, w_abs (tupleOf K j) := by
            rw [← Finset.mul_sum]
        _ ≤ (k.factorial : ℝ)⁻¹ * ∑ f ∈ T_k, ∏ j : Fin k, w_abs (f j) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [← Finset.sum_image
              (f := fun f : Fin k → WorldlineDysonPolymer L q_code => ∏ j : Fin k, w_abs (f j)) h_inj]
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr h_maps) ?_
            intro f _ _
            exact Finset.prod_nonneg fun j _ => hw_nn (f j)
        _ = (k.factorial : ℝ)⁻¹ * ((∑ γ ∈ P₀, w_abs γ) ^ k) := by
            dsimp [T_k]
            rw [← Finset.prod_univ_sum]
            simp
        _ ≤ (B ^ k) / (k.factorial : ℝ) := by
            rw [div_eq_inv_mul]
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ hP₀_sum_le k) (by positivity)
            exact Finset.sum_nonneg fun γ _ => hw_nn γ
    calc (∑ K ∈ ℱ, |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|)
      _ = ∑ k ∈ Finset.range (K_max + 1),
            ∑ K ∈ ℱ.filter (fun K => K.length = k),
              |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K| := by
          rw [Finset.sum_fiberwise_of_maps_to h_len_mem]
      _ ≤ ∑ k ∈ Finset.range (K_max + 1), (B ^ k) / (k.factorial : ℝ) :=
          Finset.sum_le_sum h_k_le
      _ ≤ Real.exp B := Real.sum_le_exp_of_nonneg hB_nn (K_max + 1)
  exact ⟨h_sum_abs, h_sum_abs.of_norm⟩

/-- Single-scale spanning-threshold bound (Part II, Section 3.5 (`subsec:worldline-expansion`), Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:J-span-full-def`). -/
lemma single_scale_worldlineSpanningThreshold_bound_partition
    {R_cut : ℕ} {Δ_RCA C_wl c_wl β J : ℝ} {f : ℕ → ℝ}
    (hf_nn : ∀ r, 0 ≤ f r) (hc_wl : 0 ≤ c_wl) (hβ : 0 ≤ β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {r : ℕ} (hr : r ∈ Finset.Icc 1 R_cut) :
    64 * Real.exp 1 * C_wl * ((r : ℝ) ^ 6) * (β * J * f r) *
      Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3)) ≤ 1 := by
  let term : ℕ → ℝ := fun s =>
    C_wl * ((s : ℝ) ^ 6) * f s * Real.exp (c_wl * (1 + β) * ((s : ℝ) ^ 3))
  have hC : 0 ≤ C_wl := by
    by_contra h_neg; push_neg at h_neg
    have h_sum_le : worldlineNativeKPSum f C_wl c_wl β R_cut ≤ 0 := by
      unfold worldlineNativeKPSum
      refine Finset.sum_nonpos fun s' _ => ?_
      have hs' := hf_nn s'
      have h1 : 0 ≤ ((s' : ℝ) ^ 6) * f s' * Real.exp (c_wl * (1 + β) * ((s' : ℝ) ^ 3)) := by positivity
      nlinarith
    linarith
  have h_term_nn : ∀ s, 0 ≤ term s := fun s => by dsimp [term]; have := hf_nn s; positivity
  have h_term_le_sum : term r ≤ worldlineNativeKPSum f C_wl c_wl β R_cut := by
    unfold worldlineNativeKPSum
    exact Finset.single_le_sum (f := term) (fun s _ => h_term_nn s) hr
  let D := 64 * Real.exp 1 * max 1 β * worldlineNativeKPSum f C_wl c_wl β R_cut
  have h_max_pos : 0 < max 1 β := lt_of_lt_of_le zero_lt_one (le_max_left 1 β)
  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hJ_le_inv : J ≤ 1 / D := le_trans h_thresh (min_le_right _ _)
  have h_num_le_D : 64 * Real.exp 1 * β * term r ≤ D := by
    dsimp [D]
    have h1 : 64 * Real.exp 1 * β ≤ 64 * Real.exp 1 * max 1 β :=
      mul_le_mul_of_nonneg_left (le_max_right 1 β) (by positivity)
    exact mul_le_mul h1 h_term_le_sum (h_term_nn r) (by positivity)
  calc 64 * Real.exp 1 * C_wl * ((r : ℝ) ^ 6) * (β * J * f r) *
        Real.exp (c_wl * (1 + β) * ((r : ℝ) ^ 3))
    _ = J * (64 * Real.exp 1 * β * term r) := by dsimp [term]; ring
    _ ≤ J * D := mul_le_mul_of_nonneg_left h_num_le_D hJ
    _ ≤ (1 / D) * D := mul_le_mul_of_nonneg_right hJ_le_inv (le_of_lt hD_pos)
    _ = 1 := one_div_mul_cancel (ne_of_gt hD_pos)

/-- Summability of `worldlineMayerPolymerClusterWeight` under the worldline spanning threshold
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`)). -/
lemma summable_worldlineMayerPolymerClusterWeight
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ} {f : ℕ → ℝ}
    (hR_cut : 1 ≤ R_cut)
    (hf_nn : ∀ r, 0 ≤ f r)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    Summable (fun K : WorldlineUrsellCluster L q_code =>
      |worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K|) ∧
    Summable (worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ) := by
  have hβ_nn : 0 ≤ β := by linarith
  have hc_wl_nn : 0 ≤ c_wl := le_trans (Nat.cast_nonneg _) hc_wl_cal
  let B : ℝ := ∑ M ∈ (worldlineScaleCubeFinset L R_cut).powerset,
    (4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p
  have h_bounds : ∀ {p : ℕ × Finset (Box3D L)}, p ∈ worldlineScaleCubeFinset L R_cut →
      0 ≤ kpMonomerWeight c_wl β J f p ∧
      kpMonomerWeight c_wl β J f p ≤ 1 ∧
      4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1) ≤ kpMonomerWeight c_wl β J f p := by
    intro p hp
    rcases mem_kpScaleCubeFinset_iff.mp hp with ⟨hp_r, _⟩
    have hr_Icc : p.1 ∈ Finset.Icc 1 R_cut :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hp_r).1,
        le_trans (Finset.mem_Icc.mp hp_r).2 (Nat.min_le_left R_cut L)⟩
    have h_ss := single_scale_worldlineSpanningThreshold_bound_partition
      hf_nn hc_wl_nn hβ_nn hJ h_sum_pos h_thresh hr_Icc
    rcases kpMonomerWeight_bounds hR_cut hf_nn hC_wl_cal hc_wl_cal hβ hJ hp h_ss with ⟨h1, _, h3, h4⟩
    exact ⟨h1, h3, h4⟩
  have hB_nn : 0 ≤ B := by
    dsimp [B]
    refine Finset.sum_nonneg fun M hM => mul_nonneg (by positivity) ?_
    exact Finset.prod_nonneg fun p hp => (h_bounds (Finset.mem_powerset.mp hM hp)).1
  refine summable_worldlineMayerPolymerClusterWeight_of_bdd hB_nn D_field sys V d_loc ν σ fun P₀ => ?_
  have h_maps_M : ∀ γ ∈ P₀.filter (IsValidWorldlinePolymer D_field sys C_RCA R_cut),
      worldlinePolymerMonomers γ ∈ (worldlineScaleCubeFinset L R_cut).powerset :=
    fun γ hγ => Finset.mem_powerset.mpr (Finset.mem_filter.mp hγ).2.1
  rw [← Finset.sum_fiberwise_of_maps_to h_maps_M]
  refine Finset.sum_le_sum fun M hM => ?_
  have hM_sub : M ⊆ worldlineScaleCubeFinset L R_cut := Finset.mem_powerset.mp hM
  let w_J (p : ℕ × Finset (Box3D L)) : ℝ :=
    2 * β * J * f p.1 * Real.exp ((1 / 27 : ℝ) * c_wl * β * ((p.1 : ℝ) ^ 3))
  let w_D (p : ℕ × Finset (Box3D L)) : ℝ :=
    4 * β * J * f p.1 * Real.exp (4 * β * J * f p.1)
  let ℱ_M := (P₀.filter (IsValidWorldlinePolymer D_field sys C_RCA R_cut)).filter
    (fun γ => worldlinePolymerMonomers γ = M)
  let F_raw (γ : WorldlineDysonPolymer L q_code) : ℝ :=
    ((γ.1.length.factorial : ℝ)⁻¹) * (γ.1.map (fun ξ => w_J ξ.1)).prod * ∏ ϑ ∈ γ.2, w_D ϑ
  have h_pt : ∀ γ ∈ ℱ_M, |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ| ≤ F_raw γ := by
    intro γ hγ
    exact worldlinePolymerWeight_abs_le_prod hR_cut hβ_nn hJ hf_nn D_field sys
      h_sys_checks h_geom hc_wl_cal V hV_norm d_loc hd_scale ν γ
      (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2 σ
  let K_max : ℕ := ℱ_M.sup (fun γ => γ.1.length)
  have h_len_mem : ∀ γ ∈ ℱ_M, γ.1.length ∈ Finset.range (K_max + 1) := fun γ hγ =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Finset.le_sup (f := fun γ : WorldlineDysonPolymer L q_code => γ.1.length) hγ))
  have h_m_bound : ∀ m ∈ Finset.range (K_max + 1),
      (∑ γ ∈ ℱ_M.filter (fun γ => γ.1.length = m), F_raw γ) ≤
        (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
          ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
    intro m _
    let ℱ_m := ℱ_M.filter (fun γ => γ.1.length = m)
    let monomerTuple (γ : WorldlineDysonPolymer L q_code) (j : Fin m) : WorldlineJumpMonomer L q_code :=
      if h : j.val < γ.1.length then γ.1.get ⟨j.val, h⟩ else ((0, ∅), (0, 0))
    let cubeTuple (γ : WorldlineDysonPolymer L q_code) (j : Fin m) : ℕ × Finset (Box3D L) :=
      (monomerTuple γ j).1
    let P_M := (Fintype.piFinset (fun _ : Fin m => M)) ×ˢ M.powerset
    have h_maps : ∀ γ ∈ ℱ_m, (cubeTuple γ, γ.2) ∈ P_M := by
      intro γ hγ
      rcases Finset.mem_filter.mp hγ with ⟨hγ_M_mem, h_len⟩
      rcases Finset.mem_filter.mp hγ_M_mem with ⟨_, h_mon⟩
      refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, Finset.mem_powerset.mpr ?_⟩
      · have hj : j.val < γ.1.length := h_len ▸ j.isLt
        dsimp [cubeTuple, monomerTuple]; rw [dif_pos hj, ← h_mon]
        exact Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem (List.get_mem _ _)))
      · rw [← h_mon]; exact Finset.subset_union_right
    have h_P_bound : ∀ P ∈ P_M,
        (∑ γ ∈ ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P), F_raw γ) ≤
          ((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
      intro P hP
      let ℱ_P := ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P)
      change (∑ γ ∈ ℱ_P, F_raw γ) ≤ _
      by_cases h_emp : ℱ_P = ∅
      · rw [h_emp, Finset.sum_empty]
        exact mul_nonneg (by positivity) (Finset.prod_nonneg fun p hp => (h_bounds (hM_sub hp)).1)
      · rcases Finset.nonempty_iff_ne_empty.mpr h_emp with ⟨γ₀, hγ₀⟩
        have h_ofFn_mon : ∀ γ ∈ ℱ_P, List.ofFn (monomerTuple γ) = γ.1 := fun γ hγ =>
          ofFn_get_eq_self γ.1 ((0, ∅), (0, 0)) m (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
        have h_ofFn_cube : ∀ γ ∈ ℱ_P, List.ofFn P.1 = γ.1.map Prod.fst := fun γ hγ => by
          rw [← congrArg Prod.fst (Finset.mem_filter.mp hγ).2, ← h_ofFn_mon γ hγ, List.map_ofFn]; rfl
        have h_union_eq : (List.ofFn P.1).toFinset ∪ P.2 = M := by
          rw [h_ofFn_cube γ₀ hγ₀, ← congrArg Prod.snd (Finset.mem_filter.mp hγ₀).2]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ₀).1).1).2
        have h_F_eq : ∀ γ ∈ ℱ_P,
            F_raw γ = ((m.factorial : ℝ)⁻¹) * (∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ := fun γ hγ => by
          have h_len : γ.1.length = m := (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
          have h_eq_P2 : γ.2 = P.2 := congrArg Prod.snd (Finset.mem_filter.mp hγ).2
          have h_map_eq : γ.1.map (fun ξ => w_J ξ.1) = List.ofFn (fun j : Fin m => w_J (P.1 j)) := by
            calc γ.1.map (fun ξ => w_J ξ.1)
              _ = (γ.1.map Prod.fst).map w_J := by rw [List.map_map]; rfl
              _ = (List.ofFn P.1).map w_J := by rw [← h_ofFn_cube γ hγ]
              _ = List.ofFn (fun j : Fin m => w_J (P.1 j)) := by rw [List.map_ofFn]; rfl
          dsimp [F_raw]; rw [h_len, h_eq_P2, h_map_eq, List.prod_ofFn]
        have h_card_P : ℱ_P.card ≤
            ∏ j : Fin m, (validJumpMonomersAtCube D_field sys (P.1 j)).card := by
          rw [← Fintype.card_piFinset]
          refine Finset.card_le_card_of_injOn monomerTuple (fun γ hγ => ?_) (fun γ₁ hγ₁ γ₂ hγ₂ h_eq => ?_)
          · refine Fintype.mem_piFinset.mpr fun j => ?_
            have h_len : γ.1.length = m := (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).2
            have h_val : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ :=
              (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hγ).1).1).1).2
            have h_eq_P1 : cubeTuple γ j = P.1 j :=
              congrFun (congrArg Prod.fst (Finset.mem_filter.mp hγ).2) j
            have hj : j.val < γ.1.length := h_len ▸ j.isLt
            have h_mon_eq : monomerTuple γ j = γ.1.get ⟨j.val, hj⟩ := dif_pos hj
            rw [← h_eq_P1]
            change monomerTuple γ j ∈ validJumpMonomersAtCube D_field sys (monomerTuple γ j).1
            rw [h_mon_eq]
            exact mem_validJumpMonomersAtCube_of_valid D_field sys
              (fun idx => (h_sys_checks idx).2.1) h_val (List.get_mem _ _)
          · have h1 : γ₁.1 = γ₂.1 := by rw [← h_ofFn_mon γ₁ hγ₁, ← h_ofFn_mon γ₂ hγ₂, h_eq]
            have h2 : γ₁.2 = γ₂.2 := by
              rw [congrArg Prod.snd (Finset.mem_filter.mp hγ₁).2,
                congrArg Prod.snd (Finset.mem_filter.mp hγ₂).2]
            exact Prod.ext h1 h2
        have h_J_prod : ((ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)) ≤
            ∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p := by
          have h_wJ_nn : 0 ≤ ∏ j : Fin m, w_J (P.1 j) :=
            Finset.prod_nonneg fun j _ => by dsimp [w_J]; have := hf_nn (P.1 j).1; positivity
          have h_P1_mem : ∀ j : Fin m, P.1 j ∈ M :=
            Fintype.mem_piFinset.mp (Finset.mem_product.mp hP).1
          calc (ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)
            _ ≤ ((∏ j : Fin m, (validJumpMonomersAtCube D_field sys (P.1 j)).card : ℕ) : ℝ) *
                  ∏ j : Fin m, w_J (P.1 j) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast h_card_P) h_wJ_nn
            _ = ∏ j : Fin m, (((validJumpMonomersAtCube D_field sys (P.1 j)).card : ℝ) * w_J (P.1 j)) := by
                push_cast; rw [← Finset.prod_mul_distrib]
            _ ≤ ∏ j : Fin m, kpMonomerWeight c_wl β J f (P.1 j) := by
                refine Finset.prod_le_prod₀ (fun j _ => by
                  have := hf_nn (P.1 j).1; dsimp [w_J]; positivity) (fun j _ => ?_)
                exact validJumpMonomersAtCube_card_mul_le_kpMonomerWeight hR_cut hβ_nn hJ hf_nn
                  D_field sys h_geom hc_wl_cal (hM_sub (h_P1_mem j))
            _ = ((List.ofFn P.1).map (kpMonomerWeight c_wl β J f)).prod := by
                rw [List.map_ofFn, List.prod_ofFn]; rfl
            _ ≤ ∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p := by
                refine list_prod_le_finset_prod_of_le_one (List.ofFn P.1) (kpMonomerWeight c_wl β J f)
                  (fun p hp => ?_) (fun p hp => ?_)
                · rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩
                  exact (h_bounds (hM_sub (h_P1_mem j))).1
                · rcases List.mem_ofFn.mp hp with ⟨j, rfl⟩
                  exact (h_bounds (hM_sub (h_P1_mem j))).2.1
        have h_D_prod : (∏ ϑ ∈ P.2, w_D ϑ) ≤ ∏ p ∈ P.2, kpMonomerWeight c_wl β J f p := by
          have hP2_sub : P.2 ⊆ M := Finset.mem_powerset.mp (Finset.mem_product.mp hP).2
          refine Finset.prod_le_prod₀ (fun ϑ _ => by dsimp [w_D]; have := hf_nn ϑ.1; positivity)
            (fun ϑ hϑ => (h_bounds (hM_sub (hP2_sub hϑ))).2.2)
        have h_union_prod :
            (∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p) *
              (∏ p ∈ P.2, kpMonomerWeight c_wl β J f p) ≤
              ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
          rw [← h_union_eq]
          refine finset_prod_mul_prod_le_prod_union_of_le_one _ _ _ (fun p hp => ?_) (fun p hp => ?_)
          · rw [h_union_eq] at hp; exact (h_bounds (hM_sub hp)).1
          · rw [h_union_eq] at hp; exact (h_bounds (hM_sub hp)).2.1
        calc (∑ γ ∈ ℱ_P, F_raw γ)
          _ = ∑ _γ ∈ ℱ_P, (((m.factorial : ℝ)⁻¹) * (∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ) :=
              Finset.sum_congr rfl h_F_eq
          _ = ((m.factorial : ℝ)⁻¹) * (((ℱ_P.card : ℝ) * ∏ j : Fin m, w_J (P.1 j)) * ∏ ϑ ∈ P.2, w_D ϑ) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ ((m.factorial : ℝ)⁻¹) *
                ((∏ p ∈ (List.ofFn P.1).toFinset, kpMonomerWeight c_wl β J f p) *
                  ∏ p ∈ P.2, kpMonomerWeight c_wl β J f p) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul h_J_prod h_D_prod
                (Finset.prod_nonneg fun ϑ _ => by dsimp [w_D]; have := hf_nn ϑ.1; positivity)
                (Finset.prod_nonneg fun p hp => ?_)) (by positivity)
              exact (h_bounds (hM_sub (h_union_eq ▸ Finset.mem_union_left _ hp))).1
          _ ≤ ((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
              mul_le_mul_of_nonneg_left h_union_prod (by positivity)
    have h_card_PM : (P_M.card : ℝ) = ((M.card : ℝ) ^ m) * ((2 : ℝ) ^ M.card) := by
      dsimp [P_M]
      rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.card_powerset]
      push_cast; rfl
    calc (∑ γ ∈ ℱ_m, F_raw γ)
      _ = ∑ P ∈ P_M, ∑ γ ∈ ℱ_m.filter (fun γ => (cubeTuple γ, γ.2) = P), F_raw γ := by
          rw [← Finset.sum_fiberwise_of_maps_to h_maps]
      _ ≤ ∑ _P ∈ P_M, (((m.factorial : ℝ)⁻¹) * ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
          Finset.sum_le_sum h_P_bound
      _ = (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
            ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
          rw [Finset.sum_const, nsmul_eq_mul, h_card_PM, div_eq_mul_inv]; ring
  have h_sum_m :
      (∑ m ∈ Finset.range (K_max + 1), (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card))) ≤
        (4 * Real.exp 1) ^ M.card := by
    rw [← Finset.sum_mul]
    calc (∑ m ∈ Finset.range (K_max + 1), (M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)
      _ ≤ Real.exp (M.card : ℝ) * ((2 : ℝ) ^ M.card) :=
          mul_le_mul_of_nonneg_right (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg M.card) (K_max + 1))
            (by positivity)
      _ = (2 * Real.exp 1) ^ M.card := by rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm]
      _ ≤ (4 * Real.exp 1) ^ M.card := by
          refine pow_le_pow_left₀ (by positivity) ?_ _
          have := Real.exp_pos 1; linarith
  have h_prod_M_nn : 0 ≤ ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
    Finset.prod_nonneg fun p hp => (h_bounds (hM_sub hp)).1
  calc (∑ γ ∈ ℱ_M, |worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ|)
    _ ≤ ∑ γ ∈ ℱ_M, F_raw γ := Finset.sum_le_sum h_pt
    _ = ∑ m ∈ Finset.range (K_max + 1), ∑ γ ∈ ℱ_M.filter (fun γ => γ.1.length = m), F_raw γ := by
        rw [← Finset.sum_fiberwise_of_maps_to h_len_mem]
    _ ≤ ∑ m ∈ Finset.range (K_max + 1),
          ((((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card)) *
            ∏ p ∈ M, kpMonomerWeight c_wl β J f p) :=
        Finset.sum_le_sum h_m_bound
    _ = (∑ m ∈ Finset.range (K_max + 1),
          (((M.card : ℝ) ^ m / (m.factorial : ℝ)) * ((2 : ℝ) ^ M.card))) *
          ∏ p ∈ M, kpMonomerWeight c_wl β J f p := by
        rw [← Finset.sum_mul]
    _ ≤ (4 * Real.exp 1) ^ M.card * ∏ p ∈ M, kpMonomerWeight c_wl β J f p :=
        mul_le_mul_of_nonneg_right h_sum_m h_prod_M_nn

/-- Duhamel–Dyson Connected Worldline Multi-Polymer Trace Expansion (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
expanding $\mathrm{e}^{-\beta(H_{\mathrm{diag}} + R_{\mathrm{off}})}$ in a Duhamel–Dyson series on
the syndrome sector $\Pi_\sigma$, expanding the interaction exponential $\mathrm{e}^{-\beta D_{\mathrm{int}}(\sigma)}
= \prod_\vartheta (1 + (\mathrm{e}^{-\beta d_{\mathrm{loc}}(\vartheta,\sigma)} - 1))$, and grouping
the active jump and diagonal monomers into connected components of the collar-overlap graph yields
the `tsum` over multi-polymer clusters `worldlineDysonMultiPolymerClusterWeight`. -/
lemma hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_tsum_dysonMultiPolymerClusterWeight
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ_pos : 0 < J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
    hilbertTrace (gibbsBoltzmannOp
      (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
      (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
        sys.syndromeProjector σ) =
      K_norm *
        (Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
          ∑' K : WorldlineUrsellCluster L q_code,
            worldlineDysonMultiPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc σ K) := by
  exact hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_tsum_dysonMultiPolymerClusterWeight_duhamel
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm e_loc d_loc
    hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA hC_wl_cal hc_wl_cal hβ hJ_pos
    h_sum_pos h_thresh hσ

/-- Per-sector Duhamel–Dyson Connected Worldline Polymer-Gas Partition Identity (Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
for every realizable syndrome $\sigma \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$, the
restricted Gibbs trace `hilbertTrace (gibbsBoltzmannOp ... β * sys.syndromeProjector σ)` equals
the character-averaged Mayer polymer-gas partition function in sector $\sigma$. -/
lemma hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_character_average_polymerPartition
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ_pos : 0 < J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
    let N_closed := ((syndromeClosedPauliFinset D_field).card : ℝ)
    hilbertTrace (gibbsBoltzmannOp
      (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
      (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
        sys.syndromeProjector σ) =
      K_norm *
        ∑ ν ∈ syndromeClosedPauliFinset D_field, N_closed⁻¹ *
          Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
            worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ := by
  have hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA := h_scale_cal.2.1
  have h_summ : ∀ ν ∈ syndromeClosedPauliFinset D_field,
      Summable (worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ) :=
    fun ν _ => (summable_worldlineMayerPolymerClusterWeight hR_cut hf_nn hC_wl_cal hc_wl_cal
      hβ (le_of_lt hJ_pos) h_sum_pos h_thresh D_field sys h_sys_checks h_geom V hV_norm d_loc
      hd_scale ν σ).2
  (try dsimp only)
  rw [character_average_worldlineMayerPolymerPartition_eq_tsum_dysonMultiPolymerClusterWeight
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le V e_loc d_loc h_scalar hσ h_summ]
  exact hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_tsum_dysonMultiPolymerClusterWeight
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm e_loc d_loc
    hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA h_rca_cal hC_wl_cal hc_wl_cal
    hΔ_RCA hβ hJ_pos h_sum_pos hJ_walsh hJ_wl h_thresh hσ

/-- **Duhamel–Dyson Connected Worldline Polymer-Gas Partition Identity**
(Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`), Equation `eq:ursell-partition-sigma`):
Expanding $\mathrm{e}^{-\beta(H_{\mathrm{diag}} + R_{\mathrm{off}})}$ in a Duhamel–Dyson series,
evaluating the trace in the joint syndrome-logical Fourier basis via the discrete character average
over $\bar P_\nu \in \mathcal{G}_{\mathrm{closed}}$, and grouping interaction monomers into minimal
connected components of the collar-overlap graph yields the exact polymer-gas partition function
`worldlineMayerPolymerPartition` in each sector $(\sigma, \nu)$. -/
theorem worldline_dyson_mayer_polymer_gas_partition_identity
    {L q_code r_0 m_max w_0 L_star R_cut : ℕ} [NeZero L]
    {C_RCA β Δ_RCA C_wl c_wl J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) (f : ℕ → ℝ)
    (hf_nn : ∀ r, 0 ≤ f r) (hf_le_one : ∀ r, f r ≤ 1)
    (hV_norm : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, ‖V.term r A‖ ≤ J * f r)
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (hd_scale : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      ∀ σ, |d_loc r A σ| ≤ 2 * (J * f r))
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (hH_trunc : IsSelfAdjoint (sys.H0 + scaleSplitTruncatedOp V R_cut))
    (hR_cut : 1 ≤ R_cut) (hR_le : R_cut ≤ L_star)
    (h_scale_cal : SatisfiesWorldlineScaleCalibration L L_star R_cut r_0 C_RCA) (hC_RCA : 0 ≤ C_RCA)
    (h_rca_cal : rcaDiagonalCoercivityConstant 3 R_cut r_0 w_0 C_RCA ≤ Δ_RCA)
    (hC_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ C_wl)
    (hc_wl_cal : (kpCollarMaxCheckCard R_cut r_0 w_0 C_RCA : ℝ) ≤ c_wl)
    (hΔ_RCA : 0 < Δ_RCA) (hβ : 16 < β) (hJ : 0 ≤ J)
    (h_sum_pos : 0 < worldlineNativeKPSum f C_wl c_wl β R_cut)
    (hJ_walsh : J ≤ collarWalshCouplingThreshold R_cut r_0 w_0 C_RCA)
    (hJ_wl : J ≤ worldlineCouplingThreshold (1 / 4) Δ_RCA)
    (h_thresh : J ≤ worldlineSpanningThreshold Δ_RCA C_wl c_wl β f R_cut) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
    let N_closed := ((syndromeClosedPauliFinset D_field).card : ℝ)
    0 < K_norm ∧
    (∀ W : Finset (IdxCSS[L, q_code, m_max]),
      hilbertTrace (gibbsBoltzmannOp
        (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
        (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
          positiveCheckWitnessProj sys W) =
        K_norm * ∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
          ∑ ν ∈ syndromeClosedPauliFinset D_field, N_closed⁻¹ *
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
              worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ) ∧
    (gibbsPartitionZ (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β =
      K_norm * ∑ σ ∈ realizableSyndromes D_field,
        ∑ ν ∈ syndromeClosedPauliFinset D_field, N_closed⁻¹ *
          Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
            worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ) := by
  let E_vac := ∑ r ∈ Finset.Icc 1 (min R_cut L), ∑ A ∈ boxCubes 3 L r, e_loc r A
  let K_norm := hilbertTrace sys.P0 * Real.exp (-β * E_vac)
  let N_closed := ((syndromeClosedPauliFinset D_field).card : ℝ)
  have hK_pos : 0 < K_norm :=
    vacuumPartitionNorm_pos_of_validDescriptorField D_field h_valid sys h_sys_checks β E_vac
  have h_witness : ∀ W : Finset (IdxCSS[L, q_code, m_max]),
      hilbertTrace (gibbsBoltzmannOp
        (opEigenbasis (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc)
        (opEigenvalues (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc) β *
          positiveCheckWitnessProj sys W) =
        K_norm * ∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
          ∑ ν ∈ syndromeClosedPauliFinset D_field, N_closed⁻¹ *
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
              worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ := by
    intro W
    rcases eq_or_lt_of_le hJ with rfl | hJ_pos
    · have hV_zero : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r, V.term r A = 0 := by
        intro r hr A hA
        have h_le := hV_norm r hr A hA
        rw [zero_mul] at h_le
        exact norm_le_zero_iff.mp h_le
      have h_trunc_zero : scaleSplitTruncatedOp V R_cut = 0 := by
        unfold scaleSplitTruncatedOp
        exact Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun A hA => hV_zero r hr A hA
      have h_diag_zero : pauliDiagonalPart sys V R_cut = 0 := by
        unfold pauliDiagonalPart
        refine Finset.sum_eq_zero fun r hr => Finset.sum_eq_zero fun A hA => ?_
        rw [hV_zero r hr A hA]
        unfold syndromePinchOp
        simp
      have h_trunc_eq : scaleSplitTruncatedOp V R_cut = pauliDiagonalPart sys V R_cut := by
        rw [h_trunc_zero, h_diag_zero]
      rw [hilbertTrace_gibbsBoltzmannOp_pauliDiagonal_witness_eq
        D_field h_valid sys h_sys_checks V e_loc d_loc h_scalar hH_trunc h_trunc_eq W]
      dsimp [K_norm, N_closed]
      congr 1
      refine Finset.sum_congr rfl fun σ _ => ?_
      have h_part_one : ∀ ν ∈ syndromeClosedPauliFinset D_field,
          worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ = 1 := by
        intro ν _
        exact (worldlineMayerPolymerPartition_and_ursell_exp_of_zero_weights
          D_field sys C_RCA β V d_loc ν σ
          (fun γ hγ => worldlinePolymerWeight_eq_zero_of_valid_and_J_zero
            D_field sys C_RCA β V f hV_norm d_loc ν γ hγ σ)).1
      have h_sum_nu :
          (∑ ν ∈ syndromeClosedPauliFinset D_field,
            (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
              Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
              worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ) =
            Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) := by
        have h_congr :
            (∑ ν ∈ syndromeClosedPauliFinset D_field,
              (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
                 Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) *
                 worldlineMayerPolymerPartition D_field sys C_RCA R_cut β V d_loc ν σ) =
            ∑ _ν ∈ syndromeClosedPauliFinset D_field,
              (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
                Real.exp (-β * pauliDiagonalSectorEnergy sys R_cut d_loc σ) := by
          refine Finset.sum_congr rfl fun ν hν => ?_
          rw [h_part_one ν hν, mul_one]
        rw [h_congr]
        exact (zero_mem_syndromeClosedPauliFinset_and_sum_inv D_field _).2.2
      exact h_sum_nu.symm
    · rw [hilbertTrace_gibbsBoltzmannOp_witness_eq_sum_realizableSyndromes
        D_field h_valid sys h_sys_checks (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc W,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      exact hilbertTrace_gibbsBoltzmannOp_syndromeProjector_eq_character_average_polymerPartition
        D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 V f hf_nn hf_le_one hV_norm
        e_loc d_loc hd_scale h_scalar hH_trunc hR_cut hR_le h_scale_cal hC_RCA
        h_rca_cal hC_wl_cal hc_wl_cal hΔ_RCA hβ hJ_pos h_sum_pos hJ_walsh hJ_wl h_thresh
        (Finset.mem_filter.mp hσ).1
  have h_empty := gibbsPartitionZ_eq_hilbertTrace_empty_witness
    D_field sys (sys.H0 + scaleSplitTruncatedOp V R_cut) hH_trunc β
  refine ⟨hK_pos, h_witness, ?_⟩
  rw [h_empty.1, h_witness ∅, h_empty.2]

end DirectWorldlineCluster
end
