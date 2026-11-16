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

import Proofs.DirectWorldlineCluster.WorldlineDysonUrsellCluster

/-!
# Multi-Polymer Amplitude Factorization, Mayer Decoupling, and Logical Character Averaging

Proves that compatible worldline polymers with disjoint native RCA collars factorize across loop amplitudes, Mayer bond factors (`worldlineMayerBondFactor_decouple_of_disjoint_nativeCollar`), and trajectory syndrome energies (`syndromeEnergy_and_exp_multiPolymer_trajectory_add`). Shows that logical Pauli coset character averaging annihilates homologically nontrivial loops and factorizes over compatible polymer families (`multiPolymer_logical_character_average_clusterWeight_eq`).

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

/-!
## 1. Multi-Polymer Amplitude, Mayer Bond Decoupling, and Energy Additivity (Part II, Lemma 3.9 (`lem:worldline-factorization-time-reversal`))
-/

/-- Exact evaluation of `worldlinePolymerWeight` for any valid worldline polymer $\gamma$ on a realizable syndrome $\sigma \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$ in terms of the sector trace on $\sigma$ and the full-syndrome Dyson simplex integral (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlinePolymerWeight_eq_sector_trace_mul_simplex_integral
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
    (ν : PauliBitstringPair L q_code)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ =
      symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) *
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
          else 0 := by
  have hV_supp : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      IsSupportedOn (SiteCSS[L, q_code]) A (V.term r A) :=
    fun r hr A hA => V.is_supported r
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
        le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩) A hA
  have h_span := spanningSurfaceSign_mul_worldlinePolymerLoopAmplitude_eq_of_valid
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V hV_supp γ hγ hσ
  unfold worldlinePolymerWeight worldlinePolymerMicroWeight
  have h_int_eq :
      (∫ τ : Fin γ.1.length → ℝ,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys γ.1
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ) β τ) *
            ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc
              (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ) β ϑ τ
        else 0) =
      ∫ τ : Fin γ.1.length → ℝ,
        if InOrderedDysonSimplex β τ then
          Real.exp (-worldlineBareAction D_field sys γ.1 σ β τ) *
            ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ
        else 0 := by
    congr 1; funext τ
    split_ifs with h_simp
    · rcases (worldlineTrajectorySyndrome_eq_outside_and_congr_on_nativeCollar
        D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar hγ τ).2.2 σ with
        ⟨h_bare, h_mayer⟩
      rw [h_bare]
      congr 1
      exact Finset.prod_congr rfl fun ϑ hϑ => h_mayer ϑ hϑ
    · rfl
  rw [h_int_eq]
  calc symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) *
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
        ((-1 : ℝ) ^ γ.1.length *
          worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ) *
          ∫ τ : Fin γ.1.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys γ.1 σ β τ) *
                ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ
            else 0)
    _ = symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) *
          (-1 : ℝ) ^ γ.1.length *
          (spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
            worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
              (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ)) *
          ∫ τ : Fin γ.1.length → ℝ,
            if InOrderedDysonSimplex β τ then
              Real.exp (-worldlineBareAction D_field sys γ.1 σ β τ) *
                ∏ ϑ ∈ γ.2, worldlineMayerBondFactor D_field γ.1 d_loc σ β ϑ τ
            else 0 := by ring
    _ = _ := by rw [h_span]

/-- Every footprint $\gamma = (M, \alpha)$ whose spanning support `worldlineUrsellSpanningSupport sys C_RCA γ` is disjoint from `Finset.univ` has `worldlineUrsellPhi = 0`, because every valid Ursell cluster $K$ is non-empty and every valid polymer $\gamma_0 \in K$ has a non-empty native check collar (`worldlinePolymerNativeCollar_nonempty_of_valid`). -/
lemma worldlineUrsellPhi_eq_zero_of_disjoint_univ
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (γ : WorldlineUrsellFootprint L q_code m_max)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    (h_disj : Disjoint (worldlineUrsellSpanningSupport sys C_RCA γ) Finset.univ) :
    worldlineUrsellPhi D_field sys C_RCA R_cut β V d_loc ν γ σ = 0 := by
  unfold worldlineUrsellPhi
  have h_zero : ∀ K : WorldlineUrsellCluster L q_code,
      (if IsValidWorldlineUrsellCluster D_field sys C_RCA R_cut K ∧
          worldlineClusterMonomers K = γ.1 ∧
          worldlineClusterSpanningSurface D_field sys C_RCA K = γ.2 then
        worldlineClusterUrsellWeight D_field sys C_RCA β V d_loc ν K σ
      else 0) = 0 := by
    intro K
    split_ifs with hK
    · rcases hK with ⟨⟨hK_ne, hK_val, hK_conn⟩, h_mon, h_surf⟩
      rcases List.exists_mem_of_ne_nil K hK_ne with ⟨γ₀, hγ₀⟩
      rcases (worldlinePolymerNativeCollar_nonempty_of_valid
        D_field sys h_sys_supp h_geom hr0_le (hK_val γ₀ hγ₀)).1 with ⟨c, hc⟩
      unfold worldlinePolymerNativeCollar nativeCollarSupport at hc
      rcases Finset.mem_biUnion.mp hc with ⟨p, hp, hc_p⟩
      have hp_K : p ∈ worldlineClusterMonomers K := by
        clear hK_ne hK_val hK_conn hc_p h_mon h_surf
        induction K with
        | nil => cases hγ₀
        | cons hd tl ih =>
          rcases List.mem_cons.mp hγ₀ with rfl | h_tl
          · exact Finset.mem_union_left _ hp
          · exact Finset.mem_union_right _ (ih h_tl)
      rw [h_mon] at hp_K
      have hc_span : c ∈ worldlineUrsellSpanningSupport sys C_RCA γ :=
        Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, hp_K, hc_p⟩)
      exact False.elim (Finset.disjoint_left.mp h_disj hc_span (Finset.mem_univ c))
    · rfl
  simp [h_zero]

/-- Multi-polymer weight factorization along any list $K$ of valid worldline polymers on a realizable syndrome $\sigma \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$ (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma list_prod_worldlinePolymerWeight_eq_of_valid
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
    (ν : PauliBitstringPair L q_code)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod =
      (K.map (fun γ =>
        symplecticPauliSign ν (worldlinePolymerLogicalCoset D_field sys C_RCA γ) *
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
            else 0)).prod := by
  congr 1
  exact List.map_congr_left fun γ hγ =>
    worldlinePolymerWeight_eq_sector_trace_mul_simplex_integral
      D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le
      V e_loc d_loc h_scalar ν (hK_valid γ hγ) hσ

/-- Character multiplicativity and orthogonality of `symplecticPauliSign` over the closed Pauli group `syndromeClosedPauliFinset D_field` (Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)): 1. `symplecticPauliSign (ν₁ + ν₂) μ = symplecticPauliSign ν₁ μ * symplecticPauliSign ν₂ μ`. 2. `symplecticPauliSign ν (μ₁ + μ₂) = symplecticPauliSign ν μ₁ * symplecticPauliSign ν μ₂`. 3. `syndromeClosedPauliFinset D_field` is closed under `+`. 4. Averaging `symplecticPauliSign ν μ` over `ν ∈ syndromeClosedPauliFinset D_field` gives `1` if `∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν μ = 1`, and `0` otherwise. -/
lemma symplecticPauliSign_mul_and_orthogonality
    {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) :
    (∀ ν₁ ν₂ μ : PauliBitstringPair L q_code,
      symplecticPauliSign (ν₁ + ν₂) μ = symplecticPauliSign ν₁ μ * symplecticPauliSign ν₂ μ) ∧
    (∀ ν μ₁ μ₂ : PauliBitstringPair L q_code,
      symplecticPauliSign ν (μ₁ + μ₂) = symplecticPauliSign ν μ₁ * symplecticPauliSign ν μ₂) ∧
    (∀ ν₁ ∈ syndromeClosedPauliFinset D_field, ∀ ν₂ ∈ syndromeClosedPauliFinset D_field,
      ν₁ + ν₂ ∈ syndromeClosedPauliFinset D_field) ∧
    (∀ μ : PauliBitstringPair L q_code,
      (∑ ν ∈ syndromeClosedPauliFinset D_field,
        (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ * symplecticPauliSign ν μ) =
      if ∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν μ = 1 then 1 else 0) := by
  have h_mul_left : ∀ ν₁ ν₂ μ : PauliBitstringPair L q_code,
      symplecticPauliSign (ν₁ + ν₂) μ = symplecticPauliSign ν₁ μ * symplecticPauliSign ν₂ μ :=
    fun ν₁ ν₂ μ => (signScalar_symplectic_eq_symplecticPauliSign_and_mul ν₁ ν₁ ν₂ μ μ μ).2.2
  have h_mul_right : ∀ ν μ₁ μ₂ : PauliBitstringPair L q_code,
      symplecticPauliSign ν (μ₁ + μ₂) = symplecticPauliSign ν μ₁ * symplecticPauliSign ν μ₂ :=
    fun ν μ₁ μ₂ => (signScalar_symplectic_eq_symplecticPauliSign_and_mul ν ν ν μ₁ μ₁ μ₂).2.1
  have h_closed_add : ∀ ν₁ ∈ syndromeClosedPauliFinset D_field,
      ∀ ν₂ ∈ syndromeClosedPauliFinset D_field,
      ν₁ + ν₂ ∈ syndromeClosedPauliFinset D_field :=
    fun _ h₁ _ h₂ => (add_mem_syndromeClosedPauliFinset_and_involutive D_field h₁ h₂).1
  refine ⟨h_mul_left, h_mul_right, h_closed_add, fun μ => ?_⟩
  split_ifs with h_all
  · have h_congr :
        (∑ ν ∈ syndromeClosedPauliFinset D_field,
          (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ * symplecticPauliSign ν μ) =
        ∑ _ν ∈ syndromeClosedPauliFinset D_field,
          (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ * (1 : ℝ) :=
      Finset.sum_congr rfl fun ν hν => by rw [h_all ν hν]
    rw [h_congr]
    exact (zero_mem_syndromeClosedPauliFinset_and_sum_inv D_field 1).2.2
  · push_neg at h_all
    rcases h_all with ⟨ν₀, hν₀_mem, hν₀_ne⟩
    have hν₀_val : symplecticPauliSign ν₀ μ = -1 := by
      unfold symplecticPauliSign at hν₀_ne ⊢
      split_ifs at hν₀_ne ⊢ with h_mod
      · rfl
      · exact False.elim (hν₀_ne rfl)
    have h_zmod2_cancel : ∀ x y : ZMod 2, x + y + y = x := by decide
    have h_inv : ∀ ν : PauliBitstringPair L q_code, ν + ν₀ + ν₀ = ν := by
      intro ν
      refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
      · exact h_zmod2_cancel (ν.1 q) (ν₀.1 q)
      · exact h_zmod2_cancel (ν.2 q) (ν₀.2 q)
    have h_sum_neg :
        (∑ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν μ) =
          -(∑ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν μ) := by
      calc ∑ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν μ
        _ = ∑ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign (ν + ν₀) μ := by
            refine Finset.sum_bij (fun ν _ => ν + ν₀)
              (fun ν hν => h_closed_add ν hν ν₀ hν₀_mem)
              (fun ν₁ _ ν₂ _ h_eq => by
                (try dsimp only at h_eq)
                rw [← h_inv ν₁, ← h_inv ν₂, h_eq])
              (fun ν hν => ⟨ν + ν₀, h_closed_add ν hν ν₀ hν₀_mem, h_inv ν⟩)
              (fun ν _ => by (try dsimp only); rw [h_inv ν])
        _ = ∑ ν ∈ syndromeClosedPauliFinset D_field, (-symplecticPauliSign ν μ) := by
            refine Finset.sum_congr rfl fun ν _ => ?_
            rw [h_mul_left ν ν₀ μ, hν₀_val, mul_neg_one]
        _ = -(∑ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν μ) :=
            Finset.sum_neg_distrib _
    have h_sum_zero : (∑ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν μ) = 0 := by
      linarith
    rw [← Finset.mul_sum, h_sum_zero, mul_zero]

/-- Multi-polymer bare `H_0` energy additivity across any list of check-disjoint syndrome shifts (Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`), Equation `eq:energy-additivity-disjoint-loops`). -/
lemma syndromeEnergy_foldr_syndromeXor_disjoint_list_add
    {α : Type*} {L q_code m_max : ℕ} [NeZero L]
    (sys : SysCSS[L, q_code, m_max])
    (S_fn : α → Finset (IdxCSS[L, q_code, m_max]))
    (δ_fn : α → IdxCSS[L, q_code, m_max] → Bool)
    (l : List α)
    (hl_pw : l.Pairwise (fun x y => Disjoint (S_fn x) (S_fn y)))
    (hl_supp : ∀ x ∈ l, ∀ c, δ_fn x c = true → c ∈ S_fn x)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool) :
    sys.syndromeEnergy (l.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀) -
      sys.syndromeEnergy σ₀ =
    (l.map (fun x => sys.syndromeEnergy (syndromeXor (δ_fn x) σ₀) - sys.syndromeEnergy σ₀)).sum ∧
    ∀ c, c ∉ l.foldr (fun x acc => S_fn x ∪ acc) ∅ →
      (l.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀) c = σ₀ c := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    rcases List.pairwise_cons.mp hl_pw with ⟨h_hd_tl, h_tl_pw⟩
    rcases ih h_tl_pw (fun x hx => hl_supp x (List.mem_cons_of_mem hd hx)) with ⟨h_sum_tl, h_out_tl⟩
    let S_tl := tl.foldr (fun x acc => S_fn x ∪ acc) ∅
    have h_disj_tl : Disjoint (S_fn hd) S_tl := by
      have h_sub : ∀ x ∈ tl, Disjoint (S_fn hd) (S_fn x) := h_hd_tl
      clear ih h_sum_tl h_out_tl h_tl_pw hl_pw hl_supp h_hd_tl
      induction tl with
      | nil => exact Finset.disjoint_empty_right _
      | cons y ys ihy =>
        change Disjoint (S_fn hd) (S_fn y ∪ ys.foldr (fun x acc => S_fn x ∪ acc) ∅)
        exact Finset.disjoint_union_right.mpr
          ⟨h_sub y List.mem_cons_self, ihy (fun z hz => h_sub z (List.mem_cons_of_mem y hz))⟩
    let σ_tl := tl.foldr (fun x acc => syndromeXor (δ_fn x) acc) σ₀
    let δ_tl : IdxCSS[L, q_code, m_max] → Bool := fun c => bne (σ_tl c) (σ₀ c)
    have h_tl_xor : syndromeXor δ_tl σ₀ = σ_tl := by
      ext c
      change bne (bne (σ_tl c) (σ₀ c)) (σ₀ c) = σ_tl c
      cases σ_tl c <;> cases σ₀ c <;> rfl
    have h_δ_tl_supp : ∀ c, δ_tl c = true → c ∈ S_tl := by
      intro c hc
      by_contra hc_not
      have h_eq := h_out_tl c hc_not
      dsimp [δ_tl, σ_tl] at hc
      rw [h_eq, bne_self_eq_false] at hc
      exact Bool.false_ne_true hc
    have h_add := syndromeEnergy_syndromeXor_disjoint_sets_add sys σ₀ (δ_fn hd) δ_tl
      h_disj_tl (hl_supp hd List.mem_cons_self) h_δ_tl_supp
    rw [h_tl_xor] at h_add
    refine ⟨?_, fun c hc_not => ?_⟩
    · simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      change sys.syndromeEnergy (syndromeXor (δ_fn hd) σ_tl) - sys.syndromeEnergy σ₀ = _
      rw [h_add, h_sum_tl]
    · simp only [List.foldr_cons, Finset.mem_union, not_or] at hc_not ⊢
      have h_hd_false : δ_fn hd c = false := by
        cases h_val : δ_fn hd c
        · rfl
        · exact False.elim (hc_not.1 (hl_supp hd List.mem_cons_self c h_val))
      change bne (δ_fn hd c) (σ_tl c) = σ₀ c
      dsimp [σ_tl]
      rw [h_hd_false, h_out_tl c hc_not.2]
      cases σ₀ c <;> rfl

/-- Multi-polymer character average over $\nu \in \mathcal{G}_{\mathrm{closed}}$ of the product
of character-twisted polymer weights $\prod_{\gamma \in K} w_\nu(\gamma; \sigma)$
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)):
factors out $\prod_{\gamma \in K} (-1)^{\langle \nu, \mu(\gamma) \rangle} = (-1)^{\langle \nu, \sum_{\gamma \in K} \mu(\gamma) \rangle}$
and evaluates the character average via `symplecticPauliSign_mul_and_orthogonality`. -/
lemma multiPolymer_logical_character_average_eq
    {L q_code r_0 m_max : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (K : WorldlineUrsellCluster L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
    (∑ ν ∈ syndromeClosedPauliFinset D_field,
      (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
        (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod) =
    if ∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 1 then
      (K.map (fun γ =>
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
          worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ))).prod
    else 0 := by
  rcases symplecticPauliSign_mul_and_orthogonality D_field with ⟨_, h_mul_right, _, h_orth⟩
  have h_prod_factor : ∀ ν : PauliBitstringPair L q_code,
      (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod =
      symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum *
        (K.map (fun γ =>
          spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
            worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
              (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ))).prod := by
    intro ν
    induction K with
    | nil =>
      simp [symplecticPauliSign]
    | cons hd tl ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih, h_mul_right]
      unfold worldlinePolymerWeight
      ring
  have h_sum_congr :
      (∑ ν ∈ syndromeClosedPauliFinset D_field,
        (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
          (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod) =
      (∑ ν ∈ syndromeClosedPauliFinset D_field,
        (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
          symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum) *
      (K.map (fun γ =>
        spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
          worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ))).prod := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [h_prod_factor ν, mul_assoc]
  rw [h_sum_congr, h_orth]
  split_ifs <;> ring

/-- Finite set of all lists of canonical jump monomers in `worldlineAllJumpMonomerFinset D_field R_cut`
of exact length $m$. -/
def worldlineJumpListFinsetOfLength
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (R_cut m : ℕ) : Finset (List (WorldlineJumpMonomer L q_code)) :=
  (Finset.univ : Finset (Fin m → ↥(worldlineAllJumpMonomerFinset D_field R_cut))).image
    (fun g => List.ofFn (fun i => (g i).1))

/-- Finite set of all candidate worldline polymers $(\mathrm{jumps}, \Theta)$ at cutoff $R_{\mathrm{cut}}$
with $\mathrm{jumps.length} = m$. -/
def worldlinePolymerFinsetOfLength
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (R_cut m : ℕ) : Finset (WorldlineDysonPolymer L q_code) :=
  worldlineJumpListFinsetOfLength D_field R_cut m ×ˢ
    (worldlineScaleCubeFinset L R_cut).powerset

/-- Every valid worldline polymer $\gamma$ (`isValidWorldlinePolymer D_field sys C_RCA R_cut γ`)
belongs to the finite set `worldlinePolymerFinsetOfLength D_field R_cut γ.1.length`. -/
lemma mem_worldlinePolymerFinsetOfLength_of_isValidWorldlinePolymer
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    γ ∈ worldlinePolymerFinsetOfLength D_field R_cut γ.1.length := by
  rcases (isValidWorldlinePolymer_monomers_and_jumps_iff D_field γ).mp ⟨hγ.1, hγ.2.1⟩ with
    ⟨h_jumps, h_mayer⟩
  unfold worldlinePolymerFinsetOfLength worldlineJumpListFinsetOfLength
  rw [Finset.mem_product]
  refine ⟨Finset.mem_image.mpr ?_, Finset.mem_powerset.mpr h_mayer⟩
  refine ⟨fun i => ⟨γ.1.get i, h_jumps (γ.1.get i) (List.get_mem γ.1 i)⟩, Finset.mem_univ _, ?_⟩
  exact List.ofFn_get γ.1

/-- For any valid worldline polymer $\gamma$ and any active Mayer bond $\vartheta = (r', B) \in \gamma.2$,
its check collar $\mathcal{C}(B^+)$ is contained in `worldlinePolymerNativeCollar sys C_RCA γ`, so
`d_loc ϑ.1 ϑ.2` is invariant under any syndrome modification outside `worldlinePolymerNativeCollar sys C_RCA γ`
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma d_loc_congr_of_disjoint_nativeCollar
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA J : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ϑ : ℕ × Finset (Box3D L)} (hϑ : ϑ ∈ γ.2) :
    rcaCollarChecks sys C_RCA ϑ.1 ϑ.2 ⊆ worldlinePolymerNativeCollar sys C_RCA γ ∧
    (∀ {η₁ η₂ : IdxCSS[L, q_code, m_max] → Bool},
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, η₁ c = η₂ c) →
      d_loc ϑ.1 ϑ.2 η₁ = d_loc ϑ.1 ϑ.2 η₂) ∧
    (∀ (δ_other η : IdxCSS[L, q_code, m_max] → Bool),
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, δ_other c = false) →
      d_loc ϑ.1 ϑ.2 (syndromeXor δ_other η) = d_loc ϑ.1 ϑ.2 η) := by
  have hp_mem : ϑ ∈ worldlinePolymerMonomers γ := Finset.mem_union_right _ hϑ
  rcases mem_scaleCubeFinset_iff.mp (hγ.1 ϑ hp_mem) with ⟨hr, hA⟩
  have h_sub : rcaCollarChecks sys C_RCA ϑ.1 ϑ.2 ⊆ worldlinePolymerNativeCollar sys C_RCA γ := by
    intro c hc
    unfold worldlinePolymerNativeCollar nativeCollarSupport
    exact Finset.mem_biUnion.mpr ⟨ϑ, hp_mem, hc⟩
  have h_congr : ∀ {η₁ η₂ : IdxCSS[L, q_code, m_max] → Bool},
      (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, η₁ c = η₂ c) →
      d_loc ϑ.1 ϑ.2 η₁ = d_loc ϑ.1 ϑ.2 η₂ :=
    fun h_ag => (h_scalar ϑ.1 hr ϑ.2 hA).2.2 _ _ fun c hc => h_ag c (h_sub hc)
  refine ⟨h_sub, h_congr, fun δ_other η h_false => h_congr fun c hc => ?_⟩
  change bne (δ_other c) (η c) = η c
  rw [h_false c hc]
  cases η c <;> rfl

/-- Hard-core length truncation of `worldlineMayerPolymerClusterWeight` (Part II, Section 3.5 (`subsec:worldline-expansion`) and Proposition 3.10 (`prop:tube-local-ursell-erasure`),
Equation `eq:ursell-partition-sigma`): since every valid polymer has at least one check
in its native collar and compatible polymers have pairwise disjoint native collars, any polymer
tuple `K` with `Fintype.card (IdxCSS[L, q_code, m_max]) < K.length` has zero Mayer polymer cluster weight. -/
lemma worldlineMayerPolymerClusterWeight_eq_zero_of_length_gt_card_checks
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (ν : PauliBitstringPair L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool)
    {K : WorldlineUrsellCluster L q_code}
    (h_gt : Fintype.card (IdxCSS[L, q_code, m_max]) < K.length) :
    worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K = 0 := by
  unfold worldlineMayerPolymerClusterWeight
  split_ifs with hK
  · exfalso
    have h_le := length_le_card_checks_of_valid_and_pairwise_compatible
      D_field sys h_sys_supp h_geom hr0_le K hK.1 hK.2
    omega
  · rfl

/-- For any two collar-compatible valid worldline polymers $\gamma_1, \gamma_2$
(`¬arePolymersIncompatible sys C_RCA γ₁ γ₂`) and any jump monomers $\xi_1 \in \gamma_1.1$,
$\xi_2 \in \gamma_2.1$, their check collars $\mathcal{C}(A_{\xi_1}^+)$ and $\mathcal{C}(A_{\xi_2}^+)$
are disjoint and their syndrome-shift jump block operators commute on every realizable syndrome
sector $\sigma_0 \in \mathcal{V}_{\mathrm{valid}}$
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma commute_worldlineSyndromeShiftBlockOp_of_compatible_polymers
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    {γ₁ γ₂ : WorldlineDysonPolymer L q_code}
    (hγ₁ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₁)
    (hγ₂ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₂)
    (h_compat : ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
    {ξ₁ ξ₂ : WorldlineJumpMonomer L q_code}
    (hξ₁ : ξ₁ ∈ γ₁.1) (hξ₂ : ξ₂ ∈ γ₂.1)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    Disjoint (rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2)
      (rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2) ∧
    worldlineSyndromeShiftBlockOp D_field sys V ξ₁ *
      (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ₀) =
    worldlineSyndromeShiftBlockOp D_field sys V ξ₂ *
      (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ₀) := by
  have h_col_disj : Disjoint (worldlinePolymerNativeCollar sys C_RCA γ₁)
      (worldlinePolymerNativeCollar sys C_RCA γ₂) := not_not.mp h_compat
  have hp₁ : ξ₁.1 ∈ worldlinePolymerMonomers γ₁ :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₁))
  have hp₂ : ξ₂.1 ∈ worldlinePolymerMonomers γ₂ :=
    Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₂))
  have h_sub₁ : rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2 ⊆
      worldlinePolymerNativeCollar sys C_RCA γ₁ := by
    intro c hc
    unfold worldlinePolymerNativeCollar nativeCollarSupport
    exact Finset.mem_biUnion.mpr ⟨ξ₁.1, hp₁, hc⟩
  have h_sub₂ : rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2 ⊆
      worldlinePolymerNativeCollar sys C_RCA γ₂ := by
    intro c hc
    unfold worldlinePolymerNativeCollar nativeCollarSupport
    exact Finset.mem_biUnion.mpr ⟨ξ₂.1, hp₂, hc⟩
  have h_disj : Disjoint (rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2)
      (rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2) :=
    Finset.disjoint_left.mpr fun c hc₁ hc₂ =>
      Finset.disjoint_left.mp h_col_disj (h_sub₁ hc₁) (h_sub₂ hc₂)
  rcases mem_scaleCubeFinset_iff.mp (hγ₁.1 ξ₁.1 hp₁) with ⟨hr₁, hA₁⟩
  rcases mem_scaleCubeFinset_iff.mp (hγ₂.1 ξ₂.1 hp₂) with ⟨hr₂, hA₂⟩
  have hr₁_L : ξ₁.1.1 ∈ Finset.Icc 1 L :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr₁).1,
      le_trans (Finset.mem_Icc.mp hr₁).2 (Nat.min_le_right R_cut L)⟩
  have hr₂_L : ξ₂.1.1 ∈ Finset.Icc 1 L :=
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr₂).1,
      le_trans (Finset.mem_Icc.mp hr₂).2 (Nat.min_le_right R_cut L)⟩
  refine ⟨h_disj, commute_worldlineSyndromeShiftBlockOp_mul_syndromeProjector_of_disjoint_rcaCollarChecks
    D_field sys h_sys_checks hC_RCA V ξ₁ ξ₂ hA₁ hA₂
    (V.is_supported ξ₁.1.1 hr₁_L ξ₁.1.2 hA₁)
    (V.is_supported ξ₂.1.1 hr₂_L ξ₂.1.2 hA₂)
    (hγ₁.2.1 ξ₁ hξ₁).2.1 (hγ₂.2.1 ξ₂ hξ₂).2.1 h_disj hσ₀⟩

/-- Commutation of full weighted polymer loop operators `worldlinePolymerWeightedLoopOp`
for collar-compatible valid worldline polymers $\gamma_1, \gamma_2$ (`¬arePolymersIncompatible sys C_RCA γ₁ γ₂`)
on every realizable syndrome sector $\sigma_0 \in \mathcal{V}_{\mathrm{valid}}$
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma commute_worldlinePolymerWeightedLoopOp_of_compatible_polymers
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    {γ₁ γ₂ : WorldlineDysonPolymer L q_code}
    (hγ₁ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₁)
    (hγ₂ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₂)
    (h_compat : ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    worldlinePolymerWeightedLoopOp D_field sys V γ₁ *
      (worldlinePolymerWeightedLoopOp D_field sys V γ₂ * sys.syndromeProjector σ₀) =
    worldlinePolymerWeightedLoopOp D_field sys V γ₂ *
      (worldlinePolymerWeightedLoopOp D_field sys V γ₁ * sys.syndromeProjector σ₀) := by
  have h_step_comm : ∀ ξ₁ ∈ γ₁.1, ∀ ξ₂ ∈ γ₂.1, ∀ σ ∈ realizableSyndromes D_field,
      worldlineSyndromeShiftBlockOp D_field sys V ξ₁ *
        (worldlineSyndromeShiftBlockOp D_field sys V ξ₂ * sys.syndromeProjector σ) =
      worldlineSyndromeShiftBlockOp D_field sys V ξ₂ *
        (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ) :=
    fun ξ₁ hξ₁ ξ₂ hξ₂ _ hσ =>
      (commute_worldlineSyndromeShiftBlockOp_of_compatible_polymers
        D_field sys h_sys_checks hC_RCA V hγ₁ hγ₂ h_compat hξ₁ hξ₂ hσ).2
  have h_single_list : ∀ (ξ₁ : WorldlineJumpMonomer L q_code), ξ₁ ∈ γ₁.1 →
      ∀ (l₂ : List (WorldlineJumpMonomer L q_code)), (∀ ξ₂ ∈ l₂, ξ₂ ∈ γ₂.1) →
      ∀ σ ∈ realizableSyndromes D_field,
      worldlineSyndromeShiftBlockOp D_field sys V ξ₁ *
        ((l₂.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
          sys.syndromeProjector σ) =
      (l₂.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
        (worldlineSyndromeShiftBlockOp D_field sys V ξ₁ * sys.syndromeProjector σ) := by
    intro ξ₁ hξ₁ l₂ hl₂
    induction l₂ with
    | nil =>
      intro σ _
      simp
    | cons hd tl ih =>
      intro σ hσ
      have h_hd_in : hd ∈ γ₂.1 := hl₂ hd List.mem_cons_self
      have h_tl_in : ∀ ξ₂ ∈ tl, ξ₂ ∈ γ₂.1 := fun ξ₂ h => hl₂ ξ₂ (List.mem_cons_of_mem hd h)
      have h_prod : ((hd :: tl).reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod =
          (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
            worldlineSyndromeShiftBlockOp D_field sys V hd := by
        rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      let δ_hd := staticCSSPauliFlip D_field hd.2.1 hd.2.2
      let δ₁ := staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2
      have h_mem_hd : syndromeXor δ_hd σ ∈ realizableSyndromes D_field :=
        syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2 σ hσ
      have h_mem₁ : syndromeXor δ₁ σ ∈ realizableSyndromes D_field :=
        syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field ξ₁.2.1 ξ₁.2.2 σ hσ
      have h_abs_hd := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V hd σ).2
      have h_abs₁ := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V ξ₁ σ).2
      (try dsimp only at h_abs_hd h_abs₁)
      let B₁ := worldlineSyndromeShiftBlockOp D_field sys V ξ₁
      let B_hd := worldlineSyndromeShiftBlockOp D_field sys V hd
      let W_tl := (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod
      rw [h_prod]
      calc B₁ * ((W_tl * B_hd) * sys.syndromeProjector σ)
        _ = B₁ * (W_tl * (sys.syndromeProjector (syndromeXor δ_hd σ) *
              (B_hd * sys.syndromeProjector σ))) := by
              rw [mul_assoc W_tl B_hd, h_abs_hd]
        _ = (B₁ * (W_tl * sys.syndromeProjector (syndromeXor δ_hd σ))) *
              (B_hd * sys.syndromeProjector σ) := by
              simp only [mul_assoc]
        _ = (W_tl * (B₁ * sys.syndromeProjector (syndromeXor δ_hd σ))) *
              (B_hd * sys.syndromeProjector σ) := by
              rw [ih h_tl_in (syndromeXor δ_hd σ) h_mem_hd]
        _ = W_tl * (B₁ * (sys.syndromeProjector (syndromeXor δ_hd σ) *
              (B_hd * sys.syndromeProjector σ))) := by
              simp only [mul_assoc]
        _ = W_tl * (B₁ * (B_hd * sys.syndromeProjector σ)) := by
              rw [h_abs_hd]
        _ = W_tl * (B_hd * (B₁ * sys.syndromeProjector σ)) := by
              rw [h_step_comm ξ₁ hξ₁ hd h_hd_in σ hσ]
        _ = (W_tl * B_hd) * (B₁ * sys.syndromeProjector σ) := by
              simp only [mul_assoc]
  have h_list_list : ∀ (l₁ : List (WorldlineJumpMonomer L q_code)), (∀ ξ₁ ∈ l₁, ξ₁ ∈ γ₁.1) →
      ∀ σ ∈ realizableSyndromes D_field,
      (l₁.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
        (worldlinePolymerWeightedLoopOp D_field sys V γ₂ * sys.syndromeProjector σ) =
      worldlinePolymerWeightedLoopOp D_field sys V γ₂ *
        ((l₁.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
          sys.syndromeProjector σ) := by
    intro l₁ hl₁
    induction l₁ with
    | nil =>
      intro σ _
      simp
    | cons hd tl ih =>
      intro σ hσ
      have h_hd_in : hd ∈ γ₁.1 := hl₁ hd List.mem_cons_self
      have h_tl_in : ∀ ξ₁ ∈ tl, ξ₁ ∈ γ₁.1 := fun ξ₁ h => hl₁ ξ₁ (List.mem_cons_of_mem hd h)
      have h_prod : ((hd :: tl).reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod =
          (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod *
            worldlineSyndromeShiftBlockOp D_field sys V hd := by
        rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      let δ_hd := staticCSSPauliFlip D_field hd.2.1 hd.2.2
      have h_mem_hd : syndromeXor δ_hd σ ∈ realizableSyndromes D_field :=
        syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field hd.2.1 hd.2.2 σ hσ
      have h_abs_hd := (worldlineSyndromeShiftBlockOp_mul_syndromeProjector D_field sys V hd σ).2
      (try dsimp only at h_abs_hd)
      let B_hd := worldlineSyndromeShiftBlockOp D_field sys V hd
      let W_tl := (tl.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod
      let W₂ := worldlinePolymerWeightedLoopOp D_field sys V γ₂
      have h_hd_W₂ : B_hd * (W₂ * sys.syndromeProjector σ) =
          W₂ * (B_hd * sys.syndromeProjector σ) :=
        h_single_list hd h_hd_in γ₂.1 (fun _ h => h) σ hσ
      rw [h_prod]
      calc (W_tl * B_hd) * (W₂ * sys.syndromeProjector σ)
        _ = W_tl * (B_hd * (W₂ * sys.syndromeProjector σ)) := by rw [mul_assoc]
        _ = W_tl * (W₂ * (B_hd * sys.syndromeProjector σ)) := by rw [h_hd_W₂]
        _ = W_tl * (W₂ * (sys.syndromeProjector (syndromeXor δ_hd σ) *
              (B_hd * sys.syndromeProjector σ))) := by rw [h_abs_hd]
        _ = (W_tl * (W₂ * sys.syndromeProjector (syndromeXor δ_hd σ))) *
              (B_hd * sys.syndromeProjector σ) := by simp only [mul_assoc]
        _ = (W₂ * (W_tl * sys.syndromeProjector (syndromeXor δ_hd σ))) *
              (B_hd * sys.syndromeProjector σ) := by
              rw [ih h_tl_in (syndromeXor δ_hd σ) h_mem_hd]
        _ = W₂ * (W_tl * (sys.syndromeProjector (syndromeXor δ_hd σ) *
              (B_hd * sys.syndromeProjector σ))) := by simp only [mul_assoc]
        _ = W₂ * ((W_tl * B_hd) * sys.syndromeProjector σ) := by
              rw [h_abs_hd, mul_assoc]
  exact h_list_list γ₁.1 (fun _ h => h) σ₀ hσ₀

/-- Disjoint-collar syndrome-closure decomposition
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)):
for any list of syndrome shifts supported in pairwise disjoint check sets, their XOR sum vanishes
if and only if every component shift vanishes. -/
lemma foldr_syndromeXor_eq_false_iff_forall_eq_false_of_pairwiseDisjoint
    {α : Type*} {L q_code m_max : ℕ}
    (δ : α → IdxCSS[L, q_code, m_max] → Bool)
    (S : α → Finset (IdxCSS[L, q_code, m_max]))
    (l : List α)
    (h_supp : ∀ a ∈ l, ∀ c, δ a c = true → c ∈ S a)
    (h_pw : l.Pairwise (fun a b => Disjoint (S a) (S b))) :
    l.foldr (fun a acc => syndromeXor (δ a) acc) (fun _ => false) = (fun _ => false) ↔
      ∀ a ∈ l, δ a = (fun _ => false) := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    rcases List.pairwise_cons.mp h_pw with ⟨h_hd_tl, h_tl_pw⟩
    have h_supp_tl : ∀ a ∈ tl, ∀ c, δ a c = true → c ∈ S a :=
      fun a ha => h_supp a (List.mem_cons_of_mem hd ha)
    have h_tl_out : ∀ c ∈ S hd,
        (tl.foldr (fun a acc => syndromeXor (δ a) acc) (fun _ => false)) c = false := by
      intro c hc_hd
      exact foldr_syndromeXor_eq_of_all_false δ tl c (fun a ha => by
        cases h_b : δ a c
        · rfl
        · exact False.elim (Finset.disjoint_left.mp (h_hd_tl a ha) hc_hd
            (h_supp_tl a ha c h_b))) (fun _ => false)
    constructor
    · intro h_tot
      have h_hd_zero : δ hd = (fun _ => false) := by
        ext c
        by_cases hc : c ∈ S hd
        · have hc_tot := congr_fun h_tot c
          rw [List.foldr_cons] at hc_tot
          change bne (δ hd c) ((tl.foldr (fun a acc => syndromeXor (δ a) acc) (fun _ => false)) c) =
            false at hc_tot
          rw [h_tl_out c hc] at hc_tot
          revert hc_tot
          cases δ hd c <;> decide
        · cases h_b : δ hd c
          · rfl
          · exact False.elim (hc (h_supp hd List.mem_cons_self c h_b))
      have h_tl_tot :
          tl.foldr (fun a acc => syndromeXor (δ a) acc) (fun _ => false) = (fun _ => false) := by
        ext c
        have hc_tot := congr_fun h_tot c
        rw [List.foldr_cons] at hc_tot
        change bne (δ hd c) ((tl.foldr (fun a acc => syndromeXor (δ a) acc) (fun _ => false)) c) =
          false at hc_tot
        rw [congr_fun h_hd_zero c] at hc_tot
        revert hc_tot
        cases (tl.foldr (fun a acc => syndromeXor (δ a) acc) (fun _ => false)) c <;> decide
      have h_tl_all := (ih h_supp_tl h_tl_pw).mp h_tl_tot
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha_tl
      · exact h_hd_zero
      · exact h_tl_all a ha_tl
    · intro h_all
      rw [List.foldr_cons, (ih h_supp_tl h_tl_pw).mpr (fun a ha => h_all a (List.mem_cons_of_mem hd ha)),
        h_all hd List.mem_cons_self]
      rfl

/-- Minimum jump length `2 ≤ jumps.length` of any non-empty syndrome-closed jump sequence
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma jump_list_length_ge_two_of_closed_and_nonempty
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {jumps : List (WorldlineJumpMonomer L q_code)}
    (h_ne : jumps ≠ [])
    (h_flips : ∀ ξ ∈ jumps, staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false))
    (h_closed : worldlineJumpListFlip D_field jumps = (fun _ => false)) :
    2 ≤ jumps.length := by
  rcases jumps with _ | ⟨ξ₁, _ | ⟨ξ₂, tl⟩⟩
  · exact False.elim (h_ne rfl)
  · exfalso
    apply h_flips ξ₁ List.mem_cons_self
    ext c
    have hc := congr_fun h_closed c
    change bne (staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2 c) false = false at hc
    revert hc
    cases staticCSSPauliFlip D_field ξ₁.2.1 ξ₁.2.2 c <;> decide
  · simp only [List.length_cons]
    omega

/-- Decomposition of `worldlineTrajectorySyndrome D_field jumps σ₀ τ t` as the XOR of the
vacuum-referenced trajectory shift `worldlineTrajectorySyndrome D_field jumps (fun _ => false) τ t`
and `σ₀`, together with native-collar support containment for any valid polymer $\gamma$
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlineTrajectorySyndrome_eq_syndromeXor_false_and_mem_nativeCollar
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA J : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ) (t : ℝ) :
    worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t =
      syndromeXor (worldlineTrajectorySyndrome D_field γ.1 (fun _ => false) τ t) σ₀ ∧
    (∀ c : IdxCSS[L, q_code, m_max],
      worldlineTrajectorySyndrome D_field γ.1 (fun _ => false) τ t c = true →
      c ∈ worldlinePolymerNativeCollar sys C_RCA γ) := by
  have h_fold : ∀ l : List (Fin γ.1.length),
      l.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2) acc) σ₀ =
      syndromeXor (l.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2) acc)
        (fun _ => false)) σ₀ := by
    intro l
    induction l with
    | nil =>
      ext c
      change σ₀ c = bne false (σ₀ c)
      cases σ₀ c <;> rfl
    | cons hd tl ih =>
      rw [List.foldr_cons, List.foldr_cons, ih]
      ext c
      let d_hd := staticCSSPauliFlip D_field (γ.1.get hd).2.1 (γ.1.get hd).2.2 c
      let d_tl := (tl.foldr (fun j acc =>
        syndromeXor (staticCSSPauliFlip D_field (γ.1.get j).2.1 (γ.1.get j).2.2) acc)
        (fun _ => false)) c
      change bne d_hd (bne d_tl (σ₀ c)) = bne (bne d_hd d_tl) (σ₀ c)
      cases d_hd <;> cases d_tl <;> cases σ₀ c <;> rfl
  refine ⟨h_fold ((List.finRange γ.1.length).filter (fun j => decide (τ j ≤ t))), ?_⟩
  intro c hc_true
  by_contra hc_not
  have h_out := (worldlineTrajectorySyndrome_eq_outside_and_congr_on_nativeCollar
    D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar hγ τ (β := 0)).1
    (fun _ => false) t c hc_not
  rw [h_out] at hc_true
  cases hc_true

/-- Mayer bond factor decoupling across collar-disjoint worldline polymers
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlineMayerBondFactor_decouple_of_disjoint_nativeCollar
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA J β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ϑ : ℕ × Finset (Box3D L)} (hϑ : ϑ ∈ γ.2)
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : Fin γ.1.length → ℝ)
    (δ_other : ℝ → IdxCSS[L, q_code, m_max] → Bool)
    (h_other_out : ∀ t : ℝ, ∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, δ_other t c = false) :
    Real.exp (-∫ t in Set.Icc 0 β,
      (d_loc ϑ.1 ϑ.2 (syndromeXor (δ_other t) (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t)) -
        d_loc ϑ.1 ϑ.2 σ₀)) - 1 =
      worldlineMayerBondFactor D_field γ.1 d_loc σ₀ β ϑ τ := by
  unfold worldlineMayerBondFactor
  have h_congr := (d_loc_congr_of_disjoint_nativeCollar
    D_field sys V e_loc d_loc h_scalar hγ hϑ).2.2
  have h_int :
      (fun t : ℝ =>
        d_loc ϑ.1 ϑ.2 (syndromeXor (δ_other t) (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t)) -
          d_loc ϑ.1 ϑ.2 σ₀) =
      fun t : ℝ =>
        d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) -
          d_loc ϑ.1 ϑ.2 σ₀ := by
    funext t
    rw [h_congr (δ_other t) (worldlineTrajectorySyndrome D_field γ.1 σ₀ τ t) (h_other_out t)]
  rw [h_int]

/-- Multi-polymer trajectory bare $H_0$ energy additivity and Boltzmann factor product identity
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`), Equation `eq:energy-additivity-disjoint-loops`). -/
lemma syndromeEnergy_and_exp_multiPolymer_trajectory_add
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA J : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : ∀ i : Fin K.length, Fin (K.get i).1.length → ℝ) (t : ℝ) :
    let δ : Fin K.length → IdxCSS[L, q_code, m_max] → Bool :=
      fun i => worldlineTrajectorySyndrome D_field (K.get i).1 (fun _ => false) (τ i) t
    let σ_tot := (List.finRange K.length).foldr (fun i acc => syndromeXor (δ i) acc) σ₀
    sys.syndromeEnergy σ_tot - sys.syndromeEnergy σ₀ =
      ((List.finRange K.length).map (fun i =>
        sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t) -
          sys.syndromeEnergy σ₀)).sum ∧
    Real.exp (-(sys.syndromeEnergy σ_tot - sys.syndromeEnergy σ₀)) =
      ((List.finRange K.length).map (fun i =>
        Real.exp (-(sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t) -
          sys.syndromeEnergy σ₀)))).prod := by
  intro δ σ_tot
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_fin_pw : (List.finRange K.length).Pairwise (fun i j =>
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get i))
        (worldlinePolymerNativeCollar sys C_RCA (K.get j))) := by
    rw [List.pairwise_iff_get]
    intro a b h_lt
    exact not_not.mp (h_pw_get ((List.finRange K.length).get a)
      ((List.finRange K.length).get b) (by simpa using h_lt))
  have h_supp : ∀ i ∈ List.finRange K.length, ∀ c,
      δ i c = true → c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get i) := by
    intro i _ c hc
    exact (worldlineTrajectorySyndrome_eq_syndromeXor_false_and_mem_nativeCollar
      D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar
      (hK_valid (K.get i) (List.get_mem K i)) σ₀ (τ i) t).2 c hc
  have h_add := (syndromeEnergy_foldr_syndromeXor_disjoint_list_add
    sys (fun i => worldlinePolymerNativeCollar sys C_RCA (K.get i)) δ
    (List.finRange K.length) h_fin_pw h_supp σ₀).1
  have h_map_eq :
      (List.finRange K.length).map (fun i =>
        sys.syndromeEnergy (syndromeXor (δ i) σ₀) - sys.syndromeEnergy σ₀) =
      (List.finRange K.length).map (fun i =>
        sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t) -
          sys.syndromeEnergy σ₀) := by
    refine List.map_congr_left fun i _ => ?_
    have h_xor := (worldlineTrajectorySyndrome_eq_syndromeXor_false_and_mem_nativeCollar
      D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar
      (hK_valid (K.get i) (List.get_mem K i)) σ₀ (τ i) t).1
    exact congrArg (fun η => sys.syndromeEnergy η - sys.syndromeEnergy σ₀) h_xor.symm
  have h_sum_eq : sys.syndromeEnergy σ_tot - sys.syndromeEnergy σ₀ =
      ((List.finRange K.length).map (fun i =>
        sys.syndromeEnergy (worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t) -
          sys.syndromeEnergy σ₀)).sum :=
    h_add.trans (congrArg List.sum h_map_eq)
  refine ⟨h_sum_eq, ?_⟩
  rw [h_sum_eq]
  have h_exp_list : ∀ l : List ℝ,
      Real.exp (-l.sum) = (l.map (fun x => Real.exp (-x))).prod := by
    intro l
    induction l with
    | nil => simp
    | cons hd tl ih =>
      rw [List.sum_cons, neg_add, Real.exp_add, List.map_cons, List.prod_cons, ih]
  rw [h_exp_list, List.map_map]
  rfl

/-- For any list $K$ of valid worldline polymers and any syndrome-closed Pauli pair
$\nu \in \text{syndromeClosedPauliFinset } D\_\text{field}$, the symplectic character of the sum of
canonical logical coset representatives $\sum_{\gamma \in K} \mu(\gamma)$ equals the symplectic
character of the sum of bare polymer loops $\sum_{\gamma \in K} (\text{worldlinePolymerLoopX } \gamma, \text{worldlinePolymerLoopZ } \gamma)$
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma symplecticPauliSign_sum_worldlinePolymerLogicalCoset_eq_sum_loop
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {K : WorldlineUrsellCluster L q_code}
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ν : PauliBitstringPair L q_code}
    (hν : ν ∈ syndromeClosedPauliFinset D_field) :
    symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum =
      symplecticPauliSign ν (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum := by
  rcases symplecticPauliSign_mul_and_orthogonality D_field with ⟨_, h_mul_right, _, _⟩
  induction K with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h_mul_right, h_mul_right,
      symplecticPauliSign_worldlinePolymerLogicalCoset_eq_loop D_field h_valid sys h_sys_checks
        (hK_valid hd List.mem_cons_self) hν,
      ih (fun γ hγ => hK_valid γ (List.mem_cons_of_mem hd hγ))]

/-- For any list $K = [\gamma_1, \dots, \gamma_p]$ of collar-compatible valid worldline polymers,
their monomer sets `worldlinePolymerMonomers (K.get i)` (and in particular their active Mayer bond
sets `(K.get i).2`) are pairwise disjoint, and on any native collar `worldlinePolymerNativeCollar sys C_RCA (K.get i)`
the combined multi-polymer syndrome trajectory $\sigma_{\mathrm{tot}}(t)$ equals the $i$-th polymer's
individual trajectory `worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t`, so every active
Mayer bond factor $\vartheta \in (K.\mathrm{get}\;i).2$ decouples
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma multiPolymer_trajectory_agree_on_nativeCollar_and_mayerBond_decouple
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA J β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : ∀ i : Fin K.length, Fin (K.get i).1.length → ℝ) :
    let δ : Fin K.length → ℝ → IdxCSS[L, q_code, m_max] → Bool :=
      fun i t => worldlineTrajectorySyndrome D_field (K.get i).1 (fun _ => false) (τ i) t
    let σ_tot : ℝ → IdxCSS[L, q_code, m_max] → Bool :=
      fun t => (List.finRange K.length).foldr (fun i acc => syndromeXor (δ i t) acc) σ₀
    (∀ i : Fin K.length, ∀ t : ℝ, ∀ c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get i),
      σ_tot t c = worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t c) ∧
    (∀ i : Fin K.length, ∀ ϑ ∈ (K.get i).2,
      Real.exp (-∫ t in Set.Icc 0 β,
        (d_loc ϑ.1 ϑ.2 (σ_tot t) - d_loc ϑ.1 ϑ.2 σ₀)) - 1 =
        worldlineMayerBondFactor D_field (K.get i).1 d_loc σ₀ β ϑ (τ i)) := by
  intro δ σ_tot
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_disj : ∀ i j : Fin K.length, i ≠ j →
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get i))
        (worldlinePolymerNativeCollar sys C_RCA (K.get j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h_lt | h_gt
    · exact not_not.mp (h_pw_get i j h_lt)
    · exact (not_not.mp (h_pw_get j i h_gt)).symm
  have h_supp : ∀ j : Fin K.length, ∀ t : ℝ, ∀ c,
      δ j t c = true → c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get j) := by
    intro j t c hc
    exact (worldlineTrajectorySyndrome_eq_syndromeXor_false_and_mem_nativeCollar
      D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar
      (hK_valid (K.get j) (List.get_mem K j)) σ₀ (τ j) t).2 c hc
  have h_agree : ∀ i : Fin K.length, ∀ t : ℝ, ∀ c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get i),
      σ_tot t c = worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t c := by
    intro i t c hc_i
    have h_xor_i := congr_fun (worldlineTrajectorySyndrome_eq_syndromeXor_false_and_mem_nativeCollar
      D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar
      (hK_valid (K.get i) (List.get_mem K i)) σ₀ (τ i) t).1 c
    rw [h_xor_i]
    have h_other_false : ∀ j : Fin K.length, j ≠ i → δ j t c = false := by
      intro j hji
      cases h_b : δ j t c
      · rfl
      · exact False.elim (Finset.disjoint_left.mp (h_disj i j hji.symm) hc_i (h_supp j t c h_b))
    have h_fold_in : ∀ (l : List (Fin K.length)), l.Nodup →
        ((l.foldr (fun j acc => syndromeXor (δ j t) acc) σ₀) c =
          if i ∈ l then (syndromeXor (δ i t) σ₀) c else σ₀ c) := by
      intro l hl_nd
      induction l with
      | nil => simp
      | cons hd tl ih =>
        rcases List.nodup_cons.mp hl_nd with ⟨hd_not_tl, htl_nd⟩
        rw [List.foldr_cons]
        change bne (δ hd t c) ((tl.foldr (fun j acc => syndromeXor (δ j t) acc) σ₀) c) = _
        rw [ih htl_nd]
        by_cases h_eq : hd = i
        · subst h_eq
          rw [if_neg hd_not_tl, if_pos List.mem_cons_self]
          rfl
        · rw [h_other_false hd h_eq]
          simp only [List.mem_cons, Ne.symm h_eq, false_or]
          cases (if i ∈ tl then (syndromeXor (δ i t) σ₀) c else σ₀ c) <;> rfl
    have h_res := h_fold_in (List.finRange K.length) (List.nodup_finRange K.length)
    rw [if_pos (List.mem_finRange i)] at h_res
    exact h_res
  refine ⟨h_agree, fun i ϑ hϑ => ?_⟩
  have h_int :
      (fun t : ℝ => d_loc ϑ.1 ϑ.2 (σ_tot t) - d_loc ϑ.1 ϑ.2 σ₀) =
      (fun t : ℝ =>
        d_loc ϑ.1 ϑ.2 (worldlineTrajectorySyndrome D_field (K.get i).1 σ₀ (τ i) t) -
          d_loc ϑ.1 ϑ.2 σ₀) := by
    funext t
    rw [(d_loc_congr_of_disjoint_nativeCollar
      D_field sys V e_loc d_loc h_scalar (hK_valid (K.get i) (List.get_mem K i)) hϑ).2.1
      (h_agree i t)]
  exact congrArg (fun g : ℝ → ℝ => Real.exp (-∫ t in Set.Icc 0 β, g t) - 1) h_int

/-- Character average over $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$ of the
Mayer polymer-gas cluster weight `worldlineMayerPolymerClusterWeight`: for any valid compatible
polymer tuple $K$, the character average projects onto tuples whose net bare loop sum
$\sum_{\gamma \in K} (\mathrm{worldlinePolymerLoopX}\;\gamma, \mathrm{worldlinePolymerLoopZ}\;\gamma)$
commutes with every $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma multiPolymer_logical_character_average_clusterWeight_eq
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA β : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (K : WorldlineUrsellCluster L q_code)
    (σ : IdxCSS[L, q_code, m_max] → Bool) :
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
          spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
            worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
              (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ))).prod
    else 0 := by
  by_cases hK : (∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) ∧
      K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂)
  · have h_term : ∀ ν ∈ syndromeClosedPauliFinset D_field,
        (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
          worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K =
        (Nat.factorial K.length : ℝ)⁻¹ *
          ((((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
            (K.map (fun γ => worldlinePolymerWeight D_field sys C_RCA β V d_loc ν γ σ)).prod) := by
      intro ν _
      unfold worldlineMayerPolymerClusterWeight
      rw [if_pos hK]
      ring
    rw [Finset.sum_congr rfl h_term, ← Finset.mul_sum,
      multiPolymer_logical_character_average_eq D_field sys V d_loc K σ]
    have h_iff :
        (∀ ν ∈ syndromeClosedPauliFinset D_field,
          symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 1) ↔
        (∀ ν ∈ syndromeClosedPauliFinset D_field,
          symplecticPauliSign ν
            (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = 1) := by
      refine forall₂_congr fun ν hν => ?_
      rw [symplecticPauliSign_sum_worldlinePolymerLogicalCoset_eq_sum_loop
        D_field h_valid sys h_sys_checks hK.1 hν]
    by_cases h_char : ∀ ν ∈ syndromeClosedPauliFinset D_field,
        symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum = 1
    · rw [if_pos h_char, if_pos ⟨hK.1, hK.2, h_iff.mp h_char⟩]
    · rw [if_neg h_char, if_neg (fun h => h_char (h_iff.mpr h.2.2)), mul_zero]
  · have h_zero : ∀ ν ∈ syndromeClosedPauliFinset D_field,
        (((syndromeClosedPauliFinset D_field).card : ℝ))⁻¹ *
          worldlineMayerPolymerClusterWeight D_field sys C_RCA R_cut β V d_loc ν σ K = 0 := by
      intro ν _
      unfold worldlineMayerPolymerClusterWeight
      rw [if_neg hK, mul_zero]
    rw [Finset.sum_eq_zero h_zero, if_neg (fun h => hK ⟨h.1, h.2.1⟩)]

/-- For any valid worldline polymer $\gamma$ and realizable syndrome $\sigma \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$,
the untwisted polymer weight `spanningSurfaceSign ... σ * worldlinePolymerMicroWeight ... (restrictSyndromeToCollar ... σ)`
equals the sector trace on $\sigma$ times the full-syndrome Dyson simplex integral
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma spanningSurfaceSign_mul_worldlinePolymerMicroWeight_eq_of_valid
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
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ : σ ∈ realizableSyndromes D_field) :
    spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) σ *
      worldlinePolymerMicroWeight D_field sys C_RCA β V d_loc γ
        (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ) =
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
        else 0 := by
  have h_w := worldlinePolymerWeight_eq_sector_trace_mul_simplex_integral (β := β)
    D_field h_valid sys h_sys_checks h_geom h_tqo1 h_tqo2 hR_le hr0_le
    V e_loc d_loc h_scalar (0, 0) hγ hσ
  have h_s0 : symplecticPauliSign (0, 0) (worldlinePolymerLogicalCoset D_field sys C_RCA γ) = 1 := by
    unfold symplecticPauliSign
    simp
  unfold worldlinePolymerWeight at h_w
  rw [h_s0, one_mul, one_mul] at h_w
  exact h_w

/-- Every monomer scale-cube $p \in \mathrm{worldlinePolymerMonomers}\;\gamma$ of a valid worldline
polymer $\gamma$ has a nonempty check collar `rcaCollarChecks sys C_RCA p.1 p.2`, so collar-compatible
valid polymers have pairwise disjoint monomer sets `worldlinePolymerMonomers` and pairwise disjoint
active Mayer bond sets $\gamma.2$, and the product of Mayer bond factors over $\bigcup_{i} (K.\mathrm{get}\;i).2$
factors into the product over $i : \mathrm{Fin}\;K.\mathrm{length}$ of each polymer's Mayer bond product
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma disjoint_worldlinePolymerMonomers_and_prod_mayerBond_of_compatible
    {L q_code r_0 m_max w_0 R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0)
    {C_RCA J β : ℝ} (hr0_le : 1 + 4 * (r_0 : ℝ) ≤ C_RCA)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (IdxCSS[L, q_code, m_max] → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_cut C_RCA J V e_loc d_loc)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (hK_pw : K.Pairwise (fun γ₁ γ₂ => ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂))
    (σ₀ : IdxCSS[L, q_code, m_max] → Bool)
    (τ : ∀ i : Fin K.length, Fin (K.get i).1.length → ℝ) :
    let δ : Fin K.length → ℝ → IdxCSS[L, q_code, m_max] → Bool :=
      fun i t => worldlineTrajectorySyndrome D_field (K.get i).1 (fun _ => false) (τ i) t
    let σ_tot : ℝ → IdxCSS[L, q_code, m_max] → Bool :=
      fun t => (List.finRange K.length).foldr (fun i acc => syndromeXor (δ i t) acc) σ₀
    (∀ i j : Fin K.length, i ≠ j →
      Disjoint (worldlinePolymerMonomers (K.get i)) (worldlinePolymerMonomers (K.get j)) ∧
      Disjoint (K.get i).2 (K.get j).2) ∧
    (∏ ϑ ∈ (Finset.univ : Finset (Fin K.length)).biUnion (fun i => (K.get i).2),
      (Real.exp (-∫ t in Set.Icc 0 β,
        (d_loc ϑ.1 ϑ.2 (σ_tot t) - d_loc ϑ.1 ϑ.2 σ₀)) - 1)) =
      ∏ i : Fin K.length, ∏ ϑ ∈ (K.get i).2,
        worldlineMayerBondFactor D_field (K.get i).1 d_loc σ₀ β ϑ (τ i) := by
  intro δ σ_tot
  have h_mon_col_ne : ∀ γ ∈ K, ∀ p ∈ worldlinePolymerMonomers γ,
      (rcaCollarChecks sys C_RCA p.1 p.2).Nonempty := by
    intro γ hγ p hp
    have hγ_val := hK_valid γ hγ
    have h_ne : γ.1 ≠ [] := by
      intro h_nil
      have h_len := hγ_val.2.2.1.1
      rw [h_nil, List.length_nil] at h_len
      omega
    rcases List.exists_mem_of_ne_nil γ.1 h_ne with ⟨ξ₀, hξ₀⟩
    have hp₀ : ξ₀.1 ∈ worldlinePolymerMonomers γ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₀))
    have h_path := hγ_val.2.2.2.2 ξ₀.1 hp₀ p hp
    cases h_path with
    | refl =>
      have h_flip_ne := (hγ_val.2.1 ξ₀ hξ₀).2.1
      have h_ex_c : ∃ c : IdxCSS[L, q_code, m_max],
          staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c = true := by
        by_contra! h_all
        apply h_flip_ne
        funext c
        cases h_val : staticCSSPauliFlip D_field ξ₀.2.1 ξ₀.2.2 c
        · rfl
        · exact False.elim (h_all c h_val)
      rcases h_ex_c with ⟨c, hc⟩
      have hp_mem : ξ₀.1 ∈ worldlinePolymerMonomers γ := hp₀
      rcases mem_scaleCubeFinset_iff.mp (hγ_val.1 ξ₀.1 hp_mem) with ⟨hr, hA⟩
      have hc_int := staticCSSPauliFlip_mem_cubeIntersectingChecks
        D_field sys (fun idx => (h_sys_checks idx).2.1) ξ₀.1.2 ξ₀.2.1 ξ₀.2.2
        (hγ_val.2.1 ξ₀ hξ₀).1 c hc
      exact ⟨c, cubeIntersectingChecks_subset_rcaCollarChecks sys h_geom hr0_le
        (Finset.mem_Icc.mp hr).1 hA hc_int⟩
    | tail _ h_step =>
      rcases Finset.not_disjoint_iff.mp h_step.2.2.2 with ⟨c, _, hc_p⟩
      exact ⟨c, hc_p⟩
  have h_pw_get := List.pairwise_iff_get.mp hK_pw
  have h_disj_col : ∀ i j : Fin K.length, i ≠ j →
      Disjoint (worldlinePolymerNativeCollar sys C_RCA (K.get i))
        (worldlinePolymerNativeCollar sys C_RCA (K.get j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h_lt | h_gt
    · exact not_not.mp (h_pw_get i j h_lt)
    · exact (not_not.mp (h_pw_get j i h_gt)).symm
  have h_disj_mon : ∀ i j : Fin K.length, i ≠ j →
      Disjoint (worldlinePolymerMonomers (K.get i)) (worldlinePolymerMonomers (K.get j)) ∧
      Disjoint (K.get i).2 (K.get j).2 := by
    intro i j hij
    have h_mon : Disjoint (worldlinePolymerMonomers (K.get i))
        (worldlinePolymerMonomers (K.get j)) := by
      refine Finset.disjoint_left.mpr fun p hp_i hp_j => ?_
      rcases h_mon_col_ne (K.get i) (List.get_mem K i) p hp_i with ⟨c, hc⟩
      have hc_i : c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get i) :=
        Finset.mem_biUnion.mpr ⟨p, hp_i, hc⟩
      have hc_j : c ∈ worldlinePolymerNativeCollar sys C_RCA (K.get j) :=
        Finset.mem_biUnion.mpr ⟨p, hp_j, hc⟩
      exact Finset.disjoint_left.mp (h_disj_col i j hij) hc_i hc_j
    refine ⟨h_mon, Finset.disjoint_left.mpr fun ϑ hϑ_i hϑ_j => ?_⟩
    exact Finset.disjoint_left.mp h_mon (Finset.mem_union_right _ hϑ_i)
      (Finset.mem_union_right _ hϑ_j)
  refine ⟨h_disj_mon, ?_⟩
  have h_pw_mayer : (↑(Finset.univ : Finset (Fin K.length)) : Set (Fin K.length)).PairwiseDisjoint
      (fun i => (K.get i).2) := by
    intro i _ j _ hij
    exact (h_disj_mon i j hij).2
  rw [Finset.prod_biUnion h_pw_mayer]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun ϑ hϑ => ?_
  exact (multiPolymer_trajectory_agree_on_nativeCollar_and_mayerBond_decouple
    D_field sys h_sys_checks h_geom hr0_le V e_loc d_loc h_scalar K hK_valid hK_pw σ₀ τ).2 i ϑ hϑ

/-- For any two collar-compatible valid worldline polymers $\gamma_1, \gamma_2$
(`¬arePolymersIncompatible sys C_RCA γ₁ γ₂`) with `1 ≤ C_RCA`, their bare Pauli loop bitstrings
have disjoint slot supports, so their bare Pauli loop operators `worldlinePolymerLoopOp γ₁` and
`worldlinePolymerLoopOp γ₂` commute and their net loop bitstrings have symplectic commutation sign `1`
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma commute_worldlinePolymerLoopOp_of_compatible_polymers
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_supp : ∀ idx, sys.support idx = staticCSSCheckSupport D_field idx)
    {C_RCA : ℝ} (hC_RCA : 1 ≤ C_RCA)
    {γ₁ γ₂ : WorldlineDysonPolymer L q_code}
    (hγ₁ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₁)
    (hγ₂ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ₂)
    (h_compat : ¬ArePolymersIncompatible sys C_RCA γ₁ γ₂) :
    (∀ ξ₁ ∈ γ₁.1, ∀ ξ₂ ∈ γ₂.1,
      Commute (worldlineJumpOp ξ₁) (worldlineJumpOp ξ₂)) ∧
    Commute (worldlinePolymerLoopOp γ₁) (worldlinePolymerLoopOp γ₂) := by
  have h_col_disj : Disjoint (worldlinePolymerNativeCollar sys C_RCA γ₁)
      (worldlinePolymerNativeCollar sys C_RCA γ₂) := not_not.mp h_compat
  have h_jump_comm : ∀ ξ₁ ∈ γ₁.1, ∀ ξ₂ ∈ γ₂.1,
      Commute (worldlineJumpOp ξ₁) (worldlineJumpOp ξ₂) := by
    intro ξ₁ hξ₁ ξ₂ hξ₂
    have hp₁ : ξ₁.1 ∈ worldlinePolymerMonomers γ₁ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₁))
    have hp₂ : ξ₂.1 ∈ worldlinePolymerMonomers γ₂ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ₂))
    have h_sub₁ : rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2 ⊆
        worldlinePolymerNativeCollar sys C_RCA γ₁ :=
      fun c hc => Finset.mem_biUnion.mpr ⟨ξ₁.1, hp₁, hc⟩
    have h_sub₂ : rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2 ⊆
        worldlinePolymerNativeCollar sys C_RCA γ₂ :=
      fun c hc => Finset.mem_biUnion.mpr ⟨ξ₂.1, hp₂, hc⟩
    have h_disj : Disjoint (rcaCollarChecks sys C_RCA ξ₁.1.1 ξ₁.1.2)
        (rcaCollarChecks sys C_RCA ξ₂.1.1 ξ₂.1.2) :=
      Finset.disjoint_left.mpr fun c hc₁ hc₂ =>
        Finset.disjoint_left.mp h_col_disj (h_sub₁ hc₁) (h_sub₂ hc₂)
    rcases mem_scaleCubeFinset_iff.mp (hγ₁.1 ξ₁.1 hp₁) with ⟨_, hA₁⟩
    rcases mem_scaleCubeFinset_iff.mp (hγ₂.1 ξ₂.1 hp₂) with ⟨_, hA₂⟩
    have h_slot_disj : ∀ slot : BoxSlot3D L q_code, slot.1 ∈ ξ₁.1.2 → slot.1 ∉ ξ₂.1.2 :=
      slot_disjoint_of_disjoint_rcaCollarChecks D_field sys h_sys_supp hC_RCA hA₁ hA₂ h_disj
    exact weylPauliZX_comm_of_disjoint_slot_support h_slot_disj
      ξ₁.2.1 ξ₁.2.2 ξ₂.2.1 ξ₂.2.2 (hγ₁.2.1 ξ₁ hξ₁).1 (hγ₂.2.1 ξ₂ hξ₂).1
  refine ⟨h_jump_comm, ?_⟩
  unfold worldlinePolymerLoopOp
  have h_prod_comm : ∀ (l₁ l₂ : List (WorldlineJumpMonomer L q_code)),
      (∀ ξ₁ ∈ l₁, ξ₁ ∈ γ₁.1) → (∀ ξ₂ ∈ l₂, ξ₂ ∈ γ₂.1) →
      Commute (l₁.map worldlineJumpOp).prod (l₂.map worldlineJumpOp).prod := by
    intro l₁ l₂ hl₁ hl₂
    induction l₁ with
    | nil => exact Commute.one_left _
    | cons hd₁ tl₁ ih₁ =>
      rw [List.map_cons, List.prod_cons]
      refine Commute.mul_left ?_ (ih₁ (fun ξ h => hl₁ ξ (List.mem_cons_of_mem hd₁ h)))
      have h_hd₁ : hd₁ ∈ γ₁.1 := hl₁ hd₁ List.mem_cons_self
      clear ih₁ hl₁ tl₁
      induction l₂ with
      | nil => exact Commute.one_right _
      | cons hd₂ tl₂ ih₂ =>
        rw [List.map_cons, List.prod_cons]
        exact Commute.mul_right (h_jump_comm hd₁ h_hd₁ hd₂ (hl₂ hd₂ List.mem_cons_self))
          (ih₂ (fun ξ h => hl₂ ξ (List.mem_cons_of_mem hd₂ h)))
  exact h_prod_comm γ₁.1.reverse γ₂.1.reverse
    (fun ξ h => List.mem_reverse.mp h) (fun ξ h => List.mem_reverse.mp h)

/-- For any valid worldline polymer $\gamma$ (`isValidWorldlinePolymer D_field sys C_RCA R_cut γ`)
with `R_cut ≤ L_star`:
1. Its bare loop operator `worldlinePolymerLoopOp γ` commutes with every syndrome projector `sys.syndromeProjector σ`.
2. There exists a collar-local complex scalar `C_γ : (IdxCSS[L, q_code, m_max] → Bool) → ℂ`
   depending only on `worldlinePolymerNativeCollar sys C_RCA γ` such that
   `worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀ = C_γ σ₀ • (worldlinePolymerLoopOp γ * sys.syndromeProjector σ₀)`
   and `sys.syndromeProjector σ₀ * worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀ = worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀`
   for every `σ₀ ∈ realizableSyndromes D_field`
   (Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma exists_collar_scalar_worldlinePolymerWeightedLoopOp_and_commute_loopOp
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    (∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      Commute (worldlinePolymerLoopOp γ) (sys.syndromeProjector σ)) ∧
    ∃ C_γ : (IdxCSS[L, q_code, m_max] → Bool) → ℂ,
      (∀ σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool,
        (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ₁ c = σ₂ c) →
        C_γ σ₁ = C_γ σ₂) ∧
      (∀ σ₀ ∈ realizableSyndromes D_field,
        worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀ =
          C_γ σ₀ • (worldlinePolymerLoopOp γ * sys.syndromeProjector σ₀) ∧
        sys.syndromeProjector σ₀ *
          (worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀) =
          worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀) := by
  have h_comm_loop : ∀ σ : IdxCSS[L, q_code, m_max] → Bool,
      Commute (worldlinePolymerLoopOp γ) (sys.syndromeProjector σ) := by
    intro σ
    rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1.reverse with ⟨s_loop, hs_loop⟩
    have h_sum_X : (γ.1.reverse.map (fun ξ => ξ.2.1)).sum = worldlinePolymerLoopX γ := by
      unfold worldlinePolymerLoopX; rw [List.map_reverse, List.sum_reverse]
    have h_sum_Z : (γ.1.reverse.map (fun ξ => ξ.2.2)).sum = worldlinePolymerLoopZ γ := by
      unfold worldlinePolymerLoopZ; rw [List.map_reverse, List.sum_reverse]
    rw [h_sum_X, h_sum_Z] at hs_loop
    have h_closed_mem : (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ) ∈
        syndromeClosedPauliFinset D_field :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hγ.2.2.1.2⟩
    have h_zx_comm := (weylPauliZX_comm_checkProj_and_syndromeProjector_of_syndromeClosed
      D_field sys h_sys_checks h_closed_mem).2.1 σ
    change Commute (worldlinePolymerLoopOpZX γ) (sys.syndromeProjector σ)
    unfold worldlinePolymerLoopOpZX
    rw [hs_loop]
    exact h_zx_comm.smul_left _
  have h_jumps_cond : ∀ ξ ∈ γ.1,
      1 ≤ ξ.1.1 ∧ ξ.1.1 ≤ L_star ∧
      ξ.1.2 ∈ boxCubes 3 L ξ.1.1 ∧
      IsSupportedOn (SiteCSS[L, q_code]) ξ.1.2 (V.term ξ.1.1 ξ.1.2) ∧
      (∀ slot : BoxSlot3D L q_code, ξ.2.1 slot ≠ 0 ∨ ξ.2.2 slot ≠ 0 → slot.1 ∈ ξ.1.2) ∧
      staticCSSPauliFlip D_field ξ.2.1 ξ.2.2 ≠ (fun _ => false) := by
    intro ξ hξ
    have hp_mem : ξ.1 ∈ worldlinePolymerMonomers γ :=
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ))
    rcases mem_scaleCubeFinset_iff.mp (hγ.1 ξ.1 hp_mem) with ⟨hr, hA⟩
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hr_min⟩
    have hr_Lstar : ξ.1.1 ≤ L_star := le_trans hr_min (le_trans (Nat.min_le_left R_cut L) hR_le)
    have hr_L : ξ.1.1 ∈ Finset.Icc 1 L :=
      Finset.mem_Icc.mpr ⟨hr1, le_trans hr_min (Nat.min_le_right R_cut L)⟩
    exact ⟨hr1, hr_Lstar, hA, V.is_supported ξ.1.1 hr_L ξ.1.2 hA,
      (hγ.2.1 ξ hξ).1, (hγ.2.1 ξ hξ).2.1⟩
  rcases exists_collar_scalar_list_prod_reverse_worldlineSyndromeShiftBlockOp_eq_smul_worldlineJumpOp
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 V γ.1 h_jumps_cond with
    ⟨C_jumps, hC_ag, hC_eq⟩
  refine ⟨h_comm_loop, C_jumps, fun σ₁ σ₂ h_ag => hC_ag σ₁ σ₂ fun ξ hξ c hc => ?_,
    fun σ₀ hσ₀ => ?_⟩
  · refine h_ag c ?_
    unfold worldlinePolymerNativeCollar nativeCollarSupport
    exact Finset.mem_biUnion.mpr ⟨ξ.1,
      Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map_of_mem hξ)), hc⟩
  · have h_act : worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀ =
        C_jumps σ₀ • (worldlinePolymerLoopOp γ * sys.syndromeProjector σ₀) :=
      hC_eq σ₀ hσ₀
    refine ⟨h_act, ?_⟩
    rw [h_act, clm_mul_smul, ← mul_assoc, (h_comm_loop σ₀).symm.eq,
      mul_assoc (worldlinePolymerLoopOp γ),
      ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1]

/-- Multi-polymer collar-scalar factorization of the ordered product of
`worldlinePolymerWeightedLoopOp D_field sys V` along any list `K` of valid worldline polymers
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma list_prod_worldlinePolymerWeightedLoopOp_mul_syndromeProjector_eq
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star)
    (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool}
    (hσ₀ : σ₀ ∈ realizableSyndromes D_field) :
    ∃ c_fam : Fin K.length → ℂ,
      (∀ i : Fin K.length,
        worldlinePolymerWeightedLoopOp D_field sys V (K.get i) * sys.syndromeProjector σ₀ =
          c_fam i • (worldlinePolymerLoopOp (K.get i) * sys.syndromeProjector σ₀)) ∧
      (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod * sys.syndromeProjector σ₀ =
        (∏ i : Fin K.length, c_fam i) •
          ((K.map worldlinePolymerLoopOp).prod * sys.syndromeProjector σ₀) := by
  have h_loop_comm_list : ∀ l : List (WorldlineDysonPolymer L q_code),
      (∀ γ ∈ l, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) →
      Commute ((l.map worldlinePolymerLoopOp).prod) (sys.syndromeProjector σ₀) := by
    intro l hl
    induction l with
    | nil => exact Commute.one_left _
    | cons g gs ihg =>
      rw [List.map_cons, List.prod_cons]
      exact Commute.mul_left
        ((exists_collar_scalar_worldlinePolymerWeightedLoopOp_and_commute_loopOp
          D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V
          (hl g List.mem_cons_self)).1 σ₀)
        (ihg (fun γ hγ => hl γ (List.mem_cons_of_mem g hγ)))
  induction K with
  | nil =>
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    simp
  | cons hd tl ih =>
    rcases (exists_collar_scalar_worldlinePolymerWeightedLoopOp_and_commute_loopOp
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V
      (hK_valid hd List.mem_cons_self)).2 with ⟨C_hd, _, hC_hd_act⟩
    rcases ih (fun γ hγ => hK_valid γ (List.mem_cons_of_mem hd hγ)) with
      ⟨c_tl, hc_tl_each, hc_tl_prod⟩
    let c_cons : Fin (hd :: tl).length → ℂ :=
      Fin.cons (C_hd σ₀) c_tl
    refine ⟨c_cons, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact (hC_hd_act σ₀ hσ₀).1
      · exact hc_tl_each j
    · have h_loop_comm_tl :
          Commute ((tl.map worldlinePolymerLoopOp).prod) (sys.syndromeProjector σ₀) :=
        h_loop_comm_list tl (fun γ hγ => hK_valid γ (List.mem_cons_of_mem hd hγ))
      have h_prod_cons : (∏ i : Fin (hd :: tl).length, c_cons i) =
          C_hd σ₀ * ∏ i : Fin tl.length, c_tl i := Fin.prod_univ_succ c_cons
      rw [List.map_cons, List.prod_cons, mul_assoc, hc_tl_prod, clm_mul_smul,
        h_loop_comm_tl.eq, ← mul_assoc (worldlinePolymerWeightedLoopOp D_field sys V hd),
        (hC_hd_act σ₀ hσ₀).1, clm_smul_mul, smul_smul,
        mul_assoc (worldlinePolymerLoopOp hd), ← h_loop_comm_tl.eq,
        ← mul_assoc (worldlinePolymerLoopOp hd),
        h_prod_cons, mul_comm (C_hd σ₀)]
      rfl

/-- Exact Pauli conjugation identity for `hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field u v) * (z • (weylPauliZ a * weylPauliX b)))`:
since $\Pi_{\mathrm{flip}(u, v)} = P_{u, v}\,\Pi_0\,P_{u, v}^{-1}$, conjugating $z \bullet (Z(a) X(b))$
by $P_{u, v}$ multiplies the vacuum trace $\operatorname{Tr}(\Pi_0\,(z \bullet (Z(a) X(b))))$ by the
symplectic character `symplecticPauliSign (u, v) (a, b)`
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma hilbertTrace_syndromeProjector_smul_weylPauliZX_eq
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (u v a b : BoxSlot3D L q_code → ZMod 2) (z : ℂ) :
    hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field u v) *
      (z • (weylPauliZ a * weylPauliX b))) =
    symplecticPauliSign (u, v) (a, b) *
      hilbertTrace (sys.P0 * (z • (weylPauliZ a * weylPauliX b))) := by
  have h_res := _root_.syndrome_resolution_indexed sys
  let U := weylPauliZ u * weylPauliX v
  let U_inv := weylPauliX v * weylPauliZ u
  let W := weylPauliZ a * weylPauliX b
  have hU_right : U * U_inv = 1 := by
    calc (weylPauliZ u * weylPauliX v) * (weylPauliX v * weylPauliZ u)
      _ = weylPauliZ u * (weylPauliX v * weylPauliX v) * weylPauliZ u := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliX_sq_eq_one v, mul_one, weylPauliZ_sq_eq_one u]
  have hU_left : U_inv * U = 1 := by
    calc (weylPauliX v * weylPauliZ u) * (weylPauliZ u * weylPauliX v)
      _ = weylPauliX v * (weylPauliZ u * weylPauliZ u) * weylPauliX v := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliZ_sq_eq_one u, mul_one, weylPauliX_sq_eq_one v]
  have hU_inter : U * sys.P0 = sys.syndromeProjector (staticCSSPauliFlip D_field u v) * U := by
    have h_flip : ∀ idx, U * sys.checkProj idx =
        (if staticCSSPauliFlip D_field u v idx then 1 - sys.checkProj idx else sys.checkProj idx) * U :=
      fun idx => by
        rw [(h_sys_checks idx).1]
        exact weylPauliZX_mul_staticCSSCheckProj D_field u v idx
    have h_int := intertwine_syndromeProjector_of_checkFlip sys h_flip (fun _ => false)
    have h_xor : (fun i => xor false (staticCSSPauliFlip D_field u v i)) =
        staticCSSPauliFlip D_field u v := by ext i; simp
    rw [h_res.1, h_xor] at h_int
    exact h_int
  have h_proj_eq : sys.syndromeProjector (staticCSSPauliFlip D_field u v) = U * sys.P0 * U_inv := by
    calc sys.syndromeProjector (staticCSSPauliFlip D_field u v)
      _ = sys.syndromeProjector (staticCSSPauliFlip D_field u v) * (U * U_inv) := by
          rw [hU_right, mul_one]
      _ = (sys.syndromeProjector (staticCSSPauliFlip D_field u v) * U) * U_inv := by
          rw [← mul_assoc]
      _ = U * sys.P0 * U_inv := by rw [← hU_inter]
  have h_comm : W * U = ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) • (U * W) := by
    dsimp [W, U]
    rw [weylPauliZX_comm_signScalar a b u v,
      ← (signScalar_symplectic_eq_symplecticPauliSign_and_mul (u, v) (u, v) (u, v) (a, b) (a, b) (a, b)).1]
    refine congrArg (· • ((weylPauliZ u * weylPauliX v) * (weylPauliZ a * weylPauliX b)))
      (congrArg signScalar ?_)
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have h_inv_comm : U_inv * (z • W) =
      ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) • ((z • W) * U_inv) := by
    have h_sq : symplecticPauliSign (u, v) (a, b) * symplecticPauliSign (u, v) (a, b) = 1 :=
      symplecticPauliSign_sq_eq_one (u, v) (a, b)
    calc U_inv * (z • W)
      _ = z • (U_inv * W * (U * U_inv)) := by rw [hU_right, mul_one, clm_mul_smul]
      _ = z • (U_inv * (W * U) * U_inv) := by simp only [mul_assoc]
      _ = z • (((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) •
            ((U_inv * U) * W * U_inv)) := by
          rw [h_comm, clm_mul_smul, clm_smul_mul]
          simp only [mul_assoc]
      _ = ((symplecticPauliSign (u, v) (a, b) : ℝ) : ℂ) • ((z • W) * U_inv) := by
          rw [hU_left, one_mul, smul_comm, clm_smul_mul]
  calc hilbertTrace (sys.syndromeProjector (staticCSSPauliFlip D_field u v) * (z • W))
    _ = hilbertTrace ((U * sys.P0) * (U_inv * (z • W))) := by
        rw [h_proj_eq]; simp only [mul_assoc]
    _ = symplecticPauliSign (u, v) (a, b) *
          hilbertTrace (((U * sys.P0) * (z • W)) * U_inv) := by
        rw [h_inv_comm, clm_mul_smul,
          (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 (symplecticPauliSign (u, v) (a, b)) 0).2.1]
        simp only [mul_assoc]
    _ = symplecticPauliSign (u, v) (a, b) *
          hilbertTrace (U_inv * ((U * sys.P0) * (z • W))) := by
        rw [hilbertTrace_mul_comm_aux ((U * sys.P0) * (z • W)) U_inv]
    _ = symplecticPauliSign (u, v) (a, b) *
          hilbertTrace (sys.P0 * (z • W)) := by
        have h_ass : U_inv * ((U * sys.P0) * (z • W)) = (U_inv * U) * (sys.P0 * (z • W)) := by
          simp only [mul_assoc]
        rw [h_ass, hU_left, one_mul]

/-- For every valid worldline polymer $\gamma$ (`isValidWorldlinePolymer D_field sys C_RCA R_cut γ`)
and every Pauli bitstring pair $(u, v)$, the spanning-surface syndrome parity sign
`spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ) (staticCSSPauliFlip D_field u v)`
equals the symplectic commutation sign of $(u, v)$ with the stabilizer-part bitstring
`worldlinePolymerLogicalCoset D_field sys C_RCA γ + (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)`
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`), Equation `eq:P-gamma-spanning-surface`). -/
lemma spanningSurfaceSign_worldlinePolymerSpanningSurface_eq_symplecticPauliSign
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    (u v : BoxSlot3D L q_code → ZMod 2) :
    spanningSurfaceSign (worldlinePolymerSpanningSurface D_field sys C_RCA γ)
      (staticCSSPauliFlip D_field u v) =
    symplecticPauliSign (u, v)
      (worldlinePolymerLogicalCoset D_field sys C_RCA γ +
        (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)) := by
  have h_span := (isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer
    D_field h_valid sys h_sys_checks γ hγ).2
  let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
  let α := worldlinePolymerSpanningSurface D_field sys C_RCA γ
  let a := worldlinePolymerLoopX γ
  let b := worldlinePolymerLoopZ γ
  let L_op := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ
  let σ := staticCSSPauliFlip D_field u v
  have hσ_mem : σ ∈ realizableSyndromes D_field := by
    rw [realizableSyndromes, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, u, v, rfl⟩
  rcases hermitianPauliZX_isSelfAdjoint_and_sq_eq_one μ.1 μ.2 with ⟨hM_sa, _⟩
  have hM_adj : (hermitianPauliZX μ.1 μ.2)† = hermitianPauliZX μ.1 μ.2 :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hM_sa
  have hM_zx : ∃ z₁ : ℂ, hermitianPauliZX μ.1 μ.2 = z₁ • (weylPauliZ μ.1 * weylPauliX μ.2) := by
    unfold hermitianPauliZX
    split_ifs
    · exact ⟨1, (one_smul ℂ _).symm⟩
    · exact ⟨Complex.I, rfl⟩
  rcases hM_zx with ⟨z₁, hz₁⟩
  rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul γ.1.reverse with ⟨s_loop, hs_loop⟩
  have h_sum_X : (γ.1.reverse.map (fun ξ => ξ.2.1)).sum = a := by
    dsimp [a, worldlinePolymerLoopX]; rw [List.map_reverse, List.sum_reverse]
  have h_sum_Z : (γ.1.reverse.map (fun ξ => ξ.2.2)).sum = b := by
    dsimp [b, worldlinePolymerLoopZ]; rw [List.map_reverse, List.sum_reverse]
  rw [h_sum_X, h_sum_Z] at hs_loop
  have h_loop_zx : worldlinePolymerLoopOp γ = signScalar s_loop • (weylPauliZ a * weylPauliX b) :=
    hs_loop
  have hL_zx : ∃ z₀ : ℂ, L_op = z₀ • (weylPauliZ (μ.1 + a) * weylPauliX (μ.2 + b)) := by
    refine ⟨z₁ * signScalar s_loop * signScalar (∑ p, a p * μ.2 p), ?_⟩
    dsimp [L_op]
    rw [hM_adj, hz₁, h_loop_zx, clm_smul_mul, clm_mul_smul, smul_smul,
      weylPauliZX_mul_weylPauliZX μ.1 μ.2 a b, smul_smul]
  rcases hL_zx with ⟨z₀, hz₀⟩
  have h_tr_eq : ∀ w : ℂ,
      spanningSurfaceSign α σ * hilbertTrace (sys.P0 * (w • L_op)) =
        symplecticPauliSign (u, v) (μ + (a, b)) * hilbertTrace (sys.P0 * (w • L_op)) := by
    intro w
    have h1 := isSpanningCheckSurfaceForPolymer_complex_smul
      D_field sys γ μ α h_span w hσ_mem
    have h2 : hilbertTrace (sys.syndromeProjector σ * (w • L_op)) =
        symplecticPauliSign (u, v) (μ + (a, b)) * hilbertTrace (sys.P0 * (w • L_op)) := by
      dsimp [σ]
      rw [hz₀, smul_smul]
      exact hilbertTrace_syndromeProjector_smul_weylPauliZX_eq
        D_field sys h_sys_checks u v (μ.1 + a) (μ.2 + b) (w * z₀)
    exact h1.symm.trans h2
  rcases h_span.1 with h_ne1 | h_neI
  · have h1 := h_tr_eq 1
    rw [one_smul] at h1
    exact mul_right_cancel₀ h_ne1 h1
  · exact mul_right_cancel₀ h_neI (h_tr_eq Complex.I)

/-- If two Pauli bitstring pairs $(u_1, v_1)$ and $(u_2, v_2)$ produce the same syndrome flip
`staticCSSPauliFlip D_field u₁ v₁ = staticCSSPauliFlip D_field u₂ v₂`, then their difference
`(u₁ + u₂, v₁ + v₂)` belongs to `syndromeClosedPauliFinset D_field`, so for any $(x, y)$ that
commutes with all $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$,
`symplecticPauliSign (u₁, v₁) (x, y) = symplecticPauliSign (u₂, v₂) (x, y)`
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma symplecticPauliSign_congr_of_staticCSSPauliFlip_eq
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    {u₁ v₁ u₂ v₂ x y : BoxSlot3D L q_code → ZMod 2}
    (h_flip : staticCSSPauliFlip D_field u₁ v₁ = staticCSSPauliFlip D_field u₂ v₂)
    (h_comm : ∀ ν ∈ syndromeClosedPauliFinset D_field, symplecticPauliSign ν (x, y) = 1) :
    symplecticPauliSign (u₁, v₁) (x, y) = symplecticPauliSign (u₂, v₂) (x, y) := by
  have h_diff_closed : (u₁ + u₂, v₁ + v₂) ∈ syndromeClosedPauliFinset D_field := by
    rw [syndromeClosedPauliFinset, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change staticCSSPauliFlip D_field (u₁ + u₂) (v₁ + v₂) = fun _ => false
    rw [staticCSSPauliFlip_add D_field u₁ u₂ v₁ v₂, h_flip]
    ext c
    exact bne_self_eq_false (staticCSSPauliFlip D_field u₂ v₂ c)
  have h_mul := (signScalar_symplectic_eq_symplecticPauliSign_and_mul
    (u₁, v₁) (u₁ + u₂, v₁ + v₂) (u₂, v₂) (x, y) (x, y) (x, y)).2.2
  have h_add_cancel : (u₁ + u₂, v₁ + v₂) + (u₂, v₂) = (u₁, v₁) := by
    have h_zmod2 : ∀ a b : ZMod 2, a + b + b = a := by decide
    ext slot
    · exact h_zmod2 (u₁ slot) (u₂ slot)
    · exact h_zmod2 (v₁ slot) (v₂ slot)
  rw [h_add_cancel, h_comm _ h_diff_closed, one_mul] at h_mul
  exact h_mul

/-- For every valid worldline polymer $\gamma$ and every syndrome-closed Pauli pair
$\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$, the stabilizer-part bitstring
`worldlinePolymerLogicalCoset D_field sys C_RCA γ + (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)`
has trivial symplectic commutation sign `1` with $\nu$
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma symplecticPauliSign_coset_add_loop_eq_one
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {γ : WorldlineDysonPolymer L q_code}
    (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ν : PauliBitstringPair L q_code}
    (hν : ν ∈ syndromeClosedPauliFinset D_field) :
    symplecticPauliSign ν
      (worldlinePolymerLogicalCoset D_field sys C_RCA γ +
        (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)) = 1 := by
  rw [(symplecticPauliSign_mul_and_orthogonality D_field).2.1,
    symplecticPauliSign_worldlinePolymerLogicalCoset_eq_loop D_field h_valid sys h_sys_checks hγ hν]
  exact symplecticPauliSign_sq_eq_one ν (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ)

/-- Multi-polymer logical coset character identity: for any list $K$ of valid worldline polymers
and any $\nu \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$, the symplectic character
of the sum of canonical logical cosets `(K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum`
equals the symplectic character of the sum of bare loop bitstrings
`(K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum`
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma symplecticPauliSign_list_sum_worldlinePolymerLogicalCoset_eq_loop
    {L q_code r_0 m_max R_cut : ℕ} [NeZero L]
    {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {ν : PauliBitstringPair L q_code}
    (hν : ν ∈ syndromeClosedPauliFinset D_field) :
    symplecticPauliSign ν (K.map (worldlinePolymerLogicalCoset D_field sys C_RCA)).sum =
      symplecticPauliSign ν
        (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum := by
  have h_mul_right := (symplecticPauliSign_mul_and_orthogonality D_field).2.1
  induction K with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h_mul_right, h_mul_right,
      symplecticPauliSign_worldlinePolymerLogicalCoset_eq_loop D_field h_valid sys h_sys_checks
        (hK_valid hd List.mem_cons_self) hν,
      ih (fun γ hγ => hK_valid γ (List.mem_cons_of_mem hd hγ))]

/-- Net loop bitstring pair sum and bare loop operator product decomposition along any polymer list `K`. -/
lemma list_sum_worldlinePolymerLoop_pair_and_prod_loopOp_eq
    {L q_code : ℕ} (K : WorldlineUrsellCluster L q_code) :
    (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum =
      ((K.map worldlinePolymerLoopX).sum, (K.map worldlinePolymerLoopZ).sum) ∧
    ∃ s : ZMod 2, (K.map worldlinePolymerLoopOp).prod =
      signScalar s •
        (weylPauliZ (K.map worldlinePolymerLoopX).sum *
          weylPauliX (K.map worldlinePolymerLoopZ).sum) := by
  induction K with
  | nil =>
    refine ⟨rfl, 0, ?_⟩
    simp [signScalar_zero, weylPauliZ_zero, weylPauliX_zero]
  | cons hd tl ih =>
    rcases ih with ⟨h_sum_tl, s_tl, hs_tl⟩
    refine ⟨by rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      List.map_cons, List.sum_cons, h_sum_tl]; rfl, ?_⟩
    rcases list_prod_map_worldlineJumpOpZX_eq_signScalar_smul hd.1.reverse with ⟨s_hd, hs_hd⟩
    have h_sum_X : (hd.1.reverse.map (fun ξ => ξ.2.1)).sum = worldlinePolymerLoopX hd := by
      unfold worldlinePolymerLoopX; rw [List.map_reverse, List.sum_reverse]
    have h_sum_Z : (hd.1.reverse.map (fun ξ => ξ.2.2)).sum = worldlinePolymerLoopZ hd := by
      unfold worldlinePolymerLoopZ; rw [List.map_reverse, List.sum_reverse]
    rw [h_sum_X, h_sum_Z] at hs_hd
    have hs_hd' : worldlinePolymerLoopOp hd =
        signScalar s_hd • (weylPauliZ (worldlinePolymerLoopX hd) * weylPauliX (worldlinePolymerLoopZ hd)) :=
      hs_hd
    refine ⟨s_hd + s_tl +
      ∑ p : BoxSlot3D L q_code, (tl.map worldlinePolymerLoopX).sum p * worldlinePolymerLoopZ hd p, ?_⟩
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [hs_hd', hs_tl, clm_smul_mul, clm_mul_smul, weylPauliZX_mul_weylPauliZX,
      smul_smul, smul_smul, ← signScalar_add, ← signScalar_add]

/-- Any list $K$ of valid worldline polymers whose net loop bitstring sum
`(K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum` anticommutes with some
syndrome-closed Pauli operator $\nu_0 \in \mathrm{syndromeClosedPauliFinset}\;D_{\mathrm{field}}$
has vanishing syndrome-sector trace
`hilbertTrace (sys.syndromeProjector σ₀ * (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) = 0`
on every realizable syndrome $\sigma_0 \in \mathrm{realizableSyndromes}\;D_{\mathrm{field}}$
(Part II, Lemma 3.9(i) (`lem:worldline-factorization-time-reversal`)). -/
lemma hilbertTrace_syndromeProjector_prod_worldlinePolymerWeightedLoopOp_eq_zero_of_anticomm
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (K : WorldlineUrsellCluster L q_code)
    (hK_valid : ∀ γ ∈ K, IsValidWorldlinePolymer D_field sys C_RCA R_cut γ)
    {σ₀ : IdxCSS[L, q_code, m_max] → Bool} (hσ₀ : σ₀ ∈ realizableSyndromes D_field)
    {ν₀ : PauliBitstringPair L q_code} (hν₀ : ν₀ ∈ syndromeClosedPauliFinset D_field)
    (h_anti : symplecticPauliSign ν₀
      (K.map (fun γ => (worldlinePolymerLoopX γ, worldlinePolymerLoopZ γ))).sum = -1) :
    hilbertTrace (sys.syndromeProjector σ₀ *
      (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) = 0 := by
  rcases list_sum_worldlinePolymerLoop_pair_and_prod_loopOp_eq K with ⟨h_sum_pair, s_K, hs_K⟩
  rcases list_prod_worldlinePolymerWeightedLoopOp_mul_syndromeProjector_eq
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V K hK_valid hσ₀ with ⟨c_K, _, hc_K⟩
  let a_K := (K.map worldlinePolymerLoopX).sum
  let b_K := (K.map worldlinePolymerLoopZ).sum
  rw [h_sum_pair] at h_anti
  let z_K : ℂ := (∏ i : Fin K.length, c_K i) * signScalar s_K
  let W_K := z_K • (weylPauliZ a_K * weylPauliX b_K)
  have h_idem := ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
  have h_tr_W : hilbertTrace (sys.syndromeProjector σ₀ *
      (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) =
      hilbertTrace (sys.syndromeProjector σ₀ * W_K) := by
    calc hilbertTrace (sys.syndromeProjector σ₀ *
          (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod)
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) *
            (K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod) := by rw [h_idem]
      _ = hilbertTrace (sys.syndromeProjector σ₀ *
            ((K.map (worldlinePolymerWeightedLoopOp D_field sys V)).prod *
              sys.syndromeProjector σ₀)) := by
          rw [mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ₀) _, mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * (W_K * sys.syndromeProjector σ₀)) := by
          rw [hc_K, hs_K, clm_smul_mul, smul_smul]; rfl
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) * W_K) := by
          rw [← mul_assoc (sys.syndromeProjector σ₀) W_K,
            hilbertTrace_mul_comm_aux _ (sys.syndromeProjector σ₀), ← mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * W_K) := by rw [h_idem]
  rw [h_tr_W]
  let U := weylPauliZ ν₀.1 * weylPauliX ν₀.2
  let U_inv := weylPauliX ν₀.2 * weylPauliZ ν₀.1
  have hU_right : U * U_inv = 1 := by
    calc (weylPauliZ ν₀.1 * weylPauliX ν₀.2) * (weylPauliX ν₀.2 * weylPauliZ ν₀.1)
      _ = weylPauliZ ν₀.1 * (weylPauliX ν₀.2 * weylPauliX ν₀.2) * weylPauliZ ν₀.1 := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliX_sq_eq_one ν₀.2, mul_one, weylPauliZ_sq_eq_one ν₀.1]
  have hU_left : U_inv * U = 1 := by
    calc (weylPauliX ν₀.2 * weylPauliZ ν₀.1) * (weylPauliZ ν₀.1 * weylPauliX ν₀.2)
      _ = weylPauliX ν₀.2 * (weylPauliZ ν₀.1 * weylPauliZ ν₀.1) * weylPauliX ν₀.2 := by simp only [mul_assoc]
      _ = 1 := by rw [weylPauliZ_sq_eq_one ν₀.1, mul_one, weylPauliX_sq_eq_one ν₀.2]
  have hU_proj : sys.syndromeProjector σ₀ * U = U * sys.syndromeProjector σ₀ :=
    ((weylPauliZX_comm_checkProj_and_syndromeProjector_of_syndromeClosed
      D_field sys h_sys_checks hν₀).2.1 σ₀).symm.eq
  have h_zx_comm : (weylPauliZ a_K * weylPauliX b_K) * U =
      ((symplecticPauliSign ν₀ (a_K, b_K) : ℝ) : ℂ) • (U * (weylPauliZ a_K * weylPauliX b_K)) := by
    dsimp [U]; rw [weylPauliZX_comm_signScalar a_K b_K ν₀.1 ν₀.2,
      ← (signScalar_symplectic_eq_symplecticPauliSign_and_mul ν₀ ν₀ ν₀ (a_K, b_K) (a_K, b_K) (a_K, b_K)).1]
    exact congrArg (· • ((weylPauliZ ν₀.1 * weylPauliX ν₀.2) * (weylPauliZ a_K * weylPauliX b_K)))
      (congrArg signScalar (Finset.sum_congr rfl fun q _ => by ring))
  have hW_comm : W_K * U = ((symplecticPauliSign ν₀ (a_K, b_K) : ℝ) : ℂ) • (U * W_K) := by
    dsimp [W_K]; rw [clm_smul_mul, h_zx_comm, clm_mul_smul, smul_comm]
  have h_neg : hilbertTrace (sys.syndromeProjector σ₀ * W_K) =
      -hilbertTrace (sys.syndromeProjector σ₀ * W_K) := by
    calc hilbertTrace (sys.syndromeProjector σ₀ * W_K)
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * (W_K * U)) * U_inv) := by
          rw [mul_assoc (sys.syndromeProjector σ₀) (W_K * U) U_inv, mul_assoc W_K U U_inv, hU_right, mul_one]
      _ = symplecticPauliSign ν₀ (a_K, b_K) *
            hilbertTrace (((sys.syndromeProjector σ₀ * U) * W_K) * U_inv) := by
          rw [hW_comm, clm_mul_smul, clm_smul_mul,
            (hilbertTrace_add_and_complex_smul_decomp _ 0 0 0 (symplecticPauliSign ν₀ (a_K, b_K)) 0).2.1]
          simp only [mul_assoc]
      _ = -hilbertTrace ((U * (sys.syndromeProjector σ₀ * W_K)) * U_inv) := by
          rw [h_anti, hU_proj, mul_assoc U (sys.syndromeProjector σ₀) W_K, neg_one_mul]
      _ = -hilbertTrace (sys.syndromeProjector σ₀ * W_K) := by
          rw [hilbertTrace_mul_comm_aux (U * (sys.syndromeProjector σ₀ * W_K)) U_inv,
            ← mul_assoc U_inv U, hU_left, one_mul]
  linarith

/-- Vacuum-trace representation of `worldlinePolymerLoopAmplitude` for any valid worldline polymer
$\gamma$ at cutoff $R_{\mathrm{cut}} \le L^*$
(Part II, Lemma 2.8(i)–(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma exists_collar_scalar_worldlinePolymerLoopAmplitude_and_weightedLoopOp_eq
    {L q_code r_0 m_max L_star R_cut : ℕ} [NeZero L] {C_RCA : ℝ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : SysCSS[L, q_code, m_max])
    (h_sys_checks : ∀ idx, sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_tqo1 : SatisfiesTQO1 sys L_star) (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_RCA)
    (hR_le : R_cut ≤ L_star) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code]))
    (γ : WorldlineDysonPolymer L q_code) (hγ : IsValidWorldlinePolymer D_field sys C_RCA R_cut γ) :
    let μ := worldlinePolymerLogicalCoset D_field sys C_RCA γ
    let L_op := (hermitianPauliZX μ.1 μ.2)† * worldlinePolymerLoopOp γ
    ∃ C_γ : (IdxCSS[L, q_code, m_max] → Bool) → ℂ,
      (∀ σ₁ σ₂ : IdxCSS[L, q_code, m_max] → Bool,
        (∀ c ∈ worldlinePolymerNativeCollar sys C_RCA γ, σ₁ c = σ₂ c) → C_γ σ₁ = C_γ σ₂) ∧
      (∀ σ₀ ∈ realizableSyndromes D_field,
        worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀ =
          C_γ σ₀ • (worldlinePolymerLoopOp γ * sys.syndromeProjector σ₀) ∧
        worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
          (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀) =
          hilbertTrace (sys.P0 * (C_γ σ₀ • L_op)) / hilbertTrace sys.P0) := by
  intro μ L_op
  rcases exists_collar_scalar_worldlinePolymerWeightedLoopOp_and_commute_loopOp
      D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V hγ with ⟨_, C_γ, hC_ag, hC_act⟩
  have hV_supp : ∀ r ∈ Finset.Icc 1 (min R_cut L), ∀ A ∈ boxCubes 3 L r,
      IsSupportedOn (SiteCSS[L, q_code]) A (V.term r A) :=
    fun r hr A hA => V.is_supported r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_right R_cut L)⟩) A hA
  have h_span := (isSpanningCheckSurfaceForPolymer_of_isValidWorldlinePolymer
    D_field h_valid sys h_sys_checks γ hγ).2
  let α := worldlinePolymerSpanningSurface D_field sys C_RCA γ
  refine ⟨C_γ, hC_ag, fun σ₀ hσ₀ => ⟨(hC_act σ₀ hσ₀).1, ?_⟩⟩
  have h_amp := spanningSurfaceSign_mul_worldlinePolymerLoopAmplitude_eq_of_valid
    D_field h_valid sys h_sys_checks h_tqo1 h_tqo2 hR_le V hV_supp γ hγ hσ₀
  have h_idem := ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ₀).1
  have h_tr_W : hilbertTrace (sys.syndromeProjector σ₀ *
      ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ)) =
      hilbertTrace (sys.syndromeProjector σ₀ * (C_γ σ₀ • L_op)) := by
    calc hilbertTrace (sys.syndromeProjector σ₀ *
          ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ))
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) *
            ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ)) := by rw [h_idem]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * ((hermitianPauliZX μ.1 μ.2)† *
            (worldlinePolymerWeightedLoopOp D_field sys V γ * sys.syndromeProjector σ₀))) := by
          rw [mul_assoc, hilbertTrace_mul_comm_aux (sys.syndromeProjector σ₀) _, mul_assoc, mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * ((C_γ σ₀ • L_op) * sys.syndromeProjector σ₀)) := by
          rw [(hC_act σ₀ hσ₀).1, clm_mul_smul,
            ← mul_assoc ((hermitianPauliZX μ.1 μ.2)†) (worldlinePolymerLoopOp γ) (sys.syndromeProjector σ₀),
            ← clm_smul_mul]
      _ = hilbertTrace ((sys.syndromeProjector σ₀ * sys.syndromeProjector σ₀) * (C_γ σ₀ • L_op)) := by
          rw [← mul_assoc (sys.syndromeProjector σ₀) (C_γ σ₀ • L_op),
            hilbertTrace_mul_comm_aux _ (sys.syndromeProjector σ₀), ← mul_assoc]
      _ = hilbertTrace (sys.syndromeProjector σ₀ * (C_γ σ₀ • L_op)) := by rw [h_idem]
  have h_span_c := isSpanningCheckSurfaceForPolymer_complex_smul D_field sys γ μ α h_span (C_γ σ₀) hσ₀
  have h_tr_denom := (hilbertTrace_syndromeProjector_eq_P0_of_realizableSyndromes
    D_field h_valid sys h_sys_checks hσ₀).1
  have h_sign_sq := (spanningSurfaceSign_insert_and_identities α σ₀).2.1
  calc worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
        (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀)
    _ = spanningSurfaceSign α σ₀ * (spanningSurfaceSign α σ₀ *
          worldlinePolymerLoopAmplitude D_field sys C_RCA V γ
            (restrictSyndromeToCollar (worldlinePolymerNativeCollar sys C_RCA γ) σ₀)) := by
        rw [← mul_assoc, h_sign_sq, one_mul]
    _ = spanningSurfaceSign α σ₀ * (hilbertTrace (sys.syndromeProjector σ₀ *
          ((hermitianPauliZX μ.1 μ.2)† * worldlinePolymerWeightedLoopOp D_field sys V γ)) /
          hilbertTrace (sys.syndromeProjector σ₀)) := by rw [h_amp]
    _ = (spanningSurfaceSign α σ₀ * spanningSurfaceSign α σ₀) *
          (hilbertTrace (sys.P0 * (C_γ σ₀ • L_op)) / hilbertTrace sys.P0) := by
        rw [h_tr_W, h_span_c, h_tr_denom]; ring
    _ = hilbertTrace (sys.P0 * (C_γ σ₀ • L_op)) / hilbertTrace sys.P0 := by rw [h_sign_sq, one_mul]

/-- Self-adjointness of `worldlineSyndromeShiftBlockOp` and time-reversal adjoint identity
`worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2) = (worldlinePolymerWeightedLoopOp D_field sys V γ)†`
(Part II, Lemma 3.9(ii) (`lem:worldline-factorization-time-reversal`)). -/
lemma worldlineSyndromeShiftBlockOp_isSelfAdjoint_and_reverse_weightedLoopOp
    {L q_code r_0 m_max : ℕ} (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : SysCSS[L, q_code, m_max]) (V : QuasiLocalPerturbation 3 L (SiteCSS[L, q_code])) :
    (∀ ξ : WorldlineJumpMonomer L q_code,
      (worldlineSyndromeShiftBlockOp D_field sys V ξ)† = worldlineSyndromeShiftBlockOp D_field sys V ξ) ∧
    (∀ γ : WorldlineDysonPolymer L q_code,
      worldlinePolymerWeightedLoopOp D_field sys V (γ.1.reverse, γ.2) =
        (worldlinePolymerWeightedLoopOp D_field sys V γ)†) := by
  have hB : ∀ ξ : WorldlineJumpMonomer L q_code,
      (worldlineSyndromeShiftBlockOp D_field sys V ξ)† = worldlineSyndromeShiftBlockOp D_field sys V ξ := fun ξ => by
    rw [← ContinuousLinearMap.star_eq_adjoint]; unfold worldlineSyndromeShiftBlockOp; (try dsimp only); rw [star_sum]
    let δ := staticCSSPauliFlip D_field ξ.2.1 ξ.2.2
    have h_inv : ∀ σ, syndromeXor δ (syndromeXor δ σ) = σ := fun σ => by
      ext c; unfold syndromeXor; cases δ c <;> cases σ c <;> rfl
    have h_off : star (pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2) = pauliOffDiagonalTerm sys V ξ.1.1 ξ.1.2 := by
      rw [ContinuousLinearMap.star_eq_adjoint]; unfold pauliOffDiagonalTerm
      rw [map_sub, ContinuousLinearMap.isSelfAdjoint_iff'.mp (V.is_selfAdjoint ξ.1.1 ξ.1.2),
        ContinuousLinearMap.isSelfAdjoint_iff'.mp
          (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint ξ.1.1 ξ.1.2)).1]
    have hP : ∀ σ, star (sys.syndromeProjector σ) = sys.syndromeProjector σ :=
      fun σ => ((PerturbedThermalBarrier.syndrome_resolution_indexed sys).2.1 σ).2.star_eq
    refine Finset.sum_nbij (syndromeXor δ)
      (fun σ hσ => syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field ξ.2.1 ξ.2.2 σ hσ)
      (fun σ₁ _ σ₂ _ h => by rw [← h_inv σ₁, h, h_inv σ₂])
      (fun σ hσ => ⟨syndromeXor δ σ,
        syndromeXor_staticCSSPauliFlip_mem_realizableSyndromes D_field ξ.2.1 ξ.2.2 σ hσ, h_inv σ⟩)
      (fun σ _ => by rw [star_mul, star_mul, hP, hP, h_off, h_inv σ, mul_assoc])
  refine ⟨hB, fun γ => ?_⟩
  unfold worldlinePolymerWeightedLoopOp; (try dsimp only)
  suffices h_list : ∀ l : List (WorldlineJumpMonomer L q_code),
      (l.reverse.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod =
        ((l.map (worldlineSyndromeShiftBlockOp D_field sys V)).prod)† from h_list γ.1.reverse
  intro l; induction l with
  | nil => simp [← ContinuousLinearMap.star_eq_adjoint]
  | cons hd tl ih =>
    rw [List.reverse_cons, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, List.map_cons, List.prod_cons,
      ← ContinuousLinearMap.star_eq_adjoint, star_mul, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.star_eq_adjoint, ← ih, hB hd]

end DirectWorldlineCluster
end
