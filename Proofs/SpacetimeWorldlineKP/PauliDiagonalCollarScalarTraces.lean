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

import Proofs.SpacetimeWorldlineKP.SpacetimeCollarPartitionSplit

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

namespace SpacetimeWorldlineKP

/-!
# Collar-Clean Annihilation, TQO-2 Local Scalar Families, and Realizable Sector Traces

Proves that witness-collar perturbations vanish on collar-clean syndrome sectors (`IsCollarCleanAround`, `collarWitnessPart_mul_syndromeProjector_eq_zero_of_clean_collar`). Uses linear TQO-2 and RCA-1 check localization to represent Pauli-diagonal cube terms as local check-collar scalar functions (`IsLocalCollarScalarFamily`, `exists_local_collar_scalar_family_of_tqo2`) and derives the realizable sector-energy partition trace formula (`boltzmann_trace_and_partitionZ_eq_realizable_sectorEnergy_sum`).

## References

* Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.5 (`prop:witness-coset-reduction`)
-/

/-- **Collar-Clean Separation Predicate (`IsCollarCleanAround`)** -/
def IsCollarCleanAround {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert : ℕ) (S : Finset (StaticCSSCheckIdx L q_code m_max))
    (σ : StaticCSSCheckIdx L q_code m_max → Bool) : Prop :=
  ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
    ¬Disjoint (rcaCollarChecks sys C_rca r A) S →
    ∀ c ∈ rcaCollarChecks sys C_rca r A, σ c = false

/-- **Exact Annihilation of `collarWitnessPart` on Collar-Clean Syndromes** -/
theorem collarWitnessPart_mul_syndromeProjector_eq_zero_of_clean_collar
    {L q_code m_max R_pert : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    {C_rca : ℝ} (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (h_cover : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      HasLocalCheckViolationCover sys (syndromePinchOp sys (V.term r A))
        (rcaCollarChecks sys C_rca r A) (e_loc r A))
    {S : Finset (StaticCSSCheckIdx L q_code m_max)}
    {σ_spec : StaticCSSCheckIdx L q_code m_max → Bool}
    (h_clean : IsCollarCleanAround sys C_rca R_pert S σ_spec) :
    collarWitnessPart sys C_rca R_pert (pauliDiagonalShiftedTerm sys V e_loc) S *
      sys.syndromeProjector σ_spec = 0 := by
  unfold collarWitnessPart; rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.sum_mul]; refine Finset.sum_eq_zero fun A hA => ?_
  rcases Finset.mem_filter.mp hA with ⟨hA_cube, h_not_disj⟩
  exact (h_cover r hr A hA_cube).2.2 σ_spec (h_clean r hr A hA_cube h_not_disj)

/-- **Exact Commutativity of `collarSpectatorPart` with Local Operators** -/
theorem commute_collarSpectatorPart_of_isSupportedOn_disjoint_collar
    {L q_code m_max R_pert : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    {C_rca : ℝ} (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (h_supp : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
        (pauliDiagonalShiftedTerm sys V e_loc r A))
    {S : Finset (StaticCSSCheckIdx L q_code m_max)} {S_w : Finset (Box3D L)}
    {U : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hU_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) S_w U)
    (h_disj : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      Disjoint (rcaCollarChecks sys C_rca r A) S → Disjoint S_w A) :
    Commute U (collarSpectatorPart sys C_rca R_pert (pauliDiagonalShiftedTerm sys V e_loc) S) := by
  unfold collarSpectatorPart
  refine Commute.sum_right _ _ _ fun r hr => Commute.sum_right _ _ _ fun A hA => ?_
  rcases Finset.mem_filter.mp hA with ⟨hA_cube, hA_disj⟩
  exact KMSPinchedGibbs.commute_of_isSupportedOn_disjoint (h_disj r hr A hA_cube hA_disj)
    hU_supp (h_supp r hr A hA_cube)

/-- **Local Collar Scalar Eigenvalue Family (`IsLocalCollarScalarFamily`)** -/
def IsLocalCollarScalarFamily {L q_code r_0 m_max : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (R_pert : ℕ) (C_rca J : ℝ)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ) : Prop :=
  ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
    ((∀ σ ∈ realizableSyndromes D_field,
        pauliDiagonalShiftedTerm sys V e_loc r A * sys.syndromeProjector σ =
          ((d_loc r A σ : ℝ) : ℂ) • sys.syndromeProjector σ) ∧
      ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool, |d_loc r A σ| ≤ 2 * J) ∧
    (∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
      (∀ c ∈ rcaCollarChecks sys C_rca r A, σ c = false) → d_loc r A σ = 0) ∧
    (∀ σ₁ σ₂ : StaticCSSCheckIdx L q_code m_max → Bool,
      (∀ c ∈ rcaCollarChecks sys C_rca r A, σ₁ c = σ₂ c) →
      d_loc r A σ₁ = d_loc r A σ₂)

/-- **Classical Perturbed Pauli-Diagonal Sector Energy (`pauliDiagonalSectorEnergy`)** -/
def pauliDiagonalSectorEnergy {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (R_pert : ℕ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (σ : StaticCSSCheckIdx L q_code m_max → Bool) : ℝ :=
  sys.syndromeEnergy σ +
    ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ

/-- **Exact Cancellation of Spectator Cube Energies Outside an Active Check Set** -/
theorem pauliDiagonalSectorEnergy_sub_eq_collarWitnessSum_of_spectator_agree
    {L q_code r_0 m_max R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    {C_rca J : ℝ} (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc)
    {S_act : Finset (StaticCSSCheckIdx L q_code m_max)}
    {σ σ_spec : StaticCSSCheckIdx L q_code m_max → Bool}
    (h_agree : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      Disjoint (rcaCollarChecks sys C_rca r A) S_act →
      ∀ c ∈ rcaCollarChecks sys C_rca r A, σ c = σ_spec c) :
    pauliDiagonalSectorEnergy sys R_pert d_loc σ -
      pauliDiagonalSectorEnergy sys R_pert d_loc σ_spec =
      (sys.syndromeEnergy σ - sys.syndromeEnergy σ_spec) +
        ∑ r ∈ Finset.Icc 1 (min R_pert L),
          ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) S_act),
            (d_loc r A σ - d_loc r A σ_spec) := by
  unfold pauliDiagonalSectorEnergy
  have h_sum_eq :
      (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ) -
        (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ_spec) =
      ∑ r ∈ Finset.Icc 1 (min R_pert L),
        ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) S_act),
          (d_loc r A σ - d_loc r A σ_spec) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun r hr => ?_
    rw [← Finset.sum_sub_distrib,
      ← Finset.sum_filter_add_sum_filter_not (boxCubes 3 L r)
        (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) S_act)]
    have h_spec_zero :
        ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬¬Disjoint (rcaCollarChecks sys C_rca r A) S_act),
          (d_loc r A σ - d_loc r A σ_spec) = 0 := by
      refine Finset.sum_eq_zero fun A hA => ?_
      rcases Finset.mem_filter.mp hA with ⟨hA_cube, h_not_not⟩
      have h_eq := (h_scalar r hr A hA_cube).2.2 σ σ_spec
        (h_agree r hr A hA_cube (not_not.mp h_not_not))
      linarith
    rw [h_spec_zero, add_zero]
  linarith

/-- **Exact Sector Energy Peeling Identity Under Clean Collar & Spectator Agreement** -/
theorem pauliDiagonalSectorEnergy_sub_eq_of_clean_collar_and_spectator_agree
    {L q_code r_0 m_max R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    {C_rca J : ℝ} (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc)
    {S_act : Finset (StaticCSSCheckIdx L q_code m_max)}
    {σ σ_spec : StaticCSSCheckIdx L q_code m_max → Bool}
    (h_clean : IsCollarCleanAround sys C_rca R_pert S_act σ_spec)
    (h_agree : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      Disjoint (rcaCollarChecks sys C_rca r A) S_act →
      ∀ c ∈ rcaCollarChecks sys C_rca r A, σ c = σ_spec c) :
    pauliDiagonalSectorEnergy sys R_pert d_loc σ -
      pauliDiagonalSectorEnergy sys R_pert d_loc σ_spec =
      (sys.syndromeEnergy σ - sys.syndromeEnergy σ_spec) +
        ∑ r ∈ Finset.Icc 1 (min R_pert L),
          ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) S_act),
            d_loc r A σ := by
  rw [pauliDiagonalSectorEnergy_sub_eq_collarWitnessSum_of_spectator_agree
    D_field sys V e_loc d_loc h_scalar h_agree]
  congr 1; refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun A hA => ?_
  rcases Finset.mem_filter.mp hA with ⟨hA_cube, h_not_disj⟩
  have h_zero := (h_scalar r hr A hA_cube).2.1 σ_spec (h_clean r hr A hA_cube h_not_disj)
  linarith

/-- **Three-Quarters Inverse Temperature Rate Calibration** -/
theorem three_quarters_beta_ge_target_witness_rate
    {β_c β : ℝ} (hβc_ge : 16 ≤ β_c) (hβ : β > β_c) (n : ℕ) :
    β_c / 2 + min (β - β_c) 1 + 7 / 2 ≤ (3 / 4 : ℝ) * β ∧
    β_c / 2 + min (β - β_c) 1 + 3 ≤ (3 / 4 : ℝ) * β ∧
    Real.exp (-((3 / 4 : ℝ) * β * (n : ℝ))) ≤
      Real.exp (-((β_c / 2 + min (β - β_c) 1 + 3) * (n : ℝ))) := by
  have h_rate35 : β_c / 2 + min (β - β_c) 1 + 7 / 2 ≤ (3 / 4 : ℝ) * β := by
    rcases le_total (β - β_c) 1 with h_le | h_ge
    · rw [min_eq_left h_le]; linarith
    · rw [min_eq_right h_ge]; linarith
  have h_rate3 : β_c / 2 + min (β - β_c) 1 + 3 ≤ (3 / 4 : ℝ) * β := by linarith
  refine ⟨h_rate35, h_rate3, Real.exp_le_exp.mpr ?_⟩
  have h_mul := mul_le_mul_of_nonneg_right h_rate3 (Nat.cast_nonneg n)
  linarith

/-! ## 1. Operator-to-Scalar Reduction Lemmas (Steps 3.1 & 3.2) -/

private lemma conj_pauli_sa_and_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {Z X D : E →L[ℂ] E} {B : ℝ}
    (hZ_sa : IsSelfAdjoint Z) (hZ_sq : Z * Z = 1) (hX_sa : IsSelfAdjoint X) (hX_sq : X * X = 1)
    (hD_sa : IsSelfAdjoint D) (hD_norm : ‖D‖ ≤ B) :
    (Z * X) * (X * Z) = 1 ∧ (X * Z) * (Z * X) = 1 ∧
    IsSelfAdjoint ((X * Z) * D * (Z * X)) ∧ ‖(X * Z) * D * (Z * X)‖ ≤ B := by
  have h1 : (Z * X) * (X * Z) = 1 := by
    calc (Z * X) * (X * Z) = Z * (X * X) * Z := by simp only [mul_assoc]
      _ = 1 := by rw [hX_sq, mul_one, hZ_sq]
  have h2 : (X * Z) * (Z * X) = 1 := by
    calc (X * Z) * (Z * X) = X * (Z * Z) * X := by simp only [mul_assoc]
      _ = 1 := by rw [hZ_sq, mul_one, hX_sq]
  have h_sa : IsSelfAdjoint ((X * Z) * D * (Z * X)) := by
    rw [isSelfAdjoint_iff, star_mul, star_mul, star_mul, star_mul,
      hZ_sa.star_eq, hX_sa.star_eq, hD_sa.star_eq]; simp only [mul_assoc]
  have hZ_n := norm_le_one_of_isSelfAdjoint_and_mul_self_eq_one hZ_sa hZ_sq
  have hX_n := norm_le_one_of_isSelfAdjoint_and_mul_self_eq_one hX_sa hX_sq
  have hZX_n : ‖Z * X‖ ≤ 1 :=
    le_trans (norm_mul_le Z X) (by rw [← mul_one (1 : ℝ)]; exact mul_le_mul hZ_n hX_n (norm_nonneg X) zero_le_one)
  have hXZ_n : ‖X * Z‖ ≤ 1 :=
    le_trans (norm_mul_le X Z) (by rw [← mul_one (1 : ℝ)]; exact mul_le_mul hX_n hZ_n (norm_nonneg Z) zero_le_one)
  have hD1 : ‖(X * Z) * D‖ ≤ ‖D‖ :=
    le_trans (norm_mul_le (X * Z) D)
      (le_trans (mul_le_mul_of_nonneg_right hXZ_n (norm_nonneg D)) (by rw [one_mul]))
  have hD2 : ‖(X * Z) * D * (Z * X)‖ ≤ ‖(X * Z) * D‖ :=
    le_trans (norm_mul_le ((X * Z) * D) (Z * X))
      (le_trans (mul_le_mul_of_nonneg_left hZX_n (norm_nonneg ((X * Z) * D))) (by rw [mul_one]))
  exact ⟨h1, h2, h_sa, le_trans hD2 (le_trans hD1 hD_norm)⟩
private lemma conj_comm_P0_of_intertwine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {U U_dag D P0 P_τ : E →L[ℂ] E} (hU_Udag : U * U_dag = 1) (hUdag_U : U_dag * U = 1)
    (hU_P0 : U * P0 = P_τ * U) (hD_τ : Commute D P_τ) : Commute (U_dag * D * U) P0 := by
  have hP0_Udag : P0 * U_dag = U_dag * P_τ := by
    calc P0 * U_dag = U_dag * (U * P0) * U_dag := by rw [← mul_assoc U_dag U, hUdag_U, one_mul]
      _ = U_dag * P_τ * (U * U_dag) := by rw [hU_P0]; simp only [mul_assoc]
      _ = U_dag * P_τ := by rw [hU_Udag, mul_one]
  rw [commute_iff_eq]
  calc U_dag * D * U * P0 = U_dag * D * (U * P0) := by simp only [mul_assoc]
    _ = U_dag * (D * P_τ) * U := by rw [hU_P0]; simp only [mul_assoc]
    _ = (U_dag * P_τ) * D * U := by rw [hD_τ.eq]; simp only [mul_assoc]
    _ = P0 * (U_dag * D * U) := by rw [← hP0_Udag]; simp only [mul_assoc]
private lemma conj_eigenvalue_of_clean_ann {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {U U_dag D P_δ P_σ localGroundProj : E →L[ℂ] E} {c : ℝ} (hU_Udag : U * U_dag = 1)
    (hP_clean : localGroundProj * P_δ = P_δ) (hc_ann : (U_dag * D * U - ((c : ℝ) : ℂ) • 1) * localGroundProj = 0)
    (h_inter_δ : U * P_δ = P_σ * U) : D * P_σ = ((c : ℝ) : ℂ) • P_σ := by
  have h_ann_δ : (U_dag * D * U - ((c : ℝ) : ℂ) • 1) * P_δ = 0 := by
    rw [← hP_clean, ← mul_assoc, hc_ann, zero_mul]
  have h_Dconj_δ : (U_dag * D * U) * P_δ = ((c : ℝ) : ℂ) • P_δ := by
    rw [sub_mul, smul_mul_assoc, one_mul, sub_eq_zero] at h_ann_δ; exact h_ann_δ
  have h_U_δ_Udag : U * P_δ * U_dag = P_σ := by rw [h_inter_δ, mul_assoc, hU_Udag, mul_one]
  calc D * P_σ = (U * U_dag) * D * (U * P_δ * U_dag) := by rw [hU_Udag, one_mul, h_U_δ_Udag]
    _ = U * ((U_dag * D * U) * P_δ) * U_dag := by simp only [mul_assoc]
    _ = U * (((c : ℝ) : ℂ) • P_δ) * U_dag := by rw [h_Dconj_δ]
    _ = ((c : ℝ) : ℂ) • (U * P_δ * U_dag) := by rw [mul_smul_comm, smul_mul_assoc]
    _ = ((c : ℝ) : ℂ) • P_σ := by rw [h_U_δ_Udag]
private lemma isSelfAdjoint_sub_real_smul_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {M : E →L[ℂ] E}
    (hM : IsSelfAdjoint M) (e : ℝ) : IsSelfAdjoint (M - ((e : ℝ) : ℂ) • 1) :=
  hM.sub (isSelfAdjoint_real_smul e (IsSelfAdjoint.one _))
private lemma zero_eq_zero_smul_clm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (P : E →L[ℂ] E) : (0 : E →L[ℂ] E) = ((0 : ℝ) : ℂ) • P := by simp
private lemma hdiag_mul_projector_eq_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {H0 P_diag P : E →L[ℂ] E} {E_vac E_sum e0 d_sum : ℝ}
    (h_H0 : H0 * P = ((e0 : ℝ) : ℂ) • P)
    (h_shift : (P_diag - ((E_sum : ℝ) : ℂ) • 1) * P = ((d_sum : ℝ) : ℂ) • P) :
    (H0 + P_diag - ((E_vac : ℝ) : ℂ) • 1) * P = (((e0 + d_sum + (E_sum - E_vac) : ℝ) : ℂ)) • P := by
  have h_decomp : H0 + P_diag - ((E_vac : ℝ) : ℂ) • (1 : E →L[ℂ] E) =
      H0 + (P_diag - ((E_sum : ℝ) : ℂ) • 1) + (((E_sum - E_vac : ℝ) : ℂ)) • 1 := by
    ext x; simp [sub_smul]; abel
  rw [h_decomp, add_mul, add_mul, h_H0, h_shift, smul_mul_assoc, one_mul]; ext x; simp [add_smul]
private def restrictSlotChainToRegion {L q_code : ℕ} (A : Finset (Box3D L))
    (a : BoxSlot3D L q_code → ZMod 2) : BoxSlot3D L q_code → ZMod 2 :=
  fun p => if p.1 ∈ A then a p else 0
private lemma eq_add_restrictSlotChainToRegion {L q_code : ℕ}
    (A : Finset (Box3D L)) (a : BoxSlot3D L q_code → ZMod 2) :
    a = restrictSlotChainToRegion A a + restrictSlotChainToRegion (Finset.univ \ A) a := by
  ext p; dsimp [restrictSlotChainToRegion]; by_cases hp : p.1 ∈ A <;> simp [hp]
private lemma isSupportedOn_weylPauliZ_restrictSlotChainToRegion {L q_code : ℕ}
    (A : Finset (Box3D L)) (a : BoxSlot3D L q_code → ZMod 2) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
      (weylPauliZ (restrictSlotChainToRegion A a)) := by
  let phaseA (α : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A) : ℂ :=
    pauliPhase (fun p : ↥A × Fin q_code => a (p.1.1, p.2))
      (fun p : ↥A × Fin q_code => boolToZMod2 (α p.1 p.2))
  refine ⟨LinearMap.toContinuousLinearMap
    { toFun := fun ψ_A => WithLp.toLp 2 (fun α => phaseA α * ψ_A.ofLp α)
      map_add' := fun ψ₁ ψ₂ => by
        ext α; change phaseA α * (ψ₁.ofLp α + ψ₂.ofLp α) =
          phaseA α * ψ₁.ofLp α + phaseA α * ψ₂.ofLp α; ring
      map_smul' := fun c ψ => by
        ext α; change phaseA α * (c * ψ.ofLp α) = c * (phaseA α * ψ.ofLp α); ring }, ?_⟩
  ext ψ σ; change pauliPhase (restrictSlotChainToRegion A a) (codeConfigBits σ) * ψ.ofLp σ =
    phaseA (restrictConfig A σ) * ψ.ofLp (spliceConfig A (restrictConfig A σ) σ)
  rw [_root_.spliceConfig_restrictConfig]; congr 1; dsimp [pauliPhase, phaseA]
  have h_sum : (∑ p : BoxSlot3D L q_code, restrictSlotChainToRegion A a p * codeConfigBits σ p) =
      ∑ p : ↥A × Fin q_code, a (p.1.1, p.2) * boolToZMod2 (restrictConfig A σ p.1 p.2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_subset (Finset.subset_univ A)]
    · rw [← Finset.sum_attach A]; refine Finset.sum_congr rfl fun vA _ => Finset.sum_congr rfl fun s _ => ?_
      simp [restrictSlotChainToRegion, codeConfigBits, restrictConfig, vA.2]
    · intro v _ hv; refine Finset.sum_eq_zero fun s _ => ?_; simp [restrictSlotChainToRegion, hv]
  rw [h_sum]
private lemma isSupportedOn_weylPauliX_restrictSlotChainToRegion {L q_code : ℕ}
    (A : Finset (Box3D L)) (b : BoxSlot3D L q_code → ZMod 2) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
      (weylPauliX (restrictSlotChainToRegion A b)) := by
  let flipSub : LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A →
      LocalConfig (UniformSite3D L (CodeSlotConfig q_code)) A :=
    fun α vA s => xor (α vA s) (zmod2ToBool (b (vA.1, s)))
  refine ⟨LinearMap.toContinuousLinearMap
    { toFun := fun ψ_A => WithLp.toLp 2 (fun α => ψ_A.ofLp (flipSub α))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }, ?_⟩
  ext ψ σ; change ψ.ofLp (flipCodeConfig (restrictSlotChainToRegion A b) σ) =
    ψ.ofLp (spliceConfig A (flipSub (restrictConfig A σ)) σ)
  refine congrArg ψ.ofLp (funext fun v => funext fun s => ?_)
  dsimp [flipCodeConfig, spliceConfig, flipSub, restrictConfig, restrictSlotChainToRegion]
  by_cases hv : v ∈ A <;> simp [hv, zmod2ToBool]
private lemma isSupportedOn_weylPauliZ_conj {L q_code : ℕ}
    (A : Finset (Box3D L)) (a : BoxSlot3D L q_code → ZMod 2)
    {D : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hD : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A D) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (weylPauliZ a * D * weylPauliZ a) := by
  let a_in := restrictSlotChainToRegion A a; let a_out := restrictSlotChainToRegion (Finset.univ \ A) a
  have hZ_in := isSupportedOn_weylPauliZ_restrictSlotChainToRegion A a
  have hZ_out := isSupportedOn_weylPauliZ_restrictSlotChainToRegion (Finset.univ \ A) a
  have h_disj : Disjoint (Finset.univ \ A) A := by
    rw [Finset.disjoint_left]; intro x hx hxA; exact (Finset.mem_sdiff.mp hx).2 hxA
  have h_comm : Commute (weylPauliZ a_out) D :=
    KMSPinchedGibbs.commute_of_isSupportedOn_disjoint h_disj hZ_out hD
  have ha : weylPauliZ a = weylPauliZ a_in * weylPauliZ a_out := by
    conv_lhs => rw [eq_add_restrictSlotChainToRegion A a]
    exact weylPauliZ_add a_in a_out
  have ha' : weylPauliZ a = weylPauliZ a_out * weylPauliZ a_in := by rw [ha, (weylPauliZ_comm a_in a_out).eq]
  have h_eq : weylPauliZ a * D * weylPauliZ a = weylPauliZ a_in * D * weylPauliZ a_in := by
    calc weylPauliZ a * D * weylPauliZ a
      _ = (weylPauliZ a_in * weylPauliZ a_out) * D * (weylPauliZ a_out * weylPauliZ a_in) := by rw [← ha, ← ha']
      _ = weylPauliZ a_in * (weylPauliZ a_out * D) * (weylPauliZ a_out * weylPauliZ a_in) := by simp only [mul_assoc]
      _ = weylPauliZ a_in * D * (weylPauliZ a_out * weylPauliZ a_out) * weylPauliZ a_in := by
        rw [h_comm.eq]; simp only [mul_assoc]
      _ = weylPauliZ a_in * D * weylPauliZ a_in := by rw [weylPauliZ_sq_eq_one, mul_one]
  rw [h_eq]; exact _root_.isSupportedOn_mul A (_root_.isSupportedOn_mul A hZ_in hD) hZ_in
private lemma isSupportedOn_weylPauliX_conj {L q_code : ℕ}
    (A : Finset (Box3D L)) (b : BoxSlot3D L q_code → ZMod 2)
    {D : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hD : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A D) :
    IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (weylPauliX b * D * weylPauliX b) := by
  let b_in := restrictSlotChainToRegion A b; let b_out := restrictSlotChainToRegion (Finset.univ \ A) b
  have hX_in := isSupportedOn_weylPauliX_restrictSlotChainToRegion A b
  have hX_out := isSupportedOn_weylPauliX_restrictSlotChainToRegion (Finset.univ \ A) b
  have h_disj : Disjoint (Finset.univ \ A) A := by
    rw [Finset.disjoint_left]; intro x hx hxA; exact (Finset.mem_sdiff.mp hx).2 hxA
  have h_comm : Commute (weylPauliX b_out) D :=
    KMSPinchedGibbs.commute_of_isSupportedOn_disjoint h_disj hX_out hD
  have hb : weylPauliX b = weylPauliX b_in * weylPauliX b_out := by
    conv_lhs => rw [eq_add_restrictSlotChainToRegion A b]
    exact weylPauliX_add b_in b_out
  have hb' : weylPauliX b = weylPauliX b_out * weylPauliX b_in := by rw [hb, (weylPauliX_comm b_in b_out).eq]
  have h_eq : weylPauliX b * D * weylPauliX b = weylPauliX b_in * D * weylPauliX b_in := by
    calc weylPauliX b * D * weylPauliX b
      _ = (weylPauliX b_in * weylPauliX b_out) * D * (weylPauliX b_out * weylPauliX b_in) := by rw [← hb, ← hb']
      _ = weylPauliX b_in * (weylPauliX b_out * D) * (weylPauliX b_out * weylPauliX b_in) := by simp only [mul_assoc]
      _ = weylPauliX b_in * D * (weylPauliX b_out * weylPauliX b_out) * weylPauliX b_in := by
        rw [h_comm.eq]; simp only [mul_assoc]
      _ = weylPauliX b_in * D * weylPauliX b_in := by rw [weylPauliX_sq_eq_one, mul_one]
  rw [h_eq]; exact _root_.isSupportedOn_mul A (_root_.isSupportedOn_mul A hX_in hD) hX_in
private lemma exists_sector_scalar_of_weylPauli_conjugation
    {L q_code r_0 m_max L_star : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_rca J : ℝ} (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    {r : ℕ} (hr1 : 1 ≤ r) (hr_Lstar : r ≤ L_star) {A : Finset (Box3D L)} (hA : A ∈ boxCubes 3 L r)
    {D : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hD_sa : IsSelfAdjoint D) (hD_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A D)
    (hD_comm : ∀ idx : StaticCSSCheckIdx L q_code m_max, Commute D (sys.checkProj idx))
    (hD_norm : ‖D‖ ≤ 2 * J) (a b : BoxSlot3D L q_code → ZMod 2) :
    ∃ c : ℝ, |c| ≤ 2 * J ∧ ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
      (∀ idx ∈ rcaCollarChecks sys C_rca r A, σ idx = staticCSSPauliFlip D_field a b idx) →
      D * sys.syndromeProjector σ = ((c : ℝ) : ℂ) • sys.syndromeProjector σ := by
  let τ := staticCSSPauliFlip D_field a b
  rcases conj_pauli_sa_and_norm (weylPauliZ_isSelfAdjoint a) (weylPauliZ_sq_eq_one a)
      (weylPauliX_isSelfAdjoint b) (weylPauliX_sq_eq_one b) hD_sa hD_norm with
    ⟨hU_Udag, hUdag_U, hD_conj_sa, hD_conj_norm⟩
  have hU_flip : ∀ idx, (weylPauliZ a * weylPauliX b) * sys.checkProj idx =
      (if τ idx then 1 - sys.checkProj idx else sys.checkProj idx) *
        (weylPauliZ a * weylPauliX b) := fun idx => by
    rw [(h_sys_checks idx).1]; exact weylPauliZX_mul_staticCSSCheckProj D_field a b idx
  have h_inter := fun σ => intertwine_syndromeProjector_of_checkFlip sys hU_flip σ
  have hU_P0 : (weylPauliZ a * weylPauliX b) * sys.P0 =
      sys.syndromeProjector τ * (weylPauliZ a * weylPauliX b) := by
    have h_xor0 : (fun i => false ^^ τ i) = τ := by
      ext i; cases τ i <;> rfl
    rw [← (_root_.syndrome_resolution_indexed sys).1, h_inter (fun _ => false), h_xor0]
  have hD_conj_supp :
      IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) (boxCube (anchorOfCube r A) r)
        ((weylPauliX b * weylPauliZ a) * D * (weylPauliZ a * weylPauliX b)) := by
    rw [boxCube_anchorOfCube hA]
    have h_eq : (weylPauliX b * weylPauliZ a) * D * (weylPauliZ a * weylPauliX b) =
        weylPauliX b * (weylPauliZ a * D * weylPauliZ a) * weylPauliX b := by simp only [mul_assoc]
    rw [h_eq]; exact isSupportedOn_weylPauliX_conj A b (isSupportedOn_weylPauliZ_conj A a hD_supp)
  have hD_syn := (indexed_check_commuting_perturbation_commutes_with_syndromeProjector sys D hD_comm).1
  have hD_conj_comm := conj_comm_P0_of_intertwine hU_Udag hUdag_U hU_P0 (hD_syn τ)
  rcases exists_indexed_sector_sandwich_of_tqo_bhm sys h_tqo2 hr1 hr_Lstar
      (anchorOfCube r A) ((weylPauliX b * weylPauliZ a) * D * (weylPauliZ a * weylPauliX b))
      hD_conj_sa hD_conj_supp hD_conj_comm with ⟨c, hc_le, _, hc_ann⟩
  rw [mul_one] at hc_ann; refine ⟨c, le_trans hc_le hD_conj_norm, fun σ h_agree => ?_⟩
  let δ := syndromeXor σ τ
  have h_clean_δ : ∀ idx, sys.support idx ⊆ rcaCollarCube C_rca r A → δ idx = false := by
    intro idx h_sub; dsimp [δ, syndromeXor]
    rw [h_agree idx (Finset.mem_filter.mpr ⟨Finset.mem_univ idx, h_sub⟩), bne_self_eq_false]
  have hP_clean := (perturbed_P_loc_mul_syndromeProjector_of_clean_region sys h_clean_δ).1
  have h_xor_δ : (fun i => δ i ^^ τ i) = σ := by
    ext i; dsimp [δ, syndromeXor]; cases σ i <;> cases τ i <;> rfl
  have h_inter_δ : (weylPauliZ a * weylPauliX b) * sys.syndromeProjector δ =
      sys.syndromeProjector σ * (weylPauliZ a * weylPauliX b) := by rw [h_inter δ, h_xor_δ]
  exact conj_eigenvalue_of_clean_ann hU_Udag hP_clean hc_ann h_inter_δ
private noncomputable def restrictCollar {L q_code m_max : ℕ}
    (C_set : Finset (StaticCSSCheckIdx L q_code m_max))
    (σ : StaticCSSCheckIdx L q_code m_max → Bool) : StaticCSSCheckIdx L q_code m_max → Bool :=
  fun idx => if idx ∈ C_set then σ idx else false

/-- **Existence of Local Collar Scalar Eigenvalues (`exists_local_collar_scalar_family_of_tqo2`)** -/
theorem exists_local_collar_scalar_family_of_tqo2
    {L q_code r_0 m_max w_0 L_star R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0) {C_rca J : ℝ}
    (hR_pos : 1 ≤ R_pert) (hR_le : R_pert ≤ L_star) (hC_rca : 0 ≤ C_rca) (hJ_nn : 0 ≤ J)
    (h_tqo1 : SatisfiesTQO1 sys L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (hV_range : HasFiniteRangeBound V R_pert J) (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (he_decomp :
      let E_sum := ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A
      pauliDiagonalPart sys V R_pert - ((E_sum : ℝ) : ℂ) • 1 =
        (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r,
          pauliDiagonalShiftedTerm sys V e_loc r A) ∧
      (pauliDiagonalPart sys V R_pert - ((E_sum : ℝ) : ℂ) • 1) * sys.P0 = 0 ∧
      ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
          (syndromePinchOp sys (V.term r A)) ∧
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
          (pauliDiagonalShiftedTerm sys V e_loc r A) ∧
        ‖pauliDiagonalShiftedTerm sys V e_loc r A‖ ≤ 2 * J ∧
        HasLocalCheckViolationCover sys (syndromePinchOp sys (V.term r A))
          (rcaCollarChecks sys C_rca r A) (e_loc r A)) :
    ∃ d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ,
      IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc := by
  have h_ex_base : ∀ (r : ℕ) (A : Finset (Box3D L))
      (τ₀ : StaticCSSCheckIdx L q_code m_max → Bool),
        ∃ c : ℝ, |c| ≤ 2 * J ∧
          ((∀ idx ∈ rcaCollarChecks sys C_rca r A, τ₀ idx = false) → c = 0) ∧
          (r ∈ Finset.Icc 1 (min R_pert L) → A ∈ boxCubes 3 L r →
            (∃ p : (BoxSlot3D L q_code → ZMod 2) × (BoxSlot3D L q_code → ZMod 2),
              ∀ idx ∈ rcaCollarChecks sys C_rca r A,
                staticCSSPauliFlip D_field p.1 p.2 idx = τ₀ idx) →
            ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
              (∀ idx ∈ rcaCollarChecks sys C_rca r A, σ idx = τ₀ idx) →
              pauliDiagonalShiftedTerm sys V e_loc r A * sys.syndromeProjector σ =
                ((c : ℝ) : ℂ) • sys.syndromeProjector σ) := by
    intro r A τ₀
    rcases Classical.em (r ∈ Finset.Icc 1 (min R_pert L) ∧ A ∈ boxCubes 3 L r) with
      ⟨hr, hA⟩ | h_not_box
    · rcases Classical.em (∀ idx ∈ rcaCollarChecks sys C_rca r A, τ₀ idx = false) with
        h_clean | h_clean
      · refine ⟨0, by rw [abs_zero]; linarith, fun _ => rfl, fun _ _ _ σ h_agree => ?_⟩
        have h_σ_clean := fun idx hidx => (h_agree idx hidx).trans (h_clean idx hidx)
        exact ((he_decomp.2.2 r hr A hA).2.2.2.2.2 σ h_σ_clean).trans
          (zero_eq_zero_smul_clm (sys.syndromeProjector σ))
      · rcases Classical.em (∃ p : (BoxSlot3D L q_code → ZMod 2) × (BoxSlot3D L q_code → ZMod 2),
            ∀ idx ∈ rcaCollarChecks sys C_rca r A,
              staticCSSPauliFlip D_field p.1 p.2 idx = τ₀ idx) with h_real | h_real
        · let p := Classical.choose h_real; have hp_spec := Classical.choose_spec h_real
          have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
          have hr_Lstar : r ≤ L_star :=
            le_trans (le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)) hR_le
          have h_props := he_decomp.2.2 r hr A hA
          have hD_sa := isSelfAdjoint_sub_real_smul_one h_props.2.2.2.1 (e_loc r A)
          have hD_comm : ∀ idx, Commute (pauliDiagonalShiftedTerm sys V e_loc r A) (sys.checkProj idx) :=
            fun idx => (h_props.2.2.2.2.1 idx).sub_left ((Commute.one_left (sys.checkProj idx)).smul_left _)
          rcases exists_sector_scalar_of_weylPauli_conjugation D_field sys h_sys_checks h_tqo2
              hr1 hr_Lstar hA hD_sa h_props.2.1 hD_comm h_props.2.2.1 p.1 p.2 with ⟨c, hc_le, hc_act⟩
          refine ⟨c, hc_le, fun h_cl => False.elim (h_clean h_cl), fun _ _ _ σ h_agree => ?_⟩
          exact hc_act σ fun idx hidx => (h_agree idx hidx).trans (hp_spec idx hidx).symm
        · refine ⟨0, by rw [abs_zero]; linarith, fun _ => rfl, fun _ _ h_ex => False.elim (h_real h_ex)⟩
    · refine ⟨0, by rw [abs_zero]; linarith, fun _ => rfl, fun hr hA => False.elim (h_not_box ⟨hr, hA⟩)⟩
  let base_c (r : ℕ) (A : Finset (Box3D L)) (τ₀ : StaticCSSCheckIdx L q_code m_max → Bool) : ℝ :=
    Classical.choose (h_ex_base r A τ₀)
  refine ⟨fun r A σ => base_c r A (restrictCollar (rcaCollarChecks sys C_rca r A) σ),
    fun r hr A hA => ?_⟩
  have h_spec := fun τ₀ => Classical.choose_spec (h_ex_base r A τ₀)
  let C_A := rcaCollarChecks sys C_rca r A
  have h_res_eq : ∀ (σ : StaticCSSCheckIdx L q_code m_max → Bool) (idx : StaticCSSCheckIdx L q_code m_max),
      idx ∈ C_A → restrictCollar C_A σ idx = σ idx := by
    intro σ idx hidx; simp [restrictCollar, hidx]
  refine ⟨⟨fun σ hσ => ?_, fun σ => (h_spec (restrictCollar C_A σ)).1⟩,
    fun σ h_clean => ?_, fun σ₁ σ₂ h_agree => ?_⟩
  · rw [realizableSyndromes, Finset.mem_filter] at hσ; rcases hσ.2 with ⟨a, b, hab⟩
    exact (h_spec (restrictCollar C_A σ)).2.2 hr hA
      ⟨(a, b), fun idx hidx => by rw [← hab, h_res_eq σ idx hidx]⟩ σ
      (fun idx hidx => (h_res_eq σ idx hidx).symm)
  · apply (h_spec (restrictCollar C_A σ)).2.1
    intro idx hidx; rw [h_res_eq σ idx hidx]; exact h_clean idx hidx
  · have h_eq_res : restrictCollar C_A σ₁ = restrictCollar C_A σ₂ := by
      ext idx; by_cases hidx : idx ∈ C_A
      · simp [restrictCollar, hidx, h_agree idx hidx]
      · simp [restrictCollar, hidx]
    (try dsimp only)
    change base_c r A (restrictCollar C_A σ₁) = base_c r A (restrictCollar C_A σ₂)
    rw [h_eq_res]

/-- **Reduction of Perturbed Pauli-Diagonal Boltzmann Trace and Partition Function
    (`boltzmann_trace_and_partitionZ_eq_realizable_sectorEnergy_sum`)** -/
theorem boltzmann_trace_and_partitionZ_eq_realizable_sectorEnergy_sum
    {L q_code r_0 m_max R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max) (h_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_rca J β E_vac : ℝ}
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (he_decomp :
      let E_sum := ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A
      pauliDiagonalPart sys V R_pert - ((E_sum : ℝ) : ℂ) • 1 =
        (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r,
          pauliDiagonalShiftedTerm sys V e_loc r A) ∧
      (pauliDiagonalPart sys V R_pert - ((E_sum : ℝ) : ℂ) • 1) * sys.P0 = 0 ∧
      ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
          (syndromePinchOp sys (V.term r A)) ∧
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
          (pauliDiagonalShiftedTerm sys V e_loc r A) ∧
        ‖pauliDiagonalShiftedTerm sys V e_loc r A‖ ≤ 2 * J ∧
        HasLocalCheckViolationCover sys (syndromePinchOp sys (V.term r A))
          (rcaCollarChecks sys C_rca r A) (e_loc r A))
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : IsLocalCollarScalarFamily D_field sys R_pert C_rca J V e_loc d_loc)
    (hH_diag_sa :
      IsSelfAdjoint (sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1))
    (hH_diag_comm : ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
      Commute (sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1)
        (sys.syndromeProjector σ))
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    let H_diag := sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1
    let E_sum := ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let K := Real.exp (-β * (E_sum - E_vac)) * hilbertTrace sys.P0
    0 ≤ K ∧
    hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag_sa)
        (opEigenvalues H_diag hH_diag_sa) β * positiveCheckWitnessProj sys W) =
      K * ∑ σ ∈ (realizableSyndromes D_field).filter (fun σ => ∀ idx ∈ W, σ idx = true),
        Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) ∧
    gibbsPartitionZ (opEigenvalues H_diag hH_diag_sa) β =
      K * ∑ σ ∈ realizableSyndromes D_field,
        Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ) := by
  intro H_diag E_sum K; have h_res := _root_.syndrome_resolution_indexed sys
  have hT0_nn : 0 ≤ hilbertTrace sys.P0 := by
    rw [← h_res.1]; exact hilbertTrace_syndromeProjector_nonneg sys (fun _ => false)
  have hK_nn : 0 ≤ K := mul_nonneg (le_of_lt (Real.exp_pos _)) hT0_nn
  have h_sec_trace : ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
      hilbertTrace (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag_sa)
          (opEigenvalues H_diag hH_diag_sa) β * sys.syndromeProjector σ) =
        if σ ∈ realizableSyndromes D_field then
          K * Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ)
        else 0 := by
    intro σ; by_cases hσ : σ ∈ realizableSyndromes D_field
    · rw [if_pos hσ]
      have h_tr_P0 : hilbertTrace sys.P0 = hilbertTrace (sys.syndromeProjector σ) := by
        rcases (Finset.mem_filter.mp hσ).2 with ⟨a, b, rfl⟩
        exact (hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq_P0 D_field h_valid sys h_sys_checks a b).symm
      let E_σ := pauliDiagonalSectorEnergy sys R_pert d_loc σ + (E_sum - E_vac)
      have h_shift_act :
          (pauliDiagonalPart sys V R_pert - ((E_sum : ℝ) : ℂ) • 1) * sys.syndromeProjector σ =
            ((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ : ℝ) : ℂ) •
              sys.syndromeProjector σ := by
        rw [he_decomp.1, Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
        exact Finset.sum_congr rfl fun A hA => (h_scalar r hr A hA).1.1 σ hσ
      have h_P_Hdiag : sys.syndromeProjector σ * H_diag = ((E_σ : ℝ) : ℂ) • sys.syndromeProjector σ :=
        (hH_diag_comm σ).symm.eq.trans (hdiag_mul_projector_eq_smul (h_res.2.2.2.2.1 σ) h_shift_act)
      have hK_eq : K = Real.exp (-β * (E_sum - E_vac)) * hilbertTrace (sys.syndromeProjector σ) := by
        dsimp [K]; rw [h_tr_P0]
      rw [hilbertTrace_gibbsBoltzmannOp_mul_eq, hK_eq,
        hilbertTrace_eq_sum_opEigenbasis H_diag hH_diag_sa (sys.syndromeProjector σ),
        Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun ω _ => ?_
      let ψ_ω := opEigenbasis H_diag hH_diag_sa ω; let E_ω := opEigenvalues H_diag hH_diag_sa ω
      let t := RCLike.re (inner ℂ ψ_ω (sys.syndromeProjector σ ψ_ω))
      have h1 : (sys.syndromeProjector σ * H_diag) ψ_ω = (E_ω : ℂ) • sys.syndromeProjector σ ψ_ω := by
        change sys.syndromeProjector σ (H_diag ψ_ω) = _
        rw [opEigenbasis_apply_H H_diag hH_diag_sa ω, map_smul]
      have h2 : (sys.syndromeProjector σ * H_diag) ψ_ω = ((E_σ : ℝ) : ℂ) • sys.syndromeProjector σ ψ_ω := by
        rw [h_P_Hdiag, ContinuousLinearMap.smul_apply]
      have h_in := congr_arg (fun v => RCLike.re (inner ℂ ψ_ω v)) (h1.symm.trans h2)
      have h_eq_re : E_ω * t = E_σ * t := by simpa only [t, inner_smul_right, re_ofReal_mul] using h_in
      have h_zero : (E_ω - E_σ) * t = 0 := by linarith
      change Real.exp (-β * E_ω) * t =
        Real.exp (-β * (E_sum - E_vac)) * t * Real.exp (-β * pauliDiagonalSectorEnergy sys R_pert d_loc σ)
      rcases mul_eq_zero.mp h_zero with hE | ht
      · rw [sub_eq_zero.mp hE]; dsimp [E_σ]
        have h_add : -β * (pauliDiagonalSectorEnergy sys R_pert d_loc σ + (E_sum - E_vac)) =
            -β * (E_sum - E_vac) + -β * pauliDiagonalSectorEnergy sys R_pert d_loc σ := by ring
        rw [h_add, Real.exp_add]; ring
      · rw [ht]; ring
    · rw [if_neg hσ]
      have h_zero : sys.syndromeProjector σ = 0 := by
        by_contra h_ne
        obtain ⟨⟨a, b, hab⟩, _⟩ :=
          hilbertTrace_syndromeProjector_eq_P0_of_ne_zero D_field h_valid sys h_sys_checks σ h_ne
        exact hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, a, b, hab⟩)
      rw [h_zero, mul_zero]; unfold hilbertTrace; simp
  refine ⟨hK_nn, ?_, ?_⟩
  · unfold positiveCheckWitnessProj; rw [Finset.mul_sum, hilbertTrace_sum]
    refine (Finset.sum_congr rfl fun x _ => h_sec_trace x).trans ?_
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    refine congrArg (K * ·) (Finset.sum_congr ?_ fun _ _ => rfl)
    ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  · rw [← perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ H_diag hH_diag_sa β,
      ← h_res.2.2.2.1, Finset.mul_sum, hilbertTrace_sum]
    refine (Finset.sum_congr rfl fun x _ => h_sec_trace x).trans ?_
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    refine congrArg (K * ·) (Finset.sum_congr ?_ fun _ _ => rfl)
    ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end SpacetimeWorldlineKP
end
