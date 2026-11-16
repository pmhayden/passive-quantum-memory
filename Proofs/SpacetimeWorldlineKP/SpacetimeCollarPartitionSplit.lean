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

import Proofs.SpacetimeWorldlineKP.RealizableSyndromeCosetPeeling

/-!
# RCA Check-Collar Hamiltonian Split and Worldline Diagonal-Action Factorization

Partitions cube perturbations around a witness into witness-collar and spectator parts (`rcaCollarCube`, `rcaCollarChecks`, `collarWitnessPart`, `collarSpectatorPart`). Bounds off-diagonal jump norms in the shifted Hamiltonian decomposition (`shiftedHamiltonian_eq_pauliDiagonal_add_offDiagonal_and_jump_bounds`) and proves Euclidean worldline expansion with diagonal-action factorization (`dyson_worldline_expansion_and_diag_action_factorization`).

## References

* Part II, Section 3.2 (`subsec:rca1-pinching`), Proposition 3.4 (`prop:pauli-diag-off`)
* Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open Filter Topology Asymptotics ContinuousLinearMap KMSPinchedGibbs PerturbedThermalBarrier

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace SpacetimeWorldlineKP

/-! ## 1. Explicit $\beta_c$-Independent Collar Walsh Coupling Threshold -/

def collarMaxCheckCard (R_pert r_0 w_0 : ℕ) (C_rca : ℝ) : ℕ :=
  (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1) + 1

def collarWalshCouplingThreshold (R_pert r_0 w_0 : ℕ) (C_rca : ℝ) : ℝ :=
  min (1 / (16 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1)))
    ((1 / (4 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1) ^ 2)) *
      Real.exp (-8 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1) *
        (((collarMaxCheckCard R_pert r_0 w_0 C_rca : ℕ) : ℝ) + 1) *
        (16 + (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1))))

theorem collarWalshCouplingThreshold_pos (R_pert r_0 w_0 : ℕ) (C_rca : ℝ) :
    0 < collarWalshCouplingThreshold R_pert r_0 w_0 C_rca := by
  unfold collarWalshCouplingThreshold
  have h_rca_nn : 0 ≤ rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca := by
    unfold rcaDiagonalCoercivityConstant; positivity
  have h_left : 0 < 1 / (16 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1)) := by positivity
  have h_right : 0 < (1 / (4 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1) ^ 2)) *
      Real.exp (-8 * (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1) *
        (((collarMaxCheckCard R_pert r_0 w_0 C_rca : ℕ) : ℝ) + 1) *
        (16 + (rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca + 1))) := by positivity
  exact lt_min h_left h_right

theorem two_mul_rcaDiagonalCoercivityConstant_mul_le_eighth_of_le_collarWalshCouplingThreshold
    {R_pert r_0 w_0 : ℕ} {C_rca J : ℝ}
    (hJ_nn : 0 ≤ J) (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca) :
    2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J ≤ 1 / 8 := by
  let Δ := rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca
  have hΔ_nn : 0 ≤ Δ := by dsimp [Δ, rcaDiagonalCoercivityConstant]; positivity
  have h_denom_pos : 0 < 16 * (Δ + 1) := by linarith
  have hJ_left : J ≤ 1 / (16 * (Δ + 1)) := le_trans hJ_le (min_le_left _ _)
  have h_mul : 2 * Δ * J ≤ 2 * Δ * (1 / (16 * (Δ + 1))) := mul_le_mul_of_nonneg_left hJ_left (by linarith)
  have h_frac : 2 * Δ * (1 / (16 * (Δ + 1))) ≤ 1 / 8 := by rw [mul_one_div, div_le_iff₀ h_denom_pos]; linarith
  exact le_trans h_mul h_frac

theorem two_mul_rcaDiagonalCoercivityConstant_mul_le_quarter_of_le_collarWalshCouplingThreshold
    {R_pert r_0 w_0 : ℕ} {C_rca J : ℝ}
    (hJ_nn : 0 ≤ J) (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca) :
    2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J ≤ 1 / 4 := by
  have h8 := two_mul_rcaDiagonalCoercivityConstant_mul_le_eighth_of_le_collarWalshCouplingThreshold hJ_nn hJ_le
  linarith

theorem two_mul_rcaDiagonalCoercivityConstant_mul_J_le_exp_collarMaxCheckCard_of_le_collarWalshCouplingThreshold
    {R_pert r_0 w_0 : ℕ} {C_rca J : ℝ}
    (hJ_nn : 0 ≤ J) (hJ_le : J ≤ collarWalshCouplingThreshold R_pert r_0 w_0 C_rca) :
    let Δ := rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca
    let E := Real.exp (-8 * (Δ + 1) * (((collarMaxCheckCard R_pert r_0 w_0 C_rca : ℕ) : ℝ) + 1) * (16 + (Δ + 1)))
    let E_pos := Real.exp (8 * (Δ + 1) * (((collarMaxCheckCard R_pert r_0 w_0 C_rca : ℕ) : ℝ) + 1) * (16 + (Δ + 1)))
    J ≤ E ∧ 2 * Δ * J ≤ E ∧ 2 * Δ * J * E_pos ≤ 1 / (2 * (Δ + 1)) := by
  intro Δ E E_pos
  have hΔ_nn : 0 ≤ Δ := by dsimp [Δ, rcaDiagonalCoercivityConstant]; positivity
  have h_denom1_pos : 0 < 2 * (Δ + 1) := by linarith
  have h_denom_pos : 0 < 4 * (Δ + 1) ^ 2 := by nlinarith
  have hE_nn : 0 ≤ E := le_of_lt (Real.exp_pos _)
  have hE_pos_nn : 0 ≤ E_pos := le_of_lt (Real.exp_pos _)
  have hJ_right : J ≤ (1 / (4 * (Δ + 1) ^ 2)) * E := le_trans hJ_le (min_le_right _ _)
  have h_one_div_le_one : 1 / (4 * (Δ + 1) ^ 2) ≤ 1 := by rw [div_le_iff₀ h_denom_pos]; nlinarith
  have hJ_le_E : J ≤ E := by
    calc J ≤ (1 / (4 * (Δ + 1) ^ 2)) * E := hJ_right
      _ ≤ 1 * E := mul_le_mul_of_nonneg_right h_one_div_le_one hE_nn
      _ = E := one_mul E
  have h_ratio_le : 2 * Δ * (1 / (4 * (Δ + 1) ^ 2)) ≤ 1 / (2 * (Δ + 1)) := by
    rw [mul_one_div, div_le_div_iff₀ h_denom_pos h_denom1_pos]; nlinarith
  have h_ratio_le_one : 2 * Δ * (1 / (4 * (Δ + 1) ^ 2)) ≤ 1 := by rw [mul_one_div, div_le_iff₀ h_denom_pos]; nlinarith
  have h2ΔJ_le_E : 2 * Δ * J ≤ E := by
    calc 2 * Δ * J ≤ 2 * Δ * ((1 / (4 * (Δ + 1) ^ 2)) * E) := mul_le_mul_of_nonneg_left hJ_right (by linarith)
      _ = (2 * Δ * (1 / (4 * (Δ + 1) ^ 2))) * E := by ring
      _ ≤ 1 * E := mul_le_mul_of_nonneg_right h_ratio_le_one hE_nn
      _ = E := one_mul E
  have h_exp_cancel : E * E_pos = 1 := by
    dsimp [E, E_pos]; rw [← Real.exp_add]
    have h_zero :
        -8 * (Δ + 1) * (((collarMaxCheckCard R_pert r_0 w_0 C_rca : ℕ) : ℝ) + 1) * (16 + (Δ + 1)) +
        8 * (Δ + 1) * (((collarMaxCheckCard R_pert r_0 w_0 C_rca : ℕ) : ℝ) + 1) * (16 + (Δ + 1)) = 0 := by ring
    rw [h_zero, Real.exp_zero]
  have h2ΔJ_prod : 2 * Δ * J * E_pos ≤ 1 / (2 * (Δ + 1)) := by
    calc 2 * Δ * J * E_pos
      _ ≤ (2 * Δ * ((1 / (4 * (Δ + 1) ^ 2)) * E)) * E_pos :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ_right (by linarith)) hE_pos_nn
      _ = (2 * Δ * (1 / (4 * (Δ + 1) ^ 2))) * (E * E_pos) := by ring
      _ = 2 * Δ * (1 / (4 * (Δ + 1) ^ 2)) := by rw [h_exp_cancel, mul_one]
      _ ≤ 1 / (2 * (Δ + 1)) := h_ratio_le
  exact ⟨hJ_le_E, h2ΔJ_le_E, h2ΔJ_prod⟩

/-! ## 2. Local $\mathrm{RCA1}$ Collar Partition Split & Spatial Support Preservation -/

/-- **Enclosing $\mathrm{RCA1}$ Collar Cube (`rcaCollarCube`)** -/
def rcaCollarCube {L : ℕ} [NeZero L] (C_rca : ℝ) (r : ℕ) (A : Finset (Box3D L)) : Finset (Box3D L) :=
  enclosingBoxCube (anchorOfCube r A) r (linearExpansionRadius C_rca r)

/-- **Enclosing $\mathrm{RCA1}$ Collar Check Set (`rcaCollarChecks`)** -/
def rcaCollarChecks {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (r : ℕ) (A : Finset (Box3D L)) : Finset (StaticCSSCheckIdx L q_code m_max) :=
  Finset.univ.filter (fun c => sys.support c ⊆ rcaCollarCube C_rca r A)

/-- **Vacuum-Shifted Local Pauli-Diagonal Term (`pauliDiagonalShiftedTerm`)** -/
def pauliDiagonalShiftedTerm {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ) (r : ℕ) (A : Finset (Box3D L)) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  syndromePinchOp sys (V.term r A) - ((e_loc r A : ℝ) : ℂ) • 1

/-- **Witness-Intersecting Local Collar Sum (`collarWitnessPart`)** -/
def collarWitnessPart {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert : ℕ)
    (D_loc : ℕ → Finset (Box3D L) →
      (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))))
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  ∑ r ∈ Finset.Icc 1 (min R_pert L),
    ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (rcaCollarChecks sys C_rca r A) W), D_loc r A

/-- **Spectator Local Collar Sum (`collarSpectatorPart`)** -/
def collarSpectatorPart {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert : ℕ)
    (D_loc : ℕ → Finset (Box3D L) →
      (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))))
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  ∑ r ∈ Finset.Icc 1 (min R_pert L),
    ∑ A ∈ (boxCubes 3 L r).filter (fun A => Disjoint (rcaCollarChecks sys C_rca r A) W), D_loc r A

/-- **Partition Identity & Spectator Agreement Outside $W$ (`local_collar_partition_split_around_witness`)** -/
theorem local_collar_partition_split_around_witness
    {L q_code m_max : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (C_rca : ℝ) (R_pert : ℕ)
    (D_loc : ℕ → Finset (Box3D L) →
      (ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))))
    (W : Finset (StaticCSSCheckIdx L q_code m_max)) :
    (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, D_loc r A) =
      collarWitnessPart sys C_rca R_pert D_loc W + collarSpectatorPart sys C_rca R_pert D_loc W ∧
    ∀ r ∈ Finset.Icc 1 (min R_pert L),
      ∀ A ∈ (boxCubes 3 L r).filter (fun A => Disjoint (rcaCollarChecks sys C_rca r A) W),
        ∀ (σ : StaticCSSCheckIdx L q_code m_max → Bool) (c : StaticCSSCheckIdx L q_code m_max),
          c ∈ rcaCollarChecks sys C_rca r A → witnessClearedSyndrome W σ c = σ c := by
  refine ⟨?_, fun r _ A hA σ c hc => ?_⟩
  · unfold collarWitnessPart collarSpectatorPart
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by rw [add_comm, Finset.sum_filter_add_sum_filter_not]
  · have hc_not_W : c ∉ W := Finset.disjoint_left.mp (Finset.mem_filter.mp hA).2 hc
    simp [witnessClearedSyndrome, hc_not_W]

/-- **Explicit Local $\mathrm{RCA1}$ Collar Check-Violation Decomposition of `pauliDiagonalPart` (`exists_pauliDiagonal_local_collar_decomposition`)** -/
theorem exists_pauliDiagonal_local_collar_decomposition
    {L q_code r_0 m_max L_star R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {C_rca J : ℝ} (hR_le : R_pert ≤ L_star)
    (h_tqo2 : SatisfiesSectorFilteredLinearTQO2 sys 1 L_star C_rca)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (hV_range : HasFiniteRangeBound V R_pert J) :
    ∃ e_loc : ℕ → Finset (Box3D L) → ℝ,
      pauliDiagonalPart sys V R_pert -
        (((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A : ℝ) : ℂ) • 1) =
        (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r,
          pauliDiagonalShiftedTerm sys V e_loc r A) ∧
      (pauliDiagonalPart sys V R_pert -
        (((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A : ℝ) : ℂ) • 1)) *
        sys.P0 = 0 ∧
      ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (syndromePinchOp sys (V.term r A)) ∧
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (pauliDiagonalShiftedTerm sys V e_loc r A) ∧
        ‖pauliDiagonalShiftedTerm sys V e_loc r A‖ ≤ 2 * J ∧
        HasLocalCheckViolationCover sys (syndromePinchOp sys (V.term r A))
          (rcaCollarChecks sys C_rca r A) (e_loc r A) := by
  let M (r : ℕ) (A : Finset (Box3D L)) := syndromePinchOp sys (V.term r A)
  have hM_props : ∀ r A, IsSelfAdjoint (M r A) ∧ (∀ c, Commute (M r A) (sys.checkProj c)) ∧ Commute (M r A) sys.P0 :=
    fun r A => by
      have h := syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys (V.is_selfAdjoint r A)
      exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  have h_ex : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      ∃ e : ℝ, IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (M r A) ∧
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (M r A - ((e : ℝ) : ℂ) • 1) ∧
        ‖M r A - ((e : ℝ) : ℂ) • 1‖ ≤ 2 * J ∧
        HasLocalCheckViolationCover sys (M r A) (rcaCollarChecks sys C_rca r A) e := by
    intro r hr A hA
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr_min : r ≤ min R_pert L := (Finset.mem_Icc.mp hr).2
    have hr_R : r ≤ R_pert := le_trans hr_min (Nat.min_le_left R_pert L)
    have hr_L : r ≤ L := le_trans hr_min (Nat.min_le_right R_pert L)
    have hr_IccL : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hr1, hr_L⟩
    have hV_supp := V.is_supported r hr_IccL A hA
    have hV_norm : ‖V.term r A‖ ≤ J := (hV_range r hr_IccL A hA).1 hr_R
    have hM_ns := syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck D_field sys h_sys_checks A hV_supp
    have hM_supp_cube : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) (boxCube (anchorOfCube r A) r) (M r A) := by
      rw [boxCube_anchorOfCube hA]; exact hM_ns.2
    rcases exists_indexed_sector_sandwich_of_tqo_bhm sys h_tqo2 hr1 (le_trans hr_R hR_le)
        (anchorOfCube r A) (M r A) (hM_props r A).1 hM_supp_cube (hM_props r A).2.2 with ⟨e, _, he_norm, he_ann⟩
    rw [mul_one] at he_ann
    have h_shift_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (M r A - ((e : ℝ) : ℂ) • 1) :=
      _root_.isSupportedOn_sub A hM_ns.2 (_root_.isSupportedOn_smul A ((e : ℝ) : ℂ) (_root_.isSupportedOn_one A))
    refine ⟨e, hM_ns.2, h_shift_supp, le_trans he_norm (by linarith [hM_ns.1, hV_norm]),
      ⟨(hM_props r A).1, (hM_props r A).2.1, fun σ h_clean => ?_⟩⟩
    have hP_clean : sys.localGroundProj (rcaCollarCube C_rca r A) * sys.syndromeProjector σ = sys.syndromeProjector σ :=
      (perturbed_P_loc_mul_syndromeProjector_of_clean_region sys fun c hc =>
        h_clean c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)).1
    rw [← hP_clean, ← mul_assoc]
    change (M r A - (e : ℂ) • 1) * sys.localGroundProj (enclosingBoxCube (anchorOfCube r A) r (linearExpansionRadius C_rca r)) *
      sys.syndromeProjector σ = 0
    rw [he_ann, zero_mul]
  obtain ⟨e_loc, he_spec⟩ : ∃ e_loc : ℕ → Finset (Box3D L) → ℝ,
      ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (M r A) ∧
        IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (pauliDiagonalShiftedTerm sys V e_loc r A) ∧
        ‖pauliDiagonalShiftedTerm sys V e_loc r A‖ ≤ 2 * J ∧
        HasLocalCheckViolationCover sys (M r A) (rcaCollarChecks sys C_rca r A) (e_loc r A) := by
    refine ⟨fun r A => if h : r ∈ Finset.Icc 1 (min R_pert L) ∧ A ∈ boxCubes 3 L r then
        Classical.choose (h_ex r h.1 A h.2) else 0, fun r hr A hA => ?_⟩
    unfold pauliDiagonalShiftedTerm; dsimp only [M]; rw [dif_pos ⟨hr, hA⟩]
    exact Classical.choose_spec (h_ex r hr A hA)
  have h_op : pauliDiagonalPart sys V R_pert -
      (((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A : ℝ) : ℂ) • 1) =
      ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, pauliDiagonalShiftedTerm sys V e_loc r A := by
    ext χ; unfold pauliDiagonalPart pauliDiagonalShiftedTerm
    simp [Finset.sum_smul, Finset.sum_sub_distrib]
  refine ⟨e_loc, h_op, ?_, he_spec⟩
  rw [h_op, Finset.sum_mul]
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.sum_mul]; refine Finset.sum_eq_zero fun A hA => ?_
  have h_P0 : sys.P0 = sys.syndromeProjector (fun _ => false) := by
    simp [IndexedCommutingProjectorHamiltonian.syndromeProjector,
      IndexedCommutingProjectorHamiltonian.P0, IndexedCommutingProjectorHamiltonian.groundProj]
  rw [h_P0]; exact (he_spec r hr A hA).2.2.2.2.2 (fun _ => false) (fun _ _ => rfl)

/-! ## 3. Explicit Off-Diagonal Local Pauli Jump Decomposition & Empty Witness Identities -/

/-- **Local Off-Diagonal Pauli Jump Operator (`pauliOffDiagonalTerm`)** -/
def pauliOffDiagonalTerm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (V : QuasiLocalPerturbation D L Site) (r : ℕ) (A : Finset (BoxD D L)) :
    ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site :=
  V.term r A - syndromePinchOp sys (V.term r A)

/-- **Shifted Hamiltonian Splitting & Local Off-Diagonal Jump Properties (`shiftedHamiltonian_eq_pauliDiagonal_add_offDiagonal_and_jump_bounds`)** -/
theorem shiftedHamiltonian_eq_pauliDiagonal_add_offDiagonal_and_jump_bounds
    {L q_code r_0 m_max : ℕ}
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    {R_pert : ℕ} {J E_vac : ℝ}
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (hV_range : HasFiniteRangeBound V R_pert J) :
    ((sys.H0 + V.totalPerturbation) - ((E_vac : ℝ) : ℂ) • 1) =
      (sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1) +
        pauliOffDiagonalPart sys V R_pert ∧
    pauliOffDiagonalPart sys V R_pert =
      (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, pauliOffDiagonalTerm sys V r A) ∧
    ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      IsSelfAdjoint (pauliOffDiagonalTerm sys V r A) ∧
      IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A (pauliOffDiagonalTerm sys V r A) ∧
      (∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
        sys.syndromeProjector σ * pauliOffDiagonalTerm sys V r A * sys.syndromeProjector σ = 0) ∧
      ‖pauliOffDiagonalTerm sys V r A‖ ≤ 2 * J := by
  have h_tot := pauliDiagonalPart_add_pauliOffDiagonalPart_eq_V_tot sys V hV_range
  refine ⟨by rw [← h_tot]; abel, rfl, fun r hr A hA => ?_⟩
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr_min : r ≤ min R_pert L := (Finset.mem_Icc.mp hr).2
  have hr_R : r ≤ R_pert := le_trans hr_min (Nat.min_le_left R_pert L)
  have hr_IccL : r ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨hr1, le_trans hr_min (Nat.min_le_right R_pert L)⟩
  have hV_sa := V.is_selfAdjoint r A
  have hV_supp := V.is_supported r hr_IccL A hA
  have hV_norm : ‖V.term r A‖ ≤ J := (hV_range r hr_IccL A hA).1 hr_R
  have h_pinch_sa := (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys hV_sa).1
  have h_pinch_diag := (syndromePinchOp_isSelfAdjoint_and_commute_checkProj sys hV_sa).2.1
  have h_pinch_ns := syndromePinchOp_norm_and_isSupportedOn_of_staticCSSCheck D_field sys h_sys_checks A hV_supp
  have h_off_sa : IsSelfAdjoint (pauliOffDiagonalTerm sys V r A) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']; unfold pauliOffDiagonalTerm
    rw [map_sub, ContinuousLinearMap.isSelfAdjoint_iff'.mp hV_sa, ContinuousLinearMap.isSelfAdjoint_iff'.mp h_pinch_sa]
  refine ⟨h_off_sa, _root_.isSupportedOn_sub A hV_supp h_pinch_ns.2, fun σ => ?_, ?_⟩
  · unfold pauliOffDiagonalTerm
    have h_idemp : sys.syndromeProjector σ * sys.syndromeProjector σ = sys.syndromeProjector σ :=
      ((_root_.syndrome_resolution_indexed sys).2.1 σ).1
    rw [mul_sub, sub_mul, (h_pinch_diag σ).2.1, mul_assoc (sys.syndromeProjector σ * V.term r A), h_idemp, sub_self]
  · unfold pauliOffDiagonalTerm
    calc ‖V.term r A - syndromePinchOp sys (V.term r A)‖
      _ ≤ ‖V.term r A‖ + ‖syndromePinchOp sys (V.term r A)‖ := norm_sub_le _ _
      _ ≤ J + J := add_le_add hV_norm (le_trans h_pinch_ns.1 hV_norm)
      _ = 2 * J := by ring

/-- **Empty Witness Identity (`positiveCheckWitnessProj_empty_eq_one`)** -/
theorem positiveCheckWitnessProj_empty_eq_one
    {D L : ℕ} {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι] (sys : IndexedCommutingProjectorHamiltonian D L Site ι) :
    positiveCheckWitnessProj sys (∅ : Finset ι) = 1 := by
  unfold positiveCheckWitnessProj
  have h_filt : Finset.univ.filter (fun σ : ι → Bool => ∀ c ∈ (∅ : Finset ι), σ c = true) = Finset.univ := by
    ext σ; simp
  rw [h_filt]; exact (_root_.syndrome_resolution_indexed sys).2.2.2.1

/-- **Gibbs Probability of Identity Operator (`gibbsFailureProb_one_eq_one`)** -/
theorem gibbsFailureProb_one_eq_one {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) (hH : IsSelfAdjoint H) (β : ℝ) :
    gibbsFailureProb H hH β 1 = 1 := by
  rw [perturbed_gibbsFailureProb_eq_inv_gibbsPartitionZ_mul_boltzmann_trace H hH β 1,
    perturbed_hilbertTrace_gibbsBoltzmannOp_mul_one_eq_partitionZ H hH β,
    inv_mul_cancel₀ (ne_of_gt (gibbsPartitionZ_pos (opEigenvalues H hH) β))]

/-! ## 4. Klarner Connected Polymer Counting & Discretized Worldline Action Factorization -/

/-- **Connected Subgraph Predicate (`IsConnectedSubgraph`, Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.3 (`lem:klarner-bound`))** -/
def IsConnectedSubgraph {V : Type*} (adj : V → V → Prop) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ adj x y) u v

/-- **Violated Check Support of a Syndrome (`syndromeViolatedChecks`)** -/
def syndromeViolatedChecks {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → Bool) : Finset ι :=
  Finset.univ.filter (fun c => σ c = true)

/-- **Perturbed Pauli-Diagonal Syndrome Energy (`perturbedDiagonalSyndromeEnergy`)** -/
noncomputable def perturbedDiagonalSyndromeEnergy {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (R_pert : ℕ) (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (σ : StaticCSSCheckIdx L q_code m_max → Bool) : ℝ :=
  sys.syndromeEnergy σ + ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ

/-- **Klarner Connected Polymer Count Bound (`klarner_connected_polymer_count_le`, Part II, Section 3.1 (`subsec:weyl-witness-poisson`), Lemma 3.3 (`lem:klarner-bound`))** -/
theorem klarner_connected_polymer_count_le
    {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Prop) [DecidableRel adj]
    (h_symm : ∀ u v : V, adj u v → adj v u) {Δ : ℕ} (hΔ : 4 ≤ Δ)
    (h_deg : ∀ v : V, (Finset.univ.filter (adj v)).card ≤ Δ)
    (v_0 : V) {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 ≤ ε) :
    let Conn_m := Finset.univ.filter (fun S : Finset V => v_0 ∈ S ∧ S.card = m ∧ IsConnectedSubgraph adj S)
    (Conn_m.card : ℝ) ≤ ((Δ : ℝ) ^ 2) ^ m ∧ (∑ S ∈ Conn_m, ε ^ S.card) ≤ ((Δ : ℝ) ^ 2 * ε) ^ m :=
  kp_klarner_connected_polymer_count_le adj h_symm hΔ h_deg v_0 hm hε

/-- **Discretized Worldline Expansion & Diagonal Action Factorization (`dyson_worldline_expansion_and_diag_action_factorization`, Part II, Section 3.5 (`subsec:worldline-expansion`), Lemma 3.9 (`lem:worldline-factorization-time-reversal`))** -/
theorem dyson_worldline_expansion_and_diag_action_factorization
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code)) (StaticCSSCheckIdx L q_code m_max))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L q_code m_max,
      sys.checkProj idx = staticCSSCheckProj D_field idx ∧
      sys.support idx = staticCSSCheckSupport D_field idx ∧ sys.weight idx = 1)
    (h_geom : sys.IsGeometricallyLocal r_0 w_0) {C_rca J β : ℝ}
    (hβ_pos : 0 < β) (hJ_nn : 0 ≤ J)
    (hJ_small : 2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J ≤ 1 / 4)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (e_loc : ℕ → Finset (Box3D L) → ℝ)
    (d_loc : ℕ → Finset (Box3D L) → (StaticCSSCheckIdx L q_code m_max → Bool) → ℝ)
    (h_scalar : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
      ((∀ σ ∈ realizableSyndromes D_field,
          pauliDiagonalShiftedTerm sys V e_loc r A * sys.syndromeProjector σ =
            ((d_loc r A σ : ℝ) : ℂ) • sys.syndromeProjector σ) ∧
        ∀ σ : StaticCSSCheckIdx L q_code m_max → Bool, |d_loc r A σ| ≤ 2 * J) ∧
      (∀ σ : StaticCSSCheckIdx L q_code m_max → Bool,
        (∀ c ∈ rcaCollarChecks sys C_rca r A, σ c = false) → d_loc r A σ = 0) ∧
      (∀ σ₁ σ₂ : StaticCSSCheckIdx L q_code m_max → Bool,
        (∀ c ∈ rcaCollarChecks sys C_rca r A, σ₁ c = σ₂ c) → d_loc r A σ₁ = d_loc r A σ₂))
    (h_shift_decomp :
      pauliDiagonalPart sys V R_pert -
        (((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A : ℝ) : ℂ) • 1) =
        ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, pauliDiagonalShiftedTerm sys V e_loc r A)
    (H_shift : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
    (hH_diag : IsSelfAdjoint (sys.H0 + pauliDiagonalPart sys V R_pert -
      (((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A : ℝ) : ℂ) • 1)))
    (hH_shift : IsSelfAdjoint H_shift) :
    let E_vac := ∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, e_loc r A
    let H_diag := sys.H0 + pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1
    let M := thermalTimeSliceCount β
    let τ_0 := thermalTimeSliceStep β
    let E_diag := perturbedDiagonalSyndromeEnergy sys R_pert d_loc
    (1 ≤ M ∧ 0 < τ_0 ∧ τ_0 ≤ 1 ∧ (M : ℝ) * τ_0 = β ∧
      gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) β =
        (gibbsBoltzmannOp (opEigenbasis H_diag hH_diag) (opEigenvalues H_diag hH_diag) τ_0) ^ M ∧
      gibbsBoltzmannOp (opEigenbasis H_shift hH_shift) (opEigenvalues H_shift hH_shift) β =
        (gibbsBoltzmannOp (opEigenbasis H_shift hH_shift) (opEigenvalues H_shift hH_shift) τ_0) ^ M) ∧
    (∀ σ ∈ realizableSyndromes D_field,
      H_diag * sys.syndromeProjector σ = ((E_diag σ : ℝ) : ℂ) • sys.syndromeProjector σ ∧
      (3 / 4 : ℝ) * sys.syndromeEnergy σ ≤ E_diag σ ∧ E_diag σ ≤ (5 / 4 : ℝ) * sys.syndromeEnergy σ) ∧
    (∀ (σ₁ σ₂ : Fin M → (StaticCSSCheckIdx L q_code m_max → Bool)),
      (∀ t : Fin M,
        Disjoint (syndromeViolatedChecks (σ₁ t)) (syndromeViolatedChecks (σ₂ t)) ∧
        ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
          Disjoint (rcaCollarChecks sys C_rca r A) (syndromeViolatedChecks (σ₁ t)) ∨
          Disjoint (rcaCollarChecks sys C_rca r A) (syndromeViolatedChecks (σ₂ t))) →
      Real.exp (-τ_0 * ∑ t : Fin M, E_diag (syndromeXor (σ₁ t) (σ₂ t))) =
        Real.exp (-τ_0 * ∑ t : Fin M, E_diag (σ₁ t)) * Real.exp (-τ_0 * ∑ t : Fin M, E_diag (σ₂ t))) := by
  intro E_vac H_diag M τ_0 E_diag
  have h_ts := thermalTimeSliceCount_pos_and_step_bounds hβ_pos
  refine ⟨⟨h_ts.1, h_ts.2.2.2.1, h_ts.2.2.2.2, h_ts.2.2.1,
    gibbsBoltzmannOp_eq_pow_thermalTimeSliceStep H_diag hH_diag hβ_pos,
    gibbsBoltzmannOp_eq_pow_thermalTimeSliceStep H_shift hH_shift hβ_pos⟩,
    fun σ hσ => ?_, fun σ₁ σ₂ h_sep => ?_⟩
  · have h_H0 := (_root_.syndrome_resolution_indexed sys).2.2.2.2.1 σ
    have h_shift_act : (pauliDiagonalPart sys V R_pert - ((E_vac : ℝ) : ℂ) • 1) * sys.syndromeProjector σ =
        ((∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ : ℝ) : ℂ) • sys.syndromeProjector σ := by
      rw [h_shift_decomp, Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.sum_mul, Complex.ofReal_sum, clm_sum_smul]
      exact Finset.sum_congr rfl fun A hA => (h_scalar r hr A hA).1.1 σ hσ
    have h_op_act : H_diag * sys.syndromeProjector σ = ((E_diag σ : ℝ) : ℂ) • sys.syndromeProjector σ := by
      dsimp [H_diag, E_diag, perturbedDiagonalSyndromeEnergy]
      rw [add_sub_assoc, add_mul, h_H0, h_shift_act]; ext ψ; simp [Complex.ofReal_add, add_smul]
    have h_term_le : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
        |d_loc r A σ| ≤ (2 * J) * ∑ c ∈ rcaCollarChecks sys C_rca r A, if σ c then (1 : ℝ) else 0 := by
      intro r hr A hA
      by_cases h_cl : ∀ c ∈ rcaCollarChecks sys C_rca r A, σ c = false
      · rw [(h_scalar r hr A hA).2.1 σ h_cl, abs_zero]
        have h_nn : 0 ≤ ∑ c ∈ rcaCollarChecks sys C_rca r A, if σ c then (1 : ℝ) else 0 :=
          Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num
        positivity
      · push_neg at h_cl; rcases h_cl with ⟨c₀, hc₀_mem, hc₀_ne⟩
        have hc₀_true : σ c₀ = true := Bool.eq_true_of_not_eq_false hc₀_ne
        have h_one : (1 : ℝ) ≤ ∑ c ∈ rcaCollarChecks sys C_rca r A, if σ c then (1 : ℝ) else 0 := by
          have h_le := Finset.single_le_sum (f := fun c => if σ c then (1 : ℝ) else 0)
            (fun c _ => by (try dsimp only); split_ifs <;> norm_num) hc₀_mem
          simpa [hc₀_true] using h_le
        calc |d_loc r A σ| ≤ (2 * J) * 1 := by linarith [(h_scalar r hr A hA).1.2 σ]
          _ ≤ (2 * J) * ∑ c ∈ rcaCollarChecks sys C_rca r A, if σ c then (1 : ℝ) else 0 :=
              mul_le_mul_of_nonneg_left h_one (by linarith)
    let K_geom : ℝ := (((2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 : ℕ) : ℝ) ^ 3) * ((w_0 + 1 : ℕ) : ℝ)
    have h_scale : ∀ r ∈ Finset.Icc 1 (min R_pert L),
        (∑ A ∈ boxCubes 3 L r, (2 * J) * ∑ c ∈ rcaCollarChecks sys C_rca r A, if σ c then (1 : ℝ) else 0) ≤
          (2 * J) * (K_geom * sys.syndromeEnergy σ) := by
      intro r hr; have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
      rw [← Finset.mul_sum]; refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      have h_swap : (∑ A ∈ boxCubes 3 L r, ∑ c ∈ rcaCollarChecks sys C_rca r A, if σ c then (1 : ℝ) else 0) =
          ∑ c : StaticCSSCheckIdx L q_code m_max,
            (((boxCubes 3 L r).filter (fun A => sys.support c ⊆ rcaCollarCube C_rca r A)).card : ℝ) * (if σ c then (1 : ℝ) else 0) := by
        simp only [rcaCollarChecks, Finset.sum_filter]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => ?_
        have h_ite : ∀ A : Finset (Box3D L),
            (if sys.support c ⊆ rcaCollarCube C_rca r A then (if σ c then (1 : ℝ) else 0) else 0) =
              (if sys.support c ⊆ rcaCollarCube C_rca r A then (1 : ℝ) else 0) * (if σ c then (1 : ℝ) else 0) := fun A => by split_ifs <;> ring
        simp_rw [h_ite, ← Finset.sum_mul, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h_energy : K_geom * sys.syndromeEnergy σ =
          ∑ c : StaticCSSCheckIdx L q_code m_max, K_geom * (if σ c then (1 : ℝ) else 0) := by
        rw [← Finset.mul_sum]; congr 1; unfold IndexedCommutingProjectorHamiltonian.syndromeEnergy
        rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun c _ => ?_; rw [(h_sys_checks c).2.2]
      rw [h_swap, h_energy]; refine Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ (by split_ifs <;> norm_num)
      rcases staticCSSCheckSupport_nonempty D_field sys h_sys_checks c with ⟨v_c, hv_c⟩
      have h_sub_filter : (boxCubes 3 L r).filter (fun A => sys.support c ⊆ rcaCollarCube C_rca r A) ⊆
          (boxCubes 3 L r).filter (fun A => v_c ∈ enclosingBoxCube (anchorOfCube r A) r (linearExpansionRadius C_rca r)) := by
        intro A hA_f; rw [Finset.mem_filter] at hA_f ⊢; exact ⟨hA_f.1, hA_f.2 hv_c⟩
      have h_card1 : ((boxCubes 3 L r).filter (fun A => sys.support c ⊆ rcaCollarCube C_rca r A)).card ≤ (2 * linearExpansionRadius C_rca r) ^ 3 :=
        le_trans (Finset.card_le_card h_sub_filter) (card_filter_mem_enclosingBoxCube_le_pow r (linearExpansionRadius C_rca r) v_c)
      have h_rad_mono : linearExpansionRadius C_rca r ≤ linearExpansionRadius C_rca R_pert := by
        rcases le_or_gt 0 C_rca with hC | hC
        · exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hr_R) hC)
        · rw [linearExpansionRadius, Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hC) (Nat.cast_nonneg r))]; exact Nat.zero_le _
      have h_base : 2 * linearExpansionRadius C_rca r ≤ 2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 := by omega
      have h_card2 : ((boxCubes 3 L r).filter (fun A => sys.support c ⊆ rcaCollarCube C_rca r A)).card ≤
          (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1) :=
        le_trans h_card1 (le_trans (Nat.pow_le_pow_left h_base 3) (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)))
      dsimp only [K_geom]; exact_mod_cast h_card2
    have h_abs_sum : |∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ| ≤ (1 / 4 : ℝ) * sys.syndromeEnergy σ := by
      have h_tri : |∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A σ| ≤
          ∑ r ∈ Finset.Icc 1 (min R_pert L), (2 * J) * (K_geom * sys.syndromeEnergy σ) :=
        le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r hr =>
          le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum fun A hA => h_term_le r hr A hA) (h_scale r hr)))
      have h_card_Icc : ((Finset.Icc 1 (min R_pert L)).card : ℝ) ≤ (R_pert : ℝ) := by
        have h_nat : (Finset.Icc 1 (min R_pert L)).card ≤ R_pert := by rw [Nat.card_Icc]; have := Nat.min_le_left R_pert L; omega
        exact_mod_cast h_nat
      have hE_nn : 0 ≤ sys.syndromeEnergy σ := Finset.sum_nonneg fun i _ => le_trans zero_le_one (sys.weight_ge_one i)
      rw [Finset.sum_const, nsmul_eq_mul] at h_tri
      have h_tot := le_trans h_tri (mul_le_mul_of_nonneg_right h_card_Icc (by dsimp [K_geom]; positivity))
      have h_ring : (R_pert : ℝ) * ((2 * J) * (K_geom * sys.syndromeEnergy σ)) =
          (2 * rcaDiagonalCoercivityConstant 3 R_pert r_0 w_0 C_rca * J) * sys.syndromeEnergy σ := by
        unfold rcaDiagonalCoercivityConstant; dsimp [K_geom]; ring
      have h_q := mul_le_mul_of_nonneg_right hJ_small hE_nn
      linarith
    have h_abs_bounds := abs_le.mp h_abs_sum
    refine ⟨h_op_act, ?_, ?_⟩ <;> { dsimp [E_diag, perturbedDiagonalSyndromeEnergy]; linarith }
  · have h_slice_add : ∀ t : Fin M, E_diag (syndromeXor (σ₁ t) (σ₂ t)) = E_diag (σ₁ t) + E_diag (σ₂ t) := by
      intro t; rcases h_sep t with ⟨h_disj_t, h_col_t⟩
      have h_disj_pt : ∀ idx : StaticCSSCheckIdx L q_code m_max, ¬(σ₁ t idx = true ∧ σ₂ t idx = true) :=
        fun idx ⟨h1, h2⟩ => Finset.disjoint_left.mp h_disj_t
          (Finset.mem_filter.mpr ⟨Finset.mem_univ idx, h1⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ idx, h2⟩)
      have h_E0_add := syndromeEnergy_syndromeXor_eq_add_of_disjoint sys h_disj_pt
      have h_d_add : ∀ r ∈ Finset.Icc 1 (min R_pert L), ∀ A ∈ boxCubes 3 L r,
          d_loc r A (syndromeXor (σ₁ t) (σ₂ t)) = d_loc r A (σ₁ t) + d_loc r A (σ₂ t) := by
        intro r hr A hA; rcases h_col_t r hr A hA with h_disj1 | h_disj2
        · have h_cl1 : ∀ c ∈ rcaCollarChecks sys C_rca r A, σ₁ t c = false := fun c hc => by
            by_contra h_ne
            exact Finset.disjoint_left.mp h_disj1 hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, Bool.eq_true_of_not_eq_false h_ne⟩)
          have h_ag : ∀ c ∈ rcaCollarChecks sys C_rca r A, syndromeXor (σ₁ t) (σ₂ t) c = σ₂ t c := by
            intro c hc; dsimp [syndromeXor]; rw [h_cl1 c hc]; cases σ₂ t c <;> rfl
          rw [(h_scalar r hr A hA).2.2 _ _ h_ag, (h_scalar r hr A hA).2.1 (σ₁ t) h_cl1, zero_add]
        · have h_cl2 : ∀ c ∈ rcaCollarChecks sys C_rca r A, σ₂ t c = false := fun c hc => by
            by_contra h_ne
            exact Finset.disjoint_left.mp h_disj2 hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, Bool.eq_true_of_not_eq_false h_ne⟩)
          have h_ag : ∀ c ∈ rcaCollarChecks sys C_rca r A, syndromeXor (σ₁ t) (σ₂ t) c = σ₁ t c := by
            intro c hc; dsimp [syndromeXor]; rw [h_cl2 c hc]; cases σ₁ t c <;> rfl
          rw [(h_scalar r hr A hA).2.2 _ _ h_ag, (h_scalar r hr A hA).2.1 (σ₂ t) h_cl2, add_zero]
      dsimp [E_diag, perturbedDiagonalSyndromeEnergy]
      have h_sum_d :
          (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A (syndromeXor (σ₁ t) (σ₂ t))) =
            (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A (σ₁ t)) +
              (∑ r ∈ Finset.Icc 1 (min R_pert L), ∑ A ∈ boxCubes 3 L r, d_loc r A (σ₂ t)) := by
        rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun r hr => ?_
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun A hA => h_d_add r hr A hA
      linarith
    simp_rw [h_slice_add, Finset.sum_add_distrib, mul_add, Real.exp_add]

/-! ## 5. Active vs. Spectator Off-Diagonal Jump Partition & Norm Bounds -/

/-- **Active Off-Diagonal Jump Sum Around an Active Check Set (`offDiagonalActiveJumpPart`)** -/
def offDiagonalActiveJumpPart {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (R_pert : ℕ)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (S_act : Finset (StaticCSSCheckIdx L q_code m_max)) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  ∑ r ∈ Finset.Icc 1 (min R_pert L),
    ∑ A ∈ (boxCubes 3 L r).filter (fun A => ¬Disjoint (cubeIntersectingChecks sys A) S_act),
      pauliOffDiagonalTerm sys V r A

/-- **Spectator Off-Diagonal Jump Sum Outside an Active Check Set (`offDiagonalSpectatorJumpPart`)** -/
def offDiagonalSpectatorJumpPart {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (R_pert : ℕ)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    (S_act : Finset (StaticCSSCheckIdx L q_code m_max)) :
    ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) :=
  ∑ r ∈ Finset.Icc 1 (min R_pert L),
    ∑ A ∈ (boxCubes 3 L r).filter (fun A => Disjoint (cubeIntersectingChecks sys A) S_act),
      pauliOffDiagonalTerm sys V r A

theorem commute_pauliOffDiagonalTerm_of_isSupportedOn_disjoint
    {L q_code m_max : ℕ}
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig q_code)))
    {r : ℕ} {A S_c : Finset (Box3D L)}
    (hK_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A
      (pauliOffDiagonalTerm sys V r A))
    {P : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code))}
    (hP_supp : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) S_c P)
    (h_disj : Disjoint A S_c) :
    Commute (pauliOffDiagonalTerm sys V r A) P :=
  KMSPinchedGibbs.commute_of_isSupportedOn_disjoint h_disj hK_supp hP_supp

private lemma card_filter_not_disjoint_boxBall_le {L : ℕ} [NeZero L]
    (v : Box3D L) (r r_0 : ℕ) {S : Finset (Box3D L)} (hS : S ⊆ boxBall v r_0) :
    ((boxCubes 3 L r).filter (fun A => ¬Disjoint A S)).card ≤ (r + 2 * r_0 + 1) ^ 3 := by
  have hL_pos : 0 < L := NeZero.pos L
  let M : ℕ := r + 2 * r_0 + 1
  let g : (Fin 3 → Fin M) → Finset (Box3D L) := fun k =>
    boxCube (fun i => ⟨min (L - 1) ((v i).val + r_0 - (k i).val),
      Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩) r
  have h_sub : (boxCubes 3 L r).filter (fun A => ¬Disjoint A S) ⊆ Finset.univ.image g := by
    intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hA_mem, h_nd⟩
    rcases Finset.not_disjoint_iff.mp h_nd with ⟨y, hyA, hyS⟩
    have hyv : y ∈ boxBall v r_0 := hS hyS
    simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at hyv
    let xA := anchorOfCube r A
    have hA_eq : boxCube xA r = A := boxCube_anchorOfCube hA_mem
    rw [← hA_eq, mem_boxCube] at hyA
    have hy_dist : ∀ i : Fin 3, coordDist (v i) (y i) ≤ r_0 := fun i =>
      le_trans (Finset.le_sup (f := fun j => coordDist (v j) (y j)) (Finset.mem_univ i)) hyv
    have hk_lt : ∀ i : Fin 3, (v i).val + r_0 - (xA i).val < M := by
      intro i; have := hyA i; have := hy_dist i; dsimp [coordDist, M] at *; omega
    let k : Fin 3 → Fin M := fun i => ⟨(v i).val + r_0 - (xA i).val, hk_lt i⟩
    have h_anchor : (fun i : Fin 3 => (⟨min (L - 1) ((v i).val + r_0 - (k i).val),
        Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (Nat.sub_lt hL_pos zero_lt_one)⟩ : Fin L)) = xA := by
      funext i; apply Fin.ext
      have := hyA i; have := hy_dist i; have := (xA i).isLt
      dsimp [coordDist] at *
      change min (L - 1) ((v i).val + r_0 - ((v i).val + r_0 - (xA i).val)) = (xA i).val
      omega
    rw [Finset.mem_image]
    exact ⟨k, Finset.mem_univ k, by dsimp [g]; rw [h_anchor, hA_eq]⟩
  calc ((boxCubes 3 L r).filter (fun A => ¬Disjoint A S)).card
    _ ≤ (Finset.univ.image g).card := Finset.card_le_card h_sub
    _ ≤ (Finset.univ : Finset (Fin 3 → Fin M)).card := Finset.card_image_le
    _ = M ^ 3 := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem card_filter_not_disjoint_cubeIntersectingChecks_le
    {L q_code r_0 m_max w_0 R_pert : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig q_code))
      (StaticCSSCheckIdx L q_code m_max))
    (h_geom : sys.IsGeometricallyLocal r_0 w_0) (C_rca : ℝ)
    (S_act : Finset (StaticCSSCheckIdx L q_code m_max))
    {r : ℕ} (hr : r ∈ Finset.Icc 1 (min R_pert L)) :
    ((boxCubes 3 L r).filter (fun A => ¬Disjoint (cubeIntersectingChecks sys A) S_act)).card ≤
      S_act.card * ((2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1)) := by
  let K_geom : ℕ :=
    (2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1) ^ 3 * (w_0 + 1)
  have hr_R : r ≤ R_pert := le_trans (Finset.mem_Icc.mp hr).2 (Nat.min_le_left R_pert L)
  have h_sub_biUnion :
      (boxCubes 3 L r).filter (fun A => ¬Disjoint (cubeIntersectingChecks sys A) S_act) ⊆
        S_act.biUnion (fun c => (boxCubes 3 L r).filter (fun A => ¬Disjoint A (sys.support c))) := by
    intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hA_mem, h_nd⟩
    rcases Finset.not_disjoint_iff.mp h_nd with ⟨c, hc_inter, hc_S⟩
    simp only [cubeIntersectingChecks, Finset.mem_filter, Finset.mem_univ, true_and] at hc_inter
    exact Finset.mem_biUnion.mpr ⟨c, hc_S, Finset.mem_filter.mpr ⟨hA_mem, fun h => hc_inter h.symm⟩⟩
  have h_each_c : ∀ c ∈ S_act,
      ((boxCubes 3 L r).filter (fun A => ¬Disjoint A (sys.support c))).card ≤ K_geom := by
    intro c _
    rcases h_geom.1 c with ⟨v, hv⟩
    have h_c1 := card_filter_not_disjoint_boxBall_le v r r_0 hv
    have h_base : r + 2 * r_0 + 1 ≤ 2 * (R_pert + 2 * linearExpansionRadius C_rca R_pert + r_0) + 1 := by
      omega
    exact le_trans h_c1 (le_trans (Nat.pow_le_pow_left h_base 3)
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos w_0)))
  calc ((boxCubes 3 L r).filter (fun A => ¬Disjoint (cubeIntersectingChecks sys A) S_act)).card
    _ ≤ (S_act.biUnion (fun c => (boxCubes 3 L r).filter (fun A => ¬Disjoint A (sys.support c)))).card :=
        Finset.card_le_card h_sub_biUnion
    _ ≤ ∑ c ∈ S_act, ((boxCubes 3 L r).filter (fun A => ¬Disjoint A (sys.support c))).card :=
        Finset.card_biUnion_le
    _ ≤ S_act.card • K_geom := Finset.sum_le_card_nsmul S_act _ K_geom h_each_c
    _ = S_act.card * K_geom := smul_eq_mul _ _

end SpacetimeWorldlineKP
end
