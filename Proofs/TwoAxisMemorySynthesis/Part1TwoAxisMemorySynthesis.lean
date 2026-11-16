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

import Proofs.TwoAxisMemorySynthesis.CodeSlotMemoryAndReindex

/-!
# Synthesis of Part I Main Theorem: Unperturbed Thermal Self-Correction and Zero-Temperature Perturbative Stability

Combines the cubic-lattice welded CSS Hamiltonian realization, multiscale cluster-decoded logical observables, unperturbed stretched-exponential Peierls and KMS-Lindblad bounds, and QAC-dressed zero-temperature spectral and Heisenberg memory stability on uniform qudit sites `Fin dLocBDL` to prove `part1_thermally_and_perturbatively_stable_memory_main`.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 5.5 (`subsec:unperturbed-kms-lifetime`), Theorem 5.8 (`thm:unperturbed-kms-lifetime`)
* Part I, Section 7.3 (`subsec:zero-temp-dressed-memory`), Theorem 7.4 (`thm:zero-temp-dressed-memory`)
* Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`)
* Part I, Section 8.1 (`subsec:conceptual-synthesis`)
-/

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Part1TwoAxisMemorySynthesis

private lemma q_code_BDL_ge_one : 1 ≤ qCodeBDL := by decide
private lemma r_0_BDL_ge_one : 1 ≤ r0BDL := by decide
private lemma w_0_BDL_ge_one : 1 ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by decide
lemma two_le_bdlLambda : 2 ≤ bdlLambda := by decide
lemma bdlBoxSide_eq_bdlLambda_pow (k : ℕ) : bdlBoxSide k = bdlLambda ^ (2 * k + 4) := rfl
lemma four_mul_r0BDL_add_one_le_37_mul_pow (k : ℕ) :
    4 * r0BDL + 1 ≤ 37 * bdlLambda ^ k := by
  have h37 : 4 * r0BDL + 1 = 37 := by decide
  have h1 : 1 ≤ bdlLambda ^ k := Nat.one_le_pow k bdlLambda bdlLambda_pos
  omega
lemma bdlLambda_pow_le_37_mul_pow (k : ℕ) :
    bdlLambda ^ k ≤ 37 * bdlLambda ^ k := Nat.le_mul_of_pos_left _ (by decide)
lemma one_le_bdlLambda : 1 ≤ bdlLambda := le_trans (by decide : 1 ≤ 2) two_le_bdlLambda

lemma self_le_bdlLambda_pow (k : ℕ) : k ≤ bdlLambda ^ k := by
  induction k with
  | zero => omega
  | succ n ih =>
    have h1 : 1 ≤ bdlLambda ^ n := Nat.one_le_pow n bdlLambda bdlLambda_pos
    have h2 : n + 1 ≤ 2 * bdlLambda ^ n := by omega
    have h3 : 2 * bdlLambda ^ n ≤ bdlLambda * bdlLambda ^ n :=
      Nat.mul_le_mul_right (bdlLambda ^ n) two_le_bdlLambda
    rw [Nat.pow_succ']
    exact le_trans h2 h3

lemma exists_k_pad_le_37_mul_bdlLambda_pow (R_bath : ℕ) :
    ∃ k_pad : ℕ, ∀ k : ℕ, k_pad ≤ k → R_bath + 2 * bdlLambda ^ k ≤ 37 * bdlLambda ^ k := by
  refine ⟨R_bath, fun k hk => ?_⟩
  have h1 : R_bath ≤ bdlLambda ^ k := le_trans hk (self_le_bdlLambda_pow k)
  omega

private lemma clm_neg_mul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) : (-A) * B = -(A * B) := by ext ψ; simp
private lemma clm_mul_neg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →L[ℂ] H) : A * (-B) = -(A * B) := by ext ψ; simp
private lemma clm_neg_one_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) : (-1 : ℂ) • A = -A := by ext ψ; simp

private lemma decoded_anticommute_and_ne_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P0 Pi_safe Z_log X_log D_Z D_X : H →L[ℂ] H)
    (hZ_DX : Commute Z_log D_X) (hX_DZ : Commute X_log D_Z) (hDZ_DX : Commute D_Z D_X)
    (h_anti_bare : X_log * Z_log = -(Z_log * X_log))
    (hOZ_P0_eq : (Z_log * D_Z) * P0 = Z_log * P0) (hZ_P0_ne : Z_log * P0 ≠ 0)
    (hOX_P0_eq : (X_log * D_X) * P0 = X_log * P0) (hX_P0_ne : X_log * P0 ≠ 0) :
    Pi_safe * (Z_log * D_Z) * (X_log * D_X) * Pi_safe =
      -(Pi_safe * (X_log * D_X) * (Z_log * D_Z) * Pi_safe) ∧
    (Z_log * D_Z) * P0 ≠ 0 ∧
    (X_log * D_X) * P0 ≠ 0 := by
  have h_anti_O : (X_log * D_X) * (Z_log * D_Z) = -((Z_log * D_Z) * (X_log * D_X)) := by
    calc (X_log * D_X) * (Z_log * D_Z)
      _ = X_log * (D_X * Z_log) * D_Z := by simp only [mul_assoc]
      _ = (X_log * Z_log) * (D_X * D_Z) := by rw [hZ_DX.symm.eq]; simp only [mul_assoc]
      _ = -(Z_log * X_log) * (D_Z * D_X) := by rw [h_anti_bare, hDZ_DX.symm.eq]
      _ = -(Z_log * (X_log * D_Z) * D_X) := by simp only [clm_neg_mul, mul_assoc]
      _ = -((Z_log * D_Z) * (X_log * D_X)) := by rw [hX_DZ.eq]; simp only [mul_assoc]
  have h_anti_Pi : Pi_safe * (Z_log * D_Z) * (X_log * D_X) * Pi_safe =
      -(Pi_safe * (X_log * D_X) * (Z_log * D_Z) * Pi_safe) := by
    calc Pi_safe * (Z_log * D_Z) * (X_log * D_X) * Pi_safe
      _ = Pi_safe * ((Z_log * D_Z) * (X_log * D_X)) * Pi_safe := by simp only [mul_assoc]
      _ = -(Pi_safe * (-((Z_log * D_Z) * (X_log * D_X))) * Pi_safe) := by
        simp only [clm_mul_neg, clm_neg_mul, neg_neg]
      _ = -(Pi_safe * ((X_log * D_X) * (Z_log * D_Z)) * Pi_safe) := by rw [h_anti_O]
      _ = -(Pi_safe * (X_log * D_X) * (Z_log * D_Z) * Pi_safe) := by simp only [mul_assoc]
  exact ⟨h_anti_Pi,
    fun h => hZ_P0_ne (hOZ_P0_eq.symm.trans h),
    fun h => hX_P0_ne (hOX_P0_eq.symm.trans h)⟩

attribute [local irreducible]
  collarConstRCABDL bdlLambda bBDL bdlHierarchySteps qCodeBDL r0BDL mMaxBDL
  IndexedCommutingProjectorHamiltonian.H0 IndexedCommutingProjectorHamiltonian.groundProj
  IndexedCommutingProjectorHamiltonian.localGroundProj
  IndexedCommutingProjectorHamiltonian.groundSpace IndexedCommutingProjectorHamiltonian.groundDegeneracy
  IndexedCommutingProjectorHamiltonian.syndromeProjector QuasiLocalPerturbation.totalPerturbation
  gibbsFailureProb opKMSNormSq SatisfiesKMSLindbladODE heisenbergFlow condExp IsSupportedOn
  syndromeSignOp syndromeSubsetProj bdlSafeSyndromeSet bdlWeldedCode bdlLocalDescriptor
  weylPauliZ weylPauliX bdlPushChain

/-!
## 1. Part I, Theorem 7.5 (`thm:main`) Synthesis: Unperturbed Thermal & Zero-Temperature Perturbative Stability
-/

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]

/-- Assembles `SatisfiesZeroTempPerturbativeMemoryStability (sys.reindex e_chk)` for an
    abstract check index equivalence `e_chk : Idx ≃ Fin N_c`. -/
lemma satisfiesZeroTempPerturbativeMemoryStability_of_dressing_bundle
    {L N_c R_bath : ℕ} [NeZero L]
    (e_chk : StaticCSSCheckIdx L qCodeBDL mMaxBDL ≃ Fin N_c)
    (m : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
    (V : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL)))
    (δ_0 δ_split : ℝ) (g_LR : ℕ → ℝ)
    (hδ_le : δ_0 ≤ δ_split)
    (h_bundle : HasZeroTempDressingBundle m V δ_0 g_LR)
    (h_cube_dress : ∀ (U_dress : unitary ℬ[L, CodeSlotConfig qCodeBDL]),
      IsQuasiLocalUnitary U_dress g_LR →
      ∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r,
        ∀ M_W : ℬ[L, CodeSlotConfig qCodeBDL],
          IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) W M_W →
          ‖(U_dress.1 * m.Pi_safe * U_dress.1†) *
              (M_W * (U_dress.1 * m.O_dec_Z * U_dress.1†) -
                (U_dress.1 * m.O_dec_Z * U_dress.1†) * M_W) *
              (U_dress.1 * m.Pi_safe * U_dress.1†)‖ ≤ δ_split * ‖M_W‖ ∧
          ‖(U_dress.1 * m.Pi_safe * U_dress.1†) *
              (M_W * (U_dress.1 * m.O_dec_X * U_dress.1†) -
                (U_dress.1 * m.O_dec_X * U_dress.1†) * M_W) *
              (U_dress.1 * m.Pi_safe * U_dress.1†)‖ ≤ δ_split * ‖M_W‖) :
    SatisfiesZeroTempPerturbativeMemoryStability
      (N_checks := N_c) (m.sys.reindex e_chk) m.Pi_safe m.O_dec_Z m.O_dec_X V R_bath δ_split g_LR := by
  rcases h_bundle with ⟨U_dress, E0, h_dress⟩
  have hP0_sa : IsSelfAdjoint m.sys.P0 := m.sys.isStarProjection_P0.isSelfAdjoint
  have hOZ := m.h_decoder_props.2.1; have hOX := m.h_decoder_props.2.2.1
  have hZ := m.h_logical_pair.2.1; have hX := m.h_logical_pair.2.2.1
  have hP0_OZ : Commute m.sys.P0 m.O_dec_Z :=
    commute_P0_of_mul_P0_eq hP0_sa hOZ.1 hZ.1 hZ.2.2.2 hOZ.2.2.2.2.1
  have hP0_OX : Commute m.sys.P0 m.O_dec_X :=
    commute_P0_of_mul_P0_eq hP0_sa hOX.1 hX.1 hX.2.2.2 hOX.2.2.2.2.1
  have hH0 : (m.sys.reindex e_chk).H0 = m.sys.H0 := m.sys.reindex_H0 e_chk
  have h_comm_P0 :
      ‖(m.sys.H0 + V.totalPerturbation) * (U_dress.1 * m.sys.P0 * U_dress.1†) -
        (U_dress.1 * m.sys.P0 * U_dress.1†) * (m.sys.H0 + V.totalPerturbation)‖ ≤ δ_split / 6 :=
    le_trans h_dress.2.1 (by linarith)
  have hδ_nn : 0 ≤ δ_split := by linarith [le_trans (norm_nonneg _) h_comm_P0]
  have h_form_q : ∀ ψ : ℋ[L, CodeSlotConfig qCodeBDL],
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (m.sys.H0 + V.totalPerturbation) * U_dress.1 - m.sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        bhmSandwichDeviation * RCLike.re (inner ℂ ψ (m.sys.H0 ψ)) + (δ_split / 4) * ‖ψ‖ ^ 2 := by
    intro ψ
    have h1 := h_dress.2.2.1 ψ
    have h2 : (δ_0 / 4) * ‖ψ‖ ^ 2 ≤ (δ_split / 4) * ‖ψ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  have h_form' : ∀ ψ : ℋ[L, CodeSlotConfig qCodeBDL],
      |RCLike.re (inner ℂ ψ
          ((U_dress.1† * (m.sys.H0 + V.totalPerturbation) * U_dress.1 - m.sys.H0 - (E0 : ℂ) • 1) ψ))| ≤
        (1 / 4 : ℝ) * RCLike.re (inner ℂ ψ (m.sys.H0 ψ)) + (δ_split / 2) * ‖ψ‖ ^ 2 := by
    intro ψ
    have h1 := h_form_q ψ
    rw [show bhmSandwichDeviation = (1 / 4 : ℝ) from rfl] at h1
    have h2 : (δ_split / 4) * ‖ψ‖ ^ 2 ≤ (δ_split / 2) * ‖ψ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  have h_1site := h_dress.2.2.2.2.2
  refine ⟨U_dress, E0, h_dress.1, ?_, ?_, ?_, ?_⟩
  · rw [hH0, m.sys.reindex_P0 e_chk]; exact le_trans h_comm_P0 (by linarith)
  · rw [hH0, m.sys.reindex_P0 e_chk]
    exact dressed_ground_subspace_splitting_opNorm_le m.sys V U_dress h_form'
  · intro ψ; rw [hH0]; exact h_form' ψ
  · intro O_0 hO_cases
    rcases hO_cases with rfl | rfl
    · have h_coh_Z : ‖(U_dress.1 * m.Pi_safe * U_dress.1†) *
          ((m.sys.H0 + V.totalPerturbation) * (U_dress.1 * m.O_dec_Z * U_dress.1†) -
            (U_dress.1 * m.O_dec_Z * U_dress.1†) * (m.sys.H0 + V.totalPerturbation)) *
          (U_dress.1 * m.Pi_safe * U_dress.1†)‖ ≤ δ_split := le_trans h_dress.2.2.2.1 hδ_le
      refine ⟨by rwa [hH0],
        fun v A_v hA_v =>
          le_trans (h_1site v A_v hA_v).1 (mul_le_mul_of_nonneg_right hδ_le (norm_nonneg _)),
        fun r hr W hW M_W hM_W => (h_cube_dress U_dress h_dress.1 r hr W hW M_W hM_W).1,
        fun t ht => ?_⟩
      rw [hH0, m.sys.reindex_P0 e_chk]
      exact zero_temp_heisenberg_ground_drift_of_relative_form
        m.sys V U_dress m.O_dec_Z hP0_OZ hOZ.2.2.1 h_comm_P0 h_form_q t ht
    · have h_coh_X : ‖(U_dress.1 * m.Pi_safe * U_dress.1†) *
          ((m.sys.H0 + V.totalPerturbation) * (U_dress.1 * m.O_dec_X * U_dress.1†) -
            (U_dress.1 * m.O_dec_X * U_dress.1†) * (m.sys.H0 + V.totalPerturbation)) *
          (U_dress.1 * m.Pi_safe * U_dress.1†)‖ ≤ δ_split := le_trans h_dress.2.2.2.2.1 hδ_le
      refine ⟨by rwa [hH0],
        fun v A_v hA_v =>
          le_trans (h_1site v A_v hA_v).2 (mul_le_mul_of_nonneg_right hδ_le (norm_nonneg _)),
        fun r hr W hW M_W hM_W => (h_cube_dress U_dress h_dress.1 r hr W hW M_W hM_W).2,
        fun t ht => ?_⟩
      rw [hH0, m.sys.reindex_P0 e_chk]
      exact zero_temp_heisenberg_ground_drift_of_relative_form
        m.sys V U_dress m.O_dec_X hP0_OX hOX.2.2.1 h_comm_P0 h_form_q t ht

/-- Deduces dressed `R_bath`-cube safe-subspace commutator bounds from bare `R_imm`-cube immunity
    (`HasSafeDecodedLogicalObservables`) via `dressed_cube_safe_commutator_telescoping`. -/
lemma dressed_cube_commutator_le_of_hasSafeDecodedLogicalObservables
    {L N_c R_bath R_cut R_imm : ℕ} [NeZero L]
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig qCodeBDL)) (Fin N_c))
    (Pi_safe O_dec_Z O_dec_X : ℬ[L, CodeSlotConfig qCodeBDL])
    (h_obs : HasSafeDecodedLogicalObservables sys Pi_safe O_dec_Z O_dec_X R_imm)
    {g_LR : ℕ → ℝ} (hg_nn : 0 ≤ g_LR R_cut)
    (h_pad : R_bath + 2 * R_cut ≤ R_imm)
    (U_dress : unitary ℬ[L, CodeSlotConfig qCodeBDL])
    (hU : IsQuasiLocalUnitary U_dress g_LR) :
    ∀ r ∈ Finset.Icc 1 (min R_bath L), ∀ W ∈ boxCubes 3 L r,
      ∀ M_W : ℬ[L, CodeSlotConfig qCodeBDL],
        IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) W M_W →
        let δ_ch' := 2 * ((R_bath ^ 3 : ℕ) : ℝ) *
          (((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) * g_LR R_cut)
        ‖(U_dress.1 * Pi_safe * U_dress.1†) *
            (M_W * (U_dress.1 * O_dec_Z * U_dress.1†) -
              (U_dress.1 * O_dec_Z * U_dress.1†) * M_W) *
            (U_dress.1 * Pi_safe * U_dress.1†)‖ ≤ δ_ch' * ‖M_W‖ ∧
        ‖(U_dress.1 * Pi_safe * U_dress.1†) *
            (M_W * (U_dress.1 * O_dec_X * U_dress.1†) -
              (U_dress.1 * O_dec_X * U_dress.1†) * M_W) *
            (U_dress.1 * Pi_safe * U_dress.1†)‖ ≤ δ_ch' * ‖M_W‖ := by
  have : Nonempty (CodeSlotConfig qCodeBDL) := ⟨fun _ => false⟩
  rcases h_obs with
    ⟨_, _, _, hPi_proj, _, _, _, _, _, _, hOZ_norm, _, _, _, _, _, hOX_norm, _, _, _, _, _, _, _, _, h_cube⟩
  have hPi_norm : ‖Pi_safe‖ ≤ 1 := isStarProjection_opNorm_le_one_ground hPi_proj
  have hU_cut : ∀ (u : Box3D L) (A_u : ℬ[L, CodeSlotConfig qCodeBDL]),
      IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {u} A_u →
      ‖U_dress.1† * A_u * U_dress.1 -
        condExp (UniformSite3D L (CodeSlotConfig qCodeBDL)) (boxBall u R_cut)
          (U_dress.1† * A_u * U_dress.1)‖ ≤ ‖A_u‖ * g_LR R_cut :=
    fun u A_u hA => hU u A_u hA R_cut
  intro r hr W hW M_W hM_W
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr_min : r ≤ min R_bath L := (Finset.mem_Icc.mp hr).2
  have hr_bath : r ≤ R_bath := le_trans hr_min (min_le_left _ _)
  have hr_L : r ≤ L := le_trans hr_min (min_le_right _ _)
  have hr_pad : r + 2 * R_cut ≤ R_imm := by omega
  have h_r3 : ((r ^ 3 : ℕ) : ℝ) ≤ ((R_bath ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_left hr_bath 3
  have h_card_pow :
      ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * r ^ 3) : ℕ) : ℝ) ≤
        ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right Fintype.card_pos
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hr_bath 3))
  have h_coef_le :
      2 * ((r ^ 3 : ℕ) : ℝ) *
        (((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * r ^ 3) : ℕ) : ℝ) * g_LR R_cut) ≤
      2 * ((R_bath ^ 3 : ℕ) : ℝ) *
        (((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) * g_LR R_cut) := by
    have h_mul1 :
        ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * r ^ 3) : ℕ) : ℝ) * g_LR R_cut ≤
          ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) * g_LR R_cut :=
      mul_le_mul_of_nonneg_right h_card_pow hg_nn
    exact mul_le_mul (by linarith) h_mul1 (by positivity) (by positivity)
  have hZ := dressed_cube_safe_commutator_telescoping U_dress Pi_safe O_dec_Z
    hg_nn hPi_norm hOZ_norm hU_cut
    (fun r' hr' A hA M_A hM_A => (h_cube r' hr' A hA M_A hM_A).1)
    hr1 hr_L hr_pad hW M_W hM_W
  have hX := dressed_cube_safe_commutator_telescoping U_dress Pi_safe O_dec_X
    hg_nn hPi_norm hOX_norm hU_cut
    (fun r' hr' A hA M_A hM_A => (h_cube r' hr' A hA M_A hM_A).2)
    hr1 hr_L hr_pad hW M_W hM_W
  exact ⟨le_trans hZ (mul_le_mul_of_nonneg_right h_coef_le (norm_nonneg _)),
    le_trans hX (mul_le_mul_of_nonneg_right h_coef_le (norm_nonneg _))⟩

/-- Geometric locality `(r_0_BDL, (2 * r_0_BDL + 1) ^ 3 * (q_code_BDL + 2 * m_max_BDL))`
    of `(bdlInhomogeneousSystem k).reindex e_chk` for an arbitrary equivalence `e_chk`. -/
lemma isGeometricallyLocal_bdlInhomogeneousSystem_reindex (k : ℕ) {N_c : ℕ}
    (e_chk : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin N_c) :
    let w_0 := (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)
    ((bdlInhomogeneousSystem k).reindex e_chk).IsGeometricallyLocal r0BDL w_0 := by
  intro w_0
  let L := bdlBoxSide k
  refine ⟨fun i => ⟨staticCSSCheckSite (e_chk.symm i),
    (staticCSSCheckSite_mem_and_subset_boxBall (bdlLocalDescriptor k) (e_chk.symm i)).2⟩, fun v => ?_⟩
  let S_fin := Finset.univ.filter (fun i : Fin N_c =>
    v ∈ ((bdlInhomogeneousSystem k).reindex e_chk).support i)
  let P_ball : Finset (Box3D L × (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)) :=
    (boxBall v r0BDL) ×ˢ Finset.univ
  have h_sub : S_fin.image e_chk.symm ⊆ P_ball.image mkStaticCSSCheckIdx := by
    intro idx hidx
    rcases Finset.mem_image.mp hidx with ⟨i, hi, rfl⟩
    have hv_mem : v ∈ staticCSSCheckSupport (bdlLocalDescriptor k) (e_chk.symm i) :=
      (Finset.mem_filter.mp hi).2
    have h_ball :=
      (staticCSSCheckSite_mem_and_subset_boxBall (bdlLocalDescriptor k) (e_chk.symm i)).2 hv_mem
    have h_site_mem : staticCSSCheckSite (e_chk.symm i) ∈ boxBall v r0BDL := by
      simp only [boxBall, Finset.mem_filter, Finset.mem_univ, true_and] at h_ball ⊢
      rwa [boxDist_comm]
    rw [Finset.mem_image]
    exact ⟨(staticCSSCheckSite (e_chk.symm i), staticCSSCheckSlot (e_chk.symm i)),
      Finset.mem_product.mpr ⟨h_site_mem, Finset.mem_univ _⟩,
      mkStaticCSSCheckIdx_site_slot (e_chk.symm i)⟩
  calc S_fin.card
    _ = (S_fin.image e_chk.symm).card :=
        (Finset.card_image_of_injective S_fin e_chk.symm.injective).symm
    _ ≤ (P_ball.image mkStaticCSSCheckIdx).card := Finset.card_le_card h_sub
    _ ≤ P_ball.card := Finset.card_image_le
    _ = (boxBall v r0BDL).card *
        (Finset.univ : Finset (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)).card :=
      Finset.card_product _ _
    _ ≤ (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL) := by
      have h1 := card_boxBall_le_pow v r0BDL
      have h2 : (Finset.univ : Finset (Fin qCodeBDL ⊕ Fin mMaxBDL ⊕ Fin mMaxBDL)).card =
          qCodeBDL + 2 * mMaxBDL := by
        rw [Finset.card_univ, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
        omega
      rw [h2]; exact Nat.mul_le_mul_right _ h1

private lemma bdlInhomogeneousSystem_checks (k : ℕ)
    (idx : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :
    (bdlInhomogeneousSystem k).checkProj idx = staticCSSCheckProj (bdlLocalDescriptor k) idx ∧
    (bdlInhomogeneousSystem k).support idx = staticCSSCheckSupport (bdlLocalDescriptor k) idx ∧
    (bdlInhomogeneousSystem k).weight idx = 1 := ⟨rfl, rfl, rfl⟩

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

private lemma satisfiesDecayBound_reindexPerturbation {L : ℕ}
    {SiteA SiteB : Type} [Fintype SiteA] [DecidableEq SiteA] [Fintype SiteB] [DecidableEq SiteB]
    (e_inv : ∀ _ : Box3D L, SiteB ≃ SiteA)
    (V₁ : QuasiLocalPerturbation 3 L (UniformSite3D L SiteB))
    {J : ℝ} {f : ℕ → ℝ} (hV₁ : V₁.SatisfiesDecayBound J f) :
    (reindexPerturbation e_inv V₁).SatisfiesDecayBound J f := by
  intro r hr A hA
  change ‖conjSiteOp e_inv (V₁.term r A)‖ ≤ J * f r
  rw [norm_conjSiteOp]; exact hV₁ r hr A hA

/-- Assembles `Inhomogeneous3DMemoryRealization` and `HasSafeDecodedLogicalObservables`
    over an abstract box size `L` and plain parameters (no `let`-bindings)
    so the Lean 4 kernel checks the declaration without unfolding `bdlBoxSide k`. -/
private lemma codeSlot_memory_package_of_components
    {L N_c r_fw R_imm : ℕ} [NeZero L]
    (D_field : Box3D L → LocalCSSDescriptor qCodeBDL r0BDL mMaxBDL)
    (h_D_valid : ValidDescriptorField D_field)
    (sys : IndexedCommutingProjectorHamiltonian 3 L
      (UniformSite3D L (CodeSlotConfig qCodeBDL))
      (StaticCSSCheckIdx L qCodeBDL mMaxBDL))
    (h_sys_checks : ∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
       sys.checkProj idx = staticCSSCheckProj D_field idx ∧
       sys.support idx = staticCSSCheckSupport D_field idx ∧
       sys.weight idx = 1)
    (h_tqo :
      SatisfiesTQO1 sys (Nat.floor (cStarBDL * (L : ℝ))) ∧
      SatisfiesLinearTQO2 sys (Nat.floor (cStarBDL * (L : ℝ))) (collarConstRCABDL : ℝ) ∧
      SatisfiesSectorFilteredLinearTQO2 sys 1 (Nat.floor (cStarBDL * (L : ℝ))) (collarConstRCABDL : ℝ))
    (e_chk : StaticCSSCheckIdx L qCodeBDL mMaxBDL ≃ Fin N_c)
    (Z_log X_log : ℬ[L, CodeSlotConfig qCodeBDL])
    (S_safe : Finset (StaticCSSCheckIdx L qCodeBDL mMaxBDL → Bool))
    (sgn_Z sgn_X : (StaticCSSCheckIdx L qCodeBDL mMaxBDL → Bool) → ZMod 2)
    (h_p0_ne : sys.P0 ≠ 0 ∧ sys.P0 ≠ 1)
    (h_bare_Z : IsSelfAdjoint Z_log ∧ Z_log * Z_log = 1 ∧ Commute sys.H0 Z_log ∧ Commute sys.P0 Z_log)
    (h_bare_X : IsSelfAdjoint X_log ∧ X_log * X_log = 1 ∧ Commute sys.H0 X_log ∧ Commute sys.P0 X_log)
    (h_bare_rest : (Z_log * X_log + X_log * Z_log) * sys.P0 = 0 ∧ (Z_log * sys.P0 ≠ 0 ∧ X_log * sys.P0 ≠ 0))
    (hZ_comm : ∀ idx, Commute (sys.checkProj idx) Z_log)
    (hX_comm : ∀ idx, Commute (sys.checkProj idx) X_log)
    (h_anti_bare : X_log * Z_log = -(Z_log * X_log))
    (h_sd_Pi : IsStarProjection (syndromeSubsetProj sys S_safe) ∧
      syndromeSubsetProj sys S_safe ≠ 0 ∧ syndromeSubsetProj sys S_safe ≠ 1 ∧
      Commute sys.H0 (syndromeSubsetProj sys S_safe) ∧
      sys.P0 * syndromeSubsetProj sys S_safe = sys.P0)
    (h_sd_OZ : IsSelfAdjoint (Z_log * syndromeSignOp sys sgn_Z) ∧
      (Z_log * syndromeSignOp sys sgn_Z) * (Z_log * syndromeSignOp sys sgn_Z) = 1 ∧
      ‖Z_log * syndromeSignOp sys sgn_Z‖ ≤ 1 ∧
      Commute sys.H0 (Z_log * syndromeSignOp sys sgn_Z) ∧
      (Z_log * syndromeSignOp sys sgn_Z) * sys.P0 = Z_log * sys.P0 ∧
      syndromeSubsetProj sys S_safe *
        (sys.P0 - (Z_log * syndromeSignOp sys sgn_Z) * sys.P0 *
          (Z_log * syndromeSignOp sys sgn_Z)†) * syndromeSubsetProj sys S_safe = 0)
    (h_sd_OX : IsSelfAdjoint (X_log * syndromeSignOp sys sgn_X) ∧
      (X_log * syndromeSignOp sys sgn_X) * (X_log * syndromeSignOp sys sgn_X) = 1 ∧
      ‖X_log * syndromeSignOp sys sgn_X‖ ≤ 1 ∧
      Commute sys.H0 (X_log * syndromeSignOp sys sgn_X) ∧
      (X_log * syndromeSignOp sys sgn_X) * sys.P0 = X_log * sys.P0 ∧
      syndromeSubsetProj sys S_safe *
        (sys.P0 - (X_log * syndromeSignOp sys sgn_X) * sys.P0 *
          (X_log * syndromeSignOp sys sgn_X)†) * syndromeSubsetProj sys S_safe = 0)
    (h_fw_1site : ∀ (v : Box3D L) (A_v : ℬ[L, CodeSlotConfig qCodeBDL]),
      IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v →
      syndromeSubsetProj sys S_safe *
        (A_v * (Z_log * syndromeSignOp sys sgn_Z) -
          (Z_log * syndromeSignOp sys sgn_Z) * A_v) * syndromeSubsetProj sys S_safe = 0 ∧
      syndromeSubsetProj sys S_safe *
        (A_v * (X_log * syndromeSignOp sys sgn_X) -
          (X_log * syndromeSignOp sys sgn_X) * A_v) * syndromeSubsetProj sys S_safe = 0)
    (h_fw_cube : ∀ r ∈ Finset.Icc 1 (min R_imm L), ∀ A ∈ boxCubes 3 L r,
      ∀ M_A : ℬ[L, CodeSlotConfig qCodeBDL],
        IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) A M_A →
        syndromeSubsetProj sys S_safe *
          (M_A * (Z_log * syndromeSignOp sys sgn_Z) -
            (Z_log * syndromeSignOp sys sgn_Z) * M_A) * syndromeSubsetProj sys S_safe = 0 ∧
        syndromeSubsetProj sys S_safe *
          (M_A * (X_log * syndromeSignOp sys sgn_X) -
            (X_log * syndromeSignOp sys sgn_X) * M_A) * syndromeSubsetProj sys S_safe = 0)
    (h_fw_macro : ∀ (W : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes 3 L r,
        syndromeSubsetProj sys S_safe *
          (W.term r A * (Z_log * syndromeSignOp sys sgn_Z) -
            (Z_log * syndromeSignOp sys sgn_Z) * W.term r A) * syndromeSubsetProj sys S_safe = 0 ∧
        syndromeSubsetProj sys S_safe *
          (W.term r A * (X_log * syndromeSignOp sys sgn_X) -
            (X_log * syndromeSignOp sys sgn_X) * W.term r A) * syndromeSubsetProj sys S_safe = 0)
    (h_peierls : ∀ β : ℝ, β > betaCritBDL →
      gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - syndromeSubsetProj sys S_safe) ≤
        Real.exp (-(cFBDL * (β - betaCritBDL) * (((L ^ 3 : ℕ) : ℝ) ^ etaBDL)))) :
    ∃ (mem : Inhomogeneous3DMemoryRealization L qCodeBDL r0BDL mMaxBDL
        cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL),
      mem.sys = sys ∧
      mem.Pi_safe = syndromeSubsetProj mem.sys S_safe ∧
      mem.D_field = D_field ∧
      (∀ (W : QuasiLocalPerturbation 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 r_fw, ∀ A ∈ boxCubes 3 L r,
          mem.Pi_safe * (W.term r A * mem.O_dec_Z - mem.O_dec_Z * W.term r A) * mem.Pi_safe = 0 ∧
          mem.Pi_safe * (W.term r A * mem.O_dec_X - mem.O_dec_X * W.term r A) * mem.Pi_safe = 0) ∧
      HasSafeDecodedLogicalObservables (N_checks := N_c)
        (mem.sys.reindex e_chk) mem.Pi_safe mem.O_dec_Z mem.O_dec_X R_imm := by
  have h_unpert :
      ∀ β : ℝ, β > betaCritBDL →
        let ΔF := cFBDL * (β - betaCritBDL) * (((L ^ 3 : ℕ) : ℝ) ^ etaBDL)
        gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - syndromeSubsetProj sys S_safe) ≤ Real.exp (-ΔF) ∧
        ∀ (bath : Finset (BathChannel 3 L (UniformSite3D L (CodeSlotConfig qCodeBDL))))
          (O_dec : ℬ[L, CodeSlotConfig qCodeBDL]),
          (O_dec = Z_log * syndromeSignOp sys sgn_Z ∨ O_dec = X_log * syndromeSignOp sys sgn_X) →
          (∀ ch ∈ bath, 0 ≤ ch.γ ∧
            ∃ v : Box3D L, IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} ch.L) →
          ∀ (O_t : ℝ → ℬ[L, CodeSlotConfig qCodeBDL]) (t : ℝ), 0 ≤ t →
            SatisfiesKMSLindbladODE sys.H0 sys.isSelfAdjoint_H0 β bath O_dec O_t t →
            opKMSNormSq sys.H0 sys.isSelfAdjoint_H0 β (O_t t - O_dec) ≤
              8 * (∑ ch ∈ bath, ch.γ * ‖ch.L‖ ^ 2) * (Real.exp (-ΔF)) ^ (1 / 2 : ℝ) * t := by
    intro β hβ
    refine ⟨h_peierls β hβ, fun bath O_dec hO_cases h_bath_loc O_t t ht h_ode => ?_⟩
    rcases hO_cases with rfl | rfl
    · exact opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed
        sys.isSelfAdjoint_H0 β bath (Z_log * syndromeSignOp sys sgn_Z) (syndromeSubsetProj sys S_safe)
        h_sd_OZ.1 h_sd_OZ.2.1 h_sd_OZ.2.2.2.1 h_sd_Pi.1
        (fun ch hch => ⟨(h_bath_loc ch hch).1,
          (h_fw_1site (h_bath_loc ch hch).2.choose ch.L (h_bath_loc ch hch).2.choose_spec).1⟩)
        (h_peierls β hβ) O_t t ht h_ode
    · exact opKMSNormSq_le_of_satisfiesKMSLindbladODE_unperturbed
        sys.isSelfAdjoint_H0 β bath (X_log * syndromeSignOp sys sgn_X) (syndromeSubsetProj sys S_safe)
        h_sd_OX.1 h_sd_OX.2.1 h_sd_OX.2.2.2.1 h_sd_Pi.1
        (fun ch hch => ⟨(h_bath_loc ch hch).1,
          (h_fw_1site (h_bath_loc ch hch).2.choose ch.L (h_bath_loc ch hch).2.choose_spec).2⟩)
        (h_peierls β hβ) O_t t ht h_ode
  have hP0_sa : IsSelfAdjoint sys.P0 := sys.isStarProjection_P0.isSelfAdjoint
  have hOZ_P0 : Commute sys.P0 (Z_log * syndromeSignOp sys sgn_Z) :=
    commute_P0_of_mul_P0_eq (P0 := sys.P0) (O := Z_log * syndromeSignOp sys sgn_Z) (L_op := Z_log)
      hP0_sa h_sd_OZ.1 h_bare_Z.1 h_bare_Z.2.2.2 h_sd_OZ.2.2.2.2.1
  have hOX_P0 : Commute sys.P0 (X_log * syndromeSignOp sys sgn_X) :=
    commute_P0_of_mul_P0_eq (P0 := sys.P0) (O := X_log * syndromeSignOp sys sgn_X) (L_op := X_log)
      hP0_sa h_sd_OX.1 h_bare_X.1 h_bare_X.2.2.2 h_sd_OX.2.2.2.2.1
  have hPi_OZ : Commute (syndromeSubsetProj sys S_safe) (Z_log * syndromeSignOp sys sgn_Z) :=
    (commute_syndromeSubsetProj_of_commute_checkProj sys hZ_comm S_safe).mul_right
      (commute_syndromeSubsetProj_syndromeSignOp sys S_safe sgn_Z)
  have hPi_OX : Commute (syndromeSubsetProj sys S_safe) (X_log * syndromeSignOp sys sgn_X) :=
    (commute_syndromeSubsetProj_of_commute_checkProj sys hX_comm S_safe).mul_right
      (commute_syndromeSubsetProj_syndromeSignOp sys S_safe sgn_X)
  have h_alg := decoded_anticommute_and_ne_zero sys.P0 (syndromeSubsetProj sys S_safe)
    Z_log X_log (syndromeSignOp sys sgn_Z) (syndromeSignOp sys sgn_X)
    (commute_of_commute_checkProj_syndromeSignOp sys hZ_comm sgn_X)
    (commute_of_commute_checkProj_syndromeSignOp sys hX_comm sgn_Z)
    (commute_syndromeSignOp_syndromeSignOp sys sgn_Z sgn_X)
    h_anti_bare h_sd_OZ.2.2.2.2.1 h_bare_rest.2.1 h_sd_OX.2.2.2.2.1 h_bare_rest.2.2
  have h_chk_comm : ∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
      Commute (sys.checkProj idx) (syndromeSubsetProj sys S_safe) ∧
      Commute (sys.checkProj idx) (Z_log * syndromeSignOp sys sgn_Z) ∧
      Commute (sys.checkProj idx) (X_log * syndromeSignOp sys sgn_X) :=
    fun idx => ⟨(syndromeSubsetProj_props sys S_safe).2.2.1 idx,
      (hZ_comm idx).mul_right ((syndromeSignOp_props sys sgn_Z).2.2.1 idx),
      (hX_comm idx).mul_right ((syndromeSignOp_props sys sgn_X).2.2.1 idx)⟩
  have h_obs : HasSafeDecodedLogicalObservables (N_checks := N_c)
      (sys.reindex e_chk) (syndromeSubsetProj sys S_safe)
      (Z_log * syndromeSignOp sys sgn_Z) (X_log * syndromeSignOp sys sgn_X) R_imm :=
    hasSafeDecodedLogicalObservables_of_commute_reindex
      (L := L) (N_c := N_c) (R_imm := R_imm) (Site0 := CodeSlotConfig qCodeBDL)
      (Idx := StaticCSSCheckIdx L qCodeBDL mMaxBDL)
      e_chk sys Z_log X_log (syndromeSubsetProj sys S_safe)
      (Z_log * syndromeSignOp sys sgn_Z) (X_log * syndromeSignOp sys sgn_X)
      h_bare_Z.2.1 h_bare_Z.2.2.1 h_bare_Z.2.2.2
      h_bare_X.2.1 h_bare_X.2.2.1 h_bare_rest.1 h_p0_ne.1 h_p0_ne.2
      h_sd_Pi.1 h_sd_Pi.2.1 h_sd_Pi.2.2.1 h_sd_Pi.2.2.2.1 h_sd_Pi.2.2.2.2
      h_sd_OZ.1 h_sd_OZ.2.1 h_sd_OZ.2.2.1 h_sd_OZ.2.2.2.1 hOZ_P0 hPi_OZ
      h_sd_OX.1 h_sd_OX.2.1 h_sd_OX.2.2.1 h_sd_OX.2.2.2.1 hOX_P0 hPi_OX
      h_chk_comm h_alg.1 h_alg.2.1 h_alg.2.2 h_fw_1site h_fw_cube
  exact ⟨{
    D_field := D_field, h_D_field_valid := h_D_valid, sys := sys,
    h_sys_checks := h_sys_checks, h_tqo := h_tqo, Z_log := Z_log, X_log := X_log,
    h_logical_pair := ⟨h_p0_ne, h_bare_Z, h_bare_X, h_bare_rest.1, h_bare_rest.2⟩,
    Pi_safe := syndromeSubsetProj sys S_safe,
    O_dec_Z := Z_log * syndromeSignOp sys sgn_Z,
    O_dec_X := X_log * syndromeSignOp sys sgn_X,
    h_decoder_props := ⟨h_sd_Pi, h_sd_OZ, h_sd_OX, h_fw_1site⟩,
    h_unperturbed_thermal_and_kms_lifetime := h_unpert
  }, rfl, rfl, rfl, h_fw_macro, h_obs⟩

private lemma bdl_weylPauli_anticommute (k : ℕ) :
    weylPauliX (bdlPushChain k (bdlWeldedLX k)) * weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) =
      -(weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) * weylPauliX (bdlPushChain k (bdlWeldedLX k))) := by
  have h_ph : pauliPhase (bdlPushChain k (bdlWeldedLZ k)) (bdlPushChain k (bdlWeldedLX k)) = -1 := by
    unfold pauliPhase
    rw [sum_bdlPushChain_mul_bdlPushChain_eq_dualPairing k (bdlWeldedLZ k) (bdlWeldedLX k),
      dualPairing_bdlWeldedLZ_bdlWeldedLX k]
    exact if_neg (by decide : (1 : ZMod 2) ≠ 0)
  exact (weylPauliX_mul_weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) (bdlWeldedLX k |> bdlPushChain k)).trans
    ((congrArg (fun c : ℂ => c • (weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) *
      weylPauliX (bdlPushChain k (bdlWeldedLX k)))) h_ph).trans (clm_neg_one_smul _))

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  bdlBoxSide HasZeroTempDressingBundle HasSafeDecodedLogicalObservables
  SatisfiesUnperturbedThermalAndKMSStability
  SatisfiesZeroTempPerturbativeMemoryStability IndexedCommutingProjectorHamiltonian.IsGeometricallyLocal
  IndexedCommutingProjectorHamiltonian.reindex bdlInhomogeneousSystem
  reindexHamiltonian reindexPerturbation conjSiteOp clusterRawWeight bdlClusterStepBase

/-- Explicit level-`k` BDL realization package on `CodeSlotConfig q_code_BDL` bundling
    `Inhomogeneous3DMemoryRealization`, macroscopic `bdlLambda ^ k` safe-subspace immunity,
    `HasSafeDecodedLogicalObservables`, and `syndromeSubsetProj` representation of `Pi_safe`. -/
lemma bdl_inhomogeneous_codeSlot_memory_package (k : ℕ) {N_c : ℕ}
    (e_chk : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin N_c) :
    ∃ (mem : Inhomogeneous3DMemoryRealization (bdlBoxSide k) qCodeBDL r0BDL mMaxBDL
        cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
      (S_safe : Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool)),
      mem.sys = bdlInhomogeneousSystem k ∧
      mem.Pi_safe = syndromeSubsetProj mem.sys S_safe ∧
      mem.D_field = bdlLocalDescriptor k ∧
      (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k)
          (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
          mem.Pi_safe * (W.term r A * mem.O_dec_Z - mem.O_dec_Z * W.term r A) * mem.Pi_safe = 0 ∧
          mem.Pi_safe * (W.term r A * mem.O_dec_X - mem.O_dec_X * W.term r A) * mem.Pi_safe = 0) ∧
      HasSafeDecodedLogicalObservables (N_checks := N_c)
        (mem.sys.reindex e_chk) mem.Pi_safe mem.O_dec_Z mem.O_dec_X (37 * bdlLambda ^ k) := by
  obtain ⟨⟨ψ_Z, W_Z, hψZ0, hWZ_card, hWZ_wt, hWZ_fail⟩,
          ⟨ψ_X, W_X, hψX0, hWX_card, hWX_wt, hWX_fail⟩⟩ :=
    hasBallParityWitnessFamily_bdlWelded_lambdaPow k
  have h37_pos : 0 < 37 * bdlLambda ^ k := Nat.mul_pos (by decide) (Nat.pow_pos bdlLambda_pos)
  have hWZ_fail_two : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q → (bdlWeldedCode k).posQ q ∈ ball3D x0 2) →
      ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' ≠
        ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err →
      ∃ c ∈ W_Z, (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e' m ≠ 0) :=
    fun e_err e' x0 h_diff => hWZ_fail e_err e' x0
      (fun q hq => ball3D_two_subset_ball3D_two_mul
        (by exact_mod_cast Nat.succ_le_of_lt h37_pos) x0 (h_diff q hq))
  have h_bare := bdl_bare_logical_props k (bdlWeldedLZ k) (bdlWeldedLX k)
    (syndrome_bdlWeldedLZ k) (syndrome_bdlWeldedLX k) (dualPairing_bdlWeldedLZ_bdlWeldedLX k)
  have hw_ge1 : (1 : ℝ) ≤ ((clusterRawWeight k : ℕ) : ℝ) :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans (three_div_two_pow_le_clusterRawWeight k)
  have h0_mem : (fun _ => false) ∈ bdlSafeSyndromeSet k W_Z W_X :=
    false_mem_bdlSafeSyndromeSet k W_Z W_X
      (fun c hc => hw_ge1.trans (hWZ_wt c hc)) (fun c hc => hw_ge1.trans (hWX_wt c hc))
  have h_sd := safeAndDecoded_props_of_commute (bdlInhomogeneousSystem k)
    (weylPauliZ (bdlPushChain k (bdlWeldedLZ k))) (weylPauliX (bdlPushChain k (bdlWeldedLX k)))
    (bdlInhomogeneousSystem_P0_ne_zero_and_ne_one k).1 h_bare.1.1 h_bare.1.2.1
    (weylPauliZ_bdlPushChain_commute_checkProj k (bdlWeldedLZ k) (syndrome_bdlWeldedLZ k))
    h_bare.2.1.1 h_bare.2.1.2.1
    (weylPauliX_bdlPushChain_commute_checkProj k (bdlWeldedLX k) (syndrome_bdlWeldedLX k))
    (bdlSafeSyndromeSet k W_Z W_X) h0_mem
    (syndromeSubsetProj_bdlSafeSyndromeSet_ne_one k ψ_Z W_Z W_X hψZ0 hWZ_fail_two)
    (fun σ => ψ_X (bdlPullSynZ k σ)) (fun σ => ψ_Z (bdlPullSynX k σ))
    (show ψ_X (bdlPullSynZ k (fun _ => false)) = 0 by rw [bdlPullSynZ_false]; exact hψX0)
    (show ψ_Z (bdlPullSynX k (fun _ => false)) = 0 by rw [bdlPullSynX_false]; exact hψZ0)
  obtain ⟨mem, h_mem⟩ := codeSlot_memory_package_of_components
    (L := bdlBoxSide k) (N_c := N_c) (r_fw := bdlLambda ^ k) (R_imm := 37 * bdlLambda ^ k)
    (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k)
    (bdlInhomogeneousSystem k) (bdlInhomogeneousSystem_checks k)
    (bdlInhomogeneousSystem_satisfiesOperatorTQO k) e_chk
    (weylPauliZ (bdlPushChain k (bdlWeldedLZ k))) (weylPauliX (bdlPushChain k (bdlWeldedLX k)))
    (bdlSafeSyndromeSet k W_Z W_X)
    (fun σ => ψ_X (bdlPullSynZ k σ)) (fun σ => ψ_Z (bdlPullSynX k σ))
    (bdlInhomogeneousSystem_P0_ne_zero_and_ne_one k) h_bare.1 h_bare.2.1 h_bare.2.2
    (weylPauliZ_bdlPushChain_commute_checkProj k (bdlWeldedLZ k) (syndrome_bdlWeldedLZ k))
    (weylPauliX_bdlPushChain_commute_checkProj k (bdlWeldedLX k) (syndrome_bdlWeldedLX k))
    (bdl_weylPauli_anticommute k) h_sd.1 h_sd.2.1 h_sd.2.2
    (fun v A_v hA_v => bdlSafeSyndromeSet_subset_boxCube_safe_immunity k ψ_Z W_Z ψ_X W_X
      hWZ_fail hWX_fail v {v} (singleton_subset_boxCube_of_pos h37_pos v) A_v hA_v)
    (fun r hr A hA M_A hM_A => bdlSafeSyndromeSet_cube_op_safe_immunity_lambdaPow k ψ_Z W_Z ψ_X W_X
      hWZ_fail hWX_fail r hr A hA M_A hM_A)
    (fun W r hr A hA => bdlSafeSyndromeSet_cube_safe_immunity_lambdaPow k ψ_Z W_Z ψ_X W_X
      hWZ_fail hWX_fail W r
      (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
        (Finset.mem_Icc.mp hr).2.trans (bdlLambda_pow_le_37_mul_pow k)⟩) A hA)
    (fun β hβ => gibbsFailureProb_bdlSafeSyndromeSet_le k W_Z W_X hWZ_card hWZ_wt hWX_card hWX_wt β hβ)
  exact ⟨mem, bdlSafeSyndromeSet k W_Z W_X, h_mem⟩

/-- Abstract-equivalence version of `bdl_inhomogeneous_zero_temp_stability_codeSlot`
    parameterized by arbitrary check equivalences `e_chk k`. -/
lemma bdl_inhomogeneous_zero_temp_stability_codeSlot_of_equiv {N_c : ℕ → ℕ}
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
    (f : ℕ → ℝ) (R_bath : ℕ) (hf : IsSuperpolynomialDecay f) (hR_bath : 1 ≤ R_bath) :
    ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
      0 < J_0 ∧ IsSuperpolynomialDecay δ_split ∧ IsSuperpolynomialDecay g_LR ∧
      ∀ (k : ℕ), k_0 ≤ k → ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
        ∀ (V : QuasiLocalPerturbation 3 (bdlBoxSide k)
            (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
          V.SatisfiesDecayBound J f →
          SatisfiesZeroTempPerturbativeMemoryStability
            (N_checks := N_c k) ((mem k).sys.reindex (e_chk k))
            (mem k).Pi_safe (mem k).O_dec_Z (mem k).O_dec_X
            V R_bath (δ_split (bdlBoxSide k)) g_LR := by
  rcases bdl_inhomogeneous_zero_temp_dressing_bundle_exists mem h_mem_spec f hf with
    ⟨J_0, k_0_qac, δ_0, g_LR, hJ0_pos, hδ0_super, hg_LR, h_bundle_k⟩
  let C_const : ℝ := 18 * ((R_bath ^ 3 : ℕ) : ℝ) *
    ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ)
  have hC_nn : 0 ≤ C_const := by positivity
  have h_resc := isSuperpolynomialDecay_cube_rescaled_profile one_le_bdlLambda hC_nn hδ0_super hg_LR
  let δ_split : ℕ → ℝ := fun n =>
    max (9 * δ_0 n) (C_const * g_LR (Nat.sqrt n / (bdlLambda ^ 2)))
  rcases exists_k_pad_le_37_mul_bdlLambda_pow R_bath with ⟨k_pad, hk_pad⟩
  refine ⟨J_0, max k_0_qac k_pad, δ_split, g_LR, hJ0_pos, h_resc.1, hg_LR,
    fun k hk J hJ_nn hJ_le V hV_dec => ?_⟩
  have hk_qac : k_0_qac ≤ k := le_trans (le_max_left _ _) hk
  have hk_p : k_pad ≤ k := le_trans (le_max_right _ _) hk
  have hδ0_nn : 0 ≤ δ_0 (bdlBoxSide k) := hδ0_super.1 (bdlBoxSide k)
  have hδ0_le : δ_0 (bdlBoxSide k) ≤ δ_split (bdlBoxSide k) :=
    le_trans (by linarith) (le_max_left _ _)
  have h_sqrt_k : Nat.sqrt (bdlBoxSide k) / (bdlLambda ^ 2) = bdlLambda ^ k := by
    rw [bdlBoxSide_eq_bdlLambda_pow k]; exact h_resc.2 k
  have hg_nn : 0 ≤ g_LR (bdlLambda ^ k) := hg_LR.1 (bdlLambda ^ k)
  have h_ch_le :
      2 * ((R_bath ^ 3 : ℕ) : ℝ) *
        (((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) *
          g_LR (bdlLambda ^ k)) ≤
      δ_split (bdlBoxSide k) := by
    have h1 :
        2 * ((R_bath ^ 3 : ℕ) : ℝ) *
          (((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) *
            g_LR (bdlLambda ^ k)) ≤
        C_const * g_LR (bdlLambda ^ k) := by
      dsimp only [C_const]
      have h_two_le :
          (2 : ℝ) * ((R_bath ^ 3 : ℕ) : ℝ) *
            ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) ≤
          18 * ((R_bath ^ 3 : ℕ) : ℝ) *
            ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) := by
        nlinarith
      calc 2 * ((R_bath ^ 3 : ℕ) : ℝ) *
            (((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ) *
              g_LR (bdlLambda ^ k))
        _ = (2 * ((R_bath ^ 3 : ℕ) : ℝ) *
              ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ)) *
              g_LR (bdlLambda ^ k) := by ring
        _ ≤ (18 * ((R_bath ^ 3 : ℕ) : ℝ) *
              ((Fintype.card (CodeSlotConfig qCodeBDL) ^ (2 * R_bath ^ 3) : ℕ) : ℝ)) *
              g_LR (bdlLambda ^ k) := mul_le_mul_of_nonneg_right h_two_le hg_nn
    have h2 : C_const * g_LR (bdlLambda ^ k) ≤ δ_split (bdlBoxSide k) := by
      dsimp only [δ_split]
      rw [h_sqrt_k]
      exact le_max_right _ _
    exact le_trans h1 h2
  refine satisfiesZeroTempPerturbativeMemoryStability_of_dressing_bundle
    (L := bdlBoxSide k) (N_c := N_c k) (R_bath := R_bath)
    (e_chk k) (mem k) V (δ_0 (bdlBoxSide k)) (δ_split (bdlBoxSide k)) g_LR
    hδ0_le (h_bundle_k k hk_qac J hJ_nn hJ_le V hV_dec)
    (fun U_dress hU r hr W hW M_W hM_W => ?_)
  have h_comm := dressed_cube_commutator_le_of_hasSafeDecodedLogicalObservables
    ((mem k).sys.reindex (e_chk k)) (mem k).Pi_safe (mem k).O_dec_Z (mem k).O_dec_X
    (h_obs_spec k) hg_nn (hk_pad k hk_p) U_dress hU r hr W hW M_W hM_W
  exact ⟨le_trans h_comm.1 (mul_le_mul_of_nonneg_right h_ch_le (norm_nonneg _)),
    le_trans h_comm.2 (mul_le_mul_of_nonneg_right h_ch_le (norm_nonneg _))⟩

lemma exists_equiv_codeSlotConfig {q : ℕ} (hq : 1 ≤ q) :
    ∃ (d_loc : ℕ), 2 ≤ d_loc ∧ Nonempty (CodeSlotConfig q ≃ Fin d_loc) := by
  refine ⟨Fintype.card (CodeSlotConfig q), ?_, ⟨Fintype.equivFin (CodeSlotConfig q)⟩⟩
  have hd_eq : Fintype.card (CodeSlotConfig q) = 2 ^ q := by
    dsimp [CodeSlotConfig]; rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hd_eq]
  exact le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) hq)

lemma exists_equiv_staticCSSCheckIdx (L : ℕ → ℕ) (q m : ℕ) :
    ∃ (N_checks : ℕ → ℕ),
      Nonempty (∀ k : ℕ, StaticCSSCheckIdx (L k) q m ≃ Fin (N_checks k)) :=
  ⟨fun k => Fintype.card (StaticCSSCheckIdx (L k) q m),
   ⟨fun k => Fintype.equivFin (StaticCSSCheckIdx (L k) q m)⟩⟩

def dLocBDL : ℕ := (exists_equiv_codeSlotConfig q_code_BDL_ge_one).choose
lemma two_le_d_loc_bdl : 2 ≤ dLocBDL :=
  (exists_equiv_codeSlotConfig q_code_BDL_ge_one).choose_spec.1
def equivCodeSlotBDL : CodeSlotConfig qCodeBDL ≃ Fin dLocBDL :=
  Classical.choice (exists_equiv_codeSlotConfig q_code_BDL_ge_one).choose_spec.2
instance instNeZeroDLocBDL : NeZero dLocBDL := ⟨by have := two_le_d_loc_bdl; omega⟩
instance instNonemptyCodeSlotBDL : Nonempty (CodeSlotConfig qCodeBDL) := ⟨fun _ => false⟩
instance instNonemptyFinDLocBDL : Nonempty (Fin dLocBDL) := ⟨⟨0, by have := two_le_d_loc_bdl; omega⟩⟩

def nChecksBDL : ℕ → ℕ :=
  (exists_equiv_staticCSSCheckIdx bdlBoxSide qCodeBDL mMaxBDL).choose
def equivStaticCSSCheckBDL :
    ∀ k : ℕ, StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin (nChecksBDL k) :=
  Classical.choice (exists_equiv_staticCSSCheckIdx bdlBoxSide qCodeBDL mMaxBDL).choose_spec

def memBDL (k : ℕ) :
    Inhomogeneous3DMemoryRealization (bdlBoxSide k) qCodeBDL r0BDL mMaxBDL
      cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL :=
  (bdl_inhomogeneous_codeSlot_memory_package k (equivStaticCSSCheckBDL k)).choose
def safeSyndromeBDL (k : ℕ) :
    Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :=
  (bdl_inhomogeneous_codeSlot_memory_package k (equivStaticCSSCheckBDL k)).choose_spec.choose
lemma memBDL_spec (k : ℕ) :
    (memBDL k).sys = bdlInhomogeneousSystem k ∧
    (memBDL k).Pi_safe = syndromeSubsetProj (memBDL k).sys (safeSyndromeBDL k) ∧
    (memBDL k).D_field = bdlLocalDescriptor k ∧
    (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k)
        (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
      ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
        (memBDL k).Pi_safe * (W.term r A * (memBDL k).O_dec_Z - (memBDL k).O_dec_Z * W.term r A) *
          (memBDL k).Pi_safe = 0 ∧
        (memBDL k).Pi_safe * (W.term r A * (memBDL k).O_dec_X - (memBDL k).O_dec_X * W.term r A) *
          (memBDL k).Pi_safe = 0) ∧
    HasSafeDecodedLogicalObservables (N_checks := nChecksBDL k)
      ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))
      (memBDL k).Pi_safe (memBDL k).O_dec_Z (memBDL k).O_dec_X (37 * bdlLambda ^ k) :=
  (bdl_inhomogeneous_codeSlot_memory_package k (equivStaticCSSCheckBDL k)).choose_spec.choose_spec

attribute [local irreducible]
  dLocBDL equivCodeSlotBDL nChecksBDL equivStaticCSSCheckBDL memBDL safeSyndromeBDL

/-- **Master Part I, Theorem 7.5 (`thm:main`) Synthesis (`part1_thermally_and_perturbatively_stable_memory_main`)**:
    Combines the unperturbed 3D BDL thermal stability realization
    with `bdl_inhomogeneous_zero_temp_stability_codeSlot_of_equiv` and site/check index transport to `Fin d_loc`
    and `Fin (N_checks k)`. -/
theorem part1_thermally_and_perturbatively_stable_memory_main :
    ∃ (d_loc r_0 w_0 Λ_scale : ℕ) (β_c c_F η : ℝ) (L N_checks : ℕ → ℕ)
      (_ : ∀ k : ℕ, NeZero (L k)) (_ : NeZero d_loc)
      (sys : ∀ k : ℕ, IndexedCommutingProjectorHamiltonian 3 (L k)
        (UniformSite3D (L k) (Fin d_loc)) (Fin (N_checks k)))
      (Pi_safe O_dec_Z O_dec_X : ∀ k : ℕ, ℬ[L k, Fin d_loc]),
      2 ≤ d_loc ∧ 1 ≤ r_0 ∧ 1 ≤ w_0 ∧ 2 ≤ Λ_scale ∧
      0 < β_c ∧ 0 < c_F ∧ 0 < η ∧
      (∀ k : ℕ, L k = Λ_scale ^ (2 * k + 4)) ∧
      IsStrictlyIncreasingBoxSequence L ∧
      (∀ k : ℕ,
        (sys k).IsGeometricallyLocal r_0 w_0 ∧
        (∀ i : Fin (N_checks k), (sys k).weight i = 1) ∧
        HasSafeDecodedLogicalObservables (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k)
          (37 * Λ_scale ^ k) ∧
        SatisfiesUnperturbedThermalAndKMSStability (sys k)
          (Pi_safe k) (O_dec_Z k) (O_dec_X k) (37 * Λ_scale ^ k) w_0 β_c c_F η) ∧
      (∀ (f : ℕ → ℝ) (R_bath : ℕ), IsSuperpolynomialDecay f → 1 ≤ R_bath →
        ∃ (J_0 : ℝ) (k_0 : ℕ) (δ_split g_LR : ℕ → ℝ),
          0 < J_0 ∧ IsSuperpolynomialDecay δ_split ∧ IsSuperpolynomialDecay g_LR ∧
          ∀ (k : ℕ), k_0 ≤ k → ∀ (J : ℝ), 0 ≤ J → J ≤ J_0 →
            ∀ (V : QuasiLocalPerturbation 3 (L k) (UniformSite3D (L k) (Fin d_loc))),
              V.SatisfiesDecayBound J f →
              SatisfiesZeroTempPerturbativeMemoryStability
                (sys k) (Pi_safe k) (O_dec_Z k) (O_dec_X k) V R_bath (δ_split (L k)) g_LR) := by
  refine ⟨dLocBDL, r0BDL, (2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL), bdlLambda,
    betaCritBDL, cFBDL, etaBDL, bdlBoxSide, nChecksBDL,
    inferInstance, inferInstance,
    fun k => reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)),
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).Pi_safe,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_Z,
    fun k => conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_X,
    two_le_d_loc_bdl, r_0_BDL_ge_one, w_0_BDL_ge_one, two_le_bdlLambda,
    beta_crit_bdl_pos, c_f_bdl_pos, eta_bdl_pos,
    bdlBoxSide_eq_bdlLambda_pow,
    fun k => (bdlBoxSide_scaling_and_strictMono k).2, ?_, ?_⟩
  · intro k
    rcases memBDL_spec k with ⟨h_sys_eq, h_Pi_eq, _hD, _h_fw_macro, h_obs₀⟩
    have h_geom : (reindexHamiltonian (fun _ => equivCodeSlotBDL)
        ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))).IsGeometricallyLocal
        r0BDL ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL)) := by
      refine reindexHamiltonian_isGeometricallyLocal equivCodeSlotBDL
        ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)) ?_
      rw [h_sys_eq]; exact isGeometricallyLocal_bdlInhomogeneousSystem_reindex k (equivStaticCSSCheckBDL k)
    have h_unit : ∀ i : Fin (nChecksBDL k),
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))).weight i = 1 := by
      intro i
      rw [reindexHamiltonian_reindex_weight equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memBDL k).sys i,
        ((memBDL k).h_sys_checks ((equivStaticCSSCheckBDL k).symm i)).2.2]
    have h_obs_k : HasSafeDecodedLogicalObservables
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_X)
        (37 * bdlLambda ^ k) :=
      hasSafeDecodedLogicalObservables_reindexHamiltonian equivCodeSlotBDL
        ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))
        (memBDL k).Pi_safe (memBDL k).O_dec_Z (memBDL k).O_dec_X h_obs₀
    have h_therm_k : SatisfiesUnperturbedThermalAndKMSStability
        (reindexHamiltonian (fun _ => equivCodeSlotBDL) ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)))
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).Pi_safe)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_Z)
        (conjSiteOp (fun _ => equivCodeSlotBDL) (memBDL k).O_dec_X)
        (37 * bdlLambda ^ k) ((2 * r0BDL + 1) ^ 3 * (qCodeBDL + 2 * mMaxBDL))
        betaCritBDL cFBDL etaBDL :=
      satisfiesUnperturbedThermalAndKMSStability_reindexHamiltonian
        equivCodeSlotBDL (equivStaticCSSCheckBDL k) (memBDL k).sys (safeSyndromeBDL k)
        (memBDL k).Pi_safe (memBDL k).O_dec_Z (memBDL k).O_dec_X
        h_Pi_eq h_geom h_unit (four_mul_r0BDL_add_one_le_37_mul_pow k)
        (fun β hβ => ((memBDL k).h_unperturbed_thermal_and_kms_lifetime β hβ).1) h_obs_k
    exact ⟨h_geom, h_unit, h_obs_k, h_therm_k⟩
  · intro f R_bath hf hR_bath
    have h_mem_spec : ∀ k : ℕ,
        (memBDL k).D_field = bdlLocalDescriptor k ∧
        (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k) (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
          ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
            (memBDL k).Pi_safe * (W.term r A * (memBDL k).O_dec_Z - (memBDL k).O_dec_Z * W.term r A) *
              (memBDL k).Pi_safe = 0 ∧
            (memBDL k).Pi_safe * (W.term r A * (memBDL k).O_dec_X - (memBDL k).O_dec_X * W.term r A) *
              (memBDL k).Pi_safe = 0) :=
      fun k => ⟨(memBDL_spec k).2.2.1, (memBDL_spec k).2.2.2.1⟩
    have h_obs_spec : ∀ k : ℕ,
        HasSafeDecodedLogicalObservables (N_checks := nChecksBDL k)
          ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))
          (memBDL k).Pi_safe (memBDL k).O_dec_Z (memBDL k).O_dec_X (37 * bdlLambda ^ k) :=
      fun k => (memBDL_spec k).2.2.2.2
    have h_ex := bdl_inhomogeneous_zero_temp_stability_codeSlot_of_equiv
      equivStaticCSSCheckBDL memBDL h_mem_spec h_obs_spec f R_bath hf hR_bath
    have h1 := h_ex.choose_spec
    have h2 := h1.choose_spec
    have h3 := h2.choose_spec
    have h4 := h3.choose_spec
    refine ⟨h_ex.choose, h1.choose, h2.choose, h3.choose, h4.1, h4.2.1, h4.2.2.1,
      fun k hk J hJ_nn hJ_le V₁ hV₁_dec => ?_⟩
    have hV₀_dec :
        (reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => equivCodeSlotBDL.symm) V₁).SatisfiesDecayBound J f :=
      satisfiesDecayBound_reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => equivCodeSlotBDL.symm) V₁ hV₁_dec
    have h_stab₀ := h4.2.2.2 k hk J hJ_nn hJ_le
      (reindexPerturbation (fun _ : Box3D (bdlBoxSide k) => equivCodeSlotBDL.symm) V₁) hV₀_dec
    have hP0_sa : IsSelfAdjoint (memBDL k).sys.P0 := (memBDL k).sys.isStarProjection_P0.isSelfAdjoint
    have hOZ := (memBDL k).h_decoder_props.2.1; have hOX := (memBDL k).h_decoder_props.2.2.1
    have hZ := (memBDL k).h_logical_pair.2.1; have hX := (memBDL k).h_logical_pair.2.2.1
    have hP0_OZ : Commute ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)).P0 (memBDL k).O_dec_Z := by
      rw [(memBDL k).sys.reindex_P0 (equivStaticCSSCheckBDL k)]
      exact commute_P0_of_mul_P0_eq hP0_sa hOZ.1 hZ.1 hZ.2.2.2 hOZ.2.2.2.2.1
    have hP0_OX : Commute ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k)).P0 (memBDL k).O_dec_X := by
      rw [(memBDL k).sys.reindex_P0 (equivStaticCSSCheckBDL k)]
      exact commute_P0_of_mul_P0_eq hP0_sa hOX.1 hX.1 hX.2.2.2 hOX.2.2.2.2.1
    exact satisfiesZeroTempPerturbativeMemoryStability_reindexHamiltonian
      equivCodeSlotBDL ((memBDL k).sys.reindex (equivStaticCSSCheckBDL k))
      (memBDL k).Pi_safe (memBDL k).O_dec_Z (memBDL k).O_dec_X
      hOZ.2.2.1 hP0_OZ hOX.2.2.1 hP0_OX V₁ h_stab₀
end Part1TwoAxisMemorySynthesis
end
