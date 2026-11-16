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

import Proofs.HierarchicalClusterDecoder.DecodedLogicalCommutation

/-!
# Multiscale Ball Parity Witness Synthesis for the Welded Code Hierarchy

Synthesizes Euclidean-ball parity witness families across primal and dual welded steps (`hasBallParityWitnessFamily_stepX`, `hasBallParityWitnessFamily_stepZ`) and across full renormalization cycles (`hasBallParityWitnessFamily_bdlIterated_succ`). Transports unique logical homology and macroscopic ball witness families to `bdlWeldedCode k` (`hasUniqueLogicalHomology_bdlWelded`, `hasBallParityWitnessFamily_bdlWelded_two`) and calibrates the critical inverse temperature against the per-step combinatorial base `bdlClusterStepBase`.

## References

* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`), Proposition 5.3 (`prop:cluster-decoder-witness`)
* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Lemma 5.4 (`lem:percolating-cluster-bounds`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Definition 4.2 (`def:multiscale-cluster-decoder`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Full Step-X and Step-Z Lifting of Ball Witness Families -/

/-- Joint primal & dual `HasBallParityWitnessFamily` step across `bdlRandomStepX B`,
    scaling the ball radius `r ↦ r / bdlLambda + 7003`. -/
theorem hasBallParityWitnessFamily_stepX (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (L_Z L_X : B.Q → ZMod 2)
    {r : ℝ} (hr0 : 0 ≤ r)
    (w_P w_D N_P N_D : ℕ)
    (h_primal : HasBallParityWitnessFamily B.code L_Z L_X (r / (bdlLambda : ℝ) + 7003) w_P N_P)
    (h_dual : HasBallParityWitnessFamily (dualCode B.code) L_X L_Z (r / (bdlLambda : ℝ) + 7003) w_D N_D) :
    HasBallParityWitnessFamily (bdlRandomStepX B).code
      (stepXLZ B L_Z) (stepXLX B L_X)
      r w_P (N_P * bdlSingleStepFactor ^ w_P) ∧
    HasBallParityWitnessFamily (dualCode (bdlRandomStepX B).code)
      (stepXLX B L_X) (stepXLZ B L_Z)
      r ((27 * w_D + 15) / 16) (N_D * (2 ^ (41 * bdlSingleStepFactor)) ^ w_D) := by
  have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
  have hlam_ne : (bdlLambda : ℝ) ≠ 0 := ne_of_gt hlam_pos
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  let c := bdlLLLPerturbation B
  let pcode := bdlPerturbedOfBundled B
  let D_edge : ℝ := 2001 * (bdlLambda : ℝ)
  have hD : HasCoarseEdgeBound pcode D_edge := by
    have hD_raw := hasCoarseEdgeBound_of_validLLLPerturbation B h_valid
    have h_eq : (2 * bdlAlpha + 1) * (bdlLambda : ℝ) = D_edge := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; ring
    rwa [h_eq] at hD_raw
  have hD0 : 0 ≤ D_edge := hD.1
  have hcQ : ∀ q, distSq3D (c.1 q) (fun _ => 0) ≤ (bdlAlpha * (bdlLambda : ℝ)) ^ 2 :=
    fun q => le_of_eq (h_valid.1 q)
  have h_alpha_nonneg : (0 : ℝ) ≤ bdlAlpha := by dsimp [bdlAlpha, bdlAlphaNat]; norm_num
  have hov_B := h_inv.1
  have hsimp_B : HasBoundedSimplexDegreeD B 32 :=
    hasBoundedSimplexDegreeD_32_of_hasBoundedCheckDegreeOverlap B hov_B
  have hF_B_X : ∀ x0 : B.M_X,
      (Finset.univ.filter (fun mX : BDLStepXMX pcode bdlSubdivPred =>
        stepXMXOwnerX pcode bdlSubdivPred mX = x0)).card ≤ bdlSingleStepFactor :=
    card_fiber_stepXMXOwnerX_le_bdlSingleStepFactor B hov_B.1 hsimp_B
  have h_pool_B : ∀ K_Z : Finset B.M_Z,
      (fineTwoHopPool pcode bdlSubdivPred K_Z).card ≤ 41 * bdlSingleStepFactor * K_Z.card :=
    card_fineTwoHopPool_le B hov_B.1 hsimp_B
  refine ⟨?_, ?_⟩
  · have h_rad_p : (r + D_edge) / (bdlLambda : ℝ) + bdlAlpha ≤ r / (bdlLambda : ℝ) + 7003 := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; field_simp [hlam_ne]; linarith
    have h_p_pert := hasBallParityWitnessFamily_bdlPerturbStep B.code bdlLambda bdlLambda_pos
      c.1 c.2.1 c.2.2 h_alpha_nonneg hcQ (by linarith) h_rad_p h_primal
    exact hasBallParityWitnessFamily_cylinder_primal pcode bdlSubdivPred hD
      L_Z L_X bdlSingleStepFactor w_P N_P hF_B_X hr0 h_p_pert
  · have h_rad_d : (r + 3 * D_edge) / (bdlLambda : ℝ) + bdlAlpha ≤ r / (bdlLambda : ℝ) + 7003 := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; field_simp [hlam_ne]; linarith
    have h_d_pert := hasBallParityWitnessFamily_dual_bdlPerturbStep B.code bdlLambda bdlLambda_pos
      c.1 c.2.1 c.2.2 h_alpha_nonneg hcQ (by linarith) h_rad_d h_dual
    exact hasBallParityWitnessFamily_cylinder_dual pcode bdlSubdivPred hD
      hov_B.2 h_inv.2.2.2.1.2 h_inv.2.2.2.2.1 L_Z L_X
      bdlSingleStepFactor w_D N_D h_pool_B hr0 h_d_pert

/-- Joint primal & dual `HasBallParityWitnessFamily` step across `bdlRandomStepZ B`,
    scaling the ball radius `r ↦ r / bdlLambda + 7003`. -/
theorem hasBallParityWitnessFamily_stepZ (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (L_Z L_X : B.Q → ZMod 2)
    {r : ℝ} (hr0 : 0 ≤ r)
    (w_P w_D N_P N_D : ℕ)
    (h_primal : HasBallParityWitnessFamily B.code L_Z L_X (r / (bdlLambda : ℝ) + 7003) w_P N_P)
    (h_dual : HasBallParityWitnessFamily (dualCode B.code) L_X L_Z (r / (bdlLambda : ℝ) + 7003) w_D N_D) :
    HasBallParityWitnessFamily (bdlRandomStepZ B).code
      (stepZLZ B L_Z) (stepZLX B L_X)
      r ((27 * w_P + 15) / 16) (N_P * (2 ^ (41 * bdlSingleStepFactor)) ^ w_P) ∧
    HasBallParityWitnessFamily (dualCode (bdlRandomStepZ B).code)
      (stepZLX B L_X) (stepZLZ B L_Z)
      r w_D (N_D * bdlSingleStepFactor ^ w_D) := by
  have h_inv_dB := hasBDLConeInvariants_dualBundled B h_inv
  have h_step := hasBallParityWitnessFamily_stepX (dualBundled B) h_inv_dB L_X L_Z
    hr0 w_D w_P N_D N_P h_dual (hasBallParityWitnessFamily_dual_dual h_primal)
  exact ⟨h_step.2, hasBallParityWitnessFamily_dual_dual h_step.1⟩

/-! ## 2. Base-Scale Ball Filling and Multiscale Weight Recurrence -/

/-- **Seed Ball-Parity Witness Family from Ball Filling (`hasBallParityWitnessFamily_of_ball_filling`, Part I, Proposition 5.3 (`prop:cluster-decoder-witness`)):**
    On any CSS code `code` where `syndrome (dualCode code) L_X = 0` and every global stabilizer in
    `Ball3D x0 r` is a stabilizer (`globalStabilizersInBall code x0 r ⊆ locallyGeneratedInBall code x0 R_fill`),
    the zero parity rule `ψ ≡ 0` and the singleton check indicators `W = image singleQubit` form a
    valid `HasBallParityWitnessFamily code L_Z L_X r 1 (Fintype.card M_X)`. -/
theorem hasBallParityWitnessFamily_of_ball_filling {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2) (r R_fill : ℝ)
    (h_syn_X : syndrome (dualCode code) L_X = 0)
    (h_fill : ∀ x0 : Point3D,
      globalStabilizersInBall code x0 r ⊆ locallyGeneratedInBall code x0 R_fill) :
    HasBallParityWitnessFamily code L_Z L_X r 1 (Fintype.card M_X) := by
  classical
  let ψ : (M_X → ZMod 2) → ZMod 2 := fun _ => 0
  let W : Finset (M_X → ZMod 2) := Finset.univ.image (singleQubit : M_X → (M_X → ZMod 2))
  refine ⟨ψ, W, rfl, ?_, ?_, ?_⟩
  · calc W.card
      _ ≤ (Finset.univ : Finset M_X).card := Finset.card_image_le
      _ = Fintype.card M_X := Finset.card_univ
  · intro c hc
    rcases Finset.mem_image.mp hc with ⟨m, _, rfl⟩
    dsimp [syndromeWeight]
    have h_mem : m ∈ Finset.univ.filter (fun m' : M_X => singleQubit m m' ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ m, by simp [singleQubit]⟩
    have h_pos : 1 ≤ (Finset.univ.filter (fun m' : M_X => singleQubit m m' ≠ 0)).card :=
      Finset.card_pos.mpr ⟨m, h_mem⟩
    exact_mod_cast h_pos
  · intro e e' x0 h_diff h_disc
    dsimp [ψ] at h_disc
    rw [zero_add, zero_add] at h_disc
    by_contra h_none
    push_neg at h_none
    have he_zero : syndrome code e = 0 := by
      ext m
      have hm_mem : singleQubit m ∈ W := Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩
      obtain ⟨⟨m1, hm1_c, hm1_s⟩, _⟩ := h_none (singleQubit m) hm_mem
      have hm1_eq : m1 = m := by
        dsimp [singleQubit] at hm1_c
        by_contra hne; exact hm1_c (if_neg hne)
      subst hm1_eq; exact hm1_s
    have he'_zero : syndrome code e' = 0 := by
      ext m
      have hm_mem : singleQubit m ∈ W := Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩
      obtain ⟨_, ⟨m1, hm1_c, hm1_s⟩⟩ := h_none (singleQubit m) hm_mem
      have hm1_eq : m1 = m := by
        dsimp [singleQubit] at hm1_c
        by_contra hne; exact hm1_c (if_neg hne)
      subst hm1_eq; exact hm1_s
    let g : Q → ZMod 2 := e' + e
    have hg_syn : syndrome code g = 0 := by
      dsimp [g]; rw [map_add, he'_zero, he_zero, add_zero]
    have hg_supp : supp1 code g ⊆ ball3D x0 r := by
      intro p ⟨q, hq_ne, hp⟩
      subst hp
      apply h_diff q
      intro h_eq
      apply hq_ne
      dsimp [g]
      rw [h_eq]
      exact zmod2_add_self (e' q)
    obtain ⟨c2, _, hc2_gen⟩ := h_fill x0 ⟨hg_syn, hg_supp⟩
    have h_pair_zero : dualPairing L_X g = 0 := by
      rw [← hc2_gen]
      exact dualPairing_checkGen_zero code c2 L_X h_syn_X
    have h_pair_add : dualPairing L_X g = dualPairing L_X e' + dualPairing L_X e :=
      dualPairing_add_right_zmod2 L_X e' e
    rw [h_pair_add] at h_pair_zero
    have h_eq_pair : dualPairing L_X e' = dualPairing L_X e := by
      have h_alg : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact h_alg _ _ h_pair_zero
    exact h_disc h_eq_pair

/-- Primal base case of `HasBallParityWitnessFamily` at `bdlIteratedBundled 1` for any `0 ≤ r ≤ 7015`. -/
theorem hasBallParityWitnessFamily_bdlIterated1_primal {r : ℝ} (hr0 : 0 ≤ r) (hr_hi : r ≤ 7015) :
    HasBallParityWitnessFamily (bdlIteratedBundled 1).code
      (bdlIteratedLZ 1) (bdlIteratedLX 1)
      r 1 (Fintype.card (bdlIteratedBundled 1).M_X) := by
  have h_hom := hasUniqueLogicalHomology_bdlIterated 1
  apply hasBallParityWitnessFamily_of_ball_filling
    (bdlIteratedBundled 1).code (bdlIteratedLZ 1) (bdlIteratedLX 1) r bdlBaseFillingRadius
    h_hom.h_syn_X
  intro x0
  exact (bdlHalfStep_subcylinder_filling 0 x0 hr0 hr_hi).1

/-- Dual base case of `HasBallParityWitnessFamily` at `bdlIteratedBundled 1` for any `0 ≤ r ≤ 7015`. -/
theorem hasBallParityWitnessFamily_bdlIterated1_dual {r : ℝ} (hr0 : 0 ≤ r) (hr_hi : r ≤ 7015) :
    HasBallParityWitnessFamily (dualCode (bdlIteratedBundled 1).code)
      (bdlIteratedLX 1) (bdlIteratedLZ 1)
      r 1 (Fintype.card (bdlIteratedBundled 1).M_Z) := by
  have h_hom := hasUniqueLogicalHomology_bdlIterated 1
  apply hasBallParityWitnessFamily_of_ball_filling
    (dualCode (bdlIteratedBundled 1).code) (bdlIteratedLX 1) (bdlIteratedLZ 1) r bdlBaseFillingRadius
    h_hom.h_syn_Z
  intro x0
  exact (bdlHalfStep_subcylinder_filling 0 x0 hr0 hr_hi).2

/-- Raw witness weight sequence `clusterRawWeight k` across `k` full RG steps from `bdlIteratedBundled 1`. -/
def clusterRawWeight : ℕ → ℕ
  | 0 => 1
  | k + 1 => (27 * clusterRawWeight k + 15) / 16

/-- For `3 ≤ k`, the raw cluster weight `clusterRawWeight k` is at least `7`. -/
lemma clusterRawWeight_ge_seven_of_ge_three {k : ℕ} (hk : 3 ≤ k) :
    7 ≤ clusterRawWeight k := by
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases hm3 : 3 ≤ m
    · have h_m := ih hm3
      dsimp [clusterRawWeight]
      omega
    · have hm2 : m = 2 := by omega
      subst hm2
      decide

/-- Exponential growth bound `3 ^ k ≤ 2 ^ k * clusterRawWeight k` for all `k : ℕ`. -/
lemma three_pow_le_two_pow_mul_clusterRawWeight (k : ℕ) :
    3 ^ k ≤ 2 ^ k * clusterRawWeight k := by
  induction k with
  | zero => simp [clusterRawWeight]
  | succ m ih =>
    have h_step : 3 * clusterRawWeight m ≤ 2 * clusterRawWeight (m + 1) := by
      dsimp [clusterRawWeight]; omega
    calc 3 ^ (m + 1)
      _ = 3 * 3 ^ m := by ring
      _ ≤ 3 * (2 ^ m * clusterRawWeight m) := Nat.mul_le_mul_left 3 ih
      _ = 2 ^ m * (3 * clusterRawWeight m) := by ring
      _ ≤ 2 ^ m * (2 * clusterRawWeight (m + 1)) := Nat.mul_le_mul_left (2 ^ m) h_step
      _ = 2 ^ (m + 1) * clusterRawWeight (m + 1) := by ring

/-- Parameterized single-step base factor `F * 2 ^ (41 * F)`. -/
def clusterStepBaseGen (F : ℕ) : ℕ :=
  F * 2 ^ (41 * F)

/-- Kernel-opaque `Nat` wrapper via `Classical.choose` to prevent `reduce_bin_nat_op` from
    evaluating large closed powers of `2`. -/
noncomputable def opaqueNat (n : ℕ) : ℕ :=
  Classical.choose (⟨n, rfl⟩ : ∃ m : ℕ, m = n)

/-- Unfolding lemma `opaqueNat n = n` via `Classical.choose_spec`. -/
lemma opaqueNat_eq (n : ℕ) : opaqueNat n = n :=
  Classical.choose_spec (⟨n, rfl⟩ : ∃ m : ℕ, m = n)

/-- Universal single-step cluster base factor `bdlSingleStepFactor * 2 ^ (41 * bdlSingleStepFactor)`. -/
noncomputable def bdlClusterStepBase : ℕ :=
  opaqueNat (clusterStepBaseGen bdlSingleStepFactor)

/-- Identification `bdlClusterStepBase = clusterStepBaseGen bdlSingleStepFactor`. -/
lemma bdlClusterStepBase_eq :
    bdlClusterStepBase = clusterStepBaseGen bdlSingleStepFactor :=
  opaqueNat_eq _

/-- Lower bound `F ≤ clusterStepBaseGen F`. -/
lemma le_clusterStepBaseGen (F : ℕ) : F ≤ clusterStepBaseGen F := by
  dsimp [clusterStepBaseGen]
  exact Nat.le_mul_of_pos_right F (Nat.two_pow_pos (41 * F))

/-- Exponential lower bound `2 ^ (41 * F) ≤ clusterStepBaseGen F` for `2 ≤ F`. -/
lemma two_pow_le_clusterStepBaseGen {F : ℕ} (hF : 2 ≤ F) :
    2 ^ (41 * F) ≤ clusterStepBaseGen F := by
  dsimp [clusterStepBaseGen]
  exact Nat.le_mul_of_pos_left (2 ^ (41 * F)) (by omega)

/-- Bounds `bdlSingleStepFactor ≤ bdlClusterStepBase`. -/
lemma bdlSingleStepFactor_le_bdlClusterStepBase :
    bdlSingleStepFactor ≤ bdlClusterStepBase := by
  rw [bdlClusterStepBase_eq]
  exact le_clusterStepBaseGen bdlSingleStepFactor

/-- Bounds `2 ^ (41 * bdlSingleStepFactor) ≤ bdlClusterStepBase`. -/
lemma two_pow_le_bdlClusterStepBase :
    2 ^ (41 * bdlSingleStepFactor) ≤ bdlClusterStepBase := by
  rw [bdlClusterStepBase_eq]
  exact two_pow_le_clusterStepBaseGen bdlSingleStepFactor_ge_two

/-- Lower bound `2 ≤ bdlClusterStepBase`. -/
lemma bdlClusterStepBase_ge_two : 2 ≤ bdlClusterStepBase :=
  le_trans bdlSingleStepFactor_ge_two bdlSingleStepFactor_le_bdlClusterStepBase

/-- Both check cardinalities `card B.M_X` and `card B.M_Z` are bounded by `bundledCellCount B`. -/
lemma card_MX_MZ_le_bundledCellCount (B : BundledCSSCode3D) :
    Fintype.card B.M_X ≤ bundledCellCount B ∧
    Fintype.card B.M_Z ≤ bundledCellCount B := by
  dsimp [bundledCellCount]; omega

/-- Base-case arithmetic bound `9 * (F ^ 2) ^ 1 ≤ (B ^ 8) ^ (clusterRawWeight 0)`. -/
lemma nine_mul_sq_pow_one_le_pow_eight {F B : ℕ} (hF : 2 ≤ F) (hFB : F ≤ B) :
    9 * (F ^ 2) ^ 1 ≤ (B ^ 8) ^ (clusterRawWeight 0) := by
  dsimp [clusterRawWeight]
  rw [pow_one, pow_one]
  have h9 : 9 ≤ F ^ 4 := by
    have : 2 ^ 4 ≤ F ^ 4 := Nat.pow_le_pow_left hF 4
    omega
  have hF1 : 1 ≤ F := by omega
  calc 9 * F ^ 2
    _ ≤ F ^ 4 * F ^ 2 := Nat.mul_le_mul_right (F ^ 2) h9
    _ = F ^ 6 := by ring
    _ ≤ F ^ 8 := Nat.pow_le_pow_right hF1 (by decide)
    _ ≤ B ^ 8 := Nat.pow_le_pow_left hFB 8

/-- Bounds the check cardinalities of `bdlIteratedBundled 1` by `(bdlClusterStepBase ^ 8) ^ (clusterRawWeight 0)`. -/
lemma card_iterated1_le_clusterStepBase :
    Fintype.card (bdlIteratedBundled 1).M_X ≤ (bdlClusterStepBase ^ 8) ^ (clusterRawWeight 0) ∧
    Fintype.card (bdlIteratedBundled 1).M_Z ≤ (bdlClusterStepBase ^ 8) ^ (clusterRawWeight 0) := by
  have h_cards := card_MX_MZ_le_bundledCellCount (bdlIteratedBundled 1)
  have h_cell : bundledCellCount (bdlIteratedBundled 1) ≤ 9 * (bdlSingleStepFactor ^ 2) ^ 1 := by
    rw [bdlIteratedBundled_eq]
    exact bundledCellCount_iterated_le 1
  have h_pow := nine_mul_sq_pow_one_le_pow_eight
    bdlSingleStepFactor_ge_two bdlSingleStepFactor_le_bdlClusterStepBase
  exact ⟨h_cards.1.trans (h_cell.trans h_pow),
         h_cards.2.trans (h_cell.trans h_pow)⟩

/-- At even half-steps `2 * n`, `bdlHalfStep (2 * n)` equals `bdlIteratedBundled n`. -/
lemma bdlHalfStep_even_eq_bdlIteratedBundled (n : ℕ) :
    bdlHalfStep (2 * n) = bdlIteratedBundled n :=
  (bdlHalfStep_even n).trans (bdlIteratedBundled_eq n).symm

/-- Every full BDL iteration `bdlIteratedBundled n` satisfies `HasBDLConeInvariants`. -/
lemma hasBDLConeInvariants_bdlIteratedBundled (n : ℕ) :
    HasBDLConeInvariants (bdlIteratedBundled n) := by
  rw [← bdlHalfStep_even_eq_bdlIteratedBundled n]
  exact hasBDLConeInvariants_bdlHalfStep (2 * n)

/-- One-step recurrence bound for the pool cardinality across a full BDL step. -/
lemma cluster_step_card_le_gen {B F G : ℕ} (hF : 2 ≤ F) (hFB : F ≤ B) (hGB : G ≤ B) (m : ℕ) :
    (((B ^ 8) ^ (clusterRawWeight m) * F ^ (clusterRawWeight m)) * G ^ (clusterRawWeight m) ≤
      (B ^ 8) ^ (clusterRawWeight (m + 1))) ∧
    (((B ^ 8) ^ (clusterRawWeight m) * G ^ (clusterRawWeight m)) *
      F ^ ((27 * clusterRawWeight m + 15) / 16) ≤
      (B ^ 8) ^ (clusterRawWeight (m + 1))) := by
  let w := clusterRawWeight m
  let w' := (27 * w + 15) / 16
  have hB1 : 1 ≤ B := le_trans (by omega : 1 ≤ F) hFB
  have hw_le : w ≤ w' := by dsimp [w']; omega
  have hexp : 8 * w + w + w' ≤ 8 * w' := by dsimp [w']; omega
  have h_Bw_le : B ^ w ≤ B ^ w' := Nat.pow_le_pow_right hB1 hw_le
  have h_Fw_le : F ^ w ≤ B ^ w := Nat.pow_le_pow_left hFB w
  have h_Fw'_le : F ^ w' ≤ B ^ w' := Nat.pow_le_pow_left hFB w'
  have h_Gw_le : G ^ w ≤ B ^ w := Nat.pow_le_pow_left hGB w
  have h_Gw_le' : G ^ w ≤ B ^ w' := h_Gw_le.trans h_Bw_le
  have h_comb : ((B ^ 8) ^ w * B ^ w) * B ^ w' ≤ (B ^ 8) ^ w' := by
    have h_lhs : ((B ^ 8) ^ w * B ^ w) * B ^ w' = B ^ (8 * w + w + w') := by ring
    have h_rhs : (B ^ 8) ^ w' = B ^ (8 * w') := by ring
    rw [h_lhs, h_rhs]
    exact Nat.pow_le_pow_right hB1 hexp
  change (((B ^ 8) ^ w * F ^ w) * G ^ w ≤ (B ^ 8) ^ w') ∧
    (((B ^ 8) ^ w * G ^ w) * F ^ w' ≤ (B ^ 8) ^ w')
  refine ⟨?_, ?_⟩
  · calc ((B ^ 8) ^ w * F ^ w) * G ^ w
      _ ≤ ((B ^ 8) ^ w * B ^ w) * B ^ w' :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h_Fw_le) h_Gw_le'
      _ ≤ (B ^ 8) ^ w' := h_comb
  · calc ((B ^ 8) ^ w * G ^ w) * F ^ w'
      _ ≤ ((B ^ 8) ^ w * B ^ w) * B ^ w' :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h_Gw_le) h_Fw'_le
      _ ≤ (B ^ 8) ^ w' := h_comb

/-- **Inductive Step for Iterated Ball-Parity Witness Families (`hasBallParityWitnessFamily_bdlIterated_succ`, Part I, Proposition 5.3 (`prop:cluster-decoder-witness`)):**
    For every `k : ℕ` and every `0 ≤ r` with `scaleDownRadius (2 * k) r ≤ 7015`,
    both `(bdlIteratedBundled (k + 1)).code` and `dualCode (bdlIteratedBundled (k + 1)).code`
    satisfy `HasBallParityWitnessFamily` at radius `r` with weight `clusterRawWeight k`
    and cardinality `(bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)`. -/
theorem hasBallParityWitnessFamily_bdlIterated_succ (k : ℕ) :
    ∀ {r : ℝ}, 0 ≤ r → scaleDownRadius (2 * k) r ≤ 7015 →
      HasBallParityWitnessFamily (bdlIteratedBundled (k + 1)).code
        (bdlIteratedLZ (k + 1)) (bdlIteratedLX (k + 1))
        r (clusterRawWeight k) ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)) ∧
      HasBallParityWitnessFamily (dualCode (bdlIteratedBundled (k + 1)).code)
        (bdlIteratedLX (k + 1)) (bdlIteratedLZ (k + 1))
        r (clusterRawWeight k) ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)) := by
  induction k with
  | zero =>
    intro r hr0 hr_hi
    dsimp [scaleDownRadius] at hr_hi
    have h_card := card_iterated1_le_clusterStepBase
    exact ⟨hasBallParityWitnessFamily_mono_N h_card.1
            (hasBallParityWitnessFamily_bdlIterated1_primal hr0 hr_hi),
           hasBallParityWitnessFamily_mono_N h_card.2
            (hasBallParityWitnessFamily_bdlIterated1_dual hr0 hr_hi)⟩
  | succ m ih =>
    intro r hr0 hr_hi
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
    let r1 : ℝ := r / (bdlLambda : ℝ) + 7003
    let r2 : ℝ := r1 / (bdlLambda : ℝ) + 7003
    have hr1 : 0 ≤ r1 := add_nonneg (div_nonneg hr0 (le_of_lt hlam_pos)) (by norm_num)
    have hr2 : 0 ≤ r2 := add_nonneg (div_nonneg hr1 (le_of_lt hlam_pos)) (by norm_num)
    have h_sd_eq : scaleDownRadius (2 * (m + 1)) r = scaleDownRadius (2 * m) r2 := by
      have h_2m : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [h_2m]
      rfl
    rw [h_sd_eq] at hr_hi
    obtain ⟨h_ih_P, h_ih_D⟩ := ih hr2 hr_hi
    let B := bdlIteratedBundled (m + 1)
    have h_inv_B : HasBDLConeInvariants B := hasBDLConeInvariants_bdlIteratedBundled (m + 1)
    have h_inv_B1 : HasBDLConeInvariants (bdlRandomStepX B) :=
      hasBDLConeInvariants_bdlRandomStepX B h_inv_B
    obtain ⟨h_B1_P, h_B1_D⟩ := hasBallParityWitnessFamily_stepX B h_inv_B
      (bdlIteratedLZ (m + 1)) (bdlIteratedLX (m + 1)) hr1
      (clusterRawWeight m) (clusterRawWeight m)
      ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight m))
      ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight m))
      h_ih_P h_ih_D
    obtain ⟨h_B2_P, h_B2_D⟩ := hasBallParityWitnessFamily_stepZ (bdlRandomStepX B) h_inv_B1
      (stepXLZ B (bdlIteratedLZ (m + 1))) (stepXLX B (bdlIteratedLX (m + 1)))
      hr0 (clusterRawWeight m) ((27 * clusterRawWeight m + 15) / 16)
      (((bdlClusterStepBase ^ 8) ^ (clusterRawWeight m)) * bdlSingleStepFactor ^ (clusterRawWeight m))
      (((bdlClusterStepBase ^ 8) ^ (clusterRawWeight m)) * (2 ^ (41 * bdlSingleStepFactor)) ^ (clusterRawWeight m))
      h_B1_P h_B1_D
    have h_bounds := cluster_step_card_le_gen
      bdlSingleStepFactor_ge_two bdlSingleStepFactor_le_bdlClusterStepBase
      two_pow_le_bdlClusterStepBase m
    exact ⟨hasBallParityWitnessFamily_mono_N h_bounds.1 h_B2_P,
           hasBallParityWitnessFamily_mono_N h_bounds.2 h_B2_D⟩

/-! ## 3. Ball-Parity Witness Family Specialization to `bdlWeldedCode` -/

/-- Transports a 1-chain `B1.Q → ZMod 2` across an equality `hB : B1 = B2` of bundled 3D CSS codes. -/
def transportBundledChain {B1 B2 : BundledCSSCode3D} (hB : B1 = B2) (c : B1.Q → ZMod 2) :
    B2.Q → ZMod 2 :=
  hB ▸ c

lemma hasUniqueLogicalHomology_transportBundled {B1 B2 : BundledCSSCode3D} (hB : B1 = B2)
    {L_Z L_X : B1.Q → ZMod 2} (h : HasUniqueLogicalHomology B1.code L_Z L_X) :
    HasUniqueLogicalHomology B2.code (transportBundledChain hB L_Z) (transportBundledChain hB L_X) := by
  subst hB; exact h

lemma hasBallParityWitnessFamily_transportBundled {B1 B2 : BundledCSSCode3D} (hB : B1 = B2)
    {L_Z L_X : B1.Q → ZMod 2} {r : ℝ} {w N : ℕ}
    (h : HasBallParityWitnessFamily B1.code L_Z L_X r w N) :
    HasBallParityWitnessFamily B2.code (transportBundledChain hB L_Z) (transportBundledChain hB L_X) r w N := by
  subst hB; exact h

lemma hasBallParityWitnessFamily_dual_transportBundled {B1 B2 : BundledCSSCode3D} (hB : B1 = B2)
    {L_Z L_X : B1.Q → ZMod 2} {r : ℝ} {w N : ℕ}
    (h : HasBallParityWitnessFamily (dualCode B1.code) L_X L_Z r w N) :
    HasBallParityWitnessFamily (dualCode B2.code)
      (transportBundledChain hB L_X) (transportBundledChain hB L_Z) r w N := by
  subst hB; exact h

/-- Canonical logical Z-cycle `bdlWeldedLZ k : BDLWeldedQubit k → ZMod 2` on `bdlWeldedCode k`. -/
noncomputable def bdlWeldedLZ (k : ℕ) : BDLWeldedQubit k → ZMod 2 :=
  transportBundledChain (bdlIteratedBundled_eq (k + 1)) (bdlIteratedLZ (k + 1))

/-- Canonical logical X-cocycle `bdlWeldedLX k : BDLWeldedQubit k → ZMod 2` on `bdlWeldedCode k`. -/
noncomputable def bdlWeldedLX (k : ℕ) : BDLWeldedQubit k → ZMod 2 :=
  transportBundledChain (bdlIteratedBundled_eq (k + 1)) (bdlIteratedLX (k + 1))

/-- `bdlWeldedCode k` satisfies `HasUniqueLogicalHomology` with `(bdlWeldedLZ k, bdlWeldedLX k)`. -/
theorem hasUniqueLogicalHomology_bdlWelded (k : ℕ) :
    HasUniqueLogicalHomology (bdlWeldedCode k) (bdlWeldedLZ k) (bdlWeldedLX k) :=
  hasUniqueLogicalHomology_transportBundled (bdlIteratedBundled_eq (k + 1))
    (hasUniqueLogicalHomology_bdlIterated (k + 1))

/-- `bdlWeldedLZ k` has zero X-check syndrome (`syndrome (bdlWeldedCode k) (bdlWeldedLZ k) = 0`). -/
lemma syndrome_bdlWeldedLZ (k : ℕ) :
    syndrome (bdlWeldedCode k) (bdlWeldedLZ k) = 0 :=
  (hasUniqueLogicalHomology_bdlWelded k).h_syn_Z

/-- `bdlWeldedLX k` has zero Z-check syndrome (`syndrome (dualCode (bdlWeldedCode k)) (bdlWeldedLX k) = 0`). -/
lemma syndrome_bdlWeldedLX (k : ℕ) :
    syndrome (dualCode (bdlWeldedCode k)) (bdlWeldedLX k) = 0 :=
  (hasUniqueLogicalHomology_bdlWelded k).h_syn_X

/-- `bdlWeldedLZ k` and `bdlWeldedLX k` have unit symplectic pairing (`dualPairing = 1`). -/
lemma dualPairing_bdlWeldedLZ_bdlWeldedLX (k : ℕ) :
    dualPairing (bdlWeldedLZ k) (bdlWeldedLX k) = 1 :=
  (hasUniqueLogicalHomology_bdlWelded k).h_pair

/-- **Main Radius-$2$ Multiscale Ball Parity Witness Theorem for `bdlWeldedCode k`
    (`hasBallParityWitnessFamily_bdlWelded_two`)**:
    At every level `k : ℕ`, both `bdlWeldedCode k` and `dualCode (bdlWeldedCode k)` admit a
    `HasBallParityWitnessFamily` at Euclidean radius `r = 2` with weight `clusterRawWeight k`
    and pool cardinality `(bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)`. -/
theorem hasBallParityWitnessFamily_bdlWelded_two (k : ℕ) :
    HasBallParityWitnessFamily (bdlWeldedCode k) (bdlWeldedLZ k) (bdlWeldedLX k)
      2 (clusterRawWeight k) ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)) ∧
    HasBallParityWitnessFamily (dualCode (bdlWeldedCode k)) (bdlWeldedLX k) (bdlWeldedLZ k)
      2 (clusterRawWeight k) ((bdlClusterStepBase ^ 8) ^ (clusterRawWeight k)) := by
  have h_pow_ge1 : (1 : ℝ) ≤ (bdlLambda : ℝ) ^ (2 * k) :=
    one_le_pow₀ (by have := bdlLambda_ge_10000; linarith)
  have h_div_le : (2 : ℝ) / ((bdlLambda : ℝ) ^ (2 * k)) ≤ 2 :=
    div_le_self (by norm_num) h_pow_ge1
  have h_sd_bd := scaleDownRadius_bound (2 * k) (by norm_num : (0 : ℝ) ≤ 2)
  have h_sd2 : scaleDownRadius (2 * k) 2 ≤ 7015 := by linarith
  obtain ⟨hP, hD⟩ := hasBallParityWitnessFamily_bdlIterated_succ k (by norm_num : (0 : ℝ) ≤ 2) h_sd2
  exact ⟨hasBallParityWitnessFamily_transportBundled (bdlIteratedBundled_eq (k + 1)) hP,
         hasBallParityWitnessFamily_dual_transportBundled (bdlIteratedBundled_eq (k + 1)) hD⟩

/-- Exponential lower bound `(3 / 2 : ℝ) ^ k ≤ (clusterRawWeight k : ℝ)` for all `k : ℕ`. -/
lemma three_div_two_pow_le_clusterRawWeight (k : ℕ) :
    (3 / 2 : ℝ) ^ k ≤ (clusterRawWeight k : ℝ) := by
  have h1 : ((3 ^ k : ℕ) : ℝ) ≤ ((2 ^ k * clusterRawWeight k : ℕ) : ℝ) := by
    exact_mod_cast three_pow_le_two_pow_mul_clusterRawWeight k
  push_cast at h1
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [div_pow, div_le_iff₀ h2k_pos]
  linarith

/-- Exponential lower bound `(1 / 3 : ℝ) * (3 / 2 : ℝ) ^ k ≤ (clusterRawWeight k : ℝ)` for all `k : ℕ`. -/
lemma one_div_three_mul_three_div_two_pow_le_clusterRawWeight (k : ℕ) :
    (1 / 3 : ℝ) * (3 / 2 : ℝ) ^ k ≤ (clusterRawWeight k : ℝ) := by
  have h := three_div_two_pow_le_clusterRawWeight k
  have h_pos : (0 : ℝ) ≤ (3 / 2 : ℝ) ^ k := by positivity
  linarith

private lemma clusterStepBaseGen_pow_eight_le_two_pow (F : ℕ) :
    clusterStepBaseGen F ^ 8 ≤ 2 ^ (336 * F) := by
  have hF_two : F ≤ 2 ^ F := le_of_lt Nat.lt_two_pow_self
  have h_base : clusterStepBaseGen F ≤ 2 ^ (42 * F) := by
    dsimp [clusterStepBaseGen]
    have h1 : F + 41 * F = 42 * F := by omega
    calc F * 2 ^ (41 * F)
      _ ≤ 2 ^ F * 2 ^ (41 * F) := Nat.mul_le_mul_right _ hF_two
      _ = 2 ^ (F + 41 * F) := (Nat.pow_add 2 F (41 * F)).symm
      _ = 2 ^ (42 * F) := congrArg (2 ^ ·) h1
  have h2 : 42 * F * 8 = 336 * F := by omega
  calc clusterStepBaseGen F ^ 8
    _ ≤ (2 ^ (42 * F)) ^ 8 := Nat.pow_le_pow_left h_base 8
    _ = 2 ^ (42 * F * 8) := (Nat.pow_mul 2 (42 * F) 8).symm
    _ = 2 ^ (336 * F) := congrArg (2 ^ ·) h2

/-- Upper bound `bdlClusterStepBase ^ 8 ≤ 2 ^ (336 * bdlSingleStepFactor)`. -/
lemma bdlClusterStepBase_pow_eight_le_two_pow :
    bdlClusterStepBase ^ 8 ≤ 2 ^ (336 * bdlSingleStepFactor) := by
  rw [bdlClusterStepBase_eq]
  exact clusterStepBaseGen_pow_eight_le_two_pow bdlSingleStepFactor

/-- Critical inverse temperature bound `Real.log ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) + 100 ≤ beta_c_BDL`. -/
lemma log_bdlClusterStepBase_pow_eight_le_beta_c_BDL :
    Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) + 100 ≤ betaCritBDL := by
  have h_pos : (0 : ℝ) < ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) := by
    have : 2 ≤ bdlClusterStepBase := bdlClusterStepBase_ge_two
    positivity
  have h_le_pow : (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (336 * bdlSingleStepFactor) := by
    exact_mod_cast bdlClusterStepBase_pow_eight_le_two_pow
  have h_log_le : Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) ≤
      (336 * bdlSingleStepFactor : ℕ) * Real.log 2 := by
    calc Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ))
      _ ≤ Real.log ((2 : ℝ) ^ (336 * bdlSingleStepFactor)) := Real.log_le_log h_pos h_le_pow
      _ = (336 * bdlSingleStepFactor : ℕ) * Real.log 2 := Real.log_pow 2 (336 * bdlSingleStepFactor)
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h_F_nonneg : (0 : ℝ) ≤ (336 * bdlSingleStepFactor : ℕ) := by positivity
  have h_log_le_336 : Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) ≤
      336 * (bdlSingleStepFactor : ℝ) := by
    calc Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ))
      _ ≤ (336 * bdlSingleStepFactor : ℕ) * Real.log 2 := h_log_le
      _ ≤ (336 * bdlSingleStepFactor : ℕ) * 1 :=
        mul_le_mul_of_nonneg_left h_log2_le_one h_F_nonneg
      _ = 336 * (bdlSingleStepFactor : ℝ) := by push_cast; ring
  have h_extra_nonneg : (0 : ℝ) ≤
      2 * ((mMaxBDL + qCodeBDL : ℕ) : ℝ) * ((4 * r0BDL + 1 : ℕ) ^ 3 : ℝ) := by positivity
  have h_F_pos : (0 : ℝ) ≤ (bdlSingleStepFactor : ℝ) := by positivity
  dsimp [betaCritBDL, bdlSingleStepFactor] at h_log_le_336 h_F_pos ⊢
  linarith

end BDLDecoder
end WeldedHierarchy
