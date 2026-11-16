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
import Proofs.HierarchicalClusterDecoder.ZeroSpilloverWitnessDecoder
import Proofs.TwoAxisMemorySynthesis.Part1TwoAxisMemorySynthesis

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder InhomogeneousMemoryChallenge
open SpacetimeWorldlineKP Part1TwoAxisMemorySynthesis

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace FixedTempPerturbativeGibbsSynthesis

/-!
# Multiscale Cluster Witness Covering and Fixed-Temperature Peierls Majorants

Constructs the multiscale connected-cluster witness family (`bdlWitnessSetX`, `bdlWitnessSetZ`, `bdlWitnessFamily`) for the three-layer welded CSS hierarchy. Verifies via the $16/27$ two-stage cleaner contraction that every unsafe syndrome admits a macroscopic connected cluster witness (`isPositiveCheckWitnessCover_bdlSafeSyndromeSet`) and bounds the resulting geometric Peierls majorant series (`sum_exp_neg_half_beta_c_bdlWitnessFamily_le_one`) at fixed temperature.

## References

* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`)
* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Lemma 5.4 (`lem:percolating-cluster-bounds`)
* Part II, Section 4 (`sec:welded-hierarchy`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

/-- Grid-snapped check index support of an $X$-syndrome parity witness $c \in W_Z$. -/
def bdlWitnessSetX (k : ℕ) (c : BDLWeldedCheckX k → ZMod 2) :
    Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :=
  (Finset.univ.filter (fun mX => c mX ≠ 0)).image (bdlCheckXSlot k)

/-- Grid-snapped check index support of a $Z$-syndrome parity witness $c \in W_X$. -/
def bdlWitnessSetZ (k : ℕ) (c : BDLWeldedCheckZ k → ZMod 2) :
    Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :=
  (Finset.univ.filter (fun mZ => c mZ ≠ 0)).image (bdlCheckZSlot k)

/-- Combined family of grid-snapped positive check-witness subsets for $(W_Z, W_X)$. -/
def bdlWitnessFamily (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2)) :
    Finset (Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL)) :=
  W_Z.image (bdlWitnessSetX k) ∪ W_X.image (bdlWitnessSetZ k)

/-- Every unsafe syndrome $\sigma \notin \mathrm{bdlSafeSyndromeSet}(k, W_Z, W_X)$ is covered by a
    witness $W \in \mathrm{bdlWitnessFamily}(k, W_Z, W_X)$ on which $\sigma_i = \mathrm{true}$. -/
theorem isPositiveCheckWitnessCover_bdlSafeSyndromeSet (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2)) :
    IsPositiveCheckWitnessCover (bdlSafeSyndromeSet k W_Z W_X) (bdlWitnessFamily k W_Z W_X) := by
  intro σ hσ
  have h_not_safe : ¬ IsSafeBDLSyndrome k W_Z W_X σ := by
    intro h_safe
    exact hσ (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, h_safe⟩)
  unfold IsSafeBDLSyndrome at h_not_safe
  rw [not_and_or] at h_not_safe
  rcases h_not_safe with hZ | hX
  · push_neg at hZ
    rcases hZ with ⟨c, hc, h_all⟩
    refine ⟨bdlWitnessSetX k c,
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc), fun i hi => ?_⟩
    rcases Finset.mem_image.mp hi with ⟨mX, hmX, rfl⟩
    have h_ne := h_all mX (Finset.mem_filter.mp hmX).2
    dsimp [bdlPullSynX] at h_ne
    cases h_b : σ (bdlCheckXSlot k mX)
    · rw [h_b] at h_ne; exact False.elim (h_ne rfl)
    · rfl
  · push_neg at hX
    rcases hX with ⟨c, hc, h_all⟩
    refine ⟨bdlWitnessSetZ k c,
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc), fun i hi => ?_⟩
    rcases Finset.mem_image.mp hi with ⟨mZ, hmZ, rfl⟩
    have h_ne := h_all mZ (Finset.mem_filter.mp hmZ).2
    dsimp [bdlPullSynZ] at h_ne
    cases h_b : σ (bdlCheckZSlot k mZ)
    · rw [h_b] at h_ne; exact False.elim (h_ne rfl)
    · rfl

/-- Injectivity of `bdlCheckXSlot k` and `bdlCheckZSlot k` preserves the witness weight lower bound
    `clusterRawWeight k ≤ W.card`. -/
theorem card_floor_bdlWitnessFamily (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_wt : ∀ c ∈ W_Z, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c)
    (hWX_wt : ∀ c ∈ W_X, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c) :
    ∀ W ∈ bdlWitnessFamily k W_Z W_X, clusterRawWeight k ≤ W.card := by
  intro W hW
  rcases Finset.mem_union.mp hW with hZ | hX
  · rcases Finset.mem_image.mp hZ with ⟨c, hc, rfl⟩
    dsimp [bdlWitnessSetX]
    rw [Finset.card_image_of_injective _ (bdlCheckXSlot_injective k)]
    have h_wt := hWZ_wt c hc
    dsimp [WeldedHierarchy.syndromeWeight] at h_wt
    exact_mod_cast h_wt
  · rcases Finset.mem_image.mp hX with ⟨c, hc, rfl⟩
    dsimp [bdlWitnessSetZ]
    rw [Finset.card_image_of_injective _ (bdlCheckZSlot_injective k)]
    have h_wt := hWX_wt c hc
    dsimp [WeldedHierarchy.syndromeWeight] at h_wt
    exact_mod_cast h_wt

private lemma bdlCheckXSlot_eq_pair (k : ℕ) (mX : BDLWeldedCheckX k) :
    bdlCheckXSlot k mX = Sum.inr (Sum.inl (bdlCheckXPair k mX)) := rfl

private lemma bdlCheckZSlot_eq_pair (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    bdlCheckZSlot k mZ = Sum.inr (Sum.inr (bdlCheckZPair k mZ)) := rfl

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  bdlWeldedCode

lemma decide_mem_bdlWitnessSetX_eq_embedSynGen (k : ℕ) (c : BDLWeldedCheckX k → ZMod 2) :
    (fun idx => decide (idx ∈ bdlWitnessSetX k c)) =
      embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) (fun _ => false) c 0 := by
  ext idx
  unfold bdlWitnessSetX embedSynGen embedCheckBits
  rcases idx with p | ix | iz
  · dsimp only
    rw [decide_eq_false]
    rintro h
    rcases Finset.mem_image.mp h with ⟨mX, _, h_eq⟩
    rw [bdlCheckXSlot_eq_pair] at h_eq
    cases h_eq
  · dsimp only
    by_cases hex : ∃ mX : BDLWeldedCheckX k, bdlCheckXPair k mX = ix
    · rw [dif_pos hex]
      have hm₀ : bdlCheckXPair k (Classical.choose hex) = ix := Classical.choose_spec hex
      have h_mem_iff :
          Sum.inr (Sum.inl ix) ∈ (Finset.univ.filter (fun mX => c mX ≠ 0)).image (bdlCheckXSlot k) ↔
            c (Classical.choose hex) ≠ 0 := by
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨mX, hmX_ne, h_slot⟩
          rw [bdlCheckXSlot_eq_pair] at h_slot
          have h_pair : bdlCheckXPair k mX = ix := Sum.inl.inj (Sum.inr.inj h_slot)
          have hm_eq : mX = Classical.choose hex := bdlCheckXPair_injective k (h_pair.trans hm₀.symm)
          rwa [← hm_eq]
        · intro hm₀_ne
          exact ⟨Classical.choose hex, hm₀_ne,
            (bdlCheckXSlot_eq_pair k (Classical.choose hex)).trans (congr_arg (Sum.inr ∘ Sum.inl) hm₀)⟩
      exact decide_eq_decide.mpr h_mem_iff
    · rw [dif_neg hex, decide_eq_false]
      rintro h
      rcases Finset.mem_image.mp h with ⟨mX, _, h_slot⟩
      rw [bdlCheckXSlot_eq_pair] at h_slot
      exact hex ⟨mX, Sum.inl.inj (Sum.inr.inj h_slot)⟩
  · dsimp only
    rw [decide_eq_false]
    · split_ifs <;> rfl
    · rintro h
      rcases Finset.mem_image.mp h with ⟨mX, _, h_slot⟩
      rw [bdlCheckXSlot_eq_pair] at h_slot
      cases h_slot

lemma decide_mem_bdlWitnessSetZ_eq_embedSynGen (k : ℕ) (c : BDLWeldedCheckZ k → ZMod 2) :
    (fun idx => decide (idx ∈ bdlWitnessSetZ k c)) =
      embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) (fun _ => false) 0 c := by
  ext idx
  unfold bdlWitnessSetZ embedSynGen embedCheckBits
  rcases idx with p | ix | iz
  · dsimp only
    rw [decide_eq_false]
    rintro h
    rcases Finset.mem_image.mp h with ⟨mZ, _, h_eq⟩
    rw [bdlCheckZSlot_eq_pair] at h_eq
    cases h_eq
  · dsimp only
    rw [decide_eq_false]
    · split_ifs <;> rfl
    · rintro h
      rcases Finset.mem_image.mp h with ⟨mZ, _, h_slot⟩
      rw [bdlCheckZSlot_eq_pair] at h_slot
      cases h_slot
  · dsimp only
    by_cases hex : ∃ mZ : BDLWeldedCheckZ k, bdlCheckZPair k mZ = iz
    · rw [dif_pos hex]
      have hm₀ : bdlCheckZPair k (Classical.choose hex) = iz := Classical.choose_spec hex
      have h_mem_iff :
          Sum.inr (Sum.inr iz) ∈ (Finset.univ.filter (fun mZ => c mZ ≠ 0)).image (bdlCheckZSlot k) ↔
            c (Classical.choose hex) ≠ 0 := by
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨mZ, hmZ_ne, h_slot⟩
          rw [bdlCheckZSlot_eq_pair] at h_slot
          have h_pair : bdlCheckZPair k mZ = iz := Sum.inr.inj (Sum.inr.inj h_slot)
          have hm_eq : mZ = Classical.choose hex := bdlCheckZPair_injective k (h_pair.trans hm₀.symm)
          rwa [← hm_eq]
        · intro hm₀_ne
          exact ⟨Classical.choose hex, hm₀_ne,
            (bdlCheckZSlot_eq_pair k (Classical.choose hex)).trans (congr_arg (Sum.inr ∘ Sum.inr) hm₀)⟩
      exact decide_eq_decide.mpr h_mem_iff
    · rw [dif_neg hex, decide_eq_false]
      rintro h
      rcases Finset.mem_image.mp h with ⟨mZ, _, h_slot⟩
      rw [bdlCheckZSlot_eq_pair] at h_slot
      exact hex ⟨mZ, Sum.inr.inj (Sum.inr.inj h_slot)⟩

/-- **Zero-Spillover Realizability of Grid-Snapped BDL Witness Family
    (`bdlWitnessFamily_mem_realizableSyndromes`, Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`))**:
    If every primal witness $c \in W_Z$ is the syndrome of a 1-chain $e_X$ on `bdlWeldedCode k`
    and every dual witness $c \in W_X$ is the syndrome of a 1-chain $e_Z$ on `dualCode (bdlWeldedCode k)`,
    then every grid-snapped witness $W \in \mathrm{bdlWitnessFamily}(k, W_Z, W_X)$ satisfies
    $(\text{fun }\mathrm{idx} \Rightarrow \mathrm{decide}(\mathrm{idx} \in W)) \in \mathrm{realizableSyndromes}(\mathrm{bdlLocalDescriptor}\;k)$. -/
theorem bdlWitnessFamily_mem_realizableSyndromes (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_real : ∀ c ∈ W_Z, ∃ e_X : BDLWeldedQubit k → ZMod 2, syndrome (bdlWeldedCode k) e_X = c)
    (hWX_real : ∀ c ∈ W_X, ∃ e_Z : BDLWeldedQubit k → ZMod 2, syndrome (dualCode (bdlWeldedCode k)) e_Z = c) :
    ∀ W ∈ bdlWitnessFamily k W_Z W_X,
      (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes (bdlLocalDescriptor k) := by
  have h_pin0 : IsValidPinSynGen (bdlLocalDescriptor k) (fun _ => false) := fun _ _ => rfl
  have h_synZ0 : syndrome (dualCode (bdlWeldedCode k)) 0 = 0 :=
    map_zero (syndrome (dualCode (bdlWeldedCode k)))
  have h_synX0 : syndrome (bdlWeldedCode k) 0 = 0 :=
    map_zero (syndrome (bdlWeldedCode k))
  intro W hW
  rw [realizableSyndromes, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases Finset.mem_union.mp hW with hZ | hX
  · rcases Finset.mem_image.mp hZ with ⟨c, hc, rfl⟩
    rcases hWZ_real c hc with ⟨e_X, rfl⟩
    rcases exists_staticCSSPauliFlip_of_isValidPinSyn k h_pin0 e_X 0 with ⟨a, b, hab⟩
    rw [h_synZ0] at hab
    exact ⟨a, b, (decide_mem_bdlWitnessSetX_eq_embedSynGen k (syndrome (bdlWeldedCode k) e_X)).trans hab.symm⟩
  · rcases Finset.mem_image.mp hX with ⟨c, hc, rfl⟩
    rcases hWX_real c hc with ⟨e_Z, rfl⟩
    rcases exists_staticCSSPauliFlip_of_isValidPinSyn k h_pin0 0 e_Z with ⟨a, b, hab⟩
    rw [h_synX0] at hab
    exact ⟨a, b, (decide_mem_bdlWitnessSetZ_eq_embedSynGen k (syndrome (dualCode (bdlWeldedCode k)) e_Z)).trans hab.symm⟩

/-- Macroscopic lower bound `c_F_BDL * (L_k^3)^eta_BDL ≤ clusterRawWeight k`. -/
theorem c_F_BDL_mul_vol_pow_eta_le_clusterRawWeight (k : ℕ) :
    cFBDL * (((bdlBoxSide k ^ 3 : ℕ) : ℝ) ^ etaBDL) ≤ (clusterRawWeight k : ℝ) := by
  have h_bar := bdlFreeEnergyBarrier_le_clusterRawWeight k
    (by linarith : betaCritBDL + 1 > betaCritBDL)
  dsimp [bdlFreeEnergyBarrier] at h_bar
  linarith

section HalfBetaCBound

private lemma beta_c_BDL_eq_def :
    betaCritBDL =
      1200 * (_root_.bdlSingleStepFactor : ℝ) +
        2 * ((mMaxBDL + qCodeBDL : ℕ) : ℝ) * ((4 * r0BDL + 1 : ℕ) ^ 3 : ℝ) + 100 := rfl

private lemma bdlSingleStepFactor_eq_root :
    WeldedHierarchy.bdlSingleStepFactor = _root_.bdlSingleStepFactor := rfl

private lemma bdlSingleStepFactor_ge_two_root : 2 ≤ _root_.bdlSingleStepFactor :=
  bdlSingleStepFactor_ge_two

private lemma bdlClusterStepBase_ge_two_root : 2 ≤ bdlClusterStepBase :=
  bdlClusterStepBase_ge_two

-- Prevent elaborator unfolding of concrete numerical constants
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  bdlClusterStepBase _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor
  betaCritBDL mMaxBDL qCodeBDL r0BDL bdlWeldedCode

/-- Strengthened critical inverse temperature bound:
    `Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) + 100 ≤ beta_c_BDL / 2`. -/
lemma log_bdlClusterStepBase_pow_eight_le_half_beta_c_BDL :
    Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) + 100 ≤ betaCritBDL / 2 := by
  have h2_nat : 2 ≤ bdlClusterStepBase ^ 8 :=
    le_trans bdlClusterStepBase_ge_two_root (Nat.le_self_pow (by decide : 8 ≠ 0) bdlClusterStepBase)
  have h2_real : (2 : ℝ) ≤ ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) := Nat.cast_le.mpr h2_nat
  have h_pos : (0 : ℝ) < ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) := by linarith
  have h_pow_nat : bdlClusterStepBase ^ 8 ≤ 2 ^ (336 * _root_.bdlSingleStepFactor) := by
    rw [← bdlSingleStepFactor_eq_root]
    exact bdlClusterStepBase_pow_eight_le_two_pow
  have h_le_pow : (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (336 * _root_.bdlSingleStepFactor) := by
    have h_c : ((bdlClusterStepBase ^ 8 : ℕ) : ℝ) ≤ ((2 ^ (336 * _root_.bdlSingleStepFactor) : ℕ) : ℝ) :=
      Nat.cast_le.mpr h_pow_nat
    rwa [Nat.cast_pow 2, Nat.cast_ofNat] at h_c
  have h_log_le : Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) ≤
      ((336 * _root_.bdlSingleStepFactor : ℕ) : ℝ) * Real.log 2 := by
    calc Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ))
      _ ≤ Real.log ((2 : ℝ) ^ (336 * _root_.bdlSingleStepFactor)) := Real.log_le_log h_pos h_le_pow
      _ = ((336 * _root_.bdlSingleStepFactor : ℕ) : ℝ) * Real.log 2 :=
        Real.log_pow 2 (336 * _root_.bdlSingleStepFactor)
  have h_log2_le_one : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h_N_nonneg : (0 : ℝ) ≤ ((336 * _root_.bdlSingleStepFactor : ℕ) : ℝ) := Nat.cast_nonneg _
  have h_log_le_N : Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ)) ≤
      336 * (_root_.bdlSingleStepFactor : ℝ) := by
    calc Real.log (((bdlClusterStepBase ^ 8 : ℕ) : ℝ))
      _ ≤ ((336 * _root_.bdlSingleStepFactor : ℕ) : ℝ) * Real.log 2 := h_log_le
      _ ≤ ((336 * _root_.bdlSingleStepFactor : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h_log2_le_one h_N_nonneg
      _ = 336 * (_root_.bdlSingleStepFactor : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat, mul_one]
  have h_extra_nonneg : (0 : ℝ) ≤
      2 * ((mMaxBDL + qCodeBDL : ℕ) : ℝ) * ((4 * r0BDL + 1 : ℕ) ^ 3 : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (pow_nonneg (Nat.cast_nonneg _) 3)
  have h_F_ge_two : (2 : ℝ) ≤ (_root_.bdlSingleStepFactor : ℝ) :=
    Nat.cast_le.mpr bdlSingleStepFactor_ge_two_root
  rw [beta_c_BDL_eq_def]
  linarith

private lemma sum_Icc_one_fourth_pow_le (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (1 / 4 : ℝ) ^ m) ≤ (1 / 2 : ℝ) * (1 - (1 / 4 : ℝ) ^ N) := by
  induction N with
  | zero =>
    have h_empty : Finset.Icc 1 0 = ∅ := rfl
    rw [h_empty, Finset.sum_empty, pow_zero, sub_self, mul_zero]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le n)), pow_succ]
    have h_pow_nn : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity
    linarith

private lemma sum_exp_neg_half_beta_syndromeWeight_le_half_of_base
    {M : Type} [Fintype M]
    (B_nat : ℕ) (β_c : ℝ)
    (hB_ge2_nat : 2 ≤ B_nat)
    (h_log_le : Real.log (B_nat : ℝ) + 100 ≤ β_c / 2)
    (W : Finset (M → ZMod 2))
    (hW_strat : ∀ m : ℕ,
      (W.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤ B_nat ^ m)
    (hW_wt1 : ∀ c ∈ W, (1 : ℝ) ≤ WeldedHierarchy.syndromeWeight c) :
    (∑ c ∈ W, Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c)) ≤ 1 / 2 := by
  let B : ℝ := (B_nat : ℝ)
  have hB_ge2 : (2 : ℝ) ≤ B := Nat.cast_le.mpr hB_ge2_nat
  have hB_pos : 0 < B := by linarith
  have h_exp_neg100 : Real.exp (-100 : ℝ) ≤ 1 / 4 := by
    have h100 : (4 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp 100]
    have h_prod : Real.exp (-100 : ℝ) * Real.exp 100 = 1 := by
      rw [← Real.exp_add]; norm_num
    have h_mul := mul_le_mul_of_nonneg_left h100 (Real.exp_pos (-100 : ℝ)).le
    linarith
  have h_q_le : B * Real.exp (-(β_c / 2)) ≤ 1 / 4 := by
    calc B * Real.exp (-(β_c / 2))
      _ = Real.exp (Real.log B) * Real.exp (-(β_c / 2)) := by rw [Real.exp_log hB_pos]
      _ = Real.exp (Real.log B + -(β_c / 2)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-100 : ℝ) := Real.exp_le_exp.mpr (by dsimp [B]; linarith)
      _ ≤ 1 / 4 := h_exp_neg100
  let wtNat (c : M → ZMod 2) : ℕ := (Finset.univ.filter (fun x => c x ≠ 0)).card
  have h_maps : ∀ c ∈ W, wtNat c ∈ Finset.Icc 1 (Fintype.card M) := by
    intro c hc
    have h1 : 1 ≤ wtNat c := by
      have h_real := hW_wt1 c hc
      dsimp [WeldedHierarchy.syndromeWeight] at h_real
      exact_mod_cast h_real
    have h2 : wtNat c ≤ Fintype.card M := Finset.card_filter_le _ _
    exact Finset.mem_Icc.mpr ⟨h1, h2⟩
  have h_fiber := (Finset.sum_fiberwise_of_maps_to h_maps
    (fun c => Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c))).symm
  have h_shell : ∀ m ∈ Finset.Icc 1 (Fintype.card M),
      (∑ c ∈ W.filter (fun c => wtNat c = m),
        Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c)) ≤ (1 / 4 : ℝ) ^ m := by
    intro m _
    have h_congr :
        (∑ c ∈ W.filter (fun c => wtNat c = m),
          Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c)) =
        ∑ _c ∈ W.filter (fun c => wtNat c = m),
          (Real.exp (-(β_c / 2))) ^ m := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hm : wtNat c = m := (Finset.mem_filter.mp hc).2
      have h_wt : WeldedHierarchy.syndromeWeight c = (m : ℝ) := congrArg Nat.cast hm
      rw [h_wt, ← Real.exp_nat_mul]
      congr 1; ring
    have h_card_real :
        ((W.filter (fun c => wtNat c = m)).card : ℝ) ≤ B ^ m := by
      have hc := Nat.cast_le (α := ℝ).mpr (hW_strat m)
      rwa [Nat.cast_pow] at hc
    rw [h_congr, Finset.sum_const, nsmul_eq_mul]
    calc ((W.filter (fun c => wtNat c = m)).card : ℝ) * (Real.exp (-(β_c / 2))) ^ m
      _ ≤ B ^ m * (Real.exp (-(β_c / 2))) ^ m :=
          mul_le_mul_of_nonneg_right h_card_real (by positivity)
      _ = (B * Real.exp (-(β_c / 2))) ^ m := (mul_pow _ _ _).symm
      _ ≤ (1 / 4 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) h_q_le m
  have h_geom := sum_Icc_one_fourth_pow_le (Fintype.card M)
  have h_pow_nn : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (Fintype.card M) := by positivity
  calc (∑ c ∈ W, Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c))
    _ = ∑ m ∈ Finset.Icc 1 (Fintype.card M),
          ∑ c ∈ W.filter (fun c => wtNat c = m),
            Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c) := h_fiber
    _ ≤ ∑ m ∈ Finset.Icc 1 (Fintype.card M), (1 / 4 : ℝ) ^ m := Finset.sum_le_sum h_shell
    _ ≤ 1 / 2 := by linarith

/-- Weight-stratified Klarner shell summation bound (Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
    if the number of witnesses `c ∈ W` of weight `m` is at most `(bdlClusterStepBase ^ 8) ^ m`
    and every `c ∈ W` has weight at least `1`, then
    `∑ c ∈ W, Real.exp (-(betaCritBDL / 2) * WeldedHierarchy.syndromeWeight c) ≤ 1 / 2`. -/
theorem sum_exp_neg_half_beta_c_BDL_syndromeWeight_le_half
    {M : Type} [Fintype M]
    (W : Finset (M → ZMod 2))
    (hW_strat : ∀ m : ℕ,
      (W.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
        (bdlClusterStepBase ^ 8) ^ m)
    (hW_wt1 : ∀ c ∈ W, (1 : ℝ) ≤ WeldedHierarchy.syndromeWeight c) :
    (∑ c ∈ W, Real.exp (-(betaCritBDL / 2) * WeldedHierarchy.syndromeWeight c)) ≤ 1 / 2 :=
  sum_exp_neg_half_beta_syndromeWeight_le_half_of_base
    (bdlClusterStepBase ^ 8) betaCritBDL
    (le_trans bdlClusterStepBase_ge_two_root (Nat.le_self_pow (by decide : 8 ≠ 0) bdlClusterStepBase))
    log_bdlClusterStepBase_pow_eight_le_half_beta_c_BDL
    W hW_strat hW_wt1

private lemma sum_union_le_one_of_sum_le_half {α : Type*} [DecidableEq α]
    (s₁ s₂ : Finset α) (f : α → ℝ) (hf_nn : ∀ x, 0 ≤ f x)
    (h1 : (∑ x ∈ s₁, f x) ≤ 1 / 2) (h2 : (∑ x ∈ s₂, f x) ≤ 1 / 2) :
    (∑ x ∈ s₁ ∪ s₂, f x) ≤ 1 := by
  have h_ui := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have h_inter : 0 ≤ ∑ x ∈ s₁ ∩ s₂, f x := Finset.sum_nonneg fun x _ => hf_nn x
  linarith

/-- Weighted-Kraft / Klarner animal sum bound for `bdlWitnessFamily k W_Z W_X`
    (Part II, Section 5.1 (`subsec:direct-worldline-synthesis`), Theorem 5.1 (`thm:direct-worldline-intact-cluster-erasure`)):
    `(∑ W ∈ bdlWitnessFamily k W_Z W_X, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1`. -/
theorem sum_exp_neg_half_beta_c_bdlWitnessFamily_le_one (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_strat : ∀ m : ℕ,
      (W_Z.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
        (bdlClusterStepBase ^ 8) ^ m)
    (hWZ_wt : ∀ c ∈ W_Z, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c)
    (hWX_strat : ∀ m : ℕ,
      (W_X.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
        (bdlClusterStepBase ^ 8) ^ m)
    (hWX_wt : ∀ c ∈ W_X, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c) :
    (∑ W ∈ bdlWitnessFamily k W_Z W_X, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1 := by
  have hw_ge1 : (1 : ℝ) ≤ ((clusterRawWeight k : ℕ) : ℝ) :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans (three_div_two_pow_le_clusterRawWeight k)
  have hZ_half := sum_exp_neg_half_beta_c_BDL_syndromeWeight_le_half W_Z hWZ_strat
    (fun c hc => hw_ge1.trans (hWZ_wt c hc))
  have hX_half := sum_exp_neg_half_beta_c_BDL_syndromeWeight_le_half W_X hWX_strat
    (fun c hc => hw_ge1.trans (hWX_wt c hc))
  have hZ_img :
      (∑ W ∈ W_Z.image (bdlWitnessSetX k), Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1 / 2 := by
    refine le_trans (Finset.sum_image_le_of_nonneg fun _ _ => (Real.exp_pos _).le) (le_trans ?_ hZ_half)
    refine le_of_eq (Finset.sum_congr rfl fun c _ => ?_)
    have h_card : ((bdlWitnessSetX k c).card : ℝ) = WeldedHierarchy.syndromeWeight c :=
      congrArg Nat.cast (Finset.card_image_of_injective _ (bdlCheckXSlot_injective k))
    exact congrArg (fun x => Real.exp (-(betaCritBDL / 2) * x)) h_card
  have hX_img :
      (∑ W ∈ W_X.image (bdlWitnessSetZ k), Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1 / 2 := by
    refine le_trans (Finset.sum_image_le_of_nonneg fun _ _ => (Real.exp_pos _).le) (le_trans ?_ hX_half)
    refine le_of_eq (Finset.sum_congr rfl fun c _ => ?_)
    have h_card : ((bdlWitnessSetZ k c).card : ℝ) = WeldedHierarchy.syndromeWeight c :=
      congrArg Nat.cast (Finset.card_image_of_injective _ (bdlCheckZSlot_injective k))
    exact congrArg (fun x => Real.exp (-(betaCritBDL / 2) * x)) h_card
  exact sum_union_le_one_of_sum_le_half
    (W_Z.image (bdlWitnessSetX k)) (W_X.image (bdlWitnessSetZ k))
    (fun W => Real.exp (-(betaCritBDL / 2) * (W.card : ℝ)))
    (fun _ => (Real.exp_pos _).le) hZ_img hX_img

private lemma sum_exp_neg_beta_syndromeWeight_le_half_barrier_of_half
    {M : Type} [Fintype M]
    (β β_c w_raw ΔF : ℝ)
    (hβc_pos : 0 < β_c) (hw_ge1 : 1 ≤ w_raw) (hβ : β > β_c)
    (h_bar : ΔF ≤ (β - β_c) * w_raw)
    (W : Finset (M → ZMod 2))
    (h_half : (∑ c ∈ W, Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c)) ≤ 1 / 2)
    (h_wt : ∀ c ∈ W, w_raw ≤ WeldedHierarchy.syndromeWeight c) :
    (∑ c ∈ W, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤ Real.exp (-ΔF) / 2 := by
  have h_term : ∀ c ∈ W,
      Real.exp (-β * WeldedHierarchy.syndromeWeight c) ≤
        Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c) * Real.exp (-ΔF) := by
    intro c hc
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcw := h_wt c hc
    have h_diff_pos : 0 ≤ β - β_c / 2 := by linarith
    have h_mul := mul_le_mul_of_nonneg_left hcw h_diff_pos
    have h_bar2 : ΔF ≤ (β - β_c / 2) * w_raw := by nlinarith
    linarith
  calc (∑ c ∈ W, Real.exp (-β * WeldedHierarchy.syndromeWeight c))
    _ ≤ ∑ c ∈ W, Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c) * Real.exp (-ΔF) :=
          Finset.sum_le_sum h_term
    _ = (∑ c ∈ W, Real.exp (-(β_c / 2) * WeldedHierarchy.syndromeWeight c)) * Real.exp (-ΔF) :=
          (Finset.sum_mul _ _ _).symm
    _ ≤ (1 / 2) * Real.exp (-ΔF) :=
          mul_le_mul_of_nonneg_right h_half (Real.exp_pos _).le
    _ = Real.exp (-ΔF) / 2 := by ring

/-- Weight-stratified unperturbed Peierls bound for `bdlSafeSyndromeSet k W_Z W_X`. -/
theorem gibbsFailureProb_bdlSafeSyndromeSet_le_of_stratified (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_strat : ∀ m : ℕ,
      (W_Z.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
        (bdlClusterStepBase ^ 8) ^ m)
    (hWZ_wt : ∀ c ∈ W_Z, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c)
    (hWX_strat : ∀ m : ℕ,
      (W_X.filter (fun c => (Finset.univ.filter (fun x => c x ≠ 0)).card = m)).card ≤
        (bdlClusterStepBase ^ 8) ^ m)
    (hWX_wt : ∀ c ∈ W_X, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c)
    (β : ℝ) (hβ : β > betaCritBDL) :
    gibbsFailureProb (bdlInhomogeneousSystem k).H0 (bdlInhomogeneousSystem k).isSelfAdjoint_H0 β
      (1 - syndromeSubsetProj (bdlInhomogeneousSystem k) (bdlSafeSyndromeSet k W_Z W_X)) ≤
      Real.exp (- bdlFreeEnergyBarrier k β) :=
  let hw_ge1 : (1 : ℝ) ≤ ((clusterRawWeight k : ℕ) : ℝ) :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans (three_div_two_pow_le_clusterRawWeight k)
  gibbsFailureProb_bdlSafeSyndromeSet_le_of_sums k W_Z W_X β hβ
    (sum_exp_neg_beta_syndromeWeight_le_half_barrier_of_half
      β betaCritBDL (clusterRawWeight k : ℝ) (bdlFreeEnergyBarrier k β)
      beta_crit_bdl_pos hw_ge1 hβ (bdlFreeEnergyBarrier_le_clusterRawWeight k hβ) W_Z
      (sum_exp_neg_half_beta_c_BDL_syndromeWeight_le_half W_Z hWZ_strat (fun c hc => hw_ge1.trans (hWZ_wt c hc)))
      hWZ_wt)
    (sum_exp_neg_beta_syndromeWeight_le_half_barrier_of_half
      β betaCritBDL (clusterRawWeight k : ℝ) (bdlFreeEnergyBarrier k β)
      beta_crit_bdl_pos hw_ge1 hβ (bdlFreeEnergyBarrier_le_clusterRawWeight k hβ) W_X
      (sum_exp_neg_half_beta_c_BDL_syndromeWeight_le_half W_X hWX_strat (fun c hc => hw_ge1.trans (hWX_wt c hc)))
      hWX_wt)

end HalfBetaCBound

private lemma sum_filter_univ_eq_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Prop) {inst : DecidablePred P} (γ : α) (hP : ∀ γ', P γ' ↔ γ' = γ) (f : α → ℝ) :
    (∑ γ' ∈ Finset.univ.filter P, f γ') = f γ := by
  have h_eq : Finset.univ.filter P = {γ} := by
    ext γ'; simp [hP γ']
  rw [h_eq, Finset.sum_singleton]

private lemma exp_neg_mul_mul_exp (x : ℝ) :
    (Real.exp (-x) * x) * Real.exp x = x := by
  calc (Real.exp (-x) * x) * Real.exp x
    _ = (Real.exp (-x) * Real.exp x) * x := by ring
    _ = Real.exp (-x + x) * x := by rw [← Real.exp_add]
    _ = x := by simp

/-- Nonnegativity of `gibbsFailureProb H hH β (positiveCheckWitnessProj sys γ)`. -/
theorem gibbsFailureProb_positiveCheckWitnessProj_nonneg {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)]
    [∀ x, Nonempty (Site x)]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (sys : IndexedCommutingProjectorHamiltonian D L Site ι)
    (H : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site)
    (hH : IsSelfAdjoint H) (β : ℝ) (γ : Finset ι) :
    0 ≤ gibbsFailureProb H hH β (positiveCheckWitnessProj sys γ) :=
  KMSPinchedGibbs.hilbertTrace_gibbsDensityOp_mul_proj_nonneg
    (opEigenbasis H hH) (opEigenvalues H hH) β
    (opEigenbasis_orthonormal H hH)
    (hilbertTrace_eq_sum_opEigenbasis H hH)
    (isStarProjection_positiveCheckWitnessProj sys γ).1

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

private lemma bdlInhomogeneousSystem_checks (k : ℕ)
    (idx : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :
    (bdlInhomogeneousSystem k).checkProj idx = staticCSSCheckProj (bdlLocalDescriptor k) idx ∧
    (bdlInhomogeneousSystem k).support idx = staticCSSCheckSupport (bdlLocalDescriptor k) idx ∧
    (bdlInhomogeneousSystem k).weight idx = 1 := ⟨rfl, rfl, rfl⟩

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
  betaCritBDL _root_.bdlSingleStepFactor WeldedHierarchy.bdlSingleStepFactor
  collarConstRCABDL bdlLambda bBDL bdlHierarchySteps qCodeBDL r0BDL mMaxBDL
  IndexedCommutingProjectorHamiltonian.H0 IndexedCommutingProjectorHamiltonian.groundProj
  IndexedCommutingProjectorHamiltonian.localGroundProj
  IndexedCommutingProjectorHamiltonian.groundSpace IndexedCommutingProjectorHamiltonian.groundDegeneracy
  IndexedCommutingProjectorHamiltonian.syndromeProjector QuasiLocalPerturbation.totalPerturbation
  gibbsFailureProb opKMSNormSq SatisfiesKMSLindbladODE heisenbergFlow condExp IsSupportedOn
  syndromeSignOp syndromeSubsetProj bdlSafeSyndromeSet bdlWeldedCode bdlLocalDescriptor
  weylPauliZ weylPauliX bdlPushChain
  bdlBoxSide HasSafeDecodedLogicalObservables SatisfiesUnperturbedThermalAndKMSStability
  SatisfiesZeroTempPerturbativeMemoryStability IndexedCommutingProjectorHamiltonian.IsGeometricallyLocal
  IndexedCommutingProjectorHamiltonian.reindex bdlInhomogeneousSystem
  reindexHamiltonian reindexPerturbation conjSiteOp clusterRawWeight bdlClusterStepBase
  bdlWitnessFamily

local notation "ℋ[" L ", " Site0 "]" => ManyBodyHilbertSpace (UniformSite3D L Site0)
local notation "ℬ[" L ", " Site0 "]" => ℋ[L, Site0] →L[ℂ] ℋ[L, Site0]

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

/-- Explicit level-`k` BDL realization package on `CodeSlotConfig qCodeBDL` bundling
    `Inhomogeneous3DMemoryRealization`, the macroscopic `bdlLambda ^ k` safe-subspace immunity,
    `HasSafeDecodedLogicalObservables`, `syndromeSubsetProj` representation of `Pi_safe`,
    and the concrete positive check-witness cover `W_family` with weight and entropy bounds. -/
theorem bdl_inhomogeneous_codeSlot_memory_package_with_witness_cover (k : ℕ) {N_c : ℕ}
    (e_chk : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL ≃ Fin N_c) :
    ∃ (mem : Inhomogeneous3DMemoryRealization (bdlBoxSide k) qCodeBDL r0BDL mMaxBDL
        cStarBDL (collarConstRCABDL : ℝ) betaCritBDL cFBDL etaBDL cMemBDL)
      (S_safe : Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool))
      (W_family : Finset (Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL))),
      mem.sys = bdlInhomogeneousSystem k ∧
      mem.Pi_safe = syndromeSubsetProj mem.sys S_safe ∧
      mem.D_field = bdlLocalDescriptor k ∧
      (∀ (W : QuasiLocalPerturbation 3 (bdlBoxSide k)
          (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL))),
        ∀ r ∈ Finset.Icc 1 (bdlLambda ^ k), ∀ A ∈ boxCubes 3 (bdlBoxSide k) r,
          mem.Pi_safe * (W.term r A * mem.O_dec_Z - mem.O_dec_Z * W.term r A) * mem.Pi_safe = 0 ∧
          mem.Pi_safe * (W.term r A * mem.O_dec_X - mem.O_dec_X * W.term r A) * mem.Pi_safe = 0) ∧
      HasSafeDecodedLogicalObservables (N_checks := N_c)
        (mem.sys.reindex e_chk) mem.Pi_safe mem.O_dec_Z mem.O_dec_X (37 * bdlLambda ^ k) ∧
      IsPositiveCheckWitnessCover S_safe W_family ∧
      (∀ W ∈ W_family, (fun idx => decide (idx ∈ W)) ∈ realizableSyndromes mem.D_field) ∧
      (∀ W ∈ W_family, clusterRawWeight k ≤ W.card) ∧
      ((∑ W ∈ W_family, Real.exp (-(betaCritBDL / 2) * (W.card : ℝ))) ≤ 1) := by
  obtain ⟨⟨ψ_Z, W_Z, hψZ0, hWZ_strat, hWZ_wt, hWZ_real, hWZ_fail⟩,
          ⟨ψ_X, W_X, hψX0, hWX_strat, hWX_wt, hWX_real, hWX_fail⟩⟩ :=
    hasZeroSpilloverBallParityWitnessFamily_bdlWelded_lambdaPow k
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
  obtain ⟨mem, h_sys_eq, h_Pi_eq, h_D_eq, h_fw_macro, h_obs⟩ := codeSlot_memory_package_of_components
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
    (fun β hβ => gibbsFailureProb_bdlSafeSyndromeSet_le_of_stratified k W_Z W_X
      hWZ_strat hWZ_wt hWX_strat hWX_wt β hβ)
  exact ⟨mem, bdlSafeSyndromeSet k W_Z W_X, bdlWitnessFamily k W_Z W_X,
    h_sys_eq, h_Pi_eq, h_D_eq, h_fw_macro, h_obs,
    isPositiveCheckWitnessCover_bdlSafeSyndromeSet k W_Z W_X,
    h_D_eq ▸ bdlWitnessFamily_mem_realizableSyndromes k W_Z W_X hWZ_real hWX_real,
    card_floor_bdlWitnessFamily k W_Z W_X hWZ_wt hWX_wt,
    sum_exp_neg_half_beta_c_bdlWitnessFamily_le_one k W_Z W_X hWZ_strat hWZ_wt hWX_strat hWX_wt⟩

end FixedTempPerturbativeGibbsSynthesis

end
