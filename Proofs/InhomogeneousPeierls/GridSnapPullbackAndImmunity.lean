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

import Proofs.InhomogeneousPeierls.SyndromeSignAndPauliFlips

/-!
# Grid-Snapped Syndrome Pullbacks and Single-Site Safe-Subspace Commutator Immunity

Constructs injective slot embeddings (`bdlCheckXSlot`, `bdlCheckZSlot`), syndrome pullbacks (`bdlPullSynX`, `bdlPullSynZ`), and the witness-free safe syndrome set `bdlSafeSyndromeSet` determined by `IsSafeBDLSyndrome`. Proves `bdlSafeSyndromeSet_singleSite_immunity`, showing that every single-site operator on the 3D cubic lattice has vanishing safe-subspace-sandwiched commutator with the decoded logical observables.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part II, Section 2 (`subsec:setup`), Definition 2.5 (`def:syndrome-safe`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-! ## 1. Grid-Snap Check Embeddings, Chain/Syndrome Pullbacks & Radius-$2$ Ball Containment -/

private lemma fiber_localRank_lt_card_bdl {X V : Type*} [Fintype X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (x : X) :
    ((Finset.univ.filter (fun x' : X => f x' = f x)).filter (fun x' => idx x' < idx x)).card <
      (Finset.univ.filter (fun x' : X => f x' = f x)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.filter_subset _ _, fun h_eq => ?_⟩
  have hx : x ∈ Finset.univ.filter (fun x' : X => f x' = f x) := by simp
  rw [← h_eq, Finset.mem_filter] at hx
  exact Nat.lt_irrefl _ hx.2

private lemma fiber_localRank_injective_bdl {X V : Type*} [Fintype X] [DecidableEq V]
    (f : X → V) (idx : X → ℕ) (h_inj : Function.Injective idx) :
    Function.Injective (fun x : X =>
      (f x, ((Finset.univ.filter (fun x' : X => f x' = f x)).filter
        (fun x' => idx x' < idx x)).card)) := by
  intro x₁ x₂ h
  have hf : f x₁ = f x₂ := (Prod.ext_iff.mp h).1
  have hr := (Prod.ext_iff.mp h).2
  have h_lt : ∀ a b : X, f a = f b → idx a < idx b →
      ((Finset.univ.filter (fun x' : X => f x' = f a)).filter (fun x' => idx x' < idx a)).card <
      ((Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b)).card := by
    intro a b hab hlt; rw [hab]; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun y hy => ?_, fun h_eq => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨hy.1, Nat.lt_trans hy.2 hlt⟩
    · have ha : a ∈ (Finset.univ.filter (fun x' : X => f x' = f b)).filter (fun x' => idx x' < idx b) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, hlt⟩
      rw [← h_eq, Finset.mem_filter] at ha; exact Nat.lt_irrefl _ ha.2
  rcases lt_trichotomy (idx x₁) (idx x₂) with h1 | heq | h2
  · exact False.elim (ne_of_lt (h_lt x₁ x₂ hf h1) hr)
  · exact h_inj heq
  · exact False.elim (ne_of_gt (h_lt x₂ x₁ hf.symm h2) hr)

lemma bdlCheckXLocalRank_lt_card (k : ℕ) (mX : BDLWeldedCheckX k) :
    bdlCheckXLocalRank k mX < (bdlCheckXFiber k (bdlGridVertexX k mX)).card :=
  fiber_localRank_lt_card_bdl (bdlGridVertexX k) (bdlCellIndexX k) mX

lemma bdlCheckXLocalRank_lt_m_max (k : ℕ) (mX : BDLWeldedCheckX k) :
    bdlCheckXLocalRank k mX < mMaxBDL :=
  (bdlCheckXLocalRank_lt_card k mX).trans_le (bdlFiber_card_bounds k (bdlGridVertexX k mX)).2.1

lemma bdlCheckZLocalRank_lt_card (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    bdlCheckZLocalRank k mZ < (bdlCheckZFiber k (bdlGridVertexZ k mZ)).card :=
  fiber_localRank_lt_card_bdl (bdlGridVertexZ k) (bdlCellIndexZ k) mZ

lemma bdlCheckZLocalRank_lt_m_max (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    bdlCheckZLocalRank k mZ < mMaxBDL :=
  (bdlCheckZLocalRank_lt_card k mZ).trans_le (bdlFiber_card_bounds k (bdlGridVertexZ k mZ)).2.2

def bdlCheckXSlot (k : ℕ) (mX : BDLWeldedCheckX k) :
    StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL :=
  Sum.inr (Sum.inl (bdlGridVertexX k mX,
    ⟨bdlCheckXLocalRank k mX, bdlCheckXLocalRank_lt_m_max k mX⟩))

def bdlCheckZSlot (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL :=
  Sum.inr (Sum.inr (bdlGridVertexZ k mZ,
    ⟨bdlCheckZLocalRank k mZ, bdlCheckZLocalRank_lt_m_max k mZ⟩))

lemma bdlCheckXSlot_injective (k : ℕ) : Function.Injective (bdlCheckXSlot k) := by
  intro m₁ m₂ h
  have h_prod : (bdlGridVertexX k m₁, (⟨bdlCheckXLocalRank k m₁, bdlCheckXLocalRank_lt_m_max k m₁⟩ : Fin mMaxBDL)) =
      (bdlGridVertexX k m₂, ⟨bdlCheckXLocalRank k m₂, bdlCheckXLocalRank_lt_m_max k m₂⟩) :=
    Sum.inl.inj (Sum.inr.inj h)
  have h_inj : Function.Injective (bdlCellIndexX k) :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  exact fiber_localRank_injective_bdl (bdlGridVertexX k) (bdlCellIndexX k) h_inj
    (Prod.ext (Prod.ext_iff.mp h_prod).1 (congr_arg Fin.val (Prod.ext_iff.mp h_prod).2))

lemma bdlCheckZSlot_injective (k : ℕ) : Function.Injective (bdlCheckZSlot k) := by
  intro m₁ m₂ h
  have h_prod : (bdlGridVertexZ k m₁, (⟨bdlCheckZLocalRank k m₁, bdlCheckZLocalRank_lt_m_max k m₁⟩ : Fin mMaxBDL)) =
      (bdlGridVertexZ k m₂, ⟨bdlCheckZLocalRank k m₂, bdlCheckZLocalRank_lt_m_max k m₂⟩) :=
    Sum.inr.inj (Sum.inr.inj h)
  have h_inj : Function.Injective (bdlCellIndexZ k) :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  exact fiber_localRank_injective_bdl (bdlGridVertexZ k) (bdlCellIndexZ k) h_inj
    (Prod.ext (Prod.ext_iff.mp h_prod).1 (congr_arg Fin.val (Prod.ext_iff.mp h_prod).2))

private lemma descriptorCheckXChain_eq_zero_of_not_mem_image_bdl (k : ℕ)
    (vX : Box3D (bdlBoxSide k)) (idxX : Fin mMaxBDL)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL)
    (hp : p ∉ Finset.univ.image (bdlQubitSiteSlot k)) :
    descriptorCheckXChain (bdlLocalDescriptor k) vX idxX p = 0 := by
  rcases p with ⟨w, s⟩
  dsimp [descriptorCheckXChain]
  rw [if_neg]
  rintro ⟨_, nb, _, h_sh, h_mask⟩
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
  rw [Bool.and_eq_true] at h_mask
  rcases decide_eq_true_iff.mp h_mask.2 with ⟨_, q, _, _, hq, _⟩
  apply hp
  rw [Finset.mem_image]
  exact ⟨q, Finset.mem_univ q, by simpa [bdlQubitSiteSlot, h_sh] using hq⟩

private lemma descriptorCheckZChain_eq_zero_of_not_mem_image_bdl (k : ℕ)
    (vZ : Box3D (bdlBoxSide k)) (idxZ : Fin mMaxBDL)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL)
    (hp : p ∉ Finset.univ.image (bdlQubitSiteSlot k)) :
    descriptorCheckZChain (bdlLocalDescriptor k) vZ idxZ p = 0 := by
  rcases p with ⟨w, s⟩
  dsimp [descriptorCheckZChain]
  rw [if_neg]
  rintro ⟨_, nb, _, h_sh, h_mask⟩
  dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement] at h_mask
  rw [Bool.and_eq_true] at h_mask
  rcases decide_eq_true_iff.mp h_mask.2 with ⟨_, q, _, _, hq, _⟩
  apply hp
  rw [Finset.mem_image]
  exact ⟨q, Finset.mem_univ q, by simpa [bdlQubitSiteSlot, h_sh] using hq⟩

def bdlPullChain (k : ℕ) (a : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    BDLWeldedQubit k → ZMod 2 :=
  fun q => a (bdlQubitSiteSlot k q)

@[simp] lemma bdlPullChain_bdlPushChain (k : ℕ) (c : BDLWeldedQubit k → ZMod 2) :
    bdlPullChain k (bdlPushChain k c) = c := by
  ext q
  exact bdlPushChain_apply_bdlQubitSiteSlot k c q

@[simp] lemma bdlPullChain_zero (k : ℕ) : bdlPullChain k 0 = 0 := rfl

lemma bdlPullChain_add (k : ℕ) (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    bdlPullChain k (a + b) = bdlPullChain k a + bdlPullChain k b := rfl

lemma sum_mul_bdlPushChain_eq_dualPairing_bdlPullChain (k : ℕ)
    (a : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2)
    (c : BDLWeldedQubit k → ZMod 2) :
    (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL, a p * bdlPushChain k c p) =
      dualPairing c (bdlPullChain k a) := by
  rw [sum_mul_bdlPushChain_eq]
  dsimp [dualPairing, bdlPullChain]
  refine Finset.sum_congr rfl fun q _ => mul_comm _ _

lemma sum_bdlPushChain_mul_eq_dualPairing_bdlPullChain (k : ℕ)
    (c : BDLWeldedQubit k → ZMod 2)
    (b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL, bdlPushChain k c p * b p) =
      dualPairing c (bdlPullChain k b) := by
  rw [sum_bdlPushChain_mul_eq]
  rfl

def bdlPullSynX (k : ℕ)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :
    BDLWeldedCheckX k → ZMod 2 :=
  fun mX => boolToZMod2 (σ (bdlCheckXSlot k mX))

def bdlPullSynZ (k : ℕ)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :
    BDLWeldedCheckZ k → ZMod 2 :=
  fun mZ => boolToZMod2 (σ (bdlCheckZSlot k mZ))

@[simp] lemma bdlPullSynX_zero (k : ℕ) : bdlPullSynX k (fun _ => false) = 0 := rfl
@[simp] lemma bdlPullSynZ_zero (k : ℕ) : bdlPullSynZ k (fun _ => false) = 0 := rfl

lemma bdlPullSynX_staticCSSPauliFlip (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    bdlPullSynX k (staticCSSPauliFlip (bdlLocalDescriptor k) a b) =
      syndrome (bdlWeldedCode k) (bdlPullChain k a) := by
  ext mX
  dsimp [bdlPullSynX, bdlCheckXSlot, staticCSSPauliFlip]
  have h_lt : bdlCheckXLocalRank k mX <
      ((bdlLocalDescriptor k (bdlGridVertexX k mX)).numXChecks).val := by
    rw [numXChecks_val_eq_card_fiber]
    exact bdlCheckXLocalRank_lt_card k mX
  rw [decide_eq_true h_lt, Bool.true_and]
  have h_sum : (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL,
      a p * descriptorCheckXChain (bdlLocalDescriptor k) (bdlGridVertexX k mX)
        ⟨bdlCheckXLocalRank k mX, bdlCheckXLocalRank_lt_m_max k mX⟩ p) =
      syndrome (bdlWeldedCode k) (bdlPullChain k a) mX := by
    have h_chain : descriptorCheckXChain (bdlLocalDescriptor k) (bdlGridVertexX k mX)
        ⟨bdlCheckXLocalRank k mX, bdlCheckXLocalRank_lt_m_max k mX⟩ =
        bdlPushChain k ((bdlWeldedCode k).checkX mX) := by
      ext p
      by_cases hp : p ∈ Finset.univ.image (bdlQubitSiteSlot k)
      · rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
        rw [descriptorCheckXChain_bdlQubitSiteSlot_eq k mX _ rfl,
          bdlPushChain_apply_bdlQubitSiteSlot]
      · rw [bdlPushChain_eq_zero_of_not_mem_image k _ p hp]
        exact descriptorCheckXChain_eq_zero_of_not_mem_image_bdl k _ _ p hp
    rw [h_chain, sum_mul_bdlPushChain_eq]
    dsimp [syndrome, f2Syndrome, bdlPullChain]
    refine Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [h_sum]
  rcases _root_.zmod2_eq_zero_or_one (syndrome (bdlWeldedCode k) (bdlPullChain k a) mX) with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

lemma bdlPullSynZ_staticCSSPauliFlip (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    bdlPullSynZ k (staticCSSPauliFlip (bdlLocalDescriptor k) a b) =
      syndrome (dualCode (bdlWeldedCode k)) (bdlPullChain k b) := by
  ext mZ
  dsimp [bdlPullSynZ, bdlCheckZSlot, staticCSSPauliFlip]
  have h_lt : bdlCheckZLocalRank k mZ <
      ((bdlLocalDescriptor k (bdlGridVertexZ k mZ)).numZChecks).val := by
    rw [numZChecks_val_eq_card_fiber]
    exact bdlCheckZLocalRank_lt_card k mZ
  rw [decide_eq_true h_lt, Bool.true_and]
  have h_sum : (∑ p : BoxSlot3D (bdlBoxSide k) qCodeBDL,
      descriptorCheckZChain (bdlLocalDescriptor k) (bdlGridVertexZ k mZ)
        ⟨bdlCheckZLocalRank k mZ, bdlCheckZLocalRank_lt_m_max k mZ⟩ p * b p) =
      syndrome (dualCode (bdlWeldedCode k)) (bdlPullChain k b) mZ := by
    have h_chain : descriptorCheckZChain (bdlLocalDescriptor k) (bdlGridVertexZ k mZ)
        ⟨bdlCheckZLocalRank k mZ, bdlCheckZLocalRank_lt_m_max k mZ⟩ =
        bdlPushChain k ((bdlWeldedCode k).checkZ mZ) := by
      ext p
      by_cases hp : p ∈ Finset.univ.image (bdlQubitSiteSlot k)
      · rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
        rw [descriptorCheckZChain_bdlQubitSiteSlot_eq k mZ _ rfl,
          bdlPushChain_apply_bdlQubitSiteSlot]
      · rw [bdlPushChain_eq_zero_of_not_mem_image k _ p hp]
        exact descriptorCheckZChain_eq_zero_of_not_mem_image_bdl k _ _ p hp
    rw [h_chain, sum_bdlPushChain_mul_eq]
    rfl
  rw [h_sum]
  rcases _root_.zmod2_eq_zero_or_one (syndrome (dualCode (bdlWeldedCode k)) (bdlPullChain k b) mZ) with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

lemma bdlPullSynX_xor_staticCSSPauliFlip (k : ℕ)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    bdlPullSynX k (fun i => xor (σ i) (staticCSSPauliFlip (bdlLocalDescriptor k) a b i)) =
      bdlPullSynX k σ + syndrome (bdlWeldedCode k) (bdlPullChain k a) := by
  rw [← bdlPullSynX_staticCSSPauliFlip k a b]
  ext mX
  dsimp [bdlPullSynX]
  exact boolToZMod2_xor _ _

lemma bdlPullSynZ_xor_staticCSSPauliFlip (k : ℕ)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    bdlPullSynZ k (fun i => xor (σ i) (staticCSSPauliFlip (bdlLocalDescriptor k) a b i)) =
      bdlPullSynZ k σ + syndrome (dualCode (bdlWeldedCode k)) (bdlPullChain k b) := by
  rw [← bdlPullSynZ_staticCSSPauliFlip k a b]
  ext mZ
  dsimp [bdlPullSynZ]
  exact boolToZMod2_xor _ _

def bdlGridCenter (k : ℕ) (v : Box3D (bdlBoxSide k)) : Point3D :=
  fun μ => ((v μ).val : ℝ) - (bdlBoxSide k : ℝ) / 2 + 1 / 2

lemma posQ_mem_ball3D_two_of_bdlGridVertexQ_eq (k : ℕ)
    (v : Box3D (bdlBoxSide k)) (q : BDLWeldedQubit k)
    (hq : bdlGridVertexQ k q = v) :
    (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v) 2 := by
  subst hq
  have hL := bdlCoordBound_add_1000_le_half_L k
  have hp := (hasBounded3DCoords_bdlWeldedBundled k).1 q
  have h0 := (snapPointToOpenBox_bounds hL hp 0).2
  have h1 := (snapPointToOpenBox_bounds hL hp 1).2
  have h2 := (snapPointToOpenBox_bounds hL hp 2).2
  dsimp [ball3D, distSq3D, bdlGridCenter, bdlGridVertexQ, bdlWeldedCode] at *
  have hsq0 : ((bdlWeldedBundled k).code.posQ q 0 -
      (((snapPointToOpenBox (bdlBoxSide k) ((bdlWeldedBundled k).code.posQ q) 0).val : ℝ) -
        (bdlBoxSide k : ℝ) / 2 + 1 / 2)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hsq1 : ((bdlWeldedBundled k).code.posQ q 1 -
      (((snapPointToOpenBox (bdlBoxSide k) ((bdlWeldedBundled k).code.posQ q) 1).val : ℝ) -
        (bdlBoxSide k : ℝ) / 2 + 1 / 2)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hsq2 : ((bdlWeldedBundled k).code.posQ q 2 -
      (((snapPointToOpenBox (bdlBoxSide k) ((bdlWeldedBundled k).code.posQ q) 2).val : ℝ) -
        (bdlBoxSide k : ℝ) / 2 + 1 / 2)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  nlinarith

/-! ## 2. Safe Syndrome Projector `Pi_safe`, Non-Vacuity `Pi_safe ≠ 1` & Single-Site Safe-Subspace Immunity -/

def IsSafeBDLSyndrome (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) : Prop :=
  (∀ c ∈ W_Z, ¬ (∀ mX : BDLWeldedCheckX k, c mX ≠ 0 → bdlPullSynX k σ mX ≠ 0)) ∧
  (∀ c ∈ W_X, ¬ (∀ mZ : BDLWeldedCheckZ k, c mZ ≠ 0 → bdlPullSynZ k σ mZ ≠ 0))

def bdlSafeSyndromeSet (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2)) :
    Finset (StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :=
  Finset.univ.filter (IsSafeBDLSyndrome k W_Z W_X)

lemma false_mem_bdlSafeSyndromeSet (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ : ∀ c ∈ W_Z, (1 : ℝ) ≤ WeldedHierarchy.syndromeWeight c)
    (hWX : ∀ c ∈ W_X, (1 : ℝ) ≤ WeldedHierarchy.syndromeWeight c) :
    (fun _ => false) ∈ bdlSafeSyndromeSet k W_Z W_X := by
  rw [bdlSafeSyndromeSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ⟨fun c hc h_sub => ?_, fun c hc h_sub => ?_⟩⟩
  · have h_wt_r := hWZ c hc
    dsimp [WeldedHierarchy.syndromeWeight] at h_wt_r
    have h_wt : 1 ≤ (Finset.univ.filter (fun mX => c mX ≠ 0)).card := by
      exact_mod_cast h_wt_r
    have h_pos : 0 < (Finset.univ.filter (fun mX => c mX ≠ 0)).card :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one h_wt
    obtain ⟨mX, hmX⟩ := Finset.card_pos.mp h_pos
    exact h_sub mX (Finset.mem_filter.mp hmX).2 rfl
  · have h_wt_r := hWX c hc
    dsimp [WeldedHierarchy.syndromeWeight] at h_wt_r
    have h_wt : 1 ≤ (Finset.univ.filter (fun mZ => c mZ ≠ 0)).card := by
      exact_mod_cast h_wt_r
    have h_pos : 0 < (Finset.univ.filter (fun mZ => c mZ ≠ 0)).card :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one h_wt
    obtain ⟨mZ, hmZ⟩ := Finset.card_pos.mp h_pos
    exact h_sub mZ (Finset.mem_filter.mp hmZ).2 rfl

private lemma exists_step_of_ne_zero_on_finset {Q : Type*} [DecidableEq Q]
    (f : (Q → ZMod 2) → ZMod 2) (S : Finset Q) (e : Q → ZMod 2)
    (h_supp : ∀ q ∉ S, e q = 0) (hne : f e ≠ f 0) :
    ∃ (e₁ e₂ : Q → ZMod 2) (q₀ : Q),
      (∀ q : Q, e₁ q ≠ e₂ q → q = q₀) ∧ f e₂ ≠ f e₁ := by
  induction S using Finset.induction_on generalizing e with
  | empty =>
    have he0 : e = 0 := funext (fun q => h_supp q (by simp))
    subst he0
    exact False.elim (hne rfl)
  | @insert q₀ S hq₀ ih =>
    let e' : Q → ZMod 2 := fun q => if q = q₀ then 0 else e q
    by_cases h_step : f e ≠ f e'
    · refine ⟨e', e, q₀, fun q hq => ?_, h_step⟩
      by_contra hne_q
      apply hq
      dsimp [e']
      rw [if_neg hne_q]
    · push_neg at h_step
      apply ih e'
      · intro q hqS
        dsimp [e']
        by_cases hqq₀ : q = q₀
        · rw [if_pos hqq₀]
        · rw [if_neg hqq₀]
          apply h_supp q
          intro h_mem
          rcases Finset.mem_insert.mp h_mem with rfl | h_in
          · exact hqq₀ rfl
          · exact hqS h_in
      · rw [← h_step]
        exact hne

private lemma exists_witness_of_ballParityWitness {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (ψ_Z : (M_X → ZMod 2) → ZMod 2) (W_Z : Finset (M_X → ZMod 2))
    (hψZ0 : ψ_Z 0 = 0)
    (h_syn_LZ : syndrome code L_Z = 0)
    (h_pair : dualPairing L_Z L_X = 1)
    (hWZ_fail : ∀ (e_err e' : Q → ZMod 2) (x0 : Point3D),
      (∀ q : Q, e_err q ≠ e' q → code.posQ q ∈ ball3D x0 2) →
      ψ_Z (syndrome code e') + dualPairing L_X e' ≠
        ψ_Z (syndrome code e_err) + dualPairing L_X e_err →
      ∃ c ∈ W_Z, (∀ m : M_X, c m ≠ 0 → syndrome code e_err m ≠ 0) ∨
               (∀ m : M_X, c m ≠ 0 → syndrome code e' m ≠ 0)) :
    ∃ (c : M_X → ZMod 2) (_ : c ∈ W_Z) (e_bad : Q → ZMod 2),
      ∀ m : M_X, c m ≠ 0 → syndrome code e_bad m ≠ 0 := by
  let f : (Q → ZMod 2) → ZMod 2 :=
    fun e => ψ_Z (syndrome code e) + dualPairing L_X e
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [map_zero, hψZ0, zero_add]
    dsimp [dualPairing]
    simp
  have hf_LZ : f L_Z = 1 := by
    dsimp [f]
    rw [h_syn_LZ, hψZ0, zero_add]
    have h_comm : dualPairing L_X L_Z = dualPairing L_Z L_X := by
      dsimp [dualPairing]
      exact Finset.sum_congr rfl (fun q _ => mul_comm _ _)
    rw [h_comm, h_pair]
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hne : f L_Z ≠ f 0 := by
    rw [hf_LZ, hf0]
    exact h10
  obtain ⟨e₁, e₂, q₀, h_diff_q₀, h_f_ne⟩ :=
    exists_step_of_ne_zero_on_finset f Finset.univ L_Z
      (fun q hq => False.elim (hq (Finset.mem_univ q))) hne
  have h_ball : ∀ q : Q, e₁ q ≠ e₂ q →
      code.posQ q ∈ ball3D (code.posQ q₀) 2 := by
    intro q hq
    rw [h_diff_q₀ q hq]
    dsimp [ball3D, distSq3D]
    simp
  obtain ⟨c, hcW, h_bad⟩ := hWZ_fail e₁ e₂ (code.posQ q₀) h_ball h_f_ne
  rcases h_bad with h1 | h2
  · exact ⟨c, hcW, e₁, h1⟩
  · exact ⟨c, hcW, e₂, h2⟩

private lemma hilbertTrace_zero_clm {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] :
    hilbertTrace (0 : ManyBodyHilbertSpace Site →L[ℂ] ManyBodyHilbertSpace Site) = 0 := by
  unfold hilbertTrace
  simp

private lemma syndromeSubsetProj_ne_one_of_hilbertTrace_eq_P0 {D L : ℕ}
    {Site : BoxD D L → Type} [∀ x, Fintype (Site x)] [∀ x, DecidableEq (Site x)] [∀ x, Nonempty (Site x)]
    {CheckIdx : Type} [Fintype CheckIdx] [DecidableEq CheckIdx]
    (sys : IndexedCommutingProjectorHamiltonian D L Site CheckIdx)
    (hP0_ne : sys.P0 ≠ 0)
    (S : Finset (CheckIdx → Bool)) (σ_bad : CheckIdx → Bool)
    (h_not_mem : σ_bad ∉ S)
    (h_tr : hilbertTrace (sys.syndromeProjector σ_bad) = hilbertTrace sys.P0) :
    syndromeSubsetProj sys S ≠ 1 := by
  have h_res := syndrome_resolution_indexed sys
  have hP0_proj : IsStarProjection sys.P0 := h_res.1 ▸ h_res.2.1 (fun _ => false)
  have h_tr_ge1 : (1 : ℝ) ≤ hilbertTrace sys.P0 :=
    one_le_hilbertTrace_of_isStarProjection_ne_zero hP0_proj hP0_ne
  have h_proj_ne : sys.syndromeProjector σ_bad ≠ 0 := by
    intro h0
    have h_tr0 : hilbertTrace (sys.syndromeProjector σ_bad) = 0 := by
      rw [h0, hilbertTrace_zero_clm]
    linarith
  intro h_eq_one
  have h_mul_zero : syndromeSubsetProj sys S * sys.syndromeProjector σ_bad = 0 := by
    dsimp [syndromeSubsetProj]
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun σ hσ => ?_
    have hne_σ : σ ≠ σ_bad := fun h => h_not_mem (h ▸ hσ)
    exact h_res.2.2.1 σ σ_bad hne_σ
  rw [h_eq_one, one_mul] at h_mul_zero
  exact h_proj_ne h_mul_zero

lemma syndromeSubsetProj_bdlSafeSyndromeSet_ne_one (k : ℕ)
    (ψ_Z : (BDLWeldedCheckX k → ZMod 2) → ZMod 2)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hψZ0 : ψ_Z 0 = 0)
    (hWZ_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q → (bdlWeldedCode k).posQ q ∈ ball3D x0 2) →
      ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' ≠
        ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err →
      ∃ c ∈ W_Z, (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e' m ≠ 0)) :
    syndromeSubsetProj (bdlInhomogeneousSystem k) (bdlSafeSyndromeSet k W_Z W_X) ≠ 1 := by
  obtain ⟨c, hcW, e_bad, he_bad⟩ := exists_witness_of_ballParityWitness
    (bdlWeldedCode k) (bdlWeldedLZ k) (bdlWeldedLX k) ψ_Z W_Z
    hψZ0 (syndrome_bdlWeldedLZ k) (dualPairing_bdlWeldedLZ_bdlWeldedLX k) hWZ_fail
  let σ_bad := staticCSSPauliFlip (bdlLocalDescriptor k) (bdlPushChain k e_bad) 0
  have h_not_safe : σ_bad ∉ bdlSafeSyndromeSet k W_Z W_X := by
    intro h_mem
    have h_safe := (Finset.mem_filter.mp h_mem).2.1 c hcW
    apply h_safe
    intro mX hmX
    rw [bdlPullSynX_staticCSSPauliFlip, bdlPullChain_bdlPushChain]
    exact he_bad mX hmX
  exact syndromeSubsetProj_ne_one_of_hilbertTrace_eq_P0
    (bdlInhomogeneousSystem k)
    (bdlInhomogeneousSystem_P0_ne_zero_and_ne_one k).1
    (bdlSafeSyndromeSet k W_Z W_X) σ_bad h_not_safe
    (hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq
      (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k)
      (bdlPushChain k e_bad) 0)

private lemma weylPauliZX_mul_weylPauliZ_bdlPushChain (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2)
    (c : BDLWeldedQubit k → ZMod 2) :
    (weylPauliZ a * weylPauliX b) * weylPauliZ (bdlPushChain k c) =
      signScalar (dualPairing c (bdlPullChain k b)) •
        (weylPauliZ (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
  calc (weylPauliZ a * weylPauliX b) * weylPauliZ (bdlPushChain k c)
    _ = weylPauliZ a * (weylPauliX b * weylPauliZ (bdlPushChain k c)) := by rw [mul_assoc]
    _ = pauliPhase (bdlPushChain k c) b •
          ((weylPauliZ a * weylPauliZ (bdlPushChain k c)) * weylPauliX b) := by
      rw [weylPauliX_mul_weylPauliZ, clm_mul_smul, mul_assoc]
    _ = signScalar (dualPairing c (bdlPullChain k b)) •
          (weylPauliZ (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
      rw [(weylPauliZ_comm a (bdlPushChain k c)).eq, mul_assoc,
        pauliPhase_eq_signScalar, sum_bdlPushChain_mul_eq_dualPairing_bdlPullChain]

private lemma weylPauliZX_mul_weylPauliX_bdlPushChain (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2)
    (c : BDLWeldedQubit k → ZMod 2) :
    (weylPauliZ a * weylPauliX b) * weylPauliX (bdlPushChain k c) =
      signScalar (dualPairing c (bdlPullChain k a)) •
        (weylPauliX (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
  have hZX : weylPauliZ a * weylPauliX (bdlPushChain k c) =
      signScalar (dualPairing c (bdlPullChain k a)) •
        (weylPauliX (bdlPushChain k c) * weylPauliZ a) := by
    have hXZ := weylPauliX_mul_weylPauliZ a (bdlPushChain k c)
    rw [pauliPhase_eq_signScalar, sum_mul_bdlPushChain_eq_dualPairing_bdlPullChain] at hXZ
    calc weylPauliZ a * weylPauliX (bdlPushChain k c)
      _ = (signScalar (dualPairing c (bdlPullChain k a)) *
            signScalar (dualPairing c (bdlPullChain k a))) •
            (weylPauliZ a * weylPauliX (bdlPushChain k c)) := by
        rw [signScalar_mul_self, one_smul]
      _ = signScalar (dualPairing c (bdlPullChain k a)) •
            (signScalar (dualPairing c (bdlPullChain k a)) •
              (weylPauliZ a * weylPauliX (bdlPushChain k c))) := by rw [smul_smul]
      _ = signScalar (dualPairing c (bdlPullChain k a)) •
            (weylPauliX (bdlPushChain k c) * weylPauliZ a) := by rw [← hXZ]
  calc (weylPauliZ a * weylPauliX b) * weylPauliX (bdlPushChain k c)
    _ = weylPauliZ a * (weylPauliX b * weylPauliX (bdlPushChain k c)) := by rw [mul_assoc]
    _ = (weylPauliZ a * weylPauliX (bdlPushChain k c)) * weylPauliX b := by
      rw [(weylPauliX_comm b (bdlPushChain k c)).eq, ← mul_assoc]
    _ = signScalar (dualPairing c (bdlPullChain k a)) •
          (weylPauliX (bdlPushChain k c) * (weylPauliZ a * weylPauliX b)) := by
      rw [hZX, clm_smul_mul, mul_assoc]

private lemma commutator_eq_zero_of_isSupportedOn_weylPauli {L q_code : ℕ}
    (A : Finset (Box3D L))
    (P O A_op : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)))
    (hA : IsSupportedOn (UniformSite3D L (CodeSlotConfig q_code)) A A_op)
    (h_pauli : ∀ a b : BoxSlot3D L q_code → ZMod 2,
      BoxSlotChainSupportedIn a A → BoxSlotChainSupportedIn b A →
      P * ((weylPauliZ a * weylPauliX b) * O - O * (weylPauliZ a * weylPauliX b)) * P = 0) :
    P * (A_op * O - O * A_op) * P = 0 := by
  obtain ⟨ι, hι_fin, w_coeff, a_fam, b_fam, ha_supp, hb_supp, hA_eq⟩ :=
    exists_weylPauli_expansion_of_isSupportedOn A hA
  letI : Fintype ι := hι_fin
  rw [hA_eq]
  ext φ : 1
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sub, map_sum, map_smul, ContinuousLinearMap.zero_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hj := congr_arg
    (fun T : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) →L[ℂ]
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig q_code)) => T φ)
    (h_pauli (a_fam j) (b_fam j) (ha_supp j) (hb_supp j))
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, map_sub] at hj
  rw [← smul_sub, hj, smul_zero]

lemma bdlSafeSyndromeSet_singleSite_immunity (k : ℕ)
    (ψ_Z : (BDLWeldedCheckX k → ZMod 2) → ZMod 2)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (ψ_X : (BDLWeldedCheckZ k → ZMod 2) → ZMod 2)
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q → (bdlWeldedCode k).posQ q ∈ ball3D x0 2) →
      ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' ≠
        ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err →
      ∃ c ∈ W_Z, (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckX k, c m ≠ 0 → syndrome (bdlWeldedCode k) e' m ≠ 0))
    (hWX_fail : ∀ (e_err e' : BDLWeldedQubit k → ZMod 2) (x0 : Point3D),
      (∀ q : BDLWeldedQubit k, e_err q ≠ e' q → (bdlWeldedCode k).posQ q ∈ ball3D x0 2) →
      ψ_X (syndrome (dualCode (bdlWeldedCode k)) e') + dualPairing (bdlWeldedLZ k) e' ≠
        ψ_X (syndrome (dualCode (bdlWeldedCode k)) e_err) + dualPairing (bdlWeldedLZ k) e_err →
      ∃ c ∈ W_X, (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e_err m ≠ 0) ∨
               (∀ m : BDLWeldedCheckZ k, c m ≠ 0 → syndrome (dualCode (bdlWeldedCode k)) e' m ≠ 0))
    (v : Box3D (bdlBoxSide k))
    (A_v : ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) →L[ℂ]
      ManyBodyHilbertSpace (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)))
    (hA_v : IsSupportedOn (UniformSite3D (bdlBoxSide k) (CodeSlotConfig qCodeBDL)) {v} A_v) :
    let sys := bdlInhomogeneousSystem k
    let Pi_safe := syndromeSubsetProj sys (bdlSafeSyndromeSet k W_Z W_X)
    let O_dec_Z := weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) *
      syndromeSignOp sys (fun σ => ψ_X (bdlPullSynZ k σ))
    let O_dec_X := weylPauliX (bdlPushChain k (bdlWeldedLX k)) *
      syndromeSignOp sys (fun σ => ψ_Z (bdlPullSynX k σ))
    Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
    Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0 := by
  intro sys Pi_safe O_dec_Z O_dec_X
  have hZ_comm : ∀ i, Commute (weylPauliZ (bdlPushChain k (bdlWeldedLZ k))) (sys.checkProj i) :=
    fun i => (weylPauliZ_bdlPushChain_commute_checkProj k (bdlWeldedLZ k) (syndrome_bdlWeldedLZ k) i).symm
  have hX_comm : ∀ i, Commute (weylPauliX (bdlPushChain k (bdlWeldedLX k))) (sys.checkProj i) :=
    fun i => (weylPauliX_bdlPushChain_commute_checkProj k (bdlWeldedLX k) (syndrome_bdlWeldedLX k) i).symm
  have h_pauli : ∀ a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2,
      BoxSlotChainSupportedIn a {v} → BoxSlotChainSupportedIn b {v} →
      Pi_safe * ((weylPauliZ a * weylPauliX b) * O_dec_Z - O_dec_Z * (weylPauliZ a * weylPauliX b)) * Pi_safe = 0 ∧
      Pi_safe * ((weylPauliZ a * weylPauliX b) * O_dec_X - O_dec_X * (weylPauliZ a * weylPauliX b)) * Pi_safe = 0 := by
    intro a b ha_supp hb_supp
    have ha_ball : ∀ q : BDLWeldedQubit k, bdlPullChain k a q ≠ 0 →
        (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v) 2 := by
      intro q hq_ne
      apply posQ_mem_ball3D_two_of_bdlGridVertexQ_eq k v q
      have hp_mem := ha_supp (bdlQubitSiteSlot k q) hq_ne
      rw [bdlQubitSiteSlot_eq k q, Finset.mem_singleton] at hp_mem
      exact hp_mem
    have hb_ball : ∀ q : BDLWeldedQubit k, bdlPullChain k b q ≠ 0 →
        (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v) 2 := by
      intro q hq_ne
      apply posQ_mem_ball3D_two_of_bdlGridVertexQ_eq k v q
      have hp_mem := hb_supp (bdlQubitSiteSlot k q) hq_ne
      rw [bdlQubitSiteSlot_eq k q, Finset.mem_singleton] at hp_mem
      exact hp_mem
    refine ⟨?_, ?_⟩
    · apply syndromeSubsetProj_commutator_eq_zero_of_checkFlip sys hZ_comm
        (fun σ => ψ_X (bdlPullSynZ k σ)) (bdlSafeSyndromeSet k W_Z W_X)
        (weylPauliZX_mul_staticCSSCheckProj (bdlLocalDescriptor k) a b)
        (weylPauliZX_mul_weylPauliZ_bdlPushChain k a b (bdlWeldedLZ k))
      intro σ hσ h_nz hσ'
      obtain ⟨a₀, b₀, hσ_eq, _⟩ := exists_chains_of_syndromeProjector_ne_zero
        (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k) σ h_nz
      let e_err := bdlPullChain k b₀
      let e' := e_err + bdlPullChain k b
      have h_syn_err : bdlPullSynZ k σ = syndrome (dualCode (bdlWeldedCode k)) e_err := by
        rw [hσ_eq, bdlPullSynZ_staticCSSPauliFlip]
      have h_syn_e' : bdlPullSynZ k (fun i => xor (σ i) (staticCSSPauliFlip (bdlLocalDescriptor k) a b i)) =
          syndrome (dualCode (bdlWeldedCode k)) e' := by
        rw [bdlPullSynZ_xor_staticCSSPauliFlip, h_syn_err, map_add]
      have h_diff : ∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
          (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v) 2 := by
        intro q hq
        apply hb_ball q
        intro hb0
        apply hq
        dsimp [e']
        rw [hb0, add_zero]
      have h_eq_parity : ψ_X (syndrome (dualCode (bdlWeldedCode k)) e') + dualPairing (bdlWeldedLZ k) e' =
          ψ_X (syndrome (dualCode (bdlWeldedCode k)) e_err) + dualPairing (bdlWeldedLZ k) e_err := by
        by_contra h_disc
        obtain ⟨c, hcW, h_or⟩ := hWX_fail e_err e' (bdlGridCenter k v) h_diff h_disc
        rcases h_or with h1 | h2
        · exact (Finset.mem_filter.mp hσ).2.2 c hcW (by rwa [h_syn_err])
        · exact (Finset.mem_filter.mp hσ').2.2 c hcW (by rwa [h_syn_e'])
      rw [h_syn_e', h_syn_err]
      have h_pair_add : dualPairing (bdlWeldedLZ k) e' =
          dualPairing (bdlWeldedLZ k) e_err + dualPairing (bdlWeldedLZ k) (bdlPullChain k b) :=
        dualPairing_add_right_zmod2 (bdlWeldedLZ k) e_err (bdlPullChain k b)
      rw [h_pair_add] at h_eq_parity
      have h_alg : ∀ x u y z : ZMod 2, x + (y + z) = u + y → x = u + z := by decide
      exact h_alg _ _ _ _ h_eq_parity
    · apply syndromeSubsetProj_commutator_eq_zero_of_checkFlip sys hX_comm
        (fun σ => ψ_Z (bdlPullSynX k σ)) (bdlSafeSyndromeSet k W_Z W_X)
        (weylPauliZX_mul_staticCSSCheckProj (bdlLocalDescriptor k) a b)
        (weylPauliZX_mul_weylPauliX_bdlPushChain k a b (bdlWeldedLX k))
      intro σ hσ h_nz hσ'
      obtain ⟨a₀, b₀, hσ_eq, _⟩ := exists_chains_of_syndromeProjector_ne_zero
        (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k) σ h_nz
      let e_err := bdlPullChain k a₀
      let e' := e_err + bdlPullChain k a
      have h_syn_err : bdlPullSynX k σ = syndrome (bdlWeldedCode k) e_err := by
        rw [hσ_eq, bdlPullSynX_staticCSSPauliFlip]
      have h_syn_e' : bdlPullSynX k (fun i => xor (σ i) (staticCSSPauliFlip (bdlLocalDescriptor k) a b i)) =
          syndrome (bdlWeldedCode k) e' := by
        rw [bdlPullSynX_xor_staticCSSPauliFlip, h_syn_err, map_add]
      have h_diff : ∀ q : BDLWeldedQubit k, e_err q ≠ e' q →
          (bdlWeldedCode k).posQ q ∈ ball3D (bdlGridCenter k v) 2 := by
        intro q hq
        apply ha_ball q
        intro ha0
        apply hq
        dsimp [e']
        rw [ha0, add_zero]
      have h_eq_parity : ψ_Z (syndrome (bdlWeldedCode k) e') + dualPairing (bdlWeldedLX k) e' =
          ψ_Z (syndrome (bdlWeldedCode k) e_err) + dualPairing (bdlWeldedLX k) e_err := by
        by_contra h_disc
        obtain ⟨c, hcW, h_or⟩ := hWZ_fail e_err e' (bdlGridCenter k v) h_diff h_disc
        rcases h_or with h1 | h2
        · exact (Finset.mem_filter.mp hσ).2.1 c hcW (by rwa [h_syn_err])
        · exact (Finset.mem_filter.mp hσ').2.1 c hcW (by rwa [h_syn_e'])
      rw [h_syn_e', h_syn_err]
      have h_pair_add : dualPairing (bdlWeldedLX k) e' =
          dualPairing (bdlWeldedLX k) e_err + dualPairing (bdlWeldedLX k) (bdlPullChain k a) :=
        dualPairing_add_right_zmod2 (bdlWeldedLX k) e_err (bdlPullChain k a)
      rw [h_pair_add] at h_eq_parity
      have h_alg : ∀ x u y z : ZMod 2, x + (y + z) = u + y → x = u + z := by decide
      exact h_alg _ _ _ _ h_eq_parity
  exact ⟨commutator_eq_zero_of_isSupportedOn_weylPauli {v} Pi_safe O_dec_Z A_v hA_v
      (fun a b ha hb => (h_pauli a b ha hb).1),
    commutator_eq_zero_of_isSupportedOn_weylPauli {v} Pi_safe O_dec_X A_v hA_v
      (fun a b ha hb => (h_pauli a b ha hb).2)⟩

end
