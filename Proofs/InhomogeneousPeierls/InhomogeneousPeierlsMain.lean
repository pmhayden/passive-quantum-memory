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

import Proofs.InhomogeneousPeierls.InhomogeneousPeierlsBound

/-!
# Main Inhomogeneous Peierls Theorem and Safe-Subspace Package for the Welded Lattice

Connects the cubic-grid realization `bdlInhomogeneousSystem k` to abstract F2 parity witness families via `gibbsFailureProb_bdlSafeSyndromeSet_le`. Proves `bdlInhomogeneousSafeProjector_and_decodedLogical_exists_aux`, establishing the existence of the safe syndrome projector and anticommuting decoded logical observables with single-site safe-subspace immunity and stretched-exponential Gibbs failure suppression.

## References

* Part I, Section 5.4 (`subsec:safe-decoded-observables`), Definition 5.6 (`def:safe-decoded-observables`), Proposition 5.7 (`prop:safe-subspace-immunity`)
* Part I, Section 7.4 (`subsec:main-theorem-synthesis`), Theorem 7.5 (`thm:main`)
* Part II, Section 2 (`subsec:setup`), Definition 2.1 (`def:bdl-lattice`), Definition 2.5 (`def:syndrome-safe`)
-/

noncomputable section

open scoped Classical BigOperators InnerProduct ComplexConjugate
open ContinuousLinearMap WeldedHierarchy WeldedHierarchy.BDLDecoder

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

/-! ## 1. BDL Grid-Snap Realizable Syndrome Bridge -/

lemma staticCSSPauliFlip_inl {r_0 L q_code m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (a b : BoxSlot3D L q_code → ZMod 2)
    (v : Box3D L) (s : Fin q_code) :
    staticCSSPauliFlip ω a b (Sum.inl (v, s)) =
      (((ω v).activeSlot s == false) && decide (b (v, s) ≠ 0)) := by
  dsimp [staticCSSPauliFlip]
  congr 1
  have h_sum : (∑ p : BoxSlot3D L q_code, singleSlotChain v s p * b p) = b (v, s) := by
    rw [Finset.sum_eq_single (v, s)]
    · dsimp [singleSlotChain]; rw [if_pos rfl, one_mul]
    · intro p _ hne
      dsimp [singleSlotChain]; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ (v, s)))
  rw [h_sum]

def IsValidPinSynGen {r_0 L q_code m_max : ℕ}
    (ω : Box3D L → LocalCSSDescriptor q_code r_0 m_max)
    (s_pin : BoxSlot3D L q_code → Bool) : Prop :=
  ∀ p : BoxSlot3D L q_code, (ω p.1).activeSlot p.2 = true → s_pin p = false

def bdlPinSyn (k : ℕ)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool) :
    BoxSlot3D (bdlBoxSide k) qCodeBDL → Bool :=
  fun p => σ (Sum.inl p)

def bdlCheckXPair (k : ℕ) (mX : BDLWeldedCheckX k) :
    Box3D (bdlBoxSide k) × Fin mMaxBDL :=
  (bdlGridVertexX k mX, ⟨bdlCheckXLocalRank k mX, bdlCheckXLocalRank_lt_m_max k mX⟩)

def bdlCheckZPair (k : ℕ) (mZ : BDLWeldedCheckZ k) :
    Box3D (bdlBoxSide k) × Fin mMaxBDL :=
  (bdlGridVertexZ k mZ, ⟨bdlCheckZLocalRank k mZ, bdlCheckZLocalRank_lt_m_max k mZ⟩)

lemma bdlCheckXPair_injective (k : ℕ) : Function.Injective (bdlCheckXPair k) :=
  fun _ _ h => bdlCheckXSlot_injective k (congr_arg (Sum.inr ∘ Sum.inl) h)

lemma bdlCheckZPair_injective (k : ℕ) : Function.Injective (bdlCheckZPair k) :=
  fun _ _ h => bdlCheckZSlot_injective k (congr_arg (Sum.inr ∘ Sum.inr) h)

lemma exists_bdlCheckXPair_iff (k : ℕ) (v : Box3D (bdlBoxSide k)) (idxX : Fin mMaxBDL) :
    (∃ mX : BDLWeldedCheckX k, bdlCheckXPair k mX = (v, idxX)) ↔
      idxX.val < (bdlLocalDescriptor k v).numXChecks.val := by
  constructor
  · rintro ⟨mX, hmX⟩
    have hv : bdlGridVertexX k mX = v := (Prod.ext_iff.mp hmX).1
    have hr : bdlCheckXLocalRank k mX = idxX.val := congr_arg Fin.val (Prod.ext_iff.mp hmX).2
    rw [numXChecks_val_eq_card_fiber, ← hv, ← hr]
    exact bdlCheckXLocalRank_lt_card k mX
  · intro hm
    rw [numXChecks_val_eq_card_fiber] at hm
    have h_injX : Function.Injective (bdlCellIndexX k) :=
      Fin.val_injective.comp (Fintype.equivFin _).injective
    obtain ⟨mX, hv, hr⟩ :=
      fiber_localRank_surjective_bdl (bdlGridVertexX k) (bdlCellIndexX k) h_injX v idxX.val hm
    exact ⟨mX, Prod.ext hv (Fin.ext hr)⟩

lemma exists_bdlCheckZPair_iff (k : ℕ) (v : Box3D (bdlBoxSide k)) (idxZ : Fin mMaxBDL) :
    (∃ mZ : BDLWeldedCheckZ k, bdlCheckZPair k mZ = (v, idxZ)) ↔
      idxZ.val < (bdlLocalDescriptor k v).numZChecks.val := by
  constructor
  · rintro ⟨mZ, hmZ⟩
    have hv : bdlGridVertexZ k mZ = v := (Prod.ext_iff.mp hmZ).1
    have hr : bdlCheckZLocalRank k mZ = idxZ.val := congr_arg Fin.val (Prod.ext_iff.mp hmZ).2
    rw [numZChecks_val_eq_card_fiber, ← hv, ← hr]
    exact bdlCheckZLocalRank_lt_card k mZ
  · intro hm
    rw [numZChecks_val_eq_card_fiber] at hm
    have h_injZ : Function.Injective (bdlCellIndexZ k) :=
      Fin.val_injective.comp (Fintype.equivFin _).injective
    obtain ⟨mZ, hv, hr⟩ :=
      fiber_localRank_surjective_bdl (bdlGridVertexZ k) (bdlCellIndexZ k) h_injZ v idxZ.val hm
    exact ⟨mZ, Prod.ext hv (Fin.ext hr)⟩

lemma staticCSSPauliFlip_eq_embedSynGen (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    staticCSSPauliFlip (bdlLocalDescriptor k) a b =
      embedSynGen (bdlCheckXPair k) (bdlCheckZPair k)
        (bdlPinSyn k (staticCSSPauliFlip (bdlLocalDescriptor k) a b))
        (syndrome (bdlWeldedCode k) (bdlPullChain k a))
        (syndrome (dualCode (bdlWeldedCode k)) (bdlPullChain k b)) := by
  ext i
  rcases i with p | ⟨v, idxX⟩ | ⟨v, idxZ⟩
  · rfl
  · dsimp [embedSynGen, embedCheckBits]
    by_cases hex : ∃ mX : BDLWeldedCheckX k, bdlCheckXPair k mX = (v, idxX)
    · rw [dif_pos hex]
      let mX := Classical.choose hex
      have hmX : bdlCheckXSlot k mX = Sum.inr (Sum.inl (v, idxX)) :=
        congr_arg (Sum.inr ∘ Sum.inl) (Classical.choose_spec hex)
      rw [← bdlPullSynX_staticCSSPauliFlip k a b]
      change staticCSSPauliFlip (bdlLocalDescriptor k) a b (Sum.inr (Sum.inl (v, idxX))) =
        decide (boolToZMod2 (staticCSSPauliFlip (bdlLocalDescriptor k) a b (bdlCheckXSlot k mX)) ≠ 0)
      rw [hmX]
      cases staticCSSPauliFlip (bdlLocalDescriptor k) a b (Sum.inr (Sum.inl (v, idxX))) <;> rfl
    · rw [dif_neg hex]
      have h_not_lt : ¬ (idxX.val < (bdlLocalDescriptor k v).numXChecks.val) :=
        mt (exists_bdlCheckXPair_iff k v idxX).mpr hex
      dsimp [staticCSSPauliFlip]
      rw [decide_eq_false h_not_lt, Bool.false_and]
  · dsimp [embedSynGen, embedCheckBits]
    by_cases hex : ∃ mZ : BDLWeldedCheckZ k, bdlCheckZPair k mZ = (v, idxZ)
    · rw [dif_pos hex]
      let mZ := Classical.choose hex
      have hmZ : bdlCheckZSlot k mZ = Sum.inr (Sum.inr (v, idxZ)) :=
        congr_arg (Sum.inr ∘ Sum.inr) (Classical.choose_spec hex)
      rw [← bdlPullSynZ_staticCSSPauliFlip k a b]
      change staticCSSPauliFlip (bdlLocalDescriptor k) a b (Sum.inr (Sum.inr (v, idxZ))) =
        decide (boolToZMod2 (staticCSSPauliFlip (bdlLocalDescriptor k) a b (bdlCheckZSlot k mZ)) ≠ 0)
      rw [hmZ]
      cases staticCSSPauliFlip (bdlLocalDescriptor k) a b (Sum.inr (Sum.inr (v, idxZ))) <;> rfl
    · rw [dif_neg hex]
      have h_not_lt : ¬ (idxZ.val < (bdlLocalDescriptor k v).numZChecks.val) :=
        mt (exists_bdlCheckZPair_iff k v idxZ).mpr hex
      dsimp [staticCSSPauliFlip]
      rw [decide_eq_false h_not_lt, Bool.false_and]

lemma bdlPinSyn_staticCSSPauliFlip_isValid (k : ℕ)
    (a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2) :
    IsValidPinSynGen (bdlLocalDescriptor k)
      (bdlPinSyn k (staticCSSPauliFlip (bdlLocalDescriptor k) a b)) := by
  intro ⟨v, s⟩ h_act
  dsimp [bdlPinSyn]
  rw [staticCSSPauliFlip_inl, h_act]
  rfl

lemma exists_staticCSSPauliFlip_of_isValidPinSyn (k : ℕ)
    {s_pin : BoxSlot3D (bdlBoxSide k) qCodeBDL → Bool}
    (h_pin : IsValidPinSynGen (bdlLocalDescriptor k) s_pin)
    (e_X e_Z : BDLWeldedQubit k → ZMod 2) :
    ∃ a b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2,
      staticCSSPauliFlip (bdlLocalDescriptor k) a b =
        embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) s_pin
          (syndrome (bdlWeldedCode k) e_X)
          (syndrome (dualCode (bdlWeldedCode k)) e_Z) := by
  let a := bdlPushChain k e_X
  let b : BoxSlot3D (bdlBoxSide k) qCodeBDL → ZMod 2 :=
    fun p => if (bdlLocalDescriptor k p.1).activeSlot p.2 then bdlPushChain k e_Z p
             else boolToZMod2 (s_pin p)
  have hb_pull : bdlPullChain k b = e_Z := by
    ext q
    dsimp [bdlPullChain, b]
    have h_act : (bdlLocalDescriptor k (bdlQubitSiteSlot k q).1).activeSlot (bdlQubitSiteSlot k q).2 = true := by
      rw [bdlQubitSiteSlot_eq k q]
      dsimp [bdlLocalDescriptor, bdlLocalDescriptorOfPlacement]
      exact decide_eq_true (bdlQubitLocalRank_lt_card k q)
    rw [if_pos h_act, bdlPushChain_apply_bdlQubitSiteSlot]
  have h_pin_eq : bdlPinSyn k (staticCSSPauliFlip (bdlLocalDescriptor k) a b) = s_pin := by
    ext ⟨v, s⟩
    dsimp [bdlPinSyn]
    rw [staticCSSPauliFlip_inl]
    by_cases h_act : (bdlLocalDescriptor k v).activeSlot s = true
    · rw [h_act, h_pin (v, s) h_act]
      rfl
    · have h_inact : (bdlLocalDescriptor k v).activeSlot s = false :=
        Bool.eq_false_of_not_eq_true h_act
      have hb_vs : b (v, s) = boolToZMod2 (s_pin (v, s)) := if_neg h_act
      rw [h_inact, hb_vs]
      cases s_pin (v, s) <;> rfl
  refine ⟨a, b, ?_⟩
  rw [staticCSSPauliFlip_eq_embedSynGen k a b, h_pin_eq, bdlPullChain_bdlPushChain, hb_pull]

lemma bdlPullSynX_embedSynGen (k : ℕ)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL → Bool)
    (sX : BDLWeldedCheckX k → ZMod 2) (sZ : BDLWeldedCheckZ k → ZMod 2) :
    bdlPullSynX k (embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) p sX sZ) = sX :=
  pullCheckBits_embedCheckBits (bdlCheckXPair_injective k) sX

lemma bdlPullSynZ_embedSynGen (k : ℕ)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL → Bool)
    (sX : BDLWeldedCheckX k → ZMod 2) (sZ : BDLWeldedCheckZ k → ZMod 2) :
    bdlPullSynZ k (embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) p sX sZ) = sZ :=
  pullCheckBits_embedCheckBits (bdlCheckZPair_injective k) sZ

lemma bdlPullSynX_false (k : ℕ) : bdlPullSynX k (fun _ => false) = 0 := rfl
lemma bdlPullSynZ_false (k : ℕ) : bdlPullSynZ k (fun _ => false) = 0 := rfl

/-! ## 2. Main Inhomogeneous Peierls & Decoded Logical Theorem -/

lemma bdl_gibbs_tr_eq (k : ℕ)
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL → Bool)
    (hp : IsValidPinSynGen (bdlLocalDescriptor k) p)
    (e_X e_Z : BDLWeldedQubit k → ZMod 2) :
    hilbertTrace ((bdlInhomogeneousSystem k).syndromeProjector
      (embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) p
        (syndrome (bdlWeldedCode k) e_X)
        (syndrome (dualCode (bdlWeldedCode k)) e_Z))) =
      hilbertTrace (bdlInhomogeneousSystem k).P0 := by
  obtain ⟨a, b, h_flip⟩ := exists_staticCSSPauliFlip_of_isValidPinSyn k hp e_X e_Z
  rw [← h_flip]
  exact hilbertTrace_syndromeProjector_staticCSSPauliFlip_eq
    (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k) a b

lemma bdl_gibbs_realizable (k : ℕ)
    (σ : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL → Bool)
    (h_proj_nz : (bdlInhomogeneousSystem k).syndromeProjector σ ≠ 0) :
    ∃ p : BoxSlot3D (bdlBoxSide k) qCodeBDL → Bool,
      IsValidPinSynGen (bdlLocalDescriptor k) p ∧
      ∃ e_X e_Z : BDLWeldedQubit k → ZMod 2,
        σ = embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) p
          (syndrome (bdlWeldedCode k) e_X)
          (syndrome (dualCode (bdlWeldedCode k)) e_Z) := by
  obtain ⟨a, b, rfl, _⟩ := exists_chains_of_syndromeProjector_ne_zero
    (bdlLocalDescriptor k) (bdlLocalDescriptor_validDescriptorField k) σ h_proj_nz
  exact ⟨bdlPinSyn k (staticCSSPauliFlip (bdlLocalDescriptor k) a b),
    bdlPinSyn_staticCSSPauliFlip_isValid k a b,
    bdlPullChain k a, bdlPullChain k b,
    staticCSSPauliFlip_eq_embedSynGen k a b⟩

lemma bdl_gibbs_unsafe (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (p : BoxSlot3D (bdlBoxSide k) qCodeBDL → Bool)
    (_hp : IsValidPinSynGen (bdlLocalDescriptor k) p)
    (sX : BDLWeldedCheckX k → ZMod 2) (sZ : BDLWeldedCheckZ k → ZMod 2)
    (h_not_safe : embedSynGen (bdlCheckXPair k) (bdlCheckZPair k) p sX sZ ∉
      bdlSafeSyndromeSet k W_Z W_X) :
    (∃ c ∈ W_Z, ∀ mX : BDLWeldedCheckX k, c mX ≠ 0 → sX mX ≠ 0) ∨
    (∃ c ∈ W_X, ∀ mZ : BDLWeldedCheckZ k, c mZ ≠ 0 → sZ mZ ≠ 0) := by
  by_contra h_both
  rcases not_or.mp h_both with ⟨h1, h2⟩
  apply h_not_safe
  rw [bdlSafeSyndromeSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ⟨fun c hc h_sub => h1 ⟨c, hc, ?_⟩, fun c hc h_sub => h2 ⟨c, hc, ?_⟩⟩⟩
  · rwa [bdlPullSynX_embedSynGen] at h_sub
  · rwa [bdlPullSynZ_embedSynGen] at h_sub

lemma bdlInhomogeneousSystem_weight_eq_one (k : ℕ)
    (i : StaticCSSCheckIdx (bdlBoxSide k) qCodeBDL mMaxBDL) :
    (bdlInhomogeneousSystem k).weight i = 1 := rfl

lemma gibbsFailureProb_bdlSafeSyndromeSet_le_of_sums (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (β : ℝ) (hβ : β > betaCritBDL)
    (hWZ_sum : (∑ c ∈ W_Z, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤
      Real.exp (- bdlFreeEnergyBarrier k β) / 2)
    (hWX_sum : (∑ c ∈ W_X, Real.exp (-β * WeldedHierarchy.syndromeWeight c)) ≤
      Real.exp (- bdlFreeEnergyBarrier k β) / 2) :
    gibbsFailureProb (bdlInhomogeneousSystem k).H0 (bdlInhomogeneousSystem k).isSelfAdjoint_H0 β
      (1 - syndromeSubsetProj (bdlInhomogeneousSystem k) (bdlSafeSyndromeSet k W_Z W_X)) ≤
      Real.exp (- bdlFreeEnergyBarrier k β) := by
  have hβ_pos : 0 ≤ β := le_of_lt (lt_trans beta_crit_bdl_pos hβ)
  have hr0 : 0 ≤ Real.exp (- bdlFreeEnergyBarrier k β) := le_of_lt (Real.exp_pos _)
  exact gibbsFailureProb_staticCSS_le_of_witness_sums
    (bdlInhomogeneousSystem k) (bdlWeldedCode k)
    (bdlCheckXPair_injective k) (bdlCheckZPair_injective k)
    (IsValidPinSynGen (bdlLocalDescriptor k)) W_Z W_X (bdlSafeSyndromeSet k W_Z W_X)
    β (Real.exp (- bdlFreeEnergyBarrier k β)) hβ_pos hr0
    (bdlInhomogeneousSystem_weight_eq_one k) hWZ_sum hWX_sum
    (bdl_gibbs_tr_eq k)
    (bdl_gibbs_realizable k)
    (bdl_gibbs_unsafe k W_Z W_X)

lemma gibbsFailureProb_bdlSafeSyndromeSet_le (k : ℕ)
    (W_Z : Finset (BDLWeldedCheckX k → ZMod 2))
    (W_X : Finset (BDLWeldedCheckZ k → ZMod 2))
    (hWZ_card : W_Z.card ≤ (bdlClusterStepBase ^ 8) ^ (clusterRawWeight k))
    (hWZ_wt : ∀ c ∈ W_Z, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c)
    (hWX_card : W_X.card ≤ (bdlClusterStepBase ^ 8) ^ (clusterRawWeight k))
    (hWX_wt : ∀ c ∈ W_X, ((clusterRawWeight k : ℕ) : ℝ) ≤ WeldedHierarchy.syndromeWeight c)
    (β : ℝ) (hβ : β > betaCritBDL) :
    gibbsFailureProb (bdlInhomogeneousSystem k).H0 (bdlInhomogeneousSystem k).isSelfAdjoint_H0 β
      (1 - syndromeSubsetProj (bdlInhomogeneousSystem k) (bdlSafeSyndromeSet k W_Z W_X)) ≤
      Real.exp (- bdlFreeEnergyBarrier k β) := by
  have hβ_pos : 0 ≤ β := le_of_lt (lt_trans beta_crit_bdl_pos hβ)
  have hr0 : 0 ≤ Real.exp (- bdlFreeEnergyBarrier k β) := le_of_lt (Real.exp_pos _)
  exact gibbsFailureProb_staticCSS_le_of_witnesses
    (bdlInhomogeneousSystem k) (bdlWeldedCode k)
    (bdlCheckXPair_injective k) (bdlCheckZPair_injective k)
    (IsValidPinSynGen (bdlLocalDescriptor k)) W_Z W_X (bdlSafeSyndromeSet k W_Z W_X)
    (clusterRawWeight k : ℝ) β (Real.exp (- bdlFreeEnergyBarrier k β)) hβ_pos hr0
    (bdlInhomogeneousSystem_weight_eq_one k) hWZ_wt hWX_wt
    (witness_card_mul_exp_le_half_barrier k hWZ_card hβ)
    (witness_card_mul_exp_le_half_barrier k hWX_card hβ)
    (bdl_gibbs_tr_eq k)
    (bdl_gibbs_realizable k)
    (bdl_gibbs_unsafe k W_Z W_X)

theorem bdlInhomogeneousSafeProjector_and_decodedLogical_exists_aux (k : ℕ) :
    let L := bdlBoxSide k
    let D_field := bdlLocalDescriptor k
    ∃ (sys : IndexedCommutingProjectorHamiltonian 3 L
        (UniformSite3D L (CodeSlotConfig qCodeBDL))
        (StaticCSSCheckIdx L qCodeBDL mMaxBDL))
      (Z_log X_log Pi_safe O_dec_Z O_dec_X :
        ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
          ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
      (∀ idx : StaticCSSCheckIdx L qCodeBDL mMaxBDL,
        sys.checkProj idx = staticCSSCheckProj D_field idx ∧
        sys.support idx = staticCSSCheckSupport D_field idx ∧
        sys.weight idx = 1) ∧
      (sys.P0 ≠ 0 ∧ sys.P0 ≠ 1) ∧
      SatisfiesTQO1 sys (bdlLinearTQORadius k) ∧
      SatisfiesLinearTQO2 sys (bdlLinearTQORadius k) (collarConstRCABDL : ℝ) ∧
      SatisfiesSectorFilteredLinearTQO2 sys 1 (bdlLinearTQORadius k) (collarConstRCABDL : ℝ) ∧
      (IsSelfAdjoint Z_log ∧ Z_log * Z_log = 1 ∧ Commute sys.H0 Z_log ∧ Commute sys.P0 Z_log) ∧
      (IsSelfAdjoint X_log ∧ X_log * X_log = 1 ∧ Commute sys.H0 X_log ∧ Commute sys.P0 X_log) ∧
      (Z_log * X_log + X_log * Z_log) * sys.P0 = 0 ∧
      (Z_log * sys.P0 ≠ 0 ∧ X_log * sys.P0 ≠ 0) ∧
      (IsStarProjection Pi_safe ∧ Pi_safe ≠ 0 ∧ Pi_safe ≠ 1 ∧
        Commute sys.H0 Pi_safe ∧ sys.P0 * Pi_safe = sys.P0) ∧
      (IsSelfAdjoint O_dec_Z ∧ O_dec_Z * O_dec_Z = 1 ∧ ‖O_dec_Z‖ ≤ 1 ∧
        Commute sys.H0 O_dec_Z ∧ O_dec_Z * sys.P0 = Z_log * sys.P0 ∧
        Pi_safe * (sys.P0 - O_dec_Z * sys.P0 * O_dec_Z†) * Pi_safe = 0) ∧
      (IsSelfAdjoint O_dec_X ∧ O_dec_X * O_dec_X = 1 ∧ ‖O_dec_X‖ ≤ 1 ∧
        Commute sys.H0 O_dec_X ∧ O_dec_X * sys.P0 = X_log * sys.P0 ∧
        Pi_safe * (sys.P0 - O_dec_X * sys.P0 * O_dec_X†) * Pi_safe = 0) ∧
      (∀ (v : Box3D L)
         (A_v : ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL)) →L[ℂ]
           ManyBodyHilbertSpace (UniformSite3D L (CodeSlotConfig qCodeBDL))),
         IsSupportedOn (UniformSite3D L (CodeSlotConfig qCodeBDL)) {v} A_v →
         Pi_safe * (A_v * O_dec_Z - O_dec_Z * A_v) * Pi_safe = 0 ∧
         Pi_safe * (A_v * O_dec_X - O_dec_X * A_v) * Pi_safe = 0) ∧
      (∀ β : ℝ, β > betaCritBDL →
        gibbsFailureProb sys.H0 sys.isSelfAdjoint_H0 β (1 - Pi_safe) ≤
          Real.exp (- bdlFreeEnergyBarrier k β)) := by
  obtain ⟨⟨ψ_Z, W_Z, hψZ0, hWZ_card, hWZ_wt, hWZ_fail⟩,
          ⟨ψ_X, W_X, hψX0, hWX_card, hWX_wt, hWX_fail⟩⟩ :=
    hasBallParityWitnessFamily_bdlWelded_two k
  have h_tqo := bdlInhomogeneousSystem_satisfiesOperatorTQO k
  have h_bare := bdl_bare_logical_props k (bdlWeldedLZ k) (bdlWeldedLX k)
    (syndrome_bdlWeldedLZ k) (syndrome_bdlWeldedLX k) (dualPairing_bdlWeldedLZ_bdlWeldedLX k)
  have hw_ge1 : (1 : ℝ) ≤ ((clusterRawWeight k : ℕ) : ℝ) :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)).trans (three_div_two_pow_le_clusterRawWeight k)
  have h0_mem : (fun _ => false) ∈ bdlSafeSyndromeSet k W_Z W_X :=
    false_mem_bdlSafeSyndromeSet k W_Z W_X
      (fun c hc => hw_ge1.trans (hWZ_wt c hc))
      (fun c hc => hw_ge1.trans (hWX_wt c hc))
  have h_sd := safeAndDecoded_props_of_commute
    (bdlInhomogeneousSystem k)
    (weylPauliZ (bdlPushChain k (bdlWeldedLZ k)))
    (weylPauliX (bdlPushChain k (bdlWeldedLX k)))
    (bdlInhomogeneousSystem_P0_ne_zero_and_ne_one k).1
    h_bare.1.1 h_bare.1.2.1
    (weylPauliZ_bdlPushChain_commute_checkProj k (bdlWeldedLZ k) (syndrome_bdlWeldedLZ k))
    h_bare.2.1.1 h_bare.2.1.2.1
    (weylPauliX_bdlPushChain_commute_checkProj k (bdlWeldedLX k) (syndrome_bdlWeldedLX k))
    (bdlSafeSyndromeSet k W_Z W_X) h0_mem
    (syndromeSubsetProj_bdlSafeSyndromeSet_ne_one k ψ_Z W_Z W_X hψZ0 hWZ_fail)
    (fun σ => ψ_X (bdlPullSynZ k σ))
    (fun σ => ψ_Z (bdlPullSynX k σ))
    (by (try dsimp only); rw [bdlPullSynZ_false]; exact hψX0)
    (by (try dsimp only); rw [bdlPullSynX_false]; exact hψZ0)
  refine ⟨bdlInhomogeneousSystem k,
    weylPauliZ (bdlPushChain k (bdlWeldedLZ k)),
    weylPauliX (bdlPushChain k (bdlWeldedLX k)),
    syndromeSubsetProj (bdlInhomogeneousSystem k) (bdlSafeSyndromeSet k W_Z W_X),
    weylPauliZ (bdlPushChain k (bdlWeldedLZ k)) *
      syndromeSignOp (bdlInhomogeneousSystem k) (fun σ => ψ_X (bdlPullSynZ k σ)),
    weylPauliX (bdlPushChain k (bdlWeldedLX k)) *
      syndromeSignOp (bdlInhomogeneousSystem k) (fun σ => ψ_Z (bdlPullSynX k σ)),
    fun idx => ⟨rfl, rfl, rfl⟩,
    bdlInhomogeneousSystem_P0_ne_zero_and_ne_one k,
    h_tqo.1, h_tqo.2.1, h_tqo.2.2,
    h_bare.1, h_bare.2.1, h_bare.2.2.1, h_bare.2.2.2,
    h_sd.1, h_sd.2.1, h_sd.2.2,
    fun v A_v hA_v => bdlSafeSyndromeSet_singleSite_immunity k ψ_Z W_Z ψ_X W_X hWZ_fail hWX_fail v A_v hA_v,
    fun β hβ => gibbsFailureProb_bdlSafeSyndromeSet_le k W_Z W_X hWZ_card hWZ_wt hWX_card hWX_wt β hβ⟩

end
