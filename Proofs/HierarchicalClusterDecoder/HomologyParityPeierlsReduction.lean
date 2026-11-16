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

import Proofs.HierarchicalClusterDecoder.TannerVertexOwnership

/-!
# Homology-Projected Parity Decoders and Classical Peierls Barrier Reduction

Constructs the homology-projected decoder `decoderOfParity` from any logical parity decision rule and reduces classical free-energy barriers `HasEquilibriumFreeEnergyBarrier` to finite subsupport witness families (`hasEquilibriumFreeEnergyBarrier_of_witness_family`, `hasEquilibriumFreeEnergyBarrier_of_hasParityWitnessFamily`). Also establishes fiber-based witness lifting (`liftWitnessFamily_of_owner`) and base-scale witness existence (`hasParityWitnessFamily_of_no_weight_one_logical`).

## References

* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`), Proposition 5.3 (`prop:cluster-decoder-witness`)
* Part I, Section 5.3 (`subsec:walsh-fourier-peierls`), Theorem 5.5 (`thm:walsh-fourier-peierls`)
* Part II, Section 3.3 (`subsec:walsh-coset-peeling`), Proposition 3.5 (`prop:witness-coset-reduction`), Proposition 3.6 (`prop:walsh-coset-dominance`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Qubit Fiber Splitting and Witness-Family Free-Energy Barrier Reduction -/

/-- The 2-cochain embedding $\mathcal{F}_{\mathcal{R}_X}^2 : C^2_{(i-1)} \to C^2_{(i)}$ for $\mathcal{R}_X$. -/
def embedCoarseStepXMZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (S_coarse : M_Z → ZMod 2) :
    BDLStepXMZ pcode M → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (z0, _)) => S_coarse z0

/-- Projection of a fine 1-cochain `f : BDLStepXQ pcode M → ZMod 2` onto $C_X^1 = \text{BDLCX1}$. -/
def splitStepXQX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (f : BDLStepXQ pcode M → ZMod 2) :
    BDLStepXQ pcode M → ZMod 2
  | Sum.inl qX => f (Sum.inl qX)
  | Sum.inr _ => 0

/-- Projection of a fine 1-cochain `f : BDLStepXQ pcode M → ZMod 2` onto $C_Q^1 = \text{BDLCQ1}$. -/
def splitStepXQQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (f : BDLStepXQ pcode M → ZMod 2) :
    BDLStepXQ pcode M → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr qQ => f (Sum.inr qQ)

/-- Subadditivity of a sum of nonnegative reals over a `Finset.biUnion`. -/
lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (W : Finset α) (F : α → Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ x ∈ W.biUnion F, f x) ≤ ∑ a ∈ W, ∑ x ∈ F a, f x := by
  induction W using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h_un : (∑ x ∈ F a ∪ s.biUnion F, f x) ≤
        (∑ x ∈ F a, f x) + ∑ x ∈ s.biUnion F, f x := by
      have h_ui := Finset.sum_union_inter (s₁ := F a) (s₂ := s.biUnion F) (f := f)
      have h_inter : 0 ≤ ∑ x ∈ F a ∩ s.biUnion F, f x :=
        Finset.sum_nonneg (fun x _ => hf x)
      linarith
    linarith

/-- **Peierls Free-Energy Barrier Reduction from a Subsupport Witness Family (`hasEquilibriumFreeEnergyBarrier_of_witness_family`):** -/
theorem hasEquilibriumFreeEnergyBarrier_of_witness_family {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (dec : Decoder code)
    (W_valid : Finset (M_X → ZMod 2)) (w ΔF_target β : ℝ)
    (hβ : 0 ≤ β)
    (hw : ∀ c ∈ W_valid, w ≤ syndromeWeight c)
    (h_card : (W_valid.card : ℝ) * Real.exp (-β * w) ≤ Real.exp (-ΔF_target))
    (h_wit : ∀ s ∈ decoderFailureSet code dec, ∃ c ∈ W_valid, ∀ m : M_X, c m ≠ 0 → s m ≠ 0) :
    HasEquilibriumFreeEnergyBarrier code β ΔF_target := by
  refine ⟨dec, ?_⟩
  intro S_fail hS_fail
  let Z := ∑ u ∈ Finset.univ.image (syndrome code), Real.exp (-β * syndromeWeight u)
  have hZ_nonneg : 0 ≤ Z :=
    Finset.sum_nonneg (fun _ _ => le_of_lt (Real.exp_pos _))
  let F : (M_X → ZMod 2) → Finset (M_X → ZMod 2) :=
    fun c => S_fail.filter (fun s => ∀ m : M_X, c m ≠ 0 → s m ≠ 0)
  have h_cov : S_fail ⊆ W_valid.biUnion F := by
    intro s hs
    obtain ⟨c, hcW, hcs⟩ := h_wit s (hS_fail hs)
    exact Finset.mem_biUnion.mpr ⟨c, hcW, Finset.mem_filter.mpr ⟨hs, hcs⟩⟩
  have h_sum_biUnion : (∑ s ∈ S_fail, Real.exp (-β * syndromeWeight s)) ≤
      ∑ c ∈ W_valid, ∑ s ∈ F c, Real.exp (-β * syndromeWeight s) := by
    calc (∑ s ∈ S_fail, Real.exp (-β * syndromeWeight s))
      _ ≤ ∑ s ∈ W_valid.biUnion F, Real.exp (-β * syndromeWeight s) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_cov (fun _ _ _ => le_of_lt (Real.exp_pos _))
      _ ≤ ∑ c ∈ W_valid, ∑ s ∈ F c, Real.exp (-β * syndromeWeight s) :=
          sum_biUnion_le_of_nonneg W_valid F _ (fun _ => le_of_lt (Real.exp_pos _))
  have h_each_c : ∀ c ∈ W_valid,
      (∑ s ∈ F c, Real.exp (-β * syndromeWeight s)) ≤ Real.exp (-β * w) * Z := by
    intro c hcW
    have h_term : ∀ s ∈ F c,
        Real.exp (-β * syndromeWeight s) ≤
          Real.exp (-β * w) * Real.exp (-β * syndromeWeight (c + s)) := by
      intro s hsF
      have h_sub : ∀ m : M_X, c m ≠ 0 → s m ≠ 0 := (Finset.mem_filter.mp hsF).2
      have h_peel := (syndromeWeight_peel_of_subsupport s c h_sub).2
      have h_add_comm : s + c = c + s := add_comm s c
      rw [h_peel, h_add_comm]
      have h_le_wt : -β * (syndromeWeight c + syndromeWeight (c + s)) ≤
          -β * w + -β * syndromeWeight (c + s) := by
        have hcw := hw c hcW
        nlinarith
      calc Real.exp (-β * (syndromeWeight c + syndromeWeight (c + s)))
        _ ≤ Real.exp (-β * w + -β * syndromeWeight (c + s)) :=
            Real.exp_le_exp.mpr h_le_wt
        _ = Real.exp (-β * w) * Real.exp (-β * syndromeWeight (c + s)) :=
            Real.exp_add _ _
    have h_fc_sub : F c ⊆ Finset.univ.image (syndrome code) := by
      intro s hsF
      exact mem_image_syndrome_of_mem_decoderFailureSet code dec (hS_fail (Finset.mem_filter.mp hsF).1)
    calc (∑ s ∈ F c, Real.exp (-β * syndromeWeight s))
      _ ≤ ∑ s ∈ F c, (Real.exp (-β * w) * Real.exp (-β * syndromeWeight (c + s))) :=
          Finset.sum_le_sum h_term
      _ = Real.exp (-β * w) * ∑ s ∈ F c, Real.exp (-β * syndromeWeight (c + s)) := by
          rw [← Finset.mul_sum]
      _ ≤ Real.exp (-β * w) * ∑ u ∈ Finset.univ.image (syndrome code), Real.exp (-β * syndromeWeight (c + u)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
          exact Finset.sum_le_sum_of_subset_of_nonneg h_fc_sub (fun _ _ _ => le_of_lt (Real.exp_pos _))
      _ ≤ Real.exp (-β * w) * Z := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
          exact coset_syndromeWeight_sum_le code β hβ c
  calc (∑ s ∈ S_fail, Real.exp (-β * syndromeWeight s))
    _ ≤ ∑ c ∈ W_valid, ∑ s ∈ F c, Real.exp (-β * syndromeWeight s) := h_sum_biUnion
    _ ≤ ∑ _c ∈ W_valid, (Real.exp (-β * w) * Z) := Finset.sum_le_sum h_each_c
    _ = ((W_valid.card : ℝ) * Real.exp (-β * w)) * Z := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
    _ ≤ Real.exp (-ΔF_target) * Z := mul_le_mul_of_nonneg_right h_card hZ_nonneg
    _ = Z * Real.exp (-ΔF_target) := mul_comm _ _

/-! ## 2. Homology-Projected Parity Decoder and Coarse Cocycle Identification -/

/-- Chosen raw recovery 1-chain `rawRep code s : Q → ZMod 2`. -/
noncomputable def rawRep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (s : M_X → ZMod 2) : Q → ZMod 2 :=
  if s = 0 then 0
  else if h : ∃ e : Q → ZMod 2, syndrome code e = s then Classical.choose h
  else 0

/-- Proves that `rawRep code s` has syndrome equal to `s` for any `s ∈ Set.range (syndrome code)`. -/
lemma syndrome_rawRep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (e : Q → ZMod 2) :
    syndrome code (rawRep code (syndrome code e)) = syndrome code e := by
  dsimp [rawRep]
  by_cases hs : syndrome code e = 0
  · rw [if_pos hs, map_zero, hs]
  · have hex : ∃ e' : Q → ZMod 2, syndrome code e' = syndrome code e := ⟨e, rfl⟩
    rw [if_neg hs, dif_pos hex]
    exact Classical.choose_spec hex

/-- Base recovery 1-chain `baseRep code L_Z L_X s : Q → ZMod 2` normalized so `dualPairing _ L_X = 0`. -/
noncomputable def baseRep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2) (s : M_X → ZMod 2) : Q → ZMod 2 :=
  fun q => rawRep code s q + dualPairing (rawRep code s) L_X * L_Z q

/-- Proves that `baseRep` has syndrome equal to `s`. -/
lemma syndrome_baseRep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_syn_Z : syndrome code L_Z = 0) (e : Q → ZMod 2) :
    syndrome code (baseRep code L_Z L_X (syndrome code e)) = syndrome code e := by
  change syndrome code (rawRep code (syndrome code e) +
    fun q => dualPairing (rawRep code (syndrome code e)) L_X * L_Z q) = _
  rw [map_add, syndrome_rawRep, syndrome_smul_zmod2, h_syn_Z]
  ext m; simp

/-- Proves that `baseRep` has zero symplectic pairing with `L_X`. -/
lemma dualPairing_baseRep_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_pair : dualPairing L_Z L_X = 1) (s : M_X → ZMod 2) :
    dualPairing (baseRep code L_Z L_X s) L_X = 0 := by
  change dualPairing (rawRep code s + fun q => dualPairing (rawRep code s) L_X * L_Z q) L_X = 0
  rw [dualPairing_add_left_zmod2, dualPairing_smul_left_zmod2, h_pair, mul_one]
  exact zmod2_add_self _

/-- Decoder `decoderOfParity code L_Z L_X h_hom ψ` determined by a logical parity decision rule `ψ`. -/
noncomputable def decoderOfParity {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_hom : HasUniqueLogicalHomology code L_Z L_X)
    (ψ : (M_X → ZMod 2) → ZMod 2) : Decoder code where
  decode s := fun q => baseRep code L_Z L_X s q + ψ s * L_Z q
  h_correct e := by
    change syndrome code (baseRep code L_Z L_X (syndrome code e) +
      fun q => ψ (syndrome code e) * L_Z q) = _
    rw [map_add, syndrome_baseRep code L_Z L_X h_hom.h_syn_Z e,
        syndrome_smul_zmod2, h_hom.h_syn_Z]
    ext m; simp

/-- Proves that `decoderOfParity` produces a correction whose pairing with `L_X` matches `ψ s`. -/
lemma dualPairing_decoderOfParity {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_hom : HasUniqueLogicalHomology code L_Z L_X)
    (ψ : (M_X → ZMod 2) → ZMod 2) (s : M_X → ZMod 2) :
    dualPairing ((decoderOfParity code L_Z L_X h_hom ψ).decode s) L_X = ψ s := by
  change dualPairing (baseRep code L_Z L_X s + fun q => ψ s * L_Z q) L_X = ψ s
  rw [dualPairing_add_left_zmod2, dualPairing_baseRep_eq_zero code L_Z L_X h_hom.h_pair s,
      zero_add, dualPairing_smul_left_zmod2, h_hom.h_pair, mul_one]

/-- Failure of `decoderOfParity` at syndrome `s` implies parity rule failure at some single qubit `q`. -/
lemma parityRuleFails_of_mem_decoderFailureSet {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_hom : HasUniqueLogicalHomology code L_Z L_X)
    (ψ : (M_X → ZMod 2) → ZMod 2) {s : M_X → ZMod 2}
    (hs : s ∈ decoderFailureSet code (decoderOfParity code L_Z L_X h_hom ψ)) :
    (∃ e_err : Q → ZMod 2, syndrome code e_err = s) ∧
    ∃ q : Q, ψ (s + syndrome code (singleQubit q)) ≠ ψ s + L_X q := by
  rcases hs with ⟨⟨e_err, rfl⟩, E, ⟨q, rfl⟩, h_no_c2⟩
  refine ⟨⟨e_err, rfl⟩, q, ?_⟩
  intro h_eq
  let dec := decoderOfParity code L_Z L_X h_hom ψ
  let s := syndrome code e_err
  let s' := s + syndrome code (singleQubit q)
  let g := dec.decode s + singleQubit q - dec.decode s'
  have hs' : s' = syndrome code (e_err + singleQubit q) := by
    dsimp [s', s]; rw [map_add]
  have hg_syn : syndrome code g = 0 := by
    dsimp [g]
    rw [sub_eq_add_neg, neg_eq_self_zmod2_pi, map_add, map_add,
        dec.h_correct e_err, hs', dec.h_correct (e_err + singleQubit q), ← hs']
    ext m
    dsimp [s']
    have h1 := zmod2_add_self (s m)
    have h2 := zmod2_add_self (syndrome code (singleQubit q) m)
    linear_combination h1 + h2
  have hg_pair : dualPairing g L_X = 0 := by
    dsimp [g]
    rw [sub_eq_add_neg, neg_eq_self_zmod2_pi,
        dualPairing_add_left_zmod2, dualPairing_add_left_zmod2,
        dualPairing_decoderOfParity, dualPairing_singleQubit_left,
        dualPairing_decoderOfParity, h_eq]
    have h1 := zmod2_add_self (ψ s)
    have h2 := zmod2_add_self (L_X q)
    linear_combination h1 + h2
  obtain ⟨c2, hc2⟩ := (h_hom.h_exact_Z g hg_syn).mpr hg_pair
  exact h_no_c2 c2 hc2

/-- Shows `dualPairing (liftCylinderLZ L_Z) (checkGen (dualCode (bdlCylinderStepX pcode M)) d2) = 0`. -/
lemma dualPairing_liftCylinderLZ_checkGen_zero_of_inl_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L_Z : Q → ZMod 2)
    (d2 : BDLStepXMX pcode M → ZMod 2)
    (hd2 : ∀ x0 : M_X, d2 (Sum.inl (x0, 0)) = 0) :
    dualPairing (liftCylinderLZ pcode M L_Z)
      (checkGen (dualCode (bdlCylinderStepX pcode M)) d2) = 0 := by
  rw [dualPairing_checkGen_dual, syndrome_liftCylinderLZ_eq_embedCoarse]
  apply Finset.sum_eq_zero
  intro mX _
  rcases mX with ⟨x0, b⟩ | ⟨sv, b⟩
  · fin_cases b
    · dsimp; rw [hd2 x0, zero_mul]
    · simp [embedCoarseStepXMX]
    · simp [embedCoarseStepXMX]
  · dsimp [embedCoarseStepXMX]; rw [mul_zero]

/-- Identifies `coarseProjCocycle pcode M h` with `projCylinderLX pcode M h`. -/
lemma coarseProjCocycle_eq_projCylinderLX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) :
    coarseProjCocycle pcode M h = projCylinderLX pcode M h := by
  ext q0
  have h_rhs : dualPairing (liftCylinderLZ pcode M (singleQubit q0))
      (cylinderResidualCocycle pcode M h) = projCylinderLX pcode M h q0 := by
    dsimp [cylinderResidualCocycle, apexResidualCocycle, projCylinderLX]
    rw [dualPairing_add_right_zmod2, dualPairing_add_right_zmod2,
        dualPairing_liftCylinderLZ_checkGen_zero_of_inl_zero pcode M (singleQubit q0)
          (apexRadialCocycle pcode M h) (fun _ => rfl),
        dualPairing_liftCylinderLZ_checkGen_zero_of_inl_zero pcode M (singleQubit q0)
          (layer1ConeCochain pcode M (coneLinkVal pcode M h)) (fun _ => rfl),
        add_zero, add_zero]
  rw [← h_rhs]
  dsimp [dualPairing]
  rw [Fintype.sum_sum_type]
  have h_inl : (∑ qX : BDLCX1 pcode M,
      liftCylinderLZ pcode M (singleQubit q0) (Sum.inl qX) *
        cylinderResidualCocycle pcode M h (Sum.inl qX)) = 0 := by
    apply Finset.sum_eq_zero
    intro qX _
    rcases qX with ⟨rv, b⟩ | _
    · fin_cases b
      · have h_rad0 : cylinderResidualCocycle pcode M h (Sum.inl (Sum.inl (rv, 0))) = 0 := by
          change apexResidualCocycle pcode M h (Sum.inl (Sum.inl (rv, 0))) +
            checkGen (dualCode (bdlCylinderStepX pcode M))
              (layer1ConeCochain pcode M (coneLinkVal pcode M h)) (Sum.inl (Sum.inl (rv, 0))) = 0
          rw [h1_radial_eq_zero, checkGen_dual_layer1ConeCochain_inl]
          simp
        dsimp; rw [h_rad0, mul_zero]
      · dsimp [liftCylinderLZ]; simp
      · dsimp [liftCylinderLZ]; simp
    · dsimp [liftCylinderLZ]; simp
  rw [h_inl, zero_add]
  rw [Finset.sum_eq_single (Sum.inl q0, (0 : Fin 3))]
  · dsimp [liftCylinderLZ, xq0LZ, singleQubit, coarseProjCocycle]
    simp
  · intro qQ _ hne
    rcases qQ with ⟨v0, b⟩
    fin_cases b
    · rcases v0 with q | _
      · have hq_ne : q ≠ q0 := fun hq => hne (by subst hq; rfl)
        dsimp [liftCylinderLZ, xq0LZ, singleQubit]
        rw [if_neg hq_ne, zero_mul]
      · dsimp [liftCylinderLZ, xq0LZ]; simp
    · dsimp [liftCylinderLZ]; simp
    · dsimp [liftCylinderLZ]; simp
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-! ## 3. Lifted Logical Dichotomies and Parity Witness Family Lifting -/

/-- Characterizes `(liftCylinderLZ pcode M L_Z) q_fine`. -/
lemma liftCylinderLZ_apply_dichotomy {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q_fine : BDLStepXQ pcode M) :
    (∀ L_Z : Q → ZMod 2, liftCylinderLZ pcode M L_Z q_fine = 0) ∨
    (∃ q0 : Q, ∀ L_Z : Q → ZMod 2, liftCylinderLZ pcode M L_Z q_fine = L_Z q0) := by
  rcases q_fine with ⟨⟨rv, b⟩ | _⟩ | ⟨v0, b⟩
  · fin_cases b
    · rcases h_v : rv.val.val.1.val.2 with q0 | _
      · by_cases hx : pcode.checkX rv.val.val.1.val.1 q0 = 0
        · exact Or.inl (fun L_Z => by dsimp [liftCylinderLZ, boundaryX0LinkLZ]; rw [h_v]; dsimp; rw [hx, zero_mul])
        · have hx1 : pcode.checkX rv.val.val.1.val.1 q0 = 1 := by
            revert hx; generalize pcode.checkX rv.val.val.1.val.1 q0 = a; decide +revert
          exact Or.inr ⟨q0, fun L_Z => by dsimp [liftCylinderLZ, boundaryX0LinkLZ]; rw [h_v]; dsimp; rw [hx1, one_mul]⟩
      · exact Or.inl (fun L_Z => by dsimp [liftCylinderLZ, boundaryX0LinkLZ]; rw [h_v])
    · exact Or.inl (fun _ => rfl)
    · exact Or.inl (fun _ => rfl)
  · exact Or.inl (fun _ => rfl)
  · fin_cases b
    · rcases v0 with q0 | _
      · exact Or.inr ⟨q0, fun _ => rfl⟩
      · exact Or.inl (fun _ => rfl)
    · exact Or.inl (fun _ => rfl)
    · exact Or.inl (fun _ => rfl)

/-- Characterizes `projCylinderLX pcode M (singleQubit q_fine)`. -/
lemma projCylinderLX_singleQubit_dichotomy {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (L_Z : Q → ZMod 2) (q_fine : BDLStepXQ pcode M) :
    (projCylinderLX pcode M (singleQubit q_fine) = 0 ∧ liftCylinderLZ pcode M L_Z q_fine = 0) ∨
    (∃ q0 : Q, projCylinderLX pcode M (singleQubit q_fine) = singleQubit q0 ∧
      liftCylinderLZ pcode M L_Z q_fine = L_Z q0) := by
  have h_eq : ∀ q' : Q, projCylinderLX pcode M (singleQubit q_fine) q' =
      liftCylinderLZ pcode M (singleQubit q') q_fine := by
    intro q'
    dsimp [projCylinderLX]
    exact dualPairing_singleQubit_right _ _
  rcases liftCylinderLZ_apply_dichotomy pcode M q_fine with h0 | ⟨q0, hq0⟩
  · refine Or.inl ⟨?_, h0 L_Z⟩
    ext q'; rw [h_eq, h0]; rfl
  · refine Or.inr ⟨q0, ?_, hq0 L_Z⟩
    ext q'; rw [h_eq, hq0]; dsimp [singleQubit]
    by_cases h : q' = q0
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]

/-- Inductive subsupport witness family package for a CSS code `(code, L_Z, L_X)`. -/
def HasParityWitnessFamily {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (_L_Z L_X : Q → ZMod 2) (w N : ℕ) : Prop :=
  ∃ (ψ : (M_X → ZMod 2) → ZMod 2) (W : Finset (M_X → ZMod 2)),
    ψ 0 = 0 ∧
    W.card ≤ N ∧
    (∀ c ∈ W, (w : ℝ) ≤ syndromeWeight c) ∧
    (∀ (e_err : Q → ZMod 2) (q : Q),
      ψ (syndrome code e_err + syndrome code (singleQubit q)) ≠ ψ (syndrome code e_err) + L_X q →
      ∃ c ∈ W, ∀ m : M_X, c m ≠ 0 → syndrome code e_err m ≠ 0)

/-- Selects a subset of size `w` from the support of `c0`. -/
noncomputable def chooseSupp {M_0 : Type} [Fintype M_0] [DecidableEq M_0]
    (w : ℕ) (c0 : M_0 → ZMod 2) : Finset M_0 :=
  if h : w ≤ (Finset.univ.filter (fun m0 => c0 m0 ≠ 0)).card then
    Classical.choose (Finset.exists_subset_card_eq h)
  else ∅

/-- Constructs the fine witness 1-chain corresponding to a coarse witness `T_0` and fiber selector `f`. -/
def mkFineWitness {M_0 M_1 : Type} [DecidableEq M_0] [DecidableEq M_1]
    (owner : M_1 → M_0) (T_0 : Finset M_0) (f : (m0 : M_0) → m0 ∈ T_0 → M_1) : M_1 → ZMod 2 :=
  fun m1 => if h : owner m1 ∈ T_0 then (if m1 = f (owner m1) h then 1 else 0) else 0

/-- Lifts a coarse witness pool `W_0` across a fiber map `owner : M_1 → M_0` with fiber bound `≤ F`. -/
lemma liftWitnessFamily_of_owner {M_0 M_1 : Type}
    [Fintype M_0] [DecidableEq M_0] [Fintype M_1] [DecidableEq M_1]
    (owner : M_1 → M_0) (F w N_0 : ℕ)
    (hF : ∀ m0 : M_0, (Finset.univ.filter (fun m1 : M_1 => owner m1 = m0)).card ≤ F)
    (W_0 : Finset (M_0 → ZMod 2))
    (h_card : W_0.card ≤ N_0)
    (h_wt : ∀ c0 ∈ W_0, (w : ℝ) ≤ syndromeWeight c0) :
    ∃ W_1 : Finset (M_1 → ZMod 2),
      W_1.card ≤ N_0 * F ^ w ∧
      (∀ c1 ∈ W_1, (w : ℝ) ≤ syndromeWeight c1) ∧
      (∀ (s1 : M_1 → ZMod 2) (c0 : M_0 → ZMod 2), c0 ∈ W_0 →
        (∀ m0 : M_0, c0 m0 ≠ 0 → ∃ m1 : M_1, owner m1 = m0 ∧ s1 m1 ≠ 0) →
        ∃ c1 ∈ W_1, ∀ m1 : M_1, c1 m1 ≠ 0 → s1 m1 ≠ 0) := by
  classical
  let fiber := fun m0 : M_0 => Finset.univ.filter (fun m1 : M_1 => owner m1 = m0)
  let W_1 : Finset (M_1 → ZMod 2) :=
    W_0.biUnion (fun c0 =>
      ((chooseSupp w c0).pi fiber).image (mkFineWitness owner (chooseSupp w c0)))
  refine ⟨W_1, ?_, ?_, ?_⟩
  · calc
      W_1.card ≤ ∑ c0 ∈ W_0, (((chooseSupp w c0).pi fiber).image (mkFineWitness owner (chooseSupp w c0))).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ c0 ∈ W_0, F ^ w := by
        refine Finset.sum_le_sum (fun c0 hc0 => ?_)
        have hw_real := h_wt c0 hc0
        dsimp [syndromeWeight] at hw_real
        have hw : w ≤ (Finset.univ.filter (fun m0 => c0 m0 ≠ 0)).card := by
          exact_mod_cast hw_real
        have hT : (chooseSupp w c0).card = w := by
          dsimp [chooseSupp]; rw [dif_pos hw]
          exact (Classical.choose_spec (Finset.exists_subset_card_eq hw)).2
        calc
          (((chooseSupp w c0).pi fiber).image (mkFineWitness owner (chooseSupp w c0))).card
            ≤ ((chooseSupp w c0).pi fiber).card := Finset.card_image_le
          _ = ∏ m0 ∈ chooseSupp w c0, (fiber m0).card := Finset.card_pi _ _
          _ ≤ ∏ _m0 ∈ chooseSupp w c0, F := Finset.prod_le_prod' (fun m0 _ => hF m0)
          _ = F ^ (chooseSupp w c0).card := by rw [Finset.prod_const]
          _ = F ^ w := by rw [hT]
      _ = W_0.card * F ^ w := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ N_0 * F ^ w := Nat.mul_le_mul_right (F ^ w) h_card
  · intro c1 hc1
    rcases Finset.mem_biUnion.mp hc1 with ⟨c0, hc0, hc1_img⟩
    rcases Finset.mem_image.mp hc1_img with ⟨f, hf, rfl⟩
    have hw_real := h_wt c0 hc0
    dsimp [syndromeWeight] at hw_real
    have hw : w ≤ (Finset.univ.filter (fun m0 => c0 m0 ≠ 0)).card := by
      exact_mod_cast hw_real
    have hT : (chooseSupp w c0).card = w := by
      dsimp [chooseSupp]; rw [dif_pos hw]
      exact (Classical.choose_spec (Finset.exists_subset_card_eq hw)).2
    have hf_owner : ∀ m0 (hm0 : m0 ∈ chooseSupp w c0), owner (f m0 hm0) = m0 := by
      intro m0 hm0
      exact (Finset.mem_filter.mp (Finset.mem_pi.mp hf m0 hm0)).2
    let imgSet := (chooseSupp w c0).attach.image (fun x => f x.1 x.2)
    have h_sub : imgSet ⊆ Finset.univ.filter (fun m1 => mkFineWitness owner (chooseSupp w c0) f m1 ≠ 0) := by
      intro m1 hm1
      rcases Finset.mem_image.mp hm1 with ⟨⟨m0, hm0⟩, _, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      dsimp [mkFineWitness]
      have hm0' : owner (f m0 hm0) ∈ chooseSupp w c0 := by rw [hf_owner m0 hm0]; exact hm0
      rw [dif_pos hm0']
      have heq : f m0 hm0 = f (owner (f m0 hm0)) hm0' := by
        congr 1
        exact (hf_owner m0 hm0).symm
      rw [if_pos heq]
      decide
    have h_inj : Function.Injective (fun x : {m0 // m0 ∈ chooseSupp w c0} => f x.1 x.2) := by
      intro x y hxy
      apply Subtype.ext
      calc
        x.1 = owner (f x.1 x.2) := (hf_owner x.1 x.2).symm
        _ = owner (f y.1 y.2) := congr_arg owner hxy
        _ = y.1 := hf_owner y.1 y.2
    have h_card_img : imgSet.card = w := by
      rw [Finset.card_image_of_injective _ h_inj, Finset.card_attach, hT]
    have h_le_card : w ≤ (Finset.univ.filter (fun m1 => mkFineWitness owner (chooseSupp w c0) f m1 ≠ 0)).card := by
      calc
        w = imgSet.card := h_card_img.symm
        _ ≤ (Finset.univ.filter (fun m1 => mkFineWitness owner (chooseSupp w c0) f m1 ≠ 0)).card :=
          Finset.card_le_card h_sub
    dsimp [syndromeWeight]
    exact_mod_cast h_le_card
  · intro s1 c0 hc0 h_act
    have hw_real := h_wt c0 hc0
    dsimp [syndromeWeight] at hw_real
    have hw : w ≤ (Finset.univ.filter (fun m0 => c0 m0 ≠ 0)).card := by
      exact_mod_cast hw_real
    have hT_sub : chooseSupp w c0 ⊆ Finset.univ.filter (fun m0 => c0 m0 ≠ 0) := by
      dsimp [chooseSupp]; rw [dif_pos hw]
      exact (Classical.choose_spec (Finset.exists_subset_card_eq hw)).1
    let f : (m0 : M_0) → m0 ∈ chooseSupp w c0 → M_1 :=
      fun m0 hm0 => Classical.choose (h_act m0 (Finset.mem_filter.mp (hT_sub hm0)).2)
    have hf_spec : ∀ m0 (hm0 : m0 ∈ chooseSupp w c0), owner (f m0 hm0) = m0 ∧ s1 (f m0 hm0) ≠ 0 :=
      fun m0 hm0 => Classical.choose_spec (h_act m0 (Finset.mem_filter.mp (hT_sub hm0)).2)
    have hf_mem : f ∈ (chooseSupp w c0).pi fiber := by
      rw [Finset.mem_pi]
      intro m0 hm0
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hf_spec m0 hm0).1⟩
    refine ⟨mkFineWitness owner (chooseSupp w c0) f, ?_, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨c0, hc0, Finset.mem_image.mpr ⟨f, hf_mem, rfl⟩⟩
    · intro m1 hm1
      dsimp [mkFineWitness] at hm1
      split_ifs at hm1 with h1 h2
      · rw [h2]
        exact (hf_spec (owner m1) h1).2
      · exact False.elim (hm1 rfl)
      · exact False.elim (hm1 rfl)

/-- Derives `HasEquilibriumFreeEnergyBarrier` from `HasParityWitnessFamily` and `HasUniqueLogicalHomology`. -/
lemma hasEquilibriumFreeEnergyBarrier_of_hasParityWitnessFamily {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_hom : HasUniqueLogicalHomology code L_Z L_X)
    (w N : ℕ) (β ΔF_target : ℝ) (hβ : 0 ≤ β)
    (h_wit : HasParityWitnessFamily code L_Z L_X w N)
    (h_bound : (N : ℝ) * Real.exp (-β * (w : ℝ)) ≤ Real.exp (-ΔF_target)) :
    HasEquilibriumFreeEnergyBarrier code β ΔF_target := by
  rcases h_wit with ⟨ψ, W, _, hW_card, hW_wt, hW_fail⟩
  apply hasEquilibriumFreeEnergyBarrier_of_witness_family code
    (decoderOfParity code L_Z L_X h_hom ψ) W (w : ℝ) ΔF_target β hβ hW_wt
  · calc
      (W.card : ℝ) * Real.exp (-β * (w : ℝ))
        ≤ (N : ℝ) * Real.exp (-β * (w : ℝ)) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hW_card) (Real.exp_nonneg _)
      _ ≤ Real.exp (-ΔF_target) := h_bound
  · intro s hs
    obtain ⟨⟨e_err, rfl⟩, q, hq_fail⟩ :=
      parityRuleFails_of_mem_decoderFailureSet code L_Z L_X h_hom ψ hs
    exact hW_fail e_err q hq_fail

/-- Establishes `HasParityWitnessFamily code L_Z L_X 1 (Fintype.card M_X)` for any code without weight-1 logicals. -/
theorem hasParityWitnessFamily_of_no_weight_one_logical {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_Z L_X : Q → ZMod 2)
    (h_no_wt1 : ∀ q : Q, syndrome code (singleQubit q) = 0 → L_X q = 0)
    (h_dist : ∀ q1 q2 : Q, syndrome code (singleQubit q1) = syndrome code (singleQubit q2) → L_X q1 = L_X q2) :
    HasParityWitnessFamily code L_Z L_X 1 (Fintype.card M_X) := by
  classical
  let ψ : (M_X → ZMod 2) → ZMod 2 :=
    fun s => if h : ∃ q : Q, s = syndrome code (singleQubit q) then L_X (Classical.choose h) else 0
  let W : Finset (M_X → ZMod 2) := Finset.univ.image (singleQubit : M_X → (M_X → ZMod 2))
  refine ⟨ψ, W, ?_, ?_, ?_, ?_⟩
  · dsimp [ψ]
    split_ifs with h
    · exact h_no_wt1 (Classical.choose h) (Classical.choose_spec h).symm
    · rfl
  · calc
      W.card ≤ (Finset.univ : Finset M_X).card := Finset.card_image_le
      _ = Fintype.card M_X := Finset.card_univ
  · intro c hc
    rcases Finset.mem_image.mp hc with ⟨m, _, rfl⟩
    dsimp [syndromeWeight]
    have h_mem : m ∈ Finset.univ.filter (fun m' : M_X => singleQubit m m' ≠ 0) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ m, by simp [singleQubit]⟩
    have h_pos : 1 ≤ (Finset.univ.filter (fun m' : M_X => singleQubit m m' ≠ 0)).card :=
      Finset.card_pos.mpr ⟨m, h_mem⟩
    exact_mod_cast h_pos
  · intro e_err q h_fail
    by_cases hs0 : syndrome code e_err = 0
    · exfalso
      apply h_fail
      rw [hs0, zero_add]
      have hψ0 : ψ 0 = 0 := by
        dsimp [ψ]
        split_ifs with h
        · exact h_no_wt1 (Classical.choose h) (Classical.choose_spec h).symm
        · rfl
      rw [hψ0, zero_add]
      dsimp [ψ]
      have h_ex : ∃ q' : Q, syndrome code (singleQubit q) = syndrome code (singleQubit q') := ⟨q, rfl⟩
      rw [dif_pos h_ex]
      exact h_dist (Classical.choose h_ex) q (Classical.choose_spec h_ex).symm
    · have h_ex : ∃ m : M_X, syndrome code e_err m ≠ 0 := by
        by_contra h_all
        push_neg at h_all
        exact hs0 (funext h_all)
      rcases h_ex with ⟨m, hm⟩
      refine ⟨singleQubit m, Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩, ?_⟩
      intro m' hm'
      dsimp [singleQubit] at hm'
      split_ifs at hm' with heq
      · subst heq; exact hm
      · exact False.elim (hm' rfl)

/-- Characterizes `projCylinderLX pcode M (singleQubit q) q0 ≠ 0`. -/
lemma liftCylinderLZ_singleQubit_eq_one_imp {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q) (q : BDLStepXQ pcode M)
    (h : projCylinderLX pcode M (singleQubit q) q0 ≠ 0) :
    (∃ (rv : RadialVertex pcode M),
      q = Sum.inl (Sum.inl (rv, 0)) ∧
      rv.val.val.1.val.2 = Sum.inl q0 ∧
      pcode.checkX rv.val.val.1.val.1 q0 ≠ 0) ∨
    q = Sum.inr (Sum.inl q0, 0) := by
  have h_eq : projCylinderLX pcode M (singleQubit q) q0 =
      liftCylinderLZ pcode M (singleQubit q0) q := dualPairing_singleQubit_right _ _
  rw [h_eq] at h
  rcases q with ⟨⟨rv, b⟩ | _⟩ | ⟨v0, b⟩
  · fin_cases b
    · rcases h_v : rv.val.val.1.val.2 with q' | _
      · dsimp [liftCylinderLZ, boundaryX0LinkLZ] at h
        rw [h_v] at h
        (try dsimp at h)
        by_cases hX : pcode.checkX rv.val.val.1.val.1 q' ≠ 0
        · by_cases hq : q' = q0
          · subst hq
            exact Or.inl ⟨rv, rfl, h_v, hX⟩
          · rw [singleQubit, if_neg hq, mul_zero] at h; exact False.elim (h rfl)
        · rw [Classical.not_not.mp hX, zero_mul] at h; exact False.elim (h rfl)
      · dsimp [liftCylinderLZ, boundaryX0LinkLZ] at h; rw [h_v] at h; exact False.elim (h rfl)
    · exact False.elim (h rfl)
    · exact False.elim (h rfl)
  · exact False.elim (h rfl)
  · fin_cases b
    · rcases v0 with q' | _
      · dsimp [liftCylinderLZ, xq0LZ, singleQubit] at h
        by_cases hq : q' = q0
        · subst hq; exact Or.inr rfl
        · rw [if_neg hq] at h; exact False.elim (h rfl)
      · exact False.elim (h rfl)
    · exact False.elim (h rfl)
    · exact False.elim (h rfl)

/-- Evaluates `syndrome code (singleQubit q) m` to `code.checkX m q`. -/
lemma syndrome_singleQubit_apply {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (q : Q) (m : M_X) :
    syndrome code (singleQubit q) m = code.checkX m q := by
  dsimp [syndrome, f2Syndrome, singleQubit]
  rw [Finset.sum_eq_single q]
  · simp
  · intro _ _ hne; rw [if_neg hne, mul_zero]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

end BDLDecoder
end WeldedHierarchy
