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

import Proofs.HierarchicalClusterDecoder.Stage1CylinderCleaner

/-!
# Stage-2 Star Cleaner Candidates and Three-Layer Complement Symmetry

Constructs the two local Stage-2 star cleaner candidates (`starCleanerCandidate0`, `starCleanerCandidate1`) on each three-layer star gadget and computes their arm and vertical coboundaries (`syndrome_starCleanerCandidate0_arm`, `syndrome_starCleanerCandidate0_vert`). Establishes three-layer complement weight duality (`wt3_layerComplementChain`, `vertCost3_layerComplementChain`) and packages Stage-1 cleaner existence (`stage1_cylinder_cleaner_exists`).

## References

* Part I, Section 4.2 (`subsec:stage1-cylinder`), Lemma 4.1 (`lem:stage1-cylinder-cleaner`)
* Part I, Section 4.3 (`subsec:stage2-star`), Lemma 4.2 (`lem:stage2-star-cleaner`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Three-Copy Pointwise Weights and Star Restriction -/

/-- 3-layer Hamming weight `wt3 t` of a 3-bit vector `t : Fin 3 → ZMod 2`. -/
def wt3 (t : Fin 3 → ZMod 2) : ℕ :=
  (if t 0 ≠ 0 then 1 else 0) + (if t 1 ≠ 0 then 1 else 0) + (if t 2 ≠ 0 then 1 else 0)

/-- Vertical coboundary cost `vertCost3 t` at an arm endpoint (`|(t 0 + t 1, t 0 + t 2)|`). -/
def vertCost3 (t : Fin 3 → ZMod 2) : ℕ :=
  (if t 0 + t 1 ≠ 0 then 1 else 0) + (if t 0 + t 2 ≠ 0 then 1 else 0)

/-- All-ones 3-bit vector `ones3 = (1, 1, 1)`. -/
def ones3 : Fin 3 → ZMod 2 := fun _ => 1

/-- Upper bound `wt3 v ≤ 3` for any 3-layer vector `v : Fin 3 → ZMod 2`. -/
lemma wt3_le_three (v : Fin 3 → ZMod 2) : wt3 v ≤ 3 := by
  dsimp only [wt3]
  split_ifs <;> omega

/-- `wt3 v = 0` if and only if `v = 0`. -/
lemma wt3_eq_zero_iff (v : Fin 3 → ZMod 2) : wt3 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    dsimp only [wt3] at h
    have h0 : v 0 = 0 := by by_contra hb; rw [if_pos hb] at h; omega
    have h1 : v 1 = 0 := by by_contra hb; rw [if_pos hb] at h; omega
    have h2 : v 2 = 0 := by by_contra hb; rw [if_pos hb] at h; omega
    ext b
    fin_cases b
    · exact h0
    · exact h1
    · exact h2
  · rintro rfl
    rfl

/-- Subadditivity of 3-layer Hamming weight: `wt3 (v + w) ≤ wt3 v + wt3 w`. -/
lemma wt3_add_le (v w : Fin 3 → ZMod 2) : wt3 (v + w) ≤ wt3 v + wt3 w := by
  simp only [wt3, Pi.add_apply]
  have h0 := zmod2_ite_add_le (v 0) (w 0)
  have h1 := zmod2_ite_add_le (v 1) (w 1)
  have h2 := zmod2_ite_add_le (v 2) (w 2)
  omega

/-- Single-bit complement identity `|a + 1|_Z + |a|_Z = 1` on `ZMod 2`. -/
lemma zmod2_ite_add_one (a : ZMod 2) :
    (if a + 1 ≠ 0 then 1 else 0) + (if a ≠ 0 then 1 else 0) = 1 := by
  fin_cases a <;> decide

/-- **Layer-Complement Weight Identity (`wt3_add_ones3`)**:
    Flipping all 3 layers via `ones3 = (1, 1, 1)` sends weight `wt3 v` to `3 - wt3 v`. -/
lemma wt3_add_ones3 (v : Fin 3 → ZMod 2) : wt3 (v + ones3) + wt3 v = 3 := by
  have h_ones : ∀ b : Fin 3, (v + ones3) b = v b + 1 := fun _ => rfl
  unfold wt3
  simp only [h_ones]
  have h0 := zmod2_ite_add_one (v 0)
  have h1 := zmod2_ite_add_one (v 1)
  have h2 := zmod2_ite_add_one (v 2)
  omega

/-- **Vertical Coboundary Invariance (`vertCost3_add_ones3`)**:
    The vertical coboundary cost `vertCost3` is invariant under the layer-complement shift `t ↦ t + ones3`. -/
lemma vertCost3_add_ones3 (t : Fin 3 → ZMod 2) : vertCost3 (t + ones3) = vertCost3 t := by
  have h01 : (t 0 + 1) + (t 1 + 1) = t 0 + t 1 := by
    have h2 := zmod2_add_self (1 : ZMod 2); linear_combination h2
  have h02 : (t 0 + 1) + (t 2 + 1) = t 0 + t 2 := by
    have h2 := zmod2_add_self (1 : ZMod 2); linear_combination h2
  unfold vertCost3
  simp only [ones3, Pi.add_apply, h01, h02]

/-- **Non-Uniform Layer Vertical Syndrome Lower Bound (`vertCost3_pos_of_wt3_eq_one_or_two`)**:
    Whenever `1 ≤ wt3 t ≤ 2`, at least one vertical check `(t 0 + t 1, t 0 + t 2)` is active (`1 ≤ vertCost3 t`). -/
lemma vertCost3_pos_of_wt3_eq_one_or_two (t : Fin 3 → ZMod 2)
    (h1 : 1 ≤ wt3 t) (h2 : wt3 t ≤ 2) : 1 ≤ vertCost3 t := by
  by_contra h_zero
  have hv0 : vertCost3 t = 0 := by omega
  have h01 : t 0 + t 1 = 0 := by
    by_contra hne; dsimp only [vertCost3] at hv0; rw [if_pos hne] at hv0; omega
  have h02 : t 0 + t 2 = 0 := by
    by_contra hne; dsimp only [vertCost3] at hv0; rw [if_pos hne] at hv0; omega
  have ht1 : t 1 = t 0 := by
    have h_self := zmod2_add_self (t 0); linear_combination h01 - h_self
  have ht2 : t 2 = t 0 := by
    have h_self := zmod2_add_self (t 0); linear_combination h02 - h_self
  have h_wt : wt3 t = 3 * (if t 0 ≠ 0 then 1 else 0) := by
    dsimp only [wt3]; rw [ht1, ht2]; omega
  split_ifs at h_wt <;> omega

/-- **Pointwise Star Arm Bound for `wt3 u ≤ 1` (`star_arm_pointwise_le_one`)**. -/
lemma star_arm_pointwise_le_one (u t : Fin 3 → ZMod 2) (hu : wt3 u ≤ 1) :
    (if u = 0 then 3 * wt3 t else 2 * wt3 t + wt3 (t + ones3)) ≤
      4 * (wt3 (t + u) + vertCost3 t) := by
  by_cases hu0 : u = 0
  · rw [if_pos hu0, hu0, add_zero]
    omega
  · rw [if_neg hu0]
    have hu_pos : 1 ≤ wt3 u := by
      by_contra h_lt
      exact hu0 ((wt3_eq_zero_iff u).mp (by omega))
    have hu1 : wt3 u = 1 := by omega
    have h_t_eq : t = (t + u) + u := by
      ext b; simp only [Pi.add_apply]; have h2 := zmod2_add_self (u b); linear_combination -h2
    have h_u_eq : u = (t + u) + t := by
      ext b; simp only [Pi.add_apply]; have h2 := zmod2_add_self (t b); linear_combination -h2
    have h_tri1 : wt3 t ≤ wt3 (t + u) + wt3 u := by
      conv_lhs => rw [h_t_eq]
      exact wt3_add_le (t + u) u
    have h_tri2 : wt3 u ≤ wt3 (t + u) + wt3 t := by
      conv_lhs => rw [h_u_eq]
      exact wt3_add_le (t + u) t
    have h_comp := wt3_add_ones3 t
    have ht_le3 := wt3_le_three t
    by_cases h_mid : 1 ≤ wt3 t ∧ wt3 t ≤ 2
    · have hv := vertCost3_pos_of_wt3_eq_one_or_two t h_mid.1 h_mid.2
      omega
    · omega

/-- **Layer-Complement Symmetry Reduction for `2 ≤ wt3 u` (`star_arm_pointwise_ge_two`)**. -/
lemma star_arm_pointwise_ge_two (u t : Fin 3 → ZMod 2) (hu : 2 ≤ wt3 u) :
    (if u = ones3 then 3 * wt3 (t + ones3) else wt3 t + 2 * wt3 (t + ones3)) ≤
      4 * (wt3 (t + u) + vertCost3 t) := by
  have hu' : wt3 (u + ones3) ≤ 1 := by have h := wt3_add_ones3 u; omega
  have h_le := star_arm_pointwise_le_one (u + ones3) (t + ones3) hu'
  have h_t11 : t + ones3 + ones3 = t := by
    ext b; simp only [ones3, Pi.add_apply]; have h2 := zmod2_add_self (1 : ZMod 2); linear_combination h2
  have h_tu : (t + ones3) + (u + ones3) = t + u := by
    ext b; simp only [ones3, Pi.add_apply]; have h2 := zmod2_add_self (1 : ZMod 2); linear_combination h2
  have h_u1 : (u + ones3 = 0) ↔ (u = ones3) := by
    constructor <;> intro h <;> ext b
    · have hb := congr_fun h b; simp only [ones3, Pi.add_apply, Pi.zero_apply] at hb ⊢
      have h2 := zmod2_add_self (1 : ZMod 2); linear_combination hb - h2
    · rw [h]; simp only [ones3, Pi.add_apply, Pi.zero_apply]; exact zmod2_add_self 1
  rw [h_t11, h_tu, vertCost3_add_ones3] at h_le
  by_cases hu_eq : u = ones3
  · rw [if_pos (h_u1.mpr hu_eq)] at h_le
    rw [if_pos hu_eq]
    exact h_le
  · rw [if_neg (mt h_u1.mp hu_eq)] at h_le
    rw [if_neg hu_eq]
    omega

/-- Elementary arithmetic helper: `3 * min A B ≤ 2 * A + B` and `3 * min A B ≤ A + 2 * B`. -/
lemma three_mul_min_le (A B : ℕ) :
    3 * min A B ≤ 2 * A + B ∧ 3 * min A B ≤ A + 2 * B := by
  omega

/-- Restriction of a 2-cochain `S : BDLStepXMZ pcode M → ZMod 2` to star `q0 : Q`. -/
def restrictCQ2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S : BDLStepXMZ pcode M → ZMod 2) : BDLStepXMZ pcode M → ZMod 2 :=
  restrictStepXMZ pcode M ({inVQ q0} : Finset (TannerVertex Q M_Z M_X)) S

/-- Terminal boundary export `γ_{Q → Z}(v)` from `C_Q^1` to `C_Z^2 = M_Z × Fin 3`. -/
noncomputable def exportQZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (v : BDLStepXQ pcode M → ZMod 2) : BDLCZ2 M_Z → ZMod 2 :=
  fun mZZ =>
    syndrome (dualCode (bdlCylinderStepX pcode M)) (splitStepXQQ pcode M v)
      (Sum.inr (Sum.inr mZZ))

/-- Explicit formula for `exportQZ` via `bdlGQZ1`. -/
lemma exportQZ_apply {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (v : BDLStepXQ pcode M → ZMod 2) (mZZ : BDLCZ2 M_Z) :
    exportQZ pcode M v mZZ =
      ∑ qQ : BDLCQ1 pcode M, bdlGQZ1 pcode M mZZ qQ * v (Sum.inr qQ) := by
  dsimp [exportQZ, syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inr mZZ)) (Sum.inl qX) *
        splitStepXQQ pcode M v (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => mul_zero _)
  rw [hX, zero_add]
  rfl

/-! ## 2. Star Cleaner Candidates and Arm/Vertical Syndromes -/

/-- Base star cleaner `v_{q0}^{(0)}` on star `q0`: restricts `cylinderResidualCocycle pcode M h1` to `xq0OwnerQ = q0`. -/
noncomputable def starCleanerCandidate0 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) : BDLStepXQ pcode M → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (v0, b) =>
      if xq0OwnerQ pcode M v0 = q0 then
        cylinderResidualCocycle pcode M h1 (Sum.inr (v0, b))
      else 0

/-- Shifted star cleaner `v_{q0}^{(1)}` on star `q0`: flips all vertices of `Y_{q0}` by `1` in all 3 layers. -/
noncomputable def starCleanerCandidate1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) : BDLStepXQ pcode M → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (v0, b) =>
      if xq0OwnerQ pcode M v0 = q0 then
        cylinderResidualCocycle pcode M h1 (Sum.inr (v0, b)) + 1
      else 0

/-- The support of `starCleanerCandidate0` is contained in the `q0`-star (`cQ1OwnerQ = q0`). -/
lemma starCleanerCandidate0_support {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) (q : BDLStepXQ pcode M)
    (hq : starCleanerCandidate0 pcode M h1 q0 q ≠ 0) :
    ∃ qQ, q = Sum.inr qQ ∧ cQ1OwnerQ pcode M qQ = q0 := by
  rcases q with qX | ⟨v0, b⟩
  · exact False.elim (hq rfl)
  · dsimp [starCleanerCandidate0] at hq
    by_cases hv : xq0OwnerQ pcode M v0 = q0
    · exact ⟨(v0, b), rfl, hv⟩
    · rw [if_neg hv] at hq
      exact False.elim (hq rfl)

/-- The support of `starCleanerCandidate1` is contained in the `q0`-star (`cQ1OwnerQ = q0`). -/
lemma starCleanerCandidate1_support {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) (q : BDLStepXQ pcode M)
    (hq : starCleanerCandidate1 pcode M h1 q0 q ≠ 0) :
    ∃ qQ, q = Sum.inr qQ ∧ cQ1OwnerQ pcode M qQ = q0 := by
  rcases q with qX | ⟨v0, b⟩
  · exact False.elim (hq rfl)
  · dsimp [starCleanerCandidate1] at hq
    by_cases hv : xq0OwnerQ pcode M v0 = q0
    · exact ⟨(v0, b), rfl, hv⟩
    · rw [if_neg hv] at hq
      exact False.elim (hq rfl)

/-- Hub 3-bit vector `u(b)` of `cylinderResidualCocycle pcode M h1` at `q0`. -/
noncomputable def starHubVec {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) (b : Fin 3) : ZMod 2 :=
  cylinderResidualCocycle pcode M h1 (Sum.inr (Sum.inl q0, b))

/-- Terminal arm 3-bit vector `t(eZ, b)` of `cylinderResidualCocycle pcode M h1` at `eZ`. -/
noncomputable def starTermVec {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (eZ : ActiveZ pcode) (b : Fin 3) : ZMod 2 :=
  cylinderResidualCocycle pcode M h1 (Sum.inr (Sum.inr (Sum.inr eZ), b))

/-- Evaluates the Z-check syndrome of `starCleanerCandidate0` on arm checks (`Sum.inl`). -/
lemma syndrome_starCleanerCandidate0_arm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) (b : Fin 3) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate0 pcode M h1 q0)
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) =
    if eZ.val.1 = q0 then
      cylinderResidualCocycle pcode M h1 (Sum.inr (armStart pcode M eZ k, b)) +
      cylinderResidualCocycle pcode M h1 (Sum.inr (armEnd pcode M eZ k, b))
    else 0 := by
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) (Sum.inl qX) *
        starCleanerCandidate0 pcode M h1 q0 (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => mul_zero _)
  rw [hX, zero_add]
  dsimp [bdlStepXCheckZ, bdlDeltaQ1]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (armStart pcode M eZ k, b)]
  · rw [Finset.sum_eq_single (armEnd pcode M eZ k, b)]
    · dsimp [starCleanerCandidate0]
      rw [if_pos rfl, if_pos rfl, one_mul, one_mul, xq0OwnerQ_armStart, xq0OwnerQ_armEnd]
      by_cases hq : eZ.val.1 = q0 <;> simp [hq]
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro _ _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Evaluates the Z-check syndrome of `starCleanerCandidate1` on arm checks (`Sum.inl`). -/
lemma syndrome_starCleanerCandidate1_arm {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) (b : Fin 3) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate1 pcode M h1 q0)
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) =
    syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate0 pcode M h1 q0)
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) := by
  rw [syndrome_starCleanerCandidate0_arm]
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) (Sum.inl qX) *
        starCleanerCandidate1 pcode M h1 q0 (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => mul_zero _)
  rw [hX, zero_add]
  dsimp [bdlStepXCheckZ, bdlDeltaQ1]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (armStart pcode M eZ k, b)]
  · rw [Finset.sum_eq_single (armEnd pcode M eZ k, b)]
    · dsimp [starCleanerCandidate1]
      rw [if_pos rfl, if_pos rfl, one_mul, one_mul, xq0OwnerQ_armStart, xq0OwnerQ_armEnd]
      by_cases hq : eZ.val.1 = q0
      · rw [if_pos hq, if_pos hq, if_pos hq]
        have h2 := zmod2_add_self (1 : ZMod 2)
        linear_combination h2
      · simp [hq]
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro _ _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Evaluates the Z-check syndrome of `starCleanerCandidate0` on vertical checks (`Sum.inr`). -/
lemma syndrome_starCleanerCandidate0_vert {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (eZ : ActiveZ pcode) (v : Fin 2) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate0 pcode M h1 q0)
      (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) =
    if eZ.val.1 = q0 then
      cylinderResidualCocycle pcode M h1 (Sum.inr (Sum.inr (Sum.inr eZ), 0)) +
      cylinderResidualCocycle pcode M h1 (Sum.inr (Sum.inr (Sum.inr eZ), v.succ))
    else 0 := by
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) (Sum.inl qX) *
        starCleanerCandidate0 pcode M h1 q0 (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => mul_zero _)
  rw [hX, zero_add]
  dsimp [bdlStepXCheckZ, bdlDeltaQ1]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), 0)]
  · rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), v.succ)]
    · dsimp [starCleanerCandidate0, xq0OwnerQ]
      rw [if_pos rfl, if_pos rfl, one_mul, one_mul]
      by_cases hq : eZ.val.1 = q0 <;> simp [hq]
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro _ _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Evaluates the Z-check syndrome of `starCleanerCandidate1` on vertical checks (`Sum.inr`). -/
lemma syndrome_starCleanerCandidate1_vert {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (eZ : ActiveZ pcode) (v : Fin 2) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate1 pcode M h1 q0)
      (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) =
    syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate0 pcode M h1 q0)
      (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) := by
  rw [syndrome_starCleanerCandidate0_vert]
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) (Sum.inl qX) *
        starCleanerCandidate1 pcode M h1 q0 (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => mul_zero _)
  rw [hX, zero_add]
  dsimp [bdlStepXCheckZ, bdlDeltaQ1]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), 0)]
  · rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), v.succ)]
    · dsimp [starCleanerCandidate1]
      rw [if_pos rfl, if_pos rfl, one_mul, one_mul]
      by_cases hq : eZ.val.1 = q0
      · simp only [xq0OwnerQ, hq, ↓reduceIte]
        have h2 := zmod2_add_self (1 : ZMod 2)
        linear_combination h2
      · simp [xq0OwnerQ, hq]
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro _ _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Relates the arm syndrome of `bdlH1Q1` to the terminal residual vector `starTermVec`. -/
lemma syndrome_h1_arm_eq_residual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2)
    (eZ : ActiveZ pcode) (k : Fin (M + 1)) (b : Fin 3)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x eZ.val.1 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h1 (Sum.inl qX) = 0) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) h1
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) =
    cylinderResidualCocycle pcode M h1 (Sum.inr (armStart pcode M eZ k, b)) +
    cylinderResidualCocycle pcode M h1 (Sum.inr (armEnd pcode M eZ k, b)) := by
  have h_syn2 : syndrome (dualCode (bdlCylinderStepX pcode M)) h1
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) =
    syndrome (dualCode (bdlCylinderStepX pcode M)) (cylinderResidualCocycle pcode M h1)
      (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) := by
    dsimp [cylinderResidualCocycle, apexResidualCocycle]
    rw [syndrome_add_checkGen_dual, syndrome_add_checkGen_dual]
  rw [h_syn2]
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) (Sum.inl qX) *
        cylinderResidualCocycle pcode M h1 (Sum.inl qX)) = 0 := by
    apply Finset.sum_eq_zero
    intro qX _
    rcases qX with _ | ⟨⟨seg, bX⟩ | _⟩
    · exact zero_mul _
    · dsimp [bdlStepXCheckZ, bdlGXQ1]
      split_ifs with hc
      · by_cases hx : pcode.checkX seg.val.1.val.1 eZ.val.1 = 0
        · rw [hx, zero_mul]
        · rw [h_zero_X seg.val.1.val.1 hx (Sum.inr (Sum.inl (seg, bX))) rfl, mul_zero]
      · exact zero_mul _
    · exact zero_mul _
  rw [hX, zero_add]
  dsimp [bdlStepXCheckZ, bdlDeltaQ1]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (armStart pcode M eZ k, b)]
  · rw [Finset.sum_eq_single (armEnd pcode M eZ k, b)]
    · simp
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro _ _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Relates the vertical syndrome of `bdlH1Q1` to the hub residual difference. -/
lemma syndrome_h1_vert_eq_residual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2)
    (eZ : ActiveZ pcode) (v : Fin 2)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x eZ.val.1 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h1 (Sum.inl qX) = 0) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) h1
      (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) =
    cylinderResidualCocycle pcode M h1 (Sum.inr (Sum.inr (Sum.inr eZ), 0)) +
    cylinderResidualCocycle pcode M h1 (Sum.inr (Sum.inr (Sum.inr eZ), v.succ)) := by
  have h_syn2 : syndrome (dualCode (bdlCylinderStepX pcode M)) h1
      (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) =
    syndrome (dualCode (bdlCylinderStepX pcode M)) (cylinderResidualCocycle pcode M h1)
      (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) := by
    dsimp [cylinderResidualCocycle, apexResidualCocycle]
    rw [syndrome_add_checkGen_dual, syndrome_add_checkGen_dual]
  rw [h_syn2]
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) (Sum.inl qX) *
        cylinderResidualCocycle pcode M h1 (Sum.inl qX)) = 0 := by
    apply Finset.sum_eq_zero
    intro qX _
    rcases qX with _ | ⟨_ | ⟨xv, b'⟩⟩
    · exact zero_mul _
    · exact zero_mul _
    · dsimp [bdlStepXCheckZ, bdlGXQ1]
      split_ifs with hc
      · by_cases hx : pcode.checkX xv.val.1 eZ.val.1 = 0
        · rw [hx, zero_mul]
        · rw [h_zero_X xv.val.1 hx (Sum.inr (Sum.inr (xv, b'))) rfl, mul_zero]
      · exact zero_mul _
  rw [hX, zero_add]
  dsimp [bdlStepXCheckZ, bdlDeltaQ1]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), 0)]
  · rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ), v.succ)]
    · simp
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro _ _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

end BDLDecoder

/-! ## 3. Layer-Complement Weight Duality $w(\bar{c}_1) = |S| - w(c_1)$ -/

/-- **Layer-Complement Weight Identity**:
    Over any finite qubit layer set $S$, the sum of weights of $\bar{c}_1 = \mathbf{1} + c_1$ and
    $c_1$ equals $|S|$. -/
theorem sum_zmod2ToNat_layerComplementChain {α : Type*} (S : Finset α) (c1 : α → ZMod 2) :
    (∑ q ∈ S, zmod2ToNat (layerComplementChain c1 q)) + (∑ q ∈ S, zmod2ToNat (c1 q)) = S.card := by
  rw [← Finset.sum_add_distrib]
  have h_one : ∀ q ∈ S, zmod2ToNat (layerComplementChain c1 q) + zmod2ToNat (c1 q) = 1 :=
    fun q _ => zmod2ToNat_layerComplementChain_add c1 q
  rw [Finset.sum_congr rfl h_one, Finset.sum_const, smul_eq_mul, mul_one]

/-- Subtracting `∑ q ∈ S, zmod2ToNat (c1 q)` gives the exact complement weight `S.card - w`. -/
theorem sum_zmod2ToNat_layerComplementChain_eq_sub {α : Type*} (S : Finset α) (c1 : α → ZMod 2) :
    (∑ q ∈ S, zmod2ToNat (layerComplementChain c1 q)) =
      S.card - (∑ q ∈ S, zmod2ToNat (c1 q)) := by
  have h := sum_zmod2ToNat_layerComplementChain S c1
  omega

/-- **4-Line Complement Majority Bound (`min_weight_complement_le_half`)**. -/
theorem min_weight_complement_le_half (M w : ℕ) (hw : w ≤ M) :
    min w (M - w) ≤ M / 2 ∧ M ≤ 2 * max w (M - w) := by
  omega

/-- Identifies `layerComplementChain t` on `Fin 3 → ZMod 2` with `t + BDLDecoder.ones3`. -/
lemma layerComplementChain_eq_add_ones3 (t : Fin 3 → ZMod 2) :
    layerComplementChain t = t + BDLDecoder.ones3 := by
  ext b
  dsimp [layerComplementChain, BDLDecoder.ones3]
  ring

/-- Expresses `BDLDecoder.wt3` as the $\mathbb{Z}_{\ge 0}$-lift sum $\sum_{b=0}^2 |t_b|_{\mathbb{Z}}$. -/
lemma wt3_eq_sum_zmod2ToNat (t : Fin 3 → ZMod 2) :
    BDLDecoder.wt3 t = ∑ b : Fin 3, zmod2ToNat (t b) := by
  rw [Fin.sum_univ_three]
  dsimp [BDLDecoder.wt3]
  simp only [zmod2ToNat_eq_ite]

/-- **Layer-Complement Identity on 3-Layer Star Vectors (`wt3_layerComplementChain`)**. -/
theorem wt3_layerComplementChain (t : Fin 3 → ZMod 2) :
    BDLDecoder.wt3 (layerComplementChain t) + BDLDecoder.wt3 t = 3 := by
  rw [layerComplementChain_eq_add_ones3]
  exact BDLDecoder.wt3_add_ones3 t

/-- **Vertical Coboundary Invariance (`vertCost3_layerComplementChain`)**. -/
theorem vertCost3_layerComplementChain (t : Fin 3 → ZMod 2) :
    BDLDecoder.vertCost3 (layerComplementChain t) = BDLDecoder.vertCost3 t := by
  rw [layerComplementChain_eq_add_ones3]
  exact BDLDecoder.vertCost3_add_ones3 t

/-- **Stage-1 Cylinder Cleaner Contraction (`stage1_cylinder_cleaner_exists`)**. -/
theorem stage1_cylinder_cleaner_exists {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    ∃ u_x : BDLStepXQ pcode M → ZMod 2,
      (∀ q, u_x q ≠ 0 → ∃ qX, q = Sum.inl qX ∧ BDLDecoder.cX1OwnerX pcode M qX = x) ∧
      BDLDecoder.restrictCX2 pcode M x
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (h + u_x)) = 0 ∧
      3 * BDLDecoder.weightNetExportXQ pcode M u_x ≤
        4 * BDLDecoder.weightCX2OnCyl pcode M x
          (syndrome (dualCode (bdlCylinderStepX pcode M)) h) ∧
      (BDLDecoder.restrictCX2 pcode M x
        (syndrome (dualCode (bdlCylinderStepX pcode M)) h) = 0 → u_x = 0) :=
  BDLDecoder.exists_local_cylinder_cleaner pcode M hov h_conn h x

end WeldedHierarchy
