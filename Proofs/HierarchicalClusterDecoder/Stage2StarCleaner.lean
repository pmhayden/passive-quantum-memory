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

import Proofs.HierarchicalClusterDecoder.Stage2StarComplementSymmetry

/-!
# Stage-2 Local Star Cleaner Existence and 4/3 Majority Export Bound

Computes the star-to-coarse-check syndrome exports of the two complementary Stage-2 star cleaner candidates (`exportQZ_starCleanerCandidate0_apply`, `exportQZ_starCleanerCandidate1_apply`) and relates their sum to `weightNetCQ2OnStar` (`sum_wt3_add_vertCost3_eq_weightNetCQ2OnStar`). Proves `exists_local_star_cleaner`, establishing that the better of the two candidates cancels residual star syndromes while exporting at most 4/3 of the net star syndrome weight.

## References

* Part I, Section 4.3 (`subsec:stage2-star`), Lemma 4.2 (`lem:stage2-star-cleaner`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Star Syndrome Cancellation and Arm Telescoping -/

/-- Adding `starCleanerCandidate0` cancels `restrictCQ2 (syndrome u)` when the residual sum vanishes. -/
lemma restrictCQ2_syndrome_starCleanerCandidate0_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x q0 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h1 (Sum.inl qX) = 0) :
    restrictCQ2 pcode M q0
      (syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate0 pcode M h1 q0)) =
    restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) := by
  ext mZ
  dsimp [restrictCQ2, restrictStepXMZ]
  rcases mZ with mZX | ⟨⟨⟨eZ, k, b⟩ | ⟨eZ, v⟩⟩ | mZZ⟩
  · dsimp [stepXMZOwnerTanner, inVX, inVQ]
  · by_cases hq : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) ∈ ({inVQ q0} : Finset _)
    · rw [if_pos hq, if_pos hq]
      have hq_eq : eZ.val.1 = q0 := by
        dsimp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ] at hq
        simp only [Finset.mem_singleton] at hq
        injection hq with h1'
        injection h1'
      rw [syndrome_starCleanerCandidate0_arm, if_pos hq_eq,
        syndrome_h1_arm_eq_residual pcode M h1 eZ k b (hq_eq.symm ▸ h_zero_X)]
    · rw [if_neg hq, if_neg hq]
  · by_cases hq : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ∈ ({inVQ q0} : Finset _)
    · rw [if_pos hq, if_pos hq]
      have hq_eq : eZ.val.1 = q0 := by
        dsimp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ] at hq
        simp only [Finset.mem_singleton] at hq
        injection hq with h1'
        injection h1'
      rw [syndrome_starCleanerCandidate0_vert, if_pos hq_eq,
        syndrome_h1_vert_eq_residual pcode M h1 eZ v (hq_eq.symm ▸ h_zero_X)]
    · rw [if_neg hq, if_neg hq]
  · dsimp [stepXMZOwnerTanner, inVZ, inVQ]

/-- Adding `starCleanerCandidate1` cancels `restrictCQ2 (syndrome u)` when the residual sum equals `ones3`. -/
lemma restrictCQ2_syndrome_starCleanerCandidate1_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x q0 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h1 (Sum.inl qX) = 0) :
    restrictCQ2 pcode M q0
      (syndrome (dualCode (bdlCylinderStepX pcode M)) (starCleanerCandidate1 pcode M h1 q0)) =
    restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) := by
  rw [← restrictCQ2_syndrome_starCleanerCandidate0_eq pcode M h1 q0 h_zero_X]
  ext mZ
  dsimp [restrictCQ2, restrictStepXMZ]
  rcases mZ with mZX | ⟨⟨⟨eZ, k, b⟩ | ⟨eZ, v⟩⟩ | mZZ⟩
  · dsimp [stepXMZOwnerTanner, inVX, inVQ]
  · by_cases hq : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) ∈ ({inVQ q0} : Finset _)
    · rw [if_pos hq, if_pos hq, syndrome_starCleanerCandidate1_arm]
    · rw [if_neg hq, if_neg hq]
  · by_cases hq : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ∈ ({inVQ q0} : Finset _)
    · rw [if_pos hq, if_pos hq, syndrome_starCleanerCandidate1_vert]
    · rw [if_neg hq, if_neg hq]
  · dsimp [stepXMZOwnerTanner, inVZ, inVQ]

/-- Telescoping sum along an `(M + 1)`-subdivided arm `eZ : ActiveZ pcode`. -/
lemma sum_armStart_add_armEnd_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (eZ : ActiveZ pcode) (f : Xq0 pcode M → ZMod 2) :
    (∑ k : Fin (M + 1), (f (armStart pcode M eZ k) + f (armEnd pcode M eZ k))) =
      f (Sum.inl eZ.val.1) + f (Sum.inr (Sum.inr eZ)) := by
  have h_ind : ∀ (n : ℕ) (hn : n < M + 1),
      (∑ i ∈ Finset.range (n + 1),
        if h : i < M + 1 then f (armStart pcode M eZ ⟨i, h⟩) + f (armEnd pcode M eZ ⟨i, h⟩) else 0) =
      f (Sum.inl eZ.val.1) + f (armEnd pcode M eZ ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero =>
      intro hn
      rw [Finset.sum_range_one, dif_pos hn]
      rfl
    | succ m ih =>
      intro hm
      have hm' : m < M + 1 := Nat.lt_of_succ_lt hm
      rw [Finset.sum_range_succ, ih hm', dif_pos hm]
      have h_link : armStart pcode M eZ ⟨m + 1, hm⟩ = armEnd pcode M eZ ⟨m, hm'⟩ := by
        dsimp [armStart, armEnd]
        have h_lt : m < M := Nat.lt_of_succ_lt_succ hm
        rw [dif_pos h_lt]
      rw [h_link]
      have h2 := zmod2_add_self (f (armEnd pcode M eZ ⟨m, hm'⟩))
      linear_combination h2
  have h_fin : (∑ k : Fin (M + 1), (f (armStart pcode M eZ k) + f (armEnd pcode M eZ k))) =
      ∑ i ∈ Finset.range (M + 1),
        if h : i < M + 1 then f (armStart pcode M eZ ⟨i, h⟩) + f (armEnd pcode M eZ ⟨i, h⟩) else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i =>
      if h : i < M + 1 then f (armStart pcode M eZ ⟨i, h⟩) + f (armEnd pcode M eZ ⟨i, h⟩) else 0)]
    apply Finset.sum_congr rfl
    intro k _
    rw [dif_pos k.isLt]
  have h_last : armEnd pcode M eZ ⟨M, Nat.lt_succ_self M⟩ = Sum.inr (Sum.inr eZ) := by
    dsimp [armEnd]
    rw [dif_neg (Nat.lt_irrefl M)]
  rw [h_fin, h_ind M (Nat.lt_succ_self M), h_last]

/-- Exact arm telescoping identity for `starTermVec` and `starHubVec`. -/
lemma starTermVec_add_starHubVec_eq_sum_syndrome {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2)
    (eZ : ActiveZ pcode) (b : Fin 3)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x eZ.val.1 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h1 (Sum.inl qX) = 0) :
    starTermVec pcode M h1 eZ b + starHubVec pcode M h1 eZ.val.1 b =
      ∑ k : Fin (M + 1),
        syndrome (dualCode (bdlCylinderStepX pcode M)) h1
          (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) := by
  simp_rw [syndrome_h1_arm_eq_residual pcode M h1 eZ _ b h_zero_X]
  rw [sum_armStart_add_armEnd_eq pcode M eZ
    (fun v0 => cylinderResidualCocycle pcode M h1 (Sum.inr (v0, b)))]
  dsimp [starTermVec, starHubVec]
  exact add_comm _ _

/-! ## 2. Exported Z-Check Syndrome Cardinality Bounds -/

/-- Explicit coordinate formula for `exportQZ` applied to `starCleanerCandidate0`. -/
lemma exportQZ_starCleanerCandidate0_apply {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) (z : M_Z) (b : Fin 3) :
    exportQZ pcode M (starCleanerCandidate0 pcode M h1 q0) (z, b) =
      if hz : pcode.checkZ z q0 ≠ 0 then
        starTermVec pcode M h1 ⟨(q0, z), hz⟩ b
      else 0 := by
  rw [exportQZ_apply]
  by_cases hz : pcode.checkZ z q0 ≠ 0
  · rw [dif_pos hz]
    let eZ0 : ActiveZ pcode := ⟨(q0, z), hz⟩
    rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ0), b)]
    · dsimp [bdlGQZ1, starCleanerCandidate0, xq0OwnerQ, starTermVec, eZ0]
      simp
    · intro qQ _ hne
      rcases qQ with ⟨q' | ⟨p | eZ⟩, b'⟩
      · exact zero_mul _
      · exact zero_mul _
      · dsimp [bdlGQZ1, starCleanerCandidate0]
        by_cases hc : eZ.val.2 = z ∧ b' = b
        · by_cases hq : eZ.val.1 = q0
          · exfalso
            apply hne
            apply Prod.ext
            · apply congr_arg Sum.inr
              apply congr_arg Sum.inr
              exact Subtype.ext (Prod.ext hq hc.1)
            · exact hc.2
          · simp [xq0OwnerQ, hq]
        · rw [if_neg hc, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · rw [dif_neg hz]
    apply Finset.sum_eq_zero
    intro qQ _
    rcases qQ with ⟨q' | ⟨p | eZ⟩, b'⟩
    · exact zero_mul _
    · exact zero_mul _
    · dsimp [bdlGQZ1, starCleanerCandidate0]
      by_cases hq : eZ.val.1 = q0
      · have heZ2 : eZ.val.2 ≠ z := by
          intro h_eq
          exact hz (h_eq ▸ hq ▸ eZ.property)
        rw [if_neg (fun hc => heZ2 hc.1), zero_mul]
      · simp [xq0OwnerQ, hq]

/-- Explicit coordinate formula for `exportQZ` applied to `starCleanerCandidate1`. -/
lemma exportQZ_starCleanerCandidate1_apply {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) (z : M_Z) (b : Fin 3) :
    exportQZ pcode M (starCleanerCandidate1 pcode M h1 q0) (z, b) =
      if hz : pcode.checkZ z q0 ≠ 0 then
        starTermVec pcode M h1 ⟨(q0, z), hz⟩ b + 1
      else 0 := by
  rw [exportQZ_apply]
  by_cases hz : pcode.checkZ z q0 ≠ 0
  · rw [dif_pos hz]
    let eZ0 : ActiveZ pcode := ⟨(q0, z), hz⟩
    rw [Finset.sum_eq_single (Sum.inr (Sum.inr eZ0), b)]
    · dsimp [bdlGQZ1, starCleanerCandidate1, xq0OwnerQ, starTermVec, eZ0]
      simp
    · intro qQ _ hne
      rcases qQ with ⟨q' | ⟨p | eZ⟩, b'⟩
      · exact zero_mul _
      · exact zero_mul _
      · dsimp [bdlGQZ1, starCleanerCandidate1]
        by_cases hc : eZ.val.2 = z ∧ b' = b
        · by_cases hq : eZ.val.1 = q0
          · exfalso
            apply hne
            apply Prod.ext
            · apply congr_arg Sum.inr
              apply congr_arg Sum.inr
              exact Subtype.ext (Prod.ext hq hc.1)
            · exact hc.2
          · simp [xq0OwnerQ, hq]
        · rw [if_neg hc, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · rw [dif_neg hz]
    apply Finset.sum_eq_zero
    intro qQ _
    rcases qQ with ⟨q' | ⟨p | eZ⟩, b'⟩
    · exact zero_mul _
    · exact zero_mul _
    · dsimp [bdlGQZ1, starCleanerCandidate1]
      by_cases hq : eZ.val.1 = q0
      · have heZ2 : eZ.val.2 ≠ z := by
          intro h_eq
          exact hz (h_eq ▸ hq ▸ eZ.property)
        rw [if_neg (fun hc => heZ2 hc.1), zero_mul]
      · simp [xq0OwnerQ, hq]

/-- The indicator sum of non-zero coordinates over `Fin 3` equals `wt3 f`. -/
lemma sum_fin3_ite_ne_zero_eq_wt3 (f : Fin 3 → ZMod 2) :
    (∑ b : Fin 3, if f b ≠ 0 then 1 else 0) = wt3 f := by
  rw [Fin.sum_univ_three]
  rfl

/-- The indicator sum of vertical differences over `Fin 2` equals `vertCost3 t`. -/
lemma sum_fin2_ite_ne_zero_eq_vertCost3 (t : Fin 3 → ZMod 2) :
    (∑ v : Fin 2, if t 0 + t v.succ ≠ 0 then 1 else 0) = vertCost3 t := by
  rw [Fin.sum_univ_two]
  rfl

/-- Subadditivity of the non-zero indicator of a finite sum in `ZMod 2`. -/
lemma ite_sum_ne_zero_le_sum_ite {α : Type*} [DecidableEq α] (s : Finset α) (g : α → ZMod 2) :
    (if (∑ x ∈ s, g x) ≠ 0 then 1 else 0) ≤ ∑ x ∈ s, if g x ≠ 0 then 1 else 0 := by
  by_cases h : (∑ x ∈ s, g x) ≠ 0
  · rw [if_pos h]
    obtain ⟨x, hx, hgx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hle := Finset.single_le_sum (f := fun y => if g y ≠ 0 then 1 else 0) (fun y _ => Nat.zero_le _) hx
    (try dsimp at hle)
    rw [if_pos hgx] at hle
    exact hle
  · rw [if_neg h]
    exact Nat.zero_le _

/-- Bijects a sum over `ActiveZ` incident to `q0` with a filtered sum over `M_Z`. -/
lemma sum_activeZ_q0_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (q0 : Q) (F : ActiveZ pcode → ℕ) :
    (∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0), F eZ) =
      ∑ z : M_Z, if hz : pcode.checkZ z q0 ≠ 0 then F ⟨(q0, z), hz⟩ else 0 := by
  rw [Finset.sum_filter]
  let G : Q × M_Z → ℕ := fun p =>
    if hp : pcode.checkZ p.2 p.1 ≠ 0 then
      (if p.1 = q0 then F ⟨p, hp⟩ else 0)
    else 0
  have h1 : (∑ eZ : ActiveZ pcode, if eZ.val.1 = q0 then F eZ else 0) =
      ∑ p ∈ Finset.univ.filter (fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0), G p := by
    have hs : (∑ eZ : ActiveZ pcode, G eZ.val) =
        ∑ p ∈ Finset.univ.filter (fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0), G p :=
      (Finset.sum_subtype (Finset.univ.filter (fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0))
        (p := fun p : Q × M_Z => pcode.checkZ p.2 p.1 ≠ 0)
        (fun _ => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))
        G).symm
    refine (Finset.sum_congr rfl ?_).trans hs
    intro eZ _
    dsimp [G]
    rw [dif_pos eZ.property]
  rw [h1, Finset.sum_filter]
  have h2 : ∀ p : Q × M_Z, (if pcode.checkZ p.2 p.1 ≠ 0 then G p else 0) = G p := by
    intro p; dsimp [G]; split_ifs <;> rfl
  simp_rw [h2]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single q0]
  · dsimp [G]
    by_cases hz : pcode.checkZ z q0 ≠ 0
    · rw [dif_pos hz, if_pos rfl, dif_pos hz]
    · rw [dif_neg hz, dif_neg hz]
  · intro q _ hne
    dsimp [G]
    by_cases hz : pcode.checkZ z q ≠ 0
    · rw [dif_pos hz, if_neg hne]
    · rw [dif_neg hz]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0))

/-- Bounds the active Z-check export count of `starCleanerCandidate0` on star `q0`. -/
lemma card_exportQZ_starCleanerCandidate0_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) :
    (Finset.univ.filter (fun mZ : BDLCZ2 M_Z =>
      exportQZ pcode M (starCleanerCandidate0 pcode M h1 q0) mZ ≠ 0)).card =
    ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
      wt3 (starTermVec pcode M h1 eZ) := by
  rw [Finset.card_filter, Fintype.sum_prod_type, sum_activeZ_q0_eq]
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [exportQZ_starCleanerCandidate0_apply]
  by_cases hz : pcode.checkZ z q0 ≠ 0
  · simp_rw [dif_pos hz]
    exact sum_fin3_ite_ne_zero_eq_wt3 _
  · simp_rw [dif_neg hz]
    simp

/-- Bounds the active Z-check export count of `starCleanerCandidate1` on star `q0`. -/
lemma card_exportQZ_starCleanerCandidate1_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q) :
    (Finset.univ.filter (fun mZ : BDLCZ2 M_Z =>
      exportQZ pcode M (starCleanerCandidate1 pcode M h1 q0) mZ ≠ 0)).card =
    ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
      wt3 (starTermVec pcode M h1 eZ + ones3) := by
  rw [Finset.card_filter, Fintype.sum_prod_type, sum_activeZ_q0_eq]
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [exportQZ_starCleanerCandidate1_apply]
  by_cases hz : pcode.checkZ z q0 ≠ 0
  · simp_rw [dif_pos hz]
    exact sum_fin3_ite_ne_zero_eq_wt3 (starTermVec pcode M h1 ⟨(q0, z), hz⟩ + ones3)
  · simp_rw [dif_neg hz]
    simp

/-! ## 3. Net Star Syndrome Weight Decomposition and Existence of Local Star Cleaner -/

/-- Decomposes `syndromeWeightNat (restrictCQ2 s)` into arm and vertical check sums on star `q0`. -/
lemma syndromeWeightNat_restrictCQ2_eq_sum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S1 : BDLStepXMZ pcode M → ZMod 2) :
    syndromeWeightNat (restrictCQ2 pcode M q0 S1) =
      ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
        ((∑ b : Fin 3, ∑ k : Fin (M + 1),
            if S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) ≠ 0 then 1 else 0) +
         (∑ v : Fin 2,
            if S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ≠ 0 then 1 else 0)) := by
  dsimp [syndromeWeightNat]
  rw [Finset.card_filter, Fintype.sum_sum_type]
  have hX : (∑ mZX : BDLCX2 pcode M,
      if restrictCQ2 pcode M q0 S1 (Sum.inl mZX) ≠ 0 then 1 else 0) = 0 :=
    Finset.sum_eq_zero (fun _ _ => by dsimp [restrictCQ2, restrictStepXMZ, stepXMZOwnerTanner, inVX, inVQ])
  have hZ : (∑ mZZ : BDLCZ2 M_Z,
      if restrictCQ2 pcode M q0 S1 (Sum.inr (Sum.inr mZZ)) ≠ 0 then 1 else 0) = 0 :=
    Finset.sum_eq_zero (fun _ _ => by dsimp [restrictCQ2, restrictStepXMZ, stepXMZOwnerTanner, inVZ, inVQ])
  rw [hX, zero_add, Fintype.sum_sum_type, hZ, add_zero, Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
  congr 1
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro eZ _
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    by_cases hq : eZ.val.1 = q0
    · rw [if_pos hq]
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro k _
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) ∈
          ({inVQ q0} : Finset (TannerVertex Q M_Z M_X)) := by
        simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, hq]
      have hr : restrictCQ2 pcode M q0 S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) =
          S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) := if_pos hm
      rw [hr]
    · rw [if_neg hq]
      apply Finset.sum_eq_zero; intro b _
      apply Finset.sum_eq_zero; intro k _
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) ∉
          ({inVQ q0} : Finset (TannerVertex Q M_Z M_X)) := by
        simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, hq]
      have hr : restrictCQ2 pcode M q0 S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) = 0 := if_neg hm
      simp [hr]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro eZ _
    by_cases hq : eZ.val.1 = q0
    · rw [if_pos hq]
      apply Finset.sum_congr rfl; intro v _
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ∈
          ({inVQ q0} : Finset (TannerVertex Q M_Z M_X)) := by
        simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, hq]
      have hr : restrictCQ2 pcode M q0 S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) =
          S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) := if_pos hm
      rw [hr]
    · rw [if_neg hq]
      apply Finset.sum_eq_zero; intro v _
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ∉
          ({inVQ q0} : Finset (TannerVertex Q M_Z M_X)) := by
        simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, hq]
      have hr : restrictCQ2 pcode M q0 S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) = 0 := if_neg hm
      simp [hr]

/-- Collapsed net syndrome weight on star `q0 : Q`. -/
def weightNetCQ2OnStar {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S1 : BDLStepXMZ pcode M → ZMod 2) : ℕ :=
  ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
    ((∑ b : Fin 3,
        if (∑ k : Fin (M + 1), S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))) ≠ 0 then 1 else 0) +
     (∑ v : Fin 2,
        if S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ≠ 0 then 1 else 0))

/-- Invariance of `weightNetCQ2OnStar` under `restrictCQ2` on star `q0`. -/
lemma weightNetCQ2OnStar_restrictCQ2_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S1 : BDLStepXMZ pcode M → ZMod 2) :
    weightNetCQ2OnStar pcode M q0 (restrictCQ2 pcode M q0 S1) =
      weightNetCQ2OnStar pcode M q0 S1 := by
  dsimp [weightNetCQ2OnStar]
  apply Finset.sum_congr rfl
  intro eZ heZ
  have hq0 : eZ.val.1 = q0 := (Finset.mem_filter.mp heZ).2
  congr 1
  · apply Finset.sum_congr rfl; intro b _
    have h_sum : (∑ k : Fin (M + 1), restrictCQ2 pcode M q0 S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))) =
        ∑ k : Fin (M + 1), S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) := by
      apply Finset.sum_congr rfl; intro k _
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) ∈ ({inVQ q0} : Finset _) := by
        simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, hq0]
      dsimp [restrictCQ2, restrictStepXMZ]; rw [if_pos hm]
    rw [h_sum]
  · apply Finset.sum_congr rfl; intro v _
    have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ∈ ({inVQ q0} : Finset _) := by
      simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, hq0]
    have hr : restrictCQ2 pcode M q0 S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) =
        S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) := if_pos hm
    rw [hr]

/-- Bounds `weightNetCQ2OnStar` above by `syndromeWeightNat (restrictCQ2 s)`. -/
lemma weightNetCQ2OnStar_le_syndromeWeightNat_restrictCQ2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S1 : BDLStepXMZ pcode M → ZMod 2) :
    weightNetCQ2OnStar pcode M q0 S1 ≤
      syndromeWeightNat (restrictCQ2 pcode M q0 S1) := by
  rw [syndromeWeightNat_restrictCQ2_eq_sum]
  dsimp [weightNetCQ2OnStar]
  apply Finset.sum_le_sum
  intro eZ _
  apply Nat.add_le_add
  · apply Finset.sum_le_sum; intro b _
    exact ite_sum_ne_zero_le_sum_ite Finset.univ _
  · exact le_rfl

/-- Identifies the sum of `wt3` and `vertCost3` over active incident arms with `weightNetCQ2OnStar`. -/
lemma sum_wt3_add_vertCost3_eq_weightNetCQ2OnStar {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h1 : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (h_zero_X : ∀ (x : M_X), pcode.checkX x q0 ≠ 0 →
      ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
        cylinderResidualCocycle pcode M h1 (Sum.inl qX) = 0) :
    (∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
      (wt3 (starTermVec pcode M h1 eZ + starHubVec pcode M h1 q0) +
       vertCost3 (starTermVec pcode M h1 eZ))) =
    weightNetCQ2OnStar pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) := by
  dsimp [weightNetCQ2OnStar]
  apply Finset.sum_congr rfl
  intro eZ heZ
  have hq0 : eZ.val.1 = q0 := (Finset.mem_filter.mp heZ).2
  have h_wt : wt3 (starTermVec pcode M h1 eZ + starHubVec pcode M h1 q0) =
      ∑ b : Fin 3,
        if (∑ k : Fin (M + 1),
            syndrome (dualCode (bdlCylinderStepX pcode M)) h1
              (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))) ≠ 0 then 1 else 0 := by
    rw [← sum_fin3_ite_ne_zero_eq_wt3]
    apply Finset.sum_congr rfl; intro b _
    have h_eq : (starTermVec pcode M h1 eZ + starHubVec pcode M h1 q0) b =
        ∑ k : Fin (M + 1),
          syndrome (dualCode (bdlCylinderStepX pcode M)) h1
            (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) := by
      change starTermVec pcode M h1 eZ b + starHubVec pcode M h1 q0 b = _
      rw [← hq0]
      exact starTermVec_add_starHubVec_eq_sum_syndrome pcode M h1 eZ b (hq0.symm ▸ h_zero_X)
    rw [h_eq]
  have h_vert : vertCost3 (starTermVec pcode M h1 eZ) =
      ∑ v : Fin 2,
        if syndrome (dualCode (bdlCylinderStepX pcode M)) h1
            (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ≠ 0 then 1 else 0 := by
    rw [← sum_fin2_ite_ne_zero_eq_vertCost3]
    apply Finset.sum_congr rfl; intro v _
    rw [syndrome_h1_vert_eq_residual pcode M h1 eZ v (hq0.symm ▸ h_zero_X)]
    rfl
  rw [h_wt, h_vert]

/-- Theorem (Stage-2 Star Cleaning with 4/3 Bound). -/
theorem exists_local_star_cleaner {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h1 : BDLStepXQ pcode M → ZMod 2)
    (h1_cyl : ∀ x : M_X, restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) = 0)
    (q0 : Q) :
    ∃ v_q0 : BDLStepXQ pcode M → ZMod 2,
      (∀ q, v_q0 q ≠ 0 → ∃ qQ, q = Sum.inr qQ ∧ cQ1OwnerQ pcode M qQ = q0) ∧
      restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) (h1 + v_q0)) = 0 ∧
      3 * (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => exportQZ pcode M v_q0 mZ ≠ 0)).card ≤
        4 * weightNetCQ2OnStar pcode M q0
          (restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1)) ∧
      (restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) = 0 → v_q0 = 0) := by
  by_cases h_zero_S : restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) = 0
  · refine ⟨0, ?_, ?_, ?_, fun _ => rfl⟩
    · intro _ h_abs; exact False.elim (h_abs rfl)
    · rw [add_zero]; exact h_zero_S
    · have h_exp0 : exportQZ pcode M 0 = 0 := by
        ext mZZ; rw [exportQZ_apply]; exact Finset.sum_eq_zero (fun _ _ => mul_zero _)
      simp [h_exp0]
  · have h_zero_X : ∀ (x : M_X), pcode.checkX x q0 ≠ 0 →
        ∀ (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
          cylinderResidualCocycle pcode M h1 (Sum.inl qX) = 0 := by
      intro x _ qX hqX
      apply cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h1 x _ _ qX hqX
      · intro seg b hseg
        have h_eq := congr_fun (h1_cyl x) (Sum.inl (Sum.inl (seg, b)))
        dsimp [restrictCX2, restrictStepXMZ] at h_eq
        have hm : stepXMZOwnerTanner pcode M (Sum.inl (Sum.inl (seg, b))) ∈ ({inVX x} : Finset _) := by
          simp [stepXMZOwnerTanner, cX2OwnerX, cX2OwnerLink, inVX, hseg]
        rw [if_pos hm] at h_eq
        exact h_eq
      · intro s' k' b' hs'
        have h_eq := congr_fun (h1_cyl x) (Sum.inl (Sum.inr (s', k', b')))
        dsimp [restrictCX2, restrictStepXMZ] at h_eq
        have hm : stepXMZOwnerTanner pcode M (Sum.inl (Sum.inr (s', k', b'))) ∈ ({inVX x} : Finset _) := by
          simp [stepXMZOwnerTanner, cX2OwnerX, cX2OwnerLink, inVX, hs']
        rw [if_pos hm] at h_eq
        exact h_eq
    let v0 := starCleanerCandidate0 pcode M h1 q0
    let v1 := starCleanerCandidate1 pcode M h1 q0
    let A := (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => exportQZ pcode M v0 mZ ≠ 0)).card
    let B := (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => exportQZ pcode M v1 mZ ≠ 0)).card
    have hA : A = ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
        wt3 (starTermVec pcode M h1 eZ) := card_exportQZ_starCleanerCandidate0_eq pcode M h1 q0
    have hB : B = ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
        wt3 (starTermVec pcode M h1 eZ + ones3) := card_exportQZ_starCleanerCandidate1_eq pcode M h1 q0
    have h_min_le_A : min A B ≤ A := Nat.min_le_left A B
    have h_min_le_B : min A B ≤ B := Nat.min_le_right A B
    have h_min_bound : 3 * min A B ≤
        4 * weightNetCQ2OnStar pcode M q0
          (restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h1)) := by
      rw [weightNetCQ2OnStar_restrictCQ2_eq,
          ← sum_wt3_add_vertCost3_eq_weightNetCQ2OnStar pcode M h1 q0 h_zero_X]
      by_cases hu : wt3 (starHubVec pcode M h1 q0) ≤ 1
      · by_cases hu0 : starHubVec pcode M h1 q0 = 0
        · have h_sum : 3 * A ≤ 4 * ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
              (wt3 (starTermVec pcode M h1 eZ + starHubVec pcode M h1 q0) + vertCost3 (starTermVec pcode M h1 eZ)) := by
            rw [hA, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro eZ _
            have h_pt := star_arm_pointwise_le_one (starHubVec pcode M h1 q0) (starTermVec pcode M h1 eZ) hu
            rw [if_pos hu0] at h_pt
            exact h_pt
          omega
        · have h_sum : 2 * A + B ≤ 4 * ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
              (wt3 (starTermVec pcode M h1 eZ + starHubVec pcode M h1 q0) + vertCost3 (starTermVec pcode M h1 eZ)) := by
            rw [hA, hB, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro eZ _
            have h_pt := star_arm_pointwise_le_one (starHubVec pcode M h1 q0) (starTermVec pcode M h1 eZ) hu
            rw [if_neg hu0] at h_pt
            exact h_pt
          have h_min := (three_mul_min_le A B).1
          omega
      · have hu2 : 2 ≤ wt3 (starHubVec pcode M h1 q0) := by omega
        by_cases hu1 : starHubVec pcode M h1 q0 = ones3
        · have h_sum : 3 * B ≤ 4 * ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
              (wt3 (starTermVec pcode M h1 eZ + starHubVec pcode M h1 q0) + vertCost3 (starTermVec pcode M h1 eZ)) := by
            rw [hB, Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro eZ _
            have h_pt := star_arm_pointwise_ge_two (starHubVec pcode M h1 q0) (starTermVec pcode M h1 eZ) hu2
            rw [if_pos hu1] at h_pt
            exact h_pt
          omega
        · have h_sum : A + 2 * B ≤ 4 * ∑ eZ ∈ Finset.univ.filter (fun eZ : ActiveZ pcode => eZ.val.1 = q0),
              (wt3 (starTermVec pcode M h1 eZ + starHubVec pcode M h1 q0) + vertCost3 (starTermVec pcode M h1 eZ)) := by
            rw [hA, hB, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro eZ _
            have h_pt := star_arm_pointwise_ge_two (starHubVec pcode M h1 q0) (starTermVec pcode M h1 eZ) hu2
            rw [if_neg hu1] at h_pt
            exact h_pt
          have h_min := (three_mul_min_le A B).2
          omega
    by_cases hAB : A ≤ B
    · refine ⟨v0, starCleanerCandidate0_support pcode M h1 q0, ?_, ?_, fun hc => False.elim (h_zero_S hc)⟩
      · ext mZ
        dsimp [restrictCQ2, restrictStepXMZ]
        split_ifs with hm
        · rw [map_add, Pi.add_apply]
          have h_eq := congr_fun (restrictCQ2_syndrome_starCleanerCandidate0_eq pcode M h1 q0 h_zero_X) mZ
          simp only [restrictCQ2, restrictStepXMZ, if_pos hm] at h_eq
          dsimp [v0]
          rw [h_eq, zmod2_add_self]
        · rfl
      · have h_min_eq : min A B = A := Nat.min_eq_left hAB
        change 3 * A ≤ _
        rw [← h_min_eq]
        exact h_min_bound
    · refine ⟨v1, starCleanerCandidate1_support pcode M h1 q0, ?_, ?_, fun hc => False.elim (h_zero_S hc)⟩
      · ext mZ
        dsimp [restrictCQ2, restrictStepXMZ]
        split_ifs with hm
        · rw [map_add, Pi.add_apply]
          have h_eq := congr_fun (restrictCQ2_syndrome_starCleanerCandidate1_eq pcode M h1 q0 h_zero_X) mZ
          simp only [restrictCQ2, restrictStepXMZ, if_pos hm] at h_eq
          dsimp [v1]
          rw [h_eq, zmod2_add_self]
        · rfl
      · have h_min_eq : min A B = B := Nat.min_eq_right (le_of_not_ge hAB)
        change 3 * B ≤ _
        rw [← h_min_eq]
        exact h_min_bound

end BDLDecoder
end WeldedHierarchy
