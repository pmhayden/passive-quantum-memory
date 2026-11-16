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

import Proofs.HierarchicalClusterDecoder.CoarseSyndromeExactness

/-!
# Two-Hop Bipartite Tanner Contraction and Fine Pool Cardinality Bounds

Composes the 4/3 Stage-1 cylinder bound, 4/3 Stage-2 star bound, and 1/3 three-layer replication factor to prove the 16/27 syndrome weight contraction on cleaner-closed Tanner components (`rxCleanedCoarseSyndrome_component_contraction`) and two-hop neighborhoods (`rxCleanedCoarseSyndrome_twoHop_contraction`). Bounds the fiber and pool cardinalities of `fineTwoHopPool` (`card_fineTwoHopPool_le`) under uniform check degree bounds.

## References

* Part I, Section 4.3 (`subsec:stage2-star`), Theorem 4.3 (`thm:16-27-contraction`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Stage-1 Exported Star Weight Sums -/

/-- Expands the stage-1 updated `CQ2` syndrome on star `q0` as a sum over incident cylinders in `KX`. -/
lemma s1_cq2_eq_sum_KX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X))
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
      inVX x ∈ K)
    (q0 : Q) (hq0_K : inVQ q0 ∈ K) (mZQ : BDLCQ2 pcode M) (hmZQ : cQ2OwnerQ pcode M mZQ = q0) :
    (S + syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanStage1X pcode M S))
      (Sum.inr (Sum.inl mZQ)) =
    S (Sum.inr (Sum.inl mZQ)) +
      ∑ x ∈ Finset.univ.filter (fun x : M_X => inVX x ∈ K),
        exportXQ pcode M (cleanCylinderX pcode M S x) mZQ := by
  have h_eq_exp : ∀ x : M_X,
      syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x) (Sum.inr (Sum.inl mZQ)) =
        exportXQ pcode M (cleanCylinderX pcode M S x) mZQ := by
    intro x
    unfold exportXQ
    rw [splitStepXQ_X_cleanCylinderX]
  rw [Pi.add_apply]
  congr 1
  dsimp [cleanStage1X]
  rw [map_sum, Finset.sum_apply]
  simp_rw [h_eq_exp]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx_not
  by_contra h_exp_nz
  have h_rest_nz : restrictCQ2 pcode M q0
      (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 := by
    intro h0
    have h_at := congr_fun h0 (Sum.inr (Sum.inl mZQ))
    dsimp [restrictCQ2, restrictStepXMZ] at h_at
    have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl mZQ)) ∈ ({inVQ q0} : Finset _) := by
      simp [stepXMZOwnerTanner, hmZQ]
    rw [if_pos hm, h_eq_exp] at h_at
    exact h_exp_nz h_at
  have h_chk : pcode.checkX x q0 ≠ 0 := by
    intro h_chk0
    exact h_rest_nz (restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero pcode M x q0 h_chk0
      (cleanCylinderX pcode M S x) (cleanCylinderX_support pcode M S x))
  have hx_K : inVX x ∈ K := hK_Q_to_X q0 x hq0_K h_chk h_rest_nz
  exact hx_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_K⟩)

/-- Expresses `weightNetCQ2OnStar` in terms of filtered active Z-edge cardinalities. -/
lemma weightNetCQ2OnStar_eq_cards {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S1 : BDLStepXMZ pcode M → ZMod 2) :
    weightNetCQ2OnStar pcode M q0 S1 =
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
        p.1.val.1 = q0 ∧ (∑ k : Fin (M + 1), S1 (Sum.inr (Sum.inl (Sum.inl (p.1, k, p.2))))) ≠ 0)).card +
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
        p.1.val.1 = q0 ∧ S1 (Sum.inr (Sum.inl (Sum.inr (p.1, p.2)))) ≠ 0)).card := by
  dsimp [weightNetCQ2OnStar]
  rw [Finset.sum_add_distrib, Finset.card_filter, Finset.card_filter,
      Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_filter, Finset.sum_filter]
  congr 1
  · apply Finset.sum_congr rfl; intro eZ _
    by_cases heZ : eZ.val.1 = q0 <;> simp [heZ]
  · apply Finset.sum_congr rfl; intro eZ _
    by_cases heZ : eZ.val.1 = q0 <;> simp [heZ]

/-- Bounds the sum of `weightNetCQ2OnStar` over `KQ` by raw `CQ2` weight plus exported cylinder weight. -/
lemma sum_weightNetCQ2OnStar_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X))
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
      inVX x ∈ K) :
    let D_1 := dualCode (bdlCylinderStepX pcode M)
    let S1 := S + syndrome D_1 (cleanStage1X pcode M S)
    let K_Q := Finset.univ.filter (fun q0 : Q => inVQ q0 ∈ K)
    let K_X := Finset.univ.filter (fun x : M_X => inVX x ∈ K)
    (∑ q0 ∈ K_Q, weightNetCQ2OnStar pcode M q0 S1) ≤
      (∑ q0 ∈ K_Q, weightCQ2OnStarStep pcode M q0 S) +
      (∑ x ∈ K_X, weightNetExportXQ pcode M (cleanCylinderX pcode M S x)) := by
  intro D_1 S1 K_Q K_X
  have h_star : ∀ q0 ∈ K_Q,
      weightNetCQ2OnStar pcode M q0 S1 ≤
        weightCQ2OnStarStep pcode M q0 S +
        ∑ x ∈ K_X,
          ((Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
              p.1.val.1 = q0 ∧
              (∑ k : Fin (M + 1), exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (p.1, k, p.2))) ≠ 0)).card +
           (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
              p.1.val.1 = q0 ∧
              exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inr (p.1, p.2)) ≠ 0)).card) := by
    intro q0 hq0
    have hq0_K : inVQ q0 ∈ K := (Finset.mem_filter.mp hq0).2
    rw [weightNetCQ2OnStar_eq_cards]
    have h_arm : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
        p.1.val.1 = q0 ∧ (∑ k : Fin (M + 1), S1 (Sum.inr (Sum.inl (Sum.inl (p.1, k, p.2))))) ≠ 0)).card ≤
        (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          p.1.val.1 = q0 ∧ S (Sum.inr (Sum.inl (Sum.inl p))) ≠ 0)).card +
        ∑ x ∈ K_X, (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
          p.1.val.1 = q0 ∧
          (∑ k : Fin (M + 1), exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (p.1, k, p.2))) ≠ 0)).card := by
      rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp_rw [Finset.card_filter, Fintype.sum_prod_type]
      rw [Finset.sum_comm (s := K_X), ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro eZ _
      rw [Finset.sum_comm (s := Finset.univ), Finset.sum_comm (s := K_X), ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro b _
      by_cases heZ : eZ.val.1 = q0
      · simp only [heZ, true_and]
        split_ifs with h_sum_nz
        · have h_expand : (∑ k : Fin (M + 1), S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))) =
              (∑ k : Fin (M + 1), S (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))) +
              ∑ x ∈ K_X, ∑ k : Fin (M + 1), exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (eZ, k, b)) := by
            have hk : ∀ k : Fin (M + 1), S1 (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) =
                S (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) +
                ∑ x ∈ K_X, exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (eZ, k, b)) :=
              fun k => s1_cq2_eq_sum_KX pcode M K S hK_Q_to_X q0 hq0_K (Sum.inl (eZ, k, b)) heZ
            simp_rw [hk, Finset.sum_add_distrib]
            congr 1
            exact Finset.sum_comm
          rw [h_expand] at h_sum_nz
          have h1 := one_le_ite_add_sum_ite_of_add_sum_ne_zero K_X
            (∑ k : Fin (M + 1), S (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))))
            (fun x => ∑ k : Fin (M + 1), exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (eZ, k, b)))
            h_sum_nz
          have h2 : (if (∑ k : Fin (M + 1), S (Sum.inr (Sum.inl (Sum.inl (eZ, k, b))))) ≠ 0 then 1 else 0) ≤
              ∑ k : Fin (M + 1), if S (Sum.inr (Sum.inl (Sum.inl (eZ, k, b)))) ≠ 0 then 1 else 0 := by
            split_ifs with hs_nz
            · exact one_le_sum_ite_of_sum_ne_zero Finset.univ _ hs_nz
            · exact Nat.zero_le _
          (try dsimp only [] at h1)
          omega
        · exact Nat.zero_le _
      · simp [heZ]
    have h_vert : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
        p.1.val.1 = q0 ∧ S1 (Sum.inr (Sum.inl (Sum.inr (p.1, p.2)))) ≠ 0)).card ≤
        (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
          p.1.val.1 = q0 ∧ S (Sum.inr (Sum.inl (Sum.inr p))) ≠ 0)).card +
        ∑ x ∈ K_X, (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
          p.1.val.1 = q0 ∧
          exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inr (p.1, p.2)) ≠ 0)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm (s := K_X), ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro ⟨eZ, v⟩ _
      by_cases heZ : eZ.val.1 = q0
      · simp only [heZ, true_and]
        by_cases h_nz : S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) ≠ 0
        · rw [if_pos h_nz]
          have h_s1_v := s1_cq2_eq_sum_KX pcode M K S hK_Q_to_X q0 hq0_K (Sum.inr (eZ, v)) heZ
          change S1 (Sum.inr (Sum.inl (Sum.inr (eZ, v)))) = _ at h_s1_v
          rw [h_s1_v] at h_nz
          exact one_le_ite_add_sum_ite_of_add_sum_ne_zero K_X _ _ h_nz
        · rw [if_neg h_nz]
          exact Nat.zero_le _
      · simp [heZ]
    have h_cq2_eq : weightCQ2OnStarStep pcode M q0 S =
        (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) × Fin 3 =>
          p.1.val.1 = q0 ∧ S (Sum.inr (Sum.inl (Sum.inl p))) ≠ 0)).card +
        (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
          p.1.val.1 = q0 ∧ S (Sum.inr (Sum.inl (Sum.inr p))) ≠ 0)).card := by
      dsimp [weightCQ2OnStarStep]
      rw [Finset.card_filter, Finset.card_filter, Finset.card_filter,
          Fintype.sum_sum_type (α₁ := ActiveZ pcode × Fin (M + 1) × Fin 3)]
      rfl
    rw [h_cq2_eq, Finset.sum_add_distrib]
    omega
  have h_sum := Finset.sum_le_sum h_star
  rw [Finset.sum_add_distrib] at h_sum
  refine h_sum.trans (Nat.add_le_add_left ?_ _)
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro x _
  dsimp [weightNetExportXQ]
  rw [Finset.sum_add_distrib]
  have h1 := sum_owner_subset_le (fun p : ActiveZ pcode × Fin 3 => p.1.val.1)
    (fun p => (∑ k : Fin (M + 1), exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (p.1, k, p.2))) ≠ 0) K_Q
  have h2 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
      p.1.val.1 ∈ K_Q ∧
      (∑ k : Fin (M + 1), exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (p.1, k, p.2))) ≠ 0)).card ≤
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
        (∑ k : Fin (M + 1), exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inl (p.1, k, p.2))) ≠ 0)).card :=
    Finset.card_le_card (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.2⟩)
  have h3 := sum_owner_subset_le (fun p : ActiveZ pcode × Fin 2 => p.1.val.1)
    (fun p => exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inr (p.1, p.2)) ≠ 0) K_Q
  have h4 : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
      p.1.val.1 ∈ K_Q ∧
      exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inr (p.1, p.2)) ≠ 0)).card ≤
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
        exportXQ pcode M (cleanCylinderX pcode M S x) (Sum.inr (p.1, p.2)) ≠ 0)).card :=
    Finset.card_le_card (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.2⟩)
  exact add_le_add (h1.trans h2) (h3.trans h4)

/-! ## 2. Component and Two-Hop Syndrome Contraction -/

/-- Component-wise `16/27` contraction of `rxCleanedCoarseSyndrome` on any backward-export-closed
    Tanner subset `K`. -/
theorem rxCleanedCoarseSyndrome_component_contraction {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hZ : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K : Finset (TannerVertex Q M_Z M_X))
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hS : ∃ h : BDLStepXQ pcode M → ZMod 2,
      syndrome (dualCode (bdlCylinderStepX pcode M)) h = S)
    (hK_Z_to_Q : ∀ z0 : M_Z, ∀ q0 : Q,
      inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (S + syndrome (dualCode (bdlCylinderStepX pcode M))
          (cleanStage1X pcode M S)) q0) (z0, b) ≠ 0) →
      inVQ q0 ∈ K)
    (hK_Q_to_X : ∀ q0 : Q, ∀ x : M_X,
      inVQ q0 ∈ K → pcode.checkX x q0 ≠ 0 →
      restrictCQ2 pcode M q0
        (syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanCylinderX pcode M S x)) ≠ 0 →
      inVX x ∈ K) :
    27 * (activeCoarseZInK pcode M K S).card ≤
      16 * syndromeWeightNat (restrictStepXMZ pcode M K S) := by
  rcases hS with ⟨h, rfl⟩
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S := syndrome D_1 h
  let S1 := S + syndrome D_1 (cleanStage1X pcode M S)
  let K_Z := activeCoarseZInK pcode M K S
  let K_Q := Finset.univ.filter (fun q0 : Q => inVQ q0 ∈ K)
  let K_X := Finset.univ.filter (fun x : M_X => inVX x ∈ K)
  have h_step2 := three_mul_card_activeCoarseZInK_le pcode M hov hZ h_conn K h hK_Z_to_Q
  change 3 * K_Z.card ≤
    (∑ z0 ∈ K_Z, weightCZ2OnCheck pcode M z0 S) +
    (∑ q0 ∈ K_Q, (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
      exportQZ pcode M (cleanStarQ pcode M S1 q0) mZZ ≠ 0)).card) at h_step2
  have h1_cyl : ∀ x : M_X,
      restrictCX2 pcode M x (syndrome D_1 (h + cleanStage1X pcode M S)) = 0 :=
    restrictCX2_syndrome_add_cleanStage1X_eq_zero pcode M hov h_conn h
  have h_star_spec : ∀ q0 ∈ K_Q,
      3 * (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
        exportQZ pcode M (cleanStarQ pcode M S1 q0) mZZ ≠ 0)).card ≤
        4 * weightNetCQ2OnStar pcode M q0 S1 := by
    intro q0 _
    have h_s1_eq : S1 = syndrome D_1 (h + cleanStage1X pcode M S) :=
      (map_add (syndrome D_1) h (cleanStage1X pcode M S)).symm
    rw [h_s1_eq]
    exact (cleanStarQ_spec pcode M hov h_conn (h + cleanStage1X pcode M S) h1_cyl q0).2.2.1
  have h_sum_star := Finset.sum_le_sum h_star_spec
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h_sum_star
  have h_step3 := sum_weightNetCQ2OnStar_le pcode M K S hK_Q_to_X
  change (∑ q0 ∈ K_Q, weightNetCQ2OnStar pcode M q0 S1) ≤
    (∑ q0 ∈ K_Q, weightCQ2OnStarStep pcode M q0 S) +
    (∑ x ∈ K_X, weightNetExportXQ pcode M (cleanCylinderX pcode M S x)) at h_step3
  have h_cyl_spec : ∀ x ∈ K_X,
      3 * weightNetExportXQ pcode M (cleanCylinderX pcode M S x) ≤
        4 * weightCX2OnCyl pcode M x S :=
    fun x _ => (cleanCylinderX_spec pcode M hov h_conn h x).2.2
  have h_sum_cyl := Finset.sum_le_sum h_cyl_spec
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h_sum_cyl
  have h_step1 := syndromeWeightNat_restrictStepXMZ_ge pcode M K S
  change (∑ x ∈ K_X, weightCX2OnCyl pcode M x S) +
    (∑ q0 ∈ K_Q, weightCQ2OnStarStep pcode M q0 S) +
    (∑ z0 ∈ K_Z, weightCZ2OnCheck pcode M z0 S) ≤
      syndromeWeightNat (restrictStepXMZ pcode M K S) at h_step1
  change 27 * K_Z.card ≤ 16 * syndromeWeightNat (restrictStepXMZ pcode M K S)
  omega

/-- 1-hop coarse qubit neighborhood of a coarse Z-check subset `K_Z`. -/
def oneHopQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (K_Z : Finset M_Z) : Finset Q :=
  Finset.univ.filter (fun q0 : Q => ∃ z0 ∈ K_Z, pcode.checkZ z0 q0 ≠ 0)

/-- 2-hop coarse X-check neighborhood of a coarse Z-check subset `K_Z`. -/
def twoHopX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (K_Z : Finset M_Z) : Finset M_X :=
  Finset.univ.filter (fun x : M_X => ∃ q0 ∈ oneHopQ pcode K_Z, pcode.checkX x q0 ≠ 0)

/-- Deterministic 2-hop Tanner neighborhood of a coarse Z-check subset `K_Z`. -/
def twoHopTannerOfZ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (K_Z : Finset M_Z) :
    Finset (TannerVertex Q M_Z M_X) :=
  (twoHopX pcode K_Z).image inVX ∪ (oneHopQ pcode K_Z).image inVQ ∪ K_Z.image inVZ

/-- Characterization of `inVZ z` membership in `twoHopTannerOfZ pcode KZ`. -/
lemma inVZ_mem_twoHopTannerOfZ_iff {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (K_Z : Finset M_Z) (z0 : M_Z) :
    inVZ z0 ∈ twoHopTannerOfZ pcode K_Z ↔ z0 ∈ K_Z := by
  simp [twoHopTannerOfZ, inVX, inVQ, inVZ]

/-- Characterization of `inVQ q` membership in `twoHopTannerOfZ pcode KZ`. -/
lemma inVQ_mem_twoHopTannerOfZ_iff {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (K_Z : Finset M_Z) (q0 : Q) :
    inVQ q0 ∈ twoHopTannerOfZ pcode K_Z ↔ q0 ∈ oneHopQ pcode K_Z := by
  simp [twoHopTannerOfZ, inVX, inVQ, inVZ]

/-- Characterization of `inVX x` membership in `twoHopTannerOfZ pcode KZ`. -/
lemma inVX_mem_twoHopTannerOfZ_iff {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (K_Z : Finset M_Z) (x : M_X) :
    inVX x ∈ twoHopTannerOfZ pcode K_Z ↔ x ∈ twoHopX pcode K_Z := by
  simp [twoHopTannerOfZ, inVX, inVQ, inVZ]

/-- If every `z0 ∈ K_Z` is active in `rxCleanedCoarseSyndrome pcode M S`, then the deterministic
    2-hop Tanner neighborhood `twoHopTannerOfZ pcode K_Z` contains at least `(27 * K_Z.card + 15) / 16`
    active fine Z-checks of `S`. -/
theorem rxCleanedCoarseSyndrome_twoHop_contraction {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hZ : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K_Z : Finset M_Z)
    (S : BDLStepXMZ pcode M → ZMod 2)
    (hS : ∃ h : BDLStepXQ pcode M → ZMod 2,
      syndrome (dualCode (bdlCylinderStepX pcode M)) h = S)
    (hKZ_active : ∀ z0 ∈ K_Z, rxCleanedCoarseSyndrome pcode M S z0 ≠ 0) :
    27 * K_Z.card ≤
      16 * syndromeWeightNat (restrictStepXMZ pcode M (twoHopTannerOfZ pcode K_Z) S) := by
  have h_sub : K_Z ⊆ activeCoarseZInK pcode M (twoHopTannerOfZ pcode K_Z) S := by
    intro z0 hz0
    rw [activeCoarseZInK, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (inVZ_mem_twoHopTannerOfZ_iff pcode K_Z z0).mpr hz0, hKZ_active z0 hz0⟩
  have h_card : K_Z.card ≤ (activeCoarseZInK pcode M (twoHopTannerOfZ pcode K_Z) S).card :=
    Finset.card_le_card h_sub
  have h_comp := rxCleanedCoarseSyndrome_component_contraction pcode M hov hZ h_conn
    (twoHopTannerOfZ pcode K_Z) S hS
    (fun z0 q0 hz0 h_chk _ => by
      rw [inVZ_mem_twoHopTannerOfZ_iff] at hz0
      rw [inVQ_mem_twoHopTannerOfZ_iff, oneHopQ, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, z0, hz0, h_chk⟩)
    (fun q0 x hq0 h_chk _ => by
      rw [inVQ_mem_twoHopTannerOfZ_iff] at hq0
      rw [inVX_mem_twoHopTannerOfZ_iff, twoHopX, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, q0, hq0, h_chk⟩)
  omega

/-! ## 3. Fine Two-Hop Syndrome Pool and Degree Cardinality Bounds -/

/-- Fixed, `S`-independent fine Z-check pool of `K_Z`. -/
def fineTwoHopPool {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (K_Z : Finset M_Z) :
    Finset (BDLStepXMZ pcode M) :=
  Finset.univ.filter (fun mZ => stepXMZOwnerTanner pcode M mZ ∈ twoHopTannerOfZ pcode K_Z)

/-- Identifies `syndromeWeightNat` on `twoHopTannerOfZ` with the active subset cardinality in `fineTwoHopPool`. -/
lemma syndromeWeightNat_restrictStepXMZ_eq_card_filter_fineTwoHopPool {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (K_Z : Finset M_Z)
    (S : BDLStepXMZ pcode M → ZMod 2) :
    syndromeWeightNat (restrictStepXMZ pcode M (twoHopTannerOfZ pcode K_Z) S) =
      ((fineTwoHopPool pcode M K_Z).filter (fun mZ => S mZ ≠ 0)).card := by
  dsimp [syndromeWeightNat, fineTwoHopPool, restrictStepXMZ]
  rw [Finset.filter_filter]
  congr 1
  ext mZ
  by_cases hm : stepXMZOwnerTanner pcode M mZ ∈ twoHopTannerOfZ pcode K_Z <;> simp [hm]

/-- Bounds `(oneHopQ pcode KZ).card` by `d_Z * KZ.card` under bounded Z-check degree. -/
lemma card_oneHopQ_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (dZ : ℕ)
    (hdZ : ∀ z0 : M_Z, (Finset.univ.filter (fun q0 : Q => pcode.checkZ z0 q0 ≠ 0)).card ≤ dZ)
    (K_Z : Finset M_Z) :
    (oneHopQ pcode K_Z).card ≤ dZ * K_Z.card := by
  have h_sub : oneHopQ pcode K_Z ⊆
      K_Z.biUnion (fun z0 => Finset.univ.filter (fun q0 : Q => pcode.checkZ z0 q0 ≠ 0)) := by
    intro q0 hq0
    rw [oneHopQ, Finset.mem_filter] at hq0
    rcases hq0.2 with ⟨z0, hz0, hchk⟩
    exact Finset.mem_biUnion.mpr ⟨z0, hz0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchk⟩⟩
  calc (oneHopQ pcode K_Z).card
    _ ≤ (K_Z.biUnion (fun z0 => Finset.univ.filter (fun q0 : Q => pcode.checkZ z0 q0 ≠ 0))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ z0 ∈ K_Z, (Finset.univ.filter (fun q0 : Q => pcode.checkZ z0 q0 ≠ 0)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _z0 ∈ K_Z, dZ := Finset.sum_le_sum (fun z0 _ => hdZ z0)
    _ = dZ * K_Z.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Bounds `(twoHopX pcode KZ).card` by `d_Q_X * (oneHopQ pcode KZ).card` under bounded qubit X-degree. -/
lemma card_twoHopX_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (dQX : ℕ)
    (hdQX : ∀ q0 : Q, (Finset.univ.filter (fun x : M_X => pcode.checkX x q0 ≠ 0)).card ≤ dQX)
    (K_Z : Finset M_Z) :
    (twoHopX pcode K_Z).card ≤ dQX * (oneHopQ pcode K_Z).card := by
  have h_sub : twoHopX pcode K_Z ⊆
      (oneHopQ pcode K_Z).biUnion (fun q0 => Finset.univ.filter (fun x : M_X => pcode.checkX x q0 ≠ 0)) := by
    intro x hx
    rw [twoHopX, Finset.mem_filter] at hx
    rcases hx.2 with ⟨q0, hq0, hchk⟩
    exact Finset.mem_biUnion.mpr ⟨q0, hq0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchk⟩⟩
  calc (twoHopX pcode K_Z).card
    _ ≤ ((oneHopQ pcode K_Z).biUnion (fun q0 => Finset.univ.filter (fun x : M_X => pcode.checkX x q0 ≠ 0))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ q0 ∈ oneHopQ pcode K_Z, (Finset.univ.filter (fun x : M_X => pcode.checkX x q0 ≠ 0)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q0 ∈ oneHopQ pcode K_Z, dQX := Finset.sum_le_sum (fun q0 _ => hdQX q0)
    _ = dQX * (oneHopQ pcode K_Z).card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- Bounds `(twoHopTannerOfZ pcode KZ).card` by `(1 + d_Z + d_Z * d_Q_X) * KZ.card`. -/
lemma card_twoHopTannerOfZ_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X)
    (hdZ : ∀ z0 : M_Z, (Finset.univ.filter (fun q0 : Q => pcode.checkZ z0 q0 ≠ 0)).card ≤ 8)
    (hdQX : ∀ q0 : Q, (Finset.univ.filter (fun x : M_X => pcode.checkX x q0 ≠ 0)).card ≤ 4)
    (K_Z : Finset M_Z) :
    (twoHopTannerOfZ pcode K_Z).card ≤ 41 * K_Z.card := by
  dsimp [twoHopTannerOfZ]
  have h1 := Finset.card_union_le
    ((twoHopX pcode K_Z).image (inVX : M_X → TannerVertex Q M_Z M_X) ∪
     (oneHopQ pcode K_Z).image (inVQ : Q → TannerVertex Q M_Z M_X))
    (K_Z.image (inVZ : M_Z → TannerVertex Q M_Z M_X))
  have h2 := Finset.card_union_le
    ((twoHopX pcode K_Z).image (inVX : M_X → TannerVertex Q M_Z M_X))
    ((oneHopQ pcode K_Z).image (inVQ : Q → TannerVertex Q M_Z M_X))
  have hX := Finset.card_image_le (s := twoHopX pcode K_Z) (f := (inVX : M_X → TannerVertex Q M_Z M_X))
  have hQ := Finset.card_image_le (s := oneHopQ pcode K_Z) (f := (inVQ : Q → TannerVertex Q M_Z M_X))
  have hZ := Finset.card_image_le (s := K_Z) (f := (inVZ : M_Z → TannerVertex Q M_Z M_X))
  have h_one := card_oneHopQ_le pcode 8 hdZ K_Z
  have h_two := card_twoHopX_le pcode 4 hdQX K_Z
  omega

/-! ## 4. Tanner Owner Fiber Injections and Pool Size Bound -/

/-- Injection from the `stepXMZOwnerTanner` fiber over `inVX x0` into a finite sum type. -/
def stepXMZTannerFiberXToSum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    {mZ : BDLStepXMZ pcode M // stepXMZOwnerTanner pcode M mZ = inVX x0} →
      ({s : ActiveSimplex2 pcode // s.val.1 = x0} × Fin (M + 1) × Fin (M + 1) × Fin 3) ⊕
      ({s : ActiveSimplex2 pcode // s.val.1 = x0} × Fin (M + 1) × Fin 2)
  | ⟨Sum.inl (Sum.inl (⟨(⟨(x, ⟨(q, z), hZ⟩), hX⟩, r, k), _⟩, b)), h⟩ =>
      Sum.inl (⟨⟨(x, q, z), ⟨hX, hZ⟩⟩, Sum.inl.inj h⟩, r, k, b)
  | ⟨Sum.inl (Sum.inr (⟨(x, ⟨(q, z), hZ⟩), hX⟩, k, b)), h⟩ =>
      Sum.inr (⟨⟨(x, q, z), ⟨hX, hZ⟩⟩, Sum.inl.inj h⟩, k, b)
  | ⟨Sum.inr (Sum.inl _), h⟩ => nomatch h
  | ⟨Sum.inr (Sum.inr _), h⟩ => nomatch h

/-- Injectivity of `stepXMZTannerFiberXToSum`. -/
lemma stepXMZTannerFiberXToSum_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) :
    Function.Injective (stepXMZTannerFiberXToSum pcode M x0) := by
  rintro ⟨mZX1 | (mZQ1 | mZZ1), h1⟩ ⟨mZX2 | (mZQ2 | mZZ2), h2⟩ h
  · rcases mZX1 with ⟨⟨⟨⟨⟨x1, ⟨⟨q1, z1⟩, hZ1⟩⟩, hX1⟩, r1, k1⟩, hs1⟩, b1⟩ |
                     ⟨⟨⟨x1, ⟨⟨q1, z1⟩, hZ1⟩⟩, hX1⟩, k1, b1⟩ <;>
    rcases mZX2 with ⟨⟨⟨⟨⟨x2, ⟨⟨q2, z2⟩, hZ2⟩⟩, hX2⟩, r2, k2⟩, hs2⟩, b2⟩ |
                     ⟨⟨⟨x2, ⟨⟨q2, z2⟩, hZ2⟩⟩, hX2⟩, k2, b2⟩
    · dsimp [stepXMZTannerFiberXToSum] at h
      injection h with hp
      have hx : x1 = x2 := (Sum.inl.inj h1).trans (Sum.inl.inj h2).symm
      have hq : q1 = q2 := congr_arg (fun u => u.1.val.val.2.1) hp
      have hz : z1 = z2 := congr_arg (fun u => u.1.val.val.2.2) hp
      have hr : r1 = r2 := congr_arg (fun u => u.2.1) hp
      have hk : k1 = k2 := congr_arg (fun u => u.2.2.1) hp
      have hb : b1 = b2 := congr_arg (fun u => u.2.2.2) hp
      subst hx hq hz hr hk hb; rfl
    · nomatch h
    · nomatch h
    · dsimp [stepXMZTannerFiberXToSum] at h
      injection h with hp
      have hx : x1 = x2 := (Sum.inl.inj h1).trans (Sum.inl.inj h2).symm
      have hq : q1 = q2 := congr_arg (fun u => u.1.val.val.2.1) hp
      have hz : z1 = z2 := congr_arg (fun u => u.1.val.val.2.2) hp
      have hk : k1 = k2 := congr_arg (fun u => u.2.1) hp
      have hb : b1 = b2 := congr_arg (fun u => u.2.2) hp
      subst hx hq hz hk hb; rfl
  · nomatch h2
  · nomatch h2
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h1

/-- Injection from the `stepXMZOwnerTanner` fiber over `inVQ q0` into a finite sum type. -/
def stepXMZTannerFiberQToSum {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q) :
    {mZ : BDLStepXMZ pcode M // stepXMZOwnerTanner pcode M mZ = inVQ q0} →
      ({z : M_Z // pcode.checkZ z q0 ≠ 0} × Fin (M + 1) × Fin 3) ⊕
      ({z : M_Z // pcode.checkZ z q0 ≠ 0} × Fin 2)
  | ⟨Sum.inl _, h⟩ => nomatch h
  | ⟨Sum.inr (Sum.inl (Sum.inl (⟨(_, z), hZ⟩, k, b))), h⟩ =>
      Sum.inl (⟨z, (Sum.inl.inj (Sum.inr.inj h)) ▸ hZ⟩, k, b)
  | ⟨Sum.inr (Sum.inl (Sum.inr (⟨(_, z), hZ⟩, b))), h⟩ =>
      Sum.inr (⟨z, (Sum.inl.inj (Sum.inr.inj h)) ▸ hZ⟩, b)
  | ⟨Sum.inr (Sum.inr _), h⟩ => nomatch h

/-- Injectivity of `stepXMZTannerFiberQToSum`. -/
lemma stepXMZTannerFiberQToSum_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q) :
    Function.Injective (stepXMZTannerFiberQToSum pcode M q0) := by
  rintro ⟨mZX1 | (mZQ1 | mZZ1), h1⟩ ⟨mZX2 | (mZQ2 | mZZ2), h2⟩ h
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h2
  · rcases mZQ1 with ⟨⟨⟨q1, z1⟩, hZ1⟩, k1, b1⟩ | ⟨⟨⟨q1, z1⟩, hZ1⟩, b1⟩ <;>
    rcases mZQ2 with ⟨⟨⟨q2, z2⟩, hZ2⟩, k2, b2⟩ | ⟨⟨⟨q2, z2⟩, hZ2⟩, b2⟩
    · dsimp [stepXMZTannerFiberQToSum] at h
      injection h with hp
      have hq : q1 = q2 := (Sum.inl.inj (Sum.inr.inj h1)).trans (Sum.inl.inj (Sum.inr.inj h2)).symm
      have hz : z1 = z2 := congr_arg (fun u => u.1.val) hp
      have hk : k1 = k2 := congr_arg (fun u => u.2.1) hp
      have hb : b1 = b2 := congr_arg (fun u => u.2.2) hp
      subst hq hz hk hb; rfl
    · nomatch h
    · nomatch h
    · dsimp [stepXMZTannerFiberQToSum] at h
      injection h with hp
      have hq : q1 = q2 := (Sum.inl.inj (Sum.inr.inj h1)).trans (Sum.inl.inj (Sum.inr.inj h2)).symm
      have hz : z1 = z2 := congr_arg (fun u => u.1.val) hp
      have hb : b1 = b2 := congr_arg Prod.snd hp
      subst hq hz hb; rfl
  · nomatch h2
  · nomatch h1
  · nomatch h1
  · nomatch h1

/-- Projection from the `stepXMZOwnerTanner` fiber over `inVZ z0` into `Fin 3`. -/
def stepXMZTannerFiberZToFin {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (z0 : M_Z) :
    {mZ : BDLStepXMZ pcode M // stepXMZOwnerTanner pcode M mZ = inVZ z0} → Fin 3
  | ⟨Sum.inl _, h⟩ => nomatch h
  | ⟨Sum.inr (Sum.inl _), h⟩ => nomatch h
  | ⟨Sum.inr (Sum.inr (_, b)), _⟩ => b

/-- Injectivity of `stepXMZTannerFiberZToFin`. -/
lemma stepXMZTannerFiberZToFin_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (z0 : M_Z) :
    Function.Injective (stepXMZTannerFiberZToFin pcode M z0) := by
  rintro ⟨mZX1 | (mZQ1 | ⟨z1, b1⟩), h1⟩ ⟨mZX2 | (mZQ2 | ⟨z2, b2⟩), h2⟩ h
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h1
  · nomatch h2
  · nomatch h2
  · dsimp [stepXMZTannerFiberZToFin] at h
    have hz : z1 = z2 := (Sum.inr.inj (Sum.inr.inj h1)).trans (Sum.inr.inj (Sum.inr.inj h2)).symm
    subst hz h; rfl

/-- Bounds every fiber of `stepXMZOwnerTanner` by `bdlSingleStepFactor`. -/
lemma card_fiber_stepXMZOwnerTanner_le_bdlSingleStepFactor (B : BundledCSSCode3D)
    (hdeg : HasBoundedCheckDegree B 8 8 4 4)
    (hsimp : HasBoundedSimplexDegreeD B 32)
    {lam : ℕ} {cQ : B.Q → Point3D} {cZ : B.M_Z → Point3D} {cX : B.M_X → Point3D}
    (v : TannerVertex B.Q B.M_Z B.M_X) :
    let pcode := bdlPerturbStep B.code lam cQ cZ cX
    (Finset.univ.filter (fun mZ : BDLStepXMZ pcode bdlSubdivPred =>
      stepXMZOwnerTanner pcode bdlSubdivPred mZ = v)).card ≤ bdlSingleStepFactor := by
  intro pcode
  let M := bdlSubdivPred
  have hM_eq : M + 1 = bdlSubdivM := bdlSubdivM_eq_succ
  have hM_ge : 2 ≤ M + 1 := by rw [hM_eq]; exact bdlSubdivM_ge_two
  rw [← Fintype.card_subtype]
  rcases v with x0 | (q0 | z0)
  · have h_simp_card : Fintype.card {s : ActiveSimplex2 pcode // s.val.1 = x0} ≤ 32 := by
      rw [Fintype.card_subtype]; exact hsimp.1 x0
    have h_inj := Fintype.card_le_of_injective (stepXMZTannerFiberXToSum pcode M x0)
      (stepXMZTannerFiberXToSum_injective pcode M x0)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h_inj
    change Fintype.card {mZ : BDLStepXMZ pcode M // stepXMZOwnerTanner pcode M mZ = inVX x0} ≤ bdlSingleStepFactor
    dsimp [bdlSingleStepFactor, _root_.bdlSingleStepFactor]; rw [← hM_eq]; nlinarith
  · have h_z_card : Fintype.card {z : B.M_Z // pcode.checkZ z q0 ≠ 0} ≤ 4 := by
      rw [Fintype.card_subtype]; exact hdeg.2.2.2 q0
    have h_inj := Fintype.card_le_of_injective (stepXMZTannerFiberQToSum pcode M q0)
      (stepXMZTannerFiberQToSum_injective pcode M q0)
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h_inj
    change Fintype.card {mZ : BDLStepXMZ pcode M // stepXMZOwnerTanner pcode M mZ = inVQ q0} ≤ bdlSingleStepFactor
    dsimp [bdlSingleStepFactor, _root_.bdlSingleStepFactor]; rw [← hM_eq]; nlinarith
  · have h_inj := Fintype.card_le_of_injective (stepXMZTannerFiberZToFin pcode M z0)
      (stepXMZTannerFiberZToFin_injective pcode M z0)
    simp only [Fintype.card_fin] at h_inj
    change Fintype.card {mZ : BDLStepXMZ pcode M // stepXMZOwnerTanner pcode M mZ = inVZ z0} ≤ bdlSingleStepFactor
    dsimp [bdlSingleStepFactor, _root_.bdlSingleStepFactor]; rw [← hM_eq]; nlinarith

/-- Bounds `(fineTwoHopPool B.code bdlLambda KZ).card` by `(41 * bdlSingleStepFactor) * KZ.card`. -/
lemma card_fineTwoHopPool_le (B : BundledCSSCode3D)
    (hdeg : HasBoundedCheckDegree B 8 8 4 4)
    (hsimp : HasBoundedSimplexDegreeD B 32)
    {lam : ℕ} {cQ : B.Q → Point3D} {cZ : B.M_Z → Point3D} {cX : B.M_X → Point3D}
    (K_Z : Finset B.M_Z) :
    let pcode := bdlPerturbStep B.code lam cQ cZ cX
    (fineTwoHopPool pcode bdlSubdivPred K_Z).card ≤
      41 * bdlSingleStepFactor * K_Z.card := by
  intro pcode
  let M := bdlSubdivPred
  have h_sub : fineTwoHopPool pcode M K_Z ⊆
      (twoHopTannerOfZ pcode K_Z).biUnion (fun v =>
        Finset.univ.filter (fun mZ : BDLStepXMZ pcode M => stepXMZOwnerTanner pcode M mZ = v)) := by
    intro mZ hmZ
    rw [fineTwoHopPool, Finset.mem_filter] at hmZ
    exact Finset.mem_biUnion.mpr ⟨stepXMZOwnerTanner pcode M mZ, hmZ.2,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have h_tan := card_twoHopTannerOfZ_le pcode hdeg.2.1 hdeg.2.2.1 K_Z
  calc (fineTwoHopPool pcode M K_Z).card
    _ ≤ ((twoHopTannerOfZ pcode K_Z).biUnion (fun v =>
          Finset.univ.filter (fun mZ : BDLStepXMZ pcode M => stepXMZOwnerTanner pcode M mZ = v))).card :=
      Finset.card_le_card h_sub
    _ ≤ ∑ v ∈ twoHopTannerOfZ pcode K_Z,
          (Finset.univ.filter (fun mZ : BDLStepXMZ pcode M => stepXMZOwnerTanner pcode M mZ = v)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ twoHopTannerOfZ pcode K_Z, bdlSingleStepFactor :=
      Finset.sum_le_sum (fun v _ => card_fiber_stepXMZOwnerTanner_le_bdlSingleStepFactor B hdeg hsimp v)
    _ = (twoHopTannerOfZ pcode K_Z).card * bdlSingleStepFactor := by
      rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (41 * K_Z.card) * bdlSingleStepFactor :=
      Nat.mul_le_mul_right bdlSingleStepFactor h_tan
    _ = 41 * bdlSingleStepFactor * K_Z.card := by ring

end BDLDecoder
end WeldedHierarchy
