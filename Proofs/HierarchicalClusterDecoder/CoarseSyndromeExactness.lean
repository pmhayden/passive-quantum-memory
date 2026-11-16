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

import Proofs.HierarchicalClusterDecoder.TwoStageCleanerComposition

/-!
# Coarse Syndrome Exactness and Restricted Z-Check Multiplicity Bounds

Proves exact homology-to-coarse syndrome intertwining (`rxCleanedCoarseProj_syndrome_eq`) after two-stage cleaning across a three-layer cylinder step. Establishes the three-layer replication lower bound (`three_mul_card_activeCoarseZInK_le`) and Tanner-component syndrome weight decomposition (`syndromeWeightNat_restrictStepXMZ_ge`) needed for the 16/27 bipartite contraction.

## References

* Part I, Section 4.1 (`subsec:cleaner-architecture`)
* Part I, Section 4.3 (`subsec:stage2-star`), Lemma 4.2 (`lem:stage2-star-cleaner`), Theorem 4.3 (`thm:16-27-contraction`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Coarse Syndrome Compatibility of Two-Stage Cleaning -/

/-- When all cylinder (`CX2`) and star (`CQ2`) syndromes vanish, the vertical `CZ2` syndrome is constant across copies and equals the coarse syndrome. -/
lemma syndrome_cz2_eq_coarse_of_cx2_cq2_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q, ∃ z, pcode.checkZ z q ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (h2 : BDLStepXQ pcode M → ZMod 2)
    (h2_X : ∀ x : M_X, restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h2) = 0)
    (h2_Q : ∀ q0 : Q, restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) h2) = 0)
    (z0 : M_Z) (b : Fin 3) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) h2 (Sum.inr (Sum.inr (z0, b))) =
      syndrome (dualCode pcode) (projCylinderLXLayer pcode M 0 h2) z0 := by
  have h_zero_X : ∀ (x : M_X) (qX : BDLCX1 pcode M), qXOwnerX pcode M qX = x →
      cylinderResidualCocycle pcode M h2 (Sum.inl qX) = 0 := by
    intro x qX hqX
    apply cylinderResidualCocycle_inl_eq_zero pcode M hov h_conn h2 x _ _ qX hqX
    · intro seg b' hseg
      have h_eq := congr_fun (h2_X x) (Sum.inl (Sum.inl (seg, b')))
      dsimp [restrictCX2, restrictStepXMZ] at h_eq
      have hm : stepXMZOwnerTanner pcode M (Sum.inl (Sum.inl (seg, b'))) ∈ ({inVX x} : Finset _) := by
        simp [stepXMZOwnerTanner, cX2OwnerX, cX2OwnerLink, inVX, hseg]
      rw [if_pos hm] at h_eq
      exact h_eq
    · intro s' k' b' hs'
      have h_eq := congr_fun (h2_X x) (Sum.inl (Sum.inr (s', k', b')))
      dsimp [restrictCX2, restrictStepXMZ] at h_eq
      have hm : stepXMZOwnerTanner pcode M (Sum.inl (Sum.inr (s', k', b'))) ∈ ({inVX x} : Finset _) := by
        simp [stepXMZOwnerTanner, cX2OwnerX, cX2OwnerLink, inVX, hs']
      rw [if_pos hm] at h_eq
      exact h_eq
  have h_term : ∀ eZ : ActiveZ pcode,
      cylinderResidualCocycle pcode M h2 (Sum.inr (Sum.inr (Sum.inr eZ), b)) =
        coarseProjCocycle pcode M h2 eZ.val.1 := by
    intro eZ
    apply cylinderResidualCocycle_inr_eq_coarse pcode M hq_z h2 eZ.val.1
    · intro x _ qX hqX
      exact h_zero_X x qX hqX
    · intro eZ' k b' heZ'
      have h_q := congr_fun (h2_Q eZ.val.1) (Sum.inr (Sum.inl (Sum.inl (eZ', k, b'))))
      dsimp [restrictCQ2, restrictStepXMZ] at h_q
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inl (eZ', k, b')))) ∈ ({inVQ eZ.val.1} : Finset _) := by
        simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, heZ']
      rw [if_pos hm] at h_q
      exact h_q
    · intro eZ' v' heZ'
      have h_q := congr_fun (h2_Q eZ.val.1) (Sum.inr (Sum.inl (Sum.inr (eZ', v'))))
      dsimp [restrictCQ2, restrictStepXMZ] at h_q
      have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl (Sum.inr (eZ', v')))) ∈ ({inVQ eZ.val.1} : Finset _) := by
        simp [stepXMZOwnerTanner, cQ2OwnerQ, cQ2OwnerActiveZ, inVQ, heZ']
      rw [if_pos hm] at h_q
      exact h_q
    · rfl
  have h_syn_res : syndrome (dualCode (bdlCylinderStepX pcode M)) h2 (Sum.inr (Sum.inr (z0, b))) =
      syndrome (dualCode (bdlCylinderStepX pcode M)) (cylinderResidualCocycle pcode M h2)
        (Sum.inr (Sum.inr (z0, b))) := by
    dsimp [cylinderResidualCocycle, apexResidualCocycle]
    rw [syndrome_add_checkGen_dual, syndrome_add_checkGen_dual]
  rw [h_syn_res]
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hX : (∑ qX : BDLCX1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, b))) (Sum.inl qX) *
        cylinderResidualCocycle pcode M h2 (Sum.inl qX)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => zero_mul _)
  rw [hX, zero_add, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single b]
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    have h_inl : (∑ q : Q, bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, b))) (Sum.inr (Sum.inl q, b)) *
        cylinderResidualCocycle pcode M h2 (Sum.inr (Sum.inl q, b))) = 0 :=
      Finset.sum_eq_zero (fun _ _ => zero_mul _)
    have h_mid : (∑ p : ActiveZ pcode × Fin M,
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, b))) (Sum.inr (Sum.inr (Sum.inl p), b)) *
          cylinderResidualCocycle pcode M h2 (Sum.inr (Sum.inr (Sum.inl p), b))) = 0 :=
      Finset.sum_eq_zero (fun _ _ => zero_mul _)
    rw [h_inl, zero_add, h_mid, zero_add]
    have h_active : ∀ eZ : ActiveZ pcode,
        bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, b))) (Sum.inr (Sum.inr (Sum.inr eZ), b)) *
          cylinderResidualCocycle pcode M h2 (Sum.inr (Sum.inr (Sum.inr eZ), b)) =
        if eZ.val.2 = z0 then coarseProjCocycle pcode M h2 eZ.val.1 else 0 := by
      intro eZ
      dsimp [bdlStepXCheckZ, bdlGQZ1]
      by_cases heZ : eZ.val.2 = z0
      · rw [if_pos ⟨heZ, rfl⟩, one_mul, if_pos heZ, h_term eZ]
      · rw [if_neg (fun hc => heZ hc.1), zero_mul, if_neg heZ]
    simp_rw [h_active]
    rw [sum_activeZ_eq pcode z0 (coarseProjCocycle pcode M h2),
        projCylinderLXLayer_zero_eq, ← coarseProjCocycle_eq_projCylinderLX]
    exact Finset.sum_congr rfl (fun q _ => mul_comm _ _)
  · intro b' _ hne
    apply Finset.sum_eq_zero
    intro v0 _
    rcases v0 with _ | ⟨_ | eZ⟩
    · exact zero_mul _
    · exact zero_mul _
    · dsimp [bdlStepXCheckZ, bdlGQZ1]
      rw [if_neg (fun hc => hne hc.2), zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- Exact commutation and three-layer replication of `rxCleanedCoarseProj` and `rxCleanedCoarseSyndrome` (Part I, Section 4.1 (`subsec:cleaner-architecture`), Theorem 4.3 (`thm:16-27-contraction`)). -/
theorem rxCleanedCoarseProj_syndrome_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q, ∃ z, pcode.checkZ z q ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) :
    syndrome (dualCode pcode) (rxCleanedCoarseProj pcode M h) =
      rxCleanedCoarseSyndrome pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h) ∧
    (let S := syndrome (dualCode (bdlCylinderStepX pcode M)) h
     let S2 := S + syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanTwoStageRX pcode M S)
     S2 = embedCoarseStepXMZ pcode M (rxCleanedCoarseSyndrome pcode M S)) := by
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S := syndrome D_1 h
  let h2 := h + cleanTwoStageRX pcode M S
  have h2_X : ∀ x : M_X, restrictCX2 pcode M x (syndrome D_1 h2) = 0 :=
    restrictCX2_syndrome_add_cleanTwoStageRX_eq_zero pcode M hov h_conn h
  have h2_Q : ∀ q0 : Q, restrictCQ2 pcode M q0 (syndrome D_1 h2) = 0 :=
    restrictCQ2_syndrome_add_cleanTwoStageRX_eq_zero pcode M hov h_conn h
  have h_s2 : S + syndrome D_1 (cleanTwoStageRX pcode M S) = syndrome D_1 h2 :=
    (map_add (syndrome D_1) h (cleanTwoStageRX pcode M S)).symm
  have h_comm : syndrome (dualCode pcode) (rxCleanedCoarseProj pcode M h) =
      rxCleanedCoarseSyndrome pcode M S := by
    ext z0
    have h_z0 := syndrome_cz2_eq_coarse_of_cx2_cq2_zero pcode M hov hq_z h_conn h2 h2_X h2_Q z0 0
    have h_z0_apply : rxCleanedCoarseSyndrome pcode M S z0 =
        syndrome D_1 h2 (Sum.inr (Sum.inr (z0, 0))) := by
      dsimp [rxCleanedCoarseSyndrome]
      exact congr_fun h_s2 (Sum.inr (Sum.inr (z0, 0)))
    rw [h_z0_apply]
    exact h_z0.symm
  refine ⟨h_comm, ?_⟩
  (try dsimp only [])
  rw [h_s2]
  ext mZ
  rcases mZ with mZX | ⟨mZQ | ⟨z0, b⟩⟩
  · have h_x := congr_fun (h2_X (cX2OwnerX pcode M mZX)) (Sum.inl mZX)
    dsimp [restrictCX2, restrictStepXMZ] at h_x
    have hm : stepXMZOwnerTanner pcode M (Sum.inl mZX) ∈ ({inVX (cX2OwnerX pcode M mZX)} : Finset _) :=
      Finset.mem_singleton_self _
    rw [if_pos hm] at h_x
    exact h_x
  · have h_q := congr_fun (h2_Q (cQ2OwnerQ pcode M mZQ)) (Sum.inr (Sum.inl mZQ))
    dsimp [restrictCQ2, restrictStepXMZ] at h_q
    have hm : stepXMZOwnerTanner pcode M (Sum.inr (Sum.inl mZQ)) ∈ ({inVQ (cQ2OwnerQ pcode M mZQ)} : Finset _) :=
      Finset.mem_singleton_self _
    rw [if_pos hm] at h_q
    exact h_q
  · rw [syndrome_cz2_eq_coarse_of_cx2_cq2_zero pcode M hov hq_z h_conn h2 h2_X h2_Q z0 b]
    dsimp [embedCoarseStepXMZ]
    exact congr_fun h_comm z0

/-- Coupling map `bdlGXQ1` vanishes when `pcode.checkX` vanishes between the owner X-check and owner qubit. -/
lemma bdlGXQ1_eq_zero_of_checkX_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZQ : BDLCQ2 pcode M) (qX : BDLCX1 pcode M)
    (h : pcode.checkX (cX1OwnerX pcode M qX) (cQ2OwnerQ pcode M mZQ) = 0) :
    bdlGXQ1 pcode M mZQ qX = 0 := by
  rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, vZ⟩ <;>
    rcases qX with ⟨rv, bX⟩ | ⟨⟨seg, bX⟩ | ⟨xv, vX⟩⟩
  · rfl
  · dsimp [bdlGXQ1, cX1OwnerX, cQ2OwnerQ, cQ2OwnerActiveZ] at h ⊢
    split_ifs with hc
    · exact h
    · rfl
  · rfl
  · rfl
  · rfl
  · dsimp [bdlGXQ1, cX1OwnerX, cQ2OwnerQ, cQ2OwnerActiveZ] at h ⊢
    split_ifs with hc
    · exact h
    · rfl

/-- A 1-chain supported on cylinder `x0` with `pcode.checkX x0 q0 = 0` induces zero syndrome on star `q0`. -/
lemma restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : M_X) (q0 : Q)
    (hxq : pcode.checkX x0 q0 = 0)
    (u : BDLStepXQ pcode M → ZMod 2)
    (h_supp : ∀ q, u q ≠ 0 → ∃ qX, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x0) :
    restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) u) = 0 := by
  ext mZ
  dsimp [restrictCQ2, restrictStepXMZ]
  split_ifs with hmZ
  · rcases mZ with mZX | (mZQ | mZZ)
    · dsimp [stepXMZOwnerTanner, inVX, inVQ] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
    · dsimp [stepXMZOwnerTanner, inVQ] at hmZ
      rw [Finset.mem_singleton, Sum.inr.injEq, Sum.inl.injEq] at hmZ
      dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
      apply Finset.sum_eq_zero; intro q _
      by_cases hq : u q = 0
      · rw [hq, mul_zero]
      · obtain ⟨qX, rfl, h_own⟩ := h_supp q hq
        dsimp [bdlStepXCheckZ]
        rw [bdlGXQ1_eq_zero_of_checkX_eq_zero pcode M mZQ qX (by rw [h_own, hmZ]; exact hxq), zero_mul]
    · dsimp [stepXMZOwnerTanner, inVZ, inVQ] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
  · rfl

/-! ## 2. Active Coarse Z-Checks and Restricted Syndrome Lower Bounds -/

/-- Active coarse Z-checks in `K` after two-stage `R_X` cleaning. -/
noncomputable def activeCoarseZInK {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X))
    (S : BDLStepXMZ pcode M → ZMod 2) : Finset M_Z :=
  Finset.univ.filter (fun z0 : M_Z =>
    inVZ z0 ∈ K ∧ rxCleanedCoarseSyndrome pcode M S z0 ≠ 0)

/-- Number of active fine Z-checks in `BDLCZ2 M_Z` owned by `z0 : M_Z`. -/
def weightCZ2OnCheck {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (z0 : M_Z)
    (S : BDLStepXMZ pcode M → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun b : Fin 3 => S (Sum.inr (Sum.inr (z0, b))) ≠ 0)).card

/-- Number of active fine Z-checks in `BDLCQ2 pcode M` owned by `q0 : Q`. -/
def weightCQ2OnStarStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S : BDLStepXMZ pcode M → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun mZQ : BDLCQ2 pcode M =>
    cQ2OwnerQ pcode M mZQ = q0 ∧ S (Sum.inr (Sum.inl mZQ)) ≠ 0)).card

/-- If `a + ∑ x ∈ s, f x ≠ 0` in `ZMod 2`, at least one term is non-zero. -/
lemma one_le_ite_add_sum_ite_of_add_sum_ne_zero {α : Type*} (s : Finset α)
    (a : ZMod 2) (f : α → ZMod 2) (h : a + ∑ x ∈ s, f x ≠ 0) :
    1 ≤ (if a ≠ 0 then 1 else 0) + ∑ x ∈ s, (if f x ≠ 0 then 1 else 0) := by
  by_contra h_lt
  push_neg at h_lt
  have ha : a = 0 := by
    by_contra ha_ne
    have : 1 ≤ (if a ≠ 0 then 1 else 0) := by rw [if_pos ha_ne]
    omega
  have hf : ∀ x ∈ s, f x = 0 := by
    intro x hx
    by_contra hx_ne
    have h1 : 1 ≤ (if f x ≠ 0 then 1 else 0) := by rw [if_pos hx_ne]
    have h2 : (if f x ≠ 0 then 1 else 0) ≤ ∑ y ∈ s, (if f y ≠ 0 then 1 else 0) :=
      Finset.single_le_sum (f := fun y => if f y ≠ 0 then 1 else 0) (fun _ _ => Nat.zero_le _) hx
    omega
  apply h
  rw [ha, zero_add]
  exact Finset.sum_eq_zero hf

/-- If `∑ x ∈ s, f x ≠ 0` in `ZMod 2`, the count of non-zero summands is at least `1`. -/
lemma one_le_sum_ite_of_sum_ne_zero {α : Type*} (s : Finset α)
    (f : α → ZMod 2) (h : ∑ x ∈ s, f x ≠ 0) :
    1 ≤ ∑ x ∈ s, (if f x ≠ 0 then 1 else 0) := by
  have h' : (0 : ZMod 2) + ∑ x ∈ s, f x ≠ 0 := by rwa [zero_add]
  have h_le := one_le_ite_add_sum_ite_of_add_sum_ne_zero s 0 f h'
  simpa using h_le

/-- Subsumes a fiber-grouped sum over a subset of owners by the total weight. -/
lemma sum_owner_subset_le {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (owner : α → β) (P : α → Prop) [DecidablePred P]
    (K_B : Finset β) :
    (∑ b ∈ K_B, (Finset.univ.filter (fun a : α => owner a = b ∧ P a)).card) ≤
      (Finset.univ.filter (fun a : α => owner a ∈ K_B ∧ P a)).card := by
  have h_eq : ∀ b ∈ K_B,
      (Finset.univ.filter (fun a : α => owner a = b ∧ P a)).card =
        ∑ a : α, if owner a = b ∧ P a then 1 else 0 := by
    intro b _; rw [Finset.card_filter]
  rw [Finset.sum_congr rfl h_eq, Finset.card_filter, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hP : P a
  · by_cases hb : owner a ∈ K_B
    · rw [if_pos ⟨hb, hP⟩, Finset.sum_eq_single (owner a)]
      · rw [if_pos ⟨rfl, hP⟩]
      · intro b _ hne; rw [if_neg (by intro hc; exact hne hc.1.symm)]
      · intro h_abs; exact False.elim (h_abs hb)
    · rw [if_neg (by intro hc; exact hb hc.1), Finset.sum_eq_zero]
      intro b hb_mem
      rw [if_neg (by intro hc; exact hb (hc.1 ▸ hb_mem))]
  · rw [if_neg (by intro hc; exact hP hc.2), Finset.sum_eq_zero]
    intro b _
    rw [if_neg (by intro hc; exact hP hc.2)]

/-- Lower-bounds `syndromeWeightNat (restrictStepXMZ K s)` by the sum of cylinder, star, and Z-check weights in `K`. -/
lemma syndromeWeightNat_restrictStepXMZ_ge {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (K : Finset (TannerVertex Q M_Z M_X))
    (S : BDLStepXMZ pcode M → ZMod 2) :
    let K_Z := activeCoarseZInK pcode M K S
    let K_Q := Finset.univ.filter (fun q0 : Q => inVQ q0 ∈ K)
    let K_X := Finset.univ.filter (fun x : M_X => inVX x ∈ K)
    (∑ x ∈ K_X, weightCX2OnCyl pcode M x S) +
    (∑ q0 ∈ K_Q, weightCQ2OnStarStep pcode M q0 S) +
    (∑ z0 ∈ K_Z, weightCZ2OnCheck pcode M z0 S) ≤
      syndromeWeightNat (restrictStepXMZ pcode M K S) := by
  intro K_Z K_Q K_X
  have h_rhs : syndromeWeightNat (restrictStepXMZ pcode M K S) =
      (Finset.univ.filter (fun mZX : BDLCX2 pcode M =>
        cX2OwnerX pcode M mZX ∈ K_X ∧ S (Sum.inl mZX) ≠ 0)).card +
      (Finset.univ.filter (fun mZQ : BDLCQ2 pcode M =>
        cQ2OwnerQ pcode M mZQ ∈ K_Q ∧ S (Sum.inr (Sum.inl mZQ)) ≠ 0)).card +
      (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
        inVZ mZZ.1 ∈ K ∧ S (Sum.inr (Sum.inr mZZ)) ≠ 0)).card := by
    dsimp [syndromeWeightNat]
    rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
        Fintype.sum_sum_type (α₁ := BDLCX2 pcode M), Fintype.sum_sum_type (α₁ := BDLCQ2 pcode M), ← add_assoc]
    congr 1
    · congr 1
      · apply Finset.sum_congr rfl; intro mZX _
        by_cases hm : inVX (cX2OwnerX pcode M mZX) ∈ K <;> simp [restrictStepXMZ, stepXMZOwnerTanner, K_X, hm]
      · apply Finset.sum_congr rfl; intro mZQ _
        by_cases hm : inVQ (cQ2OwnerQ pcode M mZQ) ∈ K <;> simp [restrictStepXMZ, stepXMZOwnerTanner, K_Q, hm]
    · apply Finset.sum_congr rfl; intro mZZ _
      by_cases hm : inVZ mZZ.1 ∈ K <;> simp [restrictStepXMZ, stepXMZOwnerTanner, cZ2OwnerZ, hm]
  rw [h_rhs]
  have hX_eq : ∀ x ∈ K_X,
      weightCX2OnCyl pcode M x S =
        (Finset.univ.filter (fun mZX : BDLCX2 pcode M =>
          cX2OwnerX pcode M mZX = x ∧ S (Sum.inl mZX) ≠ 0)).card := by
    intro x _
    dsimp [weightCX2OnCyl, syndromeWeightNat]
    rw [Finset.card_filter, Finset.card_filter,
        Fintype.sum_sum_type (α₁ := BDLCX2 pcode M), Fintype.sum_sum_type (α₁ := BDLCQ2 pcode M)]
    have hQ0 : (∑ mZQ : BDLCQ2 pcode M, if ¬restrictCX2 pcode M x S (Sum.inr (Sum.inl mZQ)) = 0 then 1 else 0) = 0 :=
      Finset.sum_eq_zero (fun mZQ _ => by simp [restrictCX2, restrictStepXMZ, stepXMZOwnerTanner, inVQ, inVX])
    have hZ0 : (∑ mZZ : BDLCZ2 M_Z, if ¬restrictCX2 pcode M x S (Sum.inr (Sum.inr mZZ)) = 0 then 1 else 0) = 0 :=
      Finset.sum_eq_zero (fun mZZ _ => by simp [restrictCX2, restrictStepXMZ, stepXMZOwnerTanner, inVZ, inVX])
    rw [hQ0, hZ0, add_zero, add_zero]
    apply Finset.sum_congr rfl; intro mZX _
    simp [restrictCX2, restrictStepXMZ, stepXMZOwnerTanner, inVX]
  have hX : (∑ x ∈ K_X, weightCX2OnCyl pcode M x S) ≤
      (Finset.univ.filter (fun mZX : BDLCX2 pcode M =>
        cX2OwnerX pcode M mZX ∈ K_X ∧ S (Sum.inl mZX) ≠ 0)).card := by
    rw [Finset.sum_congr rfl hX_eq]
    exact sum_owner_subset_le (cX2OwnerX pcode M) (fun mZX => S (Sum.inl mZX) ≠ 0) K_X
  have hQ := sum_owner_subset_le (cQ2OwnerQ pcode M) (fun mZQ => S (Sum.inr (Sum.inl mZQ)) ≠ 0) K_Q
  change (∑ q0 ∈ K_Q, weightCQ2OnStarStep pcode M q0 S) ≤ _ at hQ
  have hZ1 := sum_owner_subset_le (fun mZZ : BDLCZ2 M_Z => mZZ.1)
    (fun mZZ => S (Sum.inr (Sum.inr mZZ)) ≠ 0) K_Z
  have hZ2 : (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
      mZZ.1 ∈ K_Z ∧ S (Sum.inr (Sum.inr mZZ)) ≠ 0)).card ≤
      (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
        inVZ mZZ.1 ∈ K ∧ S (Sum.inr (Sum.inr mZZ)) ≠ 0)).card := by
    apply Finset.card_le_card
    intro mZZ hmZZ
    rw [Finset.mem_filter] at hmZZ ⊢
    refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hmZZ.2.1).2.1, hmZZ.2.2⟩
  have hZ_eq : ∀ z0 ∈ K_Z,
      weightCZ2OnCheck pcode M z0 S =
        (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
          mZZ.1 = z0 ∧ S (Sum.inr (Sum.inr mZZ)) ≠ 0)).card := by
    intro z0 _
    dsimp [weightCZ2OnCheck]
    rw [Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single z0]
    · apply Finset.sum_congr rfl; intro b _; simp
    · intro z _ hne
      apply Finset.sum_eq_zero; intro b _
      rw [if_neg (fun hc => hne hc.1)]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  have hZ : (∑ z0 ∈ K_Z, weightCZ2OnCheck pcode M z0 S) ≤
      (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
        inVZ mZZ.1 ∈ K ∧ S (Sum.inr (Sum.inr mZZ)) ≠ 0)).card := by
    rw [Finset.sum_congr rfl hZ_eq]
    exact hZ1.trans hZ2
  exact add_le_add (add_le_add hX hQ) hZ

/-- Non-zero `exportQZ` from `cleanStarQ` on `q0` implies `pcode.checkZ z0 q0 ≠ 0`. -/
lemma checkZ_ne_zero_of_exportQZ_cleanStarQ_ne_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 : BDLStepXMZ pcode M → ZMod 2) (q0 : Q) (z0 : M_Z) (b : Fin 3)
    (h_nz : exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) ≠ 0) :
    pcode.checkZ z0 q0 ≠ 0 := by
  dsimp [exportQZ, syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX] at h_nz
  have h_ex : ∃ q : BDLStepXQ pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inr (z0, b))) q *
        splitStepXQQ pcode M (cleanStarQ pcode M S1 q0) q ≠ 0 := by
    by_contra h_all; push_neg at h_all
    exact h_nz (Finset.sum_eq_zero (fun q _ => h_all q))
  rcases h_ex with ⟨qX | ⟨v0, b'⟩, hq⟩
  · exact False.elim (hq (mul_zero _))
  · have h_v_nz : cleanStarQ pcode M S1 q0 (Sum.inr (v0, b')) ≠ 0 :=
      fun h0 => hq (by dsimp [splitStepXQQ]; rw [h0, mul_zero])
    obtain ⟨qQ', h_eq, h_own⟩ := cleanStarQ_support pcode M S1 q0 _ h_v_nz
    injection h_eq with h_eq; subst h_eq
    have h_gqz : bdlGQZ1 pcode M (z0, b) (v0, b') ≠ 0 :=
      fun h0 => hq (by dsimp [bdlStepXCheckZ]; rw [h0, zero_mul])
    rcases v0 with q_in | (⟨eZ, j⟩ | eZ)
    · exact False.elim (h_gqz rfl)
    · exact False.elim (h_gqz rfl)
    · dsimp [bdlGQZ1] at h_gqz
      split_ifs at h_gqz with hc
      · dsimp [cQ1OwnerQ, xq0OwnerQ] at h_own
        rw [← hc.1, ← h_own]
        exact eZ.property
      · exact False.elim (h_gqz rfl)

/-- Stage-1 cylinder cleaner `cleanStage1X` induces zero syndrome on `BDLCZ2` checks. -/
lemma syndrome_cleanStage1X_cz2_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) (mZZ : BDLCZ2 M_Z) :
    syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanStage1X pcode M S)
      (Sum.inr (Sum.inr mZZ)) = 0 := by
  dsimp [cleanStage1X]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  apply Finset.sum_eq_zero
  intro q _
  rcases q with qX | qQ
  · exact zero_mul _
  · have h0 : cleanCylinderX pcode M S x (Sum.inr qQ) = 0 := by
      by_contra h_nz
      obtain ⟨qX', h_eq, _⟩ := cleanCylinderX_support pcode M S x _ h_nz
      nomatch h_eq
    rw [h0, mul_zero]

/-- Projects `cleanStarQ` onto `BDLCQ1` via `splitStepXQQ`. -/
lemma splitStepXQ_Q_cleanStarQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 : BDLStepXMZ pcode M → ZMod 2) (q0 : Q) :
    splitStepXQQ pcode M (cleanStarQ pcode M S1 q0) = cleanStarQ pcode M S1 q0 := by
  ext q
  rcases q with qX | qQ
  · dsimp [splitStepXQQ]
    symm
    by_contra h_nz
    obtain ⟨qQ', h_eq, _⟩ := cleanStarQ_support pcode M S1 q0 _ h_nz
    nomatch h_eq
  · rfl

/-! ## 3. Three-Copy Contraction of Active Coarse Z-Checks -/

/-- Bounds `3 * (activeCoarseZInK K u).card` by the `CZ2` syndrome weight plus exported star weights. -/
lemma three_mul_card_activeCoarseZInK_le {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hZ : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (K : Finset (TannerVertex Q M_Z M_X))
    (h : BDLStepXQ pcode M → ZMod 2)
    (hK_Z_to_Q : ∀ z0 : M_Z, ∀ q0 : Q,
      inVZ z0 ∈ K → pcode.checkZ z0 q0 ≠ 0 →
      (∃ b : Fin 3, exportQZ pcode M
        (cleanStarQ pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h +
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) q0)
        (z0, b) ≠ 0) →
      inVQ q0 ∈ K) :
    let D_1 := dualCode (bdlCylinderStepX pcode M)
    let S := syndrome D_1 h
    let S1 := S + syndrome D_1 (cleanStage1X pcode M S)
    let K_Z := activeCoarseZInK pcode M K S
    let K_Q := Finset.univ.filter (fun q0 : Q => inVQ q0 ∈ K)
    3 * K_Z.card ≤
      (∑ z0 ∈ K_Z, weightCZ2OnCheck pcode M z0 S) +
      (∑ q0 ∈ K_Q, (Finset.univ.filter (fun mZZ : BDLCZ2 M_Z =>
        exportQZ pcode M (cleanStarQ pcode M S1 q0) mZZ ≠ 0)).card) := by
  intro D_1 S S1 K_Z K_Q
  have h_pt : ∀ z0 ∈ K_Z, ∀ b : Fin 3,
      1 ≤ (if S (Sum.inr (Sum.inr (z0, b))) ≠ 0 then 1 else 0) +
          ∑ q0 ∈ K_Q, (if exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) ≠ 0 then 1 else 0) := by
    intro z0 hz0 b
    apply one_le_ite_add_sum_ite_of_add_sum_ne_zero
    have hz0_act : rxCleanedCoarseSyndrome pcode M S z0 ≠ 0 := (Finset.mem_filter.mp hz0).2.2
    have hz0_K : inVZ z0 ∈ K := (Finset.mem_filter.mp hz0).2.1
    have h_s2 := congr_fun (rxCleanedCoarseProj_syndrome_eq pcode M hov hZ h_conn h).2
      (Sum.inr (Sum.inr (z0, b)))
    dsimp [embedCoarseStepXMZ] at h_s2
    change (S + syndrome D_1 (cleanTwoStageRX pcode M S)) (Sum.inr (Sum.inr (z0, b))) =
      rxCleanedCoarseSyndrome pcode M S z0 at h_s2
    have h_decomp : (S + syndrome D_1 (cleanTwoStageRX pcode M S)) (Sum.inr (Sum.inr (z0, b))) =
        S (Sum.inr (Sum.inr (z0, b))) +
          ∑ q0 ∈ K_Q, exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) := by
      change S (Sum.inr (Sum.inr (z0, b))) +
        syndrome D_1 (cleanStage1X pcode M S + cleanStage2Q pcode M S1) (Sum.inr (Sum.inr (z0, b))) = _
      rw [map_add, Pi.add_apply, syndrome_cleanStage1X_cz2_eq_zero, zero_add]
      congr 1
      dsimp [cleanStage2Q]
      rw [map_sum, Finset.sum_apply]
      have h_eq_exp : ∀ q0 : Q,
          syndrome D_1 (cleanStarQ pcode M S1 q0) (Sum.inr (Sum.inr (z0, b))) =
            exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) := by
        intro q0
        unfold exportQZ
        rw [splitStepXQ_Q_cleanStarQ]
      simp_rw [h_eq_exp]
      symm
      apply Finset.sum_subset (Finset.subset_univ K_Q)
      intro q0 _ hq0_not
      by_contra h_exp_nz
      have h_chk : pcode.checkZ z0 q0 ≠ 0 :=
        checkZ_ne_zero_of_exportQZ_cleanStarQ_ne_zero pcode M S1 q0 z0 b h_exp_nz
      have h_inK : inVQ q0 ∈ K := hK_Z_to_Q z0 q0 hz0_K h_chk ⟨b, h_exp_nz⟩
      exact hq0_not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_inK⟩)
    rw [← h_decomp, h_s2]
    exact hz0_act
  have h_sum_b : ∀ z0 ∈ K_Z,
      3 ≤ weightCZ2OnCheck pcode M z0 S +
          ∑ b : Fin 3, ∑ q0 ∈ K_Q,
            (if exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) ≠ 0 then 1 else 0) := by
    intro z0 hz0
    have h1 := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => h_pt z0 hz0 b)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      Finset.sum_add_distrib] at h1
    dsimp [weightCZ2OnCheck]
    rw [Finset.card_filter]
    exact h1
  have h_sum_z0 := Finset.sum_le_sum h_sum_b
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib] at h_sum_z0
  rw [Nat.mul_comm] at h_sum_z0
  refine h_sum_z0.trans (Nat.add_le_add_left ?_ _)
  have h_swap : (∑ z0 ∈ K_Z, ∑ b : Fin 3, ∑ q0 ∈ K_Q,
      (if exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) ≠ 0 then 1 else 0)) =
      ∑ q0 ∈ K_Q, ∑ z0 ∈ K_Z, ∑ b : Fin 3,
        (if exportQZ pcode M (cleanStarQ pcode M S1 q0) (z0, b) ≠ 0 then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun z0 _ => Finset.sum_comm)]
    exact Finset.sum_comm
  rw [h_swap]
  apply Finset.sum_le_sum
  intro q0 _
  rw [Finset.card_filter, Fintype.sum_prod_type]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ K_Z)

/-- Projects `cleanCylinderX` onto `BDLCX1` via `splitStepXQX`. -/
lemma splitStepXQ_X_cleanCylinderX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) (x : M_X) :
    splitStepXQX pcode M (cleanCylinderX pcode M S x) = cleanCylinderX pcode M S x := by
  ext q
  rcases q with qX | qQ
  · rfl
  · dsimp [splitStepXQX]
    symm
    by_contra h_nz
    obtain ⟨qX', h_eq, _⟩ := cleanCylinderX_support pcode M S x _ h_nz
    nomatch h_eq

end BDLDecoder
end WeldedHierarchy
