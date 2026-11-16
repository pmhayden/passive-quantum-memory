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

import Proofs.HierarchicalClusterDecoder.IteratedLogicalOperatorLifts

/-!
# Stage-1 Cylinder Sector Subadditivity and Outer Vertical Check Cancellation

Constructs the explicit Stage-1 cylinder cleaner candidates `cylCleanerCand` via `outerVertCancelCochain` and proves exact cancellation of vertical and cylinder syndromes (`cylCleanerCand_vert_eq_zero`, `restrictCX2_syndrome_add_cylCleanerCand_eq_zero`). Establishes the three-arm pointwise subadditivity inequalities (`cyl_sector_pointwise_subadditive`, `min_cylArmVec_weight_le`) underlying the 4/3 Stage-1 export bound.

## References

* Part I, Section 4.2 (`subsec:stage1-cylinder`), Lemma 4.1 (`lem:stage1-cylinder-cleaner`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Lemma 4.4 (`lem:two-stage-cleaner-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Cylinder Syndrome Restriction and Exported Weight -/

/-- Restriction of a 1-cochain `h : BDLStepXQ pcode M → ZMod 2` to cylinder `x : M_X`. -/
def restrictCX1 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X)
    (h : BDLStepXQ pcode M → ZMod 2) : BDLStepXQ pcode M → ZMod 2 :=
  fun q => match q with
  | Sum.inl qX => if cX1OwnerX pcode M qX = x then h q else 0
  | Sum.inr _  => 0

/-- Restriction of a 2-cochain `S : BDLStepXMZ pcode M → ZMod 2` to cylinder `x : M_X`. -/
def restrictCX2 {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X)
    (S : BDLStepXMZ pcode M → ZMod 2) : BDLStepXMZ pcode M → ZMod 2 :=
  restrictStepXMZ pcode M ({inVX x} : Finset (TannerVertex Q M_Z M_X)) S

/-- Boundary export map `γ_{X → Q}(u)` from `C_X^1` into `C_Q^2`:
    evaluates `syndrome (dualCode (bdlCylinderStepX pcode M)) (splitStepXQX pcode M u)` on `BDLCQ2`. -/
noncomputable def exportXQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (u : BDLStepXQ pcode M → ZMod 2) : BDLCQ2 pcode M → ZMod 2 :=
  fun mZQ =>
    syndrome (dualCode (bdlCylinderStepX pcode M)) (splitStepXQX pcode M u)
      (Sum.inr (Sum.inl mZQ))

/-- Hamming weight of a `BDLStepXMZ` 2-cochain restricted to cylinder `x : M_X`. -/
def weightCX2OnCyl {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X)
    (S : BDLStepXMZ pcode M → ZMod 2) : ℕ :=
  syndromeWeightNat (restrictCX2 pcode M x S)

/-- Explicit formula for `exportXQ` via `bdlGXQ1`. -/
lemma exportXQ_apply {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (u : BDLStepXQ pcode M → ZMod 2) (mZQ : BDLCQ2 pcode M) :
    exportXQ pcode M u mZQ =
      ∑ qX : BDLCX1 pcode M, bdlGXQ1 pcode M mZQ qX * u (Sum.inl qX) := by
  dsimp [exportXQ, syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  rw [Fintype.sum_sum_type]
  have hQ : (∑ qQ : BDLCQ1 pcode M,
      bdlStepXCheckZ pcode M (Sum.inr (Sum.inl mZQ)) (Sum.inr qQ) *
        splitStepXQX pcode M u (Sum.inr qQ)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => mul_zero _)
  rw [hQ, add_zero]
  rfl

/-- Net export weight of `u : BDLStepXQ pcode M → ZMod 2` to the collapsed star checks `(eZ, b)` and `(eZ, v)`. -/
noncomputable def weightNetExportXQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (u : BDLStepXQ pcode M → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
    (∑ k : Fin (M + 1), exportXQ pcode M u (Sum.inl (p.1, k, p.2))) ≠ 0)).card +
  (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
    exportXQ pcode M u (Sum.inr (p.1, p.2)) ≠ 0)).card

/-- `bdlDeltaX1` only connects 1-cells and 2-cells with the same `M_X` cylinder owner. -/
lemma bdlDeltaX1_eq_zero_of_owner_ne {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZX : BDLCX2 pcode M) (qX : BDLCX1 pcode M)
    (hne : cX1OwnerX pcode M qX ≠ cX2OwnerX pcode M mZX) :
    bdlDeltaX1 pcode M mZX qX = 0 := by
  have h_not_eq : ∀ qX' : BDLCX1 pcode M,
      cX1OwnerX pcode M qX' = cX2OwnerX pcode M mZX →
      (if qX = qX' then (1 : ZMod 2) else 0) = 0 :=
    fun qX' h_eq => if_neg (fun (h : qX = qX') => hne (h.symm ▸ h_eq))
  rcases mZX with ⟨seg, b⟩ | ⟨s, k, v⟩
  · dsimp [bdlDeltaX1]
    by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
    · rw [dif_pos h_tri]
      by_cases hr0 : seg.val.2.1.val = 0
      · rw [dif_pos hr0]
        by_cases h_can : seg.val.1.val.2.val.1 = canonicalSquareQ pcode seg.val.1.val.1 seg.val.1.val.2.val.2
            ⟨seg.val.1.val.2.val.1, seg.val.1.property, seg.val.1.val.2.property⟩
        · rw [if_pos h_can]
          apply Finset.sum_eq_zero
          intro q' _
          by_cases hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0
          · rw [dif_pos hX']
            by_cases hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0
            · rw [dif_pos hZ', h_not_eq _ rfl, h_not_eq _ rfl, add_zero]
            · rw [dif_neg hZ']
          · rw [dif_neg hX']
        · rw [if_neg h_can]
      · rw [dif_neg hr0, h_not_eq _ rfl, h_not_eq _ rfl, h_not_eq _ rfl, add_zero, add_zero]
    · rw [dif_neg h_tri, h_not_eq _ rfl, h_not_eq _ rfl, h_not_eq _ rfl, h_not_eq _ rfl,
          add_zero, add_zero, add_zero]
  · dsimp [bdlDeltaX1]
    rw [h_not_eq _ rfl, h_not_eq _ rfl, h_not_eq _ rfl, h_not_eq _ rfl, add_zero, add_zero, add_zero]

/-- For any 0-cochain `d : BDLStepXMX pcode M → ZMod 2`,
    setting `u_x := restrictCX1 pcode M x (h + checkGen D_1 d)` clears the syndrome on cylinder `x`. -/
lemma restrictCX2_syndrome_add_restrictCX1_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X)
    (h : BDLStepXQ pcode M → ZMod 2) (d : BDLStepXMX pcode M → ZMod 2) :
    restrictCX2 pcode M x
      (syndrome (dualCode (bdlCylinderStepX pcode M))
        (h + restrictCX1 pcode M x (h + checkGen (dualCode (bdlCylinderStepX pcode M)) d))) = 0 := by
  ext mZ
  dsimp [restrictCX2, restrictStepXMZ]
  split_ifs with hmZ
  · rcases mZ with mZX | (mZQ | mZZ)
    · dsimp [stepXMZOwnerTanner, inVX] at hmZ
      rw [Finset.mem_singleton, Sum.inl.injEq] at hmZ
      have h_eq : syndrome (dualCode (bdlCylinderStepX pcode M))
          (h + restrictCX1 pcode M x (h + checkGen (dualCode (bdlCylinderStepX pcode M)) d))
          (Sum.inl mZX) =
          syndrome (dualCode (bdlCylinderStepX pcode M))
            (checkGen (dualCode (bdlCylinderStepX pcode M)) d) (Sum.inl mZX) := by
        dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
        apply Finset.sum_congr rfl
        intro q _
        rcases q with qX | qQ
        · by_cases h_own : cX1OwnerX pcode M qX = x
          · dsimp [restrictCX1]; rw [if_pos h_own]; congr 1
            have h2 := zmod2_add_self (h (Sum.inl qX)); linear_combination h2
          · dsimp [bdlStepXCheckZ]
            rw [bdlDeltaX1_eq_zero_of_owner_ne pcode M mZX qX (by rw [hmZ]; exact h_own), zero_mul, zero_mul]
        · dsimp [bdlStepXCheckZ]; simp
      rw [h_eq]
      exact congr_fun (syndrome_checkGen_zero (dualCode (bdlCylinderStepX pcode M)) d) (Sum.inl mZX)
    · dsimp [stepXMZOwnerTanner, inVQ, inVX] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
    · dsimp [stepXMZOwnerTanner, inVZ, inVX] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
  · rfl

/-! ## 2. Outer Vertical Cancellation Cochain and Candidate -/

/-- Hamming weight of a 3-layer bit-vector `v : Fin 3 → ZMod 2` (for cylinder sector bounds). -/
def wt3Cyl (v : Fin 3 → ZMod 2) : ℕ :=
  (if v 0 ≠ 0 then 1 else 0) + (if v 1 ≠ 0 then 1 else 0) + (if v 2 ≠ 0 then 1 else 0)

/-- Hamming weight of a 2-bridge bit-vector `v : Fin 2 → ZMod 2`. -/
def wt2Cyl (v : Fin 2 → ZMod 2) : ℕ :=
  (if v 0 ≠ 0 then 1 else 0) + (if v 1 ≠ 0 then 1 else 0)

/-- Reference layer `b0 = 0` net arm export vector on a cylinder sector `s`. -/
def cylArmVec0 (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) : Fin 3 → ZMod 2
  | 0 => α 0
  | 1 => α 0 + σ_c 0
  | 2 => α 0 + σ_c 1

/-- Reference layer `b0 = 1` net arm export vector on a cylinder sector `s`. -/
def cylArmVec1 (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) : Fin 3 → ZMod 2
  | 0 => α 1 + σ_c 0
  | 1 => α 1
  | 2 => α 1 + σ_c 0 + σ_c 1

/-- Reference layer `b0 = 2` net arm export vector on a cylinder sector `s`. -/
def cylArmVec2 (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) : Fin 3 → ZMod 2
  | 0 => α 2 + σ_c 1
  | 1 => α 2 + σ_c 0 + σ_c 1
  | 2 => α 2

/-- Single-bit $\mathbb{Z}_{\ge 0}$-triangle inequality on `ZMod 2`. -/
lemma zmod2_ite_add_le (a b : ZMod 2) :
    (if a + b ≠ 0 then 1 else 0) ≤
      (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> decide

/-- Three-term $\mathbb{Z}_{\ge 0}$-subadditivity on `ZMod 2`, proved by two applications of `zmod2_ite_add_le`. -/
lemma zmod2_ite_add3_le (a b c : ZMod 2) :
    (if a + b + c ≠ 0 then 1 else 0) ≤
      (if a ≠ 0 then 1 else 0) + (if b ≠ 0 then 1 else 0) + (if c ≠ 0 then 1 else 0) :=
  (zmod2_ite_add_le (a + b) c).trans (Nat.add_le_add_right (zmod2_ite_add_le a b) _)

/-- **Reference-Layer Subadditivity Bound**:
    $\sum_{b_0=0}^2 \mathrm{wt}_3(\mathrm{cylVec}_{b_0}) \le 3\,\mathrm{wt}_3(\alpha) + 4\,\mathrm{wt}_2(\sigma_c)$. -/
theorem cyl_sector_pointwise_subadditive (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) :
    wt3Cyl (cylArmVec0 α σ_c) + wt3Cyl (cylArmVec1 α σ_c) + wt3Cyl (cylArmVec2 α σ_c) ≤
      3 * wt3Cyl α + 4 * wt2Cyl σ_c := by
  have h01 := zmod2_ite_add_le (α 0) (σ_c 0)
  have h02 := zmod2_ite_add_le (α 0) (σ_c 1)
  have h10 := zmod2_ite_add_le (α 1) (σ_c 0)
  have h12 := zmod2_ite_add3_le (α 1) (σ_c 0) (σ_c 1)
  have h20 := zmod2_ite_add_le (α 2) (σ_c 1)
  have h21 := zmod2_ite_add3_le (α 2) (σ_c 0) (σ_c 1)
  change ((if α 0 ≠ 0 then 1 else 0) + (if α 0 + σ_c 0 ≠ 0 then 1 else 0) + (if α 0 + σ_c 1 ≠ 0 then 1 else 0)) +
    ((if α 1 + σ_c 0 ≠ 0 then 1 else 0) + (if α 1 ≠ 0 then 1 else 0) + (if α 1 + σ_c 0 + σ_c 1 ≠ 0 then 1 else 0)) +
    ((if α 2 + σ_c 1 ≠ 0 then 1 else 0) + (if α 2 + σ_c 0 + σ_c 1 ≠ 0 then 1 else 0) + (if α 2 ≠ 0 then 1 else 0)) ≤
    3 * ((if α 0 ≠ 0 then 1 else 0) + (if α 1 ≠ 0 then 1 else 0) + (if α 2 ≠ 0 then 1 else 0)) +
    4 * ((if σ_c 0 ≠ 0 then 1 else 0) + (if σ_c 1 ≠ 0 then 1 else 0))
  omega

/-- **Stage-1 Reference-Layer Sector Bound (`cyl_sector_pointwise_bound`)**:
    Follows immediately from `cyl_sector_pointwise_subadditive`. -/
lemma cyl_sector_pointwise_bound (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) :
    wt3Cyl (cylArmVec0 α σ_c) + wt3Cyl (cylArmVec1 α σ_c) + wt3Cyl (cylArmVec2 α σ_c) ≤
      4 * (wt3Cyl α + wt2Cyl σ_c) := by
  have h := cyl_sector_pointwise_subadditive α σ_c
  omega

/-- 3-candidate outer-shell vertical cancellation 0-cochain. -/
noncomputable def outerVertCancelCochain {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) : BDLStepXMX pcode M → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (sv, b) =>
      if sv.val.2 = Fin.last M then
        let r0 := apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (sv.val.1, 0))))
        let r1 := apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (sv.val.1, 1))))
        match b0, b with
        | 0, 0 => 0
        | 0, 1 => r0
        | 0, 2 => r1
        | 1, 0 => r0
        | 1, 1 => 0
        | 1, 2 => r0 + r1
        | 2, 0 => r1
        | 2, 1 => r0 + r1
        | 2, 2 => 0
      else 0

/-- Candidate cylinder cleaner for reference layer `b0 : Fin 3` on cylinder `x : M_X`. -/
noncomputable def cylCleanerCand {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) : BDLStepXQ pcode M → ZMod 2 :=
  restrictCX1 pcode M x
    (apexResidualCocycle pcode M h +
      checkGen (dualCode (bdlCylinderStepX pcode M)) (outerVertCancelCochain pcode M b0 h))

/-- Evaluates `checkGen` of `outerVertCancelCochain` on vertical cylinder edges. -/
lemma checkGen_outerVertCancelCochain_vert {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2)
    (xv : BoundaryX0Link pcode M) (v : Fin 2) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (outerVertCancelCochain pcode M b0 h)
      (Sum.inl (Sum.inr (Sum.inr (xv, v)))) =
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (xv, v)))) := by
  dsimp [checkGen, f2CheckGen, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (Sum.inr (mkOuterShellVertex pcode M xv, (0 : Fin 3)))]
  · rw [Finset.sum_eq_single (Sum.inr (mkOuterShellVertex pcode M xv, v.succ))]
    · rw [if_pos rfl, if_pos rfl, one_mul, one_mul]
      dsimp [outerVertCancelCochain, mkOuterShellVertex]
      rw [if_pos rfl, if_pos rfl]
      have h_alg0 : ∀ a : ZMod 2, a + (a + apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (xv, 1))))) =
          apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (xv, 1)))) := by
        intro a; have h2 := zmod2_add_self a; linear_combination h2
      have h_alg1 : ∀ b : ZMod 2, b + (apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (xv, 0)))) + b) =
          apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (xv, 0)))) := by
        intro b; have h2 := zmod2_add_self b; linear_combination h2
      fin_cases b0 <;> fin_cases v <;> dsimp <;> first | exact zero_add _ | exact add_zero _ | exact h_alg0 _ | exact h_alg1 _
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro mX _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-- The cylinder cleaner candidate `cylCleanerCand` vanishes on all vertical cylinder edges. -/
lemma cylCleanerCand_vert_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (xv : BoundaryX0Link pcode M) (v : Fin 2) :
    cylCleanerCand pcode M b0 h x (Sum.inl (Sum.inr (Sum.inr (xv, v)))) = 0 := by
  dsimp [cylCleanerCand, restrictCX1]
  split_ifs with h_own
  · simp only [checkGen_outerVertCancelCochain_vert, zmod2_add_self]
  · rfl

/-- The exported boundary syndrome `exportXQ` of `cylCleanerCand` vanishes on vertical (`Sum.inr`) coordinates. -/
lemma exportXQ_cylCleanerCand_inr_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (eZ : ActiveZ pcode) (v : Fin 2) :
    exportXQ pcode M (cylCleanerCand pcode M b0 h x) (Sum.inr (eZ, v)) = 0 := by
  rw [exportXQ_apply]
  apply Finset.sum_eq_zero
  intro qX _
  rcases qX with _ | ⟨_ | ⟨xv, v'⟩⟩
  · exact zero_mul _
  · exact zero_mul _
  · rw [cylCleanerCand_vert_eq_zero, mul_zero]

/-- Expresses `weightNetExportXQ` of `cylCleanerCand` as the cardinality of active horizontal boundary arms. -/
lemma weightNetExportXQ_cylCleanerCand_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    weightNetExportXQ pcode M (cylCleanerCand pcode M b0 h x) =
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin 3 =>
        (∑ k : Fin (M + 1), exportXQ pcode M (cylCleanerCand pcode M b0 h x) (Sum.inl (p.1, k, p.2))) ≠ 0)).card := by
  dsimp [weightNetExportXQ]
  have h_second : (Finset.univ.filter (fun p : ActiveZ pcode × Fin 2 =>
      exportXQ pcode M (cylCleanerCand pcode M b0 h x) (Sum.inr (p.1, p.2)) ≠ 0)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ⟨eZ, v⟩ _
    exact not_not.mpr (exportXQ_cylCleanerCand_inr_eq_zero pcode M b0 h x eZ v)
  rw [h_second, add_zero]

/-- The support of `cylCleanerCand` is strictly contained in the `x0`-cylinder (`cX1OwnerX = x0`). -/
lemma cylCleanerCand_support {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X)
    (q : BDLStepXQ pcode M) (hq : cylCleanerCand pcode M b0 h x q ≠ 0) :
    ∃ qX, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x := by
  rcases q with qX | qQ
  · dsimp [cylCleanerCand, restrictCX1] at hq
    by_cases hx : cX1OwnerX pcode M qX = x
    · exact ⟨qX, rfl, hx⟩
    · rw [if_neg hx] at hq; exact False.elim (hq rfl)
  · exact False.elim (hq rfl)

/-- Adding `cylCleanerCand` cancels the `x0`-restricted cylinder syndrome `restrictCX2`. -/
lemma restrictCX2_syndrome_add_cylCleanerCand_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    restrictCX2 pcode M x
      (syndrome (dualCode (bdlCylinderStepX pcode M)) (h + cylCleanerCand pcode M b0 h x)) = 0 := by
  have h_eq : cylCleanerCand pcode M b0 h x =
      restrictCX1 pcode M x
        (h + checkGen (dualCode (bdlCylinderStepX pcode M))
          (apexRadialCocycle pcode M h + outerVertCancelCochain pcode M b0 h)) := by
    dsimp [cylCleanerCand, apexResidualCocycle]
    rw [map_add, add_assoc]
  rw [h_eq]
  exact restrictCX2_syndrome_add_restrictCX1_eq_zero pcode M x h
    (apexRadialCocycle pcode M h + outerVertCancelCochain pcode M b0 h)

/-- Telescopes the collar vertical check sum along a boundary arm in the cylinder. -/
lemma collar_vert_sum_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2)
    (s : ActiveZLink pcode) (k : Fin (M + 1)) (v : Fin 2) :
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k, v)))) +
    apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, v)))) =
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)))) +
      apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ)))) +
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inr (s, k, v))) := by
  let h' := apexResidualCocycle pcode M h
  have h_syn : syndrome (dualCode (bdlCylinderStepX pcode M)) h' (Sum.inl (Sum.inr (s, k, v))) =
      syndrome (dualCode (bdlCylinderStepX pcode M)) h (Sum.inl (Sum.inr (s, k, v))) :=
    syndrome_add_checkGen_dual (bdlCylinderStepX pcode M) h (apexRadialCocycle pcode M h) _
  have h_expand : syndrome (dualCode (bdlCylinderStepX pcode M)) h' (Sum.inl (Sum.inr (s, k, v))) =
      h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)))) +
      h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ)))) +
      h' (Sum.inl (Sum.inr (Sum.inr (bxStartLink pcode M s k, v)))) +
      h' (Sum.inl (Sum.inr (Sum.inr (bxEndLink pcode M s k, v)))) := by
    dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
    rw [Fintype.sum_sum_type]
    have hQ : (∑ qQ : BDLCQ1 pcode M,
        bdlStepXCheckZ pcode M (Sum.inl (Sum.inr (s, k, v))) (Sum.inr qQ) * h' (Sum.inr qQ)) = 0 :=
      Finset.sum_eq_zero (fun _ _ => zero_mul _)
    rw [hQ, add_zero]
    dsimp [bdlStepXCheckZ, bdlDeltaX1]
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)))]
    · rw [Finset.sum_eq_single (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ)))]
      · rw [Finset.sum_eq_single (Sum.inr (Sum.inr (bxStartLink pcode M s k, v)))]
        · rw [Finset.sum_eq_single (Sum.inr (Sum.inr (bxEndLink pcode M s k, v)))]
          · simp
          · intro qX _ hne; rw [if_neg hne, zero_mul]
          · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
        · intro qX _ hne; rw [if_neg hne, zero_mul]
        · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
      · intro qX _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro qX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  rw [← h_syn, h_expand]
  have h0 := zmod2_add_self (h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0)))))
  have h1 := zmod2_add_self (h' (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ)))))
  linear_combination -h0 - h1

/-- Evaluates `checkGen` of `outerVertCancelCochain` on outer boundary segment edges. -/
lemma checkGen_outerVertCancelCochain_outer {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (b0 : Fin 3) (h : BDLStepXQ pcode M → ZMod 2)
    (s : ActiveZLink pcode) (k : Fin (M + 1)) (b : Fin 3) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (outerVertCancelCochain pcode M b0 h)
      (Sum.inl (Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, b)))) =
    outerVertCancelCochain pcode M b0 h (Sum.inr (mkOuterShellVertex pcode M (bxStartLink pcode M s k), b)) +
    outerVertCancelCochain pcode M b0 h (Sum.inr (mkOuterShellVertex pcode M (bxEndLink pcode M s k), b)) := by
  dsimp [checkGen, f2CheckGen, dualCode, dualF2ChainComplex, bdlCylinderStepX]
  dsimp [bdlStepXCheckX, bdlDeltaX0]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_eq_single (Sum.inr (shellSegStartVertex pcode M (mkOuterShellSegment pcode M s k), b))]
  · rw [Finset.sum_eq_single (Sum.inr (shellSegEndVertex pcode M (mkOuterShellSegment pcode M s k), b))]
    · rw [if_pos rfl, if_pos rfl, one_mul, one_mul, shellSegStartVertex_outer, shellSegEndVertex_outer]
    · intro mX _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro mX _ hne; rw [if_neg hne, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

end BDLDecoder

/-! ## 3. 3-Line $\mathbb{Z}_{\ge 0}$-Subadditivity on 2-Qubit and 3-Qubit Checks -/

/-- Two-term $\mathbb{Z}_{\ge 0}$-subadditivity: $|u_1 + u_2|_{\mathbb{Z}} \le |u_1|_{\mathbb{Z}} + |u_2|_{\mathbb{Z}}$. -/
lemma zmod2ToNat_two_term_subadditive (u1 u2 : ZMod 2) :
    (if (u1 + u2) ≠ 0 then 1 else 0) ≤
      (if u1 ≠ 0 then 1 else 0) + (if u2 ≠ 0 then 1 else 0) := by
  simpa only [← zmod2ToNat_eq_ite] using zmod2ToNat_add_le u1 u2

/-- Three-term $\mathbb{Z}_{\ge 0}$-subadditivity:
    $|u_1 + u_2 + u_3|_{\mathbb{Z}} \le |u_1|_{\mathbb{Z}} + |u_2|_{\mathbb{Z}} + |u_3|_{\mathbb{Z}}$. -/
lemma zmod2ToNat_three_term_subadditive (u1 u2 u3 : ZMod 2) :
    (if (u1 + u2 + u3) ≠ 0 then 1 else 0) ≤
      (if u1 ≠ 0 then 1 else 0) + (if u2 ≠ 0 then 1 else 0) + (if u3 ≠ 0 then 1 else 0) := by
  simp only [← zmod2ToNat_eq_ite]
  exact (zmod2ToNat_add_le (u1 + u2) u3).trans
    (Nat.add_le_add_right (zmod2ToNat_add_le u1 u2) _)

/-- Multiplicativity of the $\{0, 1\}$ lift: $|a \cdot b|_{\mathbb{Z}} = |a|_{\mathbb{Z}} \cdot |b|_{\mathbb{Z}}$. -/
lemma zmod2ToNat_mul (a b : ZMod 2) :
    zmod2ToNat (a * b) = zmod2ToNat a * zmod2ToNat b := by
  fin_cases a <;> fin_cases b <;> decide

/-- **Bipartite Syndrome Subadditivity**:
    For any finite check set $E$, qubit set $Q$, parity check matrix $H : E \to Q \to \mathrm{ZMod}\;2$,
    and 1-chain $c_1 : Q \to \mathrm{ZMod}\;2$, the syndrome weight is bounded by the double sum of
    active qubit indicators weighted by check-qubit incidence. -/
theorem cylinder_inner_syndrome_subadditive {E Q : Type*} [Fintype E] [Fintype Q]
    (H : E → Q → ZMod 2) (c1 : Q → ZMod 2) :
    (∑ e : E, zmod2ToNat (∑ q : Q, H e q * c1 q)) ≤
      ∑ q : Q, (∑ e : E, zmod2ToNat (H e q)) * zmod2ToNat (c1 q) := by
  have h_row : ∀ e : E,
      zmod2ToNat (∑ q : Q, H e q * c1 q) ≤ ∑ q : Q, zmod2ToNat (H e q) * zmod2ToNat (c1 q) := by
    intro e
    refine (zmod2ToNat_sum_le Finset.univ (fun q => H e q * c1 q)).trans ?_
    apply Finset.sum_le_sum
    intro q _
    rw [zmod2ToNat_mul]
  calc (∑ e : E, zmod2ToNat (∑ q : Q, H e q * c1 q))
    _ ≤ ∑ e : E, ∑ q : Q, zmod2ToNat (H e q) * zmod2ToNat (c1 q) :=
      Finset.sum_le_sum (fun e _ => h_row e)
    _ = ∑ q : Q, ∑ e : E, zmod2ToNat (H e q) * zmod2ToNat (c1 q) := Finset.sum_comm
    _ = ∑ q : Q, (∑ e : E, zmod2ToNat (H e q)) * zmod2ToNat (c1 q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_mul]

/-- **Degree-Bounded Cylinder Inner Syndrome Contraction**:
    When every qubit $q \in Q$ has inner check degree at most $d$ ($\sum_{e \in E} |H(e,q)|_{\mathbb{Z}} \le d$),
    the inner syndrome weight satisfies $|D_X^{(0)} c_1|_{\mathbb{Z}} \le d \sum_{q \in Q} |c_1(q)|_{\mathbb{Z}}$. -/
theorem cylinder_inner_syndrome_weight_le_deg_mul {E Q : Type*} [Fintype E] [Fintype Q]
    (H : E → Q → ZMod 2) (c1 : Q → ZMod 2) (d : ℕ)
    (h_deg : ∀ q : Q, (∑ e : E, zmod2ToNat (H e q)) ≤ d) :
    (∑ e : E, zmod2ToNat (∑ q : Q, H e q * c1 q)) ≤
      d * (∑ q : Q, zmod2ToNat (c1 q)) := by
  calc (∑ e : E, zmod2ToNat (∑ q : Q, H e q * c1 q))
    _ ≤ ∑ q : Q, (∑ e : E, zmod2ToNat (H e q)) * zmod2ToNat (c1 q) :=
      cylinder_inner_syndrome_subadditive H c1
    _ ≤ ∑ q : Q, d * zmod2ToNat (c1 q) :=
      Finset.sum_le_sum (fun q _ => Nat.mul_le_mul_right _ (h_deg q))
    _ = d * (∑ q : Q, zmod2ToNat (c1 q)) := by
      rw [← Finset.mul_sum]

/-- Expresses `BDLDecoder.wt3Cyl` as the $\mathbb{Z}_{\ge 0}$-lift sum $\sum_{b=0}^2 |\alpha_b|_{\mathbb{Z}}$. -/
lemma wt3Cyl_eq_sum_zmod2ToNat (α : Fin 3 → ZMod 2) :
    BDLDecoder.wt3Cyl α = zmod2ToNat (α 0) + zmod2ToNat (α 1) + zmod2ToNat (α 2) := by
  dsimp [BDLDecoder.wt3Cyl]
  simp only [zmod2ToNat_eq_ite]

/-- Expresses `BDLDecoder.wt2Cyl` as the $\mathbb{Z}_{\ge 0}$-lift sum $\sum_{v=0}^1 |\sigma_{c,v}|_{\mathbb{Z}}$. -/
lemma wt2Cyl_eq_sum_zmod2ToNat (σ_c : Fin 2 → ZMod 2) :
    BDLDecoder.wt2Cyl σ_c = zmod2ToNat (σ_c 0) + zmod2ToNat (σ_c 1) := by
  dsimp [BDLDecoder.wt2Cyl]
  simp only [zmod2ToNat_eq_ite]

/-- **Reference-Layer Subadditivity (`cyl_sector_subadditive_via_zmod2ToNat`)**. -/
theorem cyl_sector_subadditive_via_zmod2ToNat (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) :
    BDLDecoder.wt3Cyl (BDLDecoder.cylArmVec0 α σ_c) +
    BDLDecoder.wt3Cyl (BDLDecoder.cylArmVec1 α σ_c) +
    BDLDecoder.wt3Cyl (BDLDecoder.cylArmVec2 α σ_c) ≤
      3 * BDLDecoder.wt3Cyl α + 4 * BDLDecoder.wt2Cyl σ_c :=
  BDLDecoder.cyl_sector_pointwise_subadditive α σ_c

/-- **Minimum Reference-Layer Sector Contraction (`min_cylArmVec_weight_le`)**. -/
theorem min_cylArmVec_weight_le (α : Fin 3 → ZMod 2) (σ_c : Fin 2 → ZMod 2) :
    3 * min (BDLDecoder.wt3Cyl (BDLDecoder.cylArmVec0 α σ_c))
          (min (BDLDecoder.wt3Cyl (BDLDecoder.cylArmVec1 α σ_c))
               (BDLDecoder.wt3Cyl (BDLDecoder.cylArmVec2 α σ_c))) ≤
      3 * BDLDecoder.wt3Cyl α + 4 * BDLDecoder.wt2Cyl σ_c := by
  have h := BDLDecoder.cyl_sector_pointwise_subadditive α σ_c
  omega

end WeldedHierarchy
