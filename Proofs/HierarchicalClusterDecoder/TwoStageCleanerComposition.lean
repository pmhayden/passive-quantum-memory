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

import Proofs.HierarchicalClusterDecoder.Stage2StarCleaner

/-!
# Global Two-Stage Syndrome Cleaner Composition and Coarse Residual Projection

Assembles the global Stage-1 cylinder cleaner `cleanStage1X`, Stage-2 star cleaner `cleanStage2Q`, and composite two-stage cleaner `cleanTwoStageRX`, together with the cleaned coarse 1-cochain `rxCleanedCoarseProj` and coarse syndrome `rxCleanedCoarseSyndrome`. Proves disjoint local support and exact cancellation of all fine cylinder and star check syndromes (`restrictCX2_syndrome_add_cleanTwoStageRX_eq_zero`, `restrictCQ2_syndrome_add_cleanTwoStageRX_eq_zero`).

## References

* Part I, Section 4.1 (`subsec:cleaner-architecture`)
* Part I, Section 4.2 (`subsec:stage1-cylinder`), Lemma 4.1 (`lem:stage1-cylinder-cleaner`)
* Part I, Section 4.3 (`subsec:stage2-star`), Lemma 4.2 (`lem:stage2-star-cleaner`), Theorem 4.3 (`thm:16-27-contraction`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Stage-1 Cylinder Cleaner Specification -/

/-- Predicate for a valid Stage-1 local cleaner `u` on cylinder `x : M_X` for restricted syndrome `rS`. -/
def IsValidCylinderCleaner {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (rS : BDLStepXMZ pcode M → ZMod 2) (x : M_X)
    (u : BDLStepXQ pcode M → ZMod 2) : Prop :=
  (∀ q, u q ≠ 0 → ∃ qX, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x) ∧
  restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) u) = rS ∧
  3 * weightNetExportXQ pcode M u ≤ 4 * syndromeWeightNat rS

/-- Stage-1 cylinder cleaner on cylinder `x : M_X`, depending only on `restrictCX2 pcode M x S`. -/
noncomputable def cleanCylinderXAux {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (rS : BDLStepXMZ pcode M → ZMod 2) (x : M_X) : BDLStepXQ pcode M → ZMod 2 :=
  if rS = 0 then 0
  else if h_ex : ∃ u : BDLStepXQ pcode M → ZMod 2, IsValidCylinderCleaner pcode M rS x u
  then Classical.choose h_ex
  else 0

/-- Local cylinder cleaner on cylinder `x0`, vanishing when `restrictCX2 s = 0`. -/
noncomputable def cleanCylinderX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) (x : M_X) : BDLStepXQ pcode M → ZMod 2 :=
  cleanCylinderXAux pcode M (restrictCX2 pcode M x S) x

/-- Global Stage-1 cleaner summed over all cylinders `x : M_X`. -/
noncomputable def cleanStage1X {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) : BDLStepXQ pcode M → ZMod 2 :=
  ∑ x : M_X, cleanCylinderX pcode M S x

/-- If `restrictCX2 pcode M x0 s = 0`, then `cleanCylinderX pcode M x0 s = 0`. -/
lemma cleanCylinderX_eq_zero_of_restrictCX2_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) (x : M_X)
    (h0 : restrictCX2 pcode M x S = 0) :
    cleanCylinderX pcode M S x = 0 := by
  dsimp [cleanCylinderX, cleanCylinderXAux]
  rw [if_pos h0]

/-- `cleanCylinderX` depends on `s` only through its restriction `restrictCX2 pcode M x0 s`. -/
lemma cleanCylinderX_congr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S S' : BDLStepXMZ pcode M → ZMod 2) (x : M_X)
    (h_eq : restrictCX2 pcode M x S = restrictCX2 pcode M x S') :
    cleanCylinderX pcode M S x = cleanCylinderX pcode M S' x :=
  congr_arg (fun rS => cleanCylinderXAux pcode M rS x) h_eq

/-- The support of `cleanCylinderX pcode M x0 s` lies entirely inside cylinder `x0`. -/
lemma cleanCylinderX_support {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) (x : M_X) (q : BDLStepXQ pcode M)
    (hq : cleanCylinderX pcode M S x q ≠ 0) :
    ∃ qX, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x := by
  dsimp [cleanCylinderX, cleanCylinderXAux] at hq
  by_cases h0 : restrictCX2 pcode M x S = 0
  · rw [if_pos h0] at hq
    exact False.elim (hq rfl)
  · rw [if_neg h0] at hq
    by_cases hex : ∃ u, IsValidCylinderCleaner pcode M (restrictCX2 pcode M x S) x u
    · rw [dif_pos hex] at hq
      exact (Classical.choose_spec hex).1 q hq
    · rw [dif_neg hex] at hq
      exact False.elim (hq rfl)

/-- Additivity of the cylinder syndrome restriction `restrictCX2`. -/
lemma restrictCX2_add {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X)
    (S₁ S₂ : BDLStepXMZ pcode M → ZMod 2) :
    restrictCX2 pcode M x (S₁ + S₂) = restrictCX2 pcode M x S₁ + restrictCX2 pcode M x S₂ := by
  ext mZ
  dsimp [restrictCX2, restrictStepXMZ]
  by_cases hm : stepXMZOwnerTanner pcode M mZ ∈ ({inVX x} : Finset (TannerVertex Q M_Z M_X))
  · rw [if_pos hm, if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, if_neg hm, add_zero]

/-- Full specification of `cleanCylinderX`: support locality, syndrome cancellation, and export weight bound. -/
lemma cleanCylinderX_spec {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    let S := syndrome (dualCode (bdlCylinderStepX pcode M)) h
    let u_x := cleanCylinderX pcode M S x
    restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) u_x) = restrictCX2 pcode M x S ∧
    restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) (h + u_x)) = 0 ∧
    3 * weightNetExportXQ pcode M u_x ≤ 4 * weightCX2OnCyl pcode M x S := by
  intro S u_x
  have hex : ∃ u : BDLStepXQ pcode M → ZMod 2,
      IsValidCylinderCleaner pcode M (restrictCX2 pcode M x S) x u := by
    obtain ⟨u, h_supp, h_clear, h_wt, _⟩ := exists_local_cylinder_cleaner pcode M hov h_conn h x
    refine ⟨u, h_supp, ?_, h_wt⟩
    rw [map_add, restrictCX2_add] at h_clear
    ext mZ
    have hm := congr_fun h_clear mZ
    simp only [Pi.add_apply, Pi.zero_apply] at hm
    have h2 := zmod2_add_self (restrictCX2 pcode M x S mZ)
    linear_combination hm - h2
  have h_ux_eq : restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) u_x) =
      restrictCX2 pcode M x S ∧
      3 * weightNetExportXQ pcode M u_x ≤ 4 * weightCX2OnCyl pcode M x S := by
    dsimp [u_x, cleanCylinderX, cleanCylinderXAux]
    by_cases h0 : restrictCX2 pcode M x S = 0
    · rw [if_pos h0, map_zero]
      have h_zero_r : restrictCX2 pcode M x 0 = 0 := by
        ext mZ; dsimp [restrictCX2, restrictStepXMZ]; exact ite_self _
      have h_exp0 : exportXQ pcode M 0 = 0 := by
        ext mZQ; rw [exportXQ_apply]; exact Finset.sum_eq_zero (fun _ _ => mul_zero _)
      refine ⟨h_zero_r.trans h0.symm, ?_⟩
      dsimp [weightNetExportXQ]
      rw [h_exp0]
      simp
    · rw [if_neg h0, dif_pos hex]
      exact ⟨(Classical.choose_spec hex).2.1, (Classical.choose_spec hex).2.2⟩
  refine ⟨h_ux_eq.1, ?_, h_ux_eq.2⟩
  rw [map_add, restrictCX2_add, h_ux_eq.1]
  ext mZ
  exact zmod2_add_self _

/-- A 1-chain supported on cylinder `x1 ≠ x0` has zero restricted syndrome on cylinder `x0`. -/
lemma restrictCX2_syndrome_eq_zero_of_support_ne {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x x' : M_X) (hne : x' ≠ x)
    (u : BDLStepXQ pcode M → ZMod 2)
    (h_supp : ∀ q, u q ≠ 0 → ∃ qX, q = Sum.inl qX ∧ cX1OwnerX pcode M qX = x') :
    restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) u) = 0 := by
  ext mZ
  dsimp [restrictCX2, restrictStepXMZ]
  split_ifs with hmZ
  · rcases mZ with mZX | (mZQ | mZZ)
    · dsimp [stepXMZOwnerTanner, inVX] at hmZ
      rw [Finset.mem_singleton, Sum.inl.injEq] at hmZ
      dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
      apply Finset.sum_eq_zero; intro q _
      by_cases hq : u q = 0
      · rw [hq, mul_zero]
      · obtain ⟨qX, rfl, h_own⟩ := h_supp q hq
        dsimp [bdlStepXCheckZ]
        rw [bdlDeltaX1_eq_zero_of_owner_ne pcode M mZX qX (by rw [h_own, hmZ]; exact hne), zero_mul]
    · dsimp [stepXMZOwnerTanner, inVQ, inVX] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
    · dsimp [stepXMZOwnerTanner, inVZ, inVX] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
  · rfl

/-- Stage-1 cylinder cleaning `cleanStage1X` zeroes out `restrictCX2` on every cylinder `x0`. -/
lemma restrictCX2_syndrome_add_cleanStage1X_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    restrictCX2 pcode M x
      (syndrome (dualCode (bdlCylinderStepX pcode M))
        (h + cleanStage1X pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) = 0 := by
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S := syndrome D_1 h
  rw [map_add, restrictCX2_add]
  have h_sum_syn : restrictCX2 pcode M x (syndrome D_1 (cleanStage1X pcode M S)) =
      restrictCX2 pcode M x (syndrome D_1 (cleanCylinderX pcode M S x)) := by
    ext mZ
    dsimp [cleanStage1X]
    have h_map : syndrome D_1 (∑ x' : M_X, cleanCylinderX pcode M S x') =
        ∑ x' : M_X, syndrome D_1 (cleanCylinderX pcode M S x') := map_sum (syndrome D_1) _ _
    dsimp [restrictCX2, restrictStepXMZ]
    split_ifs with hmZ
    · rw [h_map, Finset.sum_apply, Finset.sum_eq_single x]
      · intro x' _ hne
        have h_z := congr_fun (restrictCX2_syndrome_eq_zero_of_support_ne pcode M x x' hne
          (cleanCylinderX pcode M S x') (cleanCylinderX_support pcode M S x')) mZ
        dsimp [restrictCX2, restrictStepXMZ] at h_z
        rw [if_pos hmZ] at h_z
        exact h_z
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ x))
    · rfl
  rw [h_sum_syn, (cleanCylinderX_spec pcode M hov h_conn h x).1]
  ext mZ
  exact zmod2_add_self _

/-! ## 2. Stage-2 Star Cleaner Definitions and Support -/

/-- Predicate for a valid Stage-2 local cleaner `v` on star `q0 : Q` for restricted syndrome `rS1`. -/
def IsValidStarCleaner {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (rS1 : BDLStepXMZ pcode M → ZMod 2) (q0 : Q)
    (v : BDLStepXQ pcode M → ZMod 2) : Prop :=
  (∀ q, v q ≠ 0 → ∃ qQ, q = Sum.inr qQ ∧ cQ1OwnerQ pcode M qQ = q0) ∧
  restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) v) = rS1 ∧
  3 * (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => exportQZ pcode M v mZ ≠ 0)).card ≤
    4 * weightNetCQ2OnStar pcode M q0 rS1

/-- Auxiliary star cleaner selected via `Classical.choose` from `exists_local_star_cleaner`. -/
noncomputable def cleanStarQAux {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (rS1 : BDLStepXMZ pcode M → ZMod 2) (q0 : Q) : BDLStepXQ pcode M → ZMod 2 :=
  if rS1 = 0 then 0
  else if h_ex : ∃ v : BDLStepXQ pcode M → ZMod 2, IsValidStarCleaner pcode M rS1 q0 v
  then Classical.choose h_ex
  else 0

/-- Stage-2 star cleaner on star `q0 : Q` given the Stage-1 residual syndrome `S1`. -/
noncomputable def cleanStarQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 : BDLStepXMZ pcode M → ZMod 2) (q0 : Q) : BDLStepXQ pcode M → ZMod 2 :=
  cleanStarQAux pcode M (restrictCQ2 pcode M q0 S1) q0

/-- Global Stage-2 cleaner summed over all stars `q0 : Q`. -/
noncomputable def cleanStage2Q {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 : BDLStepXMZ pcode M → ZMod 2) : BDLStepXQ pcode M → ZMod 2 :=
  ∑ q0 : Q, cleanStarQ pcode M S1 q0

/-- Total local two-stage cleaner `f(S) = f_X(S) + f_Q(S1)` depending only on `S`. -/
noncomputable def cleanTwoStageRX {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) : BDLStepXQ pcode M → ZMod 2 :=
  let fX := cleanStage1X pcode M S
  let S1 := S + syndrome (dualCode (bdlCylinderStepX pcode M)) fX
  fX + cleanStage2Q pcode M S1

/-- The locally cleaned coarse 1-cochain `e_coarse(h) : Q → ZMod 2`. -/
noncomputable def rxCleanedCoarseProj {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h : BDLStepXQ pcode M → ZMod 2) : Q → ZMod 2 :=
  projCylinderLXLayer pcode M 0
    (h + cleanTwoStageRX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))

/-- The locally cleaned coarse 2-cochain `σ_coarse(S) : M_Z → ZMod 2`. -/
noncomputable def rxCleanedCoarseSyndrome {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S : BDLStepXMZ pcode M → ZMod 2) : M_Z → ZMod 2 :=
  let S2 := S + syndrome (dualCode (bdlCylinderStepX pcode M)) (cleanTwoStageRX pcode M S)
  fun z0 => S2 (Sum.inr (Sum.inr (z0, 0)))

/-- If `restrictCQ2 pcode M q0 s = 0`, then `cleanStarQ pcode M hq_z q0 s = 0`. -/
lemma cleanStarQ_eq_zero_of_restrictCQ2_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 : BDLStepXMZ pcode M → ZMod 2) (q0 : Q)
    (h0 : restrictCQ2 pcode M q0 S1 = 0) :
    cleanStarQ pcode M S1 q0 = 0 := by
  dsimp [cleanStarQ, cleanStarQAux]
  rw [if_pos h0]

/-- `cleanStarQ` depends on `s` only through its restriction `restrictCQ2 pcode M q0 s`. -/
lemma cleanStarQ_congr {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 S1' : BDLStepXMZ pcode M → ZMod 2) (q0 : Q)
    (h_eq : restrictCQ2 pcode M q0 S1 = restrictCQ2 pcode M q0 S1') :
    cleanStarQ pcode M S1 q0 = cleanStarQ pcode M S1' q0 :=
  congr_arg (fun rS1 => cleanStarQAux pcode M rS1 q0) h_eq

/-- The support of `cleanStarQ pcode M hq_z q0 s` lies entirely inside star `q0`. -/
lemma cleanStarQ_support {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 : BDLStepXMZ pcode M → ZMod 2) (q0 : Q) (q : BDLStepXQ pcode M)
    (hq : cleanStarQ pcode M S1 q0 q ≠ 0) :
    ∃ qQ, q = Sum.inr qQ ∧ cQ1OwnerQ pcode M qQ = q0 := by
  dsimp [cleanStarQ, cleanStarQAux] at hq
  by_cases h0 : restrictCQ2 pcode M q0 S1 = 0
  · rw [if_pos h0] at hq
    exact False.elim (hq rfl)
  · rw [if_neg h0] at hq
    by_cases hex : ∃ v, IsValidStarCleaner pcode M (restrictCQ2 pcode M q0 S1) q0 v
    · rw [dif_pos hex] at hq
      exact (Classical.choose_spec hex).1 q hq
    · rw [dif_neg hex] at hq
      exact False.elim (hq rfl)

/-- Additivity of the star syndrome restriction `restrictCQ2`. -/
lemma restrictCQ2_add {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 : Q)
    (S₁ S₂ : BDLStepXMZ pcode M → ZMod 2) :
    restrictCQ2 pcode M q0 (S₁ + S₂) = restrictCQ2 pcode M q0 S₁ + restrictCQ2 pcode M q0 S₂ := by
  ext mZ
  dsimp [restrictCQ2, restrictStepXMZ]
  by_cases hm : stepXMZOwnerTanner pcode M mZ ∈ ({inVQ q0} : Finset (TannerVertex Q M_Z M_X))
  · rw [if_pos hm, if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, if_neg hm, add_zero]

/-- Star coboundary matrix `bdlDeltaQ1` vanishes between distinct star owners. -/
lemma bdlDeltaQ1_eq_zero_of_owner_ne {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (mZQ : BDLCQ2 pcode M) (qQ : BDLCQ1 pcode M)
    (hne : cQ1OwnerQ pcode M qQ ≠ cQ2OwnerQ pcode M mZQ) :
    bdlDeltaQ1 pcode M mZQ qQ = 0 := by
  rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
  · dsimp [bdlDeltaQ1]
    have h1 : qQ ≠ (armStart pcode M eZ k, bZ) := by
      intro h; subst h
      exact hne (xq0OwnerQ_armStart pcode M eZ k)
    have h2 : qQ ≠ (armEnd pcode M eZ k, bZ) := by
      intro h; subst h
      exact hne (xq0OwnerQ_armEnd pcode M eZ k)
    rw [if_neg h1, if_neg h2, add_zero]
  · dsimp [bdlDeltaQ1]
    have h1 : qQ ≠ (Sum.inr (Sum.inr eZ), 0) := by
      intro h; subst h; exact hne rfl
    have h2 : qQ ≠ (Sum.inr (Sum.inr eZ), v.succ) := by
      intro h; subst h; exact hne rfl
    rw [if_neg h1, if_neg h2, add_zero]

/-- A 1-chain supported on star `q1 ≠ q0` has zero restricted syndrome on star `q0`. -/
lemma restrictCQ2_syndrome_eq_zero_of_support_ne {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (q0 q0' : Q) (hne : q0' ≠ q0)
    (v : BDLStepXQ pcode M → ZMod 2)
    (h_supp : ∀ q, v q ≠ 0 → ∃ qQ, q = Sum.inr qQ ∧ cQ1OwnerQ pcode M qQ = q0') :
    restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) v) = 0 := by
  ext mZ
  dsimp [restrictCQ2, restrictStepXMZ]
  split_ifs with hmZ
  · rcases mZ with mZX | (mZQ | mZZ)
    · dsimp [stepXMZOwnerTanner, inVX, inVQ] at hmZ
      rw [Finset.mem_singleton] at hmZ
      nomatch hmZ
    · dsimp [stepXMZOwnerTanner, inVQ] at hmZ
      rw [Finset.mem_singleton, Sum.inr.injEq, Sum.inl.injEq] at hmZ
      dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
      apply Finset.sum_eq_zero
      intro q _
      by_cases hq : v q = 0
      · rw [hq, mul_zero]
      · obtain ⟨qQ, rfl, h_own⟩ := h_supp q hq
        dsimp [bdlStepXCheckZ]
        rw [bdlDeltaQ1_eq_zero_of_owner_ne pcode M mZQ qQ (by rw [h_own, hmZ]; exact hne), zero_mul]
    · dsimp [stepXMZOwnerTanner, inVZ, inVQ] at hmZ
      rw [Finset.mem_singleton] at hmZ
      nomatch hmZ
  · rfl

/-- A 1-chain supported on `BDLCQ1` (`Sum.inr`) has zero restricted syndrome on every cylinder `x0`. -/
lemma restrictCX2_syndrome_eq_zero_of_support_Q {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X)
    (v : BDLStepXQ pcode M → ZMod 2)
    (h_supp : ∀ qX : BDLCX1 pcode M, v (Sum.inl qX) = 0) :
    restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) v) = 0 := by
  ext mZ
  dsimp [restrictCX2, restrictStepXMZ]
  split_ifs with hmZ
  · rcases mZ with mZX | (mZQ | mZZ)
    · dsimp [syndrome, f2Syndrome, dualCode, dualF2ChainComplex, bdlCylinderStepX]
      apply Finset.sum_eq_zero
      intro q _
      rcases q with qX | qQ
      · rw [h_supp qX, mul_zero]
      · dsimp [bdlStepXCheckZ]; simp
    · dsimp [stepXMZOwnerTanner, inVQ, inVX] at hmZ
      rw [Finset.mem_singleton] at hmZ
      nomatch hmZ
    · dsimp [stepXMZOwnerTanner, inVZ, inVX] at hmZ
      rw [Finset.mem_singleton] at hmZ
      nomatch hmZ
  · rfl

/-! ## 3. Stage-2 and Two-Stage Syndrome Cancellation -/

/-- Full specification of `cleanStarQ`: support locality, syndrome cancellation, and export weight bound. -/
lemma cleanStarQ_spec {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h1 : BDLStepXQ pcode M → ZMod 2)
    (h1_cyl : ∀ x : M_X, restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) = 0)
    (q0 : Q) :
    let S1 := syndrome (dualCode (bdlCylinderStepX pcode M)) h1
    let v_q0 := cleanStarQ pcode M S1 q0
    restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) v_q0) = restrictCQ2 pcode M q0 S1 ∧
    restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) (h1 + v_q0)) = 0 ∧
    3 * (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => exportQZ pcode M v_q0 mZ ≠ 0)).card ≤
      4 * weightNetCQ2OnStar pcode M q0 S1 ∧
    3 * (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => exportQZ pcode M v_q0 mZ ≠ 0)).card ≤
      4 * syndromeWeightNat (restrictCQ2 pcode M q0 S1) := by
  intro S1 v_q0
  have hex : ∃ v : BDLStepXQ pcode M → ZMod 2,
      IsValidStarCleaner pcode M (restrictCQ2 pcode M q0 S1) q0 v := by
    obtain ⟨v, h_supp, h_clear, h_wt, _⟩ := exists_local_star_cleaner pcode M hov h_conn h1 h1_cyl q0
    refine ⟨v, h_supp, ?_, h_wt⟩
    rw [map_add, restrictCQ2_add] at h_clear
    ext mZ
    have hm := congr_fun h_clear mZ
    simp only [Pi.add_apply, Pi.zero_apply] at hm
    have h2 := zmod2_add_self (restrictCQ2 pcode M q0 S1 mZ)
    linear_combination hm - h2
  have h_vq0_eq : restrictCQ2 pcode M q0 (syndrome (dualCode (bdlCylinderStepX pcode M)) v_q0) =
      restrictCQ2 pcode M q0 S1 ∧
      3 * (Finset.univ.filter (fun mZ : BDLCZ2 M_Z => exportQZ pcode M v_q0 mZ ≠ 0)).card ≤
        4 * weightNetCQ2OnStar pcode M q0 S1 := by
    by_cases h0 : restrictCQ2 pcode M q0 S1 = 0
    · have hv0 : v_q0 = 0 := cleanStarQ_eq_zero_of_restrictCQ2_eq_zero pcode M S1 q0 h0
      rw [hv0, map_zero]
      have h_zero_r : restrictCQ2 pcode M q0 0 = 0 := by
        ext mZ; dsimp [restrictCQ2, restrictStepXMZ]; exact ite_self _
      have h_exp0 : exportQZ pcode M 0 = 0 := by
        ext mZZ; rw [exportQZ_apply]; exact Finset.sum_eq_zero (fun _ _ => mul_zero _)
      refine ⟨h_zero_r.trans h0.symm, ?_⟩
      rw [h_exp0]
      simp
    · have hv_ex : v_q0 = Classical.choose hex := by
        dsimp [v_q0, cleanStarQ, cleanStarQAux]
        rw [if_neg h0, dif_pos hex]
      rw [hv_ex, ← weightNetCQ2OnStar_restrictCQ2_eq]
      exact ⟨(Classical.choose_spec hex).2.1, (Classical.choose_spec hex).2.2⟩
  have h_le_syn := weightNetCQ2OnStar_le_syndromeWeightNat_restrictCQ2 pcode M q0 S1
  refine ⟨h_vq0_eq.1, ?_, h_vq0_eq.2, by omega⟩
  rw [map_add, restrictCQ2_add, h_vq0_eq.1]
  ext mZ
  exact zmod2_add_self _

/-- Stage-2 star cleaning `cleanStage2Q` zeroes out `restrictCQ2` on every star `q0`. -/
lemma restrictCQ2_syndrome_add_cleanStage2Q_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h1 : BDLStepXQ pcode M → ZMod 2)
    (h1_cyl : ∀ x : M_X, restrictCX2 pcode M x (syndrome (dualCode (bdlCylinderStepX pcode M)) h1) = 0)
    (q0 : Q) :
    restrictCQ2 pcode M q0
      (syndrome (dualCode (bdlCylinderStepX pcode M))
        (h1 + cleanStage2Q pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h1))) = 0 := by
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S1 := syndrome D_1 h1
  rw [map_add, restrictCQ2_add]
  have h_sum_syn : restrictCQ2 pcode M q0 (syndrome D_1 (cleanStage2Q pcode M S1)) =
      restrictCQ2 pcode M q0 (syndrome D_1 (cleanStarQ pcode M S1 q0)) := by
    ext mZ
    dsimp [cleanStage2Q]
    have h_map : syndrome D_1 (∑ q0' : Q, cleanStarQ pcode M S1 q0') =
        ∑ q0' : Q, syndrome D_1 (cleanStarQ pcode M S1 q0') := map_sum (syndrome D_1) _ _
    dsimp [restrictCQ2, restrictStepXMZ]
    split_ifs with hmZ
    · rw [h_map, Finset.sum_apply, Finset.sum_eq_single q0]
      · intro q0' _ hne
        have h_z := congr_fun (restrictCQ2_syndrome_eq_zero_of_support_ne pcode M q0 q0' hne
          (cleanStarQ pcode M S1 q0') (cleanStarQ_support pcode M S1 q0')) mZ
        dsimp [restrictCQ2, restrictStepXMZ] at h_z
        rw [if_pos hmZ] at h_z
        exact h_z
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ q0))
    · rfl
  rw [h_sum_syn, (cleanStarQ_spec pcode M hov h_conn h1 h1_cyl q0).1]
  ext mZ
  exact zmod2_add_self _

/-- Stage-2 star cleaning `cleanStage2Q` vanishes on cylinder qubits (`Sum.inl`). -/
lemma cleanStage2Q_inl_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (S1 : BDLStepXMZ pcode M → ZMod 2) (qX : BDLCX1 pcode M) :
    cleanStage2Q pcode M S1 (Sum.inl qX) = 0 := by
  dsimp [cleanStage2Q]
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro q0 _
  by_contra h_nz
  obtain ⟨qQ, h_eq, _⟩ := cleanStarQ_support pcode M S1 q0 (Sum.inl qX) h_nz
  nomatch h_eq

/-- Combined two-stage cleaner `cleanTwoStageRX` zeroes out `restrictCX2` on every cylinder `x0`. -/
lemma restrictCX2_syndrome_add_cleanTwoStageRX_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (x : M_X) :
    restrictCX2 pcode M x
      (syndrome (dualCode (bdlCylinderStepX pcode M))
        (h + cleanTwoStageRX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) = 0 := by
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S := syndrome D_1 h
  let fX := cleanStage1X pcode M S
  let S1 := S + syndrome D_1 fX
  change restrictCX2 pcode M x (syndrome D_1 (h + (fX + cleanStage2Q pcode M S1))) = 0
  rw [← add_assoc, map_add, restrictCX2_add,
      restrictCX2_syndrome_add_cleanStage1X_eq_zero pcode M hov h_conn h x,
      restrictCX2_syndrome_eq_zero_of_support_Q pcode M x (cleanStage2Q pcode M S1)
        (cleanStage2Q_inl_eq_zero pcode M S1),
      add_zero]

/-- Combined two-stage cleaner `cleanTwoStageRX` zeroes out `restrictCQ2` on every star `q0`. -/
lemma restrictCQ2_syndrome_add_cleanTwoStageRX_eq_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (h_conn : HasConnectedXLinks pcode)
    (h : BDLStepXQ pcode M → ZMod 2) (q0 : Q) :
    restrictCQ2 pcode M q0
      (syndrome (dualCode (bdlCylinderStepX pcode M))
        (h + cleanTwoStageRX pcode M (syndrome (dualCode (bdlCylinderStepX pcode M)) h))) = 0 := by
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S := syndrome D_1 h
  let fX := cleanStage1X pcode M S
  let h1 := h + fX
  have h1_cyl : ∀ x : M_X, restrictCX2 pcode M x (syndrome D_1 h1) = 0 :=
    restrictCX2_syndrome_add_cleanStage1X_eq_zero pcode M hov h_conn h
  have h_S1 : S + syndrome D_1 fX = syndrome D_1 h1 := (map_add (syndrome D_1) h fX).symm
  change restrictCQ2 pcode M q0 (syndrome D_1 (h + (fX + cleanStage2Q pcode M (S + syndrome D_1 fX)))) = 0
  rw [← add_assoc, h_S1]
  exact restrictCQ2_syndrome_add_cleanStage2Q_eq_zero pcode M hov h_conn h1 h1_cyl q0

end BDLDecoder
end WeldedHierarchy
