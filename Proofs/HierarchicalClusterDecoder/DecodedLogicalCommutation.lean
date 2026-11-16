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

import Proofs.HierarchicalClusterDecoder.WitnessLiftingAndParityImmunity

/-!
# Ball-Restricted Parity Witness Lifting and Local Homological Logical Immunity

Defines `HasBallParityWitnessFamily` and proves single-step ball radius propagation across primal and dual cylinder steps (`hasBallParityWitnessFamily_cylinder_primal`, `hasBallParityWitnessFamily_cylinder_dual`). Establishes local homological logical immunity (`local_immunity_stabilizer_from_zero_syndrome`, `local_immunity_difference_stabilizer_of_same_syndrome`, `local_immunity_logical_pairing_invariant`) from Euclidean F2 linear TQO (`SatisfiesEucF2LinearTQO`).

## References

* Part I, Section 3.1 (`subsec:rca-trinity`), Definition 3.1 (`def:rca`), Proposition 3.3 (`prop:trinity-equivalence`)
* Part I, Section 5.2 (`subsec:cluster-decoder`), Definition 5.2 (`def:multiscale-cluster-decoder`), Proposition 5.3 (`prop:cluster-decoder-witness`)
-/

noncomputable section

open scoped Classical
open BigOperators

set_option maxHeartbeats 800000

namespace WeldedHierarchy
namespace BDLDecoder

/-! ## 1. Ball-Restricted Parity Witness Families and Perturbation Invariance -/

/-- Euclidean-ball-parametrized symmetric witness family invariant (`HasBallParityWitnessFamily`):
    for any two chains `e, e' : Q → ZMod 2` that agree outside `Ball3D x0 r` and have different
    decoded logical parities `ψ (syndrome code _) + dualPairing L_X _`, there exists a witness
    `c ∈ W` of weight at least `w` supported either in `syndrome code e` or in `syndrome code e'`. -/
def HasBallParityWitnessFamily {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (_L_Z L_X : Q → ZMod 2) (r : ℝ) (w N : ℕ) : Prop :=
  ∃ (ψ : (M_X → ZMod 2) → ZMod 2) (W : Finset (M_X → ZMod 2)),
    ψ 0 = 0 ∧
    W.card ≤ N ∧
    (∀ c ∈ W, (w : ℝ) ≤ syndromeWeight c) ∧
    (∀ (e e' : Q → ZMod 2) (x0 : Point3D),
      (∀ q : Q, e q ≠ e' q → code.posQ q ∈ ball3D x0 r) →
      ψ (syndrome code e') + dualPairing L_X e' ≠
        ψ (syndrome code e) + dualPairing L_X e →
      ∃ c ∈ W,
        (∀ m : M_X, c m ≠ 0 → syndrome code e m ≠ 0) ∨
        (∀ m : M_X, c m ≠ 0 → syndrome code e' m ≠ 0))

/-- Monotonicity of `HasBallParityWitnessFamily` in the pool-size bound `N`. -/
lemma hasBallParityWitnessFamily_mono_N {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {code : CSSCode3D Q M_Z M_X} {L_Z L_X : Q → ZMod 2} {r : ℝ} {w N N' : ℕ}
    (h_le : N ≤ N')
    (h_wit : HasBallParityWitnessFamily code L_Z L_X r w N) :
    HasBallParityWitnessFamily code L_Z L_X r w N' := by
  rcases h_wit with ⟨ψ, W, hψ0, hW_card, hW_wt, hW_fail⟩
  exact ⟨ψ, W, hψ0, hW_card.trans h_le, hW_wt, hW_fail⟩

/-- Involutive transport of `HasBallParityWitnessFamily` across `dualCode (dualCode code)`. -/
lemma hasBallParityWitnessFamily_dual_dual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    {code : CSSCode3D Q M_Z M_X} {L_Z L_X : Q → ZMod 2} {r : ℝ} {w N : ℕ}
    (h : HasBallParityWitnessFamily code L_Z L_X r w N) :
    HasBallParityWitnessFamily (dualCode (dualCode code)) L_Z L_X r w N := h

/-- Unscaling `HasBallParityWitnessFamily` across `bdlPerturbStep` (primal sector). -/
lemma hasBallParityWitnessFamily_bdlPerturbStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L : ℕ) (hL : 0 < L)
    (cQ : Q → Point3D) (cZ : M_Z → Point3D) (cX : M_X → Point3D)
    {C_shift : ℝ} (hC : 0 ≤ C_shift)
    (hcQ : ∀ q, distSq3D (cQ q) (fun _ => 0) ≤ (C_shift * (L : ℝ)) ^ 2)
    {L_Z L_X : Q → ZMod 2} {r r_coarse : ℝ} {w N : ℕ}
    (hr : 0 ≤ r) (h_rad : r / (L : ℝ) + C_shift ≤ r_coarse)
    (h_wit : HasBallParityWitnessFamily code L_Z L_X r_coarse w N) :
    HasBallParityWitnessFamily (bdlPerturbStep code L cQ cZ cX) L_Z L_X r w N := by
  rcases h_wit with ⟨ψ, W, hψ0, hW_card, hW_wt, hW_fail⟩
  have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  have hr_div_nonneg : 0 ≤ r / (L : ℝ) + C_shift :=
    add_nonneg (div_nonneg hr (le_of_lt hL_pos)) hC
  refine ⟨ψ, W, hψ0, hW_card, hW_wt, ?_⟩
  intro e e' x0 h_diff h_disc
  apply hW_fail e e' (fun axis => x0 axis / (L : ℝ))
  · intro q hq_ne
    have h_in_pert := h_diff q hq_ne
    have h_in_coarse := perturb_point_mem_coarse_ball x0 (code.posQ q) (cQ q) L hL hr hC (hcQ q) h_in_pert
    exact ball3D_mono _ hr_div_nonneg h_rad h_in_coarse
  · exact h_disc

/-- Unscaling `HasBallParityWitnessFamily` across `bdlPerturbStep` (dual sector). -/
lemma hasBallParityWitnessFamily_dual_bdlPerturbStep {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L : ℕ) (hL : 0 < L)
    (cQ : Q → Point3D) (cZ : M_Z → Point3D) (cX : M_X → Point3D)
    {C_shift : ℝ} (hC : 0 ≤ C_shift)
    (hcQ : ∀ q, distSq3D (cQ q) (fun _ => 0) ≤ (C_shift * (L : ℝ)) ^ 2)
    {L_Z L_X : Q → ZMod 2} {r r_coarse : ℝ} {w N : ℕ}
    (hr : 0 ≤ r) (h_rad : r / (L : ℝ) + C_shift ≤ r_coarse)
    (h_wit : HasBallParityWitnessFamily (dualCode code) L_X L_Z r_coarse w N) :
    HasBallParityWitnessFamily (dualCode (bdlPerturbStep code L cQ cZ cX)) L_X L_Z r w N :=
  hasBallParityWitnessFamily_bdlPerturbStep (dualCode code) L hL cQ cX cZ hC hcQ hr h_rad h_wit

/-! ## 2. Local Support Propagation Under Cylinder Projection -/

/-- Pointwise locality of `rxCleanedCoarseProj`: for any coarse qubit `q0 : Q`,
    `rxCleanedCoarseProj pcode M h q0` depends only on `h` on star `q0` (`cQ1OwnerQ = q0`)
    and on cylinders `x` incident to `q0` (`pcode.checkX x q0 ≠ 0`). -/
theorem rxCleanedCoarseProj_eq_of_local_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ)
    (h h' : BDLStepXQ pcode M → ZMod 2) (q0 : Q)
    (hh_star : ∀ qQ : BDLCQ1 pcode M, cQ1OwnerQ pcode M qQ = q0 →
      h (Sum.inr qQ) = h' (Sum.inr qQ))
    (hh_cyl : ∀ x : M_X, pcode.checkX x q0 ≠ 0 →
      ∀ qX : BDLCX1 pcode M, cX1OwnerX pcode M qX = x →
        h (Sum.inl qX) = h' (Sum.inl qX)) :
    rxCleanedCoarseProj pcode M h q0 = rxCleanedCoarseProj pcode M h' q0 := by
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let S := syndrome D_1 h
  let S' := syndrome D_1 h'
  have hS_cyl : ∀ x : M_X, pcode.checkX x q0 ≠ 0 →
      restrictCX2 pcode M x S = restrictCX2 pcode M x S' := by
    intro x hx; ext mZ; dsimp [restrictCX2, restrictStepXMZ]; split_ifs with hmZ
    · rcases mZ with mZX | (mZQ | mZZ)
      · dsimp [stepXMZOwnerTanner, inVX] at hmZ
        rw [Finset.mem_singleton, Sum.inl.injEq] at hmZ
        dsimp [S, S', syndrome, f2Syndrome, D_1, dualCode, dualF2ChainComplex, bdlCylinderStepX]
        apply Finset.sum_congr rfl; intro q _; rcases q with qX | qQ
        · by_cases h_own : cX1OwnerX pcode M qX = x
          · rw [hh_cyl x hx qX h_own]
          · dsimp [bdlStepXCheckZ]
            rw [bdlDeltaX1_eq_zero_of_owner_ne pcode M mZX qX (by rw [hmZ]; exact h_own),
                zero_mul, zero_mul]
        · dsimp [bdlStepXCheckZ]; rw [zero_mul, zero_mul]
      · dsimp [stepXMZOwnerTanner, inVQ, inVX] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
      · dsimp [stepXMZOwnerTanner, inVZ, inVX] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
    · rfl
  have hfX_eq : ∀ x : M_X, pcode.checkX x q0 ≠ 0 →
      cleanCylinderX pcode M S x = cleanCylinderX pcode M S' x :=
    fun x hx => cleanCylinderX_congr pcode M S S' x (hS_cyl x hx)
  have hS_star : restrictCQ2 pcode M q0 S = restrictCQ2 pcode M q0 S' := by
    ext mZ; dsimp [restrictCQ2, restrictStepXMZ]; split_ifs with hmZ
    · rcases mZ with mZX | (mZQ | mZZ)
      · dsimp [stepXMZOwnerTanner, inVX, inVQ] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
      · dsimp [stepXMZOwnerTanner, inVQ] at hmZ
        rw [Finset.mem_singleton, Sum.inr.injEq, Sum.inl.injEq] at hmZ
        dsimp [S, S', syndrome, f2Syndrome, D_1, dualCode, dualF2ChainComplex, bdlCylinderStepX]
        apply Finset.sum_congr rfl; intro q _; rcases q with qX | qQ
        · by_cases hx : pcode.checkX (cX1OwnerX pcode M qX) q0 = 0
          · dsimp [bdlStepXCheckZ]
            rw [bdlGXQ1_eq_zero_of_checkX_eq_zero pcode M mZQ qX (by rw [hmZ]; exact hx),
                zero_mul, zero_mul]
          · rw [hh_cyl (cX1OwnerX pcode M qX) hx qX rfl]
        · by_cases h_own : cQ1OwnerQ pcode M qQ = q0
          · rw [hh_star qQ h_own]
          · dsimp [bdlStepXCheckZ]
            rw [bdlDeltaQ1_eq_zero_of_owner_ne pcode M mZQ qQ (by rw [hmZ]; exact h_own),
                zero_mul, zero_mul]
      · dsimp [stepXMZOwnerTanner, inVZ, inVQ] at hmZ; rw [Finset.mem_singleton] at hmZ; nomatch hmZ
    · rfl
  have hS1_star :
      restrictCQ2 pcode M q0 (S + syndrome D_1 (cleanStage1X pcode M S)) =
      restrictCQ2 pcode M q0 (S' + syndrome D_1 (cleanStage1X pcode M S')) := by
    have h_fX : restrictCQ2 pcode M q0 (syndrome D_1 (cleanStage1X pcode M S)) =
        restrictCQ2 pcode M q0 (syndrome D_1 (cleanStage1X pcode M S')) := by
      dsimp [cleanStage1X]; rw [map_sum (syndrome D_1), map_sum (syndrome D_1)]
      ext mZ; dsimp [restrictCQ2, restrictStepXMZ]; split_ifs with hmZ
      · rw [Finset.sum_apply, Finset.sum_apply]
        apply Finset.sum_congr rfl; intro x _
        by_cases hx : pcode.checkX x q0 = 0
        · have h1 := congr_fun (restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero pcode M x q0 hx
            (cleanCylinderX pcode M S x) (cleanCylinderX_support pcode M S x)) mZ
          have h2 := congr_fun (restrictCQ2_syndrome_eq_zero_of_support_cyl_checkX_eq_zero pcode M x q0 hx
            (cleanCylinderX pcode M S' x) (cleanCylinderX_support pcode M S' x)) mZ
          dsimp [restrictCQ2, restrictStepXMZ] at h1 h2; rw [if_pos hmZ] at h1 h2
          exact h1.trans h2.symm
        · rw [hfX_eq x hx]
      · rfl
    rw [restrictCQ2_add, restrictCQ2_add, hS_star, h_fX]
  have hfQ_eq :
      cleanStarQ pcode M (S + syndrome D_1 (cleanStage1X pcode M S)) q0 =
      cleanStarQ pcode M (S' + syndrome D_1 (cleanStage1X pcode M S')) q0 :=
    cleanStarQ_congr pcode M _ _ q0 hS1_star
  dsimp [rxCleanedCoarseProj]
  rw [projCylinderLXLayer_zero_eq, projCylinderLXLayer_zero_eq]
  dsimp [projCylinderLX, dualPairing]
  apply Finset.sum_congr rfl; intro q _
  by_cases hlz : liftCylinderLZ pcode M (singleQubit q0) q = 0
  · rw [hlz, zero_mul, zero_mul]
  · have h_proj_nz : projCylinderLX pcode M (singleQubit q) q0 ≠ 0 := by
      rw [show projCylinderLX pcode M (singleQubit q) q0 =
        liftCylinderLZ pcode M (singleQubit q0) q from dualPairing_singleQubit_right _ _]
      exact hlz
    have hq_eq : h q + cleanTwoStageRX pcode M S q = h' q + cleanTwoStageRX pcode M S' q := by
      rcases liftCylinderLZ_singleQubit_eq_one_imp pcode M q0 q h_proj_nz with ⟨rv, rfl, _, h_chk⟩ | rfl
      · have hx_rv : pcode.checkX (cX1OwnerX pcode M (Sum.inl (rv, 0))) q0 ≠ 0 := h_chk
        have hfX_rv : cleanStage1X pcode M S (Sum.inl (Sum.inl (rv, 0))) =
            cleanStage1X pcode M S' (Sum.inl (Sum.inl (rv, 0))) := by
          dsimp [cleanStage1X]; rw [Finset.sum_apply, Finset.sum_apply]
          apply Finset.sum_congr rfl; intro x _
          by_cases hx : x = cX1OwnerX pcode M (Sum.inl (rv, 0))
          · subst hx
            rw [hfX_eq _ hx_rv]
          · have h1 : cleanCylinderX pcode M S x (Sum.inl (Sum.inl (rv, 0))) = 0 := by
              by_contra h_nz
              obtain ⟨qX', h_eq, h_own⟩ := cleanCylinderX_support pcode M S x _ h_nz
              injection h_eq with h_eq; subst h_eq; exact hx h_own.symm
            have h2 : cleanCylinderX pcode M S' x (Sum.inl (Sum.inl (rv, 0))) = 0 := by
              by_contra h_nz
              obtain ⟨qX', h_eq, h_own⟩ := cleanCylinderX_support pcode M S' x _ h_nz
              injection h_eq with h_eq; subst h_eq; exact hx h_own.symm
            rw [h1, h2]
        dsimp [cleanTwoStageRX]
        rw [cleanStage2Q_inl_eq_zero, cleanStage2Q_inl_eq_zero, add_zero, add_zero,
            hh_cyl _ hx_rv (Sum.inl (rv, 0)) rfl, hfX_rv]
      · have hfX_inr : ∀ S_any : BDLStepXMZ pcode M → ZMod 2,
            cleanStage1X pcode M S_any (Sum.inr (Sum.inl q0, 0)) = 0 := by
          intro S_any; dsimp [cleanStage1X]; rw [Finset.sum_apply]
          apply Finset.sum_eq_zero; intro x _; by_contra h_nz
          obtain ⟨qX', h_eq, _⟩ := cleanCylinderX_support pcode M S_any x _ h_nz
          nomatch h_eq
        have hfQ_q0 : cleanStage2Q pcode M (S + syndrome D_1 (cleanStage1X pcode M S)) (Sum.inr (Sum.inl q0, 0)) =
            cleanStage2Q pcode M (S' + syndrome D_1 (cleanStage1X pcode M S')) (Sum.inr (Sum.inl q0, 0)) := by
          dsimp [cleanStage2Q]; rw [Finset.sum_apply, Finset.sum_apply]
          apply Finset.sum_congr rfl; intro q0' _
          by_cases hq0' : q0' = q0
          · subst hq0'; rw [hfQ_eq]
          · have h1 : cleanStarQ pcode M (S + syndrome D_1 (cleanStage1X pcode M S)) q0' (Sum.inr (Sum.inl q0, 0)) = 0 := by
              by_contra h_nz
              obtain ⟨qQ', h_eq, h_own⟩ := cleanStarQ_support pcode M _ q0' _ h_nz
              injection h_eq with h_eq; subst h_eq; exact hq0' h_own.symm
            have h2 : cleanStarQ pcode M (S' + syndrome D_1 (cleanStage1X pcode M S')) q0' (Sum.inr (Sum.inl q0, 0)) = 0 := by
              by_contra h_nz
              obtain ⟨qQ', h_eq, h_own⟩ := cleanStarQ_support pcode M _ q0' _ h_nz
              injection h_eq with h_eq; subst h_eq; exact hq0' h_own.symm
            rw [h1, h2]
        dsimp [cleanTwoStageRX]
        rw [hfX_inr S, hfX_inr S', zero_add, zero_add,
            hh_star (Sum.inl q0, 0) rfl, hfQ_q0]
    change liftCylinderLZ pcode M (singleQubit q0) q * (h q + cleanTwoStageRX pcode M S q) =
      liftCylinderLZ pcode M (singleQubit q0) q * (h' q + cleanTwoStageRX pcode M S' q)
    rw [hq_eq]

/-- **Local Support Propagation for `rxCleanedCoarseProj` (`rxCleanedCoarseProj_diff_in_ball`,
    Part I, Proposition 5.3 (`prop:cluster-decoder-witness`)):**
    If `h, h' : BDLStepXQ pcode M → ZMod 2` agree outside `ball3D x0 r`, then
    `rxCleanedCoarseProj pcode M h` and `rxCleanedCoarseProj pcode M h'` agree outside
    `ball3D x0 (r + 3 * D_edge)`. -/
theorem rxCleanedCoarseProj_diff_in_ball {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (x0 : Point3D) {r : ℝ} (hr : 0 ≤ r)
    (h h' : BDLStepXQ pcode M → ZMod 2)
    (h_diff : ∀ q : BDLStepXQ pcode M, h q ≠ h' q →
      (bdlCylinderStepX pcode M).posQ q ∈ ball3D x0 r) :
    ∀ q0 : Q, rxCleanedCoarseProj pcode M h q0 ≠ rxCleanedCoarseProj pcode M h' q0 →
      pcode.posQ q0 ∈ ball3D x0 (r + 3 * D_edge) := by
  have hD0 := hD.1
  intro q0 h_ne
  by_contra h_not_in
  apply h_ne
  apply rxCleanedCoarseProj_eq_of_local_eq pcode M h h' q0
  · intro ⟨v0, b⟩ h_own
    by_contra hq_ne
    have hv0_in : xq0Pos pcode M v0 ∈ ball3D x0 r := h_diff (Sum.inr (v0, b)) hq_ne
    have hq0_in := ownerQ_mem_ball3D_of_xq0Pos pcode M hD x0 hr v0 hv0_in
    dsimp [cQ1OwnerQ] at h_own
    rw [h_own] at hq0_in
    exact h_not_in (ball3D_mono x0 (by linarith) (by linarith) hq0_in)
  · intro x hx qX hqX
    by_contra hqX_ne
    have hqX_in := h_diff (Sum.inl qX) hqX_ne
    have hx_in := ownerX_mem_ball3D_of_bdlCylinderStepX_posQ_inl pcode M hD x0 hr qX hqX_in
    have h_own_eq : qXOwnerX pcode M qX = cX1OwnerX pcode M qX := by
      rcases qX with ⟨rv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, b⟩⟩ <;> rfl
    rw [h_own_eq, hqX] at hx_in
    have hq0_in := ball3D_step_of_distSq3D_le x0 (pcode.posX x) (pcode.posQ q0)
      (by linarith) hD0 hx_in (hD.2.2 x q0 hx)
    have h_eq : r + 2 * D_edge + D_edge = r + 3 * D_edge := by ring
    rw [h_eq] at hq0_in
    exact h_not_in hq0_in

/-- **Local Support Propagation for `projCylinderLZ` (`projCylinderLZ_diff_in_ball`,
    Part I, Proposition 5.3 (`prop:cluster-decoder-witness`)):**
    If `e, e' : BDLStepXQ pcode M → ZMod 2` agree outside `ball3D x0 r`, then
    `projCylinderLZ pcode M e` and `projCylinderLZ pcode M e'` agree outside
    `ball3D x0 (r + D_edge)`. -/
theorem projCylinderLZ_diff_in_ball {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (x0 : Point3D) {r : ℝ} (hr : 0 ≤ r)
    (e e' : BDLStepXQ pcode M → ZMod 2)
    (h_diff : ∀ q : BDLStepXQ pcode M, e q ≠ e' q →
      (bdlCylinderStepX pcode M).posQ q ∈ ball3D x0 r) :
    ∀ q0 : Q, projCylinderLZ pcode M e q0 ≠ projCylinderLZ pcode M e' q0 →
      pcode.posQ q0 ∈ ball3D x0 (r + D_edge) := by
  intro q0 h_ne
  dsimp [projCylinderLZ, dualPairing] at h_ne
  have h_ex : ∃ q : BDLStepXQ pcode M,
      e q * liftCylinderLX pcode M (singleQubit q0) q ≠
      e' q * liftCylinderLX pcode M (singleQubit q0) q := by
    by_contra h_all; push_neg at h_all
    exact h_ne (Finset.sum_congr rfl (fun q _ => h_all q))
  rcases h_ex with ⟨q, hq⟩
  have he_ne : e q ≠ e' q := fun h_eq => hq (by rw [h_eq])
  have hlx_ne : liftCylinderLX pcode M (singleQubit q0) q ≠ 0 :=
    fun h0 => hq (by rw [h0, mul_zero, mul_zero])
  rcases q with qX | ⟨v0, b⟩
  · exact False.elim (hlx_ne rfl)
  · have hq0_own : xq0OwnerQ pcode M v0 = q0 := by
      dsimp [liftCylinderLX, singleQubit] at hlx_ne
      by_cases hq_eq : xq0OwnerQ pcode M v0 = q0
      · exact hq_eq
      · rw [if_neg hq_eq] at hlx_ne
        exact False.elim (hlx_ne rfl)
    have hv0_in : xq0Pos pcode M v0 ∈ ball3D x0 r := h_diff (Sum.inr (v0, b)) he_ne
    have hq0_in := ownerQ_mem_ball3D_of_xq0Pos pcode M hD x0 hr v0 hv0_in
    rwa [hq0_own] at hq0_in

/-! ## 3. Primal and Dual Cylinder Step Lifting of Ball Witness Families -/

/-- Primal single-step reduction of `HasBallParityWitnessFamily` across `bdlCylinderStepX pcode M`. -/
theorem hasBallParityWitnessFamily_cylinder_primal {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (L_Z L_X : Q → ZMod 2)
    (F w N_0 : ℕ)
    (hF : ∀ x0 : M_X, (Finset.univ.filter (fun mX : BDLStepXMX pcode M => stepXMXOwnerX pcode M mX = x0)).card ≤ F)
    {r : ℝ} (hr : 0 ≤ r)
    (h_wit : HasBallParityWitnessFamily pcode L_Z L_X (r + D_edge) w N_0) :
    HasBallParityWitnessFamily (bdlCylinderStepX pcode M)
      (liftCylinderLZ pcode M L_Z) (liftCylinderLX pcode M L_X)
      r w (N_0 * F ^ w) := by
  rcases h_wit with ⟨ψ_0, W_0, hψ0, hW0_card, hW0_wt, hW0_fail⟩
  let ψ_1 := rzCoarseParityRule pcode M ψ_0
  obtain ⟨W_1, hW1_card, hW1_wt, hW1_lift⟩ :=
    liftWitnessFamily_of_owner (stepXMXOwnerX pcode M) F w N_0 hF W_0 hW0_card hW0_wt
  refine ⟨ψ_1, W_1, rzCoarseParityRule_zero pcode M ψ_0 hψ0, hW1_card, hW1_wt, ?_⟩
  intro e e' x0 h_diff h_disc
  have h_disc_e := rzCoarseParityRule_discrepancy_eq pcode M ψ_0 L_X e
  have h_disc_e' := rzCoarseParityRule_discrepancy_eq pcode M ψ_0 L_X e'
  have h_coarse_disc :
      ψ_0 (syndrome pcode (projCylinderLZ pcode M e')) + dualPairing L_X (projCylinderLZ pcode M e') ≠
      ψ_0 (syndrome pcode (projCylinderLZ pcode M e)) + dualPairing L_X (projCylinderLZ pcode M e) := by
    intro h_eq
    exact h_disc (h_disc_e'.trans (h_eq.trans h_disc_e.symm))
  have h_coarse_diff : ∀ q0 : Q,
      projCylinderLZ pcode M e q0 ≠ projCylinderLZ pcode M e' q0 →
      pcode.posQ q0 ∈ ball3D x0 (r + D_edge) :=
    projCylinderLZ_diff_in_ball pcode M hD x0 hr e e' h_diff
  obtain ⟨c0, hc0_mem, hc0_or⟩ :=
    hW0_fail (projCylinderLZ pcode M e) (projCylinderLZ pcode M e') x0 h_coarse_diff h_coarse_disc
  rcases hc0_or with hc0_e | hc0_e'
  · have h_fib : ∀ x0 : M_X, c0 x0 ≠ 0 →
        ∃ mX : BDLStepXMX pcode M, stepXMXOwnerX pcode M mX = x0 ∧
          syndrome (bdlCylinderStepX pcode M) e mX ≠ 0 := by
      intro x0 hx0
      have h_syn_nz : coarseSyndromeStepXMX pcode M (syndrome (bdlCylinderStepX pcode M) e) x0 ≠ 0 := by
        rw [coarseSyndromeStepXMX_syndrome_eq]
        exact hc0_e x0 hx0
      exact exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero pcode M _ x0 h_syn_nz
    obtain ⟨c1, hc1_mem, hc1_act⟩ := hW1_lift (syndrome (bdlCylinderStepX pcode M) e) c0 hc0_mem h_fib
    exact ⟨c1, hc1_mem, Or.inl hc1_act⟩
  · have h_fib : ∀ x0 : M_X, c0 x0 ≠ 0 →
        ∃ mX : BDLStepXMX pcode M, stepXMXOwnerX pcode M mX = x0 ∧
          syndrome (bdlCylinderStepX pcode M) e' mX ≠ 0 := by
      intro x0 hx0
      have h_syn_nz : coarseSyndromeStepXMX pcode M (syndrome (bdlCylinderStepX pcode M) e') x0 ≠ 0 := by
        rw [coarseSyndromeStepXMX_syndrome_eq]
        exact hc0_e' x0 hx0
      exact exists_active_in_fiber_of_coarseSyndromeStepXMX_ne_zero pcode M _ x0 h_syn_nz
    obtain ⟨c1, hc1_mem, hc1_act⟩ := hW1_lift (syndrome (bdlCylinderStepX pcode M) e') c0 hc0_mem h_fib
    exact ⟨c1, hc1_mem, Or.inr hc1_act⟩

/-- Dual single-step reduction of `HasBallParityWitnessFamily` across `bdlCylinderStepX pcode M`. -/
theorem hasBallParityWitnessFamily_cylinder_dual {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) {D_edge : ℝ}
    (hD : HasCoarseEdgeBound pcode D_edge)
    (hov : ∀ (x' : M_X) (z' : M_Z),
      (Finset.univ.filter (fun q' : Q => pcode.checkX x' q' ≠ 0 ∧ pcode.checkZ z' q' ≠ 0)).card ≤ 2)
    (hq_z : ∀ q0 : Q, ∃ z0 : M_Z, pcode.checkZ z0 q0 ≠ 0)
    (h_conn : HasConnectedXLinks pcode)
    (L_Z L_X : Q → ZMod 2)
    (F w N_0 : ℕ)
    (h_pool : ∀ K_Z : Finset M_Z, (fineTwoHopPool pcode M K_Z).card ≤ 41 * F * K_Z.card)
    {r : ℝ} (hr : 0 ≤ r)
    (h_wit : HasBallParityWitnessFamily (dualCode pcode) L_X L_Z (r + 3 * D_edge) w N_0) :
    HasBallParityWitnessFamily (dualCode (bdlCylinderStepX pcode M))
      (liftCylinderLX pcode M L_X) (liftCylinderLZ pcode M L_Z)
      r ((27 * w + 15) / 16) (N_0 * (2 ^ (41 * F)) ^ w) := by
  rcases h_wit with ⟨ψ_0, W_0, hψ0, hW0_card, hW0_wt, hW0_fail⟩
  let D_0 := dualCode pcode
  let D_1 := dualCode (bdlCylinderStepX pcode M)
  let ψ_1 := rxCleanedParityRule pcode M ψ_0 L_Z
  obtain ⟨W_1, hW1_card, hW1_wt, hW1_lift⟩ :=
    liftWitnessFamily_rx_twoHop_step pcode M F w N_0 hov hq_z h_conn h_pool W_0 hW0_card hW0_wt
  refine ⟨ψ_1, W_1, rxCleanedParityRule_zero pcode M ψ_0 hψ0 L_Z, hW1_card, hW1_wt, ?_⟩
  intro h h' x0 h_diff h_disc
  have h_disc_h := rxCleanedParityRule_discrepancy_eq pcode M hov hq_z h_conn ψ_0 L_Z h
  have h_disc_h' := rxCleanedParityRule_discrepancy_eq pcode M hov hq_z h_conn ψ_0 L_Z h'
  have h_coarse_disc :
      ψ_0 (syndrome D_0 (rxCleanedCoarseProj pcode M h')) + dualPairing L_Z (rxCleanedCoarseProj pcode M h') ≠
      ψ_0 (syndrome D_0 (rxCleanedCoarseProj pcode M h)) + dualPairing L_Z (rxCleanedCoarseProj pcode M h) := by
    intro h_eq
    exact h_disc (h_disc_h'.trans (h_eq.trans h_disc_h.symm))
  have h_coarse_diff : ∀ q0 : Q,
      rxCleanedCoarseProj pcode M h q0 ≠ rxCleanedCoarseProj pcode M h' q0 →
      pcode.posQ q0 ∈ ball3D x0 (r + 3 * D_edge) :=
    rxCleanedCoarseProj_diff_in_ball pcode M hD x0 hr h h' h_diff
  obtain ⟨c0, hc0_mem, hc0_or⟩ :=
    hW0_fail (rxCleanedCoarseProj pcode M h) (rxCleanedCoarseProj pcode M h') x0 h_coarse_diff h_coarse_disc
  rcases hc0_or with hc0_h | hc0_h'
  · have hc0_rx : ∀ z0 : M_Z, c0 z0 ≠ 0 →
        rxCleanedCoarseSyndrome pcode M (syndrome D_1 h) z0 ≠ 0 := by
      intro z0 hz0
      rw [← (rxCleanedCoarseProj_syndrome_eq pcode M hov hq_z h_conn h).1]
      exact hc0_h z0 hz0
    obtain ⟨c1, hc1_mem, hc1_act⟩ := hW1_lift h c0 hc0_mem hc0_rx
    exact ⟨c1, hc1_mem, Or.inl hc1_act⟩
  · have hc0_rx : ∀ z0 : M_Z, c0 z0 ≠ 0 →
        rxCleanedCoarseSyndrome pcode M (syndrome D_1 h') z0 ≠ 0 := by
      intro z0 hz0
      rw [← (rxCleanedCoarseProj_syndrome_eq pcode M hov hq_z h_conn h').1]
      exact hc0_h' z0 hz0
    obtain ⟨c1, hc1_mem, hc1_act⟩ := hW1_lift h' c0 hc0_mem hc0_rx
    exact ⟨c1, hc1_mem, Or.inr hc1_act⟩

end BDLDecoder

/-! ## 4. Local Homological Logical Immunity and Parity Invariance (Part I, Proposition 5.3 (`prop:cluster-decoder-witness`)) -/

/-- Euclidean-ball $\mathbb{F}_2$ linear TQO-2 (cone acyclicity) predicate on a 3D CSS code. -/
def SatisfiesEucF2LinearTQO {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (L_star C : ℝ) : Prop :=
  ∀ (x0 : Point3D) (r : ℝ), 1 ≤ r → r ≤ L_star →
    globalStabilizersInBall code x0 r ⊆ locallyGeneratedInBall code x0 (C * r)

/-- **Local Homological Logical Immunity (Part I, Proposition 5.3 (`prop:cluster-decoder-witness`))**:
    Under `SatisfiesEucF2LinearTQO code L_star C`, any cleaned residual 1-chain $g$ supported in
    `ball3D x0 r` ($1 \le r \le L^*$) with zero syndrome is locally generated by $Z$-checks inside
    `ball3D x0 (C * r)`. -/
theorem local_immunity_stabilizer_from_zero_syndrome
    {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) {L_star C : ℝ}
    (h_tqo2 : SatisfiesEucF2LinearTQO code L_star C)
    (x0 : Point3D) {r : ℝ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star)
    (g : Q → ZMod 2) (hg_syn : syndrome code g = 0)
    (hg_supp : supp1 code g ⊆ ball3D x0 r) :
    g ∈ locallyGeneratedInBall code x0 (C * r) :=
  h_tqo2 x0 r hr1 hrL ⟨hg_syn, hg_supp⟩

/-- **Local Homological Immunity for Syndrome-Matched Chains (Part I, Proposition 5.3 (`prop:cluster-decoder-witness`))**:
    If an error chain $e$ and its local recovery chain $e'$ agree outside `ball3D x0 r` ($1 \le r \le L^*$)
    and have identical syndromes `syndrome code e' = syndrome code e`, then the residual cycle
    $g = e' + e$ belongs to `locallyGeneratedInBall code x0 (C * r)`. -/
theorem local_immunity_difference_stabilizer_of_same_syndrome
    {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) {L_star C : ℝ}
    (h_tqo2 : SatisfiesEucF2LinearTQO code L_star C)
    (x0 : Point3D) {r : ℝ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star)
    (e e' : Q → ZMod 2)
    (h_diff : ∀ q : Q, e q ≠ e' q → code.posQ q ∈ ball3D x0 r)
    (h_syn : syndrome code e' = syndrome code e) :
    (e' + e) ∈ locallyGeneratedInBall code x0 (C * r) := by
  apply local_immunity_stabilizer_from_zero_syndrome code h_tqo2 x0 hr1 hrL (e' + e)
  · rw [map_add, h_syn]
    ext m
    exact zmod2_add_self (syndrome code e m)
  · intro p ⟨q, hq_ne, hp⟩
    subst hp
    apply h_diff q
    intro h_eq
    apply hq_ne
    dsimp
    rw [h_eq]
    exact zmod2_add_self (e' q)

/-- **Local Homological Logical Parity Invariance (Part I, Proposition 5.3 (`prop:cluster-decoder-witness`), Equation (43) (`eq:local-pairing-invariance`))**:
    Whenever $e$ and $e'$ agree outside `ball3D x0 r` and share the same syndrome on a code
    satisfying `SatisfiesEucF2LinearTQO code L_star C`, their symplectic pairings with any dual cycle
    $L_X$ (`syndrome (dualCode code) L_X = 0`) are identical. -/
theorem local_immunity_logical_pairing_invariant
    {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) {L_star C : ℝ}
    (h_tqo2 : SatisfiesEucF2LinearTQO code L_star C)
    (L_X : Q → ZMod 2) (h_syn_X : syndrome (dualCode code) L_X = 0)
    (x0 : Point3D) {r : ℝ} (hr1 : 1 ≤ r) (hrL : r ≤ L_star)
    (e e' : Q → ZMod 2)
    (h_diff : ∀ q : Q, e q ≠ e' q → code.posQ q ∈ ball3D x0 r)
    (h_syn : syndrome code e' = syndrome code e) :
    dualPairing L_X e' = dualPairing L_X e := by
  obtain ⟨c2, _, hc2_gen⟩ :=
    local_immunity_difference_stabilizer_of_same_syndrome code h_tqo2 x0 hr1 hrL e e' h_diff h_syn
  have h_pair_zero : dualPairing L_X (e' + e) = 0 := by
    rw [← hc2_gen]
    exact dualPairing_checkGen_zero code c2 L_X h_syn_X
  rw [dualPairing_add_right_zmod2] at h_pair_zero
  have h_alg : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact h_alg _ _ h_pair_zero

/-- **Geometric Series Multiscale Volume Ratio (Part I, Lemma 5.4 (`lem:percolating-cluster-bounds`), Equation (45) (`eq:linear-multiscale-volume`))**:
    $\frac{2}{1 - 16/27} = \frac{54}{11}$. -/
theorem geometric_series_volume_ratio :
    (2 : ℝ) / (1 - 16 / 27) = 54 / 11 := by
  norm_num

/-- **Discrete Geometric Series Partial Sum Bound (`geometric_series_16_27_sum_le`,
    Part I, Lemma 5.4 (`lem:percolating-cluster-bounds`), Equation (45) (`eq:linear-multiscale-volume`))**:
    $11 \sum_{j=0}^n 16^j \cdot 27^{n-j} \le 27^{n+1}$. -/
theorem geometric_series_16_27_sum_le (n : ℕ) :
    11 * (∑ j ∈ Finset.range (n + 1), 16 ^ j * 27 ^ (n - j)) ≤ 27 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ']
    have h_split : (∑ k ∈ Finset.range (m + 1), 16 ^ (k + 1) * 27 ^ (m + 1 - (k + 1))) =
        16 * ∑ k ∈ Finset.range (m + 1), 16 ^ k * 27 ^ (m - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.succ_sub_succ_eq_sub, pow_succ']
      ring
    rw [h_split, pow_zero, Nat.sub_zero, one_mul, Nat.mul_add]
    have h16 := Nat.mul_le_mul_left 16 ih
    have h_alg : 16 * (11 * ∑ k ∈ Finset.range (m + 1), 16 ^ k * 27 ^ (m - k)) =
        11 * (16 * ∑ k ∈ Finset.range (m + 1), 16 ^ k * 27 ^ (m - k)) := by ring
    rw [h_alg] at h16
    have h_rhs : 16 * 27 ^ (m + 1) + 11 * 27 ^ (m + 1) = 27 ^ (m + 2) := by
      change 16 * 27 ^ (m + 1) + 11 * 27 ^ (m + 1) = 27 ^ (m + 1) * 27
      ring
    omega

end WeldedHierarchy
