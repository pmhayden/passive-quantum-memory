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

import Proofs.ConeAcyclicityRCA.CylinderCocycleLocalization

/-!
# Iterated Half-Step Stabilizer Transfer and Barycentric Simplex Ray Separation

Proves single-step and m-step affine collar recurrences (scaleDownRadius, scaleUpRadius, bdlHalfStep_iterated_globalStabilizers_step) transferring local stabilizer generation from coarse hierarchy levels up to fine welded levels. Establishes lower bounds on Euclidean distances between subdivided simplex rays (simplex_vec_comb_distSq3D_ge, triGridPos3D_ray_separation) and vanishing of hRadialShell outside small shells when the cylinder apex is far from the ball center.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.2 (`def:well-separated-base`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Part I, Section 3.3 (`subsec:scale-matched-rca`), Lemma 3.8 (`lem:clean-shell-subcylinder`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
-/

noncomputable section
open scoped Classical
open BigOperators
namespace WeldedHierarchy

/-! ## 1. Single-Step Primal and Dual `globalStabilizersInBall` Reductions -/

theorem bdlRandomStepX_globalStabilizers_step (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (x0 : Point3D) {r R_coarse : ℝ}
    (hr0 : 0 ≤ r) (hrR : r / (bdlLambda : ℝ) + 7003 ≤ R_coarse)
    (h_primal : globalStabilizersInBall B.code
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall B.code (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse)
    (h_dual : globalStabilizersInBall (dualCode B.code)
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall (dualCode B.code) (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse) :
    globalStabilizersInBall (bdlRandomStepX B).code x0 r ⊆
      locallyGeneratedInBall (bdlRandomStepX B).code x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) ∧
    globalStabilizersInBall (dualCode (bdlRandomStepX B).code) x0 r ⊆
      locallyGeneratedInBall (dualCode (bdlRandomStepX B).code) x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) := by
  have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
  have hlam_ne : (bdlLambda : ℝ) ≠ 0 := ne_of_gt hlam_pos
  have hR0 : 0 ≤ R_coarse := by
    have : 0 ≤ r / (bdlLambda : ℝ) := div_nonneg hr0 (le_of_lt hlam_pos)
    linarith
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  let c := bdlLLLPerturbation B
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  let D_edge : ℝ := 2001 * (bdlLambda : ℝ)
  have hD : HasCoarseEdgeBound pcode D_edge := by
    have hD_raw := hasCoarseEdgeBound_of_validLLLPerturbation B h_valid
    have h_eq : (2 * bdlAlpha + 1) * (bdlLambda : ℝ) = D_edge := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; ring
    rwa [h_eq] at hD_raw
  have hD0 : 0 ≤ D_edge := hD.1
  have hcQ : ∀ q, distSq3D (c.1 q) (fun _ => 0) ≤ (bdlAlpha * (bdlLambda : ℝ)) ^ 2 :=
    fun q => le_of_eq (h_valid.1 q)
  have hcZ : ∀ mZ, distSq3D (c.2.1 mZ) (fun _ => 0) ≤ (bdlAlpha * (bdlLambda : ℝ)) ^ 2 :=
    fun mZ => le_of_eq (h_valid.2.1 mZ)
  have hcX : ∀ mX, distSq3D (c.2.2 mX) (fun _ => 0) ≤ (bdlAlpha * (bdlLambda : ℝ)) ^ 2 :=
    fun mX => le_of_eq (h_valid.2.2.1 mX)
  have h_alpha_nonneg : (0 : ℝ) ≤ bdlAlpha := by dsimp [bdlAlpha, bdlAlphaNat]; norm_num
  refine ⟨?_, ?_⟩
  · have h_rad_p : (r + D_edge) / (bdlLambda : ℝ) + bdlAlpha ≤ r / (bdlLambda : ℝ) + 7003 := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; field_simp [hlam_ne]; linarith
    have h_p_coarse_sub : globalStabilizersInBall B.code
        (fun axis => x0 axis / (bdlLambda : ℝ)) ((r + D_edge) / (bdlLambda : ℝ) + bdlAlpha) ⊆
        locallyGeneratedInBall B.code (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse := by
      intro g ⟨hg_syn, hg_supp⟩
      apply h_primal
      refine ⟨hg_syn, Set.Subset.trans hg_supp (ball3D_mono _ ?_ h_rad_p)⟩
      have : 0 ≤ (r + D_edge) / (bdlLambda : ℝ) := div_nonneg (by linarith) (le_of_lt hlam_pos)
      linarith
    have h_p_perturb := bdlPerturbStep_globalStabilizers_step B.code bdlLambda bdlLambda_pos
      c.1 c.2.1 c.2.2 h_alpha_nonneg hcQ hcZ x0 (r := r + D_edge) (R_coarse := R_coarse)
      (by linarith) hR0 h_p_coarse_sub
    apply bdlCylinderStepX_primal_globalStabilizers_step pcode bdlSubdivPred hD
      h_inv.1.2 h_inv.2.2.2.2.1 h_inv.2.2.2.1.2 x0
      (r := r) (R_coarse := (bdlLambda : ℝ) * (R_coarse + bdlAlpha))
      (R_fine := (bdlLambda : ℝ) * (R_coarse + 13006))
      hr0 (by positivity)
    · dsimp [D_edge, bdlAlpha, bdlAlphaNat]
      have : r ≤ (R_coarse - 7003) * (bdlLambda : ℝ) :=
        (div_le_iff₀ hlam_pos).mp (show r / (bdlLambda : ℝ) ≤ R_coarse - 7003 by linarith)
      nlinarith
    · dsimp [D_edge, bdlAlpha, bdlAlphaNat]; linarith
    · exact h_p_perturb
  · have h_rad_d : (r + 3 * D_edge) / (bdlLambda : ℝ) + bdlAlpha = r / (bdlLambda : ℝ) + 7003 := by
      dsimp [D_edge, bdlAlpha, bdlAlphaNat]; field_simp [hlam_ne]; ring
    have h_d_coarse_sub : globalStabilizersInBall (dualCode B.code)
        (fun axis => x0 axis / (bdlLambda : ℝ)) ((r + 3 * D_edge) / (bdlLambda : ℝ) + bdlAlpha) ⊆
        locallyGeneratedInBall (dualCode B.code) (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse := by
      rw [h_rad_d]; exact h_dual
    have h_d_perturb : globalStabilizersInBall (dualCode pcode) x0 (r + 3 * D_edge) ⊆
        locallyGeneratedInBall (dualCode pcode) x0 ((bdlLambda : ℝ) * (R_coarse + bdlAlpha)) :=
      bdlPerturbStep_globalStabilizers_step (dualCode B.code) bdlLambda bdlLambda_pos
        c.1 c.2.2 c.2.1 h_alpha_nonneg hcQ hcX x0 (r := r + 3 * D_edge) (R_coarse := R_coarse)
        (by linarith) hR0 h_d_coarse_sub
    have h_step_d := bdlCylinderStepX_dual_globalStabilizers_step pcode bdlSubdivPred hD
      h_inv.1.2 h_inv.2.2.2.2.1 h_inv.2.2.2.1.2 x0
      (r := r) (R_coarse := (bdlLambda : ℝ) * (R_coarse + bdlAlpha)) hr0
      (by
        dsimp [D_edge, bdlAlpha, bdlAlphaNat]
        have : r ≤ (R_coarse - 7003) * (bdlLambda : ℝ) :=
          (div_le_iff₀ hlam_pos).mp (show r / (bdlLambda : ℝ) ≤ R_coarse - 7003 by linarith)
        nlinarith)
      h_d_perturb
    intro h hh
    obtain ⟨d2, hd2_supp, hd2_gen⟩ := h_step_d hh
    refine ⟨d2, Set.Subset.trans hd2_supp (ball3D_mono x0 ?_ ?_), hd2_gen⟩
    · positivity
    · dsimp [D_edge, bdlAlpha, bdlAlphaNat]; linarith

/-! ## 2. Iterated Rescaled Ball Radii (`scaleDownRadius`, `scaleUpRadius`) -/

theorem bdlRandomStepZ_globalStabilizers_step (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (x0 : Point3D) {r R_coarse : ℝ}
    (hr0 : 0 ≤ r) (hrR : r / (bdlLambda : ℝ) + 7003 ≤ R_coarse)
    (h_primal : globalStabilizersInBall B.code
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall B.code (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse)
    (h_dual : globalStabilizersInBall (dualCode B.code)
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall (dualCode B.code) (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse) :
    globalStabilizersInBall (bdlRandomStepZ B).code x0 r ⊆
      locallyGeneratedInBall (bdlRandomStepZ B).code x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) ∧
    globalStabilizersInBall (dualCode (bdlRandomStepZ B).code) x0 r ⊆
      locallyGeneratedInBall (dualCode (bdlRandomStepZ B).code) x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) := by
  have h_dual_step := bdlRandomStepX_globalStabilizers_step (dualBundled B)
    (hasBDLConeInvariants_dualBundled B h_inv) x0 hr0 hrR h_dual h_primal
  exact ⟨h_dual_step.2, h_dual_step.1⟩

theorem bdlHalfStep_globalStabilizers_step (n : ℕ)
    (x0 : Point3D) {r R_coarse : ℝ}
    (hr0 : 0 ≤ r) (hrR : r / (bdlLambda : ℝ) + 7003 ≤ R_coarse)
    (h_primal : globalStabilizersInBall (bdlHalfStep n).code
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall (bdlHalfStep n).code (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse)
    (h_dual : globalStabilizersInBall (dualCode (bdlHalfStep n).code)
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall (dualCode (bdlHalfStep n).code) (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse) :
    globalStabilizersInBall (bdlHalfStep (n + 1)).code x0 r ⊆
      locallyGeneratedInBall (bdlHalfStep (n + 1)).code x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) ∧
    globalStabilizersInBall (dualCode (bdlHalfStep (n + 1)).code) x0 r ⊆
      locallyGeneratedInBall (dualCode (bdlHalfStep (n + 1)).code) x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) := by
  by_cases h_even : n % 2 = 0
  · have h_step : bdlHalfStep (n + 1) = bdlRandomStepX (bdlHalfStep n) := if_pos h_even
    rw [h_step]
    exact bdlRandomStepX_globalStabilizers_step (bdlHalfStep n)
      (hasBDLConeInvariants_bdlHalfStep n) x0 hr0 hrR h_primal h_dual
  · have h_step : bdlHalfStep (n + 1) = bdlRandomStepZ (bdlHalfStep n) := if_neg h_even
    rw [h_step]
    exact bdlRandomStepZ_globalStabilizers_step (bdlHalfStep n)
      (hasBDLConeInvariants_bdlHalfStep n) x0 hr0 hrR h_primal h_dual

def scaleDownCenter : ℕ → Point3D → Point3D
  | 0, x0 => x0
  | m + 1, x0 => scaleDownCenter m (fun axis => x0 axis / (bdlLambda : ℝ))

def scaleDownRadius : ℕ → ℝ → ℝ
  | 0, r => r
  | m + 1, r => scaleDownRadius m (r / (bdlLambda : ℝ) + 7003)

def scaleUpRadius : ℕ → ℝ → ℝ
  | 0, R => R
  | m + 1, R => (bdlLambda : ℝ) * (scaleUpRadius m R + 13006)

lemma scaleDownRadius_nonneg (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ scaleDownRadius m r := by
  induction m generalizing r with
  | zero => exact hr
  | succ m ih =>
    apply ih
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
    have : 0 ≤ r / (bdlLambda : ℝ) := div_nonneg hr (le_of_lt hlam_pos)
    linarith

lemma scaleDownRadius_le_scaleUpRadius (m : ℕ) {r R : ℝ}
    (hr : 0 ≤ r) (h_le : scaleDownRadius m r ≤ R) :
    r ≤ scaleUpRadius m R := by
  induction m generalizing r with
  | zero => exact h_le
  | succ m ih =>
    dsimp [scaleDownRadius] at h_le
    dsimp [scaleUpRadius]
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
    have hr' : 0 ≤ r / (bdlLambda : ℝ) + 7003 := by
      have : 0 ≤ r / (bdlLambda : ℝ) := div_nonneg hr (le_of_lt hlam_pos)
      linarith
    have h_ih : r / (bdlLambda : ℝ) + 7003 ≤ scaleUpRadius m R := ih hr' h_le
    have h_div : r ≤ (scaleUpRadius m R - 7003) * (bdlLambda : ℝ) :=
      (div_le_iff₀ hlam_pos).mp (by linarith)
    nlinarith

lemma scaleDownRadius_comm (m : ℕ) (r : ℝ) :
    scaleDownRadius m (r / (bdlLambda : ℝ) + 7003) =
      (scaleDownRadius m r) / (bdlLambda : ℝ) + 7003 := by
  induction m generalizing r with
  | zero => rfl
  | succ m ih =>
    dsimp [scaleDownRadius]
    exact ih (r / (bdlLambda : ℝ) + 7003)

lemma scaleDownRadius_bound (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    scaleDownRadius m r ≤ r / ((bdlLambda : ℝ) ^ m) + 7004 := by
  induction m generalizing r with
  | zero =>
    dsimp [scaleDownRadius]
    rw [pow_zero, div_one]
    linarith
  | succ m ih =>
    dsimp [scaleDownRadius]
    rw [scaleDownRadius_comm m r]
    have hlam : (10000 : ℝ) ≤ (bdlLambda : ℝ) := bdlLambda_ge_10000
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := by linarith
    have h_ih := ih hr
    have h_div1 : (scaleDownRadius m r) / (bdlLambda : ℝ) ≤
        (r / ((bdlLambda : ℝ) ^ m) + 7004) / (bdlLambda : ℝ) :=
      div_le_div_of_nonneg_right h_ih (le_of_lt hlam_pos)
    have h_div2 : (r / ((bdlLambda : ℝ) ^ m) + 7004) / (bdlLambda : ℝ) =
        r / ((bdlLambda : ℝ) ^ (m + 1)) + 7004 / (bdlLambda : ℝ) := by
      rw [add_div, div_div, ← pow_succ]
    have h_7004 : 7004 / (bdlLambda : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hlam_pos]
      linarith
    linarith

lemma scaleDownRadius_bound_tight (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    scaleDownRadius m r ≤ r / ((bdlLambda : ℝ) ^ m) + 70031 / 10 := by
  induction m generalizing r with
  | zero =>
    dsimp [scaleDownRadius]
    rw [pow_zero, div_one]
    linarith
  | succ m ih =>
    dsimp [scaleDownRadius]
    rw [scaleDownRadius_comm m r]
    have hlam : (100000 : ℝ) ≤ (bdlLambda : ℝ) := by dsimp [bdlLambda]; norm_num
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := by linarith
    have h_ih := ih hr
    have h_div1 : (scaleDownRadius m r) / (bdlLambda : ℝ) ≤
        (r / ((bdlLambda : ℝ) ^ m) + 70031 / 10) / (bdlLambda : ℝ) :=
      div_le_div_of_nonneg_right h_ih (le_of_lt hlam_pos)
    have h_div2 : (r / ((bdlLambda : ℝ) ^ m) + 70031 / 10) / (bdlLambda : ℝ) =
        r / ((bdlLambda : ℝ) ^ (m + 1)) + (70031 / 10) / (bdlLambda : ℝ) := by
      rw [add_div, div_div, ← pow_succ]
    have h_70031 : (70031 / 10) / (bdlLambda : ℝ) ≤ 1 / 10 := by
      rw [div_le_iff₀ hlam_pos]
      linarith
    linarith

lemma mul_add_le_scaleUpRadius (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    scaleUpRadius m R ≤ ((bdlLambda : ℝ) ^ m) * R + (((bdlLambda : ℝ) ^ m) - 1) * 13008 := by
  induction m with
  | zero =>
    dsimp [scaleUpRadius]
    rw [pow_zero]
    linarith
  | succ m ih =>
    dsimp [scaleUpRadius]
    have hlam : (10000 : ℝ) ≤ (bdlLambda : ℝ) := bdlLambda_ge_10000
    have h_pow_ge_one : (1 : ℝ) ≤ (bdlLambda : ℝ) ^ m := one_le_pow₀ (by linarith)
    have h_step : (bdlLambda : ℝ) * (((bdlLambda : ℝ) ^ m) * R + (((bdlLambda : ℝ) ^ m) - 1) * 13008 + 13006) ≤
        ((bdlLambda : ℝ) ^ (m + 1)) * R + (((bdlLambda : ℝ) ^ (m + 1)) - 1) * 13008 := by
      rw [pow_succ']
      nlinarith
    nlinarith

lemma scaleUpRadius_bound (m : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    scaleUpRadius m R ≤ ((bdlLambda : ℝ) ^ m) * (R + 13008) := by
  have h_aux := mul_add_le_scaleUpRadius m hR
  linarith

theorem bdlHalfStep_iterated_globalStabilizers_step (j m : ℕ)
    (x0 : Point3D) {r R_base : ℝ}
    (hr0 : 0 ≤ r) (hrR : scaleDownRadius m r ≤ R_base)
    (h_primal : globalStabilizersInBall (bdlHalfStep j).code
      (scaleDownCenter m x0) (scaleDownRadius m r) ⊆
      locallyGeneratedInBall (bdlHalfStep j).code (scaleDownCenter m x0) R_base)
    (h_dual : globalStabilizersInBall (dualCode (bdlHalfStep j).code)
      (scaleDownCenter m x0) (scaleDownRadius m r) ⊆
      locallyGeneratedInBall (dualCode (bdlHalfStep j).code) (scaleDownCenter m x0) R_base) :
    globalStabilizersInBall (bdlHalfStep (j + m)).code x0 r ⊆
      locallyGeneratedInBall (bdlHalfStep (j + m)).code x0 (scaleUpRadius m R_base) ∧
    globalStabilizersInBall (dualCode (bdlHalfStep (j + m)).code) x0 r ⊆
      locallyGeneratedInBall (dualCode (bdlHalfStep (j + m)).code) x0 (scaleUpRadius m R_base) := by
  induction m generalizing x0 r with
  | zero =>
    dsimp [scaleDownCenter, scaleDownRadius, scaleUpRadius] at h_primal h_dual ⊢
    exact ⟨h_primal, h_dual⟩
  | succ m ih =>
    have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
    have hr' : 0 ≤ r / (bdlLambda : ℝ) + 7003 := by
      have : 0 ≤ r / (bdlLambda : ℝ) := div_nonneg hr0 (le_of_lt hlam_pos)
      linarith
    have h_ih := ih (fun axis => x0 axis / (bdlLambda : ℝ)) hr' hrR h_primal h_dual
    have hrR_step : r / (bdlLambda : ℝ) + 7003 ≤ scaleUpRadius m R_base :=
      scaleDownRadius_le_scaleUpRadius m hr' hrR
    have h_step := bdlHalfStep_globalStabilizers_step (j + m) x0 hr0 hrR_step h_ih.1 h_ih.2
    have h_add : j + (m + 1) = (j + m) + 1 := by omega
    rw [h_add]
    exact h_step

/-! ## 3. Euclidean Ball Separation and Barycentric Shell Bounds -/

lemma distSq3D_scale_diff (P1 P2 A B : Point3D) (s : ℝ)
    (h : ∀ axis : Fin 3, P1 axis - P2 axis = s * (A axis - B axis)) :
    distSq3D P1 P2 = s ^ 2 * distSq3D A B := by
  dsimp [distSq3D]
  rw [h 0, h 1, h 2]
  ring

lemma distSq3D_le_add_sq_of_mem_ball3D (y0 p1 p2 : Point3D) {r1 r2 : ℝ}
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hp1 : p1 ∈ ball3D y0 r1) (hp2 : p2 ∈ ball3D y0 r2) :
    distSq3D p1 p2 ≤ (r1 + r2) ^ 2 := by
  have hp1' : y0 ∈ ball3D p1 r1 := by
    dsimp [ball3D] at hp1 ⊢
    rw [distSq3D_comm]
    exact hp1
  have h_in := ball3D_step_of_distSq3D_le p1 y0 p2 hr1 hr2 hp1' hp2
  dsimp [ball3D] at h_in
  rw [distSq3D_comm]
  exact h_in

lemma not_mem_ball3D_of_near_and_sep (y0 p1 p2 : Point3D) {R_near R_sep r_0 : ℝ}
    (hr0 : 0 ≤ r_0) (hR_near : 0 ≤ R_near) (h_gap : R_near + r_0 < R_sep)
    (h_near : p1 ∈ ball3D y0 R_near) (h_sep : R_sep ^ 2 ≤ distSq3D p1 p2) :
    p2 ∉ ball3D y0 r_0 := by
  intro hp2
  have h_le := distSq3D_le_add_sq_of_mem_ball3D y0 p1 p2 hR_near hr0 h_near hp2
  have h_lt : (R_near + r_0) ^ 2 < R_sep ^ 2 := by nlinarith
  linarith

lemma not_mem_ball3D_of_far_and_step (y0 p1 p2 : Point3D) {R_far R_step r_0 : ℝ}
    (hr0 : 0 ≤ r_0) (hR_step : 0 ≤ R_step) (h_sum : R_step + r_0 ≤ R_far)
    (h_far : p1 ∉ ball3D y0 R_far) (h_step : p2 ∈ ball3D p1 R_step) :
    p2 ∉ ball3D y0 r_0 := by
  intro hp2
  apply h_far
  have h_step' : distSq3D p1 p2 ≤ R_step ^ 2 := by
    rw [distSq3D_comm]
    exact h_step
  have h_in := ball3D_step_of_distSq3D_le y0 p2 p1 hr0 hR_step hp2 h_step'
  exact ball3D_mono y0 (by linarith) (by linarith) h_in

lemma simplex_vec_comb_distSq3D_ge (pX pQ pZ P1 P2 : Point3D) {L α β : ℝ}
    (_hL : 0 ≤ L) (hβ : 0 < β)
    (h_alt : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      L ^ 2 ≤ distSq3D pX (lerpPoint3D pQ pZ ε) ∧
      L ^ 2 ≤ distSq3D pQ (lerpPoint3D pX pZ ε) ∧
      L ^ 2 ≤ distSq3D pZ (lerpPoint3D pX pQ ε))
    (h_diff : ∀ axis : Fin 3, P1 axis - P2 axis = α * (pQ axis - pX axis) + β * (pZ axis - pQ axis)) :
    (β * L) ^ 2 ≤ distSq3D P1 P2 := by
  by_cases h1 : 0 ≤ α ∧ α ≤ β
  · let ε : ℝ := 1 - α / β
    have hε0 : 0 ≤ ε := by
      dsimp [ε]
      have : α / β ≤ 1 := (div_le_one hβ).mpr h1.2
      linarith
    have hε1 : ε ≤ 1 := by
      dsimp [ε]
      have : 0 ≤ α / β := div_nonneg h1.1 (le_of_lt hβ)
      linarith
    have h_eq : ∀ axis : Fin 3, P1 axis - P2 axis = β * (pZ axis - lerpPoint3D pX pQ ε axis) := by
      intro axis
      rw [h_diff axis]
      dsimp [lerpPoint3D, ε]
      have hβ_ne : β ≠ 0 := ne_of_gt hβ
      field_simp [hβ_ne]
      ring
    rw [distSq3D_scale_diff P1 P2 pZ (lerpPoint3D pX pQ ε) β h_eq]
    have h_ge := (h_alt ε hε0 hε1).2.2
    calc (β * L) ^ 2 = β ^ 2 * L ^ 2 := by ring
      _ ≤ β ^ 2 * distSq3D pZ (lerpPoint3D pX pQ ε) :=
          mul_le_mul_of_nonneg_left h_ge (sq_nonneg β)
  · by_cases h2 : β < α
    · have hα_pos : 0 < α := lt_trans hβ h2
      let ε : ℝ := β / α
      have hε0 : 0 ≤ ε := div_nonneg (le_of_lt hβ) (le_of_lt hα_pos)
      have hε1 : ε ≤ 1 := (div_le_one hα_pos).mpr (le_of_lt h2)
      have h_eq : ∀ axis : Fin 3, P1 axis - P2 axis = (-α) * (pX axis - lerpPoint3D pQ pZ ε axis) := by
        intro axis
        rw [h_diff axis]
        dsimp [lerpPoint3D, ε]
        have hα_ne : α ≠ 0 := ne_of_gt hα_pos
        field_simp [hα_ne]
        ring
      rw [distSq3D_scale_diff P1 P2 pX (lerpPoint3D pQ pZ ε) (-α) h_eq]
      have h_ge := (h_alt ε hε0 hε1).1
      have h_sq : β ^ 2 ≤ (-α) ^ 2 := by nlinarith
      calc (β * L) ^ 2 = β ^ 2 * L ^ 2 := by ring
        _ ≤ (-α) ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right h_sq (sq_nonneg L)
        _ ≤ (-α) ^ 2 * distSq3D pX (lerpPoint3D pQ pZ ε) :=
            mul_le_mul_of_nonneg_left h_ge (sq_nonneg (-α))
    · have hα_neg : α < 0 := by
        by_contra h_nonneg
        push_neg at h_nonneg h2
        exact h1 ⟨h_nonneg, h2⟩
      have h_ba_pos : 0 < β - α := by linarith
      let ε : ℝ := β / (β - α)
      have hε0 : 0 ≤ ε := div_nonneg (le_of_lt hβ) (le_of_lt h_ba_pos)
      have hε1 : ε ≤ 1 := (div_le_one h_ba_pos).mpr (by linarith)
      have h_eq : ∀ axis : Fin 3, P1 axis - P2 axis = (-(β - α)) * (pQ axis - lerpPoint3D pX pZ ε axis) := by
        intro axis
        rw [h_diff axis]
        dsimp [lerpPoint3D, ε]
        have hba_ne : β - α ≠ 0 := ne_of_gt h_ba_pos
        field_simp [hba_ne]
        ring
      rw [distSq3D_scale_diff P1 P2 pQ (lerpPoint3D pX pZ ε) (-(β - α)) h_eq]
      have h_ge := (h_alt ε hε0 hε1).2.1
      have h_sq : β ^ 2 ≤ (-(β - α)) ^ 2 := by nlinarith
      calc (β * L) ^ 2 = β ^ 2 * L ^ 2 := by ring
        _ ≤ (-(β - α)) ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right h_sq (sq_nonneg L)
        _ ≤ (-(β - α)) ^ 2 * distSq3D pQ (lerpPoint3D pX pZ ε) :=
            mul_le_mul_of_nonneg_left h_ge (sq_nonneg (-(β - α)))

lemma triGridPos3D_ray_separation (pX pQ pZ : Point3D) (m u1 v1 u2 v2 : ℕ) {L : ℝ}
    (hm : 0 < m) (hL : 0 ≤ L)
    (hv1 : v1 ≤ u1) (hv2 : v2 ≤ u2) (h_lt : v2 < v1)
    (h_alt : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      L ^ 2 ≤ distSq3D pX (lerpPoint3D pQ pZ ε) ∧
      L ^ 2 ≤ distSq3D pQ (lerpPoint3D pX pZ ε) ∧
      L ^ 2 ≤ distSq3D pZ (lerpPoint3D pX pQ ε)) :
    ((((v1 : ℝ) - (v2 : ℝ)) / (m : ℝ)) * L) ^ 2 ≤
      distSq3D (triGridPos3D pX pQ pZ m u1 v1) (triGridPos3D pX pQ pZ m u2 v2) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hv_pos : (0 : ℝ) < (v1 : ℝ) - (v2 : ℝ) := sub_pos.mpr (Nat.cast_lt.mpr h_lt)
  have hβ_pos : 0 < ((v1 : ℝ) - (v2 : ℝ)) / (m : ℝ) := div_pos hv_pos hm_pos
  apply simplex_vec_comb_distSq3D_ge pX pQ pZ
    (triGridPos3D pX pQ pZ m u1 v1) (triGridPos3D pX pQ pZ m u2 v2)
    hL hβ_pos h_alt (α := ((u1 : ℝ) - (u2 : ℝ)) / (m : ℝ))
  intro axis
  dsimp [triGridPos3D]
  rw [Nat.cast_sub hv1, Nat.cast_sub hv2]
  ring

lemma distSq3D_posX_boundaryX0Pos_ge (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (x : B.M_X)
    (v : BoundaryX0 (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred)
    (hv : InLinkOfX (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred x v) :
    let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤ distSq3D (pcode.posX x) (boundaryX0Pos pcode bdlSubdivPred v) := by
  intro pcode
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · obtain ⟨z, hzq⟩ := h_inv.2.2.2.1.2 q
    let s : ActiveSimplex2 B.code := ⟨(x, (q, z)), ⟨hv, hzq⟩⟩
    have h_alt := (h_valid.2.2.2.2.2.1 s 0 (le_refl 0) (by norm_num)).1
    have h_lerp : lerpPoint3D (pcode.posQ q) (pcode.posZ z) 0 = pcode.posQ q := by
      ext axis; dsimp [lerpPoint3D]; ring
    dsimp [boundaryX0Pos]
    rwa [h_lerp] at h_alt
  · let s : ActiveSimplex2 B.code := ⟨(x, eZ.val), ⟨hv, eZ.property⟩⟩
    let ε : ℝ := ((j.val + 1 : ℕ) : ℝ) / ((bdlSubdivPred + 1 : ℕ) : ℝ)
    have hε0 : 0 ≤ ε := by dsimp [ε]; positivity
    have hε1 : ε ≤ 1 := by
      dsimp [ε]
      rw [div_le_one (by positivity)]
      exact Nat.cast_le.mpr (Nat.add_le_add_right (le_of_lt j.isLt) 1)
    have h_alt := (h_valid.2.2.2.2.2.1 s ε hε0 hε1).1
    have h_lerp : lerpPoint3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) ε =
        subdividePoint3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (bdlSubdivPred + 1) (j.val + 1) := by
      ext axis; dsimp [lerpPoint3D, subdividePoint3D, ε]; ring
    dsimp [boundaryX0Pos]
    rwa [h_lerp] at h_alt
  · rcases hv with ⟨q, hxq, hzq⟩
    let s : ActiveSimplex2 B.code := ⟨(x, (q, z)), ⟨hxq, hzq⟩⟩
    have h_alt := (h_valid.2.2.2.2.2.1 s 1 (by norm_num) (le_refl 1)).1
    have h_lerp : lerpPoint3D (pcode.posQ q) (pcode.posZ z) 1 = pcode.posZ z := by
      ext axis; dsimp [lerpPoint3D]; ring
    dsimp [boundaryX0Pos]
    rwa [h_lerp] at h_alt

lemma shellVertexPos_mem_ball3D_posX_succ (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (sv : ShellVertex (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred) :
    let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
    shellVertexPos pcode bdlSubdivPred sv ∈ ball3D (pcode.posX sv.val.1.val.1) (sv.val.2.val + 1 : ℝ) := by
  intro pcode
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  let D_edge : ℝ := 2001 * (bdlLambda : ℝ)
  have hD : HasCoarseEdgeBound pcode D_edge := by
    have hD_raw := hasCoarseEdgeBound_of_validLLLPerturbation B h_valid
    have h_eq : (2 * bdlAlpha + 1) * (bdlLambda : ℝ) = D_edge := by dsimp [D_edge, bdlAlpha, bdlAlphaNat]; ring
    rwa [h_eq] at hD_raw
  let m : ℕ := bdlSubdivPred + 1
  have hm_eq : (m : ℝ) = 2 * D_edge := by
    have h1 : bdlSubdivPred + 1 = bdlSubdivM := bdlSubdivM_eq_succ
    dsimp [m, D_edge]
    rw [h1]
    dsimp [bdlSubdivM, bdlSubdivFactor, bdlAlphaNat]
    push_cast
    ring
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have h_tri_bound : ∀ (pQ pZ : Point3D) (u v : ℕ),
      v ≤ u →
      distSq3D pQ (pcode.posX sv.val.1.val.1) ≤ (m : ℝ) ^ 2 →
      distSq3D pZ (pcode.posX sv.val.1.val.1) ≤ (m : ℝ) ^ 2 →
      distSq3D (triGridPos3D (pcode.posX sv.val.1.val.1) pQ pZ m u v) (pcode.posX sv.val.1.val.1) ≤ (u : ℝ) ^ 2 := by
    intro pQ pZ u v hvu hQ hZ
    let a : ℝ := ((u - v : ℕ) : ℝ) / (m : ℝ)
    let b : ℝ := (v : ℝ) / (m : ℝ)
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have hb0 : 0 ≤ b := by dsimp [b]; positivity
    have hab : a + b = (u : ℝ) / (m : ℝ) := by
      dsimp [a, b]
      rw [← add_div, Nat.cast_sub hvu]
      ring
    have h_coord : ∀ axis : Fin 3,
        (triGridPos3D (pcode.posX sv.val.1.val.1) pQ pZ m u v axis - pcode.posX sv.val.1.val.1 axis) ^ 2 ≤
        (a + b) * (a * (pQ axis - pcode.posX sv.val.1.val.1 axis) ^ 2 +
                   b * (pZ axis - pcode.posX sv.val.1.val.1 axis) ^ 2) := by
      intro axis
      dsimp [triGridPos3D]
      have h_id : (pcode.posX sv.val.1.val.1 axis + a * (pQ axis - pcode.posX sv.val.1.val.1 axis) +
          b * (pZ axis - pcode.posX sv.val.1.val.1 axis) - pcode.posX sv.val.1.val.1 axis) ^ 2 =
          (a + b) * (a * (pQ axis - pcode.posX sv.val.1.val.1 axis) ^ 2 +
                     b * (pZ axis - pcode.posX sv.val.1.val.1 axis) ^ 2) -
          a * b * ((pQ axis - pcode.posX sv.val.1.val.1 axis) - (pZ axis - pcode.posX sv.val.1.val.1 axis)) ^ 2 := by ring
      nlinarith [sq_nonneg ((pQ axis - pcode.posX sv.val.1.val.1 axis) - (pZ axis - pcode.posX sv.val.1.val.1 axis)),
                 mul_nonneg ha0 hb0]
    have h0 := h_coord 0
    have h1 := h_coord 1
    have h2 := h_coord 2
    have h_sum : distSq3D (triGridPos3D (pcode.posX sv.val.1.val.1) pQ pZ m u v) (pcode.posX sv.val.1.val.1) ≤
        (a + b) * (a * distSq3D pQ (pcode.posX sv.val.1.val.1) + b * distSq3D pZ (pcode.posX sv.val.1.val.1)) := by
      dsimp [distSq3D]
      linarith
    have h_ab_m : (a + b) * (a * (m : ℝ) ^ 2 + b * (m : ℝ) ^ 2) = (u : ℝ) ^ 2 := by
      calc (a + b) * (a * (m : ℝ) ^ 2 + b * (m : ℝ) ^ 2)
        _ = (a + b) ^ 2 * (m : ℝ) ^ 2 := by ring
        _ = ((u : ℝ) / (m : ℝ)) ^ 2 * (m : ℝ) ^ 2 := by rw [hab]
        _ = (u : ℝ) ^ 2 := by field_simp [ne_of_gt hm_pos]
    calc distSq3D (triGridPos3D (pcode.posX sv.val.1.val.1) pQ pZ m u v) (pcode.posX sv.val.1.val.1)
      _ ≤ (a + b) * (a * distSq3D pQ (pcode.posX sv.val.1.val.1) + b * distSq3D pZ (pcode.posX sv.val.1.val.1)) := h_sum
      _ ≤ (a + b) * (a * (m : ℝ) ^ 2 + b * (m : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact add_le_add (mul_le_mul_of_nonneg_left hQ ha0) (mul_le_mul_of_nonneg_left hZ hb0)
      _ = (u : ℝ) ^ 2 := h_ab_m
  rcases sv with ⟨⟨⟨⟨x, v⟩, hp⟩, r_idx⟩, h_in⟩
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · have hQ : distSq3D (pcode.posQ q) (pcode.posX x) ≤ (m : ℝ) ^ 2 := by
      have h1 := hD.2.2 x q hp
      rw [hm_eq]; nlinarith [hD.1]
    have h_eq : shellVertexPos pcode bdlSubdivPred ⟨(⟨(x, Sum.inl q), hp⟩, r_idx), h_in⟩ =
        triGridPos3D (pcode.posX x) (pcode.posQ q) (pcode.posQ q) m (r_idx.val + 1) 0 := by
      ext axis; dsimp [shellVertexPos, subdividePoint3D, triGridPos3D, m]; simp
    dsimp [ball3D]
    rw [h_eq]
    exact_mod_cast h_tri_bound (pcode.posQ q) (pcode.posQ q) (r_idx.val + 1) 0 (Nat.zero_le _) hQ hQ
  · have hQ : distSq3D (pcode.posQ eZ.val.1) (pcode.posX x) ≤ (m : ℝ) ^ 2 := by
      have h1 := hD.2.2 x eZ.val.1 hp
      rw [hm_eq]; nlinarith [hD.1]
    have hZ : distSq3D (pcode.posZ eZ.val.2) (pcode.posX x) ≤ (m : ℝ) ^ 2 := by
      have h1 : pcode.posQ eZ.val.1 ∈ ball3D (pcode.posX x) D_edge := hD.2.2 x eZ.val.1 hp
      have h2 := hD.2.1 eZ.val.2 eZ.val.1 eZ.property
      rw [distSq3D_comm] at h2
      have h3 := ball3D_step_of_distSq3D_le (pcode.posX x) (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2)
        hD.1 hD.1 h1 h2
      dsimp [ball3D] at h3
      rw [hm_eq]; linarith
    dsimp [ball3D, shellVertexPos]
    have h_in' : j.val < r_idx.val := h_in
    exact_mod_cast h_tri_bound (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2)
      (r_idx.val + 1) (j.val + 1) (Nat.add_le_add_right (le_of_lt h_in') 1) hQ hZ
  · rcases hp with ⟨q, hxq, hzq⟩
    have hZ : distSq3D (pcode.posZ z) (pcode.posX x) ≤ (m : ℝ) ^ 2 := by
      have h1 : pcode.posQ q ∈ ball3D (pcode.posX x) D_edge := hD.2.2 x q hxq
      have h2 := hD.2.1 z q hzq
      rw [distSq3D_comm] at h2
      have h3 := ball3D_step_of_distSq3D_le (pcode.posX x) (pcode.posQ q) (pcode.posZ z)
        hD.1 hD.1 h1 h2
      dsimp [ball3D] at h3
      rw [hm_eq]; linarith
    have h_eq : shellVertexPos pcode bdlSubdivPred ⟨(⟨(x, Sum.inr (Sum.inr z)), ⟨q, hxq, hzq⟩⟩, r_idx), h_in⟩ =
        triGridPos3D (pcode.posX x) (pcode.posZ z) (pcode.posZ z) m (r_idx.val + 1) (r_idx.val + 1) := by
      ext axis; dsimp [shellVertexPos, subdividePoint3D, triGridPos3D, m]; rw [Nat.sub_self]; simp
    dsimp [ball3D]
    rw [h_eq]
    exact_mod_cast h_tri_bound (pcode.posZ z) (pcode.posZ z) (r_idx.val + 1) (r_idx.val + 1) (le_refl _) hZ hZ

lemma bdlGamma_half_mul_bdlLambda_ge :
    (3500000000000000000000000 : ℝ) ≤ (bdlGamma / 2) * (bdlLambda : ℝ) := by
  have hg := bdlGamma_ge_seven_fifths
  dsimp [bdlLambda]
  linarith

lemma hRadialShell_eq_zero_of_far_posX_and_small_shell (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (y0 : Point3D) {r_0 : ℝ} (hr0 : 0 ≤ r_0) (hr_hi : r_0 ≤ 7015)
    (h : BDLStepXQ (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred → ZMod 2)
    (hh_supp : supp1 (dualCode (bdlRandomStepX B).code) h ⊆ ball3D y0 r_0)
    (x : B.M_X)
    (hx_far : (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posX x ∉
      ball3D y0 ((bdlGamma / 2) * (bdlLambda : ℝ)))
    (sv : ShellVertex (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred)
    (hsv_x : sv.val.1.val.1 = x) (hsv_r : sv.val.2.val ≤ 300000000) :
    let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
    hRadialShell pcode bdlSubdivPred h sv 0 = 0 := by
  intro pcode
  have h_sv_not_mem : ∀ (sv' : ShellVertex pcode bdlSubdivPred),
      sv'.val.1.val.1 = x → sv'.val.2.val ≤ 300000000 →
      shellVertexPos pcode bdlSubdivPred sv' ∉ ball3D y0 r_0 := by
    intro sv' hsv'_x hsv'_r
    have h_step := shellVertexPos_mem_ball3D_posX_succ B h_inv sv'
    rw [hsv'_x] at h_step
    have h_step_300 : shellVertexPos pcode bdlSubdivPred sv' ∈ ball3D (pcode.posX x) 300000001 := by
      apply ball3D_mono (pcode.posX x) (by positivity) _ h_step
      have : (sv'.val.2.val : ℝ) ≤ 300000000 := Nat.cast_le.mpr hsv'_r
      linarith
    apply not_mem_ball3D_of_far_and_step y0 (pcode.posX x) (shellVertexPos pcode bdlSubdivPred sv')
      hr0 (by norm_num) _ hx_far h_step_300
    have h_big := bdlGamma_half_mul_bdlLambda_ge
    linarith
  dsimp [hRadialShell]
  by_cases h_nd : ¬ IsDiagZeroVertex pcode bdlSubdivPred sv
  · rw [dif_pos h_nd]
    by_contra h_ne
    have h_in := hh_supp ⟨Sum.inl (Sum.inl (⟨sv, h_nd⟩, 0)), h_ne, rfl⟩
    exact h_sv_not_mem sv hsv_x hsv_r h_in
  · rw [dif_neg h_nd]
    rcases h_v : sv.val.1.val.2 with q0 | ⟨⟨eZ, j⟩ | z⟩
    · rfl
    · rfl
    · (try dsimp only)
      split_ifs with h_ex
      · let q_can := canonicalSquareQ pcode sv.val.1.val.1 z h_ex
        let h_can := canonicalSquareQ_spec pcode sv.val.1.val.1 z h_ex
        have h1 : h (Sum.inl (Sum.inl (cornerSpokeRadial pcode bdlSubdivPred sv.val.1.val.1 q_can h_can.1, 0))) = 0 := by
          by_contra h1_ne
          have h_in := hh_supp ⟨Sum.inl (Sum.inl (cornerSpokeRadial pcode bdlSubdivPred sv.val.1.val.1 q_can h_can.1, 0)), h1_ne, rfl⟩
          exact h_sv_not_mem (cornerSpoke pcode bdlSubdivPred sv.val.1.val.1 q_can h_can.1) hsv_x (Nat.zero_le _) h_in
        have h2 : h (Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode bdlSubdivPred sv.val.1.val.1 q_can z h_can.1 h_can.2, 0)))) = 0 := by
          by_contra h2_ne
          have h_in := hh_supp ⟨Sum.inl (Sum.inr (Sum.inl (cornerSeg pcode bdlSubdivPred sv.val.1.val.1 q_can z h_can.1 h_can.2, 0))), h2_ne, rfl⟩
          exact h_sv_not_mem (shellSegEndVertex pcode bdlSubdivPred (cornerSeg pcode bdlSubdivPred sv.val.1.val.1 q_can z h_can.1 h_can.2))
            hsv_x (Nat.zero_le _) h_in
        rw [h1, h2, add_zero]
      · rfl

lemma iterate_radialParentVertex_r_val {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (i : ℕ) (sv : ShellVertex pcode M) :
    ((radialParentVertex pcode M)^[i] sv).val.2.val = sv.val.2.val - i := by
  induction i generalizing sv with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    dsimp [radialParentVertex, finPred]
    omega

lemma iterate_radialParentVertex_v_of_lt {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (j : Fin M)
    (i : ℕ) (sv : ShellVertex pcode M)
    (hv : sv.val.1.val.2 = Sum.inr (Sum.inl (eZ, j)))
    (hlt : j.val < sv.val.2.val - i) :
    ((radialParentVertex pcode M)^[i] sv).val.1.val.2 = Sum.inr (Sum.inl (eZ, j)) := by
  induction i generalizing sv with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    apply ih (radialParentVertex pcode M sv)
    · dsimp [radialParentVertex, radialParentLink, radialParentV]
      rw [hv]
      dsimp
      have hj : j.val < (finPred sv.val.2).val := by
        dsimp [finPred]; omega
      rw [if_pos hj]
    · dsimp [radialParentVertex, finPred]
      omega

end WeldedHierarchy
