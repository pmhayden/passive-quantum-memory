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

import Proofs.ConeAcyclicityRCA.SubcylinderRayConstancyAndCheckpoints
import Defs.RescaledRCA

/-!
# Two-Step Sub-Cylinder Filling and Continuum Cone Acyclicity of the Welded Hierarchy

Applies six-checkpoint pigeonhole selection to express coarseProjCocycle as a local coboundary of subcylinderCoarseCochain on a clean shell (coarseProjCocycle_eq_checkGen_subcylinderCoarseCochain), proving base-scale local stabilizer filling after two alternating welding half-steps (bdlHalfStep_subcylinder_filling). Combines scale-matched stopping with iterated collar transfer to establish Euclidean and l_infty cone acyclicity across all levels of bdlWeldedCode (bdl_random_cone_acyclicity_extended, bdlWeldedCode_inf_cone_acyclicity).

## References

* Part I, Section 3.3 (`subsec:scale-matched-rca`), Lemma 3.8 (`lem:clean-shell-subcylinder`), Theorem 3.9 (`thm:rca-welded-hierarchy`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section
open scoped Classical
open BigOperators
namespace WeldedHierarchy

/-! ## 1. Coarse Coboundary Identification via Candidate Shell Pigeonhole -/

theorem coarseProjCocycle_eq_checkGen_subcylinderCoarseCochain (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (y0 : Point3D) {r_0 : ℝ} (hr0 : 0 ≤ r_0) (hr_hi : r_0 ≤ 7015)
    (h : BDLStepXQ (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred → ZMod 2)
    (hh_syn : syndrome (dualCode (bdlRandomStepX B).code) h = 0)
    (hh_supp : supp1 (dualCode (bdlRandomStepX B).code) h ⊆ ball3D y0 r_0) :
    let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
    checkGen (dualCode pcode) (subcylinderCoarseCochain B y0 h) =
      coarseProjCocycle pcode bdlSubdivPred h := by
  intro pcode
  let M := bdlSubdivPred
  have h_syn_at : ∀ mZ, syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0 :=
    fun mZ => congr_fun hh_syn mZ
  ext q0
  obtain ⟨x_any, hx_any⟩ := h_inv.2.2.2.1.1 q0
  obtain ⟨z0, hz0⟩ := h_inv.2.2.2.1.2 q0
  let eZ0 : ActiveZ pcode := ⟨(q0, z0), hz0⟩
  let v0_cand : Fin 6 → Xq0 pcode M := fun a => Sum.inr (Sum.inl (eZ0, subcylinderCandidateJ a))
  let Bad0 : Finset (Fin 6) := Finset.univ.filter (fun a : Fin 6 => h (Sum.inr (v0_cand a, 0)) ≠ 0)
  have h_cand_le_M : ∀ c : Fin 6, (subcylinderCandidateJ c).val + 1 ≤ M + 1 :=
    fun c => Nat.add_le_add_right (le_of_lt (subcylinderCandidateJ c).isLt) 1
  have h_card_Bad0 : Bad0.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have ha_ne : h (Sum.inr (v0_cand a, 0)) ≠ 0 := (Finset.mem_filter.mp ha).2
    have hb_ne : h (Sum.inr (v0_cand b, 0)) ≠ 0 := (Finset.mem_filter.mp hb).2
    have ha_in := hh_supp ⟨Sum.inr (v0_cand a, 0), ha_ne, rfl⟩
    have hb_in := hh_supp ⟨Sum.inr (v0_cand b, 0), hb_ne, rfl⟩
    change (bdlCylinderStepX pcode M).posQ (Sum.inr (v0_cand a, 0)) ∈ ball3D y0 r_0 at ha_in
    change (bdlCylinderStepX pcode M).posQ (Sum.inr (v0_cand b, 0)) ∈ ball3D y0 r_0 at hb_in
    have h_pos_eq : ∀ c : Fin 6, (bdlCylinderStepX pcode M).posQ (Sum.inr (v0_cand c, 0)) =
        triGridPos3D (pcode.posX x_any) (pcode.posQ q0) (pcode.posZ z0)
          (M + 1) (M + 1) ((subcylinderCandidateJ c).val + 1) := by
      intro c
      ext axis
      dsimp [bdlCylinderStepX, bdlStepXPosQ, xq0Pos, projXq0ToBoundaryX0, v0_cand,
        boundaryX0Pos, subdividePoint3D, triGridPos3D, eZ0]
      rw [Nat.cast_sub (h_cand_le_M c)]
      have hm_ne : (M + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hm_ne]
      ring
    rw [h_pos_eq a] at ha_in
    rw [h_pos_eq b] at hb_in
    exact not_both_mem_ball3D_of_subcylinderCandidateJ B h_inv y0 hr0 hr_hi x_any q0 z0
      hx_any hz0 a b hab (M + 1) (M + 1)
      (h_cand_le_M a) (h_cand_le_M b)
      ha_in hb_in
  let S_B : Finset B.M_X := Finset.univ.filter (fun x : B.M_X =>
    pcode.checkX x q0 ≠ 0 ∧ pcode.posX x ∉ ball3D y0 ((bdlGamma / 2) * (bdlLambda : ℝ)))
  have h_card_SB : S_B.card ≤ 4 := by
    have h_sub : S_B ⊆ Finset.univ.filter (fun x : B.M_X => B.code.checkX x q0 ≠ 0) :=
      fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2.1⟩
    exact le_trans (Finset.card_le_card h_sub) (h_inv.1.1.2.2.1 q0)
  let BadRay : B.M_X → Finset (Fin 6) := fun x =>
    Finset.univ.filter (fun a : Fin 6 =>
      ∃ hx : pcode.checkX x q0 ≠ 0,
        radialRaySum pcode M h
          (mkOuterShellVertex pcode M ⟨(x, projXq0ToBoundaryX0 pcode M (v0_cand a)),
            inLinkOfX_projXq0_of_checkX_ne_zero pcode M x (v0_cand a) hx⟩) 0 ≠ 0)
  have h_card_BadRay : ∀ x ∈ S_B, (BadRay x).card ≤ 1 := by
    intro x hx_SB
    rcases (Finset.mem_filter.mp hx_SB).2 with ⟨hx_chk, hx_far⟩
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    have h_extract_hit : ∀ c : Fin 6, c ∈ BadRay x →
        ∃ u_c : ℕ, (subcylinderCandidateJ c).val + 1 ≤ u_c ∧
          triGridPos3D (pcode.posX x) (pcode.posQ q0) (pcode.posZ z0)
            (M + 1) u_c ((subcylinderCandidateJ c).val + 1) ∈ ball3D y0 r_0 := by
      intro c hc
      obtain ⟨_, h_ray_ne⟩ := (Finset.mem_filter.mp hc).2
      let sv_out := mkOuterShellVertex pcode M ⟨(x, projXq0ToBoundaryX0 pcode M (v0_cand c)),
        inLinkOfX_projXq0_of_checkX_ne_zero pcode M x (v0_cand c) hx_chk⟩
      obtain ⟨i, hi_mem, hi_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_ray_ne
      let sv_i := (radialParentVertex pcode M)^[i] sv_out
      have hsv_i_x : sv_i.val.1.val.1 = x := iterate_radialParentVertex_ownerX pcode M i sv_out
      have hsv_i_r : sv_i.val.2.val = M - i := iterate_radialParentVertex_r_val pcode M i sv_out
      have h_gt_j : (subcylinderCandidateJ c).val < sv_i.val.2.val := by
        by_contra h_le_j
        push_neg at h_le_j
        have h_le_300 : sv_i.val.2.val ≤ 300000000 :=
          le_trans h_le_j (subcylinderCandidateJ_le_300000000 c)
        exact hi_ne (hRadialShell_eq_zero_of_far_posX_and_small_shell B h_inv y0 hr0 hr_hi h hh_supp x hx_far sv_i hsv_i_x h_le_300)
      have hsv_i_v : sv_i.val.1.val.2 = Sum.inr (Sum.inl (eZ0, subcylinderCandidateJ c)) :=
        iterate_radialParentVertex_v_of_lt pcode M eZ0 (subcylinderCandidateJ c) i sv_out rfl (hsv_i_r ▸ h_gt_j)
      have h_nd : ¬ IsDiagZeroVertex pcode M sv_i := by
        intro ⟨hr0_i, _⟩
        omega
      dsimp [hRadialShell] at hi_ne
      rw [dif_pos h_nd] at hi_ne
      have h_in_ball := hh_supp ⟨Sum.inl (Sum.inl (⟨sv_i, h_nd⟩, 0)), hi_ne, rfl⟩
      change (bdlCylinderStepX pcode M).posQ (Sum.inl (Sum.inl (⟨sv_i, h_nd⟩, 0))) ∈ ball3D y0 r_0 at h_in_ball
      have h_pos_sv : (bdlCylinderStepX pcode M).posQ (Sum.inl (Sum.inl (⟨sv_i, h_nd⟩, 0))) =
          triGridPos3D (pcode.posX x) (pcode.posQ q0) (pcode.posZ z0)
            (M + 1) (sv_i.val.2.val + 1) ((subcylinderCandidateJ c).val + 1) := by
        change shellVertexPos pcode M sv_i = _
        dsimp [shellVertexPos]
        rw [hsv_i_v, hsv_i_x]
      rw [h_pos_sv] at h_in_ball
      exact ⟨sv_i.val.2.val + 1, Nat.add_le_add_right (le_of_lt h_gt_j) 1, h_in_ball⟩
    obtain ⟨u1, hu1, h1⟩ := h_extract_hit a ha
    obtain ⟨u2, hu2, h2⟩ := h_extract_hit b hb
    exact not_both_mem_ball3D_of_subcylinderCandidateJ B h_inv y0 hr0 hr_hi x q0 z0
      hx_chk hz0 a b hab u1 u2 hu1 hu2 h1 h2
  let BadTotal : Finset (Fin 6) := Bad0 ∪ S_B.biUnion BadRay
  have h_card_BadTotal : BadTotal.card < (Finset.univ : Finset (Fin 6)).card := by
    have h1 : BadTotal.card ≤ Bad0.card + (S_B.biUnion BadRay).card := Finset.card_union_le _ _
    have h2 : (S_B.biUnion BadRay).card ≤ ∑ x ∈ S_B, (BadRay x).card := Finset.card_biUnion_le
    have h3 : ∑ x ∈ S_B, (BadRay x).card ≤ S_B.card * 1 :=
      Finset.sum_le_card_nsmul S_B (fun x => (BadRay x).card) 1 h_card_BadRay
    simp only [Fintype.card_fin, Finset.card_univ]
    omega
  have h_not_sub : ¬ (Finset.univ : Finset (Fin 6)) ⊆ BadTotal := by
    intro h_sub
    have := Finset.card_le_card h_sub
    omega
  obtain ⟨a, _, ha_good⟩ := Finset.not_subset.mp h_not_sub
  have ha_not_Bad0 : a ∉ Bad0 := fun h_mem => ha_good (Finset.mem_union_left _ h_mem)
  have ha_h_zero : h (Sum.inr (v0_cand a, 0)) = 0 := by
    by_contra h_ne
    exact ha_not_Bad0 (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h_ne⟩)
  have h_coarse_eq : coarseProjCocycle pcode M h q0 =
      cylinderResidualCocycle pcode M h (Sum.inr (v0_cand a, 0)) :=
    (cylinderResidualCocycle_inr_eq_coarse pcode M h_inv.2.2.2.1.2 h q0
      (fun x _ qX hqX => cylinderResidualCocycle_inl_eq_zero pcode M h_inv.1.2 h_inv.2.2.2.2.1 h x
        (fun _ _ _ => h_syn_at _) (fun _ _ _ _ => h_syn_at _) qX hqX)
      (fun _ _ _ _ => h_syn_at _) (fun _ _ _ => h_syn_at _) (v0_cand a) rfl 0).symm
  have h_res_eq : cylinderResidualCocycle pcode M h (Sum.inr (v0_cand a, 0)) =
      checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) (Sum.inr (v0_cand a, 0)) := by
    change h (Sum.inr (v0_cand a, 0)) +
      checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) (Sum.inr (v0_cand a, 0)) +
      checkGen (dualCode (bdlCylinderStepX pcode M)) (layer1ConeCochain pcode M (coneLinkVal pcode M h))
        (Sum.inr (v0_cand a, 0)) = _
    rw [ha_h_zero, checkGen_dual_layer1ConeCochain_inr_zero, zero_add, add_zero]
  rw [h_coarse_eq, h_res_eq, checkGen_dual_apexRadialCocycle_inr_zero]
  dsimp [checkGen, dualCode, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : pcode.checkX x q0 ≠ 0
  · have hx1 : pcode.checkX x q0 = 1 := zmod2_eq_one_of_ne_zero _ hx
    have hx' : pcode.checkX x (xq0OwnerQ pcode M (v0_cand a)) ≠ 0 := hx
    rw [hx1, one_mul, dif_pos hx']
    by_cases hx_near : pcode.posX x ∈ ball3D y0 ((bdlGamma / 2) * (bdlLambda : ℝ))
    · exact (radialRaySum_outer_eq_subcylinderCoarseCochain_of_near B h_inv y0 hr0 hr_hi h hh_syn hh_supp x hx_near
        ⟨(x, projXq0ToBoundaryX0 pcode M (v0_cand a)),
          inLinkOfX_projXq0_of_checkX_ne_zero pcode M x (v0_cand a) hx⟩ rfl).symm
    · have hc_zero : subcylinderCoarseCochain B y0 h x = 0 := by
        dsimp [subcylinderCoarseCochain]
        rw [if_neg hx_near]
      have hx_in_SB : x ∈ S_B := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx, hx_near⟩
      have ha_not_BadRay : a ∉ BadRay x :=
        fun h_mem => ha_good (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, hx_in_SB, h_mem⟩))
      have h_ray_zero : radialRaySum pcode M h
          (mkOuterShellVertex pcode M ⟨(x, projXq0ToBoundaryX0 pcode M (v0_cand a)),
            inLinkOfX_projXq0_of_checkX_ne_zero pcode M x (v0_cand a) hx⟩) 0 = 0 := by
        by_contra h_ne
        exact ha_not_BadRay (Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨hx, h_ne⟩⟩)
      rw [hc_zero, h_ray_zero]
  · push_neg at hx
    have h_not : ¬ pcode.checkX x (xq0OwnerQ pcode M (v0_cand a)) ≠ 0 := not_not.mpr hx
    rw [hx, zero_mul, dif_neg h_not]

/-! ## 2. Primal and Dual Sub-Cylinder Filling and Scale-Up Inclusions -/

theorem bdlRandomStepX_dual_subcylinder_filling (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (y0 : Point3D) {r_0 : ℝ} (hr0 : 0 ≤ r_0) (hr_hi : r_0 ≤ 7015) :
    globalStabilizersInBall (dualCode (bdlRandomStepX B).code) y0 r_0 ⊆
      locallyGeneratedInBall (dualCode (bdlRandomStepX B).code) y0 (10005 * (bdlLambda : ℝ)) := by
  intro h ⟨hh_syn, hh_supp⟩
  let c := bdlLLLPerturbation B
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  let M := bdlSubdivPred
  let D_edge : ℝ := 2001 * (bdlLambda : ℝ)
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  have hD : HasCoarseEdgeBound pcode D_edge := by
    have hD_raw := hasCoarseEdgeBound_of_validLLLPerturbation B h_valid
    have h_eq : (2 * bdlAlpha + 1) * (bdlLambda : ℝ) = D_edge := by dsimp [D_edge, bdlAlpha, bdlAlphaNat]; ring
    rwa [h_eq] at hD_raw
  let c_apex := subcylinderCoarseCochain B y0 h
  have hc_supp : supp2 (dualCode pcode) c_apex ⊆ ball3D y0 (2 * D_edge) :=
    subcylinderCoarseCochain_supp2_subset B y0 h
  have hrR : r_0 + 2 * D_edge ≤ 3 * D_edge := by
    have hlam := bdlLambda_ge_10000
    dsimp [D_edge]
    linarith
  have hc_supp' : supp2 (dualCode pcode) c_apex ⊆ ball3D y0 (3 * D_edge) :=
    Set.Subset.trans hc_supp (ball3D_mono y0 (by positivity) (by linarith [hD.1]))
  have hc_eq := coarseProjCocycle_eq_checkGen_subcylinderCoarseCochain B h_inv y0 hr0 hr_hi h hh_syn hh_supp
  have h_supp2 := fullCylinderCocycle_supp2_subset pcode M hD y0 hr0 hrR h c_apex hh_supp hc_supp'
  have h_gen := checkGen_fullCylinderCocycle_global pcode M h_inv.1.2 h_inv.2.2.2.2.1 h_inv.2.2.2.1.2
    h c_apex hh_syn hc_eq
  refine ⟨fullCylinderCocycle pcode M h c_apex, ?_, h_gen⟩
  apply Set.Subset.trans h_supp2
  apply ball3D_mono y0 (by positivity)
  dsimp [D_edge]
  linarith [hD.1]

theorem bdlRandomStepZ_primal_subcylinder_filling (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (y0 : Point3D) {r_0 : ℝ} (hr0 : 0 ≤ r_0) (hr_hi : r_0 ≤ 7015) :
    globalStabilizersInBall (bdlRandomStepZ B).code y0 r_0 ⊆
      locallyGeneratedInBall (bdlRandomStepZ B).code y0 (10005 * (bdlLambda : ℝ)) :=
  bdlRandomStepX_dual_subcylinder_filling (dualBundled B)
    (hasBDLConeInvariants_dualBundled B h_inv) y0 hr0 hr_hi

theorem globalStabilizers_bdlRandomStepX_subset_scaleUp (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (x0 : Point3D) {r R_coarse : ℝ}
    (hr0 : 0 ≤ r) (hrR : r / (bdlLambda : ℝ) + 7003 ≤ R_coarse)
    (h_primal : globalStabilizersInBall B.code
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall B.code (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse) :
    globalStabilizersInBall (bdlRandomStepX B).code x0 r ⊆
      locallyGeneratedInBall (bdlRandomStepX B).code x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) := by
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
    have h_eq : (2 * bdlAlpha + 1) * (bdlLambda : ℝ) = D_edge := by dsimp [D_edge, bdlAlpha, bdlAlphaNat]; ring
    rwa [h_eq] at hD_raw
  have hcQ : ∀ q, distSq3D (c.1 q) (fun _ => 0) ≤ (bdlAlpha * (bdlLambda : ℝ)) ^ 2 :=
    fun q => le_of_eq (h_valid.1 q)
  have hcZ : ∀ mZ, distSq3D (c.2.1 mZ) (fun _ => 0) ≤ (bdlAlpha * (bdlLambda : ℝ)) ^ 2 :=
    fun mZ => le_of_eq (h_valid.2.1 mZ)
  have h_alpha_nonneg : (0 : ℝ) ≤ bdlAlpha := by dsimp [bdlAlpha, bdlAlphaNat]; norm_num
  have h_rad_p : (r + D_edge) / (bdlLambda : ℝ) + bdlAlpha ≤ r / (bdlLambda : ℝ) + 7003 := by
    dsimp [D_edge, bdlAlpha, bdlAlphaNat]; field_simp [hlam_ne]; linarith
  have h_p_coarse_sub : globalStabilizersInBall B.code
      (fun axis => x0 axis / (bdlLambda : ℝ)) ((r + D_edge) / (bdlLambda : ℝ) + bdlAlpha) ⊆
      locallyGeneratedInBall B.code (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse := by
    intro g ⟨hg_syn, hg_supp⟩
    apply h_primal
    refine ⟨hg_syn, Set.Subset.trans hg_supp (ball3D_mono _ ?_ h_rad_p)⟩
    have : 0 ≤ (r + D_edge) / (bdlLambda : ℝ) := div_nonneg (by linarith [hD.1]) (le_of_lt hlam_pos)
    linarith
  have h_p_perturb := bdlPerturbStep_globalStabilizers_step B.code bdlLambda bdlLambda_pos
    c.1 c.2.1 c.2.2 h_alpha_nonneg hcQ hcZ x0 (r := r + D_edge) (R_coarse := R_coarse)
    (by linarith [hD.1]) hR0 h_p_coarse_sub
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

theorem globalStabilizers_dual_bdlRandomStepZ_subset_scaleUp (B : BundledCSSCode3D)
    (h_inv : HasBDLConeInvariants B)
    (x0 : Point3D) {r R_coarse : ℝ}
    (hr0 : 0 ≤ r) (hrR : r / (bdlLambda : ℝ) + 7003 ≤ R_coarse)
    (h_dual : globalStabilizersInBall (dualCode B.code)
      (fun axis => x0 axis / (bdlLambda : ℝ)) (r / (bdlLambda : ℝ) + 7003) ⊆
      locallyGeneratedInBall (dualCode B.code) (fun axis => x0 axis / (bdlLambda : ℝ)) R_coarse) :
    globalStabilizersInBall (dualCode (bdlRandomStepZ B).code) x0 r ⊆
      locallyGeneratedInBall (dualCode (bdlRandomStepZ B).code) x0 ((bdlLambda : ℝ) * (R_coarse + 13006)) :=
  globalStabilizers_bdlRandomStepX_subset_scaleUp (dualBundled B)
    (hasBDLConeInvariants_dualBundled B h_inv) x0 hr0 hrR h_dual

/-! ## 3. Joint Base-Scale Sub-Cylinder Filling and Multi-Scale Cone Acyclicity -/

def bdlBaseFillingRadius : ℝ :=
  (bdlLambda : ℝ) * (10005 * (bdlLambda : ℝ) + 13006)

theorem bdlHalfStep_subcylinder_filling (j' : ℕ)
    (y0 : Point3D) {r_0 : ℝ} (hr0 : 0 ≤ r_0) (hr_hi : r_0 ≤ 7015) :
    globalStabilizersInBall (bdlHalfStep (j' + 2)).code y0 r_0 ⊆
      locallyGeneratedInBall (bdlHalfStep (j' + 2)).code y0 bdlBaseFillingRadius ∧
    globalStabilizersInBall (dualCode (bdlHalfStep (j' + 2)).code) y0 r_0 ⊆
      locallyGeneratedInBall (dualCode (bdlHalfStep (j' + 2)).code) y0 bdlBaseFillingRadius := by
  have hlam := bdlLambda_ge_10000
  have hlam_pos : (0 : ℝ) < (bdlLambda : ℝ) := by linarith
  have hr_coarse_nonneg : 0 ≤ r_0 / (bdlLambda : ℝ) + 7003 := by
    have : 0 ≤ r_0 / (bdlLambda : ℝ) := div_nonneg hr0 (le_of_lt hlam_pos)
    linarith
  have hr_coarse_hi : r_0 / (bdlLambda : ℝ) + 7003 ≤ 7015 := by
    have : r_0 / (bdlLambda : ℝ) ≤ 1 := (div_le_one hlam_pos).mpr (by linarith)
    linarith
  have hrR : r_0 / (bdlLambda : ℝ) + 7003 ≤ 10005 * (bdlLambda : ℝ) := by nlinarith
  have h_R0_le_Rbase : 10005 * (bdlLambda : ℝ) ≤ bdlBaseFillingRadius := by
    dsimp [bdlBaseFillingRadius]; nlinarith
  by_cases h_even : (j' + 1) % 2 = 0
  · have h_odd : j' % 2 ≠ 0 := by omega
    have h_step2 : bdlHalfStep (j' + 2) = bdlRandomStepX (bdlHalfStep (j' + 1)) := if_pos h_even
    have h_step1 : bdlHalfStep (j' + 1) = bdlRandomStepZ (bdlHalfStep j') := if_neg h_odd
    rw [h_step2]
    refine ⟨?_, ?_⟩
    · apply globalStabilizers_bdlRandomStepX_subset_scaleUp (bdlHalfStep (j' + 1))
        (hasBDLConeInvariants_bdlHalfStep (j' + 1)) y0 hr0 hrR
      rw [h_step1]
      exact bdlRandomStepZ_primal_subcylinder_filling (bdlHalfStep j')
        (hasBDLConeInvariants_bdlHalfStep j')
        (fun axis => y0 axis / (bdlLambda : ℝ)) hr_coarse_nonneg hr_coarse_hi
    · intro h hh
      obtain ⟨d2, hd2_supp, hd2_gen⟩ := bdlRandomStepX_dual_subcylinder_filling (bdlHalfStep (j' + 1))
        (hasBDLConeInvariants_bdlHalfStep (j' + 1)) y0 hr0 hr_hi hh
      exact ⟨d2, Set.Subset.trans hd2_supp (ball3D_mono y0 (by positivity) h_R0_le_Rbase), hd2_gen⟩
  · have h_even' : j' % 2 = 0 := by omega
    have h_step2 : bdlHalfStep (j' + 2) = bdlRandomStepZ (bdlHalfStep (j' + 1)) := if_neg h_even
    have h_step1 : bdlHalfStep (j' + 1) = bdlRandomStepX (bdlHalfStep j') := if_pos h_even'
    rw [h_step2]
    refine ⟨?_, ?_⟩
    · intro g hg
      obtain ⟨c2, hc2_supp, hc2_gen⟩ := bdlRandomStepZ_primal_subcylinder_filling (bdlHalfStep (j' + 1))
        (hasBDLConeInvariants_bdlHalfStep (j' + 1)) y0 hr0 hr_hi hg
      exact ⟨c2, Set.Subset.trans hc2_supp (ball3D_mono y0 (by positivity) h_R0_le_Rbase), hc2_gen⟩
    · apply globalStabilizers_dual_bdlRandomStepZ_subset_scaleUp (bdlHalfStep (j' + 1))
        (hasBDLConeInvariants_bdlHalfStep (j' + 1)) y0 hr0 hrR
      rw [h_step1]
      exact bdlRandomStepX_dual_subcylinder_filling (bdlHalfStep j')
        (hasBDLConeInvariants_bdlHalfStep j')
        (fun axis => y0 axis / (bdlLambda : ℝ)) hr_coarse_nonneg hr_coarse_hi

def bdlRandomLinearConstant : ℝ :=
  (bdlLambda : ℝ) * (bdlBaseFillingRadius + 13008)

theorem bdl_random_cone_acyclicity_extended (k : ℕ)
    (x0 : Point3D) {r_euc : ℝ}
    (hr1 : 1 ≤ r_euc) (hr_hi : r_euc ≤ 11 * ((bdlLambda : ℝ) ^ (2 * k))) :
    globalStabilizersInBall (bdlRandomCode k) x0 r_euc ⊆
      locallyGeneratedInBall (bdlRandomCode k) x0
        ((bdlRandomLinearConstant / 11) * r_euc + bdlBaseFillingRadius) ∧
    globalStabilizersInBall (dualCode (bdlRandomCode k)) x0 r_euc ⊆
      locallyGeneratedInBall (dualCode (bdlRandomCode k)) x0
        ((bdlRandomLinearConstant / 11) * r_euc + bdlBaseFillingRadius) := by
  have hlam := bdlLambda_ge_10000
  have hlam_ge2 : (2 : ℝ) ≤ (bdlLambda : ℝ) := by linarith
  have h_Rbase_ge : 7015 ≤ bdlBaseFillingRadius := by
    dsimp [bdlBaseFillingRadius]; nlinarith
  have h_Rbase_nonneg : 0 ≤ bdlBaseFillingRadius := by linarith
  have hr0 : 0 ≤ r_euc := by linarith
  have h_depth : ∃ m : ℕ, m ≤ 2 * k ∧
      r_euc / ((bdlLambda : ℝ) ^ m) ≤ 11 ∧
      scaleUpRadius m bdlBaseFillingRadius ≤
        (bdlRandomLinearConstant / 11) * r_euc + bdlBaseFillingRadius := by
    by_cases h_le11 : r_euc ≤ 11
    · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · rw [pow_zero, div_one]; exact h_le11
      · dsimp [scaleUpRadius]
        have : 0 ≤ (bdlRandomLinearConstant / 11) * r_euc := by
          dsimp [bdlRandomLinearConstant]; positivity
        linarith
    · push_neg at h_le11
      have h_div_lo : 1 ≤ r_euc / 11 := by linarith
      have h_div_hi : r_euc / 11 ≤ (bdlLambda : ℝ) ^ (2 * k) := by linarith
      obtain ⟨m, hm_le, hm_hi, hm_lo⟩ :=
        exists_truncation_depth hlam_ge2 (2 * k) (r_euc / 11) h_div_lo h_div_hi
      refine ⟨m, hm_le, ?_, ?_⟩
      · have h_pow_pos : (0 : ℝ) < (bdlLambda : ℝ) ^ m := by positivity
        rw [div_le_iff₀ h_pow_pos]
        linarith
      · have h_su := scaleUpRadius_bound m h_Rbase_nonneg
        dsimp [bdlRandomLinearConstant]
        nlinarith
  obtain ⟨m, hm_le, hm_div, h_su_bound⟩ := h_depth
  let j' := 2 * k - m
  have hj_add : (j' + 2) + m = 2 * (k + 1) := by omega
  have h_sd_nonneg : 0 ≤ scaleDownRadius m r_euc := scaleDownRadius_nonneg m hr0
  have h_sd_raw := scaleDownRadius_bound m hr0
  have h_sd_hi : scaleDownRadius m r_euc ≤ 7015 := by linarith
  have h_base := bdlHalfStep_subcylinder_filling j' (scaleDownCenter m x0) h_sd_nonneg h_sd_hi
  have h_iter := bdlHalfStep_iterated_globalStabilizers_step (j' + 2) m x0
    (r := r_euc) (R_base := bdlBaseFillingRadius) hr0 (le_trans h_sd_hi h_Rbase_ge)
    h_base.1 h_base.2
  have h_su_nonneg : 0 ≤ scaleUpRadius m bdlBaseFillingRadius :=
    le_trans hr0 (scaleDownRadius_le_scaleUpRadius m hr0 (le_trans h_sd_hi h_Rbase_ge))
  have h_code_eq : bdlHalfStep ((j' + 2) + m) = bdlRandomBundled k :=
    (congr_arg bdlHalfStep hj_add).trans (bdlHalfStep_eq_bdlRandomBundled k)
  rw [h_code_eq] at h_iter
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨c2, hc2_supp, hc2_gen⟩ := h_iter.1 hg
    exact ⟨c2, Set.Subset.trans hc2_supp (ball3D_mono x0 h_su_nonneg h_su_bound), hc2_gen⟩
  · intro g hg
    obtain ⟨c2, hc2_supp, hc2_gen⟩ := h_iter.2 hg
    exact ⟨c2, Set.Subset.trans hc2_supp (ball3D_mono x0 h_su_nonneg h_su_bound), hc2_gen⟩

/-! ## 4. $\ell_\infty$ to Euclidean Ball Conversion for `bdlWeldedCode k` -/

lemma mem_ball3D_of_distInf3D_le (p x0 : Point3D) {r : ℝ} (hr0 : 0 ≤ r)
    (h_inf : distInf3D p x0 ≤ r) :
    p ∈ ball3D x0 (2 * r + 1) := by
  dsimp [distInf3D] at h_inf
  have h01 : max |p 0 - x0 0| |p 1 - x0 1| ≤ r := le_trans (le_max_left _ _) h_inf
  have h0 : |p 0 - x0 0| ≤ r := le_trans (le_max_left _ _) h01
  have h1 : |p 1 - x0 1| ≤ r := le_trans (le_max_right _ _) h01
  have h2 : |p 2 - x0 2| ≤ r := le_trans (le_max_right _ _) h_inf
  have h0_bounds := abs_le.mp h0
  have h1_bounds := abs_le.mp h1
  have h2_bounds := abs_le.mp h2
  dsimp [ball3D, distSq3D]
  nlinarith

lemma distInf3D_le_of_mem_ball3D (p x0 : Point3D) {R : ℝ} (hR0 : 0 ≤ R)
    (h_euc : p ∈ ball3D x0 R) :
    distInf3D p x0 ≤ R := by
  dsimp [ball3D, distSq3D] at h_euc
  have h_axis : ∀ i : Fin 3, |p i - x0 i| ≤ R := by
    intro i
    have h_sq : (p i - x0 i) ^ 2 ≤ R ^ 2 := by
      fin_cases i <;> dsimp <;>
        nlinarith [sq_nonneg (p 0 - x0 0), sq_nonneg (p 1 - x0 1), sq_nonneg (p 2 - x0 2)]
    have h_abs_sq : |p i - x0 i| ^ 2 ≤ R ^ 2 := by rwa [sq_abs]
    nlinarith [abs_nonneg (p i - x0 i)]
  dsimp [distInf3D]
  exact max_le (max_le (h_axis 0) (h_axis 1)) (h_axis 2)

theorem bdlWeldedCode_inf_cone_acyclicity (k : ℕ) (x0 : Point3D) {r_inf : ℝ}
    (hr0 : 0 ≤ r_inf) (hr_hi : r_inf ≤ (bdlLambda : ℝ) ^ (2 * k) + 2) :
    (∀ z1 : BDLWeldedQubit k → ZMod 2,
      syndrome (bdlWeldedCode k) z1 = 0 →
      (∀ q, z1 q ≠ 0 → q ∈ ballQ (bdlWeldedCode k) x0 r_inf) →
      ∃ c2 : BDLWeldedCheckZ k → ZMod 2,
        checkGen (bdlWeldedCode k) c2 = z1 ∧
        (∀ mZ, c2 mZ ≠ 0 → mZ ∈ ballMZ (bdlWeldedCode k) x0
          ((bdlRandomLinearConstant / 11) * (2 * r_inf + 1) + bdlBaseFillingRadius))) ∧
    (∀ b1 : BDLWeldedQubit k → ZMod 2,
      syndrome (dualCode (bdlWeldedCode k)) b1 = 0 →
      (∀ q, b1 q ≠ 0 → q ∈ ballQ (bdlWeldedCode k) x0 r_inf) →
      ∃ d2 : BDLWeldedCheckX k → ZMod 2,
        checkGen (dualCode (bdlWeldedCode k)) d2 = b1 ∧
        (∀ mX, d2 mX ≠ 0 → mX ∈ ballMX (bdlWeldedCode k) x0
          ((bdlRandomLinearConstant / 11) * (2 * r_inf + 1) + bdlBaseFillingRadius))) := by
  let r_euc : ℝ := 2 * r_inf + 1
  have hr_euc1 : 1 ≤ r_euc := by dsimp [r_euc]; linarith
  have h_pow_ge1 : (1 : ℝ) ≤ (bdlLambda : ℝ) ^ (2 * k) :=
    one_le_pow₀ (by have := bdlLambda_ge_10000; linarith)
  have hr_euc_hi : r_euc ≤ 11 * ((bdlLambda : ℝ) ^ (2 * k)) := by
    dsimp [r_euc]; linarith
  have h_ext := bdl_random_cone_acyclicity_extended k x0 hr_euc1 hr_euc_hi
  have h_lin_nonneg : 0 ≤ (bdlRandomLinearConstant / 11) * r_euc + bdlBaseFillingRadius := by
    have : 0 ≤ bdlRandomLinearConstant := by
      dsimp [bdlRandomLinearConstant, bdlBaseFillingRadius]
      have := bdlLambda_pos
      positivity
    have : 0 ≤ bdlBaseFillingRadius := by
      dsimp [bdlBaseFillingRadius]
      have := bdlLambda_pos
      positivity
    nlinarith
  refine ⟨?_, ?_⟩
  · intro z1 h_syn h_supp
    have hz1_mem : z1 ∈ globalStabilizersInBall (bdlRandomCode k) x0 r_euc := by
      refine ⟨h_syn, ?_⟩
      intro p ⟨q, hq_ne, hp⟩
      subst hp
      exact mem_ball3D_of_distInf3D_le _ x0 hr0 (h_supp q hq_ne)
    obtain ⟨c2, hc2_supp, hc2_gen⟩ := h_ext.1 hz1_mem
    refine ⟨c2, hc2_gen, ?_⟩
    intro mZ hmZ_ne
    have h_in_euc : (bdlRandomCode k).posZ mZ ∈
        ball3D x0 ((bdlRandomLinearConstant / 11) * r_euc + bdlBaseFillingRadius) :=
      hc2_supp ⟨mZ, hmZ_ne, rfl⟩
    exact distInf3D_le_of_mem_ball3D _ x0 h_lin_nonneg h_in_euc
  · intro b1 h_syn h_supp
    have hb1_mem : b1 ∈ globalStabilizersInBall (dualCode (bdlRandomCode k)) x0 r_euc := by
      refine ⟨h_syn, ?_⟩
      intro p ⟨q, hq_ne, hp⟩
      subst hp
      exact mem_ball3D_of_distInf3D_le _ x0 hr0 (h_supp q hq_ne)
    obtain ⟨d2, hd2_supp, hd2_gen⟩ := h_ext.2 hb1_mem
    refine ⟨d2, hd2_gen, ?_⟩
    intro mX hmX_ne
    have h_in_euc : (dualCode (bdlRandomCode k)).posZ mX ∈
        ball3D x0 ((bdlRandomLinearConstant / 11) * r_euc + bdlBaseFillingRadius) :=
      hd2_supp ⟨mX, hmX_ne, rfl⟩
    exact distInf3D_le_of_mem_ball3D _ x0 h_lin_nonneg h_in_euc

end WeldedHierarchy
