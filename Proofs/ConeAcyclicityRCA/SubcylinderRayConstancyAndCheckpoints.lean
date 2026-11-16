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

import Proofs.ConeAcyclicityRCA.DualConeAcyclicityTransfer

/-!
# Sub-Cylinder Ray-Sum Constancy and Six-Checkpoint Shell Disjointness

Defines the truncated sub-cylinder coarse cochain subcylinderCoarseCochain at shell index j, proves outer radial ray-sum constancy for cylinders near a small ball (radialRaySum_outer_eq_subcylinderCoarseCochain_of_near) and star-interface coboundary vanishing outside the ball (checkGen_dual_apexRadialCocycle_inr_zero), and establishes pairwise Euclidean ball disjointness across the six checkpoint shells subcylinderCandidateJ (not_both_mem_ball3D_of_subcylinderCandidateJ).

## References

* Part I, Section 3.3 (`subsec:scale-matched-rca`), Lemma 3.8 (`lem:clean-shell-subcylinder`)
* Part II, Section 4 (`subsec:welded-hierarchy-cleaner`), Proposition 4.3 (`prop:rca-hierarchy`)
-/

noncomputable section
open scoped Classical
open BigOperators
namespace WeldedHierarchy

/-! ## 1. Sub-Cylinder Coarse Cochain and Near-Apex Ray-Sum Constancy -/

noncomputable def subcylinderCoarseCochain (B : BundledCSSCode3D)
    (y0 : Point3D)
    (h : BDLStepXQ (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred → ZMod 2)
    (x : B.M_X) : ZMod 2 :=
  let c := bdlLLLPerturbation B
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  if _ : pcode.posX x ∈ ball3D y0 ((bdlGamma / 2) * (bdlLambda : ℝ)) then
    if hex : ∃ q : B.Q, pcode.checkX x q ≠ 0 then
      radialRaySum pcode bdlSubdivPred h
        (mkOuterShellVertex pcode bdlSubdivPred ⟨(x, Sum.inl (Classical.choose hex)), Classical.choose_spec hex⟩) 0
    else 0
  else 0

lemma zmod2_eq_one_of_ne_zero (a : ZMod 2) (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (h rfl)
  · rfl

lemma subcylinderCoarseCochain_supp2_subset (B : BundledCSSCode3D)
    (y0 : Point3D)
    (h : BDLStepXQ (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred → ZMod 2) :
    let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
    supp2 (dualCode pcode) (subcylinderCoarseCochain B y0 h) ⊆
      ball3D y0 (2 * (2001 * (bdlLambda : ℝ))) := by
  intro pcode p ⟨x, hx_ne, hp⟩; subst hp
  dsimp [subcylinderCoarseCochain] at hx_ne
  split_ifs at hx_ne with hx_in hex
  · change pcode.posX x ∈ ball3D y0 (2 * (2001 * (bdlLambda : ℝ)))
    refine ball3D_mono y0 ?_ ?_ hx_in
    · have := bdlGamma_ge_seven_fifths
      have := bdlLambda_pos
      positivity
    · have h1 := bdlGamma_le_five_halves
      have h2 : (0 : ℝ) ≤ (bdlLambda : ℝ) := by positivity
      nlinarith
  · exact False.elim (hx_ne rfl)
  · exact False.elim (hx_ne rfl)

lemma radialRaySum_outer_eq_subcylinderCoarseCochain_of_near (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (y0 : Point3D) {r_0 : ℝ} (hr0 : 0 ≤ r_0) (_hr_hi : r_0 ≤ 7015)
    (h : BDLStepXQ (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred → ZMod 2)
    (hh_syn : syndrome (dualCode (bdlRandomStepX B).code) h = 0)
    (hh_supp : supp1 (dualCode (bdlRandomStepX B).code) h ⊆ ball3D y0 r_0)
    (x : B.M_X)
    (hx_near : (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posX x ∈
      ball3D y0 ((bdlGamma / 2) * (bdlLambda : ℝ)))
    (xv : BoundaryX0Link (bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2) bdlSubdivPred)
    (hxv : xv.val.1 = x) :
    let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
    radialRaySum pcode bdlSubdivPred h (mkOuterShellVertex pcode bdlSubdivPred xv) 0 =
      subcylinderCoarseCochain B y0 h x := by
  intro pcode
  let M := bdlSubdivPred
  have h_syn_at : ∀ mZ, syndrome (dualCode (bdlCylinderStepX pcode M)) h mZ = 0 :=
    fun mZ => congr_fun hh_syn mZ
  have h_seg_step : ∀ (s : ActiveZLink pcode) (hs : s.val.1 = x) (k' : Fin (M + 1)),
      radialRaySum pcode M h (mkOuterShellVertex pcode M (bxStartLink pcode M s k')) 0 =
      radialRaySum pcode M h (mkOuterShellVertex pcode M (bxEndLink pcode M s k')) 0 := by
    intro s hs k'
    let seg := mkOuterShellSegment pcode M s k'
    have h_az0 : apexResidualCocycle pcode M h (Sum.inl (Sum.inr (Sum.inl (seg, 0)))) = 0 :=
      h1_azimuthal_eq_zero pcode M h_inv.1.2 h x 0 (fun seg' _ => h_syn_at _) seg hs
    have h_seg_h_zero : h (Sum.inl (Sum.inr (Sum.inl (seg, 0)))) = 0 := by
      by_contra h_ne
      have h_in := hh_supp ⟨Sum.inl (Sum.inr (Sum.inl (seg, 0))), h_ne, rfl⟩
      change (bdlCylinderStepX pcode M).posQ (Sum.inl (Sum.inr (Sum.inl (seg, 0)))) ∈ ball3D y0 r_0 at h_in
      have h_pos_eq : (bdlCylinderStepX pcode M).posQ (Sum.inl (Sum.inr (Sum.inl (seg, 0)))) =
          boundaryX0Pos pcode M (bxEndLink pcode M s k').val.2 := by
        change shellVertexPos pcode M (shellSegEndVertex pcode M seg) = _
        rw [shellSegEndVertex_outer pcode M s k', shellVertexPos_outer_eq]
      rw [h_pos_eq] at h_in
      have h_sep := distSq3D_posX_boundaryX0Pos_ge B h_inv x (bxEndLink pcode M s k').val.2
        (hs ▸ (bxEndLink pcode M s k').property)
      have h_not_in := not_mem_ball3D_of_near_and_sep y0 (pcode.posX x)
        (boundaryX0Pos pcode M (bxEndLink pcode M s k').val.2)
        hr0 (by have := bdlGamma_half_mul_bdlLambda_ge; linarith)
        (by have := bdlGamma_half_mul_bdlLambda_ge; linarith) hx_near h_sep
      exact h_not_in h_in
    change h (Sum.inl (Sum.inr (Sum.inl (seg, 0)))) +
      checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h)
        (Sum.inl (Sum.inr (Sum.inl (seg, 0)))) = 0 at h_az0
    rw [h_seg_h_zero, zero_add] at h_az0
    dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex] at h_az0
    dsimp [bdlStepXCheckX, bdlDeltaX0] at h_az0
    simp_rw [add_mul, Finset.sum_add_distrib] at h_az0
    rw [Finset.sum_eq_single (Sum.inr (shellSegStartVertex pcode M seg, 0))] at h_az0
    · rw [Finset.sum_eq_single (Sum.inr (shellSegEndVertex pcode M seg, 0))] at h_az0
      · rw [if_pos rfl, if_pos rfl, one_mul, one_mul,
            shellSegStartVertex_outer pcode M s k', shellSegEndVertex_outer pcode M s k'] at h_az0
        dsimp [apexRadialCocycle] at h_az0
        have h2 := zmod2_add_self (radialRaySum pcode M h (mkOuterShellVertex pcode M (bxEndLink pcode M s k')) 0)
        linear_combination h_az0 - h2
      · intro _ _ hne; rw [if_neg hne, zero_mul]
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    · intro _ _ hne; rw [if_neg hne, zero_mul]
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  have h_arm_ind : ∀ (s : ActiveZLink pcode) (hs : s.val.1 = x) (n : ℕ) (hn : n < M + 1),
      radialRaySum pcode M h (mkOuterShellVertex pcode M (bxStartLink pcode M s ⟨n, hn⟩)) 0 =
        radialRaySum pcode M h (mkOuterShellVertex pcode M (bxStartLink pcode M s 0)) 0 ∧
      radialRaySum pcode M h (mkOuterShellVertex pcode M (bxEndLink pcode M s ⟨n, hn⟩)) 0 =
        radialRaySum pcode M h (mkOuterShellVertex pcode M (bxStartLink pcode M s 0)) 0 := by
    intro s hs n
    induction n with
    | zero =>
      intro hn
      have h0 : (⟨0, hn⟩ : Fin (M + 1)) = 0 := rfl
      rw [h0]
      exact ⟨rfl, (h_seg_step s hs 0).symm⟩
    | succ m ih =>
      intro hm
      have hm' : m < M + 1 := Nat.lt_of_succ_lt hm
      have h_link : bxStartLink pcode M s ⟨m + 1, hm⟩ = bxEndLink pcode M s ⟨m, hm'⟩ := by
        apply Subtype.ext; apply Prod.ext
        · rfl
        · dsimp [bxStartLink, bxEndLink, bxStart, bxEnd, armStart, armEnd, projXq0ToBoundaryX0]
          have h_lt : m < M := Nat.lt_of_succ_lt_succ hm
          rw [dif_pos h_lt]
      have h_start : radialRaySum pcode M h (mkOuterShellVertex pcode M (bxStartLink pcode M s ⟨m + 1, hm⟩)) 0 =
          radialRaySum pcode M h (mkOuterShellVertex pcode M (bxStartLink pcode M s 0)) 0 := by
        rw [h_link, (ih hm').2]
      exact ⟨h_start, (h_seg_step s hs ⟨m + 1, hm⟩).symm.trans h_start⟩
  have h_arm_z : ∀ (q : B.Q) (z : B.M_Z) (hq : pcode.checkX x q ≠ 0) (hz : pcode.checkZ z q ≠ 0),
      radialRaySum pcode M h (mkOuterShellVertex pcode M ⟨(x, Sum.inr (Sum.inr z)), ⟨q, hq, hz⟩⟩) 0 =
      radialRaySum pcode M h (mkOuterShellVertex pcode M ⟨(x, Sum.inl q), hq⟩) 0 := by
    intro q z hq hz
    let s : ActiveZLink pcode := ⟨(x, ⟨(q, z), hz⟩), hq⟩
    have h_end := (h_arm_ind s rfl M (Nat.lt_succ_self M)).2
    have h_l1 : bxEndLink pcode M s ⟨M, Nat.lt_succ_self M⟩ = ⟨(x, Sum.inr (Sum.inr z)), ⟨q, hq, hz⟩⟩ := by
      apply Subtype.ext; apply Prod.ext
      · rfl
      · dsimp [bxEndLink, bxEnd, armEnd, projXq0ToBoundaryX0]
    have h_l0 : bxStartLink pcode M s 0 = ⟨(x, Sum.inl q), hq⟩ := rfl
    rw [← h_l1, h_end, h_l0]
  have h_rel : ∀ (q1 q2 : B.Q) (hq1 : pcode.checkX x q1 ≠ 0) (hq2 : pcode.checkX x q2 ≠ 0),
      Relation.ReflTransGen
        (fun a b : B.Q => pcode.checkX x a ≠ 0 ∧ pcode.checkX x b ≠ 0 ∧
          ∃ z : B.M_Z, pcode.checkZ z a ≠ 0 ∧ pcode.checkZ z b ≠ 0)
        q1 q2 →
      radialRaySum pcode M h (mkOuterShellVertex pcode M ⟨(x, Sum.inl q1), hq1⟩) 0 =
      radialRaySum pcode M h (mkOuterShellVertex pcode M ⟨(x, Sum.inl q2), hq2⟩) 0 := by
    intro q1 q2 hq1 hq2 h_path
    induction h_path with
    | refl => rfl
    | tail _ h_step ih =>
      rcases h_step with ⟨ha, hb, z, hza, hzb⟩
      have h1 := h_arm_z _ z ha hza
      have h2 := h_arm_z _ z hb hzb
      have h_sub : (⟨(x, Sum.inr (Sum.inr z)), ⟨_, ha, hza⟩⟩ : BoundaryX0Link pcode M) =
          ⟨(x, Sum.inr (Sum.inr z)), ⟨_, hb, hzb⟩⟩ := Subtype.ext rfl
      rw [h_sub] at h1
      exact (ih ha).trans (h1.symm.trans h2)
  have h_q_eq : ∀ (q : B.Q) (hq : pcode.checkX x q ≠ 0),
      radialRaySum pcode M h (mkOuterShellVertex pcode M ⟨(x, Sum.inl q), hq⟩) 0 =
      subcylinderCoarseCochain B y0 h x := by
    intro q hq
    have hex : ∃ q' : B.Q, pcode.checkX x q' ≠ 0 := ⟨q, hq⟩
    dsimp [subcylinderCoarseCochain]
    rw [if_pos hx_near, dif_pos hex]
    exact h_rel q (Classical.choose hex) hq (Classical.choose_spec hex)
      (h_inv.2.2.2.2.1 x q (Classical.choose hex) hq (Classical.choose_spec hex))
  rcases xv with ⟨⟨x', v⟩, hp⟩
  (try dsimp at hxv)
  subst hxv
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · exact h_q_eq q hp
  · let s : ActiveZLink pcode := ⟨(x', eZ), hp⟩
    have h_j := (h_arm_ind s rfl (j.val + 1) (Nat.succ_lt_succ j.isLt)).1
    have h_lj : bxStartLink pcode M s ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ =
        ⟨(x', Sum.inr (Sum.inl (eZ, j))), hp⟩ := by
      apply Subtype.ext; apply Prod.ext
      · rfl
      · dsimp [bxStartLink, bxStart, armStart, projXq0ToBoundaryX0]
    have h_l0 : bxStartLink pcode M s 0 = ⟨(x', Sum.inl eZ.val.1), hp⟩ := rfl
    rw [← h_lj, h_j, h_l0]
    exact h_q_eq eZ.val.1 hp
  · rcases hp with ⟨q, hq, hz⟩
    rw [h_arm_z q z hq hz]
    exact h_q_eq q hq

/-! ## 2. Star-Qubit Coboundary Cancellation for `apexRadialCocycle` -/

lemma checkGen_dual_apexRadialCocycle_inr_zero {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (h : BDLStepXQ pcode M → ZMod 2) (v0 : Xq0 pcode M) :
    checkGen (dualCode (bdlCylinderStepX pcode M)) (apexRadialCocycle pcode M h) (Sum.inr (v0, 0)) =
      ∑ x : M_X,
        if hx : pcode.checkX x (xq0OwnerQ pcode M v0) ≠ 0 then
          radialRaySum pcode M h
            (mkOuterShellVertex pcode M ⟨(x, projXq0ToBoundaryX0 pcode M v0),
              inLinkOfX_projXq0_of_checkX_ne_zero pcode M x v0 hx⟩) 0
        else 0 := by
  dsimp [checkGen, dualCode, bdlCylinderStepX, f2CheckGen, f2Syndrome, dualF2ChainComplex]
  dsimp [bdlStepXCheckX]
  rw [Fintype.sum_sum_type]
  have h_inl : (∑ x : M_X × Fin 3, bdlGXQ0 pcode M (Sum.inl x) (v0, 0) *
      apexRadialCocycle pcode M h (Sum.inl x)) = 0 :=
    Finset.sum_eq_zero (fun _ _ => by dsimp [bdlGXQ0]; simp)
  rw [h_inl, zero_add, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single (0 : Fin 3)]
  · rw [sum_shellVertex_eq pcode M (fun sv => bdlGXQ0 pcode M (Sum.inr (sv, 0)) (v0, 0) *
        apexRadialCocycle pcode M h (Sum.inr (sv, 0)))]
    have h_inner : ∀ xv : BoundaryX0Link pcode M,
        (∑ r : Fin (M + 1),
          if hr : InShellR pcode M xv r then
            bdlGXQ0 pcode M (Sum.inr (⟨(xv, r), hr⟩, 0)) (v0, 0) *
              apexRadialCocycle pcode M h (Sum.inr (⟨(xv, r), hr⟩, 0))
          else 0) =
        if xv.val.2 = projXq0ToBoundaryX0 pcode M v0 then
          pcode.checkX xv.val.1 (xq0OwnerQ pcode M v0) *
            radialRaySum pcode M h (mkOuterShellVertex pcode M xv) 0
        else 0 := by
      intro xv
      rw [Finset.sum_eq_single (Fin.last M)]
      · rw [dif_pos (inShellR_last pcode M xv)]
        dsimp [bdlGXQ0, apexRadialCocycle, mkOuterShellVertex]
        by_cases hv : xv.val.2 = projXq0ToBoundaryX0 pcode M v0
        · rw [if_pos ⟨rfl, hv, rfl⟩, if_pos hv]
        · have hc : ¬ (Fin.last M = Fin.last M ∧ xv.val.2 = projXq0ToBoundaryX0 pcode M v0 ∧ (0 : Fin 3) = 0) :=
            fun h => hv h.2.1
          rw [if_neg hc, if_neg hv, zero_mul]
      · intro r _ hne
        split_ifs with h_in
        · dsimp [bdlGXQ0]
          have hc : ¬ (r = Fin.last M ∧ xv.val.2 = projXq0ToBoundaryX0 pcode M v0 ∧ (0 : Fin 3) = 0) :=
            fun h => hne h.1
          rw [if_neg hc, zero_mul]
        · rfl
      · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
    simp_rw [h_inner]
    let f : M_X × BoundaryX0 pcode M → ZMod 2 := fun p =>
      if hlink : InLinkOfX pcode M p.1 p.2 then
        if p.2 = projXq0ToBoundaryX0 pcode M v0 then
          pcode.checkX p.1 (xq0OwnerQ pcode M v0) *
            radialRaySum pcode M h (mkOuterShellVertex pcode M ⟨p, hlink⟩) 0
        else 0
      else 0
    have h_sub : (∑ xv : BoundaryX0Link pcode M,
        if xv.val.2 = projXq0ToBoundaryX0 pcode M v0 then
          pcode.checkX xv.val.1 (xq0OwnerQ pcode M v0) *
            radialRaySum pcode M h (mkOuterShellVertex pcode M xv) 0
        else 0) = ∑ p : M_X × BoundaryX0 pcode M, f p := by
      have h_filt : (∑ p : M_X × BoundaryX0 pcode M, f p) =
          ∑ p ∈ Finset.univ.filter (fun p : M_X × BoundaryX0 pcode M => InLinkOfX pcode M p.1 p.2), f p := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro p _
        by_cases hp : InLinkOfX pcode M p.1 p.2
        · rw [if_pos hp]
        · rw [if_neg hp]; dsimp [f]; rw [dif_neg hp]
      rw [h_filt]
      refine Finset.sum_bij (fun (xv : BoundaryX0Link pcode M) _ => xv.val)
        (fun xv _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, xv.property⟩)
        (fun xv1 _ xv2 _ h_eq => Subtype.ext h_eq)
        (fun p hp => ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩)
        (fun xv _ => by dsimp [f]; rw [dif_pos xv.property])
    rw [h_sub, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single (projXq0ToBoundaryX0 pcode M v0)]
    · dsimp [f]
      by_cases hx : pcode.checkX x (xq0OwnerQ pcode M v0) ≠ 0
      · have hlink := inLinkOfX_projXq0_of_checkX_ne_zero pcode M x v0 hx
        have hx1 : pcode.checkX x (xq0OwnerQ pcode M v0) = 1 :=
          zmod2_eq_one_of_ne_zero _ hx
        rw [dif_pos hlink, if_pos rfl, dif_pos hx, hx1, one_mul]
      · push_neg at hx
        rw [dif_neg (not_not.mpr hx)]
        split_ifs <;> simp [hx]
    · intro v _ hne
      dsimp [f]
      split_ifs <;> rfl
    · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))
  · intro b _ hne
    apply Finset.sum_eq_zero
    intro sv _
    dsimp [bdlGXQ0]
    have hc : ¬ (sv.val.2 = Fin.last M ∧ sv.val.1.val.2 = projXq0ToBoundaryX0 pcode M v0 ∧ b = 0) :=
      fun h => hne h.2.2
    rw [if_neg hc, zero_mul]
  · intro h_abs; exact False.elim (h_abs (Finset.mem_univ _))

/-! ## 3. Six Candidate Shells (`subcylinderCandidateJ`) and Ball Disjointness -/

def subcylinderCandidateJ (a : Fin 6) : Fin bdlSubdivPred :=
  ⟨(a.val + 1) * 50000000, by
    have ha := a.isLt
    dsimp [bdlSubdivPred, bdlSubdivM, bdlSubdivFactor, bdlAlphaNat, bdlLambda]
    omega⟩

lemma subcylinderCandidateJ_le_300000000 (a : Fin 6) :
    (subcylinderCandidateJ a).val ≤ 300000000 := by
  have ha := a.isLt
  dsimp [subcylinderCandidateJ]
  omega

lemma not_both_mem_ball3D_of_subcylinderCandidateJ (B : BundledCSSCode3D) (h_inv : HasBDLConeInvariants B)
    (y0 : Point3D) {r_0 : ℝ} (hr0 : 0 ≤ r_0) (hr_hi : r_0 ≤ 7015)
    (x : B.M_X) (q0 : B.Q) (z0 : B.M_Z)
    (hxq : B.code.checkX x q0 ≠ 0) (hzq : B.code.checkZ z0 q0 ≠ 0)
    (a b : Fin 6) (hab : a ≠ b)
    (u1 u2 : ℕ)
    (hu1 : (subcylinderCandidateJ a).val + 1 ≤ u1)
    (hu2 : (subcylinderCandidateJ b).val + 1 ≤ u2)
    (h1 : triGridPos3D
      ((bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posX x)
      ((bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posQ q0)
      ((bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posZ z0)
      (bdlSubdivPred + 1) u1 ((subcylinderCandidateJ a).val + 1) ∈ ball3D y0 r_0)
    (h2 : triGridPos3D
      ((bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posX x)
      ((bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posQ q0)
      ((bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2).posZ z0)
      (bdlSubdivPred + 1) u2 ((subcylinderCandidateJ b).val + 1) ∈ ball3D y0 r_0) :
    False := by
  let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
  have h_valid := validLLLSphericalCapPerturbation_of_invariants B h_inv
  let s : ActiveSimplex2 B.code := ⟨(x, (q0, z0)), ⟨hxq, hzq⟩⟩
  have h_alt := h_valid.2.2.2.2.2.1 s
  have hL_nonneg : 0 ≤ bdlGamma * (bdlLambda : ℝ) := by
    have := bdlGamma_ge_seven_fifths
    have := bdlLambda_pos
    positivity
  have h_upper := distSq3D_le_add_sq_of_mem_ball3D y0 _ _ hr0 hr0 h1 h2
  have h_upper_num : distSq3D
      (triGridPos3D (pcode.posX x) (pcode.posQ q0) (pcode.posZ z0) (bdlSubdivPred + 1) u1 ((subcylinderCandidateJ a).val + 1))
      (triGridPos3D (pcode.posX x) (pcode.posQ q0) (pcode.posZ z0) (bdlSubdivPred + 1) u2 ((subcylinderCandidateJ b).val + 1)) ≤
      14030 ^ 2 := by
    calc _ ≤ (r_0 + r_0) ^ 2 := h_upper
      _ ≤ 14030 ^ 2 := by nlinarith
  have h_sep_lt : ∀ (c d : Fin 6) (u_c u_d : ℕ),
      c.val < d.val →
      (subcylinderCandidateJ c).val + 1 ≤ u_c →
      (subcylinderCandidateJ d).val + 1 ≤ u_d →
      17490 ^ 2 ≤ distSq3D
        (triGridPos3D (pcode.posX x) (pcode.posQ q0) (pcode.posZ z0) (bdlSubdivPred + 1) u_d ((subcylinderCandidateJ d).val + 1))
        (triGridPos3D (pcode.posX x) (pcode.posQ q0) (pcode.posZ z0) (bdlSubdivPred + 1) u_c ((subcylinderCandidateJ c).val + 1)) := by
    intro c d u_c u_d hcd huc hud
    have h_v_lt : (subcylinderCandidateJ c).val + 1 < (subcylinderCandidateJ d).val + 1 := by
      dsimp [subcylinderCandidateJ]; omega
    have h_ray := triGridPos3D_ray_separation (pcode.posX x) (pcode.posQ q0) (pcode.posZ z0)
      (bdlSubdivPred + 1) u_d ((subcylinderCandidateJ d).val + 1) u_c ((subcylinderCandidateJ c).val + 1)
      (Nat.succ_pos _) hL_nonneg hud huc h_v_lt h_alt
    have h_diff_ge : (50000000 : ℝ) ≤ (((subcylinderCandidateJ d).val + 1 : ℕ) : ℝ) - (((subcylinderCandidateJ c).val + 1 : ℕ) : ℝ) := by
      have h_nat : 50000000 + ((subcylinderCandidateJ c).val + 1) ≤ (subcylinderCandidateJ d).val + 1 := by
        dsimp [subcylinderCandidateJ]; omega
      have h_cast : ((50000000 + ((subcylinderCandidateJ c).val + 1) : ℕ) : ℝ) ≤ (((subcylinderCandidateJ d).val + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr h_nat
      push_cast at h_cast ⊢
      linarith
    have hm_eq : ((bdlSubdivPred + 1 : ℕ) : ℝ) = 4002 * (bdlLambda : ℝ) := by
      rw [bdlSubdivM_eq_succ]
      dsimp [bdlSubdivM, bdlSubdivFactor, bdlAlphaNat]
      push_cast
      ring
    have h_ratio : (17490 : ℝ) ≤
        (((((subcylinderCandidateJ d).val + 1 : ℕ) : ℝ) - (((subcylinderCandidateJ c).val + 1 : ℕ) : ℝ)) /
          ((bdlSubdivPred + 1 : ℕ) : ℝ)) * (bdlGamma * (bdlLambda : ℝ)) := by
      rw [hm_eq]
      have hlam_ne : (bdlLambda : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr bdlLambda_pos)
      have h_id : ((((subcylinderCandidateJ d).val + 1 : ℕ) : ℝ) - (((subcylinderCandidateJ c).val + 1 : ℕ) : ℝ)) /
          (4002 * (bdlLambda : ℝ)) * (bdlGamma * (bdlLambda : ℝ)) =
          (((((subcylinderCandidateJ d).val + 1 : ℕ) : ℝ) - (((subcylinderCandidateJ c).val + 1 : ℕ) : ℝ)) / 4002) * bdlGamma := by
        field_simp [hlam_ne]
      rw [h_id]
      have hg := bdlGamma_ge_seven_fifths
      nlinarith
    have h_sq : (17490 : ℝ) ^ 2 ≤
        (((((subcylinderCandidateJ d).val + 1 : ℕ) : ℝ) - (((subcylinderCandidateJ c).val + 1 : ℕ) : ℝ)) /
          ((bdlSubdivPred + 1 : ℕ) : ℝ) * (bdlGamma * (bdlLambda : ℝ))) ^ 2 := by
      nlinarith
    exact le_trans h_sq h_ray
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h_ab | h_ba
  · have h_low := h_sep_lt a b u1 u2 h_ab hu1 hu2
    rw [distSq3D_comm] at h_low
    linarith
  · have h_low := h_sep_lt b a u2 u1 h_ba hu2 hu1
    linarith

end WeldedHierarchy
