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

import Proofs.Step1LLLDensity.SubdivisionPointGrid

/-!
# Cylinder Welding Euclidean Locality and Inductive Interaction Range 8

Proves Euclidean locality of every non-zero check-qubit incidence in `bdlCylinderStepX` (`bdlCylinderStepX_interaction_locality`) and bounds the coordinate shift of `bdlLLLPerturbation` (`bdlLLLPerturbation_abs_le`). Defines `HasInteractionRange8` and proves by induction across `(bdlStepZ ∘ bdlStepX)` iterations that every level of the welded hierarchy satisfies interaction range at most 8 (`bdl_random_interaction_range8`).

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Shell Segment Endpoint & Radial Parent Distance Bounds -/

lemma shellVertexPos_start_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    shellVertexPos pcode M (shellSegStartVertex pcode M seg) =
      triGridPos3D (pcode.posX seg.val.1.val.1) (pcode.posQ seg.val.1.val.2.val.1)
        (pcode.posZ seg.val.1.val.2.val.2) (M + 1) (seg.val.2.1.val + 1) seg.val.2.2.val := by
  rw [shellVertexPos_eq_V]
  ext axis
  dsimp [shellSegStartVertex, bxStartLink, bxStart, armStart, projXq0ToBoundaryX0]
  by_cases hk0 : seg.val.2.2.val = 0
  · rw [dif_pos hk0]
    dsimp [shellVertexPosV, subdividePoint3D, triGridPos3D]
    rw [hk0, Nat.sub_zero]
    push_cast
    ring
  · rw [dif_neg hk0]
    dsimp [shellVertexPosV, triGridPos3D]
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]

/-- Expresses the 3D position of the end vertex of a shell segment `seg` as the adjacent point
    on the triangular grid `triGridPos3D` of its parent 2-simplex. -/
lemma shellVertexPos_end_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    shellVertexPos pcode M (shellSegEndVertex pcode M seg) =
      triGridPos3D (pcode.posX seg.val.1.val.1) (pcode.posQ seg.val.1.val.2.val.1)
        (pcode.posZ seg.val.1.val.2.val.2) (M + 1) (seg.val.2.1.val + 1) (seg.val.2.2.val + 1) := by
  have h_le : seg.val.2.2.val ≤ seg.val.2.1.val := seg.property
  rw [shellVertexPos_eq_V]
  ext axis
  dsimp [shellSegEndVertex, shellSegEndLink, shellSegEndV]
  by_cases hk : seg.val.2.2.val < seg.val.2.1.val
  · rw [dif_pos hk]
    dsimp [shellVertexPosV, triGridPos3D]
  · rw [dif_neg hk]
    have h_eq : seg.val.2.2.val = seg.val.2.1.val := by omega
    dsimp [shellVertexPosV, subdividePoint3D, triGridPos3D]
    rw [h_eq, Nat.sub_self]
    push_cast
    ring

/-- Shows that a shell vertex on the outermost shell $r = M$ coincides geometrically with
    the corresponding cone boundary position `boundaryX0Pos`. -/
lemma shellVertexPos_outer_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (xv : BoundaryX0Link pcode M) :
    shellVertexPos pcode M (mkOuterShellVertex pcode M xv) =
      boundaryX0Pos pcode M xv.val.2 := by
  rw [shellVertexPos_eq_V]
  ext axis
  rcases xv with ⟨⟨x, v⟩, hp⟩
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · dsimp [mkOuterShellVertex, shellVertexPosV, boundaryX0Pos, Fin.last]
    rw [subdividePoint3D_self _ _ (M + 1) (Nat.succ_ne_zero M)]
  · dsimp [mkOuterShellVertex, shellVertexPosV, boundaryX0Pos, triGridPos3D, subdividePoint3D, Fin.last]
    have hj_le : j.val + 1 ≤ M + 1 := by omega
    have h_sub : ((M + 1 - (j.val + 1) : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) - ((j.val + 1 : ℕ) : ℝ) :=
      Nat.cast_sub hj_le
    rw [h_sub]
    push_cast
    have hM : (M : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hM]
    ring
  · dsimp [mkOuterShellVertex, shellVertexPosV, boundaryX0Pos, Fin.last]
    rw [subdividePoint3D_self _ _ (M + 1) (Nat.succ_ne_zero M)]

/-- Bounds the squared Euclidean distance between the start and end vertices of a shell
    segment by $r_{\mathrm{loc}}^2$ whenever the parent $(q, z)$ edge has length at most $(M+1) r_{\mathrm{loc}}$. -/
lemma distSq3D_shellSegStart_shellSegEnd_le_rloc {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) (r_loc : ℝ)
    (h_dist : distSq3D (pcode.posQ seg.val.1.val.2.val.1) (pcode.posZ seg.val.1.val.2.val.2) ≤
      (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2) :
    distSq3D (shellVertexPos pcode M (shellSegStartVertex pcode M seg))
             (shellVertexPos pcode M (shellSegEndVertex pcode M seg)) ≤ r_loc ^ 2 := by
  rw [shellVertexPos_start_eq, shellVertexPos_end_eq]
  have hvu : seg.val.2.2.val + 1 ≤ seg.val.2.1.val + 1 := Nat.succ_le_succ seg.property
  rw [triGridPos3D_step_v _ _ _ (M + 1) (seg.val.2.1.val + 1) seg.val.2.2.val (Nat.succ_pos M) hvu]
  have hL_pos : (0 : ℝ) < (((M + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [div_le_iff₀ hL_pos]
  calc distSq3D (pcode.posQ seg.val.1.val.2.val.1) (pcode.posZ seg.val.1.val.2.val.2)
    _ ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2 := h_dist
    _ = r_loc ^ 2 * (((M + 1 : ℕ) : ℝ) ^ 2) := by ring

/-- Bounds the squared Euclidean distance between any shell vertex ($r > 0$) and its radial
    parent vertex by $r_{\mathrm{loc}}^2$ under coarse interaction range $(M+1) r_{\mathrm{loc}}$. -/
lemma distSq3D_shellVertex_radialParent_le_rloc {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv : ShellVertex pcode M) (r_loc : ℝ)
    (hr_nz : sv.val.2.val ≠ 0)
    (hX_q : ∀ (x : M_X) (q : Q), pcode.checkX x q ≠ 0 →
      distSq3D (pcode.posX x) (pcode.posQ q) ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2)
    (hX_z : ∀ xv : BoundaryX0Link pcode M,
      distSq3D (pcode.posX xv.val.1) (boundaryX0Pos pcode M xv.val.2) ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2) :
    distSq3D (shellVertexPos pcode M sv) (shellVertexPos pcode M (radialParentVertex pcode M sv)) ≤ r_loc ^ 2 := by
  rw [shellVertexPos_eq_V, shellVertexPos_eq_V]
  rcases sv with ⟨⟨⟨⟨x, v⟩, hp⟩, r⟩, h_in⟩
  have hr_pos : 0 < r.val := Nat.pos_of_ne_zero hr_nz
  unfold radialParentVertex radialParentLink radialParentV finPred
  simp only
  -- Step 1: Case split on the boundary link vertex type (qubit, subdivided Z-arm, or Z-check).
  rcases v with q | ⟨⟨eZ, j⟩ | z⟩
  · dsimp [shellVertexPosV]
    rw [Nat.sub_add_cancel hr_pos]
    exact subdividePoint3D_step_le_rloc (pcode.posX x) (pcode.posQ q) (M + 1) r.val r_loc
      (Nat.succ_pos M) (by rw [distSq3D_comm]; exact hX_q x q hp)
  -- Step 2: Subdivided Z-arm vertex case: compare j with r - 1 and apply triGridPos3D_step_u.
  · dsimp [InShellR] at h_in
    dsimp only
    by_cases hj : j.val < r.val - 1
    · rw [if_pos hj]
      dsimp [shellVertexPosV]
      rw [Nat.sub_add_cancel hr_pos]
      have hvu : j.val + 1 ≤ r.val := by omega
      rw [triGridPos3D_step_u (pcode.posX x) (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (M + 1) r.val (j.val + 1) (Nat.succ_pos M) hvu]
      have hL_pos : (0 : ℝ) < (((M + 1 : ℕ) : ℝ) ^ 2) := by positivity
      rw [div_le_iff₀ hL_pos, distSq3D_comm]
      calc distSq3D (pcode.posX x) (pcode.posQ eZ.val.1)
        _ ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2 := hX_q x eZ.val.1 hp
        _ = r_loc ^ 2 * (((M + 1 : ℕ) : ℝ) ^ 2) := by ring
    · rw [if_neg hj]
      have hj_eq : j.val + 1 = r.val := by omega
      have h_rhs : shellVertexPosV pcode M x (Sum.inr (Sum.inr eZ.val.2)) (r.val - 1) =
          triGridPos3D (pcode.posX x) (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (M + 1) r.val (j.val + 1) := by
        ext axis
        dsimp [shellVertexPosV, subdividePoint3D, triGridPos3D]
        rw [Nat.sub_add_cancel hr_pos, hj_eq, Nat.sub_self]
        push_cast; ring
      rw [h_rhs]
      dsimp [shellVertexPosV]
      have hvu : j.val + 1 ≤ r.val := by omega
      rw [triGridPos3D_step_u (pcode.posX x) (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (M + 1) r.val (j.val + 1) (Nat.succ_pos M) hvu]
      have hL_pos : (0 : ℝ) < (((M + 1 : ℕ) : ℝ) ^ 2) := by positivity
      rw [div_le_iff₀ hL_pos, distSq3D_comm]
      calc distSq3D (pcode.posX x) (pcode.posQ eZ.val.1)
        _ ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2 := hX_q x eZ.val.1 hp
        _ = r_loc ^ 2 * (((M + 1 : ℕ) : ℝ) ^ 2) := by ring
  -- Step 3: Z-check vertex case: apply subdividePoint3D_step_le_rloc along the cone ray.
  · dsimp [shellVertexPosV]
    rw [Nat.sub_add_cancel hr_pos]
    exact subdividePoint3D_step_le_rloc (pcode.posX x) (pcode.posZ z) (M + 1) r.val r_loc
      (Nat.succ_pos M) (by rw [distSq3D_comm]; exact hX_z ⟨(x, Sum.inr (Sum.inr z)), hp⟩)

/-! ## 2. Coupled Cylinder Complex Interaction Locality Theorem -/

/-- **Coupled Cylinder Complex Interaction Locality Theorem (`bdlCylinderStepX_interaction_locality`):**
    If every active `(q, z)` edge in `pcode` has `distSq3D (pcode.posQ q) (pcode.posZ z) ≤ ((M + 1) * r_loc)^2`
    and every link vertex `xv : BoundaryX0Link pcode M` has
    `distSq3D (pcode.posX xv.val.1) (boundaryX0Pos pcode M xv.val.2) ≤ ((M + 1) * r_loc)^2`,
    then every check-qubit pair `(mZ, q)` and `(mX, q)` in `bdlCylinderStepX pcode M` satisfies
    `distSq3D ≤ r_loc^2`. -/
theorem bdlCylinderStepX_interaction_locality {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (r_loc : ℝ)
    (hZ_arm : ∀ eZ : ActiveZ pcode,
      distSq3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2)
    (hX_cone : ∀ xv : BoundaryX0Link pcode M,
      distSq3D (pcode.posX xv.val.1) (boundaryX0Pos pcode M xv.val.2) ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2) :
    (∀ (mZ : BDLStepXMZ pcode M) (q : BDLStepXQ pcode M),
      (bdlCylinderStepX pcode M).checkZ mZ q ≠ 0 →
      distSq3D ((bdlCylinderStepX pcode M).posQ q) ((bdlCylinderStepX pcode M).posZ mZ) ≤ r_loc ^ 2) ∧
    (∀ (mX : BDLStepXMX pcode M) (q : BDLStepXQ pcode M),
      (bdlCylinderStepX pcode M).checkX mX q ≠ 0 →
      distSq3D ((bdlCylinderStepX pcode M).posQ q) ((bdlCylinderStepX pcode M).posX mX) ≤ r_loc ^ 2) := by
  -- Step 1: Derive coarse X-check to qubit distance bound from the cone boundary hypothesis.
  have hX_q : ∀ (x : M_X) (q : Q), pcode.checkX x q ≠ 0 →
      distSq3D (pcode.posX x) (pcode.posQ q) ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2 :=
    fun x q hxq => hX_cone ⟨(x, Sum.inl q), hxq⟩
  refine ⟨?_, ?_⟩
  · intro mZ q h_nz
    dsimp [bdlCylinderStepX, bdlStepXCheckZ] at h_nz ⊢
  -- Step 2: Bound Z-check to qubit distances across all four Z-check and two qubit sectors.
    rcases mZ with mZX | ⟨mZQ | mZZ⟩ <;> rcases q with qX | qQ
    · -- BDLCX2 vs BDLCX1 (bdlDeltaX1)
      rcases mZX with ⟨seg, b⟩ | ⟨s, k, v⟩
      · dsimp [bdlDeltaX1] at h_nz
        by_cases h_tri : seg.val.2.2.val = seg.val.2.1.val
        · rw [dif_pos h_tri] at h_nz
          by_cases hr0 : seg.val.2.1.val = 0
          · rw [dif_pos hr0] at h_nz
            split_ifs at h_nz with h_can
            · obtain ⟨q', _, hq'_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_nz
              by_cases hX' : pcode.checkX seg.val.1.val.1 q' ≠ 0
              · rw [dif_pos hX'] at hq'_nz
                by_cases hZ' : pcode.checkZ seg.val.1.val.2.val.2 q' ≠ 0
                · rw [dif_pos hZ'] at hq'_nz
                  by_cases h_sp : qX = Sum.inl (cornerSpokeRadial pcode M seg.val.1.val.1 q' hX', b)
                  · subst h_sp
                    dsimp [bdlStepXPosQ, bdlStepXPosZ]
                    let cseg := cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ'
                    have h_start_pos : shellVertexPos pcode M (cornerSpokeRadial pcode M seg.val.1.val.1 q' hX').val =
                        shellVertexPos pcode M (shellSegStartVertex pcode M cseg) := by
                      dsimp [shellVertexPos, cornerSpokeRadial, cornerSpoke, shellSegStartVertex, cseg, cornerSeg,
                        bxStartLink, bxStart, armStart, projXq0ToBoundaryX0]
                    have h_end_pos : shellVertexPos pcode M (shellSegEndVertex pcode M seg) =
                        shellVertexPos pcode M (shellSegEndVertex pcode M cseg) := by
                      dsimp [shellVertexPos, shellSegEndVertex, shellSegEndLink, shellSegEndV, cseg, cornerSeg]
                      have h_not_lt : ¬ (seg.val.2.2.val < seg.val.2.1.val) := by omega
                      rw [dif_neg h_not_lt, hr0]
                    rw [h_start_pos, h_end_pos]
                    exact distSq3D_shellSegStart_shellSegEnd_le_rloc pcode M cseg r_loc
                      (hZ_arm ⟨(q', seg.val.1.val.2.val.2), hZ'⟩)
                  · by_cases h_cs : qX = Sum.inr (Sum.inl (cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ', b))
                    · subst h_cs
                      dsimp [bdlStepXPosQ, bdlStepXPosZ]
                      have h_end_pos : shellVertexPos pcode M
                          (shellSegEndVertex pcode M (cornerSeg pcode M seg.val.1.val.1 q' seg.val.1.val.2.val.2 hX' hZ')) =
                          shellVertexPos pcode M (shellSegEndVertex pcode M seg) := by
                        dsimp [shellVertexPos, shellSegEndVertex, shellSegEndLink, shellSegEndV, cornerSeg]
                        have h_not_lt : ¬ (seg.val.2.2.val < seg.val.2.1.val) := by omega
                        rw [dif_neg h_not_lt, hr0]
                      rw [h_end_pos, distSq3D_self]; exact sq_nonneg r_loc
                    · exfalso; apply hq'_nz; rw [if_neg h_sp, if_neg h_cs]; rfl
                · rw [dif_neg hZ'] at hq'_nz; exact False.elim (hq'_nz rfl)
              · rw [dif_neg hX'] at hq'_nz; exact False.elim (hq'_nz rfl)
            · exfalso; exact h_nz rfl
          · rw [dif_neg hr0] at h_nz
            by_cases h1 : qX = Sum.inl (shellSegStartRadial pcode M seg, b)
            · subst h1
              dsimp [bdlStepXPosQ, bdlStepXPosZ, shellSegStartRadial]
              exact distSq3D_shellSegStart_shellSegEnd_le_rloc pcode M seg r_loc (hZ_arm seg.val.1.val.2)
            · by_cases h2 : qX = Sum.inl (shellSegEndRadial pcode M seg hr0, b)
              · subst h2
                dsimp [bdlStepXPosQ, bdlStepXPosZ, shellSegEndRadial]
                rw [distSq3D_self]; exact sq_nonneg r_loc
              · by_cases h3 : qX = Sum.inr (Sum.inl (seg, b))
                · subst h3
                  dsimp [bdlStepXPosQ, bdlStepXPosZ]
                  rw [distSq3D_self]; exact sq_nonneg r_loc
                · exfalso; apply h_nz; rw [if_neg h1, if_neg h2, if_neg h3]; rfl
        · rw [dif_neg h_tri] at h_nz
          by_cases h1 : qX = Sum.inl (shellSegStartRadial pcode M seg, b)
          · subst h1
            dsimp [bdlStepXPosQ, bdlStepXPosZ, shellSegStartRadial]
            exact distSq3D_shellSegStart_shellSegEnd_le_rloc pcode M seg r_loc (hZ_arm seg.val.1.val.2)
          · by_cases h2 : qX = Sum.inl (shellSegEndRadial pcode M seg (by have := seg.property; omega), b)
            · subst h2
              dsimp [bdlStepXPosQ, bdlStepXPosZ, shellSegEndRadial]
              rw [distSq3D_self]; exact sq_nonneg r_loc
            · by_cases h3 : qX = Sum.inr (Sum.inl (shellSegPred pcode M seg h_tri, b))
              · subst h3
                dsimp [bdlStepXPosQ, bdlStepXPosZ]
                rw [ ← radialParent_end_eq_end_pred pcode M seg h_tri, distSq3D_comm]
                have hr_nz : (shellSegEndVertex pcode M seg).val.2.val ≠ 0 := by
                  have := seg.property; dsimp [shellSegEndVertex]; omega
                exact distSq3D_shellVertex_radialParent_le_rloc pcode M (shellSegEndVertex pcode M seg)
                  r_loc hr_nz hX_q hX_cone
              · by_cases h4 : qX = Sum.inr (Sum.inl (seg, b))
                · subst h4
                  dsimp [bdlStepXPosQ, bdlStepXPosZ]
                  rw [distSq3D_self]; exact sq_nonneg r_loc
                · exfalso; apply h_nz; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]; rfl
      · dsimp [bdlDeltaX1] at h_nz
        by_cases h1 : qX = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, 0))
        · subst h1
          dsimp [bdlStepXPosQ, bdlStepXPosZ]
          rw [shellSegEndVertex_outer, shellVertexPos_outer_eq]
          dsimp [bxEndLink]
          rw [distSq3D_self]; exact sq_nonneg r_loc
        · by_cases h2 : qX = Sum.inr (Sum.inl (mkOuterShellSegment pcode M s k, v.succ))
          · subst h2
            dsimp [bdlStepXPosQ, bdlStepXPosZ]
            rw [shellSegEndVertex_outer, shellVertexPos_outer_eq]
            dsimp [bxEndLink]
            rw [distSq3D_self]; exact sq_nonneg r_loc
          · by_cases h3 : qX = Sum.inr (Sum.inr (bxStartLink pcode M s k, v))
            · subst h3
              dsimp [bdlStepXPosQ, bdlStepXPosZ, bxStartLink]
              exact distSq3D_bxStart_bxEnd_le_rloc pcode M s.val.2 k r_loc (hZ_arm s.val.2)
            · by_cases h4 : qX = Sum.inr (Sum.inr (bxEndLink pcode M s k, v))
              · subst h4
                dsimp [bdlStepXPosQ, bdlStepXPosZ, bxEndLink]
                rw [distSq3D_self]; exact sq_nonneg r_loc
              · exfalso; apply h_nz; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]; rfl
    · exfalso; exact h_nz rfl
    · -- BDLCQ2 vs BDLCX1 (bdlGXQ1)
  -- Step 3: Bound coupling-map and outer-boundary Z-check distances (bdlGXQ1, bdlDeltaQ1, bdlGQZ1).
      rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, vZ⟩
      · rcases qX with _ | ⟨⟨seg, bX⟩ | _⟩
        · exfalso; exact h_nz rfl
        · dsimp [bdlGXQ1] at h_nz
          split_ifs at h_nz with hc
          · rcases hc with ⟨hr_last, heZ, hk, rfl⟩
            have hseg_eq : seg = mkOuterShellSegment pcode M seg.val.1 k :=
              Subtype.ext (Prod.ext rfl (Prod.ext hr_last hk))
            rw [hseg_eq]
            dsimp [bdlStepXPosQ, bdlStepXPosZ]
            rw [shellSegEndVertex_outer, shellVertexPos_outer_eq]
            dsimp [bxEndLink, bxEnd, xq0Pos]
            rw [heZ, distSq3D_self]
            exact sq_nonneg r_loc
          · exfalso; exact h_nz rfl
        · exfalso; exact h_nz rfl
      · rcases qX with _ | ⟨_ | ⟨xv, vX⟩⟩
        · exfalso; exact h_nz rfl
        · exfalso; exact h_nz rfl
        · dsimp [bdlGXQ1] at h_nz
          split_ifs at h_nz with hc
          · dsimp [bdlStepXPosQ, bdlStepXPosZ]
            rw [hc.1]
            dsimp [boundaryX0Pos]
            rw [distSq3D_self]; exact sq_nonneg r_loc
          · exfalso; exact h_nz rfl
    · -- BDLCQ2 vs BDLCQ1 (bdlDeltaQ1)
      rcases mZQ with ⟨eZ, k, bZ⟩ | ⟨eZ, v⟩
      · dsimp [bdlDeltaQ1] at h_nz
        by_cases h1 : qQ = (armStart pcode M eZ k, bZ)
        · subst h1
          dsimp [bdlStepXPosQ, bdlStepXPosZ, xq0Pos]
          exact distSq3D_bxStart_bxEnd_le_rloc pcode M eZ k r_loc (hZ_arm eZ)
        · by_cases h2 : qQ = (armEnd pcode M eZ k, bZ)
          · subst h2
            dsimp [bdlStepXPosQ, bdlStepXPosZ]
            rw [distSq3D_self]; exact sq_nonneg r_loc
          · exfalso; apply h_nz; rw [if_neg h1, if_neg h2]; rfl
      · dsimp [bdlDeltaQ1] at h_nz
        by_cases h1 : qQ = (Sum.inr (Sum.inr eZ), 0)
        · subst h1
          dsimp [bdlStepXPosQ, bdlStepXPosZ, xq0Pos, projXq0ToBoundaryX0, boundaryX0Pos]
          rw [distSq3D_self]; exact sq_nonneg r_loc
        · by_cases h2 : qQ = (Sum.inr (Sum.inr eZ), v.succ)
          · subst h2
            dsimp [bdlStepXPosQ, bdlStepXPosZ, xq0Pos, projXq0ToBoundaryX0, boundaryX0Pos]
            rw [distSq3D_self]; exact sq_nonneg r_loc
          · exfalso; apply h_nz; rw [if_neg h1, if_neg h2]; rfl
    · exfalso; exact h_nz rfl
    · -- BDLCZ2 vs BDLCQ1 (bdlGQZ1)
      rcases qQ with ⟨v0, bQ⟩
      rcases v0 with _ | ⟨_ | eZ⟩
      · exfalso; exact h_nz rfl
      · exfalso; exact h_nz rfl
      · dsimp [bdlGQZ1] at h_nz
        split_ifs at h_nz with hc
        · dsimp [bdlStepXPosQ, bdlStepXPosZ, xq0Pos, projXq0ToBoundaryX0, boundaryX0Pos]
          rw [hc.1, distSq3D_self]
          exact sq_nonneg r_loc
        · exfalso; exact h_nz rfl
  -- Step 4: Bound X-check to qubit distances across bdlDeltaX0 and bdlGXQ0.
  · intro mX q h_nz
    dsimp [bdlCylinderStepX, bdlStepXCheckX] at h_nz ⊢
    rcases q with qX | qQ
    · -- BDLStepXMX vs BDLCX1 (bdlDeltaX0)
      rcases qX with ⟨sv, b⟩ | ⟨⟨seg, b⟩ | ⟨xv, v⟩⟩
      · dsimp [bdlDeltaX0] at h_nz
        by_cases hr0 : sv.val.val.2.val = 0
        · rw [if_pos hr0] at h_nz
          by_cases h1 : mX = Sum.inl (sv.val.val.1.val.1, b)
          · subst h1
            dsimp [bdlStepXPosQ, bdlStepXPosX]
            rcases sv with ⟨⟨⟨⟨⟨x, v⟩, hp⟩, r⟩, h_in⟩, h_not_diag⟩
            (try dsimp at hr0 ⊢)
            rcases v with q | ⟨⟨eZ, j⟩ | z⟩
            · dsimp [shellVertexPos]
              rw [hr0, zero_add]
              have h_step := subdividePoint3D_step_le_rloc (pcode.posX x) (pcode.posQ q)
                (M + 1) 0 r_loc (Nat.succ_pos M) (by rw [distSq3D_comm]; exact hX_q x q hp)
              rwa [subdividePoint3D_zero] at h_step
            · dsimp [InShellR] at h_in
              omega
            · dsimp [shellVertexPos]
              rw [hr0, zero_add]
              have h_step := subdividePoint3D_step_le_rloc (pcode.posX x) (pcode.posZ z)
                (M + 1) 0 r_loc (Nat.succ_pos M)
                (by rw [distSq3D_comm]; exact hX_cone ⟨(x, Sum.inr (Sum.inr z)), hp⟩)
              rwa [subdividePoint3D_zero] at h_step
          · by_cases h2 : mX = Sum.inr (sv.val, b)
            · subst h2
              dsimp [bdlStepXPosQ, bdlStepXPosX]
              rw [distSq3D_self]; exact sq_nonneg r_loc
            · exfalso; apply h_nz; rw [if_neg h1, if_neg h2]; rfl
        · rw [if_neg hr0] at h_nz
          by_cases h1 : mX = Sum.inr (radialParentVertex pcode M sv.val, b)
          · subst h1
            dsimp [bdlStepXPosQ, bdlStepXPosX]
            exact distSq3D_shellVertex_radialParent_le_rloc pcode M sv.val r_loc hr0 hX_q hX_cone
          · by_cases h2 : mX = Sum.inr (sv.val, b)
            · subst h2
              dsimp [bdlStepXPosQ, bdlStepXPosX]
              rw [distSq3D_self]; exact sq_nonneg r_loc
            · exfalso; apply h_nz; rw [if_neg h1, if_neg h2]; rfl
      · dsimp [bdlDeltaX0] at h_nz
        by_cases h1 : mX = Sum.inr (shellSegStartVertex pcode M seg, b)
        · subst h1
          dsimp [bdlStepXPosQ, bdlStepXPosX]
          rw [distSq3D_comm]
          exact distSq3D_shellSegStart_shellSegEnd_le_rloc pcode M seg r_loc (hZ_arm seg.val.1.val.2)
        · by_cases h2 : mX = Sum.inr (shellSegEndVertex pcode M seg, b)
          · subst h2
            dsimp [bdlStepXPosQ, bdlStepXPosX]
            rw [distSq3D_self]; exact sq_nonneg r_loc
          · exfalso; apply h_nz; rw [if_neg h1, if_neg h2]; rfl
      · dsimp [bdlDeltaX0] at h_nz
        by_cases h1 : mX = Sum.inr (mkOuterShellVertex pcode M xv, 0)
        · subst h1
          dsimp [bdlStepXPosQ, bdlStepXPosX]
          rw [shellVertexPos_outer_eq, distSq3D_self]
          exact sq_nonneg r_loc
        · by_cases h2 : mX = Sum.inr (mkOuterShellVertex pcode M xv, v.succ)
          · subst h2
            dsimp [bdlStepXPosQ, bdlStepXPosX]
            rw [shellVertexPos_outer_eq, distSq3D_self]
            exact sq_nonneg r_loc
          · exfalso; apply h_nz; rw [if_neg h1, if_neg h2]; rfl
    · -- BDLStepXMX vs BDLCQ1 (bdlGXQ0)
      rcases mX with _ | ⟨sv, b⟩
      · exfalso; exact h_nz rfl
      · dsimp [bdlGXQ0] at h_nz
        split_ifs at h_nz with hc
        · rcases hc with ⟨hr_last, hv_eq, rfl⟩
          have hsv_eq : sv = mkOuterShellVertex pcode M sv.val.1 :=
            Subtype.ext (Prod.ext rfl hr_last)
          rw [hsv_eq]
          dsimp [bdlStepXPosQ, bdlStepXPosX, xq0Pos]
          rw [shellVertexPos_outer_eq, hv_eq, distSq3D_self]
          exact sq_nonneg r_loc
        · exfalso; exact h_nz rfl

/-- Coordinatewise bound $|v_a| \le R$ for any 3D vector $v$ on the sphere of radius $R \ge 0$. -/
lemma abs_le_of_distSq3D_origin_eq (v : Point3D) (R : ℝ) (hR : 0 ≤ R)
    (h : distSq3D v (fun _ => 0) = R ^ 2) (axis : Fin 3) :
    |v axis| ≤ R := by
  dsimp [distSq3D] at h
  have h0 : 0 ≤ (v 0 - 0) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (v 1 - 0) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (v 2 - 0) ^ 2 := sq_nonneg _
  have h_sq : (v axis) ^ 2 ≤ R ^ 2 := by
    fin_cases axis <;> { dsimp; nlinarith }
  exact abs_le.mpr (abs_le_of_sq_le_sq' h_sq hR)

/-- Coordinatewise bound $|\mathrm{fallbackCapShift}_a| \le 1000 \Lambda$ for the deterministic fallback shift. -/
lemma abs_fallbackCapShift_le (axis_idx axis : Fin 3) :
    |fallbackCapShift axis_idx axis| ≤ 1000 * (bdlLambda : ℝ) := by
  dsimp [fallbackCapShift, bdlCapRadius, bdlAlpha, bdlAlphaNat]
  have h_lam : (0 : ℝ) ≤ 1000 * (bdlLambda : ℝ) := by positivity
  split_ifs
  · exact le_of_eq (abs_of_nonneg h_lam)
  · rw [abs_zero]
    exact h_lam

/-- Shows that all qubit, $Z$-check, and $X$-check perturbation vectors in `bdlLLLPerturbation B`
    have $\ell_\infty$ coordinates bounded by $1000 \Lambda$. -/
lemma bdlLLLPerturbation_abs_le (B : BundledCSSCode3D) :
    (∀ q axis, |(bdlLLLPerturbation B).1 q axis| ≤ 1000 * (bdlLambda : ℝ)) ∧
    (∀ mZ axis, |(bdlLLLPerturbation B).2.1 mZ axis| ≤ 1000 * (bdlLambda : ℝ)) ∧
    (∀ mX axis, |(bdlLLLPerturbation B).2.2 mX axis| ≤ 1000 * (bdlLambda : ℝ)) := by
  dsimp [bdlLLLPerturbation]
  split_ifs with h
  · have h_spec := (Classical.choose_spec h).1
    have hR : bdlCapRadius = 1000 * (bdlLambda : ℝ) := by dsimp [bdlCapRadius, bdlAlpha, bdlAlphaNat]
    have hR_nonneg : (0 : ℝ) ≤ 1000 * (bdlLambda : ℝ) := by positivity
    refine ⟨?_, ?_, ?_⟩
    · intro q axis
      have hq := h_spec.1 q
      rw [hR] at hq
      exact abs_le_of_distSq3D_origin_eq _ _ hR_nonneg hq axis
    · intro mZ axis
      have hmZ := h_spec.2.1 mZ
      rw [hR] at hmZ
      exact abs_le_of_distSq3D_origin_eq _ _ hR_nonneg hmZ axis
    · intro mX axis
      have hmX := h_spec.2.2.1 mX
      rw [hR] at hmX
      exact abs_le_of_distSq3D_origin_eq _ _ hR_nonneg hmX axis
  · refine ⟨fun _ axis => abs_fallbackCapShift_le 0 axis,
            fun _ axis => abs_fallbackCapShift_le 1 axis,
            fun _ axis => abs_fallbackCapShift_le 2 axis⟩

/-! ## 3. Preservation of Euclidean Interaction Range 8 -/

/-- **Preservation of Check-Qubit Interaction Range (`distSq3D ≤ 8^2`) Across All Levels `k`:** -/
def HasInteractionRange8 (B : BundledCSSCode3D) : Prop :=
  (∀ mZ q, B.code.checkZ mZ q ≠ 0 → distSq3D (B.code.posQ q) (B.code.posZ mZ) ≤ 8 ^ 2) ∧
  (∀ mX q, B.code.checkX mX q ≠ 0 → distSq3D (B.code.posQ q) (B.code.posX mX) ≤ 8 ^ 2)

/-- Verifies by finite exhaustion that the 5-qubit surface seed code satisfies `HasInteractionRange8`. -/
lemma hasInteractionRange8_surfaceSeed : HasInteractionRange8 bdlSurfaceSeedBundled := by
  refine ⟨?_, ?_⟩
  · intro mZ q _
    fin_cases mZ <;> fin_cases q <;>
      dsimp [bdlSurfaceSeedBundled, bdlSurfaceSeedCode, surfacePosQ, surfacePosZ, distSq3D] <;>
      norm_num
  · intro mX q _
    fin_cases mX <;> fin_cases q <;>
      dsimp [bdlSurfaceSeedBundled, bdlSurfaceSeedCode, surfacePosQ, surfacePosX, distSq3D] <;>
      norm_num

/-- Bounds the squared Euclidean distance between two $\Lambda$-rescaled points shifted by
    perturbation vectors of $\ell_\infty$ norm $\le 1000 \Lambda$ when their unperturbed distance is $\le 8$. -/
lemma distSq3D_perturb_le (p1 p2 c1 c2 : Point3D) (lam : ℕ)
    (hp : distSq3D p1 p2 ≤ 8 ^ 2)
    (hc1 : ∀ axis, |c1 axis| ≤ 1000 * (lam : ℝ))
    (hc2 : ∀ axis, |c2 axis| ≤ 1000 * (lam : ℝ)) :
    distSq3D (fun axis => (lam : ℝ) * p1 axis + c1 axis)
             (fun axis => (lam : ℝ) * p2 axis + c2 axis) ≤
      18000192 * ((lam : ℝ) ^ 2) := by
  dsimp [distSq3D] at hp ⊢
  have h1_0 : (c1 0) ^ 2 ≤ (1000 * (lam : ℝ)) ^ 2 := by have := abs_le.mp (hc1 0); nlinarith
  have h1_1 : (c1 1) ^ 2 ≤ (1000 * (lam : ℝ)) ^ 2 := by have := abs_le.mp (hc1 1); nlinarith
  have h1_2 : (c1 2) ^ 2 ≤ (1000 * (lam : ℝ)) ^ 2 := by have := abs_le.mp (hc1 2); nlinarith
  have h2_0 : (c2 0) ^ 2 ≤ (1000 * (lam : ℝ)) ^ 2 := by have := abs_le.mp (hc2 0); nlinarith
  have h2_1 : (c2 1) ^ 2 ≤ (1000 * (lam : ℝ)) ^ 2 := by have := abs_le.mp (hc2 1); nlinarith
  have h2_2 : (c2 2) ^ 2 ≤ (1000 * (lam : ℝ)) ^ 2 := by have := abs_le.mp (hc2 2); nlinarith
  nlinarith [
    sq_nonneg ((lam : ℝ) * (p1 0 - p2 0) - c1 0),
    sq_nonneg ((lam : ℝ) * (p1 0 - p2 0) + c2 0),
    sq_nonneg (c1 0 + c2 0),
    sq_nonneg ((lam : ℝ) * (p1 1 - p2 1) - c1 1),
    sq_nonneg ((lam : ℝ) * (p1 1 - p2 1) + c2 1),
    sq_nonneg (c1 1 + c2 1),
    sq_nonneg ((lam : ℝ) * (p1 2 - p2 2) - c1 2),
    sq_nonneg ((lam : ℝ) * (p1 2 - p2 2) + c2 2),
    sq_nonneg (c1 2 + c2 2)
  ]

/-- Proves that `bdlRandomStepX` preserves the Euclidean interaction range bound $r_{\mathrm{loc}} = 8$. -/
lemma bdlRandomStepX_preserves_interaction_range8 (B : BundledCSSCode3D)
    (h : HasInteractionRange8 B) :
    HasInteractionRange8 (bdlRandomStepX B) := by
  -- Step 1: Bound perturbed coarse check-qubit distances using the LLL shift bound.
  have h_lll := bdlLLLPerturbation_abs_le B
  let pcode := bdlPerturbStep B.code bdlLambda (bdlLLLPerturbation B).1 (bdlLLLPerturbation B).2.1 (bdlLLLPerturbation B).2.2
  have h_scale_bound : 72000768 * ((bdlLambda : ℝ) ^ 2) ≤ (((bdlSubdivPred + 1 : ℕ) : ℝ) * 8) ^ 2 := by
    rw [bdlSubdivM_eq_succ]
    dsimp [bdlSubdivM, bdlSubdivFactor, bdlAlphaNat]
    push_cast
    nlinarith [sq_nonneg (bdlLambda : ℝ)]
  have hZ_pcode : ∀ (q : B.Q) (mZ : B.M_Z), B.code.checkZ mZ q ≠ 0 →
      distSq3D (pcode.posQ q) (pcode.posZ mZ) ≤ 18000192 * ((bdlLambda : ℝ) ^ 2) := by
    intro q mZ h_nz
    exact distSq3D_perturb_le (B.code.posQ q) (B.code.posZ mZ)
      ((bdlLLLPerturbation B).1 q) ((bdlLLLPerturbation B).2.1 mZ) bdlLambda
      (h.1 mZ q h_nz) (h_lll.1 q) (h_lll.2.1 mZ)
  have hX_pcode : ∀ (q : B.Q) (mX : B.M_X), B.code.checkX mX q ≠ 0 →
      distSq3D (pcode.posX mX) (pcode.posQ q) ≤ 18000192 * ((bdlLambda : ℝ) ^ 2) := by
    intro q mX h_nz
    rw [distSq3D_comm]
    exact distSq3D_perturb_le (B.code.posQ q) (B.code.posX mX)
      ((bdlLLLPerturbation B).1 q) ((bdlLLLPerturbation B).2.2 mX) bdlLambda
      (h.2 mX q h_nz) (h_lll.1 q) (h_lll.2.2 mX)
  -- Step 2: Verify the Z-arm and X-cone hypotheses of bdlCylinderStepX_interaction_locality.
  have hZ_arm : ∀ eZ : ActiveZ pcode,
      distSq3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) ≤ (((bdlSubdivPred + 1 : ℕ) : ℝ) * 8) ^ 2 := by
    intro eZ
    have h1 := hZ_pcode eZ.val.1 eZ.val.2 eZ.property
    nlinarith [sq_nonneg (bdlLambda : ℝ)]
  have hX_cone : ∀ xv : BoundaryX0Link pcode bdlSubdivPred,
      distSq3D (pcode.posX xv.val.1) (boundaryX0Pos pcode bdlSubdivPred xv.val.2) ≤ (((bdlSubdivPred + 1 : ℕ) : ℝ) * 8) ^ 2 := by
    intro ⟨⟨x, v⟩, h_link⟩
    rcases v with q | ⟨⟨eZ, j⟩ | z⟩
    · dsimp [InLinkOfX, boundaryX0Pos] at h_link ⊢
      have h1 := hX_pcode q x h_link
      nlinarith [sq_nonneg (bdlLambda : ℝ)]
    · dsimp [InLinkOfX, boundaryX0Pos] at h_link ⊢
      have h_tri := distSq3D_triangle (pcode.posX x) (pcode.posQ eZ.val.1)
        (subdividePoint3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (bdlSubdivPred + 1) (j.val + 1))
      have h_sub := distSq3D_subdividePoint3D_le_right (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2)
        (bdlSubdivPred + 1) (j.val + 1) (by omega)
      have h1 := hX_pcode eZ.val.1 x h_link
      have h2 := hZ_pcode eZ.val.1 eZ.val.2 eZ.property
      nlinarith [sq_nonneg (bdlLambda : ℝ)]
    · dsimp [InLinkOfX, boundaryX0Pos] at h_link ⊢
      rcases h_link with ⟨q, hxq, hzq⟩
      have h_tri := distSq3D_triangle (pcode.posX x) (pcode.posQ q) (pcode.posZ z)
      have h1 := hX_pcode q x hxq
      have h2 := hZ_pcode q z hzq
      nlinarith [sq_nonneg (bdlLambda : ℝ)]
  exact bdlCylinderStepX_interaction_locality pcode bdlSubdivPred 8 hZ_arm hX_cone

/-- Proves that CSS code duality `dualBundled` preserves `HasInteractionRange8`. -/
lemma dualBundled_preserves_interaction_range8 (B : BundledCSSCode3D)
    (h : HasInteractionRange8 B) :
    HasInteractionRange8 (dualBundled B) :=
  ⟨h.2, h.1⟩

/-- Proves that `bdlRandomStepZ` preserves the Euclidean interaction range bound $r_{\mathrm{loc}} = 8$. -/
lemma bdlRandomStepZ_preserves_interaction_range8 (B : BundledCSSCode3D)
    (h : HasInteractionRange8 B) :
    HasInteractionRange8 (bdlRandomStepZ B) :=
  dualBundled_preserves_interaction_range8 _
    (bdlRandomStepX_preserves_interaction_range8 _
      (dualBundled_preserves_interaction_range8 _ h))

/-- Proves by induction on $k$ that `(bdlRandomStepZ ∘ bdlRandomStepX)^[k]` preserves `HasInteractionRange8`. -/
lemma hasInteractionRange8_bdlIterated (k : ℕ) (B : BundledCSSCode3D)
    (h : HasInteractionRange8 B) :
    HasInteractionRange8 ((bdlRandomStepZ ∘ bdlRandomStepX)^[k] B) := by
  induction k generalizing B with
  | zero => exact h
  | succ k ih =>
    exact ih ((bdlRandomStepZ ∘ bdlRandomStepX) B)
      (bdlRandomStepZ_preserves_interaction_range8 _
        (bdlRandomStepX_preserves_interaction_range8 _ h))

/-- **Theorem (`bdl_random_interaction_range8`):** Every level `k` of the full random BDL code
    `bdlRandomCode k` satisfies check-qubit interaction range `distSq3D ≤ 8^2` in both Z and X sectors
    (Proved). -/
theorem bdl_random_interaction_range8 (k : ℕ) :
    HasInteractionRange8 (bdlRandomBundled k) :=
  hasInteractionRange8_bdlIterated (k + 1) bdlSurfaceSeedBundled hasInteractionRange8_surfaceSeed

end WeldedHierarchy
