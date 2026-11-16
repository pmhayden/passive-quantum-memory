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

import Proofs.Step1LLLDensity.TriangularGridUnitBallPacking

/-!
# Step-2 Cylinder Replacement Unit-Ball Vertex Density from Valid LLL Perturbation

Proves `bdlReplaceStepX_unit_ball_density_of_valid_lll`, showing that if a bundled 3D CSS code has bounded check degree, satisfies `HasNoIsolatedQ`, and carries a valid Step-1 spherical-cap perturbation, then the Step-2 cylinder replacement code satisfies uniform unit-ball vertex density. Also establishes segment and arm endpoint distinctness (`shellSegStartVertex_ne_end`, `armStart_ne_armEnd`) and shell-vertex segment incidence (`svIncidentSeg`).

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Step-2 Unit-Ball Density Theorem from Valid Step-1 LLL Perturbation -/

/-- **Step 2 Embedding Density Theorem (`bdlReplaceStepX_unit_ball_density_of_valid_lll`; Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.12):**
    For any coarse CSS code `B : BundledCSSCode3D` without isolated qubits (`HasNoIsolatedQ B.code`)
    and any perturbation `c` satisfying the Step 1 LLL conditions (`ValidLLLSphericalCapPerturbation B c`),
    the replaced code `bdlReplaceStepX B.code bdlLambda bdlSubdivPred c.1 c.2.1 c.2.2` is a `(t, 1)`-embedding
    with unit-ball vertex multiplicity at most `bdlDensityT`. -/
theorem bdlReplaceStepX_unit_ball_density_of_valid_lll
    (B : BundledCSSCode3D) (hq : HasNoIsolatedQ B.code)
    (c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D))
    (h_valid : ValidLLLSphericalCapPerturbation B c)
    (x0 : Point3D) :
    let rstep := bdlReplaceStepX B.code bdlLambda bdlSubdivPred c.1 c.2.1 c.2.2
    ((Finset.univ.filter (fun q => rstep.posQ q ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT ∧
    ((Finset.univ.filter (fun m => rstep.posZ m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT ∧
    ((Finset.univ.filter (fun m => rstep.posX m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT := by
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  let M := bdlSubdivPred
  have hq_pcode : HasNoIsolatedQ pcode := hq
  have h_gp_real := card_gridPoint_in_unit_ball_le B c h_valid x0
  have h_Q_real : ((Finset.univ.filter (fun q : B.Q => pcode.posQ q ∈ ball3D x0 1)).card : ℝ) ≤ 5595 :=
    (h_valid.2.2.2.2.2.2 x0).2.1
  have h_MZ_real : ((Finset.univ.filter (fun m : B.M_Z => pcode.posZ m ∈ ball3D x0 1)).card : ℝ) ≤ 5595 :=
    (h_valid.2.2.2.2.2.2 x0).2.2.1
  have h_MX_real : ((Finset.univ.filter (fun m : B.M_X => pcode.posX m ∈ ball3D x0 1)).card : ℝ) ≤ 5595 :=
    (h_valid.2.2.2.2.2.2 x0).2.2.2
  -- Step 1: Establish the grid-point unit-ball packing bound (≤ 675) and coarse cell bounds.
  have h_sv_le : (Finset.univ.filter (fun sv : ShellVertex pcode M =>
      shellVertexPos pcode M sv ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)).card :=
    card_filter_le_of_injective _ _ (svToGrid pcode M hq_pcode) (svToGrid_injective pcode M hq_pcode)
      (fun sv h => by rw [gridPointPos_svToGrid]; exact h)
  have h_seg_le : (Finset.univ.filter (fun seg : ShellSegment pcode M =>
      shellVertexPos pcode M (shellSegEndVertex pcode M seg) ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)).card :=
    card_filter_le_of_injective _ _ (segToGrid pcode M) (segToGrid_injective pcode M)
      (fun seg h => by rw [gridPointPos_segToGrid]; exact h)
  have h_arm_le : (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) =>
      xq0Pos pcode M (armEnd pcode M p.1 p.2) ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)).card :=
    card_filter_le_of_injective _ _ (armToGrid pcode M hq_pcode) (armToGrid_injective pcode M hq_pcode)
      (fun p h => by rw [gridPointPos_armToGrid]; exact h)
  have h_bx_le : (Finset.univ.filter (fun xv : BoundaryX0Link pcode M =>
      boundaryX0Pos pcode M xv.val.2 ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun sv : ShellVertex pcode M => shellVertexPos pcode M sv ∈ ball3D x0 1)).card :=
  -- Step 2: Bound the number of BDLStepXQ qubits in the unit ball by decomposing into sectors.
    card_filter_le_of_injective _ _ (mkOuterShellVertex pcode M)
      (fun xv1 xv2 h => congr_arg (fun sv : ShellVertex pcode M => sv.val.1) h)
      (fun xv h => by rw [shellVertexPos_outer_eq]; exact h)
  have h_outer_seg_le : (Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) =>
      boundaryX0Pos pcode M (bxEnd pcode M p.1.val.2 p.2) ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun seg : ShellSegment pcode M =>
        shellVertexPos pcode M (shellSegEndVertex pcode M seg) ∈ ball3D x0 1)).card :=
    card_filter_le_of_injective _ _ (fun p => mkOuterShellSegment pcode M p.1 p.2)
      (fun p1 p2 h => Prod.ext (congr_arg (fun s : ShellSegment pcode M => s.val.1) h)
        (congr_arg (fun s : ShellSegment pcode M => s.val.2.2) h))
      (fun p h => by
        have h_end : shellVertexPos pcode M (shellSegEndVertex pcode M (mkOuterShellSegment pcode M p.1 p.2)) =
            boundaryX0Pos pcode M (bxEnd pcode M p.1.val.2 p.2) := by
          rw [shellVertexPos_end_eq]
          dsimp [mkOuterShellSegment]
          have h_arm := gridPointPos_armToGrid pcode M hq_pcode (p.1.val.2, p.2)
          dsimp [armToGrid, gridPointPos] at h_arm
          have hLr : (M + 1 : ℝ) ≠ 0 := by positivity
          have h_tri : triGridPos3D (pcode.posX p.1.val.1) (pcode.posQ p.1.val.2.val.1) (pcode.posZ p.1.val.2.val.2)
              (M + 1) (M + 1) (p.2.val + 1) =
              triGridPos3D (pcode.posX (Classical.choose (hq_pcode.2 p.1.val.2.val.1 ⟨p.1.val.2.val.2, p.1.val.2.property⟩))) (pcode.posQ p.1.val.2.val.1)
                (pcode.posZ p.1.val.2.val.2) (M + 1) (M + 1) (p.2.val + 1) := by
            ext axis
            dsimp [triGridPos3D]
            rw [Nat.cast_sub (Nat.succ_le_succ (Nat.le_of_lt_succ p.2.isLt))]
            field_simp
            ring
          rw [h_tri, h_arm]
          rfl
        rw [h_end]; exact h)
  have h_activeZ_le : (Finset.univ.filter (fun eZ : ActiveZ pcode =>
      pcode.posZ eZ.val.2 ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) =>
        xq0Pos pcode M (armEnd pcode M p.1 p.2) ∈ ball3D x0 1)).card :=
    card_filter_le_of_injective _ _ (fun eZ => (eZ, Fin.last M))
      (fun eZ1 eZ2 h => congr_arg Prod.fst h)
      (fun eZ h => by
        have h_end : xq0Pos pcode M (armEnd pcode M eZ (Fin.last M)) = pcode.posZ eZ.val.2 := by
          dsimp [xq0Pos, projXq0ToBoundaryX0, armEnd, Fin.last, boundaryX0Pos]
        rw [h_end]; exact h)
  have h_activeZ_finM_le : (Finset.univ.filter (fun p : ActiveZ pcode × Fin M =>
      xq0Pos pcode M (Sum.inr (Sum.inl p)) ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) =>
        xq0Pos pcode M (armEnd pcode M p.1 p.2) ∈ ball3D x0 1)).card :=
    card_filter_le_of_injective _ _ (fun p => (p.1, ⟨p.2.val, Nat.lt_succ_of_lt p.2.isLt⟩))
      (fun p1 p2 h => by
        injection h with h1 h2
        exact Prod.ext h1 (Fin.ext (congr_arg (fun x : Fin (M + 1) => x.val) h2)))
      (fun p h => by
        have h_end : armEnd pcode M p.1 ⟨p.2.val, Nat.lt_succ_of_lt p.2.isLt⟩ = Sum.inr (Sum.inl p) := by
          dsimp [armEnd]
          split_ifs with hk
          · rfl
          · exfalso; exact hk p.2.isLt
        rw [h_end]; exact h)
  refine ⟨?_, ?_, ?_⟩
  · -- 1. Qubits (BDLStepXQ)
    unfold bdlReplaceStepX bdlCylinderStepX bdlStepXPosQ
    simp only [card_filter_sum_eq, card_filter_prod_fin3_eq, card_filter_prod_fin2_eq]
    have h_rv_le : (Finset.univ.filter (fun rv : RadialVertex pcode M =>
        shellVertexPos pcode M rv.val ∈ ball3D x0 1)).card ≤
      (Finset.univ.filter (fun sv : ShellVertex pcode M =>
        shellVertexPos pcode M sv ∈ ball3D x0 1)).card :=
  -- Step 3: Bound the number of BDLStepXMZ Z-checks and BDLStepXMX X-checks in the unit ball.
      card_filter_le_of_injective _ _ (fun rv => rv.val)
        (fun _ _ h => Subtype.ext h) (fun _ h => h)
    have h_rv_r : ((Finset.univ.filter (fun rv : RadialVertex pcode M => shellVertexPos pcode M rv.val ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr (h_rv_le.trans h_sv_le)).trans h_gp_real
    have h_sv_r : ((Finset.univ.filter (fun sv : ShellVertex pcode M => shellVertexPos pcode M sv ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr h_sv_le).trans h_gp_real
    have h_seg_r : ((Finset.univ.filter (fun seg : ShellSegment pcode M => shellVertexPos pcode M (shellSegEndVertex pcode M seg) ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr h_seg_le).trans h_gp_real
    have h_bx_r : ((Finset.univ.filter (fun xv : BoundaryX0Link pcode M => boundaryX0Pos pcode M xv.val.2 ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr (h_bx_le.trans h_sv_le)).trans h_gp_real
    have h_azM_r : ((Finset.univ.filter (fun p : ActiveZ pcode × Fin M => xq0Pos pcode M (Sum.inr (Sum.inl p)) ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr (h_activeZ_finM_le.trans h_arm_le)).trans h_gp_real
    have h_az_r : ((Finset.univ.filter (fun eZ : ActiveZ pcode => xq0Pos pcode M (Sum.inr (Sum.inr eZ)) ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr (h_activeZ_le.trans h_arm_le)).trans h_gp_real
    have h_Q_r : ((Finset.univ.filter (fun q : B.Q => xq0Pos pcode M (Sum.inl q) ∈ ball3D x0 1)).card : ℝ) ≤ 5595 := h_Q_real
    dsimp [bdlDensityT]
    push_cast
    linarith
  · -- 2. Z-checks (BDLStepXMZ)
    unfold bdlReplaceStepX bdlCylinderStepX bdlStepXPosZ
    simp only [card_filter_sum_eq, card_filter_prod_fin3_eq, card_filter_prod_prod_fin2_eq,
      card_filter_prod_prod_fin3_eq, card_filter_prod_fin2_eq]
    have h_seg_r : ((Finset.univ.filter (fun seg : ShellSegment pcode M => shellVertexPos pcode M (shellSegEndVertex pcode M seg) ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr h_seg_le).trans h_gp_real
    have h_out_r : ((Finset.univ.filter (fun p : ActiveZLink pcode × Fin (M + 1) => boundaryX0Pos pcode M (bxEnd pcode M p.1.val.2 p.2) ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr (h_outer_seg_le.trans h_seg_le)).trans h_gp_real
    have h_arm_r : ((Finset.univ.filter (fun p : ActiveZ pcode × Fin (M + 1) => xq0Pos pcode M (armEnd pcode M p.1 p.2) ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr h_arm_le).trans h_gp_real
    have h_az_r : ((Finset.univ.filter (fun eZ : ActiveZ pcode => pcode.posZ eZ.val.2 ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr (h_activeZ_le.trans h_arm_le)).trans h_gp_real
    dsimp [bdlDensityT]
    push_cast
    linarith
  · -- 3. X-checks (BDLStepXMX)
    unfold bdlReplaceStepX bdlCylinderStepX bdlStepXPosX
    simp only [card_filter_sum_eq, card_filter_prod_fin3_eq]
    have h_sv_r : ((Finset.univ.filter (fun sv : ShellVertex pcode M => shellVertexPos pcode M sv ∈ ball3D x0 1)).card : ℝ) ≤
        5595 * 5719 * 118 := (Nat.cast_le.mpr h_sv_le).trans h_gp_real
    dsimp [bdlDensityT]
    push_cast
    linarith

/-! ## 2. Endpoint Distinctness & Incident Azimuthal Segment Construction -/

lemma hasNoIsolatedQ_surfaceSeed : HasNoIsolatedQ bdlSurfaceSeedCode := by
  constructor <;> decide

/-- Proves that CSS code duality `dualCode` preserves `HasNoIsolatedQ` by swapping the two clauses. -/
lemma hasNoIsolatedQ_dualCode {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) (hq : HasNoIsolatedQ code) :
    HasNoIsolatedQ (dualCode code) :=
  ⟨hq.2, hq.1⟩

/-- Proves that the start and end vertices of any azimuthal `ShellSegment` are distinct. -/
lemma shellSegStartVertex_ne_end {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    shellSegStartVertex pcode M seg ≠ shellSegEndVertex pcode M seg := by
  intro h_eq
  have h_v : (shellSegStartVertex pcode M seg).val.1.val.2 = (shellSegEndVertex pcode M seg).val.1.val.2 :=
    congr_arg (fun sv : ShellVertex pcode M => sv.val.1.val.2) h_eq
  dsimp [shellSegStartVertex, shellSegEndVertex, bxStartLink, bxStart, armStart,
    projXq0ToBoundaryX0, shellSegEndLink, shellSegEndV] at h_v
  split_ifs at h_v with hk0 hkr
  · (try dsimp at h_v)
    injection h_v with h_inl
    have hj := congr_arg (fun p => p.2.val) (Sum.inl.inj h_inl)
    (try dsimp at hj)
    omega
  · (try dsimp at h_v)
    injection h_v with h_inr
    contradiction

/-- Proves that the start and end vertices of any subdivided $Z$-check arm segment are distinct. -/
lemma armStart_ne_armEnd {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) :
    armStart pcode M eZ k ≠ armEnd pcode M eZ k := by
  intro h_eq
  dsimp [armStart, armEnd] at h_eq
  split_ifs at h_eq with hk0 hkm
  · injection h_eq with h_inl
    have hj := congr_arg (fun p => p.2.val) (Sum.inl.inj h_inl)
    (try dsimp at hj)
    omega
  · injection h_eq with h_inr
    contradiction

/-- Selects an azimuthal `ShellSegment` incident to a given `ShellVertex sv` on the same
    radial shell under the `HasNoIsolatedQ` hypothesis. -/
noncomputable def svIncidentSeg {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (sv : ShellVertex pcode M) : ShellSegment pcode M :=
  match h : sv.val.1.val.2 with
  | Sum.inl q0 =>
      have hx0 : pcode.checkX sv.val.1.val.1 q0 ≠ 0 := by
        have hp := sv.val.1.property; dsimp [InLinkOfX] at hp; rw [h] at hp; exact hp
      let hz_ex := hq.1 q0 ⟨sv.val.1.val.1, hx0⟩
      let z0 := Classical.choose hz_ex
      let hz0 := Classical.choose_spec hz_ex
      ⟨(⟨(sv.val.1.val.1, ⟨(q0, z0), hz0⟩), hx0⟩, sv.val.2, 0), Nat.zero_le _⟩
  | Sum.inr (Sum.inl (eZ, j)) =>
      have hx0 : pcode.checkX sv.val.1.val.1 eZ.val.1 ≠ 0 := by
        have hp := sv.val.1.property; dsimp [InLinkOfX] at hp; rw [h] at hp; exact hp
      have hin : j.val < sv.val.2.val := by
        have hp := sv.property; dsimp [InShellR] at hp; rw [h] at hp; exact hp
      ⟨(⟨(sv.val.1.val.1, eZ), hx0⟩, sv.val.2, ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self M)⟩),
        Nat.le_of_lt hin⟩
  | Sum.inr (Sum.inr z0) =>
      have hp : ∃ q0 : Q, pcode.checkX sv.val.1.val.1 q0 ≠ 0 ∧ pcode.checkZ z0 q0 ≠ 0 := by
        have hp := sv.val.1.property; dsimp [InLinkOfX] at hp; rw [h] at hp; exact hp
      let q0 := Classical.choose hp
      let hq0 := Classical.choose_spec hp
      ⟨(⟨(sv.val.1.val.1, ⟨(q0, z0), hq0.2⟩), hq0.1⟩, sv.val.2, sv.val.2), le_rfl⟩

/-- Proves that `svIncidentSeg pcode M hq sv` lies on shell `sv.val.2` and has `sv` as
    either its start vertex or its end vertex. -/
lemma svIncidentSeg_start_or_end {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (sv : ShellVertex pcode M) :
    (svIncidentSeg pcode M hq sv).val.2.1 = sv.val.2 ∧
    (sv = shellSegStartVertex pcode M (svIncidentSeg pcode M hq sv) ∨
     sv = shellSegEndVertex pcode M (svIncidentSeg pcode M hq sv)) := by
  rcases sv with ⟨⟨⟨⟨x, v⟩, hlink⟩, r⟩, h_property⟩
  rcases v with q0 | ⟨⟨eZ, j⟩ | z0⟩
  · refine ⟨rfl, Or.inl ?_⟩
    apply Subtype.ext; apply Prod.ext; · apply Subtype.ext; apply Prod.ext; rfl; rfl
    · rfl
  · refine ⟨rfl, Or.inr ?_⟩
    have hin : j.val < r.val := h_property
    apply Subtype.ext; apply Prod.ext
    · apply Subtype.ext; apply Prod.ext
      · rfl
      · dsimp [svIncidentSeg, shellSegEndVertex, shellSegEndLink, shellSegEndV]
        rw [if_pos hin]
    · rfl
  · refine ⟨rfl, Or.inr ?_⟩
    have h_not_lt : ¬ (r.val < r.val) := Nat.lt_irrefl r.val
    apply Subtype.ext; apply Prod.ext
    · apply Subtype.ext; apply Prod.ext
      · rfl
      · dsimp [svIncidentSeg, shellSegEndVertex, shellSegEndLink, shellSegEndV]
        rw [dif_neg h_not_lt]
    · rfl

end WeldedHierarchy
