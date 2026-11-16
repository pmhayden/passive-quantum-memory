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

import Proofs.Step1LLLDensity.CylinderInteractionLocality

/-!
# Triangular Subdivision Grid Unit-Ball Packing and Cylinder Cell Embeddings

Defines the unified subdivision grid `GridPoint` together with unit-ball index slices `vBallFinset` and `uBallFinset`, and proves the unit-ball packing bound `card_gridPoint_in_unit_ball_le` (`card_vBallFinset_le`, `card_uBallFinset_le`) on well-separated 2-simplices. Introduces the non-isolated qubit predicate `HasNoIsolatedQ` and constructs injective position-preserving grid embeddings (`segToGrid`, `svToGrid`, `armToGrid`) for cylinder segments, shell vertices, and star-interface arms.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.2 (`def:well-separated-base`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Unit-Ball Radial and Azimuthal Grid Fiber Bounds -/

abbrev GridPoint {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) : Type :=
  { p : ActiveSimplex2 pcode × Fin (M + 2) × Fin (M + 2) // p.2.2.val ≤ p.2.1.val }

/-- The 3D Euclidean embedding of a `GridPoint` via `triGridPos3D` at subdivision scale $L = M + 1$. -/
def gridPointPos {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (gp : GridPoint pcode M) : Point3D :=
  triGridPos3D (pcode.posX gp.val.1.val.1) (pcode.posQ gp.val.1.val.2.1)
    (pcode.posZ gp.val.1.val.2.2) (M + 1) gp.val.2.1.val gp.val.2.2.val

/-- The set of azimuthal indices $v \le u$ on radial shell $u$ of simplex $s$ whose 3D grid
    point falls inside the unit ball `Ball3D x0 1`. -/
def vBallFinset {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : Point3D)
    (s : ActiveSimplex2 pcode) (u : Fin (M + 2)) : Finset (Fin (M + 2)) :=
  Finset.univ.filter (fun v : Fin (M + 2) =>
    v.val ≤ u.val ∧
    triGridPos3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2)
      (M + 1) u.val v.val ∈ ball3D x0 1)

/-- The set of radial shell indices $u \in \mathrm{Fin}(M+2)$ of simplex $s$ for which at least
    one azimuthal grid point $(u, v)$ falls inside `Ball3D x0 1`. -/
def uBallFinset {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x0 : Point3D)
    (s : ActiveSimplex2 pcode) : Finset (Fin (M + 2)) :=
  Finset.univ.filter (fun u : Fin (M + 2) => (vBallFinset pcode M x0 s u).Nonempty)

/-- Shows that on any fixed radial shell $u$ of a 2-simplex whose $(Q, Z)$ edge has length
    at least $(M+1)/2$, at most $5$ azimuthal grid points fall inside any unit ball. -/
lemma card_vBallFinset_le (B : BundledCSSCode3D)
    (c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D))
    (h_valid : ValidLLLSphericalCapPerturbation B c)
    (x0 : Point3D)
    (s : ActiveSimplex2 (bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2))
    (u : Fin (bdlSubdivPred + 2)) :
    (vBallFinset (bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2) bdlSubdivPred x0 s u).card ≤ 118 := by
  -- Step 1: Show any two grid points in VBallFinset have squared v-index difference at most 16.
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  apply finset_fin_card_le_of_sub_sq_le _ 117
  intro v1 hv1 v2 hv2
  dsimp [vBallFinset] at hv1 hv2
  rw [Finset.mem_filter] at hv1 hv2
  rcases hv1 with ⟨_, hv1_le, hp1⟩
  rcases hv2 with ⟨_, hv2_le, hp2⟩
  have h_dist_le := distSq3D_le_four_of_mem_ball3D_one x0 _ _ hp1 hp2
  rw [triGridPos3D_same_u_distSq _ _ _ _ _ _ _ hv1_le hv2_le, distSq3D_comm (pcode.posZ _)] at h_dist_le
  have h_edge : ((bdlAlpha2 - 1) * (bdlLambda : ℝ)) ^ 2 ≤
      distSq3D (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) :=
    (h_valid.2.2.2.1 s.val.2.2 s.val.2.1 s.property.2).1
  have h_sub_eq : ((bdlSubdivPred + 1 : ℕ) : ℝ) = 4002 * (bdlLambda : ℝ) := by
    rw [bdlSubdivM_eq_succ]; dsimp [bdlSubdivM, bdlSubdivFactor, bdlAlphaNat]; push_cast; ring
  rw [h_sub_eq] at h_dist_le
  have h_lam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
  have h_lam_ne : (bdlLambda : ℝ) ≠ 0 := ne_of_gt h_lam_pos
  have h_lhs_eq : ((((v1.val : ℝ) - (v2.val : ℝ)) / (4002 * (bdlLambda : ℝ))) ^ 2) *
      (((bdlAlpha2 - 1) * (bdlLambda : ℝ)) ^ 2) =
      (((v1.val : ℝ) - (v2.val : ℝ)) ^ 2) * ((137 / 8004 : ℝ) ^ 2) := by
    dsimp [bdlAlpha2, bdlAlpha1]
    field_simp
    ring
  have h_sq_nonneg : 0 ≤ (((v1.val : ℝ) - (v2.val : ℝ)) / (4002 * (bdlLambda : ℝ))) ^ 2 := sq_nonneg _
  have h_mul_le : ((((v1.val : ℝ) - (v2.val : ℝ)) / (4002 * (bdlLambda : ℝ))) ^ 2) *
  -- Step 2: Apply finset_fin_card_le_of_sub_sq_le with D = 4 to obtain cardinality ≤ 5.
      (((bdlAlpha2 - 1) * (bdlLambda : ℝ)) ^ 2) ≤
      ((((v1.val : ℝ) - (v2.val : ℝ)) / (4002 * (bdlLambda : ℝ))) ^ 2) *
      distSq3D (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) :=
    mul_le_mul_of_nonneg_left h_edge h_sq_nonneg
  have h_comb : (((v1.val : ℝ) - (v2.val : ℝ)) ^ 2) * ((137 / 8004 : ℝ) ^ 2) ≤ 4 := by
    linarith
  push_cast
  linarith

/-- Shows that on any 2-simplex whose altitudes have length at least $\gamma (M+1)$ with
    $\gamma \ge 7/5$, at most $3$ radial shells $u$ intersect any unit ball. -/
lemma card_uBallFinset_le (B : BundledCSSCode3D)
    (c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D))
    (h_valid : ValidLLLSphericalCapPerturbation B c)
    (x0 : Point3D)
    (s : ActiveSimplex2 (bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2)) :
    (uBallFinset (bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2) bdlSubdivPred x0 s).card ≤ 5719 := by
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  apply finset_fin_card_le_of_sub_sq_le _ 5718
  intro u1 hu1 u2 hu2
  -- Step 1: Use simplex width lower bound W ≥ (7/5) * (M + 1) to bound squared u-index difference by 8.
  dsimp [uBallFinset] at hu1 hu2
  rw [Finset.mem_filter] at hu1 hu2
  obtain ⟨v1, hv1⟩ := hu1.2
  obtain ⟨v2, hv2⟩ := hu2.2
  dsimp [vBallFinset] at hv1 hv2
  rw [Finset.mem_filter] at hv1 hv2
  rcases hv1 with ⟨_, hv1_le, hp1⟩
  rcases hv2 with ⟨_, hv2_le, hp2⟩
  have h_dist_le := distSq3D_le_four_of_mem_ball3D_one x0 _ _ hp1 hp2
  have h_lam_pos : (0 : ℝ) < (bdlLambda : ℝ) := Nat.cast_pos.mpr bdlLambda_pos
  have h_lam_ne : (bdlLambda : ℝ) ≠ 0 := ne_of_gt h_lam_pos
  have h_gamma_ge := bdlGamma_ge_seven_fifths
  have hW_pos : (0 : ℝ) ≤ (7 / 5 : ℝ) * (bdlLambda : ℝ) := by positivity
  have hW_le_gamma : (7 / 5 : ℝ) * (bdlLambda : ℝ) ≤ bdlGamma * (bdlLambda : ℝ) :=
    mul_le_mul_of_nonneg_right h_gamma_ge (le_of_lt h_lam_pos)
  have hW_sq_le : ((7 / 5 : ℝ) * (bdlLambda : ℝ)) ^ 2 ≤ (bdlGamma * (bdlLambda : ℝ)) ^ 2 := by
    nlinarith
  have h_width := h_valid.2.2.2.2.2.1 s
  have h_w_ge := triGridPos3D_distSq_ge_of_width
    (pcode.posX s.val.1) (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2)
    (bdlSubdivPred + 1) u1.val v1.val u2.val v2.val ((7 / 5 : ℝ) * (bdlLambda : ℝ))
    (Nat.succ_pos _) hv1_le hv2_le hW_pos
    (fun ε hε0 hε1 => hW_sq_le.trans (h_width ε hε0 hε1).1)
    (fun ε hε0 hε1 => hW_sq_le.trans (h_width ε hε0 hε1).2.1)
    (fun ε hε0 hε1 => hW_sq_le.trans (h_width ε hε0 hε1).2.2)
  have h_sub_eq : ((bdlSubdivPred + 1 : ℕ) : ℝ) = 4002 * (bdlLambda : ℝ) := by
    rw [bdlSubdivM_eq_succ]; dsimp [bdlSubdivM, bdlSubdivFactor, bdlAlphaNat]; push_cast; ring
  rw [h_sub_eq] at h_w_ge
  have h_lhs_eq : ((((u1.val : ℝ) - (u2.val : ℝ)) / (4002 * (bdlLambda : ℝ))) ^ 2) *
      (((7 / 5 : ℝ) * (bdlLambda : ℝ)) ^ 2) =
  -- Step 2: Apply finset_fin_card_le_of_sub_sq_le with D = 2 to obtain cardinality ≤ 3.
      (((u1.val : ℝ) - (u2.val : ℝ)) ^ 2) * ((7 / 20010 : ℝ) ^ 2) := by
    field_simp
    ring
  rw [h_lhs_eq] at h_w_ge
  have h_comb : (((u1.val : ℝ) - (u2.val : ℝ)) ^ 2) * ((7 / 20010 : ℝ) ^ 2) ≤ 4 :=
    h_w_ge.trans h_dist_le
  push_cast
  linarith

/-- **Unit-Ball Triangular Grid Packing Bound (Part I, Section 2.3 (`subsec:step2-mapping-cone`), Proposition 2.6 (`prop:mapping-cone-invariants`); Balasubramanian–Davydova–Lin (2026), Lemma 3.9)**:
    Under the Step-1 LLL simplex density ($\le 45$ simplices per unit ball), edge length,
    and altitude bounds, at most $45 \times 3 \times 5 = 675$ grid points lie in any unit ball. -/
lemma card_gridPoint_in_unit_ball_le (B : BundledCSSCode3D)
    (c : (B.Q → Point3D) × (B.M_Z → Point3D) × (B.M_X → Point3D))
    (h_valid : ValidLLLSphericalCapPerturbation B c)
    (x0 : Point3D) :
    ((Finset.univ.filter (fun gp : GridPoint (bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2) bdlSubdivPred =>
      gridPointPos (bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2) bdlSubdivPred gp ∈ ball3D x0 1)).card : ℝ) ≤
      5595 * 5719 * 118 := by
  let pcode := bdlPerturbStep B.code bdlLambda c.1 c.2.1 c.2.2
  let M := bdlSubdivPred
  -- Step 1: Bound the fiber of unit-ball grid points over each active 2-simplex s by 3 * 5 = 15.
  let S_ball : Finset (ActiveSimplex2 pcode) :=
    Finset.univ.filter (fun s : ActiveSimplex2 pcode =>
      (simplex2D3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) ∩
        ball3D x0 1).Nonempty)
  let T_ball : Finset (ActiveSimplex2 pcode × Fin (M + 2) × Fin (M + 2)) :=
    S_ball.biUnion (fun s =>
      (uBallFinset pcode M x0 s).biUnion (fun u =>
        (vBallFinset pcode M x0 s u).image (fun v => (s, u, v))))
  have h_maps : Set.MapsTo Subtype.val
      (↑(Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)) : Set (GridPoint pcode M))
      (↑T_ball : Set (ActiveSimplex2 pcode × Fin (M + 2) × Fin (M + 2))) := by
    intro gp hgp
    rw [Finset.mem_coe, Finset.mem_filter] at hgp
    rw [Finset.mem_coe]
    dsimp [T_ball]
    rw [Finset.mem_biUnion]
    refine ⟨gp.val.1, ?_, ?_⟩
    · dsimp [S_ball]
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, gridPointPos pcode M gp, ?_, hgp.2⟩
      exact triGridPos3D_mem_simplex2D3D _ _ _ (M + 1) gp.val.2.1.val gp.val.2.2.val
        (Nat.succ_pos M) (Nat.le_of_lt_succ gp.val.2.1.isLt) gp.property
    · rw [Finset.mem_biUnion]
      have hv_mem : gp.val.2.2 ∈ vBallFinset pcode M x0 gp.val.1 gp.val.2.1 := by
        dsimp [vBallFinset]
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, gp.property, hgp.2⟩
      refine ⟨gp.val.2.1, ?_, ?_⟩
      · dsimp [uBallFinset]
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, gp.val.2.2, hv_mem⟩
      · rw [Finset.mem_image]
        exact ⟨gp.val.2.2, hv_mem, rfl⟩
  have h_inj : Set.InjOn Subtype.val
      (↑(Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)) : Set (GridPoint pcode M)) :=
    Subtype.val_injective.injOn
  have h_card_le_T : (Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)).card ≤ T_ball.card :=
    Finset.card_le_card_of_injOn Subtype.val h_maps h_inj
  have h_T_le : T_ball.card ≤ S_ball.card * (5719 * 118) := by
  -- Step 2: Sum over the active 2-simplices intersecting the unit ball to get ≤ 15 * 45 = 675.
    calc T_ball.card
      _ ≤ ∑ s ∈ S_ball, ((uBallFinset pcode M x0 s).biUnion (fun u =>
            (vBallFinset pcode M x0 s u).image (fun v => (s, u, v)))).card := Finset.card_biUnion_le
      _ ≤ ∑ _s ∈ S_ball, 5719 * 118 := by
        apply Finset.sum_le_sum
        intro s _
        calc ((uBallFinset pcode M x0 s).biUnion (fun u =>
              (vBallFinset pcode M x0 s u).image (fun v => (s, u, v)))).card
          _ ≤ ∑ u ∈ uBallFinset pcode M x0 s, ((vBallFinset pcode M x0 s u).image (fun v => (s, u, v))).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _u ∈ uBallFinset pcode M x0 s, 118 := by
            apply Finset.sum_le_sum
            intro u _
            exact Finset.card_image_le.trans (card_vBallFinset_le B c h_valid x0 s u)
          _ = (uBallFinset pcode M x0 s).card * 118 := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ 5719 * 118 := Nat.mul_le_mul_right 118 (card_uBallFinset_le B c h_valid x0 s)
      _ = S_ball.card * (5719 * 118) := by rw [Finset.sum_const, smul_eq_mul]
  have h_nat : (Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)).card ≤
      S_ball.card * (5719 * 118) := h_card_le_T.trans h_T_le
  have h_real : ((Finset.univ.filter (fun gp : GridPoint pcode M => gridPointPos pcode M gp ∈ ball3D x0 1)).card : ℝ) ≤
      (S_ball.card : ℝ) * (5719 * 118 : ℝ) := by exact_mod_cast h_nat
  have h_S_le : (S_ball.card : ℝ) ≤ 5595 := h_valid.2.2.2.2.2.2 x0 |>.1
  linarith

/-! ## 2. Finite Filter Cardinality Decomposition Helpers -/

def HasNoIsolatedQ {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (code : CSSCode3D Q M_Z M_X) : Prop :=
  (∀ q : Q, (∃ x : M_X, code.checkX x q ≠ 0) → ∃ z : M_Z, code.checkZ z q ≠ 0) ∧
  (∀ q : Q, (∃ z : M_Z, code.checkZ z q ≠ 0) → ∃ x : M_X, code.checkX x q ≠ 0)

/-- Decomposes the cardinality of a filtered disjoint sum $\alpha \oplus \beta$ into the sum
    of the filtered cardinalities on $\alpha$ and $\beta$. -/
lemma card_filter_sum_eq {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : α ⊕ β → Prop) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun a : α => P (Sum.inl a))).card +
      (Finset.univ.filter (fun b : β => P (Sum.inr b))).card := by
  simp only [Finset.card_filter, Fintype.sum_sum_type]

/-- Decomposes the cardinality of a filtered product $\alpha \times \mathrm{Fin}\, 2$ into the
    sum of fibers over $0$ and $1$. -/
lemma card_filter_prod_fin2_eq {α : Type} [Fintype α] [DecidableEq α]
    (P : α × Fin 2 → Prop) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun a : α => P (a, 0))).card +
      (Finset.univ.filter (fun a : α => P (a, 1))).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

/-- Decomposes the cardinality of a filtered product $\alpha \times \beta \times \mathrm{Fin}\, 2$
    into the sum of fibers over $0$ and $1$. -/
lemma card_filter_prod_prod_fin2_eq {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : α × β × Fin 2 → Prop) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun p : α × β => P (p.1, p.2, 0))).card +
      (Finset.univ.filter (fun p : α × β => P (p.1, p.2, 1))).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

/-- Decomposes the cardinality of a filtered product $\alpha \times \mathrm{Fin}\, 3$ into the
    sum of fibers over $0, 1, 2$. -/
lemma card_filter_prod_fin3_eq {α : Type} [Fintype α] [DecidableEq α]
    (P : α × Fin 3 → Prop) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun a : α => P (a, 0))).card +
      (Finset.univ.filter (fun a : α => P (a, 1))).card +
      (Finset.univ.filter (fun a : α => P (a, 2))).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_three, Finset.sum_add_distrib]

/-- Decomposes the cardinality of a filtered product $\alpha \times \beta \times \mathrm{Fin}\, 3$
    into the sum of fibers over $0, 1, 2$. -/
lemma card_filter_prod_prod_fin3_eq {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : α × β × Fin 3 → Prop) :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun p : α × β => P (p.1, p.2, 0))).card +
      (Finset.univ.filter (fun p : α × β => P (p.1, p.2, 1))).card +
      (Finset.univ.filter (fun p : α × β => P (p.1, p.2, 2))).card := by
  simp only [Finset.card_filter, Fintype.sum_prod_type, Fin.sum_univ_three, Finset.sum_add_distrib]

/-- Bounds `(univ.filter P).card ≤ (univ.filter Q_pred).card` via an injective map $f$ that
    maps $P$-satisfying elements to $Q_{\mathrm{pred}}$-satisfying elements. -/
lemma card_filter_le_of_injective {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : α → Prop) [DecidablePred P] (Q_pred : β → Prop) [DecidablePred Q_pred]
    (f : α → β) (hf_inj : Function.Injective f) (hf_imp : ∀ a : α, P a → Q_pred (f a)) :
    (Finset.univ.filter P).card ≤ (Finset.univ.filter Q_pred).card := by
  apply Finset.card_le_card_of_injOn f
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, hf_imp a ha.2⟩
  · exact hf_inj.injOn

/-! ## 3. Injective Cell-to-Grid Embeddings (Segments, Shell Vertices, Arms) -/

def segToGrid {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) : GridPoint pcode M :=
  ⟨(⟨(seg.val.1.val.1, seg.val.1.val.2.val), ⟨seg.val.1.property, seg.val.1.val.2.property⟩⟩,
    ⟨seg.val.2.1.val + 1, Nat.succ_lt_succ seg.val.2.1.isLt⟩,
    ⟨seg.val.2.2.val + 1, Nat.succ_lt_succ seg.val.2.2.isLt⟩),
    Nat.succ_le_succ seg.property⟩

/-- Proves that the embedding `segToGrid` from `ShellSegment pcode M` into `GridPoint pcode M` is injective. -/
lemma segToGrid_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) :
    Function.Injective (segToGrid pcode M) := by
  intro seg1 seg2 h
  have h_val := congr_arg Subtype.val h
  dsimp [segToGrid] at h_val
  injection h_val with hs hp
  injection hp with hr hk
  have hs_val := congr_arg Subtype.val hs
  injection hs_val with hx heZ
  have hr_val : seg1.val.2.1 = seg2.val.2.1 := Fin.ext (Nat.succ.inj (congr_arg Fin.val hr))
  have hk_val : seg1.val.2.2 = seg2.val.2.2 := Fin.ext (Nat.succ.inj (congr_arg Fin.val hk))
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext hx (Subtype.ext heZ)
  · exact Prod.ext hr_val hk_val

/-- Shows that the 3D position of `segToGrid pcode M seg` equals the end-vertex position of `seg`. -/
lemma gridPointPos_segToGrid {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (seg : ShellSegment pcode M) :
    gridPointPos pcode M (segToGrid pcode M seg) =
      shellVertexPos pcode M (shellSegEndVertex pcode M seg) := by
  rw [shellVertexPos_end_eq]
  rfl

/-- Embeds each `ShellVertex pcode M` into `GridPoint pcode M` using `HasNoIsolatedQ` to
    select a witness 2-simplex for coarse qubit vertices. -/
def svToGrid {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (sv : ShellVertex pcode M) : GridPoint pcode M :=
  match h_v : sv.val.1.val.2 with
  | Sum.inl q =>
      have hp : pcode.checkX sv.val.1.val.1 q ≠ 0 := by
        have h_prop := sv.val.1.property; rw [h_v] at h_prop; exact h_prop
      have hz_ex := hq.1 q ⟨sv.val.1.val.1, hp⟩
      ⟨(⟨(sv.val.1.val.1, (q, Classical.choose hz_ex)), ⟨hp, Classical.choose_spec hz_ex⟩⟩,
        ⟨sv.val.2.val + 1, Nat.succ_lt_succ sv.val.2.isLt⟩,
        ⟨0, Nat.succ_pos (M + 1)⟩),
        Nat.zero_le _⟩
  | Sum.inr (Sum.inl (eZ, j)) =>
      have hp : pcode.checkX sv.val.1.val.1 eZ.val.1 ≠ 0 := by
        have h_prop := sv.val.1.property; rw [h_v] at h_prop; exact h_prop
      have h_in : j.val < sv.val.2.val := by
        have h_sr := sv.property; dsimp [InShellR] at h_sr; rw [h_v] at h_sr; exact h_sr
      ⟨(⟨(sv.val.1.val.1, eZ.val), ⟨hp, eZ.property⟩⟩,
        ⟨sv.val.2.val + 1, Nat.succ_lt_succ sv.val.2.isLt⟩,
        ⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_succ_of_lt j.isLt)⟩),
        Nat.succ_le_succ (le_of_lt h_in)⟩
  | Sum.inr (Sum.inr z) =>
      have hp : ∃ q : Q, pcode.checkX sv.val.1.val.1 q ≠ 0 ∧ pcode.checkZ z q ≠ 0 := by
        have h_prop := sv.val.1.property; rw [h_v] at h_prop; exact h_prop
      ⟨(⟨(sv.val.1.val.1, (Classical.choose hp, z)), Classical.choose_spec hp⟩,
        ⟨sv.val.2.val + 1, Nat.succ_lt_succ sv.val.2.isLt⟩,
        ⟨sv.val.2.val + 1, Nat.succ_lt_succ sv.val.2.isLt⟩),
        le_rfl⟩

/-- Shows that the 3D position of `svToGrid pcode M hq sv` agrees with `shellVertexPos pcode M sv`. -/
lemma gridPointPos_svToGrid {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (sv : ShellVertex pcode M) :
    gridPointPos pcode M (svToGrid pcode M hq sv) = shellVertexPos pcode M sv := by
  rcases sv with ⟨⟨⟨⟨x, v_bx⟩, hp⟩, r⟩, h_in⟩
  rcases v_bx with q | ⟨⟨eZ, j⟩ | z⟩
  · ext axis
    dsimp [svToGrid, gridPointPos, shellVertexPos, subdividePoint3D, triGridPos3D]
    push_cast
    ring
  · rfl
  · ext axis
    dsimp [svToGrid, gridPointPos, shellVertexPos, subdividePoint3D, triGridPos3D]
    rw [Nat.sub_self]
    push_cast
    ring

/-- Proves that the embedding `svToGrid` from `ShellVertex pcode M` into `GridPoint pcode M` is injective. -/
lemma svToGrid_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode) :
    Function.Injective (svToGrid pcode M hq) := by
  intro sv1 sv2 h_eq
  rcases sv1 with ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩
  rcases sv2 with ⟨⟨⟨⟨x2, v2⟩, hp2⟩, r2⟩, hin2⟩
  -- Step 1: Extract equality of the simplex coordinates (x, q, z) and grid indices (u, v).
  have h_x : (svToGrid pcode M hq ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩).val.1.val.1 =
      (svToGrid pcode M hq ⟨⟨⟨⟨x2, v2⟩, hp2⟩, r2⟩, hin2⟩).val.1.val.1 :=
    congr_arg (fun g : GridPoint pcode M => g.val.1.val.1) h_eq
  have h_q : (svToGrid pcode M hq ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩).val.1.val.2.1 =
      (svToGrid pcode M hq ⟨⟨⟨⟨x2, v2⟩, hp2⟩, r2⟩, hin2⟩).val.1.val.2.1 :=
    congr_arg (fun g : GridPoint pcode M => g.val.1.val.2.1) h_eq
  have h_z : (svToGrid pcode M hq ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩).val.1.val.2.2 =
      (svToGrid pcode M hq ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩).val.1.val.2.2 := rfl
  have h_z' : (svToGrid pcode M hq ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩).val.1.val.2.2 =
      (svToGrid pcode M hq ⟨⟨⟨⟨x2, v2⟩, hp2⟩, r2⟩, hin2⟩).val.1.val.2.2 :=
    congr_arg (fun g : GridPoint pcode M => g.val.1.val.2.2) h_eq
  have h_u : (svToGrid pcode M hq ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩).val.2.1.val =
      (svToGrid pcode M hq ⟨⟨⟨⟨x2, v2⟩, hp2⟩, r2⟩, hin2⟩).val.2.1.val :=
    congr_arg (fun g : GridPoint pcode M => g.val.2.1.val) h_eq
  have h_v : (svToGrid pcode M hq ⟨⟨⟨⟨x1, v1⟩, hp1⟩, r1⟩, hin1⟩).val.2.2.val =
      (svToGrid pcode M hq ⟨⟨⟨⟨x2, v2⟩, hp2⟩, r2⟩, hin2⟩).val.2.2.val :=
    congr_arg (fun g : GridPoint pcode M => g.val.2.2.val) h_eq
  -- Step 2: Case split on boundary link sectors v1, v2 and eliminate cross-sector contradictions.
  rcases v1 with q1 | ⟨⟨eZ1, j1⟩ | z1⟩ <;> rcases v2 with q2 | ⟨⟨eZ2, j2⟩ | z2⟩ <;>
    dsimp [svToGrid] at h_x h_q h_z' h_u h_v
  · subst h_x; subst h_q
    have hr : r1 = r2 := Fin.ext (Nat.succ.inj h_u)
    subst hr; rfl
  · omega
  · omega
  · omega
  · subst h_x
    have heZ : eZ1 = eZ2 := Subtype.ext (Prod.ext h_q h_z')
    have hr : r1 = r2 := Fin.ext (Nat.succ.inj h_u)
    have hj : j1 = j2 := Fin.ext (Nat.succ.inj h_v)
    subst heZ; subst hr; subst hj; rfl
  · dsimp [InShellR] at hin1
    omega
  · omega
  · dsimp [InShellR] at hin2
    omega
  · subst h_x; subst h_z'
    have hr : r1 = r2 := Fin.ext (Nat.succ.inj h_u)
    subst hr; rfl

/-- Embeds each subdivided $Z$-arm vertex `(eZ, j)` into `GridPoint pcode M` on the outer shell $u = M + 1$. -/
def armToGrid {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (p : ActiveZ pcode × Fin (M + 1)) : GridPoint pcode M :=
  have hx_ex := hq.2 p.1.val.1 ⟨p.1.val.2, p.1.property⟩
  ⟨(⟨(Classical.choose hx_ex, p.1.val), ⟨Classical.choose_spec hx_ex, p.1.property⟩⟩,
    ⟨M + 1, Nat.lt_succ_self (M + 1)⟩,
    ⟨p.2.val + 1, Nat.succ_lt_succ p.2.isLt⟩),
    Nat.succ_le_succ (Nat.le_of_lt_succ p.2.isLt)⟩

/-- Proves that the embedding `armToGrid` on subdivided $Z$-arm vertices is injective. -/
lemma armToGrid_injective {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode) :
    Function.Injective (armToGrid pcode M hq) := by
  intro p1 p2 h_eq
  have h_eZ : (armToGrid pcode M hq p1).val.1.val.2 = (armToGrid pcode M hq p2).val.1.val.2 :=
    congr_arg (fun g : GridPoint pcode M => g.val.1.val.2) h_eq
  have h_k : (armToGrid pcode M hq p1).val.2.2.val = (armToGrid pcode M hq p2).val.2.2.val :=
    congr_arg (fun g : GridPoint pcode M => g.val.2.2.val) h_eq
  dsimp [armToGrid] at h_eZ h_k
  exact Prod.ext (Subtype.ext h_eZ) (Fin.ext (Nat.succ.inj h_k))

/-- Shows that the 3D position of `armToGrid` agrees with the subdivided $Z$-arm position `xq0Pos`. -/
lemma gridPointPos_armToGrid {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (hq : HasNoIsolatedQ pcode)
    (p : ActiveZ pcode × Fin (M + 1)) :
    gridPointPos pcode M (armToGrid pcode M hq p) = xq0Pos pcode M (armEnd pcode M p.1 p.2) := by
  have hLr : (M + 1 : ℝ) ≠ 0 := by positivity
  dsimp [armToGrid, gridPointPos, xq0Pos, projXq0ToBoundaryX0, armEnd]
  by_cases hk : p.2.val < M
  · rw [dif_pos hk]
    ext axis
    dsimp [boundaryX0Pos, subdividePoint3D, triGridPos3D]
    rw [Nat.cast_sub (Nat.succ_le_succ (Nat.le_of_lt_succ p.2.isLt))]
    field_simp
    ring
  · rw [dif_neg hk]
    have hk_eq : p.2.val + 1 = M + 1 := by omega
    ext axis
    dsimp [boundaryX0Pos, triGridPos3D]
    rw [hk_eq, Nat.sub_self]
    field_simp
    ring

end WeldedHierarchy
