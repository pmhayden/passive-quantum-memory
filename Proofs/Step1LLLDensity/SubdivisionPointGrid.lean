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

import Defs.Step2CheckMatrices

/-!
# Linear Segment and Triangular 2-Simplex Subdivision Grid Metric Bounds

Establishes Euclidean metric properties for 1D segment subdivision (`subdividePoint3D`) and 2D triangular simplex subdivision (`triGridPos3D`), including step-length locality bounds (`subdividePoint3D_step_le_rloc`, `triGridPos3D_step_u`, `triGridPos3D_step_v`) and convex-hull membership (`triGridPos3D_mem_simplex2D3D`). Proves lower bounds on squared distance between distinct triangular grid points from 2-simplex altitude (`triGridPos3D_distSq_ge_of_width`).

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.2 (`def:well-separated-base`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
* Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

abbrev bdlRandomStepX := bdlStepX
abbrev bdlRandomStepZ := bdlStepZ
abbrev bdlRandomBundled := bdlWeldedBundled
abbrev bdlRandomCode := bdlWeldedCode
abbrev BDLRandomQubit := BDLWeldedQubit
abbrev BDLRandomCheckZ := BDLWeldedCheckZ
abbrev BDLRandomCheckX := BDLWeldedCheckX

/-! ## 1. Linear 3D Segment Subdivision (`subdividePoint3D`) -/

/-- At step `j = 0`, `subdividePoint3D p q L 0` equals the starting point `p`. -/
theorem subdividePoint3D_zero (p q : Point3D) (L : ℕ) :
    subdividePoint3D p q L 0 = p := by
  ext axis
  dsimp [subdividePoint3D]
  ring

/-- At step `j = L` (`L ≠ 0`), `subdividePoint3D p q L L` equals the endpoint `q`. -/
theorem subdividePoint3D_self (p q : Point3D) (L : ℕ) (hL : L ≠ 0) :
    subdividePoint3D p q L L = q := by
  ext axis
  dsimp [subdividePoint3D]
  have hL_real : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
  rw [div_self hL_real]
  ring

/-- Symmetry of squared 3D Euclidean distance `distSq3D`. -/
lemma distSq3D_comm (x y : Point3D) : distSq3D x y = distSq3D y x := by
  dsimp [distSq3D]
  ring

/-- Squared 3D Euclidean distance from a point to itself is zero. -/
lemma distSq3D_self (x : Point3D) : distSq3D x x = 0 := by
  dsimp [distSq3D]
  ring

/--
Exact squared distance between adjacent subdivision steps `j` and `j + 1` along `subdividePoint3D`:
`distSq3D (subdividePoint3D p q L (j + 1)) (subdividePoint3D p q L j) = distSq3D q p / L^2`.
-/
theorem subdividePoint3D_step_distSq (p q : Point3D) (L : ℕ) (j : ℕ) (hL : 0 < L) :
    distSq3D (subdividePoint3D p q L (j + 1)) (subdividePoint3D p q L j) =
      distSq3D q p / ((L : ℝ) ^ 2) := by
  -- Step 1: Unfold `distSq3D` and `subdividePoint3D` and simplify each coordinate difference.
  dsimp [distSq3D, subdividePoint3D]
  push_cast
  have hL_real : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hL)
  have h_axis : ∀ axis : Fin 3,
      (p axis + ((j : ℝ) + 1) / (L : ℝ) * (q axis - p axis) -
       (p axis + (j : ℝ) / (L : ℝ) * (q axis - p axis))) =
      (q axis - p axis) / (L : ℝ) := by
    intro axis
    ring
  -- Step 2: Substitute the axis differences and clear denominators via `field_simp`.
  rw [h_axis 0, h_axis 1, h_axis 2]
  field_simp [hL_real]

/--
**Subdivision Interaction Range Restoration Theorem**:
If `distSq3D q p ≤ ((L : ℝ) * r_loc) ^ 2` and `0 < L`, then for every step `j`:
`distSq3D (subdividePoint3D p q L (j + 1)) (subdividePoint3D p q L j) ≤ r_loc ^ 2`.
-/
theorem subdividePoint3D_step_le_rloc (p q : Point3D) (L : ℕ) (j : ℕ) (r_loc : ℝ)
    (hL : 0 < L) (h_dist : distSq3D q p ≤ ((L : ℝ) * r_loc) ^ 2) :
    distSq3D (subdividePoint3D p q L (j + 1)) (subdividePoint3D p q L j) ≤ r_loc ^ 2 := by
  rw [subdividePoint3D_step_distSq p q L j hL]
  have hL_pos : (0 : ℝ) < ((L : ℝ) ^ 2) := by positivity
  rw [div_le_iff₀ hL_pos]
  calc distSq3D q p
    _ ≤ ((L : ℝ) * r_loc) ^ 2 := h_dist
    _ = r_loc ^ 2 * ((L : ℝ) ^ 2) := by ring

/-- Symmetric version of `subdividePoint3D_step_le_rloc` with arguments `(j, j + 1)` and `(p, q)`. -/
lemma subdividePoint3D_step_le_rloc_symm (p q : Point3D) (L : ℕ) (j : ℕ) (r_loc : ℝ)
    (hL : 0 < L) (h_dist : distSq3D p q ≤ ((L : ℝ) * r_loc) ^ 2) :
    distSq3D (subdividePoint3D p q L j) (subdividePoint3D p q L (j + 1)) ≤ r_loc ^ 2 := by
  rw [distSq3D_comm]
  apply subdividePoint3D_step_le_rloc p q L j r_loc hL
  rw [distSq3D_comm]
  exact h_dist

/-- Squared Euclidean triangle inequality `distSq3D p r ≤ 2 * distSq3D p q + 2 * distSq3D q r`. -/
lemma distSq3D_triangle (p q r : Point3D) :
    distSq3D p r ≤ 2 * distSq3D p q + 2 * distSq3D q r := by
  dsimp [distSq3D]
  nlinarith [sq_nonneg ((p 0 - q 0) - (q 0 - r 0)),
             sq_nonneg ((p 1 - q 1) - (q 1 - r 1)),
             sq_nonneg ((p 2 - q 2) - (q 2 - r 2))]

/-- Homothety identity for `subdividePoint3D` sharing a common origin `p` at step `j`. -/
lemma distSq3D_subdividePoint3D_eq_mul (p q1 q2 : Point3D) (L j : ℕ) :
    distSq3D (subdividePoint3D p q1 L j) (subdividePoint3D p q2 L j) =
      ((j : ℝ) / (L : ℝ)) ^ 2 * distSq3D q1 q2 := by
  dsimp [distSq3D, subdividePoint3D]
  ring

/-- Contraction bound for `subdividePoint3D` rays from a common origin `p` when `j ≤ L`. -/
lemma distSq3D_subdividePoint3D_same_origin (p q1 q2 : Point3D) (L j : ℕ) (hj : j ≤ L) :
    distSq3D (subdividePoint3D p q1 L j) (subdividePoint3D p q2 L j) ≤ distSq3D q1 q2 := by
  by_cases hL : L = 0
  · subst hL
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst hj0
    rw [subdividePoint3D_zero, subdividePoint3D_zero, distSq3D_self]
    dsimp [distSq3D]; positivity
  · rw [distSq3D_subdividePoint3D_eq_mul p q1 q2 L j]
    have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hL)
    have ht0 : 0 ≤ (j : ℝ) / (L : ℝ) := div_nonneg (Nat.cast_nonneg j) (le_of_lt hL_pos)
    have ht1 : (j : ℝ) / (L : ℝ) ≤ 1 := (div_le_one hL_pos).mpr (Nat.cast_le.mpr hj)
    have htsq : ((j : ℝ) / (L : ℝ)) ^ 2 ≤ 1 := by nlinarith
    have hd : 0 ≤ distSq3D q1 q2 := by dsimp [distSq3D]; positivity
    nlinarith

/-- Any intermediate subdivision point `subdividePoint3D p q L j` (`j ≤ L`) lies no farther from `p`
than `q` does. -/
lemma distSq3D_subdividePoint3D_le_right (p q : Point3D) (L j : ℕ) (hj : j ≤ L) :
    distSq3D p (subdividePoint3D p q L j) ≤ distSq3D p q := by
  have h0 : distSq3D p (subdividePoint3D p q L j) =
      distSq3D (subdividePoint3D p p L j) (subdividePoint3D p q L j) := by
    dsimp [distSq3D, subdividePoint3D]; ring
  rw [h0]
  exact distSq3D_subdividePoint3D_same_origin p p q L j hj

/-! ## 2. Boundary Subdivision Arm and Shell Vertex Geometry -/

/-- The 3D position of `bxStart pcode M eZ k` equals `subdividePoint3D` at step `k.val`. -/
lemma boundaryX0Pos_bxStart_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) :
    boundaryX0Pos pcode M (bxStart pcode M eZ k) =
      subdividePoint3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (M + 1) k.val := by
  dsimp [bxStart, armStart]
  split_ifs with h
  · dsimp [projXq0ToBoundaryX0, boundaryX0Pos]
    rw [h, subdividePoint3D_zero]
  · dsimp [projXq0ToBoundaryX0, boundaryX0Pos]
    rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]

/-- The 3D position of `bxEnd pcode M eZ k` equals `subdividePoint3D` at step `k.val + 1`. -/
lemma boundaryX0Pos_bxEnd_eq {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) :
    boundaryX0Pos pcode M (bxEnd pcode M eZ k) =
      subdividePoint3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) (M + 1) (k.val + 1) := by
  dsimp [bxEnd, armEnd]
  split_ifs with h
  · dsimp [projXq0ToBoundaryX0, boundaryX0Pos]
  · dsimp [projXq0ToBoundaryX0, boundaryX0Pos]
    have hk : k.val + 1 = M + 1 := by omega
    rw [hk, subdividePoint3D_self _ _ (M + 1) (Nat.succ_ne_zero M)]

/-- Adjacent boundary arm vertices `bxStart` and `bxEnd` lie within squared distance `r_loc ^ 2`. -/
lemma distSq3D_bxStart_bxEnd_le_rloc {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (eZ : ActiveZ pcode) (k : Fin (M + 1)) (r_loc : ℝ)
    (h_dist : distSq3D (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2) ≤ (((M + 1 : ℕ) : ℝ) * r_loc) ^ 2) :
    distSq3D (boundaryX0Pos pcode M (bxStart pcode M eZ k))
             (boundaryX0Pos pcode M (bxEnd pcode M eZ k)) ≤ r_loc ^ 2 := by
  rw [boundaryX0Pos_bxStart_eq, boundaryX0Pos_bxEnd_eq]
  exact subdividePoint3D_step_le_rloc_symm _ _ (M + 1) k.val r_loc (Nat.succ_pos M) h_dist

/-- Explicit 3D coordinate evaluation of a shell vertex `(x, v, r)` by boundary case. -/
def shellVertexPosV {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (x : M_X) (v : BoundaryX0 pcode M) (r : ℕ) : Point3D :=
  match v with
  | Sum.inl q =>
      subdividePoint3D (pcode.posX x) (pcode.posQ q) (M + 1) (r + 1)
  | Sum.inr (Sum.inl (eZ, j)) =>
      triGridPos3D (pcode.posX x) (pcode.posQ eZ.val.1) (pcode.posZ eZ.val.2)
        (M + 1) (r + 1) (j.val + 1)
  | Sum.inr (Sum.inr z) =>
      subdividePoint3D (pcode.posX x) (pcode.posZ z) (M + 1) (r + 1)

/-- Definitional equality unpacking `shellVertexPos` into `shellVertexPosV`. -/
lemma shellVertexPos_eq_V {Q M_Z M_X : Type}
    [Fintype Q] [DecidableEq Q] [Fintype M_Z] [DecidableEq M_Z] [Fintype M_X] [DecidableEq M_X]
    (pcode : CSSCode3D Q M_Z M_X) (M : ℕ) (sv : ShellVertex pcode M) :
    shellVertexPos pcode M sv = shellVertexPosV pcode M sv.val.1.val.1 sv.val.1.val.2 sv.val.2.val := rfl

/-- Exact squared distance of a single step along the `v` parameter of `triGridPos3D`. -/
lemma triGridPos3D_step_v (pX pQ pZ : Point3D) (L u v : ℕ) (hL : 0 < L) (hvu : v + 1 ≤ u) :
    distSq3D (triGridPos3D pX pQ pZ L u v) (triGridPos3D pX pQ pZ L u (v + 1)) =
      distSq3D pQ pZ / ((L : ℝ) ^ 2) := by
  -- Step 1: Unfold `triGridPos3D` and rewrite `(u - v : ℝ) = (u - (v + 1) : ℝ) + 1`.
  dsimp [distSq3D, triGridPos3D]
  have h_sub : ((u - v : ℕ) : ℝ) = ((u - (v + 1) : ℕ) : ℝ) + 1 := by
    have : u - v = (u - (v + 1)) + 1 := by omega
    exact_mod_cast this
  rw [h_sub]
  push_cast
  -- Step 2: Simplify each coordinate difference and clear denominators.
  have hL_real : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hL)
  have h_axis : ∀ axis : Fin 3,
      (pX axis + ((u - (v + 1) : ℕ) + 1) / (L : ℝ) * (pQ axis - pX axis) + (v : ℝ) / (L : ℝ) * (pZ axis - pX axis) -
      (pX axis + ((u - (v + 1) : ℕ) : ℝ) / (L : ℝ) * (pQ axis - pX axis) + ((v : ℝ) + 1) / (L : ℝ) * (pZ axis - pX axis))) =
      (pQ axis - pZ axis) / (L : ℝ) := by
    intro axis; ring
  rw [h_axis 0, h_axis 1, h_axis 2]
  field_simp [hL_real]

/-- Exact squared distance of a single step along the `u` parameter of `triGridPos3D`. -/
lemma triGridPos3D_step_u (pX pQ pZ : Point3D) (L u v : ℕ) (hL : 0 < L) (hvu : v ≤ u) :
    distSq3D (triGridPos3D pX pQ pZ L (u + 1) v) (triGridPos3D pX pQ pZ L u v) =
      distSq3D pQ pX / ((L : ℝ) ^ 2) := by
  -- Step 1: Unfold `triGridPos3D` and rewrite `(u + 1 - v : ℝ) = (u - v : ℝ) + 1`.
  dsimp [distSq3D, triGridPos3D]
  have h_sub : ((u + 1 - v : ℕ) : ℝ) = ((u - v : ℕ) : ℝ) + 1 := by
    have : u + 1 - v = (u - v) + 1 := by omega
    exact_mod_cast this
  rw [h_sub]
  -- Step 2: Simplify each coordinate difference and clear denominators.
  have hL_real : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hL)
  have h_axis : ∀ axis : Fin 3,
      (pX axis + (((u - v : ℕ) : ℝ) + 1) / (L : ℝ) * (pQ axis - pX axis) + (v : ℝ) / (L : ℝ) * (pZ axis - pX axis) -
      (pX axis + ((u - v : ℕ) : ℝ) / (L : ℝ) * (pQ axis - pX axis) + (v : ℝ) / (L : ℝ) * (pZ axis - pX axis))) =
      (pQ axis - pX axis) / (L : ℝ) := by
    intro axis; ring
  rw [h_axis 0, h_axis 1, h_axis 2]
  field_simp [hL_real]

/-! ## 3. Barycentric Difference Identities & Simplex Altitude Separation -/

lemma bdlGamma_ge_seven_fifths : (7 / 5 : ℝ) ≤ bdlGamma := by
  dsimp [bdlGamma, bdlAlpha, bdlAlphaNat, bdlAlpha2, bdlAlpha1]
  have h_abs : |(139 / 2 / 1000 : ℝ)| ≤ 1 := by norm_num
  have h_cb := (abs_le.mp (Real.cos_bound h_abs)).2
  rw [abs_of_nonneg (by norm_num)] at h_cb
  linarith

/-- Triangle inequality bound: any two points inside a unit ball `Ball3D x0 1` have squared
    Euclidean distance at most $2^2 = 4$. -/
lemma distSq3D_le_four_of_mem_ball3D_one (x0 p1 p2 : Point3D)
    (hp1 : p1 ∈ ball3D x0 1) (hp2 : p2 ∈ ball3D x0 1) :
    distSq3D p1 p2 ≤ 4 := by
  dsimp [ball3D] at hp1 hp2
  have h_tri := distSq3D_triangle p1 x0 p2
  have h_comm : distSq3D x0 p2 = distSq3D p2 x0 := distSq3D_comm x0 p2
  linarith

/-- Shows that every triangular grid point `triGridPos3D P0 P1 P2 L u v` ($v \le u \le L$)
    lies in the convex hull `Simplex2D3D P0 P1 P2`. -/
lemma triGridPos3D_mem_simplex2D3D (P0 P1 P2 : Point3D) (L u v : ℕ)
    (hL : 0 < L) (hu : u ≤ L) (hv : v ≤ u) :
    triGridPos3D P0 P1 P2 L u v ∈ simplex2D3D P0 P1 P2 := by
  have hLr : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  refine ⟨((L - u : ℕ) : ℝ) / (L : ℝ), ((u - v : ℕ) : ℝ) / (L : ℝ), (v : ℝ) / (L : ℝ),
    by positivity, by positivity, by positivity, ?_, ?_⟩
  · rw [Nat.cast_sub hu, Nat.cast_sub hv]
    field_simp
    ring
  · intro axis
    dsimp [triGridPos3D]
    rw [Nat.cast_sub hu, Nat.cast_sub hv]
    field_simp
    ring

/-- Exact formula for the squared distance between two triangular grid points on the same
    radial shell $u$: $\|g(u, v_1) - g(u, v_2)\|^2 = ((v_1 - v_2)/L)^2 \|P_2 - P_1\|^2$. -/
lemma triGridPos3D_same_u_distSq (P0 P1 P2 : Point3D) (L u v1 v2 : ℕ)
    (hv1 : v1 ≤ u) (hv2 : v2 ≤ u) :
    distSq3D (triGridPos3D P0 P1 P2 L u v1) (triGridPos3D P0 P1 P2 L u v2) =
      ((((v1 : ℝ) - (v2 : ℝ)) / (L : ℝ)) ^ 2) * distSq3D P2 P1 := by
  dsimp [distSq3D, triGridPos3D]
  rw [Nat.cast_sub hv1, Nat.cast_sub hv2]
  ring

/-- Algebraic barycentric identity decomposing the difference of two grid points relative
    to vertex $a_1$ and the opposite edge $[a_0, a_2]$ when $(u_1 - u_2) - (v_1 - v_2) \ne 0$. -/
lemma bary_diff_case1 (a0 a1 a2 Lr u1 v1 u2 v2 : ℝ) (hL : Lr ≠ 0)
    (hdb : (u1 - u2) - (v1 - v2) ≠ 0) :
    (a0 + ((u1 - v1) / Lr) * (a1 - a0) + (v1 / Lr) * (a2 - a0)) -
    (a0 + ((u2 - v2) / Lr) * (a1 - a0) + (v2 / Lr) * (a2 - a0)) =
    (((u1 - u2) - (v1 - v2)) / Lr) *
      (a1 - ((1 - (-(v1 - v2) / ((u1 - u2) - (v1 - v2)))) * a0 +
        (-(v1 - v2) / ((u1 - u2) - (v1 - v2))) * a2)) := by
  field_simp
  ring

/-- Algebraic barycentric identity decomposing the difference of two grid points relative
    to vertex $a_0$ and the opposite edge $[a_1, a_2]$ when $u_1 - u_2 \ne 0$. -/
lemma bary_diff_case2 (a0 a1 a2 Lr u1 v1 u2 v2 : ℝ) (hL : Lr ≠ 0)
    (hdu : u1 - u2 ≠ 0) :
    (a0 + ((u1 - v1) / Lr) * (a1 - a0) + (v1 / Lr) * (a2 - a0)) -
    (a0 + ((u2 - v2) / Lr) * (a1 - a0) + (v2 / Lr) * (a2 - a0)) =
    (-(u1 - u2) / Lr) *
      (a0 - ((1 - ((v1 - v2) / (u1 - u2))) * a1 +
        ((v1 - v2) / (u1 - u2)) * a2)) := by
  field_simp
  ring

/-- Algebraic barycentric identity decomposing the difference of two grid points relative
    to vertex $a_2$ and the opposite edge $[a_0, a_1]$ when $v_1 - v_2 \ne 0$. -/
lemma bary_diff_case3 (a0 a1 a2 Lr u1 v1 u2 v2 : ℝ) (hL : Lr ≠ 0)
    (hdv : v1 - v2 ≠ 0) :
    (a0 + ((u1 - v1) / Lr) * (a1 - a0) + (v1 / Lr) * (a2 - a0)) -
    (a0 + ((u2 - v2) / Lr) * (a1 - a0) + (v2 / Lr) * (a2 - a0)) =
    ((v1 - v2) / Lr) *
      (a2 - ((1 - (((v1 - v2) - (u1 - u2)) / (v1 - v2))) * a0 +
        (((v1 - v2) - (u1 - u2)) / (v1 - v2)) * a1)) := by
  field_simp
  ring

/-- **Triangular Grid Separation Bound (Ordered Shells $u_2 \le u_1$, Part I, Section 2.3 (`subsec:step2-mapping-cone`), Definition 2.5 (`def:three-layer-mapping-cone`))**:
    If all three altitudes of a 2-simplex $(P_0, P_1, P_2)$ have length at least $W$, then any
    two grid points with $u_2 \le u_1$ are separated by at least $((u_1 - u_2)/L)^2 W^2$. -/
lemma triGridPos3D_distSq_ge_of_width_le (P0 P1 P2 : Point3D) (L u1 v1 u2 v2 : ℕ) (W : ℝ)
    (hL : 0 < L) (hv1 : v1 ≤ u1) (hv2 : v2 ≤ u2) (hu_le : u2 ≤ u1) (_hW : 0 ≤ W)
    (h0 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → W ^ 2 ≤ distSq3D P0 (lerpPoint3D P1 P2 ε))
    (h1 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → W ^ 2 ≤ distSq3D P1 (lerpPoint3D P0 P2 ε))
    (h2 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → W ^ 2 ≤ distSq3D P2 (lerpPoint3D P0 P1 ε)) :
    ((((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ)) ^ 2) * (W ^ 2) ≤
      distSq3D (triGridPos3D P0 P1 P2 L u1 v1) (triGridPos3D P0 P1 P2 L u2 v2) := by
  have hLr : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hLr
  -- Step 1: Handle the degenerate case u1 = u2 and set up strict inequality u2 < u1.
  by_cases hu_eq : u1 = u2
  · subst hu_eq
    rw [sub_self, zero_div, sq, zero_mul, zero_mul]
    dsimp [distSq3D]; positivity
  · have hu_lt : u2 < u1 := Nat.lt_of_le_of_ne hu_le (Ne.symm hu_eq)
    have hdu_pos : (0 : ℝ) < (u1 : ℝ) - (u2 : ℝ) := sub_pos.mpr (Nat.cast_lt.mpr hu_lt)
  -- Step 2: Case 1 (v1 - v2 ≤ 0): express the displacement via bary_diff_case1 and altitude from P1.
    rcases le_total ((v1 : ℝ) - (v2 : ℝ)) 0 with hdv_neg | hdv_nonneg
    · have hdb_pos : (0 : ℝ) < ((u1 : ℝ) - (u2 : ℝ)) - ((v1 : ℝ) - (v2 : ℝ)) := by linarith
      let ε : ℝ := -((v1 : ℝ) - (v2 : ℝ)) / (((u1 : ℝ) - (u2 : ℝ)) - ((v1 : ℝ) - (v2 : ℝ)))
      have hε0 : 0 ≤ ε := div_nonneg (by linarith) (le_of_lt hdb_pos)
      have hε1 : ε ≤ 1 := (div_le_one hdb_pos).mpr (by linarith)
      have h_eq : distSq3D (triGridPos3D P0 P1 P2 L u1 v1) (triGridPos3D P0 P1 P2 L u2 v2) =
          ((((u1 : ℝ) - (u2 : ℝ)) - ((v1 : ℝ) - (v2 : ℝ))) / (L : ℝ)) ^ 2 *
            distSq3D P1 (lerpPoint3D P0 P2 ε) := by
        dsimp [distSq3D, triGridPos3D, lerpPoint3D, ε]
        rw [Nat.cast_sub hv1, Nat.cast_sub hv2,
          bary_diff_case1 (P0 0) (P1 0) (P2 0) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdb_pos),
          bary_diff_case1 (P0 1) (P1 1) (P2 1) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdb_pos),
          bary_diff_case1 (P0 2) (P1 2) (P2 2) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdb_pos)]
        ring
      rw [h_eq]
      have hW_le := h1 ε hε0 hε1
      have h_div_le : ((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ) ≤
          (((u1 : ℝ) - (u2 : ℝ)) - ((v1 : ℝ) - (v2 : ℝ))) / (L : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hLr)
      have h_div_nonneg : 0 ≤ ((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ) := div_nonneg (le_of_lt hdu_pos) (le_of_lt hLr)
      have h_sq_le : (((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ)) ^ 2 ≤
          ((((u1 : ℝ) - (u2 : ℝ)) - ((v1 : ℝ) - (v2 : ℝ))) / (L : ℝ)) ^ 2 := by nlinarith
      nlinarith
  -- Step 3: Cases 2 and 3 (0 ≤ v1 - v2): use bary_diff_case2 (altitude from P0) or bary_diff_case3 (altitude from P2).
    · rcases le_total ((v1 : ℝ) - (v2 : ℝ)) ((u1 : ℝ) - (u2 : ℝ)) with hdv_le | hdv_ge
      · let ε : ℝ := ((v1 : ℝ) - (v2 : ℝ)) / ((u1 : ℝ) - (u2 : ℝ))
        have hε0 : 0 ≤ ε := div_nonneg hdv_nonneg (le_of_lt hdu_pos)
        have hε1 : ε ≤ 1 := (div_le_one hdu_pos).mpr hdv_le
        have h_eq : distSq3D (triGridPos3D P0 P1 P2 L u1 v1) (triGridPos3D P0 P1 P2 L u2 v2) =
            (((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ)) ^ 2 *
              distSq3D P0 (lerpPoint3D P1 P2 ε) := by
          dsimp [distSq3D, triGridPos3D, lerpPoint3D, ε]
          rw [Nat.cast_sub hv1, Nat.cast_sub hv2,
            bary_diff_case2 (P0 0) (P1 0) (P2 0) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdu_pos),
            bary_diff_case2 (P0 1) (P1 1) (P2 1) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdu_pos),
            bary_diff_case2 (P0 2) (P1 2) (P2 2) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdu_pos)]
          ring
        rw [h_eq]
        have hW_le := h0 ε hε0 hε1
        have h_sq_nonneg : 0 ≤ (((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ)) ^ 2 := sq_nonneg _
        nlinarith
      · have hdv_pos : (0 : ℝ) < (v1 : ℝ) - (v2 : ℝ) := by linarith
        let ε : ℝ := (((v1 : ℝ) - (v2 : ℝ)) - ((u1 : ℝ) - (u2 : ℝ))) / ((v1 : ℝ) - (v2 : ℝ))
        have hε0 : 0 ≤ ε := div_nonneg (by linarith) (le_of_lt hdv_pos)
        have hε1 : ε ≤ 1 := (div_le_one hdv_pos).mpr (by linarith)
        have h_eq : distSq3D (triGridPos3D P0 P1 P2 L u1 v1) (triGridPos3D P0 P1 P2 L u2 v2) =
            (((v1 : ℝ) - (v2 : ℝ)) / (L : ℝ)) ^ 2 *
              distSq3D P2 (lerpPoint3D P0 P1 ε) := by
          dsimp [distSq3D, triGridPos3D, lerpPoint3D, ε]
          rw [Nat.cast_sub hv1, Nat.cast_sub hv2,
            bary_diff_case3 (P0 0) (P1 0) (P2 0) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdv_pos),
            bary_diff_case3 (P0 1) (P1 1) (P2 1) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdv_pos),
            bary_diff_case3 (P0 2) (P1 2) (P2 2) (L : ℝ) u1 v1 u2 v2 hL_ne (ne_of_gt hdv_pos)]
          ring
        rw [h_eq]
        have hW_le := h2 ε hε0 hε1
        have h_div_le : ((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ) ≤ ((v1 : ℝ) - (v2 : ℝ)) / (L : ℝ) :=
          div_le_div_of_nonneg_right hdv_ge (le_of_lt hLr)
        have h_div_nonneg : 0 ≤ ((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ) := div_nonneg (le_of_lt hdu_pos) (le_of_lt hLr)
        have h_sq_le : (((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ)) ^ 2 ≤
            (((v1 : ℝ) - (v2 : ℝ)) / (L : ℝ)) ^ 2 := by nlinarith
        nlinarith

/-- Symmetric form of `triGridPos3D_distSq_ge_of_width_le` for arbitrary radial shell indices $u_1, u_2$. -/
lemma triGridPos3D_distSq_ge_of_width (P0 P1 P2 : Point3D) (L u1 v1 u2 v2 : ℕ) (W : ℝ)
    (hL : 0 < L) (hv1 : v1 ≤ u1) (hv2 : v2 ≤ u2) (hW : 0 ≤ W)
    (h0 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → W ^ 2 ≤ distSq3D P0 (lerpPoint3D P1 P2 ε))
    (h1 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → W ^ 2 ≤ distSq3D P1 (lerpPoint3D P0 P2 ε))
    (h2 : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → W ^ 2 ≤ distSq3D P2 (lerpPoint3D P0 P1 ε)) :
    ((((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ)) ^ 2) * (W ^ 2) ≤
      distSq3D (triGridPos3D P0 P1 P2 L u1 v1) (triGridPos3D P0 P1 P2 L u2 v2) := by
  rcases le_total u2 u1 with h_le | h_le
  · exact triGridPos3D_distSq_ge_of_width_le P0 P1 P2 L u1 v1 u2 v2 W hL hv1 hv2 h_le hW h0 h1 h2
  · rw [distSq3D_comm]
    have h_symm : ((((u1 : ℝ) - (u2 : ℝ)) / (L : ℝ)) ^ 2) * (W ^ 2) =
        ((((u2 : ℝ) - (u1 : ℝ)) / (L : ℝ)) ^ 2) * (W ^ 2) := by ring
    rw [h_symm]
    exact triGridPos3D_distSq_ge_of_width_le P0 P1 P2 L u2 v2 u1 v1 W hL hv2 hv1 h_le hW h0 h1 h2

/-- Discrete 1D packing lemma: if every pair of elements in $S \subseteq \mathrm{Fin}\, N$
    satisfies $(x - y)^2 \le D^2$, then $|S| \le D + 1$. -/
lemma finset_fin_card_le_of_sub_sq_le {N : ℕ} (S : Finset (Fin N)) (D : ℕ)
    (h_sub : ∀ a ∈ S, ∀ b ∈ S, ((a.val : ℝ) - (b.val : ℝ)) ^ 2 ≤ (D : ℝ) ^ 2) :
    S.card ≤ D + 1 := by
  by_cases hS : S.Nonempty
  · obtain ⟨b, hb_mem, hb_min⟩ := S.exists_min_image Fin.val hS
    have h_maps : Set.MapsTo (fun a : Fin N => a.val - b.val) (↑S : Set (Fin N)) (↑(Finset.range (D + 1)) : Set ℕ) := by
      intro a ha
      rw [Finset.mem_coe] at ha ⊢
      rw [Finset.mem_range]
      dsimp only
      have h_le : b.val ≤ a.val := hb_min a ha
      have h_sq := h_sub a ha b hb_mem
      have hD_nonneg : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
      have h_diff_le : (a.val : ℝ) - (b.val : ℝ) ≤ (D : ℝ) := by nlinarith
      have h_nat : a.val - b.val ≤ D := by
        have : ((a.val - b.val : ℕ) : ℝ) ≤ (D : ℝ) := by
          rw [Nat.cast_sub h_le]
          exact h_diff_le
        exact Nat.cast_le.mp this
      omega
    have h_inj : Set.InjOn (fun a : Fin N => a.val - b.val) (↑S : Set (Fin N)) := by
      intro a1 ha1 a2 ha2 h_eq
      rw [Finset.mem_coe] at ha1 ha2
      dsimp only at h_eq
      have h1 : b.val ≤ a1.val := hb_min a1 ha1
      have h2 : b.val ≤ a2.val := hb_min a2 ha2
      ext
      omega
    calc S.card
      _ ≤ (Finset.range (D + 1)).card := Finset.card_le_card_of_injOn _ h_maps h_inj
      _ = D + 1 := Finset.card_range (D + 1)
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    rw [hS, Finset.card_empty]
    omega

end WeldedHierarchy
