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

import Proofs.Step1LLLDensity.NonIsolatedQubitsInvariant

/-!
# Rational Spherical-Cap Parameterization, Cramer Residuals, and Simplex Width Bounds

Defines 3D vector algebra operations (`dot3D`, `cross3D`, `det3D`, `sub3D`), proves the four-plane Cramer residual inequality `four_planes_cramer_residual_bound` for simplices intersecting a unit ball, and introduces the rational stereographic parameterization (`rcos`, `rsin`) of the axis-aligned spherical caps (`rationalCap0`, `rationalCap1`, `rationalCap2`). Establishes perturbed edge-length and altitude bounds (`rationalCap_edgeZ_bounds`, `rationalCap_edgeX_bounds`, `rationalCap_simplex_width_bounds`) under `HasInteractionRange8`.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.2 (`def:well-separated-base`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. 3D Vector Algebra & Four-Plane Cramer Residual Bounds -/

def dot3D (u v : Point3D) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Standard 3D vector cross product $u \times v$ on `Point3D`. -/
def cross3D (u v : Point3D) : Point3D :=
  fun i => match i with
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- Determinant $\det(u, v, w) = \langle u, v \times w \rangle$ of three 3D vectors. -/
def det3D (u v w : Point3D) : ℝ :=
  dot3D u (cross3D v w)

/-- Coordinatewise difference $u - v$ of two 3D points. -/
def sub3D (u v : Point3D) : Point3D :=
  fun i => u i - v i

/-- **2-Simplex Normal Plane Residual Bound (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`); Balasubramanian–Davydova–Lin (2026), Lemma 3.8)**:
    If a 2-simplex $(A, B, C)$ intersects `Ball3D x0 1` and its edge lengths are bounded by $E$,
    then the plane residual $|\langle A - x_0, (B - A) \times (C - A) \rangle|$ is at most $E^2$. -/
lemma simplex2D3D_inter_ball3D_plane_residual (A B C x0 : Point3D)
    (h_inter : (simplex2D3D A B C ∩ ball3D x0 1).Nonempty) :
    let N := cross3D (sub3D B A) (sub3D C A)
    (dot3D N (sub3D x0 A)) ^ 2 ≤ dot3D N N := by
  intro N
  -- Step 1: Extract a point p in the intersection and show N is orthogonal to p - A.
  obtain ⟨p, hp_simp, hp_ball⟩ := h_inter
  obtain ⟨t1, t2, t3, _, _, _, ht, hp⟩ := hp_simp
  have hp0 : p 0 = t1 * A 0 + t2 * B 0 + t3 * C 0 := hp 0
  have hp1 : p 1 = t1 * A 1 + t2 * B 1 + t3 * C 1 := hp 1
  have hp2 : p 2 = t1 * A 2 + t2 * B 2 + t3 * C 2 := hp 2
  have h_plane : dot3D N (sub3D p A) = 0 := by
    dsimp [N, dot3D, cross3D, sub3D]
    rw [hp0, hp1, hp2]
    linear_combination ((B 1 - A 1) * (C 2 - A 2) * A 0 - (B 2 - A 2) * (C 1 - A 1) * A 0 +
      (B 2 - A 2) * (C 0 - A 0) * A 1 - (B 0 - A 0) * (C 2 - A 2) * A 1 +
      (B 0 - A 0) * (C 1 - A 1) * A 2 - (B 1 - A 1) * (C 0 - A 0) * A 2) * ht
  have h_eq : dot3D N (sub3D x0 A) = - dot3D N (sub3D p x0) := by
    dsimp [dot3D, sub3D] at h_plane ⊢
    linarith
  -- Step 2: Apply Lagrange's identity (Cauchy–Schwarz in 3D) and ||p - x0||^2 ≤ 1.
  have h_cs : dot3D N N * distSq3D p x0 - (dot3D N (sub3D p x0)) ^ 2 =
      (N 0 * (p 1 - x0 1) - N 1 * (p 0 - x0 0)) ^ 2 +
      (N 1 * (p 2 - x0 2) - N 2 * (p 1 - x0 1)) ^ 2 +
      (N 2 * (p 0 - x0 0) - N 0 * (p 2 - x0 2)) ^ 2 := by
    dsimp [dot3D, sub3D, distSq3D]
    ring
  have h_ball : distSq3D p x0 ≤ 1 := by
    dsimp [ball3D] at hp_ball
    linarith
  have h_N_nonneg : 0 ≤ dot3D N N := by
    dsimp [dot3D]
    nlinarith [sq_nonneg (N 0), sq_nonneg (N 1), sq_nonneg (N 2)]
  have h_eq_sq : (dot3D N (sub3D x0 A)) ^ 2 = (dot3D N (sub3D p x0)) ^ 2 := by
    rw [h_eq]; ring
  have h_mul : dot3D N N * distSq3D p x0 ≤ dot3D N N := by
    nlinarith [h_N_nonneg, h_ball]
  linarith [sq_nonneg (N 0 * (p 1 - x0 1) - N 1 * (p 0 - x0 0)),
            sq_nonneg (N 1 * (p 2 - x0 2) - N 2 * (p 1 - x0 1)),
            sq_nonneg (N 2 * (p 0 - x0 0) - N 0 * (p 2 - x0 2))]

/-- **Four-Simplex Cramer Elimination Identity (Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`); Balasubramanian–Davydova–Lin (2026), Lemma 3.8)**:
    Eliminates the common ball center $x_0$ from four plane equations $\langle x_0, N_i \rangle = b_i - r_i$
    via Cramer's rule, bounding the $3 \times 3$ determinant residual by the sum of $|r_i| \cdot |\det|$. -/
lemma four_planes_cramer_residual_bound (N1 N2 N3 N4 x0 : Point3D) (b1 b2 b3 b4 : ℝ)
    (h1 : (dot3D N1 x0 - b1) ^ 2 ≤ dot3D N1 N1)
    (h2 : (dot3D N2 x0 - b2) ^ 2 ≤ dot3D N2 N2)
    (h3 : (dot3D N3 x0 - b3) ^ 2 ≤ dot3D N3 N3)
    (h4 : (dot3D N4 x0 - b4) ^ 2 ≤ dot3D N4 N4) :
    let D1 := det3D N2 N3 N4
    let D2 := - det3D N1 N3 N4
    let D3 := det3D N1 N2 N4
    let D4 := - det3D N1 N2 N3
    (D1 * b1 + D2 * b2 + D3 * b3 + D4 * b4) ^ 2 ≤
      4 * (D1 ^ 2 * dot3D N1 N1 + D2 ^ 2 * dot3D N2 N2 + D3 ^ 2 * dot3D N3 N3 + D4 ^ 2 * dot3D N4 N4) := by
  intro D1 D2 D3 D4
  let r1 := dot3D N1 x0 - b1
  let r2 := dot3D N2 x0 - b2
  let r3 := dot3D N3 x0 - b3
  let r4 := dot3D N4 x0 - b4
  have hr1 : D1 ^ 2 * r1 ^ 2 ≤ D1 ^ 2 * dot3D N1 N1 := mul_le_mul_of_nonneg_left h1 (sq_nonneg D1)
  have hr2 : D2 ^ 2 * r2 ^ 2 ≤ D2 ^ 2 * dot3D N2 N2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg D2)
  have hr3 : D3 ^ 2 * r3 ^ 2 ≤ D3 ^ 2 * dot3D N3 N3 := mul_le_mul_of_nonneg_left h3 (sq_nonneg D3)
  have hr4 : D4 ^ 2 * r4 ^ 2 ≤ D4 ^ 2 * dot3D N4 N4 := mul_le_mul_of_nonneg_left h4 (sq_nonneg D4)
  have h_id : (D1 * b1 + D2 * b2 + D3 * b3 + D4 * b4) ^ 2 = (D1 * r1 + D2 * r2 + D3 * r3 + D4 * r4) ^ 2 := by
    dsimp [D1, D2, D3, D4, r1, r2, r3, r4, det3D, dot3D, cross3D]
    ring
  have h_cs4 : 4 * (D1 ^ 2 * r1 ^ 2 + D2 ^ 2 * r2 ^ 2 + D3 ^ 2 * r3 ^ 2 + D4 ^ 2 * r4 ^ 2) -
      (D1 * r1 + D2 * r2 + D3 * r3 + D4 * r4) ^ 2 =
      (D1 * r1 - D2 * r2) ^ 2 + (D1 * r1 - D3 * r3) ^ 2 + (D1 * r1 - D4 * r4) ^ 2 +
      (D2 * r2 - D3 * r3) ^ 2 + (D2 * r2 - D4 * r4) ^ 2 + (D3 * r3 - D4 * r4) ^ 2 := by
    ring
  linarith [sq_nonneg (D1 * r1 - D2 * r2), sq_nonneg (D1 * r1 - D3 * r3),
            sq_nonneg (D1 * r1 - D4 * r4), sq_nonneg (D2 * r2 - D3 * r3),
            sq_nonneg (D2 * r2 - D4 * r4), sq_nonneg (D3 * r3 - D4 * r4)]

/-! ## 2. Rational Circle Parameterization & Spherical Cap Embeddings -/

def rcos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
/-- Rational parameterization of sine on the unit circle: $\mathrm{rsin}(t) = 2t/(1 + t^2)$. -/
def rsin (t : ℝ) : ℝ := (2 * t) / (1 + t ^ 2)

/-- Algebraic identity $\mathrm{rcos}(t)^2 + \mathrm{rsin}(t)^2 = 1$ for all $t \in \mathbb{R}$. -/
lemma rcos_sq_add_rsin_sq (t : ℝ) : (rcos t) ^ 2 + (rsin t) ^ 2 = 1 := by
  have h_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  dsimp [rcos, rsin]
  field_simp
  ring

/-- Bounds $-1 \le \mathrm{rcos}(t) \le 1$ for all $t \in \mathbb{R}$. -/
lemma rcos_bounds (t : ℝ) : -1 ≤ rcos t ∧ rcos t ≤ 1 := by
  have h_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  dsimp [rcos]
  constructor
  · rw [le_div_iff₀ h_pos]; nlinarith [sq_nonneg t]
  · rw [div_le_iff₀ h_pos]; nlinarith [sq_nonneg t]

/-- Bounds $-1 \le \mathrm{rsin}(t) \le 1$ for all $t \in \mathbb{R}$. -/
lemma rsin_bounds (t : ℝ) : -1 ≤ rsin t ∧ rsin t ≤ 1 := by
  have h_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  dsimp [rsin]
  constructor
  · rw [le_div_iff₀ h_pos]; nlinarith [sq_nonneg (t + 1)]
  · rw [div_le_iff₀ h_pos]; nlinarith [sq_nonneg (t - 1)]

/-- Major-axis coordinate $(2499000 / 2501) \Lambda$ of the rational spherical cap on $S^2(\alpha \Lambda)$. -/
def capMajor : ℝ := (2499000 / 2501 : ℝ) * (bdlLambda : ℝ)
/-- Minor-axis radius $(100000 / 2501) \Lambda$ of the rational spherical cap on $S^2(\alpha \Lambda)$. -/
def capMinor : ℝ := (100000 / 2501 : ℝ) * (bdlLambda : ℝ)

/-- Rational circle parameterization on the $S^2(\alpha \Lambda)$ spherical cap centered along axis $0$ (for qubits). -/
def rationalCap0 (t : ℝ) : Point3D :=
  fun a => if a = 0 then capMajor else if a = 1 then capMinor * rcos t else capMinor * rsin t

/-- Rational circle parameterization on the $S^2(\alpha \Lambda)$ spherical cap centered along axis $1$ (for $Z$-checks). -/
def rationalCap1 (t : ℝ) : Point3D :=
  fun a => if a = 0 then capMinor * rsin t else if a = 1 then capMajor else capMinor * rcos t

/-- Rational circle parameterization on the $S^2(\alpha \Lambda)$ spherical cap centered along axis $2$ (for $X$-checks). -/
def rationalCap2 (t : ℝ) : Point3D :=
  fun a => if a = 0 then capMinor * rcos t else if a = 1 then capMinor * rsin t else capMajor

/-- Verifies that `rationalCap0 t` lies exactly on the sphere of radius $\alpha \Lambda$ centered at the origin. -/
lemma rationalCap0_distSq3D_origin (t : ℝ) :
    distSq3D (rationalCap0 t) (fun _ => 0) = (bdlAlpha * (bdlLambda : ℝ)) ^ 2 := by
  have h_cs := rcos_sq_add_rsin_sq t
  dsimp [distSq3D, rationalCap0, capMajor, capMinor, bdlAlpha, bdlAlphaNat]
  linear_combination ((100000 / 2501 : ℝ) * (bdlLambda : ℝ)) ^ 2 * h_cs

/-- Verifies that `rationalCap1 t` lies exactly on the sphere of radius $\alpha \Lambda$ centered at the origin. -/
lemma rationalCap1_distSq3D_origin (t : ℝ) :
    distSq3D (rationalCap1 t) (fun _ => 0) = (bdlAlpha * (bdlLambda : ℝ)) ^ 2 := by
  have h_cs := rcos_sq_add_rsin_sq t
  dsimp [distSq3D, rationalCap1, capMajor, capMinor, bdlAlpha, bdlAlphaNat]
  linear_combination ((100000 / 2501 : ℝ) * (bdlLambda : ℝ)) ^ 2 * h_cs

/-- Verifies that `rationalCap2 t` lies exactly on the sphere of radius $\alpha \Lambda$ centered at the origin. -/
lemma rationalCap2_distSq3D_origin (t : ℝ) :
    distSq3D (rationalCap2 t) (fun _ => 0) = (bdlAlpha * (bdlLambda : ℝ)) ^ 2 := by
  have h_cs := rcos_sq_add_rsin_sq t
  dsimp [distSq3D, rationalCap2, capMajor, capMinor, bdlAlpha, bdlAlphaNat]
  linear_combination ((100000 / 2501 : ℝ) * (bdlLambda : ℝ)) ^ 2 * h_cs

/-- Numerical norm bounds $(137/2)^2 \le u_0^2 + u_1^2 + u_2^2 \le 2001^2$ for difference vectors
    between distinct orthogonal spherical caps. -/
lemma u_box_distSq_bounds (u0 u1 u2 : ℝ)
    (hu0_lo : 951 ≤ u0) (hu0_hi : u0 ≤ 1048)
    (hu1_lo : -1048 ≤ u1) (hu1_hi : u1 ≤ -951)
    (hu2_lo : -88 ≤ u2) (hu2_hi : u2 ≤ 88) :
    (137 / 2 : ℝ) ^ 2 ≤ u0 ^ 2 + u1 ^ 2 + u2 ^ 2 ∧
    u0 ^ 2 + u1 ^ 2 + u2 ^ 2 ≤ (2001 : ℝ) ^ 2 := by
  refine ⟨by nlinarith [sq_nonneg u1, sq_nonneg u2], ?_⟩
  have h0 : u0 ^ 2 ≤ 1048 ^ 2 := by nlinarith
  have h1 : u1 ^ 2 ≤ 1048 ^ 2 := by nlinarith
  have h2 : u2 ^ 2 ≤ 88 ^ 2 := by nlinarith
  linarith

/-! ## 3. Perturbed Edge-Length & Simplex Altitude Bounds -/

set_option maxHeartbeats 400000 in
lemma rationalCap_edgeZ_bounds (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (mZ : B.M_Z) (q : B.Q) (hz : B.code.checkZ mZ q ≠ 0) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    ((bdlAlpha2 - 1) * (bdlLambda : ℝ)) ^ 2 ≤ distSq3D (pcode.posQ q) (pcode.posZ mZ) ∧
    distSq3D (pcode.posQ q) (pcode.posZ mZ) ≤ ((2 * bdlAlpha + 1) * (bdlLambda : ℝ)) ^ 2 := by
  intro pcode
  -- Step 1: Extract coarse coordinate differences and rational trigonometric bounds.
  have h_dist := h8.1 mZ q hz
  have h0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_dist 0)
  have h1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_dist 1)
  have h2 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_dist 2)
  have h_cQ := rcos_bounds (tQ q)
  have h_sQ := rsin_bounds (tQ q)
  have h_cZ := rcos_bounds (tZ mZ)
  have h_sZ := rsin_bounds (tZ mZ)
  let dx := B.code.posQ q 0 - B.code.posZ mZ 0
  let dy := B.code.posQ q 1 - B.code.posZ mZ 1
  let dz := B.code.posQ q 2 - B.code.posZ mZ 2
  let u0 := dx + 2499000 / 2501 - (100000 / 2501) * rsin (tZ mZ)
  let u1 := dy + (100000 / 2501) * rcos (tQ q) - 2499000 / 2501
  let u2 := dz + (100000 / 2501) * rsin (tQ q) - (100000 / 2501) * rcos (tZ mZ)
  -- Step 2: Rescale by bdlLambda and apply u_box_distSq_bounds.
  have h_eq : distSq3D (pcode.posQ q) (pcode.posZ mZ) =
      ((bdlLambda : ℝ) ^ 2) * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) := by
    dsimp [pcode, bdlPerturbStep, distSq3D, rationalCap0, rationalCap1, capMajor, capMinor, u0, u1, u2, dx, dy, dz]
    ring
  rw [h_eq]
  dsimp [bdlAlpha2, bdlAlpha1, bdlAlpha, bdlAlphaNat]
  have hu0_lo : (951 : ℝ) ≤ u0 := by dsimp [u0, dx]; linarith
  have hu0_hi : u0 ≤ 1048 := by dsimp [u0, dx]; linarith
  have hu1_lo : (-1048 : ℝ) ≤ u1 := by dsimp [u1, dy]; linarith
  have hu1_hi : u1 ≤ -951 := by dsimp [u1, dy]; linarith
  have hu2_lo : (-88 : ℝ) ≤ u2 := by dsimp [u2, dz]; linarith
  have hu2_hi : u2 ≤ 88 := by dsimp [u2, dz]; linarith
  obtain ⟨h_low, h_high⟩ := u_box_distSq_bounds u0 u1 u2 hu0_lo hu0_hi hu1_lo hu1_hi hu2_lo hu2_hi
  have h_eq1 : ((139 / 2 - 1 : ℝ) * (bdlLambda : ℝ)) ^ 2 = ((bdlLambda : ℝ) ^ 2) * ((137 / 2 : ℝ) ^ 2) := by ring
  have h_eq2 : ((2 * 1000 + 1 : ℝ) * (bdlLambda : ℝ)) ^ 2 = ((bdlLambda : ℝ) ^ 2) * ((2001 : ℝ) ^ 2) := by ring
  rw [h_eq1, h_eq2]
  exact ⟨mul_le_mul_of_nonneg_left h_low (sq_nonneg _), mul_le_mul_of_nonneg_left h_high (sq_nonneg _)⟩

set_option maxHeartbeats 400000 in
/-- Proves that under any spherical-cap perturbation `(rationalCap0, rationalCap1, rationalCap2)`,
    every active $(q, m_X)$ edge has length in $[(\alpha_2 - 1)\Lambda, (2\alpha + 1)\Lambda]$. -/
lemma rationalCap_edgeX_bounds (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (mX : B.M_X) (q : B.Q) (hx : B.code.checkX mX q ≠ 0) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    ((bdlAlpha2 - 1) * (bdlLambda : ℝ)) ^ 2 ≤ distSq3D (pcode.posQ q) (pcode.posX mX) ∧
    distSq3D (pcode.posQ q) (pcode.posX mX) ≤ ((2 * bdlAlpha + 1) * (bdlLambda : ℝ)) ^ 2 := by
  intro pcode
  -- Step 1: Extract coarse coordinate differences and rational trigonometric bounds.
  have h_dist := h8.2 mX q hx
  have h0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_dist 0)
  have h1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_dist 1)
  have h2 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_dist 2)
  have h_cQ := rcos_bounds (tQ q)
  have h_sQ := rsin_bounds (tQ q)
  have h_cX := rcos_bounds (tX mX)
  have h_sX := rsin_bounds (tX mX)
  let dx := B.code.posQ q 0 - B.code.posX mX 0
  let dy := B.code.posQ q 1 - B.code.posX mX 1
  let dz := B.code.posQ q 2 - B.code.posX mX 2
  let u0 := dx + 2499000 / 2501 - (100000 / 2501) * rcos (tX mX)
  let u1 := dy + (100000 / 2501) * rcos (tQ q) - (100000 / 2501) * rsin (tX mX)
  let u2 := dz + (100000 / 2501) * rsin (tQ q) - 2499000 / 2501
  -- Step 2: Rescale by bdlLambda and apply u_box_distSq_bounds.
  have h_eq : distSq3D (pcode.posQ q) (pcode.posX mX) =
      ((bdlLambda : ℝ) ^ 2) * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) := by
    dsimp [pcode, bdlPerturbStep, distSq3D, rationalCap0, rationalCap2, capMajor, capMinor, u0, u1, u2, dx, dy, dz]
    ring
  rw [h_eq]
  dsimp [bdlAlpha2, bdlAlpha1, bdlAlpha, bdlAlphaNat]
  have hu0_lo : (951 : ℝ) ≤ u0 := by dsimp [u0, dx]; linarith
  have hu0_hi : u0 ≤ 1048 := by dsimp [u0, dx]; linarith
  have hu1_lo : (-88 : ℝ) ≤ u1 := by dsimp [u1, dy]; linarith
  have hu1_hi : u1 ≤ 88 := by dsimp [u1, dy]; linarith
  have hu2_lo : (-1048 : ℝ) ≤ u2 := by dsimp [u2, dz]; linarith
  have hu2_hi : u2 ≤ -951 := by dsimp [u2, dz]; linarith
  obtain ⟨h_low, h_high⟩ := u_box_distSq_bounds u0 u2 u1 hu0_lo hu0_hi hu2_lo hu2_hi hu1_lo hu1_hi
  have h_low' : (137 / 2 : ℝ) ^ 2 ≤ u0 ^ 2 + u1 ^ 2 + u2 ^ 2 := by linarith
  have h_high' : u0 ^ 2 + u1 ^ 2 + u2 ^ 2 ≤ (2001 : ℝ) ^ 2 := by linarith
  have h_eq1 : ((139 / 2 - 1 : ℝ) * (bdlLambda : ℝ)) ^ 2 = ((bdlLambda : ℝ) ^ 2) * ((137 / 2 : ℝ) ^ 2) := by ring
  have h_eq2 : ((2 * 1000 + 1 : ℝ) * (bdlLambda : ℝ)) ^ 2 = ((bdlLambda : ℝ) ^ 2) * ((2001 : ℝ) ^ 2) := by ring
  rw [h_eq1, h_eq2]
  exact ⟨mul_le_mul_of_nonneg_left h_low' (sq_nonneg _), mul_le_mul_of_nonneg_left h_high' (sq_nonneg _)⟩

/-- Shows that if two 3D points differ by at least $900 \Lambda$ along any coordinate axis,
    their squared Euclidean distance is at least $(\gamma \Lambda)^2$. -/
lemma altitude_distSq3D_ge_of_coord_diff_ge (p1 p2 : Point3D) (axis : Fin 3) (u : ℝ)
    (hu : 900 ≤ u) (h_coord : p1 axis - p2 axis = (bdlLambda : ℝ) * u) :
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤ distSq3D p1 p2 := by
  have h_gamma_nonneg : 0 ≤ bdlGamma := le_trans (by norm_num) bdlGamma_ge_seven_fifths
  have h_gamma_le : bdlGamma ≤ 5 / 2 := bdlGamma_le_five_halves
  have h_sq : bdlGamma ^ 2 ≤ u ^ 2 := by nlinarith
  have h_mul := mul_le_mul_of_nonneg_right h_sq (sq_nonneg (bdlLambda : ℝ))
  have h_axis_sq : (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤ (p1 axis - p2 axis) ^ 2 := by
    rw [h_coord]
    linarith [show (bdlGamma * (bdlLambda : ℝ)) ^ 2 = bdlGamma ^ 2 * (bdlLambda : ℝ) ^ 2 by ring,
              show ((bdlLambda : ℝ) * u) ^ 2 = u ^ 2 * (bdlLambda : ℝ) ^ 2 by ring]
  dsimp [distSq3D]
  have hp0 : 0 ≤ (p1 0 - p2 0) ^ 2 := sq_nonneg _
  have hp1 : 0 ≤ (p1 1 - p2 1) ^ 2 := sq_nonneg _
  have hp2 : 0 ≤ (p1 2 - p2 2) ^ 2 := sq_nonneg _
  fin_cases axis <;> { (try dsimp at h_axis_sq); linarith }

/-- Proves that under any spherical-cap perturbation `(rationalCap0, rationalCap1, rationalCap2)`,
    all three altitudes of every active 2-simplex have length at least $\gamma \Lambda$. -/
lemma rationalCap_simplex_width_bounds (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (s : ActiveSimplex2 B.code) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤
      distSq3D (pcode.posX s.val.1) (lerpPoint3D (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) ε) ∧
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤
      distSq3D (pcode.posQ s.val.2.1) (lerpPoint3D (pcode.posX s.val.1) (pcode.posZ s.val.2.2) ε) ∧
    (bdlGamma * (bdlLambda : ℝ)) ^ 2 ≤
      distSq3D (pcode.posZ s.val.2.2) (lerpPoint3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) ε) := by
  intro pcode
  -- Step 1: Bound coarse coordinate differences along active X- and Z-edges of the 2-simplex.
  have h_distX := h8.2 s.val.1 s.val.2.1 s.property.1
  have h_distZ := h8.1 s.val.2.2 s.val.2.1 s.property.2
  have hX0 := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distX 0)).1
  have hX0_hi := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distX 0)).2
  have hX1 := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distX 1)).1
  have hX1_hi := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distX 1)).2
  have hX2 := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distX 2)).1
  have hX2_hi := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distX 2)).2
  have hZ0 := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distZ 0)).1
  have hZ0_hi := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distZ 0)).2
  have hZ1 := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distZ 1)).1
  have hZ1_hi := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distZ 1)).2
  have hZ2 := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distZ 2)).1
  have hZ2_hi := (abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ h_distZ 2)).2
  have h_cQ := rcos_bounds (tQ s.val.2.1)
  have h_sQ := rsin_bounds (tQ s.val.2.1)
  have h_cZ := rcos_bounds (tZ s.val.2.2)
  have h_sZ := rsin_bounds (tZ s.val.2.2)
  have h_cX := rcos_bounds (tX s.val.1)
  have h_sX := rsin_bounds (tX s.val.1)
  refine ⟨?_, ?_, ?_⟩
  -- Step 2: Apply altitude_distSq3D_ge_of_coord_diff_ge along axes 2, 0, and 1.
  · apply altitude_distSq3D_ge_of_coord_diff_ge _ _ 2
      (2499000 / 2501 + (1 - ε) * (B.code.posX s.val.1 2 - B.code.posQ s.val.2.1 2 - (100000 / 2501) * rsin (tQ s.val.2.1)) +
        ε * (B.code.posX s.val.1 2 - B.code.posZ s.val.2.2 2 - (100000 / 2501) * rcos (tZ s.val.2.2)))
      (by nlinarith)
    dsimp [pcode, bdlPerturbStep, lerpPoint3D, rationalCap0, rationalCap1, rationalCap2, capMajor, capMinor]
    ring
  · apply altitude_distSq3D_ge_of_coord_diff_ge _ _ 0
      (2499000 / 2501 + (1 - ε) * (B.code.posQ s.val.2.1 0 - B.code.posX s.val.1 0 - (100000 / 2501) * rcos (tX s.val.1)) +
        ε * (B.code.posQ s.val.2.1 0 - B.code.posZ s.val.2.2 0 - (100000 / 2501) * rsin (tZ s.val.2.2)))
      (by nlinarith)
    dsimp [pcode, bdlPerturbStep, lerpPoint3D, rationalCap0, rationalCap1, rationalCap2, capMajor, capMinor]
    ring
  · apply altitude_distSq3D_ge_of_coord_diff_ge _ _ 1
      (2499000 / 2501 + (1 - ε) * (B.code.posZ s.val.2.2 1 - B.code.posX s.val.1 1 - (100000 / 2501) * rsin (tX s.val.1)) +
        ε * (B.code.posZ s.val.2.2 1 - B.code.posQ s.val.2.1 1 - (100000 / 2501) * rcos (tQ s.val.2.1)))
      (by nlinarith)
    dsimp [pcode, bdlPerturbStep, lerpPoint3D, rationalCap0, rationalCap1, rationalCap2, capMajor, capMinor]
    ring

end WeldedHierarchy
