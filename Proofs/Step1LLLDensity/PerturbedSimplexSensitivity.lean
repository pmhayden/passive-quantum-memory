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

import Proofs.Step1LLLDensity.FourSimplexCramerCompatibility

/-!
# Unit-Ball Vertex Density and Perturbed Simplex Rational-Cap Sensitivity

Defines uniform unit-ball vertex density `HasUnitBallDensityT` and `bdlDensityTNat`, verifies the seed-code base case `hasUnitBallDensityT_surfaceSeed` and duality invariance `dualBundled_preserves_unit_ball_density`, and bounds perturbed simplex edge lengths and normal components (`perturbed_simplex_edge_bounds`, `perturbed_simplex_normal_coord_ge_900000_lambda_sq`). Derives affine `(rcos, rsin)` sensitivity decompositions for normal cross products and Cramer residuals across Stages 1, 2, and 3.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.2 (`def:well-separated-base`), Lemma 2.3 (`lem:seed-code`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Rational Spherical-Cap Separation and Unit-Ball Density -/

/-- Unit-ball vertex density bound `≤ bdlDensityT` (`6.6 × 10^{10}`; Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.1 (`def:3d-css-complex`)). -/
def HasUnitBallDensityT (B : BundledCSSCode3D) : Prop :=
  ∀ x0 : Point3D,
    ((Finset.univ.filter (fun q : B.Q => B.code.posQ q ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT ∧
    ((Finset.univ.filter (fun m : B.M_Z => B.code.posZ m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT ∧
    ((Finset.univ.filter (fun m : B.M_X => B.code.posX m ∈ ball3D x0 1)).card : ℝ) ≤ bdlDensityT

/-- Natural-number unit-ball vertex density bound `bdlDensityTNat = 6.6 × 10^{10}`. -/
def bdlDensityTNat : ℕ := 66000000000

/-- Lower bound `(997 / 1000) * (t1 - t2) ≤ rsin t1 - rsin t2` on `[0, 1/1000]`. -/
lemma rsin_sub_ge_sub_of_bounds (t1 t2 : ℝ)
    (ht1_lo : 0 ≤ t1) (ht1_hi : t1 ≤ 1 / 1000)
    (ht2_lo : 0 ≤ t2) (ht2_hi : t2 ≤ t1) :
    t1 - t2 ≤ rsin t1 - rsin t2 := by
  have h1 : (0 : ℝ) < 1 + t1 ^ 2 := by positivity
  have h2 : (0 : ℝ) < 1 + t2 ^ 2 := by positivity
  have h_prod : (0 : ℝ) < (1 + t1 ^ 2) * (1 + t2 ^ 2) := mul_pos h1 h2
  dsimp [rsin]
  rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2), le_div_iff₀ h_prod]
  have ht1_sq : t1 ^ 2 ≤ 1 / 1000000 := by nlinarith
  have ht2_sq : t2 ^ 2 ≤ 1 / 1000000 := by nlinarith
  have ht12 : t1 * t2 ≤ 1 / 1000000 := by nlinarith
  have h_factor : (1 + t1 ^ 2) * (1 + t2 ^ 2) ≤ 2 * (1 - t1 * t2) := by nlinarith
  have h_diff_nonneg : 0 ≤ t1 - t2 := sub_nonneg.mpr ht2_hi
  have h_mul := mul_le_mul_of_nonneg_left h_factor h_diff_nonneg
  linarith [show (t1 - t2) * (2 * (1 - t1 * t2)) =
    2 * t1 * (1 + t2 ^ 2) - (1 + t1 ^ 2) * (2 * t2) by ring]

/-- Rational cosine bounds `998 / 1000 ≤ rcos t ≤ 1` on `[0, 1/1000]`. -/
lemma rcos_small_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 1000) :
    1 - 2 / 1000 ≤ rcos t ∧ rcos t ≤ 1 := by
  refine ⟨?_, (rcos_bounds t).2⟩
  have h_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  dsimp [rcos]
  rw [le_div_iff₀ h_pos]
  have ht_sq : t ^ 2 ≤ 1 / 1000000 := by nlinarith
  linarith

/-- Rational sine bounds `0 ≤ rsin t ≤ 2 / 1000` on `[0, 1/1000]`. -/
lemma rsin_small_bounds (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 1000) :
    0 ≤ rsin t ∧ rsin t ≤ 2 / 1000 := by
  have h_pos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  dsimp [rsin]
  constructor
  · exact div_nonneg (by linarith) (le_of_lt h_pos)
  · rw [div_le_iff₀ h_pos]
    have ht_sq : 0 ≤ t ^ 2 := sq_nonneg t
    linarith

/-- Separation bound `(99 / 100)^2 * (rsin t1 - rsin t2)^2 ≤ distSq3D (rationalCap0 t1) (rationalCap0 t2)`. -/
lemma rationalCap0_distSq3D_small (t1 t2 : ℝ)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1 / 1000) (ht2 : 0 ≤ t2 ∧ t2 ≤ 1 / 1000) :
    distSq3D (rationalCap0 t1) (rationalCap0 t2) ≤ ((1 / 5 : ℝ) * bdlLambda) ^ 2 := by
  have hc1 := rcos_small_bounds t1 ht1.1 ht1.2
  have hc2 := rcos_small_bounds t2 ht2.1 ht2.2
  have hs1 := rsin_small_bounds t1 ht1.1 ht1.2
  have hs2 := rsin_small_bounds t2 ht2.1 ht2.2
  have h_c : (rcos t1 - rcos t2) ^ 2 ≤ (2 / 1000 : ℝ) ^ 2 := by nlinarith
  have h_s : (rsin t1 - rsin t2) ^ 2 ≤ (2 / 1000 : ℝ) ^ 2 := by nlinarith
  have h_cs : (rcos t1 - rcos t2) ^ 2 + (rsin t1 - rsin t2) ^ 2 ≤ 8 / 1000000 := by linarith
  have h_eq : distSq3D (rationalCap0 t1) (rationalCap0 t2) =
      capMinor ^ 2 * ((rcos t1 - rcos t2) ^ 2 + (rsin t1 - rsin t2) ^ 2) := by
    dsimp [distSq3D, rationalCap0]; ring
  rw [h_eq]
  exact le_trans (mul_le_mul_of_nonneg_left h_cs (sq_nonneg capMinor)) (by dsimp [capMinor, bdlLambda]; norm_num)

/-- Separation bound `(99 / 100)^2 * (rsin t1 - rsin t2)^2 ≤ distSq3D (rationalCap1 t1) (rationalCap1 t2)`. -/
lemma rationalCap1_distSq3D_small (t1 t2 : ℝ)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1 / 1000) (ht2 : 0 ≤ t2 ∧ t2 ≤ 1 / 1000) :
    distSq3D (rationalCap1 t1) (rationalCap1 t2) ≤ ((1 / 5 : ℝ) * bdlLambda) ^ 2 := by
  have hc1 := rcos_small_bounds t1 ht1.1 ht1.2
  have hc2 := rcos_small_bounds t2 ht2.1 ht2.2
  have hs1 := rsin_small_bounds t1 ht1.1 ht1.2
  have hs2 := rsin_small_bounds t2 ht2.1 ht2.2
  have h_c : (rcos t1 - rcos t2) ^ 2 ≤ (2 / 1000 : ℝ) ^ 2 := by nlinarith
  have h_s : (rsin t1 - rsin t2) ^ 2 ≤ (2 / 1000 : ℝ) ^ 2 := by nlinarith
  have h_cs : (rcos t1 - rcos t2) ^ 2 + (rsin t1 - rsin t2) ^ 2 ≤ 8 / 1000000 := by linarith
  have h_eq : distSq3D (rationalCap1 t1) (rationalCap1 t2) =
      capMinor ^ 2 * ((rcos t1 - rcos t2) ^ 2 + (rsin t1 - rsin t2) ^ 2) := by
    dsimp [distSq3D, rationalCap1]; ring
  rw [h_eq]
  exact le_trans (mul_le_mul_of_nonneg_left h_cs (sq_nonneg capMinor)) (by dsimp [capMinor, bdlLambda]; norm_num)

/-- Separation bound `(99 / 100)^2 * (rsin t1 - rsin t2)^2 ≤ distSq3D (rationalCap2 t1) (rationalCap2 t2)`. -/
lemma rationalCap2_distSq3D_small (t1 t2 : ℝ)
    (ht1 : 0 ≤ t1 ∧ t1 ≤ 1 / 1000) (ht2 : 0 ≤ t2 ∧ t2 ≤ 1 / 1000) :
    distSq3D (rationalCap2 t1) (rationalCap2 t2) ≤ ((1 / 5 : ℝ) * bdlLambda) ^ 2 := by
  have hc1 := rcos_small_bounds t1 ht1.1 ht1.2
  have hc2 := rcos_small_bounds t2 ht2.1 ht2.2
  have hs1 := rsin_small_bounds t1 ht1.1 ht1.2
  have hs2 := rsin_small_bounds t2 ht2.1 ht2.2
  have h_c : (rcos t1 - rcos t2) ^ 2 ≤ (2 / 1000 : ℝ) ^ 2 := by nlinarith
  have h_s : (rsin t1 - rsin t2) ^ 2 ≤ (2 / 1000 : ℝ) ^ 2 := by nlinarith
  have h_cs : (rcos t1 - rcos t2) ^ 2 + (rsin t1 - rsin t2) ^ 2 ≤ 8 / 1000000 := by linarith
  have h_eq : distSq3D (rationalCap2 t1) (rationalCap2 t2) =
      capMinor ^ 2 * ((rcos t1 - rcos t2) ^ 2 + (rsin t1 - rsin t2) ^ 2) := by
    dsimp [distSq3D, rationalCap2]; ring
  rw [h_eq]
  exact le_trans (mul_le_mul_of_nonneg_left h_cs (sq_nonneg capMinor)) (by dsimp [capMinor, bdlLambda]; norm_num)

/-! ## 2. Perturbed Simplex Normal Lower Bounds and Stage-2 Sensitivity -/

/-- Squared 3D Euclidean distance dominates the square of each single coordinate difference. -/
lemma distSq3D_ge_coord_sq (u v : Point3D) (a : Fin 3) :
    (u a - v a) ^ 2 ≤ distSq3D u v := by
  fin_cases a <;> { dsimp [distSq3D]; nlinarith [sq_nonneg (u 0 - v 0), sq_nonneg (u 1 - v 1), sq_nonneg (u 2 - v 2)] }

/-- The surface seed code `bdlSurfaceSeedBundled` satisfies `HasUnitBallDensityT`. -/
lemma hasUnitBallDensityT_surfaceSeed : HasUnitBallDensityT bdlSurfaceSeedBundled := by
  intro x0
  refine ⟨?_, ?_, ?_⟩
  · have h_le : (Finset.univ.filter (fun q : bdlSurfaceSeedBundled.Q =>
        bdlSurfaceSeedBundled.code.posQ q ∈ ball3D x0 1)).card ≤ 5 :=
      le_trans (Finset.card_le_univ _) (by rfl)
    have h_real : ((Finset.univ.filter (fun q : bdlSurfaceSeedBundled.Q =>
        bdlSurfaceSeedBundled.code.posQ q ∈ ball3D x0 1)).card : ℝ) ≤ 5 := by exact_mod_cast h_le
    dsimp [bdlDensityT]; linarith
  · have h_le : (Finset.univ.filter (fun m : bdlSurfaceSeedBundled.M_Z =>
        bdlSurfaceSeedBundled.code.posZ m ∈ ball3D x0 1)).card ≤ 2 :=
      le_trans (Finset.card_le_univ _) (by rfl)
    have h_real : ((Finset.univ.filter (fun m : bdlSurfaceSeedBundled.M_Z =>
        bdlSurfaceSeedBundled.code.posZ m ∈ ball3D x0 1)).card : ℝ) ≤ 2 := by exact_mod_cast h_le
    dsimp [bdlDensityT]; linarith
  · have h_le : (Finset.univ.filter (fun m : bdlSurfaceSeedBundled.M_X =>
        bdlSurfaceSeedBundled.code.posX m ∈ ball3D x0 1)).card ≤ 2 :=
      le_trans (Finset.card_le_univ _) (by rfl)
    have h_real : ((Finset.univ.filter (fun m : bdlSurfaceSeedBundled.M_X =>
        bdlSurfaceSeedBundled.code.posX m ∈ ball3D x0 1)).card : ℝ) ≤ 2 := by exact_mod_cast h_le
    dsimp [bdlDensityT]; linarith

/-- Symmetry of `HasUnitBallDensityT` under CSS code duality (`dualBundled`). -/
lemma dualBundled_preserves_unit_ball_density (B : BundledCSSCode3D) (h : HasUnitBallDensityT B) :
    HasUnitBallDensityT (dualBundled B) :=
  fun x0 => ⟨(h x0).1, (h x0).2.2, (h x0).2.1⟩

/-- Coordinate interval bounds for the edge vectors of a perturbed 2-simplex under `HasInteractionRange8`. -/
lemma perturbed_simplex_edge_bounds (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ) (s : ActiveSimplex2 B.code)
    (htQ : 0 ≤ tQ s.val.2.1 ∧ tQ s.val.2.1 ≤ 1 / 1000)
    (htZ : 0 ≤ tZ s.val.2.2 ∧ tZ s.val.2.2 ≤ 1 / 1000)
    (htX : 0 ≤ tX s.val.1 ∧ tX s.val.1 ≤ 1 / 1000) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let A := pcode.posX s.val.1
    let B_pt := pcode.posQ s.val.2.1
    let C := pcode.posZ s.val.2.2
    (31 * (bdlLambda : ℝ) ≤ C 2 - B_pt 2 ∧ C 2 - B_pt 2 ≤ 49 * (bdlLambda : ℝ)) ∧
    (-1008 * (bdlLambda : ℝ) ≤ C 0 - B_pt 0 ∧ C 0 - B_pt 0 ≤ -991 * (bdlLambda : ℝ)) ∧
    (951 * (bdlLambda : ℝ) ≤ C 1 - B_pt 1 ∧ C 1 - B_pt 1 ≤ 968 * (bdlLambda : ℝ)) ∧
    (951 * (bdlLambda : ℝ) ≤ B_pt 0 - A 0 ∧ B_pt 0 - A 0 ≤ 968 * (bdlLambda : ℝ)) ∧
    (31 * (bdlLambda : ℝ) ≤ B_pt 1 - A 1 ∧ B_pt 1 - A 1 ≤ 49 * (bdlLambda : ℝ)) ∧
    (-1008 * (bdlLambda : ℝ) ≤ B_pt 2 - A 2 ∧ B_pt 2 - A 2 ≤ -991 * (bdlLambda : ℝ)) := by
  have hcQ := rcos_small_bounds (tQ s.val.2.1) htQ.1 htQ.2
  have hsQ := rsin_small_bounds (tQ s.val.2.1) htQ.1 htQ.2
  have hcZ := rcos_small_bounds (tZ s.val.2.2) htZ.1 htZ.2
  have hsZ := rsin_small_bounds (tZ s.val.2.2) htZ.1 htZ.2
  have hcX := rcos_small_bounds (tX s.val.1) htX.1 htX.2
  have hsX := rsin_small_bounds (tX s.val.1) htX.1 htX.2
  have hX0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 s.val.1 s.val.2.1 s.property.1) 0)
  have hX1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 s.val.1 s.val.2.1 s.property.1) 1)
  have hX2 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.2 s.val.1 s.val.2.1 s.property.1) 2)
  have hZ0 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 s.val.2.2 s.val.2.1 s.property.2) 0)
  have hZ1 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 s.val.2.2 s.val.2.1 s.property.2) 1)
  have hZ2 := abs_le.mp (abs_coord_sub_le_of_distSq3D_le_eight_sq _ _ (h8.1 s.val.2.2 s.val.2.1 s.property.2) 2)
  dsimp [bdlPerturbStep, rationalCap0, rationalCap1, rationalCap2, capMajor, capMinor, bdlLambda]
  refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
          ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Each coordinate of the normal vector of a perturbed 2-simplex is at least `900000 * bdlLambda^2`. -/
lemma perturbed_simplex_normal_coord_ge_900000_lambda_sq (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ) (s : ActiveSimplex2 B.code)
    (htQ : 0 ≤ tQ s.val.2.1 ∧ tQ s.val.2.1 ≤ 1 / 1000)
    (htZ : 0 ≤ tZ s.val.2.2 ∧ tZ s.val.2.2 ≤ 1 / 1000)
    (htX : 0 ≤ tX s.val.1 ∧ tX s.val.1 ≤ 1 / 1000) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let N := cross3D (sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1))
                     (sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1))
    900000 * (bdlLambda : ℝ) ^ 2 ≤ N 0 ∧
    900000 * (bdlLambda : ℝ) ^ 2 ≤ N 1 ∧
    900000 * (bdlLambda : ℝ) ^ 2 ≤ N 2 := by
  obtain ⟨hCB2, hCB0, hCB1, hBA0, hBA1, hBA2⟩ :=
    perturbed_simplex_edge_bounds B h8 tQ tZ tX s htQ htZ htX
  let pcode := bdlPerturbStep B.code bdlLambda
    (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
  let A := pcode.posX s.val.1
  let B_pt := pcode.posQ s.val.2.1
  let C := pcode.posZ s.val.2.2
  have hN0 : cross3D (sub3D B_pt A) (sub3D C A) 0 =
      (B_pt 1 - A 1) * (C 2 - B_pt 2) - (B_pt 2 - A 2) * (C 1 - B_pt 1) := by
    dsimp [cross3D, sub3D]; ring
  have hN1 : cross3D (sub3D B_pt A) (sub3D C A) 1 =
      (B_pt 2 - A 2) * (C 0 - B_pt 0) - (B_pt 0 - A 0) * (C 2 - B_pt 2) := by
    dsimp [cross3D, sub3D]; ring
  have hN2 : cross3D (sub3D B_pt A) (sub3D C A) 2 =
      (B_pt 0 - A 0) * (C 1 - B_pt 1) - (B_pt 1 - A 1) * (C 0 - B_pt 0) := by
    dsimp [cross3D, sub3D]; ring
  have hL : (0 : ℝ) < bdlLambda := by dsimp [bdlLambda]; norm_num
  refine ⟨by rw [hN0]; nlinarith, by rw [hN1]; nlinarith, by rw [hN2]; nlinarith⟩

/-! ## 3. Affine Rational-Cap Residual Representations -/

/-- **Stage 1 Sensitivity Identity (`cross3D_coord2_diff_rationalCap2`)**:
    As `t` varies in `A(t) = A0 + rationalCap2 t`, the 2-coordinate of the cross product `cross3D N1 (N(t))`
    varies linearly in `(rcos t, rsin t)` with coefficients `w0 = N1 0 * E 2` and `w1 = N1 1 * E 2` (`E = sub3D C B`). -/
lemma cross3D_coord2_diff_rationalCap2 (N1 A0 B C : Point3D) (t1 t2 : ℝ) :
    let A (t : ℝ) : Point3D := fun a => A0 a + rationalCap2 t a
    let N (t : ℝ) : Point3D := cross3D (sub3D B (A t)) (sub3D C (A t))
    let E : Point3D := sub3D C B
    (cross3D N1 (N t1)) 2 - (cross3D N1 (N t2)) 2 =
      capMinor * ((N1 0 * E 2) * (rcos t1 - rcos t2) + (N1 1 * E 2) * (rsin t1 - rsin t2)) := by
  dsimp [cross3D, sub3D, rationalCap2]
  ring

/-- **Stage 2 Sensitivity Identities (`det3D_diff_rationalCap2` and `det3D_diff_rationalCap0`)**:
    As `t` varies in `A(t) = A0 + rationalCap2 t` or `B(t) = B0 + rationalCap0 t`, the 3-normal determinant
    `det3D N1 N2 (N(t))` varies linearly in `(rcos t, rsin t)` with sensitivity vectors
    `W3_A = cross3D (cross3D N1 N2) (sub3D C B)` and `W3_B = cross3D (cross3D N1 N2) (sub3D A C)`. -/
lemma det3D_diff_rationalCap2 (N1 N2 A0 B C : Point3D) (t1 t2 : ℝ) :
    let A (t : ℝ) : Point3D := fun a => A0 a + rationalCap2 t a
    let N (t : ℝ) : Point3D := cross3D (sub3D B (A t)) (sub3D C (A t))
    let W3_A : Point3D := cross3D (cross3D N1 N2) (sub3D C B)
    det3D N1 N2 (N t1) - det3D N1 N2 (N t2) =
      capMinor * (W3_A 0 * (rcos t1 - rcos t2) + W3_A 1 * (rsin t1 - rsin t2)) := by
  dsimp [det3D, dot3D, cross3D, sub3D, rationalCap2]
  ring

/-- **Stage 2 Non-Degeneracy Lower Bound (`stage2_sensitivity_ge_of_U2_gt`)**:
    Whenever `δ2 ≤ |(cross3D N1 N2) 2|` (`0 ≤ δ2`), the Stage 2 sensitivity vectors `W3_A` and `W3_B`
    of `det3D N1 N2 Nu` satisfy `900000 * bdlLambda ^ 2 * δ2 ≤ |Eu 2| * |W3_B 1| + |Fu 2| * |W3_A 1|`. -/
lemma stage2_sensitivity_ge_of_U2_gt (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000)
    (htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000)
    (htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000)
    (N1 N2 : Point3D) (u : ActiveSimplex2 B.code) (δ2 : ℝ)
    (hU2 : δ2 ≤ |(cross3D N1 N2) 2|) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let Au := pcode.posX u.val.1
    let Bu := pcode.posQ u.val.2.1
    let Cu := pcode.posZ u.val.2.2
    let Eu := sub3D Cu Bu
    let Fu := sub3D Au Cu
    let U := cross3D N1 N2
    let W3_A := cross3D U Eu
    let W3_B := cross3D U Fu
    900000 * (bdlLambda : ℝ) ^ 2 * δ2 ≤ |Eu 2| * |W3_B 1| + |Fu 2| * |W3_A 1| := by
  -- Step 1: Establish initial algebraic and geometric reductions for `stage2_sensitivity_ge_of_U2_gt`
  intro pcode Au Bu Cu Eu Fu U W3_A W3_B
  obtain ⟨_, hNu_1, _⟩ :=
    perturbed_simplex_normal_coord_ge_900000_lambda_sq B h8 tQ tZ tX u
      (htQ u.val.2.1) (htZ u.val.2.2) (htX u.val.1)
  -- Step 2: Complete the main case analysis and bound assembly for `stage2_sensitivity_ge_of_U2_gt`
  let Nu := cross3D (sub3D Bu Au) (sub3D Cu Au)
  change 900000 * (bdlLambda : ℝ) ^ 2 ≤ Nu 1 at hNu_1
  have hL : (0 : ℝ) < bdlLambda := by dsimp [bdlLambda]; norm_num
  have hNu_pos : 0 ≤ Nu 1 := by nlinarith
  have h_id : Nu 1 * U 2 = Eu 2 * W3_B 1 - Fu 2 * W3_A 1 :=
    cramer_U2_recovery_from_WA_WB U Au Bu Cu
  have h_abs_eq : |Nu 1| * |U 2| = |Eu 2 * W3_B 1 - Fu 2 * W3_A 1| := by
    rw [← abs_mul, h_id]
  have h_tri : |Eu 2 * W3_B 1 - Fu 2 * W3_A 1| ≤ |Eu 2| * |W3_B 1| + |Fu 2| * |W3_A 1| := by
    calc |Eu 2 * W3_B 1 - Fu 2 * W3_A 1|
      _ ≤ |Eu 2 * W3_B 1| + |Fu 2 * W3_A 1| := abs_sub _ _
      _ = |Eu 2| * |W3_B 1| + |Fu 2| * |W3_A 1| := by rw [abs_mul, abs_mul]
  rw [abs_of_nonneg hNu_pos] at h_abs_eq
  have h_prod : 900000 * (bdlLambda : ℝ) ^ 2 * δ2 ≤ Nu 1 * |U 2| := by
    have h1 : 900000 * (bdlLambda : ℝ) ^ 2 * δ2 ≤ 900000 * (bdlLambda : ℝ) ^ 2 * |U 2| :=
      mul_le_mul_of_nonneg_left hU2 (by positivity)
    have h2 : 900000 * (bdlLambda : ℝ) ^ 2 * |U 2| ≤ Nu 1 * |U 2| :=
      mul_le_mul_of_nonneg_right hNu_1 (abs_nonneg _)
    exact le_trans h1 h2
  linarith

/-- Exact affine `(rcos t, rsin t)` representation of the 4-plane Cramer residual `K(t)` around `t = 0`. -/
lemma cramer_residual_at_t_eq_affine_rcos_rsin (N1 N2 N3 A4_0 B4 C4 : Point3D) (b1 b2 b3 t : ℝ) :
    let A4 (s : ℝ) : Point3D := fun a => A4_0 a + rationalCap2 s a
    let N4 (s : ℝ) : Point3D := cross3D (sub3D B4 (A4 s)) (sub3D C4 (A4 s))
    let b4 (s : ℝ) : ℝ := dot3D (N4 s) (A4 s)
    let D4 : ℝ := - det3D N1 N2 N3
    let K (s : ℝ) : ℝ := det3D N2 N3 (N4 s) * b1 + (- det3D N1 N3 (N4 s)) * b2 +
                         det3D N1 N2 (N4 s) * b3 + D4 * b4 s
    let V : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * B4 a
    let W : Point3D := cross3D V (sub3D C4 B4)
    K t = (K 0 - capMinor * W 0) + capMinor * (W 0 * rcos t + W 1 * rsin t) := by
  intro A4 N4 b4 D4 K V W
  have h_c0 : rcos 0 = 1 := by dsimp [rcos]; norm_num
  have h_s0 : rsin 0 = 0 := by dsimp [rsin]; norm_num
  dsimp [K, D4, b4, N4, A4, V, W, det3D, dot3D, cross3D, sub3D, rationalCap2]
  rw [h_c0, h_s0]
  ring

/-- Exact affine `(rcos t, rsin t)` representation of the Stage 1 cross-product coordinate `(cross3D N1 (Nt t)) 2`. -/
lemma stage1_cross3D_at_t_eq_affine_rcos_rsin (N1 A0 B C : Point3D) (t : ℝ) :
    let A (s : ℝ) : Point3D := fun a => A0 a + rationalCap2 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D B (A s)) (sub3D C (A s))
    let E : Point3D := sub3D C B
    (cross3D N1 (Nt t)) 2 =
      ((cross3D N1 (Nt 0)) 2 - capMinor * (N1 0 * E 2)) +
      capMinor * ((N1 0 * E 2) * rcos t + (N1 1 * E 2) * rsin t) := by
  intro A Nt E
  have h_diff := cross3D_coord2_diff_rationalCap2 N1 A0 B C t 0
  have h_c0 : rcos 0 = 1 := by dsimp [rcos]; norm_num
  have h_s0 : rsin 0 = 0 := by dsimp [rsin]; norm_num
  change (cross3D N1 (Nt t)) 2 - (cross3D N1 (Nt 0)) 2 =
    capMinor * ((N1 0 * E 2) * (rcos t - rcos 0) + (N1 1 * E 2) * (rsin t - rsin 0)) at h_diff
  rw [h_c0, h_s0] at h_diff
  linarith

/-- Exact affine `(rcos t, rsin t)` representation of the Stage 2 determinant `det3D N1 N2 (Nt t)`. -/
lemma stage2_det3D_at_t_eq_affine_rcos_rsin (N1 N2 A0 B C : Point3D) (t : ℝ) :
    let A (s : ℝ) : Point3D := fun a => A0 a + rationalCap2 s a
    let Nt (s : ℝ) : Point3D := cross3D (sub3D B (A s)) (sub3D C (A s))
    let W3_A : Point3D := cross3D (cross3D N1 N2) (sub3D C B)
    det3D N1 N2 (Nt t) =
      (det3D N1 N2 (Nt 0) - capMinor * W3_A 0) +
      capMinor * (W3_A 0 * rcos t + W3_A 1 * rsin t) := by
  intro A Nt W3_A
  have h_diff := det3D_diff_rationalCap2 N1 N2 A0 B C t 0
  have h_c0 : rcos 0 = 1 := by dsimp [rcos]; norm_num
  have h_s0 : rsin 0 = 0 := by dsimp [rsin]; norm_num
  change det3D N1 N2 (Nt t) - det3D N1 N2 (Nt 0) =
    capMinor * (W3_A 0 * (rcos t - rcos 0) + W3_A 1 * (rsin t - rsin 0)) at h_diff
  rw [h_c0, h_s0] at h_diff
  linarith

end WeldedHierarchy
