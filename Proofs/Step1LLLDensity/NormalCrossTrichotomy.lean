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

import Proofs.Step1LLLDensity.ConditionalBadVertexLLL

/-!
# Stage-3 Normal Cross-Product Trichotomy and Tight Rational Slab Bound

Proves the tight rational trigonometric slab cardinality bound `card_filter_rcos_rsin_slab_le_one_of_linear_dom_tight`, the Stage-3 coordinate sensitivity lower bound `stage3_coord1_sensitivity_ge`, and the Cramer normal cross-product identity `cramer_normal_cross_WA_WB_WC`. Combines these estimates to establish `stage3_dominant_type_trichotomy`, classifying which vertex sector dominates the four-simplex Cramer determinant in Stage 3 of the Step-1 Lovasz Local Lemma argument.

## References

* Part I, Section 2.1 (`subsec:css-complexes`), Definition 2.2 (`def:well-separated-base`)
* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`), Equation (2) (`eq:archimedes-slab-bound`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Tightened First-Order Linear-Dominance 1-Point Slab Bound -/

/-- **Tightened First-Order Linear-Dominance 1-Point Slab Bound (`card_filter_rcos_rsin_slab_le_one_of_linear_dom_tight`)**:
    On `[0, 1/1000]`, `(1 + t1^2)(1 + t2^2) ≤ 1001/1000` and `|Q12| ≥ (989/1000) * |w1|` when `|w0| ≤ 5 * |w1|`,
    so `(51 / 100) * ε < Δ * |w1|` guarantees at most 1 grid index in the slab `≤ (capMinor * ε) / 2`. -/
lemma card_filter_rcos_rsin_slab_le_one_of_linear_dom_tight {N : ℕ} (gridParam : Fin (N + 1) → ℝ) (Δ : ℝ) (hΔ : 0 < Δ)
    (h_bounds : ∀ i : Fin (N + 1), 0 ≤ gridParam i ∧ gridParam i ≤ 1 / 1000)
    (h_sep : ∀ i j : Fin (N + 1), j.val < i.val → gridParam j + Δ ≤ gridParam i)
    (C0 w0 w1 ε : ℝ) (h_dom : |w0| ≤ 5 * |w1|) (hw : (51 / 100) * ε < Δ * |w1|) :
    (Finset.univ.filter (fun i : Fin (N + 1) =>
      |C0 + capMinor * (w0 * rcos (gridParam i) + w1 * rsin (gridParam i))| ≤ (capMinor * ε) / 2)).card ≤ 1 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `card_filter_rcos_rsin_slab_le_one_of_linear_dom_tight`
  rw [Finset.card_le_one]
  intro i hi j hj
  rw [Finset.mem_filter] at hi hj
  by_contra hne
  have h_prove_lt : ∀ i1 i2 : Fin (N + 1), i1.val < i2.val →
      |C0 + capMinor * (w0 * rcos (gridParam i1) + w1 * rsin (gridParam i1))| ≤ (capMinor * ε) / 2 →
      |C0 + capMinor * (w0 * rcos (gridParam i2) + w1 * rsin (gridParam i2))| ≤ (capMinor * ε) / 2 → False := by
    intro i1 i2 h12 h_in1 h_in2
    let t1 := gridParam i1
    let t2 := gridParam i2
    have ht1 := h_bounds i1
    have ht2 := h_bounds i2
    have h_step : t1 + Δ ≤ t2 := h_sep i2 i1 h12
    have h_cm : (0 : ℝ) < capMinor := by dsimp [capMinor, bdlLambda]; norm_num
    have h_diff : |(w0 * rcos t2 + w1 * rsin t2) - (w0 * rcos t1 + w1 * rsin t1)| ≤ ε := by
      have h_sub := abs_sub_le
        (C0 + capMinor * (w0 * rcos t2 + w1 * rsin t2)) 0
        (C0 + capMinor * (w0 * rcos t1 + w1 * rsin t1))
      rw [sub_zero, zero_sub, abs_neg] at h_sub
      have h_eq : (C0 + capMinor * (w0 * rcos t2 + w1 * rsin t2)) -
          (C0 + capMinor * (w0 * rcos t1 + w1 * rsin t1)) =
          capMinor * ((w0 * rcos t2 + w1 * rsin t2) - (w0 * rcos t1 + w1 * rsin t1)) := by ring
      rw [h_eq, abs_mul, abs_of_pos h_cm] at h_sub
      have h_mul_le : capMinor * |(w0 * rcos t2 + w1 * rsin t2) - (w0 * rcos t1 + w1 * rsin t1)| ≤ capMinor * ε := by
        linarith [h_in1, h_in2, h_sub]
      exact le_of_mul_le_mul_left h_mul_le h_cm
    have h_id := rcos_rsin_two_point_identity w0 w1 t1 t2
    have ht1_sq : t1 ^ 2 ≤ 1 / 1000000 := by nlinarith [ht1.1, ht1.2]
    have ht2_sq : t2 ^ 2 ≤ 1 / 1000000 := by nlinarith [ht2.1, ht2.2]
    have h_prod_le : (1 + t1 ^ 2) * (1 + t2 ^ 2) ≤ 1001 / 1000 := by nlinarith [ht1_sq, ht2_sq]
    have h_prod_pos : 0 ≤ (1 + t1 ^ 2) * (1 + t2 ^ 2) := by positivity
    let Q12 := w1 * (1 - t1 * t2) - w0 * (t1 + t2)
    have h_abs_Q : 2 * Δ * |Q12| ≤ (1001 / 1000) * ε := by
      have h_lhs : |2 * (t2 - t1) * Q12| ≤ (1001 / 1000) * ε := by
        -- Step 2: Complete the main case analysis and bound assembly for `card_filter_rcos_rsin_slab_le_one_of_linear_dom_tight`
        rw [← h_id, abs_mul, abs_of_nonneg h_prod_pos]
        calc ((1 + t1 ^ 2) * (1 + t2 ^ 2)) * |(w0 * rcos t2 + w1 * rsin t2) - (w0 * rcos t1 + w1 * rsin t1)|
          _ ≤ (1001 / 1000) * ε :=
            mul_le_mul h_prod_le h_diff (abs_nonneg _) (by positivity)
      rw [abs_mul, abs_of_pos (by linarith : 0 < 2 * (t2 - t1))] at h_lhs
      have h_mono : (2 * Δ) * |Q12| ≤ (2 * (t2 - t1)) * |Q12| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg Q12)
      linarith
    have h_1m : 999 / 1000 ≤ 1 - t1 * t2 := by nlinarith [ht1.1, ht1.2, ht2.1, ht2.2]
    have h_sum_le : t1 + t2 ≤ 2 / 1000 := by linarith [ht1.2, ht2.2]
    have h_sum_nonneg : 0 ≤ t1 + t2 := by linarith [ht1.1, ht2.1]
    have h_Q_lo : (989 / 1000) * |w1| ≤ |Q12| := by
      have h_tri : |w1 * (1 - t1 * t2)| - |w0 * (t1 + t2)| ≤ |Q12| := by
        dsimp [Q12]; linarith [abs_sub_abs_le_abs_sub (w1 * (1 - t1 * t2)) (w0 * (t1 + t2))]
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t1 * t2),
          abs_mul, abs_of_nonneg h_sum_nonneg] at h_tri
      have h1 : (999 / 1000) * |w1| ≤ |w1| * (1 - t1 * t2) := by
        calc (999 / 1000) * |w1| = |w1| * (999 / 1000) := by ring
          _ ≤ |w1| * (1 - t1 * t2) := mul_le_mul_of_nonneg_left h_1m (abs_nonneg w1)
      have h2 : |w0| * (t1 + t2) ≤ (10 / 1000) * |w1| := by
        calc |w0| * (t1 + t2) ≤ (5 * |w1|) * (2 / 1000) :=
              mul_le_mul h_dom h_sum_le h_sum_nonneg (by positivity)
          _ = (10 / 1000) * |w1| := by ring
      linarith
    have h_contra : (989 / 500) * (51 / 100 * ε) < (1001 / 1000) * ε := by
      calc (989 / 500) * (51 / 100 * ε)
        _ < (989 / 500) * (Δ * |w1|) := mul_lt_mul_of_pos_left hw (by norm_num)
        _ = (2 * Δ) * ((989 / 1000) * |w1|) := by ring
        _ ≤ (2 * Δ) * |Q12| := mul_le_mul_of_nonneg_left h_Q_lo (by positivity)
        _ ≤ (1001 / 1000) * ε := h_abs_Q
    have hε_nonneg : 0 ≤ ε := by
      have : 0 ≤ (2 * Δ) * |Q12| := mul_nonneg (by positivity) (abs_nonneg Q12)
      linarith [h_abs_Q]
    linarith
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · exact h_prove_lt i j hlt hi.2 hj.2
  · exact hne (Fin.ext heq)
  · exact h_prove_lt j i hgt hj.2 hi.2

/-- **Stage 3 Coordinate-1 Sensitivity Decomposition (`stage3_coord1_sensitivity_ge`)**:
    Because `WA 1 + WB 1 + WC 1 = D4 * N4 1` (`cramer_W_sum_eq_det_mul_normal ... 1`) and `900000 * bdlLambda^2 ≤ N4 1`,
    we have `900000 * bdlLambda^2 * |D4| ≤ |WA 1| + |WB 1| + |WC 1|` unconditionally. -/
lemma stage3_coord1_sensitivity_ge (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000)
    (htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000)
    (htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000)
    (N1 N2 N3 : Point3D) (b1 b2 b3 : ℝ) (u : ActiveSimplex2 B.code) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let A4 := pcode.posX u.val.1
    let B4 := pcode.posQ u.val.2.1
    let C4 := pcode.posZ u.val.2.2
    let D4 := - det3D N1 N2 N3
    let VA : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * B4 a
    let VB : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * C4 a
    let VC : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a + D4 * A4 a
    let WA := cross3D VA (sub3D C4 B4)
    let WB := cross3D VB (sub3D A4 C4)
    let WC := cross3D VC (sub3D B4 A4)
    900000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| + |WB 1| + |WC 1| := by
  -- Step 1: Establish initial algebraic and geometric reductions for `stage3_coord1_sensitivity_ge`
  intro pcode A4 B4 C4 D4 VA VB VC WA WB WC
  obtain ⟨_, hNu_1, _⟩ :=
    perturbed_simplex_normal_coord_ge_900000_lambda_sq B h8 tQ tZ tX u
      (htQ u.val.2.1) (htZ u.val.2.2) (htX u.val.1)
  -- Step 2: Complete the main case analysis and bound assembly for `stage3_coord1_sensitivity_ge`
  let N4 := cross3D (sub3D B4 A4) (sub3D C4 A4)
  change 900000 * (bdlLambda : ℝ) ^ 2 ≤ N4 1 at hNu_1
  have hL : (0 : ℝ) < bdlLambda := by dsimp [bdlLambda]; norm_num
  have hNu_pos : 0 ≤ N4 1 := by nlinarith
  have h_id : WA 1 + WB 1 + WC 1 = D4 * N4 1 :=
    cramer_W_sum_eq_det_mul_normal N1 N2 N3 A4 B4 C4 b1 b2 b3 1
  have h_abs_eq : |D4| * |N4 1| = |WA 1 + WB 1 + WC 1| := by
    rw [← abs_mul, ← h_id]
  have h_tri : |WA 1 + WB 1 + WC 1| ≤ |WA 1| + |WB 1| + |WC 1| := by
    linarith [abs_add_le (WA 1 + WB 1) (WC 1), abs_add_le (WA 1) (WB 1)]
  rw [abs_of_nonneg hNu_pos] at h_abs_eq
  have h_prod : 900000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ N4 1 * |D4| :=
    mul_le_mul_of_nonneg_right hNu_1 (abs_nonneg _)
  linarith

/-! ## 2. 3D Normal-Cross Algebraic Identity and Dominance Extraction -/

/-- **Cramer Sensitivity Normal Cross Identities (`cramer_normal_cross_WA_WB_WC`)**:
    Exact identities relating the `rcos` and `rsin` components of `WA`, `WB`, `WC` via `N4` and `K = dot3D VA N4`. -/
lemma cramer_normal_cross_WA_WB_WC (V0 A4 B4 C4 : Point3D) (D4 : ℝ) :
    let N4 := cross3D (sub3D B4 A4) (sub3D C4 A4)
    let VA : Point3D := fun a => V0 a + D4 * B4 a
    let VB : Point3D := fun a => V0 a + D4 * C4 a
    let VC : Point3D := fun a => V0 a + D4 * A4 a
    let WA := cross3D VA (sub3D C4 B4)
    let WB := cross3D VB (sub3D A4 C4)
    let WC := cross3D VC (sub3D B4 A4)
    let K := dot3D VA N4
    (N4 1 * WA 0 - N4 0 * WA 1 = (C4 2 - B4 2) * K) ∧
    (N4 1 * WB 2 - N4 2 * WB 1 = - (A4 0 - C4 0) * K) ∧
    (N4 1 * WC 0 - N4 0 * WC 1 = (B4 2 - A4 2) * K) ∧
    (N4 0 * WC 2 - N4 2 * WC 0 = (B4 1 - A4 1) * K) := by
  dsimp [cross3D, sub3D, dot3D]
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **Universal Normal-Cross Sensitivity Conversion (`abs_dom_and_lower_of_normal_cross_eq`)**:
    Given `N_a * W_b - N_b * W_a = E * K` with `N_a, N_b ∈ [900000 L^2, 987000 L^2]`, `|E| ≤ 1008 L`, and `|K| ≤ 7000000 L^2 |D4|`:
    1. If `300000 L^2 |D4| ≤ |W_a|`, then `273000 L^2 |D4| ≤ |W_b|` and `|W_a| ≤ 5 * |W_b|`.
    2. If `273000 L^2 |D4| ≤ |W_a|`, then `|W_b| ≤ 5 * |W_a|`. -/
lemma abs_dom_and_lower_of_normal_cross_eq {N_a N_b W_a W_b E K D4 : ℝ}
    (hNa : 900000 * (bdlLambda : ℝ) ^ 2 ≤ N_a ∧ N_a ≤ 987000 * (bdlLambda : ℝ) ^ 2)
    (hNb : 900000 * (bdlLambda : ℝ) ^ 2 ≤ N_b ∧ N_b ≤ 987000 * (bdlLambda : ℝ) ^ 2)
    (hE : |E| ≤ 1008 * (bdlLambda : ℝ))
    (hK : |K| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4|)
    (h_id : N_a * W_b - N_b * W_a = E * K) :
    (300000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |W_a| →
      273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |W_b| ∧ |W_a| ≤ 5 * |W_b|) ∧
    (273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |W_a| → |W_b| ≤ 5 * |W_a|) := by
  -- Step 1: Establish initial algebraic and geometric reductions for `abs_dom_and_lower_of_normal_cross_eq`
  let L := (bdlLambda : ℝ)
  have hNa_pos : 0 ≤ N_a := by dsimp [L, bdlLambda] at hNa; linarith [hNa.1]
  have hNb_pos : 0 ≤ N_b := by dsimp [L, bdlLambda] at hNb; linarith [hNb.1]
  have hEK : |E * K| ≤ 549000000 * L ^ 4 * |D4| := by
    rw [abs_mul]
    have h1 : |E| * |K| ≤ (1008 * L) * (7000000 * L ^ 2 * |D4|) :=
      mul_le_mul hE hK (abs_nonneg K) (by dsimp [L, bdlLambda]; norm_num)
    have h2 : (1008 * L) * (7000000 * L ^ 2 * |D4|) = 7056000000 * L ^ 3 * |D4| := by ring
    have h3 : 7056000000 * L ^ 3 * |D4| ≤ 549000000 * L ^ 4 * |D4| := by
      have h_l : 7056000000 * L ^ 3 ≤ 549000000 * L ^ 4 := by dsimp [L, bdlLambda]; norm_num
      exact mul_le_mul_of_nonneg_right h_l (abs_nonneg D4)
    linarith
  have h_prove_dom_a : 273000 * L ^ 2 * |D4| ≤ |W_b| → |W_a| ≤ 5 * |W_b| := by
    intro hWb
    have h_eq : N_b * W_a = N_a * W_b - E * K := by linarith [h_id]
    have h_tri : |N_b * W_a| ≤ |N_a * W_b| + |E * K| := by
      rw [h_eq]; exact abs_sub _ _
    rw [abs_mul N_b W_a, abs_of_nonneg hNb_pos, abs_mul N_a W_b, abs_of_nonneg hNa_pos] at h_tri
    have h_lhs : (900000 * L ^ 2) * |W_a| ≤ N_b * |W_a| :=
      mul_le_mul_of_nonneg_right hNb.1 (abs_nonneg W_a)
    have h_rhs1 : N_a * |W_b| ≤ (987000 * L ^ 2) * |W_b| :=
      mul_le_mul_of_nonneg_right hNa.2 (abs_nonneg W_b)
    have h_rhs2 : 549000000 * L ^ 4 * |D4| ≤ (2013 * L ^ 2) * |W_b| := by
      have h_c : 549000000 * L ^ 4 ≤ 549549000 * L ^ 4 := by dsimp [L, bdlLambda]; norm_num
      calc 549000000 * L ^ 4 * |D4|
        _ ≤ 549549000 * L ^ 4 * |D4| := mul_le_mul_of_nonneg_right h_c (abs_nonneg D4)
        _ = (2013 * L ^ 2) * (273000 * L ^ 2 * |D4|) := by ring
        _ ≤ (2013 * L ^ 2) * |W_b| := mul_le_mul_of_nonneg_left hWb (by dsimp [L, bdlLambda]; norm_num)
    have h_tot : (900000 * L ^ 2) * |W_a| ≤ (900000 * L ^ 2) * (5 * |W_b|) := by
      have h_pos_L2 : 0 ≤ L ^ 2 := by dsimp [L, bdlLambda]; norm_num
      have h_pos_Wb : 0 ≤ L ^ 2 * |W_b| := mul_nonneg h_pos_L2 (abs_nonneg W_b)
      linarith
    exact le_of_mul_le_mul_left h_tot (by dsimp [L, bdlLambda]; norm_num)
  have h_prove_dom_b : 273000 * L ^ 2 * |D4| ≤ |W_a| → |W_b| ≤ 5 * |W_a| := by
    intro hWa
    -- Step 2: Complete the main case analysis and bound assembly for `abs_dom_and_lower_of_normal_cross_eq`
    have h_eq : N_a * W_b = N_b * W_a + E * K := by linarith [h_id]
    have h_tri : |N_a * W_b| ≤ |N_b * W_a| + |E * K| := by
      rw [h_eq]; exact abs_add_le _ _
    rw [abs_mul N_a W_b, abs_of_nonneg hNa_pos, abs_mul N_b W_a, abs_of_nonneg hNb_pos] at h_tri
    have h_lhs : (900000 * L ^ 2) * |W_b| ≤ N_a * |W_b| :=
      mul_le_mul_of_nonneg_right hNa.1 (abs_nonneg W_b)
    have h_rhs1 : N_b * |W_a| ≤ (987000 * L ^ 2) * |W_a| :=
      mul_le_mul_of_nonneg_right hNb.2 (abs_nonneg W_a)
    have h_rhs2 : 549000000 * L ^ 4 * |D4| ≤ (2013 * L ^ 2) * |W_a| := by
      have h_c : 549000000 * L ^ 4 ≤ 549549000 * L ^ 4 := by dsimp [L, bdlLambda]; norm_num
      calc 549000000 * L ^ 4 * |D4|
        _ ≤ 549549000 * L ^ 4 * |D4| := mul_le_mul_of_nonneg_right h_c (abs_nonneg D4)
        _ = (2013 * L ^ 2) * (273000 * L ^ 2 * |D4|) := by ring
        _ ≤ (2013 * L ^ 2) * |W_a| := mul_le_mul_of_nonneg_left hWa (by dsimp [L, bdlLambda]; norm_num)
    have h_tot : (900000 * L ^ 2) * |W_b| ≤ (900000 * L ^ 2) * (5 * |W_a|) := by
      have h_pos_L2 : 0 ≤ L ^ 2 := by dsimp [L, bdlLambda]; norm_num
      have h_pos_Wa : 0 ≤ L ^ 2 * |W_a| := mul_nonneg h_pos_L2 (abs_nonneg W_a)
      linarith
    exact le_of_mul_le_mul_left h_tot (by dsimp [L, bdlLambda]; norm_num)
  refine ⟨fun hWa => ?_, h_prove_dom_b⟩
  have hWb : 273000 * L ^ 2 * |D4| ≤ |W_b| := by
    have h_eq : N_a * W_b = N_b * W_a + E * K := by linarith [h_id]
    have h_tri : |N_b * W_a| - |E * K| ≤ |N_a * W_b| := by
      have := abs_sub_abs_le_abs_sub (N_b * W_a) (- (E * K))
      rw [sub_neg_eq_add, abs_neg, ← h_eq] at this
      exact this
    rw [abs_mul N_b W_a, abs_of_nonneg hNb_pos, abs_mul N_a W_b, abs_of_nonneg hNa_pos] at h_tri
    have h_lhs : (900000 * L ^ 2) * (300000 * L ^ 2 * |D4|) ≤ N_b * |W_a| :=
      mul_le_mul hNb.1 hWa (by positivity) hNb_pos
    have h_rhs : N_a * |W_b| ≤ (987000 * L ^ 2) * |W_b| :=
      mul_le_mul_of_nonneg_right hNa.2 (abs_nonneg W_b)
    have h_tot : (987000 * L ^ 2) * (273000 * L ^ 2 * |D4|) ≤ (987000 * L ^ 2) * |W_b| := by
      calc (987000 * L ^ 2) * (273000 * L ^ 2 * |D4|)
        _ = (900000 * L ^ 2) * (300000 * L ^ 2 * |D4|) - 549000000 * L ^ 4 * |D4| := by ring
        _ ≤ N_b * |W_a| - |E * K| := sub_le_sub h_lhs hEK
        _ ≤ (987000 * L ^ 2) * |W_b| := le_trans h_tri h_rhs
    exact le_of_mul_le_mul_left h_tot (by dsimp [L, bdlLambda]; norm_num)
  exact ⟨hWb, h_prove_dom_a hWb⟩

/-! ## 3. Stage-3 Dominant Vertex-Type Trichotomy -/

/-- **Stage 3 Dominant Vertex Type Trichotomy (`stage3_dominant_type_trichotomy`)**:
    Under `FourSimplicesDominantCramerCompatible pcode s1 s2 s3 u`, at least one of the three vertices
    of `u` (`u.val.1 ∈ B.M_X`, `u.val.2.1 ∈ B.Q`, `u.val.2.2 ∈ B.M_Z`) has dominant `rsin` sensitivity
    `≥ 273000 * bdlLambda^2 * |D4|` and `rcos` sensitivity `≤ 5` times its `rsin` sensitivity. -/
lemma stage3_dominant_type_trichotomy (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000)
    (htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000)
    (htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000)
    (s1 s2 s3 u : ActiveSimplex2 B.code)
    (h_dom : FourSimplicesDominantCramerCompatible
      (bdlPerturbStep B.code bdlLambda
        (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x)))
      s1 s2 s3 u) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let N (s : ActiveSimplex2 B.code) :=
      cross3D (sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1))
              (sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1))
    let N1 := N s1; let N2 := N s2; let N3 := N s3
    let b1 := dot3D (pcode.posX s1.val.1) N1
    let b2 := dot3D (pcode.posX s2.val.1) N2
    let b3 := dot3D (pcode.posX s3.val.1) N3
    let A4 := pcode.posX u.val.1
    let B4 := pcode.posQ u.val.2.1
    let C4 := pcode.posZ u.val.2.2
    let D4 := - det3D N1 N2 N3
    let V0 : Point3D := fun a =>
      b1 * cross3D N2 N3 a - b2 * cross3D N1 N3 a + b3 * cross3D N1 N2 a
    let WA := cross3D (fun a => V0 a + D4 * B4 a) (sub3D C4 B4)
    let WB := cross3D (fun a => V0 a + D4 * C4 a) (sub3D A4 C4)
    let WC := cross3D (fun a => V0 a + D4 * A4 a) (sub3D B4 A4)
    (273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| ∧ |WA 0| ≤ 5 * |WA 1|) ∨
    (273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WB 2| ∧ |WB 1| ≤ 5 * |WB 2|) ∨
    (273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WC 0| ∧ |WC 2| ≤ 5 * |WC 0|) := by
  -- Step 1: Establish initial algebraic and geometric reductions for `stage3_dominant_type_trichotomy`
  intro pcode N N1 N2 N3 b1 b2 b3 A4 B4 C4 D4 V0 WA WB WC
  have h_sum := stage3_coord1_sensitivity_ge B h8 tQ tZ tX htQ htZ htX N1 N2 N3 b1 b2 b3 u
  change 900000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| + |WB 1| + |WC 1| at h_sum
  obtain ⟨hCB2, hCB0, hCB1, hBA0, hBA1, hBA2⟩ :=
    perturbed_simplex_edge_bounds B h8 tQ tZ tX u (htQ u.val.2.1) (htZ u.val.2.2) (htX u.val.1)
  change (31 * (bdlLambda : ℝ) ≤ C4 2 - B4 2 ∧ C4 2 - B4 2 ≤ 49 * (bdlLambda : ℝ)) at hCB2
  change (-1008 * (bdlLambda : ℝ) ≤ C4 0 - B4 0 ∧ C4 0 - B4 0 ≤ -991 * (bdlLambda : ℝ)) at hCB0
  change (951 * (bdlLambda : ℝ) ≤ C4 1 - B4 1 ∧ C4 1 - B4 1 ≤ 968 * (bdlLambda : ℝ)) at hCB1
  change (951 * (bdlLambda : ℝ) ≤ B4 0 - A4 0 ∧ B4 0 - A4 0 ≤ 968 * (bdlLambda : ℝ)) at hBA0
  change (31 * (bdlLambda : ℝ) ≤ B4 1 - A4 1 ∧ B4 1 - A4 1 ≤ 49 * (bdlLambda : ℝ)) at hBA1
  change (-1008 * (bdlLambda : ℝ) ≤ B4 2 - A4 2 ∧ B4 2 - A4 2 ≤ -991 * (bdlLambda : ℝ)) at hBA2
  obtain ⟨hNu0_lo, hNu1_lo, hNu2_lo⟩ :=
    perturbed_simplex_normal_coord_ge_900000_lambda_sq B h8 tQ tZ tX u
      (htQ u.val.2.1) (htZ u.val.2.2) (htX u.val.1)
  let N4 := N u
  change 900000 * (bdlLambda : ℝ) ^ 2 ≤ N4 0 at hNu0_lo
  change 900000 * (bdlLambda : ℝ) ^ 2 ≤ N4 1 at hNu1_lo
  change 900000 * (bdlLambda : ℝ) ^ 2 ≤ N4 2 at hNu2_lo
  have hL : (0 : ℝ) < bdlLambda := by dsimp [bdlLambda]; norm_num
  have hNu0_hi : N4 0 ≤ 987000 * (bdlLambda : ℝ) ^ 2 := by
    have h_eq : N4 0 = (B4 1 - A4 1) * (C4 2 - B4 2) - (B4 2 - A4 2) * (C4 1 - B4 1) := by
      dsimp [N4, N, cross3D, sub3D]; ring
    -- Step 2: Complete the main case analysis and bound assembly for `stage3_dominant_type_trichotomy`
    rw [h_eq]; nlinarith
  have hNu1_hi : N4 1 ≤ 987000 * (bdlLambda : ℝ) ^ 2 := by
    have h_eq : N4 1 = (B4 2 - A4 2) * (C4 0 - B4 0) - (B4 0 - A4 0) * (C4 2 - B4 2) := by
      dsimp [N4, N, cross3D, sub3D]; ring
    rw [h_eq]; nlinarith
  have hNu2_hi : N4 2 ≤ 987000 * (bdlLambda : ℝ) ^ 2 := by
    have h_eq : N4 2 = (B4 0 - A4 0) * (C4 1 - B4 1) - (B4 1 - A4 1) * (C4 0 - B4 0) := by
      dsimp [N4, N, cross3D, sub3D]; ring
    rw [h_eq]; nlinarith
  obtain ⟨h_idA, h_idB, h_idC1, h_idC2⟩ := cramer_normal_cross_WA_WB_WC V0 A4 B4 C4 D4
  let K := dot3D (fun a => V0 a + D4 * B4 a) N4
  have hK : |K| ≤ 7000000 * (bdlLambda : ℝ) ^ 2 * |D4| := by
    unfold FourSimplicesDominantCramerCompatible at h_dom
    have h_eq_K : K =
        det3D N2 N3 N4 * dot3D N1 (pcode.posX s1.val.1) +
        (- det3D N1 N3 N4) * dot3D N2 (pcode.posX s2.val.1) +
        det3D N1 N2 N4 * dot3D N3 (pcode.posX s3.val.1) +
        D4 * dot3D N4 A4 := by
      dsimp [K, V0, D4, N4, N, b1, b2, b3, A4, B4, C4, dot3D, det3D, cross3D, sub3D]; ring
    rw [h_eq_K]
    exact h_dom
  have hE_A : |C4 2 - B4 2| ≤ 1008 * (bdlLambda : ℝ) := by
    rw [abs_le]; constructor <;> linarith [hCB2.1, hCB2.2]
  have hE_B : |- (A4 0 - C4 0)| ≤ 1008 * (bdlLambda : ℝ) := by
    rw [abs_neg, abs_le]; constructor <;> linarith [hCB0.1, hCB0.2, hBA0.1, hBA0.2]
  have hE_C1 : |B4 2 - A4 2| ≤ 1008 * (bdlLambda : ℝ) := by
    rw [abs_le]; constructor <;> linarith [hBA2.1, hBA2.2]
  have hE_C2 : |B4 1 - A4 1| ≤ 1008 * (bdlLambda : ℝ) := by
    rw [abs_le]; constructor <;> linarith [hBA1.1, hBA1.2]
  have h_trich : 300000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| ∨
      300000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WB 1| ∨
      300000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WC 1| := by
    by_contra h_not
    push_neg at h_not
    linarith [h_not.1, h_not.2.1, h_not.2.2, h_sum]
  rcases h_trich with hWA | hWB | hWC
  · left
    have hWA_lo : 273000 * (bdlLambda : ℝ) ^ 2 * |D4| ≤ |WA 1| := by
      linarith [hWA, show 0 ≤ (bdlLambda : ℝ) ^ 2 * |D4| by positivity]
    have h_conv := (abs_dom_and_lower_of_normal_cross_eq
      ⟨hNu1_lo, hNu1_hi⟩ ⟨hNu0_lo, hNu0_hi⟩ hE_A hK h_idA).2 hWA_lo
    exact ⟨hWA_lo, h_conv⟩
  · right; left
    exact (abs_dom_and_lower_of_normal_cross_eq
      ⟨hNu1_lo, hNu1_hi⟩ ⟨hNu2_lo, hNu2_hi⟩ hE_B hK h_idB).1 hWB
  · right; right
    have hWC0 := ((abs_dom_and_lower_of_normal_cross_eq
      ⟨hNu1_lo, hNu1_hi⟩ ⟨hNu0_lo, hNu0_hi⟩ hE_C1 hK h_idC1).1 hWC).1
    have hWC2 := (abs_dom_and_lower_of_normal_cross_eq
      ⟨hNu0_lo, hNu0_hi⟩ ⟨hNu2_lo, hNu2_hi⟩ hE_C2 hK h_idC2).2 hWC0
    exact ⟨hWC0, hWC2⟩

end WeldedHierarchy
