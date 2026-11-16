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

import Proofs.Step1LLLDensity.PerturbedSimplexSensitivity

/-!
# Three-Stage Dominant Cramer Determinant Cascade for Unit-Ball Simplex Multiplicity

Bounds inner products of perturbed 2-simplex normals (`perturbed_simplex_normal_dot3D_le`) and upgrades four-simplex Cramer compatibility to dominant-determinant compatibility (`fourSimplicesDominantCramerCompatible_of_cramerCompatible_of_max_det`). Proves the three-stage combinatorial cascade `card_le_bdlDensityTPrime_of_three_stage_dominant_cramer_cascade`, showing that avoiding Stage-1, Stage-2, and Stage-3 degeneracies bounds unit-ball active 2-simplex multiplicity by `bdlDensityTPrime`.

## References

* Part I, Section 2.2 (`subsec:step1-lll`), Proposition 2.4 (`prop:step1-lll`)
-/

noncomputable section
open scoped Classical BigOperators
namespace WeldedHierarchy

/-! ## 1. Perturbed Simplex Normal Norm Upper Bounds -/

/-- Fast standalone algebraic bound `dot3D (cross3D u v) (cross3D u v) ≤ (1750000 * L ^ 2) ^ 2`
    from the simplex edge coordinate intervals. -/
lemma cross3D_normal_dot3D_le_of_edge_bounds (u v : Point3D) (L : ℝ) (hL : 0 ≤ L)
    (hu0 : 951 * L ≤ u 0 ∧ u 0 ≤ 968 * L)
    (hu1 : 31 * L ≤ u 1 ∧ u 1 ≤ 49 * L)
    (hu2 : -1008 * L ≤ u 2 ∧ u 2 ≤ -991 * L)
    (hw0 : -1008 * L ≤ v 0 - u 0 ∧ v 0 - u 0 ≤ -991 * L)
    (hw1 : 951 * L ≤ v 1 - u 1 ∧ v 1 - u 1 ≤ 968 * L)
    (hw2 : 31 * L ≤ v 2 - u 2 ∧ v 2 - u 2 ≤ 49 * L) :
    dot3D (cross3D u v) (cross3D u v) ≤ (1750000 * L ^ 2) ^ 2 := by
  have h0_eq : cross3D u v 0 = u 1 * (v 2 - u 2) - u 2 * (v 1 - u 1) := by dsimp [cross3D]; ring
  have h1_eq : cross3D u v 1 = u 2 * (v 0 - u 0) - u 0 * (v 2 - u 2) := by dsimp [cross3D]; ring
  have h2_eq : cross3D u v 2 = u 0 * (v 1 - u 1) - u 1 * (v 0 - u 0) := by dsimp [cross3D]; ring
  have h0_lo : 0 ≤ cross3D u v 0 := by rw [h0_eq]; nlinarith
  have h0_hi : cross3D u v 0 ≤ 987000 * L ^ 2 := by rw [h0_eq]; nlinarith
  have h1_lo : 0 ≤ cross3D u v 1 := by rw [h1_eq]; nlinarith
  have h1_hi : cross3D u v 1 ≤ 987000 * L ^ 2 := by rw [h1_eq]; nlinarith
  have h2_lo : 0 ≤ cross3D u v 2 := by rw [h2_eq]; nlinarith
  have h2_hi : cross3D u v 2 ≤ 987000 * L ^ 2 := by rw [h2_eq]; nlinarith
  have h0_sq : cross3D u v 0 * cross3D u v 0 ≤ (987000 * L ^ 2) ^ 2 := by nlinarith [h0_lo, h0_hi]
  have h1_sq : cross3D u v 1 * cross3D u v 1 ≤ (987000 * L ^ 2) ^ 2 := by nlinarith [h1_lo, h1_hi]
  have h2_sq : cross3D u v 2 * cross3D u v 2 ≤ (987000 * L ^ 2) ^ 2 := by nlinarith [h2_lo, h2_hi]
  dsimp [dot3D]
  nlinarith [h0_sq, h1_sq, h2_sq]

/-- Upper bound `dot3D N N ≤ (1750000 * bdlLambda^2)^2` on the squared Euclidean norm of the normal vector
    `N = cross3D (B - A) (C - A)` of any perturbed active 2-simplex `s` for parameters in `[0, 1/1000]`. -/
lemma perturbed_simplex_normal_dot3D_le (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ) (s : ActiveSimplex2 B.code)
    (htQ : 0 ≤ tQ s.val.2.1 ∧ tQ s.val.2.1 ≤ 1 / 1000)
    (htZ : 0 ≤ tZ s.val.2.2 ∧ tZ s.val.2.2 ≤ 1 / 1000)
    (htX : 0 ≤ tX s.val.1 ∧ tX s.val.1 ≤ 1 / 1000) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    let N := cross3D (sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1))
                     (sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1))
    dot3D N N ≤ (1750000 * (bdlLambda : ℝ) ^ 2) ^ 2 := by
  obtain ⟨hCB2, hCB0, hCB1, hBA0, hBA1, hBA2⟩ :=
    perturbed_simplex_edge_bounds B h8 tQ tZ tX s htQ htZ htX
  let pcode := bdlPerturbStep B.code bdlLambda
    (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
  let u := sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1)
  let v := sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1)
  have h_sub : ∀ a : Fin 3, v a - u a = pcode.posZ s.val.2.2 a - pcode.posQ s.val.2.1 a := by
    intro a; dsimp [u, v, sub3D]; ring
  exact cross3D_normal_dot3D_le_of_edge_bounds u v (bdlLambda : ℝ) (by dsimp [bdlLambda]; norm_num)
    hBA0 hBA1 hBA2
    (by rw [h_sub 0]; exact hCB0)
    (by rw [h_sub 1]; exact hCB1)
    (by rw [h_sub 2]; exact hCB2)

/-- Pure algebraic helper: if `R^2 ≤ 4 * (D1^2 * n1 + D2^2 * n2 + D3^2 * n3 + D4^2 * n4)` with
    `|D1|, |D2|, |D3| ≤ |D4|` and `0 ≤ n_i ≤ M^2`, then `|R| ≤ 4 * M * |D4|`. -/
lemma abs_le_four_mul_of_sq_le_four_mul_sum {R D1 D2 D3 D4 n1 n2 n3 n4 M : ℝ}
    (hM : 0 ≤ M)
    (hn1 : 0 ≤ n1 ∧ n1 ≤ M ^ 2) (hn2 : 0 ≤ n2 ∧ n2 ≤ M ^ 2)
    (hn3 : 0 ≤ n3 ∧ n3 ≤ M ^ 2) (hn4 : 0 ≤ n4 ∧ n4 ≤ M ^ 2)
    (hD1 : |D1| ≤ |D4|) (hD2 : |D2| ≤ |D4|) (hD3 : |D3| ≤ |D4|)
    (h_sq : R ^ 2 ≤ 4 * (D1 ^ 2 * n1 + D2 ^ 2 * n2 + D3 ^ 2 * n3 + D4 ^ 2 * n4)) :
    |R| ≤ 4 * M * |D4| := by
  have hD1_sq : D1 ^ 2 ≤ D4 ^ 2 := sq_le_sq.mpr hD1
  have hD2_sq : D2 ^ 2 ≤ D4 ^ 2 := sq_le_sq.mpr hD2
  have hD3_sq : D3 ^ 2 ≤ D4 ^ 2 := sq_le_sq.mpr hD3
  have h1 : D1 ^ 2 * n1 ≤ D4 ^ 2 * M ^ 2 := mul_le_mul hD1_sq hn1.2 hn1.1 (sq_nonneg D4)
  have h2 : D2 ^ 2 * n2 ≤ D4 ^ 2 * M ^ 2 := mul_le_mul hD2_sq hn2.2 hn2.1 (sq_nonneg D4)
  have h3 : D3 ^ 2 * n3 ≤ D4 ^ 2 * M ^ 2 := mul_le_mul hD3_sq hn3.2 hn3.1 (sq_nonneg D4)
  have h4 : D4 ^ 2 * n4 ≤ D4 ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left hn4.2 (sq_nonneg D4)
  have h_tot : R ^ 2 ≤ (4 * M * |D4|) ^ 2 := by
    have h_eq : (4 * M * |D4|) ^ 2 = 16 * (D4 ^ 2 * M ^ 2) := by
      calc (4 * M * |D4|) ^ 2 = 16 * M ^ 2 * |D4| ^ 2 := by ring
        _ = 16 * M ^ 2 * D4 ^ 2 := by rw [sq_abs]
        _ = 16 * (D4 ^ 2 * M ^ 2) := by ring
    rw [h_eq]
    linarith
  exact abs_le.mpr (abs_le_of_sq_le_sq' h_tot (by positivity))

/-- Whenever `(s1, s2, s3)` has dominant 3-minor (`|D1| ≤ |D4|`, `|D2| ≤ |D4|`, `|D3| ≤ |D4|`),
    `FourSimplicesCramerCompatible pcode s1 s2 s3 s4` implies `FourSimplicesDominantCramerCompatible pcode s1 s2 s3 s4`. -/
lemma fourSimplicesDominantCramerCompatible_of_cramerCompatible_of_max_det
    (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000)
    (htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000)
    (htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000)
    (s1 s2 s3 s4 : ActiveSimplex2 B.code)
    (h_compat : FourSimplicesCramerCompatible
      (bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x)))
      s1 s2 s3 s4)
    (hD1 : let pcode := bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
           let N1 := cross3D (sub3D (pcode.posQ s1.val.2.1) (pcode.posX s1.val.1)) (sub3D (pcode.posZ s1.val.2.2) (pcode.posX s1.val.1))
           let N2 := cross3D (sub3D (pcode.posQ s2.val.2.1) (pcode.posX s2.val.1)) (sub3D (pcode.posZ s2.val.2.2) (pcode.posX s2.val.1))
           let N3 := cross3D (sub3D (pcode.posQ s3.val.2.1) (pcode.posX s3.val.1)) (sub3D (pcode.posZ s3.val.2.2) (pcode.posX s3.val.1))
           let N4 := cross3D (sub3D (pcode.posQ s4.val.2.1) (pcode.posX s4.val.1)) (sub3D (pcode.posZ s4.val.2.2) (pcode.posX s4.val.1))
           |det3D N2 N3 N4| ≤ |- det3D N1 N2 N3|)
    (hD2 : let pcode := bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
           let N1 := cross3D (sub3D (pcode.posQ s1.val.2.1) (pcode.posX s1.val.1)) (sub3D (pcode.posZ s1.val.2.2) (pcode.posX s1.val.1))
           let N2 := cross3D (sub3D (pcode.posQ s2.val.2.1) (pcode.posX s2.val.1)) (sub3D (pcode.posZ s2.val.2.2) (pcode.posX s2.val.1))
           let N3 := cross3D (sub3D (pcode.posQ s3.val.2.1) (pcode.posX s3.val.1)) (sub3D (pcode.posZ s3.val.2.2) (pcode.posX s3.val.1))
           let N4 := cross3D (sub3D (pcode.posQ s4.val.2.1) (pcode.posX s4.val.1)) (sub3D (pcode.posZ s4.val.2.2) (pcode.posX s4.val.1))
           |- det3D N1 N3 N4| ≤ |- det3D N1 N2 N3|)
    (hD3 : let pcode := bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
           let N1 := cross3D (sub3D (pcode.posQ s1.val.2.1) (pcode.posX s1.val.1)) (sub3D (pcode.posZ s1.val.2.2) (pcode.posX s1.val.1))
           let N2 := cross3D (sub3D (pcode.posQ s2.val.2.1) (pcode.posX s2.val.1)) (sub3D (pcode.posZ s2.val.2.2) (pcode.posX s2.val.1))
           let N3 := cross3D (sub3D (pcode.posQ s3.val.2.1) (pcode.posX s3.val.1)) (sub3D (pcode.posZ s3.val.2.2) (pcode.posX s3.val.1))
           let N4 := cross3D (sub3D (pcode.posQ s4.val.2.1) (pcode.posX s4.val.1)) (sub3D (pcode.posZ s4.val.2.2) (pcode.posX s4.val.1))
           |det3D N1 N2 N4| ≤ |- det3D N1 N2 N3|) :
    FourSimplicesDominantCramerCompatible
      (bdlPerturbStep B.code bdlLambda (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x)))
      s1 s2 s3 s4 := by
  -- Step 1: Establish initial algebraic and geometric reductions for `fourSimplicesDominantCramerCompatible_of_cramerCompatible_of_max_det`
  have hN1 := perturbed_simplex_normal_dot3D_le B h8 tQ tZ tX s1 (htQ _) (htZ _) (htX _)
  have hN2 := perturbed_simplex_normal_dot3D_le B h8 tQ tZ tX s2 (htQ _) (htZ _) (htX _)
  have hN3 := perturbed_simplex_normal_dot3D_le B h8 tQ tZ tX s3 (htQ _) (htZ _) (htX _)
  have hN4 := perturbed_simplex_normal_dot3D_le B h8 tQ tZ tX s4 (htQ _) (htZ _) (htX _)
  -- Step 2: Complete the main case analysis and bound assembly for `fourSimplicesDominantCramerCompatible_of_cramerCompatible_of_max_det`
  have h_dot_nonneg : ∀ u : Point3D, 0 ≤ dot3D u u := fun u => by dsimp [dot3D]; nlinarith
  unfold FourSimplicesCramerCompatible at h_compat
  unfold FourSimplicesDominantCramerCompatible
  have h_res := abs_le_four_mul_of_sq_le_four_mul_sum
    (by dsimp [bdlLambda]; positivity : 0 ≤ 1750000 * (bdlLambda : ℝ) ^ 2)
    ⟨h_dot_nonneg _, hN1⟩ ⟨h_dot_nonneg _, hN2⟩ ⟨h_dot_nonneg _, hN3⟩ ⟨h_dot_nonneg _, hN4⟩
    hD1 hD2 hD3 h_compat
  linarith

/-! ## 2. Dominant Cramer Compatibility via Maximum-Determinant Selection -/

/-- **3-Stage Dominant Cramer Cascade Theorem (`card_le_bdlDensityTPrime_of_three_stage_dominant_cramer_cascade`)**:
    Uses `Finset.exists_max_image` on the nonempty set `T_disj` of pairwise vertex-disjoint triples in `S(x0)`
    to select a triple `(s1*, s2*, s3*) ∈ T_disj` that simultaneously:
    1. inherits `Stage2Good_max s1* s2* s3*` from the 2-stage greedy witness `(s1_0, s2_0, s3_0) ∈ T_disj`, AND
    2. dominates all 3-minors (`|D1|, |D2|, |D3| ≤ |D4*|`), upgrading `FourSimplicesCramerCompatible` to
       `FourSimplicesDominantCramerCompatible pcode s1* s2* s3* u` for every `u ∈ S(x0) \ (star s1* ∪ star s2* ∪ star s3*)`. -/
lemma card_le_bdlDensityTPrime_of_three_stage_dominant_cramer_cascade
    (B : BundledCSSCode3D) (h8 : HasInteractionRange8 B)
    (D M1 M2 M3 : ℕ) (hDM : (3 + M1) * D ≤ 5595 ∧ (6 + M2) * D ≤ 5595 ∧ (9 + M3) * D ≤ 5595)
    (h_deg : HasBoundedSimplexDegreeD B D)
    (tQ : B.Q → ℝ) (tZ : B.M_Z → ℝ) (tX : B.M_X → ℝ)
    (htQ : ∀ q, 0 ≤ tQ q ∧ tQ q ≤ 1 / 1000)
    (htZ : ∀ z, 0 ≤ tZ z ∧ tZ z ≤ 1 / 1000)
    (htX : ∀ x, 0 ≤ tX x ∧ tX x ≤ 1 / 1000)
    (δ3 : ℝ)
    (LocalClose : ActiveSimplex2 B.code → ActiveSimplex2 B.code → Prop)
    (Stage1Good : ActiveSimplex2 B.code → ActiveSimplex2 B.code → Prop)
    (h_stage1 : ∀ s1 : ActiveSimplex2 B.code,
      (Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
        VertexDisjointSimplex2 s1.val u.val ∧
        LocalClose s1 u ∧
        ¬ Stage1Good s1 u)).card ≤ M1 * D)
    (h_stage2 : ∀ s1 s2 : ActiveSimplex2 B.code,
      VertexDisjointSimplex2 s1.val s2.val →
      LocalClose s1 s2 →
      Stage1Good s1 s2 →
      let pcode := bdlPerturbStep B.code bdlLambda
        (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
      let N (s : ActiveSimplex2 B.code) :=
        -- Step 1: Establish initial algebraic and geometric reductions for `card_le_bdlDensityTPrime_of_three_stage_dominant_cramer_cascade`
        cross3D (sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1))
                (sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1))
      (Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
        VertexDisjointSimplex2 s1.val u.val ∧
        VertexDisjointSimplex2 s2.val u.val ∧
        LocalClose s1 u ∧
        ¬ (δ3 < |- det3D (N s1) (N s2) (N u)|))).card ≤ M2 * D)
    (h_stage3 : ∀ s1 s2 s3 : ActiveSimplex2 B.code,
      VertexDisjointSimplex2 s1.val s2.val →
      VertexDisjointSimplex2 s1.val s3.val →
      VertexDisjointSimplex2 s2.val s3.val →
      LocalClose s1 s2 →
      LocalClose s1 s3 →
      let pcode := bdlPerturbStep B.code bdlLambda
        (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
      let N (s : ActiveSimplex2 B.code) :=
        cross3D (sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1))
                (sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1))
      δ3 < |- det3D (N s1) (N s2) (N s3)| →
      (Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
        VertexDisjointSimplex2 s1.val u.val ∧
        VertexDisjointSimplex2 s2.val u.val ∧
        VertexDisjointSimplex2 s3.val u.val ∧
        LocalClose s1 u ∧
        FourSimplicesDominantCramerCompatible pcode s1 s2 s3 u)).card ≤ M3 * D)
    (x0 : Point3D)
    (h_local_close :
      let pcode := bdlPerturbStep B.code bdlLambda
        (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
      ∀ s1 s2 : ActiveSimplex2 B.code,
        (simplex2D3D (pcode.posX s1.val.1) (pcode.posQ s1.val.2.1) (pcode.posZ s1.val.2.2) ∩
          ball3D x0 1).Nonempty →
        (simplex2D3D (pcode.posX s2.val.1) (pcode.posQ s2.val.2.1) (pcode.posZ s2.val.2.2) ∩
          ball3D x0 1).Nonempty →
        LocalClose s1 s2) :
    let pcode := bdlPerturbStep B.code bdlLambda
      (fun q => rationalCap0 (tQ q)) (fun z => rationalCap1 (tZ z)) (fun x => rationalCap2 (tX x))
    ((Finset.univ.filter (fun s : ActiveSimplex2 B.code =>
      (simplex2D3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) ∩
        ball3D x0 1).Nonempty)).card : ℝ) ≤ bdlDensityTPrime := by
  intro pcode
  let N (s : ActiveSimplex2 B.code) : Point3D :=
    cross3D (sub3D (pcode.posQ s.val.2.1) (pcode.posX s.val.1))
            (sub3D (pcode.posZ s.val.2.2) (pcode.posX s.val.1))
  let S := Finset.univ.filter (fun s : ActiveSimplex2 B.code =>
    (simplex2D3D (pcode.posX s.val.1) (pcode.posQ s.val.2.1) (pcode.posZ s.val.2.2) ∩
      ball3D x0 1).Nonempty)
  have h_le_5595 : S.card ≤ 5595 := by
    by_contra h_gt
    push_neg at h_gt
    obtain ⟨s1_0, hs1_0⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) h_gt)
    let Bad1 := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      VertexDisjointSimplex2 s1_0.val u.val ∧
      LocalClose s1_0 u ∧
      ¬ Stage1Good s1_0 u)
    have hBad1_le : Bad1.card ≤ M1 * D := h_stage1 s1_0
    let S1 := (S \ simplexVertexStar B.code s1_0) \ Bad1
    have h_star1 : (simplexVertexStar B.code s1_0).card ≤ 3 * D :=
      card_simplexVertexStar_le_three_mul B h_deg s1_0
    have hS1_gt : 0 < S1.card := by
      have h1 : S.card ≤ (S \ simplexVertexStar B.code s1_0).card + 3 * D :=
        le_trans Finset.card_le_card_sdiff_add_card (Nat.add_le_add_left h_star1 _)
      have h2 : (S \ simplexVertexStar B.code s1_0).card ≤ S1.card + M1 * D :=
        le_trans Finset.card_le_card_sdiff_add_card (Nat.add_le_add_left hBad1_le _)
      have hDM1 := hDM.1
      simp only [Nat.add_mul] at *
      omega
    obtain ⟨s2_0, hs2_0_S1⟩ := Finset.card_pos.mp hS1_gt
    rw [Finset.mem_sdiff, Finset.mem_sdiff] at hs2_0_S1
    have hs2_0 : s2_0 ∈ S := hs2_0_S1.1.1
    have hd12_0 : VertexDisjointSimplex2 s1_0.val s2_0.val :=
      (not_mem_simplexVertexStar_iff B.code s1_0 s2_0).mp hs2_0_S1.1.2
    have h_loc12_0 : LocalClose s1_0 s2_0 :=
      h_local_close s1_0 s2_0 (Finset.mem_filter.mp hs1_0).2 (Finset.mem_filter.mp hs2_0).2
    have h_good12_0 : Stage1Good s1_0 s2_0 := by
      by_contra h_not
      exact hs2_0_S1.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd12_0, h_loc12_0, h_not⟩)
    let Bad2 := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      VertexDisjointSimplex2 s1_0.val u.val ∧
      VertexDisjointSimplex2 s2_0.val u.val ∧
      LocalClose s1_0 u ∧
      ¬ (δ3 < |- det3D (N s1_0) (N s2_0) (N u)|))
    -- Step 2: Complete the main case analysis and bound assembly for `card_le_bdlDensityTPrime_of_three_stage_dominant_cramer_cascade`
    have hBad2_le : Bad2.card ≤ M2 * D := h_stage2 s1_0 s2_0 hd12_0 h_loc12_0 h_good12_0
    let S2 := ((S \ simplexVertexStar B.code s1_0) \ simplexVertexStar B.code s2_0) \ Bad2
    have h_star2 : (simplexVertexStar B.code s2_0).card ≤ 3 * D :=
      card_simplexVertexStar_le_three_mul B h_deg s2_0
    have hS2_gt : 0 < S2.card := by
      have h0 : S.card ≤ (S \ simplexVertexStar B.code s1_0).card + 3 * D :=
        le_trans Finset.card_le_card_sdiff_add_card (Nat.add_le_add_left h_star1 _)
      have h1 : (S \ simplexVertexStar B.code s1_0).card ≤
          ((S \ simplexVertexStar B.code s1_0) \ simplexVertexStar B.code s2_0).card + 3 * D :=
        le_trans Finset.card_le_card_sdiff_add_card (Nat.add_le_add_left h_star2 _)
      have h2 : ((S \ simplexVertexStar B.code s1_0) \ simplexVertexStar B.code s2_0).card ≤ S2.card + M2 * D :=
        le_trans Finset.card_le_card_sdiff_add_card (Nat.add_le_add_left hBad2_le _)
      have hDM2 := hDM.2.1
      simp only [Nat.add_mul] at *
      omega
    obtain ⟨s3_0, hs3_0_S2⟩ := Finset.card_pos.mp hS2_gt
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_sdiff] at hs3_0_S2
    have hs3_0 : s3_0 ∈ S := hs3_0_S2.1.1.1
    have hd13_0 : VertexDisjointSimplex2 s1_0.val s3_0.val :=
      (not_mem_simplexVertexStar_iff B.code s1_0 s3_0).mp hs3_0_S2.1.1.2
    have hd23_0 : VertexDisjointSimplex2 s2_0.val s3_0.val :=
      (not_mem_simplexVertexStar_iff B.code s2_0 s3_0).mp hs3_0_S2.1.2
    have h_loc13_0 : LocalClose s1_0 s3_0 :=
      h_local_close s1_0 s3_0 (Finset.mem_filter.mp hs1_0).2 (Finset.mem_filter.mp hs3_0).2
    have h_good123_0 : δ3 < |- det3D (N s1_0) (N s2_0) (N s3_0)| := by
      by_contra h_not
      exact hs3_0_S2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd13_0, hd23_0, h_loc13_0, h_not⟩)
    -- Now select `(s1, s2, s3) ∈ T_disj` maximizing `|- det3D (N s1) (N s2) (N s3)|` across `S`!
    let T_disj : Finset (ActiveSimplex2 B.code × ActiveSimplex2 B.code × ActiveSimplex2 B.code) :=
      (S ×ˢ (S ×ˢ S)).filter (fun t =>
        VertexDisjointSimplex2 t.1.val t.2.1.val ∧
        VertexDisjointSimplex2 t.1.val t.2.2.val ∧
        VertexDisjointSimplex2 t.2.1.val t.2.2.val)
    -- Step 3: Conclude final cardinality and norm estimates for `card_le_bdlDensityTPrime_of_three_stage_dominant_cramer_cascade`
    have hT_mem0 : (s1_0, s2_0, s3_0) ∈ T_disj := by
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
      exact ⟨⟨hs1_0, hs2_0, hs3_0⟩, hd12_0, hd13_0, hd23_0⟩
    obtain ⟨⟨s1, s2, s3⟩, ht_mem, ht_max⟩ :=
      Finset.exists_max_image T_disj (fun t => |- det3D (N t.1) (N t.2.1) (N t.2.2)|) ⟨(s1_0, s2_0, s3_0), hT_mem0⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at ht_mem
    rcases ht_mem with ⟨⟨hs1, hs2, hs3⟩, hd12, hd13, hd23⟩
    have h_good123 : δ3 < |- det3D (N s1) (N s2) (N s3)| :=
      lt_of_lt_of_le h_good123_0 (ht_max (s1_0, s2_0, s3_0) hT_mem0)
    have h_loc12 : LocalClose s1 s2 :=
      h_local_close s1 s2 (Finset.mem_filter.mp hs1).2 (Finset.mem_filter.mp hs2).2
    have h_loc13 : LocalClose s1 s3 :=
      h_local_close s1 s3 (Finset.mem_filter.mp hs1).2 (Finset.mem_filter.mp hs3).2
    let S' := ((S \ simplexVertexStar B.code s1) \ simplexVertexStar B.code s2) \ simplexVertexStar B.code s3
    have hS'_gt : M3 * D < S'.card := by
      have h1 := card_sdiff_simplexVertexStar_ge_three_mul B h_deg S s1
      have h2 := card_sdiff_simplexVertexStar_ge_three_mul B h_deg (S \ simplexVertexStar B.code s1) s2
      have h3 := card_sdiff_simplexVertexStar_ge_three_mul B h_deg ((S \ simplexVertexStar B.code s1) \ simplexVertexStar B.code s2) s3
      have hDM3 := hDM.2.2
      dsimp [S']
      simp only [Nat.add_mul] at hDM3
      omega
    let Bad3 := Finset.univ.filter (fun u : ActiveSimplex2 B.code =>
      VertexDisjointSimplex2 s1.val u.val ∧
      VertexDisjointSimplex2 s2.val u.val ∧
      VertexDisjointSimplex2 s3.val u.val ∧
      LocalClose s1 u ∧
      FourSimplicesDominantCramerCompatible pcode s1 s2 s3 u)
    have hS'_sub : S' ⊆ Bad3 := by
      intro u hu
      dsimp [S'] at hu
      rw [Finset.mem_sdiff] at hu
      have hu2 := hu.1
      rw [Finset.mem_sdiff] at hu2
      have hu1 := hu2.1
      rw [Finset.mem_sdiff] at hu1
      have hu_S := hu1.1
      have hd1u := (not_mem_simplexVertexStar_iff B.code s1 u).mp hu1.2
      have hd2u := (not_mem_simplexVertexStar_iff B.code s2 u).mp hu2.2
      have hd3u := (not_mem_simplexVertexStar_iff B.code s3 u).mp hu.2
      have h_loc1u := h_local_close s1 u (Finset.mem_filter.mp hs1).2 (Finset.mem_filter.mp hu_S).2
      have h_cramer := four_simplices_inter_ball3D_implies_cramer_compatible pcode x0 s1 s2 s3 u
        (Finset.mem_filter.mp hs1).2 (Finset.mem_filter.mp hs2).2
        (Finset.mem_filter.mp hs3).2 (Finset.mem_filter.mp hu_S).2
      have hT1 : (s2, s3, u) ∈ T_disj := by
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨hs2, hs3, hu_S⟩, hd23, hd2u, hd3u⟩
      have hT2 : (s1, s3, u) ∈ T_disj := by
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨hs1, hs3, hu_S⟩, hd13, hd1u, hd3u⟩
      have hT3 : (s1, s2, u) ∈ T_disj := by
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product]
        exact ⟨⟨hs1, hs2, hu_S⟩, hd12, hd1u, hd2u⟩
      have hD1 : |det3D (N s2) (N s3) (N u)| ≤ |- det3D (N s1) (N s2) (N s3)| := by
        rw [← abs_neg (det3D (N s2) (N s3) (N u))]
        exact ht_max (s2, s3, u) hT1
      have hD2 : |- det3D (N s1) (N s3) (N u)| ≤ |- det3D (N s1) (N s2) (N s3)| :=
        ht_max (s1, s3, u) hT2
      have hD3 : |det3D (N s1) (N s2) (N u)| ≤ |- det3D (N s1) (N s2) (N s3)| := by
        rw [← abs_neg (det3D (N s1) (N s2) (N u))]
        exact ht_max (s1, s2, u) hT3
      have h_dom := fourSimplicesDominantCramerCompatible_of_cramerCompatible_of_max_det
        B h8 tQ tZ tX htQ htZ htX s1 s2 s3 u h_cramer hD1 hD2 hD3
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd1u, hd2u, hd3u, h_loc1u, h_dom⟩
    have hS'_le : S'.card ≤ M3 * D :=
      le_trans (Finset.card_le_card hS'_sub) (h_stage3 s1 s2 s3 hd12 hd13 hd23 h_loc12 h_loc13 h_good123)
    omega
  have h_real : (S.card : ℝ) ≤ 5595 := by exact_mod_cast h_le_5595
  dsimp [bdlDensityTPrime]
  linarith

end WeldedHierarchy
